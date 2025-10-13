//! Memory-efficient data structures based on patricia tree (a.k.a, radix tree).
//!
//! A common prefixes of the keys in a patricia tree are represented by a shared path.
//! So if the prefixes of the key set is highly redundant,
//! the memory usage of the resulting patricia tree will be drastically less than
//! more generic data structures (e.g., `BTreeMap`).
//!
//! See [Radix tree](https://en.wikipedia.org/wiki/Radix_tree) for more details.
//!
//! # Examples
//!
//! ```
//! use patricia_tree::PatriciaMap;
//!
//! let mut map = PatriciaMap::new();
//! map.insert("foo", 1);
//! map.insert("bar", 2);
//! map.insert("baz", 3);
//! assert_eq!(map.len(), 3);
//!
//! assert_eq!(map.get("foo"), Some(&1));
//! assert_eq!(map.get("bar"), Some(&2));
//! assert_eq!(map.get("baz"), Some(&3));
//! ```
#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
extern crate alloc;

use alloc::borrow::ToOwned;
use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::Ordering;

pub use map::{GenericPatriciaMap, PatriciaMap, StringPatriciaMap};
pub use set::{GenericPatriciaSet, PatriciaSet, StringPatriciaSet};

pub mod map;
pub mod set;

mod node;
mod node_header;
mod tree;

/// This trait represents a bytes type that can be used as the key type of patricia trees.
pub trait Bytes {
    /// Borrowed type of this type.
    type Borrowed: ?Sized + BorrowedBytes + ToOwned<Owned = Self>;
}

impl Bytes for Vec<u8> {
    type Borrowed = [u8];
}

impl Bytes for String {
    type Borrowed = str;
}

/// Borrowed type of [`Bytes`].
pub trait BorrowedBytes {
    /// Returns the byte representation of this instance.
    fn as_bytes(&self) -> &[u8];

    /// Returns `true` if the given bytes is a valid representation of this type, otherwise `false`.
    fn is_valid_bytes(bytes: &[u8]) -> bool;

    /// Converts the given bytes to an instance of this type.
    ///
    /// Caller can assume that `is_valid_bytes(bytes)` is `true`.
    fn from_bytes(bytes: &[u8]) -> &Self;

    /// Returns a suffix of this instance not containing the common prefix with the given bytes.
    fn strip_common_prefix(&self, bytes: &[u8]) -> &Self;

    /// Same as [`strip_common_prefix()`], but also returns the length of the common prefix.
    fn strip_common_prefix_and_len(&self, bytes: &[u8]) -> (&Self, usize) {
        let next = self.strip_common_prefix(bytes);
        let common_prefix_len = self.as_bytes().len() - next.as_bytes().len();
        (next, common_prefix_len)
    }

    fn longest_common_prefix(&self, bytes: &[u8]) -> (usize, Option<Ordering>);

    /// Compares the first item of this instance with the first item represented in the the given bytes.
    fn cmp_first_item(&self, bytes: &[u8]) -> Ordering;

    /// Returns `true` if this instance is empty, otherwise `false`.
    fn is_empty(&self) -> bool {
        self.as_bytes().is_empty()
    }

    /// Returns a suffix of this instance not containing the first `n` bytes.
    fn strip_n_prefix(&self, n: usize) -> &Self;
}

impl BorrowedBytes for [u8] {
    fn as_bytes(&self) -> &[u8] {
        self
    }

    fn is_valid_bytes(_bytes: &[u8]) -> bool {
        true
    }

    fn from_bytes(bytes: &[u8]) -> &Self {
        bytes
    }

    fn strip_common_prefix(&self, bytes: &[u8]) -> &Self {
        let (i, _) = longest_common_prefix(self, bytes);
        &self[i..]
    }

    fn cmp_first_item(&self, bytes: &[u8]) -> Ordering {
        self.first().cmp(&bytes.first())
    }

    fn strip_n_prefix(&self, n: usize) -> &Self {
        &self[n..]
    }

    fn longest_common_prefix(&self, bytes: &[u8]) -> (usize, Option<Ordering>) {
        longest_common_prefix(self, bytes)
    }
}

impl BorrowedBytes for str {
    fn as_bytes(&self) -> &[u8] {
        self.as_bytes()
    }

    fn is_valid_bytes(bytes: &[u8]) -> bool {
        core::str::from_utf8(bytes).is_ok()
    }

    fn from_bytes(bytes: &[u8]) -> &Self {
        core::str::from_utf8(bytes).expect("unreachable")
    }

    // TODO: remove. we should work on bytes only at node level
    fn strip_common_prefix(&self, bytes: &[u8]) -> &Self {
        for (i, c) in self.char_indices() {
            let n = c.len_utf8();
            if self.as_bytes()[i..i + n]
                .iter()
                .ne(bytes[i..].iter().take(n))
            {
                return &self[i..];
            }
        }
        ""
    }

    fn cmp_first_item(&self, bytes: &[u8]) -> Ordering {
        self.chars()
            .next()
            .cmp(&Self::from_bytes(bytes).chars().next())
    }

    fn strip_n_prefix(&self, n: usize) -> &Self {
        &self[n..]
    }

    fn longest_common_prefix(&self, bytes: &[u8]) -> (usize, Option<Ordering>) {
        longest_common_prefix(self.as_bytes(), bytes)
    }
}

#[inline(always)]
pub(crate) fn strip_prefix<'a>(haystack: &'a [u8], prefix: &[u8]) -> Option<&'a [u8]> {
    if !memchr::arch::all::is_prefix(haystack, prefix) {
        None
    } else {
        Some(&haystack[prefix.len()..])
    }
}

/// returns index of where a & b differ, and the ordering of the differing bit
/// otherwise returns None
pub fn longest_common_prefix_by_byte(a: &[u8], b: &[u8]) -> (usize, Option<Ordering>) {
    let min_len = core::cmp::min(a.len(), b.len());
    let i = a.iter().zip(b.iter()).take_while(|(a, b)| a == b).count();
    // return None if we can't index a or b to determine if the next element diff
    let cmp = if a.is_empty() || b.is_empty() || i >= min_len {
        None
    } else {
        Some(a[i].cmp(&b[i]))
    };
    (i, cmp)
}

/// returns index of where a & b differ, and the ordering of the differing bit
/// otherwise returns None
#[inline(always)]
pub fn longest_common_prefix(a: &[u8], b: &[u8]) -> (usize, Option<Ordering>) {
    const CHUNK: usize = (u32::BITS / 8) as usize;
    let min_len = core::cmp::min(a.len(), b.len());

    let mut i = 0;
    // go through 4 bytes at a time
    for (a_chunk, b_chunk) in a.chunks_exact(CHUNK).zip(b.chunks_exact(CHUNK)) {
        let ax = u32::from_ne_bytes(a_chunk.try_into().ok().unwrap());
        let bx = u32::from_ne_bytes(b_chunk.try_into().ok().unwrap());

        if ax != bx {
            // find byte diff
            let diff = i + ((ax ^ bx).trailing_zeros() / 8) as usize;
            return (diff, Some(a[diff].cmp(&b[diff])));
        }
        i += CHUNK;
    }
    // process remaining bytes less than 8 - one at a time
    while i < min_len {
        if a[i] != b[i] {
            return (i, Some(a[i].cmp(&b[i])));
        }
        i += 1;
    }

    (i, None)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_longest_common_prefix() {
        // short common prefix
        assert_eq!(
            longest_common_prefix(b"123456789", b"1234abcdef"),
            (4, Some(Ordering::Less))
        );
        assert_eq!(
            longest_common_prefix_by_byte(b"123456789", b"1234abcdef"),
            (4, Some(Ordering::Less))
        );
        // short common prefix
        assert_eq!(
            longest_common_prefix(b"123456789", b"12345abcdef"),
            (5, Some(Ordering::Less))
        );
        assert_eq!(
            longest_common_prefix_by_byte(b"123456789", b"12345abcdef"),
            (5, Some(Ordering::Less))
        );
        // long common prefix
        assert_eq!(
            longest_common_prefix(
                b"1234444444444444444444444456789",
                b"12344444444444444444444444a"
            ),
            (26, Some(Ordering::Less))
        );
        assert_eq!(
            longest_common_prefix_by_byte(
                b"1234444444444444444444444456789",
                b"12344444444444444444444444a"
            ),
            (26, Some(Ordering::Less))
        );
        // both empty
        assert_eq!(longest_common_prefix(b"", b""), (0, None));
        assert_eq!(longest_common_prefix_by_byte(b"", b""), (0, None));
        // no common prefix -- min_len == 0
        assert_eq!(longest_common_prefix(b"123", b""), (0, None));
        assert_eq!(longest_common_prefix_by_byte(b"123", b""), (0, None));
        // no common prefix but both have bytes
        assert_eq!(
            longest_common_prefix(b"foobar", b"notfoobar"),
            (0, Some(Ordering::Less))
        );
        assert_eq!(
            longest_common_prefix_by_byte(b"foobar", b"notfoobar"),
            (0, Some(Ordering::Less))
        );
        // 8 byte len not prefixed
        assert_eq!(longest_common_prefix(b"000000001", b"00000000"), (8, None));
        assert_eq!(
            longest_common_prefix_by_byte(b"000000001", b"00000000"),
            (8, None)
        );
    }

    #[test]
    fn test_strip_common_prefix() {
        assert_eq!(b"foobar123".strip_common_prefix(b""), b"foobar123");
        assert_eq!(b"foobar123".strip_common_prefix(b"foobar"), b"123");
        assert_eq!(b"".strip_common_prefix(b"foobar"), b"");
        assert_eq!(b"foobar123".strip_common_prefix(b"notfoobar"), b"foobar123");
    }
}
