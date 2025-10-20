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
//! use fast_radix_tree::PatriciaMap;
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

use alloc::{borrow::ToOwned, string::String, vec::Vec};
use core::cmp::Ordering;

// pub use map::{GenericPatriciaMap, PatriciaMap, StringPatriciaMap};
// pub use set::{GenericPatriciaSet, PatriciaSet, StringPatriciaSet};

// pub mod map;
// pub mod set;

// mod tree;
mod node_common;

#[cfg(feature = "realloc")]
pub mod node;
#[cfg(feature = "realloc")]
mod node_header;
#[cfg(feature = "realloc")]
pub(crate) use node_header::*;

#[cfg(not(feature = "realloc"))]
mod node_alloc;
#[cfg(not(feature = "realloc"))]
pub use node_alloc::node;

#[cfg(not(feature = "realloc"))]
pub(crate) use node_alloc::node_header::*;

pub use node::Node;

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

    /// returns the index of the longest common prefix and the ordering of the next character
    /// if it exists
    fn longest_common_prefix(&self, bytes: &[u8]) -> (usize, Option<Ordering>);

    /// Returns `true` if this instance is empty, otherwise `false`.
    fn is_empty(&self) -> bool {
        self.as_bytes().is_empty()
    }
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

    fn longest_common_prefix(&self, bytes: &[u8]) -> (usize, Option<Ordering>) {
        crate::longest_common_prefix(self, bytes)
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

    fn longest_common_prefix(&self, bytes: &[u8]) -> (usize, Option<Ordering>) {
        longest_common_prefix(self.as_bytes(), bytes)
    }
}

/// uses memchr to strip the prefix from the haystack if it is a valid prefix
#[inline(always)]
pub fn strip_prefix<'a>(haystack: &'a [u8], prefix: &[u8]) -> Option<&'a [u8]> {
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
        // both are equal
        assert_eq!(longest_common_prefix(b"000000001", b"000000001"), (9, None));
    }
}
