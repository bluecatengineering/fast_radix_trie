#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![cfg_attr(not(any(feature = "std", test)), no_std)]

#[macro_use]
extern crate alloc;

use alloc::{borrow::ToOwned, string::String, vec::Vec};
use core::cmp::Ordering;

pub use map::{GenericRadixMap, RadixMap, StringRadixMap};
pub use set::{GenericRadixSet, RadixSet, StringRadixSet};

pub mod entry;
pub mod map;
pub mod set;

mod node_common;
mod tree;

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
}

impl<const N: usize> BorrowedBytes for [u8; N] {
    fn as_bytes(&self) -> &[u8] {
        self
    }

    fn is_valid_bytes(_bytes: &[u8]) -> bool {
        true
    }

    fn from_bytes(bytes: &[u8]) -> &Self {
        bytes.try_into().unwrap()
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
}

/// strip the prefix from the haystack
#[inline(always)]
pub fn strip_prefix<'a>(haystack: &'a [u8], prefix: &[u8]) -> Option<&'a [u8]> {
    if memchr::arch::all::is_prefix(haystack, prefix) {
        // Safety:
        // - `is_prefix` ensures that `prefix.len() <= haystack.len()`
        // - Therefore, slicing `haystack` from `prefix.len()` is guaranteed to be in bounds
        unsafe { Some(haystack.get_unchecked(prefix.len()..)) }
    } else {
        None
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
        // Safety:
        // - `i` is the count of matching elements from zip, so i <= min_len
        // - The condition `i >= min_len` is false, so i < min_len
        // - min_len <= a.len() and min_len <= b.len()
        // - Therefore i < a.len() and i < b.len()
        // - `get_unchecked(i)` is safe for both a and b
        unsafe { Some(a.get_unchecked(i).cmp(b.get_unchecked(i))) }
    };
    (i, cmp)
}

macro_rules! fn_lcp {
    ($ty:ty, $name:ident) => {
        /// returns longest common prefix with index of where a & b differ, and the ordering of the differing bit
        /// otherwise returns None
        #[inline(always)]
        pub fn $name(a: &[u8], b: &[u8]) -> (usize, Option<Ordering>) {
            const CHUNK_LEN: usize = (<$ty>::BITS / 8) as usize;
            let min_len = core::cmp::min(a.len(), b.len());

            let mut i = 0;
            // go through CHUNK_LEN bytes at a time
            for (a_chunk, b_chunk) in a.chunks_exact(CHUNK_LEN).zip(b.chunks_exact(CHUNK_LEN)) {
                let a_num = <$ty>::from_ne_bytes(a_chunk.try_into().ok().unwrap());
                let b_num = <$ty>::from_ne_bytes(b_chunk.try_into().ok().unwrap());

                if a_num != b_num {
                    // find byte diff
                    let diff_idx = i + ((a_num ^ b_num).trailing_zeros() / 8) as usize;
                    return (diff_idx, Some(a[diff_idx].cmp(&b[diff_idx])));
                }
                i += CHUNK_LEN;
            }
            // process remaining bytes less than CHUNK_LEN - one at a time
            while i < min_len {
                // Safety:
                // - Loop condition ensures i < min_len
                // - min_len = min(a.len(), b.len())
                // - Therefore i < a.len() and i < b.len()
                // - `get_unchecked(i)` is safe for both a and b
                let a_byte = unsafe { a.get_unchecked(i) };
                let b_byte = unsafe { b.get_unchecked(i) };
                if a_byte != b_byte {
                    return (i, Some(a_byte.cmp(&b_byte)));
                }
                i += 1;
            }

            (i, None)
        }
    };
}

fn_lcp!(u32, lcp_by4);
fn_lcp!(u32, longest_common_prefix);
fn_lcp!(u64, lcp_by8);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_longest_common_prefix() {
        // short common prefix
        assert_eq!(
            lcp_by4(b"123456789", b"1234abcdef"),
            (4, Some(Ordering::Less))
        );
        assert_eq!(
            lcp_by4(b"123456789", b"1234abcdef"),
            (4, Some(Ordering::Less))
        );
        // short common prefix
        assert_eq!(
            lcp_by4(b"123456789", b"12345abcdef"),
            (5, Some(Ordering::Less))
        );
        assert_eq!(
            lcp_by4(b"123456789", b"12345abcdef"),
            (5, Some(Ordering::Less))
        );
        // long common prefix
        assert_eq!(
            lcp_by4(
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
        assert_eq!(lcp_by4(b"", b""), (0, None));
        assert_eq!(longest_common_prefix_by_byte(b"", b""), (0, None));
        // no common prefix -- min_len == 0
        assert_eq!(lcp_by4(b"123", b""), (0, None));
        assert_eq!(longest_common_prefix_by_byte(b"123", b""), (0, None));
        // no common prefix but both have bytes
        assert_eq!(lcp_by4(b"foobar", b"notfoobar"), (0, Some(Ordering::Less)));
        assert_eq!(
            longest_common_prefix_by_byte(b"foobar", b"notfoobar"),
            (0, Some(Ordering::Less))
        );
        // 8 byte len not prefixed
        assert_eq!(lcp_by4(b"000000001", b"00000000"), (8, None));
        assert_eq!(
            longest_common_prefix_by_byte(b"000000001", b"00000000"),
            (8, None)
        );
        // both are equal
        assert_eq!(lcp_by4(b"000000001", b"000000001"), (9, None));
    }
}
