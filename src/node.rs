//! A node which represents a subtree of a patricia tree.
use crate::{
    BorrowedBytes, Bytes,
    node_header::{NodeHeader, NodePtrAndData, PtrData},
};
use alloc::vec::Vec;
use core::{
    cmp::Ordering,
    marker::PhantomData,
    mem,
    ptr::{self, NonNull},
};

macro_rules! assert_some {
    ($expr:expr) => {
        if let Some(value) = $expr {
            value
        } else {
            panic!("`{}` must be `Some(..)`", stringify!($expr));
        }
    };
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Flags(u8);

impl Flags {
    pub(crate) const CHILD_ALLOCATED: Flags = Flags(0b0000_0001);
    pub(crate) const CHILD_INITIALIZED: Flags = Flags(0b0000_0010);
    pub(crate) const SIBLING_ALLOCATED: Flags = Flags(0b0000_0100);
    pub(crate) const SIBLING_INITIALIZED: Flags = Flags(0b0000_1000);

    #[allow(unused)]
    const VALID_BITS_MASK: u8 = 0b0000_1111; // Mask of all valid flag bits.

    const fn empty() -> Self {
        Flags(0)
    }

    #[allow(unused)]
    pub(crate) const fn from_bits_truncate(bits: u8) -> Self {
        Flags(bits & Self::VALID_BITS_MASK)
    }

    #[allow(unused)]
    pub(crate) const fn bits(self) -> u8 {
        self.0
    }

    pub(crate) const fn contains(self, other: Flags) -> bool {
        (self.0 & other.0) == other.0
    }

    #[allow(dead_code)]
    const fn intersects(self, other: Flags) -> bool {
        (self.0 & other.0) != 0
    }

    pub(crate) fn insert(&mut self, other: Flags) {
        self.0 |= other.0;
    }

    pub(crate) fn set(&mut self, other: Flags, value: bool) {
        if value {
            self.0 |= other.0;
        } else {
            self.0 &= !other.0;
        }
    }
}

impl core::ops::BitOr for Flags {
    type Output = Self;

    fn bitor(self, other: Self) -> Self {
        Flags(self.0 | other.0)
    }
}

const MAX_LABEL_LEN: usize = u8::MAX as usize;

/// A node which represents a subtree of a patricia tree.
///
/// Note that this is a low level building block.
/// Usually it is recommended to use more high level data structures (e.g., `PatriciaTree`).
#[derive(Debug)]
pub struct Node<V> {
    // layout:
    //   - flags: u8
    //   - label_len: u8
    //   - label: [u8; label_len]
    //   - value: Option<V>
    //   - child: Option<Node<V>> -- conditionally allocated
    //   - sibling: Option<Node<V>> -- conditionally allocated
    pub(crate) ptr: ptr::NonNull<NodeHeader>,
    pub(crate) _marker: PhantomData<V>,
}

unsafe impl<V: Send> Send for Node<V> {}
unsafe impl<V: Sync> Sync for Node<V> {}

impl<V> Node<V> {
    /// Makes a new node which represents an empty tree.
    pub fn root() -> Self {
        Node::new(b"", [], None)
    }

    /// Makes a new node.
    /// SAFETY: - label len must not exceed 255
    ///         - children len must not exceed 255
    pub fn new<const N: usize>(label: &[u8], children: [Node<V>; N], value: Option<V>) -> Self {
        // known at compile time
        if N > u8::MAX as usize {
            panic!("children_len {} exceeds the max {}", N, u8::MAX);
        }
        assert!(
            label.len() <= MAX_LABEL_LEN,
            "nodes must have a label len <= 255"
        );
        // let mut flags = Flags::empty();
        // if child.is_some() {
        //     flags.insert(Flags::CHILD_ALLOCATED | Flags::CHILD_INITIALIZED);
        // }
        // if sibling.is_some() {
        //     flags.insert(Flags::SIBLING_ALLOCATED | Flags::SIBLING_INITIALIZED);
        // }

        let header = NodeHeader {
            label_len: label.len() as u8,
            children_len: children.len() as u8,
        };
        let mut ptr = header.ptr_data().allocate();
        unsafe {
            ptr.write_header(header);
            ptr.write_label(label);
            ptr.write_children(children);
            ptr.write_value(value);
            ptr.assume_init()
        }
    }

    /// Returns the label of this node.
    pub fn label(&self) -> &[u8] {
        unsafe { PtrData::<V>::label(self.ptr) }
    }

    #[cfg(feature = "serde")]
    pub(crate) fn label_mut(&mut self) -> &mut [u8] {
        unsafe { PtrData::<V>::label_mut(self.ptr) }
    }

    /// Returns a reference to the header for this node.
    #[inline]
    fn header(&self) -> &NodeHeader {
        unsafe { self.ptr.as_ref() }
    }

    #[inline]
    fn header_mut(&mut self) -> &mut NodeHeader {
        unsafe { self.ptr.as_mut() }
    }
    /// Returns the layout and field offsets for the allocated buffer backing this node.
    #[inline]
    fn ptr_data(&self) -> PtrData<V> {
        self.header().ptr_data()
    }

    /// Returns the reference to the value of this node.
    pub fn value(&self) -> Option<&V> {
        unsafe { (self.ptr_data().value_ptr(self.ptr)).as_ref() }.as_ref()
    }

    /// Returns the mutable reference to the value of this node.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        unsafe { (self.ptr_data().value_ptr(self.ptr)).as_mut() }.as_mut()
    }

    pub fn children(&self) -> &[Node<V>] {
        unsafe { self.ptr_data().children(self.ptr) }
    }
    pub fn children_mut(&mut self) -> &mut [Node<V>] {
        unsafe { self.ptr_data().children_mut(self.ptr) }
    }
    // TODO: consider storing first bytes in node? trade memory for lookup speed
    fn children_first_bytes(&self) -> impl Iterator<Item = Option<u8>> {
        self.children().iter().map(|n| n.label().first().cloned())
    }

    /// Returns mutable references to the node itself with its sibling and child
    pub fn as_mut(&mut self) -> NodeMut<'_, V> {
        let value = unsafe { self.ptr_data().value_ptr(self.ptr).as_mut() }.as_mut();
        let children = unsafe { self.ptr_data().children_mut(self.ptr) };

        NodeMut {
            label: self.label(),
            value,
            children,
        }
    }

    /// Takes the value out of this node.
    pub fn take_value(&mut self) -> Option<V> {
        unsafe {
            let ptr = self.ptr_data().value_ptr(self.ptr);
            ptr.replace(None)
        }
    }

    pub fn take_children(&mut self) -> Option<Vec<Node<V>>> {
        let len = self.children_len();
        if len == 0 {
            return None;
        }
        let mut ret = Vec::with_capacity(len);
        unsafe {
            let ptr = self.ptr_data().children_ptr(self.ptr)?;
            for i in 0..len {
                ret.push(ptr.add(i).read());
            }
            // reallocate parent now that children are gone
            let value = self.take_value();
            let node = Node::new(self.label(), [], value);
            *self = node;
        }
        Some(ret)
    }
    pub fn children_len(&self) -> usize {
        self.header().children_len as usize
    }
    /// adds child at i and shifts elements right
    /// node must have children already and i <= len
    unsafe fn add_child(&mut self, new_child: Node<V>, i: usize) {
        debug_assert!(
            i <= self.children_len() as usize,
            "child index out of bounds: {i} > {}",
            self.children_len()
        );

        let new_header = NodeHeader {
            label_len: self.label_len() as u8,
            children_len: self.children_len() as u8 + 1,
        };
        let old_children_len = self.children_len();
        let new_ptr_data = new_header.ptr_data();
        let old_ptr_data = self.ptr_data();
        let value = self.take_value();

        dbg!(self.ptr_data().layout);
        dbg!(new_header.ptr_data::<V>().layout);

        unsafe {
            let raw_ptr = alloc::alloc::realloc(
                self.ptr.as_ptr().cast(),
                old_ptr_data.layout,
                new_ptr_data.layout.size(),
            )
            .cast();

            let Some(raw_ptr) = NonNull::new(raw_ptr) else {
                alloc::alloc::handle_alloc_error(new_ptr_data.layout);
            };
            let mut new_ptr = NodePtrAndData {
                ptr: raw_ptr,
                ptr_data: new_ptr_data,
            };
            let old_ptr = NodePtrAndData {
                ptr: raw_ptr,
                ptr_data: old_ptr_data,
            };
            let num = old_children_len - i;
            dbg!(num);
            // write data in right to left order since we're growing
            new_ptr.write_value(value);

            // let old_i = old_ptr.children_ptr().map(|p| p.add(i));
            // // shift children from [i..] to [i+1..]
            // if let Some((p, old_i)) = new_ptr
            //     .children_ptr()
            //     .and_then(|p| Some((p.add(i + 1), old_i?)))
            // {
            //     p.copy_from(old_i, num);
            // }
            // assert_some!(new_ptr.children_ptr()).add(i).write(new_child);

            // if let Some(old_i) = old_ptr.children_ptr() {
            //     assert_some!(new_ptr.children_ptr()).copy_from(old_i, i);
            // }

            if num > 0 {
                assert_some!(new_ptr.children_ptr())
                    .add(i)
                    .copy_to(assert_some!(new_ptr.children_ptr()).add(i + 1), num);
            }
            // write child at i
            assert_some!(new_ptr.children_ptr()).add(i).write(new_child);
            // update header value:
            new_ptr.write_header(new_header);
            // label already there from realloc
            // re-assign ptr to avoid Drop
            self.ptr = new_ptr.assume_init().into_ptr_forget();
        }
    }
    /// forget self so Drop is not called and return the ptr
    fn into_ptr_forget(self) -> NonNull<NodeHeader> {
        let ptr = self.ptr;
        mem::forget(self);
        ptr
    }

    /// removes child at i and shifts elements left
    /// node must have children already
    unsafe fn remove_child(&mut self, i: usize) -> Node<V> {
        debug_assert!(
            i < self.children_len() as usize,
            "child index out of bounds: {i} >= {}",
            self.children_len()
        );

        let new_header = NodeHeader {
            label_len: self.label_len() as u8,
            children_len: self.children_len() as u8 - 1,
        };
        let old_children_len = self.children_len();
        let new_ptr_data = new_header.ptr_data::<V>();
        let new_size = new_ptr_data.layout.size();
        let new_layout = new_ptr_data.layout;
        let old_layout = self.ptr_data().layout;
        // TODO: could use ptr::copy since we use realloc
        let value = self.take_value();
        let old_ptr = NodePtrAndData {
            ptr: self.ptr,
            ptr_data: self.ptr_data(),
        };

        unsafe {
            // get child at i
            let removed_child = assert_some!(old_ptr.children_ptr()).add(i).read();
            // child.drop_in_place(); // if we want to drop instead of return

            let mut new_ptr = NodePtrAndData {
                ptr: self.ptr,
                ptr_data: new_ptr_data,
            };
            // write data in left to right order since we're shrinking
            new_ptr.write_header(new_header);
            // shift children from [i+1..] to [i..]
            let num = old_children_len - (i + 1);
            if let Some(child_ptr) = new_ptr.children_ptr() {
                child_ptr.add(i).copy_from(child_ptr.add(i + 1), num);
            }

            let new_ptr =
                alloc::alloc::realloc(self.ptr.as_ptr().cast(), old_layout, new_size).cast();
            let Some(new_ptr) = NonNull::new(new_ptr) else {
                alloc::alloc::handle_alloc_error(new_layout);
            };
            let new_ptr_data = new_header.ptr_data();
            let mut new_ptr = NodePtrAndData {
                ptr: new_ptr,
                ptr_data: new_ptr_data,
            };
            // write value in new shrunken space
            new_ptr.write_value(value);
            // re-assign ptr to avoid drop
            self.ptr = new_ptr.assume_init().into_ptr_forget();
            removed_child
        }
    }

    /// Sets the value of this node.
    pub fn set_value(&mut self, value: V) {
        // self.take_value();
        unsafe {
            let ptr = self.ptr_data().value_ptr(self.ptr);
            let _ = ptr.replace(Some(value));
        }
    }

    // /// Sets the child of this node.
    // pub fn set_child(&mut self, child: Self) {
    //     self.take_child();
    //     if let Some(ptr) = unsafe { self.ptr_data().child_ptr_alloc(self.ptr) } {
    //         self.set_flags(Flags::CHILD_INITIALIZED, true);
    //         unsafe {
    //             ptr.write(child);
    //         }
    //     } else {
    //         let value = self.take_value();
    //         let sibling = self.take_sibling();
    //         // let node = Node::new(self.label(), value, Some(child), sibling);
    //         // *self = node;
    //         todo!();
    //     }
    // }

    // /// Sets the sibling of this node.
    // pub fn set_sibling(&mut self, sibling: Self) {
    //     self.take_sibling();
    //     if let Some(ptr) = unsafe { self.ptr_data().sibling_ptr_alloc(self.ptr) } {
    //         self.set_flags(Flags::SIBLING_INITIALIZED, true);
    //         unsafe {
    //             ptr.write(sibling);
    //         }
    //     } else {
    //         let value = self.take_value();
    //         let child = self.take_child();
    //         // let node = Node::new(self.label(), value, child, Some(sibling));
    //         // *self = node;
    //         todo!();
    //     }
    // }

    /// Gets an iterator which traverses the nodes in this tree, in depth first order.
    // pub fn iter(&self) -> Iter<'_, V> {
    //     Iter {
    //         stack: vec![(0, self)],
    //     }
    // }

    /// Gets a mutable iterator which traverses the nodes in this tree, in depth first order.
    pub fn iter_mut(&mut self) -> IterMut<'_, V> {
        IterMut {
            stack: vec![(0, self)],
        }
    }

    // pub(crate) fn iter_descendant(&self) -> Iter<'_, V> {
    //     Iter {
    //         stack: vec![(0, self)],
    //     }
    // }

    pub(crate) fn iter_descendant_mut(&mut self) -> IterMut<'_, V> {
        IterMut {
            stack: vec![(0, self)],
        }
    }

    pub(crate) fn common_prefixes<'a, 'b, K>(
        &'a self,
        key: &'b K,
    ) -> CommonPrefixesIter<'a, 'b, K, V>
    where
        K: ?Sized + BorrowedBytes,
    {
        CommonPrefixesIter {
            key,
            stack: vec![(0, self)],
        }
    }

    pub(crate) fn common_prefixes_owned<K: Bytes>(
        &self,
        key: K,
    ) -> CommonPrefixesIterOwned<'_, K, V> {
        CommonPrefixesIterOwned {
            key,
            stack: vec![(0, self)],
        }
    }

    // TODO: child methods could use binary search?
    fn child_with_first(&self, byte: u8) -> Option<&Self> {
        let i = self.child_index_with_first(byte)?;
        // SAFETY: we know i is inside the bounds already
        Some(unsafe { self.children().get_unchecked(i) })
    }
    fn child_with_first_mut(&mut self, byte: u8) -> Option<&mut Self> {
        let i = self.child_index_with_first(byte)?;
        Some(unsafe { self.children_mut().get_unchecked_mut(i) })
    }
    fn child_index_with_first(&self, byte: u8) -> Option<usize> {
        self.children_first_bytes()
            .enumerate()
            .find(|(_, b)| b.is_some_and(|b| b == byte))
            .map(|(i, _)| i)
    }

    pub(crate) fn get<K: ?Sized + BorrowedBytes>(&self, key: &K) -> Option<&V> {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            key = crate::strip_prefix(key, cur.label())?;
            match key.first() {
                None => return cur.value(),
                Some(first) => {
                    cur = cur.child_with_first(*first)?;
                }
            }
        }
    }

    pub(crate) fn get_mut<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<&mut V> {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            key = crate::strip_prefix(key, cur.label())?;
            match key.first() {
                None => return cur.value_mut(),
                Some(first) => {
                    cur = cur.child_with_first_mut(*first)?;
                }
            }
        }
    }

    // pub(crate) fn longest_common_prefix_len<K: ?Sized + BorrowedBytes>(
    //     &self,
    //     key: &K,
    //     offset: usize,
    // ) -> usize {
    //     let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
    //     let next_offset = offset + common_prefix_len;
    //     if common_prefix_len == self.label().len() {
    //         if next.is_empty() {
    //             next_offset
    //         } else {
    //             self.child()
    //                 .map(|child| child.longest_common_prefix_len(next, next_offset))
    //                 .unwrap_or(next_offset)
    //         }
    //     } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
    //         self.sibling()
    //             .map(|sibling| sibling.longest_common_prefix_len(next, offset))
    //             .unwrap_or(next_offset)
    //     } else {
    //         next_offset
    //     }
    // }
    // pub(crate) fn get_longest_common_prefix<K: ?Sized + BorrowedBytes>(
    //     &self,
    //     key: &K,
    //     offset: usize,
    // ) -> Option<(usize, &V)> {
    //     let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
    //     if common_prefix_len == self.label().len() {
    //         let offset = offset + common_prefix_len;
    //         if next.is_empty() {
    //             self.value().map(|v| (offset, v))
    //         } else {
    //             self.child()
    //                 .and_then(|child| child.get_longest_common_prefix(next, offset))
    //                 .or_else(|| self.value().map(|v| (offset, v)))
    //         }
    //     } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
    //         self.sibling()
    //             .and_then(|sibling| sibling.get_longest_common_prefix(next, offset))
    //     } else {
    //         None
    //     }
    // }
    // pub(crate) fn get_longest_common_prefix_mut<K: ?Sized + BorrowedBytes>(
    //     &mut self,
    //     key: &K,
    //     offset: usize,
    // ) -> Option<(usize, &mut V)> {
    //     let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
    //     if common_prefix_len == self.label().len() {
    //         let offset = offset + common_prefix_len;
    //         if next.is_empty() {
    //             self.value_mut().map(|v| (offset, v))
    //         } else {
    //             let this = self.as_mut();
    //             this.child
    //                 .and_then(|child| child.get_longest_common_prefix_mut(next, offset))
    //                 .or_else(|| this.value.map(|v| (offset, v)))
    //         }
    //     } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
    //         self.sibling_mut()
    //             .and_then(|sibling| sibling.get_longest_common_prefix_mut(next, offset))
    //     } else {
    //         None
    //     }
    // }

    // pub(crate) fn get_prefix_node<K: ?Sized + BorrowedBytes>(
    //     &self,
    //     key: &K,
    // ) -> Option<(usize, &Self)> {
    //     let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
    //     if next.is_empty() {
    //         Some((common_prefix_len, self))
    //     } else if common_prefix_len == self.label().len() {
    //         self.child().and_then(|child| child.get_prefix_node(next))
    //     } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
    //         self.sibling()
    //             .and_then(|sibling| sibling.get_prefix_node(next))
    //     } else {
    //         None
    //     }
    // }

    // pub(crate) fn get_prefix_node_mut<K: ?Sized + BorrowedBytes>(
    //     &mut self,
    //     key: &K,
    // ) -> Option<(usize, &mut Self)> {
    //     let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
    //     if next.is_empty() {
    //         Some((common_prefix_len, self))
    //     } else if common_prefix_len == self.label().len() {
    //         self.child_mut()
    //             .and_then(|child| child.get_prefix_node_mut(next))
    //     } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
    //         self.sibling_mut()
    //             .and_then(|sibling| sibling.get_prefix_node_mut(next))
    //     } else {
    //         None
    //     }
    // }

    // pub(crate) fn split_by_prefix<K: ?Sized + BorrowedBytes>(
    //     &mut self,
    //     prefix: &K,
    //     level: usize,
    // ) -> Option<Self> {
    //     let (next, common_prefix_len) = prefix.strip_common_prefix_and_len(self.label());
    //     if common_prefix_len == prefix.as_bytes().len() {
    //         let value = self.take_value();
    //         let child = self.take_child();
    //         // let node = Node::new(&self.label()[common_prefix_len..], value, child, None);
    //         todo!();
    //         if let Some(sibling) = self.take_sibling() {
    //             *self = sibling;
    //         }
    //         Some(node)
    //     } else if common_prefix_len == self.label().len() {
    //         self.child_mut()
    //             .and_then(|child| child.split_by_prefix(next, level + 1))
    //             .inspect(|_old| {
    //                 self.try_reclaim_child();
    //                 self.try_merge_with_child(level);
    //             })
    //     } else if common_prefix_len == 0 && prefix.cmp_first_item(self.label()).is_ge() {
    //         self.sibling_mut()
    //             .and_then(|sibling| sibling.split_by_prefix(next, level))
    //             .inspect(|_old| {
    //                 self.try_reclaim_sibling();
    //             })
    //     } else {
    //         None
    //     }
    // }
    // pub(crate) fn remove<K: ?Sized + BorrowedBytes>(&mut self, key: &K, level: usize) -> Option<V> {
    //     let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
    //     if common_prefix_len == self.label().len() {
    //         if next.is_empty() {
    //             self.take_value().inspect(|_old| {
    //                 self.try_merge_with_child(level);
    //             })
    //         } else {
    //             self.child_mut()
    //                 .and_then(|child| child.remove(next, level + 1))
    //                 .inspect(|_old| {
    //                     self.try_reclaim_child();
    //                     self.try_merge_with_child(level);
    //                 })
    //         }
    //     } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
    //         self.sibling_mut()
    //             .and_then(|sibling| sibling.remove(next, level))
    //             .inspect(|_old| {
    //                 self.try_reclaim_sibling();
    //             })
    //     } else {
    //         None
    //     }
    // }

    pub(crate) fn insert<K: ?Sized + BorrowedBytes>(&mut self, key: &K, value: V) -> Option<V> {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            match crate::longest_common_prefix(cur.label(), key) {
                (0, Some(ord)) => {
                    // insert new root
                    // no common prefix, this only happens if we're at the root node
                    let old_root = Node {
                        ptr: cur.ptr,
                        _marker: PhantomData,
                    };
                    let child = Node::new(key, [], Some(value));
                    let children = if ord == Ordering::Greater {
                        [child, old_root]
                    } else {
                        [old_root, child]
                    };
                    let new_root = Node::new(b"", children, None);
                    // swap out current root for new root w/ children
                    cur.ptr = new_root.ptr;
                    mem::forget(new_root);

                    return None;
                }
                (n, Some(_)) => {
                    // new child from common prefix that needs split at n
                    let (_, new_suffix) = unsafe { key.split_at_unchecked(n) };
                    let new_child = Node::new(new_suffix, [], Some(value));
                    unsafe {
                        cur.split_at(n, Some(new_child));
                    }
                    return None;
                }
                (_, None) => {
                    // new child needed but next element doesn't exist
                    match key.len().cmp(&cur.label_len()) {
                        Ordering::Less => {
                            unsafe { cur.split_at(key.len(), None) };
                            cur.set_value(value);
                            return None;
                        }
                        Ordering::Equal => {
                            // key and node are equal, replace data
                            let old_val = cur.take_value();
                            cur.set_value(value);
                            return old_val;
                        }
                        Ordering::Greater => {
                            // prefix match but key is longer, so we need to insert into a child
                            key = unsafe { key.get_unchecked(cur.label_len()..) };
                            let first_byte = key[0];
                            match cur.child_index_with_first(first_byte) {
                                Some(i) => {
                                    // SAFETY: we just checked i is in range
                                    cur = unsafe { cur.children_mut().get_unchecked_mut(i) };
                                    continue;
                                }
                                None => {
                                    // TODO: use binary_search(first_byte).unwrap_err()
                                    // if we switch to storing first bytes
                                    let insert_index = cur
                                        .children_first_bytes()
                                        .enumerate()
                                        .find(|(_, b)| b.is_some_and(|b| b > first_byte))
                                        .map(|(i, _)| i)
                                        .unwrap_or(cur.children_len());

                                    // we now have index of where we can insert
                                    let child = Node::new(key, [], Some(value));
                                    // SAFETY: insert_index must be <= children len
                                    dbg!(&child.label(), insert_index);
                                    unsafe {
                                        cur.add_child(child, insert_index);
                                    }
                                    return None;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // pub(crate) fn flags(&self) -> Flags {
    //     Flags::from_bits_truncate(self.header().flags.bits())
    // }
    // fn set_flags(&mut self, other: Flags, value: bool) {
    //     self.header_mut().flags.set(other, value);
    // }

    fn label_len(&self) -> usize {
        self.header().label_len as usize
    }
    unsafe fn split_at(&mut self, position: usize, new_child: Option<Node<V>>) {
        debug_assert!(
            position < self.label_len(),
            "label offset must be within label bounds"
        );
        let value = self.take_value();

        let child = unsafe {
            let suffix = self.label().get_unchecked(position..);
            let old_children_len = self.children_len();
            let child_hdr = NodeHeader {
                label_len: suffix.len() as u8,
                children_len: old_children_len as u8,
            };
            let ptr_data = child_hdr.ptr_data();
            let mut ptr = ptr_data.allocate();

            // copy data
            ptr.write_header(child_hdr);
            ptr.write_label(suffix);
            if old_children_len > 0 {
                let dst_children = assert_some!(ptr.children_ptr());
                let src_children = assert_some!(self.ptr_data().children_ptr(self.ptr));
                dst_children
                    .copy_from_nonoverlapping(src_children, child_hdr.children_len as usize);
            }
            ptr.write_value(value);
            ptr.assume_init()
        };
        // resize old allocation
        let new_hdr = NodeHeader {
            label_len: position as u8,
            children_len: 1 + new_child.is_some() as u8,
        };

        let new_data = new_hdr.ptr_data::<V>();
        let new_layout = new_data.layout;
        let old_layout = self.ptr_data().layout;

        let mut new_ptr = unsafe {
            let new_ptr =
                alloc::alloc::realloc(self.ptr.as_ptr().cast(), old_layout, new_layout.size())
                    .cast();
            let Some(new_ptr) = NonNull::new(new_ptr) else {
                alloc::alloc::handle_alloc_error(new_layout);
            };
            NodePtrAndData {
                ptr: new_ptr,
                ptr_data: new_data,
            }
        };
        unsafe {
            new_ptr.write_header(new_hdr);
            if let Some(new_child) = new_child {
                let children = {
                    let suffix_first = assert_some!(child.label().first());
                    let new_child_first = assert_some!(new_child.label().first());
                    if new_child_first < suffix_first {
                        [new_child, child]
                    } else {
                        [child, new_child]
                    }
                };

                new_ptr.write_children(children);
            } else {
                new_ptr.write_children([child]);
            }
            new_ptr.write_value(None);
            // re-assign ptr to avoid Drop of old children
            self.ptr = new_ptr.assume_init().into_ptr_forget();
        }
    }

    // pub(crate) fn try_merge_with_child(&mut self, level: usize) {
    //     if level == 0 {
    //         return;
    //     }

    //     if self.value().is_some() || !self.flags().contains(Flags::CHILD_INITIALIZED) {
    //         return;
    //     }

    //     let flags = assert_some!(self.child()).flags();
    //     if !flags.contains(Flags::SIBLING_INITIALIZED)
    //         && (self.label_len() + assert_some!(self.child()).label_len()) <= MAX_LABEL_LEN
    //     {
    //         let mut child = assert_some!(self.take_child());
    //         let sibling = self.take_sibling();
    //         let value = child.take_value();
    //         let grandchild = child.take_child();

    //         let mut label = Vec::with_capacity(self.label_len() + child.label_len());
    //         label.extend(self.label());
    //         label.extend(child.label());
    //         // let node = Self::new(&label, value, grandchild, sibling);
    //         // *self = node;
    //         todo!();
    //     }
    // }
}

impl<V> Drop for Node<V> {
    fn drop(&mut self) {
        self.ptr_data().dealloc(self.ptr);
    }
}

// impl<V: Clone> Clone for Node<V> {
//     fn clone(&self) -> Self {
//         let label = self.label();
//         let value = self.value().cloned();
//         let children = self.children();
//         Node::new(label, value, child, sibling)
//     }
// }

// impl<V> IntoIterator for Node<V> {
//     type Item = (usize, Node<V>);
//     type IntoIter = IntoIter<V>;
//     fn into_iter(self) -> Self::IntoIter {
//         IntoIter {
//             stack: vec![(0, self)],
//         }
//     }
// }

/// An iterator which traverses the nodes in a tree, in depth first order.
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct Iter<'a, V: 'a> {
    stack: Vec<(usize, &'a Node<V>)>,
}
// impl<'a, V: 'a> Iterator for Iter<'a, V> {
//     type Item = (usize, &'a Node<V>);
//     fn next(&mut self) -> Option<Self::Item> {
//         if let Some((level, node)) = self.stack.pop() {
//             if level != 0 {
//                 if let Some(sibling) = node.sibling() {
//                     self.stack.push((level, sibling));
//                 }
//             }
//             if let Some(child) = node.child() {
//                 self.stack.push((level + 1, child));
//             }
//             Some((level, node))
//         } else {
//             None
//         }
//     }
// }

/// A mutable iterator which traverses the nodes in a tree, in depth first order.
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct IterMut<'a, V: 'a> {
    stack: Vec<(usize, &'a mut Node<V>)>,
}

/// A reference to an immediate node (without child or sibling) with its
/// label and a mutable reference to its value, if present.
pub struct NodeMut<'a, V: 'a> {
    label: &'a [u8],
    value: Option<&'a mut V>,
    children: &'a mut [Node<V>],
}
impl<'a, V: 'a> NodeMut<'a, V> {
    /// Returns the label of the node.
    pub fn label(&self) -> &'a [u8] {
        self.label
    }

    /// Converts into a mutable reference to the value.
    pub fn into_value_mut(self) -> Option<&'a mut V> {
        self.value
    }
}

impl<'a, V: 'a> Iterator for IterMut<'a, V> {
    type Item = (usize, NodeMut<'a, V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.stack.pop() {
            let mut node = node.as_mut();
            // if level != 0 {
            //     if let Some(sibling) = node.sibling.take() {
            //         self.stack.push((level, sibling));
            //     }
            // }
            // if let Some(child) = node.child.take() {
            //     self.stack.push((level + 1, child));
            // }
            todo!();
            Some((level, node))
        } else {
            None
        }
    }
}

/// An iterator over entries in that collects all values up to
/// until the key stops matching.
#[derive(Debug)]
pub(crate) struct CommonPrefixesIter<'a, 'b, K: ?Sized, V> {
    key: &'b K,
    stack: Vec<(usize, &'a Node<V>)>,
}

impl<'a, K, V> Iterator for CommonPrefixesIter<'a, '_, K, V>
where
    K: ?Sized + BorrowedBytes,
{
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((offset, node)) = self.stack.pop() {
            let key = self.key.strip_n_prefix(offset);
            let (_next, common_prefix_len) = key.strip_common_prefix_and_len(node.label());
            if common_prefix_len == 0 && key.cmp_first_item(node.label()).is_ge() {
                // if let Some(sibling) = node.sibling() {
                //     self.stack.push((offset, sibling));
                // }
                todo!();
            }

            if common_prefix_len == node.label().len() {
                let prefix_len = offset + common_prefix_len;
                // if let Some(child) = node.child() {
                //     self.stack.push((prefix_len, child));
                // }
                todo!();
                return Some((prefix_len, node));
            }
        }
        None
    }
}

/// An iterator over entries in that collects all values up to
/// until the key stops matching.
#[derive(Debug)]
pub(crate) struct CommonPrefixesIterOwned<'a, K, V> {
    key: K,
    stack: Vec<(usize, &'a Node<V>)>,
}

impl<'a, K, V> Iterator for CommonPrefixesIterOwned<'a, K, V>
where
    K: Bytes + AsRef<K::Borrowed>,
{
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((offset, node)) = self.stack.pop() {
            let key = self.key.as_ref().strip_n_prefix(offset);
            let (_next, common_prefix_len) = key.strip_common_prefix_and_len(node.label());
            if common_prefix_len == 0 && key.cmp_first_item(node.label()).is_ge() {
                // if let Some(sibling) = node.sibling() {
                //     self.stack.push((offset, sibling));
                // }
                todo!();
            }

            if common_prefix_len == node.label().len() {
                let prefix_len = offset + common_prefix_len;
                // if let Some(child) = node.child() {
                //     self.stack.push((prefix_len, child));
                // }
                todo!();
                return Some((prefix_len, node));
            }
        }
        None
    }
}

/// An owning iterator which traverses the nodes in a tree, in depth first order.
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct IntoIter<V> {
    stack: Vec<(usize, Node<V>)>,
}
// impl<V> Iterator for IntoIter<V> {
//     type Item = (usize, Node<V>);
//     fn next(&mut self) -> Option<Self::Item> {
//         if let Some((level, mut node)) = self.stack.pop() {
//             if let Some(sibling) = node.take_sibling() {
//                 self.stack.push((level, sibling));
//             }
//             if let Some(child) = node.take_child() {
//                 self.stack.push((level + 1, child));
//             }
//             Some((level, node))
//         } else {
//             None
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;
    // use crate::{PatriciaSet, StringPatriciaMap};
    use core::str;

    #[test]
    fn root_works() {
        let node = Node::<()>::root();
        assert!(node.label().is_empty());
        assert!(node.value().is_none());
        // assert!(node.child().is_none());
        // assert!(node.sibling().is_none());
        assert!(node.children().is_empty());
    }

    #[test]
    fn new_works() {
        let node0 = Node::new("foo".as_ref(), [], Some(3));
        let node1 = Node::new("bar".as_ref(), [node0], None);
        assert_eq!(node1.label(), b"bar");
        assert_eq!(node1.value(), None);
        assert_eq!(
            node1
                .children()
                .iter()
                .map(|n| n.label())
                .collect::<Vec<_>>(),
            vec![b"foo"]
        );

        // assert_eq!(node0.label(), b"foo");
        // assert_eq!(node0.value(), Some(&3));
        // assert_eq!(
        //     node0
        //         .children()
        //         .iter()
        //         .map(|n| n.label())
        //         .collect::<Vec<_>>(),
        //     vec![]
        // );
    }

    #[test]
    fn test_children_first_bytes() {
        // no children
        let root = Node::<()>::new(b"", [], None);
        assert_eq!(root.children_first_bytes().count(), 0);

        // with children, including one with an empty label
        let child1 = Node::<()>::new(b"apple", [], None);
        let child2 = Node::<()>::new(b"banana", [], None);
        let child3 = Node::<()>::new(b"", [], None); // empty label
        let child4 = Node::<()>::new(b"cherry", [], None);
        let parent = Node::new(b"parent", [child1, child2, child3, child4], None);

        let mut first_bytes = parent.children_first_bytes();
        assert_eq!(first_bytes.next(), Some(Some(b'a')));
        assert_eq!(first_bytes.next(), Some(Some(b'b')));
        assert_eq!(first_bytes.next(), Some(None));
        assert_eq!(first_bytes.next(), Some(Some(b'c')));
        assert_eq!(first_bytes.next(), None);
    }

    #[test]
    fn test_add_child() {
        let child1 = Node::new(b"a", [], None);
        let mut parent = Node::new(b"parent", [child1], Some(100));

        // Add at the end
        let child2 = Node::new(b"c", [], None);
        unsafe { parent.add_child(child2, 1) };
        assert_eq!(parent.children_len(), 2);
        assert_eq!(parent.children()[0].label(), b"a");
        assert_eq!(parent.children()[1].label(), b"c");
        assert_eq!(parent.value(), Some(&100));

        // Add in the middle
        let child3 = Node::new(b"b", [], None);
        unsafe { parent.add_child(child3, 1) };
        assert_eq!(parent.children_len(), 3);
        assert_eq!(parent.children()[0].label(), b"a");
        assert_eq!(parent.children()[1].label(), b"b");
        assert_eq!(parent.children()[2].label(), b"c");

        // Add at the beginning
        let child4 = Node::new(b"_", [], None);
        unsafe { parent.add_child(child4, 0) };
        assert_eq!(parent.children_len(), 4);
        assert_eq!(parent.children()[0].label(), b"_");
        assert_eq!(parent.children()[1].label(), b"a");
        assert_eq!(parent.children()[2].label(), b"b");
        assert_eq!(parent.children()[3].label(), b"c");
        assert_eq!(parent.label(), b"parent");
        assert_eq!(parent.value(), Some(&100));
    }

    #[test]
    fn test_remove_child() {
        let child1 = Node::new(b"a", [], None);
        let child2 = Node::new(b"b", [], None);
        let child3 = Node::new(b"c", [], None);
        let child4 = Node::new(b"d", [], None);
        let mut parent = Node::new(b"parent", [child1, child2, child3, child4], Some(100));

        // Remove from the middle
        let removed = unsafe { parent.remove_child(1) };
        assert_eq!(removed.label(), b"b");
        assert_eq!(parent.children_len(), 3);
        assert_eq!(parent.children()[0].label(), b"a");
        assert_eq!(parent.children()[1].label(), b"c");
        assert_eq!(parent.children()[2].label(), b"d");
        assert_eq!(parent.value(), Some(&100));

        // Remove from the end
        let removed = unsafe { parent.remove_child(2) };
        assert_eq!(removed.label(), b"d");
        assert_eq!(parent.children_len(), 2);
        assert_eq!(parent.children()[0].label(), b"a");
        assert_eq!(parent.children()[1].label(), b"c");

        // Remove from the beginning
        let removed = unsafe { parent.remove_child(0) };
        assert_eq!(removed.label(), b"a");
        assert_eq!(parent.children_len(), 1);
        assert_eq!(parent.children()[0].label(), b"c");

        // Remove the last child
        let removed = unsafe { parent.remove_child(0) };
        assert_eq!(removed.label(), b"c");
        assert_eq!(parent.children_len(), 0);
        assert!(parent.children().is_empty());
        assert_eq!(parent.label(), b"parent");
        assert_eq!(parent.value(), Some(&100));
    }

    #[test]
    fn test_get_and_get_mut() {
        let mut root: Node<u32> = Node::new(b"", [], Some(2));
        root.insert("test", 1);
        // root.insert("team", 2);
        // root.insert("toast", 3);

        // // Test get
        // assert_eq!(root.get("test"), Some(&1));
        // assert_eq!(root.get("team"), Some(&2));
        // assert_eq!(root.get("toast"), Some(&3));
        // assert_eq!(root.get("te"), None); // prefix, no value
        // assert_eq!(root.get("testing"), None); // non-matching
        // assert_eq!(root.get(""), root.value()); // root value

        // // Test get_mut
        // let val = root.get_mut("test");
        // assert_eq!(*val.as_deref().unwrap(), 1);
        // *val.unwrap() = 10;
        // assert_eq!(root.get("test"), Some(&10));

        // // Test get_mut on non-existent key
        // assert_eq!(root.get_mut("nonexistent"), None);
    }

    #[test]
    fn test_insert() {
        let mut root = Node::root();

        // Insert test key
        assert_eq!(root.insert("test", 1), None);
        assert_eq!(root.get("test"), Some(&1));
        assert_eq!(root.label(), b"");
        assert_eq!(root.children_len(), 1);
        assert_eq!(root.children()[0].label(), b"test");

        // Insert key with common prefix -> split
        assert_eq!(root.insert("team", 2), None);
        assert_eq!(root.get("test"), Some(&1));
        assert_eq!(root.get("team"), Some(&2));
        assert_eq!(root.children_len(), 1);
        assert_eq!(root.children()[0].label(), b"te"); // parent splits
        let te_node = &root.children()[0];
        assert_eq!(te_node.children_len(), 2);
        assert_eq!(te_node.children()[0].label(), b"am"); // "team" -> "am"
        assert_eq!(te_node.children()[1].label(), b"st"); // "test" -> "st"

        // 3. Insert key that is a prefix of an existing key -> add value
        assert_eq!(root.insert("te", 3), None);
        assert_eq!(root.get("te"), Some(&3));
        let te_node = &root.children()[0];
        assert_eq!(te_node.value(), Some(&3));

        // 4. Insert key that extends an existing key -> new child
        assert_eq!(root.insert("testing", 4), None);
        assert_eq!(root.get("testing"), Some(&4));
        let te_node = &root.children()[0];
        let st_node = &te_node.children()[1];
        assert_eq!(st_node.children_len(), 1);
        assert_eq!(st_node.children()[0].label(), b"ing");

        // 5. Replace existing key
        assert_eq!(root.insert("test", 10), Some(1));
        assert_eq!(root.get("test"), Some(&10));

        // 6. Insert key with no common prefix to existing children
        assert_eq!(root.insert("apple", 5), None);
        assert_eq!(root.get("apple"), Some(&5));
        assert_eq!(root.children_len(), 2); // root now has 'apple' and 'te'
        assert_eq!(root.children()[0].label(), b"apple");
        assert_eq!(root.children()[1].label(), b"te");
    }
    // #[test]
    // fn new_methods() {
    //     let node0 = Node::new("foo".as_ref(), Some(3), None, None);
    //     assert_eq!(node0.label(), b"foo");
    //     assert_eq!(node0.value(), Some(&3));
    //     assert_eq!(node0.child().map(|n| n.label()), None);
    //     assert_eq!(node0.sibling().map(|n| n.label()), None);

    //     let mut node1 = Node::new("bar".as_ref(), None, None, Some(node0));
    //     assert_eq!(node1.label(), b"bar");
    //     assert_eq!(node1.value(), None);
    //     assert_eq!(node1.child().map(|n| n.label()), None);
    //     assert_eq!(node1.sibling().map(|n| n.label()), Some(&b"foo"[..]));
    //     // take sibling
    //     let node0 = node1.take_sibling().unwrap();
    //     assert_eq!(node0.label(), b"foo");
    //     assert_eq!(node0.value(), Some(&3));

    //     assert_eq!(node1.sibling().map(|n| n.label()), None);

    //     // we took sibling out of 0 so should be no cycle
    //     let node2 = Node::new("com".as_ref(), Some(1), Some(node1), Some(node0));
    //     assert_eq!(node2.label(), b"com");
    //     assert_eq!(node2.value(), Some(&1));
    //     assert_eq!(node2.child().map(|n| n.label()), Some(&b"bar"[..]));
    //     assert_eq!(node2.sibling().map(|n| n.label()), Some(&b"foo"[..]));
    // }

    // #[test]
    // fn iter_works() {
    //     let mut set = PatriciaSet::new();
    //     set.insert("foo");
    //     set.insert("bar");
    //     set.insert("baz");

    //     let root = set.into_node();
    //     let nodes = root
    //         .iter()
    //         .map(|(level, node)| (level, node.label()))
    //         .collect::<Vec<_>>();
    //     assert_eq!(
    //         nodes,
    //         [
    //             (0, "".as_ref()),
    //             (1, "ba".as_ref()),
    //             (2, "r".as_ref()),
    //             (2, "z".as_ref()),
    //             (1, "foo".as_ref())
    //         ]
    //     );
    // }

    // #[test]
    // fn iter_mut_works() {
    //     let mut set = PatriciaSet::new();
    //     set.insert("foo");
    //     set.insert("bar");
    //     set.insert("baz");

    //     let mut root = set.into_node();
    //     let nodes = root
    //         .iter_mut()
    //         .map(|(level, node)| (level, node.label()))
    //         .collect::<Vec<_>>();
    //     assert_eq!(
    //         nodes,
    //         [
    //             (0, "".as_ref()),
    //             (1, "ba".as_ref()),
    //             (2, "r".as_ref()),
    //             (2, "z".as_ref()),
    //             (1, "foo".as_ref())
    //         ]
    //     );
    // }

    // #[test]
    // fn long_label_works() {
    //     let node = Node::new(&[b'a'; 256][..], Some(10), None, None);
    //     assert_eq!(node.label(), &[b'a'; 255][..]);
    //     assert_eq!(node.value(), None);
    //     assert!(node.child().is_some());

    //     let child = node.child().unwrap();
    //     assert_eq!(child.label(), b"a");
    //     assert_eq!(child.value(), Some(&10));
    // }

    // #[test]
    // fn reclaim_works() {
    //     let mut set = ["123", "123456", "123abc", "123def"]
    //         .iter()
    //         .collect::<PatriciaSet>();
    //     assert_eq!(
    //         set_to_labels(&set),
    //         [(0, ""), (1, "123"), (2, "456"), (2, "abc"), (2, "def")]
    //     );

    //     set.remove("123def");
    //     assert_eq!(
    //         set_to_labels(&set),
    //         [(0, ""), (1, "123"), (2, "456"), (2, "abc")]
    //     );

    //     set.remove("123456");
    //     assert_eq!(set_to_labels(&set), [(0, ""), (1, "123"), (2, "abc")]);

    //     set.remove("123");
    //     assert_eq!(set_to_labels(&set), [(0, ""), (1, "123abc")]);
    // }

    // #[test]
    // fn get_longest_common_prefix_works() {
    //     let set = ["123", "123456", "1234_67", "123abc", "123def"]
    //         .iter()
    //         .collect::<PatriciaSet>();

    //     let lcp = |key| set.get_longest_common_prefix(key);
    //     assert_eq!(lcp(""), None);
    //     assert_eq!(lcp("12"), None);
    //     assert_eq!(lcp("123"), Some("123".as_bytes()));
    //     assert_eq!(lcp("1234"), Some("123".as_bytes()));
    //     assert_eq!(lcp("123456"), Some("123456".as_bytes()));
    //     assert_eq!(lcp("1234_6"), Some("123".as_bytes()));
    //     assert_eq!(lcp("123456789"), Some("123456".as_bytes()));
    // }

    // #[test]
    // fn get_longest_common_prefix_mut_works() {
    //     let mut map = [
    //         ("123", 1),
    //         ("123456", 2),
    //         ("1234_67", 3),
    //         ("123abc", 4),
    //         ("123def", 5),
    //     ]
    //     .iter()
    //     .cloned()
    //     .map(|(k, v)| (String::from(k), v))
    //     .collect::<StringPatriciaMap<usize>>();

    //     assert_eq!(map.get_longest_common_prefix_mut(""), None);
    //     assert_eq!(map.get_longest_common_prefix_mut("12"), None);
    //     assert_eq!(
    //         map.get_longest_common_prefix_mut("123"),
    //         Some(("123", &mut 1))
    //     );
    //     *map.get_longest_common_prefix_mut("123").unwrap().1 = 10;
    //     assert_eq!(
    //         map.get_longest_common_prefix_mut("1234"),
    //         Some(("123", &mut 10))
    //     );
    //     assert_eq!(
    //         map.get_longest_common_prefix_mut("123456"),
    //         Some(("123456", &mut 2))
    //     );
    //     *map.get_longest_common_prefix_mut("1234567").unwrap().1 = 20;
    //     assert_eq!(
    //         map.get_longest_common_prefix_mut("1234_6"),
    //         Some(("123", &mut 10))
    //     );
    //     assert_eq!(
    //         map.get_longest_common_prefix_mut("123456789"),
    //         Some(("123456", &mut 20))
    //     );
    // }

    // fn set_to_labels(set: &PatriciaSet) -> Vec<(usize, &str)> {
    //     set.as_node()
    //         .iter()
    //         .map(|(level, n)| (level, str::from_utf8(n.label()).unwrap()))
    //         .collect()
    // }
}
