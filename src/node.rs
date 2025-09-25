//! A node which represents a subtree of a patricia tree.
use crate::{
    BorrowedBytes, Bytes,
    node_header::{NodeHeader, PtrData},
};
use alloc::vec::Vec;
use core::{marker::PhantomData, mem};

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

    const VALID_BITS_MASK: u8 = 0b0000_1111; // Mask of all valid flag bits.

    const fn empty() -> Self {
        Flags(0)
    }

    pub(crate) const fn from_bits_truncate(bits: u8) -> Self {
        Flags(bits & Self::VALID_BITS_MASK)
    }

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

    fn insert(&mut self, other: Flags) {
        self.0 |= other.0;
    }

    fn set(&mut self, other: Flags, value: bool) {
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

const MAX_LABEL_LEN: usize = 255;

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
    //   - child: Option<Node<V>>
    //   - sibling: Option<Node<V>>
    pub(crate) ptr: std::ptr::NonNull<NodeHeader>,
    pub(crate) _marker: PhantomData<V>,
}

impl<V> Node<V> {
    /// Makes a new node which represents an empty tree.
    pub fn root() -> Self {
        Node::new(b"", None, None, None)
    }

    /// Makes a new node.
    pub fn new(
        mut label: &[u8],
        mut value: Option<V>,
        mut child: Option<Self>,
        sibling: Option<Self>,
    ) -> Self {
        if label.len() > MAX_LABEL_LEN {
            child = Some(Node::new(&label[MAX_LABEL_LEN..], value, child, None));
            label = &label[..MAX_LABEL_LEN];
            value = None;
        }

        let mut flags = Flags::empty();
        if child.is_some() {
            flags.insert(Flags::CHILD_ALLOCATED | Flags::CHILD_INITIALIZED);
        }
        if sibling.is_some() {
            flags.insert(Flags::SIBLING_ALLOCATED | Flags::SIBLING_INITIALIZED);
        }

        let header = NodeHeader {
            flags,
            label_len: label.len() as u8,
        };
        let mut ptr = header.ptr_data().allocate();
        unsafe {
            ptr.write_header(header);

            ptr.write_label(label);
            ptr.write_value(value);
            if let Some(child) = child {
                ptr.write_child(child);
            }
            if let Some(sibling) = sibling {
                ptr.write_sibling(sibling);
            }
            ptr.assume_init()
        }
    }

    #[cfg(feature = "serde")]
    pub(crate) fn new_for_decoding(flags: Flags, label_len: u8) -> Self {
        let mut flags = Flags::from_bits_truncate(flags.bits());
        // If the decoded flags say a child/sibling was initialized,
        // we must set the ALLOCATED flag as well for the layout to be correct
        if flags.contains(Flags::CHILD_INITIALIZED) {
            flags.insert(Flags::CHILD_ALLOCATED);
        }
        if flags.contains(Flags::SIBLING_INITIALIZED) {
            flags.insert(Flags::SIBLING_ALLOCATED);
        }

        let header = NodeHeader { flags, label_len };
        let mut ptr = header.ptr_data().allocate();

        unsafe {
            ptr.write_header(header);
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

    /// Returns the reference to the child of this node.
    pub fn child(&self) -> Option<&Self> {
        if let Some(child) = unsafe { self.ptr_data().child_ptr_init(self.ptr) } {
            return Some(unsafe { child.as_ref() });
        }
        None
    }

    /// Returns the mutable reference to the child of this node.
    pub fn child_mut(&mut self) -> Option<&mut Self> {
        if let Some(mut child) = unsafe { self.ptr_data().child_ptr_init(self.ptr) } {
            return Some(unsafe { child.as_mut() });
        }
        None
    }

    /// Returns the reference to the sibling of this node.
    pub fn sibling(&self) -> Option<&Self> {
        if let Some(sibling) = unsafe { self.ptr_data().sibling_ptr_init(self.ptr) } {
            return Some(unsafe { sibling.as_ref() });
        }
        None
    }

    /// Returns the mutable reference to the sibling of this node.
    pub fn sibling_mut(&mut self) -> Option<&mut Self> {
        if let Some(mut sibling) = unsafe { self.ptr_data().sibling_ptr_init(self.ptr) } {
            return Some(unsafe { sibling.as_mut() });
        }
        None
    }

    /// Returns mutable references to the node itself with its sibling and child
    pub fn as_mut(&mut self) -> NodeMut<'_, V> {
        let child_result =
            if let Some(mut child) = unsafe { self.ptr_data().child_ptr_init(self.ptr) } {
                Some(unsafe { child.as_mut() })
            } else {
                None
            };
        let sibling_result =
            if let Some(mut sibling) = unsafe { self.ptr_data().sibling_ptr_init(self.ptr) } {
                Some(unsafe { sibling.as_mut() })
            } else {
                None
            };

        let value_result = unsafe { self.ptr_data().value_ptr(self.ptr).as_mut() }.as_mut();

        NodeMut {
            label: self.label(),
            sibling: sibling_result,
            child: child_result,
            value: value_result,
        }
    }

    /// Takes the value out of this node.
    pub fn take_value(&mut self) -> Option<V> {
        unsafe {
            let mut ptr = self.ptr_data().value_ptr(self.ptr);
            ptr.as_mut().take()
            // ptr.replace(None)
        }
    }

    /// Takes the child out of this node.
    pub fn take_child(&mut self) -> Option<Self> {
        if let Some(child) = unsafe { self.ptr_data().child_ptr_init(self.ptr) } {
            self.set_flags(Flags::CHILD_INITIALIZED, false);
            return Some(unsafe { child.read() });
        }
        None
    }

    /// Takes the sibling out of this node.
    pub fn take_sibling(&mut self) -> Option<Self> {
        if let Some(sibling) = unsafe { self.ptr_data().sibling_ptr_init(self.ptr) } {
            self.set_flags(Flags::SIBLING_INITIALIZED, false);
            return Some(unsafe { sibling.read() });
        }
        None
    }

    /// Sets the value of this node.
    pub fn set_value(&mut self, value: V) {
        // self.take_value();
        unsafe {
            let ptr = self.ptr_data().value_ptr(self.ptr);
            let _ = ptr.replace(Some(value));
        }
    }

    /// Sets the child of this node.
    pub fn set_child(&mut self, child: Self) {
        self.take_child();
        unsafe {
            if let Some(ptr) = self.ptr_data().child_ptr_alloc(self.ptr) {
                self.set_flags(Flags::CHILD_INITIALIZED, true);
                ptr.write(child);
            } else {
                let value = self.take_value();
                let sibling = self.take_sibling();
                let node = Node::new(self.label(), value, Some(child), sibling);
                *self = node;
            }
        }
    }

    /// Sets the sibling of this node.
    pub fn set_sibling(&mut self, sibling: Self) {
        self.take_sibling();
        unsafe {
            if let Some(ptr) = self.ptr_data().sibling_ptr_alloc(self.ptr) {
                self.set_flags(Flags::SIBLING_INITIALIZED, true);
                ptr.write(sibling);
            } else {
                let value = self.take_value();
                let child = self.take_child();
                let node = Node::new(self.label(), value, child, Some(sibling));
                *self = node;
            }
        }
    }

    /// Gets an iterator which traverses the nodes in this tree, in depth first order.
    pub fn iter(&self) -> Iter<'_, V> {
        Iter {
            stack: vec![(0, self)],
        }
    }

    /// Gets a mutable iterator which traverses the nodes in this tree, in depth first order.
    pub fn iter_mut(&mut self) -> IterMut<'_, V> {
        IterMut {
            stack: vec![(0, self)],
        }
    }

    pub(crate) fn iter_descendant(&self) -> Iter<'_, V> {
        Iter {
            stack: vec![(0, self)],
        }
    }

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

    pub(crate) fn get<K: ?Sized + BorrowedBytes>(&self, key: &K) -> Option<&V> {
        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        if common_prefix_len == self.label().len() {
            if next.is_empty() {
                self.value()
            } else {
                self.child().and_then(|child| child.get(next))
            }
        } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
            self.sibling().and_then(|sibling| sibling.get(next))
        } else {
            None
        }
    }

    pub(crate) fn get_mut<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<&mut V> {
        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        if common_prefix_len == self.label().len() {
            if next.is_empty() {
                self.value_mut()
            } else {
                self.child_mut().and_then(|child| child.get_mut(next))
            }
        } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
            self.sibling_mut().and_then(|sibling| sibling.get_mut(next))
        } else {
            None
        }
    }
    pub(crate) fn longest_common_prefix_len<K: ?Sized + BorrowedBytes>(
        &self,
        key: &K,
        offset: usize,
    ) -> usize {
        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        let next_offset = offset + common_prefix_len;
        if common_prefix_len == self.label().len() {
            if next.is_empty() {
                next_offset
            } else {
                self.child()
                    .map(|child| child.longest_common_prefix_len(next, next_offset))
                    .unwrap_or(next_offset)
            }
        } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
            self.sibling()
                .map(|sibling| sibling.longest_common_prefix_len(next, offset))
                .unwrap_or(next_offset)
        } else {
            next_offset
        }
    }
    pub(crate) fn get_longest_common_prefix<K: ?Sized + BorrowedBytes>(
        &self,
        key: &K,
        offset: usize,
    ) -> Option<(usize, &V)> {
        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        if common_prefix_len == self.label().len() {
            let offset = offset + common_prefix_len;
            if next.is_empty() {
                self.value().map(|v| (offset, v))
            } else {
                self.child()
                    .and_then(|child| child.get_longest_common_prefix(next, offset))
                    .or_else(|| self.value().map(|v| (offset, v)))
            }
        } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
            self.sibling()
                .and_then(|sibling| sibling.get_longest_common_prefix(next, offset))
        } else {
            None
        }
    }
    pub(crate) fn get_longest_common_prefix_mut<K: ?Sized + BorrowedBytes>(
        &mut self,
        key: &K,
        offset: usize,
    ) -> Option<(usize, &mut V)> {
        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        if common_prefix_len == self.label().len() {
            let offset = offset + common_prefix_len;
            if next.is_empty() {
                self.value_mut().map(|v| (offset, v))
            } else {
                let this = self.as_mut();
                this.child
                    .and_then(|child| child.get_longest_common_prefix_mut(next, offset))
                    .or_else(|| this.value.map(|v| (offset, v)))
            }
        } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
            self.sibling_mut()
                .and_then(|sibling| sibling.get_longest_common_prefix_mut(next, offset))
        } else {
            None
        }
    }

    pub(crate) fn get_prefix_node<K: ?Sized + BorrowedBytes>(
        &self,
        key: &K,
    ) -> Option<(usize, &Self)> {
        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        if next.is_empty() {
            Some((common_prefix_len, self))
        } else if common_prefix_len == self.label().len() {
            self.child().and_then(|child| child.get_prefix_node(next))
        } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
            self.sibling()
                .and_then(|sibling| sibling.get_prefix_node(next))
        } else {
            None
        }
    }

    pub(crate) fn get_prefix_node_mut<K: ?Sized + BorrowedBytes>(
        &mut self,
        key: &K,
    ) -> Option<(usize, &mut Self)> {
        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        if next.is_empty() {
            Some((common_prefix_len, self))
        } else if common_prefix_len == self.label().len() {
            self.child_mut()
                .and_then(|child| child.get_prefix_node_mut(next))
        } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
            self.sibling_mut()
                .and_then(|sibling| sibling.get_prefix_node_mut(next))
        } else {
            None
        }
    }

    pub(crate) fn split_by_prefix<K: ?Sized + BorrowedBytes>(
        &mut self,
        prefix: &K,
        level: usize,
    ) -> Option<Self> {
        let (next, common_prefix_len) = prefix.strip_common_prefix_and_len(self.label());
        if common_prefix_len == prefix.as_bytes().len() {
            let value = self.take_value();
            let child = self.take_child();
            let node = Node::new(&self.label()[common_prefix_len..], value, child, None);
            if let Some(sibling) = self.take_sibling() {
                *self = sibling;
            }
            Some(node)
        } else if common_prefix_len == self.label().len() {
            self.child_mut()
                .and_then(|child| child.split_by_prefix(next, level + 1))
                .inspect(|_old| {
                    self.try_reclaim_child();
                    self.try_merge_with_child(level);
                })
        } else if common_prefix_len == 0 && prefix.cmp_first_item(self.label()).is_ge() {
            self.sibling_mut()
                .and_then(|sibling| sibling.split_by_prefix(next, level))
                .inspect(|_old| {
                    self.try_reclaim_sibling();
                })
        } else {
            None
        }
    }
    pub(crate) fn remove<K: ?Sized + BorrowedBytes>(&mut self, key: &K, level: usize) -> Option<V> {
        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        if common_prefix_len == self.label().len() {
            if next.is_empty() {
                self.take_value().inspect(|_old| {
                    self.try_merge_with_child(level);
                })
            } else {
                self.child_mut()
                    .and_then(|child| child.remove(next, level + 1))
                    .inspect(|_old| {
                        self.try_reclaim_child();
                        self.try_merge_with_child(level);
                    })
            }
        } else if common_prefix_len == 0 && key.cmp_first_item(self.label()).is_ge() {
            self.sibling_mut()
                .and_then(|sibling| sibling.remove(next, level))
                .inspect(|_old| {
                    self.try_reclaim_sibling();
                })
        } else {
            None
        }
    }
    pub(crate) fn insert<K: ?Sized + BorrowedBytes>(&mut self, key: &K, value: V) -> Option<V> {
        if key.cmp_first_item(self.label()).is_lt() {
            let old = mem::replace(self, Node::root());
            let node = Node::new(key.as_bytes(), Some(value), None, Some(old));
            *self = node;
            // mem::forget(node);
            return None;
        }

        let (next, common_prefix_len) = key.strip_common_prefix_and_len(self.label());
        let is_label_matched = common_prefix_len == self.label().len();
        if next.as_bytes().is_empty() {
            if is_label_matched {
                let old = self.take_value();
                self.set_value(value);
                old
            } else {
                self.split_at(common_prefix_len);
                self.set_value(value);
                None
            }
        } else if is_label_matched {
            if let Some(child) = self.child_mut() {
                return child.insert(next, value);
            }
            let child = Node::new(next.as_bytes(), Some(value), None, None);
            self.set_child(child);
            None
        } else if common_prefix_len == 0 {
            if let Some(sibling) = self.sibling_mut() {
                return sibling.insert(next, value);
            }
            let sibling = Node::new(next.as_bytes(), Some(value), None, None);
            self.set_sibling(sibling);
            None
        } else {
            self.split_at(common_prefix_len);
            assert_some!(self.child_mut()).insert(next, value);
            None
        }
    }
    pub(crate) fn flags(&self) -> Flags {
        self.header().flags
        // Flags::from_bits_truncate(unsafe { *self.ptr })
    }
    fn set_flags(&mut self, other: Flags, value: bool) {
        self.header_mut().flags.set(other, value);
    }
    fn label_len(&self) -> usize {
        self.header().label_len as usize
    }
    fn split_at(&mut self, position: usize) {
        debug_assert!(position < self.label_len());
        let value = self.take_value();
        let child = self.take_child();
        let sibling = self.take_sibling();

        let child = Node::new(&self.label()[position..], value, child, None);
        let parent = Node::new(&self.label()[..position], None, Some(child), sibling);
        *self = parent;
    }
    fn try_reclaim_sibling(&mut self) {
        let sibling = assert_some!(self.sibling());
        if sibling.value().is_some() || sibling.flags().contains(Flags::CHILD_INITIALIZED) {
            return;
        }
        if let Some(sibling) = self.take_sibling().and_then(|mut n| n.take_sibling()) {
            self.set_sibling(sibling);
        }
    }
    fn try_reclaim_child(&mut self) {
        let child = assert_some!(self.child());
        if child.value().is_some() || child.flags().contains(Flags::CHILD_INITIALIZED) {
            return;
        }
        if let Some(child) = self.take_child().and_then(|mut n| n.take_sibling()) {
            self.set_child(child);
        }
    }
    pub(crate) fn try_merge_with_child(&mut self, level: usize) {
        if level == 0 {
            return;
        }

        if self.value().is_some() || !self.flags().contains(Flags::CHILD_INITIALIZED) {
            return;
        }

        let flags = assert_some!(self.child()).flags();
        if !flags.contains(Flags::SIBLING_INITIALIZED)
            && (self.label_len() + assert_some!(self.child()).label_len()) <= MAX_LABEL_LEN
        {
            let mut child = assert_some!(self.take_child());
            let sibling = self.take_sibling();
            let value = child.take_value();
            let grandchild = child.take_child();

            let mut label = Vec::with_capacity(self.label_len() + child.label_len());
            label.extend(self.label());
            label.extend(child.label());
            let node = Self::new(&label, value, grandchild, sibling);
            *self = node;
        }
    }
}

impl<V> Drop for Node<V> {
    fn drop(&mut self) {
        // let _ = self.take_value();
        // let _ = self.take_child();
        // let _ = self.take_sibling();

        self.ptr_data().dealloc(self.ptr);
        // let mut layout = Self::initial_layout(self.label_len());
        // layout = extend!(layout.extend(Layout::new::<Option<V>>())).0;
        // if self.flags().contains(Flags::CHILD_ALLOCATED) {
        //     layout = extend!(layout.extend(Layout::new::<Self>())).0;
        // }
        // if self.flags().contains(Flags::SIBLING_ALLOCATED) {
        //     layout = extend!(layout.extend(Layout::new::<Self>())).0;
        // }

        // unsafe { dealloc(self.ptr, layout.pad_to_align()) }
    }
}
impl<V: Clone> Clone for Node<V> {
    fn clone(&self) -> Self {
        let label = self.label();
        let value = self.value().cloned();
        let child = self.child().cloned();
        let sibling = self.sibling().cloned();
        Node::new(label, value, child, sibling)
    }
}
impl<V> IntoIterator for Node<V> {
    type Item = (usize, Node<V>);
    type IntoIter = IntoIter<V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            stack: vec![(0, self)],
        }
    }
}

/// An iterator which traverses the nodes in a tree, in depth first order.
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct Iter<'a, V: 'a> {
    stack: Vec<(usize, &'a Node<V>)>,
}
impl<'a, V: 'a> Iterator for Iter<'a, V> {
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.stack.pop() {
            if level != 0 {
                if let Some(sibling) = node.sibling() {
                    self.stack.push((level, sibling));
                }
            }
            if let Some(child) = node.child() {
                self.stack.push((level + 1, child));
            }
            Some((level, node))
        } else {
            None
        }
    }
}

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
    sibling: Option<&'a mut Node<V>>,
    child: Option<&'a mut Node<V>>,
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
            if level != 0 {
                if let Some(sibling) = node.sibling.take() {
                    self.stack.push((level, sibling));
                }
            }
            if let Some(child) = node.child.take() {
                self.stack.push((level + 1, child));
            }
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
                if let Some(sibling) = node.sibling() {
                    self.stack.push((offset, sibling));
                }
            }

            if common_prefix_len == node.label().len() {
                let prefix_len = offset + common_prefix_len;
                if let Some(child) = node.child() {
                    self.stack.push((prefix_len, child));
                }
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
                if let Some(sibling) = node.sibling() {
                    self.stack.push((offset, sibling));
                }
            }

            if common_prefix_len == node.label().len() {
                let prefix_len = offset + common_prefix_len;
                if let Some(child) = node.child() {
                    self.stack.push((prefix_len, child));
                }
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
impl<V> Iterator for IntoIter<V> {
    type Item = (usize, Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, mut node)) = self.stack.pop() {
            if let Some(sibling) = node.take_sibling() {
                self.stack.push((level, sibling));
            }
            if let Some(child) = node.take_child() {
                self.stack.push((level + 1, child));
            }
            Some((level, node))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{PatriciaSet, StringPatriciaMap};
    use std::str;

    #[test]
    fn root_works() {
        let node = Node::<()>::root();
        assert!(node.label().is_empty());
        assert!(node.value().is_none());
        assert!(node.child().is_none());
        assert!(node.sibling().is_none());
    }

    #[test]
    fn new_works() {
        let node0 = Node::new("foo".as_ref(), Some(3), None, None);
        assert_eq!(node0.label(), b"foo");
        assert_eq!(node0.value(), Some(&3));
        assert_eq!(node0.child().map(|n| n.label()), None);
        assert_eq!(node0.sibling().map(|n| n.label()), None);

        let node1 = Node::new("bar".as_ref(), None, None, Some(node0));
        assert_eq!(node1.label(), b"bar");
        assert_eq!(node1.value(), None);
        assert_eq!(node1.child().map(|n| n.label()), None);
        assert_eq!(node1.sibling().map(|n| n.label()), Some(&b"foo"[..]));

        // If the length of a label name is longer than 255, it will be splitted to two nodes.
        let node2 = Node::new([b'a'; 256].as_ref(), Some(4), Some(node1), None);
        assert_eq!(node2.label(), [b'a'; 255].as_ref());
        assert_eq!(node2.value(), None);
        assert_eq!(node2.child().map(|n| n.label()), Some(&b"a"[..]));
        assert_eq!(node2.sibling().map(|n| n.label()), None);

        assert_eq!(node2.child().unwrap().value(), Some(&4));
        assert_eq!(node2.child().unwrap().child().unwrap().label(), b"bar");
    }

    #[test]
    fn ietr_works() {
        let mut set = PatriciaSet::new();
        set.insert("foo");
        set.insert("bar");
        set.insert("baz");

        // let root = set.into_node();
        // let nodes = root
        //     .iter()
        //     .map(|(level, node)| (level, node.label()))
        //     .collect::<Vec<_>>();
        // assert_eq!(
        //     nodes,
        //     [
        //         (0, "".as_ref()),
        //         (1, "ba".as_ref()),
        //         (2, "r".as_ref()),
        //         (2, "z".as_ref()),
        //         (1, "foo".as_ref())
        //     ]
        // );
    }

    #[test]
    fn iter_mut_works() {
        let mut set = PatriciaSet::new();
        set.insert("foo");
        set.insert("bar");
        set.insert("baz");

        let mut root = set.into_node();
        let nodes = root
            .iter_mut()
            .map(|(level, node)| (level, node.label()))
            .collect::<Vec<_>>();
        assert_eq!(
            nodes,
            [
                (0, "".as_ref()),
                (1, "ba".as_ref()),
                (2, "r".as_ref()),
                (2, "z".as_ref()),
                (1, "foo".as_ref())
            ]
        );
    }

    #[test]
    fn long_label_works() {
        let node = Node::new(&[b'a'; 256][..], Some(10), None, None);
        assert_eq!(node.label(), &[b'a'; 255][..]);
        assert_eq!(node.value(), None);
        assert!(node.child().is_some());

        let child = node.child().unwrap();
        assert_eq!(child.label(), b"a");
        assert_eq!(child.value(), Some(&10));
    }

    #[test]
    fn reclaim_works() {
        let mut set = ["123", "123456", "123abc", "123def"]
            .iter()
            .collect::<PatriciaSet>();
        assert_eq!(
            set_to_labels(&set),
            [(0, ""), (1, "123"), (2, "456"), (2, "abc"), (2, "def")]
        );

        set.remove("123def");
        assert_eq!(
            set_to_labels(&set),
            [(0, ""), (1, "123"), (2, "456"), (2, "abc")]
        );

        set.remove("123456");
        assert_eq!(set_to_labels(&set), [(0, ""), (1, "123"), (2, "abc")]);

        set.remove("123");
        assert_eq!(set_to_labels(&set), [(0, ""), (1, "123abc")]);
    }

    #[test]
    fn get_longest_common_prefix_works() {
        let set = ["123", "123456", "1234_67", "123abc", "123def"]
            .iter()
            .collect::<PatriciaSet>();

        let lcp = |key| set.get_longest_common_prefix(key);
        assert_eq!(lcp(""), None);
        assert_eq!(lcp("12"), None);
        assert_eq!(lcp("123"), Some("123".as_bytes()));
        assert_eq!(lcp("1234"), Some("123".as_bytes()));
        assert_eq!(lcp("123456"), Some("123456".as_bytes()));
        assert_eq!(lcp("1234_6"), Some("123".as_bytes()));
        assert_eq!(lcp("123456789"), Some("123456".as_bytes()));
    }

    #[test]
    fn get_longest_common_prefix_mut_works() {
        let mut map = [
            ("123", 1),
            ("123456", 2),
            ("1234_67", 3),
            ("123abc", 4),
            ("123def", 5),
        ]
        .iter()
        .cloned()
        .map(|(k, v)| (String::from(k), v))
        .collect::<StringPatriciaMap<usize>>();

        assert_eq!(map.get_longest_common_prefix_mut(""), None);
        assert_eq!(map.get_longest_common_prefix_mut("12"), None);
        assert_eq!(
            map.get_longest_common_prefix_mut("123"),
            Some(("123", &mut 1))
        );
        *map.get_longest_common_prefix_mut("123").unwrap().1 = 10;
        assert_eq!(
            map.get_longest_common_prefix_mut("1234"),
            Some(("123", &mut 10))
        );
        assert_eq!(
            map.get_longest_common_prefix_mut("123456"),
            Some(("123456", &mut 2))
        );
        *map.get_longest_common_prefix_mut("1234567").unwrap().1 = 20;
        assert_eq!(
            map.get_longest_common_prefix_mut("1234_6"),
            Some(("123", &mut 10))
        );
        assert_eq!(
            map.get_longest_common_prefix_mut("123456789"),
            Some(("123456", &mut 20))
        );
    }

    fn set_to_labels(set: &PatriciaSet) -> Vec<(usize, &str)> {
        set.as_node()
            .iter()
            .map(|(level, n)| (level, str::from_utf8(n.label()).unwrap()))
            .collect()
    }
}
