//! node common methods
use crate::{BorrowedBytes, Bytes, Node};
use crate::{NodeHeader, PtrData};
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::marker::PhantomData;
use core::mem;

macro_rules! assert_some {
    ($expr:expr) => {
        if let Some(value) = $expr {
            value
        } else {
            // TODO: change to unreachable?
            panic!("`{}` must be `Some(..)`", stringify!($expr));
        }
    };
}

macro_rules! extend {
    ($expr:expr) => {{
        let val = match $expr {
            Ok(tuple) => tuple,
            Err(_) => unreachable!("Layout extension failed"),
        };
        val
    }};
}

pub(crate) use {assert_some, extend};

pub const MAX_LABEL_LEN: usize = u8::MAX as usize;

impl<V> Node<V> {
    /// Makes a new node which represents an empty tree.
    pub fn root() -> Self {
        Node::new(b"", [], None)
    }

    /// Returns the label of this node.
    pub fn label(&self) -> &[u8] {
        unsafe { PtrData::<V>::label(self.ptr) }
    }

    #[allow(unused)]
    pub(crate) fn label_mut(&mut self) -> &mut [u8] {
        unsafe { PtrData::<V>::label_mut(self.ptr) }
    }

    /// Returns a reference to the header for this node.
    #[inline]
    pub(crate) fn header(&self) -> &NodeHeader {
        unsafe { self.ptr.as_ref() }
    }

    #[allow(unused)]
    #[inline]
    pub(crate) fn header_mut(&mut self) -> &mut NodeHeader {
        unsafe { self.ptr.as_mut() }
    }
    /// Returns the layout and field offsets for the allocated buffer backing this node.
    #[inline]
    pub(crate) fn ptr_data(&self) -> PtrData<V> {
        self.header().ptr_data()
    }

    /// get all children for node as slice
    pub fn children(&self) -> &[Node<V>] {
        unsafe { self.ptr_data().children(self.ptr) }
    }
    /// get all children for node as mut slice
    pub fn children_mut(&mut self) -> &mut [Node<V>] {
        unsafe { self.ptr_data().children_mut(self.ptr) }
    }
    /// return the first byte of each childs label
    pub(crate) fn children_first_bytes(&self) -> impl Iterator<Item = Option<u8>> {
        // TODO: consider storing first bytes in node? trade memory for lookup speed
        self.children().iter().map(|n| n.label().first().cloned())
    }

    /// take all the children out of a node and return them
    pub fn take_children(&mut self) -> Option<Vec<Node<V>>> {
        let len = self.children_len();
        if len == 0 {
            return None;
        }
        let mut ret = Vec::with_capacity(len);
        unsafe {
            let ptr = self.ptr_data().children_ptr(self.ptr).unwrap();
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
    /// return number of children
    pub fn children_len(&self) -> usize {
        self.header().children_len as usize
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

    pub(crate) fn child_with_first(&self, byte: u8) -> Option<&Self> {
        // TODO: child methods could use binary search?
        let i = self.child_index_with_first(byte)?;
        // SAFETY: we know i is inside the bounds already
        Some(unsafe { self.children().get_unchecked(i) })
    }
    pub(crate) fn child_with_first_mut(&mut self, byte: u8) -> Option<&mut Self> {
        let i = self.child_index_with_first(byte)?;
        Some(unsafe { self.children_mut().get_unchecked_mut(i) })
    }
    pub(crate) fn child_index_with_first(&self, byte: u8) -> Option<usize> {
        self.children_first_bytes()
            .enumerate()
            .find(|(_, b)| b.is_some_and(|b| b == byte))
            .map(|(i, _)| i)
    }

    pub(crate) fn get<K: ?Sized + BorrowedBytes>(&self, key: &K) -> Option<&V> {
        self.get_node(key).and_then(|n| n.value())
    }

    #[inline]
    pub(crate) fn get_node<K: ?Sized + BorrowedBytes>(&self, key: &K) -> Option<&Self> {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            key = crate::strip_prefix(key, cur.label())?;
            match key.first() {
                None => return Some(cur),
                Some(first) => {
                    cur = cur.child_with_first(*first)?;
                }
            }
        }
    }

    #[inline]
    pub(crate) fn get_node_mut<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<&mut Self> {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            key = crate::strip_prefix(key, cur.label())?;
            match key.first() {
                None => return Some(cur),
                Some(first) => {
                    cur = cur.child_with_first_mut(*first)?;
                }
            }
        }
    }

    pub(crate) fn get_mut<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<&mut V> {
        self.get_node_mut(key).and_then(|n| n.value_mut())
    }

    pub(crate) fn get_longest_common_prefix<K: ?Sized + BorrowedBytes>(
        &self,
        key: &K,
    ) -> Option<(usize, &Self)> {
        let mut cur = self;
        let mut key = key.as_bytes();
        let mut matched_len = 0;
        let mut last_match = None;

        loop {
            let Some(remaining) = crate::strip_prefix(key, cur.label()) else {
                return last_match;
            };
            key = remaining;
            matched_len += cur.label_len();

            if cur.value().is_some() {
                last_match = Some((matched_len, cur));
            }
            if key.is_empty() {
                return last_match;
            }

            match cur.child_with_first(unsafe { *key.get_unchecked(0) }) {
                None => {
                    return last_match;
                }
                Some(child) => {
                    cur = child;
                }
            }
        }
    }

    pub(crate) fn get_longest_common_prefix_mut<K: ?Sized + BorrowedBytes>(
        &mut self,
        key: &K,
    ) -> Option<(usize, &mut Self)> {
        let mut cur = self;
        let mut key = key.as_bytes();
        let mut matched_len = 0;
        let mut last_match: Option<(usize, *mut Node<V>)> = None;
        loop {
            let Some(remaining) = crate::strip_prefix(key, cur.label()) else {
                return last_match.map(|(len, ptr)| unsafe { (len, &mut *ptr) });
            };
            key = remaining;
            matched_len += cur.label_len();

            if cur.value().is_some() {
                last_match = Some((matched_len, cur));
            }
            if key.is_empty() {
                return last_match.map(|(len, ptr)| unsafe { (len, &mut *ptr) });
            }
            match cur.child_with_first_mut(unsafe { *key.get_unchecked(0) }) {
                None => {
                    return last_match.map(|(len, ptr)| unsafe { (len, &mut *ptr) });
                }
                Some(child) => {
                    cur = child;
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

    /// insert key and value into node
    pub fn insert<K: ?Sized + BorrowedBytes>(&mut self, key: &K, value: V) -> Option<V> {
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

    pub(crate) fn label_len(&self) -> usize {
        self.header().label_len as usize
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
            let next_level = level + 1;
            for child in node.children() {
                self.stack.push((next_level, child))
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
    pub(crate) label: &'a [u8],
    pub(crate) value: Option<&'a mut V>,
    pub(crate) children: Option<&'a mut [Node<V>]>,
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
            let next_level = level + 1;
            if let Some(children) = node.children.take() {
                for child in children {
                    self.stack.push((next_level, child))
                }
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
            let key = self.key.strip_n_prefix(offset).as_bytes();
            let next = crate::strip_prefix(key, node.label())?;
            let common_prefix_len = key.len() - next.len();
            let prefix_len = offset + common_prefix_len;
            match key.first() {
                None => return Some((prefix_len, node)),
                Some(first) => {
                    self.stack
                        .push((prefix_len, node.child_with_first(*first)?));
                }
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
            let key = self.key.as_ref().strip_n_prefix(offset).as_bytes();
            let next = crate::strip_prefix(key, node.label())?;
            let common_prefix_len = key.len() - next.len();
            let prefix_len = offset + common_prefix_len;
            match key.first() {
                None => return Some((prefix_len, node)),
                Some(first) => {
                    self.stack
                        .push((prefix_len, node.child_with_first(*first)?));
                }
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
            let next_level = level + 1;
            if let Some(children) = node.take_children() {
                for child in children {
                    self.stack.push((next_level, child))
                }
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
    // use crate::{PatriciaSet, StringPatriciaMap};

    #[test]
    fn root_works() {
        let node = Node::<()>::root();
        assert!(node.label().is_empty());
        assert!(node.value().is_none());
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

        match node1.children() {
            [node0] => {
                assert_eq!(node0.label(), b"foo");
                assert_eq!(node0.value(), Some(&3));
                assert_eq!(
                    node0
                        .children()
                        .iter()
                        .map(|n| n.label())
                        .collect::<Vec<&[u8]>>(),
                    Vec::<&[u8]>::new()
                );
            }
            _ => {
                panic!("test failed")
            }
        }
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
        let mut root: Node<u32> = Node::new(b"test", [], Some(1));
        // insert test
        // split at 2 so we have te -> am
        //                          -> st
        unsafe {
            root.split_at(2, Some(Node::new(b"am", [], Some(2))));
        }
        assert_eq!(root.get("team"), Some(&2));
        assert_eq!(root.get("test"), Some(&1));

        // recreate root
        let mut root: Node<u32> = Node::new(b"", [], Some(2));
        root.insert("test", 1);
        assert_eq!(root.get("test"), Some(&1));

        root.insert("team", 2);
        assert_eq!(root.get("team"), Some(&2));

        root.insert("toast", 3);

        // Test get
        assert_eq!(root.get("test"), Some(&1));
        assert_eq!(root.get("team"), Some(&2));
        assert_eq!(root.get("toast"), Some(&3));
        assert_eq!(root.get("te"), None); // prefix, no value
        assert_eq!(root.get("testing"), None); // non-matching
        assert_eq!(root.get(""), root.value()); // root value

        // Test get_mut
        let val = root.get_mut("test");
        assert_eq!(*val.as_deref().unwrap(), 1);
        *val.unwrap() = 10;
        assert_eq!(root.get("test"), Some(&10));

        // Test get_mut on non-existent key
        assert_eq!(root.get_mut("nonexistent"), None);
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

    /// Creates a standard test tree with the following structure:
    /// "" (root, val: 0)
    ///  ├─ "a" (val: 1)
    ///  │   └─ "pp"
    ///  │       ├─ "le" (val: 2)
    ///  │       └─ "ly" (val: 3)
    ///  └─ "box" (val: 4)
    fn create_test_tree_with_root_val() -> Node<u32> {
        let mut root = Node::root();
        root.insert("", 0);
        root.insert("a", 1);
        root.insert("apple", 2);
        root.insert("apply", 3);
        root.insert("box", 4);
        root
    }

    /// Creates a standard test tree with the following structure:
    /// "" (root, val: None)
    ///  ├─ "a" (val: 1)
    ///  │   └─ "pp"
    ///  │       ├─ "le" (val: 2)
    ///  │       └─ "ly" (val: 3)
    ///  └─ "box" (val: 4)
    fn create_test_tree() -> Node<u32> {
        let mut root = Node::root();
        root.insert("a", 1);
        root.insert("apple", 2);
        root.insert("apply", 3);
        root.insert("box", 4);
        root
    }
    #[test]
    fn test_get_node() {
        let root = create_test_tree();

        // Exact matches
        assert_eq!(root.get_node("").unwrap().value(), None);
        assert_eq!(root.get_node("a").unwrap().label(), b"a");
        assert_eq!(root.get_node("a").unwrap().value(), Some(&1));
        assert_eq!(root.get_node("apple").unwrap().label(), b"e"); // "e" is the node for "apple"
        assert_eq!(root.get_node("apply").unwrap().label(), b"y"); // "y" is the node for "apply"
        assert_eq!(root.get_node("box").unwrap().label(), b"box");

        // Prefix of a node that's not been split on
        assert!(root.get_node("ap").is_none());
        assert!(root.get_node("bo").is_none());

        // Non-existent keys
        assert!(root.get_node("b").is_none());
        assert!(root.get_node("apples").is_none());
        assert!(root.get_node("xyz").is_none());

        // Intermediate node without a value
        let a_node = root.get_node("a").unwrap();
        let pp_node = a_node
            .children()
            .iter()
            .find(|n| n.label() == b"ppl")
            .unwrap();
        assert!(pp_node.value().is_none());
    }

    #[test]
    fn test_get_node_mut() {
        let mut root = create_test_tree();

        // Exact match and mutate
        let apple_node = root.get_node_mut("apple").unwrap();
        assert_eq!(apple_node.value(), Some(&2));
        apple_node.set_value(20);
        assert_eq!(apple_node.value(), Some(&20));

        // Verify change from root
        assert_eq!(root.get("apple"), Some(&20));

        // Non-existent key
        assert!(root.get_node_mut("xyz").is_none());
    }

    #[test]
    fn test_get_longest_common_prefix() {
        let mut root = create_test_tree_with_root_val();

        // Key is shorter than any entry
        assert_eq!(
            root.get_longest_common_prefix("")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((0, &0))
        );
        // Root has value 0
        assert_eq!(
            root.get_longest_common_prefix("b")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((0, &0))
        );

        // Key is a prefix of an entry
        assert_eq!(
            root.get_longest_common_prefix("ap")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((1, &1))
        ); // "a" is the LCP
        assert_eq!(
            root.get_longest_common_prefix("app")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((1, &1))
        );
        assert_eq!(
            root.get_longest_common_prefix("appl")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((1, &1))
        );

        // Key matches an entry exactly
        assert_eq!(
            root.get_longest_common_prefix("a")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((1, &1))
        );
        assert_eq!(
            root.get_longest_common_prefix("apple")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((5, &2))
        );
        assert_eq!(
            root.get_longest_common_prefix("box")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((3, &4))
        );

        // Key extends an entry
        assert_eq!(
            root.get_longest_common_prefix("apples")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((5, &2))
        );
        assert_eq!(
            root.get_longest_common_prefix("boxer")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((3, &4))
        );

        // No match beyond root
        assert_eq!(
            root.get_longest_common_prefix_mut("xyz")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((0, &0))
        );

        // Test with a tree where root has no value
        let mut root_no_val = Node::root();
        root_no_val.insert("test", 10);
        assert!(root_no_val.get_longest_common_prefix("t").is_none());
        assert_eq!(
            root_no_val
                .get_longest_common_prefix("testing")
                .and_then(|(len, n)| Some((len, n.value()?))),
            Some((4, &10))
        );
    }

    #[test]
    fn test_get_longest_common_prefix_mut() {
        let mut root = create_test_tree();

        // Find LCP and mutate it
        let (len, val) = root.get_longest_common_prefix_mut("apples").unwrap();
        assert_eq!(len, 5);
        assert_eq!(*val.value_mut().unwrap(), 2);
        *val.value_mut().unwrap() = 22;

        // Verify the change
        assert_eq!(root.get("apple"), Some(&22));

        // Find another LCP and mutate
        let (len, val) = root.get_longest_common_prefix_mut("app").unwrap();
        assert_eq!(len, 1);
        assert_eq!(*val.value().unwrap(), 1);
        *val.value_mut().unwrap() = 11;

        // Verify the change
        assert_eq!(root.get("a"), Some(&11));
        assert_eq!(root.get("apple"), Some(&22)); // Previous change should persist

        // No match
        assert!(dbg!(root.get_longest_common_prefix_mut("xyz")).is_none());

        // Match root
        assert!(root.get_longest_common_prefix_mut("b").is_none());
    }

    #[test]
    fn iter_works() {
        let mut set = Node::root();
        set.insert("foo", ());
        set.insert("bar", ());
        set.insert("baz", ());

        let nodes = set
            .iter()
            .map(|(level, node)| (level, node.label()))
            .collect::<Vec<_>>();
        assert_eq!(
            nodes,
            [
                // TODO: is this order wrong?
                (0, "".as_ref()),
                (1, "foo".as_ref()),
                (1, "ba".as_ref()),
                (2, "z".as_ref()),
                (2, "r".as_ref()),
            ]
        );
    }

    #[test]
    fn iter_mut_works() {
        let mut set = Node::root();
        set.insert("foo", ());
        set.insert("bar", ());
        set.insert("baz", ());

        let nodes = set
            .iter_mut()
            .map(|(level, node)| (level, node.label()))
            .collect::<Vec<_>>();
        assert_eq!(
            nodes,
            [
                (0, "".as_ref()),
                (1, "foo".as_ref()),
                (1, "ba".as_ref()),
                (2, "z".as_ref()),
                (2, "r".as_ref()),
            ]
        );
    }

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
