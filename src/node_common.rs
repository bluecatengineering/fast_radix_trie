//! node common methods
use crate::{BorrowedBytes, Bytes, Node, NodeHeader, NodePtrAndData, PtrData};
use alloc::{collections::VecDeque, string::String, vec::Vec};
use core::{cmp::Ordering, fmt, marker::PhantomData, mem};

macro_rules! assert_some {
    ($expr:expr) => {
        match $expr {
            Some(value) => value,
            // TODO: change to unreachable?
            None => panic!("`{}` must be `Some(..)`", stringify!($expr)),
        }
    };
}

macro_rules! extend {
    ($expr:expr) => {{
        match $expr {
            Ok(tuple) => tuple,
            Err(_) => unreachable!("Layout extension failed"),
        }
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
    pub(crate) fn children_first_bytes(
        &self,
    ) -> impl DoubleEndedIterator<Item = u8> + ExactSizeIterator {
        // TODO: consider storing first bytes in node? trade memory for lookup speed
        self.children()
            .iter()
            .map(|n| *n.label().first().expect("child nodes must have label"))
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
            // swap out children
            let old_ptr = NodePtrAndData {
                ptr: self.ptr,
                ptr_data: self.ptr_data(),
            };
            // re-assign new node
            self.ptr = node.into_ptr_forget();
            // dealloc old block but forget value/children, they've moved
            old_ptr.ptr_data.dealloc_forget(old_ptr.ptr);
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

    /// Gets an iterator which traverses the nodes in this tree, in breadth first order.
    pub fn iter_bfs(&self) -> IterBfs<'_, V> {
        IterBfs {
            queue: vec![(0, self)].into(),
        }
    }

    /// Gets a mutable iterator which traverses the nodes in this tree, in breadth first order.
    pub fn iter_mut_bfs(&mut self) -> IterMutBfs<'_, V> {
        IterMutBfs {
            queue: vec![(0, self)].into(),
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
            .find(|(_, b)| *b == byte)
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

    /// will get node based on prefix, so partial matches are allowed. i.e. if a node was inserted for "apples"
    /// get_prefix_node("ap") will retrieve the node "apples" and return the length of the partial match
    #[inline]
    pub(crate) fn get_prefix_node<K: ?Sized + BorrowedBytes>(
        &self,
        key: &K,
    ) -> Option<(usize, &Self)> {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            // strip label prefix off key
            let Some(next) = crate::strip_prefix(key, cur.label()) else {
                // if label is longer than key, we are at final node,
                // see if there is a partial match at the current node
                if crate::strip_prefix(cur.label(), key).is_some() {
                    return Some((key.len(), cur));
                } else {
                    // key doesn't partially match label, so return None
                    return None;
                }
            };
            key = next;
            match key.first() {
                // end of the line-- got an exact match
                None => return Some((cur.label_len(), cur)),
                Some(first) => {
                    // find child or return None
                    cur = cur.child_with_first(*first)?;
                }
            }
        }
    }

    /// will get mutable node based on prefix, so partial matches are allowed. i.e. if a node was inserted for "apples"
    /// get_prefix_node_mut("ap") will retrieve the node
    #[inline]
    pub(crate) fn get_prefix_node_mut<K: ?Sized + BorrowedBytes>(
        &mut self,
        key: &K,
    ) -> Option<(usize, &mut Self)> {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            // strip label prefix off key
            let Some(next) = crate::strip_prefix(key, cur.label()) else {
                // if label is longer than key, we are at final node,
                // see if there is a partial match at the current node
                if crate::strip_prefix(cur.label(), key).is_some() {
                    return Some((key.len(), cur));
                } else {
                    // key doesn't partially match label, so return None
                    return None;
                }
            };
            key = next;
            match key.first() {
                // end of the line-- got an exact match
                None => return Some((cur.label_len(), cur)),
                Some(first) => {
                    // find child or return None
                    cur = cur.child_with_first_mut(*first)?;
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

    pub(crate) fn split_by_prefix<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<Self> {
        let mut cur = self;
        let key = key.as_bytes();
        let mut suffix = key;
        let mut parent: *mut Node<V> = &raw mut *cur;
        loop {
            let Some(key_suffix) = crate::strip_prefix(suffix, cur.label()) else {
                break;
            };
            suffix = key_suffix;
            match key_suffix.first() {
                None => break,
                Some(first) => {
                    parent = &raw mut *cur;
                    cur = cur.child_with_first_mut(*first)?;
                }
            }
        }
        // parent should always point to something
        let parent = unsafe { &mut *parent };

        // SAFETY: using `cur` after mutating parent can cause UB
        match cur.label().first() {
            Some(first) => {
                let child_index = parent.child_index_with_first(*first)?;
                let child = &mut parent.children_mut()[child_index];
                // if prefix ends mid label then we must split the node
                if !suffix.is_empty() && suffix.len() < child.label_len() {
                    unsafe {
                        // split node so we can set label properly
                        child.split_at(suffix.len(), None);
                        // remove node we created
                        let mut detached = child.remove_child(0);
                        if parent.children_len() != 0 {
                            // remove split node that may have been left over
                            parent.remove_child(child_index);
                        }
                        // set label
                        detached.prefix_label(key);
                        Some(detached)
                    }
                } else if suffix == child.label() {
                    // we are at a leaf
                    unsafe {
                        let detached = parent.remove_child(child_index);
                        parent.try_merge_child();
                        Some(detached)
                    }
                } else if suffix.is_empty() {
                    // full match on node
                    let mut detached = unsafe { parent.remove_child(child_index) };
                    detached.set_label(key, false);
                    parent.try_merge_child();
                    Some(detached)
                } else {
                    // if suffix > child.label_len then we didn't descend far enough?
                    None
                }
            }
            None => None,
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
                None => return last_match,
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

    /// remove the value at `key` and return it, merging the tree with its children
    /// if necessary.
    pub fn remove<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<V> {
        // Find the index of child
        let key = key.as_bytes();
        let i = self.child_index_with_first(*key.first()?)?;
        let child = &mut self.children_mut()[i];

        let suffix = crate::strip_prefix(key, child.label())?;
        if suffix.is_empty() {
            // The child's label is equal to the key, so we remove the child.
            let value = child.take_value();

            if child.children().is_empty() {
                // If the child is a leaf, we remove the child node itself.
                unsafe {
                    self.remove_child(i);
                }
            } else {
                // try to merge with child if there is a single
                child.try_merge_child();
            }

            value
        } else {
            let value = child.remove(suffix);
            child.try_merge_child();
            value
        }
    }

    /// merge child if we only have one child
    pub fn try_merge_child(&mut self) {
        if self.value().is_some() || self.children_len() != 1 {
            return;
        }
        let old_parent = crate::NodePtrAndData {
            ptr: self.ptr,
            ptr_data: self.ptr_data(),
        };
        // SAFETY:
        // - we know there is exactly 1 child
        let mut child: Node<V> = unsafe { assert_some!(old_parent.children_ptr()).read() };
        // merge child label
        child.prefix_label(self.label());
        // SAFETY:
        // - dealloc old node and set child to parent
        // - dont drop children or data since they were copied
        unsafe {
            old_parent.ptr_data.dealloc_forget(old_parent.ptr);
        }
        self.ptr = child.into_ptr_forget();
    }

    /// insert key and value into node
    /// SAFETY:
    /// caller must not insert an empty label into children. only the root node can have an empty label
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
                                        // TODO: is this right? >= or > ?
                                        .find(|(_, b)| *b >= first_byte)
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

    pub fn label_len(&self) -> usize {
        self.header().label_len as usize
    }

    /// construct into_iter iterates breadth first search style
    pub fn into_iter_bfs(self) -> IntoIterBfs<V> {
        IntoIterBfs {
            queue: vec![(0, self)].into(),
        }
    }
}

impl<V: fmt::Debug> fmt::Debug for Node<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const HORIZ: char = '─';
        // const VERT: char = '|';
        const BRANCH: char = '├';
        const END: char = '└';
        let mut stack = vec![(self, 0, 0, false)];

        while let Some((next, white_indentation, line_indentation, last)) = stack.pop() {
            let label = String::from_utf8_lossy(next.label());
            let value = next
                .value()
                .map(|v| format!("({v:?})"))
                .unwrap_or_else(|| String::from("(-)"));

            let prefix = if white_indentation == 0 && line_indentation == 0 {
                String::new()
            } else {
                let whitespace = " ".repeat(white_indentation);
                let line = " ".repeat(line_indentation - 1);
                let branch_char = if last { END } else { BRANCH };
                format!("{whitespace}{line}{branch_char}{HORIZ}")
            };

            writeln!(f, "{prefix}\"{label}\" {value}")?;

            for (i, child) in next.children().iter().rev().enumerate() {
                let new_line_indentation = 4;
                let white_indentation = white_indentation + line_indentation + 2;
                let last = i == 0;
                stack.push((child, white_indentation, new_line_indentation, last));
            }
        }
        Ok(())
    }
}

impl<V: PartialEq> PartialEq for Node<V> {
    fn eq(&self, other: &Self) -> bool {
        self.label() == other.label()
            && self.value() == other.value()
            && self.children() == other.children()
    }
}

impl<V: Eq> Eq for Node<V> {}

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
            for child in node.children().iter().rev() {
                self.stack.push((next_level, child))
            }
            Some((level, node))
        } else {
            None
        }
    }
}

/// An iterator which traverses the nodes in a tree, in breadth first order
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct IterBfs<'a, V: 'a> {
    queue: VecDeque<(usize, &'a Node<V>)>,
}
impl<'a, V: 'a> Iterator for IterBfs<'a, V> {
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.queue.pop_front() {
            let next_level = level + 1;
            for child in node.children() {
                self.queue.push_back((next_level, child))
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

impl<'a, V: 'a> Iterator for IterMut<'a, V> {
    type Item = (usize, NodeMut<'a, V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.stack.pop() {
            let mut node = node.as_mut();
            let next_level = level + 1;
            if let Some(children) = node.children.take() {
                for child in children.iter_mut().rev() {
                    self.stack.push((next_level, child))
                }
            }
            Some((level, node))
        } else {
            None
        }
    }
}

/// A mutable iterator which traverses the nodes in a tree, in breadth first order.
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct IterMutBfs<'a, V: 'a> {
    queue: VecDeque<(usize, &'a mut Node<V>)>,
}

impl<'a, V: 'a> Iterator for IterMutBfs<'a, V> {
    type Item = (usize, NodeMut<'a, V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.queue.pop_front() {
            let mut node = node.as_mut();
            let next_level = level + 1;
            if let Some(children) = node.children.take() {
                for child in children {
                    self.queue.push_back((next_level, child))
                }
            }
            Some((level, node))
        } else {
            None
        }
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
                for child in children.into_iter().rev() {
                    self.stack.push((next_level, child))
                }
            }
            Some((level, node))
        } else {
            None
        }
    }
}

/// An owning iterator which traverses the nodes in a tree, in breadth first order.
///
/// The first element of an item is the level of the traversing node.
#[derive(Debug)]
pub struct IntoIterBfs<V> {
    queue: VecDeque<(usize, Node<V>)>,
}
impl<V> Iterator for IntoIterBfs<V> {
    type Item = (usize, Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, mut node)) = self.queue.pop_front() {
            let next_level = level + 1;
            if let Some(children) = node.take_children() {
                for child in children {
                    self.queue.push_back((next_level, child))
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
            let key = &self.key.as_bytes()[offset..];
            let next = crate::strip_prefix(key, node.label())?;
            let common_prefix_len = key.len() - next.len();
            let prefix_len = offset + common_prefix_len;

            if let Some(first) = next.first() {
                if let Some(child) = node.child_with_first(*first) {
                    self.stack.push((prefix_len, child));
                }
            }
            // we could val.is_some() if we dont want to return nodes with no value (that have been split)
            if common_prefix_len == node.label_len() {
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
            let key = &self.key.as_ref().as_bytes()[offset..];
            let next = crate::strip_prefix(key, node.label())?;
            let common_prefix_len = key.len() - next.len();
            let prefix_len = offset + common_prefix_len;

            if let Some(first) = next.first() {
                if let Some(child) = node.child_with_first(*first) {
                    self.stack.push((prefix_len, child));
                }
            }
            // we could val.is_some() if we dont want to return nodes with no value (that have been split)
            if common_prefix_len == node.label_len() {
                return Some((prefix_len, node));
            }
        }
        None
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{RadixSet, StringRadixMap};

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
        let child4 = Node::<()>::new(b"cherry", [], None);
        let child3 = Node::<()>::new(b"mango", [], None);
        let parent = Node::new(b"", [child1, child2, child3, child4], None);

        let mut first_bytes = parent.children_first_bytes();
        assert_eq!(first_bytes.next(), Some(b'a'));
        assert_eq!(first_bytes.next(), Some(b'b'));
        assert_eq!(first_bytes.next(), Some(b'm'));
        assert_eq!(first_bytes.next(), Some(b'c'));
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
        let mut parent = Node::new(b"", [child1, child2, child3, child4], Some(100));

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
        assert_eq!(parent.label(), b"");
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

    /// &root = "" (-)
    ///      ├─"a" (1)
    ///            ├─"b" (-)
    ///                  ├─"ort" (5)
    ///                  └─"s" (6)
    ///            └─"ppl" (-)
    ///                  ├─"e" (2)
    ///                        └─"sauce" (3)
    ///                  └─"y" (4)
    ///      └─"box" (7)
    fn create_bigger_test_tree() -> Node<u32> {
        let mut root = Node::root();
        root.insert("a", 1);
        root.insert("apple", 2);
        root.insert("applesauce", 3);
        root.insert("apply", 4);
        root.insert("abort", 5);
        root.insert("abs", 6);
        root.insert("box", 7);
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

        // Find another LCP and mutate (matches "a")
        let (len, val) = root.get_longest_common_prefix_mut("app").unwrap();
        assert_eq!(len, 1);
        assert_eq!(*val.value().unwrap(), 1);
        // mutate "a"
        *val.value_mut().unwrap() = 11;

        // Verify the change
        assert_eq!(root.get("a"), Some(&11));
        assert_eq!(root.get("apple"), Some(&22)); // Previous change should persist

        // No match
        assert!(root.get_longest_common_prefix_mut("xyz").is_none());

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
                (0, "".as_ref()),
                (1, "ba".as_ref()),
                (2, "r".as_ref()),
                (2, "z".as_ref()),
                (1, "foo".as_ref()),
            ]
        );

        let nodes = set
            .iter_bfs()
            .map(|(level, node)| (level, node.label()))
            .collect::<Vec<_>>();
        assert_eq!(
            nodes,
            [
                (0, "".as_ref()),
                (1, "ba".as_ref()),
                (1, "foo".as_ref()),
                (2, "r".as_ref()),
                (2, "z".as_ref()),
            ]
        );

        let nodes = set
            .into_iter_bfs()
            .map(|(level, node)| (level, node.label().to_vec()))
            .collect::<Vec<_>>();
        assert_eq!(
            nodes,
            [
                (0, b"".to_vec()),
                (1, b"ba".to_vec()),
                (1, b"foo".to_vec()),
                (2, b"r".to_vec()),
                (2, b"z".to_vec()),
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
                (1, "ba".as_ref()),
                (2, "r".as_ref()),
                (2, "z".as_ref()),
                (1, "foo".as_ref()),
            ]
        );

        let nodes = set
            .iter_mut_bfs()
            .map(|(level, node)| (level, node.label()))
            .collect::<Vec<_>>();
        assert_eq!(
            nodes,
            [
                (0, "".as_ref()),
                (1, "ba".as_ref()),
                (1, "foo".as_ref()),
                (2, "r".as_ref()),
                (2, "z".as_ref()),
            ]
        );
    }

    #[test]
    fn node_into_iter_works() {
        let mut set = Node::root();
        set.insert("foo", ());
        set.insert("bar", ());
        set.insert("baz", ());

        let nodes = set
            .into_iter()
            .map(|(level, node)| (level, node.label().to_vec()))
            .collect::<Vec<_>>();
        assert_eq!(
            nodes,
            [
                (0, b"".to_vec()),
                (1, b"ba".to_vec()),
                (2, b"r".to_vec()),
                (2, b"z".to_vec()),
                (1, b"foo".to_vec()),
            ]
        );
    }

    #[test]
    fn test_prefix_label() {
        let child = Node::new(b"ld", [], Some(2));
        let mut node = Node::new(b"wor", [child], Some(1));

        node.prefix_label(b"hello ");

        assert_eq!(node.label(), b"hello wor");
        assert_eq!(node.value(), Some(&1));
        assert_eq!(node.children_len(), 1);
        assert_eq!(node.children()[0].label(), b"ld");
        assert_eq!(node.children()[0].value(), Some(&2));
    }

    #[test]
    fn test_try_merge_child() {
        // Case 1: Node has no value and one child -> should merge.
        let child = Node::new(b"c", [], Some(3));
        let mut node = Node::new(b"b", [child], None); // No value
        node.try_merge_child();
        // should merge
        assert_eq!(node.label(), b"bc");
        assert_eq!(node.value(), Some(&3));
        assert_eq!(node.children_len(), 0);

        // Case 2: Node has a value -> should NOT merge.
        let child = Node::new(b"c", [], Some(3));
        let mut node = Node::new(b"b", [child], Some(2)); // Has a value
        let cloned_node = node.clone();
        node.try_merge_child();
        // should not merge
        assert_eq!(node.label(), b"b");
        assert_eq!(
            node, cloned_node,
            "Should not merge when parent has a value"
        );

        // Case 3: Node has multiple children -> should NOT merge.
        let child1 = Node::new(b"c", [], Some(3));
        let child2 = Node::new(b"d", [], Some(4));
        let mut node = Node::new(b"b", [child1, child2], None); // No value, but 2 children
        let cloned_node = node.clone();
        node.try_merge_child();
        assert_eq!(node.label(), b"b");
        assert_eq!(node.children_len(), 2);
        assert_eq!(
            node, cloned_node,
            "Should not merge when parent has multiple children"
        );

        // Case 4: Node has no children -> should do nothing.
        let mut node: Node<u32> = Node::new(b"b", [], None);
        let cloned_node = node.clone();
        node.try_merge_child();
        assert_eq!(
            node, cloned_node,
            "Should not panic or change when node has no children"
        );
    }

    #[test]
    fn test_try_merge_child_remove() {
        let mut root = Node::root();
        root.insert("a", 1);
        root.insert("ab", 2);
        root.insert("abc", 3);

        // Tree is: "" -> "a" (val:1) -> "b" (val:2) -> "c" (val:3)
        // Remove "ab". This leaves node "b" with no value and one child "c".
        // `try_merge_child` should be called on "b", merging it with "c".
        assert_eq!(root.remove("ab"), Some(2));

        // Check that node "b" has merged with "c" to become "bc".
        let node_a = root.get_node("a").unwrap();
        assert_eq!(node_a.children_len(), 1);
        let merged_node = &node_a.children()[0];
        assert_eq!(merged_node.label(), b"bc");
        assert_eq!(merged_node.value(), Some(&3));

        // Now, let's verify the whole tree structure via get.
        assert_eq!(root.get("a"), Some(&1));
        assert_eq!(root.get("ab"), None); // Was removed
        assert_eq!(root.get("abc"), Some(&3)); // Still accessible via the merged node

        // re-insert "ab"
        root.insert("ab", 2);
        assert_eq!(root.get("ab"), Some(&2));
    }

    #[test]
    fn test_try_merge_child_integration() {
        // Scenario 1: A node with two children has one removed, leaving one.
        // The parent node has no value, so it should merge with the remaining child.
        let mut root = Node::root();
        root.insert("apply", 1);
        root.insert("apple", 2);
        // Tree is: "" -> "appl" -> ["y"(v:1), "e"(v:2)]
        // The "appl" node has no value.
        assert!(root.get_node("appl").unwrap().value().is_none());

        // Remove "apply". This leaves "appl" with one child, "e".
        assert_eq!(root.remove("apply"), Some(1));

        // "appl" should merge with "e" to become "apple".
        // The root should now have one child, "apple".
        assert_eq!(root.children_len(), 1);
        let merged_node = &root.children()[0];
        assert_eq!(merged_node.label(), b"apple");
        assert_eq!(merged_node.value(), Some(&2));

        // Scenario 2: A parent with a value should NOT merge, even if left with one child.
        let mut root = Node::root();
        root.insert("a", 10); // Parent "a" has a value.
        root.insert("ab", 2);
        root.insert("ac", 3);

        // Remove "ac". Node "a" is left with one child "b".
        assert_eq!(root.remove("ac"), Some(3));

        // Node "a" should NOT merge because it has a value.
        let node_a = root.get_node("a").unwrap();
        assert_eq!(node_a.value(), Some(&10));
        assert_eq!(node_a.children_len(), 1);
        assert_eq!(node_a.children()[0].label(), b"b");
    }

    #[test]
    fn test_split_by_prefix() {
        let mut root = create_bigger_test_tree();
        // dbg!(&root);
        let other = root.split_by_prefix("ap").unwrap();
        assert_eq!(other.value(), None);
        assert_eq!(other.label(), b"appl");
        assert_eq!(other.children_len(), 2);

        let other = root.split_by_prefix("ab").unwrap();
        assert_eq!(other.value(), None);
        assert_eq!(other.label(), b"ab");
        assert_eq!(other.children_len(), 2);

        let mut root = create_bigger_test_tree();
        let other = root.split_by_prefix("b").unwrap();
        assert_eq!(other.value(), Some(&7)); // box value
        assert_eq!(other.label(), b"box");
        assert_eq!(other.children_len(), 0);

        // matches a leaf split over many prefix nodes
        let mut root = create_bigger_test_tree();
        let other = root.split_by_prefix("abort").unwrap();
        assert_eq!(other.value(), Some(&5));
        assert_eq!(other.label(), b"abort");
        assert_eq!(other.children_len(), 0);

        let mut root = create_bigger_test_tree();
        let other = root.split_by_prefix("x");
        assert_eq!(other, None);

        let mut root = create_bigger_test_tree();
        let other = root.split_by_prefix("xyx");
        assert_eq!(other, None);
    }

    #[test]
    fn test_take_children() {
        let mut root = create_bigger_test_tree();
        let children = root.take_children().unwrap();
        assert_eq!(children.len(), 2);
    }

    #[test]
    fn test_common_prefixes_iter() {
        let root = create_bigger_test_tree();
        // dbg!(&root);
        let ret = root
            .common_prefixes("applesauces")
            .map(|(_, n)| n.value())
            .collect::<Vec<_>>();
        assert_eq!(ret, vec![None, Some(&1), None, Some(&2), Some(&3)])
    }

    #[test]
    fn test_issue42_iter_prefix() {
        let mut root = Node::root();
        root.insert("a0/b0", 1);
        root.insert("a1/b1", 2);
        // dbg!(&root);
        assert_eq!(root.get_prefix_node("b"), None);
        assert_eq!(root.get_prefix_node("b0"), None);
        assert_eq!(root.get_prefix_node("a0").unwrap().1.value().unwrap(), &1);
        assert_eq!(root.get_prefix_node("a0").unwrap().0, 1);
        assert_eq!(dbg!(root.get_prefix_node("a0/b1")), None);
        assert_eq!(root.get_prefix_node("a1/").unwrap().1.value().unwrap(), &2);
        assert_eq!(root.get_prefix_node("a1/").unwrap().0, 2);
        assert_eq!(root.get_prefix_node("a1/b").unwrap().1.value().unwrap(), &2);
        assert_eq!(root.get_prefix_node("a1/b").unwrap().0, 3);
        assert_eq!(root.get_prefix_node("a1/b2"), None);
    }
    #[test]
    fn get_longest_common_prefix_works() {
        let set = ["123", "123456", "1234_67", "123abc", "123def"]
            .iter()
            .collect::<RadixSet>();

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
        .collect::<StringRadixMap<usize>>();

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
}
