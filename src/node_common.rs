//! node common methods
use crate::{BorrowedBytes, Bytes, Node, NodeHeader, NodePtrAndData, PtrData, entry::*};
use alloc::{collections::VecDeque, string::String, vec::Vec};
use core::{cmp::Ordering, fmt};

macro_rules! some {
    ($expr:expr) => {
        match $expr {
            Some(value) => value,
            None => unreachable!("`{}` must be `Some(..)`", stringify!($expr)),
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

pub(crate) use {extend, some};

pub const MAX_LABEL_LEN: usize = u8::MAX as usize;

impl<V> Node<V> {
    /// Makes a new node which represents an empty tree.
    pub fn root() -> Self {
        Node::new(b"", [], None)
    }

    /// Returns the label of this node.
    pub fn label(&self) -> &[u8] {
        // Safety:
        // - `self.ptr` must point to a valid allocation created via NodeHeader::ptr_data().allocate()
        // - The allocation must still be valid and not deallocated
        // - The label region within the allocation must have been initialized
        unsafe { PtrData::<V>::label(self.ptr) }
    }

    #[allow(unused)]
    /// Returns the label of this node.
    pub(crate) fn label_str_lossy(&self) -> alloc::borrow::Cow<'_, str> {
        String::from_utf8_lossy(self.label())
    }

    #[allow(unused)]
    pub(crate) fn label_mut(&mut self) -> &mut [u8] {
        // Safety:
        // - `self.ptr` must point to a valid allocation created via NodeHeader::ptr_data().allocate()
        // - The allocation must still be valid and not deallocated
        // - The label region within the allocation must have been initialized
        // - We have exclusive access to this node via `&mut self`
        unsafe { PtrData::<V>::label_mut(self.ptr) }
    }

    /// Returns a reference to the header for this node.
    #[inline]
    pub(crate) fn header(&self) -> &NodeHeader {
        // Safety:
        // - `self.ptr` is guaranteed to be properly aligned and point to a valid NodeHeader
        // - The NodeHeader was initialized during node allocation and remains valid
        // - The pointer is not null (NonNull invariant)
        unsafe { self.ptr.as_ref() }
    }

    #[allow(unused)]
    #[inline]
    pub(crate) fn header_mut(&mut self) -> &mut NodeHeader {
        // Safety:
        // - `self.ptr` is guaranteed to be properly aligned and point to a valid NodeHeader
        // - The NodeHeader was initialized during node allocation and remains valid
        // - The pointer is not null (NonNull invariant)
        // - We have exclusive access to this node via `&mut self`
        unsafe { self.ptr.as_mut() }
    }
    /// Returns the layout and field offsets for the allocated buffer backing this node.
    #[inline]
    pub(crate) fn ptr_data(&self) -> PtrData<V> {
        self.header().ptr_data()
    }

    /// get all children for node as slice
    #[inline]
    pub fn children(&self) -> &[Node<V>] {
        // Safety:
        // - `self.ptr` points to a valid allocation with the layout specified in `ptr_data()`
        // - The children array, if present, was initialized during node creation
        // - The offset calculation in `children()` is correct for this node's layout
        // - The slice length matches the `children_len` in the header
        unsafe { self.ptr_data().children(self.ptr) }
    }
    /// get all children for node as mut slice
    #[inline]
    pub(crate) fn children_mut(&mut self) -> &mut [Node<V>] {
        // Safety:
        // - `self.ptr` points to a valid allocation with the layout specified in `ptr_data()`
        // - The children array, if present, was initialized during node creation
        // - The offset calculation in `children_mut()` is correct for this node's layout
        // - The slice length matches the `children_len` in the header
        // - We have exclusive access to this node via `&mut self`
        unsafe { self.ptr_data().children_mut(self.ptr) }
    }
    /// return the first byte of each childs label
    #[inline]
    pub(crate) fn children_first_bytes(
        &self,
    ) -> impl DoubleEndedIterator<Item = u8> + ExactSizeIterator {
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
        // Safety:
        // - `children_ptr()` returns a valid pointer when children_len > 0
        // - `ptr.add(i).read()` is safe for i in 0..len as the children array has exactly `len` initialized elements
        // - After reading all children, we create a new node without children and swap it in
        // - `dealloc_forget` is safe because the children have been moved to `ret` and won't be double-dropped
        // - The old allocation is deallocated, but its contents (children) are not dropped since we use `dealloc_forget`
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

    /// Gets an iterator which traverses nodes matching a wildcard pattern.
    ///
    /// The pattern supports:
    /// - `*` matches zero or more characters
    /// - `?` matches exactly one character
    /// - Any other byte matches literally
    ///
    /// Patterns `?` and `*` can be escaped with `\\` like so: `foo\\*b?r` to search the literal "foo*b" and `?r`
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixSet;
    ///
    /// let mut set = RadixSet::new();
    /// set.insert("foo.bar.com");
    /// set.insert("foo.baz.com");
    /// set.insert("hello.world");
    ///
    /// let matches: Vec<_> = set.wildcard_iter(b"foo.*.com").collect();
    /// assert_eq!(matches.len(), 2);
    /// ```
    pub fn wildcard_iter<'a, 'b, K: ?Sized + BorrowedBytes>(
        &'a self,
        pattern: &'b K,
    ) -> WildcardIter<'a, 'b, V> {
        WildcardIter {
            patterns: WildcardFilter::parse(pattern.as_bytes()),
            stack: vec![WildcardState {
                depth: 0,
                node: self,
                key: Vec::new(),
            }],
        }
    }

    pub(crate) fn child_with_first(&self, byte: u8) -> Option<&Self> {
        let i = self.child_index_with_first(byte)?;
        // Safety:
        // - `child_index_with_first` returns an index within bounds (i < children_len)
        // - `get_unchecked` is safe because `i` is a valid index into the children slice
        Some(unsafe { self.children().get_unchecked(i) })
    }
    pub(crate) fn child_with_first_mut(&mut self, byte: u8) -> Option<&mut Self> {
        let i = self.child_index_with_first(byte)?;
        // Safety:
        // - `child_index_with_first` returns an index within bounds (i < children_len)
        // - `get_unchecked_mut` is safe because `i` is a valid index into the children slice
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
        let mut remaining = key.as_bytes();
        loop {
            remaining = crate::strip_prefix(remaining, cur.label())?;
            match remaining.first() {
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

    /// descend the node with the key and get a mutable reference to the matching element
    pub(crate) fn get_node_mut<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<&mut Self> {
        let mut cur = self;
        let mut remaining = key.as_bytes();
        loop {
            remaining = crate::strip_prefix(remaining, cur.label())?;
            match remaining.first() {
                None => return Some(cur),
                Some(first) => {
                    cur = cur.child_with_first_mut(*first)?;
                }
            }
        }
    }

    /// split the node by the prefix into two distinct nodes
    pub fn split_by_prefix<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<Self> {
        let mut cur = self;
        let key = key.as_bytes();
        let mut suffix = key;
        let mut parent: *mut Node<V> = &raw mut *cur;
        // descend as we would for `get_prefix_node` but keep the parent ptr to lag behind `cur`
        loop {
            let Some(key_suffix) = crate::strip_prefix(suffix, cur.label()) else {
                // see if the suffix is in the label. i.e. suffix: "ba" in "bar"
                // meaning we'll split on "ba"
                if crate::strip_prefix(cur.label(), suffix).is_some() {
                    break;
                } else {
                    // key doesn't partially match label, so return None
                    return None;
                }
            };
            suffix = key_suffix;
            match suffix.first() {
                // no more key to traverse
                None => break,
                Some(first) => {
                    parent = &raw mut *cur;
                    cur = cur.child_with_first_mut(*first)?;
                }
            }
        }
        // parent should always point to something
        // Safety:
        // - `parent` points to a valid Node<V> that was obtained from `&raw mut *cur` earlier
        // - The pointer remains valid because we haven't moved or deallocated the node
        // - We have exclusive access through the original `&mut self` parameter
        let parent = unsafe { &mut *parent };

        // SAFETY: using `cur` after mutating parent can cause UB
        let first = cur.label().first()?;

        let child_index = parent.child_index_with_first(*first)?;
        let child = &mut parent.children_mut()[child_index];
        // if prefix ends mid label then we must split the node
        if !suffix.is_empty() && suffix.len() < child.label_len() {
            // Safety:
            // - `split_at(suffix.len(), None)` is safe because suffix.len() < child.label_len()
            // - `remove_child(0)` is safe because split_at creates a new child
            // - `remove_child(child_index)` is safe because child_index is a valid index
            // - These operations maintain all node invariants
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
            // Safety:
            // - `remove_child(child_index)` is safe because child_index is a valid index
            // - The child at child_index is the one we've been working with
            unsafe {
                let detached = parent.remove_child(child_index);
                parent.try_merge_child();
                Some(detached)
            }
        } else if suffix.is_empty() {
            // full match on node
            // Safety:
            // - `remove_child(child_index)` is safe because child_index is a valid index
            let mut detached = unsafe { parent.remove_child(child_index) };
            detached.replace_label(key);
            parent.try_merge_child();
            Some(detached)
        } else {
            // if suffix > child.label_len then we didn't descend far enough?
            None
        }
    }

    pub(crate) fn get_mut<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<&mut V> {
        self.get_node_mut(key).and_then(|n| n.value_mut())
    }

    pub(crate) fn longest_common_prefix_len<K: ?Sized + BorrowedBytes>(&self, key: &K) -> usize {
        let mut cur = self;
        let mut key = key.as_bytes();
        let mut matched_len = 0;

        loop {
            let (offset, _next) = crate::lcp_by4(key, cur.label());
            key = &key[offset..];
            matched_len += offset;

            if key.is_empty() || offset != cur.label_len() {
                return matched_len;
            }

            // Safety:
            // - We just checked that key is not empty, so indexing at 0 is safe
            // - `get_unchecked(0)` is safe because we verified key.is_empty() is false
            match cur.child_with_first(unsafe { *key.get_unchecked(0) }) {
                None => return matched_len,
                Some(child) => {
                    cur = child;
                }
            }
        }
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

            // Safety:
            // - We just checked that key is not empty, so indexing at 0 is safe
            // - `get_unchecked(0)` is safe because we verified key.is_empty() is false
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
                // Safety:
                // - We're converting the raw pointer back to a mutable reference
                // - The pointer came from `cur` which was a valid &mut reference
                // - No aliasing occurs because we only dereference when returning
                return last_match.map(|(len, ptr)| unsafe { (len, &mut *ptr) });
            }
            // Safety:
            // - We just checked that key is not empty, so indexing at 0 is safe
            // - `get_unchecked(0)` is safe because we verified key.is_empty() is false
            match cur.child_with_first_mut(unsafe { *key.get_unchecked(0) }) {
                None => {
                    // Safety: same as above
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
        let key = key.as_bytes();
        if key.is_empty() && self.label().is_empty() {
            // we're at root node
            return self.take_value();
        }
        let i = self.child_index_with_first(*key.first()?)?;
        // Safety:
        // - `i` is a valid index returned by `child_index_with_first`
        // - `get_unchecked_mut(i)` is safe because `i < children_len()`
        let child = unsafe { self.children_mut().get_unchecked_mut(i) };

        let remaining = crate::strip_prefix(key, child.label())?;
        if remaining.is_empty() {
            // no remaining suffix left (child == parent), so remove
            let val = child.take_value();
            if child.children().is_empty() {
                // the child is a leaf so remove
                // Safety:
                // - `i` is a valid index (we got it from `child_index_with_first`)
                // - `remove_child(i)` is safe because i < children_len()
                unsafe {
                    self.remove_child(i);
                }
            } else {
                // there are children, call try_merge
                child.try_merge_child();
            }

            val
        } else {
            // go deeper, recursively call remove on child with remaining
            let val = child.remove(remaining);
            child.try_merge_child();
            val
        }
    }

    /// merge child if we only have one child
    pub fn try_merge_child(&mut self) {
        if self.value().is_some() || self.children_len() != 1 {
            return;
        }
        // Do not merge if the combined label would exceed MAX_LABEL_LEN
        //
        // SAFETY: we know children_len == 1 so we can skip bounds check
        if (self.label_len() + unsafe { self.children().get_unchecked(0) }.label_len())
            > MAX_LABEL_LEN
        {
            return;
        }
        let old_parent = crate::NodePtrAndData {
            ptr: self.ptr,
            ptr_data: self.ptr_data(),
        };
        // Safety:
        // - We know there is exactly 1 child (checked by the if condition)
        // - `children_ptr().unwrap()` is safe because children_len() == 1
        // - `read()` transfers ownership of the child node to `child`
        let mut child: Node<V> = unsafe { some!(old_parent.children_ptr()).read() };
        // merge child label
        child.prefix_label(self.label());
        // Safety:
        // - We're deallocating the old parent node but not dropping its contents
        // - The child has been moved out via `read()` so it won't be double-freed
        // - `dealloc_forget` is appropriate here because we've transferred ownership of the child
        unsafe {
            old_parent.ptr_data.dealloc_forget(old_parent.ptr);
        }
        self.ptr = child.into_ptr_forget();
    }

    /// entry api for node
    #[inline]
    pub fn entry<K>(&mut self, key: &K) -> Entry<'_, V>
    where
        K: ?Sized + BorrowedBytes,
    {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            let (n, next) = crate::lcp_by4(cur.label(), key);
            if next.is_some() {
                // new child from common prefix that needs split at n
                // Safety:
                // - `split_at_unchecked(n)` is safe because `n` is the length of the longest common prefix
                // - `n < key.len()` is guaranteed because next.is_some() means there's a mismatch
                //
                // Split cur at the common prefix length and insert the first chunk of the
                // suffix as a new child. Then point cur at that child and key at the full
                // suffix and continue the loop
                let (_, new_suffix) = unsafe { key.split_at_unchecked(n) };
                if new_suffix.len() > MAX_LABEL_LEN {
                    let new_child: Node<V> = Node::new(&new_suffix[..MAX_LABEL_LEN], [], None);
                    // Safety:
                    // - `split_at(n, Some(new_child))` is safe because n <= cur.label_len() (from lcp_by4)
                    unsafe {
                        let idx = cur.split_at(n, Some(new_child));
                        cur = cur.children_mut().get_unchecked_mut(idx);
                    }
                    // advance key to new suffix
                    key = new_suffix;
                    continue;
                } else {
                    let new_child: Node<V> = Node::new(new_suffix, [], None);
                    // Safety:
                    //   - `split_at(n, Some(new_child))` is safe because n <= cur.label_len()
                    //     (from lcp_by4).
                    let idx = unsafe { cur.split_at(n, Some(new_child)) };
                    return Entry::Vacant(VacantEntry {
                        node: unsafe { cur.children_mut().get_unchecked_mut(idx) },
                    });
                }
            } else {
                // new child needed but next element doesn't exist
                match key.len().cmp(&cur.label_len()) {
                    Ordering::Less => {
                        // Safety:
                        // - `split_at(key.len(), None)` is safe because key.len() < cur.label_len()
                        unsafe { cur.split_at(key.len(), None) };
                        // cur.set_value(val);
                        return Entry::Vacant(VacantEntry { node: cur });
                    }
                    Ordering::Equal => {
                        return if cur.value().is_some() {
                            Entry::Occupied(OccupiedEntry { node: cur })
                        } else {
                            Entry::Vacant(VacantEntry { node: cur })
                        };
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
                                // get insert index
                                let insert_index = cur
                                    .children_first_bytes()
                                    .enumerate()
                                    .find(|(_, b)| *b >= first_byte)
                                    .map(|(i, _)| i)
                                    .unwrap_or(cur.children_len());

                                // if key is bigger than max len and there's no common prefix
                                // or the previous length was 255, we need to split off
                                // the first chunk and chain the labels together
                                if key.len() > MAX_LABEL_LEN {
                                    let child: Node<V> = Node::new(&key[..MAX_LABEL_LEN], [], None);
                                    // Safety:
                                    // - `insert_index <= children_len()` (from the computation above)
                                    // - `add_child` is safe when i <= children_len() and children_len() < u8::MAX
                                    // - `get_unchecked_mut(insert_index)` is safe because add_child guarantees the child exists at insert_index
                                    unsafe {
                                        cur.add_child(child, insert_index);
                                        cur = cur.children_mut().get_unchecked_mut(insert_index)
                                    }
                                    continue;
                                } else {
                                    // we now have index of where we can insert
                                    let child = Node::new(key, [], None);
                                    // Safety:
                                    // - `insert_index <= children_len()` (from the computation above)
                                    // - `add_child` is safe when i <= children_len() and children_len() < u8::MAX
                                    // - `get_unchecked_mut(insert_index)` is safe because add_child guarantees the child exists at insert_index
                                    unsafe {
                                        cur.add_child(child, insert_index);
                                    }
                                    return Entry::Vacant(VacantEntry {
                                        node: unsafe {
                                            cur.children_mut().get_unchecked_mut(insert_index)
                                        },
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// insert key and value into node, replacing value if key exists
    /// could be re-written to use `Entry` but the non-entry version is 5-10% faster
    /// so I'm leaving this for now
    ///
    /// # Safety
    /// caller must not insert an empty label into children. only the root node can have an empty label
    pub fn insert<K: ?Sized + BorrowedBytes>(&mut self, key: &K, value: V) -> Option<V> {
        let mut cur = self;
        let mut key = key.as_bytes();
        loop {
            let (n, next) = crate::lcp_by4(cur.label(), key);
            if next.is_some() {
                // new child from common prefix that needs split at n
                // Safety:
                // - `split_at_unchecked(n)` is safe because `n` is the length of the longest common prefix
                // - `n < key.len()` is guaranteed because next.is_some() means there's a mismatch
                let (_, new_suffix) = unsafe { key.split_at_unchecked(n) };
                if new_suffix.len() > MAX_LABEL_LEN {
                    let new_child: Node<V> = Node::new(&new_suffix[..MAX_LABEL_LEN], [], None);
                    // Safety:
                    // - `split_at(n, Some(new_child))` is safe because n <= cur.label_len() (from lcp_by4)
                    unsafe {
                        let idx = cur.split_at(n, Some(new_child));
                        cur = cur.children_mut().get_unchecked_mut(idx);
                    }
                    // advance key to new suffix
                    key = new_suffix;
                    continue;
                } else {
                    let new_child: Node<V> = Node::new(new_suffix, [], Some(value));
                    // Safety:
                    //   - `split_at(n, Some(new_child))` is safe because n <= cur.label_len()
                    //     (from lcp_by4).
                    unsafe { cur.split_at(n, Some(new_child)) };
                    return None;
                }
            } else {
                // new child needed but next element doesn't exist
                match key.len().cmp(&cur.label_len()) {
                    Ordering::Less => {
                        // Safety:
                        // - `split_at(key.len(), None)` is safe because key.len() < cur.label_len()
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
                        // Safety:
                        // - `get_unchecked(cur.label_len()..)` is safe because key.len() > cur.label_len()
                        // - This ensures cur.label_len() is a valid index within key
                        key = unsafe { key.get_unchecked(cur.label_len()..) };
                        let first_byte = key[0];
                        match cur.child_index_with_first(first_byte) {
                            Some(i) => {
                                // Safety:
                                // - `i` is a valid index returned by `child_index_with_first`
                                // - `get_unchecked_mut(i)` is safe because i < children_len()
                                cur = unsafe { cur.children_mut().get_unchecked_mut(i) };
                                continue;
                            }
                            None => {
                                // benchmarked a binary search and it's actually slower than sequential.
                                // Likely the max label size (255) makes branch misses not worth it.
                                let insert_index = cur
                                    .children_first_bytes()
                                    .enumerate()
                                    .find(|(_, b)| *b >= first_byte)
                                    .map(|(i, _)| i)
                                    .unwrap_or(cur.children_len());

                                // if key is bigger than max len and there's no common prefix
                                // or the previous length was 255, we need to split off
                                // the first chunk and chain the labels together
                                if key.len() > MAX_LABEL_LEN {
                                    let child: Node<V> = Node::new(&key[..MAX_LABEL_LEN], [], None);
                                    // Safety:
                                    // - `insert_index <= children_len()` (from the computation above)
                                    // - `add_child` is safe when i <= children_len() and children_len() < u8::MAX
                                    // - `get_unchecked_mut(insert_index)` is safe because add_child guarantees the child exists at insert_index
                                    unsafe {
                                        cur.add_child(child, insert_index);
                                        cur = cur.children_mut().get_unchecked_mut(insert_index)
                                    }
                                    continue;
                                } else {
                                    // we now have index of where we can insert
                                    let child = Node::new(key, [], Some(value));
                                    // Safety:
                                    // - `insert_index <= children_len()` (from the computation above)
                                    // - `add_child` is safe when i <= children_len() and children_len() < u8::MAX
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

    /// return node label length
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

impl<V: fmt::Debug> fmt::Debug for super::Node<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // First, print the root node's information. It has no prefix or branch.
        // Stack: (node, prefix_for_this_level, is_last_child)
        let mut stack = vec![(self, String::new(), false)];

        while let Some((node, prefix, is_last)) = stack.pop() {
            let root = prefix.is_empty();

            let label = String::from_utf8_lossy(node.label());
            let value = node
                .value()
                .map(|v| format!("({v:?})"))
                .unwrap_or_else(|| String::from("(-)"));

            if root {
                writeln!(f, "{label:?} {value}")?;
            } else {
                // Determine the branch characters for the current node
                let branch = if is_last { "└── " } else { "├── " };
                writeln!(f, "{prefix}{branch}{label:?} {value}")?;
            }

            // This prefix extends the line drawing from the parent
            let child_prefix = format!("{prefix}{}", if is_last || root { "    " } else { "│   " });

            // Push the current node's children onto the stack in reverse
            for (i, child) in node.children().iter().rev().enumerate() {
                stack.push((child, child_prefix.clone(), i == 0));
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

/// State for wildcard pattern matching traversal
#[derive(Debug, Clone)]
struct WildcardState<'a, V> {
    depth: usize,
    node: &'a Node<V>,
    key: Vec<u8>,
}

/// A parsed wildcard pattern segment
#[derive(Debug, Clone, PartialEq, Eq)]
enum Pattern<'a> {
    /// `*` matches zero or more chars
    Any,
    /// `?` matches exactly one char
    One,
    /// Literal bytes to match exactly
    Literal(&'a [u8]),
}

const ANY: u8 = b'*';
const ONE: u8 = b'?';
const ESCAPE: u8 = b'\\';

/// Parser for wildcard patterns
struct WildcardFilter;

impl WildcardFilter {
    /// Parse a pattern potentially with wildcards
    fn parse(pattern: &[u8]) -> Vec<Pattern<'_>> {
        let mut patterns = Vec::new();
        let mut escaped = false;

        let mut iter = pattern.iter().copied().enumerate().peekable();
        while let Some((i, cur)) = iter.next() {
            let next = iter.peek().map(|(_, c)| *c);
            // (current char, next char, started escape)
            match (cur, next, escaped) {
                (ESCAPE, _, false) => {
                    escaped = true;
                    continue;
                }
                (ANY, Some(ANY), false) => {} // ** means *, skip to next
                (ANY, Some(ONE), false) => {
                    // consume *? -> ?*, *?? -> ??* -> *?*? -> ??*
                    while let Some((_, c)) = iter.peek().copied() {
                        match c {
                            ONE => patterns.push(Pattern::One),
                            ANY => {}
                            _ => break,
                        }
                        iter.next();
                    }
                    patterns.push(Pattern::Any);
                }
                (ANY, _, false) => {
                    patterns.push(Pattern::Any);
                }
                (ONE, _, false) => patterns.push(Pattern::One),
                (_, _, true) => {
                    // escaped chars start new literal
                    patterns.push(Pattern::Literal(&pattern[i..=i]));
                }
                _ => {
                    // literal
                    if let Some(Pattern::Literal(slice)) = patterns.last_mut() {
                        let start = i - slice.len();
                        *slice = &pattern[start..=(start + slice.len())];
                    } else {
                        patterns.push(Pattern::Literal(&pattern[i..=i]));
                    }
                }
            }
            escaped = false;
        }
        patterns
    }
}

/// An iterator over nodes matching a wildcard pattern
///
/// supports:
/// - `*` matches zero or more characters
/// - `?` matches exactly one character
/// - literal slices
#[derive(Debug)]
pub struct WildcardIter<'a, 'b, V> {
    patterns: Vec<Pattern<'b>>,
    stack: Vec<WildcardState<'a, V>>,
}

/// Result item from WildcardIter containing the accumulated key and the matching node
#[derive(Debug)]
pub struct WildcardMatch<'a, V> {
    pub(crate) key: Vec<u8>,
    pub(crate) node: &'a Node<V>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WalkResult {
    /// Exact pattern match. Don't explore further.
    Match,
    /// Key matches so far AND children could also produce matches (e.g. trailing `*`).
    MatchAndPartial,
    /// Key is valid prefix of a match, explore children but don't yield this node.
    PartialMatch,
    /// Key cannot match, stop searching.
    NoMatch,
}

impl WalkResult {
    fn is_match(self) -> bool {
        matches!(self, WalkResult::Match | WalkResult::MatchAndPartial)
    }

    fn explore_children(self) -> bool {
        matches!(self, WalkResult::PartialMatch | WalkResult::MatchAndPartial)
    }
}

impl<'a, 'b, V> WildcardIter<'a, 'b, V> {
    fn check_pattern(key: &[u8], patterns: &[Pattern<'_>]) -> WalkResult {
        Self::check_recursive(key, patterns, 0, 0)
    }

    fn check_recursive(
        key: &[u8],
        patterns: &[Pattern<'_>],
        key_idx: usize,
        pat_idx: usize,
    ) -> WalkResult {
        // both exhausted
        // exact match, children have extra bytes pattern can't consume
        if key_idx == key.len() && pat_idx == patterns.len() {
            return WalkResult::Match;
        }
        // pattern exhausted
        // no match, prune
        if pat_idx >= patterns.len() {
            return WalkResult::NoMatch;
        }
        // key exhausted
        // but more pattern: children could have matches
        if key_idx == key.len() {
            return WalkResult::PartialMatch;
        }

        match &patterns[pat_idx] {
            Pattern::Literal(lit) => {
                let remaining = &key[key_idx..];
                let (n, _) = crate::lcp_by4(remaining, lit);
                if n == lit.len() {
                    // full literal match, continue with next pattern
                    Self::check_recursive(key, patterns, key_idx + n, pat_idx + 1)
                } else if n == remaining.len() {
                    // key exhausted mid-literal, children could complete it
                    WalkResult::PartialMatch
                } else {
                    WalkResult::NoMatch
                }
            }
            Pattern::One => {
                // consume one byte
                Self::check_recursive(key, patterns, key_idx + 1, pat_idx + 1)
            }
            Pattern::Any => {
                // try to consume, starting with longest first
                let mut is_match = false;
                for consume in (0..=(key.len() - key_idx)).rev() {
                    if Self::check_recursive(key, patterns, key_idx + consume, pat_idx + 1)
                        .is_match()
                    {
                        is_match = true;
                        break;
                    }
                }
                // Any can always consume child bytes too, so always explore children
                if is_match {
                    WalkResult::MatchAndPartial
                } else {
                    WalkResult::PartialMatch
                }
            }
        }
    }
}

impl<'a, 'b, V> Iterator for WildcardIter<'a, 'b, V> {
    type Item = WildcardMatch<'a, V>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(state) = self.stack.pop() {
            let WildcardState {
                depth,
                node,
                mut key,
            } = state;

            // append current node's label to the accumulated key
            key.extend_from_slice(node.label());

            let result = Self::check_pattern(&key, &self.patterns);

            if result.explore_children() {
                for child in node.children().iter().rev() {
                    self.stack.push(WildcardState {
                        depth: depth + 1,
                        node: child,
                        key: key.clone(),
                    });
                }
            }

            if result.is_match() {
                return Some(WildcardMatch { key, node });
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
    use crate::{RadixMap, RadixSet, StringRadixMap};

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
        let mut root = Node::new(b"", [], None);
        unsafe { root.add_child(Node::new(b"b", [], Some(2)), 0) };
        // should shift children right
        unsafe { root.add_child(Node::new(b"a", [], Some(1)), 0) };
        assert_eq!(
            root.children_first_bytes().collect::<Vec<_>>(),
            vec![b'a', b'b']
        );

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
    fn test_insert_with_or_modify() {
        let mut root = Node::root();
        root.insert("test", 10);

        // modify
        let mut modify_called = false;
        root.entry("test")
            .and_modify(|v| {
                *v += 5;
                modify_called = true;
            })
            .or_insert_with(|| panic!("insert should not be called"));

        assert!(modify_called);
        assert_eq!(root.get("test"), Some(&15));

        // insert new
        let mut insert_called = false;
        root.entry("new_key")
            .and_modify(|_| panic!("modified"))
            .or_insert_with(|| {
                insert_called = true;
                100
            });
        assert!(insert_called);
        assert_eq!(root.get("new_key"), Some(&100));

        root.insert("apple", 1);
        // create intermediate node "appl"
        let mut insert_called_on_prefix = false;
        root.entry("appl")
            .and_modify(|_| panic!("modify called"))
            .or_insert_with(|| {
                insert_called_on_prefix = true;
                99
            });
        assert!(insert_called_on_prefix);
        assert_eq!(root.get("appl"), Some(&99));
    }

    #[test]
    fn test_insert_with_or_modify_vec() {
        let mut root: Node<Vec<u32>> = Node::root();

        // insert() a new key
        root.entry("counts")
            .and_modify(|_| panic!("modified"))
            .or_insert_with(
                || vec![0], // Create a new vector with one element.
            );
        assert_eq!(root.get("counts"), Some(&vec![0]));

        // modify() the existing key
        root.entry("counts")
            .and_modify(|v| v.push(1))
            .or_insert_with(|| panic!("insert should not be called on modify"));
        assert_eq!(root.get("counts"), Some(&vec![0, 1]));

        // modify()
        root.entry("counts")
            .and_modify(|v| {
                v.push(2);
            })
            .or_insert_with(|| panic!("insert should not be called on modify"));
        // created with 0 then pushed 1, 2
        assert_eq!(root.get("counts"), Some(&vec![0, 1, 2]));
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

        let mut root = Node::root();
        // Insert test key
        assert_eq!(root.insert("b", 1), None);
        assert_eq!(root.insert("a", 1), None);
        assert_eq!(root.insert("z", 1), None);
        assert_eq!(root.children()[0].label(), b"a");
        assert_eq!(root.children()[1].label(), b"b");
        assert_eq!(root.children()[2].label(), b"z");

        let mut root = Node::root();
        // Insert test key
        assert_eq!(root.insert("b", 1), None);
        assert_eq!(root.insert("aa", 1), None);
        assert_eq!(root.insert("z", 1), None);
        assert_eq!(root.children()[0].label(), b"aa");
        assert_eq!(root.children()[1].label(), b"b");
        assert_eq!(root.children()[2].label(), b"z");

        let mut root = Node::root();
        // Insert test key
        assert_eq!(root.insert("z", 1), None);
        assert_eq!(root.insert("b", 1), None);
        assert_eq!(root.insert("a", 1), None);
        assert_eq!(root.insert("a", 2), Some(1));
        assert_eq!(root.children()[0].label(), b"a");
        assert_eq!(root.children()[0].value(), Some(&2));
        assert_eq!(root.children()[1].label(), b"b");
        assert_eq!(root.children()[2].label(), b"z");

        let mut root = Node::root();
        // Insert test key
        assert_eq!(root.insert("z", 1), None);
        assert_eq!(root.insert("b", 1), None);
        assert_eq!(root.insert("a", 1), None);
        assert_eq!(root.children()[0].label(), b"a");
        assert_eq!(root.children()[1].label(), b"b");
        assert_eq!(root.children()[2].label(), b"z");
    }

    #[test]
    fn test_children_push_full() {
        let mut node = Node::root();

        for i in 0..255_u8 {
            node.insert(&i.to_be_bytes()[..], i);
        }

        assert_eq!(node.children().len(), 255);
        for i in 0..255u8 {
            assert_eq!(
                node.children()[i as usize].label(),
                i.to_be_bytes().as_slice()
            );
        }
    }

    #[test]
    fn test_insert_static_size() {
        let mut node = Node::root();

        let label = [b'0'; 35];
        node.insert(&label, 1);

        assert_eq!(node.get(&label), Some(&1));
    }

    #[test]
    fn test_insert_long_label() {
        let mut node = Node::root();

        // insert 000...00000
        let label = [b'0'; 260];
        node.insert(&label[..], 1);

        assert_eq!(node.get(&label[..]), Some(&1));
        node.insert("1", 2);
        assert_eq!(node.get("1"), Some(&2));
        node.insert("2", 3);
        assert_eq!(node.get("2"), Some(&3));

        // insert 000...11111
        let mut label = [b'0'; 255].to_vec();
        label.extend(b"11111");
        node.insert(&label[..], 4);
        assert_eq!(node.get(label.as_slice()), Some(&4));

        let label = [b'1'; 240];
        node.insert(&label[..], 5);
        assert_eq!(node.get(&label), Some(&5));
        assert_eq!(node.get("1"), Some(&2));

        let label = [b'1'; 260];
        node.insert(&label[..], 6);
        assert_eq!(node.get(&[b'1'; 240]), Some(&5));
        assert_eq!(node.get(&label), Some(&6));
        assert_eq!(node.get("1"), Some(&2));

        // 240 - 1 = 239
        assert_eq!(node.get_node(&[b'1'; 240]).unwrap().label_len(), 239);
        // 260 - 240 = 20
        assert_eq!(node.get_node(&label).unwrap().label_len(), 20);

        assert_eq!(node.remove(&label[..]), Some(6));
        assert_eq!(node.remove(&[b'1'; 240]), Some(5));
        dbg!(&node);
    }

    #[test]
    fn test_insert_partial_prefix_match_and_long_suffix_label() {
        let mut node = Node::root();

        // insert 000...0 with length 10.
        let label = [b'0'; 10];

        node.insert(&label[..], 1);
        assert_eq!(node.get(&label[..]), Some(&1));

        // insert 000...1111 sharing first 5 bytes and spanning > 255 bytes of suffix.
        let mut label = [b'0'; 5].to_vec();
        label.extend(b"1".repeat(300));

        node.insert(&label[..], 2);
        assert_eq!(node.get(label.as_slice()), Some(&2));
        dbg!(&node);
    }

    #[test]
    fn test_insert_total_prefix_match_and_long_suffix_label() {
        let mut node = Node::root();

        // insert 000...0 with length 10.
        let label = [b'0'; 10];

        node.insert(&label[..], 1);
        assert_eq!(node.get(&label[..]), Some(&1));

        // insert 000...1111 with 1s suffix extending after the original 10 bytes.
        let mut label = [b'0'; 10].to_vec();
        label.extend(b"1".repeat(300));

        node.insert(&label[..], 2);
        assert_eq!(node.get(label.as_slice()), Some(&2));
        dbg!(&node);
    }

    #[test]
    fn test_insert_double_long_label() {
        let mut node = Node::root();

        let label = [b'3'; 560];
        node.insert(&label[..], 3);

        assert_eq!(node.get(&label[..]), Some(&3));
        node.insert("1", 1);
        assert_eq!(node.get("1"), Some(&1));
        node.insert("2", 2);
        assert_eq!(node.get("2"), Some(&2));
    }

    // Two long labels that share no common prefix — each becomes an independent chain.
    #[test]
    fn test_two_disjoint_long_labels() {
        let mut node = Node::root();
        let a = [b'a'; 300];
        let b = [b'b'; 300];
        node.insert(&a[..], 1);
        node.insert(&b[..], 2);
        assert_eq!(node.get(&a[..]), Some(&1));
        assert_eq!(node.get(&b[..]), Some(&2));
        // removing one leaves the other intact
        assert_eq!(node.remove(&a[..]), Some(1));
        assert_eq!(node.get(&a[..]), None);
        assert_eq!(node.get(&b[..]), Some(&2));
    }

    // Two long labels that share a long common prefix (>255 bytes) before diverging.
    #[test]
    fn test_long_shared_prefix_long_suffixes() {
        let mut node = Node::root();
        // shared: 'x' * 260, then diverge
        let mut a = [b'x'; 260].to_vec();
        a.extend(b"aaa");
        let mut b = [b'x'; 260].to_vec();
        b.extend(b"bbb");

        node.insert(&a[..], 1);
        node.insert(&b[..], 2);
        assert_eq!(node.get(&a[..]), Some(&1));
        assert_eq!(node.get(&b[..]), Some(&2));
        assert_eq!(node.remove(&a[..]), Some(1));
        assert_eq!(node.get(&a[..]), None);
        assert_eq!(node.get(&b[..]), Some(&2));
    }

    // Replace the value of an existing long-label key.
    #[test]
    fn test_overwrite_long_label() {
        let mut node = Node::root();
        let label = [b'z'; 510];
        node.insert(&label[..], 1);
        assert_eq!(node.insert(&label[..], 2), Some(1));
        assert_eq!(node.get(&label[..]), Some(&2));
        dbg!(&node);
    }

    // Insert a short key that is a prefix of a long key, and vice versa.
    #[test]
    fn test_short_prefix_of_long_label() {
        let mut node = Node::root();
        let short = [b'p'; 10];
        let mut long = [b'p'; 10].to_vec();
        long.extend(b"q".repeat(300));

        node.insert(&short[..], 1);
        node.insert(&long[..], 2);
        assert_eq!(node.get(&short[..]), Some(&1));
        assert_eq!(node.get(&long[..]), Some(&2));

        // inserting another long sibling under the same short prefix
        let mut long2 = [b'p'; 10].to_vec();
        long2.extend(b"r".repeat(300));
        node.insert(&long2[..], 3);
        assert_eq!(node.get(&long2[..]), Some(&3));
        assert_eq!(node.get(&short[..]), Some(&1));
        assert_eq!(node.get(&long[..]), Some(&2));
        dbg!(&node);
    }

    // Three-chunk chain: label length > 2 * MAX_LABEL_LEN (>510 bytes).
    #[test]
    fn test_triple_chunk_long_label() {
        let mut node = Node::root();
        let label = [b'k'; 700];
        node.insert(&label[..], 42);
        assert_eq!(node.get(&label[..]), Some(&42));
        assert_eq!(node.remove(&label[..]), Some(42));
        assert_eq!(node.get(&label[..]), None);
        dbg!(&node);
    }

    // entry() API with a long-label key that needs chaining.
    #[test]
    fn test_entry_long_label() {
        let mut node = Node::root();
        let label = [b'm'; 600];
        node.entry(&label[..]).or_insert(99);
        assert_eq!(node.get(&label[..]), Some(&99));

        // calling entry again on the same key returns Occupied
        *node.entry(&label[..]).or_insert(0) = 100;
        assert_eq!(node.get(&label[..]), Some(&100));
        dbg!(&node);
    }

    // entry() with a partial-prefix-match long suffix.
    #[test]
    fn test_entry_partial_prefix_long_suffix() {
        let mut node = Node::root();
        let short = [b'e'; 5];
        node.insert(&short[..], 1);

        let mut long = [b'e'; 5].to_vec();
        long.extend(b"f".repeat(300));
        node.entry(&long[..]).or_insert(2);
        assert_eq!(node.get(&short[..]), Some(&1));
        assert_eq!(node.get(&long[..]), Some(&2));
    }

    #[test]
    #[should_panic]
    fn test_children_push_more_than_255_items() {
        let mut node = Node::root();
        for i in 0..=255_u8 {
            node.insert(&i.to_be_bytes()[..], i);
        }
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
        dbg!(&root);
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

    // modified test from patricia_tree suite
    #[test]
    fn long_label_works() {
        let mut root = Node::root();
        root.insert(&[b'a'; 256][..], 10);
        assert_eq!(root.children()[0].label(), &[b'a'; 255][..]);
        assert_eq!(root.children()[0].value(), None);
        assert!(!root.children()[0].children().is_empty());

        let child = &root.children()[0].children()[0];
        assert_eq!(child.label(), b"a");
        assert_eq!(child.value(), Some(&10));
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
    fn test_root() {
        // test creation of new root where nothing matches
        let mut root = Node::new(b"notfoobar", [], Some(1));
        root.insert(b"foobar", 1);
        // makes child "baz" under "foobar"
        root.insert(b"foobarbaz", 3);
        assert_eq!(root.label_len(), 0);
        assert_eq!(root.children()[0].label(), b"foobar");
        assert_eq!(root.children()[1].label(), b"notfoobar");
    }

    #[test]
    fn test_split_by_prefix() {
        let mut root = create_bigger_test_tree();

        let mut map = RadixMap::from_node(root.clone());
        let other = map.split_by_prefix("ap");
        dbg!(&map);
        dbg!(&other);

        let other = root.split_by_prefix("ap").unwrap();
        dbg!(&root);
        dbg!(&other);
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

        assert_eq!(root.get_prefix_node("b"), None);
        assert_eq!(root.get_prefix_node("b0"), None);
        assert_eq!(root.get_prefix_node("a0").unwrap().1.value().unwrap(), &1);
        assert_eq!(root.get_prefix_node("a0").unwrap().0, 1);
        assert_eq!(root.get_prefix_node("a0/b1"), None);
        assert_eq!(root.get_prefix_node("a1/").unwrap().1.value().unwrap(), &2);
        assert_eq!(root.get_prefix_node("a1/").unwrap().0, 2);
        assert_eq!(root.get_prefix_node("a1/b").unwrap().1.value().unwrap(), &2);
        assert_eq!(root.get_prefix_node("a1/b").unwrap().0, 3);
        assert_eq!(root.get_prefix_node("a1/b2"), None);

        let mut root = Node::root();
        root.insert("foo", 1);
        root.insert("bar", 2);
        root.insert("baz", 3);
        assert_eq!(root.get_prefix_node("bax"), None);
    }

    #[test]
    fn test_issue42_split_by() {
        let create = || {
            let mut root = Node::root();
            root.insert("a0/b0", 1);
            root.insert("a1/b1", 2);
            root
        };

        let mut root = create();
        assert_eq!(root.split_by_prefix("b"), None);
        let mut root = create();
        assert_eq!(root.split_by_prefix("b0"), None);

        let mut root = create();
        assert_eq!(root.split_by_prefix("a0").unwrap().value().unwrap(), &1);

        let mut root = create();
        assert_eq!(root.split_by_prefix("a0/b1"), None);

        let mut root = create();
        assert_eq!(root.split_by_prefix("a1/").unwrap().value().unwrap(), &2);
        let mut root = create();
        assert_eq!(root.split_by_prefix("a1/b").unwrap().value().unwrap(), &2);
        let mut root = create();
        assert_eq!(root.split_by_prefix("a1/b2"), None);

        let mut root = Node::root();
        root.insert("foo", 1);
        root.insert("bar", 2);
        root.insert("baz", 3);
        assert_eq!(root.split_by_prefix("bax"), None);
        assert_eq!(root.split_by_prefix("baxx"), None);
        assert_eq!(root.split_by_prefix("x"), None);
        assert_eq!(root.split_by_prefix("f").unwrap().value().unwrap(), &1);
    }

    #[test]
    fn get_longest_common_prefix() {
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
    fn get_longest_common_prefix_mut() {
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

    #[test]
    fn wildcard_parse() {
        // literal
        assert_eq!(
            WildcardFilter::parse(b"foo"),
            vec![Pattern::Literal(b"foo")]
        );

        // *
        assert_eq!(
            WildcardFilter::parse(b"foo.*.com"),
            vec![
                Pattern::Literal(b"foo."),
                Pattern::Any,
                Pattern::Literal(b".com")
            ]
        );

        // ?
        assert_eq!(
            WildcardFilter::parse(b"ba?.txt"),
            vec![
                Pattern::Literal(b"ba"),
                Pattern::One,
                Pattern::Literal(b".txt")
            ]
        );

        // multiple wildcards
        assert_eq!(
            WildcardFilter::parse(b"*.*"),
            vec![Pattern::Any, Pattern::Literal(b"."), Pattern::Any]
        );

        // multiple consecutive * should collapse to single Any
        assert_eq!(
            WildcardFilter::parse(b"foo.**.com"),
            vec![
                Pattern::Literal(b"foo."),
                Pattern::Any,
                Pattern::Literal(b".com")
            ]
        );

        assert_eq!(
            WildcardFilter::parse(b"foo.****bar"),
            vec![
                Pattern::Literal(b"foo."),
                Pattern::Any,
                Pattern::Literal(b"bar")
            ]
        );

        // mixed wildcards
        assert_eq!(
            WildcardFilter::parse(b"f?o.*.???.com"),
            vec![
                Pattern::Literal(b"f"),
                Pattern::One,
                Pattern::Literal(b"o."),
                Pattern::Any,
                Pattern::Literal(b"."),
                Pattern::One,
                Pattern::One,
                Pattern::One,
                Pattern::Literal(b".com")
            ]
        );

        // pattern starting with wildcard
        assert_eq!(
            WildcardFilter::parse(b"*.com"),
            vec![Pattern::Any, Pattern::Literal(b".com")]
        );

        // pattern ending with wildcard
        assert_eq!(
            WildcardFilter::parse(b"foo.*"),
            vec![Pattern::Literal(b"foo."), Pattern::Any]
        );

        // only wildcards
        assert_eq!(
            // ** -> *
            // *? -> ?*
            // ?** -> ?*
            WildcardFilter::parse(b"**?*"),
            vec![Pattern::One, Pattern::Any]
        );

        // *?? changes to ??*
        assert_eq!(
            WildcardFilter::parse(b"foo.*??.com"),
            vec![
                Pattern::Literal(b"foo."),
                Pattern::One,
                Pattern::One,
                Pattern::Any,
                Pattern::Literal(b".com")
            ]
        );

        // *??? changes to ???*
        assert_eq!(
            WildcardFilter::parse(b"foo.*???.com"),
            vec![
                Pattern::Literal(b"foo."),
                Pattern::One,
                Pattern::One,
                Pattern::One,
                Pattern::Any,
                Pattern::Literal(b".com")
            ]
        );

        // *?*? changes to ??*
        assert_eq!(
            WildcardFilter::parse(b"foo.*?*?.com"),
            vec![
                Pattern::Literal(b"foo."),
                Pattern::One,
                Pattern::One,
                Pattern::Any,
                Pattern::Literal(b".com")
            ]
        );
    }

    #[test]
    fn wildcard_iter_works() {
        let mut set = RadixSet::new();
        set.insert("foo.bar.com");
        set.insert("foo.baz.com");
        set.insert("foo.qux.com");
        set.insert("hello.world");
        set.insert("hello.rust");
        set.insert("test");
        set.insert("foobar");

        // matches zero or more characters
        let matches: Vec<_> = set
            .wildcard_iter(b"foo.*.com")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 3);
        assert!(matches.contains(&"foo.bar.com".to_string()));
        assert!(matches.contains(&"foo.baz.com".to_string()));
        assert!(matches.contains(&"foo.qux.com".to_string()));

        // matches zero chars
        let matches: Vec<_> = set
            .wildcard_iter(b"foo.bar*.com")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 1);
        assert!(matches.contains(&"foo.bar.com".to_string()));

        // matches single character
        let matches: Vec<_> = set
            .wildcard_iter(b"foo.ba?.com")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 2);
        assert!(matches.contains(&"foo.bar.com".to_string()));
        assert!(matches.contains(&"foo.baz.com".to_string()));

        // ending *
        let matches: Vec<_> = set
            .wildcard_iter(b"foo.*")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 3);
        assert!(matches.contains(&"foo.bar.com".to_string()));
        assert!(matches.contains(&"foo.baz.com".to_string()));
        assert!(matches.contains(&"foo.qux.com".to_string()));

        let matches: Vec<_> = set
            .wildcard_iter(b"hello.*")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 2);
        assert!(matches.contains(&"hello.world".to_string()));
        assert!(matches.contains(&"hello.rust".to_string()));

        // exact match
        let matches: Vec<_> = set
            .wildcard_iter(b"test")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches, vec!["test"]);

        // no matches
        let matches: Vec<_> = set
            .wildcard_iter(b"nonexistent.*")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 0);

        // * at beginning
        let matches: Vec<_> = set
            .wildcard_iter(b"*.com")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 3);

        // multiple *
        let matches: Vec<_> = set
            .wildcard_iter(b"*.*")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 5);

        // ? with multiple positions
        let matches: Vec<_> = set
            .wildcard_iter(b"foo???")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches, vec!["foobar"]);
    }

    #[test]
    fn wildcard_parse_escaped() {
        assert_eq!(WildcardFilter::parse(b"\\*"), vec![Pattern::Literal(b"*")]);

        assert_eq!(WildcardFilter::parse(b"\\?"), vec![Pattern::Literal(b"?")]);

        // escaped wildcard followed by literal chars
        assert_eq!(
            WildcardFilter::parse(b"\\*foo"),
            vec![Pattern::Literal(b"*foo")]
        );

        // mix: literal prefix, escaped *, literal suffix
        assert_eq!(
            WildcardFilter::parse(b"foo.\\*.com"),
            vec![Pattern::Literal(b"foo."), Pattern::Literal(b"*.com")]
        );
    }

    #[test]
    fn wildcard_iter_escaped() {
        let mut set = RadixSet::new();
        set.insert("foo.*.com");
        set.insert("foo.bar.com");
        set.insert("foo.?.com");

        let matches: Vec<_> = set
            .wildcard_iter(b"foo.\\*.com")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches, vec!["foo.*.com"]);

        let matches: Vec<_> = set
            .wildcard_iter(b"foo.*.com")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches.len(), 3);

        let matches: Vec<_> = set
            .wildcard_iter(b"foo.\\?.com")
            .map(|k| String::from_utf8(k).unwrap())
            .collect();
        assert_eq!(matches, vec!["foo.?.com"]);
    }

    #[test]
    fn wildcard_iter_calling_conventions() {
        use crate::StringRadixSet;

        let mut byte_set = RadixSet::new();
        byte_set.insert("foo.bar.com");
        byte_set.insert("foo.baz.com");
        byte_set.insert("hello.world");

        // byte literal, coerces with AsRef
        let matches: Vec<_> = byte_set.wildcard_iter(b"foo.*.com").collect();
        assert_eq!(matches.len(), 2);

        // &[u8] slice reference
        let pattern: &[u8] = b"foo.*.com";
        let matches: Vec<_> = byte_set.wildcard_iter(pattern).collect();
        assert_eq!(matches.len(), 2);

        // str impls AsRef<[u8]>
        let matches: Vec<_> = byte_set.wildcard_iter("foo.*.com").collect();
        assert_eq!(matches.len(), 2);

        // &String, impls AsRef<[u8]>
        let owned = String::from("foo.*.com");
        let matches: Vec<_> = byte_set.wildcard_iter(&owned).collect();
        assert_eq!(matches.len(), 2);

        // &Vec<u8> impls AsRef<[u8]>
        let owned_bytes = b"foo.*.com".to_vec();
        let matches: Vec<_> = byte_set.wildcard_iter(&owned_bytes).collect();
        assert_eq!(matches.len(), 2);

        // StringRadixSet
        let mut str_set = StringRadixSet::new();
        str_set.insert("foo.bar.com");
        str_set.insert("foo.baz.com");
        str_set.insert("hello.world");

        // str implements AsRef<str>
        let matches: Vec<_> = str_set.wildcard_iter("foo.*.com").collect();
        assert_eq!(matches.len(), 2);

        // &String — String implements AsRef<str>
        let owned_str = String::from("foo.*.com");
        let matches: Vec<_> = str_set.wildcard_iter(&owned_str).collect();
        assert_eq!(matches.len(), 2);

        // RadixMap calling conventions
        let mut map = RadixMap::new();
        map.insert("foo.bar.com", 1u32);
        map.insert("foo.baz.com", 2u32);
        map.insert("hello.world", 3u32);

        let matches: Vec<_> = map.wildcard_iter(b"foo.*.com").collect();
        assert_eq!(matches.len(), 2);

        let matches: Vec<_> = map.wildcard_iter("foo.*.com").collect();
        assert_eq!(matches.len(), 2);

        // StringRadixMap calling conventions
        let mut str_map = StringRadixMap::new();
        str_map.insert("foo.bar.com", 1u32);
        str_map.insert("foo.baz.com", 2u32);
        str_map.insert("hello.world", 3u32);

        // str
        let matches: Vec<_> = str_map.wildcard_iter("foo.*.com").collect();
        assert_eq!(matches.len(), 2);

        // &String
        let matches: Vec<_> = str_map.wildcard_iter(&owned_str).collect();
        assert_eq!(matches.len(), 2);
    }
}
