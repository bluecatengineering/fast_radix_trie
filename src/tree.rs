use core::fmt;

use alloc::vec::Vec;

use crate::{
    BorrowedBytes, Bytes, entry,
    node::Node,
    node_common::{self, NodeMut},
};

#[derive(Clone)]
pub struct RadixTrie<V> {
    root: Node<V>,
    len: usize,
}

impl<V: fmt::Debug> fmt::Debug for RadixTrie<V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("RadixTrie")
            .field("root", &self.root)
            .field("len", &self.len)
            .finish()
    }
}

impl<V> RadixTrie<V> {
    pub fn new() -> Self {
        RadixTrie {
            root: Node::root(),
            len: 0,
        }
    }
    pub(crate) fn root(&self) -> &Node<V> {
        &self.root
    }
    pub(crate) fn into_root(self) -> Node<V> {
        self.root
    }
    pub fn insert<K: ?Sized + BorrowedBytes>(&mut self, key: &K, value: V) -> Option<V> {
        if let Some(old) = self.root.insert(key, value) {
            Some(old)
        } else {
            self.len += 1;
            None
        }
    }

    pub fn entry<K>(&mut self, key: &K) -> Entry<'_, V>
    where
        K: ?Sized + BorrowedBytes,
    {
        match self.root.entry(key) {
            entry::Entry::Occupied(entry) => Entry::Occupied(OccupiedEntry { inner: entry }),
            entry::Entry::Vacant(entry) => Entry::Vacant(VacantEntry {
                inner: entry,
                len: &mut self.len,
            }),
        }
    }

    pub fn get<K: ?Sized + BorrowedBytes>(&self, key: &K) -> Option<&V> {
        self.root.get(key)
    }
    pub fn get_mut<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<&mut V> {
        self.root.get_mut(key)
    }
    pub fn split_by_prefix<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Self {
        match self.root.split_by_prefix(key) {
            Some(node) => {
                let new_root = Node::new(b"", [node], None);
                let split = Self::from(new_root);
                self.len -= split.len();
                split
            }
            None => Self::new(),
        }
    }
    pub fn longest_common_prefix_len<K: ?Sized + BorrowedBytes>(&self, key: &K) -> usize {
        self.root.longest_common_prefix_len(key)
    }
    pub fn get_longest_common_prefix<'a, K: ?Sized + BorrowedBytes>(
        &self,
        key: &'a K,
    ) -> Option<(&'a [u8], &V)> {
        self.root
            .get_longest_common_prefix(key)
            .and_then(|(n, v)| Some((&key.as_bytes()[..n], v.value()?)))
    }
    pub fn get_longest_common_prefix_mut<'a, K: ?Sized + BorrowedBytes>(
        &mut self,
        key: &'a K,
    ) -> Option<(&'a [u8], &mut V)> {
        self.root
            .get_longest_common_prefix_mut(key)
            .and_then(|(n, v)| Some((&key.as_bytes()[..n], v.value_mut()?)))
    }
    pub fn iter_prefix<K: ?Sized + BorrowedBytes>(
        &self,
        prefix: &K,
    ) -> Option<(usize, Nodes<'_, V>)> {
        if let Some((common_len, node)) = self.root.get_prefix_node(prefix) {
            let nodes = Nodes {
                nodes: node.iter(),
                label_lens: Vec::new(),
            };
            Some((prefix.as_bytes().len() - common_len, nodes))
        } else {
            None
        }
    }
    pub fn iter_prefix_mut<K: ?Sized + BorrowedBytes>(
        &mut self,
        prefix: &K,
    ) -> Option<(usize, NodesMut<'_, V>)> {
        if let Some((common_len, node)) = self.root.get_prefix_node_mut(prefix) {
            let nodes = NodesMut {
                nodes: node.iter_mut(),
                label_lens: Vec::new(),
            };
            Some((prefix.as_bytes().len() - common_len, nodes))
        } else {
            None
        }
    }
    pub(crate) fn common_prefixes<'a, 'b, K>(
        &'a self,
        key: &'b K,
    ) -> node_common::CommonPrefixesIter<'a, 'b, K, V>
    where
        K: ?Sized + BorrowedBytes,
    {
        self.root.common_prefixes(key)
    }
    pub(crate) fn common_prefixes_owned<K>(
        &self,
        key: K,
    ) -> node_common::CommonPrefixesIterOwned<'_, K, V>
    where
        K: Bytes + AsRef<K::Borrowed>,
    {
        self.root.common_prefixes_owned(key)
    }
    pub fn remove<K: ?Sized + BorrowedBytes>(&mut self, key: &K) -> Option<V> {
        if let Some(old) = self.root.remove(key) {
            self.len -= 1;
            Some(old)
        } else {
            None
        }
    }
    pub fn clear(&mut self) {
        self.root = Node::root();
        self.len = 0;
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn nodes(&self) -> Nodes<'_, V> {
        Nodes {
            nodes: self.root.iter(),
            label_lens: Vec::new(),
        }
    }
    pub fn nodes_mut(&mut self) -> NodesMut<'_, V> {
        NodesMut {
            nodes: self.root.iter_mut(),
            label_lens: Vec::new(),
        }
    }
    pub fn wildcard_nodes<'a, 'b, K: ?Sized + BorrowedBytes>(
        &'a self,
        pattern: &'b K,
    ) -> WildcardNodes<'a, 'b, V> {
        WildcardNodes {
            nodes: self.root.wildcard_iter(pattern),
        }
    }
    pub fn into_nodes(self) -> IntoNodes<V> {
        IntoNodes {
            nodes: self.root.into_iter(),
            label_lens: Vec::new(),
        }
    }
}
impl<V> Default for RadixTrie<V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<V> From<Node<V>> for RadixTrie<V> {
    fn from(f: Node<V>) -> Self {
        let mut this = RadixTrie { root: f, len: 0 };
        let count = this.nodes().filter(|n| n.1.value().is_some()).count();
        this.len = count;
        this
    }
}

#[derive(Debug)]
pub struct Nodes<'a, V: 'a> {
    nodes: node_common::Iter<'a, V>,
    label_lens: Vec<usize>,
}
impl<'a, V: 'a> Iterator for Nodes<'a, V> {
    type Item = (usize, &'a Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.nodes.next() {
            self.label_lens.resize(level + 1, 0);
            self.label_lens[level] = node.label().len();
            let parent_key_len = self.label_lens.iter().take(level).sum();
            Some((parent_key_len, node))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct WildcardNodes<'a, 'b, V: 'a> {
    nodes: node_common::WildcardIter<'a, 'b, V>,
}

impl<'a, 'b, V: 'a> Iterator for WildcardNodes<'a, 'b, V> {
    type Item = node_common::WildcardMatch<'a, V>;
    fn next(&mut self) -> Option<Self::Item> {
        self.nodes.next()
    }
}

#[derive(Debug)]
pub struct NodesMut<'a, V: 'a> {
    nodes: node_common::IterMut<'a, V>,
    label_lens: Vec<usize>,
}
impl<'a, V: 'a> Iterator for NodesMut<'a, V> {
    type Item = (usize, NodeMut<'a, V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.nodes.next() {
            self.label_lens.resize(level + 1, 0);
            self.label_lens[level] = node.label().len();

            let parent_key_len = self.label_lens.iter().take(level).sum();
            Some((parent_key_len, node))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct IntoNodes<V> {
    nodes: node_common::IntoIter<V>,
    label_lens: Vec<usize>,
}

impl<V> Iterator for IntoNodes<V> {
    type Item = (usize, Node<V>);
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((level, node)) = self.nodes.next() {
            self.label_lens.resize(level + 1, 0);
            self.label_lens[level] = node.label().len();
            let parent_key_len = self.label_lens.iter().take(level).sum();
            Some((parent_key_len, node))
        } else {
            None
        }
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the `entry` method on `RadixTrie`.
pub enum Entry<'a, V: 'a> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, V>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, V>),
}

/// A view into an occupied entry in a `RadixTrie`.
/// It is part of the `Entry` enum.
pub struct OccupiedEntry<'a, V: 'a> {
    pub(crate) inner: entry::OccupiedEntry<'a, V>,
}

impl<'a, V: 'a> OccupiedEntry<'a, V> {
    /// Gets a reference to the value in the entry
    pub fn get(&self) -> &V {
        // An occupied entry always has a value.
        self.inner.node.value().unwrap()
    }

    /// Gets a mutable reference to the value in the entry
    pub fn get_mut(&mut self) -> &mut V {
        self.inner.node.value_mut().unwrap()
    }
}

/// A view into a vacant entry in a `RadixTrie`.
/// It is part of the `Entry` enum.
pub struct VacantEntry<'a, V: 'a> {
    pub(crate) inner: entry::VacantEntry<'a, V>,
    /// A mutable reference to the trie's length, to be updated on insertion.
    pub(crate) len: &'a mut usize,
}

impl<'a, V: 'a> VacantEntry<'a, V> {
    /// Sets the value for the entry and returns a mutable reference to it.
    ///
    /// This increments the `RadixTrie`'s length.
    pub fn insert(self, value: V) -> &'a mut V {
        // Increment the trie's length.
        *self.len += 1;
        // Insert the value into the underlying node.
        self.inner.insert(value)
    }
}

// You can also implement `or_insert`, `and_modify`, etc. on the new `Entry` enum.
impl<'a, V: 'a> Entry<'a, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.inner.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.inner.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Provides in-place mutable access to an occupied entry.
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.inner.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_entry_api() {
        let mut tree = RadixTrie::new();

        // Test `or_insert` on a vacant entry
        let val = tree.entry("a").or_insert(10);
        assert_eq!(*val, 10);
        assert_eq!(tree.len(), 1);
        assert_eq!(tree.get("a"), Some(&10));

        // Test `or_insert` on an occupied entry
        let val = tree.entry("a").or_insert(99); // Should not insert
        assert_eq!(*val, 10); // Returns reference to existing value

        // Modify through the returned reference
        *val = 11;

        assert_eq!(tree.len(), 1); // Length does not change
        assert_eq!(tree.get("a"), Some(&11));

        // Test `or_insert_with` on a vacant entry
        let mut closure_called = false;
        tree.entry("b").or_insert_with(|| {
            closure_called = true;
            20
        });
        assert!(closure_called);
        assert_eq!(tree.len(), 2);
        assert_eq!(tree.get("b"), Some(&20));

        // Test `or_insert_with` on an occupied entry
        tree.entry("b")
            .or_insert_with(|| panic!("closure should not be called"));
        assert_eq!(tree.len(), 2);

        // Test `and_modify` on an occupied entry
        let mut modify_closure_called = false;
        tree.entry("b").and_modify(|v| {
            *v += 5;
            modify_closure_called = true;
        });
        assert!(modify_closure_called);
        assert_eq!(tree.get("b"), Some(&25));

        // Test `and_modify` on a vacant entry
        tree.entry("c")
            .and_modify(|_| panic!("closure should not be called"));

        // Test chaining `and_modify` and `or_insert`
        // On an occupied entry:
        tree.entry("b").and_modify(|v| *v = 30).or_insert(99); // This part is ignored
        assert_eq!(tree.get("b"), Some(&30));
        assert_eq!(tree.len(), 2);

        // On a vacant entry:
        tree.entry("c")
            .and_modify(|_| panic!("closure should not be called"))
            .or_insert(40); // This part is executed
        assert_eq!(tree.get("c"), Some(&40));
        assert_eq!(tree.len(), 3);
    }

    #[test]
    fn it_works() {
        let mut tree = RadixTrie::new();
        assert_eq!(tree.insert("".as_bytes(), 1), None);
        assert_eq!(tree.insert("".as_bytes(), 2), Some(1));

        assert_eq!(tree.insert("foo".as_bytes(), 3), None);
        assert_eq!(tree.insert("foo".as_bytes(), 4), Some(3));

        assert_eq!(tree.insert("foobar".as_bytes(), 5), None);

        assert_eq!(tree.insert("bar".as_bytes(), 6), None);
        assert_eq!(tree.insert("baz".as_bytes(), 7), None);

        assert_eq!(tree.insert("bar".as_bytes(), 7), Some(6));
        assert_eq!(tree.insert("baz".as_bytes(), 8), Some(7));

        assert_eq!(tree.get("".as_bytes()), Some(&2));
        assert_eq!(tree.get("foo".as_bytes()), Some(&4));
        assert_eq!(tree.get("foobar".as_bytes()), Some(&5));
        assert_eq!(tree.get("bar".as_bytes()), Some(&7));
        assert_eq!(tree.get("baz".as_bytes()), Some(&8));
        assert_eq!(tree.get("qux".as_bytes()), None);

        let tree2 = tree.clone();
        assert_eq!(tree2.get("".as_bytes()), Some(&2));
        assert_eq!(tree2.get("foo".as_bytes()), Some(&4));
        assert_eq!(tree2.get("foobar".as_bytes()), Some(&5));
        assert_eq!(tree2.get("bar".as_bytes()), Some(&7));
        assert_eq!(tree2.get("baz".as_bytes()), Some(&8));

        assert_eq!(tree.remove("".as_bytes()), Some(2));
        assert_eq!(tree.remove("foo".as_bytes()), Some(4));
        assert_eq!(tree.remove("foobar".as_bytes()), Some(5));
        assert_eq!(tree.remove("bar".as_bytes()), Some(7));
        assert_eq!(tree.remove("baz".as_bytes()), Some(8));
        assert_eq!(tree.remove("qux".as_bytes()), None);

        assert_eq!(tree.get("".as_bytes()), None);
        assert_eq!(tree.get("foo".as_bytes()), None);
        assert_eq!(tree.get("foobar".as_bytes()), None);
        assert_eq!(tree.get("bar".as_bytes()), None);
        assert_eq!(tree.get("baz".as_bytes()), None);
        assert_eq!(tree.get("qux".as_bytes()), None);

        assert_eq!(tree2.get("".as_bytes()), Some(&2));
        assert_eq!(tree2.get("foo".as_bytes()), Some(&4));
        assert_eq!(tree2.get("foobar".as_bytes()), Some(&5));
        assert_eq!(tree2.get("bar".as_bytes()), Some(&7));
        assert_eq!(tree2.get("baz".as_bytes()), Some(&8));
    }
}
