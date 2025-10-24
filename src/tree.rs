use core::fmt;

use alloc::vec::Vec;

use crate::{
    BorrowedBytes, Bytes,
    node::Node,
    node_common::{self, NodeMut},
};

#[derive(Clone)]
pub struct RadixTree<V> {
    root: Node<V>,
    len: usize,
}

impl<V: fmt::Debug> fmt::Debug for RadixTree<V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("RadixTree")
            .field("root", &self.root)
            .field("len", &self.len)
            .finish()
    }
}

impl<V> RadixTree<V> {
    pub fn new() -> Self {
        RadixTree {
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
        self.root
            .get_longest_common_prefix(key)
            .map(|(len, _)| len)
            .unwrap_or(0)
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
        if let Some(node) = self.root.get_node(prefix) {
            let nodes = Nodes {
                nodes: node.iter(),
                label_lens: Vec::new(),
            };
            Some((prefix.as_bytes().len() - node.label_len(), nodes))
        } else {
            None
        }
    }
    pub fn iter_prefix_mut<K: ?Sized + BorrowedBytes>(
        &mut self,
        prefix: &K,
    ) -> Option<(usize, NodesMut<'_, V>)> {
        if let Some(node) = self.root.get_node_mut(prefix) {
            let len = node.label_len();
            let nodes = NodesMut {
                nodes: node.iter_mut(),
                label_lens: Vec::new(),
            };
            Some((prefix.as_bytes().len() - len, nodes))
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
    pub fn into_nodes(self) -> IntoNodes<V> {
        IntoNodes {
            nodes: self.root.into_iter(),
            label_lens: Vec::new(),
        }
    }
}
impl<V> Default for RadixTree<V> {
    fn default() -> Self {
        Self::new()
    }
}
impl<V> From<Node<V>> for RadixTree<V> {
    fn from(f: Node<V>) -> Self {
        let mut this = RadixTree { root: f, len: 0 };
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

#[cfg(test)]
mod tests {
    use super::*;

    // this test is copied from the old library, there is an important
    // difference in how the new code handles the root node.
    // it's not recommended to insert/remove values at ""
    #[test]
    fn it_works() {
        let mut tree = RadixTree::new();
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

        // old library difference. You can't remove root node anymore!
        // assert_eq!(tree.remove("".as_bytes()), Some(2));
        assert_eq!(tree.remove("foo".as_bytes()), Some(4));
        assert_eq!(tree.remove("foobar".as_bytes()), Some(5));
        assert_eq!(tree.remove("bar".as_bytes()), Some(7));
        assert_eq!(tree.remove("baz".as_bytes()), Some(8));
        assert_eq!(tree.remove("qux".as_bytes()), None);

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
