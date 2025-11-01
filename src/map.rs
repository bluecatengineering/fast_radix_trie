//! A map based on a patricia tree.
use crate::tree::{self, RadixTrie};
use crate::{BorrowedBytes, Bytes};
use alloc::{borrow::ToOwned, string::String, vec::Vec};
use core::{iter::FromIterator, marker::PhantomData};

/// Radix tree based map with [`Vec<u8>`] as key.
pub type RadixMap<V> = GenericRadixMap<Vec<u8>, V>;

/// Radix tree based map with [`String`] as key.
pub type StringRadixMap<V> = GenericRadixMap<String, V>;

/// Radix tree based map.
#[derive(Debug)]
pub struct GenericRadixMap<K, V> {
    tree: RadixTrie<V>,
    _key: PhantomData<K>,
}

impl<K, V> GenericRadixMap<K, V> {
    /// Makes a new empty `RadixMap` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert("foo", 10);
    /// assert_eq!(map.len(), 1);
    /// assert_eq!(map.get("foo"), Some(&10));
    ///
    /// map.remove("foo");
    /// assert_eq!(map.get("foo"), None);
    /// ```
    pub fn new() -> Self {
        GenericRadixMap {
            tree: RadixTrie::new(),
            _key: PhantomData,
        }
    }

    /// Clears this map, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.tree.clear();
    }

    /// Returns the number of elements in this map.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// map.insert("bar", 2);
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Returns `true` if this map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert("foo", 1);
    /// assert!(!map.is_empty());
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// create map from node (NOTE: calling methods on node directly seriously mess up your tree)
    pub fn from_node(node: crate::Node<V>) -> Self {
        Self {
            tree: node.into(),
            _key: PhantomData,
        }
    }

    /// get ref to root node  (NOTE: calling methods on node directly seriously mess up your tree)
    pub fn as_node(&self) -> &crate::Node<V> {
        self.tree.root()
    }

    /// get root node out of map (NOTE: calling methods on node directly seriously mess up your tree)
    pub fn into_node(self) -> crate::Node<V> {
        self.tree.into_root()
    }
}
impl<K: Bytes, V> GenericRadixMap<K, V> {
    /// Returns `true` if this map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// assert!(map.contains_key("foo"));
    /// assert!(!map.contains_key("bar"));
    /// ```
    pub fn contains_key<Q: AsRef<K::Borrowed>>(&self, key: Q) -> bool {
        self.tree.get(key.as_ref()).is_some()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// assert_eq!(map.get("foo"), Some(&1));
    /// assert_eq!(map.get("bar"), None);
    /// ```
    pub fn get<Q: AsRef<K::Borrowed>>(&self, key: Q) -> Option<&V> {
        self.tree.get(key.as_ref())
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// map.get_mut("foo").map(|v| *v = 2);
    /// assert_eq!(map.get("foo"), Some(&2));
    /// ```
    pub fn get_mut<Q: AsRef<K::Borrowed>>(&mut self, key: Q) -> Option<&mut V> {
        self.tree.get_mut(key.as_ref())
    }

    /// Finds the longest common prefix of `key` and the keys in this map,
    /// and returns a reference to the entry whose key matches the prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// map.insert("foobar", 2);
    /// assert_eq!(map.get_longest_common_prefix("fo"), None);
    /// assert_eq!(map.get_longest_common_prefix("foo"), Some(("foo".as_bytes(), &1)));
    /// assert_eq!(map.get_longest_common_prefix("fooba"), Some(("foo".as_bytes(), &1)));
    /// assert_eq!(map.get_longest_common_prefix("foobar"), Some(("foobar".as_bytes(), &2)));
    /// assert_eq!(map.get_longest_common_prefix("foobarbaz"), Some(("foobar".as_bytes(), &2)));
    /// ```
    pub fn get_longest_common_prefix<'a, Q>(&self, key: &'a Q) -> Option<(&'a K::Borrowed, &V)>
    where
        Q: ?Sized + AsRef<K::Borrowed>,
    {
        let (key, value) = self.tree.get_longest_common_prefix(key.as_ref())?;
        Some((K::Borrowed::from_bytes(key), value))
    }

    /// Finds the longest common prefix of `key` and the keys in this map,
    /// and returns a mutable reference to the entry whose key matches the prefix.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// map.insert("foobar", 2);
    /// assert_eq!(map.get_longest_common_prefix_mut("fo"), None);
    /// assert_eq!(map.get_longest_common_prefix_mut("foo"), Some(("foo".as_bytes(), &mut 1)));
    /// *map.get_longest_common_prefix_mut("foo").unwrap().1 = 3;
    /// assert_eq!(map.get_longest_common_prefix_mut("fooba"), Some(("foo".as_bytes(), &mut 3)));
    /// assert_eq!(map.get_longest_common_prefix_mut("foobar"), Some(("foobar".as_bytes(), &mut 2)));
    /// *map.get_longest_common_prefix_mut("foobar").unwrap().1 = 4;
    /// assert_eq!(map.get_longest_common_prefix_mut("foobarbaz"), Some(("foobar".as_bytes(), &mut 4)));
    /// ```
    pub fn get_longest_common_prefix_mut<'a, Q>(
        &mut self,
        key: &'a Q,
    ) -> Option<(&'a K::Borrowed, &mut V)>
    where
        Q: ?Sized + AsRef<K::Borrowed>,
    {
        let (key, value) = self.tree.get_longest_common_prefix_mut(key.as_ref())?;
        Some((K::Borrowed::from_bytes(key), value))
    }

    /// Returns the longest common prefix length of `key` and the keys in this map.
    ///
    /// Unlike `get_longest_common_prefix()`, this method does not check if there is a key that matches the prefix in this map.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// map.insert("foobar", 2);
    /// assert_eq!(map.longest_common_prefix_len("fo"), 2);
    /// assert_eq!(map.longest_common_prefix_len("foo"), 3);
    /// assert_eq!(map.longest_common_prefix_len("fooba"), 5);
    /// assert_eq!(map.longest_common_prefix_len("foobar"), 6);
    /// assert_eq!(map.longest_common_prefix_len("foobarbaz"), 6);
    /// assert_eq!(map.longest_common_prefix_len("foba"), 2);
    /// ```
    pub fn longest_common_prefix_len<Q>(&self, key: &Q) -> usize
    where
        Q: ?Sized + AsRef<K::Borrowed>,
    {
        self.tree.longest_common_prefix_len(key.as_ref())
    }

    /// Inserts a key-value pair into this map.
    ///
    /// If the map did not have this key present, `None` is returned.
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// assert_eq!(map.insert("foo", 1), None);
    /// assert_eq!(map.get("foo"), Some(&1));
    /// assert_eq!(map.insert("foo", 2), Some(1));
    /// assert_eq!(map.get("foo"), Some(&2));
    /// ```
    pub fn insert<Q: AsRef<K::Borrowed>>(&mut self, key: Q, value: V) -> Option<V> {
        self.tree.insert(key.as_ref(), value)
    }

    /// Inserts a key-value pair into this map with closure, or modify existing value
    ///
    /// If the map did not have this key present, `None` is returned.
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert_with_or_modify("foo", || vec![1], |v| v.push(2));
    /// map.insert_with_or_modify("foo", || vec![1], |v| v.push(2));
    /// assert_eq!(map.get("foo"), Some(&vec![1, 2]));
    /// ```
    pub fn insert_with_or_modify<Q, F, G>(&mut self, key: Q, insert: F, modify: G)
    where
        Q: AsRef<K::Borrowed>,
        F: FnOnce() -> V,
        G: for<'a> FnOnce(&'a mut V),
    {
        self.tree
            .insert_with_or_modify(key.as_ref(), insert, modify);
    }
    /// Removes a key from this map, returning the value at the key if the key was previously in it.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map = RadixMap::new();
    /// map.insert("foo", 1);
    /// assert_eq!(map.remove("foo"), Some(1));
    /// assert_eq!(map.remove("foo"), None);
    /// ```
    pub fn remove<Q: AsRef<K::Borrowed>>(&mut self, key: Q) -> Option<V> {
        self.tree.remove(key.as_ref())
    }

    /// Returns an iterator that collects all entries in the map up to a certain key.
    ///
    /// # Example
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut t = RadixMap::new();
    /// t.insert("a", vec!["a"]);
    /// t.insert("x", vec!["x"]);
    /// t.insert("ab", vec!["b"]);
    /// t.insert("abc", vec!["c"]);
    /// t.insert("abcd", vec!["d"]);
    /// t.insert("abcdf", vec!["f"]);
    /// assert!(t
    ///     .common_prefixes(b"abcde")
    ///     .map(|(_, v)| v)
    ///     .flatten()
    ///     .eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
    /// ```
    pub fn common_prefixes<'a, 'b, Q>(
        &'a self,
        key: &'b Q,
    ) -> CommonPrefixesIter<'a, 'b, K::Borrowed, V>
    where
        Q: ?Sized + AsRef<K::Borrowed>,
    {
        CommonPrefixesIter {
            key_bytes: key.as_ref().as_bytes(),
            iterator: self.tree.common_prefixes(key.as_ref()),
        }
    }

    /// Returns an iterator that collects all values of entries in the map up to a certain key.
    ///
    /// # Example
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    /// let mut t = RadixMap::new();
    /// t.insert("a", vec!["a"]);
    /// t.insert("x", vec!["x"]);
    /// t.insert("ab", vec!["b"]);
    /// t.insert("abc", vec!["c"]);
    /// t.insert("abcd", vec!["d"]);
    /// t.insert("abcdf", vec!["f"]);
    /// assert!(t
    ///     .common_prefix_values(b"abcde")
    ///     .flatten()
    ///     .eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
    /// ```
    pub fn common_prefix_values<'a, 'b, Q>(&'a self, key: &'b Q) -> impl Iterator<Item = &'a V>
    where
        Q: ?Sized + AsRef<K::Borrowed>,
        <K as Bytes>::Borrowed: 'b,
    {
        self.tree
            .common_prefixes(key.as_ref())
            .filter_map(|(_, n)| n.value())
    }

    /// Returns an iterator that collects all values of entries in the map up to a certain key.
    /// Takes owned key value so that iterator is not tied to key lifetime
    ///
    /// # Example
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    /// let mut t = RadixMap::new();
    /// t.insert("a", vec!["a"]);
    /// t.insert("x", vec!["x"]);
    /// t.insert("ab", vec!["b"]);
    /// t.insert("abc", vec!["c"]);
    /// t.insert("abcd", vec!["d"]);
    /// t.insert("abcdf", vec!["f"]);
    /// assert!(t
    ///     .common_prefix_values_owned(b"abcde".to_vec())
    ///     .flatten()
    ///     .eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
    /// ```
    pub fn common_prefix_values_owned(&self, key: K) -> impl Iterator<Item = &V>
    where
        K: AsRef<K::Borrowed>,
    {
        self.tree
            .common_prefixes_owned(key)
            .filter_map(|(_, n)| n.value())
    }
    /// Splits the map into two at the given prefix.
    ///
    /// The returned map contains all the entries of which keys are prefixed by `prefix`.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut a = RadixMap::new();
    /// a.insert("rust", 1);
    /// a.insert("ruby", 2);
    /// a.insert("bash", 3);
    /// a.insert("erlang", 4);
    /// a.insert("elixir", 5);
    ///
    /// let b = a.split_by_prefix("e");
    /// assert_eq!(a.len(), 3);
    /// assert_eq!(b.len(), 2);
    ///
    /// assert_eq!(a.keys().collect::<Vec<_>>(), [b"bash", b"ruby", b"rust"]);
    /// assert_eq!(b.keys().collect::<Vec<_>>(), [b"elixir", b"erlang"]);
    /// ```
    pub fn split_by_prefix<Q: AsRef<K::Borrowed>>(&mut self, prefix: Q) -> Self {
        let subtree = self.tree.split_by_prefix(prefix.as_ref());
        GenericRadixMap {
            tree: subtree,
            _key: PhantomData,
        }
    }

    /// Gets an iterator over the entries of this map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let map: RadixMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![(Vec::from("bar"), &2), ("baz".into(), &3), ("foo".into(), &1)],
    ///            map.iter().collect::<Vec<_>>());
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::new(self.tree.nodes(), Vec::new())
    }

    /// Gets a mutable iterator over the entries of this map, soretd by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map: RadixMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// for (_, v) in map.iter_mut() {
    ///    *v += 10;
    /// }
    /// assert_eq!(map.get("bar"), Some(&12));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut::new(self.tree.nodes_mut(), Vec::new())
    }

    /// Gets an iterator over the keys of this map, in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let map: RadixMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![Vec::from("bar"), "baz".into(), "foo".into()],
    ///            map.keys().collect::<Vec<_>>());
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys(self.iter())
    }

    /// Gets an iterator over the values of this map, in order by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let map: RadixMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![2, 3, 1],
    ///            map.values().cloned().collect::<Vec<_>>());
    /// ```
    pub fn values(&self) -> Values<'_, V> {
        Values {
            nodes: self.tree.nodes(),
        }
    }

    /// Gets a mutable iterator over the values of this map, in order by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map: RadixMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// for v in map.values_mut() {
    ///     *v += 10;
    /// }
    /// assert_eq!(vec![12, 13, 11],
    ///            map.values().cloned().collect::<Vec<_>>());
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, V> {
        ValuesMut {
            nodes: self.tree.nodes_mut(),
        }
    }
}
impl<K: Bytes, V> GenericRadixMap<K, V> {
    /// Gets an iterator over the entries having the given prefix of this map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let map: RadixMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![(Vec::from("bar"), &2), ("baz".into(), &3)],
    ///            map.iter_prefix(b"ba").collect::<Vec<_>>());
    /// ```
    pub fn iter_prefix<'a>(&'a self, prefix: &K::Borrowed) -> impl Iterator<Item = (K, &'a V)> {
        self.tree
            .iter_prefix(prefix)
            .into_iter()
            .flat_map(move |(prefix_len, nodes)| {
                Iter::<K, V>::new(nodes, Vec::from(&prefix.as_bytes()[..prefix_len]))
            })
    }

    /// Gets a mutable iterator over the entries having the given prefix of this map, sorted by key.
    ///
    /// # Examples
    ///
    /// ```
    /// use fast_radix_trie::RadixMap;
    ///
    /// let mut map: RadixMap<_> =
    ///     vec![("foo", 1), ("bar", 2), ("baz", 3)].into_iter().collect();
    /// assert_eq!(vec![(Vec::from("bar"), &mut 2), ("baz".into(), &mut 3)],
    ///            map.iter_prefix_mut(b"ba").collect::<Vec<_>>());
    /// ```
    pub fn iter_prefix_mut<'a>(
        &'a mut self,
        prefix: &K::Borrowed,
    ) -> impl Iterator<Item = (K, &'a mut V)> {
        self.tree
            .iter_prefix_mut(prefix)
            .into_iter()
            .flat_map(move |(prefix_len, nodes)| {
                IterMut::<K, V>::new(nodes, Vec::from(&prefix.as_bytes()[..prefix_len]))
            })
    }
}

// impl<K: Bytes + fmt::Debug, V: fmt::Debug> fmt::Debug for GenericRadixMap<K, V> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         f.debug_struct("RadixMap")
//             .field("root", &self.tree.root())
//             .finish()
//     }
// }

impl<K, V: Clone> Clone for GenericRadixMap<K, V> {
    fn clone(&self) -> Self {
        Self {
            tree: self.tree.clone(),
            _key: PhantomData,
        }
    }
}
impl<K, V> Default for GenericRadixMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Bytes, V> IntoIterator for GenericRadixMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            nodes: self.tree.into_nodes(),
            key_bytes: Vec::new(),
            _key: PhantomData,
        }
    }
}

impl<K, Q, V> FromIterator<(Q, V)> for GenericRadixMap<K, V>
where
    K: Bytes,
    Q: AsRef<K::Borrowed>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (Q, V)>,
    {
        let mut map = GenericRadixMap::new();
        for (k, v) in iter {
            map.insert(k, v);
        }
        map
    }
}
impl<K, Q, V> Extend<(Q, V)> for GenericRadixMap<K, V>
where
    K: Bytes,
    Q: AsRef<K::Borrowed>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (Q, V)>,
    {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

/// An iterator over a `RadixMap`'s entries.
#[derive(Debug)]
pub struct Iter<'a, K, V: 'a> {
    nodes: tree::Nodes<'a, V>,
    key_bytes: Vec<u8>,
    key_offset: usize,
    _key: PhantomData<K>,
}
impl<'a, K, V: 'a> Iter<'a, K, V> {
    fn new(nodes: tree::Nodes<'a, V>, key: Vec<u8>) -> Self {
        let key_offset = key.len();
        Self {
            nodes,
            key_bytes: key,
            key_offset,
            _key: PhantomData,
        }
    }
}
impl<'a, K: Bytes, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        for (key_len, node) in &mut self.nodes {
            self.key_bytes.truncate(self.key_offset + key_len);
            self.key_bytes.extend(node.label());
            if let Some(value) = node.value() {
                return Some((K::Borrowed::from_bytes(&self.key_bytes).to_owned(), value));
            }
        }
        None
    }
}

/// An owning iterator over a `RadixMap`'s entries.
#[derive(Debug)]
pub struct IntoIter<K, V> {
    nodes: tree::IntoNodes<V>,
    key_bytes: Vec<u8>,
    _key: PhantomData<K>,
}
impl<K: Bytes, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        for (key_len, mut node) in &mut self.nodes {
            self.key_bytes.truncate(key_len);
            self.key_bytes.extend(node.label());
            if let Some(value) = node.take_value() {
                return Some((K::Borrowed::from_bytes(&self.key_bytes).to_owned(), value));
            }
        }
        None
    }
}

/// A mutable iterator over a `RadixMap`'s entries.
#[derive(Debug)]
pub struct IterMut<'a, K, V: 'a> {
    nodes: tree::NodesMut<'a, V>,
    key_bytes: Vec<u8>,
    key_offset: usize,
    _key: PhantomData<K>,
}
impl<'a, K, V: 'a> IterMut<'a, K, V> {
    fn new(nodes: tree::NodesMut<'a, V>, key: Vec<u8>) -> Self {
        let key_offset = key.len();
        Self {
            nodes,
            key_bytes: key,
            key_offset,
            _key: PhantomData,
        }
    }
}
impl<'a, K: Bytes, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        for (key_len, node) in &mut self.nodes {
            self.key_bytes.truncate(self.key_offset + key_len);
            self.key_bytes.extend(node.label());
            if let Some(value) = node.into_value_mut() {
                return Some((K::Borrowed::from_bytes(&self.key_bytes).to_owned(), value));
            }
        }
        None
    }
}

/// An iterator over a `RadixMap`'s keys.
#[derive(Debug)]
pub struct Keys<'a, K, V: 'a>(Iter<'a, K, V>);
impl<'a, K: Bytes, V: 'a> Iterator for Keys<'a, K, V> {
    type Item = K;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }
}

/// An iterator over a `RadixMap`'s values.
#[derive(Debug)]
pub struct Values<'a, V: 'a> {
    nodes: tree::Nodes<'a, V>,
}
impl<'a, V: 'a> Iterator for Values<'a, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        for (_, node) in &mut self.nodes {
            if let Some(value) = node.value() {
                return Some(value);
            }
        }
        None
    }
}

/// A mutable iterator over a `RadixMap`'s values.
#[derive(Debug)]
pub struct ValuesMut<'a, V: 'a> {
    nodes: tree::NodesMut<'a, V>,
}
impl<'a, V: 'a> Iterator for ValuesMut<'a, V> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<Self::Item> {
        for (_, node) in &mut self.nodes {
            if let Some(value) = node.into_value_mut() {
                return Some(value);
            }
        }
        None
    }
}

/// An iterator over entries in a `RadixMap` that share a common prefix with
/// a given key.
#[derive(Debug)]
pub struct CommonPrefixesIter<'a, 'b, K: ?Sized, V> {
    key_bytes: &'b [u8],
    iterator: crate::node_common::CommonPrefixesIter<'a, 'b, K, V>,
}
impl<'a, 'b, K, V> Iterator for CommonPrefixesIter<'a, 'b, K, V>
where
    K: 'b + ?Sized + BorrowedBytes,
{
    type Item = (&'b K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        for (prefix_len, n) in self.iterator.by_ref() {
            if let Some(v) = n.value() {
                return Some((K::from_bytes(&self.key_bytes[..prefix_len]), v));
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, sync::LazyLock};

    use crate::RadixSet;

    use super::*;
    use rand::seq::SliceRandom;

    #[test]
    fn it_works() {
        let input = [
            ("7", 7),
            ("43", 43),
            ("92", 92),
            ("37", 37),
            ("31", 31),
            ("21", 21),
            ("0", 0),
            ("35", 35),
            ("47", 47),
            ("82", 82),
            ("61", 61),
            ("9", 9),
        ];

        let mut map = RadixMap::new();
        for &(ref k, v) in input.iter() {
            assert_eq!(map.insert(k, v), None);
            assert_eq!(map.get(k), Some(&v));
        }
    }

    #[test]
    fn clear_works() {
        let mut map = RadixMap::new();
        assert!(map.is_empty());

        map.insert("foo", 1);
        assert!(!map.is_empty());

        map.clear();
        assert!(map.is_empty());
    }

    #[test]
    fn into_iter_works() {
        let map: RadixMap<_> = vec![("foo", 1), ("bar", 2), ("baz", 3)]
            .into_iter()
            .collect();
        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            [(Vec::from("bar"), 2), ("baz".into(), 3), ("foo".into(), 1)]
        );
    }

    #[test]
    fn iter_mut_works() {
        let mut map: RadixMap<_> = vec![("foo", 1), ("bar", 2), ("baz", 3)]
            .into_iter()
            .collect();

        for (_key, x) in map.iter_mut() {
            (*x) *= 2;
        }

        assert_eq!(
            map.into_iter().collect::<Vec<_>>(),
            [(Vec::from("bar"), 4), ("baz".into(), 6), ("foo".into(), 2)]
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn large_map_works() {
        let mut input = (0..10000).map(|i| (i.to_string(), i)).collect::<Vec<_>>();
        input.shuffle(&mut rand::rng());

        // Insert
        let mut map = input.iter().cloned().collect::<RadixMap<_>>();
        assert_eq!(map.len(), input.len());

        // Get
        for &(ref k, v) in input.iter() {
            assert_eq!(map.get(k), Some(&v));
        }

        // Remove
        for &(ref k, v) in input.iter().take(input.len() / 2) {
            assert_eq!(map.remove(k), Some(v));
            assert_eq!(map.remove(k), None);
        }
        for (k, _) in input.iter().take(input.len() / 2) {
            assert_eq!(map.get(k), None);
        }
        for &(ref k, v) in input.iter().skip(input.len() / 2) {
            assert_eq!(map.get(k), Some(&v));
        }

        // Insert
        for &(ref k, v) in input.iter().take(input.len() / 2) {
            assert_eq!(map.insert(k, v), None);
        }
        for &(ref k, v) in input.iter().skip(input.len() / 2) {
            assert_eq!(map.insert(k, v), Some(v));
        }

        // Get
        for &(ref k, v) in input.iter() {
            assert_eq!(map.get(k), Some(&v));
        }
    }

    #[test]
    fn test_common_word_prefixes() {
        let mut t = RadixMap::new();
        t.insert(".com.foo.", vec!["b"]);
        t.insert(".", vec!["a"]);
        t.insert(".com.foo.bar.", vec!["c"]);
        t.insert("..", vec!["e"]);
        t.insert("x", vec!["d"]);

        let results = t
            .common_prefixes(b".com.foo.bar.baz.")
            .flat_map(|(_, v)| v)
            .cloned()
            .collect::<Vec<_>>();

        assert!(results.iter().eq(vec![&"a", &"b", &"c"].into_iter()));
    }

    #[test]
    fn test_letter_prefixes() {
        let mut t = RadixMap::new();
        t.insert("x", vec!["x"]);
        t.insert("a", vec!["a"]);
        t.insert("ab", vec!["b"]);
        t.insert("abc", vec!["c"]);
        t.insert("abcd", vec!["d"]);
        t.insert("abcdf", vec!["f"]);

        let results = t
            .common_prefixes(b"abcde")
            .flat_map(|(_, v)| v)
            .cloned()
            .collect::<Vec<_>>();
        assert!(results.iter().eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
    }

    #[test]
    fn test_common_prefixes() {
        let mut t = RadixMap::new();
        t.insert("b", vec!["b"]);
        t.insert("a", vec!["a"]);
        t.insert("c", vec!["c"]);
        t.insert("..", vec!["e"]);
        t.insert("x", vec!["d"]);

        let results = t
            .common_prefixes(b"abc")
            .flat_map(|(k, v)| {
                unsafe {
                    println!("{:?}", core::str::from_utf8_unchecked(k));
                }
                v
            })
            .cloned()
            .collect::<Vec<_>>();
        dbg!(&results);
        assert!(results.iter().eq(vec![&"a"].into_iter()));

        let mut t = RadixMap::new();
        t.insert("ab", vec!["b"]);
        t.insert("a", vec!["a"]);
        t.insert("abc", vec!["c"]);
        t.insert("..", vec!["e"]);
        t.insert("x", vec!["d"]);

        let results = t
            .common_prefixes(b"abcd")
            .flat_map(|(_, v)| v)
            .cloned()
            .collect::<Vec<_>>();

        assert!(results.iter().eq(vec![&"a", &"b", &"c"].into_iter()));

        let mut list = RadixMap::new();
        list.insert(b".com.foocatnetworks.".as_ref(), vec![0_u16]);
        list.insert(b".com.foocatnetworks.foo.".as_ref(), vec![1]);
        list.insert(b".com.foocatnetworks.foo.baz.".as_ref(), vec![2]);
        list.insert(b".com.google.".as_ref(), vec![0]);
        list.insert(b".com.cisco.".as_ref(), vec![0]);
        list.insert(b".org.wikipedia.".as_ref(), vec![0]);

        let results = list
            .common_prefixes(b".com.foocatnetworks.foo.baz.")
            .flat_map(|(_, v)| v)
            .cloned()
            .collect::<Vec<_>>();

        assert!(vec![0_u16, 1, 2].into_iter().eq(results.into_iter()));
    }

    #[test]
    fn issue21() {
        let mut map = RadixMap::new();
        map.insert("1", 0);
        map.insert("2", 0);
        map.remove("2");
        map.insert("2", 0);
        assert_eq!(map.len(), map.iter().count());
        assert_eq!(map.len(), map.iter_mut().count());
    }

    #[test]
    fn issue35() {
        let mut map = StringRadixMap::<u8>::new();
        map.insert("インターポール", 1);
        map.insert("インターポル", 2);
        map.insert("インターリーブ", 3);
        map.insert("インターン", 4);

        assert_eq!(map.get("インターポール"), Some(&1));
        assert_eq!(map.get("インターポル"), Some(&2));
    }

    #[test]
    fn issue42_iter_prefix() {
        let mut map = StringRadixMap::new();
        map.insert("a0/b0", 0);
        map.insert("a1/b1", 0);
        let items: Vec<_> = {
            let prefix = "a0".to_owned();
            map.iter_prefix(&prefix).collect()
        };

        assert_eq!(items, vec![("a0/b0".to_owned(), &0)])
    }

    #[test]
    fn issue42_iter_prefix_mut() {
        let mut map = StringRadixMap::new();
        map.insert("a0/b0", 0);
        map.insert("a1/b1", 0);
        let items: Vec<_> = {
            let prefix = "a0".to_owned();
            map.iter_prefix_mut(&prefix).collect()
        };

        assert_eq!(items, vec![("a0/b0".to_owned(), &mut 0)])
    }

    #[test]
    fn test_iter_prefix_case() {
        // using longest_common_prefix can traverse the tree incorrectly
        let mut map = StringRadixMap::new();
        map.insert("foo", 1);
        map.insert("foobar", 2);
        let items: Vec<_> = {
            let prefix = "foba".to_owned();
            map.iter_prefix_mut(&prefix).collect()
        };

        assert_eq!(items, vec![])
    }

    #[test]
    fn issue42_common_prefix_values() {
        let mut map = StringRadixMap::new();
        map.insert("a0/b0", 0);
        map.insert("a1/b1", 0);

        let items: Vec<_> = {
            let prefix = "a0/b0/c0".to_owned();
            map.common_prefix_values(&prefix).collect()
        };

        assert_eq!(items, vec![&0])
    }

    #[test]
    fn test_owned_impl_iter() {
        struct TestTrie<T> {
            map: GenericRadixMap<Vec<u8>, T>,
        }

        impl<T> TestTrie<T> {
            #[expect(dead_code)]
            fn common_prefix_test(&self, domain: &[u8]) -> impl Iterator<Item = &T> {
                let domain = domain.to_vec();
                self.map.common_prefix_values_owned(domain)
            }
        }
    }

    // insert big list of domains and make sure all entries are there
    #[test]
    #[ignore]
    fn test_big_set() {
        const TOP_MILLION: &str = include_str!("../data/top-domains.txt");

        static DOMAINS_REV: LazyLock<Vec<String>> = LazyLock::new(|| {
            TOP_MILLION
                .split(|c: char| c.is_whitespace())
                .collect::<HashSet<_>>()
                .into_iter()
                .map(|s| s.chars().rev().collect::<String>())
                .collect()
        });

        fn get_domain_text() -> Vec<&'static str> {
            DOMAINS_REV.iter().map(|s| s.as_str()).collect()
        }

        let words: Vec<&str> = get_domain_text();
        let trie: RadixSet = words.iter().copied().collect();

        let unique_words = words
            .into_iter()
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();

        for word in &unique_words {
            assert!(trie.contains(word))
        }

        assert_eq!(unique_words.len(), trie.len());
    }
}
