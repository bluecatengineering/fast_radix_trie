//! A node which represents a subtree of a patricia tree.
use crate::{
    node_common::{NodeMut, assert_some},
    node_header::{NodeHeader, NodePtrAndData},
};
use core::{
    marker::PhantomData,
    mem,
    ptr::{self, NonNull},
};

/// A node which represents a subtree of a patricia tree.
///
/// Note that this is a low level building block.
/// Usually it is recommended to use more high level data structures (e.g., `PatriciaTree`).
#[derive(Debug)]
pub struct Node<V> {
    // alignment: will be no less than 8 on x86-64 because NonNull<V> is 8 bytes
    // if V is wider, then the alignment will be bigger
    // layout:
    //   - label_len: u8
    //   - label: [u8; label_len]
    //   - children: [NonNull<Node<V>>; children_len]
    //   - value: Option<V>
    pub(crate) ptr: ptr::NonNull<NodeHeader>,
    pub(crate) _marker: PhantomData<V>,
}

unsafe impl<V: Send> Send for Node<V> {}
unsafe impl<V: Sync> Sync for Node<V> {}

impl<V> Node<V> {
    /// Makes a new node.
    /// SAFETY: - label len must not exceed 255
    ///         - children len must not exceed 255
    pub fn new<const N: usize>(label: &[u8], children: [Node<V>; N], value: Option<V>) -> Self {
        // known at compile time
        if N > u8::MAX as usize {
            panic!("children_len {} exceeds the max {}", N, u8::MAX);
        }
        assert!(
            label.len() <= crate::node_common::MAX_LABEL_LEN,
            "nodes must have a label len <= 255"
        );

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

    /// Returns the reference to the value of this node.
    pub fn value(&self) -> Option<&V> {
        unsafe { (self.ptr_data().value_ptr(self.ptr)).as_ref() }.as_ref()
    }

    /// Returns the mutable reference to the value of this node.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        unsafe { (self.ptr_data().value_ptr(self.ptr)).as_mut() }.as_mut()
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

    /// adds child at i and shifts elements right
    /// node must have children already and i <= len
    pub(crate) unsafe fn add_child(&mut self, new_child: Node<V>, i: usize) {
        debug_assert!(
            i <= self.children_len(),
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

        // dbg!(self.ptr_data().layout);
        // dbg!(new_header.ptr_data::<V>().layout);

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
            let num = old_children_len - i;
            // write data in right to left order since we're growing
            new_ptr.write_value(value);

            // shift children from [i..] to [i+1..]
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
    pub(crate) unsafe fn remove_child(&mut self, i: usize) -> Node<V> {
        debug_assert!(
            i < self.children_len(),
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

    pub(crate) unsafe fn split_at(&mut self, position: usize, new_child: Option<Node<V>>) {
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

#[cfg(test)]
mod tests {
    use super::*;
    // use crate::{PatriciaSet, StringPatriciaMap};

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
        root.insert("team", 2);
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
