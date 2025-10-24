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

impl<V: Clone> Clone for Node<V> {
    fn clone(&self) -> Self {
        let mut new_ptr = self.ptr_data().allocate();
        unsafe {
            new_ptr.write_header(*self.header());
            new_ptr.write_label(self.label());
            if let Some(mut children) = new_ptr.children_ptr() {
                for child in self.children() {
                    children.write(child.clone());
                    children = children.add(1);
                }
            }
            new_ptr.write_value(self.value().cloned());
            new_ptr.assume_init()
        }
    }
}

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
        let children = unsafe { self.ptr_data().children_mut_opt(self.ptr) };

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

    /// set label with prefix slice
    /// NOTE: you can seriously mess up a node calling these functions manually
    pub fn prefix_label(&mut self, prefix: &[u8]) {
        self.modify_label(prefix, true);
    }

    /// swap label with new one (will realloc node)
    /// NOTE: you can seriously mess up a node calling these functions manually
    pub fn replace_label(&mut self, prefix: &[u8]) {
        self.modify_label(prefix, false);
    }

    /// reallocate node with new_label either prefixed the current one or replacing it
    /// NOTE: you can seriously mess up a node calling these functions manually
    pub(crate) fn modify_label(&mut self, new_label: &[u8], prefix: bool) {
        let new_header = NodeHeader {
            label_len: if prefix {
                new_label.len() + self.label_len()
            } else {
                new_label.len()
            } as u8,
            children_len: self.children_len() as u8,
        };
        let old_label_len = self.label_len();
        let value = self.take_value();
        let new_ptr_data = new_header.ptr_data();
        let old_ptr_data = self.ptr_data();

        debug_assert!(
            old_ptr_data.layout.size() <= new_ptr_data.layout.size(),
            "When prepending a prefix to the label, the allocation size should not decrease."
        );

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

            // write right to left since we are expanding
            new_ptr.write_value(value);
            if let Some(new_child_ptr) = new_ptr.children_ptr() {
                if let Some(old_child_ptr) = old_ptr.children_ptr() {
                    new_child_ptr.copy_from(old_child_ptr, new_header.children_len as usize);
                }
            }
            // write merged label
            let new_label_ptr = new_ptr.label_ptr().as_ptr();
            if prefix {
                // shift the suffix
                new_label_ptr
                    .add(new_label.len())
                    .copy_from(old_ptr.label_ptr().as_ptr(), old_label_len);
            }
            // copy the prefix
            new_label_ptr.copy_from_nonoverlapping(new_label.as_ptr(), new_label.len());

            new_ptr.write_header(new_header);
            self.ptr = new_ptr.assume_init().into_ptr_forget();
        }
    }

    /// forget self so Drop is not called and return the ptr
    pub(crate) fn into_ptr_forget(self) -> NonNull<NodeHeader> {
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
        let mut new_ptr = NodePtrAndData {
            ptr: self.ptr,
            ptr_data: new_ptr_data,
        };

        unsafe {
            // get child at i
            let removed_child = assert_some!(old_ptr.children_ptr()).add(i).read();
            // child.drop_in_place(); // if we want to drop instead of return
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
