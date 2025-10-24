//! A node which represents a subtree of a patricia tree.
use crate::{
    node_alloc::node_header::{Flags, NodeHeader, NodePtrAndData, PtrData},
    node_common::{NodeMut, assert_some},
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
    // alignment: will be 2 on nodes with no children and/or no value
    // if it has children then 8 on x86-64 and more if V is wider
    // layout:
    //   - flags: u8
    //   - label_len: u8
    //   - label: [u8; label_len]
    //   - children: [NonNull<Node<V>>; children_len] -- optionally allocated
    //   - value: V -- optionally allocated
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
            if let Some(val) = self.value().cloned() {
                new_ptr.write_value(val);
            }
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
        let mut flags = Flags::empty();
        if value.is_some() {
            flags.insert(Flags::VALUE_ALLOCATED | Flags::VALUE_INITIALIZED);
        }

        let header = NodeHeader {
            flags,
            label_len: label.len() as u8,
            children_len: children.len() as u8,
        };
        let mut ptr = header.ptr_data().allocate();
        unsafe {
            ptr.write_header(header);
            ptr.write_label(label);
            ptr.write_children(children);
            if let Some(val) = value {
                ptr.write_value(val);
            }
            ptr.assume_init()
        }
    }

    /// Returns the reference to the value of this node.
    pub fn value(&self) -> Option<&V> {
        if let Some(val) = unsafe { self.ptr_data().value_ptr_init(self.ptr) } {
            return Some(unsafe { val.as_ref() });
        }
        None
    }

    /// Returns the mutable reference to the value of this node.
    pub fn value_mut(&mut self) -> Option<&mut V> {
        if let Some(mut val) = unsafe { self.ptr_data().value_ptr_init(self.ptr) } {
            return Some(unsafe { val.as_mut() });
        }
        None
    }

    /// Returns mutable references to the node itself with its sibling and child
    pub fn as_mut(&mut self) -> NodeMut<'_, V> {
        let value = if let Some(mut value) = unsafe { self.ptr_data().value_ptr_init(self.ptr) } {
            Some(unsafe { value.as_mut() })
        } else {
            None
        };
        let children = unsafe { self.ptr_data().children_mut_opt(self.ptr) };

        NodeMut {
            label: self.label(),
            value,
            children,
        }
    }

    /// Takes the value out of this node.
    pub fn take_value(&mut self) -> Option<V> {
        unsafe { self.ptr_data().take_value(self.ptr) }
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
            flags: self.flags(),
            label_len: self.label_len() as u8,
            children_len: self.children_len() as u8 + 1,
        };
        let old_children_len = self.children_len();
        let mut new_ptr = new_header.ptr_data().allocate();
        let old_ptr = NodePtrAndData {
            ptr: self.ptr,
            ptr_data: self.ptr_data(),
        };
        let value = self.take_value();

        // dbg!(self.ptr_data().layout);
        // dbg!(new_header.ptr_data::<V>().layout);

        unsafe {
            // update header value/label
            new_ptr.write_header(new_header);
            new_ptr.write_label(self.label());

            let num = old_children_len - i;
            // copy children
            if let Some(new_child_ptr) = new_ptr.children_ptr() {
                if let Some(old_child) = old_ptr.children_ptr() {
                    // copy ..i
                    new_child_ptr.copy_from_nonoverlapping(old_child, i);
                    // copy i + 1..i+num
                    new_child_ptr
                        .add(i + 1)
                        .copy_from_nonoverlapping(old_child.add(i), num);
                }
                // write child at i
                new_child_ptr.add(i).write(new_child);
            }
            if let Some(val) = value {
                new_ptr.write_value(val);
            }
            // re-assign ptr to avoid Drop
            self.ptr = new_ptr.assume_init().into_ptr_forget();
            // dealloc old node without drop
            old_ptr.ptr_data.dealloc_forget(old_ptr.ptr);
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
            flags: self.flags(),
            label_len: if prefix {
                new_label.len() + self.label_len()
            } else {
                new_label.len()
            } as u8,
            children_len: self.children_len() as u8,
        };

        let old_label_len = self.label_len();
        // allocate new node
        let mut new_ptr = new_header.ptr_data().allocate();
        let old_ptr = NodePtrAndData {
            ptr: self.ptr,
            ptr_data: self.ptr_data(),
        };
        let value = self.take_value();

        unsafe {
            // update header value/label
            new_ptr.write_header(new_header);

            // write merged label
            let new_label_ptr = new_ptr.label_ptr().as_ptr();
            // Copy the new label
            new_label_ptr.copy_from_nonoverlapping(new_label.as_ptr(), new_label.len());
            if prefix {
                // Copy the original label as suffix
                new_label_ptr
                    .add(new_label.len())
                    .copy_from_nonoverlapping(old_ptr.label_ptr().as_ptr(), old_label_len);
            }

            if let Some(new_child_ptr) = new_ptr.children_ptr() {
                if let Some(old_child_ptr) = old_ptr.children_ptr() {
                    new_child_ptr.copy_from(old_child_ptr, new_header.children_len as usize);
                }
            }

            if let Some(val) = value {
                new_ptr.write_value(val);
            }
            // re-assign ptr to avoid Drop
            self.ptr = new_ptr.assume_init().into_ptr_forget();
            // dealloc old node without drop
            old_ptr.ptr_data.dealloc_forget(old_ptr.ptr);
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
            flags: self.flags(),
            label_len: self.label_len() as u8,
            children_len: self.children_len() as u8 - 1,
        };
        let old_children_len = self.children_len();

        let mut new_ptr = new_header.ptr_data::<V>().allocate();
        let old_ptr = NodePtrAndData {
            ptr: self.ptr,
            ptr_data: self.ptr_data(),
        };
        let value = self.take_value();

        unsafe {
            // get child at i
            let removed_child = assert_some!(old_ptr.children_ptr()).add(i).read();

            // write header/label
            new_ptr.write_header(new_header);
            new_ptr.write_label(self.label());
            // copy children
            // shift children from [i+1..] to [i..]
            let num = old_children_len - (i + 1);
            // copy children
            if let Some(new_child) = new_ptr.children_ptr() {
                if let Some(old_child) = old_ptr.children_ptr() {
                    // copy ..i
                    new_child.copy_from_nonoverlapping(old_child, i);
                    // copy i + 1..i+num
                    new_child
                        .add(i)
                        .copy_from_nonoverlapping(old_child.add(i + 1), num);
                }
            }
            // write value
            if let Some(val) = value {
                new_ptr.write_value(val);
            }
            // re-assign ptr to avoid drop
            self.ptr = new_ptr.assume_init().into_ptr_forget();
            // dealloc old buffet without calling drop on value/children
            old_ptr.ptr_data.dealloc_forget(old_ptr.ptr);
            removed_child
        }
    }

    /// Sets the value of this node.
    pub fn set_value(&mut self, value: V) {
        self.take_value();
        if let Some(ptr) = unsafe { self.ptr_data().value_ptr_alloc(self.ptr) } {
            self.set_flags(Flags::VALUE_INITIALIZED, true);
            unsafe {
                ptr.write(value);
            }
        } else {
            let mut new_header = *self.header();
            new_header
                .flags
                .insert(Flags::VALUE_ALLOCATED | Flags::VALUE_INITIALIZED);

            let children_len = self.children_len();
            let old_ptr_data = self.ptr_data();

            let old_ptr = NodePtrAndData {
                ptr: self.ptr,
                ptr_data: old_ptr_data,
            };

            // allocate space for new node
            let mut new_ptr = new_header.ptr_data().allocate();

            unsafe {
                // copy header
                new_ptr.write_header(new_header);
                // copy label
                new_ptr.write_label(self.label());
                // copy children
                if let Some(new_child) = new_ptr.children_ptr() {
                    if let Some(old_child) = old_ptr.children_ptr() {
                        new_child.copy_from_nonoverlapping(old_child, children_len);
                    }
                }
                // write new value
                new_ptr.write_value(value);
                // assign to self
                self.ptr = new_ptr.assume_init().into_ptr_forget();
                // dealloc the old node without calling drop on its contents
                old_ptr.ptr_data.dealloc_forget(old_ptr.ptr);
            }
        }
    }

    fn flags(&self) -> Flags {
        Flags::from_bits_truncate(self.header().flags.bits())
    }
    fn set_flags(&mut self, other: Flags, value: bool) {
        self.header_mut().flags.set(other, value);
    }

    pub(crate) unsafe fn split_at(&mut self, position: usize, new_child: Option<Node<V>>) {
        debug_assert!(
            position < self.label_len(),
            "label offset must be within label bounds"
        );
        let flags = self.flags();
        let value = self.take_value();
        let old_ptr = NodePtrAndData {
            ptr: self.ptr,
            ptr_data: self.ptr_data(),
        };

        let child = unsafe {
            let suffix = self.label().get_unchecked(position..);
            let old_children_len = self.children_len();
            let child_hdr = NodeHeader {
                flags,
                label_len: suffix.len() as u8,
                children_len: old_children_len as u8,
            };

            let mut ptr = child_hdr.ptr_data().allocate();

            // copy data
            ptr.write_header(child_hdr);
            ptr.write_label(suffix);
            if old_children_len > 0 {
                let dst_children = assert_some!(ptr.children_ptr());
                let src_children = assert_some!(self.ptr_data().children_ptr(self.ptr));
                dst_children
                    .copy_from_nonoverlapping(src_children, child_hdr.children_len as usize);
            }
            if let Some(val) = value {
                ptr.write_value(val);
            }
            ptr.assume_init()
        };
        // make new allocation for self with no value
        let new_hdr = NodeHeader {
            flags: Flags::empty(),
            label_len: position as u8,
            children_len: 1 + new_child.is_some() as u8,
        };

        let mut new_ptr = new_hdr.ptr_data().allocate();

        unsafe {
            new_ptr.write_header(new_hdr);
            new_ptr.write_label(self.label().get_unchecked(..position));
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
            // re-assign ptr to avoid Drop of old children
            self.ptr = new_ptr.assume_init().into_ptr_forget();
            old_ptr.ptr_data.dealloc_forget(old_ptr.ptr);
        }
    }
}

impl<V> Drop for Node<V> {
    fn drop(&mut self) {
        self.ptr_data().dealloc(self.ptr);
    }
}
