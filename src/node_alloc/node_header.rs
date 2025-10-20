//! this provides an alternate layout that cannot be used with realloc but saves space
//! by minimizing alignment padding and skipping value allocations
//!
use core::{
    alloc::Layout,
    marker::PhantomData,
    ptr::{self, NonNull},
    slice,
};

use alloc::alloc;

use crate::node_alloc::node::Node;
use crate::node_common::extend;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Flags(u8);

impl Flags {
    pub(crate) const VALUE_INITIALIZED: Flags = Flags(0b0000_0001);
    pub(crate) const VALUE_ALLOCATED: Flags = Flags(0b0000_0010);

    #[allow(unused)]
    const VALID_BITS_MASK: u8 = 0b0000_0011; // Mask of all valid flag bits.

    pub(crate) const fn empty() -> Self {
        Flags(0)
    }

    #[allow(unused)]
    pub(crate) const fn from_bits_truncate(bits: u8) -> Self {
        Flags(bits & Self::VALID_BITS_MASK)
    }

    #[allow(unused)]
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

    pub(crate) fn insert(&mut self, other: Flags) {
        self.0 |= other.0;
    }

    pub(crate) fn set(&mut self, other: Flags, value: bool) {
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

const LABEL_OFFSET: isize = core::mem::size_of::<NodeHeader>() as isize;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct NodeHeader {
    pub(crate) flags: Flags,
    pub(crate) label_len: u8,
    pub(crate) children_len: u8,
}

pub(crate) struct PtrData<V> {
    pub(crate) layout: Layout,
    pub(crate) children_offset: Option<usize>,
    pub(crate) value_offset: Option<usize>,
    pub(crate) _marker: PhantomData<V>,
}

pub(crate) struct NodePtrAndData<V> {
    pub(crate) ptr: ptr::NonNull<NodeHeader>,
    pub(crate) ptr_data: PtrData<V>,
}

impl<V> NodePtrAndData<V> {
    #[inline]
    pub(crate) unsafe fn write_header(&mut self, header: NodeHeader) {
        unsafe { self.ptr.write(header) }
    }
    #[inline]
    pub unsafe fn write_value(&mut self, value: V) {
        if let Some(offset) = self.ptr_data.value_offset {
            unsafe { ptr::write(self.ptr.byte_add(offset).cast().as_ptr(), value) }
        }
    }
    #[inline]
    pub(crate) unsafe fn write_children<const N: usize>(&mut self, children: [Node<V>; N]) {
        if let Some(children_offset) = self.ptr_data.children_offset {
            unsafe {
                self.ptr
                    .byte_add(children_offset)
                    .cast::<[Node<V>; N]>()
                    .write(children);
            }
        }
    }

    #[inline]
    pub(crate) unsafe fn children_ptr(&self) -> Option<NonNull<Node<V>>> {
        unsafe { self.ptr_data.children_ptr(self.ptr) }
    }
    #[inline]
    pub(crate) unsafe fn value_ptr(&self) -> Option<NonNull<V>> {
        unsafe { self.ptr_data.value_ptr(self.ptr, Flags::VALUE_INITIALIZED) }
    }
    #[inline]
    pub(crate) unsafe fn write_label(&mut self, label: &[u8]) {
        unsafe {
            ptr::copy_nonoverlapping(
                label.as_ptr(),
                self.ptr.byte_offset(LABEL_OFFSET).cast().as_ptr(),
                label.len(),
            )
        }
    }

    // TODO
    #[allow(unused)]
    #[inline]
    pub(crate) fn into_parts(self) -> (NonNull<NodeHeader>, PtrData<V>) {
        (self.ptr, self.ptr_data)
    }

    #[inline]
    pub(crate) unsafe fn assume_init(self) -> Node<V> {
        Node {
            ptr: self.ptr,
            _marker: PhantomData,
        }
    }
}

impl NodeHeader {
    #[inline]
    fn initial_layout(label_len: usize) -> Layout {
        extend!(Layout::from_size_align(
            LABEL_OFFSET as usize + label_len,
            // alignment is size of max element (should be 1)
            core::mem::align_of::<NodeHeader>()
        ))
    }

    #[inline]
    pub(crate) fn ptr_data<V>(&self) -> PtrData<V> {
        let layout = Self::initial_layout(self.label_len as usize);

        let (mut layout, children_offset) = if self.children_len > 0 {
            let (new_layout, offset) = extend!(layout.extend(extend!(Layout::array::<Node<V>>(
                self.children_len as usize
            ))));
            (new_layout, Some(offset))
        } else {
            // This layout is NOT compatible with realloc. Nodes must use alloc/dealloc
            // if they are modified because the alignment can change
            // this will minimize memory usage at the cost of slower mutations.
            // branch nodes will not allocate values if they have no value,
            // and leaf nodes will not be effected by children alignment
            (layout, None)
        };

        let value_offset = if self.flags.contains(Flags::VALUE_ALLOCATED) {
            let (new_layout, offset) = extend!(layout.extend(Layout::new::<V>()));
            layout = new_layout;
            Some(offset)
        } else {
            None
        };

        PtrData {
            layout: layout.pad_to_align(),
            children_offset,
            value_offset,
            _marker: PhantomData,
        }
    }
}

impl<V> PtrData<V> {
    #[inline]
    pub(crate) fn allocate(self) -> NodePtrAndData<V> {
        unsafe {
            let ptr = alloc::alloc(self.layout).cast();
            let Some(ptr) = NonNull::new(ptr) else {
                alloc::handle_alloc_error(self.layout)
            };

            NodePtrAndData {
                ptr,
                ptr_data: self,
            }
        }
    }

    #[inline]
    pub(crate) fn dealloc(self, header_ptr: NonNull<NodeHeader>) {
        let layout = self.layout;
        unsafe {
            // drop_in_place tears down the value, but if value
            // was a ptr (like the child/sibling), we would need to use ptr::read to drop
            let _ = self.take_value(header_ptr);
            (&raw mut *self.children_mut(header_ptr)).drop_in_place();

            alloc::dealloc(header_ptr.as_ptr().cast(), layout);
        }
    }

    /// Deallocates the memory block without dropping its contents (children/value).
    ///
    /// # Safety
    /// This is only safe to call when ownership of the contents has been
    /// moved elsewhere (e.g., via `ptr::copy` or `ptr::read`).
    #[inline]
    pub(crate) unsafe fn dealloc_forget(self, header_ptr: NonNull<NodeHeader>) {
        unsafe {
            alloc::dealloc(header_ptr.as_ptr().cast(), self.layout);
        }
    }

    #[inline]
    pub(crate) unsafe fn label<'a>(header_ptr: NonNull<NodeHeader>) -> &'a [u8] {
        unsafe {
            let label_len = (*header_ptr.as_ptr()).label_len as usize;
            slice::from_raw_parts(
                header_ptr.as_ptr().byte_offset(LABEL_OFFSET).cast(),
                label_len,
            )
        }
    }

    #[allow(unused)]
    #[inline]
    pub(crate) unsafe fn label_mut<'a>(header_ptr: NonNull<NodeHeader>) -> &'a mut [u8] {
        unsafe {
            let label_len = (*header_ptr.as_ptr()).label_len as usize;
            slice::from_raw_parts_mut(
                header_ptr.as_ptr().byte_offset(LABEL_OFFSET).cast(),
                label_len,
            )
        }
    }
    #[inline]
    pub(crate) unsafe fn children<'a>(&self, header_ptr: NonNull<NodeHeader>) -> &'a [Node<V>] {
        if let Some(ptr) = unsafe { self.children_ptr(header_ptr) } {
            unsafe {
                let children_len = (*header_ptr.as_ptr()).children_len as usize;
                slice::from_raw_parts(ptr.as_ptr(), children_len)
            }
        } else {
            &[]
        }
    }

    #[inline]
    pub(crate) unsafe fn children_ptr(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> Option<NonNull<Node<V>>> {
        self.children_offset
            .map(|offset| unsafe { header_ptr.byte_add(offset).cast::<Node<V>>() })
    }

    #[inline]
    pub(crate) unsafe fn children_mut<'a>(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> &'a mut [Node<V>] {
        if let Some(ptr) = unsafe { self.children_ptr(header_ptr) } {
            unsafe {
                let children_len = (*header_ptr.as_ptr()).children_len as usize;
                slice::from_raw_parts_mut(ptr.as_ptr(), children_len)
            }
        } else {
            &mut []
        }
    }
    #[inline]
    pub unsafe fn take_value(&self, mut header_ptr: NonNull<NodeHeader>) -> Option<V> {
        unsafe {
            if let Some(ptr) = self.value_ptr(header_ptr, Flags::VALUE_INITIALIZED) {
                header_ptr
                    .as_mut()
                    .flags
                    .set(Flags::VALUE_INITIALIZED, false);
                Some(ptr.read())
            } else {
                None
            }
        }
    }
    #[inline]
    pub unsafe fn value_ptr_alloc(&self, header_ptr: NonNull<NodeHeader>) -> Option<NonNull<V>> {
        unsafe { self.value_ptr(header_ptr, Flags::VALUE_ALLOCATED) }
    }

    #[inline]
    pub unsafe fn value_ptr_init(&self, header_ptr: NonNull<NodeHeader>) -> Option<NonNull<V>> {
        unsafe { self.value_ptr(header_ptr, Flags::VALUE_INITIALIZED) }
    }
    #[inline]
    unsafe fn value_ptr(
        &self,
        header_ptr: NonNull<NodeHeader>,
        flags: Flags,
    ) -> Option<NonNull<V>> {
        if unsafe { *header_ptr.as_ptr() }.flags.contains(flags) {
            let offset = self.value_offset?;
            unsafe {
                return Some(header_ptr.byte_add(offset).cast());
            }
        }
        None
    }
}
