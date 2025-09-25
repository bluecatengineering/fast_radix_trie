use core::{
    alloc::Layout,
    marker::PhantomData,
    ptr::{self, NonNull},
    slice,
};

use alloc::alloc;

use crate::node::{Flags, Node};

macro_rules! extend {
    ($expr:expr) => {{
        let val = match $expr {
            Ok(tuple) => tuple,
            Err(_) => unreachable!("Layout extension failed"),
        };
        val
    }};
}

// const LABEL_OFFSET: isize = core::mem::size_of::<NodeHeader>() as isize;
const LABEL_OFFSET: isize = 2 as isize;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct NodeHeader {
    pub(crate) flags: Flags,
    pub(crate) label_len: u8,
}

pub(crate) struct PtrData<V> {
    pub(crate) layout: Layout,
    pub(crate) value_offset: usize,
    pub(crate) child_offset: Option<usize>,
    pub(crate) sibling_offset: Option<usize>,
    pub(crate) _marker: PhantomData<V>,
}

pub(crate) struct NodePtrAndData<V> {
    pub(crate) ptr: std::ptr::NonNull<NodeHeader>,
    pub(crate) ptr_data: PtrData<V>,
}

impl<V> NodePtrAndData<V> {
    #[inline]
    pub unsafe fn write_header(&mut self, header: NodeHeader) {
        unsafe { self.ptr.write(header) }
    }

    #[inline]
    pub unsafe fn write_value(&mut self, value: Option<V>) {
        unsafe {
            ptr::write(
                self.ptr
                    .byte_add(self.ptr_data.value_offset)
                    .cast()
                    .as_ptr(),
                value,
            )
        }
    }
    /// must have flags already set as allocated
    #[inline]
    pub unsafe fn write_child(&mut self, value: Node<V>) {
        if let Some(offset) = self.ptr_data.child_offset {
            unsafe { ptr::write(self.ptr.byte_add(offset).cast().as_ptr(), value) }
        }
    }
    /// must have flags already set as allocated
    #[inline]
    pub unsafe fn write_sibling(&mut self, value: Node<V>) {
        if let Some(offset) = self.ptr_data.sibling_offset {
            unsafe { ptr::write(self.ptr.byte_add(offset).cast().as_ptr(), value) }
        }
    }

    #[inline]
    pub unsafe fn write_label(&mut self, label: &[u8]) {
        unsafe {
            ptr::copy_nonoverlapping(
                label.as_ptr(),
                self.ptr.byte_offset(LABEL_OFFSET).cast().as_ptr(),
                label.len(),
            )
        }
    }
    pub fn into_parts(self) -> (NonNull<NodeHeader>, PtrData<V>) {
        (self.ptr, self.ptr_data)
    }

    #[inline]
    pub unsafe fn assume_init(self) -> Node<V> {
        Node {
            ptr: self.ptr,
            _marker: PhantomData,
        }
    }
}

unsafe impl<V: Send> Send for Node<V> {}
unsafe impl<V: Sync> Sync for Node<V> {}

impl NodeHeader {
    #[inline]
    fn initial_layout(label_len: usize) -> Layout {
        extend!(Layout::from_size_align(
            LABEL_OFFSET as usize + label_len,
            1
        ))
    }

    #[inline]
    pub fn ptr_data<V>(&self) -> PtrData<V> {
        let layout = Self::initial_layout(self.label_len as usize);
        let (mut layout, value_offset) = extend!(layout.extend(Layout::new::<Option<V>>()));

        let child_offset = if self.flags.contains(Flags::CHILD_ALLOCATED) {
            let (new_layout, offset) = extend!(layout.extend(Layout::new::<Node<V>>()));
            layout = new_layout;
            Some(offset)
        } else {
            None
        };
        let sibling_offset = if self.flags.contains(Flags::SIBLING_ALLOCATED) {
            let (new_layout, offset) = extend!(layout.extend(Layout::new::<Node<V>>()));
            layout = new_layout;
            Some(offset)
        } else {
            None
        };
        PtrData {
            layout: layout.pad_to_align(),
            value_offset,
            child_offset,
            sibling_offset,
            _marker: PhantomData,
        }
    }
}

impl<V> PtrData<V> {
    #[inline]
    pub fn allocate(self) -> NodePtrAndData<V> {
        unsafe {
            let ptr = alloc::alloc(self.layout) as *mut NodeHeader;
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
    pub fn dealloc(self, header_ptr: NonNull<NodeHeader>) {
        let layout = self.layout;

        // drop
        unsafe {
            let value_ptr = self.value_ptr(header_ptr);
            let _ = value_ptr.read();
            // could use ptr::read also
            // drop_in_place tears down the value, but if value
            // was a ptr, we would need to use ptr::read to drop
            // ptr::drop_in_place(value_ptr.as_ptr());
            if let Some(sibling_ptr) = self.sibling_ptr_init(header_ptr) {
                let _ = sibling_ptr.read();
            }
            if let Some(child_ptr) = self.child_ptr_init(header_ptr) {
                let _ = child_ptr.read();
            }
        }
        unsafe {
            alloc::dealloc(header_ptr.as_ptr().cast(), layout);
        }
    }

    #[inline]
    pub unsafe fn label<'a>(header_ptr: NonNull<NodeHeader>) -> &'a [u8] {
        unsafe {
            let label_len = (*header_ptr.as_ptr()).label_len as usize;
            slice::from_raw_parts(
                header_ptr.as_ptr().byte_offset(LABEL_OFFSET).cast(),
                label_len,
            )
        }
    }

    #[inline]
    pub unsafe fn label_mut<'a>(header_ptr: NonNull<NodeHeader>) -> &'a mut [u8] {
        unsafe {
            let label_len = (*header_ptr.as_ptr()).label_len as usize;
            slice::from_raw_parts_mut(
                header_ptr.as_ptr().byte_offset(LABEL_OFFSET).cast(),
                label_len,
            )
        }
    }
    #[inline]
    pub unsafe fn value_ptr(&self, header_ptr: NonNull<NodeHeader>) -> NonNull<Option<V>> {
        let offset = self.value_offset;
        unsafe { header_ptr.byte_offset(offset as isize).cast::<Option<V>>() }
    }

    #[inline]
    pub unsafe fn child_ptr_init(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> Option<NonNull<Node<V>>> {
        unsafe { self.child_ptr(header_ptr, Flags::CHILD_INITIALIZED) }
    }

    #[inline]
    pub unsafe fn child_ptr_alloc(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> Option<NonNull<Node<V>>> {
        unsafe { self.child_ptr(header_ptr, Flags::CHILD_ALLOCATED) }
    }

    #[inline]
    unsafe fn child_ptr(
        &self,
        header_ptr: NonNull<NodeHeader>,
        flags: Flags,
    ) -> Option<NonNull<Node<V>>> {
        if unsafe { *header_ptr.as_ptr() }.flags.contains(flags) {
            let offset = self.child_offset?;
            unsafe {
                return Some(header_ptr.byte_add(offset).cast());
            }
        }
        None
    }

    #[inline]
    pub unsafe fn sibling_ptr_init(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> Option<NonNull<Node<V>>> {
        unsafe { self.sibling_ptr(header_ptr, Flags::SIBLING_INITIALIZED) }
    }

    #[inline]
    pub unsafe fn sibling_ptr_alloc(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> Option<NonNull<Node<V>>> {
        unsafe { self.sibling_ptr(header_ptr, Flags::SIBLING_ALLOCATED) }
    }
    #[inline]
    unsafe fn sibling_ptr(
        &self,
        header_ptr: NonNull<NodeHeader>,
        flags: Flags,
    ) -> Option<NonNull<Node<V>>> {
        if unsafe { *header_ptr.as_ptr() }.flags.contains(flags) {
            let offset = self.sibling_offset?;
            unsafe {
                return Some(header_ptr.byte_add(offset).cast());
            }
        }
        None
    }
}
