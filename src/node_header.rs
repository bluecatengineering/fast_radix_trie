use core::{
    alloc::Layout,
    marker::PhantomData,
    ptr::{self, NonNull},
    slice,
};

use alloc::alloc;

use crate::{node::Node, node_common::extend};

const LABEL_OFFSET: isize = core::mem::size_of::<NodeHeader>() as isize;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct NodeHeader {
    pub(crate) label_len: u8,
    pub(crate) children_len: u8,
}

pub(crate) struct PtrData<V> {
    pub(crate) layout: Layout,
    pub(crate) children_offset: Option<usize>,
    pub(crate) value_offset: usize,
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
    pub(crate) unsafe fn write_value(&mut self, value: Option<V>) {
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
    pub(crate) unsafe fn value_ptr(&self) -> NonNull<Option<V>> {
        unsafe { self.ptr_data.value_ptr(self.ptr) }
    }

    #[inline]
    pub(crate) unsafe fn label_ptr(&self) -> NonNull<u8> {
        unsafe { self.ptr.byte_offset(LABEL_OFFSET).cast() }
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

        let (layout, children_offset) = if self.children_len > 0 {
            let (new_layout, offset) = extend!(layout.extend(extend!(Layout::array::<Node<V>>(
                self.children_len as usize
            ))));
            (new_layout, Some(offset))
        } else {
            // because we use re-alloc we must always include this in layout because it affects the alignment
            // there are basically two options:
            // - have nodes with different alignments and optional offsets using the flags BUT
            // we must never use realloc because the alignment could change
            // - keep the alignment consistent and use realloc
            //
            // The first will minimize memory usage at the cost of slower mutations
            // the second will make mutations faster but use more memory because of potentially larger
            // padding/always allocated parts of layout (like the value)
            let (new_layout, _offset) =
                extend!(layout.extend(extend!(Layout::array::<Node<V>>(0))));
            (new_layout, None)
        };

        let (layout, value_offset) = extend!(layout.extend(Layout::new::<Option<V>>()));

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
    pub(crate) fn dealloc(self, header_ptr: NonNull<NodeHeader>) {
        let layout = self.layout;
        unsafe {
            // drop_in_place tears down the value, but if value
            // was a ptr (like the child/sibling), we would need to use ptr::read to drop
            self.value_ptr(header_ptr).drop_in_place();
            (&raw mut *self.children_mut(header_ptr)).drop_in_place();

            alloc::dealloc(header_ptr.as_ptr().cast(), layout);
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
    pub(crate) unsafe fn value_ptr(&self, header_ptr: NonNull<NodeHeader>) -> NonNull<Option<V>> {
        let offset = self.value_offset;
        unsafe { header_ptr.byte_offset(offset as isize).cast::<Option<V>>() }
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
    pub(crate) unsafe fn children_mut_opt<'a>(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> Option<&'a mut [Node<V>]> {
        match unsafe { self.children_ptr(header_ptr) } {
            Some(ptr) => unsafe {
                let children_len = (*header_ptr.as_ptr()).children_len as usize;
                Some(slice::from_raw_parts_mut(ptr.as_ptr(), children_len))
            },
            None => None,
        }
    }
}
