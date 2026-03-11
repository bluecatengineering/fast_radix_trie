use core::{
    alloc::Layout,
    marker::PhantomData,
    ptr::{self, NonNull},
    slice,
};

use alloc::alloc;

use crate::{node::Node, node_common::extend};

const LABEL_OFFSET: isize = core::mem::size_of::<NodeHeader>() as isize;

// these are the sized values that we know on initial allocation of a node
// we know the label length and the number of children. The offsets of
// other values can be determined dynamically based on these values.
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
    /// writes header
    /// # Safety
    /// Header values must always be in alignment with the offsets of the allocation
    /// If you create a node, then write a header with different label/children lens, you
    /// will have UB on accessing elements of the node
    #[inline]
    pub(crate) unsafe fn write_header(&mut self, header: NodeHeader) {
        unsafe { self.ptr.write(header) }
    }

    /// writes value at offset calculated via header
    /// # Safety
    /// Value offset must point to a spot in memory sized correctly to hold the
    /// value.
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

    /// write children nodes to child offset (if children_len > 0)
    /// # Safety
    /// node must have been sized with the same child alignment and size.
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

    /// get children pointer
    /// # Safety
    /// header pointer must point to an allocation with the same layout in `ptr_data`
    /// header pointer must point to allocation large enough to contain the offset pointer
    #[inline]
    pub(crate) unsafe fn children_ptr(&self) -> Option<NonNull<Node<V>>> {
        unsafe { self.ptr_data.children_ptr(self.ptr) }
    }

    /// get value pointer
    /// # Safety
    /// header pointer must point to an allocation with the same layout in `ptr_data`
    /// header pointer must point to allocation large enough to contain the offset pointer
    #[allow(dead_code)]
    #[inline]
    pub(crate) unsafe fn value_ptr(&self) -> NonNull<Option<V>> {
        unsafe { self.ptr_data.value_ptr(self.ptr) }
    }

    /// label pointer
    /// # Safety
    /// - `self.ptr` must point to a valid allocation with at least `LABEL_OFFSET` bytes
    /// - The allocation must remain valid for the duration of the returned pointer's use
    /// - The label region must have been initialized
    #[inline]
    pub(crate) unsafe fn label_ptr(&self) -> NonNull<u8> {
        // Safety:
        // - `byte_offset(LABEL_OFFSET)` is safe because the allocation is guaranteed
        //   to be at least LABEL_OFFSET bytes (size of NodeHeader) plus label_len
        // - The cast to *mut u8 is valid for the label data
        unsafe { self.ptr.byte_offset(LABEL_OFFSET).cast() }
    }

    /// Writes the label bytes to the allocated label region
    ///
    /// # Safety
    /// - `self.ptr` must point to a valid allocation with sufficient space for the label
    /// - The label region (starting at `LABEL_OFFSET`) must have been allocated with enough space
    ///   to hold `label.len()` bytes
    /// - The label region must not overlap with `label` source data
    #[inline]
    pub(crate) unsafe fn write_label(&mut self, label: &[u8]) {
        // Safety:
        // - `byte_offset(LABEL_OFFSET)` is safe because the allocation includes space for the header and label
        // - `copy_nonoverlapping` is safe because:
        //   - Both pointers are valid and properly aligned
        //   - The destination has been allocated with sufficient space
        //   - The source and destination do not overlap (label comes from outside the node allocation)
        //   - The count (label.len()) is valid for both source and destination
        unsafe {
            ptr::copy_nonoverlapping(
                label.as_ptr(),
                self.ptr.byte_offset(LABEL_OFFSET).cast().as_ptr(),
                label.len(),
            )
        }
    }

    #[allow(unused)]
    #[inline]
    pub(crate) fn into_parts(self) -> (NonNull<NodeHeader>, PtrData<V>) {
        (self.ptr, self.ptr_data)
    }

    /// # Safety:
    /// all of the nodes fields must have been initialized
    /// with valid data after allocation
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
    /// Allocates memory for a node with this layout
    ///
    /// Returns a `NodePtrAndData` with an uninitialized allocation.
    /// The caller must initialize all fields before using the node.
    #[inline]
    pub(crate) fn allocate(self) -> NodePtrAndData<V> {
        // Safety:
        // - `alloc::alloc` is called with a valid layout (self.layout)
        // - If allocation fails, we call `handle_alloc_error` which aborts
        // - The returned pointer is checked for null and wrapped in NonNull
        // - The pointer is properly aligned according to the layout
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
    /// The caller must ensure that children and value are not accessed after this call.
    #[inline]
    pub(crate) unsafe fn dealloc_forget(self, header_ptr: NonNull<NodeHeader>) {
        // Safety:
        // - `header_ptr` must point to a valid allocation created with `self.layout`
        // - The caller guarantees that contents (children/value) have been moved out
        // - The layout matches the one used during allocation
        unsafe {
            alloc::dealloc(header_ptr.as_ptr().cast(), self.layout);
        }
    }

    /// Deallocates the node and drops all its contents
    ///
    /// # Safety
    /// - The layout in dealloc must match the layout used with alloc
    /// - `header_ptr` must point to a valid, fully initialized node allocation
    /// - The node's contents (value and children) must be valid and initialized
    /// - This function must not be called more than once on the same allocation
    #[inline]
    pub(crate) fn dealloc(self, header_ptr: NonNull<NodeHeader>) {
        let layout = self.layout;
        // Safety:
        // - `value_ptr` and `children_mut` return valid pointers to initialized data
        // - `drop_in_place` properly drops the Option<V> value
        // - `drop_in_place` on the children slice drops all children nodes
        // - After dropping, we deallocate with the same layout used for allocation
        unsafe {
            // drop_in_place tears down the value, but if value
            // was a ptr (like the child/sibling), we would need to use ptr::read to drop
            self.value_ptr(header_ptr).drop_in_place();
            (&raw mut *self.children_mut(header_ptr)).drop_in_place();

            alloc::dealloc(header_ptr.as_ptr().cast(), layout);
        }
    }

    /// Returns a reference to the label bytes of a node
    ///
    /// # Safety
    /// - `header_ptr` must point to a valid, initialized NodeHeader
    /// - The label region must have been initialized with `label_len` bytes
    /// - The returned lifetime 'a must not outlive the node allocation
    #[inline]
    pub(crate) unsafe fn label<'a>(header_ptr: NonNull<NodeHeader>) -> &'a [u8] {
        // Safety:
        // - `header_ptr.as_ptr()` dereference is safe because header_ptr is NonNull and valid
        // - `byte_offset(LABEL_OFFSET)` is safe because the allocation includes the label
        // - `from_raw_parts` is safe because:
        //   - The pointer is valid and properly aligned
        //   - `label_len` bytes have been initialized
        //   - The lifetime is tied to the input parameter, not the pointer
        unsafe {
            let label_len = (*header_ptr.as_ptr()).label_len as usize;
            slice::from_raw_parts(
                header_ptr.as_ptr().byte_offset(LABEL_OFFSET).cast(),
                label_len,
            )
        }
    }

    /// Returns a mutable reference to the label bytes of a node
    ///
    /// # Safety
    /// - `header_ptr` must point to a valid, initialized NodeHeader
    /// - The label region must have been initialized with `label_len` bytes
    /// - The returned lifetime 'a must not outlive the node allocation
    /// - No other references to the label must exist when this is called
    #[allow(unused)]
    #[inline]
    pub(crate) unsafe fn label_mut<'a>(header_ptr: NonNull<NodeHeader>) -> &'a mut [u8] {
        // Safety:
        // - `header_ptr.as_ptr()` dereference is safe because header_ptr is NonNull and valid
        // - `byte_offset(LABEL_OFFSET)` is safe because the allocation includes the label
        // - `from_raw_parts_mut` is safe because:
        //   - The pointer is valid and properly aligned
        //   - `label_len` bytes have been initialized
        //   - The lifetime is tied to the input parameter
        //   - We have exclusive access (guaranteed by caller)
        unsafe {
            let label_len = (*header_ptr.as_ptr()).label_len as usize;
            slice::from_raw_parts_mut(
                header_ptr.as_ptr().byte_offset(LABEL_OFFSET).cast(),
                label_len,
            )
        }
    }
    /// Returns a pointer to the value field of a node
    ///
    /// # Safety
    /// - `header_ptr` must point to a valid NodeHeader  
    /// - The value region must exist at the calculated offset
    /// - The allocation must be large enough to contain the value at the offset
    #[inline]
    pub(crate) unsafe fn value_ptr(&self, header_ptr: NonNull<NodeHeader>) -> NonNull<Option<V>> {
        let offset = self.value_offset;
        // Safety:
        // - `byte_offset` is safe because value_offset was calculated during layout creation
        // - The cast is safe because the allocation includes space for Option<V> at this offset
        // - The offset is guaranteed to be within the allocated region
        unsafe { header_ptr.byte_offset(offset as isize).cast::<Option<V>>() }
    }

    /// Returns a reference to the children slice of a node
    ///
    /// # Safety
    /// - `header_ptr` must point to a valid, initialized NodeHeader
    /// - If children exist (children_len > 0), they must have been initialized
    /// - The returned lifetime 'a must not outlive the node allocation
    #[inline]
    pub(crate) unsafe fn children<'a>(&self, header_ptr: NonNull<NodeHeader>) -> &'a [Node<V>] {
        // Safety:
        // - `children_ptr` returns a valid pointer if children_offset is Some
        // - `from_raw_parts` is safe because:
        //   - The pointer is valid and properly aligned
        //   - `children_len` nodes have been initialized
        //   - The lifetime is tied to the input parameter
        if let Some(ptr) = unsafe { self.children_ptr(header_ptr) } {
            unsafe {
                let children_len = (*header_ptr.as_ptr()).children_len as usize;
                slice::from_raw_parts(ptr.as_ptr(), children_len)
            }
        } else {
            &[]
        }
    }

    /// Returns an optional pointer to the children array start
    ///
    /// # Safety
    /// - `header_ptr` must point to a valid NodeHeader
    /// - If children_offset is Some, the allocation must include space for the children array
    #[inline]
    pub(crate) unsafe fn children_ptr(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> Option<NonNull<Node<V>>> {
        // Safety:
        // - If children_offset is Some, `byte_add` is safe because the allocation includes room for children
        // - The cast is safe because the allocation was laid out with Node<V> array at this offset
        self.children_offset
            .map(|offset| unsafe { header_ptr.byte_add(offset).cast::<Node<V>>() })
    }

    /// Returns a mutable reference to the children slice of a node
    ///
    /// # Safety
    /// - `header_ptr` must point to a valid, initialized NodeHeader
    /// - If children exist (children_len > 0), they must have been initialized
    /// - The returned lifetime 'a must not outlive the node allocation
    /// - No other references to the children must exist when this is called
    #[inline]
    pub(crate) unsafe fn children_mut<'a>(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> &'a mut [Node<V>] {
        // Safety:
        // - `children_ptr` returns a valid pointer if children_offset is Some
        // - `from_raw_parts_mut` is safe because:
        //   - The pointer is valid and properly aligned
        //   - `children_len` nodes have been initialized
        //   - The lifetime is tied to the input parameter
        //   - We have exclusive access (guaranteed by caller)
        if let Some(ptr) = unsafe { self.children_ptr(header_ptr) } {
            unsafe {
                let children_len = (*header_ptr.as_ptr()).children_len as usize;
                slice::from_raw_parts_mut(ptr.as_ptr(), children_len)
            }
        } else {
            &mut []
        }
    }

    /// Returns an optional mutable reference to the children slice of a node
    ///
    /// # Safety
    /// - `header_ptr` must point to a valid, initialized NodeHeader
    /// - If children exist (children_len > 0), they must have been initialized
    /// - The returned lifetime 'a must not outlive the node allocation
    /// - No other references to the children must exist when this is called
    #[inline]
    pub(crate) unsafe fn children_mut_opt<'a>(
        &self,
        header_ptr: NonNull<NodeHeader>,
    ) -> Option<&'a mut [Node<V>]> {
        // Safety:
        // - `children_ptr` returns a valid pointer if children_offset is Some
        // - `from_raw_parts_mut` is safe because:
        //   - The pointer is valid and properly aligned
        //   - `children_len` nodes have been initialized
        //   - The lifetime is tied to the input parameter
        //   - We have exclusive access (guaranteed by caller)
        match unsafe { self.children_ptr(header_ptr) } {
            Some(ptr) => unsafe {
                let children_len = (*header_ptr.as_ptr()).children_len as usize;
                Some(slice::from_raw_parts_mut(ptr.as_ptr(), children_len))
            },
            None => None,
        }
    }
}
