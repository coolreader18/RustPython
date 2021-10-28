//! const-safe version of https://docs.rs/field-offset

// TODO: replace with field_offset crate once that can be const

pub struct FieldOffset<T: ?Sized, U> {
    /// # Safety
    /// While this shouldn't be directly used by anyone, only the macro, FieldOffset provides
    /// "stable-deref"-like guarantees - for a given &T, field_offset.apply() should always return
    /// the exact same &U
    #[doc(hidden)]
    pub f: unsafe fn(*mut T) -> *mut U,
}

impl<T, U> Copy for FieldOffset<T, U> {}

impl<T, U> Clone for FieldOffset<T, U> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, U> FieldOffset<T, U> {
    #[inline]
    pub fn apply(self, x: &T) -> &U {
        unsafe { &*self.apply_ptr(x) }
    }

    #[inline]
    pub fn apply_mut(self, x: &mut T) -> &mut U {
        unsafe { &mut *self.apply_ptr_mut(x) }
    }

    /// # Safety
    /// The passed pointer must be derefenceable
    #[inline]
    pub unsafe fn apply_ptr(self, x: *const T) -> *const U {
        (self.f)(x as *mut T)
    }

    /// # Safety
    /// The passed pointer must be derefenceable
    #[inline]
    pub unsafe fn apply_ptr_mut(self, x: *mut T) -> *mut U {
        (self.f)(x)
    }
}

#[macro_export]
macro_rules! field_offset {
    ($parent:path, $field:tt) => {{
        $crate::field_offset::FieldOffset {
            f: unsafe { |x: *mut $parent| ::core::ptr::addr_of_mut!((*x).$field) },
        }
    }};
}
