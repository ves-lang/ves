pub mod view;

use std::{borrow::Cow, cell::Cell};

use ves_cc::{Cc, CcContext, Trace};

pub use self::view::VesStrView;

#[derive(Debug)]
pub struct VesStr {
    s: Cow<'static, str>,
    hash: Cell<Option<u64>>,
}

pub trait StrCcExt<T> {
    fn view(&self) -> T;
}

impl StrCcExt<VesStrView> for Cc<VesStr> {
    fn view(&self) -> VesStrView {
        VesStrView(self.clone())
    }
}

impl VesStr {
    pub fn new(s: Cow<'static, str>) -> Self {
        Self {
            s,
            hash: Cell::new(None),
        }
    }

    #[inline]
    pub fn on_heap<S: Into<Cow<'static, str>>>(ctx: &CcContext, s: S) -> Cc<Self> {
        ctx.cc(Self::new(s.into()))
    }

    #[inline]
    pub fn inner(&self) -> &Cow<'static, str> {
        &self.s
    }

    #[inline]
    pub fn clone_inner(&self) -> Cow<'static, str> {
        self.s.clone()
    }
}

impl From<&'static str> for VesStr {
    fn from(s: &'static str) -> Self {
        Self::new(Cow::Borrowed(s))
    }
}

impl From<String> for VesStr {
    fn from(s: String) -> Self {
        Self::new(Cow::Owned(s))
    }
}

impl std::ops::Deref for VesStr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &*self.s
    }
}

impl Trace for VesStr {
    fn trace(&self, _tracer: &mut ves_cc::Tracer) {}
}
