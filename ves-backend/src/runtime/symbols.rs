use crate::{
    gc::{GcHandle, VesGc},
    objects::ves_str::view::VesStrView,
};

pub struct SymbolTable<T: VesGc> {
    pub add: VesStrView,
    pub radd: VesStrView,
    pub sub: VesStrView,
    pub rsub: VesStrView,
    pub mul: VesStrView,
    pub rmul: VesStrView,
    pub div: VesStrView,
    pub rdiv: VesStrView,
    pub rem: VesStrView,
    pub rrem: VesStrView,
    pub pow: VesStrView,
    pub rpow: VesStrView,
    _gc: GcHandle<T>,
}

impl<T: VesGc> SymbolTable<T> {
    pub fn new(mut gc: GcHandle<T>) -> Self {
        Self {
            add: VesStrView::new(gc.alloc_permanent("add")),
            radd: VesStrView::new(gc.alloc_permanent("radd")),
            sub: VesStrView::new(gc.alloc_permanent("sub")),
            rsub: VesStrView::new(gc.alloc_permanent("rsub")),
            mul: VesStrView::new(gc.alloc_permanent("mul")),
            rmul: VesStrView::new(gc.alloc_permanent("rmul")),
            div: VesStrView::new(gc.alloc_permanent("div")),
            rdiv: VesStrView::new(gc.alloc_permanent("rdiv")),
            rem: VesStrView::new(gc.alloc_permanent("rem")),
            rrem: VesStrView::new(gc.alloc_permanent("rrem")),
            pow: VesStrView::new(gc.alloc_permanent("pow")),
            rpow: VesStrView::new(gc.alloc_permanent("rpow")),
            _gc: gc,
        }
    }
}

impl<T: VesGc> Clone for SymbolTable<T> {
    #[inline]
    fn clone(&self) -> SymbolTable<T> {
        SymbolTable {
            add: self.add,
            radd: self.radd,
            sub: self.sub,
            rsub: self.rsub,
            mul: self.mul,
            rmul: self.rmul,
            div: self.div,
            rdiv: self.rdiv,
            rem: self.rem,
            rrem: self.rrem,
            pow: self.pow,
            rpow: self.rpow,
            _gc: self._gc.clone(),
        }
    }
}
