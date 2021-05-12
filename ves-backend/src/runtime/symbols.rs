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
            _gc: gc,
        }
    }
}

impl<T: VesGc> Clone for SymbolTable<T> {
    #[inline]
    fn clone(&self) -> SymbolTable<T> {
        SymbolTable {
            add: self.add.clone(),
            radd: self.radd.clone(),
            sub: self.sub.clone(),
            rsub: self.rsub.clone(),
            mul: self.mul.clone(),
            rmul: self.rmul.clone(),
            div: self.div.clone(),
            rdiv: self.rdiv.clone(),
            rem: self.rem.clone(),
            rrem: self.rrem.clone(),
            _gc: self._gc.clone(),
        }
    }
}
