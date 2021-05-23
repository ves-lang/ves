use crate::{
    gc::{GcHandle, VesGc},
    values::strings::StrView,
};

macro_rules! symbol_table {
    ($($symbol:ident),*) => {
        pub struct SymbolTable<T: VesGc> {
            $( pub $symbol: StrView, )*
            _gc: GcHandle<T>
        }
        impl<T: VesGc> SymbolTable<T> {
            pub fn new(mut gc: GcHandle<T>) -> Self {
                Self {
                    $( $symbol: StrView::new(gc.alloc_permanent(stringify!($symbol))), )*
                    _gc: gc
                }
            }
        }
        impl<T: VesGc> Clone for SymbolTable<T> {
            #[inline]
            fn clone(&self) -> SymbolTable<T> {
                SymbolTable {
                    $( $symbol: self.$symbol, )*
                    _gc: self._gc.clone(),
                }
            }
        }
    }
}

// NOTE: whenever this is changed, go to resolver.rs:validate_magic_method and change it there, too
// TODO: somehow resolve this duplication
symbol_table! {
    init, add, radd, sub, rsub, mul, rmul, div, rdiv, rem, rrem, pow, rpow, cmp, str
}
