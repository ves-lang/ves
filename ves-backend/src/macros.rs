#[macro_export]
macro_rules! unwrap_unchecked {
    ($self:ident, $which:ident) => {
        if let Self::$which(v) = $self {
            v
        } else if cfg!(debug_assertions) {
            unreachable!()
        } else {
            unsafe { std::hint::unreachable_unchecked() }
        }
    };
}
