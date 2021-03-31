use crate::util::container::Orientation;

pub struct Parts<P, T> {
    pub inside: P,
    pub tangent: T,
    pub outside: P
}

impl <IP, IT> Default for Parts<Option<IP>, Option<IT>> {
    fn default() -> Self {
        Parts {
            inside: None,
            tangent: None,
            outside: None
        }
    }
}

impl <IP, IT> Parts<Option<IP>, Option<IT>> {
    pub fn orient(o: Orientation, p: IP, tangent: Option<IT>) -> Self {
        match o {
            Orientation::In => Parts { inside: Some(p), tangent, outside: None },
            Orientation::Out => Parts { inside: None, tangent, outside: Some(p) },
            Orientation::On => Parts { tangent, ..Default::default() }
        }
    }
}

/// A type that implements `Knife<I, P, T>` is a more advanced variant
/// of `Container<P>`. It divides an input type `I` into an inside part `P`,
/// a tangent part `T`, and an outside part that must also be `P`.
///
/// The key invariant is that all returned inner / outer parts must be in or on
/// the original input.
pub trait Knife<I, P, T> {
    fn cut(&self, input: I) -> Parts<P, T>;
}