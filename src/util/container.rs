#[derive(Debug, Eq, PartialEq)]
pub enum Orientation {
    In,
    On,
    Out
}

use Orientation::*;
impl Orientation {
    pub fn reverse(self) -> Self {
        match self {
            In => Out,
            On => On,
            Out => In
        }
    }
}

/// A type that implements `Container<P>` divides all possible values of `P` into
/// cases enumerated by `Orientation`:
///
/// Unlike `Ord`, there is no symmetry possible as the container and queried
/// value can have different types.
///
/// This is generally implemented for the relevant vector class of a field (e.g.
/// Point2) and more complex objects like halfspaces, polygons, and polyhedra.
pub trait Container<P> {
    fn contains(&self, p: &P) -> Orientation;
}

/// A type that implements `PartialContainer<P>`, like `Container<P>`, divides
/// the values of a given type into three possible states.
///
/// However, it does not necessarily have a definition for all values of `P` and
/// `Self`. It thus returns an `Option<Orientation>`, similarly to `PartialEq` and
/// `PartialOrd`.
///
/// If `P` is `Self`, the transitive law analogous to `Ord` is expected to hold.
/// `a in b` and `b in c` implies that `a in c`.
///
/// `None` is expected if an appropriate ordering does not exist. Polygons that
/// are totally separate or that partially intersect are some examples.
pub trait PartialContainer<P> {
    fn partial_contains(&self, p: &P) -> Option<Orientation>;
}