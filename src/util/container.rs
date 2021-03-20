use std::cmp::Ordering;

/// A type that implements `Container<P>` divides all possible values of `P` into
/// cases enumerated by `Ordering`:
///
/// - `Ordering::Greater`: the point is within the container.
/// - `Ordering::Eq`: the point is on the boundary of the container.
/// - `Ordering::Less`: the point is outside the container.
///
/// Unlike `Ord`, there is no symmetry possible as the container and queried
/// value can have different types.
///
/// This is generally implemented for the relevant vector class of a field (e.g.
/// Point2) and more complex objects like halfspaces, polygons, and polyhedra.
pub trait Container<P> {
    fn contains(&self, p: &P) -> Ordering;
}

/// A type that implements `PartialContainer<P>`, like `Container<P>`, divides
/// the values of type into three classes.
///
/// However, it does not necessarily have a definition for all values of `P` and
/// `Self`. It thus returns an `Option<Ordering>`, similarly to `PartialEq` and
/// `PartialOrd`.
///
/// The transitive law of `Ord` is still expected to hold. `a > b` and `b > c`
/// implies that `a > c`. The same must hold for `==` and `<`.
///
/// `None` is expected if an appropriate ordering does not exist. Polygons that
/// are totally separate or that partially intersect are some examples.
pub trait PartialContainer<P> {
    fn partial_contains(&self, p: &P) -> Option<Ordering>;
}