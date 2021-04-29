//! Defines a [`Shape2`] that is a union of many disjoint [`Polygon2`]. Can be
//! used to model arbitrary two-dimensional shapes, including concave polygons
//! and shapes with holes.
//!
//! Shapes, like polygons, also are [`Point2`] containers.
use crate::plane::Point2;
use crate::plane::polygon::{Polygon2, Vertex2};
use std::collections::HashMap;
use std::iter;
use crate::util::container::{Container, Orientation};
use crate::util::knife::{Knife, Parts};

#[derive(Clone)]
struct IndexedPolygon {
    point_ixs: Vec<usize>
}

/// A union of one or more [`Polygon2`].
///
/// Must obey two laws:
/// - **non-zero**: must contain at least one polygon.
/// - **non-overlapping**: the intersection of any two polygons must be zero.
///
/// Also, all polygon parts must obey the associated [`Polygon2`] laws.
///
/// Corresponding violations are tracked via the [`ShapeError`] enum.
#[derive(Clone)]
pub struct Shape2 {
    points: im::Vector<Point2>,
    polygons: im::Vector<IndexedPolygon>
}

/// Possible violations of the [`Shape2`] laws.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ShapeError {
    Zero,
    BadPolygon,
    Overlapping
}

impl Shape2 {
    fn empty() -> Self {
        Shape2 {
            points: im::Vector::new(),
            polygons: im::Vector::new()
        }
    }

    fn extend<I>(&mut self, it: I)
    where I: IntoIterator<Item=Polygon2> {
        let mut points: HashMap<_, _> = self.points.iter().enumerate()
            .map(|(ix, p)| (exact_hash(p), ix)).collect();

        for polygon in it.into_iter() {
            let point_ixs: Vec<usize> = polygon.vertices.into_iter().map(|v| {
                v.index.filter(|i| self.points.get(*i) == Some(&v.point)).unwrap_or_else(|| {
                    let p = v.point;
                    points.get(&exact_hash(&p)).cloned().unwrap_or_else(|| {
                        let ix = self.points.len();
                        self.points.push_back(p.clone());
                        points.insert(exact_hash(&p), ix);
                        ix
                    })
                })
            }).collect();

            self.polygons.push_back(IndexedPolygon { point_ixs })
        }
    }

    fn flat_polygons(&self) -> impl Iterator<Item=Polygon2> + '_ {
        self.polygons.iter().map(move |p| {
            let vertices = p.point_ixs.iter().map(|point_ix| {
                Vertex2 {
                    index: Some(*point_ix),
                    reverse: false,
                    point: self.points[*point_ix]
                }
            }).collect();

            Polygon2 { vertices }
        })
    }

    fn into_flat_polygons(self) -> impl Iterator<Item=Polygon2> {
        let points = self.points;
        self.polygons.into_iter().map(move |p| {
            let vertices = p.point_ixs.iter().map(|point_ix| {
                Vertex2 {
                    index: Some(*point_ix),
                    reverse: false,
                    point: points[*point_ix]
                }
            }).collect();

            Polygon2 { vertices }
        })
    }

    fn backed_empty(&self) -> Shape2 {
        Shape2 { points: self.points.clone(), polygons: im::Vector::new() }
    }

    fn non_empty(self) -> Option<Shape2> {
        if self.polygons.len() > 0 {
            Some(self)
        } else {
            None
        }
    }

    /// Find the union of this shape and the `other` shape, eliminating any
    /// overlapping polygons.
    pub fn union(mut self, other: &Shape2) -> Shape2 {
        let parts = self.cut(other);
        self.extend(parts.outside.into_iter().flat_map(|p| p.into_flat_polygons()));
        self
    }

    pub fn intersect(&self, other: &Shape2) -> Option<Shape2> {
        self.cut(other).inside
    }

    /// Remove all parts of the `other` shape also contained in this shape,
    /// potentially resulting in no shape at all (e.g. `self.remove(&self)`).
    pub fn remove(&self, other: &Shape2) -> Option<Shape2> {
        other.cut(self).outside
    }

    /// Verify this shape follows all associated laws.
    pub fn validate(&self) -> Option<ShapeError> {
        if self.polygons.len() == 0 {
            return Some(ShapeError::Zero)
        }

        for (ix, polygon) in self.flat_polygons().enumerate() {
            if polygon.validate().is_some() {
                return Some(ShapeError::BadPolygon)
            }

            for (other_ix, other) in self.flat_polygons().enumerate() {
                if ix != other_ix {
                    let shape: Shape2 = polygon.clone().into();
                    let intersect = shape.intersect(&other.clone().into());
                    if intersect.is_some() {
                        return Some(ShapeError::Overlapping)
                    }
                }
            }
        }

        None
    }
}

impl Knife<&Shape2> for Polygon2
{
    type Output = Option<Shape2>;
    type Tangent = Vec<Vertex2>;

    fn cut(&self, target: &Shape2) -> Parts<Option<Shape2>, Vec<Vertex2>> {
        let mut in_parts = target.backed_empty();
        let mut out_parts = target.backed_empty();
        let mut tangent = vec![];

        for polygon in target.flat_polygons() {
            let parts = self.cut(polygon);
            in_parts.extend(parts.inside);
            out_parts.extend(parts.outside);
            tangent.extend(parts.tangent);
        }

        let inside = in_parts.non_empty();
        let outside = out_parts.non_empty();

        Parts { inside, outside, tangent }
    }
}

impl Knife<&Shape2> for Shape2
{
    type Output = Option<Shape2>;
    type Tangent = Vec<Vertex2>;
    fn cut(&self, target: &Shape2) -> Parts<Option<Shape2>, Vec<Vertex2>> {
        let mut remains = target.clone();
        let mut in_parts = target.backed_empty();
        let mut tangent = vec![];

        for polygon in self.flat_polygons() {
            let parts = polygon.cut(&remains);
            in_parts.extend(parts.inside.into_iter().flat_map(|p| p.into_flat_polygons()));
            remains = parts.outside.unwrap_or(self.backed_empty());
            tangent.extend(parts.tangent);
        }

        let inside = in_parts.non_empty();
        let outside = remains.non_empty();

        Parts { inside, outside, tangent }
    }
}

impl Container<Point2> for Shape2 {
    /// Compares the given point to this shape:
    ///
    /// - if `p` is in `self`, then `self > p`
    /// - if `p` is tangent to some segment in `self`, then `self == p`
    /// - if `p` is outside of `poly`, then `self < p`
    ///
    /// Examples:
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::shape::Shape2;
    /// # use fajita::plane::shapes::rectangle;
    /// # use fajita::util::container::{Container, Orientation};
    /// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// let s: Shape2 = r.into();
    /// assert_eq!(s.contains(&p2(0.5, 0.5)), Orientation::In);
    /// assert_eq!(s.contains(&p2(0.5, 0.0)), Orientation::On);
    /// assert_eq!(s.contains(&p2(0.5, 2.0)), Orientation::Out);
    /// ```
    fn contains(&self, p: &Point2) -> Orientation {
        let mut prior_equal = false;
        for polygon in self.flat_polygons() {
            match polygon.contains(p) {
                Orientation::In => return Orientation::In,
                Orientation::On => {
                    if prior_equal {
                        return Orientation::In
                    }
                    prior_equal = true;
                },
                _ => ()
            }
        }

        if prior_equal { Orientation::On } else { Orientation::Out }
    }
}

impl From<Polygon2> for Shape2 {
    fn from(poly: Polygon2) -> Shape2 {
        let mut shape = Shape2::empty();

        shape.extend(iter::once(poly));

        shape
    }
}

// Note that this has all the obvious issues with floating point comparisons
fn exact_hash(p: &Point2) -> (u64, u64) {
    (p.x.to_bits(), p.y.to_bits())
}

#[cfg(test)]
mod test {
    use crate::plane::{p2, v2};
    use crate::plane::shapes::rectangle;
    use super::*;

    fn assert_union_ok(a: &Shape2, b: &Shape2) {
        let result = a.clone().union(b);

        assert_eq!(result.validate(), None);

        for part in result.flat_polygons() {
            for point in part.points() {
                assert!(
                    a.contains(&point) != Orientation::Out
                    || b.contains(&point) != Orientation::Out,
                    format!("point {:?} not in a or b", point)
                )
            }

            assert!(
                a.intersect(&part.clone().into()).is_some()
                || b.intersect(&part.clone().into()).is_some()
            );
        }

        for part in a.flat_polygons().chain(b.flat_polygons()) {
            for point in part.points() {
                assert!(
                    result.contains(&point) != Orientation::Out,
                    format!("point {:?} not in final shape", point)
                )
            }
        }
    }

    #[test]
    fn test_validation() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = rectangle(p2(0.5, 0.5), v2(1.0, 1.0));

        let mut shape = Shape2::empty();
        assert_eq!(shape.validate(), Some(ShapeError::Zero));

        shape.extend(vec![a, b]);
        assert_eq!(shape.validate(), Some(ShapeError::Overlapping));
    }

    #[test]
    fn test_extension() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = rectangle(p2(1.0, 0.0), v2(1.0, 1.0));

        let mut shape = Shape2::empty();
        shape.extend(vec![a, b]);
        assert_eq!(shape.points.len(), 6);
    }

    #[test]
    fn test_simple_union() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = rectangle(p2(0.5, 0.5), v2(1.0, 1.0));

        assert_union_ok(&a.into(), &b.into());
    }
}