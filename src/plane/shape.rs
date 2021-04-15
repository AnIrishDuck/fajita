use crate::plane::Point2;
use crate::plane::polygon::{FlatPolygon2, Vertex2};
use std::collections::HashMap;
use std::iter;
use crate::util::container::{Container, Orientation};
use crate::util::knife::{Knife, Parts};

#[derive(Clone)]
pub struct IndexedPolygon {
    pub point_ixs: Vec<usize>
}

#[derive(Clone)]
pub struct FlatShape2 {
    pub points: im::Vector<Point2>,
    pub polygons: im::Vector<IndexedPolygon>
}

impl FlatShape2 {
    fn extend<I>(&mut self, it: I)
    where I: IntoIterator<Item=FlatPolygon2> {
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

    fn flat_polygons(&self) -> impl Iterator<Item=FlatPolygon2> + '_ {
        self.polygons.iter().map(move |p| {
            let vertices = p.point_ixs.iter().map(|point_ix| {
                Vertex2 {
                    index: Some(*point_ix),
                    point: self.points[*point_ix]
                }
            }).collect();

            FlatPolygon2 { vertices }
        })
    }

    fn into_flat_polygons(self) -> impl Iterator<Item=FlatPolygon2> {
        let points = self.points;
        self.polygons.into_iter().map(move |p| {
            let vertices = p.point_ixs.iter().map(|point_ix| {
                Vertex2 {
                    index: Some(*point_ix),
                    point: points[*point_ix]
                }
            }).collect();

            FlatPolygon2 { vertices }
        })
    }

    fn backed_empty(&self) -> FlatShape2 {
        FlatShape2 { points: self.points.clone(), polygons: im::Vector::new() }
    }

    fn non_empty(self) -> Option<FlatShape2> {
        if self.polygons.len() > 0 {
            Some(self)
        } else {
            None
        }
    }

    pub fn union(mut self, other: &FlatShape2) -> FlatShape2 {
        let parts = self.cut(&other);
        self.extend(parts.outside.into_iter().flat_map(|p| p.into_flat_polygons()));
        self
    }

    pub fn intersect(&self, other: &FlatShape2) -> Option<FlatShape2> {
        self.cut(&other).inside
    }

    pub fn remove(&self, other: &FlatShape2) -> Option<FlatShape2> {
        other.cut(&self).outside
    }
}

impl Knife<&FlatShape2, Option<FlatShape2>, Vec<Vertex2>> for FlatPolygon2
{
    fn cut(&self, target: &FlatShape2) -> Parts<Option<FlatShape2>, Vec<Vertex2>> {
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

impl Knife<&FlatShape2, Option<FlatShape2>, Vec<Vertex2>> for FlatShape2
{
    fn cut(&self, target: &FlatShape2) -> Parts<Option<FlatShape2>, Vec<Vertex2>> {
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

impl Container<Point2> for FlatShape2 {
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
    /// # use fajita::plane::shape::FlatShape2;
    /// # use fajita::plane::shapes::rectangle;
    /// # use fajita::util::container::{Container, Orientation};
    /// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// let s: FlatShape2 = r.into();
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

impl From<FlatPolygon2> for FlatShape2 {
    fn from(poly: FlatPolygon2) -> FlatShape2 {
        let mut shape = FlatShape2 {
            points: im::Vector::new(),
            polygons: im::Vector::new()
        };

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

    fn assert_union_ok(a: &FlatShape2, b: &FlatShape2) {
        let result = a.clone().union(b);

        for part in result.flat_polygons() {
            for point in part.points() {
                assert!(
                    a.contains(&point) != Orientation::Out
                    || b.contains(&point) != Orientation::Out,
                    format!("point {:?} not in a or b", point)
                )
            }
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
    fn test_simple_union() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = rectangle(p2(0.5, 0.5), v2(1.0, 1.0));

        assert_union_ok(&a.into(), &b.into());
    }
}