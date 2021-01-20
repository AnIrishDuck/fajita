use std::borrow::Borrow;
use std::sync::Arc;
use std::collections::HashMap;
use std::cmp::Ordering;
use std::fmt;
use std::iter;
use std::ops;
use cgmath::EuclideanSpace;

use crate::plane::{v2, LineSegment2, Point2, Vector2};
use crate::plane::line::Halfspace2;
use crate::plane::pool::Pool2;

#[derive(Copy, Clone, Debug)]
pub struct LineIs {
    pub a: usize,
    pub b: usize,
}

#[derive(Clone, Debug)]
pub struct HalfspaceIs {
    pub line_index: usize,
    pub normal: Vector2
}

#[derive(Clone, Debug)]
pub struct PolygonIs {
    pub halfspaces: Vec<HalfspaceIs>
}

#[derive(Clone)]
pub struct Polygon2<R>
    where R: Clone + Borrow<Pool2>
{
    pub pool: R,
    pub index: usize
}

impl<R> Polygon2<R>
    where R: Clone + Borrow<Pool2>
    {

    pub fn halfspaces(&self) -> impl Iterator<Item=Halfspace2> + '_ {
        let pool = self.pool.borrow();
        let indices = &pool.polygons[self.index];
        indices.halfspaces.iter().map(move |hs| {
            let line = pool.lines[hs.line_index];
            let line = LineSegment2::new(
                pool.points[line.a],
                pool.points[line.b]
            );
            Halfspace2 {
                normal: hs.normal,
                line
            }
        })
    }

    /// Compares the given point to this polygon:
    ///
    /// - if `p` is in `poly`, then `p < poly`
    /// - if `p` is tangent to some segment in `poly`, then `p == poly`
    /// - if `p` is outside of `poly`, then `p > poly`
    ///
    /// Examples:
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::shapes::rectangle;
    /// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// assert_eq!(r.cmp_point(p2(0.5, 0.5)), Ordering::Less);
    /// assert_eq!(r.cmp_point(p2(0.5, 0.0)), Ordering::Equal);
    /// assert_eq!(r.cmp_point(p2(0.5, 2.0)), Ordering::Greater);
    /// ```
    pub fn cmp_point(&self, point: Point2) -> Ordering {
        let mut it = self.halfspaces().filter_map(|space| {
            let ord = space.contains_point(point);
            if ord == Ordering::Less {
                None
            } else {
                Some(ord)
            }
        });


        let positive = it.map(|v| {
            if v == Ordering::Greater { 1 } else { 0 }
        }).max();

        match positive {
            Some(v) => {
                if v > 0 { Ordering::Greater } else { Ordering::Equal }
            }
            None => Ordering::Less
        }
    }

    pub fn ring(&self) -> Vec<Point2> {
        let pool = self.pool.borrow();
        let indices = &pool.polygons[self.index];
        let mut ends: HashMap<usize, Vec<LineIs>> = HashMap::new();
        for h in &indices.halfspaces {
            let l = pool.lines[h.line_index];
            ends.entry(l.a).or_insert(vec![]).push(l);
            ends.entry(l.b).or_insert(vec![]).push(l);
        }
        let start = pool.lines[indices.halfspaces[0].line_index];
        let mut prior: usize = start.a;
        let mut current: usize = start.b;
        indices.halfspaces.iter().map(|_| {
            let old_prior = current;
            current = ends[&current].iter()
                .filter(|l| l.a != prior && l.b != prior)
                .flat_map(|l| iter::once(l.a).chain(iter::once(l.b)))
                .filter(|p| *p != current)
                .next().unwrap();
            prior = old_prior;
            pool.points[old_prior]
        }).collect()
    }

    pub fn center(&self) -> Point2 {
        let ring = self.ring();
        let sum: Vector2 = ring.iter().map(|p| p.to_vec()).sum();
        Point2::from_vec(sum / ring.len() as f64)
    }

    pub fn unlink(&self) -> Polygon2<Pool2> {
        let pool = self.pool.borrow().clone();
        Polygon2 {
            pool, index: self.index
        }
    }
}

impl<R1, R2> PartialEq<Polygon2<R2>> for Polygon2<R1>
    where R1: Clone + Borrow<Pool2>,
          R2: Clone + Borrow<Pool2> {
    fn eq(&self, other: &Polygon2<R2>) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl <R> ops::Add<Vector2> for Polygon2<R>
    where R: Clone + Borrow<Pool2>
    {
    type Output = Polygon2<Pool2>;

    fn add(self, other: Vector2) -> Self::Output {
        let mut pool: Pool2 = self.pool.borrow().clone();
        for p in pool.points.iter_mut() {
            *p += other;
        }
        Polygon2 {
            index: self.index,
            pool
        }
    }
}

fn direction<R1, R2>(p: &Polygon2<R1>, other: &Polygon2<R2>) -> Option<Ordering>
    where R1: Clone + Borrow<Pool2>,
          R2: Clone + Borrow<Pool2> {
    let points = other.ring();
    let it = points.iter().map(|&point| p.cmp_point(point));
    let mut it = it.skip_while(|&ord| ord == Ordering::Equal);
    let ne = it.next();
    match ne {
        Some(dir) => {
            if it.all(|ord| ord == dir || ord == Ordering::Equal) {
                Some(dir)
            } else {
                None
            }
        }
        None => Some(Ordering::Equal)
    }
}

/// Partial ordering on polygons:
/// - if `other` is within `self`, `other < self`
/// - if all points inside `other` are also in `self`, and vice versa,
///   `other == self`
/// - if `self` is contained within `other`, `other > self`
///
/// If none of the above conditions are true (polygons are disjoint or
/// intersect each other), return `None`.
///
/// Examples:
///
/// ```
/// # use std::cmp::Ordering;
/// # use fajita::plane::{p2, v2};
/// # use fajita::plane::shapes::rectangle;
/// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
/// let inner = rectangle(p2(0.25, 0.25), v2(0.5, 0.5));
/// let outer = rectangle(p2(-1.0, -1.0), v2(3.0, 3.0));
/// assert_eq!(r.partial_cmp(&inner), Some(Ordering::Greater));
/// assert_eq!(r.partial_cmp(&outer), Some(Ordering::Less));
/// assert_eq!(r.partial_cmp(&r), Some(Ordering::Equal));
/// assert_eq!(r.partial_cmp(&(r.clone() + v2(2.0, 0.0))), None);
/// ```
impl<R1, R2> PartialOrd<Polygon2<R2>> for Polygon2<R1>
    where R1: Clone + Borrow<Pool2>,
          R2: Clone + Borrow<Pool2> {
    fn partial_cmp(&self, other: &Polygon2<R2>) -> Option<Ordering> {
        let self_to_other = direction(&self, other);
        let other_to_self = direction(other, &self);

        if self_to_other.is_none() || other_to_self.is_none() {
            None
        } else {
            if self_to_other == Some(Ordering::Equal) {
                other_to_self
            } else if other_to_self == Some(Ordering::Equal) {
                self_to_other.map(|o| o.reverse())
            } else if self_to_other != other_to_self {
                other_to_self
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;
    use crate::plane::{p2, v2};
    use super::*;

    type P2 = Polygon2<Arc<Pool2>>;

    fn square(pool: &mut Pool2) -> usize {
        pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0))
    }

    #[test]
    fn test_ring() {
        let mut pool = Pool2::new();
        let ri = pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let mut new_pool = pool.clone();
        let r = pool.get_polygon(ri);

        for l in new_pool.lines.iter_mut() {
            let mut ab = [l.a, l.b];
            ab.sort();
            let [a, b] = ab;
            *l = LineIs { a, b }
        }

        let ordered = new_pool.get_polygon(ri);
        assert_eq!(r.ring(), ordered.ring());
    }

    #[test]
    fn test_point_compare() {
        let mut pool = Pool2::new();
        let r = pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let r = pool.get_polygon(r);
        assert_eq!(r.cmp_point(p2(0.5, 0.5)), Ordering::Less);
        assert_eq!(r.cmp_point(p2(0.5, 0.0)), Ordering::Equal);
        assert_eq!(r.cmp_point(p2(0.5, 2.0)), Ordering::Greater);
    }

    #[test]
    fn test_poly_compare() {
        let mut pool = Pool2::new();
        let r = pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let inner = pool.rectangle(p2(0.25, 0.25), v2(0.5, 0.5));
        let outer = pool.rectangle(p2(-1.0, -1.0), v2(3.0, 3.0));

        let r = pool.get_polygon(r);
        let inner = pool.get_polygon(inner);
        let outer = pool.get_polygon(outer);
        assert_eq!(r.partial_cmp(&inner), Some(Ordering::Greater));
        assert_eq!(r.partial_cmp(&outer), Some(Ordering::Less));
        assert_eq!(r.partial_cmp(&r), Some(Ordering::Equal));
        assert_eq!(r.partial_cmp(&(r.clone() + v2(2.0, 0.0))), None);
    }
}