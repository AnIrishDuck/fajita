use either::{Left, Right};
use std::collections::HashMap;
use std::cmp::Ordering;
use std::iter;
use std::ops;
use cgmath::InnerSpace;

use crate::plane::{Line2, Point2, Vector2};

#[derive(Clone, Debug)]
pub struct LineIndex {
    pub a: usize,
    pub b: usize,
    pub normal: Vector2
}

struct IndexedSegment<'a> {
    ix: LineIndex,
    backing: &'a Vec<Point2>
}

#[derive(Clone, Debug)]
pub struct Polygon2 {
    pub points: Vec<Point2>,
    pub lines: Vec<LineIndex>
}

impl Polygon2 {
    fn lines(&self) -> impl Iterator<Item=(LineIndex, Line2)> + '_ {
        self.lines.iter().map(move |li|
            (li.clone(), Line2::from_points(self.points[li.a], self.points[li.b]))
        )
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
        let mut it = self.lines.iter().filter_map(|li| {
            let dot = (point - self.points[li.a]).dot(li.normal);
            if dot >= 0.0 { Some(dot) } else { None }
        });


        let positive = it.map(|v| if v > 0.0 { 1 } else { 0 }).max();

        match positive {
            Some(v) => {
                if v > 0 { Ordering::Greater } else { Ordering::Equal }
            }
            None => Ordering::Less
        }
    }

    fn divide(&self, division: Line2, normal: Vector2) -> Option<[Polygon2;2]> {
        let mut intersections = vec![];
        let updated_lines: Vec<_> = self.lines().flat_map(|(indices, poly_line)| {
            let intersect = poly_line.intersect(&division);
            let on_line = intersect.filter(|&(u_poly_line, _, _)| u_poly_line >= 0.0 && u_poly_line <= 1.0);
            match on_line {
                Some((_, _, pi)) => {
                    let new_ix = self.lines.len() + intersections.len();
                    intersections.push(pi);
                    let normal = indices.normal;
                    Left(
                        iter::once(LineIndex { a: indices.a, b: new_ix, normal })
                            .chain(iter::once(LineIndex { a: new_ix, b: indices.b, normal }))
                    )
                },
                None => Right(iter::once(indices))
            }
        }).collect();

        if intersections.len() < 2 {
            None
        } else {
            let combined: Vec<_> = self.points.iter().chain(intersections.iter()).map(|p| p.clone()).collect();

            let (mut inside, mut outside): (Vec<_>, Vec<_>) = updated_lines.into_iter().partition(|li| {
                let a = combined[li.a];
                let b = combined[li.b];
                (division.p - a).dot(normal) > 0.0 || (division.p - b).dot(normal) > 0.0
            });

            let a = self.points.len();
            let b = a + 1;
            inside.push(LineIndex { a, b, normal });
            outside.push(LineIndex { a: b, b: a, normal: -normal });

            Some(
                [
                    Polygon2 { points: combined.clone(), lines: inside },
                    Polygon2 { points: combined, lines: outside }
                ]
            )
        }
    }

    fn ring(&self) -> Vec<Point2> {
        let a_ends: HashMap<_, _> = self.lines.iter().map(|l| (l.a, l)).collect();
        let b_ends: HashMap<_, _> = self.lines.iter().map(|l| (l.b, l)).collect();
        let mut current: Option<usize> = Some(self.lines[0].a);
        self.lines.iter().flat_map(|_| {
            match current {
                Some(prior) => {
                    let ab = a_ends.get(&prior).map(|x| x.b);
                    let ba = b_ends.get(&prior).map(|x| x.a);
                    current = ab.or(ba);
                    Some(self.points[prior])
                },
                None => None
            }
        }).collect()
    }
}

impl PartialEq for Polygon2 {
    fn eq(&self, other: &Polygon2) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)

    }
}

impl ops::Add<Vector2> for Polygon2 {
    type Output = Polygon2;

    fn add(mut self, other: Vector2) -> Self {
        self.points.iter_mut().map(|p| *p += other).last();
        self
    }
}

fn direction(p: &Polygon2, other: &Polygon2) -> Option<Ordering> {
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
impl PartialOrd for Polygon2 {
    fn partial_cmp(&self, other: &Polygon2) -> Option<Ordering> {
        let self_to_other = direction(&self, other);
        let other_to_self = direction(other, &self);

        if self_to_other.is_none() || other_to_self.is_none() {
            None
        } else {
            let equal = self_to_other == Some(Ordering::Equal);
            if self_to_other != other_to_self || equal {
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
    use crate::plane::shapes::rectangle;
    use super::*;

    fn square() -> Polygon2 {
        rectangle(p2(0.0, 0.0), v2(1.0, 1.0))
    }

    #[test]
    fn test_poly_compare() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let inner = rectangle(p2(0.25, 0.25), v2(0.5, 0.5));
        let outer = rectangle(p2(-1.0, -1.0), v2(3.0, 3.0));
        assert_eq!(r.partial_cmp(&inner), Some(Ordering::Greater));
        assert_eq!(r.partial_cmp(&outer), Some(Ordering::Less));
        assert_eq!(r.partial_cmp(&r), Some(Ordering::Equal));
        assert_eq!(r.partial_cmp(&(r.clone() + v2(2.0, 0.0))), None);
    }

    #[test]
    fn test_simple_division() {
        let p = square();
        let parts = p.divide(Line2::new(p2(-1.0, 0.5), v2(1.0, 0.0)), v2(0.0, 1.0));
        let parts = parts.unwrap();
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0].ring().len(), 4);
        assert_eq!(parts[1].ring().len(), 4);
    }

    #[test]
    fn test_no_division() {
        let p = square();
        let parts = p.divide(Line2::new(p2(-1.0, 1.5), v2(1.0, 0.0)), v2(0.0, 1.0));
        assert_eq!(parts.is_none(), true);
    }
}