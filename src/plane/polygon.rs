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
    pub normal: Vector2,
    pub internal: bool,
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
    pub fn lines(&self) -> impl Iterator<Item=(LineIndex, Line2)> + '_ {
        self.lines.iter().map(move |li|
            (li.clone(), Line2::from_points(self.points[li.a], self.points[li.b]))
        )
    }

    fn fragment_lines(self, lines: Vec<(LineIndex, Line2)>) -> Vec<Polygon2> {
        let fragments = vec![self];

        lines.iter().fold(fragments, |acc, (li, l)| {
            acc.into_iter().flat_map(|frag| {
                let new_fragments = frag.divide(l.clone(), li.normal);
                new_fragments.map(|fs| {
                    let [a, b] = fs;
                    Left(iter::once(a).chain(iter::once(b)))
                }).unwrap_or(Right(iter::once(frag)))
            }).collect()
        })
    }

    pub fn fragment(self, other: Polygon2) -> Vec<Polygon2> {
        let self_lines: Vec<_> = self.lines().collect();
        let other_lines: Vec<_> = other.lines().collect();

        self.fragment_lines(other_lines).into_iter()
            .chain(other.fragment_lines(self_lines).into_iter())
            .collect()
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
                        iter::once(LineIndex { a: indices.a, b: new_ix, normal, internal: false })
                            .chain(iter::once(LineIndex { a: new_ix, b: indices.b, normal, internal: false }))
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
            inside.push(LineIndex { a, b, normal, internal: true });
            outside.push(LineIndex { a: b, b: a, normal: -normal, internal: true });

            Some(
                [
                    Polygon2 { points: combined.clone(), lines: inside },
                    Polygon2 { points: combined, lines: outside }
                ]
            )
        }
    }

    pub fn ring(&self) -> Vec<Point2> {
        let mut ends = HashMap::new();
        for l in self.lines.iter() {
            ends.entry(l.a).or_insert(vec![]).push(l);
            ends.entry(l.b).or_insert(vec![]).push(l);
        }
        let mut prior: usize = self.lines[0].a;
        let mut current: usize = self.lines[0].b;
        self.lines.iter().map(|_| {
            let old_prior = current;
            current = ends[&current].iter()
                .filter(|l| l.a != prior && l.b != prior)
                .flat_map(|l| iter::once(l.a).chain(iter::once(l.b)))
                .filter(|p| *p != current)
                .next().unwrap();
            prior = old_prior;
            self.points[old_prior]
        }).collect()
    }

    /// Combines the points in `self` and `other`, and returns two new polygons with
    /// the same backing point array:
    ///
    /// ```
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::shapes::rectangle;
    /// let r1 = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// let r2 = rectangle(p2(1.0, 0.0), v2(1.0, 1.0));
    /// let (a, b) = r1.clone().unify(r2.clone());
    /// assert_eq!(a.ring(), r1.ring());
    /// assert_eq!(b.ring(), r2.ring());
    /// assert_eq!(a.points.len(), 6);
    /// assert_eq!(b.points.len(), 6);
    /// ```
    pub fn unify(mut self, other: Polygon2) -> (Polygon2, Polygon2) {
        let self_points: HashMap<_, _> = self.points.iter().enumerate()
            .map(|(ix, p)| (exact_hash(p), ix)).collect();

        let mapped: HashMap<_, _> = other.points.into_iter().enumerate().map(|(ix, op)| {
            let h = exact_hash(&op);
            match self_points.get(&h) {
                Some(self_ix) => (ix, *self_ix),
                None => {
                    let self_ix = self.points.len();
                    self.points.push(op);
                    (ix, self_ix)
                }
            }
        }).collect();

        let lines = other.lines.into_iter().map(|l| {
            LineIndex {
                a: mapped[&l.a],
                b: mapped[&l.b],
                internal: l.internal,
                normal: l.normal,
            }
        }).collect();

        let points = self.points.clone();

        (
            self,
            Polygon2 { points, lines }
        )
    }
}

// Note that this has all the obvious issues with floating point comparisons
fn exact_hash(p: &Point2) -> (u64, u64) {
    (p.x.to_bits(), p.y.to_bits())
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
    use crate::plane::shapes::rectangle;
    use super::*;

    fn square() -> Polygon2 {
        rectangle(p2(0.0, 0.0), v2(1.0, 1.0))
    }

    fn assert_division_ok(divide: &Polygon2, parts: &[Polygon2;2]) {
        for part in parts.iter() {
            for p in part.ring() {
                assert!(divide.cmp_point(p) == Ordering::Equal, "!({:?} == {:?})", p, divide.ring())
            }
            assert!(part < divide, "!({:?} < {:?})", part.ring(), divide.ring());
        }
    }

    #[test]
    fn test_ring() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let ordered = Polygon2 {
            points: r.points.clone(),
            lines: r.lines.iter().map(|l| {
                let mut ab = [l.a, l.b];
                ab.sort();
                let [a, b] = ab;
                LineIndex { a, b, normal: l.normal, internal: l.internal }
            }).collect()
        };

        assert_eq!(r.ring(), ordered.ring());
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

    #[test]
    fn test_equal_greater_partial_cmp() {
        let a = rectangle(p2(0.0, 0.0), v2(2.0, 1.0));
        let b = rectangle(p2(1.0, 0.0), v2(1.0, 1.0));
        assert!(a > b);
        assert!(b < a);
    }

    #[test]
    fn test_fragment_division() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let parts = a.divide(Line2::new(p2(0.5, 0.5), v2(1.0, 0.0)), v2(0.0, -1.0));
        let parts = parts.unwrap();
        assert_division_ok(&a, &parts);
        for p in parts.iter() {
            assert_eq!(p.ring().len(), 4);
        }
    }

    #[test]
    fn test_simple_fragment() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = rectangle(p2(0.5, 0.5), v2(1.0, 1.0));
        let fragments = a.clone().fragment(b.clone());

        assert_eq!(fragments.len(), 8);
        for fragment in fragments {
            assert!(fragment < a || fragment < b);
            for p in fragment.ring() {
                let on_a = a.cmp_point(p) == Ordering::Equal;
                let on_b = b.cmp_point(p) == Ordering::Equal;
                assert!(on_a || on_b);
            }
        }
    }
}