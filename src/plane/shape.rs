use crate::plane::{Point2, Polygon2};
use crate::plane::polygon::{HalfspaceIs, PolygonIs, LineIs};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::iter;
use std::ops::Range;
use either::{Left, Right};
use crate::plane::line::{Halfspace2, LineSegment2};
use crate::util::container::Container;

#[derive(Clone)]
pub struct Shape2 {
    pub points: im::Vector<Point2>,
    pub lines: im::Vector<LineIs>,
    pub polygons: im::Vector<PolygonIs>,
}

pub fn insert<T: Clone>(v: &mut im::Vector<T>, e: T) -> usize {
    let ix = v.len();
    v.push_back(e);
    ix
}

impl Shape2 {
    pub fn new() -> Self {
        Shape2 {
            points: im::Vector::new(),
            lines: im::Vector::new(),
            polygons: im::Vector::new()
        }
    }


    pub fn get_polygon(&self, index: usize) -> Polygon2<&Shape2> {
        Polygon2 {
            pool: &self,
            index
        }
    }

    pub fn polygons(&self) -> impl Iterator<Item=Polygon2<&Shape2>> {
        (0..self.polygons.len()).into_iter().map(move |ix| {
            self.get_polygon(ix)
        })
    }

    /// Add all parts (points, lines, and polygons) from `other` into `self`.
    ///
    /// ```
    /// # use fajita::plane::shape::Shape2;
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::shapes::rectangle;
    /// let mut r1 = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// let r2 = rectangle(p2(1.0, 0.0), v2(1.0, 1.0));
    /// r1.extend(&r2);
    /// assert_eq!(r1.polygons.len(), 2);
    /// assert_eq!(r1.points.len(), 6);
    /// ```
    pub fn extend(&mut self, other: &Self) {
        let self_points: HashMap<_, _> = self.points.iter().enumerate()
            .map(|(ix, p)| (exact_hash(p), ix)).collect();

        let mapped: HashMap<_, _> = other.points.iter().enumerate().map(|(ix, op)| {
            let h = exact_hash(&op);
            match self_points.get(&h) {
                Some(self_ix) => (ix, *self_ix),
                None => {
                    (ix, insert(&mut self.points, op.clone()))
                }
            }
        }).collect();

        self.lines.extend(other.lines.iter().map(|l| {
            LineIs {
                a: mapped[&l.a],
                b: mapped[&l.b],
            }
        }));

        self.polygons.extend(
            other.polygons.iter().map(|p| {
                let halfspaces = p.halfspaces.iter().map(|hs| {
                    HalfspaceIs {
                        normal: hs.normal,
                        line_index: hs.line_index + other.lines.len()
                    }
                }).collect();

                PolygonIs {
                    halfspaces
                }
            })
        );
    }

    pub fn divide(&mut self, ix: usize, divide: &Halfspace2) -> Option<usize> {
        let mut new_points = vec![];
        let mut spaces: Vec<_> = {
            let update = self.polygons[ix].halfspaces.clone();
            update.iter().flat_map(|hs| {
                let li = self.lines[hs.line_index];
                let line = LineSegment2::new(self.points[li.a], self.points[li.b]);
                let intersect = line.intersect(&divide.line);
                let on_line = intersect.filter(|&(u_poly_line, _, _)| {
                    u_poly_line > 0.0 && u_poly_line < 1.0
                });
                match on_line {
                    Some((_, _, pi)) => {
                        let i_ix = insert(&mut self.points, pi);
                        let al = insert(&mut self.lines, LineIs { a: li.a, b: i_ix });
                        let bl = insert(&mut self.lines, LineIs { a: i_ix, b: li.b });
                        new_points.push(i_ix);
                        Right(
                            iter::once(
                                HalfspaceIs { line_index: al, normal: hs.normal },
                            ).chain(
                                iter::once(
                                    HalfspaceIs { line_index: bl, normal: hs.normal },
                                )
                            )
                        )
                    },
                    None => Left(iter::once(hs.clone()))
                }
            }).collect()
        };

        if new_points.len() < 2 {
            None
        } else {
            let mut polygon = PolygonIs { halfspaces: vec![] };
            std::mem::swap(&mut self.polygons[ix], &mut polygon);

            let (mut inside, mut outside): (Vec<_>, Vec<_>) = spaces.drain(..).into_iter().partition(|hs| {
                let l = self.lines[hs.line_index];
                let a = self.points[l.a];
                let b = self.points[l.b];
                let o = divide.contains(&a) == Ordering::Greater;
                let o = o || divide.contains(&b) == Ordering::Greater;
                o
            });

            let a = new_points[0];
            let b = new_points[1];
            let line_index = insert(&mut self.lines, LineIs { a, b });
            let normal = divide.normal;
            inside.push(HalfspaceIs { line_index, normal });
            outside.push(HalfspaceIs { line_index, normal: -normal });

            polygon.halfspaces = inside;
            std::mem::swap(&mut self.polygons[ix], &mut polygon);
            let new_ix = insert(&mut self.polygons, PolygonIs { halfspaces: outside });
            Some(new_ix)
        }
    }

    fn fragment_from_range(&mut self, ixs: Range<usize>) {
        let ix = 0;
        while ix < self.polygons.len() {
            if !ixs.contains(&ix) {
                let r = ixs.clone();
                for other_ix in r {
                    self.fragment_polygon(ix, other_ix);
                }
            }
        }
    }

    fn fragment_polygon(&mut self, a: usize, b: usize) -> Vec<usize> {
        let spaces: Vec<_> = self.get_polygon(b).halfspaces().collect();
        let fragments = vec![a];

        spaces.iter().fold(fragments, |acc, hs| {
            acc.into_iter().flat_map(|frag| {
                let generated = self.divide(frag, hs);
                iter::once(frag).chain(generated.into_iter())
            }).collect()
        })
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
    /// # use fajita::plane::shapes::rectangle;
    /// # use fajita::util::container::Container;
    /// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// assert_eq!(r.contains(&p2(0.5, 0.5)), Ordering::Greater);
    /// assert_eq!(r.contains(&p2(0.5, 0.0)), Ordering::Equal);
    /// assert_eq!(r.contains(&p2(0.5, 2.0)), Ordering::Less);
    /// ```
    fn contains(&self, p: &Point2) -> Ordering {
        let mut prior_equal = false;
        for polygon in self.polygons() {
            match polygon.contains(p) {
                Ordering::Greater => return Ordering::Greater,
                Ordering::Equal => {
                    if prior_equal {
                        return Ordering::Greater
                    }
                    prior_equal = true;
                },
                _ => ()
            }
        }

        if prior_equal { Ordering::Equal } else { Ordering::Less }
    }
}

// Note that this has all the obvious issues with floating point comparisons
fn exact_hash(p: &Point2) -> (u64, u64) {
    (p.x.to_bits(), p.y.to_bits())
}

#[cfg(test)]
mod test {
    use std::cmp::Ordering;
    use crate::plane::{p2, v2};
    use crate::plane::shapes::{rectangle, add_rectangle};
    use super::*;

    fn assert_division_ok(pool: &mut Shape2, ix: usize, hs: Halfspace2) -> Option<usize> {
        let original = pool.get_polygon(ix).unlink();
        let other = pool.divide(ix, &hs);
        for part_ix in vec![ix].into_iter().chain(other.into_iter()).into_iter() {
            let polygon = pool.get_polygon(part_ix);
            assert!(
                original.contains(&polygon.center()) == Ordering::Greater,
                "center of {:?} not in original polygon", polygon.ring()
            );
            assert!(
                polygon.contains(&polygon.center()) == Ordering::Greater,
                "center not in {:?}", polygon.ring()
            );
            for p in polygon.ring() {
                assert!(original.contains(&p) == Ordering::Equal, "!({:?} == {:?})", p, original.ring())
            }
            assert!(polygon <= original, "!({:?} < {:?})", polygon.ring(), original.ring());
        }
        other
    }

    fn assert_fragment_ok(pool: &mut Shape2, a: usize, b: usize) {
        let original = pool.get_polygon(a).unlink();
        let fragments = pool.fragment_polygon(a, b);

        for frag in fragments {
            assert!(
                pool.get_polygon(frag) <= original,
                "fragment not in original"
            )
        }
    }

    #[test]
    fn test_simple_division() {
        let mut r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 0.5), v2(1.0, 0.0))
        };
        let other = assert_division_ok(&mut r, 0, hs);
        let other = other.unwrap();

        let p1 = r.get_polygon(0);
        let p2 = r.get_polygon(other);
        assert_eq!(p1.ring().len(), 4);
        assert_eq!(p2.ring().len(), 4);
    }

    #[test]
    fn test_no_division() {
        let mut r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 1.5), v2(1.0, 0.0))
        };
        let other = assert_division_ok(&mut r, 0, hs);
        assert!(other.is_none());
    }

    #[test]
    fn test_tangent_no_division() {
        let mut r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 1.0), v2(1.0, 0.0))
        };
        let other = assert_division_ok(&mut r, 0, hs);
        assert!(other.is_none());
    }

    #[test]
    fn test_extended_division() {
        let mut a = rectangle(p2(0.0, 0.0), v2(2.0, 1.0));
        let b = rectangle(p2(1.0, 1.0), v2(1.0, 1.0));
        let abi = a.polygons.len();
        a.extend(&b);

        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(0.5, 1.5), v2(1.0, 0.0))
        };
        let other = assert_division_ok(&mut a, abi, hs);
        assert!(other.is_some());
    }

    #[test]
    fn test_equal_greater_partial_cmp() {
        let mut pool = Shape2::new();
        let a = add_rectangle(&mut pool, p2(0.0, 0.0), v2(2.0, 1.0));
        let b = add_rectangle(&mut pool, p2(1.0, 0.0), v2(1.0, 1.0));
        let a = pool.get_polygon(a);
        let b = pool.get_polygon(b);
        assert!(a > b);
        assert!(b < a);
    }

    #[test]
    fn test_simple_fragment() {
        let mut pool = Shape2::new();
        let a = add_rectangle(&mut pool, p2(0.0, 0.0), v2(1.0, 1.0));
        let b = add_rectangle(&mut pool, p2(0.5, 0.5), v2(1.0, 1.0));

        assert_fragment_ok(&mut pool, a, b);
    }
}