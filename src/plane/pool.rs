use crate::plane::{p2, v2, Point2, Vector2, Polygon2};
use crate::plane::polygon::{HalfspaceIs, PolygonIs, LineIs};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::iter;
use std::ops::Range;
use either::{Left, Right};
use crate::plane::line::{Halfspace2, LineSegment2};

#[derive(Clone)]
pub struct Pool2 {
    pub points: Vec<Point2>,
    pub lines: Vec<LineIs>,
    pub polygons: Vec<PolygonIs>,
}

pub fn insert<T>(v: &mut Vec<T>, e: T) -> usize {
    let ix = v.len();
    v.push(e);
    ix
}

impl Pool2 {
    pub fn new() -> Self {
        Pool2 {
            points: vec![],
            lines: vec![],
            polygons: vec![]
        }
    }

    pub fn rectangle(&mut self, origin: Point2, extent: Vector2) -> usize {
        assert!(extent.x > 0.0 && extent.y > 0.0);

        let ex = v2(extent.x, 0.0);
        let ey = v2(0.0, extent.y);

        let oo = insert(&mut self.points, origin);
        let eo = insert(&mut self.points, origin + ex);
        let ee = insert(&mut self.points, origin + extent);
        let oe = insert(&mut self.points, origin + ey);

        let lines = vec![
            insert(&mut self.lines, LineIs { a: oo, b: eo }),
            insert(&mut self.lines, LineIs { a: eo, b: ee }),
            insert(&mut self.lines, LineIs { a: ee, b: oe }),
            insert(&mut self.lines, LineIs { a: oe, b: oo }),
        ];

        let normals = vec![
            v2( 0.0, -1.0),
            v2( 1.0,  0.0),
            v2( 0.0,  1.0),
            v2(-1.0,  0.0),
        ];

        let halfspaces = lines.iter().zip(normals).map(|(&line_index, normal)|
            HalfspaceIs { line_index, normal }
        ).collect();

        insert(&mut self.polygons, PolygonIs { halfspaces })
    }


    pub fn get_polygon(&self, index: usize) -> Polygon2<&Pool2> {
        Polygon2 {
            pool: &self,
            index
        }
    }

    /// Add all parts (points, lines, and polygons) from `other` into `self`.
    ///
    /// ```
    /// # use fajita::plane::pool::Pool2;
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::shapes::rectangle;
    /// let mut pool = Pool2::new();
    /// let r1 = pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// let r2 = rectangle(p2(1.0, 0.0), v2(1.0, 1.0));
    /// pool.extend(&r2.pool);
    /// assert_eq!(pool.polygons.len(), 2);
    /// assert_eq!(pool.points.len(), 6);
    /// ```
    pub fn extend(&mut self, other: &Pool2) {
        let self_points: HashMap<_, _> = self.points.iter().enumerate()
            .map(|(ix, p)| (exact_hash(p), ix)).collect();

        let mapped: HashMap<_, _> = other.points.iter().enumerate().map(|(ix, op)| {
            let h = exact_hash(&op);
            match self_points.get(&h) {
                Some(self_ix) => (ix, *self_ix),
                None => {
                    let self_ix = self.points.len();
                    self.points.push(op.clone());
                    (ix, self_ix)
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
        )
    }

    pub fn divide(&mut self, original_ix: usize, divide: &Halfspace2) -> Option<usize> {
        let mut new_points = vec![];
        let mut spaces: Vec<_> = {
            let update = self.polygons[original_ix].halfspaces.clone();
            update.iter().flat_map(|hs| {
                let li = self.lines[hs.line_index];
                let line = LineSegment2::new(self.points[li.a], self.points[li.b]);
                let intersect = line.intersect(&divide.line);
                let on_line = intersect.filter(|&(u_poly_line, _, _)| u_poly_line >= 0.0 && u_poly_line <= 1.0);
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
            std::mem::swap(&mut self.polygons[original_ix], &mut polygon);

            let (mut inside, mut outside): (Vec<_>, Vec<_>) = spaces.drain(..).into_iter().partition(|hs| {
                let l = self.lines[hs.line_index];
                let a = self.points[l.a];
                let b = self.points[l.b];
                let o = divide.contains_point(a) == Ordering::Greater;
                let o = o || divide.contains_point(b) == Ordering::Greater;
                o
            });

            let a = new_points[0];
            let b = new_points[1];
            let line_index = insert(&mut self.lines, LineIs { a, b });
            let normal = divide.normal;
            inside.push(HalfspaceIs { line_index, normal });
            outside.push(HalfspaceIs { line_index, normal: -normal });

            polygon.halfspaces = inside;
            std::mem::swap(&mut self.polygons[original_ix], &mut polygon);
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


// Note that this has all the obvious issues with floating point comparisons
fn exact_hash(p: &Point2) -> (u64, u64) {
    (p.x.to_bits(), p.y.to_bits())
}

#[cfg(test)]
mod test {
    use std::cmp::Ordering;
    use crate::plane::{p2, v2};
    use super::*;

    fn assert_division_ok(pool: &mut Pool2, ix: usize, hs: Halfspace2) -> Option<usize> {
        let original = pool.get_polygon(ix).unlink();
        let other = pool.divide(ix, &hs);
        for part_ix in vec![ix].into_iter().chain(other.into_iter()).into_iter() {
            let polygon = pool.get_polygon(part_ix);
            assert!(
                original.cmp_point(polygon.center()) == Ordering::Greater,
                "center of {:?} not in original polygon", polygon.ring()
            );
            assert!(
                polygon.cmp_point(polygon.center()) == Ordering::Greater,
                "center not in {:?}", polygon.ring()
            );
            for p in polygon.ring() {
                assert!(original.cmp_point(p) == Ordering::Equal, "!({:?} == {:?})", p, original.ring())
            }
            assert!(polygon <= original, "!({:?} < {:?})", polygon.ring(), original.ring());
        }
        other
    }

    fn assert_fragment_ok(pool: &mut Pool2, a: usize, b: usize) {
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
        let mut pool = Pool2::new();
        let p = pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 0.5), v2(1.0, 0.0))
        };
        let other = assert_division_ok(&mut pool, p, hs);
        let other = other.unwrap();

        let p1 = pool.get_polygon(p);
        let p2 = pool.get_polygon(other);
        assert_eq!(p1.ring().len(), 4);
        assert_eq!(p2.ring().len(), 4);
    }

    #[test]
    fn test_no_division() {
        let mut pool = Pool2::new();
        let p = pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 1.5), v2(1.0, 0.0))
        };
        let other = assert_division_ok(&mut pool, p, hs);
        assert!(other.is_none());
    }

    #[test]
    fn test_extended_division() {
        let mut ap = Pool2::new();
        ap.rectangle(p2(0.0, 0.0), v2(2.0, 1.0));
        let mut bp = Pool2::new();
        let b = bp.rectangle(p2(1.0, 1.0), v2(1.0, 1.0));
        let abi = ap.polygons.len() + b;
        ap.extend(&bp);

        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(0.5, 1.5), v2(1.0, 0.0))
        };
        let other = assert_division_ok(&mut ap, abi, hs);
        assert!(other.is_some());
    }

    #[test]
    fn test_equal_greater_partial_cmp() {
        let mut pool = Pool2::new();
        let a = pool.rectangle(p2(0.0, 0.0), v2(2.0, 1.0));
        let b = pool.rectangle(p2(1.0, 0.0), v2(1.0, 1.0));
        let a = pool.get_polygon(a);
        let b = pool.get_polygon(b);
        assert!(a > b);
        assert!(b < a);
    }

    #[test]
    fn test_simple_fragment() {
        let mut pool = Pool2::new();
        let a = pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = pool.rectangle(p2(0.5, 0.5), v2(1.0, 1.0));

        assert_fragment_ok(&mut pool, a, b);
    }
}