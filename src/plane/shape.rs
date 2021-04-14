use crate::plane::{Point2, Polygon2};
use crate::plane::polygon::{HalfspaceIs, PolygonIs, LineIs, FlatPolygon2, Vertex2};
use std::collections::HashMap;
use std::iter;
use std::ops::Range;
use either::{Left, Right};
use crate::plane::line::{Halfspace2, LineSegment2};
use crate::util::container::{Container, Orientation, PartialContainer};
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
    /// # use fajita::plane::shapes::flat_rectangle;
    /// # use fajita::util::container::{Container, Orientation};
    /// let r = flat_rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
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
                let o = divide.contains(&a) == Orientation::In;
                let o = o || divide.contains(&b) == Orientation::In;
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
        let mut ix = ixs.end;
        let upper_bound = self.polygons.len() * (self.polygons.len() + 1);
        while ix < self.polygons.len() && ix < upper_bound {
            let r = ixs.clone();
            for other_ix in r {
                self.fragment_polygon(ix, other_ix);
            }
            ix += 1;
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

    pub fn union(mut self, other: &Shape2) -> Self {
        let start = {
            let start = self.polygons.len();
            self.extend(other);
            self.fragment_from_range(0..start);
            start
        };
        let (whole, mut fragments) = self.polygons.split_at(start);

        self.polygons = whole;
        fragments.retain(|f| {
            let frag = Shape2 {
                points: self.points.clone(),
                lines: self.lines.clone(),
                polygons: im::Vector::from(vec![f.clone()])
            };
            (0..start).into_iter().all(|ix|
                self.get_polygon(ix).partial_contains(&frag.get_polygon(0)) == None
            )
        });

        self.polygons.extend(fragments);
        self
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
    /// # use fajita::util::container::{Container, Orientation};
    /// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// assert_eq!(r.contains(&p2(0.5, 0.5)), Orientation::In);
    /// assert_eq!(r.contains(&p2(0.5, 0.0)), Orientation::On);
    /// assert_eq!(r.contains(&p2(0.5, 2.0)), Orientation::Out);
    /// ```
    fn contains(&self, p: &Point2) -> Orientation {
        let mut prior_equal = false;
        for polygon in self.polygons() {
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

// Note that this has all the obvious issues with floating point comparisons
fn exact_hash(p: &Point2) -> (u64, u64) {
    (p.x.to_bits(), p.y.to_bits())
}

#[cfg(test)]
mod test {
    use crate::plane::{p2, v2};
    use crate::plane::shapes::{rectangle, add_rectangle, flat_rectangle};
    use super::*;

    fn assert_division_ok(pool: &mut Shape2, ix: usize, hs: Halfspace2) -> Option<usize> {
        let original = pool.get_polygon(ix).unlink();
        let other = pool.divide(ix, &hs);
        for part_ix in vec![ix].into_iter().chain(other.into_iter()).into_iter() {
            let polygon = pool.get_polygon(part_ix);
            assert!(
                original.contains(&polygon.center()) == Orientation::In,
                "center of {:?} not in original polygon", polygon.ring()
            );
            assert!(
                polygon.contains(&polygon.center()) == Orientation::In,
                "center {:?} not in {:?}", polygon.center(), polygon.ring()
            );
            for p in polygon.ring() {
                assert!(original.contains(&p) == Orientation::On, "!({:?} == {:?})", p, original.ring())
            }
            assert!(
                original.partial_contains(&polygon) != Some(Orientation::Out),
                "!({:?} < {:?})", polygon.ring(), original.ring()
            );
        }
        other
    }

    fn assert_fragment_ok(pool: &mut Shape2, a: usize, b: usize) {
        let original = pool.get_polygon(a).unlink();
        let fragments = pool.fragment_polygon(a, b);

        for frag in fragments {
            assert!(
                original.partial_contains(&pool.get_polygon(frag)) != Some(Orientation::Out),
                "fragment not in original"
            )
        }
    }

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
        assert!(a.partial_contains(&b) == Some(Orientation::In));
        assert!(b.partial_contains(&a) == Some(Orientation::Out));
    }

    #[test]
    fn test_simple_fragment() {
        let mut pool = Shape2::new();
        let a = add_rectangle(&mut pool, p2(0.0, 0.0), v2(1.0, 1.0));
        let b = add_rectangle(&mut pool, p2(0.5, 0.5), v2(1.0, 1.0));

        assert_fragment_ok(&mut pool, a, b);
    }

    #[test]
    fn test_no_fragment() {
        let mut pool = Shape2::new();
        let a = add_rectangle(&mut pool, p2(0.0, 0.0), v2(1.0, 1.0));
        let b = add_rectangle(&mut pool, p2(1.0, 0.5), v2(0.5, 0.5));

        assert_fragment_ok(&mut pool, a, b);
    }

    #[test]
    fn test_simple_union() {
        let a = flat_rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = flat_rectangle(p2(0.5, 0.5), v2(1.0, 1.0));

        assert_union_ok(&a.into(), &b.into());
    }
}