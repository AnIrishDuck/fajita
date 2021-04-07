use std::borrow::Borrow;
use std::collections::HashMap;
use std::iter;
use std::ops;
use cgmath::EuclideanSpace;

use crate::plane::{LineSegment2, Point2, Vector2};
use crate::plane::line::{Halfspace2, Segment, Intersect, Hole};
use crate::plane::shape::Shape2;
use crate::util::container::{Container, Orientation, PartialContainer};
use crate::util::knife::{Knife, Parts};

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
where R: Clone + Borrow<Shape2>
{
    pub pool: R,
    pub index: usize
}

#[derive(Clone)]
pub struct PolygonPoint2<R>
where R: Clone + Borrow<Shape2>
{
    pool: R,
    ix: usize,
}

impl<R> From<&PolygonPoint2<R>> for Point2
where R: Clone + Borrow<Shape2>
{
    fn from(p: &PolygonPoint2<R>) -> Point2 {
        p.pool.borrow().points[p.ix]
    }
}

type CutPoint2<R> = Diff<PolygonPoint2<R>, Point2>;

impl<R> Container<CutPoint2<R>> for Halfspace2
where R: Clone + Borrow<Shape2>
{
    fn contains(&self, p: &CutPoint2<R>) -> Orientation {
        self.contains(&resolve(p))
    }
}

#[derive(Clone)]
pub struct CutEdge2<R>
where R: Clone + Borrow<Shape2>
{
    a: CutPoint2<R>,
    b: CutPoint2<R>
}

impl<R> From<&CutEdge2<R>> for LineSegment2
where R: Clone + Borrow<Shape2>
{
    fn from(e: &CutEdge2<R>) -> LineSegment2 {
        let a = resolve(&e.a);
        let b = resolve(&e.b);

        LineSegment2 { a, b }
    }
}

#[derive(Clone)]
pub enum Diff<P, N>
{
    Prior(P),
    New(N)
}

pub trait Value<T> {
    fn value(&self) -> T;
}

fn resolve<'a, P: 'a, N: From<&'a P> + Clone>(d: &'a Diff<P, N>) -> N {
    match d {
        Diff::Prior(p) => N::from(&p),
        Diff::New(n) => n.clone()
    }
}

impl<R> Segment<CutPoint2<R>> for CutEdge2<R>
where R: Clone + Borrow<Shape2>
{
    fn from_endpoints(a: CutPoint2<R>, b: CutPoint2<R>) -> Self {
        CutEdge2 { a, b }
    }

    fn start(&self) -> CutPoint2<R> { self.a.clone() }
    fn end(&self) -> CutPoint2<R> { self.b.clone() }
}

impl<R> Intersect<Halfspace2, Option<CutPoint2<R>>> for CutEdge2<R>
where R: Clone + Borrow<Shape2>
{
    fn intersect(&self, knife: Halfspace2) -> Option<CutPoint2<R>> {
        let intersect = knife.line.intersect(&self.into());
        intersect.filter(|&(u_poly_line, _, _)| {
            u_poly_line >= 0.0 && u_poly_line <= 1.0
        }).map(|(u_poly_line, _, p)| {
            if u_poly_line == 0.0 {
                self.a.clone()
            } else if u_poly_line == 1.0 {
                self.b.clone()
            } else {
                Diff::New(p)
            }
        })
    }
}

pub struct CutPolygon2<R>
where R: Clone + Borrow<Shape2>
{
    edges: Vec<CutEdge2<R>>
}

impl<R> Knife<CutPolygon2<R>, Option<CutPolygon2<R>>, ()> for Halfspace2
where R: Clone + Borrow<Shape2>
{
    fn cut(&self, target: CutPolygon2<R>) -> Parts<Option<CutPolygon2<R>>, ()> {
        let mut inside = CutPolygon2 { edges: vec![] };
        let mut outside = CutPolygon2 { edges: vec![] };

        let mut points = vec![];
        let mut segments = vec![];
        for edge in target.edges.into_iter() {
            let parts = self.cut(edge);
            inside.edges.extend(parts.inside);
            outside.edges.extend(parts.outside);
            for hole in parts.tangent.into_iter() {
                match hole {
                    Hole::Point(p) => points.push(p),
                    Hole::Segment(s) => segments.push(s)
                }
            }
        }

        let mut result = Parts {
           inside: if inside.edges.len() > 0 { Some(inside) } else { None },
           outside: if outside.edges.len() > 0 { Some(outside) } else { None },
           tangent: ()
        };

        if segments.len() > 0 {
            match result.inside.as_mut() {
                Some(p) => p.edges.extend(segments),
                None => {
                    result.outside.as_mut().map(|p| p.edges.extend(segments));
                }
            }
        } else if points.len() >= 2 {
            if points.len() > 2 {
                panic!("cut polygons cannot produce more than two points");
            };

            let mut i = points.into_iter();
            let a = i.next().unwrap();
            let b = i.next().unwrap();
            let edge = CutEdge2 { a, b };

            result.inside.as_mut().map(|p| p.edges.push(edge.clone()));
            result.outside.as_mut().map(|p| p.edges.push(edge.clone()));
        }

        result
    }
}

impl<R> Polygon2<R>
    where R: Clone + Borrow<Shape2>
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
                .next().expect("matching endpoint");
            prior = old_prior;
            pool.points[old_prior]
        }).collect()
    }

    pub fn center(&self) -> Point2 {
        let ring = self.ring();
        let sum: Vector2 = ring.iter().map(|p| p.to_vec()).sum();
        Point2::from_vec(sum / ring.len() as f64)
    }

    pub fn unlink(&self) -> Polygon2<Shape2> {
        let pool = self.pool.borrow().clone();
        Polygon2 {
            pool, index: self.index
        }
    }
}

impl<R> Container<Point2> for Polygon2<R>
    where R: Clone + Borrow<Shape2>
    {
    /// Checks the given point against this polygon.
    ///
    /// Examples:
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::shapes::rectangle;
    /// # use fajita::util::container::{Container, Orientation};
    /// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// let r = r.get_polygon(0);
    /// assert_eq!(r.contains(&p2(0.5, 0.5)), Orientation::In);
    /// assert_eq!(r.contains(&p2(0.5, 0.0)), Orientation::On);
    /// assert_eq!(r.contains(&p2(0.5, 2.0)), Orientation::Out);
    /// ```
    fn contains(&self, point: &Point2) -> Orientation {
        let it = self.halfspaces().filter_map(|space| {
            let ord = space.contains(point);
            if ord == Orientation::In {
                None
            } else {
                Some(ord)
            }
        });


        let positive = it.map(|v| {
            if v == Orientation::Out { 1 } else { 0 }
        }).max();

        match positive {
            Some(v) => {
                if v > 0 { Orientation::Out } else { Orientation::On }
            }
            None => Orientation::In
        }
    }
}

impl <R> ops::Add<Vector2> for Polygon2<R>
    where R: Clone + Borrow<Shape2>
    {
    type Output = Polygon2<Shape2>;

    fn add(self, other: Vector2) -> Self::Output {
        let mut pool: Shape2 = self.pool.borrow().clone();
        for p in pool.points.iter_mut() {
            *p += other;
        }
        Polygon2 {
            index: self.index,
            pool
        }
    }
}

fn direction<R1, R2>(p: &Polygon2<R1>, other: &Polygon2<R2>) -> Option<Orientation>
    where R1: Clone + Borrow<Shape2>,
          R2: Clone + Borrow<Shape2> {
    let points = other.ring();
    let it = points.iter().map(|&point| p.contains(&point));
    let mut it = it.skip_while(|ord| *ord == Orientation::On);

    let ne = it.next();
    match ne {
        Some(dir) => {
            if it.all(|ord| ord == dir || ord == Orientation::On) {
                Some(dir)
            } else {
                None
            }
        }
        None => Some(Orientation::On)
    }
}

/// Polygons partially contain other polygons.
///
/// If they are not equal, or one does not fully contain the other, (polygons are
/// disjoint or intersect each other), return `None`.
///
/// Examples:
///
/// ```
/// # use fajita::plane::{p2, v2};
/// # use fajita::plane::shapes::rectangle;
/// # use fajita::util::container::{PartialContainer, Orientation};
/// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
/// let inner = rectangle(p2(0.25, 0.25), v2(0.5, 0.5));
/// let outer = rectangle(p2(-1.0, -1.0), v2(3.0, 3.0));
/// let r = r.get_polygon(0);
/// let inner = inner.get_polygon(0);
/// let outer = outer.get_polygon(0);
/// assert_eq!(r.partial_contains(&inner), Some(Orientation::In));
/// assert_eq!(r.partial_contains(&outer), Some(Orientation::Out));
/// assert_eq!(r.partial_contains(&r), Some(Orientation::On));
/// assert_eq!(r.partial_contains(&(r.clone() + v2(2.0, 0.0))), None);
/// ```
impl<R1, R2> PartialContainer<Polygon2<R2>> for Polygon2<R1>
    where R1: Clone + Borrow<Shape2>,
          R2: Clone + Borrow<Shape2> {
    fn partial_contains(&self, other: &Polygon2<R2>) -> Option<Orientation> {
        let other_to_self = direction(&self, other);
        let self_to_other = direction(other, &self);

        if self_to_other.is_none() || other_to_self.is_none() {
            None
        } else {
            if self_to_other == Some(Orientation::On) {
                other_to_self
            } else if other_to_self == Some(Orientation::On) {
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
    use crate::plane::{p2, v2};
    use crate::plane::shapes::rectangle;
    use super::*;

    #[test]
    fn test_ring() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let mut r2 = r.clone();
        let r = r.get_polygon(0);

        for l in r2.lines.iter_mut() {
            let mut ab = [l.a, l.b];
            ab.sort();
            let [a, b] = ab;
            *l = LineIs { a, b }
        }

        let ordered = r2.get_polygon(0);
        assert_eq!(r.ring(), ordered.ring());
    }

    #[test]
    fn test_point_compare() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let r = r.get_polygon(0);
        assert_eq!(r.contains(&p2(0.5, 0.5)), Orientation::In);
        assert_eq!(r.contains(&p2(0.5, 0.0)), Orientation::On);
        assert_eq!(r.contains(&p2(0.5, 2.0)), Orientation::Out);
    }

    #[test]
    fn test_poly_compare() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let inner = rectangle(p2(0.25, 0.25), v2(0.5, 0.5));
        let outer = rectangle(p2(-1.0, -1.0), v2(3.0, 3.0));

        let r = r.get_polygon(0);
        let inner = inner.get_polygon(0);
        let outer = outer.get_polygon(0);
        assert_eq!(r.partial_contains(&inner), Some(Orientation::In));
        assert_eq!(r.partial_contains(&outer), Some(Orientation::Out));
        assert_eq!(r.partial_contains(&r), Some(Orientation::On));
        assert_eq!(r.partial_contains(&(r.clone() + v2(2.0, 0.0))), None);
    }
}