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

#[derive(Clone, Debug)]
pub struct Vertex2
{
    pub index: Option<usize>,
    pub point: Point2
}

impl Container<Vertex2> for Halfspace2 {
    fn contains(&self, v: &Vertex2) -> Orientation {
        self.contains(&v.point)
    }
}

#[derive(Clone, Debug)]
pub struct Edge2
{
    a: Vertex2,
    b: Vertex2
}

impl Edge2
{
    pub fn line(&self) -> LineSegment2 {
        LineSegment2 { a: self.a.point, b: self.b.point }
    }

    pub fn vertices(&self) -> impl Iterator<Item=Vertex2> {
        iter::once(self.a.clone()).chain(iter::once(self.b.clone()))
    }
}

fn extend(vertices: &mut Vec<Vertex2>, v: Vertex2) -> bool {
    if vertices.last().iter().all(|ev| ev.point != v.point) {
        vertices.push(v);
        true
    } else {
        false
    }
}

/// Returns the Clockwise-wound perpendicular vector for a given vector
pub fn perpendicular(v: Vector2) -> Vector2 {
    Vector2 { x: v.y, y: -v.x }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Winding {
    Clockwise,
    CounterClockwise
}

impl Winding {
    pub fn from_points(a: Point2, b: Point2, c: Point2) -> Option<Self> {
        let normal = perpendicular(b - a);
        let hs = Halfspace2 { normal, line: LineSegment2 { a, b } };
        // perpendicular always returns a clockwise vector, and normals point out
        // therefore Out => Clockwise
        match hs.contains(&c) {
            Orientation::In => Some(Winding::CounterClockwise),
            Orientation::On => None,
            Orientation::Out => Some(Winding::Clockwise),
        }
    }

    pub fn find_from_points<'a, I>(points: I) -> Option<Self>
    where
    I: IntoIterator<Item = &'a Point2>
    {
        let mut it = points.into_iter();
        let a = it.next();
        let b = it.next();
        match (a, b) {
            (Some(a), Some(b)) => {
                it.find_map(|c| {
                    Winding::from_points(a.clone(), b.clone(), c.clone())
                })
            },
            _ => None
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PolygonError {
    Zero,
    InvalidWinding,
    NonConvex
}

#[derive(Clone, Debug)]
pub struct FlatPolygon2
{
    pub vertices: Vec<Vertex2>,
}

impl FlatPolygon2
{
    pub fn edges(&self) -> impl Iterator<Item=Edge2> + '_ {
        let len = self.vertices.len();
        (0..len).into_iter().map(move |ix| {
            Edge2 {
                a: self.vertices[ix].clone(),
                b: self.vertices[(ix + 1) % len].clone()
            }
        })
    }

    pub fn halfspaces(&self) -> impl Iterator<Item=Halfspace2> + '_ {
        self.edges().map(move |e| {
            let a = e.a.point;
            let b = e.b.point;
            Halfspace2 {
                normal: perpendicular(b - a),
                line: LineSegment2 { a, b}
            }
        })
    }

    pub fn extend(&mut self, v: Vertex2) -> bool {
        extend(&mut self.vertices, v)
    }

    pub fn validate(&self) -> Option<PolygonError> {
        if self.winding() == Some(Winding::Clockwise) {
            Some(PolygonError::InvalidWinding)
        } else {
            let points = self.vertices.iter().map(|v| v.point).collect();
            FlatPolygon2::new(points).err()
        }
    }

    pub fn winding(&self) -> Option<Winding> {
        Winding::find_from_points(self.vertices.iter().map(|v| &v.point))
    }

    pub fn new(points: Vec<Point2>) -> Result<FlatPolygon2, PolygonError> {
        if points.len() < 3 {
            Err(PolygonError::Zero)
        } else {
            match Winding::find_from_points(points.iter()) {
                Some(winding) => {
                    let in_order = if winding == Winding::Clockwise {
                        points.into_iter().rev().collect()
                    } else { points };

                    let vertices = in_order.into_iter().map(
                        |point| Vertex2 { index: None, point }
                    ).collect();

                    let polygon = FlatPolygon2 { vertices };

                    let convex = polygon.halfspaces().all(|hs| {
                        polygon.vertices.iter().all(|v| hs.contains(&v.point) != Orientation::Out)
                    });

                    if convex {
                        Ok(polygon)
                    } else {
                        Err(PolygonError::NonConvex)
                    }
                },
                None => Err(PolygonError::Zero)
            }
        }
    }
}

impl Segment<Vertex2> for Edge2
{
    fn from_endpoints(a: Vertex2, b: Vertex2) -> Self {
        Edge2 { a, b }
    }

    fn start(&self) -> Vertex2 { self.a.clone() }
    fn end(&self) -> Vertex2 { self.b.clone() }
}

impl Intersect<Halfspace2, Option<Vertex2>> for Edge2
{
    fn intersect(&self, knife: Halfspace2) -> Option<Vertex2> {
        let intersect = knife.line.intersect(&self.line());
        intersect.filter(|&(_, u, _)| {
            u >= 0.0 && u <= 1.0
        }).map(|(_, u, p)| {
            if u == 0.0 {
                self.a.clone()
            } else if u == 1.0 {
                self.b.clone()
            } else {
                Vertex2 {
                    point: p,
                    index: None,
                }
            }
        })
    }
}

impl Knife<FlatPolygon2, Option<FlatPolygon2>, Vec<Vertex2>> for Halfspace2
{
    fn cut(&self, target: FlatPolygon2) -> Parts<Option<FlatPolygon2>, Vec<Vertex2>> {
        let mut inside = FlatPolygon2 { vertices: vec![] };
        let mut outside = FlatPolygon2 { vertices: vec![] };
        let mut tangent = vec![];

        fn check_add(polygon: &mut FlatPolygon2, v: Vertex2) {
            if polygon.vertices.last().iter().all(|ev| ev.point != v.point) {
                polygon.vertices.push(v)
            }
        }

        fn add_start_vertex(polygon: &mut FlatPolygon2, e: &Option<Edge2>) {
            e.into_iter().for_each(|e| check_add(polygon, e.a.clone()));
        }

        let mut has_inside = false;
        let mut has_outside = false;
        for edge in target.edges().into_iter() {
            let parts = self.cut(edge);

            has_inside = has_inside || parts.inside.is_some();
            add_start_vertex(&mut inside, &parts.inside);
            has_outside = has_outside || parts.outside.is_some();
            add_start_vertex(&mut outside, &parts.outside);
            match parts.tangent {
                Some(hole) => {
                    let p = match hole {
                        Hole::Point(p) => p,
                        Hole::Segment(s) => s.a
                    };

                    inside.extend(p.clone());
                    outside.extend(p.clone());
                    extend(&mut tangent, p);
                },
                None => {}
           }
        }

        Parts {
           inside: if has_inside { Some(inside) } else { None },
           outside: if has_outside { Some(outside) } else { None },
           tangent
        }
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

    pub fn flat_rectangle(origin: Point2, extent: Vector2) -> FlatPolygon2 {
        assert!(extent.x > 0.0 && extent.y > 0.0);

        let ex = v2(extent.x, 0.0);
        let ey = v2(0.0, extent.y);

        let vertices = vec![
            origin,
            origin + ex,
            origin + extent,
            origin + ey
        ].into_iter().enumerate().map(|(index, point)| {
            Vertex2 { index: Some(index), point }

        }).collect();

        FlatPolygon2 { vertices }
    }

    fn assert_cut_ok(polygon: FlatPolygon2, hs: Halfspace2) -> Parts<Option<FlatPolygon2>, Vec<Vertex2>> {
        let parts = hs.cut(polygon);

        for polygon in parts.inside.iter().chain(parts.outside.iter()) {
            assert_eq!(polygon.validate(), None);
        }

        parts
    }

    #[test]
    fn test_simple_cut() {
        let r = flat_rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 0.5), v2(1.0, 0.0))
        };
        let parts = assert_cut_ok(r, hs);

        let p1 = parts.inside.unwrap();
        let p2 = parts.outside.unwrap();
        assert_eq!(p1.vertices.len(), 4);
        assert_eq!(p2.vertices.len(), 4);
    }

    #[test]
    fn test_no_cut() {
        let r = flat_rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 1.5), v2(1.0, 0.0))
        };
        let parts = assert_cut_ok(r, hs);
        let remains = parts.inside.unwrap();
        assert_eq!(remains.vertices.len(), 4);
        assert!(parts.outside.is_none());
    }

    #[test]
    fn test_tangent_no_cut() {
        let r = flat_rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 1.0), v2(1.0, 0.0))
        };
        let parts = assert_cut_ok(r, hs);
        let remains = parts.inside.unwrap();
        assert_eq!(remains.vertices.len(), 4);
        assert!(parts.outside.is_none());
        assert_eq!(parts.tangent.len(), 2);
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