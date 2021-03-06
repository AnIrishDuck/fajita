//! Definitions for [`Polygon`], [`Polygon2`], and associated helpers.
use cgmath::EuclideanSpace;

use crate::plane::{LineSegment2, Point2, Vector2};
use crate::plane::line::{perpendicular, Halfspace2};
use super::shape::Shape2;
use crate::util::container::{containers, Container, Orientation};
use crate::util::intersect::Intersect;
use crate::util::knife::{knives, Knife, Parts};
use crate::util::segment::{Edge, Segment, Span};
use crate::util::vertex::Vertex;
use crate::util::winding::Winding;

pub type Vertex2 = Vertex<Point2>;
pub type Edge2 = Edge<Point2>;

impl From<&Edge2> for LineSegment2 {
    fn from(e: &Edge2) -> LineSegment2 {
        LineSegment2 { a: e.start().point, b: e.end().point }
    }
}

fn extend<P: Clone + PartialEq>(vertices: &mut Vec<Vertex<P>>, v: Vertex<P>) -> bool {
    let start = vertices.iter().take(1);
    let end = vertices.last().clone().into_iter();
    if start.chain(end).all(|ev| ev.point != v.point) {
        vertices.push(v);
        true
    } else {
        false
    }
}

impl Winding {
    pub fn from_points(a: Point2, b: Point2, c: Point2) -> Option<Self> {
        let normal = perpendicular(b - a);
        let hs = Halfspace2 { normal, origin: a };
        // perpendicular always returns a clockwise vector, and normals point out
        // therefore Out => Clockwise
        match hs.contains(&c) {
            Orientation::In => Some(Winding::CounterClockwise),
            Orientation::On => None,
            Orientation::Out => Some(Winding::Clockwise),
        }
    }

    pub fn find_from_points<I>(points: I) -> Option<Self>
    where
    I: IntoIterator<Item = Point2>
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

/// Enumerates violations of the laws that [`Polygon2`] must follow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PolygonError {
    Zero,
    InvalidWinding,
    NotConvex
}

/// A generic cycle of points that form a polygon in the plane or in
/// space. Used to define the concrete [`Polygon2`] and [`crate::space::polygon::Polygon3`]
/// types.
#[derive(Clone, Debug)]
pub struct Polygon<P: Clone>
{
    pub vertices: Vec<Vertex<P>>,
}

impl<P: Clone + PartialEq> Polygon<P>
{
    /// Iterate over all points in this polygon.
    pub fn points(&self) -> impl Iterator<Item=P> + '_ {
        self.vertices.iter().map(|v| v.point.clone())
    }

    /// Iterate over all eges in this polygon, including the final edge from the
    /// end to start vertex.
    pub fn edges(&self) -> impl Iterator<Item=Edge<P>> + '_ {
        let len = self.vertices.len();
        (0..len).into_iter().map(move |ix| {
            Edge::from_endpoints(
                self.vertices[ix].clone(),
                self.vertices[(ix + 1) % len].clone()
            )
        })
    }

    /// Adds the given vertex to this polygon if it is not already present at the
    /// start or end.
    pub fn extend(&mut self, v: Vertex<P>) -> bool {
        extend(&mut self.vertices, v)
    }
}

/// A polygon composed of two-dimensional points.
///
/// Every [`Polygon2`] must follow three laws:
///
/// - **non-zero**: must have at least three points.
/// - **clockwise**: vertices are stored so that their winding is clockwise.
/// - **convex**: all points must be _in_ or _on_ all halfspaces of the polygon.
///
/// The associated [`PolygonError`] enum tracks violations of these laws.
///
/// There is also a fourth, implicit law guaranteed by this representation: every
/// vertex belongs to exactly two segments, making the polygon closed.
pub type Polygon2 = Polygon<Point2>;

impl Polygon2
{
    /// Iterates over every associated halfspace of this polygon.
    pub fn halfspaces(&self) -> impl Iterator<Item=Halfspace2> + '_ {
        self.edges().map(move |e| {
            let a = e.start().point;
            let b = e.end().point;
            Halfspace2 {
                normal: perpendicular(b - a),
                origin: a
            }
        })
    }

    /// The center point of this polygon. As the polygon is convex, the center is
    /// guaranteed to be inside it.
    pub fn center(&self) -> Point2 {
        let sum: Vector2 = self.vertices.iter().map(|v| v.point.to_vec()).sum();
        Point2::from_vec(sum / self.vertices.len() as f64)
    }

    /// Verify that this polygon follows all associated laws.
    pub fn validate(&self) -> Option<PolygonError> {
        if self.winding() == Some(Winding::Clockwise) {
            Some(PolygonError::InvalidWinding)
        } else {
            let points: Vec<Point2> = self.vertices.iter().map(|v| v.point).collect();
            Polygon2::new(points).err()
        }
    }

    /// Calculates the winding of this polygon. For all valid polygons, must be
    /// [`Winding::Clockwise`].
    pub fn winding(&self) -> Option<Winding> {
        Winding::find_from_points(self.vertices.iter().map(|v| v.point))
    }

    /// Calculate the union of this polygon with `other`.
    pub fn union<I: Into<Shape2>>(self, other: I) -> Shape2 {
        let shape: Shape2 = self.into();
        shape.union(&other.into())
    }

    /// Calculates the result of removing the `other` polygon from this one. If
    /// the result is zero, return `None`.
    pub fn remove<I: Into<Shape2>>(self, other: I) -> Option<Shape2> {
        let shape: Shape2 = self.into();
        shape.remove(&other.into())
    }

    /// Construct a new polygon from points. Returns a [`PolygonError`] if the
    /// result does not obey the polygon laws.
    pub fn new<'a, I, N>(into: N) -> Result<Polygon2, PolygonError>
    where
    N: IntoIterator<Item = Point2, IntoIter=I>,
    I: DoubleEndedIterator<Item = Point2> + ExactSizeIterator + Clone
    {
        let points = into.into_iter();
        if points.len() < 3 {
            Err(PolygonError::Zero)
        } else {
            match Winding::find_from_points(points.clone()) {
                Some(winding) => {
                    let in_order: Vec<Point2> = if winding == Winding::Clockwise {
                        points.into_iter().rev().collect()
                    } else { points.collect() };

                    let vertices = in_order.into_iter().map(
                        |point| Vertex2 { index: None, reverse: false, point }
                    ).collect();

                    let polygon = Polygon2 { vertices };

                    let convex = polygon.halfspaces().all(|hs| {
                        polygon.vertices.iter().all(|v| hs.contains(&v.point) != Orientation::Out)
                    });

                    if convex {
                        Ok(polygon)
                    } else {
                        Err(PolygonError::NotConvex)
                    }
                },
                None => Err(PolygonError::Zero)
            }
        }
    }
}

impl Intersect<Polygon2> for Polygon2
{
    type Output = Option<Polygon2>;

    fn intersect(&self, knife: Polygon2) -> Self::Output {
        knife.cut(self.clone()).inside.first().cloned()
    }
}

impl Intersect<Halfspace2> for Edge2
{
    type Output = Option<Vertex2>;

    fn intersect(&self, knife: Halfspace2) -> Option<Vertex2> {
        Edge::intersect::<_, LineSegment2>(&self, knife)
    }
}

impl<K, P> Knife<Polygon<P>> for K
where
    K: Knife<Edge<P>, Output=Option<Edge<P>>, Tangent=Option<Span<Vertex<P>, Edge<P>>>>,
    P: Clone + PartialEq
{
    type Output = Option<Polygon<P>>;
    type Tangent = Vec<Vertex<P>>;

    fn cut(&self, target: Polygon<P>) -> Parts<Option<Polygon<P>>, Vec<Vertex<P>>> {
        let mut inside = Polygon { vertices: vec![] };
        let mut outside = Polygon { vertices: vec![] };
        let mut tangent = vec![];

        fn add_start_vertex<P: Clone + PartialEq>(polygon: &mut Polygon<P>, e: &Option<Edge<P>>) {
            e.into_iter().for_each(|e| { polygon.extend(e.start().clone()); });
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
                        Span::Point(p) => p,
                        Span::Segment(s) => s.start()
                    };

                    inside.extend(p.clone());
                    outside.extend(p.reversed());
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

impl Container<Point2> for Polygon2
{
    fn contains(&self, point: &Point2) -> Orientation {
        containers::intersect(self.halfspaces(), point)
    }
}

impl Knife<Polygon2> for Polygon2
{
    type Output = Vec<Polygon2>;
    type Tangent = Vec<Vertex2>;

    fn cut(&self, target: Polygon2) -> Parts<Vec<Polygon2>, Vec<Vertex2>> {
        knives::carve(self.halfspaces(), target)
    }
}

#[cfg(test)]
mod tests {
    use crate::plane::{p2, v2};
    use crate::plane::shapes::rectangle;
    use super::*;

    fn assert_hs_cut_ok(original: Polygon2, hs: Halfspace2) -> Parts<Option<Polygon2>, Vec<Vertex2>> {
        let parts = hs.cut(original.clone());

        for polygon in parts.inside.iter().chain(parts.outside.iter()) {
            let polygon = polygon.clone();
            assert_eq!(polygon.validate(), None);

            assert!(
                original.contains(&polygon.center()) == Orientation::In,
                "center of {:?} not in original polygon", polygon.vertices
            );
            assert!(
                polygon.contains(&polygon.center()) == Orientation::In,
                "center {:?} not in {:?}", polygon.center(), polygon.vertices
            );
            for v in polygon.vertices {
                let p = v.point;
                assert!(
                    original.contains(&p) == Orientation::On,
                    "!({:?} == {:?})", p, original.vertices
                )
            }
        }

        parts
    }

    fn assert_poly_cut_ok(knife: Polygon2, target: Polygon2) {
        let part = knife.cut(target.clone());

        for frag in part.outside {
            let recut = knife.cut(frag);

            assert_eq!(
                recut.inside.len(), 0,
                "outer fragment has part inside original"
            );

            assert_eq!(
                recut.outside.len(), 1,
                "outer fragment does not have part outside original"
            );
        }

        for i in part.inside.into_iter() {
            let recut = knife.cut(i);

            assert_eq!(
                recut.inside.len(), 1,
                "inner fragment has no part inside original"
            );

            assert_eq!(
                recut.outside.len(), 0,
                "inner fragment has part outside original"
            );
        }

        for v in part.tangent.into_iter() {
            assert!(
                knife.contains(&v.point) == Orientation::On
                || target.contains(&v.point) == Orientation::On,
                "tangent point not on either shape"
            )
        }
    }

    #[test]
    fn test_validation() {
        let linear = Polygon2::new(vec![p2(0.0, 0.0), p2(1.0, 0.0), p2(2.0, 0.0)]);
        assert_eq!(linear.err(), Some(PolygonError::Zero));

        let concave = Polygon2::new(vec![
            p2(0.0, 0.0), p2(1.0, 0.5), p2(2.0, 0.0), p2(1.0, 1.0)
        ]);
        assert_eq!(concave.err(), Some(PolygonError::NotConvex));

        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let mut vertices = r.vertices;
        vertices.reverse();
        let reversed = Polygon2 { vertices };
        assert_eq!(reversed.validate(), Some(PolygonError::InvalidWinding));
    }

    #[test]
    fn test_simple_cut() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            origin: p2(-1.0, 0.5)
        };
        let parts = assert_hs_cut_ok(r, hs);

        let p1 = parts.inside.unwrap();
        let p2 = parts.outside.unwrap();
        assert_eq!(p1.vertices.len(), 4);
        assert_eq!(p2.vertices.len(), 4);
    }

    #[test]
    fn test_no_cut() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            origin: p2(-1.0, 1.5)
        };
        let parts = assert_hs_cut_ok(r, hs);
        let remains = parts.inside.unwrap();
        assert_eq!(remains.vertices.len(), 4);
        assert!(parts.outside.is_none());
    }

    #[test]
    fn test_tangent_no_cut() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        for hs in r.halfspaces() {
            let parts = assert_hs_cut_ok(r.clone(), hs);
            let remains = parts.inside.unwrap();
            assert_eq!(remains.vertices.len(), 4);
            assert!(parts.outside.is_none());
            assert_eq!(parts.tangent.len(), 2);
        }
    }

    #[test]
    fn test_point_compare() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        assert_eq!(r.contains(&p2(0.5, 0.5)), Orientation::In);
        assert_eq!(r.contains(&p2(0.5, 0.0)), Orientation::On);
        assert_eq!(r.contains(&p2(0.5, 2.0)), Orientation::Out);
    }

    #[test]
    fn test_simple_polygon_cut() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = rectangle(p2(0.5, 0.5), v2(1.0, 1.0));

        assert_poly_cut_ok(a, b);
    }

    #[test]
    fn test_no_polygon_cut() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = rectangle(p2(1.0, 0.5), v2(0.5, 0.5));

        assert_poly_cut_ok(a, b);
    }
}