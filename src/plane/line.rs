use std::ops;
use std::cmp::Ordering;
use crate::plane::{p2, Point2, Vector2};
use crate::util::container::{Container, Orientation};
use crate::util::intersect::Intersect;
use crate::util::knife::{Knife, Parts};
use crate::util::segment::Segment;
use cgmath::InnerSpace;

#[derive(Clone, Debug, PartialEq)]
pub struct Halfspace2 {
    pub line: LineSegment2,
    pub normal: Vector2
}

impl Container<Point2> for Halfspace2 {
    fn contains(&self, p: &Point2) -> Orientation {
        match (self.line.a - p).dot(self.normal).partial_cmp(&0.0).unwrap() {
            Ordering::Less => Orientation::Out,
            Ordering::Equal => Orientation::On,
            Ordering::Greater => Orientation::In,
        }
    }
}

impl Segment<Point2> for LineSegment2 {
    fn from_endpoints(a: Point2, b: Point2) -> Self {
        LineSegment2 { a, b }
    }

    fn start(&self) -> Point2 { self.a }
    fn end(&self) -> Point2 { self.b }
}

impl Intersect<Halfspace2, Option<Point2>> for LineSegment2 {
    fn intersect(&self, knife: Halfspace2) -> Option<Point2> {
        let intersect = knife.line.intersect(&self);
        intersect.filter(|&(_, u, _)| {
            u >= 0.0 && u <= 1.0
        }).map(|(_, _, p)| p)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct LineSegment2 {
    pub a: Point2,
    pub b: Point2
}

/// Represents an infinite line:
///
/// ```
/// # use fajita::plane::{p2, v2};
/// # use fajita::plane::line::LineSegment2;
/// let l = LineSegment2::new(p2(1.0, 1.0), p2(2.0, 2.0));
/// ```
///
/// Supports common arithmetic operations:
///
/// ```
/// # use fajita::plane::{p2, v2};
/// # use fajita::plane::line::LineSegment2;
/// let l = LineSegment2::new(p2(1.0, 1.0), p2(2.0, 1.0)) + v2(1.0, 1.0);
/// assert_eq!(l, LineSegment2::from_pv(p2(2.0, 2.0), v2(1.0, 0.0)));
/// ```
impl LineSegment2 {
    pub fn new(a: Point2, b: Point2) -> LineSegment2 {
        LineSegment2 { a, b }
    }

    pub fn from_pv(p: Point2, dp: Vector2) -> LineSegment2 {
        LineSegment2 { a: p, b: p + dp }
    }

    /// Finds the intersection of this object and another:
    ///
    /// ```
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::line::LineSegment2;
    /// let l = LineSegment2::from_pv(p2(0.0, 2.0), v2(0.0, -2.0));
    /// let i = l.intersect(&LineSegment2::from_pv(p2(2.0, 0.0), v2(-1.0, 0.0)));
    /// assert_eq!(i, Some((1.0, 2.0, p2(0.0, 0.0))));
    ///
    /// let i = l.intersect(&LineSegment2::from_pv(p2(1.0, 2.0), v2(0.0, -2.0)));
    /// assert_eq!(i, None)
    /// ```
    ///
    /// Returns the scalar multiples of `self.v` and `other.v` where the
    /// intersection occurs, and the intersection point.
    pub fn intersect(&self, other: &LineSegment2) -> Option<(f64, f64, Point2)> {
        let ov = other.b - other.a;
        let sv = self.b - self.a;
        let d = ov.y * sv.x - ov.x * sv.y;
        if d == 0.0 {
            None
        } else {
            let dy = self.a.y - other.a.y;
            let dx = self.a.x - other.a.x;
            let ua = (ov.x * dy - ov.y * dx) / d;
            let ub = (sv.x * dy - sv.y * dx) / d;

            let i = p2(self.a.x + ua * sv.x,
                       self.a.y + ua * sv.y);

            Some((ua, ub, i))
        }
    }
}

impl ops::Add<Vector2> for LineSegment2 {
    type Output = LineSegment2;

    fn add(self, dp: Vector2) -> Self {
        LineSegment2::new(self.a + dp, self.b + dp)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::plane::{p2, v2};
    use crate::util::segment::Span;

    #[test]
    fn test_halfspace_direction() {
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::new(p2(0.0, 0.0), p2(1.0, 0.0))
        };

        assert_eq!(hs.contains(&p2(1.0, 1.0)), Orientation::Out);
        assert_eq!(hs.contains(&p2(2.0, 0.0)), Orientation::On);
        assert_eq!(hs.contains(&p2(2.0, -1.0)), Orientation::In);
    }

    #[test]
    fn test_halfspace_cuts() {
        for x in vec![-10.0, 0.0, 10.0] {
            let hs = Halfspace2 {
                normal: v2(0.0, 1.0),
                line: LineSegment2::from_pv(p2(x, 0.0), v2(1.0, 0.0))
            };

            let parts = hs.cut(LineSegment2::new(p2(0.5, -1.0), p2(0.5, 1.0)));
            assert_eq!(parts.inside, Some(LineSegment2::new(p2(0.5, -1.0), p2(0.5, 0.0))));
            assert_eq!(parts.tangent, Some(Span::Point(p2(0.5, 0.0))));
            assert_eq!(parts.outside, Some(LineSegment2::new(p2(0.5, 0.0), p2(0.5, 1.0))));


            let parts = hs.cut(LineSegment2::new(p2(0.5, 1.0), p2(0.5, 2.0)));
            assert_eq!(parts.inside, None);
            assert_eq!(parts.tangent, None);
            assert_eq!(parts.outside, Some(LineSegment2::new(p2(0.5, 1.0), p2(0.5, 2.0))));

            let parts = hs.cut(LineSegment2::new(p2(0.5, 0.0), p2(0.5, 2.0)));
            assert_eq!(parts.inside, None);
            assert_eq!(parts.tangent, Some(Span::Point(p2(0.5, 0.0))));
            assert_eq!(parts.outside, Some(LineSegment2::new(p2(0.5, 0.0), p2(0.5, 2.0))));

            let parts = hs.cut(LineSegment2::new(p2(0.5, -1.0), p2(0.5, -2.0)));
            assert_eq!(parts.inside, Some(LineSegment2::new(p2(0.5, -1.0), p2(0.5, -2.0))));
            assert_eq!(parts.tangent, None);
            assert_eq!(parts.outside, None);

            let original = LineSegment2::new(p2(-2.0, 0.0), p2(-1.0, 0.0));
            let parts = hs.cut(original.clone());
            assert_eq!(parts.inside, None);
            assert_eq!(parts.tangent, Some(Span::Segment(original)));
            assert_eq!(parts.outside, None);
        }
    }

    #[test]
    fn test_halfspace_cuts_preserve_order() {
        let hs = Halfspace2 {
            normal: v2(0.0, 1.0),
            line: LineSegment2::from_pv(p2(-1.0, 0.5), v2(1.0, 0.0))
        };

        let parts = hs.cut(LineSegment2::new(p2(0.0, 1.0), p2(0.0, 0.0)));
        assert_eq!(parts.inside, Some(LineSegment2::new(p2(0.0, 0.5), p2(0.0, 0.0))));
        assert_eq!(parts.tangent, Some(Span::Point(p2(0.0, 0.5))));
        assert_eq!(parts.outside, Some(LineSegment2::new(p2(0.0, 1.0), p2(0.0, 0.5))));
    }
}