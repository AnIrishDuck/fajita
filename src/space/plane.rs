use crate::space::{Point3, Vector3};
use crate::util::container::{Container, Orientation};
use crate::util::intersect::Intersect;
use crate::util::segment::Segment;
use crate::util::winding::Winding;
use cgmath::{InnerSpace, EuclideanSpace};

#[derive(Clone, Debug, PartialEq)]
pub struct LineSegment3 {
    pub a: Point3,
    pub b: Point3
}

impl LineSegment3 {
    pub fn new(a: Point3, b: Point3) -> Self {
        LineSegment3 { a, b }
    }

    pub fn from_pv(p: Point3, v: Vector3) -> Self {
        LineSegment3 { a: p, b: p + v }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Halfspace3 {
    pub origin: Point3,
    pub normal: Vector3
}

impl Container<Point3> for Halfspace3 {
    fn contains(&self, p: &Point3) -> Orientation {
        self.contains(&(p - self.origin))
    }
}

impl Container<Vector3> for Halfspace3 {
    fn contains(&self, v: &Vector3) -> Orientation {
        let dp = v.dot(self.normal);
        if dp.abs() < 0.000000001 {
            Orientation::On
        } else if dp < 0.0 {
            Orientation::In
        } else {
            Orientation::Out
        }
    }
}

impl Halfspace3 {
    pub fn find_from_points<I>(points: I) -> Option<Self>
    where
    I: IntoIterator<Item = Point3>
    {
        let mut it = points.into_iter();
        let a = it.next();
        let b = it.next();
        match (a, b) {
            (Some(a), Some(b)) => {
                it.find_map(|c| {
                    let v1 = b - a;
                    let v2 = c - b;
                    let normal = v1.cross(v2);
                    if normal.dot(normal) != 0.0 {
                        let hs = Halfspace3 {
                            normal,
                            origin: a
                        };

                        Some(hs)
                    } else {
                        None
                    }
                })
            },
            _ => None
        }
    }

    pub fn winding_from_points(&self, a: Point3, b: Point3, c: Point3) -> Option<Winding> {
        let v1 = b - a;
        let v2 = c - b;
        let wn = v1.cross(v2);
        // due to the right-hand-rule, the cross product of two vectors in a
        // plane is counter-clockwise. the dot product of a vector and itself is
        // positive, and the dot product of a vector and its inverse is negative.
        let dot = wn.dot(self.normal);
        if dot < 0.0 {
            Some(Winding::Clockwise)
        } else if dot == 0.0 {
            None
        } else {
            Some(Winding::CounterClockwise)
        }
    }

    pub fn find_winding_from_points<I>(&self, points: I) -> Option<Winding>
    where
    I: IntoIterator<Item = Point3>
    {
        let mut it = points.into_iter();
        let a = it.next();
        let b = it.next();
        match (a, b) {
            (Some(a), Some(b)) => {
                it.find_map(|c| {
                    self.winding_from_points(a.clone(), b.clone(), c.clone())
                })
            },
            _ => None
        }
    }
}

impl Segment for LineSegment3 {
    type Point = Point3;

    fn from_endpoints(a: Point3, b: Point3) -> Self {
        LineSegment3 { a, b }
    }

    fn start(&self) -> Point3 { self.a }
    fn end(&self) -> Point3 { self.b }
}

impl Intersect<Halfspace3> for LineSegment3 {
    type Output = Option<Point3>;

    fn intersect(&self, knife: Halfspace3) -> Option<Point3> {
        let v = self.vector();
        let n = knife.normal.normalize();
        let d = n.dot(v);
        let k = n.dot(knife.origin.to_vec());

        if d == 0.0 {
            None
        } else {
            let u = (k - n.dot(self.start().to_vec())) / d;
            if u >= 0.0 && u <= 1.0 {
                Some(self.start() + u * v)
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::space::{p3, v3};
    use crate::util::segment::Span;
    use crate::util::knife::Knife;

    #[test]
    fn test_halfspace_direction() {
        let hs = Halfspace3 {
            normal: v3(0.0, 0.0, 1.0),
            origin: p3(0.0, 0.0, 5.0)
        };

        assert_eq!(hs.contains(&v3(1.0, 1.0, 1.0)), Orientation::Out);
        assert_eq!(hs.contains(&-v3(1.0, 1.0, 1.0)), Orientation::In);

        assert_eq!(hs.contains(&p3(1.0, 1.0, 0.0)), Orientation::In);
        assert_eq!(hs.contains(&p3(2.0, 0.0, 5.0)), Orientation::On);
        assert_eq!(hs.contains(&p3(2.0, -1.0, 8.0)), Orientation::Out);
    }

    #[test]
    fn test_halfspace_cuts() {
        let hs = Halfspace3 {
            normal: v3(0.0, 0.0, 1.0),
            origin: p3(0.0, 0.0, 0.0)
        };

        let parts = hs.cut(LineSegment3::new(p3(-0.5, -0.5, -1.0), p3(0.5, 0.5, 1.0)));
        assert_eq!(parts.inside, Some(LineSegment3::new(p3(-0.5, -0.5, -1.0), p3(0.0, 0.0, 0.0))));
        assert_eq!(parts.tangent, Some(Span::Point(p3(0.0, 0.0, 0.0))));
        assert_eq!(parts.outside, Some(LineSegment3::new(p3(0.0, 0.0, 0.0), p3(0.5, 0.5, 1.0))));


        let parts = hs.cut(LineSegment3::new(p3(0.5, 1.0, 2.0), p3(0.5, 2.0, 3.0)));
        assert_eq!(parts.inside, None);
        assert_eq!(parts.tangent, None);
        assert_eq!(parts.outside, Some(LineSegment3::new(p3(0.5, 1.0, 2.0), p3(0.5, 2.0, 3.0))));

        let parts = hs.cut(LineSegment3::new(p3(0.5, 0.0, 0.0), p3(0.5, 2.0, 1.0)));
        assert_eq!(parts.inside, None);
        assert_eq!(parts.tangent, Some(Span::Point(p3(0.5, 0.0, 0.0))));
        assert_eq!(parts.outside, Some(LineSegment3::new(p3(0.5, 0.0, 0.0), p3(0.5, 2.0, 1.0))));

        let parts = hs.cut(LineSegment3::new(p3(0.5, -1.0, -1.0), p3(0.5, -2.0, -2.0)));
        assert_eq!(parts.inside, Some(LineSegment3::new(p3(0.5, -1.0, -1.0), p3(0.5, -2.0, -2.0))));
        assert_eq!(parts.tangent, None);
        assert_eq!(parts.outside, None);

        let original = LineSegment3::new(p3(-2.0, 0.0, 0.0), p3(-1.0, 0.0, 0.0));
        let parts = hs.cut(original.clone());
        assert_eq!(parts.inside, None);
        assert_eq!(parts.tangent, Some(Span::Segment(original)));
        assert_eq!(parts.outside, None);
    }

    #[test]
    fn test_halfspace_winding() {
        let hs = Halfspace3 {
            normal: v3(0.0, 0.0, 1.0),
            origin: p3(0.0, 0.0, 0.0)
        };

        let tri = vec![p3(0.0, 0.0, 0.0), p3(1.0, 0.0, 0.0), p3(0.0, 1.0, 0.0)];

        assert_eq!(
            hs.winding_from_points(tri[0], tri[1], tri[2]),
            Some(Winding::CounterClockwise)
        );

        assert_eq!(
            hs.winding_from_points(tri[2], tri[1], tri[0]),
            Some(Winding::Clockwise)
        );

        assert_eq!(
            hs.winding_from_points(tri[2], tri[1], tri[0]),
            Some(Winding::Clockwise)
        );

        assert_eq!(
            hs.winding_from_points(
                p3(0.0, 0.0, 0.0),
                p3(1.0, 0.0, 0.0),
                p3(2.0, 0.0, 0.0)
            ),
            None
        );
    }
}

