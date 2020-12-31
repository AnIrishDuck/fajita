use std::ops;
use crate::plane::{p2, Point2, Vector2};

#[derive(Clone, Debug, PartialEq)]
pub struct Line2 {
    pub p: Point2,
    pub v: Vector2
}

/// Represents an infinite line:
/// 
/// ```
/// # use fajita::plane::{p2, v2};
/// # use fajita::plane::line::Line2;
/// let l = Line2::from_points(p2(1.0, 1.0), p2(2.0, 2.0));
/// assert_eq!(l.v, v2(1.0, 1.0));
/// ```
///
/// Supports common arithmetic operations:
///
/// ```
/// # use fajita::plane::{p2, v2};
/// # use fajita::plane::line::Line2;
/// let l = Line2::from_points(p2(1.0, 1.0), p2(2.0, 1.0)) + v2(1.0, 1.0);
/// assert_eq!(l, Line2::new(p2(2.0, 2.0), v2(1.0, 0.0)));
/// ```
impl Line2 {
    pub fn new(p: Point2, v: Vector2) -> Line2 {
        Line2 { p, v }
    }

    pub fn from_points(p1: Point2, p2: Point2) -> Line2 {
        Line2 { p: p1, v: p2 - p1 }
    }

    /// Finds the intersection of this object and another:
    ///
    /// ```
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::line::Line2;
    /// let l = Line2::new(p2(0.0, 2.0), v2(0.0, -2.0));
    /// let i = l.intersect(&Line2::new(p2(2.0, 0.0), v2(-1.0, 0.0)));
    /// assert_eq!(i, Some((1.0, 2.0, p2(0.0, 0.0))));
    ///
    /// let i = l.intersect(&Line2::new(p2(1.0, 2.0), v2(0.0, -2.0)));
    /// assert_eq!(i, None)
    /// ```
    ///
    /// Returns the scalar multiples of `self.v` and `other.v` where the
    /// intersection occurs, and the intersection point.
    pub fn intersect(&self, other: &Line2) -> Option<(f64, f64, Point2)> {
        let d = other.v.y * self.v.x - other.v.x * self.v.y;
        if d == 0.0 {
            None
        } else {
            let dy = self.p.y - other.p.y;
            let dx = self.p.x - other.p.x;
            let ua = (other.v.x * dy - other.v.y * dx) / d;
            let ub = (self.v.x * dy - self.v.y * dx) / d;

            let i = p2(self.p.x + ua * self.v.x,
                       self.p.y + ua * self.v.y);

            Some((ua, ub, i))
        }
    }
}

impl ops::Add<Vector2> for Line2 {
    type Output = Line2;

    fn add(self, other: Vector2) -> Self {
        Line2::new(self.p + other, self.v)
    }
}