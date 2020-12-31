use std::ops;
use crate::plane::{Point2, Vector2};

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
}

impl ops::Add<Vector2> for Line2 {
    type Output = Line2;

    fn add(self, other: Vector2) -> Self {
        Line2::new(self.p + other, self.v)
    }
}