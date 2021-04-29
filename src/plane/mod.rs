//! Various useful objects in the two-dimensional plane.
//!
//! The building blocks are the [`Point2`] and [`Vector2`] types taken directly
//! from cgmath. These can be used to create the core [`Halfspace2`] and
//! [`LineSegment2`] types, from which we can construct [`Polygon2`], which can
//! be used to define [`Shape2`].
//!
//! [`Shape2`] can be used to model arbitrary two-dimensional shapes.
use cgmath;
pub mod line;
pub mod shape;
pub mod polygon;
pub mod shapes;

pub type Point2 = cgmath::Point2<f64>;
pub type Vector2 = cgmath::Vector2<f64>;

pub use line::{LineSegment2, Halfspace2};
pub use polygon::Polygon2;
pub use shape::Shape2;

/// Short constructor for `Point2`
pub fn p2<T>(x: T, y: T) -> cgmath::Point2<T> {
    cgmath::Point2::new(x, y)
}
pub use cgmath::vec2 as v2;