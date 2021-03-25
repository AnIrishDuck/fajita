use cgmath;
pub mod line;
pub mod shape;
pub mod polygon;
pub mod shapes;

pub type Point2 = cgmath::Point2<f64>;
pub type Vector2 = cgmath::Vector2<f64>;

pub use line::LineSegment2;

pub fn p2<T>(x: T, y: T) -> cgmath::Point2<T> {
    cgmath::Point2::new(x, y)
}
pub use cgmath::vec2 as v2;

pub use polygon::Polygon2 as Polygon2;