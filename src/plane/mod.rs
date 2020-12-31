use cgmath;
pub mod line;

pub type Point2 = cgmath::Point2<f64>;
pub type Vector2 = cgmath::Vector2<f64>;

pub fn p2<T>(x: T, y: T) -> cgmath::Point2<T> {
    cgmath::Point2::new(x, y)
}
pub use cgmath::vec2 as v2;