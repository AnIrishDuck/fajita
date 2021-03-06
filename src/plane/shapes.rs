//! Constructors for common two-dimensional shapes in the plane.
use crate::plane::{v2, Point2, Vector2};
use crate::plane::polygon::{Polygon2, Vertex2};

/// A simple four-sided box constructed from an `origin` and vector `extent`. The
/// extent must be non-negative.
pub fn rectangle(origin: Point2, extent: Vector2) -> Polygon2 {
    assert!(extent.x > 0.0 && extent.y > 0.0);

    let ex = v2(extent.x, 0.0);
    let ey = v2(0.0, extent.y);

    let vertices = vec![
        origin,
        origin + ex,
        origin + extent,
        origin + ey
    ].into_iter().enumerate().map(|(index, point)| {
        Vertex2 { index: Some(index), reverse: false, point }
    }).collect();

    Polygon2 { vertices }
}