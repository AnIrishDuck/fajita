use crate::plane::{v2, Point2, Vector2};
use crate::plane::shape::Shape2;
use crate::plane::polygon::{HalfspaceIs, LineIs, PolygonIs};

pub fn rectangle(origin: Point2, extent: Vector2) -> Shape2 {
    let mut p = Shape2::new();
    add_rectangle(&mut p, origin, extent);
    p
}

pub fn add_rectangle(p: &mut Shape2, origin: Point2, extent: Vector2) -> usize {
    assert!(extent.x > 0.0 && extent.y > 0.0);

    let ex = v2(extent.x, 0.0);
    let ey = v2(0.0, extent.y);

    let point_start = p.points.len();
    p.points.extend(vec![
        origin,
        origin + ex,
        origin + extent,
        origin + ey
    ]);

    let line_start = p.lines.len();
    p.lines.extend(vec![
        LineIs { a: point_start, b: point_start + 1 },
        LineIs { a: point_start + 1, b: point_start + 2 },
        LineIs { a: point_start + 2, b: point_start + 3 },
        LineIs { a: point_start + 3, b: point_start },
    ]);

    let normals = vec![
        v2( 0.0, -1.0),
        v2( 1.0,  0.0),
        v2( 0.0,  1.0),
        v2(-1.0,  0.0),
    ];

    let halfspaces = normals.into_iter().enumerate().map(|(ix, normal)|
        HalfspaceIs { line_index: line_start + ix, normal }
    ).collect();

    let ix = p.polygons.len();
    p.polygons.push_back(PolygonIs { halfspaces });
    ix
}

