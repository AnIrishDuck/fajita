use crate::plane::{p2, v2, Point2, Vector2, Polygon2};
use crate::plane::polygon::{HalfspaceIs, PolygonIs, LineIs};

#[derive(Clone)]
pub struct Pool2 {
    pub points: Vec<Point2>,
    pub lines: Vec<LineIs>,
    pub polygons: Vec<PolygonIs>,
}

pub fn insert<T>(v: &mut Vec<T>, e: T) -> usize {
    let ix = v.len();
    v.push(e);
    ix
}

impl Pool2 {
    pub fn new() -> Self {
        Pool2 {
            points: vec![],
            lines: vec![],
            polygons: vec![]
        }
    }

    pub fn rectangle(&mut self, origin: Point2, extent: Vector2) -> usize {
        assert!(extent.x > 0.0 && extent.y > 0.0);

        let ex = v2(extent.x, 0.0);
        let ey = v2(0.0, extent.y);

        let oo = insert(&mut self.points, origin);
        let eo = insert(&mut self.points, origin + ex);
        let ee = insert(&mut self.points, origin + extent);
        let oe = insert(&mut self.points, origin + ey);

        let lines = vec![
            insert(&mut self.lines, LineIs { a: oo, b: eo }),
            insert(&mut self.lines, LineIs { a: eo, b: ee }),
            insert(&mut self.lines, LineIs { a: ee, b: oe }),
            insert(&mut self.lines, LineIs { a: oe, b: oo }),
        ];

        let normals = vec![
            v2( 0.0, -1.0),
            v2( 1.0,  0.0),
            v2( 0.0,  1.0),
            v2(-1.0,  0.0),
        ];

        let halfspaces = lines.iter().zip(normals).map(|(&line_index, normal)|
            HalfspaceIs { line_index, normal }
        ).collect();

        insert(&mut self.polygons, PolygonIs { halfspaces })
    }


    pub fn get_polygon<'a>(&'a self, ix: usize) -> Polygon2<'a, &Pool2> {
        Polygon2 {
            pool: &self,
            indices: &self.polygons[ix]
        }
    }
}