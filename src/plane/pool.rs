use crate::plane::{p2, v2, Point2, Vector2, Polygon2};
use crate::plane::polygon::{HalfspaceIs, PolygonIs, LineIs};
use std::collections::HashMap;

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


    pub fn get_polygon(&self, index: usize) -> Polygon2<&Pool2> {
        Polygon2 {
            pool: &self,
            index
        }
    }

    /// Combines the points in `self` and `other`, updating the backing point
    /// array in self and returning a new polygon for `other` that uses this same
    /// array:
    ///
    /// ```
    /// # use fajita::plane::pool::Pool2;
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::shapes::rectangle;
    /// let mut pool = Pool2::new();
    /// let r1 = pool.rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// let r2 = rectangle(p2(1.0, 0.0), v2(1.0, 1.0));
    /// pool.unify(&r2.pool);
    /// assert_eq!(pool.polygons.len(), 2);
    /// assert_eq!(pool.points.len(), 6);
    /// ```
    pub fn unify(&mut self, other: &Pool2) {
        let self_points: HashMap<_, _> = self.points.iter().enumerate()
            .map(|(ix, p)| (exact_hash(p), ix)).collect();

        let mapped: HashMap<_, _> = other.points.iter().enumerate().map(|(ix, op)| {
            let h = exact_hash(&op);
            match self_points.get(&h) {
                Some(self_ix) => (ix, *self_ix),
                None => {
                    let self_ix = self.points.len();
                    self.points.push(op.clone());
                    (ix, self_ix)
                }
            }
        }).collect();

        self.lines.extend(other.lines.iter().map(|l| {
            LineIs {
                a: mapped[&l.a],
                b: mapped[&l.b],
            }
        }));

        self.polygons.extend(
            other.polygons.iter().map(|p| {
                let halfspaces = p.halfspaces.iter().map(|hs| {
                    HalfspaceIs {
                        normal: hs.normal,
                        line_index: hs.line_index + other.lines.len()
                    }
                }).collect();

                PolygonIs {
                    halfspaces
                }
            })
        )
    }
}


// Note that this has all the obvious issues with floating point comparisons
fn exact_hash(p: &Point2) -> (u64, u64) {
    (p.x.to_bits(), p.y.to_bits())
}