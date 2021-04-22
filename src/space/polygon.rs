use cgmath::EuclideanSpace;
use crate::space::{p3, v3, Point3, Vector3};
use crate::space::plane::{Halfspace3, LineSegment3};
use super::polyhedron::Face3;
use crate::plane::polygon::{Polygon2, Polygon};
use crate::util::container::{Container, Orientation};
use crate::util::intersect::Intersect;
use crate::util::segment::{Edge, Segment};
use crate::util::vertex::Vertex;

pub type Vertex3 = Vertex<Point3>;
pub type Edge3 = Edge<Point3>;
pub type Polygon3 = Polygon<Point3>;

pub struct Basis3 {
    x: Vector3,
    y: Vector3,
    z: Vector3,
}

impl Basis3 {
    pub fn project(&self, p: Point3) -> Point3 {
        Point3::from_vec(p.x * self.x + p.y * self.y + p.z * self.z)
    }

    pub fn unit() -> Self {
        Basis3 {
            x: v3(1.0, 0.0, 0.0),
            y: v3(0.0, 1.0, 0.0),
            z: v3(0.0, 0.0, 1.0),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PolygonError3 {
    Zero,
    NotConvex,
    NotPlanar
}

impl Polygon3
{
    pub fn validate(&self) -> Option<PolygonError3> {
        let points: Vec<Point3> = self.vertices.iter().map(|v| v.point).collect();
        Polygon3::new(points).err()
    }

    pub fn face(self) -> Face3 {
        Face3::from_wound_polygon(self).unwrap()
    }

    pub fn project(polygon: &Polygon2, basis: &Basis3) -> Polygon3 {
        let vertices = polygon.vertices.iter().map(|v| {
            Vertex3 {
                index: None,
                point: basis.project(p3(v.point.x, v.point.y, 0.0))
            }
        }).collect();

        Polygon3 { vertices }
    }

    pub fn new<'a, I, N>(into: N) -> Result<Polygon3, PolygonError3>
    where
    N: IntoIterator<Item = Point3, IntoIter=I>,
    I: DoubleEndedIterator<Item = Point3> + ExactSizeIterator + Clone
    {
        let points = into.into_iter();
        if points.len() < 3 {
            Err(PolygonError3::Zero)
        } else {
            match Halfspace3::find_from_points(points.clone()) {
                Some(hs) => {
                    let vertices = points.into_iter().map(
                        |point| Vertex3 { index: None, point }
                    ).collect();

                    let polygon = Polygon3 { vertices };

                    if polygon.vertices.iter().any(|v| hs.contains(&v.point) != Orientation::On) {
                        Err(PolygonError3::NotPlanar)
                    } else {
                        let convex = polygon.edges().all(|e| {
                            let ehs = Halfspace3 {
                                origin: e.start().point,
                                normal: (e.end().point - e.start().point).cross(hs.normal)
                            };

                            polygon.vertices.iter().all(|v| ehs.contains(&v.point) != Orientation::Out)
                        });

                        if convex {
                            Ok(polygon)
                        } else {
                            Err(PolygonError3::NotConvex)
                        }
                    }
                },
                None => Err(PolygonError3::Zero)
            }
        }
    }
}

impl core::ops::Add<Vector3> for Polygon3 {
    type Output = Polygon3;

    fn add(mut self, delta: Vector3) -> Self {
        for v in self.vertices.iter_mut() {
            *v = v.clone() + delta;
        }
        self
    }
}

impl Intersect<Halfspace3> for Edge3
{
    type Output = Option<Vertex3>;

    fn intersect(&self, knife: Halfspace3) -> Option<Vertex3> {
        Edge::intersect::<_, LineSegment3>(&self, knife)
    }
}


#[cfg(test)]
mod test {
    use crate::plane::{p2, v2};
    use crate::plane::shapes::rectangle;
    use crate::space::p3;
    use crate::util::knife::Knife;
    use super::*;

    #[test]
    fn test_validation() {
        let linear = Polygon3::new(
            vec![
                p3(0.0, 0.0, 0.0),
                p3(1.0, 0.0, 0.0),
                p3(2.0, 0.0, 0.0)
            ]
        );
        assert_eq!(linear.err(), Some(PolygonError3::Zero));

        let concave = Polygon3::new(vec![
            p3(0.0, 0.0, 2.0),
            p3(1.0, 0.5, 2.0),
            p3(2.0, 0.0, 2.0),
            p3(1.0, 1.0, 2.0)
        ]);
        assert_eq!(concave.err(), Some(PolygonError3::NotConvex));

        let nonplanar = Polygon3::new(
            vec![
                p3(0.0, 0.0, 0.0),
                p3(1.0, 0.0, 0.0),
                p3(0.0, 1.0, 0.0),
                p3(0.0, 0.0, 1.0)
            ]
        );
        assert_eq!(nonplanar.err(), Some(PolygonError3::NotPlanar));
    }

    #[test]
    fn test_cut() {
        let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = Basis3::unit();

        let poly = Polygon3::project(&r, &b);
        let hs = Halfspace3 {
            origin: p3(0.0, 0.0, 0.0),
            normal: v3(1.0, -1.0, 0.0)
        };

        let parts = hs.cut(poly);
        assert!(parts.inside.is_some());
        assert!(parts.outside.is_some());
        assert!(parts.tangent.len() > 0);
    }
}