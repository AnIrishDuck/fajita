use crate::space::Point3;
use crate::space::plane::Halfspace3;
use crate::plane::polygon::Polygon;
use crate::util::container::{Container, Orientation};
use crate::util::segment::Segment;
use crate::util::vertex::Vertex;

pub type Vertex3 = Vertex<Point3>;
pub type Polygon3 = Polygon<Point3>;

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


#[cfg(test)]
mod test {
    use crate::space::p3;
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
}