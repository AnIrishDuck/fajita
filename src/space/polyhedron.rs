use super::{Point3, Vector3};
use super::plane::Halfspace3;
use super::polygon::Polygon3;
use crate::plane::polygon::Polygon;
use crate::util::container::{Container, Orientation};
use crate::util::segment::Segment;

use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Face3
{
    pub normal: Vector3,
    pub polygon: Polygon<Point3>
}

impl Face3 {
    pub fn from_wound_polygon(polygon: Polygon3) -> Option<Self> {
        Halfspace3::find_from_points(polygon.points()).map(|hs| {
            Face3 {
                normal: hs.normal,
                polygon
            }
        })
    }

    pub fn halfspace(&self) -> Halfspace3 {
        Halfspace3 { normal: self.normal, origin: self.polygon.vertices[0].point }
    }

    pub fn invert(&mut self) {
        self.polygon.vertices.reverse();
        self.normal = -self.normal;
    }
}

#[derive(Clone, Debug)]
pub struct Polyhedron3
{
    pub faces: Vec<Face3>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolyhedronError {
    Zero,
    NotConvex,
    BadPolygon,
    NotClosed
}

impl Polyhedron3
{
    pub fn halfspaces(&self) -> impl Iterator<Item=Halfspace3> + '_ {
        self.faces.iter().map(move |f| {
            f.halfspace()
        })
    }

    pub fn validate(&self) -> Option<PolyhedronError> {
        Polyhedron3::new(self.faces.clone()).err()
    }

    pub fn new<'a, I, N>(into: N) -> Result<Polyhedron3, PolyhedronError>
    where
    N: IntoIterator<Item = Face3, IntoIter=I>,
    I: DoubleEndedIterator<Item = Face3> + ExactSizeIterator + Clone
    {
        let faces = into.into_iter();
        if faces.len() < 4 {
            Err(PolyhedronError::Zero)
        } else {
            let faces: Vec<_> = faces.collect();
            let mut counts: HashMap<((u64, u64, u64), (u64, u64, u64)), u8> = HashMap::new();

            for face in faces.iter() {
                for e in face.polygon.edges() {
                    let ah = exact_hash(&e.start().point);
                    let bh = exact_hash(&e.end().point);

                    let abv = counts.entry((ah, bh)).or_insert(0);
                    *abv += 1;
                    if *abv > 2 {
                        return Err(PolyhedronError::NotClosed)
                    }

                    let bav = counts.entry((bh, ah)).or_insert(0);
                    *bav += 1;
                    if *bav > 2 {
                        return Err(PolyhedronError::NotClosed)
                    }
                }
            }

            for v in counts.values() {
                if *v != 2 {
                    return Err(PolyhedronError::NotClosed)
                }
            }

            let result = Polyhedron3 { faces };
            for face in result.faces.iter() {
                if face.polygon.validate().is_some() {
                    return Err(PolyhedronError::BadPolygon)
                }

                let hs = face.halfspace();
                for other in result.faces.iter() {
                    let all_in = other.polygon.vertices.iter().all(|v| {
                        hs.contains(&v.point) != Orientation::Out
                    });

                    if !all_in {
                        return Err(PolyhedronError::NotConvex)
                    }
                }
            }

            Ok(result)
        }
    }
}

// Note that this has all the obvious issues with floating point comparisons
fn exact_hash(p: &Point3) -> (u64, u64, u64) {
    (p.x.to_bits(), p.y.to_bits(), p.z.to_bits())
}

#[cfg(test)]
mod test {
    use crate::plane::p2;
    use crate::space::v3;
    use crate::plane::polygon::Polygon2;
    use crate::space::polygon::{Polygon3, Basis3};
    use crate::space::solids;
    use super::*;

    #[test]
    fn test_validation() {
        let tri = Polygon2::new(vec![p2(0.0, 0.0), p2(2.0, 0.0), p2(1.0, 2.0)]).unwrap();
        let base = Polygon3::project(&tri, &Basis3::unit());
        let prism = solids::extrude(base, v3(0.0, 0.0, 1.0)).unwrap();

        assert_eq!(prism.validate(), None);

        let mut unclosed = prism.clone();
        unclosed.faces = unclosed.faces[(1..)].to_vec();
        assert_eq!(unclosed.validate(), Some(PolyhedronError::NotClosed));
    }
}
