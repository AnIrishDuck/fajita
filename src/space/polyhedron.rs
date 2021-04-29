use cgmath::EuclideanSpace;
use super::{Point3, Vector3};
use super::plane::Halfspace3;
use super::polygon::{Vertex3, Polygon3};
use crate::plane::polygon::Polygon;
use crate::util::container::{Container, Orientation};
use crate::util::knife::{Knife, Parts};
use crate::util::segment::Segment;
use crate::util::winding::Winding;

use std::collections::{HashMap, HashSet};

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

impl Knife<Face3> for Halfspace3
{
    type Output = Option<Face3>;
    type Tangent = Vec<Vertex3>;

    fn cut(&self, target: Face3) -> Parts<Self::Output, Self::Tangent> {
        let normal = target.normal;
        let parts = self.cut(target.polygon);
        Parts {
            inside: parts.inside.map(|polygon| Face3 { polygon, normal }),
            outside: parts.outside.map(|polygon| Face3 { polygon, normal }),
            tangent: parts.tangent
        }
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

    pub fn vertices(&self) -> impl Iterator<Item=Vertex3> + '_ {
        let mut prior = HashSet::new();

        self.faces.iter().flat_map(|f| {
            f.polygon.vertices.iter()
        }).cloned().filter(move |v| {
            let k = exact_hash(&v.point);
            prior.insert(k)
        })
    }

    pub fn center(&self) -> Point3 {
        let mut count = 0;
        let sum: Vector3 = self.vertices()
            .map(|v| { count += 1; v.point.to_vec() })
            .sum();
        Point3::from_vec(sum / count as f64)
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

impl Container<Point3> for Polyhedron3
{
    fn contains(&self, point: &Point3) -> Orientation {
        Self::intersect(self.halfspaces(), point)
    }
}

#[derive(Clone)]
struct PartialPolygon3 {
    starts: HashMap<(u64, u64, u64), Vec<Vertex3>>,
}

impl PartialPolygon3 {
    fn extend(&mut self, line: Vec<Vertex3>) {
        if line.len() > 1 {
            let start = line[0].point;
            if !self.starts.contains_key(&exact_hash(&start)) {
                self.starts.insert(exact_hash(&start), line);
            }
        }
    }

    fn ring(mut self) -> Option<Vec<Vertex3>> {
        let mut current = self.starts.values().next().cloned();
        let mut result = vec![];
        while !self.starts.is_empty() {
            match current {
                Some(vertices) => {
                    current = vertices.last().and_then(|v|
                        self.starts.remove(&exact_hash(&v.point))
                    );
                    let no_end = vertices.len() - 1;
                    result.extend(vertices.into_iter().take(no_end));
                },
                None => {
                    return None
                }
            }
        }

        if self.starts.len() == 0 {
            Some(result)
        } else {
            None
        }
    }
}

impl Knife<Polyhedron3> for Halfspace3
{
    type Output = Option<Polyhedron3>;
    type Tangent = Vec<Vertex3>;

    fn cut(&self, target: Polyhedron3) -> Parts<Self::Output, Self::Tangent> {
        let mut inside = Polyhedron3 { faces: vec![] };
        let mut outside = Polyhedron3 { faces: vec![] };
        let mut tangent = vec![];
        let mut partial = PartialPolygon3 { starts: HashMap::new() };

        let mut has_inside = false;
        let mut has_outside = false;
        for face in target.faces.into_iter() {
            let hs = face.halfspace();
            let parts = self.cut(face);

            has_inside = has_inside || parts.inside.is_some();
            inside.faces.extend(parts.inside);
            has_outside = has_outside || parts.outside.is_some();
            outside.faces.extend(parts.outside);

            let mut ts = parts.tangent;
            if let (Some(a), Some(b)) = (ts.get(0), ts.get(1)) {
                let a = a.point;
                let b = b.point;
                let wind = hs.winding_from_points(a, b, a + self.normal);
                if wind == Some(Winding::Clockwise) {
                    ts.reverse();
                }
            }

            partial.extend(ts.clone());
            tangent.extend(ts);
        }

        if let Some(vertices) = partial.ring() {
            let mut inner = (Polygon3 { vertices }).face();
            if inner.halfspace().contains(&self.normal) == Orientation::In {
                inner.invert()
            }
            inside.faces.push(inner.clone());
            let mut outer = inner;
            outer.invert();
            outside.faces.push(outer);
        }

        Parts {
           inside: if has_inside { Some(inside) } else { None },
           outside: if has_outside { Some(outside) } else { None },
           tangent
        }
    }
}

// Note that this has all the obvious issues with floating point comparisons
fn exact_hash(p: &Point3) -> (u64, u64, u64) {
    (p.x.to_bits(), p.y.to_bits(), p.z.to_bits())
}

#[cfg(test)]
mod test {
    use cgmath::InnerSpace;
    use crate::plane::{p2, v2};
    use crate::plane::shapes;
    use crate::plane::polygon::Polygon2;
    use crate::space::{p3, v3};
    use crate::space::polygon::{Polygon3, Basis3};
    use crate::space::solids;
    use super::*;

    fn assert_hs_cut_ok(original: Polyhedron3, hs: Halfspace3) -> Parts<Option<Polyhedron3>, Vec<Vertex3>> {
        let parts = hs.cut(original.clone());

        for polyhedron in parts.inside.iter().chain(parts.outside.iter()) {
            let polyhedron = polyhedron.clone();
            assert_eq!(polyhedron.validate(), None);

            assert!(
                original.contains(&polyhedron.center()) == Orientation::In,
                "center of {:?} not in original polyhedron", polyhedron
            );
            assert!(
                polyhedron.contains(&polyhedron.center()) == Orientation::In,
                "center {:?} not in {:?}", polyhedron.center(), polyhedron
            );
            for v in polyhedron.vertices() {
                let p = v.point;
                assert!(
                    original.contains(&p) == Orientation::On,
                    "({:?} not in/on {:?})", p, original
                )
            }
        }

        parts
    }

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

    fn verify_multidirectional_cut(p: &Polyhedron3) {
        for v in [v3(0.0, 0.0, 1.0), v3(0.0, 1.0, 1.0), v3(1.0, 1.0, 1.0)].iter() {
            for dir in [1.0, -1.0].iter() {
                let normal = (v * (*dir)).normalize();
                let hs = Halfspace3 { origin: p3(0.5, 0.5, 0.5), normal };

                let parts = assert_hs_cut_ok(p.clone(), hs);
                assert!(parts.inside.is_some());
                assert!(parts.outside.is_some());
            }
        }
    }

    #[test]
    fn test_cube() {
        let square = shapes::rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let base = Polygon3::project(&square, &Basis3::unit());
        let cube = solids::extrude(base, v3(0.0, 0.0, 1.0)).unwrap();
        verify_multidirectional_cut(&cube);
    }

    #[test]
    fn test_extrusion() {
        let square = shapes::rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let base = Polygon3::project(&square, &Basis3::unit());
        let p = solids::extrude(base, v3(0.1, 0.2, 1.0)).unwrap();
        verify_multidirectional_cut(&p);
    }
}
