use crate::plane::{LineSegment2, Point2, Polygon2, Vector2};
use crate::plane::polygon::LineIndex;
use either::{Left, Right};
use std::iter;
use std::collections::HashMap;
use std::cmp::Ordering;
use cgmath::InnerSpace;

#[derive(Clone, Debug)]
pub struct Shape2<'a> {
    points: Vec<Point2>,
    polygons: Vec<Polygon2<'a>>
}

impl Shape2<'_> {
    pub fn unchecked_new(points: Vec<Point2>, polygons: Vec<Polygon2>) -> Shape2 {
        Shape2 { points, polygons }
    }

    fn cmp_poly(&self, other: &Polygon2) -> Option<Ordering> {
        if self.polygons.len() == 1 {
            self.polygons[0].partial_cmp(&other)
        } else {
            if self.polygons.iter().any(|p| p >= other) {
                Some(Ordering::Greater)
            } else if self.polygons.iter().all(|p| p < other) {
                Some(Ordering::Less)
            } else {
                None
            }
        }
    }

    /*
    fn unify(&mut self, mut other: Shape2) -> Shape2 {
        let mut combined = self.polygons[0].clone();
        other.polygons = other.polygons.into_iter().map(|p| {
            combined.unify(p)
        }).collect();

        for polygon in self.polygons.iter_mut() {
            polygon.points = combined.points.clone();
        }

        other
    }
    */

    fn union(mut self, other: Shape2) -> Shape2 {
        let fragments = self.polygons;
        self.polygons = vec![];
        let fragments = self.fragment(fragments, &other);

        /*
        for polygon in fragments.iter() {
            println!("ring: {:?}", polygon.ring());
        }
        */

        let filtered: Vec<_> = fragments.into_iter()
            .filter(|polygon| other.cmp_poly(&polygon) != Some(Ordering::Greater))
            .collect();

        let polygons = filtered; // .into_iter().chain(other.polygons).collect();

        Shape2 {
            points: self.points,
            polygons
        }
    }

    fn lines(&self) -> impl Iterator<Item=&LineIndex> + '_ {
        self.polygons.iter().flat_map(|p| {
            p.lines.iter()
        })
    }

    fn fragment(&mut self, polygons: Vec<Polygon2>, other: &Shape2) -> Vec<Polygon2> {
        polygons.into_iter().flat_map(|p| {
            other.polygons.iter().fold(vec![p], |frags, op| {
                frags.into_iter().flat_map(|f| self.fragment_polygon(f, op)).collect()
            })
        }).collect()
    }

    fn fragment_lines(&mut self, polygon: Polygon2, lines: Vec<(LineIndex, Line2)>) -> Vec<Polygon2> {
        let fragments = vec![polygon];

        lines.iter().fold(fragments, |acc, (li, l)| {
            acc.into_iter().flat_map(|frag| {
                let (guarantee, possible) = self.divide(frag, l.clone(), li.normal);
                iter::once(Some(guarantee)).chain(iter::once(possible)).flatten()
            }).collect()
        })
    }

    pub fn fragment_polygon(&mut self, polygon: Polygon2, other: &Polygon2) -> Vec<Polygon2> {
        let other_lines: Vec<_> = Polygon2 { points: &self.points, polygon: other }.lines().collect();
        self.fragment_lines(polygon, other_lines)
    }

    fn divide(&mut self, polygon: Polygon2, division: Line2, normal: Vector2) -> (Polygon2, Option<Polygon2>) {
        let mut intersections = vec![];
        let bound = Polygon2 { points: &self.points, polygon: &polygon };
        let updated_lines: Vec<_> = bound.lines().flat_map(|(indices, poly_line)| {
            let intersect = poly_line.intersect(&division);
            let on_line = intersect.filter(|&(u_poly_line, _, _)| u_poly_line >= 0.0 && u_poly_line <= 1.0);
            match on_line {
                Some((_, _, pi)) => {
                    let new_ix = self.points.len() + intersections.len();
                    intersections.push(pi);
                    let normal = indices.normal;
                    Left(
                        iter::once(LineIndex { a: indices.a, b: new_ix, normal, internal: false })
                            .chain(iter::once(LineIndex { a: new_ix, b: indices.b, normal, internal: false }))
                    )
                },
                None => Right(iter::once(indices))
            }
        }).collect();

        if intersections.len() < 2 {
            (polygon, None)
        } else {
            self.points.extend(intersections.into_iter());

            let (mut inside, mut outside): (Vec<_>, Vec<_>) = updated_lines.into_iter().partition(|li| {
                let a = self.points[li.a];
                let b = self.points[li.b];
                (division.p - a).dot(normal) > 0.0 || (division.p - b).dot(normal) > 0.0
            });

            let a = self.points.len();
            let b = a + 1;
            inside.push(LineIndex { a, b, normal, internal: true });
            outside.push(LineIndex { a: b, b: a, normal: -normal, internal: true });

            (
                Polygon2 { lines: inside },
                Some(Polygon2 { lines: outside })
            )
        }
    }
}

mod tests {
    use super::*;
    use crate::plane::{p2, v2};
    use crate::plane::shapes::rectangle;
    use std::cmp::Ordering;

    #[test]
    fn test_simple_union() {
        let a = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
        let b = rectangle(p2(0.5, 0.5), v2(1.0, 1.0));

        let combined = a.clone().union(b.clone());
        println!("fin");
        for polygon in combined.bound_polygons() {
            println!("ring: {:?}", polygon.ring());
        }
        // println!("ring: {:?}", combined.ring());
    }
}