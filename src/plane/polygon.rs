use either::{Left, Right};
use std::collections::HashMap;
use std::iter;
use cgmath::InnerSpace;

use crate::plane::{Line2, Point2, Vector2};

#[derive(Clone, Debug)]
struct LineIndex {
    a: usize,
    b: usize,
    normal: Vector2
}

struct IndexedSegment<'a> {
    ix: LineIndex,
    backing: &'a Vec<Point2>
}

#[derive(Clone, Debug)]
struct Polygon {
    points: Vec<Point2>,
    lines: Vec<LineIndex>
}

impl Polygon {
    fn lines(&self) -> impl Iterator<Item=(LineIndex, Line2)> + '_ {
        self.lines.iter().map(move |li|
            (li.clone(), Line2::from_points(self.points[li.a], self.points[li.b]))
        )
    }

    fn divide(&self, division: Line2, normal: Vector2) -> Option<[Polygon;2]> {
        let mut intersections = vec![];
        let updated_lines: Vec<_> = self.lines().flat_map(|(indices, poly_line)| {
            let intersect = poly_line.intersect(&division);
            let on_line = intersect.filter(|&(u_poly_line, _, _)| u_poly_line >= 0.0 && u_poly_line <= 1.0);
            match on_line {
                Some((_, _, pi)) => {
                    let new_ix = self.lines.len() + intersections.len();
                    intersections.push(pi);
                    let normal = indices.normal;
                    Left(
                        iter::once(LineIndex { a: indices.a, b: new_ix, normal })
                            .chain(iter::once(LineIndex { a: new_ix, b: indices.b, normal }))
                    )
                },
                None => Right(iter::once(indices))
            }
        }).collect();

        if intersections.len() < 2 {
            None
        } else {
            let combined: Vec<_> = self.points.iter().chain(intersections.iter()).map(|p| p.clone()).collect();

            let (mut inside, mut outside): (Vec<_>, Vec<_>) = updated_lines.into_iter().partition(|li| {
                let a = combined[li.a];
                let b = combined[li.b];
                (division.p - a).dot(normal) > 0.0 || (division.p - b).dot(normal) > 0.0
            });

            let a = self.points.len();
            let b = a + 1;
            inside.push(LineIndex { a, b, normal });
            outside.push(LineIndex { a: b, b: a, normal: -normal });

            Some(
                [
                    Polygon { points: combined.clone(), lines: inside },
                    Polygon { points: combined, lines: outside }
                ]
            )
        }
    }

    fn ring(&self) -> Vec<Point2> {
        let m: HashMap<_, _> = self.lines.iter().map(|l| (l.a, l)).collect();
        let mut current: Option<usize> = Some(self.lines[0].a);
        self.lines.iter().flat_map(|_| {
            match current {
                Some(prior) => {
                    current = m.get(&prior).map(|x| x.b);
                    Some(self.points[prior])
                },
                None => None
            }
        }).collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::plane::{p2, v2};
    use super::*;

    fn square() -> Polygon {
        Polygon {
            points: vec![p2(0.0, 0.0), p2(1.0, 0.0), p2(1.0, 1.0), p2(0.0, 1.0)],
            lines: vec![
                LineIndex { a: 0, b: 1, normal: v2( 0.0, -1.0) },
                LineIndex { a: 1, b: 2, normal: v2( 1.0,  0.0) },
                LineIndex { a: 2, b: 3, normal: v2( 0.0,  1.0) },
                LineIndex { a: 3, b: 0, normal: v2(-1.0,  0.0) },
            ]
        }
    }

    #[test]
    fn test_simple_division() {
        let p = square();
        let parts = p.divide(Line2::new(p2(-1.0, 0.5), v2(1.0, 0.0)), v2(0.0, 1.0));
        let parts = parts.unwrap();
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0].ring().len(), 4);
        assert_eq!(parts[1].ring().len(), 4);
    }

    #[test]
    fn test_no_division() {
        let p = square();
        let parts = p.divide(Line2::new(p2(-1.0, 1.5), v2(1.0, 0.0)), v2(0.0, 1.0));
        assert_eq!(parts.is_none(), true);
    }
}