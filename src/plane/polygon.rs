use either::{Left, Right};
use std::collections::HashMap;
use std::cmp::Ordering;
use std::iter;
use cgmath::InnerSpace;

use crate::plane::{Line2, Point2, Vector2};

#[derive(Clone, Debug)]
pub struct LineIndex {
    pub a: usize,
    pub b: usize,
    pub normal: Vector2
}

struct IndexedSegment<'a> {
    ix: LineIndex,
    backing: &'a Vec<Point2>
}

#[derive(Clone, Debug)]
pub struct Polygon2 {
    pub points: Vec<Point2>,
    pub lines: Vec<LineIndex>
}

impl Polygon2 {
    fn lines(&self) -> impl Iterator<Item=(LineIndex, Line2)> + '_ {
        self.lines.iter().map(move |li|
            (li.clone(), Line2::from_points(self.points[li.a], self.points[li.b]))
        )
    }

    /// Compares the given point to this polygon:
    ///
    /// - if `p` is in `poly`, then `p < poly`
    /// - if `p` is tangent to some segment in `poly`, then `p == poly`
    /// - if `p` is outside of `poly`, then `p > poly`
    ///
    /// Examples:
    ///
    /// ```
    /// # use std::cmp::Ordering;
    /// # use fajita::plane::{p2, v2};
    /// # use fajita::plane::shapes::rectangle;
    /// let r = rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
    /// assert_eq!(r.cmp_point(p2(0.5, 0.5)), Ordering::Less);
    /// assert_eq!(r.cmp_point(p2(0.5, 0.0)), Ordering::Equal);
    /// assert_eq!(r.cmp_point(p2(0.5, 2.0)), Ordering::Greater);
    /// ```
    pub fn cmp_point(&self, point: Point2) -> Ordering {
        let mut it = self.lines.iter().filter_map(|li| {
            let dot = (point - self.points[li.a]).dot(li.normal);
            if dot >= 0.0 { Some(dot) } else { None }
        });


        let positive = it.map(|v| if v > 0.0 { 1 } else { 0 }).max();

        match positive {
            Some(v) => {
                if v > 0 { Ordering::Greater } else { Ordering::Equal }
            }
            None => Ordering::Less
        }
    }

    fn divide(&self, division: Line2, normal: Vector2) -> Option<[Polygon2;2]> {
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
                    Polygon2 { points: combined.clone(), lines: inside },
                    Polygon2 { points: combined, lines: outside }
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
    use crate::plane::shapes::rectangle;
    use super::*;

    fn square() -> Polygon2 {
        rectangle(p2(0.0, 0.0), v2(1.0, 1.0))
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