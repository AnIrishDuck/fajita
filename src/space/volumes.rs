//! Constructors and utilities for building three-dimensional volumes in space.
use super::Vector3;
use super::polygon::Polygon3;
use super::polyhedron::Polyhedron3;
use crate::util::container::{Container, Orientation};
use crate::util::segment::Segment;

/// Extrudes a `base` polygon in the given `direction`, using quads to stitch
/// together the top and bottom faces.
///
/// If the `direction` is on the same plane as `base`, `None` will be returned.
pub fn extrude(base: Polygon3, direction: Vector3) -> Option<Polyhedron3> {
    let mut base = base.face();

    let orientation = base.halfspace().contains(&direction);
    if orientation == Orientation::On {
        None
    } else {
        if orientation == Orientation::Out {
            base.invert();
        }

        let mut top = base.clone();
        top.invert();
        top.polygon = top.polygon + direction;

        let mut faces = vec![];
        faces.extend(base.polygon.edges().map(|e| {
            let mut a = e.start();
            let mut b = e.end();
            let last_leg = b.clone() + direction;
            a.reverse = true;
            b.reverse = true;
            let vertices = vec![
                b,
                a.clone(),
                a + direction,
                last_leg,
            ];

            Polygon3 { vertices }.face()
        }));

        faces.push(base);
        faces.push(top);

        Some(Polyhedron3 { faces })
    }
}