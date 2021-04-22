use super::Vector3;
use super::polygon::Polygon3;
use super::polyhedron::Polyhedron3;
use crate::util::container::{Container, Orientation};
use crate::util::segment::Segment;

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
            let a = e.start();
            let b = e.end();
            let vertices = vec![
                b.clone(),
                a.clone(),
                a + direction,
                b + direction,
            ];

            Polygon3 { vertices }.face()
        }));

        faces.push(base);
        faces.push(top);

        Some(Polyhedron3 { faces })
    }
}