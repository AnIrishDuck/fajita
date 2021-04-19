use crate::util::container::{Container, Orientation};

#[derive(Clone, Debug)]
pub struct Vertex<P: Clone>
{
    pub index: Option<usize>,
    pub point: P
}


impl<P, H> Container<Vertex<P>> for H
where
H: Container<P>,
P: Clone
{
    fn contains(&self, v: &Vertex<P>) -> Orientation {
        self.contains(&v.point)
    }
}