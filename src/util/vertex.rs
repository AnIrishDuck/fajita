use cgmath::EuclideanSpace;
use core::ops::Add;
use crate::util::container::{Container, Orientation};

#[derive(Clone, Debug)]
pub struct Vertex<P: Clone>
{
    pub index: Option<usize>,
    pub reverse: bool,
    pub point: P
}

impl<P: Clone> Vertex<P> {
    pub fn unindexed(point: P, reverse: bool) -> Self {
        Vertex { point, reverse, index: None }
    }

    pub fn reversed(&self) -> Self {
        Vertex {
            point: self.point.clone(),
            reverse: !self.reverse,
            index: self.index
        }
    }
}

impl<P, V> Add<V> for Vertex<P>
where P: Clone + EuclideanSpace<Diff=V>
{
    type Output = Vertex<P>;

    fn add(self, o: V) -> Self {
        Vertex::unindexed(self.point + o, self.reverse)
    }
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