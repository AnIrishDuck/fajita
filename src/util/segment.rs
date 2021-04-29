use core::ops::Sub;
use std::iter;

use crate::util::container::{Container, Orientation};
use crate::util::intersect::Intersect;
use crate::util::knife::{Parts, Knife};
use crate::util::vertex::Vertex;

pub trait Line<P, V> {
    fn origin(&self) -> P;
    fn direction(&self) -> V;
}

#[derive(Clone, Debug, PartialEq)]
pub enum Span<P, S> {
    Point(P),
    Segment(S)
}

pub trait Segment {
    type Point;

    fn from_endpoints(start: Self::Point, end: Self::Point) -> Self;
    fn start(&self) -> Self::Point;
    fn end(&self) -> Self::Point;

    fn vector<V>(&self) -> V
    where Self::Point: Sub<Output=V>
    {
        self.end() - self.start()
    }
}

#[derive(Clone, Debug)]
pub struct Edge<P: Clone>
{
    a: Vertex<P>,
    b: Vertex<P>
}

impl<P: Clone> Edge<P>
{
    pub fn vertices(&self) -> impl Iterator<Item=Vertex<P>> {
        iter::once(self.a.clone()).chain(iter::once(self.b.clone()))
    }

    pub fn intersect<K, S>(&self, knife: K) -> Option<Vertex<P>>
    where
        P: PartialEq,
        S: Segment<Point=P> + Intersect<K, Output=Option<P>>
    {
        let a = self.a.point.clone();
        let b = self.b.point.clone();
        let (a, b) = if self.a.reverse {
            (b, a)
        } else {
            (a, b)
        };
        let intersect = S::from_endpoints(a, b).intersect(knife);
        intersect.map(|p| {
            if p == self.a.point {
                self.a.clone()
            } else if p == self.b.point {
                self.b.clone()
            } else {
                Vertex {
                    point: p,
                    reverse: self.a.reverse,
                    index: None,
                }
            }
        })
    }
}

impl<P: Clone> Segment for Edge<P> {
    type Point = Vertex<P>;

    fn from_endpoints(a: Vertex<P>, b: Vertex<P>) -> Self {
        Edge { a, b }
    }

    fn start(&self) -> Vertex<P> { self.a.clone() }
    fn end(&self) -> Vertex<P> { self.b.clone() }
}

impl<S, P, V> Line<P, V> for S
where
S: Segment<Point=P>,
P: Sub<Output=V>
{
    fn origin(&self) -> P { self.start() }
    fn direction(&self) -> V { self.vector() }
}

impl<K, S, P> Knife<S> for K
where
    S: Segment<Point = P> + Intersect<K, Output = Option<P>> + Clone,
    K: Container<P> + Clone,
    P: Clone
{
    type Output = Option<S>;
    type Tangent = Option<Span<P, S>>;

    fn cut(&self, target: S) -> Parts<Self::Output, Self::Tangent>
    {
        let knife = self;
        let a = target.start();
        let b = target.end();
        let oa = knife.contains(&a);
        let ob = knife.contains(&b);

        if oa == ob {
            if oa == Orientation::On {
                Parts { tangent: Some(Span::Segment(target.clone())), ..Default::default()}
            } else {
                Parts::orient(oa, target.clone(), None)
            }
        } else if oa == Orientation::On {
            Parts::orient(ob, target.clone(), Some(Span::Point(a)))
        } else if ob == Orientation::On {
            Parts::orient(oa, target.clone(), Some(Span::Point(b)))
        } else {
            let intersect = target.intersect(knife.clone());

            match intersect {
                Some(p) => {
                    let sa = S::from_endpoints(a, p.clone());
                    let sb = S::from_endpoints(p.clone(), b);
                    let (inner, outer) = if oa == Orientation::In {
                        (sa, sb)
                    } else {
                        (sb, sa)
                    };
                    Parts {
                        inside: Some(inner),
                        tangent: Some(Span::Point(p)),
                        outside: Some(outer),
                    }
                },
                None => panic!("segment crosses halfspace but no intersect found")
            }
        }
    }
}
