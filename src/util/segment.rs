use core::ops::Sub;

use crate::util::container::{Container, Orientation};
use crate::util::intersect::Intersect;
use crate::util::knife::{Parts, Knife};

pub trait Line<P, V> {
    fn origin(&self) -> P;
    fn direction(&self) -> V;
}

#[derive(Clone, Debug, PartialEq)]
pub enum Span<P, S> {
    Point(P),
    Segment(S)
}

pub trait Segment<P> {
    fn from_endpoints(start: P, end: P) -> Self;
    fn start(&self) -> P;
    fn end(&self) -> P;

    fn vector<V>(&self) -> V
    where P: Sub<Output=V>
    {
        self.end() - self.start()
    }
}

impl<S, P, V> Line<P, V> for S
where
S: Segment<P>,
P: Sub<Output=V>
{
    fn origin(&self) -> P { self.start() }
    fn direction(&self) -> V { self.vector() }
}

impl<K, S, P> Knife<S, Option<S>, Option<Span<P, S>>> for K
where
S: Segment<P> + Intersect<K, Option<P>> + Clone,
K: Container<P> + Clone,
P: Clone
{
    fn cut(&self, target: S) -> Parts<Option<S>, Option<Span<P, S>>>
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
