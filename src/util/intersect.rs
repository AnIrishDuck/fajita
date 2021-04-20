/// A generic trait for two objects that have some kind of intersection
pub trait Intersect<K> {
    type Output;

    fn intersect(&self, knife: K) -> Self::Output;
}