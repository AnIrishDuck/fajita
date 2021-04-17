/// A generic trait for two objects that have some kind of intersection
pub trait Intersect<K, I> {
    fn intersect(&self, knife: K) -> I;
}