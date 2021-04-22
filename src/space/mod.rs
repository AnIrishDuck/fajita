use cgmath;
pub mod plane;
pub mod polygon;
pub mod polyhedron;
pub mod solids;

pub type Point3 = cgmath::Point3<f64>;
pub type Vector3 = cgmath::Vector3<f64>;

pub fn p3<T>(x: T, y: T, z: T) -> cgmath::Point3<T> {
    cgmath::Point3::new(x, y, z)
}
pub use cgmath::vec3 as v3;
