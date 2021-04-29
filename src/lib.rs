//! A library for performing computational solid geometry on two-dimensional
//! shapes and three-dimensional volumes:
//!
//! ```
//! use fajita::plane::{p2, v2};
//! use fajita::util::intersect::Intersect;
//! use fajita::shapes;
//!
//! let a = shapes::rectangle(p2(0.0, 0.0), v2(1.0, 1.0));
//! let b = shapes::rectangle(p2(0.5, 0.5), v2(1.0, 1.0));
//!
//! a.clone().union(b.clone());
//! a.clone().intersect(b.clone());
//! a.clone().remove(b.clone());
//! ```
//!
//! Common [`shapes`] and [`volumes`] can be constructed directly from the
//! corresponding modules.
extern crate cgmath;
extern crate either;
pub mod plane;
pub mod space;
pub mod util;

pub use plane::shapes;
pub use space::volumes;