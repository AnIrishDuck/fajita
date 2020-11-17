use regex::Regex;
use std::collections::BTreeMap;
use std::cmp::Ordering;
use std::fmt;

#[derive(Debug, Clone, Eq, PartialEq)]
struct GrevlexMonomial {
    index: u32
}

impl Ord for GrevlexMonomial {
    fn cmp(&self, other: &Self) -> Ordering {
        self.index.cmp(&other.index).reverse()
    }
}

impl PartialOrd for GrevlexMonomial {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug)]
struct Term<I: Ord> {
    parts: BTreeMap<I, u32>
}

impl<I: Ord + Clone> Term<I> {
    fn degree(&self) -> u32 {
        self.parts.values().sum()
    }

    fn full_div(&self, other: &Term<I>) -> Option<Term<I>> {
        if PairZip::new(self, other).any(|(_, p1, p2)| p1 < p2) {
            None
        } else {
            let parts = PairZip::new(self, other).map(|(i, p1, p2)| {
                ((*i).clone(), p1.unwrap_or(0) - p2.unwrap_or(0))
            }).filter(|(_, p)| *p != 0).collect::<BTreeMap<I, u32>>();

            Some(Term { parts })
        }
    }
}

impl<I: Ord + Clone> std::ops::Mul<&Term<I>> for Term<I> {
    type Output = Self;

    fn mul(self, other: &Self) -> Self {
        let parts = PairZip::new(&self, &other).map(|(i, p1, p2)| {
            ((*i).clone(), p1.unwrap_or(0) + p2.unwrap_or(0))
        }).collect::<BTreeMap<I, u32>>();

        Term { parts }
    }
}

struct PairZip<'a, I: Ord> {
    i1: std::collections::btree_map::Iter<'a, I, u32>,
    i2: std::collections::btree_map::Iter<'a, I, u32>,
    i1c: Option<(&'a I, &'a u32)>,
    i2c: Option<(&'a I, &'a u32)>
}

impl<'a, I: Ord> PairZip<'a, I> {
    fn new(t1: &'a Term<I>, t2: &'a Term<I>) -> Self {
        let mut i1 = t1.parts.iter();
        let mut i2 = t2.parts.iter();
        let i1c = i1.next();
        let i2c = i2.next();
        PairZip { i1, i2, i1c, i2c }
    }

    fn pull1(&mut self) -> Option<(&'a I, Option<u32>, Option<u32>)> {
        self.i1c.map(|(i, p)| {
            self.i1c = self.i1.next();
            (i, Some(*p), None)
        })
    }

    fn pull2(&mut self) -> Option<(&'a I, Option<u32>, Option<u32>)> {
        self.i2c.map(|(i, p)| {
            self.i2c = self.i2.next();
            (i, None, Some(*p))
        })
    }
}

impl<'a, I: Ord> Iterator for PairZip<'a, I> {
    type Item = (&'a I, Option<u32>, Option<u32>);

    fn next(&mut self) -> Option<Self::Item> {
        match (self.i1c, self.i2c) {
            (Some((i1, p1)), Some((i2, p2))) => {
                if i1 < i2 {
                    self.pull1()
                } else if i1 == i2 {
                    self.i1c = self.i1.next();
                    self.i2c = self.i2.next();
                    Some((i1, Some(*p1), Some(*p2)))
                } else {
                    self.pull2()
                }
            },
            (Some(_), None) => self.pull1(),
            (None, Some(_)) => self.pull2(),
            (None, None) => None,
        }
    }
}

impl Ord for Term<GrevlexMonomial> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.degree().cmp(&other.degree())
            .then_with(|| {
                let mut i1 = self.parts.iter();
                let mut i2 = other.parts.iter();
                loop {
                    match (i1.next(), i2.next()) {
                        (Some((m1, p1)), Some((m2, p2))) => {
                            let o = m1.cmp(&m2).then(p2.cmp(p1));
                            if o != Ordering::Equal { return o }
                        },
                        (None, Some(_)) => return Ordering::Less,
                        (Some(_), None) => return Ordering::Greater,
                        (None, None) => return Ordering::Equal
                    }
                }
            })
    }
}

impl PartialOrd for Term<GrevlexMonomial> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Term<GrevlexMonomial> {
    fn eq(&self, other: &Self) -> bool {
        self.parts.len() == other.parts.len() && {
            self.parts.iter().zip(other.parts.iter()).all(|((k,v), (ok, ov))| {
                k == ok && v == ov
            })
        }
    }
}

impl Eq for Term<GrevlexMonomial> {}

struct Bound<'a, T: Named + Ord> {
    names: &'a BTreeMap<u32, String>,
    polynomial: &'a Term<T>
}

impl <'a, T: Named + Ord> fmt::Display for Bound<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut last = false;
        self.polynomial.parts.iter().try_for_each(|(k, v)| {
            if last {
                write!(f, "*")
            } else {
                fmt::Result::Ok(())
            }.and_then(|_| {
                last = true;
                write!(f, "{}^{}", k.get_name(self.names), v)
            })
        })
    }
}

trait Named {
    fn get_name(&self, names: &BTreeMap<u32, String>) -> String;
}

impl Named for GrevlexMonomial {
    fn get_name(&self, names: &BTreeMap<u32, String>) -> String {
        names.get(&self.index).unwrap_or(&"???".to_string()).clone()
    }
}

struct Polynomial {
    terms: BTreeMap<Term<GrevlexMonomial>, f64>
}

impl Polynomial {
    fn lead_term(&self) -> Option<(&Term<GrevlexMonomial>, f64)> {
        self.terms.iter().next_back().map(|(k, v)| (k, *v))
    }

    fn reduction(&self, other: Polynomial) -> Option<Polynomial> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_simple(names: &mut BTreeMap<String, u32>, v: &str) -> Term<GrevlexMonomial> {
        let re = Regex::new(r"([a-z]+\d*)\^(\d+)").unwrap();

        let mut terms = re.captures_iter(v).map(|caps| {
            let next = names.len() as u32;
            let name = caps[1].to_string();
            let degree = caps[2].parse().unwrap();
            let index = *names.entry(name).or_insert(next);
            Term {
                parts: vec![(GrevlexMonomial { index }, degree)].into_iter().collect()
            }
        });

        let first = terms.next().unwrap();
        terms.fold(first, |a, c| a * &c)
    }

    fn string_term(names: &BTreeMap<String, u32>, value: &Term<GrevlexMonomial>) -> String {
        let inverted = names.iter().map(|(k, v)| { (*v, k.clone()) }).collect();
        format!("{}", Bound { names: &inverted, polynomial: value }).to_string()
    }

    fn norm(names: &mut BTreeMap<String, u32>, v: &str) -> String {
        let t = parse_simple(names, v);
        string_term(names, &t)
    }

    #[test]
    fn test_display() {
        let mut names = BTreeMap::new();
        let value = parse_simple(&mut names, "x^1*y^3*z^1*x^1");
        assert_eq!(string_term(&names, &value), "z^1*y^3*x^2");
    }

    #[test]
    fn test_order() {
        let mut names = BTreeMap::new();
        let t1 = parse_simple(&mut names, "x^1*y^3*z^1");
        let t2 = parse_simple(&mut names, "x^1*y^2*z^2");
        assert_eq!(t1.cmp(&t2), Ordering::Greater);
        assert_eq!(t1.cmp(&t1), Ordering::Equal);
        assert_eq!(t2.cmp(&t1), Ordering::Less);
        println!("next");
        let t2 = parse_simple(&mut names, "x^3*y^2");
        assert_eq!(t1.cmp(&t2), Ordering::Less);
        assert_eq!(t1.cmp(&t1), Ordering::Equal);
        assert_eq!(t2.cmp(&t1), Ordering::Greater);
    }

    #[test]
    fn test_lead_term() {
        let mut names = BTreeMap::new();
        let a = parse_simple(&mut names, "x^2*y^8");
        let b = parse_simple(&mut names, "x^5*y^1*z^4");
        let c = parse_simple(&mut names, "x^1*y^4");
        let d = parse_simple(&mut names, "x^1*y^1*z^3");
        assert_eq!(a.cmp(&b), Ordering::Greater);

        let terms = vec![(a, 2.0), (b, -3.0), (c, -1.0), (d, 1.0)].into_iter().collect();
        let p = Polynomial { terms };
        let (lead, coef) = p.lead_term().unwrap();
        assert_eq!(string_term(&names, lead), "y^8*x^2");
        assert_eq!(coef, 2.0);
    }

    #[test]
    fn test_full_div() {
        let mut names = BTreeMap::new();
        let a = parse_simple(&mut names, "x^2*y^8");
        let b = parse_simple(&mut names, "x^1*y^8");
        let c = parse_simple(&mut names, "x^3*y^8*z^2");
        let d = parse_simple(&mut names, "x^3*y^8");

        assert_eq!(string_term(&names, &a.full_div(&b).unwrap()), norm(&mut names, "x^1"));
        assert_eq!(a.full_div(&c), None);
        assert_eq!(string_term(&names, &c.full_div(&a).unwrap()), norm(&mut names, "x^1*z^2"));
        assert_eq!(a.full_div(&d), None);
    }

    #[test]
    fn test_mul() {
        let mut names = BTreeMap::new();
        let a = parse_simple(&mut names, "x^2*y^3");
        let b = parse_simple(&mut names, "x^1*y^8");
        let c = parse_simple(&mut names, "y^4*z^2");
        let d = parse_simple(&mut names, "x^3*z^3");

        assert_eq!(string_term(&names, &(a.clone() * &b)), norm(&mut names, "x^3*y^11"));
        assert_eq!(string_term(&names, &(a.clone() * &c)), norm(&mut names, "x^2*y^7*z^2"));
        assert_eq!(string_term(&names, &(a.clone() * &d)), norm(&mut names, "x^5*y^3*z^3"));
    }
}