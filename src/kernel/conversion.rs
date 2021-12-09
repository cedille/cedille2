
use crate::database::Database;
use crate::kernel::*;
/* 
impl Term {
    pub fn convertible(db: &mut Database, a: Term, b: Term) -> bool {
        let a = Term::normalize(db, a.erase(), None);
        let b = Term::normalize(db, b.erase(), None);
        a == b
    }
}

impl Type {
    pub fn convertible(db: &mut Database, a: Type, b: Type) -> bool {
        let a = Type::normalize(db, a.clone(), None);
        let b = Type::normalize(db, b.clone(), None);
        Type::convertible_head(db, a, b)
    }

    fn convertible_head(db: &mut Database, a: Type, b: Type) -> bool {
        match (a, b) {
            (Type::Fn { domain:d1, body:b1 },
                Type::Fn { domain:d2, body:b2 })
            => Kind::convertible(db, *d1, *d2) && Type::convertible(db, *b1, *b2),
            (Type::TermFn { mode:m1, domain:d1, body:b1 },
                Type::TermFn { mode:m2, domain:d2, body:b2 })
            => m1 == m2 && Type::convertible(db, *d1, *d2) && Type::convertible(db, *b1, *b2),
            (Type::Lambda { domain:d1, body:b1 },
                Type::Lambda { domain:d2, body:b2 })
            => Kind::convertible(db, *d1, *d2) && Type::convertible(db, *b1, *b2),
            (Type::TermLambda { domain:d1, body:b1 },
                Type::TermLambda { domain:d2, body:b2 })
            => Type::convertible(db, *d1, *d2) && Type::convertible(db, *b1, *b2),
            (Type::Intersection { first:f1, second:s1 },
                Type::Intersection { first:f2, second:s2 })
            => Type::convertible(db, *f1, *f2) && Type::convertible(db, *s1, *s2),
            (Type::Equality { left:l1, right:r1 },
                Type::Equality { left:l2, right:r2 })
            => Term::convertible(db, *l1, *l2) && Term::convertible(db, *r1, *r2),
            (Type::Apply { fun:f1, arg:a1 },
                Type::Apply { fun:f2, arg:a2 })
            => Type::convertible_head(db, *f1, *f2) && Type::convertible(db, *a1, *a2),
            (Type::TermApply { fun:f1, arg:a1 },
                Type::TermApply { fun:f2, arg:a2 })
            => Type::convertible_head(db, *f1, *f2) && Term::convertible(db, *a1, *a2),
            (Type::Var { index:i1 }, Type::Var { index:i2 }) => i1 == i2,
            (Type::Ref { id:i1 }, Type::Ref { id:i2 }) => i1 == i2,
            (Type::Hole, Type::Hole) => true,
            _ => false
        }
    }
}

impl Kind {
    pub fn convertible(db: &mut Database, a: Kind, b: Kind) -> bool {
        match (a, b) {
            (Kind::Fn { domain:d1, body:b1 },
                Kind::Fn { domain:d2, body:b2 })
            => Kind::convertible(db, *d1, *d2) && Kind::convertible(db, *b1, *b2),
            (Kind::TypeFn { domain:d1, body:b1 },
                Kind::TypeFn { domain:d2, body:b2 })
            => Type::convertible(db, *d1, *d2) && Kind::convertible(db, *b1, *b2),
            (Kind::Star, Kind::Star) => true,
            _ => false
        }
    }
}
 */