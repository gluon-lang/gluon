//! Checks `match` expressions for missing and unreachable alternatives using the usefulness
//! algorithm described in "Warnings for pattern matching" (Maranget, 2007).

use std::cell::Cell;

use crate::base::{
    ast::{self, Alternative, Literal, Pattern, SpannedPattern},
    pos::{BytePos, Span},
    symbol::Symbol,
    types::{ArgType, BuiltinType, Type, row_iter},
};

use crate::typ::RcType;

use super::Typecheck;

#[derive(Clone, Debug)]
enum Ctor {
    Variant(Symbol),
    Single,
    Lit(Literal),
}

impl Ctor {
    fn same(&self, other: &Ctor) -> bool {
        match (self, other) {
            (Ctor::Variant(a), Ctor::Variant(b)) => a.declared_name() == b.declared_name(),
            (Ctor::Single, Ctor::Single) => true,
            (Ctor::Lit(a), Ctor::Lit(b)) => a == b,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
enum DeconPat {
    Wild,
    Constructed(Ctor, Vec<DeconPat>),
}

enum Signature {
    Finite(Vec<Ctor>),
    Infinite,
    Opaque,
}

enum Usefulness {
    Useful(Vec<Witness>),
    NotUseful,
}

#[derive(Clone)]
struct Witness(Vec<DeconPat>);

impl Witness {
    fn apply(mut self, ctor: Ctor, arity: usize) -> Witness {
        let args: Vec<DeconPat> = self.0.drain(0..arity).collect();
        self.0.insert(0, DeconPat::Constructed(ctor, args));
        self
    }
}

pub(super) struct MatchAnalysis {
    pub missing: Vec<String>,
    pub unreachable: Vec<Span<BytePos>>,
}

struct Analyzer<'a, 'b, 'ast> {
    tc: &'a Typecheck<'b, 'ast>,
    inconclusive: Cell<bool>,
}

impl<'a, 'b, 'ast> Analyzer<'a, 'b, 'ast> {
    fn resolve(&self, typ: &RcType) -> RcType {
        let mut typ = self.tc.subs.zonk(typ);
        loop {
            typ = self.tc.remove_aliases(typ);
            let inner = match &*typ {
                Type::Forall(_, inner) => Some(inner.clone()),
                _ => None,
            };
            match inner {
                Some(inner) => typ = inner,
                None => return typ,
            }
        }
    }

    fn deconstruct(&self, pat: &SpannedPattern<'_, Symbol>, typ: &RcType) -> DeconPat {
        match &pat.value {
            Pattern::Ident(_) | Pattern::Error => DeconPat::Wild,
            Pattern::As(_, inner) => self.deconstruct(inner, typ),
            Pattern::Literal(lit) => DeconPat::Constructed(Ctor::Lit(lit.clone()), Vec::new()),
            Pattern::Constructor(id, args) => {
                let ctor = Ctor::Variant(id.name.clone());
                let field_types = self.ctor_fields(typ, &ctor);
                let fields = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        let sub_ty = field_types.get(i).cloned().unwrap_or_else(|| typ.clone());
                        self.deconstruct(arg, &sub_ty)
                    })
                    .collect();
                DeconPat::Constructed(ctor, fields)
            }
            Pattern::Tuple { elems, .. } => {
                let field_types = self.ctor_fields(typ, &Ctor::Single);
                let fields = elems
                    .iter()
                    .enumerate()
                    .map(|(i, elem)| {
                        let sub_ty = field_types.get(i).cloned().unwrap_or_else(|| typ.clone());
                        self.deconstruct(elem, &sub_ty)
                    })
                    .collect();
                DeconPat::Constructed(Ctor::Single, fields)
            }
            Pattern::Record { fields, .. } => {
                let order = self.record_fields(typ);
                let mut sub = vec![DeconPat::Wild; order.len()];
                for (name, value) in ast::pattern_values(fields) {
                    if let Some(idx) = order
                        .iter()
                        .position(|(n, _)| n.declared_name() == name.value.declared_name())
                    {
                        sub[idx] = match value {
                            Some(value) => self.deconstruct(value, &order[idx].1),
                            None => DeconPat::Wild,
                        };
                    }
                }
                DeconPat::Constructed(Ctor::Single, sub)
            }
        }
    }

    fn record_fields(&self, typ: &RcType) -> Vec<(Symbol, RcType)> {
        let resolved = self.resolve(typ);
        match &*resolved {
            Type::Record(row) => row_iter(row)
                .map(|field| (field.name.clone(), field.typ.clone()))
                .collect(),
            _ => Vec::new(),
        }
    }

    fn variant_row(&self, typ: &RcType) -> Option<(Vec<(Symbol, Vec<RcType>)>, bool)> {
        let resolved = self.resolve(typ);
        match &*resolved {
            Type::Variant(row) => {
                let ctors = row_iter(row)
                    .map(|field| (field.name.clone(), ctor_arg_types(&field.typ)))
                    .collect();
                let mut tail = &**row;
                let closed = loop {
                    match tail {
                        Type::ExtendRow { rest, .. } => tail = &**rest,
                        Type::EmptyRow => break true,
                        _ => break false,
                    }
                };
                Some((ctors, closed))
            }
            _ => None,
        }
    }

    fn ctor_fields(&self, typ: &RcType, ctor: &Ctor) -> Vec<RcType> {
        match ctor {
            Ctor::Lit(_) => Vec::new(),
            Ctor::Single => self
                .record_fields(typ)
                .into_iter()
                .map(|(_, t)| t)
                .collect(),
            Ctor::Variant(name) => {
                if let Some((ctors, _)) = self.variant_row(typ) {
                    for (ctor_name, args) in ctors {
                        if ctor_name.declared_name() == name.declared_name() {
                            return args;
                        }
                    }
                }
                Vec::new()
            }
        }
    }

    fn signature(&self, typ: &RcType) -> Signature {
        let resolved = self.resolve(typ);
        match &*resolved {
            Type::Variant(_) => match self.variant_row(typ) {
                Some((ctors, true)) => {
                    Signature::Finite(ctors.into_iter().map(|(n, _)| Ctor::Variant(n)).collect())
                }
                _ => Signature::Infinite,
            },
            Type::Record(_) => Signature::Finite(vec![Ctor::Single]),
            Type::Builtin(BuiltinType::Int)
            | Type::Builtin(BuiltinType::Byte)
            | Type::Builtin(BuiltinType::Char)
            | Type::Builtin(BuiltinType::Float)
            | Type::Builtin(BuiltinType::String) => Signature::Infinite,
            _ => Signature::Opaque,
        }
    }

    fn arity_of(&self, typ: &RcType, ctor: &Ctor) -> usize {
        self.ctor_fields(typ, ctor).len()
    }

    fn specialize_row(&self, row: &[DeconPat], ctor: &Ctor, arity: usize) -> Option<Vec<DeconPat>> {
        let mut head = match &row[0] {
            DeconPat::Wild => vec![DeconPat::Wild; arity],
            DeconPat::Constructed(c, fields) if c.same(ctor) => fields.clone(),
            DeconPat::Constructed(..) => return None,
        };
        head.resize(arity, DeconPat::Wild);
        head.extend_from_slice(&row[1..]);
        Some(head)
    }

    fn default_row(&self, row: &[DeconPat]) -> Option<Vec<DeconPat>> {
        match &row[0] {
            DeconPat::Wild => Some(row[1..].to_vec()),
            DeconPat::Constructed(..) => None,
        }
    }

    fn head_ctors(&self, matrix: &[Vec<DeconPat>]) -> Vec<Ctor> {
        let mut ctors: Vec<Ctor> = Vec::new();
        for row in matrix {
            if let DeconPat::Constructed(c, _) = &row[0] {
                if !ctors.iter().any(|seen| seen.same(c)) {
                    ctors.push(c.clone());
                }
            }
        }
        ctors
    }

    fn is_useful(&self, matrix: &[Vec<DeconPat>], v: &[DeconPat], types: &[RcType]) -> Usefulness {
        if v.is_empty() {
            return if matrix.is_empty() {
                Usefulness::Useful(vec![Witness(Vec::new())])
            } else {
                Usefulness::NotUseful
            };
        }

        let head_type = &types[0];

        if let Signature::Opaque = self.signature(head_type) {
            let constructed = |pat: &DeconPat| matches!(pat, DeconPat::Constructed(..));
            if constructed(&v[0]) || matrix.iter().any(|row| constructed(&row[0])) {
                self.inconclusive.set(true);
            }
        }

        match &v[0] {
            DeconPat::Constructed(ctor, _) => {
                let arity = self.arity_of(head_type, ctor);
                self.useful_against_ctor(matrix, v, types, ctor, arity)
            }
            DeconPat::Wild => {
                let sig = self.signature(head_type);
                let present = self.head_ctors(matrix);
                let complete = match &sig {
                    Signature::Finite(all) => all.iter().all(|c| present.iter().any(|p| p.same(c))),
                    _ => false,
                };

                if complete {
                    let all = match sig {
                        Signature::Finite(all) => all,
                        _ => unreachable!(),
                    };
                    let mut witnesses = Vec::new();
                    for ctor in &all {
                        let arity = self.arity_of(head_type, ctor);
                        if let Usefulness::Useful(ws) =
                            self.useful_against_ctor(matrix, v, types, ctor, arity)
                        {
                            witnesses.extend(ws);
                        }
                    }
                    if witnesses.is_empty() {
                        Usefulness::NotUseful
                    } else {
                        Usefulness::Useful(witnesses)
                    }
                } else {
                    let default: Vec<Vec<DeconPat>> = matrix
                        .iter()
                        .filter_map(|row| self.default_row(row))
                        .collect();
                    let sub_types = types[1..].to_vec();
                    match self.is_useful(&default, &v[1..], &sub_types) {
                        Usefulness::NotUseful => Usefulness::NotUseful,
                        Usefulness::Useful(ws) => {
                            let head = self.missing_witness(head_type, &sig, &present);
                            Usefulness::Useful(
                                ws.into_iter()
                                    .map(|mut w| {
                                        w.0.insert(0, head.clone());
                                        w
                                    })
                                    .collect(),
                            )
                        }
                    }
                }
            }
        }
    }

    fn useful_against_ctor(
        &self,
        matrix: &[Vec<DeconPat>],
        v: &[DeconPat],
        types: &[RcType],
        ctor: &Ctor,
        arity: usize,
    ) -> Usefulness {
        let specialized: Vec<Vec<DeconPat>> = matrix
            .iter()
            .filter_map(|row| self.specialize_row(row, ctor, arity))
            .collect();
        let v_spec = match self.specialize_row(v, ctor, arity) {
            Some(v_spec) => v_spec,
            None => return Usefulness::NotUseful,
        };
        let head_type = &types[0];
        let mut sub_types = self.ctor_fields(head_type, ctor);
        sub_types.resize(arity, head_type.clone());
        sub_types.extend_from_slice(&types[1..]);
        match self.is_useful(&specialized, &v_spec, &sub_types) {
            Usefulness::NotUseful => Usefulness::NotUseful,
            Usefulness::Useful(ws) => Usefulness::Useful(
                ws.into_iter()
                    .map(|w| w.apply(ctor.clone(), arity))
                    .collect(),
            ),
        }
    }

    fn missing_witness(&self, head_type: &RcType, sig: &Signature, present: &[Ctor]) -> DeconPat {
        if let Signature::Finite(all) = sig {
            for ctor in all {
                if !present.iter().any(|p| p.same(ctor)) {
                    let arity = self.arity_of(head_type, ctor);
                    return DeconPat::Constructed(ctor.clone(), vec![DeconPat::Wild; arity]);
                }
            }
        }
        DeconPat::Wild
    }
}

fn ctor_arg_types(typ: &RcType) -> Vec<RcType> {
    let mut args = Vec::new();
    let mut current = typ;
    loop {
        match &**current {
            Type::Forall(_, inner) => current = inner,
            Type::Function(ArgType::Constructor, arg, ret) => {
                args.push(arg.clone());
                current = ret;
            }
            _ => break,
        }
    }
    args
}

fn render(pat: &DeconPat) -> String {
    match pat {
        DeconPat::Wild => "_".to_string(),
        DeconPat::Constructed(ctor, fields) => match ctor {
            Ctor::Lit(lit) => render_literal(lit),
            Ctor::Single => {
                let inner: Vec<String> = fields.iter().map(render).collect();
                format!("({})", inner.join(", "))
            }
            Ctor::Variant(name) => {
                if fields.is_empty() {
                    name.declared_name().to_string()
                } else {
                    let inner: Vec<String> = fields.iter().map(render_nested).collect();
                    format!("{} {}", name.declared_name(), inner.join(" "))
                }
            }
        },
    }
}

fn render_nested(pat: &DeconPat) -> String {
    match pat {
        DeconPat::Constructed(Ctor::Variant(_), fields) if !fields.is_empty() => {
            format!("({})", render(pat))
        }
        _ => render(pat),
    }
}

fn render_literal(lit: &Literal) -> String {
    match lit {
        Literal::Byte(b) => format!("{}b", b),
        Literal::Int(i) => i.to_string(),
        Literal::Float(f) => f.to_string(),
        Literal::String(s) => format!("{:?}", s),
        Literal::Char(c) => format!("{:?}", c),
    }
}

impl<'a, 'b, 'ast> Analyzer<'a, 'b, 'ast> {
    fn missing_patterns(&self, rows: &[DeconPat], scrutinee: &RcType) -> Vec<String> {
        if let Signature::Opaque = self.signature(scrutinee) {
            return Vec::new();
        }
        let matrix: Vec<Vec<DeconPat>> = rows.iter().map(|p| vec![p.clone()]).collect();
        let wildcard = vec![DeconPat::Wild];
        match self.is_useful(&matrix, &wildcard, &[scrutinee.clone()]) {
            Usefulness::Useful(witnesses) => {
                let mut rendered: Vec<String> = Vec::new();
                for witness in &witnesses {
                    if let Some(head) = witness.0.first() {
                        let text = render(head);
                        if !rendered.contains(&text) {
                            rendered.push(text);
                        }
                    }
                }
                rendered
            }
            Usefulness::NotUseful => Vec::new(),
        }
    }
}

pub(super) fn analyse<'ast>(
    tc: &Typecheck<'_, 'ast>,
    scrutinee_type: &RcType,
    alts: &[Alternative<'ast, Symbol>],
) -> MatchAnalysis {
    let analyzer = Analyzer {
        tc,
        inconclusive: Cell::new(false),
    };
    let resolved = analyzer.resolve(scrutinee_type);

    let rows: Vec<DeconPat> = alts
        .iter()
        .map(|alt| analyzer.deconstruct(&alt.pattern, &resolved))
        .collect();

    let mut unreachable = Vec::new();
    for (i, _) in rows.iter().enumerate() {
        let matrix: Vec<Vec<DeconPat>> = rows[..i].iter().map(|p| vec![p.clone()]).collect();
        let candidate = vec![rows[i].clone()];
        if let Usefulness::NotUseful = analyzer.is_useful(&matrix, &candidate, &[resolved.clone()])
        {
            unreachable.push(alts[i].pattern.span);
        }
    }

    let missing = analyzer.missing_patterns(&rows, &resolved);

    if analyzer.inconclusive.get() {
        return MatchAnalysis {
            missing: Vec::new(),
            unreachable: Vec::new(),
        };
    }

    MatchAnalysis {
        missing,
        unreachable,
    }
}
