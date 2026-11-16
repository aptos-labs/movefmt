// Copyright © Aptos Foundation
// Copyright (c) The BitsLab.MoveBit Contributors
// SPDX-License-Identifier: Apache-2.0

//! Support for the `[weight = N]` annotation of the Move specification language.
//!
//! The annotation is written directly after the return type of a spec function,
//! after the bindings (and triggers) of a quantifier, and after the bindings (and
//! triggers) of a `forall .. apply` in a proof:
//!
//! ```move
//! spec fun sum(v: vector<u64>, n: num): num [weight = 15] { .. }
//! ensures forall k: num [weight = 3]: p(k);
//! forall x: u64 [weight = 2] apply lemma(x);
//! ```
//!
//! The parser this formatter is built on does not know the annotation. The token
//! tree is built from the source text itself, so the annotation's tokens are printed
//! like any others; the parser is only needed for the structure around them. When a
//! source does not parse and contains such annotations, it is parsed again with each
//! annotation replaced by blanks of the same length, which keeps every location
//! valid. A source that parses as it is never takes this path, so its output cannot
//! change.
//!
//! An annotation is only accepted where the language allows one. The definitions
//! parsed from the blanked text say where that is; a candidate elsewhere is put back,
//! and the source is then either an ordinary expression that parses, or rejected.

use crate::tools::utils::get_compile_env;
use move_command_line_common::files::FileHash;
use move_compiler::diagnostics::Diagnostics;
use move_compiler::parser::ast::*;
use move_compiler::parser::lexer::{Lexer, Tok};
use move_compiler::parser::syntax::parse_file_string;
use std::collections::HashSet;

/// The result of parsing a source for formatting.
pub struct Parsed {
    pub defs: Vec<Definition>,
    /// Start offsets of the `[` of every `[weight = N]` annotation that had to be
    /// blanked to parse the source. Empty when the source parsed as it is.
    pub weight_starts: HashSet<u32>,
}

/// Parses `content`, tolerating `[weight = N]` annotations.
///
/// On failure the diagnostics are those of the unmodified source.
pub fn parse_for_format(content: &str) -> Result<Parsed, Diagnostics> {
    let err = match parse_file_string(&mut get_compile_env(), FileHash::empty(), content) {
        Ok((defs, _)) => {
            return Ok(Parsed {
                defs,
                weight_starts: HashSet::new(),
            });
        }
        Err(err) => err,
    };
    let Some(toks) = lex(content) else {
        return Err(err);
    };
    let candidates = candidates(content, &toks);
    if candidates.is_empty() {
        return Err(err);
    }
    let Some((defs, kept)) = settle(content, &toks, &candidates, true)
        .or_else(|| settle(content, &toks, &candidates, false))
    else {
        return Err(err);
    };
    Ok(Parsed {
        defs,
        weight_starts: kept.iter().map(|i| toks[*i].start as u32).collect(),
    })
}

/// How often [`settle`] parses the source at most.
const MAX_PARSES: usize = 16;

/// Finds the candidates that are annotations: a non-empty subset such that the source
/// parses with exactly these blanked and each of them stands where the language allows
/// an annotation. The other candidates are then ordinary text the parser accepted.
///
/// Starts with every candidate blanked and puts back those that are in no such
/// position, all at once or, with `all` unset, the first one only. Putting text back
/// changes the structure around the others, so the first way can miss a subset the
/// second finds: in `forall x in v[weight = 1] {x} [weight = 2]: ..` blanking both
/// turns `v {x}` into a pack.
fn settle(
    content: &str,
    toks: &[Token],
    candidates: &[usize],
    all: bool,
) -> Option<(Vec<Definition>, Vec<usize>)> {
    let mut blanked = candidates.to_vec();
    for _ in 0..MAX_PARSES {
        if blanked.is_empty() {
            return None;
        }
        let defs = parse_blanked(content, toks, &blanked)?;
        let kept = in_annotation_position(content, toks, &defs, &blanked);
        if kept.len() == blanked.len() {
            return Some((defs, kept));
        }
        if all {
            blanked = kept;
        } else {
            let first = blanked.iter().position(|i| !kept.contains(i))?;
            blanked.remove(first);
        }
    }
    None
}

/// Like [`parse_for_format`], for callers that only need the definitions.
pub fn parse_defs(content: &str) -> Result<Vec<Definition>, Diagnostics> {
    parse_for_format(content).map(|p| p.defs)
}

struct Token {
    tok: Tok,
    start: usize,
    end: usize,
}

/// The tokens of `content`, without comments. `None` if it does not lex.
fn lex(content: &str) -> Option<Vec<Token>> {
    let mut toks = vec![];
    let mut lexer = Lexer::new(content, FileHash::empty());
    lexer.advance().ok()?;
    while lexer.peek() != Tok::EOF {
        let start = lexer.start_loc();
        toks.push(Token {
            tok: lexer.peek(),
            start,
            end: start + lexer.content().len(),
        });
        lexer.advance().ok()?;
    }
    Some(toks)
}

fn is_ident(content: &str, t: &Token, name: &str) -> bool {
    t.tok == Tok::Identifier && &content[t.start..t.end] == name
}

/// Indices of the `[` tokens that start the token sequence `[ weight = N ]`.
///
/// Found on the token stream, so text in comments and strings is never taken for
/// one. Whether a candidate is an annotation is decided by its position, see
/// [`in_annotation_position`].
fn candidates(content: &str, toks: &[Token]) -> Vec<usize> {
    let mut found = vec![];
    let mut i = 0;
    while i + 4 < toks.len() {
        if toks[i].tok == Tok::LBracket
            // `#[weight = 1]` is an attribute.
            && (i == 0 || toks[i - 1].tok != Tok::NumSign)
            && is_ident(content, &toks[i + 1], "weight")
            && toks[i + 2].tok == Tok::Equal
            && toks[i + 3].tok == Tok::NumValue
            // The language takes a plain decimal number that fits `u32`.
            && content[toks[i + 3].start..toks[i + 3].end]
                .parse::<u32>()
                .is_ok()
            && toks[i + 4].tok == Tok::RBracket
        {
            found.push(i);
            i += 5;
        } else {
            i += 1;
        }
    }
    found
}

/// Parses `content` with the given candidates blanked.
fn parse_blanked(content: &str, toks: &[Token], candidates: &[usize]) -> Option<Vec<Definition>> {
    let mut bytes = content.as_bytes().to_vec();
    for i in candidates {
        // Every byte from `[` to `]`, comments between the tokens included; line
        // breaks stay, so that all other offsets and lines are as in the source.
        for b in &mut bytes[toks[*i].start..toks[*i + 4].end] {
            if *b != b'\n' && *b != b'\r' {
                *b = b' ';
            }
        }
    }
    let masked = String::from_utf8(bytes).ok()?;
    parse_file_string(&mut get_compile_env(), FileHash::empty(), &masked)
        .ok()
        .map(|(defs, _)| defs)
}

/// What an annotation belongs to, which decides what may follow it.
#[derive(Clone, Copy, PartialEq)]
enum Owner {
    /// `spec fun f(..): T [weight = N] { .. }`, or `;`, or a `reads`/`modifies` clause.
    SpecFun,
    /// `forall x: T {triggers} [weight = N] where c: e`, or `: e`.
    Quant,
    /// `forall x: T {triggers} [weight = N] apply lemma(..)`.
    ForallApply,
}

/// A place where an annotation may stand: after the source position `after` and
/// `groups` trigger groups `{ .. }`.
struct Slot {
    after: usize,
    groups: usize,
    owner: Owner,
    /// Where the variable of the last binding ends, and the source range of the part of
    /// its range expression that ends it without taking an index, if there is one (see
    /// [`unindexed_tail`]). With no triggers, brackets after a binding `x in e` index
    /// `e`, unless `e` is `*` or ends in such a part.
    last_bind: Option<(usize, Option<(usize, usize)>)>,
}

/// The candidates among `blanked` that stand where the language allows an annotation,
/// according to definitions parsed from `content` with exactly those blanked. `blanked`
/// is in source order.
fn in_annotation_position(
    content: &str,
    toks: &[Token],
    defs: &[Definition],
    blanked: &[usize],
) -> Vec<usize> {
    let candidates = blanked;
    let mut slots = vec![];
    for def in defs {
        match def {
            Definition::Module(m) => visit_module(&mut slots, m),
            Definition::Address(a) => a.modules.iter().for_each(|m| visit_module(&mut slots, m)),
            Definition::Script(s) => {
                s.constants
                    .iter()
                    .for_each(|c| visit_exp(&mut slots, &c.value));
                visit_function(&mut slots, &s.function);
                s.specs.iter().for_each(|b| visit_spec_block(&mut slots, b));
            }
        }
    }
    // Where each slot expects its annotation: the token after its trigger groups.
    let mut expected: std::collections::HashMap<usize, Vec<&Slot>> = Default::default();
    for slot in &slots {
        if let Some(at) = annotation_token(toks, slot, blanked) {
            expected.entry(at).or_default().push(slot);
        }
    }
    candidates
        .iter()
        .copied()
        .filter(|i| {
            expected
                .get(i)
                .is_some_and(|slots| slots.iter().any(|slot| fills(content, toks, *i, slot)))
        })
        .collect()
}

/// The index of the token at which an annotation in `slot` starts: the first token
/// after the slot's position and its trigger groups `{ .. }`. Scanned forward from
/// the slot, so that braces before it, such as a block used as a range, are not taken
/// for trigger groups. `None` if the braces do not match up.
fn annotation_token(toks: &[Token], slot: &Slot, blanked: &[usize]) -> Option<usize> {
    let mut j = toks.partition_point(|t| t.start < slot.after);
    for _ in 0..slot.groups {
        // A blanked candidate in front of a trigger group is not this slot's annotation;
        // the parser did not see it.
        while blanked.binary_search(&j).is_ok() {
            j += 5;
        }
        if toks.get(j)?.tok != Tok::LBrace {
            return None;
        }
        let mut depth = 0usize;
        loop {
            match toks.get(j)?.tok {
                Tok::LBrace => depth += 1,
                Tok::RBrace => depth -= 1,
                _ => {}
            }
            j += 1;
            if depth == 0 {
                break;
            }
        }
    }
    Some(j)
}

/// Whether the candidate starting at token `i`, which is where `slot` expects its
/// annotation, may stand there.
fn fills(content: &str, toks: &[Token], i: usize, slot: &Slot) -> bool {
    let placed = slot.groups > 0
        || slot.last_bind.is_none_or(|(var_end, tail)| {
            let j = toks.partition_point(|t| t.start < var_end);
            // `x: T`, or `x in *`, or a range that ends in a part taking no index and
            // is not wrapped in parentheses, which would take one.
            toks.get(j).is_some_and(|t| t.tok == Tok::Colon)
                || toks.get(j + 1).is_some_and(|t| t.tok == Tok::Star)
                || tail.is_some_and(|(start, end)| {
                    end == slot.after && !parenthesized(toks, start, end)
                })
        });
    let Some(next) = toks.get(i + 5) else {
        return false;
    };
    let followed = match slot.owner {
        Owner::SpecFun => {
            matches!(next.tok, Tok::LBrace | Tok::Semicolon)
                || is_ident(content, next, "reads")
                || is_ident(content, next, "modifies")
        }
        Owner::Quant => next.tok == Tok::Colon || is_ident(content, next, "where"),
        Owner::ForallApply => is_ident(content, next, "apply"),
    };
    placed && followed
}

/// The source range of the part of `e` that ends it and after which brackets are not
/// an index of `e`: a cast, a type test, `move x`, `copy x`, or the spec block of a
/// lambda. The parser reads those, and the expressions that end in them, without
/// looking for an index.
fn unindexed_tail(e: &Exp) -> Option<(usize, usize)> {
    match &e.value {
        Exp_::Cast(_, _) | Exp_::Test(_, _) | Exp_::Move(_) | Exp_::Copy(_) => {
            Some((e.loc.start() as usize, e.loc.end() as usize))
        }
        Exp_::Lambda(_, body, _, spec) => match spec {
            Some(s) => Some((s.loc.start() as usize, s.loc.end() as usize)),
            None => unindexed_tail(body),
        },
        Exp_::Quant(_, _, _, _, body) => unindexed_tail(body),
        Exp_::StateLabeled(_, inner, _) => unindexed_tail(inner),
        // Not the right operand of a binary operator: after `if (c) {a} else {b} + copy x`
        // brackets index the whole sum.
        Exp_::Assign(_, _, rhs) => unindexed_tail(rhs),
        Exp_::UnaryExp(_, inner) | Exp_::Borrow(_, inner) | Exp_::Dereference(inner) => {
            unindexed_tail(inner)
        }
        _ => None,
    }
}

/// Whether the tokens of the source range `start..end` are one parenthesized group.
fn parenthesized(toks: &[Token], start: usize, end: usize) -> bool {
    let first = toks.partition_point(|t| t.start < start);
    let last = toks.partition_point(|t| t.start < end);
    if last == 0 || toks.get(first).is_none_or(|t| t.tok != Tok::LParen) {
        return false;
    }
    let mut depth = 0usize;
    for (j, t) in toks[first..last].iter().enumerate() {
        match t.tok {
            Tok::LParen => depth += 1,
            Tok::RParen => depth -= 1,
            _ => {}
        }
        if depth == 0 {
            return first + j == last - 1;
        }
    }
    false
}

/// The slot after bindings and triggers.
fn binding_slot(bindings: &BindWithRangeList, triggers: &[Vec<Exp>], owner: Owner) -> Slot {
    Slot {
        after: bindings.loc.end() as usize,
        groups: triggers.len(),
        owner,
        last_bind: bindings
            .value
            .last()
            .map(|b| (b.value.0.loc.end() as usize, unindexed_tail(&b.value.1))),
    }
}

fn visit_module(slots: &mut Vec<Slot>, m: &ModuleDefinition) {
    for member in &m.members {
        match member {
            ModuleMember::Function(f) => visit_function(slots, f),
            ModuleMember::Constant(c) => visit_exp(slots, &c.value),
            ModuleMember::Spec(b) => visit_spec_block(slots, b),
            ModuleMember::Struct(_) | ModuleMember::Use(_) | ModuleMember::Friend(_) => {}
        }
    }
}

fn visit_function(slots: &mut Vec<Slot>, f: &Function) {
    visit_body(slots, &f.body);
}

fn visit_body(slots: &mut Vec<Slot>, body: &FunctionBody) {
    match &body.value {
        FunctionBody_::Defined(seq) => visit_sequence(slots, seq),
        FunctionBody_::Native => {}
    }
}

fn visit_sequence(slots: &mut Vec<Slot>, seq: &Sequence) {
    for item in &seq.1 {
        match &item.value {
            SequenceItem_::Seq(e) | SequenceItem_::Bind(_, _, e) => visit_exp(slots, e),
            SequenceItem_::Declare(_, _) => {}
        }
    }
    if let Some(e) = seq.3.as_ref() {
        visit_exp(slots, e);
    }
}

fn visit_spec_block(slots: &mut Vec<Slot>, block: &SpecBlock) {
    block
        .value
        .members
        .iter()
        .for_each(|m| visit_spec_member(slots, m));
}

fn visit_spec_member(slots: &mut Vec<Slot>, member: &SpecBlockMember) {
    match &member.value {
        SpecBlockMember_::Condition {
            kind: _,
            properties: _,
            exp,
            additional_exps,
        } => {
            visit_exp(slots, exp);
            visit_exps(slots, additional_exps);
        }
        SpecBlockMember_::Function {
            uninterpreted: _,
            name: _,
            signature,
            modifies,
            reads: _,
            body,
        } => {
            slots.push(Slot {
                after: signature.return_type.loc.end() as usize,
                groups: 0,
                owner: Owner::SpecFun,
                last_bind: None,
            });
            visit_exps(slots, modifies);
            visit_body(slots, body);
        }
        SpecBlockMember_::ModifiesOf {
            fun_param: _,
            params: _,
            targets,
            all: _,
        } => visit_exps(slots, targets),
        SpecBlockMember_::Modifies { targets } => visit_exps(slots, targets),
        SpecBlockMember_::Variable {
            is_global: _,
            name: _,
            type_parameters: _,
            type_: _,
            init,
        } => {
            if let Some(e) = init {
                visit_exp(slots, e);
            }
        }
        SpecBlockMember_::Let {
            name: _,
            post_state: _,
            def,
        } => visit_exp(slots, def),
        SpecBlockMember_::Update { lhs, rhs } => {
            visit_exp(slots, lhs);
            visit_exp(slots, rhs);
        }
        SpecBlockMember_::Include { properties: _, exp } => visit_exp(slots, exp),
        SpecBlockMember_::Apply {
            exp,
            patterns: _,
            exclusion_patterns: _,
        } => visit_exp(slots, exp),
        SpecBlockMember_::Proof { body } => visit_proof(slots, body),
        SpecBlockMember_::Lemma {
            name: _,
            signature: _,
            spec_members,
            proof,
        } => {
            spec_members
                .iter()
                .for_each(|m| visit_spec_member(slots, m));
            if let Some(p) = proof {
                visit_proof(slots, p);
            }
        }
        SpecBlockMember_::ReadsOf {
            fun_param: _,
            types: _,
            all: _,
        }
        | SpecBlockMember_::Reads { types: _ }
        | SpecBlockMember_::Pragma { properties: _ } => {}
    }
}

fn visit_proof(slots: &mut Vec<Slot>, proof: &Proof) {
    match &proof.value {
        Proof_::Let(_, e) | Proof_::Assert(e) | Proof_::Assume(_, e) | Proof_::Split(e) => {
            visit_exp(slots, e)
        }
        Proof_::IfElse(c, t, e) => {
            visit_exp(slots, c);
            visit_proof(slots, t);
            if let Some(e) = e {
                visit_proof(slots, e);
            }
        }
        Proof_::Block(ps) => ps.iter().for_each(|p| visit_proof(slots, p)),
        Proof_::Apply(_, args) => visit_exps(slots, args),
        Proof_::ForallApply {
            bindings,
            patterns,
            lemma: _,
            args,
        } => {
            slots.push(binding_slot(bindings, patterns, Owner::ForallApply));
            bindings
                .value
                .iter()
                .for_each(|b| visit_exp(slots, &b.value.1));
            patterns.iter().for_each(|p| visit_exps(slots, p));
            visit_exps(slots, args);
        }
        Proof_::Calc(steps) => steps.iter().for_each(|(e, _)| visit_exp(slots, e)),
        Proof_::Post(p) => visit_proof(slots, p),
    }
}

fn visit_exps(slots: &mut Vec<Slot>, exps: &[Exp]) {
    exps.iter().for_each(|e| visit_exp(slots, e));
}

// Every variant is listed, with no catch-all, so that a new kind of expression
// cannot be left out without a compile error.
fn visit_exp(slots: &mut Vec<Slot>, exp: &Exp) {
    match &exp.value {
        Exp_::Quant(kind, bindings, triggers, condition, body) => {
            // `choose` takes no annotation.
            if matches!(kind.value, QuantKind_::Forall | QuantKind_::Exists) {
                slots.push(binding_slot(bindings, triggers, Owner::Quant));
            }
            bindings
                .value
                .iter()
                .for_each(|b| visit_exp(slots, &b.value.1));
            triggers.iter().for_each(|t| visit_exps(slots, t));
            if let Some(c) = condition {
                visit_exp(slots, c);
            }
            visit_exp(slots, body);
        }
        Exp_::Call(_, _, _, args) | Exp_::Vector(_, _, args) => visit_exps(slots, &args.value),
        Exp_::ExpCall(f, args) | Exp_::Behavior(_, f, args) => {
            visit_exp(slots, f);
            visit_exps(slots, &args.value);
        }
        Exp_::Pack(_, _, fields) => fields.iter().for_each(|(_, e)| visit_exp(slots, e)),
        Exp_::IfElse(c, t, e) => {
            visit_exp(slots, c);
            visit_exp(slots, t);
            if let Some(e) = e {
                visit_exp(slots, e);
            }
        }
        Exp_::While(_, c, b) => {
            visit_exp(slots, c);
            visit_exp(slots, b);
        }
        Exp_::Match(e, arms) => {
            visit_exp(slots, e);
            for arm in arms {
                if let Some(guard) = &arm.value.1 {
                    visit_exp(slots, guard);
                }
                visit_exp(slots, &arm.value.2);
            }
        }
        Exp_::Block(seq) => visit_sequence(slots, seq),
        Exp_::Lambda(_, body, _, spec) => {
            visit_exp(slots, body);
            if let Some(s) = spec {
                visit_exp(slots, s);
            }
        }
        Exp_::ExpList(es) => visit_exps(slots, es),
        Exp_::Assign(l, _, r) | Exp_::BinopExp(l, _, r) | Exp_::Index(l, r) => {
            visit_exp(slots, l);
            visit_exp(slots, r);
        }
        Exp_::Return(e) => {
            if let Some(e) = e {
                visit_exp(slots, e);
            }
        }
        Exp_::Loop(_, e)
        | Exp_::StateLabeled(_, e, _)
        | Exp_::Abort(e)
        | Exp_::Dereference(e)
        | Exp_::UnaryExp(_, e)
        | Exp_::Borrow(_, e)
        | Exp_::Dot(e, _)
        | Exp_::Cast(e, _)
        | Exp_::Annotate(e, _)
        | Exp_::Test(e, _) => visit_exp(slots, e),
        Exp_::Spec(block) => visit_spec_block(slots, block),
        Exp_::Value(_)
        | Exp_::Move(_)
        | Exp_::Copy(_)
        | Exp_::Name(_, _)
        | Exp_::Unit
        | Exp_::Break(_)
        | Exp_::Continue(_)
        | Exp_::UnresolvedError => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kept(src: &str) -> Vec<String> {
        match parse_for_format(src) {
            Ok(p) => {
                let mut starts: Vec<u32> = p.weight_starts.into_iter().collect();
                starts.sort();
                starts
                    .iter()
                    .map(|s| {
                        let rest = &src[*s as usize..];
                        rest[..=rest.find(']').unwrap()].to_string()
                    })
                    .collect()
            }
            Err(_) => vec!["<rejected>".to_string()],
        }
    }

    #[test]
    fn finds_annotations_on_tokens_only() {
        let src =
            "module 0x1::m { spec module { fun f(): num /* [weight = 9] */ [weight = 5] { 1 } } }";
        assert_eq!(kept(src), ["[weight = 5]"]);
    }

    #[test]
    fn accepts_every_position_of_the_language() {
        let src = "module 0x1::m {
            struct S has key {}
            fun f(x: u64): u64 { x }
            spec f {
                ensures forall k: num [weight = 1]: k == k;
                ensures exists k: num, j: num {f(k), f(j)} {f(j)} [weight = 2] where k < j: k == j;
                ensures forall a: num: forall b: num [weight = 3]: a == b;
            } proof {
                forall y: u64 [weight = 4] apply l(y);
                forall y: u64 {f(y)} [weight = 5] apply l(y);
            }
            spec module {
                fun g(): num [weight = 6] { 1 }
                fun h(): num [weight = 7];
                fun r(): num [weight = 8] reads S { 1 }
            }
            spec f {
                ensures forall k: num {f(k),} [weight = 9]: true;
                ensures forall s in * [weight = 17]: true;
                ensures forall a: num, s in * [weight = 18]: true;
                ensures forall j in 0..3, a: num [weight = 19]: true;
                ensures forall j in 0..3 {f(j)} [weight = 20]: true;
                ensures forall j in { 0..3 } {f(j)} [weight = 21]: true;
                ensures forall j in { 0..3 } {} {f(j),} [weight = 22] where j > 0: true;
                ensures forall x in |y| y as u64 [weight = 23]: true;
                ensures forall x in (f(1) as u64) as u64 [weight = 24]: true;
                ensures forall k in vec()[weight = 99] {f(1)} [weight = 25]: true;
                ensures forall k in copy v [weight = 26]: true;
                ensures forall k in !copy b [weight = 27] where true: true;
                ensures exists k: num {} [weight = 10]: true;
                ensures forall k: num {f(k)} {} [weight = 11] where k > 0: true;
                ensures forall k: num {forall j: num [weight = 12]: j == k} [weight = 13]: true;
            } proof {
                forall y: u64 {f(y),} [weight = 14] apply l(y);
            }
        }";
        let all = kept(src);
        let expected: Vec<String> = (1..=14)
            .chain(17..=27)
            .map(|n| format!("[weight = {n}]"))
            .collect();
        let mut sorted = all.clone();
        sorted.sort();
        let mut want = expected.clone();
        want.sort();
        assert_eq!(sorted, want);
    }

    #[test]
    fn puts_back_one_look_alike_at_a_time() {
        // Blanking the index too would turn `v {x}` into a pack and hide the annotation.
        for (src, want) in [
            (
                "module 0x1::m { fun f() { forall x in v[weight = 99] {x} [weight = 1]: true } }",
                vec!["[weight = 1]"],
            ),
            (
                "module 0x1::m { fun f() { forall x in v[weight = 99] {x,} [weight = 1]: true } }",
                vec!["[weight = 1]"],
            ),
            (
                "module 0x1::m { fun f() { forall a in v[weight = 98] {a} [weight = 1]: \
                 forall b in w[weight = 99] {b} [weight = 2]: true } }",
                vec!["[weight = 1]", "[weight = 2]"],
            ),
        ] {
            assert_eq!(kept(src), want, "{src}");
        }
        // The search is bounded.
        let many = "forall x in v[weight = 99] {x} [weight = 1]: ".repeat(MAX_PARSES);
        assert!(
            parse_for_format(&format!("module 0x1::m {{ fun f() {{ {many}true }} }}")).is_err()
        );
    }

    #[test]
    fn rejects_other_positions() {
        for src in [
            // A spec function needs a return type, with or without an annotation.
            "module 0x1::m { spec module { fun u() [weight = 1] { true } } }",
            // After the delimiter instead of before it.
            "module 0x1::m { spec module { invariant forall x: num: [weight = 1] { true }; } }",
            "module 0x1::m { spec module { invariant forall x: num where [weight = 1] { true }: true; } }",
            // Before the triggers instead of after them.
            "module 0x1::m { fun f() {} spec f { ensures forall k: num [weight = 1] {k}: true; } }",
            // After a clause of a spec function instead of before it.
            "module 0x1::m { struct S has key {} spec module { fun h(): num reads S [weight = 2]; } }",
            // After `apply`.
            "module 0x1::m { fun f() {} spec f { ensures true; } proof { forall x: u64 apply [weight = 1] l(x); } }",
            // `choose` takes none.
            "module 0x1::m { fun f() {} spec f { ensures (choose x: u64 [weight = 1] where x > 0) > 0; } }",
            // Not a decimal number that fits `u32`.
            "module 0x1::m { spec module { fun g(): num [weight = 0x10] { 1 } } }",
            "module 0x1::m { spec module { fun g(): num [weight = 1_000] { 1 } } }",
            "module 0x1::m { spec module { fun g(): num [weight = 99999999999999] { 1 } } }",
            // On things that take no annotation.
            "module 0x1::m [weight = 1] { fun f() {} }",
            "module 0x1::m { fun f() [weight = 1] {} }",
            "module 0x1::m { fun f() {} spec f [weight = 1] { ensures true; } }",
        ] {
            assert_eq!(kept(src), ["<rejected>"], "{src}");
        }
    }

    #[test]
    fn leaves_index_expressions_alone() {
        let src = "module 0x1::m {
            fun f(v: vector<u64>, weight: u64) { let w = vector[weight = 1]; v[weight = 2]; }
            spec module { fun g(): num [weight = 3] { 1 } }
        }";
        assert_eq!(kept(src), ["[weight = 3]"]);
    }

    #[test]
    fn brackets_after_a_range_binding_index_the_range() {
        // `v[weight = 1]` is an index expression here, as it is without the spec function.
        let src = "module 0x1::m {
            fun f(v: vector<u64>): bool { forall k in v[weight = 1]: true }
            spec module { fun g(): num [weight = 3] { 1 } }
        }";
        assert_eq!(kept(src), ["[weight = 3]"]);
        // Also after a parenthesized cast, which takes an index like any other term.
        let src = "module 0x1::m {
            fun f(v: vector<u64>): bool { forall k in (v as vector<u64>)[weight = 1]: true }
            spec module { fun g(): num [weight = 3] { 1 } }
        }";
        assert_eq!(kept(src), ["[weight = 3]"]);
        // Also after a binary operator whose left operand ends in a block.
        let src = "module 0x1::m {
            fun f(a: u64, w: u64, b: bool) {}
            spec f { ensures forall k in if (b) {a} else {w} + copy w [weight = 1]: true; }
            spec module { fun g(): num [weight = 3] { 1 } }
        }";
        assert_eq!(kept(src), ["[weight = 3]"]);
    }

    #[test]
    fn range_tails_agree_with_the_parser() {
        let src = |range: &str| {
            format!(
                "module 0x1::m {{
                    fun f(a: u64, w: u64, b: bool, v: vector<u64>) {{}}
                    spec f {{ ensures forall k in {range} [weight = 1]: true; }}
                    spec module {{ fun g(): num [weight = 3] {{ 1 }} }}
                }}"
            )
        };
        // The range ends in a part that takes no index: an annotation.
        for range in [
            "a as u64",
            "a is u64",
            "(a) as u64",
            "&copy w",
            "!copy b",
            "x = copy w",
            "|y| copy w",
            "|y| y as u64",
            "forall y: u64: copy b",
        ] {
            assert_eq!(
                kept(&src(range)),
                ["[weight = 1]", "[weight = 3]"],
                "{range}"
            );
        }
        // The range ends in a term, which takes the brackets as an index.
        for range in [
            "(a as u64)",
            "!(copy b)",
            "|y| (copy w)",
            "!if (b) { b } else { b }",
            "x = if (b) { a } else { w }",
            "|y| if (b) { y } else { y }",
        ] {
            assert_eq!(kept(&src(range)), ["[weight = 3]"], "{range}");
        }
    }

    #[test]
    fn an_attribute_is_not_an_annotation() {
        let src = "module 0x1::m {
            #[weight = 1]
            fun f(): u64 { 0 }
            spec module { fun g(): num [weight = 2] { 1 } }
        }";
        assert_eq!(kept(src), ["[weight = 2]"]);
    }

    #[test]
    fn unmodified_source_reports_its_own_error() {
        let src =
            "module 0x1::m { fun f() { let } spec module { fun g(): num [weight = 5] { 1 } } }";
        assert_eq!(kept(src), ["<rejected>"]);
    }
}
