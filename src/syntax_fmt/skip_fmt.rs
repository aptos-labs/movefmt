// Copyright © Aptos Foundation
// Copyright (c) The BitsLab.MoveBit Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::core::token_tree::*;
use move_compiler::parser::ast::*;
use move_compiler::shared::ast_debug;
use move_ir_types::location::*;
use std::collections::HashSet;
use std::{cell::RefCell, sync::Arc};

use super::syntax_trait::{Preprocessor, SingleSyntaxExtractor};

#[derive(Clone, Debug, Default)]
pub struct SkipHandler {
    pub module_attributes: Vec<Vec<Attributes>>,
    pub struct_attributes: Vec<Vec<Attributes>>,
    pub fun_attributes: Vec<Vec<Attributes>>,
    pub module_body_loc_vec: Vec<Loc>,
    pub struct_body_loc_vec: Vec<Loc>,
    pub fun_body_loc_vec: Vec<Loc>,
    pub skipped_body_loc_vec: RefCell<Vec<Loc>>,
    pub module_end_set: HashSet<u32>,
    pub struct_end_set: HashSet<u32>,
    pub fun_end_set: HashSet<u32>,
    pub skipped_end_set: RefCell<HashSet<u32>>,
    pub source: String,
}

#[derive(PartialEq)]
pub enum SkipType {
    SkipModuleBody,
    SkipStructBody,
    SkipFunBody,
    SkipNone,
}

impl SingleSyntaxExtractor for SkipHandler {
    fn new(fmt_buffer: &str) -> Self {
        Self {
            module_attributes: vec![],
            struct_attributes: vec![],
            fun_attributes: vec![],
            module_body_loc_vec: vec![],
            struct_body_loc_vec: vec![],
            fun_body_loc_vec: vec![],
            skipped_body_loc_vec: vec![].into(),
            module_end_set: HashSet::new(),
            struct_end_set: HashSet::new(),
            fun_end_set: HashSet::new(),
            skipped_end_set: RefCell::new(HashSet::new()),
            source: fmt_buffer.to_string(),
        }
    }

    fn collect_seq_item(&mut self, _s: &SequenceItem) {}

    fn collect_seq(&mut self, _s: &Sequence) {}

    fn collect_spec(&mut self, _spec_block: &SpecBlock) {}

    fn collect_expr(&mut self, _e: &Exp) {}

    fn collect_const(&mut self, _c: &Constant) {}

    fn collect_struct(&mut self, s: &StructDefinition) {
        self.struct_attributes.push(s.attributes.clone());
        self.struct_body_loc_vec.push(s.loc);
        self.struct_end_set.insert(s.loc.end());
    }

    fn collect_function(&mut self, d: &Function) {
        self.fun_attributes.push(d.attributes.clone());
        self.fun_body_loc_vec.push(d.body.loc);
        self.fun_end_set.insert(d.body.loc.end());
    }

    fn collect_module(&mut self, d: &ModuleDefinition) {
        self.module_attributes.push(d.attributes.clone());
        self.module_body_loc_vec.push(d.loc);
        self.module_end_set.insert(d.loc.end());

        for m in d.members.iter() {
            match m {
                ModuleMember::Function(x) => self.collect_function(x),
                ModuleMember::Struct(x) => self.collect_struct(x),
                _ => {}
            }
        }
    }

    fn collect_script(&mut self, d: &Script) {
        self.collect_function(&d.function);
    }

    fn collect_definition(&mut self, d: &Definition) {
        match d {
            Definition::Module(x) => self.collect_module(x),
            Definition::Address(x) => {
                for x in x.modules.iter() {
                    self.collect_module(x);
                }
            }
            Definition::Script(x) => self.collect_script(x),
        }
    }
}

impl Preprocessor for SkipHandler {
    fn preprocess(&mut self, module_defs: &Arc<Vec<Definition>>) {
        for d in module_defs.iter() {
            self.collect_definition(d);
        }
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

impl SkipHandler {
    pub(crate) fn should_skip_block_body(&self, kind: &NestKind, skip_type: SkipType) -> bool {
        if skip_type == SkipType::SkipNone {
            return false;
        }

        let (body_attributes, body_loc_vec, end_set) = match skip_type {
            SkipType::SkipModuleBody => (
                &self.module_attributes,
                &self.module_body_loc_vec,
                &self.module_end_set,
            ),
            SkipType::SkipStructBody => (
                &self.struct_attributes,
                &self.struct_body_loc_vec,
                &self.struct_end_set,
            ),
            SkipType::SkipFunBody => (
                &self.fun_attributes,
                &self.fun_body_loc_vec,
                &self.fun_end_set,
            ),
            _ => return false,
        };

        let target_end = kind.end_pos + 1;
        if !end_set.contains(&target_end) {
            return false;
        }

        let len = body_loc_vec.len();
        let mut left = 0;
        let mut right = len;

        while left < right {
            let mid = left + (right - left) / 2;
            let mid_loc = body_loc_vec[mid];

            if target_end == mid_loc.end() {
                for attribute in &body_attributes[mid] {
                    let attribute_str = ast_debug::display(&attribute.value);
                    if attribute_str.contains("#[fmt::skip]") {
                        tracing::trace!("{:?}", attribute_str);
                        self.skipped_end_set.borrow_mut().insert(target_end);
                        return true;
                    }
                }
                return false;
            } else if mid_loc.start() < kind.start_pos {
                left = mid + 1;
            } else {
                right = mid;
            }
        }

        false
    }

    pub(crate) fn has_skipped_module_body(&self, kind: &NestKind) -> bool {
        self.skipped_end_set.borrow().contains(&(kind.end_pos + 1))
    }

    pub(crate) fn is_module_block(&self, kind: &NestKind) -> bool {
        kind.kind == NestKind_::Brace && self.module_end_set.contains(&(kind.end_pos + 1))
    }
}

#[allow(dead_code)]
fn get_fun_attributes(fmt_buffer: String) {
    // let buf = fmt_buffer.clone();
    // let mut result = fmt_buffer.clone();
    let skip_extractor = SkipHandler::new(&fmt_buffer);
    for attributes in skip_extractor.fun_attributes {
        for attribute in attributes {
            // ast_debug::print(&attribute.value);
            let attribute_str = ast_debug::display(&attribute.value);
            eprintln!("{:?}", attribute_str);
        }
    }
}

#[test]
fn test_get_fun_attributes() {
    get_fun_attributes(
        "
module 0x42::LambdaTest1 {  
    #[test]
    #[test(user = @0x1)]
    #[fmt::skip]
    #[test(bob = @0x345)]
    #[expected_failure(abort_code = 0x10007, location = Self)]
    /** Public inline function */  
    #[expected_failure(abort_code = 0x8000f, location = Self)]
    public inline fun inline_mul(/** Input parameter a */ a: u64,   
                                 /** Input parameter b */ b: u64)   
    /** Returns a u64 value */ : u64 {  
        /** Multiply a and b */  
        a * b  
    }  
}
"
        .to_string(),
    );
}
