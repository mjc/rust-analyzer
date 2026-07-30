//! Instruction and allocation benchmarks for attribute lowering.

use std::{convert::Infallible, hint::black_box, ops::ControlFlow};

use cfg::CfgOptions;
use gungraun::{Dhat, prelude::*};
use hir_expand::attrs::collect_item_tree_attrs;
use syntax::{
    AstNode, Edition, SourceFile,
    ast::{self, HasAttrs},
};

fn setup_filtered_attrs() -> Vec<ast::Fn> {
    let mut source = String::new();
    for item in 0..4096 {
        source.push_str(&format!("#[allow(dead_code)]\nfn filtered_item_{item}() {{}}\n"));
    }
    SourceFile::parse(&source, Edition::CURRENT)
        .syntax_node()
        .descendants()
        .filter_map(ast::Fn::cast)
        .collect()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::filtered_attrs(setup_filtered_attrs())]
fn filter_item_tree_attrs(items: Vec<ast::Fn>) -> usize {
    let cfg_options = CfgOptions::default();
    let mut retained = 0;
    for item in black_box(&items) {
        let result = collect_item_tree_attrs::<Infallible>(
            item as &dyn HasAttrs,
            || &cfg_options,
            |_, _| {
                retained += 1;
                ControlFlow::Continue(())
            },
        );
        assert!(result.is_none());
    }
    black_box(retained)
}

library_benchmark_group!(name = attrs_group, benchmarks = [filter_item_tree_attrs]);
main!(library_benchmark_groups = attrs_group);
