use std::hint::black_box;

use gungraun::prelude::*;
use ide_db::{
    LocalRoots, RootDatabase,
    symbol_index::{Query, world_symbols},
};
use salsa::Setter;
use syntax::{Edition, SourceFile, SyntaxNode};
use test_fixture::{WORKSPACE, WithFixture};

fn setup_workspace() -> (RootDatabase, Query) {
    let mut fixture = String::from("//- /lib.rs crate:main\n");
    for module in 0..32 {
        fixture.push_str(&format!("pub mod m{module};\n"));
    }
    for module in 0..32 {
        fixture.push_str(&format!("//- /m{module}.rs\n"));
        for symbol in 0..256 {
            fixture.push_str(&format!("pub fn function_{module}_{symbol}() {{}}\n"));
        }
    }

    let (mut db, _) = RootDatabase::with_many_files(&fixture);
    let mut local_roots = ide_db::FxHashSet::default();
    local_roots.insert(WORKSPACE);
    LocalRoots::get(&db).set_roots(&mut db).to(local_roots);

    let mut query = Query::new("function_0_0".to_owned());
    query.exact();
    (db, query)
}

#[library_benchmark]
#[bench::workspace(setup_workspace())]
fn workspace_symbol((db, query): (RootDatabase, Query)) -> usize {
    black_box(world_symbols(&db, query).len())
}

fn setup_ast_id_map() -> SyntaxNode {
    let mut source = String::new();
    for function in 0..1024 {
        source.push_str(&format!("fn function_{function}() {{}}\n"));
    }
    SourceFile::parse(&source, Edition::CURRENT).syntax_node().clone()
}

#[library_benchmark]
#[bench::large_file(setup_ast_id_map())]
fn ast_id_map(source: SyntaxNode) -> usize {
    black_box(span::AstIdMap::from_source(&source).len())
}

library_benchmark_group!(
    name = workspace_symbol_group,
    benchmarks = [workspace_symbol, ast_id_map]
);
main!(library_benchmark_groups = workspace_symbol_group);
