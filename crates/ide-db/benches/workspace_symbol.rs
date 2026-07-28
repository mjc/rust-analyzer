use std::hint::black_box;

use gungraun::prelude::*;
use ide_db::{
    LocalRoots, RootDatabase,
    symbol_index::{Query, world_symbols},
};
use salsa::Setter;
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

library_benchmark_group!(name = workspace_symbol_group, benchmarks = workspace_symbol);
main!(library_benchmark_groups = workspace_symbol_group);
