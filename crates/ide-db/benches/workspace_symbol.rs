//! Instruction and allocation benchmarks for retained syntax and workspace symbol indexing.

use std::{fmt::Write, hint::black_box, sync::Once};

use gungraun::{Dhat, prelude::*};
use hir::{Crate, Module};
use ide_db::base_db::SourceDatabase;
use ide_db::{
    LocalRoots, RootDatabase,
    symbol_index::{Query, SymbolIndex, world_symbols},
};
use rayon::ThreadPoolBuilder;
use rowan::{GreenToken, SyntaxKind};
use rustc_hash::{FxHashMap, FxHashSet};
use salsa::Setter;
use syntax::{Edition, GreenNode, SourceFile, SyntaxNode, TextSize};
use syntax_bridge::{
    DocCommentDesugarMode,
    dummy_test_span_utils::{DUMMY, DummyTestSpanMap},
    parse_to_token_tree_static_span, syntax_node_to_token_tree, syntax_node_to_token_tree_modified,
    token_tree_to_syntax_node,
};
use test_fixture::{WORKSPACE, WithFixture};

fn init_single_thread_rayon() {
    static RAYON: Once = Once::new();
    RAYON.call_once(|| {
        ThreadPoolBuilder::new().num_threads(1).use_current_thread().build_global().unwrap()
    });
}

fn setup_workspace_fixture() -> String {
    init_single_thread_rayon();
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
    fixture
}

fn workspace(fixture: &str) -> (RootDatabase, Query) {
    let (mut db, _) = RootDatabase::with_many_files(fixture);
    let mut local_roots = ide_db::FxHashSet::default();
    local_roots.insert(WORKSPACE);
    LocalRoots::get(&db).set_roots(&mut db).to(local_roots);

    let mut query = Query::new("function_0_0".to_owned());
    query.exact();
    (db, query)
}

fn setup_workspace() -> (RootDatabase, Query) {
    workspace(&setup_workspace_fixture())
}

fn setup_file_text_fixture() -> String {
    let mut fixture = String::new();
    for file in 0..128 {
        if file == 0 {
            writeln!(fixture, "//- /lib.rs crate:main new_source_root:library").unwrap();
        } else {
            writeln!(fixture, "//- /file_{file}.rs").unwrap();
        }
        for item in 0..128 {
            writeln!(
                fixture,
                "pub fn function_{file}_{item}() -> usize {{ let value = {file} + {item}; value }}"
            )
            .unwrap();
        }
    }
    fixture
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::rust_sources(setup_file_text_fixture())]
fn retain_file_texts(fixture: String) -> (RootDatabase, usize) {
    let (db, files) = RootDatabase::with_many_files(black_box(&fixture));
    let retained_bytes =
        files.into_iter().map(|file| db.file_text(file.file_id(&db)).text(&db).len()).sum();
    black_box((db, retained_bytes))
}

fn setup_named_item_tree_fixture() -> String {
    let mut fixture = String::from("//- /lib.rs crate:main\n");
    for item in 0..4096 {
        fixture.push_str(&format!("pub const ITEM_{item}: () = ();\n"));
    }
    fixture
}

fn setup_filtered_attr_item_tree_fixture() -> String {
    init_single_thread_rayon();
    let mut fixture = String::from("//- /lib.rs crate:main\n");
    for item in 0..4096 {
        fixture
            .push_str(&format!("#[allow(dead_code)]\npub const FILTERED_ITEM_{item}: () = ();\n"));
    }
    fixture
}

fn setup_token_tree_attr_item_tree_fixture() -> String {
    init_single_thread_rayon();
    let mut fixture = String::from("//- /lib.rs crate:main\n");
    for item in 0..1024 {
        fixture.push_str(&format!(
            "#[custom(foo, bar = \"baz\")]\npub const ATTR_ITEM_{item}: () = ();\n"
        ));
    }
    fixture
}

fn setup_large_symbol_index() -> (RootDatabase, Module) {
    init_single_thread_rayon();
    let mut fixture = String::from("//- /lib.rs crate:main\n");
    for symbol in 0..8192 {
        fixture.push_str(&format!("pub fn Function_{symbol}() {{}}\n"));
    }
    let (db, _) = workspace(&fixture);
    let module = Crate::all(&db).into_iter().next().unwrap().root_module(&db);
    black_box(module.declarations(&db).len());
    (db, module)
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::workspace(setup_workspace())]
fn workspace_symbol((db, query): (RootDatabase, Query)) -> usize {
    black_box(world_symbols(&db, query).len())
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::workspace(setup_workspace_fixture())]
fn build_workspace_symbol(fixture: String) -> usize {
    let (db, query) = workspace(black_box(&fixture));
    let modules =
        Crate::all(&db).into_iter().flat_map(|krate| krate.modules(&db)).collect::<Vec<_>>();
    let declarations = modules.iter().map(|module| module.declarations(&db).len()).sum::<usize>();
    let scope_items = modules.iter().map(|module| module.scope(&db, None).len()).sum::<usize>();
    assert_eq!(modules.len(), 33);
    assert_eq!(declarations, 32 * 257);
    assert_eq!(scope_items, 32 * 257);
    black_box(modules.len() + declarations + scope_items + world_symbols(&db, query).len())
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::large_module(setup_large_symbol_index())]
fn build_module_symbol_index((db, module): (RootDatabase, Module)) -> usize {
    black_box(SymbolIndex::module_symbols(&db, module).len())
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::named_consts(setup_named_item_tree_fixture())]
fn build_named_item_tree(fixture: String) -> usize {
    let (db, _) = RootDatabase::with_many_files(black_box(&fixture));
    let declarations = Crate::all(&db)
        .into_iter()
        .flat_map(|krate| krate.modules(&db))
        .flat_map(|module| module.declarations(&db));
    black_box(declarations.count())
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::filtered_attrs(setup_filtered_attr_item_tree_fixture())]
fn build_filtered_attr_item_tree(fixture: String) -> usize {
    let (db, _) = RootDatabase::with_many_files(black_box(&fixture));
    let declarations = Crate::all(&db)
        .into_iter()
        .flat_map(|krate| krate.modules(&db))
        .flat_map(|module| module.declarations(&db));
    black_box(declarations.count())
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::token_tree_attrs(setup_token_tree_attr_item_tree_fixture())]
fn build_token_tree_attr_item_tree(fixture: String) -> usize {
    let (db, _) = RootDatabase::with_many_files(black_box(&fixture));
    let declarations = Crate::all(&db)
        .into_iter()
        .flat_map(|krate| krate.modules(&db))
        .flat_map(|module| module.declarations(&db));
    black_box(declarations.count())
}

fn setup_ast_id_map() -> SyntaxNode {
    let mut source = String::new();
    for function in 0..1024 {
        source.push_str(&format!("fn function_{function}() {{}}\n"));
    }
    SourceFile::parse(&source, Edition::CURRENT).syntax_node().clone()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::large_file(setup_ast_id_map())]
fn ast_id_map(source: SyntaxNode) -> usize {
    black_box(span::AstIdMap::from_source(&source).len())
}

fn setup_tiny_ast_id_maps() -> Vec<SyntaxNode> {
    (0..1024)
        .map(|function| {
            SourceFile::parse(&format!("fn function_{function}() {{}}"), Edition::CURRENT)
                .syntax_node()
                .clone()
        })
        .collect()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::tiny_files(setup_tiny_ast_id_maps())]
fn tiny_ast_id_maps(sources: Vec<SyntaxNode>) -> usize {
    black_box(sources.iter().map(|source| span::AstIdMap::from_source(source).len()).sum())
}

fn setup_nested_ast_id_map() -> SyntaxNode {
    let mut source = String::new();
    for module in 0..32 {
        source.push_str(&format!("mod module_{module} {{\n"));
        for function in 0..32 {
            source.push_str(&format!("fn function_{module}_{function}() {{}}\n"));
        }
        source.push_str("}\n");
    }
    SourceFile::parse(&source, Edition::CURRENT).syntax_node().clone()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::nested_modules(setup_nested_ast_id_map())]
fn nested_ast_id_map(source: SyntaxNode) -> usize {
    black_box(span::AstIdMap::from_source(&source).len())
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::nested_tree(setup_nested_ast_id_map())]
fn syntax_cursor_traversal(source: SyntaxNode) -> usize {
    black_box(
        source
            .descendants_with_tokens()
            .map(|element| {
                let range = element.text_range();
                u32::from(range.start()) as usize + u32::from(range.end()) as usize
            })
            .sum(),
    )
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::nested_tree(setup_nested_ast_id_map())]
fn syntax_token_at_offset(source: SyntaxNode) -> usize {
    let len = u32::from(source.text_range().len());
    black_box(
        (0..len)
            .step_by(16)
            .filter_map(|offset| source.token_at_offset(TextSize::from(offset)).left_biased())
            .map(|token| u32::from(token.text_range().start()) as usize)
            .sum(),
    )
}

fn setup_tiny_sources() -> Vec<String> {
    (0..1024).map(|index| format!("fn f{index}() {{ let value = (); }}")).collect()
}

fn setup_green_nodes_for_drop() -> Vec<GreenNode> {
    (0..16_384).map(|_| GreenNode::new(SyntaxKind(0), [])).collect()
}

fn setup_wide_green_token() -> GreenToken {
    GreenToken::new(SyntaxKind(0), &"x".repeat(70_000))
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::owned_nodes(setup_green_nodes_for_drop())]
fn drop_green_nodes(nodes: Vec<GreenNode>) -> usize {
    let len = nodes.len();
    drop(black_box(nodes));
    black_box(len)
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::wide_text(setup_wide_green_token())]
fn wide_green_token_access(token: GreenToken) -> usize {
    black_box(
        (0..4096)
            .map(|_| {
                let token = black_box(&token);
                black_box(token.text()).len() + u32::from(black_box(token.text_len())) as usize
            })
            .sum(),
    )
}

fn setup_indented_sources() -> Vec<String> {
    (0..1024)
        .map(|index| {
            format!(
                "fn f{index}() {{\n    if true {{\n        let value = ();\n    }}\n\n    let other = ();\n}}\n"
            )
        })
        .collect()
}

fn setup_raw_string_sources(payload: &str) -> Vec<String> {
    (0..256).map(|index| format!("const VALUE_{index}: &str = r#\"{payload}\"#;\n")).collect()
}

fn setup_empty_raw_string_sources() -> Vec<String> {
    setup_raw_string_sources("")
}

fn setup_text_heavy_sources() -> Vec<String> {
    setup_raw_string_sources(&"x".repeat(4096))
}

fn setup_shared_cache_churn_sources() -> Vec<String> {
    (0..4096)
        .map(|file| {
            let mut source = String::new();
            for item in 0..64 {
                writeln!(
                    source,
                    "pub fn function_{file}_{item}() -> usize {{ let value_{file}_{item} = {file} + {item}; value_{file}_{item} }}"
                )
                .unwrap();
            }
            source
        })
        .collect()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::tiny_files(setup_tiny_sources())]
#[bench::indented_files(setup_indented_sources())]
fn parse_source_files(sources: Vec<String>) -> usize {
    sources
        .iter()
        .map(|source| {
            u32::from(
                SourceFile::parse(black_box(source), Edition::CURRENT).syntax_node().text().len(),
            ) as usize
        })
        .sum()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::tiny_files(setup_tiny_sources())]
#[bench::empty_raw_string_files(setup_empty_raw_string_sources())]
#[bench::text_heavy_files(setup_text_heavy_sources())]
fn retain_parsed_source_files(sources: Vec<String>) -> (Vec<String>, Vec<SyntaxNode>) {
    let syntax_trees = sources
        .iter()
        .map(|source| SourceFile::parse(black_box(source), Edition::CURRENT).syntax_node().clone())
        .collect();
    black_box((sources, syntax_trees))
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::tiny_files(setup_tiny_sources())]
#[bench::empty_raw_string_files(setup_empty_raw_string_sources())]
#[bench::text_heavy_files(setup_text_heavy_sources())]
fn retain_shared_parsed_source_files(sources: Vec<String>) -> (Vec<String>, Vec<SyntaxNode>) {
    let syntax_trees = sources
        .iter()
        .map(|source| {
            SourceFile::parse_with_shared_cache(black_box(source), Edition::CURRENT)
                .syntax_node()
                .clone()
        })
        .collect();
    black_box((sources, syntax_trees))
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::many_unique_files(setup_shared_cache_churn_sources())]
fn fill_shared_parse_cache(sources: Vec<String>) -> usize {
    let parsed_bytes = black_box(
        sources
            .iter()
            .map(|source| {
                u32::from(
                    SourceFile::parse_with_shared_cache(black_box(source), Edition::CURRENT)
                        .syntax_node()
                        .text_range()
                        .len(),
                ) as usize
            })
            .sum(),
    );
    syntax::clear_shared_parse_cache();
    parsed_bytes
}

fn setup_populated_shared_parse_cache() -> usize {
    setup_tiny_sources()
        .iter()
        .map(|source| {
            u32::from(
                SourceFile::parse_with_shared_cache(source, Edition::CURRENT)
                    .syntax_node()
                    .text_range()
                    .len(),
            ) as usize
        })
        .sum()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::tiny_files(setup_populated_shared_parse_cache())]
fn clear_shared_parse_cache(parsed_bytes: usize) -> usize {
    syntax::clear_shared_parse_cache();
    black_box(parsed_bytes)
}

fn setup_macro_token_tree() -> tt::TopSubtree {
    let mut source = String::new();
    for function in 0..256 {
        source.push_str(&format!(
            "fn function_{function}() {{ let value_{function} = ({function}, {function}); }}\n"
        ));
    }
    parse_to_token_tree_static_span(Edition::CURRENT, DUMMY, &source).unwrap()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::large_expansion(setup_macro_token_tree())]
fn token_tree_to_syntax(token_tree: tt::TopSubtree) -> usize {
    (0..64)
        .map(|_| {
            let (parse, span_map) = token_tree_to_syntax_node(
                black_box(&token_tree),
                parser::TopEntryPoint::SourceFile,
                &mut |_| Edition::CURRENT,
            );
            u32::from(parse.syntax_node().text_range().len()) as usize + span_map.iter().count()
        })
        .sum()
}

fn setup_shared_attr_syntax_nodes() -> Vec<SyntaxNode> {
    let source = "#[custom(foo, bar = \"baz\")]\nfn item<'a>() { let _ = a::b::<1>(); }\n";
    (0..1024)
        .map(|_| {
            SourceFile::parse_with_shared_cache(source, Edition::CURRENT).syntax_node().clone()
        })
        .collect()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::shared_trees(setup_shared_attr_syntax_nodes())]
fn syntax_to_token_tree_green(nodes: Vec<SyntaxNode>) -> usize {
    nodes
        .iter()
        .map(|node| {
            syntax_node_to_token_tree(
                black_box(node),
                DummyTestSpanMap,
                DUMMY,
                DocCommentDesugarMode::ProcMacro,
            )
            .as_token_trees()
            .len()
        })
        .sum()
}

#[library_benchmark(config = LibraryBenchmarkConfig::default().tool(Dhat::default()))]
#[bench::shared_trees(setup_shared_attr_syntax_nodes())]
fn syntax_to_token_tree_event(nodes: Vec<SyntaxNode>) -> usize {
    nodes
        .iter()
        .map(|node| {
            syntax_node_to_token_tree_modified(
                black_box(node),
                DummyTestSpanMap,
                FxHashMap::default(),
                FxHashSet::default(),
                DUMMY,
                DocCommentDesugarMode::ProcMacro,
                |_, _| (true, Vec::new()),
            )
            .as_token_trees()
            .len()
        })
        .sum()
}

library_benchmark_group!(
    name = workspace_symbol_group,
    benchmarks = [
        workspace_symbol,
        build_workspace_symbol,
        build_module_symbol_index,
        retain_file_texts,
        build_named_item_tree,
        build_filtered_attr_item_tree,
        build_token_tree_attr_item_tree,
        ast_id_map,
        tiny_ast_id_maps,
        nested_ast_id_map,
        syntax_cursor_traversal,
        syntax_token_at_offset,
        drop_green_nodes,
        wide_green_token_access,
        parse_source_files,
        retain_parsed_source_files,
        retain_shared_parsed_source_files,
        fill_shared_parse_cache,
        clear_shared_parse_cache,
        token_tree_to_syntax,
        syntax_to_token_tree_green,
        syntax_to_token_tree_event
    ]
);
main!(library_benchmark_groups = workspace_symbol_group);
