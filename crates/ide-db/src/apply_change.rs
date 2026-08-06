//! Applies changes to the IDE state transactionally.

use std::time::{Duration, Instant};

use crate::{ChangeWithProcMacros, RootDatabase};
use profile::Bytes;
use salsa::Database as _;

impl RootDatabase {
    pub fn apply_change(&mut self, change: ChangeWithProcMacros) -> Duration {
        let _p = tracing::info_span!("RootDatabase::apply_change").entered();
        let now = Instant::now();
        self.trigger_cancellation();
        let elapsed = now.elapsed();
        tracing::trace!("apply_change {:?}", change);
        change.apply(self);
        elapsed
    }

    // Feature: Memory Usage
    //
    // Reports rust-analyzer's retained Salsa query memory.
    //
    // | Editor  | Action Name |
    // |---------|-------------|
    // | VS Code | **rust-analyzer: Memory Usage**

    // ![Memory Usage](https://user-images.githubusercontent.com/48062697/113065592-08559f00-91b1-11eb-8c96-64b88068ec02.gif)
    pub fn per_query_memory_usage(&mut self) -> Vec<(String, Bytes, usize)> {
        let info = <dyn salsa::Database>::memory_usage(self);
        let mut acc = info
            .queries
            .into_iter()
            .map(|(name, info)| {
                let bytes = info.size_of_metadata()
                    + info.size_of_fields()
                    + info.heap_size_of_fields().unwrap_or_default();
                (name.to_owned(), Bytes::new(bytes as isize), info.count())
            })
            .collect::<Vec<_>>();
        acc.sort_by_key(|it| std::cmp::Reverse(it.1));
        acc
    }
}

#[cfg(test)]
mod tests {
    use test_fixture::WithFixture;

    use super::*;

    #[test]
    fn per_query_memory_usage_reports_current_salsa_queries() {
        let (db, _) =
            RootDatabase::with_many_files("//- /main.rs crate:main\nfn searched_function() {}\n");
        let mut db = db;
        let mut query = crate::symbol_index::Query::new("searched_function".to_owned());
        query.exact();
        assert_eq!(crate::symbol_index::world_symbols(&db, query).len(), 1);

        let memory = db.per_query_memory_usage();
        assert!(
            memory.iter().any(|(name, bytes, entries)| {
                name == "module_symbols" && *bytes > Bytes::new(0) && *entries > 0
            }),
            "Salsa query report did not include module_symbols: {:?}",
            memory.iter().map(|(name, _, _)| name).collect::<Vec<_>>()
        );
    }
}
