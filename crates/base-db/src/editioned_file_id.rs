//! Defines [`EditionedFileId`], an interned wrapper around [`span::EditionedFileId`] that
//! is interned (so queries can take it) and stores only the underlying `span::EditionedFileId`.

use std::hash::Hash;

use salsa::Database;
use span::Edition;
use syntax::{SyntaxError, ast};
use vfs::FileId;

use crate::SourceDatabase;

#[salsa::interned(debug, constructor = from_span_file_id, no_lifetime)]
#[derive(PartialOrd, Ord)]
pub struct EditionedFileId {
    field: span::EditionedFileId,
}

#[salsa::tracked(lru = 64, self_ty = EditionedFileId)]
fn parse(db: &dyn SourceDatabase, file: EditionedFileId) -> syntax::Parse<ast::SourceFile> {
    let _p = tracing::info_span!("parse", ?file).entered();
    let (file_id, edition) = file.unpack(db);
    let text = db.file_text(file_id).text(db);
    ast::SourceFile::parse_with_shared_cache(text, edition)
}

#[salsa::tracked]
impl EditionedFileId {
    // firewall query
    #[salsa::tracked(returns(as_deref))]
    pub fn parse_errors(self, db: &dyn SourceDatabase) -> Option<Box<[SyntaxError]>> {
        let errors = self.parse(db).errors();
        match &*errors {
            [] => None,
            [..] => Some(errors.into()),
        }
    }
}

impl EditionedFileId {
    /// Set the retained syntax-tree parse capacity for this database.
    pub fn set_parse_lru_capacity(db: &mut dyn SourceDatabase, capacity: usize) {
        parse::set_lru_capacity(db, capacity);
    }

    pub fn parse(self, db: &dyn SourceDatabase) -> syntax::Parse<ast::SourceFile> {
        parse(db, self)
    }

    #[inline]
    pub fn new(db: &dyn Database, file_id: FileId, edition: Edition) -> Self {
        Self::from_span_file_id(db, span::EditionedFileId::new(file_id, edition))
    }

    #[inline]
    pub fn current_edition(db: &dyn Database, file_id: FileId) -> Self {
        Self::from_span_file_id(db, span::EditionedFileId::current_edition(file_id))
    }

    #[inline]
    pub fn file_id(self, db: &dyn Database) -> vfs::FileId {
        self.field(db).file_id()
    }

    #[inline]
    pub fn span_file_id(self, db: &dyn Database) -> span::EditionedFileId {
        self.field(db)
    }

    #[inline]
    pub fn unpack(self, db: &dyn Database) -> (vfs::FileId, span::Edition) {
        self.field(db).unpack()
    }

    #[inline]
    pub fn edition(self, db: &dyn Database) -> Edition {
        self.field(db).edition()
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fmt, panic,
        sync::{Arc as StdArc, Mutex},
    };

    use salsa::{Database as _, Durability};
    use span::TextSize;
    use triomphe::Arc;
    use vfs::FileId;

    use super::EditionedFileId;
    use crate::{
        CratesMap, FileSourceRootInput, Files, Nonce, SourceDatabase, SourceRoot, SourceRootId,
        SourceRootInput,
    };

    #[salsa::db]
    struct TestDb {
        storage: salsa::Storage<Self>,
        files: Arc<Files>,
        crates_map: Arc<CratesMap>,
        events: StdArc<Mutex<Vec<salsa::Event>>>,
        nonce: Nonce,
    }

    impl Default for TestDb {
        fn default() -> Self {
            let events = StdArc::new(Mutex::new(Vec::new()));
            let callback_events = events.clone();
            Self {
                storage: salsa::Storage::new(Some(Box::new(move |event| {
                    callback_events.lock().unwrap().push(event);
                }))),
                files: Default::default(),
                crates_map: Default::default(),
                events,
                nonce: Nonce::new(),
            }
        }
    }

    impl Clone for TestDb {
        fn clone(&self) -> Self {
            Self {
                storage: self.storage.clone(),
                files: self.files.clone(),
                crates_map: self.crates_map.clone(),
                events: self.events.clone(),
                nonce: self.nonce,
            }
        }
    }

    #[salsa::db]
    impl salsa::Database for TestDb {}

    impl fmt::Debug for TestDb {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("TestDb").finish()
        }
    }

    impl panic::RefUnwindSafe for TestDb {}

    #[salsa::db]
    impl SourceDatabase for TestDb {
        fn file_text(&self, file_id: FileId) -> crate::FileText {
            self.files.file_text(file_id)
        }

        fn set_file_text(&mut self, file_id: FileId, text: &str) {
            let files = self.files.clone();
            files.set_file_text(self, file_id, text);
        }

        fn set_file_text_with_durability(
            &mut self,
            file_id: FileId,
            text: &str,
            durability: Durability,
        ) {
            let files = self.files.clone();
            files.set_file_text_with_durability(self, file_id, text, durability);
        }

        fn source_root(&self, _: SourceRootId) -> SourceRootInput {
            panic!("source roots are not needed by this test")
        }

        fn file_source_root(&self, _: FileId) -> FileSourceRootInput {
            panic!("source roots are not needed by this test")
        }

        fn set_file_source_root_with_durability(
            &mut self,
            _: FileId,
            _: SourceRootId,
            _: Durability,
        ) {
            panic!("source roots are not needed by this test")
        }

        fn set_source_root_with_durability(
            &mut self,
            _: SourceRootId,
            _: Arc<SourceRoot>,
            _: Durability,
        ) {
            panic!("source roots are not needed by this test")
        }

        fn crates_map(&self) -> Arc<CratesMap> {
            self.crates_map.clone()
        }

        fn nonce_and_revision(&self) -> (Nonce, salsa::Revision) {
            (self.nonce, salsa::plumbing::ZalsaDatabase::zalsa(self).current_revision())
        }

        fn line_column(&self, _: FileId, _: TextSize) -> Result<(u32, u32), ()> {
            Err(())
        }
    }

    impl TestDb {
        fn executed(&self, f: impl FnOnce()) -> Vec<String> {
            self.events.lock().unwrap().clear();
            f();
            self.events
                .lock()
                .unwrap()
                .drain(..)
                .filter_map(|event| match event.kind {
                    salsa::EventKind::WillExecute { database_key } => Some(
                        (self as &dyn salsa::Database)
                            .ingredient_debug_name(database_key.ingredient_index())
                            .to_string(),
                    ),
                    _ => None,
                })
                .collect()
        }
    }

    #[test]
    fn parse_lru_capacity_evicts_old_syntax_trees() {
        let mut db = TestDb::default();
        let first_file = FileId::from_raw(0);
        let second_file = FileId::from_raw(1);
        db.set_file_text(first_file, "fn first() {}\n");
        db.set_file_text(second_file, "fn second() {}\n");
        let first = EditionedFileId::current_edition(&db, first_file);
        let second = EditionedFileId::current_edition(&db, second_file);

        EditionedFileId::set_parse_lru_capacity(&mut db, 1);
        assert_eq!(
            db.executed(|| {
                first.parse(&db);
                second.parse(&db);
            })
            .into_iter()
            .filter(|name| name == "EditionedFileId::parse")
            .count(),
            2
        );

        db.trigger_lru_eviction();
        assert_eq!(
            db.executed(|| {
                first.parse(&db);
            })
            .into_iter()
            .filter(|name| name == "EditionedFileId::parse")
            .count(),
            1
        );
    }
}
