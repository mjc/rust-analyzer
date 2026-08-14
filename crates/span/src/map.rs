//! A map that maps a span to every position in a file. Usually maps a span to some range of positions.
//! Allows bidirectional lookup.

use std::{fmt, hash::Hash};

use smallvec::SmallVec;
use stdx::{always, itertools::Itertools};

use crate::{
    EditionedFileId, ErasedFileAstId, ROOT_ERASED_FILE_AST_ID, Span, SpanAnchor, SyntaxContext,
    TextRange, TextSize,
};

/// Maps absolute text ranges for the corresponding file to the relevant span data.
#[derive(Clone)]
pub struct SpanMap {
    /// The offset stored here is the *end* of the node.
    spans: Vec<SpanMapEntry>,
    bases: SmallVec<[SpanMapBase; 2]>,
    /// Index of the matched macro arm on successful expansion for declarative macros.
    // FIXME: Does it make sense to have this here?
    pub matched_arm: Option<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct SpanMapEntry {
    end: TextSize,
    range: TextRange,
    base: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct SpanMapBase {
    anchor: SpanAnchor,
    ctx: SyntaxContext,
}

impl fmt::Debug for SpanMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SpanMap")
            .field("spans", &SpanMapDebug(self))
            .field("matched_arm", &self.matched_arm)
            .finish()
    }
}

struct SpanMapDebug<'a>(&'a SpanMap);

impl fmt::Debug for SpanMapDebug<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.iter()).finish()
    }
}

impl PartialEq for SpanMap {
    fn eq(&self, other: &Self) -> bool {
        self.matched_arm == other.matched_arm && self.iter().eq(other.iter())
    }
}

impl Eq for SpanMap {}

impl Hash for SpanMap {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.spans.len().hash(state);
        self.iter().for_each(|span| span.hash(state));
        self.matched_arm.hash(state);
    }
}

impl SpanMap {
    /// Creates a new empty [`SpanMap`].
    pub fn empty() -> Self {
        Self { spans: Vec::new(), bases: SmallVec::new(), matched_arm: None }
    }

    /// Finalizes the [`SpanMap`], shrinking its backing storage and validating that the offsets are
    /// in order.
    pub fn finish(&mut self) {
        always!(
            self.spans.iter().array_windows().all(|[a, b]| a.end < b.end),
            "spans are not in order"
        );
        self.spans.shrink_to_fit();
        self.bases.shrink_to_fit();
    }

    /// Pushes a new span onto the [`SpanMap`].
    pub fn push(&mut self, offset: TextSize, span: Span) {
        if cfg!(debug_assertions)
            && let Some(last) = self.spans.last()
        {
            assert!(
                last.end < offset,
                "last_offset({:?}) must be smaller than offset({offset:?})",
                last.end,
            );
        }
        let entry = self.entry(offset, span);
        self.spans.push(entry);
    }

    /// Returns all [`TextRange`]s that correspond to the given span.
    ///
    /// Note this does a linear search through the entire backing vector.
    pub fn ranges_with_span_exact(
        &self,
        span: Span,
    ) -> impl Iterator<Item = (TextRange, SyntaxContext)> + '_ {
        self.spans.iter().copied().enumerate().filter_map(move |(idx, entry)| {
            let s = self.span(entry);
            if !s.eq_ignoring_ctx(span) {
                return None;
            }
            let start = idx.checked_sub(1).map_or(TextSize::new(0), |prev| self.spans[prev].end);
            Some((TextRange::new(start, entry.end), s.ctx))
        })
    }

    /// Returns all [`TextRange`]s whose spans contain the given span.
    ///
    /// Note this does a linear search through the entire backing vector.
    pub fn ranges_with_span(
        &self,
        span: Span,
    ) -> impl Iterator<Item = (TextRange, SyntaxContext)> + '_ {
        self.spans.iter().copied().enumerate().filter_map(move |(idx, entry)| {
            let s = self.span(entry);
            if s.anchor != span.anchor {
                return None;
            }
            if !s.range.contains_range(span.range) {
                return None;
            }
            let start = idx.checked_sub(1).map_or(TextSize::new(0), |prev| self.spans[prev].end);
            Some((TextRange::new(start, entry.end), s.ctx))
        })
    }

    /// Returns the span at the given position.
    pub fn span_at(&self, offset: TextSize) -> Span {
        let entry = self.spans.partition_point(|entry| entry.end <= offset);
        self.span(self.spans[entry])
    }

    /// Returns the spans associated with the given range.
    /// In other words, this will return all spans that correspond to all offsets within the given range.
    pub fn spans_for_range(&self, range: TextRange) -> impl Iterator<Item = Span> + '_ {
        let (start, end) = (range.start(), range.end());
        let start_entry = self.spans.partition_point(|entry| entry.end <= start);
        let end_entry = self.spans[start_entry..].partition_point(|entry| entry.end <= end); // FIXME: this might be wrong?
        self.spans[start_entry..][..end_entry].iter().copied().map(|entry| self.span(entry))
    }

    pub fn iter(&self) -> impl Iterator<Item = (TextSize, Span)> + '_ {
        self.spans.iter().copied().map(|entry| (entry.end, self.span(entry)))
    }

    /// Merges this span map with another span map, where `other` is inserted at (and replaces) `other_range`.
    ///
    /// The length of the replacement node needs to be `other_size`.
    pub fn merge(&mut self, other_range: TextRange, other_size: TextSize, other: &SpanMap) {
        // I find the following diagram helpful to illustrate the bounds and why we use `<` or `<=`:
        // --------------------------------------------------------------------
        //   1   3   5   6   7   10    11          <-- offsets we store
        // 0-1 1-3 3-5 5-6 6-7 7-10 10-11          <-- ranges these offsets refer to
        //       3   ..      7                     <-- other_range
        //         3-5 5-6 6-7                     <-- ranges we replace (len = 7-3 = 4)
        //         ^^^^^^^^^^^ ^^^^^^^^^^
        //           remove       shift
        //   2   3   5   9                         <-- offsets we insert
        // 0-2 2-3 3-5 5-9                         <-- ranges we insert (other_size = 9-0 = 9)
        // ------------------------------------
        //   1   3
        // 0-1 1-3                                 <-- these remain intact
        //           5   6   8   12
        //         3-5 5-6 6-8 8-12                <-- we shift these by other_range.start() and insert them
        //                             15    16
        //                          12-15 15-16    <-- we shift these by other_size-other_range.len() = 9-4 = 5
        // ------------------------------------
        //   1   3   5   6   8   12    15    16    <-- final offsets we store
        // 0-1 1-3 3-5 5-6 6-8 8-12 12-15 15-16    <-- final ranges

        self.spans.retain_mut(|entry| {
            if other_range.start() < entry.end && entry.end <= other_range.end() {
                false
            } else {
                if entry.end > other_range.end() {
                    entry.end += other_size;
                    entry.end -= other_range.len();
                }
                true
            }
        });

        for (offset, span) in other.iter() {
            let entry = self.entry(offset + other_range.start(), span);
            self.spans.push(entry);
        }

        self.spans.sort_unstable_by_key(|entry| entry.end);

        // Matched arm info is no longer correct once we have multiple macros.
        self.matched_arm = None;
    }

    fn entry(&mut self, end: TextSize, span: Span) -> SpanMapEntry {
        let base = SpanMapBase { anchor: span.anchor, ctx: span.ctx };
        let base = self
            .spans
            .last()
            .map(|entry| entry.base)
            .filter(|&index| self.bases[index as usize] == base)
            .map(|index| index as usize)
            .or_else(|| self.bases.iter().position(|&it| it == base))
            .unwrap_or_else(|| {
                let index = self.bases.len();
                self.bases.push(base);
                index
            });
        let base = u32::try_from(base).expect("span map has more than u32::MAX distinct bases");
        SpanMapEntry { end, range: span.range, base }
    }

    fn span(&self, entry: SpanMapEntry) -> Span {
        let base = self.bases[entry.base as usize];
        Span { range: entry.range, anchor: base.anchor, ctx: base.ctx }
    }
}

#[cfg(not(no_salsa_async_drops))]
impl Drop for SpanMap {
    fn drop(&mut self) {
        let spans = std::mem::take(&mut self.spans);
        let bases = std::mem::take(&mut self.bases);
        static SPAN_MAP_DROP_THREAD: std::sync::OnceLock<
            std::sync::mpsc::Sender<(Vec<SpanMapEntry>, SmallVec<[SpanMapBase; 2]>)>,
        > = std::sync::OnceLock::new();

        SPAN_MAP_DROP_THREAD
            .get_or_init(|| {
                let (sender, receiver) =
                    std::sync::mpsc::channel::<(Vec<SpanMapEntry>, SmallVec<[SpanMapBase; 2]>)>();
                std::thread::Builder::new()
                    .name("SpanMapDropper".to_owned())
                    .spawn(move || {
                        loop {
                            // block on a receive
                            _ = receiver.recv();
                            // then drain the entire channel
                            while receiver.try_recv().is_ok() {}
                            // and sleep for a bit
                            std::thread::sleep(std::time::Duration::from_millis(100));
                        }
                        // why do this over just a `receiver.iter().for_each(drop)`? To reduce contention on the channel lock.
                        // otherwise this thread will constantly wake up and sleep again.
                    })
                    .unwrap();
                sender
            })
            .send((spans, bases))
            .unwrap();
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct RealSpanMap {
    file_id: EditionedFileId,
    /// Invariant: Sorted vec over TextSize
    // FIXME: SortedVec<(TextSize, ErasedFileAstId)>?
    pairs: Box<[(TextSize, ErasedFileAstId)]>,
    end: TextSize,
}

impl fmt::Display for RealSpanMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "RealSpanMap({:?}):", self.file_id)?;
        for span in self.pairs.iter() {
            writeln!(f, "{}: {:#?}", u32::from(span.0), span.1)?;
        }
        Ok(())
    }
}

impl RealSpanMap {
    /// Creates a real file span map that returns absolute ranges (relative ranges to the root ast id).
    pub fn absolute(file_id: EditionedFileId) -> Self {
        RealSpanMap {
            file_id,
            pairs: Box::from([(TextSize::new(0), ROOT_ERASED_FILE_AST_ID)]),
            end: TextSize::new(!0),
        }
    }

    pub fn from_file(
        file_id: EditionedFileId,
        pairs: Box<[(TextSize, ErasedFileAstId)]>,
        end: TextSize,
    ) -> Self {
        Self { file_id, pairs, end }
    }

    #[cfg(feature = "salsa")]
    pub fn span_for_range(&self, range: TextRange) -> Span {
        assert!(
            range.end() <= self.end,
            "range {range:?} goes beyond the end of the file {:?}",
            self.end
        );
        let start = range.start();
        let idx = self
            .pairs
            .binary_search_by(|&(it, _)| it.cmp(&start).then(std::cmp::Ordering::Less))
            .unwrap_err();
        let (offset, ast_id) = self.pairs[idx - 1];
        Span {
            range: range - offset,
            anchor: crate::SpanAnchor { file_id: self.file_id, ast_id },
            ctx: SyntaxContext::root(self.file_id.edition()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Edition, FileId, SpanAnchor};

    #[test]
    fn repeated_span_bases_use_compact_storage() {
        assert!(std::mem::size_of::<SpanMapEntry>() < std::mem::size_of::<(TextSize, Span)>());

        let anchor = SpanAnchor {
            file_id: EditionedFileId::current_edition(FileId::from_raw(0)),
            ast_id: ROOT_ERASED_FILE_AST_ID,
        };
        let ctx = SyntaxContext::root(Edition::CURRENT);
        let spans = [
            Span { range: TextRange::new(0.into(), 1.into()), anchor, ctx },
            Span { range: TextRange::new(1.into(), 3.into()), anchor, ctx },
            Span { range: TextRange::new(3.into(), 6.into()), anchor, ctx },
        ];
        let mut map = SpanMap::empty();
        for (end, span) in [1, 3, 6].into_iter().zip(spans) {
            map.push(end.into(), span);
        }
        map.finish();

        assert_eq!(map.bases.len(), 1);
        assert_eq!(
            map.iter().collect::<Vec<_>>(),
            [(1.into(), spans[0]), (3.into(), spans[1]), (6.into(), spans[2])]
        );
        assert_eq!(map.span_at(2.into()), spans[1]);

        let mut with_unused_base = SpanMap::empty();
        with_unused_base.push(
            1.into(),
            Span {
                anchor: SpanAnchor {
                    file_id: EditionedFileId::current_edition(FileId::from_raw(1)),
                    ..anchor
                },
                ..spans[0]
            },
        );
        with_unused_base.merge(TextRange::new(0.into(), 1.into()), 6.into(), &map);
        assert_eq!(with_unused_base, map);

        let hash = |map: &SpanMap| {
            let mut hasher = std::hash::DefaultHasher::new();
            map.hash(&mut hasher);
            std::hash::Hasher::finish(&hasher)
        };
        assert_eq!(hash(&with_unused_base), hash(&map));
    }
}
