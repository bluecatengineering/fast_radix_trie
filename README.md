# fast_radix_tree

================

[![fast_radix_tree](https://img.shields.io/crates/v/fast_radix_tree.svg)](https://crates.io/crates/fast_radix_tree)
[![Documentation](https://docs.rs/fast_radix_tree/badge.svg)](https://docs.rs/fast_radix_tree)
[![Actions Status](https://github.com/sile/fast_radix_tree/workflows/CI/badge.svg)](https://github.com/sile/fast_radix_tree/actions)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

Memory-efficient data structures based on radix tree. Offers two impls, one optimized for absolute minimum memory usage (minimizing padding/alignment where possible), and one optimized for mutations that uses `realloc`.

Originally based on [fast_radix_tree](https://github.com/sile/fast_radix_tree), but whereas patricia tree uses a child/sibling pointer for each node, where siblings are traversed in a linked list to find nodes at the same level, this radix tree stores children nodes directly inline for faster traversal. It costs a small bit more memory, around 5-10% depending on the data set, but can be up to 4x faster to build or traverse the data structure. Moreso if you use the `realloc` impl which can speed up mutations by resizing nodes instead of allocating new ones.

This library uses unsafe and raw pointers ubiquitously because nodes are dynamically sized to store node labels and children pointers at dynamic offsets inline in each node allocation. By doing this we can drastically reduce memory usage.

[Documentation](https://docs.rs/fast_radix_tree)

A radix tree compresses nodes such that common prefixes are shared. This minimizes memory usage for storing large sets of strings/bytes. Additionally, this library tries to optimize memory layout/padding to further reduce memory consumption, leading to significant memory savings and fast traversal time for large data sets. Memory usage can be dramatically less than storing in std's HashMap or BTreeMap.

See [Radix tree](https://en.wikipedia.org/wiki/Radix_tree) for more details.

## Examples

```rust
use fast_radix_tree::RadixTree;

let mut map = RadixTree::new();
map.insert("foo", 1);
map.insert("bar", 2);
map.insert("baz", 3);
assert_eq!(map.len(), 3);

assert_eq!(map.get("foo"), Some(&1));
assert_eq!(map.get("bar"), Some(&2));
assert_eq!(map.get("baz"), Some(&3));
```

## Benchmarks

```console
$ cargo run --example insert_lines --release -- --version 2> /dev/null
insert_lines 0.1.0

///
/// INPUT: Wikipedia
///
$ curl -s https://dumps.wikimedia.org/enwiki/latest/enwiki-latest-all-titles-in-ns0.gz | gzip -d > enwiki-latest-all-titles-in-ns0
$ du -hs enwiki-latest-all-titles-in-ns0
271M    enwiki-latest-all-titles-in-ns0

// HashSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind hash < enwiki-latest-all-titles-in-ns0
# LINES: 13450823
# ELAPSED: 0:10.23
# MEMORY: 1001548  // 978 MB

// BTreeSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind btree < enwiki-latest-all-titles-in-ns0
# LINES: 13450823
# ELAPSED: 0:10.90
# MEMORY: 1112068  // 1,086 MB

// PatriciaSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind patricia < enwiki-latest-all-titles-in-ns0
# LINES: 13450823
# ELAPSED: 1:12.55
# MEMORY: 434340   // 424 MB

///
/// INPUT: Google 5-gram
///
$ curl -s http://storage.googleapis.com/books/ngrams/books/googlebooks-eng-all-5gram-20120701-0.gz | gzip -d > googlebooks-eng-all-5gram-20120701-0
$ du -hs googlebooks-eng-all-5gram-20120701-0
331M    googlebooks-eng-all-5gram-20120701-0

// HashSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind hash < googlebooks-eng-all-5gram-20120701-0
# LINES: 9814743
# ELAPSED: 0:08.36
# MEMORY: 1115544  // 1,089 MB

// BTreeSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind btree < googlebooks-eng-all-5gram-20120701-0
# LINES: 9814743
# ELAPSED: 0:06.85
# MEMORY: 942236   // 920 MB

// PatriciaSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind patricia < googlebooks-eng-all-5gram-20120701-0
# LINES: 9814743
# ELAPSED: 0:25.62
# MEMORY: 223616   // 218 MB
```
