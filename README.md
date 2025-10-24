# fast_radix_tree

================

[![fast_radix_tree](https://img.shields.io/crates/v/fast_radix_tree.svg)](https://crates.io/crates/fast_radix_tree)
[![Documentation](https://docs.rs/fast_radix_tree/badge.svg)](https://docs.rs/fast_radix_tree)
[![Actions Status](https://github.com/bluecatengineering/fast_radix_tree/workflows/CI/badge.svg)](https://github.com/bluecatengineering/fast_radix_tree/actions)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

Memory-efficient data structures based on radix tree. Offers two impls, one optimized for absolute minimum memory usage (minimizing padding/alignment where possible), and one optimized for mutations that uses `realloc`.

Originally based on [fast_radix_tree](https://github.com/bluecatengineering/fast_radix_tree), but whereas patricia tree uses a child/sibling pointer for each node, where siblings are traversed in a linked list to find nodes at the same level, this radix tree stores children nodes directly inline for faster traversal. It costs a small bit more memory, around 5-10% depending on the data set, but can be up to 4x faster to build or traverse the data structure. Moreso if you use the `realloc` impl which can speed up mutations by resizing nodes instead of allocating new ones.

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

Run `cargo bench` for results, but the performance for retrieval/removal is on par or better in some cases than hashmap/btreemap from std.

However, the library offers significant memory savings over the std data structures:(j)

```console
$ cargo run --example insert_lines --release -- --version 2> /dev/null
insert_lines 0.1.0

///
/// INPUT: Wikipedia
///
$ curl -s https://dumps.wikimedia.org/enwiki/latest/enwiki-latest-all-titles-in-ns0.gz | gzip -d > enwiki-latest-all-titles-in-ns0
$ du -hs enwiki-latest-all-titles-in-ns0
387M    enwiki-latest-all-titles-in-ns0

// HashSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind hash < enwiki-latest-all-titles-in-ns0
# LINES: 18509089
# ELAPSED: 0:08.14
# MEMORY: 1784336 // 1,784 MB

// BTreeSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind btree < enwiki-latest-all-titles-in-ns0
# LINES: 18509089
# ELAPSED: 0:04.45
# MEMORY: 1607680 // 1,607 MB

// RadixSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --example insert_lines --release -- --kind patricia < enwiki-latest-all-titles-in-ns0
# LINES: 18509089
# ELAPSED: 0:04.59
# MEMORY: 905360 // 905 MB (for reference sile's original code takes 20s and 850 MB on the same set)
```

with the top 1 million domains:

```console
$ du -sh top-1000000-domains
15M top-1000000-domains

// HashSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --no-default-features --example insert_lines --release -- --kind radix < top-1000000-domains
# LINES: 1000000
# ELAPSED: 0:00.30
# MEMORY: 108324 // 108 MB

// BTreeSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --no-default-features --example insert_lines --release -- --kind radix < top-1000000-domains
# LINES: 1000000
# ELAPSED: 0:00.48
# MEMORY: 73412 // 73 MB

// RadixSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --no-default-features --example insert_lines --release -- --kind radix < top-1000000-domains
# LINES: 1000000
# ELAPSED: 0:00.45
# MEMORY: 51820 // 51 MB
```

`cargo bench` results

```

Benchmarking insertion/RadixSet: Collecting 100 samples in estimated 5.0008 s (12M iinsertion/RadixSet      time:   [231.26 ns 238.41 ns 244.68 ns]
                        change: [−9.9600% −3.5885% +3.1847%] (p = 0.29 > 0.05)
                        No change in performance detected.
Benchmarking insertion/HashSet: Collecting 100 samples in estimated 5.0001 s (14M itinsertion/HashSet       time:   [83.052 ns 87.479 ns 91.939 ns]
                        change: [−99.089% +8.3219% +12010%] (p = 0.84 > 0.05)
                        No change in performance detected.
Found 6 outliers among 100 measurements (6.00%)
  4 (4.00%) high mild
  2 (2.00%) high severe
Benchmarking insertion/BTreeSet: Collecting 100 samples in estimated 5.0022 s (8.2M insertion/BTreeSet      time:   [343.38 ns 358.40 ns 371.50 ns]
                        change: [+2.9753% +9.7439% +17.069%] (p = 0.01 < 0.05)
                        Performance has regressed.

Benchmarking retrieval/RadixSet: Collecting 100 samples in estimated 5.0004 s (34M iretrieval/RadixSet      time:   [146.45 ns 150.14 ns 154.03 ns]
                        change: [−5.8085% −2.8884% +0.0718%] (p = 0.07 > 0.05)
                        No change in performance detected.
Found 8 outliers among 100 measurements (8.00%)
  7 (7.00%) high mild
  1 (1.00%) high severe
Benchmarking retrieval/HashSet: Collecting 100 samples in estimated 5.0002 s (66M itretrieval/HashSet       time:   [69.112 ns 72.517 ns 76.187 ns]
                        change: [−18.567% −13.987% −9.1918%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 10 outliers among 100 measurements (10.00%)
  8 (8.00%) high mild
  2 (2.00%) high severe
Benchmarking retrieval/BTreeSet: Collecting 100 samples in estimated 5.0007 s (20M iretrieval/BTreeSet      time:   [256.68 ns 268.80 ns 281.71 ns]
                        change: [−4.1414% −0.3666% +3.7733%] (p = 0.85 > 0.05)
                        No change in performance detected.

Benchmarking removal/RadixSet: Collecting 100 samples in estimated 5.1899 s (1800 itremoval/RadixSet        time:   [226.38 ns 233.16 ns 241.09 ns]
                        change: [+0.5957% +4.5543% +8.9064%] (p = 0.03 < 0.05)
                        Change within noise threshold.
Found 16 outliers among 100 measurements (16.00%)
  10 (10.00%) high mild
  6 (6.00%) high severe
Benchmarking removal/HashSet: Collecting 100 samples in estimated 5.1522 s (2100 iteremoval/HashSet         time:   [134.58 ns 140.27 ns 146.56 ns]
                        change: [−41.200% −34.891% −28.117%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 5 outliers among 100 measurements (5.00%)
  3 (3.00%) high mild
  2 (2.00%) high severe
Benchmarking removal/BTreeSet: Collecting 100 samples in estimated 5.1337 s (1800 itremoval/BTreeSet        time:   [575.11 ns 603.57 ns 634.72 ns]
                        change: [−16.099% −10.766% −5.1496%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 6 outliers among 100 measurements (6.00%)
  4 (4.00%) high mild
  2 (2.00%) high severe
```
