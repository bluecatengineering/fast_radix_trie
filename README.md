# fast_radix_trie

[![fast_radix_trie](https://img.shields.io/crates/v/fast_radix_trie.svg)](https://crates.io/crates/fast_radix_trie)
[![Documentation](https://docs.rs/fast_radix_trie/badge.svg)](https://docs.rs/fast_radix_trie)
[![Actions Status](https://github.com/bluecatengineering/fast_radix_trie/workflows/CI/badge.svg)](https://github.com/bluecatengineering/fast_radix_trie/actions)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

[Documentation](https://docs.rs/fast_radix_trie)

A radix tree compresses nodes such that common prefixes are shared. This minimizes memory usage for storing large sets of strings/bytes. Additionally, this library optimizes memory layout/padding to further reduce memory consumption, leading to significant memory savings and fast traversal time for large data sets. Memory usage can be dramatically less than storing in std's HashMap, BTreeMap or other rust trie crates.

I've compared to other popular rust trie libraries, and `fast_radix_trie` seems to use dramatically less memory than most while also being faster for insert/remove/retrieve operations.

See [Radix tree](https://en.wikipedia.org/wiki/Radix_tree) for more details.

## Implementation

Crate offers two implementations, one optimized for absolute minimum memory usage (minimizing padding/alignment where possible), and one optimized for mutations that uses `realloc`. Use `--no-default-features` to disable the `realloc` feature and use the implementation that's optimized for memory. This crate is no_std compatible.

The code is originally based on the excellent [patricia_tree](https://github.com/sile/patricia_tree), but whereas patricia tree uses a child/sibling pointer for each node (where siblings are traversed in a linked list to find nodes at the same level) a radix tree stores all children node pointers inline for faster traversal. It costs a small bit more memory, around 5% depending on the data set, but can be around 4x faster to build the data structure, 2x faster for removals (more comparisons in `cargo bench`). If you use the `realloc` impl, mutations should be faster as we attempt to resize nodes rather than allocate new ones on mutation, particularly useful if you are removing entries.

This library uses unsafe and raw pointers because nodes are dynamically sized to store node labels and children pointers at dynamic offsets inline in each node allocation. By doing this we can drastically reduce memory usage. The test suite is comprehensive and passes `miri`.

## Examples

```rust
use fast_radix_trie::RadixMap;

let mut map = RadixMap::new();
map.insert("a", 1);
map.insert("apple", 2);
map.insert("applesauce", 3);
map.insert("apply", 4);
map.insert("abort", 5);
map.insert("abs", 6);
map.insert("box", 7);

// &map = "" (-)
//      ├─"a" (1)
//            ├─"b" (-)
//                  ├─"ort" (5)
//                  └─"s" (6)
//            └─"ppl" (-)
//                  ├─"e" (2)
//                        └─"sauce" (3)
//                  └─"y" (4)
//      └─"box" (7)

assert_eq!(map.len(), 7);

assert_eq!(map.get("a"), Some(&1));
assert_eq!(map.get("apple"), Some(&2));
assert_eq!(map.get("applesauce"), Some(&3));
assert_eq!(map.get("applebees"), None);

// You can split by prefix also to create separate the tree:
let other = map.split_by_prefix("ap");
dbg!(&map);
// &map = "" (-)
//      ├─"a" (1)
//            └─"b" (-)
//                  ├─"ort" (5)
//                  └─"s" (6)
//      └─"box" (7)
dbg!(&other);
// &other = "appl" (-)
//      ├─"e" (2)
//            └─"sauce" (3)
//      └─"y" (4)

// You can also use `common_prefixes` to return an iterator over all matching entries
// as you traverse:

let mut t = RadixMap::new();
t.insert("a", vec!["a"]);
t.insert("x", vec!["x"]);
t.insert("ab", vec!["b"]);
t.insert("abc", vec!["c"]);
t.insert("abcd", vec!["d"]);
t.insert("abcdf", vec!["f"]);

assert!(t
    .common_prefixes(b"abcde")
    .map(|(_, v)| v)
    .flatten()
    .eq(vec![&"a", &"b", &"c", &"d"].into_iter()));
```

## Differences with patricia_tree

This library passes the original test suite (with minor modifications like debug output), so you should just be able to substitute one for the other and enjoy the benefits. There's one cavet: node labels can't be longer than 255. Keys can be as long as you want, but a node label, i.e. a compressed subsection of the key that is inserted into the trie cannot.

## Benchmarks

Run `cargo bench` for results, but the performance for retrieval/removal is on par or better in some cases than hashmap/btreemap from std.

However, the library offers significant memory savings over the std data structures:

| crate                                                                                 |  time   |  memory  |                        data set |
| :------------------------------------------------------------------------------------ | :-----: | :------: | ------------------------------: |
| hashset                                                                               |  8.1s   | 1_784 MB | enwiki-latest-all-titles-in-ns0 |
| btree                                                                                 |  4.5s   | 1,607 MB | enwiki-latest-all-titles-in-ns0 |
| [fast_radix_trie](https://github.com/bluecatengineering/fast_radix_trie) (this crate) |  4.5s   |  905 MB  | enwiki-latest-all-titles-in-ns0 |
| hashset                                                                               | 0.3s \* |  108 MB  |                     top-domains |
| btree                                                                                 |  0.48s  |  73 MB   |                     top-domains |
| [fast_radix_trie](https://github.com/bluecatengineering/fast_radix_trie) (this crate) |  0.45s  | 51 MB \* |                     top-domains |
| [rust_radix_trie](https://github.com/michaelsproul/rust_radix_trie/)                  |  1.03s  |  430 MB  |                     top-domains |
| [qptrie](https://github.com/jedisct1/rust-qptrie/)                                    |  0.80s  |  115 MB  |                     top-domains |

You can see the only data structure to beat the insertion time is std HashSet but it takes almost twice as much memory for the top 1 million domains.

For retrieving individual random values, the benches show `fast_radix_trie` on the order of ~150 ns, competitive with std lib.

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
# MEMORY: 905360 // 905 MB
```

For reference, sile's original code takes 20s and 850 MB on the same set)

with the top 1 million domains, saves over 50% compared to HashSet:

```console
$ du -sh top-domains.txt
15M top-domains.txt

// HashSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --no-default-features --example insert_lines --release -- --kind hashset < rev top-domains.txt
# LINES: 1000000
# ELAPSED: 0:00.30
# MEMORY: 108324 // 108 MB

// BTreeSet
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --no-default-features --example insert_lines --release -- --kind btree < rev top-domains.txt
# LINES: 1000000
# ELAPSED: 0:00.48
# MEMORY: 73412 // 73 MB

// RadixSet (this crate)
$ /usr/bin/time -f "# ELAPSED: %E\n# MEMORY: %M" cargo run --no-default-features --example insert_lines --release -- --kind radix < rev top-domains.txt
# LINES: 1000000
# ELAPSED: 0:00.45
# MEMORY: 49936 // 50 MB
```

`rust_radix_trie` uses ~430 MB on the reversed domains . **Compared to just 50 MB for this crate.**

## Comparison with other trie libraries

`cargo bench` results for insert/get/remove of random values, which is probably a worst case for a prefix matching data structure like a trie (Patricia is the `patricia_tree` crate):

```
                                [min       avg       max      ]
insertion/RadixSet      time:   [246.95 ns 257.41 ns 266.66 ns]
insertion/PatriciaSet   time:   [310.23 ns 355.22 ns 456.34 ns]
insertion/HashSet       time:   [82.404 ns 86.007 ns 89.868 ns]
insertion/BTreeSet      time:   [188.51 ns 190.63 ns 192.38 ns]

retrieval/RadixSet      time:   [138.52 ns 140.90 ns 143.69 ns]
retrieval/PatriciaSet   time:   [334.98 ns 337.53 ns 340.35 ns]
retrieval/HashSet       time:   [64.858 ns 66.914 ns 69.170 ns]
retrieval/BTreeSet      time:   [262.30 ns 267.49 ns 273.57 ns]

removal/RadixSet        time:   [229.88 ns 238.68 ns 248.85 ns]
removal/PatriciaSet     time:   [506.72 ns 514.99 ns 524.06 ns]
removal/HashSet         time:   [156.06 ns 162.75 ns 169.71 ns]
removal/BTreeSet        time:   [637.92 ns 682.83 ns 731.40 ns]
```

Comparison with cloudflare's [trie-hard](https://github.com/cloudflare/trie-hard/) and [rust_radix_trie](https://github.com/michaelsproul/rust_radix_trie/):

for inserting the set of top 1 million domains reversed, this library is almost twice as fast as the others. (time is for adding all entries)

```
domains trie insert comparison/(ours) RadixSet insert*
                        time:   [569.11 ms 580.38 ms 591.60 ms]
domains trie insert comparison/TrieHard insert
                        time:   [1.0824 s 1.0870 s 1.0919 s]
domains trie insert comparison/radix_trie::Trie insert
                        time:   [856.71 ms 862.44 ms 868.34 ms]
```

get (times are for getting all 1 million entries)

```
domains trie get comparison/(ours) RadixSet get
                        time:   [448.71 ms 451.81 ms 455.01 ms]
domains trie get comparison/TrieHard get*
                        time:   [352.87 ms 355.59 ms 358.43 ms]
domains trie get comparison/radix_trie::Trie get
                        time:   [665.16 ms 669.68 ms 674.39 ms]
```

remove (times are for removing all 1 million entries). `trie-hard` doesn't have a `remove`

```
domains trie remove comparison/(ours) RadixSet remove*
                        time:   [882.75 ms 889.10 ms 895.61 ms]
domains trie remove comparison/radix_trie::Trie remove
                        time:   [1.7784 s 1.7912 s 1.8043 s]
```
