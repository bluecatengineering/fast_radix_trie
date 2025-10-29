use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use fast_radix_trie::RadixSet;
use patricia_tree::PatriciaSet;
use rand::{Rng, seq::IndexedRandom};

use std::{
    collections::{BTreeSet, HashSet},
    hint::black_box,
    sync::LazyLock,
};

fn bench_longest_common_prefix(c: &mut Criterion) {
    let mut group = c.benchmark_group("longest_common_prefix");

    group.bench_function("LCP by 4 bytes", |b| {
        b.iter(|| {
            fast_radix_trie::longest_common_prefix(
                black_box(b"abcdefghijklmnopqrstuvwxyz123"),
                black_box(b"abcdefghijklmnopqrstuvwxyzabc"),
            );
        })
    });

    group.bench_function("LCP byte by byte", |b| {
        b.iter(|| {
            fast_radix_trie::longest_common_prefix_by_byte(
                black_box(b"abcdefghijklmnopqrstuvwxyz123"),
                black_box(b"abcdefghijklmnopqrstuvwxyzabc"),
            );
        })
    });

    group.finish();
}

fn bench_insertion(c: &mut Criterion) {
    let mut group = c.benchmark_group("random insertion");

    group.bench_function("RadixSet", |b| {
        let mut set = RadixSet::new();
        let mut rng = rand::rng();
        b.iter(|| {
            set.insert(black_box(rng.random::<u64>().to_string()));
        })
    });

    group.bench_function("PatriciaSet", |b| {
        let mut set = PatriciaSet::new();
        let mut rng = rand::rng();
        b.iter(|| {
            set.insert(black_box(rng.random::<u64>().to_string()));
        })
    });

    group.bench_function("HashSet", |b| {
        let mut set = HashSet::new();
        let mut rng = rand::rng();
        b.iter(|| {
            set.insert(black_box(rng.random::<u64>().to_string()));
        })
    });

    group.bench_function("BTreeSet", |b| {
        let mut set = BTreeSet::new();
        let mut rng = rand::rng();
        b.iter(|| {
            set.insert(black_box(rng.random::<u64>().to_string()));
        })
    });

    group.finish();
}

fn bench_retrieval(c: &mut Criterion) {
    const MAX: u64 = 1_000_000;
    let mut group = c.benchmark_group("random retrieval");
    let mut set = RadixSet::new();
    let mut rng = rand::rng();

    // Pre-populate the set
    for _ in 0..MAX / 2 {
        set.insert((rng.random::<u64>() % MAX).to_string());
    }

    group.bench_function("RadixSet", |b| {
        b.iter(|| {
            set.contains(black_box((rng.random::<u64>() % MAX).to_string()));
        })
    });

    let mut set = PatriciaSet::new();
    // Pre-populate the set
    for _ in 0..MAX / 2 {
        set.insert((rng.random::<u64>() % MAX).to_string());
    }

    group.bench_function("PatriciaSet", |b| {
        b.iter(|| {
            set.contains(black_box((rng.random::<u64>() % MAX).to_string()));
        })
    });

    let mut hash_set = HashSet::new();
    for _ in 0..MAX / 2 {
        hash_set.insert((rng.random::<u64>() % MAX).to_string());
    }
    group.bench_function("HashSet", |b| {
        b.iter(|| {
            hash_set.contains(black_box(&(rng.random::<u64>() % MAX).to_string()));
        })
    });

    let mut btree_set = BTreeSet::new();
    for _ in 0..MAX / 2 {
        btree_set.insert((rng.random::<u64>() % MAX).to_string());
    }
    group.bench_function("BTreeSet", |b| {
        b.iter(|| {
            btree_set.contains(black_box(&(rng.random::<u64>() % MAX).to_string()));
        })
    });
    group.finish();
}

fn bench_removal(c: &mut Criterion) {
    let mut group = c.benchmark_group("random removal");
    const MAX: u64 = 100_000;

    let mut values = Vec::with_capacity(MAX as usize);
    for i in 0..MAX {
        values.push(i.to_string());
    }
    let radix_set: RadixSet = values.iter().cloned().collect();
    let hashset: HashSet<String> = values.iter().cloned().collect();
    let btreeset: BTreeSet<String> = values.iter().cloned().collect();
    let pat_set: PatriciaSet = values.iter().cloned().collect();

    group.bench_function("RadixSet", |b| {
        b.iter_batched_ref(
            // setup
            || {
                let val = values.choose(&mut rand::rng()).unwrap().clone();
                (radix_set.clone(), val.clone())
            },
            // time removal
            |(set, val)| {
                set.remove(black_box(val));
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("PatriciaSet", |b| {
        b.iter_batched_ref(
            // setup
            || {
                let val = values.choose(&mut rand::rng()).unwrap().clone();
                (pat_set.clone(), val.clone())
            },
            // time removal
            |(set, val)| {
                set.remove(black_box(val));
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("HashSet", |b| {
        b.iter_batched_ref(
            // setup
            || {
                let val = values.choose(&mut rand::rng()).unwrap().clone();
                (hashset.clone(), val.clone())
            },
            |(set, val)| {
                set.remove(black_box(&*val));
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("BTreeSet", |b| {
        b.iter_batched_ref(
            // setup
            || {
                let val = values.choose(&mut rand::rng()).unwrap().clone();
                (btreeset.clone(), val.clone())
            },
            |(set, val)| {
                set.remove(black_box(&*val));
            },
            BatchSize::SmallInput,
        )
    });
    group.finish();
}

// these benchmarks were taken from https://github.com/cloudflare/trie-hard/
// which was taken from https://github.com/michaelsproul/rust_radix_trie/

const OW_1984: &str = include_str!("../data/1984.txt");
const RANDOM: &str = include_str!("../data/random.txt");
const TOP_MILLION: &str = include_str!("../data/top-domains.txt");

static DOMAINS_REV: LazyLock<Vec<String>> = LazyLock::new(|| {
    TOP_MILLION
        .split(|c: char| c.is_whitespace())
        .collect::<HashSet<_>>()
        .into_iter()
        .map(|s| s.chars().rev().collect::<String>())
        .collect()
});

fn get_big_text() -> Vec<&'static str> {
    OW_1984
        .split(|c: char| c.is_whitespace())
        .collect::<HashSet<_>>()
        .into_iter()
        .collect()
}

fn get_domain_text() -> Vec<&'static str> {
    DOMAINS_REV.iter().map(|s| s.as_str()).collect()
}

fn get_random_text() -> Vec<&'static str> {
    RANDOM
        .split(|c: char| c.is_whitespace())
        .collect::<HashSet<_>>()
        .into_iter()
        .collect()
}

fn make_trie_hard<'a>(words: &[&'a str]) -> trie_hard::TrieHard<'a, &'a str> {
    words.iter().copied().collect()
}
fn make_my_trie(words: &[&str]) -> RadixSet {
    words.iter().copied().collect()
}
fn make_rust_radix_trie<'a>(words: &[&'a str]) -> radix_trie::Trie<&'a str, usize> {
    let mut trie = radix_trie::Trie::new();
    for w in words {
        trie.insert(*w, w.len());
    }
    trie
}

// bench insert

fn bench_domains_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("domains trie insert comparison");

    let words = get_domain_text();
    group.bench_function("(ours) RadixSet insert", |b| {
        b.iter(|| make_my_trie(black_box(&words)))
    });

    group.bench_function("TrieHard insert", |b| {
        b.iter(|| make_trie_hard(black_box(&words)))
    });

    group.bench_function("radix_trie::Trie insert", |b| {
        b.iter(|| make_rust_radix_trie(black_box(&words)))
    });

    group.finish();
}

fn bench_long_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("1984 trie insert comparison");

    let words = get_big_text();
    group.bench_function("(ours) RadixSet insert", |b| {
        b.iter(|| make_my_trie(black_box(&words)))
    });

    group.bench_function("TrieHard insert", |b| {
        b.iter(|| make_trie_hard(black_box(&words)))
    });

    group.bench_function("radix_trie::Trie insert", |b| {
        b.iter(|| make_rust_radix_trie(black_box(&words)))
    });

    group.finish();
}

fn bench_random_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("random trie insert comparison");

    let words = get_random_text();
    group.bench_function("(ours) RadixSet insert", |b| {
        b.iter(|| make_my_trie(black_box(&words)))
    });

    group.bench_function("TrieHard insert", |b| {
        b.iter(|| make_trie_hard(black_box(&words)))
    });

    group.bench_function("radix_trie::Trie insert", |b| {
        b.iter(|| make_rust_radix_trie(black_box(&words)))
    });

    group.finish();
}

// bench get

fn bench_domains_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("domains trie get comparison");

    let words = get_domain_text();

    let trie = make_my_trie(&words);
    group.bench_function("(ours) RadixSet get", |b| {
        b.iter(|| {
            words
                .iter()
                .map(|w| trie.contains(w))
                .collect::<Vec<bool>>()
        })
    });

    let trie = make_trie_hard(&words);
    group.bench_function("TrieHard get", |b| {
        b.iter(|| words.iter().map(|w| trie.get(w)).collect::<Vec<_>>())
    });

    let trie = make_rust_radix_trie(&words);
    group.bench_function("radix_trie::Trie get", |b| {
        b.iter(|| words.iter().map(|w| trie.get(w)).collect::<Vec<_>>())
    });

    group.finish();
}

fn bench_random_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("random trie get comparison");

    let words = get_random_text();

    let trie = make_my_trie(&words);
    group.bench_function("(ours) RadixSet get", |b| {
        b.iter(|| {
            words
                .iter()
                .map(|w| trie.contains(w))
                .collect::<Vec<bool>>()
        })
    });

    let trie = make_trie_hard(&words);
    group.bench_function("TrieHard get", |b| {
        b.iter(|| words.iter().map(|w| trie.get(w)).collect::<Vec<_>>())
    });

    let trie = make_rust_radix_trie(&words);
    group.bench_function("radix_trie::Trie get", |b| {
        b.iter(|| words.iter().map(|w| trie.get(w)).collect::<Vec<_>>())
    });

    group.finish();
}

fn bench_long_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("long trie get comparison");

    let words = get_big_text();

    let trie = make_my_trie(&words);
    group.bench_function("(ours) RadixSet get", |b| {
        b.iter(|| {
            words
                .iter()
                .map(|w| trie.contains(w))
                .collect::<Vec<bool>>()
        })
    });

    let trie = make_trie_hard(&words);
    group.bench_function("TrieHard get", |b| {
        b.iter(|| words.iter().map(|w| trie.get(w)).collect::<Vec<_>>())
    });

    let trie = make_rust_radix_trie(&words);
    group.bench_function("radix_trie::Trie get", |b| {
        b.iter(|| words.iter().map(|w| trie.get(w)).collect::<Vec<_>>())
    });

    group.finish();
}

// bench removal

fn bench_domains_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("domains trie remove comparison");

    let words = get_domain_text();

    group.bench_function("(ours) RadixSet remove", |b| {
        b.iter(|| {
            let mut trie = make_my_trie(&words);
            for w in &words {
                trie.remove(w);
            }
        })
    });

    // group.bench_function("TrieHard remove", |b| {
    //     b.iter(|| {
    //         let mut trie = make_trie_hard(&words);
    //         for w in &words {
    //             trie.remove(w);
    //         }
    //     })
    // });

    group.bench_function("radix_trie::Trie remove", |b| {
        b.iter(|| {
            let mut trie = make_rust_radix_trie(&words);
            for w in &words {
                trie.remove(w);
            }
        })
    });

    group.finish();
}

fn bench_random_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("random trie remove comparison");

    let words = get_random_text();

    group.bench_function("(ours) RadixSet remove", |b| {
        b.iter(|| {
            let mut trie = make_my_trie(&words);
            for w in &words {
                trie.remove(w);
            }
        })
    });

    // group.bench_function("TrieHard remove", |b| {
    //     b.iter(|| {
    //         let mut trie = make_trie_hard(&words);
    //         for w in &words {
    //             trie.remove(w);
    //         }
    //     })
    // });

    group.bench_function("radix_trie::Trie remove", |b| {
        b.iter(|| {
            let mut trie = make_rust_radix_trie(&words);
            for w in &words {
                trie.remove(w);
            }
        })
    });

    group.finish();
}

fn bench_long_remove(c: &mut Criterion) {
    let mut group = c.benchmark_group("long trie remove comparison");

    let words = get_big_text();

    group.bench_function("(ours) RadixSet remove", |b| {
        b.iter(|| {
            let mut trie = make_my_trie(&words);
            for w in &words {
                trie.remove(w);
            }
        })
    });

    // group.bench_function("TrieHard remove", |b| {
    //     b.iter(|| {
    //         let mut trie = make_trie_hard(&words);
    //         for w in &words {
    //             trie.remove(w);
    //         }
    //     })
    // });

    group.bench_function("radix_trie::Trie remove", |b| {
        b.iter(|| {
            let mut trie = make_rust_radix_trie(&words);
            for w in &words {
                trie.remove(w);
            }
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_longest_common_prefix,
    bench_insertion,
    bench_retrieval,
    bench_removal
);

criterion_group!(
    bench_insert,
    bench_domains_insert,
    bench_random_insert,
    bench_long_insert
);

criterion_group!(
    bench_get,
    bench_domains_get,
    bench_random_get,
    bench_long_get
);

criterion_group!(
    bench_remove,
    bench_domains_remove,
    bench_random_remove,
    bench_long_remove
);

criterion_main!(benches, bench_insert, bench_get, bench_remove);
