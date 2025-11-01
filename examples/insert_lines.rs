use fast_radix_trie::{RadixMap, RadixSet};
use radix_trie::TrieCommon;
use std::{
    collections::{BTreeSet, HashSet},
    io::BufRead,
};

fn main() -> noargs::Result<()> {
    let mut args = noargs::raw_args();
    noargs::HELP_FLAG.take_help(&mut args);

    let kinds = [
        "radix_map",
        "radix",
        "hash",
        "btree",
        "count",
        "radix_trie",
        "patricia",
        "patricia_map",
        "qptrie",
    ];

    let kind = noargs::opt("kind")
        .doc("Data structure kindt")
        .ty(kinds.join(" | ").leak())
        .default("radix")
        .take(&mut args)
        .then(|a| {
            let value = a.value();
            if kinds.contains(&value) {
                Ok(value.to_string())
            } else {
                Err(format!("must be one of: {}", kinds.join(" , ")))
            }
        })?;
    if let Some(help) = args.finish()? {
        print!("{help}");
        return Ok(());
    }

    match kind.as_str() {
        "radix_map" => {
            let mut set = RadixMap::new();
            each_line(|line| {
                set.insert(line, 1_u32);
            });
            println!("# LINES: {}", set.len());
        }
        "radix" => {
            let mut set = RadixSet::new();
            each_line(|line| {
                set.insert(line);
            });
            println!("# LINES: {}", set.len());
        }
        "patricia" => {
            let mut set = patricia_tree::PatriciaSet::new();
            each_line(|line| {
                set.insert(line);
            });
            println!("# LINES: {}", set.len());
        }
        "patricia_map" => {
            let mut set = patricia_tree::PatriciaMap::new();
            each_line(|line| {
                set.insert(line, 1_u32);
            });
            println!("# LINES: {}", set.len());
        }
        "radix_trie" => {
            let mut set = radix_trie::Trie::new();
            each_line(|line| {
                set.insert(line, ());
            });
            println!("# LINES: {}", set.len());
        }
        "qptrie" => {
            let mut set = qptrie::Trie::new();
            let mut len = 0;
            each_line(|line| {
                set.insert(line, ());
                len += 1;
            });
            println!("# LINES: {len}");
        }
        "hash" => {
            let mut set = HashSet::new();
            each_line(|line| {
                set.insert(line);
            });
            println!("# LINES: {}", set.len());
        }
        "btree" => {
            let mut set = BTreeSet::new();
            each_line(|line| {
                set.insert(line);
            });
            println!("# LINES: {}", set.len());
        }
        "count" => {
            let mut count = 0;
            each_line(|_| {
                count += 1;
            });
            println!("# LINES: {count}");
        }
        _ => unreachable!(),
    }

    Ok(())
}

fn each_line<F>(mut f: F)
where
    F: FnMut(String),
{
    let stdin = std::io::stdin();
    for line in stdin.lock().lines() {
        f(line.unwrap());
    }
}
