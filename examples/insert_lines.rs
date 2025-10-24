use fast_radix_tree::{RadixMap, RadixSet};
use std::{
    collections::{BTreeSet, HashSet},
    io::BufRead,
};

fn main() -> noargs::Result<()> {
    let mut args = noargs::raw_args();
    noargs::HELP_FLAG.take_help(&mut args);

    let kind = noargs::opt("kind")
        .doc("Data structure kindt")
        .ty("radix | radix_map | hash | btree | count")
        .default("radix")
        .take(&mut args)
        .then(|a| {
            let value = a.value();
            match value {
                "radix_map" | "radix" | "hash" | "btree" | "count" => Ok(value.to_string()),
                _ => Err("must be one of: radix, radix_map, hash, btree, count"),
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
                set.insert(line, rand::random::<u64>());
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
