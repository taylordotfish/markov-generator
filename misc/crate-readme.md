markov-generator
================

A highly customizable Rust library for building [Markov chains] and
generating sequences of data from them.

[Markov chains]: https://en.wikipedia.org/wiki/Markov_chain

[`Chain`] implements [Serde]'s [`Serialize`] and [`Deserialize`] traits, so
you can use a chain multiple times without having to regenerate it every
time (which can be a lengthy process).

Example
-------

```rust
use markov_generator::{AddEdges, Chain};

const DEPTH: usize = 6;
// Maps each sequence of 6 items to a list of possible next items.
let mut chain = Chain::new(DEPTH);

// In this case, corpus.txt contains one paragraph per line.
let file = File::open("examples/corpus.txt").unwrap();
let mut reader = BufReader::new(file);
let mut line = String::new();
let mut prev_line = String::new();

while let Ok(1..) = reader.read_line(&mut line) {
    // `Both` means that the generated random output could start with the
    // beginning of `line`, and that the generated output could end after
    // the end of `line`.
    chain.add_all(line.chars(), AddEdges::Both);

    // Starting index of last `DEPTH` chars in `prev_line`.
    let prev_tail =
        prev_line.char_indices().nth_back(DEPTH - 1).map_or(0, |(i, _)| i);

    // This makes sure there's a chance that the end of the previous line
    // could be followed by the start of the current line when generating
    // random output.
    chain.add_all(
        prev_line[prev_tail..].chars().chain(line.chars().take(DEPTH)),
        AddEdges::Neither,
    );

    std::mem::swap(&mut line, &mut prev_line);
    line.clear();
}

// Generate and print random Markov data.
let output: String = chain
    .generate()
    .flat_map(|c| iter::repeat(c).take(1 + (*c == '\n') as usize))
    .collect();
print!("{}", &output[..output.len() - 1]);
```

Crate features
--------------

* `std` (default: enabled): Use [`std`]. If disabled, this crate is marked
  `no_std`.
* `hash` (default: enabled): Use hash maps internally. If disabled, B-trees
  will be used instead. This feature requires `std`.
* `serde` (default: enabled): Implement [Serde]'s [`Serialize`] and
  [`Deserialize`] traits for [`Chain`].

[`Chain`]: https://docs.rs/markov-generator/0.1/markov_generator/struct.Chain.html
[Serde]: https://docs.rs/serde/1.0/serde/
[`Serialize`]: https://docs.rs/serde/1.0/serde/trait.Serialize.html
[`Deserialize`]: https://docs.rs/serde/1.0/serde/trait.Deserialize.html
[`std`]: https://doc.rust-lang.org/stable/std/
