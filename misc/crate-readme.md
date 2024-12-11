markov-generator
================

A highly customizable Rust library for building [Markov chains] and
generating random sequences from them.

[Markov chains]: https://en.wikipedia.org/wiki/Markov_chain

[`Chain`] implements [Serde]’s [`Serialize`] and [`Deserialize`] traits, so
you can reuse chains without having to regenerate them every time (which
can be a lengthy process).

Example
-------

```rust
use markov_generator::{AddEdges, HashChain};

const DEPTH: usize = 6;
// Maps each sequence of 6 items to a list of possible next items.
// `HashChain` uses hash maps internally; b-trees can also be used.
let mut chain = HashChain::new(DEPTH);

// In this case, corpus.txt contains one paragraph per line.
let file = File::open("examples/corpus.txt")?;
let mut reader = BufReader::new(file);
let mut line = String::new();
// The previous `DEPTH` characters before `line`.
let mut prev = Vec::<char>::new();

while let Ok(1..) = reader.read_line(&mut line) {
    // `Both` means that the generated random output could start with the
    // beginning of `line` or end after the end of `line`.
    chain.add_all(line.chars(), AddEdges::Both);

    // This makes sure there's a chance that the end of the previous line
    // could be followed by the start of the current line when generating
    // random output.
    chain.add_all(
        prev.iter().copied().chain(line.chars().take(DEPTH)),
        AddEdges::Neither,
    );

    if let Some((n, (i, _c))) =
        line.char_indices().rev().enumerate().take(DEPTH).last()
    {
        // Keep only the most recent `DEPTH` characters.
        prev.drain(0..prev.len().saturating_sub(DEPTH - n - 1));
        prev.extend(line[i..].chars());
    }
    line.clear();
}

// Generate and print random Markov data.
let mut stdout = BufWriter::new(io::stdout().lock());
let mut prev_newline = false;
for &c in chain.generate() {
    if prev_newline {
        writeln!(stdout)?;
    }
    prev_newline = c == '\n';
    write!(stdout, "{c}")?;
}
stdout.flush()?;
```

Crate features
--------------

* `std` (default: enabled): Use [`std`]. If disabled, this crate is marked
  `no_std`.
* `serde` (default: enabled): Implement [Serde]’s [`Serialize`] and
  [`Deserialize`] traits for [`Chain`].

[`Chain`]: https://docs.rs/markov-generator/0.2/markov_generator/struct.Chain.html
[Serde]: https://docs.rs/serde/1/serde/
[`Serialize`]: https://docs.rs/serde/1/serde/trait.Serialize.html
[`Deserialize`]: https://docs.rs/serde/1/serde/trait.Deserialize.html
[`std`]: https://doc.rust-lang.org/stable/std/
