use markov_generator::{AddEdges, Chain};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::iter;

fn main() {
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
}
