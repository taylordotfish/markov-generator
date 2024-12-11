/*
 * To the extent possible under law, the author(s) have dedicated all
 * copyright and neighboring rights to this software to the public domain
 * worldwide. This software is distributed without any warranty. See
 * <http://creativecommons.org/publicdomain/zero/1.0/> for a copy of the
 * CC0 Public Domain Dedication.
 *
 * Note that the above copyright notice applies only to the code in this
 * file: markov-generator, which this code depends on, is licensed under
 * version 3 or later of the GNU General Public License. Thus, any version of
 * this code that links to or is otherwise a derived work of markov-generator
 * may be distributed only in accordance with markov-generator's license.
 */

use markov_generator::{AddEdges, HashChain};
use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Write};

fn main() -> io::Result<()> {
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
    stdout.flush()
}
