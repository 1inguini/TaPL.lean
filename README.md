# TaPL.lean

Implementing and learning _[Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/checkers/arith.tar.gz)_ in [Lean 4](https://github.com/leanprover/lean4)

This code does not have one-to-one correspondence to the [original implentation](https://www.cis.upenn.edu/~bcpierce/tapl/checkers)

## Run

`lean --run src/main.lean LANGUAGE_NAME` at project root

## Progress

- Chapter 1~4
  - [x] arith
- Chapter 5~7
  - [ ] untyped
  - [ ] fulluntyped
- Chapter 8
  - [x] tyarith
- Chapte 9~10
  - [ ] simplebool
  - [ ] fullsimple
- [ ] bot
- [ ] equirec
- [ ] fomega
- [ ] fomsub
- [ ] fullequirec
- [ ] fullerror
- [ ] fullfomsub
- [ ] fullfsub
- [ ] fullisorec
- [ ] fullomega
- [ ] fullpoly
- [ ] fullrecon
- [ ] fullref
- [ ] fullsub
- [ ] fullupdate
- [ ] letexercise
- [ ] purefsub
- [ ] rcdsubbot
- [ ] recon
- [ ] reconbase

## License

The test.f file in each directories under [examples](./examples) is copied from the [original implentation](https://www.cis.upenn.edu/~bcpierce/tapl/checkers), and their copyright belongs to [Benjamin C. Pierce](https://www.cis.upenn.edu/~bcpierce) as far as I know (I couldn't find the copyright notice of them).

Everything else (including examples/#/test_ex.f) is licensed under the [BSD3](https://opensource.org/licenses/BSD-3-Clause) License - see the [LICENSE.txt](./LICENSE.txt) file for details
