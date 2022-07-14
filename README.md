# TaPL.lean

Implementing and learning /[[https://www.cis.upenn.edu/~bcpierce/tapl/checkers/arith.tar.gz][Types and Programming Languages]]/ in [[https://github.com/leanprover-community/lean][Lean 3]]

This code does not have one-to-one correspondence to the [[https://www.cis.upenn.edu/~bcpierce/tapl/checkers][original implentation]]

## Run

~lean --run src/main.lean LANGUAGE_NAME~ at project root

## Progress

- Chapter 1~4
  - [X] arith
- Chapter 5~7
  - [ ] untyped
  - [ ] fulluntyped
- Chapter 8
  - [X] tyarith
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

The test.f file in each directories under [[examples][examples]] is copied from the [[https://www.cis.upenn.edu/~bcpierce/tapl/checkers][original implentation]], and their copyright belongs to [[ <https://www.cis.upenn.edu/~bcpierce>][Benjamin C. Pierce]] as far as I know (I couldn't find the copyright notice of them).

Everything else (including examples/#/test_ex.f) is licensed under the [[https://opensource.org/licenses/BSD-3-Clause][BSD3]] License - see the [[LICENSE.txt][LICENSE.txt]] file for details
