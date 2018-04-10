[![Build Status](https://travis-ci.org/semorrison/lean-category-theory-pr.svg?branch=master)](https://travis-ci.org/semorrison/lean-category-theory-pr)

# lean-category-theory-pr

This is a temporary staging area for code that we plan extract from [lean-category-theory](https://github.com/semorrison/lean-category-theory) and pull request into [mathlib](https://github.com/leanprover/mathlib).

## TODO
1. Copy over just enough files to include `universal/types/default.lean` and its dependencies.
2. Clean them up.
3. Minimise (remove?) the dependency on `lean-tidy`. (A good strategy may be to progressively move the imports from lean-tidy to later and later files.)
4. Pull request!