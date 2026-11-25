# loop-subgroups

A Lean 4 formalization of J. Breitner, *Loop subgroups of F_r and the image of their stabilizer
subgroups in GL_r(Z)* (Israel J. Math., 2011; arXiv:1012.2729), built on Mathlib and
[Tau Ceti](https://github.com/TauCetiProject/TauCeti).

The main result is `LoopSubgroups.image_Stab_eq` in `LoopSubgroups/Main.lean`, and
`LoopSubgroups.image_stabilizer_eq` in `LoopSubgroups/General.lean` for an arbitrary basis.
See `BLUEPRINT.md` for how the paper's statements map to Lean declarations, and for remarks on
the paper.

## Building

```
lake exe cache get                                         # Mathlib oleans
bash .lake/packages/TauCeti/scripts/lake-cache-get.sh .lake/packages/TauCeti   # Tau Ceti oleans
lake build
```
