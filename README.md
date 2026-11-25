# loop-subgroups

A Lean 4 formalization of J. Breitner, *Loop subgroups of F_r and the image of their stabilizer
subgroups in GL_r(Z)* (Israel J. Math., 2011,
[doi:10.1007/s11856-011-0213-3](https://doi.org/10.1007/s11856-011-0213-3);
[arXiv:1012.2729](https://arxiv.org/abs/1012.2729)), built on Mathlib and
[Tau Ceti](https://github.com/TauCetiProject/TauCeti).

There is no `sorry`, and the only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
`BLUEPRINT.md` maps each statement of the paper to its Lean declaration.
`formalization.yaml` (v0.4) holds the metadata for Palomar.

## What is proved

* **Theorem 1.** For a loop subgroup `U ≤ F_r`, `r ≥ 3`, with at most `r − 2` looplets,
  `B(Stab_{Aut(F_r)}(U)) = {M ∈ GL_r(ℤ) | v·M ≡ v (mod 2)}`, where `v_i = 1` iff `s_i` is even.
  It is formalized in every formulation the paper gives:
  * `image_Stab_eq`;
  * `mem_image_Stab_iff`, the introduction's form with an integral `v`;
  * `Γ₂_le_image_Stab` together with `map_reduce_image_Stab`, the Section 8 form;
  * `image_stabilizer_eq`, for an arbitrary free group with an arbitrary basis.
* **The steps of the proof.**
  * Lemma 5, in a coordinate-free generalisation and in the paper's form.
  * Remark 6 and Corollary 7: generators of `Γ₂`.
  * Lemma 8: generators of `S(v)`.
  * Definition 9: the map `B` is a group homomorphism.
  * Remarks 3 and 4, Lemmas 10, 12, 13, 14, and Propositions 15 and 16. Proposition 16 is proved
    for arbitrary finite-index subgroups.
* **The excluded case** (`r − 1` looplets): Remark 17, surjectivity of `B`, and Proposition 18,
  that is, `B(Stab U) = Stab_{GL_r(ℤ)}(U')` and `Γ_{s_1} ≤ B(Stab U)`.
* **Existence.** For every `s` with all `s_i ≥ 1` there is an `s_1/…/s_r` loop subgroup, built
  explicitly from its coset graph. Its index is `1 + Σ(s_i − 1)`.
* **Example 2.** The 3/3/1 loop subgroup has index 5, and `B(Stab U) = GL_3(ℤ)`. This is an
  instance of the thesis's "odd case", `image_Stab_eq_top_of_odd`.

## Corrections and additions to the paper

1. **Lemma 8 needs `r ≥ 3`.** For `r = 2` and `v = (1,1)` the generating set is empty, but
   `S(v)` contains the swap matrix. The paper only uses the lemma for `r ≥ 3`, so the main results
   are not affected.
2. **`τ_j ∈ Stab(U)` needed a proof.** The paper uses that the automorphism `τ_j` inverting
   `g_j` stabilizes `U`, without proof. The formalization proves it by reflecting the `j`-th loop.
3. **Remark 17 doesn't need the characteristic kernel** once the induced map is given.
4. **Proposition 18.** The preimages that show `B` is surjective are the Nielsen moves.
5. **Typo in the preface:** `B(GL_r(ℤ))` should be `B(Stab(U))`.

## Not formalized

* That `s_1` is exactly the congruence level in Proposition 18. Only `Γ_{s_1} ≤ B(Stab U)` is
  proved.
* That the loop lengths determine the loop subgroup.
* The free basis of `U` given after Example 2, and Example 11.
* The probabilistic remark in the preface.
* That Definition 1 implies finite index. It is assumed as a hypothesis instead.
* Thesis-only material: the CosetProject algorithm, maximality of `S(v)`, index-two subgroups,
  and the counting appendix.

## Building

```
lake exe cache get                                                              # Mathlib oleans
bash .lake/packages/TauCeti/scripts/lake-cache-get.sh .lake/packages/TauCeti   # Tau Ceti oleans
lake build
```
