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
* **More from the paper:**
  * loop subgroups have finite index, and their lengths determine them;
  * the index formula `[F_r : U] = 1 + Σ(s_i − 1)`;
  * the free basis `{g_i^{s_i}} ∪ {g_i^{-k} g_j g_i^k}` given after Example 2;
  * in the excluded case, `s_1` is exactly the congruence level.

## Material from the Diplomarbeit

* **CosetProject algorithm:** a computable Lean implementation (`CosetProject.cosetProject`).
  Its correctness theorem says that the output table is a coset table of `U ⊔ ⟪R⟫`, the preimage
  of `π(U)`.
* **Lemma `index2intersection`:** generators of `U ∩ S` for `S` of index two.
* **Lemma `unboundstabgroup`:** `[Aut(F_r) : Stab U] ≥ s_i`, and `[F_r : U] ≤ r · [Aut(F_r) : Stab U]`.
* **Lemmas `stabconj` and `max`:** `S(v)` is conjugate to `S(𝟙)`, and it is maximal in
  `GL_r(ℤ/2ℤ)` (already for `r ≥ 2`). Its index is `2^r − 1`.
* **Discussion section:** `[GL_r(ℤ) : B(Stab U)]` is `1` if all loops are odd, and `2^r − 1`
  otherwise.
* **Index-two subgroups:** `B̄(Stab U) = S(v)` with `v_i = 1` iff `g_i ∉ U`.

## Corrections and additions to the paper

1. **Lemma 8 needs `r ≥ 3`.** For `r = 2` and `v = (1,1)` the generating set is empty, but
   `S(v)` contains the swap matrix. The paper only uses the lemma for `r ≥ 3`, so the main results
   are not affected.
2. **`τ_j ∈ Stab(U)` needed a proof.** The paper uses that the automorphism `τ_j` inverting
   `g_j` stabilizes `U`, without proof. The formalization proves it by reflecting the `j`-th loop.
3. **Remark 17 doesn't need the characteristic kernel** once the induced map is given.
4. **Proposition 18.** The preimages that show `B` is surjective are the Nielsen moves.
5. **Typo in the preface:** `B(GL_r(ℤ))` should be `B(Stab(U))`.
6. **Gap in Lemma `unboundstabgroup` (thesis).** The proof assumes that `π(g_i)^n` is an
   `s_i`-cycle, which fails when `gcd(n, s_i) > 1`. The statement still holds, and the formal
   proof uses a different test word.
7. **Lemma `max`** needs only `r ≥ 2`, not `r ≥ 3`.
8. **CosetProject.** The formal version repeats the "row merged?" check before every relator. It
   is not proved that the pseudocode's once-per-row check is safe. See `BLUEPRINT.md`.

## Not formalized

* Example 11, and the probabilistic remark in the preface.
* Thesis-only material:
  * Todd–Coxeter, the subgroup-intersection and generator-rewriting procedures, and the run-time
    analysis;
  * the congruence-level detection, which needs `Γ_l = ⟪X₁₂^l⟫`;
  * the discussion examples and the GAP table;
  * chapter 1, which Mathlib already covers.

## Building

```
lake exe cache get                                                              # Mathlib oleans
bash .lake/packages/TauCeti/scripts/lake-cache-get.sh .lake/packages/TauCeti   # Tau Ceti oleans
lake build
```
