# lean-loop-subgroups

A Lean 4 formalization of J. Breitner, *Loop subgroups of F_r and the image of their stabilizer
subgroups in GL_r(Z)*, Israel J. Math. 191 (2012), 545–557
([doi:10.1007/s11856-011-0213-3](https://doi.org/10.1007/s11856-011-0213-3);
[arXiv:1012.2729](https://arxiv.org/abs/1012.2729)), and of further material from the author's
Diplomarbeit (KIT), whose LaTeX source is included as `Diplomarbeit.tex`. It builds on Mathlib
and [Tau Ceti](https://github.com/TauCetiProject/TauCeti).

**This formalization was autoformalized by Claude** (Anthropic's Claude Opus 5.5, in Claude Code).
The author of the paper chose the target, the libraries and the scope; Claude wrote all Lean
code, the statements, and this documentation, using several AI sub-agents for individual parts.
The Lean kernel checks every proof.

There is no `sorry` outside `Challenge.lean`, and the only axioms used are `propext`,
`Classical.choice` and `Quot.sound`. `BLUEPRINT.md` maps each statement of the paper and the
thesis to its Lean declaration. `formalization.yaml` (v0.4) holds the metadata for
[Palomar](https://palomar-registry.org/).

## The statement of record: `Challenge.lean`

`Challenge.lean` is a short, self-contained file (importing only Mathlib) that states the main
result; `Solution.lean` proves exactly these statements from the library, which
[`lake comparator`](https://github.com/leanprover/comparator) checks (`comparator.json`).

* **Setting.** `G` is a free group with a basis `b = (b_i)_{i ∈ ι}` of finite rank `r = |ι|`.
  `B(γ)` is the integer matrix with entries `B(γ)_{ij} = #_{b_i} γ(b_j)`, the exponent sum of
  `b_i` in `γ(b_j)`; this is the action of `γ` on the abelianization `ℤ^r` (`autMatrix`).
* **Loop subgroups (Definition 1, `IsLoopSubgroup`).** `U ≤ G` is an `s_1/…/s_r` loop subgroup if
  each `b_i` acts on the left cosets `G ⧸ U` either trivially (then `s_i = 1`, a *looplet*) or as a
  single cycle of length `s_i` through the coset `U`, and two different generators move no common
  coset other than `U`.
* **Theorem 1 (`main`).** If `U` is an `s_1/…/s_r` loop subgroup of finite index, `r ≥ 3`, and at
  most `r − 2` of the `s_i` equal `1`, then an invertible integer matrix `M` equals `B(γ)` for an
  automorphism `γ` with `γ(U) = U` if and only if `v · M ≡ v (mod 2)`, where `v_i = 1` if `s_i` is
  even and `v_i = 0` otherwise. So `B(Stab U)` is a congruence subgroup of level 2, and all of
  `GL_r(ℤ)` when all loops are odd.
* **Existence (`exists_isLoopSubgroup`).** For all `s_i ≥ 1` the free group `FreeGroup ι` with its
  standard basis has an `s_1/…/s_r` loop subgroup, of index `1 + Σ (s_i − 1)`, so the hypotheses
  of Theorem 1 can be met.

**Differences from the paper in the statement of record.** Finite index of `U` is a hypothesis of
`main`; the paper works with subgroups of a fixed finite index throughout, and the library proves
that it follows from Definition 1 when all `s_i ≥ 1` (`IsLoopSubgroup.finiteIndex`, standard
basis). The cases excluded by the hypotheses (`r ≤ 2`, or `r − 1` looplets) are not covered by
`main`; the `r − 1` case is Proposition 18, proved in the library (`Excluded.lean`, standard basis)
but not part of the Challenge.

**Proof outline.** The upper bound (Proposition 16) holds for every finite-index subgroup: an
automorphism stabilizing `U` permutes the cosets compatibly with the action, so it preserves the
parity of each generator's permutation, which gives `v · B(γ) ≡ v`. For the lower bound one writes
down, for generators of the target group, automorphisms of the form `b_j ↦ w·x·b_j` stabilizing
`U`, where `w` is a commutator word chosen (Lemma 5) so that `w·x` acts trivially on the cosets; a
generating set of the principal congruence subgroup `Γ_2` (Remark 6) and of the vector stabilizer
`S(v)` in `GL_r(ℤ/2)` (Lemma 8) then gives everything.

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

## Possible future work via Tau Ceti

The thesis's congruence-level detection needs `Γ_l = ⟪X₁₂^l⟫` in `SL_r(ℤ)`, `r ≥ 3` (Mennicke,
Bass–Milnor–Serre). That would follow from the target `sinteger_relative_elementary_generation`
of the unclaimed Tau Ceti roadmap
[KTheoryLowDegrees](https://github.com/TauCetiProject/TauCetiRoadmap/tree/main/TauCetiRoadmap/KTheoryLowDegrees)
(Layers 9–11).

## Sources, previous work, licence

* **Sources.** The formalization follows the paper and, for proof details and the additional
  material, the Diplomarbeit (included). A literature search (zbMATH, Crossref, OpenAlex,
  Semantic Scholar, targeted full-text checks; Google Scholar and MathSciNet were not accessible)
  found no work citing, duplicating or generalizing the paper's main results; novelty of the
  mathematics is therefore as in the 2011 paper, and no claim beyond that is made.
* **Previous formalizations.** None known of these results. The development uses Mathlib and
  Tau Ceti (elementary matrices, generation of `SL_n(ℤ)`, Hopfian property and Schreier index
  formula for free groups).
* **Licence.** Apache-2.0 (`LICENSE`). The included thesis source is the author's.

## Building

```
lake exe cache get                                                              # Mathlib oleans
bash .lake/packages/TauCeti/scripts/lake-cache-get.sh .lake/packages/TauCeti   # Tau Ceti oleans
lake build
```
