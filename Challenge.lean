module

public import Mathlib

@[expose] public section

/-!
# Loop subgroups of `F_r` and the image of their stabilizer subgroups in `GL_r(ℤ)`

This file states the main theorem of

  J. Breitner, *Loop subgroups of `F_r` and the image of their stabilizer subgroups in `GL_r(ℤ)`*,
  Israel J. Math. 191 (2012), 545–557, doi:10.1007/s11856-011-0213-3, arXiv:1012.2729.

Let `G` be a free group with basis `b = (b_i)_{i ∈ ι}` of finite rank `r = |ι|`. The group
`Aut(G)` acts on the subgroups of `G`; `Stab(U)` is the stabilizer of `U`. Every automorphism `γ`
induces an automorphism of the abelianization `ℤ^r`, with matrix
`B(γ)_{ij} = #_{b_i} γ(b_j)` (the exponent sum of `b_i` in `γ(b_j)`), giving
`B : Aut(G) → GL_r(ℤ)`.

A subgroup `U` is an `s_1/…/s_r` *loop subgroup* (with respect to `b`) if each `b_i` acts on the
left cosets of `U` as a single cycle of length `s_i` through the coset `U` (trivially if
`s_i = 1`, a *looplet*), and these cycles meet only in the coset `U`.

**Theorem 1** (`main`). If `r ≥ 3` and at most `r − 2` of the `s_i` equal `1`, then a matrix
`M ∈ GL_r(ℤ)` is of the form `B(γ)` with `γ ∈ Stab(U)` iff `v · M ≡ v (mod 2)`, where `v` is the
row vector with `v_i = 1` if `s_i` is even and `v_i = 0` if `s_i` is odd.

**Existence** (`exists_isLoopSubgroup`). For every `s` with all `s_i ≥ 1` there is an
`s_1/…/s_r` loop subgroup of the free group `FreeGroup ι` (with its standard basis); it has index
`1 + ∑ (s_i − 1)`. So the hypotheses of Theorem 1 are satisfiable.

The finite index of `U` is assumed in Theorem 1, as in the paper (which studies subgroups of a
fixed index `n`).
-/

namespace LoopSubgroups.Challenge

/-- `expSum i w` is the exponent sum `#_{g_i} w` of the generator `g_i = FreeGroup.of i` in the
word `w`, as an element of `Multiplicative ℤ`. -/
noncomputable def expSum {ι : Type*} [DecidableEq ι] (i : ι) : FreeGroup ι →* Multiplicative ℤ :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if j = i then 1 else 0)

/-- The matrix `B_b(γ)` of an automorphism `γ` of `G` on the abelianization, in the basis `b`:
its `(i, j)` entry is the exponent sum of `b i` in `γ (b j)`, i.e. of `g_i` in `b.repr (γ (b j))`.
Column `j` is the abelianization of `γ (b j)`. -/
noncomputable def autMatrix {ι G : Type*} [Group G] [DecidableEq ι] (b : FreeGroupBasis ι G)
    (γ : MulAut G) : Matrix ι ι ℤ :=
  Matrix.of fun i j => Multiplicative.toAdd (expSum i (b.repr (γ (b j))))

/-- **Definition 1.** `U ≤ G` is an `s_1/…/s_r` loop subgroup with respect to the basis `b`: for
each `i`, the action `x ↦ b i • x` of `b i` on the left cosets `G ⧸ U` is either trivial with
`s i = 1`, or a single cycle whose support has `s i` elements and contains the coset `U`; and two
different generators move no common coset other than `U`. -/
structure IsLoopSubgroup {ι G : Type*} [Group G] (b : FreeGroupBasis ι G) (U : Subgroup G)
    (s : ι → ℕ) : Prop where
  loop : ∀ i, (s i = 1 ∧ ∀ x : G ⧸ U, b i • x = x) ∨
    ((MulAction.toPerm (b i) : Equiv.Perm (G ⧸ U)).IsCycle ∧
      {x : G ⧸ U | b i • x ≠ x}.ncard = s i ∧
      b i • ((1 : G) : G ⧸ U) ≠ ((1 : G) : G ⧸ U))
  inter : ∀ i j, i ≠ j → ∀ x : G ⧸ U, b i • x ≠ x → b j • x ≠ x → x = ((1 : G) : G ⧸ U)

/-- **Theorem 1.** For an `s_1/…/s_r` loop subgroup `U` of finite index, `r ≥ 3`, with at most
`r − 2` looplets: an invertible integer matrix `M` is `B(γ)` for an automorphism `γ` with
`γ(U) = U` iff `v · M ≡ v (mod 2)`, where `v_i = 1` if `s_i` is even and `v_i = 0` if it is odd.
That is, `B(Stab(U)) = {M ∈ GL_r(ℤ) | v · M ≡ v (mod 2)}`. -/
theorem main {ι G : Type*} [Group G] [Fintype ι] [DecidableEq ι] (b : FreeGroupBasis ι G)
    (U : Subgroup G) [U.FiniteIndex] (s : ι → ℕ) (hU : IsLoopSubgroup b U s)
    (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (fun i => s i = 1)).card ≤ Fintype.card ι - 2) (M : GL ι ℤ) :
    (∃ γ : MulAut G, U.map γ.toMonoidHom = U ∧ autMatrix b γ = (M : Matrix ι ι ℤ)) ↔
      ∀ j, (∑ i, (if Even (s i) then 1 else 0) * (M : Matrix ι ι ℤ) i j) ≡
        (if Even (s j) then 1 else 0) [ZMOD 2] := by
  sorry

/-- **Existence of loop subgroups.** For every `s` with all `s_i ≥ 1`, the free group
`FreeGroup ι` with its standard basis has an `s_1/…/s_r` loop subgroup, of index
`1 + ∑ (s_i − 1)`. -/
theorem exists_isLoopSubgroup {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    (hs : ∀ i, 1 ≤ s i) :
    ∃ U : Subgroup (FreeGroup ι), U.index = 1 + ∑ i, (s i - 1) ∧
      IsLoopSubgroup (FreeGroupBasis.ofFreeGroup ι) U s := by
  sorry

end LoopSubgroups.Challenge
