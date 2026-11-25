module

public import Mathlib
public import LoopSubgroups

@[expose] public section

/-!
# Solution

Proofs of the statements in `Challenge.lean`. The definitions are repeated verbatim from
`Challenge.lean`; the theorems are derived from the library `LoopSubgroups`:

* `main` from `LoopSubgroups.image_stabilizer_eq` (Theorem 1 for an arbitrary basis), after
  identifying `autMatrix` with `LoopSubgroups.Bb` and `IsLoopSubgroup` with
  `LoopSubgroups.IsLoopSubgroupWrt`;
* `exists_isLoopSubgroup` from the explicit model `LoopSubgroups.loopSubgroup`
  (`LoopSubgroups.isLoopSubgroup_loopSubgroup`, `LoopSubgroups.index_loopSubgroup`).
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

/-! ### Bridges to the library -/

theorem expSum_eq {ι : Type*} [DecidableEq ι] (i : ι) :
    expSum i = (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : ι => ℤ) i)).comp
      LoopSubgroups.ab := by
  ext j : 1
  simp [expSum, Pi.single_apply, eq_comm]

theorem toAdd_expSum {ι : Type*} [DecidableEq ι] (i : ι) (w : FreeGroup ι) :
    Multiplicative.toAdd (expSum i w) = LoopSubgroups.count i w := by
  rw [expSum_eq]
  rfl

theorem autMatrix_eq {ι G : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    (b : FreeGroupBasis ι G) (γ : MulAut G) :
    autMatrix b γ = (LoopSubgroups.Bb b γ : Matrix ι ι ℤ) := by
  ext i j
  rw [LoopSubgroups.Bb_apply]
  simp [autMatrix, toAdd_expSum]

theorem toPerm_eq {ι G : Type*} [Group G] [Fintype ι] [DecidableEq ι] (b : FreeGroupBasis ι G)
    (U : Subgroup G) (i : ι) :
    ((MulAction.toPermHom G (G ⧸ U)).comp (b.repr.symm : FreeGroup ι →* G)) (.of i) =
      MulAction.toPerm (b i) :=
  Equiv.ext fun q => LoopSubgroups.IsLoopSubgroupWrt.of_apply i q

theorem isLoopSubgroup_iff {ι G : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    (b : FreeGroupBasis ι G) (U : Subgroup G) (s : ι → ℕ) :
    IsLoopSubgroup b U s ↔ LoopSubgroups.IsLoopSubgroupWrt b U s := by
  unfold LoopSubgroups.IsLoopSubgroupWrt
  constructor
  · rintro ⟨hl, hi⟩
    refine ⟨fun i => ?_, fun i j hij x => ?_⟩
    · simp only [toPerm_eq, MulAction.toPerm_apply, Equiv.Perm.ext_iff, Equiv.Perm.one_apply]
      exact hl i
    · simp only [toPerm_eq, MulAction.toPerm_apply]
      exact hi i j hij x
  · rintro ⟨hl, hi⟩
    refine ⟨fun i => ?_, fun i j hij x => ?_⟩
    · have := hl i
      simp only [toPerm_eq, MulAction.toPerm_apply, Equiv.Perm.ext_iff,
        Equiv.Perm.one_apply] at this
      exact this
    · have := hi i j hij x
      simp only [toPerm_eq, MulAction.toPerm_apply] at this
      exact this

theorem mem_comap_S_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ) (M : GL ι ℤ) :
    M ∈ (LoopSubgroups.S (LoopSubgroups.parityVec s)).comap LoopSubgroups.reduce ↔
      ∀ j, (∑ i, (if Even (s i) then 1 else 0) * (M : Matrix ι ι ℤ) i j) ≡
        (if Even (s j) then 1 else 0) [ZMOD 2] := by
  rw [Subgroup.mem_comap, LoopSubgroups.mem_S, funext_iff]
  refine forall_congr' fun j => ?_
  change _ ↔ _ ≡ _ [ZMOD ((2 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast [apply_ite (Int.cast : ℤ → ZMod 2)]
  simp [Matrix.vecMul, dotProduct, LoopSubgroups.parityVec, LoopSubgroups.reduce]

open scoped Pointwise in
theorem mem_stabilizer_iff_map_eq {G : Type*} [Group G] (U : Subgroup G) (γ : MulAut G) :
    γ ∈ MulAction.stabilizer (MulAut G) U ↔ U.map γ.toMonoidHom = U := by
  rw [LoopSubgroups.mem_stabilizer_subgroup_iff]
  constructor
  · intro h
    ext w
    rw [Subgroup.mem_map_equiv, ← h, MulEquiv.apply_symm_apply]
  · intro h w
    conv_lhs => rw [← h]
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-! ### The theorems of `Challenge.lean` -/

theorem main {ι G : Type*} [Group G] [Fintype ι] [DecidableEq ι] (b : FreeGroupBasis ι G)
    (U : Subgroup G) [U.FiniteIndex] (s : ι → ℕ) (hU : IsLoopSubgroup b U s)
    (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (fun i => s i = 1)).card ≤ Fintype.card ι - 2) (M : GL ι ℤ) :
    (∃ γ : MulAut G, U.map γ.toMonoidHom = U ∧ autMatrix b γ = (M : Matrix ι ι ℤ)) ↔
      ∀ j, (∑ i, (if Even (s i) then 1 else 0) * (M : Matrix ι ι ℤ) i j) ≡
        (if Even (s j) then 1 else 0) [ZMOD 2] := by
  have key := LoopSubgroups.image_stabilizer_eq b ((isLoopSubgroup_iff b U s).mp hU) hr
    (by omega)
  rw [← mem_comap_S_iff, ← key]
  constructor
  · rintro ⟨γ, hγ, hM⟩
    exact ⟨γ, (mem_stabilizer_iff_map_eq U γ).mpr hγ, Units.ext (by rw [← hM, autMatrix_eq])⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, (mem_stabilizer_iff_map_eq U γ).mp hγ, autMatrix_eq b γ⟩

theorem exists_isLoopSubgroup {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    (hs : ∀ i, 1 ≤ s i) :
    ∃ U : Subgroup (FreeGroup ι), U.index = 1 + ∑ i, (s i - 1) ∧
      IsLoopSubgroup (FreeGroupBasis.ofFreeGroup ι) U s := by
  refine ⟨LoopSubgroups.loopSubgroup s, LoopSubgroups.index_loopSubgroup s, ?_⟩
  rw [isLoopSubgroup_iff]
  have h := LoopSubgroups.isLoopSubgroup_loopSubgroup hs
  unfold LoopSubgroups.IsLoopSubgroupWrt
  unfold LoopSubgroups.IsLoopSubgroup at h
  convert h using 2
  apply FreeGroup.ext_hom
  intro a
  simp [FreeGroupBasis.ofFreeGroup]

end LoopSubgroups.Challenge
