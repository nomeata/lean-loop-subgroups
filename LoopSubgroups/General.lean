import LoopSubgroups.Transfer
import LoopSubgroups.Excluded

/-!
# The main theorem for an arbitrary free group with an arbitrary basis

Definition 1 asks for *some* basis `{g_1, …, g_r}` of `F_r`, and `B` is defined with respect to
that basis. Here `G` is any group with a free basis `b : FreeGroupBasis ι G`, and we transport the
main theorem from `FreeGroup ι` along `b.repr : G ≃* FreeGroup ι`.
-/

open scoped Pointwise
open Equiv Equiv.Perm

set_option linter.unusedSectionVars false

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Group G]

/-- **Definition 9** for a basis `b`: `B_b(γ) = (#_{b_i} γ(b_j))_{i,j}`. -/
noncomputable def Bb (b : FreeGroupBasis ι G) : MulAut G →* GL ι ℤ :=
  B.comp (MulAut.congr b.repr).toMonoidHom

theorem Bb_apply (b : FreeGroupBasis ι G) (γ : MulAut G) (i j : ι) :
    (Bb b γ : Matrix ι ι ℤ) i j = count i (b.repr (γ (b j))) := rfl

/-- **Definition 1** for a basis `b` of `G`: the action of each `b_i` on the left cosets of `U` is a
single cycle of length `s_i` through the coset `U` (trivial if `s_i = 1`), and these cycles are
otherwise disjoint. -/
def IsLoopSubgroupWrt (b : FreeGroupBasis ι G) (U : Subgroup G) (s : ι → ℕ) : Prop :=
  IsLoopRep ((MulAction.toPermHom G (G ⧸ U)).comp (b.repr.symm : FreeGroup ι →* G))
    (QuotientGroup.mk 1) s

theorem IsLoopSubgroupWrt.of_apply {b : FreeGroupBasis ι G} {U : Subgroup G} (i : ι) (q : G ⧸ U) :
    ((MulAction.toPermHom G (G ⧸ U)).comp (b.repr.symm : FreeGroup ι →* G)) (.of i) q = b i • q :=
  rfl

/-- The coset spaces of `U ≤ G` and of `b.repr(U) ≤ FreeGroup ι` are equivariantly isomorphic. -/
def quotientMapEquiv (φ : G ≃* FreeGroup ι) (U : Subgroup G) :
    FreeGroup ι ⧸ U.map φ.toMonoidHom ≃ G ⧸ U :=
  Quotient.congr φ.symm.toEquiv fun a b => by
    simp only [QuotientGroup.leftRel_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_equiv

/-- **Theorem 1** for an arbitrary free group `G` with basis `b`: if `U ≤ G` is an `s_1/…/s_r` loop
subgroup with respect to `b`, `r ≥ 3`, with at most `r - 2` looplets, then
`B_b(Stab_{Aut G}(U)) = {M ∈ GL_r(ℤ) | v · M ≡ v (mod 2)}`. -/
theorem image_stabilizer_eq (b : FreeGroupBasis ι G) {U : Subgroup G} [U.FiniteIndex]
    {s : ι → ℕ} (hU : IsLoopSubgroupWrt b U s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    (MulAction.stabilizer (MulAut G) U).map (Bb b) = (S (parityVec s)).comap reduce := by
  set φ := b.repr with hφ
  set U' := U.map φ.toMonoidHom with hU'def
  have hU' : IsLoopSubgroup U' s := by
    refine hU.of_equiv (quotientMapEquiv φ U) (fun w q => ?_) (by
      show ((φ.symm 1 : G) : G ⧸ U) = _; rw [map_one])
    induction q using QuotientGroup.induction_on with | H a =>
    change ((φ.symm (w * a) : G) : G ⧸ U) = φ.symm w • ((φ.symm a : G) : G ⧸ U)
    rw [map_mul, MulAction.Quotient.smul_mk, smul_eq_mul]
  have : Finite (FreeGroup ι ⧸ U') := Finite.of_equiv _ (quotientMapEquiv φ U).symm
  have : U'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hStab : (MulAction.stabilizer (MulAut G) U).map (MulAut.congr φ).toMonoidHom = Stab U' := by
    ext δ
    rw [Subgroup.mem_map_equiv, mem_stabilizer_subgroup_iff, mem_Stab_iff]
    constructor
    · intro h w
      have := h (φ.symm w)
      simp only [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at this
      rw [hU'def, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, ← this]
    · intro h g
      have := h (φ g)
      rw [hU'def, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
      simpa only [MulAut.congr_symm_apply, MulEquiv.trans_apply] using this
  rw [Bb, ← Subgroup.map_map, hStab]
  exact image_Stab_eq hU' hr hl

end LoopSubgroups
