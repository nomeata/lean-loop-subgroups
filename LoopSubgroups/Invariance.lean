import LoopSubgroups.General

/-!
# Two small statements from the paper

* **Remark 3 (2):** `π(w) = Id ⟺ w ∈ NT(U) := ⋂_v v⁻¹ U v`.
* After **Definition 1**: "This definition is invariant under the natural action of `Aut(F_r)` on
  subgroups of `F_r`": if `U` is an `s_1/…/s_r` loop subgroup with respect to the basis `b`, then
  `γ(U)` is one with respect to the basis `γ(b)`.
-/

open Equiv

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Group G]

/-- **Remark 3 (2).** `π(w) = Id` iff `w` lies in the normal core of `U`. -/
theorem toPermHom_eq_one_iff (U : Subgroup G) (w : G) :
    MulAction.toPermHom G (G ⧸ U) w = 1 ↔ w ∈ U.normalCore := by
  rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker]

/-- **Invariance of Definition 1** under `Aut(F_r)`. -/
theorem IsLoopSubgroupWrt.map {b : FreeGroupBasis ι G} {U : Subgroup G} {s : ι → ℕ}
    (hU : IsLoopSubgroupWrt b U s) (γ : MulAut G) :
    IsLoopSubgroupWrt (b.map γ) (U.map γ.toMonoidHom) s := by
  let e : G ⧸ U.map γ.toMonoidHom ≃ G ⧸ U :=
    Quotient.congr γ.symm.toEquiv fun x y => by
      simp only [QuotientGroup.leftRel_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
      rw [← map_inv, ← map_mul]
      exact Subgroup.mem_map_equiv
  refine IsLoopRep.of_equiv hU e (fun w q => ?_) ?_
  · induction q using QuotientGroup.induction_on with | H a =>
    change ((γ.symm ((b.map γ).repr.symm w * a) : G) : G ⧸ U) =
      b.repr.symm w • ((γ.symm a : G) : G ⧸ U)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, map_mul]
    congr 2
    simp [FreeGroupBasis.map]
  · change ((γ.symm 1 : G) : G ⧸ U) = _
    rw [map_one]

end LoopSubgroups
