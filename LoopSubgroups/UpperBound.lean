module

public import LoopSubgroups.LowerBound

@[expose] public section

/-!
# The upper bound (Section 8 of the paper)

**Proposition 16** holds for arbitrary subgroups of finite index: the image of `B(Stab(U))` in
`GL_r(ℤ/2ℤ)` stabilizes the vector `v` recording which generators act by odd permutations on the
cosets of `U`.
-/

open scoped Pointwise
open Equiv Equiv.Perm Matrix

set_option linter.unusedSectionVars false

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- `v_i = 0` if `ρ(g_i)` is an even permutation and `v_i = 1` if it is odd. -/
def signVec (ρ : FreeGroup ι →* Perm Ω) : ι → ZMod 2 :=
  fun i => if sign (ρ (.of i)) = 1 then 0 else 1

private def toSign (a : ZMod 2) : ℤˣ := if a = 0 then 1 else -1

private theorem toSign_add (a b : ZMod 2) : toSign (a + b) = toSign a * toSign b := by
  unfold toSign; revert a b; decide

private theorem toSign_neg (a : ZMod 2) : toSign (-a) = (toSign a)⁻¹ := by
  unfold toSign; revert a; decide

private theorem toSign_injective : Function.Injective toSign := by
  unfold toSign; intro a b; revert a b; decide

/-- The sign of `ρ(w)` is determined by the exponent sums of the odd generators in `w`. -/
private theorem sign_eq_toSign (ρ : FreeGroup ι →* Perm Ω) (w : FreeGroup ι) :
    sign (ρ w) = toSign (∑ j, (count j w : ZMod 2) * signVec ρ j) := by
  induction w using FreeGroup.induction_on with
  | one => simp [toSign]
  | of i =>
    show sign (ρ (.of i)) = toSign (∑ j, (count j (.of i) : ZMod 2) * signVec ρ j)
    simp only [count_of, Int.cast_ite, Int.cast_one, Int.cast_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, signVec]
    rcases Int.units_eq_one_or (sign (ρ (.of i))) with h | h <;> simp [h, toSign]
  | inv_of i ih =>
    simp only [map_inv, count_inv, Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
      toSign_neg, ih]
  | mul x y hx hy =>
    simp only [map_mul, count_mul, Int.cast_add, add_mul, Finset.sum_add_distrib, toSign_add,
      hx, hy]

/-- **Proposition 16** (for a general permutation representation): if `ρ ∘ γ` is conjugate to `ρ`,
then `v · B(γ) ≡ v (mod 2)`. -/
theorem reduce_B_mem_S {ρ : FreeGroup ι →* Perm Ω} {γ : MulAut (FreeGroup ι)} (c : Perm Ω)
    (hc : ∀ w, ρ (γ w) = c * ρ w * c⁻¹) : reduce (B γ) ∈ S (signVec ρ) := by
  rw [mem_S]
  ext i
  have h1 := sign_eq_toSign ρ (γ (.of i))
  rw [hc, map_mul, map_mul, map_inv, mul_comm (sign c), mul_assoc, mul_inv_cancel, mul_one,
    sign_eq_toSign] at h1
  have h2 := toSign_injective h1
  simp only [count_of, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [h2]
  simp [vecMul, dotProduct, B_apply, mul_comm]

/-! ### Automorphisms in the stabilizer permute the cosets -/

section Coset

variable {U : Subgroup (FreeGroup ι)}

theorem mem_iff_of_mem_Stab {γ : MulAut (FreeGroup ι)} (hγ : γ ∈ Stab U) (w : FreeGroup ι) :
    γ w ∈ U ↔ w ∈ U := mem_Stab_iff.mp hγ w

/-- For `γ ∈ Stab(U)`, the permutation `π(γ) : vU ↦ γ(v)U` of the left cosets of `U`. -/
def cosetPerm {γ : MulAut (FreeGroup ι)} (hγ : γ ∈ Stab U) : Perm (FreeGroup ι ⧸ U) :=
  Quotient.congr γ.toEquiv fun a b => by
    simp only [QuotientGroup.leftRel_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      ← map_inv, ← map_mul, mem_iff_of_mem_Stab hγ]

theorem cosetPerm_mk {γ : MulAut (FreeGroup ι)} (hγ : γ ∈ Stab U) (v : FreeGroup ι) :
    cosetPerm hγ (v : FreeGroup ι ⧸ U) = (γ v : FreeGroup ι ⧸ U) := rfl

/-- **Remark 3 (3).** For `γ ∈ Stab(U)`, `π(γ(w)) = π(γ) ∘ π(w) ∘ π(γ)⁻¹`. -/
theorem toPermHom_aut {γ : MulAut (FreeGroup ι)} (hγ : γ ∈ Stab U) (w : FreeGroup ι) :
    MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U) (γ w) =
      cosetPerm hγ * MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U) w * (cosetPerm hγ)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  ext q
  induction q using QuotientGroup.induction_on with
  | H v =>
    simp only [Perm.mul_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply, cosetPerm_mk,
      MulAction.Quotient.smul_mk, smul_eq_mul, map_mul]

/-- The stabilizer of the base coset `U` under the coset action is `U`. -/
theorem stabPt_toPermHom :
    stabPt (MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)) (QuotientGroup.mk 1) = U := by
  ext w
  rw [mem_stabPt]
  show w • ((1 : FreeGroup ι) : FreeGroup ι ⧸ U) = ((1 : FreeGroup ι) : FreeGroup ι ⧸ U) ↔ _
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]

/-- **Proposition 16.** Let `U ≤ F_r` have finite index and let `v_i = 0` if `π(g_i)` is an even
permutation of the cosets of `U` and `1` otherwise. Then `B(Stab(U))` maps into `S(v)`. -/
theorem image_le_comap_S [Fintype (FreeGroup ι ⧸ U)] [DecidableEq (FreeGroup ι ⧸ U)] :
    (Stab U).map B ≤
      (S (signVec (MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)))).comap reduce := by
  rintro _ ⟨γ, hγ, rfl⟩
  exact reduce_B_mem_S _ (toPermHom_aut hγ)

end Coset

end LoopSubgroups
