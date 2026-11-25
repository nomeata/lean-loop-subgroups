import LoopSubgroups.Existence
import TauCeti.GroupTheory.FreeGroup.Hopfian
import TauCeti.GroupTheory.FreeGroup.Schreier

/-!
# A free basis of the loop subgroup (paper, after Example 2)

With respect to the basis `g_1, …, g_r`, the `s_1/…/s_r` loop subgroup has the free basis
`{g_i^{s_i}} ∪ {g_i^{-k} g_j g_i^k | i ≠ j, 1 ≤ k ≤ s_i - 1}`.
-/

open Equiv

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Index type of the basis: `inl i` for `g_i^{s_i}`, and `inr ⟨i, j, k⟩` for
`g_i^{-(k+1)} g_j g_i^{k+1}`. -/
abbrev LoopBasisIdx (s : ι → ℕ) := ι ⊕ (Σ i : ι, {j : ι // j ≠ i} × Fin (s i - 1))

/-- The proposed basis elements. -/
def loopBasisFun (s : ι → ℕ) : LoopBasisIdx s → FreeGroup ι
  | .inl i => FreeGroup.of i ^ s i
  | .inr ⟨i, j, k⟩ => FreeGroup.of i ^ (-((k : ℤ) + 1)) * FreeGroup.of j.1 *
      FreeGroup.of i ^ ((k : ℤ) + 1)

omit [Fintype ι] [DecidableEq ι] in
private theorem zpow_natCast_add_one' (g : FreeGroup ι) (n : ℕ) :
    g ^ ((n : ℤ) + 1) = g ^ (n + 1) := by
  rw [← zpow_natCast]; push_cast; rfl

theorem loopRep_of_none (s : ι → ℕ) (i : ι) :
    loopRep s (.of i) none = if h : 0 < s i - 1 then some ⟨i, ⟨0, h⟩⟩ else none := by
  have hlen : 0 < (loopList s i).length := by simp [loopList]
  have := List.formPerm_apply_getElem (loopList s i) (loopList_nodup s i) 0 hlen
  rw [loopRep_of]
  have h0 : (loopList s i)[0] = none := rfl
  rw [h0] at this
  rw [this]
  split_ifs with h
  · simp [loopList, Nat.mod_eq_of_lt (show 1 < s i - 1 + 1 by omega)]
  · have : s i - 1 = 0 := by omega
    simp [loopList, this]

theorem loopRep_of_some_self (s : ι → ℕ) (i : ι) (k : Fin (s i - 1)) :
    loopRep s (.of i) (some ⟨i, k⟩) =
      if h : k.val + 1 < s i - 1 then some ⟨i, ⟨k.val + 1, h⟩⟩ else none := by
  have hlen : k.val + 1 < (loopList s i).length := by simp [loopList]
  have := List.formPerm_apply_getElem (loopList s i) (loopList_nodup s i) (k.val + 1) hlen
  rw [loopRep_of]
  have h0 : (loopList s i)[k.val + 1] = some ⟨i, k⟩ := by simp [loopList]
  rw [h0] at this
  rw [this]
  split_ifs with h
  · simp [loopList, Nat.mod_eq_of_lt (show k.val + 1 + 1 < s i - 1 + 1 by omega)]
  · have : k.val + 1 = s i - 1 := by omega
    simp [loopList, this]

theorem loopRep_of_some_ne (s : ι → ℕ) {i j : ι} (h : j ≠ i) (k : Fin (s j - 1)) :
    loopRep s (.of i) (some ⟨j, k⟩) = some ⟨j, k⟩ := by
  rw [loopRep_of]
  refine List.formPerm_apply_of_notMem fun hm => ?_
  rcases mem_loopList.mp hm with h' | ⟨l, hl⟩
  · simp at h'
  · simp only [Option.some.injEq, Sigma.mk.inj_iff] at hl
    exact h hl.1


theorem loopRep_pow_none (s : ι → ℕ) (i : ι) (k : Fin (s i - 1)) :
    loopRep s (FreeGroup.of i ^ (k.val + 1)) none = some ⟨i, k⟩ := by
  have hlen : 0 < (loopList s i).length := by simp [loopList]
  have := List.formPerm_pow_apply_getElem (loopList s i) (loopList_nodup s i) (k.val + 1) 0 hlen
  rw [map_pow, loopRep_of]
  have hk : (0 + (k.val + 1)) % (loopList s i).length = k.val + 1 := by
    rw [loopList_length]; have := k.isLt; rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp only [hk] at this
  have h0 : (loopList s i)[0] = none := rfl
  rw [h0] at this
  rw [this]
  simp [loopList, List.getElem_cons_succ]

theorem loopBasisFun_mem (s : ι → ℕ) (x : LoopBasisIdx s) : loopBasisFun s x ∈ loopSubgroup s := by
  rw [loopSubgroup, mem_stabPt]
  rcases x with i | ⟨i, j, k⟩
  · rcases Nat.eq_zero_or_pos (s i) with h | h
    · simp [loopBasisFun, h]
    · have : s i = (loopList s i).length := by rw [loopList_length]; omega
      simp only [loopBasisFun, map_pow, loopRep_of]
      rw [this, List.formPerm_pow_length_eq_one_of_nodup _ (loopList_nodup s i)]
      rfl
  · have h1 := loopRep_pow_none s i k
    have h2 := loopRep_of_some_ne s (Ne.symm j.2) k
    simp only [loopBasisFun, zpow_neg, zpow_natCast_add_one', map_mul, map_inv, Perm.mul_apply,
      h1, h2, Perm.inv_eq_iff_eq]

/-- The coset representatives `1` and `g_i^{k+1}`. -/
def loopTr (s : ι → ℕ) : LoopPt s → FreeGroup ι
  | none => 1
  | some ⟨i, k⟩ => FreeGroup.of i ^ (k.val + 1)

theorem loopTr_mem_closure {s : ι → ℕ} (hs : ∀ i, 1 ≤ s i) (w : FreeGroup ι) (p : LoopPt s) :
    (loopTr s (loopRep s w p))⁻¹ * w * loopTr s p ∈
      Subgroup.closure (Set.range (loopBasisFun s)) := by
  set K := Subgroup.closure (Set.range (loopBasisFun s))
  induction w using FreeGroup.induction_on generalizing p with
  | one => simp
  | of i =>
    rcases p with _ | ⟨j, k⟩
    · rw [loopRep_of_none]
      split_ifs with h
      · convert K.one_mem using 1; simp [loopTr]
      · have : s i = 1 := by have := hs i; omega
        refine Subgroup.subset_closure ⟨.inl i, ?_⟩
        simp [loopTr, loopBasisFun, this]
    · by_cases hji : j = i
      · subst hji
        rw [loopRep_of_some_self]
        split_ifs with h
        · convert K.one_mem using 1; simp only [loopTr]; group
        · refine Subgroup.subset_closure ⟨.inl j, ?_⟩
          simp only [loopTr, loopBasisFun, inv_one, one_mul]
          rw [← pow_succ']
          congr 1
          omega
      · rw [loopRep_of_some_ne s hji]
        refine Subgroup.subset_closure ⟨.inr ⟨j, ⟨i, Ne.symm hji⟩, k⟩, ?_⟩
        simp only [loopTr, loopBasisFun, zpow_neg, zpow_natCast_add_one']
  | inv_of i ih =>
    set q := (loopRep s (.of i))⁻¹ p
    have hq : loopRep s (.of i) q = p := by simp [q]
    have := K.inv_mem (ih q)
    rw [hq] at this
    simp only [mul_inv_rev, inv_inv, ← mul_assoc] at this
    simpa [map_inv, q] using this
  | mul a b iha ihb =>
    have := K.mul_mem (iha (loopRep s b p)) (ihb p)
    simp only [map_mul, Perm.mul_apply]
    convert this using 1
    group

theorem closure_loopBasisFun {s : ι → ℕ} (hs : ∀ i, 1 ≤ s i) :
    Subgroup.closure (Set.range (loopBasisFun s)) = loopSubgroup s := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun w hw => ?_
  · rintro - ⟨x, rfl⟩
    exact loopBasisFun_mem s x
  · have := loopTr_mem_closure hs w none
    rw [loopSubgroup, mem_stabPt] at hw
    simpa [hw, loopTr] using this

/-- The words `g_i^{s_i}` and `g_i^{-k} g_j g_i^k` form a free basis of the loop subgroup. -/
theorem exists_basis_loopSubgroup {s : ι → ℕ} (hs : ∀ i, 1 ≤ s i) :
    ∃ b : FreeGroupBasis (LoopBasisIdx s) (loopSubgroup s),
      ∀ x, (b x : FreeGroup ι) = loopBasisFun s x := by
  set U := loopSubgroup s
  let f : FreeGroup (LoopBasisIdx s) →* U :=
    FreeGroup.lift fun x => ⟨loopBasisFun s x, loopBasisFun_mem s x⟩
  have hf' : U.subtype.comp f = FreeGroup.lift (loopBasisFun s) :=
    FreeGroup.ext_hom _ _ fun x => by simp [f]
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (FreeGroup.lift (loopBasisFun s)).range := by
      rw [FreeGroup.range_lift_eq_closure, closure_loopBasisFun hs]; exact hy
    obtain ⟨x, hx⟩ := hy'
    refine ⟨x, Subtype.ext ?_⟩
    exact (DFunLike.congr_fun hf' x).trans hx
  let c := IsFreeGroup.basis U
  have hcard : Nat.card (LoopBasisIdx s) ≤ Nat.card (IsFreeGroup.Generators U) := by
    rw [← c.rank_eq_nat_card]
    have h := U.rank_add_index_eq_index_mul_natCard_add_one
    rw [show U.index = _ from index_loopSubgroup s] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin] at h ⊢
    have hne : ∀ x : ι, Fintype.card {j // j ≠ x} = Fintype.card ι - 1 := fun x => by simp
    simp only [hne, ← Finset.mul_sum] at h ⊢
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
    · simp [h0]
    · obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hm] at h ⊢
      simp only [Nat.add_sub_cancel] at h ⊢
      nlinarith
  have hinj := c.injective_of_surjective_of_card_le hsurj hcard
  refine ⟨FreeGroupBasis.ofRepr (MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
  show ((f (FreeGroup.of x) : U) : FreeGroup ι) = _
  simp [f]

end LoopSubgroups
