module

public import LoopSubgroups.Existence

@[expose] public section

/-!
# Loop subgroups are determined by their loop lengths

Definition 1 implies finite index, and with respect to a fixed basis the loop lengths determine
the loop subgroup (as claimed after Definition 1 in the paper).
-/

open Equiv Equiv.Perm

set_option linter.unusedSectionVars false

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IsLoopSubgroup.finiteIndex {U : Subgroup (FreeGroup ι)} {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hs : ∀ i, 1 ≤ s i) : U.FiniteIndex := by
  set ρ := MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)
  set x₀ : FreeGroup ι ⧸ U := QuotientGroup.mk 1
  set S : Set (FreeGroup ι ⧸ U) := {x₀} ∪ ⋃ i, {x | ρ (.of i) x ≠ x}
  have hfin : S.Finite := by
    refine (Set.finite_singleton x₀).union (Set.finite_iUnion fun i => ?_)
    rcases hU.loop i with ⟨-, h1⟩ | ⟨-, hcard, -⟩
    · have h1' : ρ (.of i) = 1 := h1
      simp [h1']
    · exact Set.finite_of_ncard_pos (by rw [hcard]; exact hs i)
  have hstep : ∀ i x, x ∈ S → ρ (.of i) x ∈ S ∧ (ρ (.of i))⁻¹ x ∈ S := by
    intro i x hx
    by_cases hfix : ρ (.of i) x = x
    · refine ⟨by rwa [hfix], ?_⟩
      have : (ρ (.of i))⁻¹ x = x := by rw [Perm.inv_eq_iff_eq, hfix]
      rwa [this]
    · refine ⟨Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩), Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)⟩
      · exact fun h => hfix ((ρ (.of i)).injective h)
      · intro h
        apply hfix
        rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply, eq_comm, Perm.inv_eq_iff_eq] at h
        exact h.symm
  have hw : ∀ w, ∀ x ∈ S, ρ w x ∈ S := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => simp
    | of i => exact fun x hx => (hstep i x hx).1
    | inv_of i _ => intro x hx; rw [map_inv]; exact (hstep i x hx).2
    | mul a b ha hb => intro x hx; rw [map_mul, Perm.mul_apply]; exact ha _ (hb x hx)
  have huniv : (Set.univ : Set (FreeGroup ι ⧸ U)) ⊆ S := by
    intro q _
    induction q using QuotientGroup.induction_on with | H w =>
    have : ρ w x₀ = (w : FreeGroup ι ⧸ U) := by
      change w • ((1 : FreeGroup ι) : FreeGroup ι ⧸ U) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [← this]
    exact hw w x₀ (Or.inl rfl)
  have : Finite (FreeGroup ι ⧸ U) := Set.finite_univ_iff.mp (hfin.subset huniv)
  exact Subgroup.finiteIndex_of_finite_quotient
/-- The loop lengths determine the loop subgroup. -/
theorem IsLoopSubgroup.eq_loopSubgroup {U : Subgroup (FreeGroup ι)} {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hs : ∀ i, 1 ≤ s i) : U = loopSubgroup s := by
  classical
  have := hU.finiteIndex hs
  have : Fintype (FreeGroup ι ⧸ U) := Fintype.ofFinite _
  set ρ := MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)
  set x₀ : FreeGroup ι ⧸ U := QuotientGroup.mk 1
  have hpow : ∀ i, ρ (.of i) ^ s i = 1 := by
    intro i
    by_cases h1 : ρ (.of i) = 1
    · simp [h1]
    · rw [← hU.card_support h1, ← (hU.isCycle h1).orderOf, pow_orderOf_eq_one]
  have hmod : ∀ i m, ρ (.of i) ^ (m % s i) = ρ (.of i) ^ m := by
    intro i m
    conv_rhs => rw [← Nat.mod_add_div m (s i), pow_add, pow_mul, hpow, one_pow, mul_one]
  have hn : ∀ i, ρ (.of i) ≠ 1 → ∀ m : ℕ, (ρ (.of i) ^ m) x₀ = x₀ ↔ s i ∣ m := by
    intro i h1 m
    have hc := hU.isCycle h1
    have hx : ρ (.of i) x₀ ≠ x₀ := Equiv.Perm.mem_support.mp (hU.mem_support h1)
    rw [← hc.pow_eq_one_iff' hx, ← orderOf_dvd_iff_pow_eq_one, hc.orderOf, hU.card_support h1]
  -- the points of the `j`-th loop
  have hloop : ∀ j (k : Fin (s j - 1)), ρ (.of j) ≠ 1 ∧ (ρ (.of j) ^ (k.val + 1)) x₀ ≠ x₀ ∧
      ρ (.of j) ((ρ (.of j) ^ (k.val + 1)) x₀) ≠ (ρ (.of j) ^ (k.val + 1)) x₀ := by
    intro j k
    have hk := k.isLt
    have h1 : ρ (.of j) ≠ 1 := fun h => by have := hU.eq_one_iff.mp h; omega
    refine ⟨h1, fun h => ?_, ?_⟩
    · have := Nat.le_of_dvd (by omega) ((hn j h1 _).mp h); omega
    · rw [← Perm.mem_support]
      exact Perm.pow_apply_mem_support.mpr (hU.mem_support h1)
  -- injectivity within a loop
  have hinj : ∀ i, ∀ a b, a < s i → b < s i →
      (ρ (.of i) ^ a) x₀ = (ρ (.of i) ^ b) x₀ → a = b := by
    have key : ∀ i, ∀ a b, a ≤ b → b < s i →
        (ρ (.of i) ^ a) x₀ = (ρ (.of i) ^ b) x₀ → a = b := by
      intro i a b hab hb h
      by_cases h1 : ρ (.of i) = 1
      · rw [hU.eq_one_iff.mp h1] at hb; omega
      rw [← Nat.add_sub_cancel' hab, pow_add, Perm.mul_apply] at h
      have h' := ((hn i h1 _).mp ((ρ (.of i) ^ a).injective h).symm)
      rcases Nat.eq_zero_or_pos (b - a) with h0 | h0
      · omega
      · have := Nat.le_of_dvd h0 h'; omega
    intro i a b ha hb h
    rcases le_total a b with hab | hab
    · exact key i a b hab hb h
    · exact (key i b a hab ha h.symm).symm
  let f : LoopPt s → FreeGroup ι ⧸ U := fun y => match y with
    | none => x₀
    | some ⟨i, k⟩ => (ρ (.of i) ^ (k.val + 1)) x₀
  have hf : ∀ i n (hn : n < (loopList s i).length), f (loopList s i)[n] = (ρ (.of i) ^ n) x₀ := by
    intro i n hn
    cases n with
    | zero => rfl
    | succ n => simp [loopList, f]
  have hgen : ∀ i y, f (loopRep s (.of i) y) = ρ (.of i) (f y) := by
    intro i y
    rw [loopRep_of]
    by_cases hy : y ∈ loopList s i
    · obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hy
      rw [List.formPerm_apply_getElem _ (loopList_nodup s i), hf, hf, ← Perm.mul_apply,
        ← pow_succ', loopList_length, Nat.sub_add_cancel (hs i), hmod]
    · rw [List.formPerm_apply_of_notMem hy]
      obtain ⟨⟨j, k⟩, rfl⟩ : ∃ z, y = some z := by
        cases y with
        | none => exact absurd (mem_loopList.mpr (Or.inl rfl)) hy
        | some z => exact ⟨z, rfl⟩
      have hij : i ≠ j := by
        rintro rfl; exact hy (mem_loopList.mpr (Or.inr ⟨k, rfl⟩))
      obtain ⟨-, hne, hsupp⟩ := hloop j k
      by_contra hc
      exact hne (hU.inter i j hij _ (Ne.symm hc) hsupp)
  have hequiv : ∀ w y, f (loopRep s w y) = ρ w (f y) := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => simp
    | of i => exact hgen i
    | inv_of i _ =>
      intro y
      rw [map_inv, map_inv, eq_comm, Perm.inv_eq_iff_eq, ← hgen, ← Perm.mul_apply,
        mul_inv_cancel, Perm.one_apply]
    | mul a b ha hb => intro y; rw [map_mul, map_mul, Perm.mul_apply, Perm.mul_apply, ha, hb]
  have hfinj : Function.Injective f := by
    rintro (_ | ⟨i, k⟩) (_ | ⟨j, l⟩) h
    · rfl
    · exact absurd h.symm (hloop j l).2.1
    · exact absurd h (hloop i k).2.1
    · change (ρ (.of i) ^ (k.val + 1)) x₀ = (ρ (.of j) ^ (l.val + 1)) x₀ at h
      by_cases hij : i = j
      · subst hij
        have := hinj i _ _ (by omega) (by omega) h
        have hkl : k = l := Fin.ext (by omega)
        rw [hkl]
      · exfalso
        apply (hloop i k).2.1
        refine hU.inter i j hij _ (hloop i k).2.2 ?_
        rw [h]; exact (hloop j l).2.2
  ext w
  rw [← stabPt_toPermHom (U := U), mem_stabPt, loopSubgroup, mem_stabPt]
  change ρ w (f none) = f none ↔ _
  exact ⟨fun h => hfinj ((hequiv w none).trans h),
    fun h => (hequiv w none).symm.trans (congrArg f h)⟩
theorem IsLoopSubgroup.index_eq {U : Subgroup (FreeGroup ι)} {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hs : ∀ i, 1 ≤ s i) : U.index = 1 + ∑ i, (s i - 1) := by
  rw [hU.eq_loopSubgroup hs, index_loopSubgroup]

/-- **Theorem 1** without assuming finite index (which follows from Definition 1 when all
`s_i ≥ 1`). -/
theorem image_Stab_eq_of_isLoopSubgroup {U : Subgroup (FreeGroup ι)} {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hs : ∀ i, 1 ≤ s i) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    (Stab U).map B = (S (parityVec s)).comap reduce :=
  have := hU.finiteIndex hs
  image_Stab_eq hU hr hl

end LoopSubgroups
