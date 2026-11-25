module

public import LoopSubgroups.Transfer
public import LoopSubgroups.Main

@[expose] public section

/-!
# Existence of loop subgroups

For every `s : ι → ℕ` with all `s_i ≥ 1` we construct the `s_1/…/s_r` loop subgroup explicitly,
as the stabilizer of the base point of the action of `F_r` on its coset graph (cf. Figure 1 of the
paper): the vertices are the base point `U` and, for every `i`, the `s_i - 1` further points
`g_i U, …, g_i^{s_i - 1} U` of the `i`-th loop. This shows that the hypotheses of the main theorem
are satisfiable; we also compute the index `[F_r : U] = 1 + ∑ (s_i - 1)`.
-/

open Equiv Equiv.Perm

set_option linter.unusedSectionVars false

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vertices of the coset graph of the `s_1/…/s_r` loop subgroup: the base point `none` and
the points `some ⟨i, k⟩`, standing for `g_i^{k+1} U`, `k < s_i - 1`. -/
abbrev LoopPt (s : ι → ℕ) := Option (Σ i : ι, Fin (s i - 1))

/-- The `i`-th loop `U, g_i U, …, g_i^{s_i - 1} U`. -/
def loopList (s : ι → ℕ) (i : ι) : List (LoopPt s) :=
  none :: (List.finRange (s i - 1)).map fun k => some ⟨i, k⟩

/-- The action of `F_r` on the coset graph: `g_i` cycles through the `i`-th loop. -/
def loopRep (s : ι → ℕ) : FreeGroup ι →* Perm (LoopPt s) :=
  FreeGroup.lift fun i => (loopList s i).formPerm

/-- The `s_1/…/s_r` loop subgroup with respect to the standard basis. -/
def loopSubgroup (s : ι → ℕ) : Subgroup (FreeGroup ι) := stabPt (loopRep s) none

theorem loopList_nodup (s : ι → ℕ) (i : ι) : (loopList s i).Nodup := by
  simp only [loopList, List.nodup_cons, List.mem_map, reduceCtorEq, and_false, exists_false,
    not_false_eq_true, true_and]
  refine (List.nodup_finRange _).map fun a b hab => ?_
  simpa using hab

theorem loopList_length (s : ι → ℕ) (i : ι) : (loopList s i).length = s i - 1 + 1 := by
  simp [loopList]

theorem mem_loopList {s : ι → ℕ} {i : ι} {x : LoopPt s} :
    x ∈ loopList s i ↔ x = none ∨ ∃ k, x = some ⟨i, k⟩ := by
  simp [loopList, eq_comm]

theorem loopRep_of (s : ι → ℕ) (i : ι) : loopRep s (.of i) = (loopList s i).formPerm := by
  simp [loopRep]

theorem loopRep_transitive (s : ι → ℕ) : ∀ y, ∃ w, loopRep s w none = y := by
  rintro (_ | ⟨i, k⟩)
  · exact ⟨1, rfl⟩
  · refine ⟨FreeGroup.of i ^ (k.val + 1), ?_⟩
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

/-- The explicit construction satisfies Definition 1. -/
theorem isLoopRep_loopRep {s : ι → ℕ} (hs : ∀ i, 1 ≤ s i) : IsLoopRep (loopRep s) none s := by
  constructor
  · intro i
    rw [loopRep_of]
    by_cases h1 : s i = 1
    · left
      refine ⟨h1, ?_⟩
      have : loopList s i = [none] := by simp [loopList, h1]
      rw [this, List.formPerm_singleton]
    · right
      have hlen : 2 ≤ (loopList s i).length := by rw [loopList_length]; have := hs i; omega
      have hne : ∀ x, loopList s i ≠ [x] := fun x hx => by
        have := congrArg List.length hx; simp at this; omega
      refine ⟨List.isCycle_formPerm (loopList_nodup s i) hlen, ?_, ?_⟩
      · rw [List.support_formPerm_of_nodup' _ (loopList_nodup s i) hne, Set.ncard_coe_finset,
          List.toFinset_card_of_nodup (loopList_nodup s i), loopList_length]
        have := hs i; omega
      · exact (List.formPerm_apply_mem_ne_self_iff _ (loopList_nodup s i) none
          (mem_loopList.mpr (Or.inl rfl))).mpr hlen
  · intro i j hij x hi hj
    rw [loopRep_of] at hi hj
    have hi' := mem_loopList.mp (by_contra fun h => hi (List.formPerm_apply_of_notMem h))
    have hj' := mem_loopList.mp (by_contra fun h => hj (List.formPerm_apply_of_notMem h))
    rcases hi' with rfl | ⟨k, rfl⟩
    · rfl
    · rcases hj' with h | ⟨l, hl⟩
      · exact h
      · simp only [Option.some.injEq, Sigma.mk.inj_iff] at hl
        exact absurd hl.1 hij

/-- **Existence of loop subgroups.** For all `s_i ≥ 1`, `loopSubgroup s` is an `s_1/…/s_r` loop
subgroup. -/
theorem isLoopSubgroup_loopSubgroup {s : ι → ℕ} (hs : ∀ i, 1 ≤ s i) :
    IsLoopSubgroup (loopSubgroup s) s :=
  (isLoopRep_loopRep hs).isLoopSubgroup (loopRep_transitive s)

instance (s : ι → ℕ) : (loopSubgroup s).FiniteIndex := by
  have : Finite (FreeGroup ι ⧸ loopSubgroup s) :=
    Finite.of_equiv _ (quotientEquivOfTransitive (loopRep s) none (loopRep_transitive s)).symm
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The index of the `s_1/…/s_r` loop subgroup is `1 + ∑ (s_i - 1)`. -/
theorem index_loopSubgroup (s : ι → ℕ) : (loopSubgroup s).index = 1 + ∑ i, (s i - 1) := by
  rw [Subgroup.index_eq_card, loopSubgroup,
    Nat.card_congr (quotientEquivOfTransitive (loopRep s) none (loopRep_transitive s)),
    Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sigma]
  simp [add_comm]

/-- The main theorem for the explicitly constructed loop subgroups. -/
theorem image_Stab_loopSubgroup {s : ι → ℕ} (hs : ∀ i, 1 ≤ s i) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    (Stab (loopSubgroup s)).map B = (S (parityVec s)).comap reduce :=
  image_Stab_eq (isLoopSubgroup_loopSubgroup hs) hr hl

end LoopSubgroups
