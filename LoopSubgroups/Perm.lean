module

public import Mathlib

@[expose] public section

/-!
# Permutation lemmas

* Lemma 5 of the paper (in a coordinate-free generalisation): if two cycles `σ`, `ω` share
  exactly one point of their supports, every even permutation supported on the union of their
  supports lies in the commutator subgroup of `⟨σ, ω⟩`.
* A cycle is conjugate to its inverse by a "reflection" that fixes a given point of the cycle
  and is supported in the support of the cycle. (Used, implicitly, in the paper to see that the
  automorphism inverting a generator stabilizes a loop subgroup.)
-/

open Equiv Equiv.Perm

namespace LoopSubgroups

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- The commutator of two permutations whose supports meet exactly in `a` is the 3-cycle
`a ↦ α a ↦ β a ↦ a`. -/
theorem comm_eq_swap_mul_swap (α β : Perm X) (a : X) (hα : α a ≠ a) (hβ : β a ≠ a)
    (h : ∀ x, α x ≠ x → β x ≠ x → x = a) :
    α * β * α⁻¹ * β⁻¹ = swap a (β a) * swap a (α a) := by
  ext p
  have h1 : ∀ x, α x ≠ x → x ≠ a → β x = x := fun x hx hxa => by_contra fun hb => hxa (h x hx hb)
  have h2 : ∀ x, β x ≠ x → x ≠ a → α x = x := fun x hx hxa => by_contra fun hb => hxa (h x hb hx)
  have hαα : α (α a) ≠ α a := fun e => hα (α.injective e)
  have hββ : β (β a) ≠ β a := fun e => hβ (β.injective e)
  simp only [Perm.mul_apply, swap_apply_def]
  obtain ⟨r, rfl⟩ : ∃ r, p = β (α r) := ⟨α⁻¹ (β⁻¹ p), by simp⟩
  simp only [Perm.inv_def, Equiv.symm_apply_apply]
  grind [Equiv.apply_eq_iff_eq]

/-- **Lemma 5** (generalised). Let `σ, ω` be cycles whose supports intersect in exactly one
point. Then every even permutation supported in `supp σ ∪ supp ω` lies in the commutator
subgroup of `⟨σ, ω⟩`.

The paper states this for `σ = (1, 2, …, m)` and `ω = (1, m+1, …, n)` in `S_n`, `1 < m < n`. -/
theorem mem_commutator_closure_of_sign_eq_one {σ ω : Perm X} (hσ : σ.IsCycle) (hω : ω.IsCycle)
    {a : X} (hσω : σ.support ∩ ω.support = {a}) {τ : Perm X} (hτ : sign τ = 1)
    (hτs : τ.support ⊆ σ.support ∪ ω.support) :
    τ ∈ ⁅Subgroup.closure {σ, ω}, Subgroup.closure {σ, ω}⁆ := by
  set G := Subgroup.closure ({σ, ω} : Set (Perm X))
  set K := ⁅G, G⁆
  have hint : ∀ x, x ∈ σ.support → x ∈ ω.support → x = a := fun x h1 h2 => by
    have : x ∈ σ.support ∩ ω.support := Finset.mem_inter.2 ⟨h1, h2⟩
    rwa [hσω, Finset.mem_singleton] at this
  have haS : a ∈ σ.support := (Finset.mem_inter.1 (hσω ▸ Finset.mem_singleton_self a)).1
  have haW : a ∈ ω.support := (Finset.mem_inter.1 (hσω ▸ Finset.mem_singleton_self a)).2
  have hσG : σ ∈ G := Subgroup.subset_closure (by simp)
  have hωG : ω ∈ G := Subgroup.subset_closure (by simp)
  have mixed : ∀ {π ρ : Perm X}, π.IsCycle → ρ.IsCycle → π ∈ G → ρ ∈ G →
      (∀ x, x ∈ π.support → x ∈ ρ.support → x = a) → a ∈ π.support → a ∈ ρ.support →
      ∀ x y, x ∈ π.support → y ∈ ρ.support → x ≠ a → y ≠ a → swap a y * swap a x ∈ K := by
    intro π ρ hπ hρ hπG hρG hπρ haπ haρ x y hx hy hxa hya
    obtain ⟨i, hi⟩ := hπ.exists_pow_eq (mem_support.1 haπ) (mem_support.1 hx)
    obtain ⟨j, hj⟩ := hρ.exists_pow_eq (mem_support.1 haρ) (mem_support.1 hy)
    have key := comm_eq_swap_mul_swap (π ^ i) (ρ ^ j) a (by rw [hi]; exact hxa)
      (by rw [hj]; exact hya) (fun z h1 h2 =>
        hπρ z (support_pow_le π i (mem_support.2 h1)) (support_pow_le ρ j (mem_support.2 h2)))
    rw [hi, hj] at key
    rw [← key, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (pow_mem hπG i) (pow_mem hρG j)
  have hint' : ∀ x, x ∈ ω.support → x ∈ σ.support → x = a := fun x h1 h2 => hint x h2 h1
  have hgen : ∀ x y, (x ∈ σ.support ∨ x ∈ ω.support) → (y ∈ σ.support ∨ y ∈ ω.support) →
      x ≠ a → y ≠ a → swap a y * swap a x ∈ K := by
    intro x y hx hy hxa hya
    have hσa : σ a ≠ a := mem_support.1 haS
    have hωa : ω a ≠ a := mem_support.1 haW
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [show swap a y * swap a x = (swap a y * swap a (ω a)) * (swap a (ω a) * swap a x) by
        simp [mul_assoc]]
      exact mul_mem (mixed hω hσ hωG hσG hint' haW haS _ _ (apply_mem_support.2 haW) hy hωa hya)
        (mixed hσ hω hσG hωG hint haS haW _ _ hx (apply_mem_support.2 haW) hxa hωa)
    · exact mixed hσ hω hσG hωG hint haS haW _ _ hx hy hxa hya
    · exact mixed hω hσ hωG hσG hint' haW haS _ _ hx hy hxa hya
    · rw [show swap a y * swap a x = (swap a y * swap a (σ a)) * (swap a (σ a) * swap a x) by
        simp [mul_assoc]]
      exact mul_mem (mixed hσ hω hσG hωG hint haS haW _ _ (apply_mem_support.2 haS) hy hσa hya)
        (mixed hω hσ hωG hσG hint' haW haS _ _ hx (apply_mem_support.2 haS) hxa hσa)
  set b := σ a
  have hbS : b ∈ σ.support := apply_mem_support.2 haS
  have hba : b ≠ a := mem_support.1 haS
  set N := σ.support ∪ ω.support
  have hpair : ∀ p q, p ∈ N → q ∈ N → p ≠ q → swap a b * swap p q ∈ K := by
    intro p q hp hq hpq
    rw [Finset.mem_union] at hp hq
    by_cases hpa : p = a
    · subst p
      exact hgen _ _ hq (Or.inl hbS) (Ne.symm hpq) hba
    by_cases hqa : q = a
    · subst q
      rw [swap_comm p a]
      exact hgen _ _ hp (Or.inl hbS) hpa hba
    rw [show swap a b * swap p q = (swap a b * swap a p) * (swap a q * swap a p) by
      rw [mul_assoc]
      congr 1
      ext z
      simp only [Perm.mul_apply, swap_apply_def]
      grind]
    exact mul_mem (hgen _ _ hp (Or.inl hbS) hpa hba) (hgen _ _ hp hq hpa hqa)
  have hpair' : ∀ p q, p ∈ N → q ∈ N → p ≠ q → swap p q * swap a b ∈ K := by
    intro p q hp hq hpq
    have := inv_mem (hpair p q hp hq hpq)
    simpa [mul_inv_rev, swap_inv] using this
  have h₁ : ∀ x, τ x ∈ N ↔ x ∈ N := by
    intro x
    by_cases hx : τ x = x
    · rw [hx]
    · exact iff_of_true (hτs (apply_mem_support.2 (mem_support.2 hx))) (hτs (mem_support.2 hx))
  have h₂ : ∀ x, τ x ≠ x → x ∈ N := fun x hx => hτs (mem_support.2 hx)
  rw [← ofSubtype_subtypePerm h₁ h₂]
  have hs : sign (τ.subtypePerm h₁) = 1 := by convert (sign_subtypePerm _ h₁ h₂).trans hτ
  suffices H : ∀ f : Perm {x // x ∈ N},
      (sign f = 1 → ofSubtype f ∈ K) ∧ (sign f = -1 → swap a b * ofSubtype f ∈ K) from
    (H _).1 hs
  intro f
  induction f using swap_induction_on with
  | one => simp
  | swap_mul f x y hxy ih =>
    rw [Perm.sign_mul, sign_swap hxy, map_mul, ofSubtype_swap_eq]
    have hxy' : (x : X) ≠ y := fun h => hxy (Subtype.ext h)
    rcases Int.units_eq_one_or (sign f) with h' | h'
    · refine ⟨fun h => absurd h (by rw [h']; decide), fun _ => ?_⟩
      rw [← mul_assoc]
      exact mul_mem (hpair _ _ x.2 y.2 hxy') (ih.1 h')
    · refine ⟨fun _ => ?_, fun h => absurd h (by rw [h']; decide)⟩
      rw [show swap (x : X) y * ofSubtype f = (swap (x : X) y * swap a b) * (swap a b * ofSubtype f)
        by simp [mul_assoc]]
      exact mul_mem (hpair' _ _ x.2 y.2 hxy') (ih.2 h')

theorem mem_finRange_take_iff {n m : ℕ} (x : Fin n) :
    x ∈ (List.finRange n).take m ↔ x.val < m := by
  simp only [List.mem_take_iff_getElem, List.getElem_finRange, List.length_finRange]
  constructor
  · rintro ⟨i, hi, rfl⟩; simp; omega
  · intro h; exact ⟨x, by omega, rfl⟩

theorem mem_finRange_drop_iff {n m : ℕ} (x : Fin n) :
    x ∈ (List.finRange n).drop m ↔ m ≤ x.val := by
  simp only [List.mem_drop_iff_getElem, List.getElem_finRange, List.length_finRange]
  constructor
  · rintro ⟨i, hi, rfl⟩; simp
  · intro h; exact ⟨x - m, by omega, by ext; simp; omega⟩

/-- The paper's original formulation of Lemma 5: for `σ = (1, 2, …, m)` and
`ω = (1, m+1, …, n)` with `1 < m < n`, `A_n ≤ [⟨σ, ω⟩, ⟨σ, ω⟩]`. Indices are `0`-based here,
so `σ = (0, 1, …, m-1)` and `ω = (0, m, …, n-1)`. -/
theorem alternatingGroup_le_commutator {n m : ℕ} (hm : 1 < m) (hmn : m < n) :
    alternatingGroup (Fin n) ≤
      ⁅Subgroup.closure {((List.finRange n).take m).formPerm,
          (⟨0, by omega⟩ :: (List.finRange n).drop m).formPerm},
        Subgroup.closure {((List.finRange n).take m).formPerm,
          (⟨0, by omega⟩ :: (List.finRange n).drop m).formPerm}⁆ := by
  set L₁ := (List.finRange n).take m
  set L₂ : List (Fin n) := ⟨0, by omega⟩ :: (List.finRange n).drop m
  have hn₁ : L₁.Nodup := (List.nodup_finRange n).sublist (List.take_sublist _ _)
  have hn₂ : L₂.Nodup := by
    refine List.nodup_cons.2 ⟨?_, (List.nodup_finRange n).sublist (List.drop_sublist _ _)⟩
    rw [mem_finRange_drop_iff]; simp; omega
  have hl₁ : 2 ≤ L₁.length := by simp [L₁]; omega
  have hl₂ : 2 ≤ L₂.length := by simp [L₂]; omega
  have hs₁ : L₁.formPerm.support = L₁.toFinset :=
    List.support_formPerm_of_nodup _ hn₁ (fun x h => by simp [h] at hl₁)
  have hs₂ : L₂.formPerm.support = L₂.toFinset :=
    List.support_formPerm_of_nodup _ hn₂ (fun x h => by simp [h] at hl₂)
  intro τ hτ
  apply mem_commutator_closure_of_sign_eq_one (List.isCycle_formPerm hn₁ hl₁)
    (List.isCycle_formPerm hn₂ hl₂) (a := ⟨0, by omega⟩) ?_ (mem_alternatingGroup.1 hτ) ?_
  · ext x
    rw [hs₁, hs₂, Finset.mem_inter, List.mem_toFinset, List.mem_toFinset, mem_finRange_take_iff,
      List.mem_cons, mem_finRange_drop_iff, Finset.mem_singleton, Fin.ext_iff]
    dsimp only
    omega
  · intro x _
    rw [hs₁, hs₂, Finset.mem_union, List.mem_toFinset, List.mem_toFinset, mem_finRange_take_iff,
      List.mem_cons, mem_finRange_drop_iff, Fin.ext_iff]
    dsimp only
    omega

/-- A cycle `σ` is conjugate to its inverse by a permutation that fixes a given point `a` of
its support and is supported in the support of `σ`. -/
theorem exists_conj_eq_inv {σ : Perm X} (hσ : σ.IsCycle) {a : X} (ha : a ∈ σ.support) :
    ∃ c : Perm X, c * σ * c⁻¹ = σ⁻¹ ∧ c a = a ∧ c.support ⊆ σ.support := by
  obtain ⟨c₁, hc₁⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (cycleType_inv σ).symm)
  -- c₁ maps the support of σ to itself
  have hsupp : ∀ {c : Perm X}, c * σ * c⁻¹ = σ⁻¹ → ∀ x, c x ∈ σ.support ↔ x ∈ σ.support := by
    intro c hc x
    have : σ⁻¹ (c x) = c (σ x) := by rw [← hc]; simp
    simp only [mem_support]
    constructor
    · intro h e; apply h
      have : σ⁻¹ (c x) = c x := by rw [this, e]
      exact (inv_eq_iff_eq.1 this).symm
    · intro h e; apply h
      apply c.injective
      rw [← this]; exact inv_eq_iff_eq.2 e.symm
  have hca : c₁ a ∈ σ.support := (hsupp hc₁ a).2 ha
  obtain ⟨i, hi⟩ := hσ.exists_pow_eq (mem_support.1 hca) (mem_support.1 ha)
  set c₂ := σ ^ i * c₁
  have hc₂ : c₂ * σ * c₂⁻¹ = σ⁻¹ := by
    simp only [c₂, mul_inv_rev]
    calc σ ^ i * c₁ * σ * (c₁⁻¹ * (σ ^ i)⁻¹) = σ ^ i * (c₁ * σ * c₁⁻¹) * (σ ^ i)⁻¹ := by group
      _ = σ⁻¹ := by rw [hc₁]; group
  have hc₂a : c₂ a = a := by simp [c₂, Perm.mul_apply, hi]
  refine ⟨ofSubtype (c₂.subtypePerm (hsupp hc₂)), ?_, ?_, ?_⟩
  · rw [mul_inv_eq_iff_eq_mul]
    ext x
    simp only [Perm.mul_apply]
    by_cases hx : x ∈ σ.support
    · have hσx : σ x ∈ σ.support := apply_mem_support.2 hx
      rw [ofSubtype_apply_of_mem _ hσx, ofSubtype_apply_of_mem _ hx]
      simp only [subtypePerm_apply]
      rw [← hc₂]; simp
    · have hσx : σ x = x := notMem_support.1 hx
      rw [hσx, ofSubtype_apply_of_not_mem _ hx, inv_eq_iff_eq.2 hσx.symm]
  · rw [ofSubtype_apply_of_mem _ ha]; simpa using hc₂a
  · intro x hx
    by_contra h
    exact (mem_support.1 hx) (ofSubtype_apply_of_not_mem _ h)

end LoopSubgroups
