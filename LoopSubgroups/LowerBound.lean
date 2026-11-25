module

public import LoopSubgroups.Defs
public import LoopSubgroups.Perm
public import LoopSubgroups.Matrix.Gamma2
public import LoopSubgroups.Matrix.StabMod2

@[expose] public section

/-!
# The lower bound (Sections 6 and 7 of the paper)

Throughout, `ρ : F_r → Sym(X)` is a permutation representation on a finite set `X` with base point
`x₀`, satisfying Definition 1 with loop lengths `s`. The loop subgroup is the stabilizer
`stabPt ρ x₀` of `x₀`; for the coset action this is `U` itself.
-/

open scoped Pointwise
open Equiv Equiv.Perm Matrix

set_option linter.unusedSectionVars false

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*}

/-- The stabilizer `{w | ρ(w)(x₀) = x₀}` of the base point. -/
def stabPt (ρ : FreeGroup ι →* Perm Ω) (x₀ : Ω) : Subgroup (FreeGroup ι) :=
  (MulAction.stabilizer (Perm Ω) x₀).comap ρ

theorem mem_stabPt {ρ : FreeGroup ι →* Perm Ω} {x₀ : Ω} {w : FreeGroup ι} :
    w ∈ stabPt ρ x₀ ↔ ρ w x₀ = x₀ := Iff.rfl

theorem mem_Stab_iff {U : Subgroup (FreeGroup ι)} {γ : MulAut (FreeGroup ι)} :
    γ ∈ Stab U ↔ ∀ w, γ w ∈ U ↔ w ∈ U := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hU w
    conv_rhs => rw [← Subgroup.smul_mem_pointwise_smul_iff (a := γ), hU, MulAut.smul_def]
  · intro H
    ext w
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← H,
      MulAut.apply_inv_self]

/-- To check that `ρ ∘ γ` is conjugate to `ρ`, it suffices to check it on generators. -/
theorem conj_of_gen {ρ : FreeGroup ι →* Perm Ω} {γ : MulAut (FreeGroup ι)} (c : Perm Ω)
    (h : ∀ k, ρ (γ (.of k)) = c * ρ (.of k) * c⁻¹) (w : FreeGroup ι) :
    ρ (γ w) = c * ρ w * c⁻¹ := by
  have : ρ.comp (γ : FreeGroup ι →* FreeGroup ι) = (MulAut.conj c).toMonoidHom.comp ρ := by
    ext k : 1
    simpa using h k
  simpa using DFunLike.congr_fun this w

/-- **Remark 3 (3)**, converse direction, generalising **Remark 4**: if `ρ ∘ γ` is `ρ` conjugated
by a permutation fixing `x₀`, then `γ` stabilizes the stabilizer of `x₀`. -/
theorem mem_Stab_of_conj {ρ : FreeGroup ι →* Perm Ω} {x₀ : Ω} {γ : MulAut (FreeGroup ι)}
    (c : Perm Ω) (hc : c x₀ = x₀) (h : ∀ w, ρ (γ w) = c * ρ w * c⁻¹) :
    γ ∈ Stab (stabPt ρ x₀) := by
  rw [mem_Stab_iff]
  intro w
  have hc' : c⁻¹ x₀ = x₀ := by rw [Perm.inv_eq_iff_eq, hc]
  simp only [mem_stabPt, h, Perm.mul_apply, hc']
  constructor
  · intro hw
    exact c.injective (hw.trans hc.symm)
  · intro hw; rw [hw, hc]

/-- **Remark 4.** `g_j ↦ u g_j` stabilizes the loop subgroup if `ρ(u) = 1`. -/
theorem elemAut_mem_Stab {ρ : FreeGroup ι →* Perm Ω} {x₀ : Ω} {j : ι} {u : FreeGroup ι}
    (hu : u ∈ avoiding j) (hρ : ρ u = 1) : elemAut j u hu ∈ Stab (stabPt ρ x₀) := by
  refine mem_Stab_of_conj 1 rfl (conj_of_gen 1 fun k => ?_)
  by_cases hk : k = j
  · subst hk; simp [hρ]
  · simp [elemHom_of_ne hk]

variable [Fintype Ω] [DecidableEq Ω]

/-! ### Consequences of Definition 1 -/

section IsLoopRep

variable {ρ : FreeGroup ι →* Perm Ω} {x₀ : Ω} {s : ι → ℕ} (h : IsLoopRep ρ x₀ s)
include h

theorem IsLoopRep.card_support {i : ι} (hi : ρ (.of i) ≠ 1) : (ρ (.of i)).support.card = s i := by
  rcases h.loop i with ⟨-, h1⟩ | ⟨-, hcard, -⟩
  · exact absurd h1 hi
  · rw [← hcard, ← Set.ncard_coe_finset, Perm.coe_support_eq_set_support]

theorem IsLoopRep.isCycle {i : ι} (hi : ρ (.of i) ≠ 1) : (ρ (.of i)).IsCycle := by
  rcases h.loop i with ⟨-, h1⟩ | ⟨hc, -⟩
  · exact absurd h1 hi
  · exact hc

theorem IsLoopRep.mem_support {i : ι} (hi : ρ (.of i) ≠ 1) : x₀ ∈ (ρ (.of i)).support := by
  rcases h.loop i with ⟨-, h1⟩ | ⟨-, -, hx⟩
  · exact absurd h1 hi
  · exact Perm.mem_support.mpr hx

/-- A generator acts trivially iff its loop is a looplet. -/
theorem IsLoopRep.eq_one_iff {i : ι} : ρ (.of i) = 1 ↔ s i = 1 := by
  constructor
  · intro hi
    rcases h.loop i with ⟨hs, -⟩ | ⟨hc, -⟩
    · exact hs
    · exact absurd hi hc.ne_one
  · intro hs
    by_contra hi
    have := (h.isCycle hi).two_le_card_support
    rw [h.card_support hi] at this
    omega

theorem IsLoopRep.one_le (i : ι) : 1 ≤ s i := by
  by_cases hi : ρ (.of i) = 1
  · exact (h.eq_one_iff.mp hi).ge
  · have := (h.isCycle hi).two_le_card_support
    rw [h.card_support hi] at this
    omega

theorem IsLoopRep.sign_eq {i : ι} : sign (ρ (.of i)) = if Even (s i) then -1 else 1 := by
  by_cases hi : ρ (.of i) = 1
  · have := h.eq_one_iff.mp hi
    simp [hi, this]
  · rw [(h.isCycle hi).sign, h.card_support hi]
    split_ifs with he
    · simp [he.neg_one_pow]
    · simp [(Nat.not_even_iff_odd.mp he).neg_one_pow]

theorem IsLoopRep.support_inter {i k : ι} (hik : i ≠ k) (hi : ρ (.of i) ≠ 1) (hk : ρ (.of k) ≠ 1) :
    (ρ (.of i)).support ∩ (ρ (.of k)).support = {x₀} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton, Perm.mem_support]
  constructor
  · rintro ⟨h1, h2⟩; exact h.inter i k hik x h1 h2
  · rintro rfl
    exact ⟨Perm.mem_support.mp (h.mem_support hi), Perm.mem_support.mp (h.mem_support hk)⟩

/-- The key step in the proofs of Lemmas 10, 12 and 13: using Lemma 5, every even permutation
supported on two non-trivial loops `i ≠ k` is the image of a word `w` in the commutator subgroup
of `⟨g_i, g_k⟩`; in particular `w` does not involve any third generator `g_j`, and has exponent
sum zero in every generator. -/
theorem IsLoopRep.exists_word {i k j : ι} (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k)
    (hi : ρ (.of i) ≠ 1) (hk : ρ (.of k) ≠ 1) {τ : Perm Ω} (hτ : sign τ = 1)
    (hτs : τ.support ⊆ (ρ (.of i)).support ∪ (ρ (.of k)).support) :
    ∃ w ∈ avoiding j, (∀ a, count a w = 0) ∧ ρ w = τ := by
  have h5 := mem_commutator_closure_of_sign_eq_one (h.isCycle hi) (h.isCycle hk)
    (h.support_inter hik hi hk) hτ hτs
  set K : Subgroup (FreeGroup ι) := Subgroup.closure {FreeGroup.of i, FreeGroup.of k}
  have hK : K.map ρ = Subgroup.closure {ρ (.of i), ρ (.of k)} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  rw [← hK, ← Subgroup.map_commutator] at h5
  obtain ⟨w, hw, rfl⟩ := h5
  refine ⟨w, ?_, fun a => count_eq_zero_of_mem_commutator ?_ a, rfl⟩
  · have : K ≤ avoiding j := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.subset_closure ⟨i, hji.symm, rfl⟩
      · exact Subgroup.subset_closure ⟨k, hjk.symm, rfl⟩
    refine this (Subgroup.commutator_le.mpr (fun a ha b hb => ?_) hw)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · exact Subgroup.commutator_mono le_top le_top hw

end IsLoopRep

/-! ### Lemmas 10, 12, 13 -/

theorem B_elemAut_eq_X {i j : ι} (hij : i ≠ j) {u : FreeGroup ι} (hu : u ∈ avoiding j) (c : ℤ)
    (hc : ∀ a, count a u = if a = i then c else 0) : B (elemAut j u hu) = X hij c := by
  ext a b
  rw [B_elemAut]
  simp only [X, TauCeti.coe_transvectionUnit_eq_one_add_single, Matrix.add_apply, of_apply, hc,
    single_apply]
  by_cases hb : b = j <;> by_cases ha : a = i <;> simp [ha, hb] <;> intros <;> simp_all

theorem B_elemAut_eq_XX {i i' k : ι} (hik : i ≠ k) (hi'k : i' ≠ k) (hii' : i ≠ i')
    {u : FreeGroup ι} (hu : u ∈ avoiding k)
    (hc : ∀ a, count a u = (if a = i then 1 else 0) + (if a = i' then 1 else 0)) :
    B (elemAut k u hu) = X hik (1 : ℤ) * X hi'k 1 := by
  have hz : single i k (1 : ℤ) * single i' k 1 = 0 := single_mul_single_of_ne (h := Ne.symm hi'k) ..
  ext a b
  rw [B_elemAut]
  simp only [X, Units.val_mul, hz, TauCeti.coe_transvectionUnit_eq_one_add_single, add_mul, mul_add,
    one_mul, mul_one, add_zero, Matrix.add_apply, of_apply, hc,
    single_apply]
  rcases eq_or_ne b k with rfl | hb <;> rcases eq_or_ne a i with rfl | ha <;>
    rcases eq_or_ne a i' with rfl | ha' <;>
    simp_all [eq_comm]

variable {ρ : FreeGroup ι →* Perm Ω} {x₀ : Ω} {s : ι → ℕ}

/-- The image `B(Stab(U))` of the stabilizer. -/
abbrev image (ρ : FreeGroup ι →* Perm Ω) (x₀ : Ω) : Subgroup (GL ι ℤ) :=
  (Stab (stabPt ρ x₀)).map B

/-- **Lemma 10.** -/
theorem X_mem_image (h : IsLoopRep ρ x₀ s) {i j : ι} (hij : i ≠ j) (hodd : Odd (s i))
    (hk : s i = 1 ∨ ∃ k, k ≠ i ∧ k ≠ j ∧ 1 < s k) : X hij (1 : ℤ) ∈ image ρ x₀ := by
  by_cases hi : ρ (.of i) = 1
  · have hu : FreeGroup.of i ∈ avoiding j := Subgroup.subset_closure ⟨i, hij, rfl⟩
    refine ⟨_, elemAut_mem_Stab hu hi, B_elemAut_eq_X hij hu 1 fun a => ?_⟩
    simp
  · obtain ⟨k, hki, hkj, hsk⟩ : ∃ k, k ≠ i ∧ k ≠ j ∧ 1 < s k := by
      rcases hk with hk | hk
      · exact absurd (h.eq_one_iff.mpr hk) hi
      · exact hk
    have hk1 : ρ (.of k) ≠ 1 := fun h1 => by rw [h.eq_one_iff] at h1; omega
    have hsign : sign (ρ (.of i))⁻¹ = 1 := by
      rw [sign_inv, h.sign_eq, if_neg (Nat.not_even_iff_odd.mpr hodd)]
    obtain ⟨w, hw, hcount, hρw⟩ := h.exists_word hki.symm hij.symm hkj.symm hi hk1 hsign
      (by rw [support_inv]; exact Finset.subset_union_left)
    have hu : w * FreeGroup.of i ∈ avoiding j :=
      mul_mem hw (Subgroup.subset_closure ⟨i, hij, rfl⟩)
    refine ⟨_, elemAut_mem_Stab hu (by simp [hρw]), B_elemAut_eq_X hij hu 1 fun a => ?_⟩
    simp [hcount]

/-- **Lemma 12.** -/
theorem X_two_mem_image (h : IsLoopRep ρ x₀ s) {i j : ι} (hij : i ≠ j)
    (hk : s i = 1 ∨ ∃ k, k ≠ i ∧ k ≠ j ∧ 1 < s k) : X hij (2 : ℤ) ∈ image ρ x₀ := by
  have hgi : FreeGroup.of i ∈ avoiding j := Subgroup.subset_closure ⟨i, hij, rfl⟩
  by_cases hi : ρ (.of i) = 1
  · have hu : FreeGroup.of i ^ 2 ∈ avoiding j := pow_mem hgi 2
    refine ⟨_, elemAut_mem_Stab hu (by simp [hi]), B_elemAut_eq_X hij hu 2 fun a => ?_⟩
    simp only [count_pow, count_of]; split_ifs <;> simp
  · obtain ⟨k, hki, hkj, hsk⟩ : ∃ k, k ≠ i ∧ k ≠ j ∧ 1 < s k := by
      rcases hk with hk | hk
      · exact absurd (h.eq_one_iff.mpr hk) hi
      · exact hk
    have hk1 : ρ (.of k) ≠ 1 := fun h1 => by rw [h.eq_one_iff] at h1; omega
    have hsign : sign ((ρ (.of i)) ^ 2)⁻¹ = 1 := by
      rw [sign_inv, map_pow, Int.units_sq]
    obtain ⟨w, hw, hcount, hρw⟩ := h.exists_word hki.symm hij.symm hkj.symm hi hk1 hsign
      (by
        rw [support_inv]
        exact (support_pow_le _ 2).trans Finset.subset_union_left)
    have hu : w * FreeGroup.of i ^ 2 ∈ avoiding j := mul_mem hw (pow_mem hgi 2)
    refine ⟨_, elemAut_mem_Stab hu (by simp [hρw]), B_elemAut_eq_X hij hu 2 fun a => ?_⟩
    simp only [count_mul, hcount, count_pow, count_of, zero_add]; split_ifs <;> simp

/-- **Lemma 13.** -/
theorem XX_mem_image (h : IsLoopRep ρ x₀ s) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : Even (s i)) (hj : Even (s j)) : X hik (1 : ℤ) * X hjk 1 ∈ image ρ x₀ := by
  have hi1 : ρ (.of i) ≠ 1 := fun h1 => by
    rw [h.eq_one_iff] at h1; rw [h1] at hi; exact Nat.not_even_one hi
  have hj1 : ρ (.of j) ≠ 1 := fun h1 => by
    rw [h.eq_one_iff] at h1; rw [h1] at hj; exact Nat.not_even_one hj
  have hsign : sign (ρ (.of i) * ρ (.of j))⁻¹ = 1 := by
    rw [sign_inv, map_mul, h.sign_eq, h.sign_eq, if_pos hi, if_pos hj]; rfl
  obtain ⟨w, hw, hcount, hρw⟩ := h.exists_word hij hik.symm hjk.symm hi1 hj1 hsign
    (by rw [support_inv]; exact support_mul_le _ _)
  have hu : w * (FreeGroup.of i * FreeGroup.of j) ∈ avoiding k :=
    mul_mem hw (mul_mem (Subgroup.subset_closure ⟨i, hik, rfl⟩)
      (Subgroup.subset_closure ⟨j, hjk, rfl⟩))
  refine ⟨_, elemAut_mem_Stab hu (by simp [hρw]), B_elemAut_eq_XX hik hjk hij hu fun a => ?_⟩
  simp [hcount]

/-- The automorphisms `τ_i` stabilize every loop subgroup. (Implicit in the proof of Lemma 14 of
the paper.) -/
theorem invAut_mem_Stab (h : IsLoopRep ρ x₀ s) (i : ι) : invAut i ∈ Stab (stabPt ρ x₀) := by
  by_cases hi : ρ (.of i) = 1
  · refine mem_Stab_of_conj 1 rfl (conj_of_gen 1 fun k => ?_)
    by_cases hk : k = i
    · subst hk; simp [invAut_of_self, hi]
    · simp [invAut_of_ne hk]
  · obtain ⟨c, hc, hca, hcs⟩ := exists_conj_eq_inv (h.isCycle hi) (h.mem_support hi)
    refine mem_Stab_of_conj c hca (conj_of_gen c fun k => ?_)
    by_cases hk : k = i
    · subst hk; simp [invAut_of_self, hc]
    · rw [invAut_of_ne hk]
      have hdisj : Perm.Disjoint c (ρ (.of k)) := by
        intro x
        by_cases hcx : c x = x
        · exact Or.inl hcx
        · right
          by_contra hkx
          have hx : x ∈ (ρ (.of i)).support := hcs (Perm.mem_support.mpr hcx)
          have := h.inter i k (Ne.symm hk) x (Perm.mem_support.mp hx) hkx
          subst this
          exact hcx hca
      rw [hdisj.commute.eq, mul_inv_cancel_right]

/-! ### Lemma 14 and Proposition 15 -/

/-- If all loops other than `a`, `b` are looplets and there are at most `r - 2` looplets, the loop
`b` is not a looplet. -/
theorem one_lt_of_forall (h : IsLoopRep ρ x₀ s)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) {a b : ι}
    (hall : ∀ k, k ≠ a → k ≠ b → s k = 1) : 1 < s b := by
  by_contra hb
  have hb1 : s b = 1 := le_antisymm (not_lt.mp hb) (h.one_le b)
  have : Finset.univ.erase a ⊆ Finset.univ.filter (s · = 1) := by
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hkb : k = b
    · rw [hkb, hb1]
    · exact hall k hk hkb
  have := Finset.card_le_card this
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
  omega

theorem exists_third (hr : 3 ≤ Fintype.card ι) (a b : ι) : ∃ k, k ≠ a ∧ k ≠ b := by
  by_contra hcon
  push Not at hcon
  have : Finset.univ ⊆ ({a, b} : Finset ι) := fun k _ => by
    by_cases hka : k = a
    · simp [hka]
    · simp [hcon k hka]
  have := Finset.card_le_card this
  rw [Finset.card_univ] at this
  have := Finset.card_le_two (a := a) (b := b)
  omega

/-- **Lemma 14.** For `r ≥ 3` and at most `r - 2` looplets, `Γ₂ ≤ B(Stab(U))`. -/
theorem Γ₂_le_image (h : IsLoopRep ρ x₀ s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) : Γ₂ ≤ image ρ x₀ := by
  refine Γ₂_le_of_gens _ (fun a b hab => ?_) (fun i => ⟨_, invAut_mem_Stab h i, B_invAut i⟩)
  by_cases hc : s a = 1 ∨ ∃ k, k ≠ a ∧ k ≠ b ∧ 1 < s k
  · exact X_two_mem_image h hab hc
  · push Not at hc
    obtain ⟨-, hc⟩ := hc
    have hall : ∀ k, k ≠ a → k ≠ b → s k = 1 := fun k hka hkb =>
      le_antisymm (hc k hka hkb) (h.one_le k)
    obtain ⟨k, hka, hkb⟩ := exists_third hr a b
    have hsb := one_lt_of_forall h hl hall
    have h1 : X hka.symm (2 : ℤ) ∈ image ρ x₀ :=
      X_two_mem_image h hka.symm (Or.inr ⟨b, hab.symm, hkb.symm, hsb⟩)
    have h2 : X hkb (1 : ℤ) ∈ image ρ x₀ :=
      X_mem_image h hkb (by rw [hall k hka hkb]; exact odd_one) (Or.inl (hall k hka hkb))
    have := Subgroup.commutator_mem_commutator h1 h2
    rw [X, X, TauCeti.commutatorElement_transvectionUnit hka.symm hkb hab, mul_one] at this
    exact (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) this
  
theorem parityVec_eq_zero_iff {s : ι → ℕ} {i : ι} : parityVec s i = 0 ↔ Odd (s i) := by
  unfold parityVec
  split_ifs with h
  · simp only [one_ne_zero, false_iff, Nat.not_odd_iff_even]; exact h
  · simp only [true_iff]; exact Nat.not_even_iff_odd.mp h

theorem parityVec_eq_one_iff {s : ι → ℕ} {i : ι} : parityVec s i = 1 ↔ Even (s i) := by
  unfold parityVec
  split_ifs with h
  · simpa using h
  · simpa using h

/-- **Proposition 15.** For `r ≥ 3` and at most `r - 2` looplets, `S(v)` is contained in the
image of `B(Stab(U))` in `GL_r(ℤ/2ℤ)`, where `v_i = 0` if `s_i` is odd and `v_i = 1` otherwise. -/
theorem S_le_map_image (h : IsLoopRep ρ x₀ s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    S (parityVec s) ≤ (image ρ x₀).map reduce := by
  rw [← closure_stabGens hr, Subgroup.closure_le]
  rintro M (⟨i, j, hij, hv, rfl⟩ | ⟨i, j, k, hik, hjk, hij, hvi, hvj, rfl⟩)
  · have hodd : Odd (s i) := parityVec_eq_zero_iff.mp hv
    suffices hX : X hij (1 : ℤ) ∈ image ρ x₀ from ⟨_, hX, by simp [X]⟩
    by_cases hc : s i = 1 ∨ ∃ k, k ≠ i ∧ k ≠ j ∧ 1 < s k
    · exact X_mem_image h hij hodd hc
    · push Not at hc
      obtain ⟨-, hc⟩ := hc
      have hall : ∀ k, k ≠ i → k ≠ j → s k = 1 := fun k hki hkj =>
        le_antisymm (hc k hki hkj) (h.one_le k)
      obtain ⟨k, hki, hkj⟩ := exists_third hr i j
      have hsj := one_lt_of_forall h hl hall
      have h1 : X hki.symm (1 : ℤ) ∈ image ρ x₀ :=
        X_mem_image h hki.symm hodd (Or.inr ⟨j, hij.symm, hkj.symm, hsj⟩)
      have h2 : X hkj (1 : ℤ) ∈ image ρ x₀ :=
        X_mem_image h hkj (by rw [hall k hki hkj]; exact odd_one) (Or.inl (hall k hki hkj))
      have := Subgroup.commutator_mem_commutator h1 h2
      rw [X, X, TauCeti.commutatorElement_transvectionUnit hki.symm hkj hij, mul_one] at this
      exact (Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) this
  · exact ⟨_, XX_mem_image h hij hik hjk (parityVec_eq_one_iff.mp hvi)
      (parityVec_eq_one_iff.mp hvj), by simp [X]⟩

/-- The lower bound of the main theorem: every `M ∈ GL_r(ℤ)` with `v M ≡ v (mod 2)` lies in
`B(Stab(U))`. (Combination of Lemma 14 and Proposition 15.) -/
theorem comap_S_le_image (h : IsLoopRep ρ x₀ s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    (S (parityVec s)).comap reduce ≤ image ρ x₀ := by
  intro M hM
  obtain ⟨g, hg, hgM⟩ := S_le_map_image h hr hl hM
  have h2 : g⁻¹ * M ∈ Γ₂ := by
    rw [Γ₂, MonoidHom.mem_ker, map_mul, map_inv, hgM, inv_mul_cancel]
  simpa using mul_mem hg (Γ₂_le_image h hr hl h2)

end LoopSubgroups
