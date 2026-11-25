module

public import LoopSubgroups.Main

@[expose] public section

/-!
# The stabilizer index is unbounded (thesis, Lemma `unboundstabgroup`)

The index `[Aut(F_r) : Stab(U)]` of the stabilizer of a loop subgroup goes to infinity with the
index `[F_r : U]`. We prove the quantitative statements `[Aut(F_r) : Stab(U)] ≥ s_i` for every `i`,
and `[F_r : U] ≤ r · [Aut(F_r) : Stab(U)]`. (The cardinalities are taken in `ℕ∞`, so that the
statements do not depend on knowing that the index is finite.)

The thesis' proof claims that `π(g_i)^n` is again an `s_i`-cycle for `1 ≤ n < s_i`, which fails
when `gcd(n, s_i) > 1`; the formal proof uses a different test word.
-/

open Equiv

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem elemAut_pow_of_self {i j : ι} (hij : i ≠ j) (hu : FreeGroup.of i ∈ avoiding j) (n : ℕ) :
    (elemAut j (.of i) hu ^ n) (.of j) = FreeGroup.of i ^ n * .of j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, elemAut_apply, elemAut_apply,
      elemHom_of_ne hij, elemHom_of_self, pow_succ, mul_assoc]

theorem elemAut_pow_of_ne {i j : ι} (hij : i ≠ j) (hu : FreeGroup.of i ∈ avoiding j) (n : ℕ) :
    (elemAut j (.of i) hu ^ n) (.of i) = FreeGroup.of i := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, elemAut_apply, elemHom_of_ne hij]

theorem le_card_quotient_Stab {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hr : 2 ≤ Fintype.card ι) (i : ι) :
    (s i : ℕ∞) ≤ ENat.card (MulAut (FreeGroup ι) ⧸ Stab U) := by
  classical
  have := Subgroup.fintypeQuotientOfFiniteIndex (H := U)
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  have hij : i ≠ j := hji.symm
  have hu : FreeGroup.of i ∈ avoiding j := Subgroup.subset_closure ⟨i, hij, rfl⟩
  set ρ := MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)
  set x₀ : FreeGroup ι ⧸ U := QuotientGroup.mk 1
  have hmem : ∀ w, w ∈ U ↔ ρ w x₀ = x₀ := fun w => by
    rw [← mem_stabPt (ρ := ρ), stabPt_toPermHom]
  set σ := ρ (.of i)
  -- σ^n x₀ ≠ x₀ for 0 < n < s i
  have hσ : ∀ n : ℕ, 0 < n → n < s i → (σ ^ n) x₀ ≠ x₀ := by
    intro n hn hns heq
    have h1 : σ ≠ 1 := fun h => by rw [hU.eq_one_iff] at h; omega
    have hc := hU.isCycle h1
    have hx : σ x₀ ≠ x₀ := Perm.mem_support.mp (hU.mem_support h1)
    have := (hc.pow_eq_one_iff' hx).mpr heq
    rw [← orderOf_dvd_iff_pow_eq_one, hc.orderOf, hU.card_support h1] at this
    exact absurd (Nat.le_of_dvd hn this) (by omega)
  have hnot : ∀ n : ℕ, 0 < n → n < s i → elemAut j (.of i) hu ^ n ∉ Stab U := by
    intro n hn hns hS
    have hw := (mem_Stab_iff.mp hS ((FreeGroup.of i)⁻¹ * .of j * .of i)).mpr
    have hx : σ x₀ ≠ x₀ := by simpa using hσ 1 one_pos (by omega)
    have hτ : ρ (.of j) (σ x₀) = σ x₀ := by
      by_contra h
      exact hx (hU.inter j i hji _ h fun h' => hx (σ.injective h'))
    rw [hmem, hmem] at hw
    simp only [map_mul, map_inv, elemAut_pow_of_self hij, elemAut_pow_of_ne hij, map_pow,
      Perm.mul_apply] at hw
    change σ⁻¹ (ρ (.of j) (σ x₀)) = x₀ → σ⁻¹ ((σ ^ n) (ρ (.of j) (σ x₀))) = x₀ at hw
    have hinv : ∀ y, σ⁻¹ (σ y) = y := fun y => Perm.inv_eq_iff_eq.mpr rfl
    rw [hτ, hinv, ← Perm.mul_apply (σ ^ n) σ, ← pow_succ, pow_succ', Perm.mul_apply,
      hinv] at hw
    exact hσ n hn hns (hw rfl)
  have hinj : Function.Injective fun n : Fin (s i) =>
      (QuotientGroup.mk (elemAut j (.of i) hu ^ (n : ℕ)) : MulAut (FreeGroup ι) ⧸ Stab U) := by
    have key : ∀ a b : Fin (s i), a < b →
        (QuotientGroup.mk (elemAut j (.of i) hu ^ (a : ℕ)) : MulAut (FreeGroup ι) ⧸ Stab U) ≠
          QuotientGroup.mk (elemAut j (.of i) hu ^ (b : ℕ)) := by
      intro a b hab heq
      rw [QuotientGroup.eq, ← Nat.add_sub_cancel' (Fin.le_iff_val_le_val.mp hab.le), pow_add,
        inv_mul_cancel_left] at heq
      exact hnot _ (by have := Fin.lt_def.mp hab; omega) (by omega) heq
    intro a b h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact absurd h (key a b hab)
    · exact hab
    · exact absurd h.symm (key b a hab)
  simpa [ENat.card_eq_coe_fintype_card] using ENat.card_le_card_of_injective hinj


/-- **Lemma `unboundstabgroup`.** -/
theorem index_le_card_mul_card_quotient_Stab {U : Subgroup (FreeGroup ι)} [U.FiniteIndex]
    {s : ι → ℕ} (hU : IsLoopSubgroup U s) (hr : 2 ≤ Fintype.card ι) :
    (U.index : ℕ∞) ≤ Fintype.card ι * ENat.card (MulAut (FreeGroup ι) ⧸ Stab U) := by
  classical
  have := Subgroup.fintypeQuotientOfFiniteIndex (H := U)
  set ρ := MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)
  set x₀ : FreeGroup ι ⧸ U := QuotientGroup.mk 1
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  set A : Finset (FreeGroup ι ⧸ U) := Finset.univ.biUnion fun i => insert x₀ (ρ (.of i)).support
  have hx₀ : x₀ ∈ A := Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ _, Finset.mem_insert_self _ _⟩
  have hgen : ∀ (k : ι) (x : FreeGroup ι ⧸ U), x ∈ A → ρ (.of k) x ∈ A ∧ (ρ (.of k))⁻¹ x ∈ A := by
    intro k x hx
    have mk : ∀ y, y ∈ (ρ (.of k)).support → y ∈ A := fun y hy =>
      Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_insert_of_mem hy⟩
    constructor
    · by_cases h : ρ (.of k) x = x
      · rwa [h]
      · exact mk _ (Perm.apply_mem_support.mpr (Perm.mem_support.mpr h))
    · by_cases h : (ρ (.of k))⁻¹ x = x
      · rwa [h]
      · refine mk _ ?_
        rw [← Perm.support_inv, Perm.apply_mem_support, Perm.mem_support]
        exact h
  have hall : ∀ w : FreeGroup ι, ∀ x ∈ A, ρ w x ∈ A := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => simp
    | of k => exact fun x hx => (hgen k x hx).1
    | inv_of k _ => exact fun x hx => by rw [map_inv]; exact (hgen k x hx).2
    | mul v w hv hw => exact fun x hx => by rw [map_mul, Perm.mul_apply]; exact hv _ (hw x hx)
  have huniv : Finset.univ ⊆ A := by
    intro q _
    induction q using QuotientGroup.induction_on with
    | H w =>
      have := hall w x₀ hx₀
      simpa [ρ, x₀] using this
  have hcard : ∀ i, (insert x₀ (ρ (.of i)).support).card = s i := by
    intro i
    by_cases h : ρ (.of i) = 1
    · rw [h, Perm.support_one, hU.eq_one_iff.mp h]; rfl
    · rw [Finset.insert_eq_of_mem (hU.mem_support h), hU.card_support h]
  have h1 : U.index ≤ ∑ i, s i := by
    rw [Subgroup.index, Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine (Finset.card_le_card huniv).trans (Finset.card_biUnion_le.trans_eq ?_)
    simp only [hcard]
  calc (U.index : ℕ∞) ≤ ((∑ i, s i : ℕ) : ℕ∞) := by exact_mod_cast h1
    _ = ∑ i, (s i : ℕ∞) := by push_cast; rfl
    _ ≤ ∑ _i : ι, ENat.card (MulAut (FreeGroup ι) ⧸ Stab U) :=
      Finset.sum_le_sum fun i _ => le_card_quotient_Stab hU hr i
    _ = Fintype.card ι * ENat.card (MulAut (FreeGroup ι) ⧸ Stab U) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

end LoopSubgroups
