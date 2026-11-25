import LoopSubgroups.UpperBound

/-!
# Transporting Definition 1 along equivariant bijections

* `IsLoopRep.of_equiv`: Definition 1 is invariant under equivariant bijections.
* `quotientEquivOfTransitive`: for a transitive action of `F_r` on `Ω` and `U` the stabilizer of
  `x₀`, the coset space `F_r ⧸ U` is equivariantly isomorphic to `Ω`.
-/

open Equiv Equiv.Perm

set_option linter.unusedSectionVars false

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω Ω' : Type*}

/-- Definition 1 is invariant under equivariant bijections. -/
theorem IsLoopRep.of_equiv {ρ : FreeGroup ι →* Perm Ω} {ρ' : FreeGroup ι →* Perm Ω'} {x₀ : Ω}
    {x₀' : Ω'} {s : ι → ℕ} (h : IsLoopRep ρ x₀ s) (e : Ω' ≃ Ω)
    (he : ∀ w q, e (ρ' w q) = ρ w (e q)) (hx : e x₀' = x₀) : IsLoopRep ρ' x₀' s := by
  have hne : ∀ w q, ρ' w q ≠ q ↔ ρ w (e q) ≠ e q := fun w q => by
    rw [← he, e.injective.ne_iff]
  have hone : ∀ w, ρ' w = 1 ↔ ρ w = 1 := fun w => by
    simp only [Perm.ext_iff, Perm.one_apply]
    constructor
    · intro h1 y; obtain ⟨q, rfl⟩ := e.surjective y; rw [← he, h1]
    · intro h1 q; apply e.injective; rw [he, h1]
  constructor
  · intro i
    rcases h.loop i with ⟨hs, h1⟩ | ⟨hc, hcard, hx₀⟩
    · exact Or.inl ⟨hs, (hone _).mpr h1⟩
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · obtain ⟨x, hx1, hx2⟩ := hc
        refine ⟨e.symm x, by rw [hne, e.apply_symm_apply]; exact hx1, fun y hy => ?_⟩
        rw [hne] at hy
        obtain ⟨k, hk⟩ := hx2 hy
        refine ⟨k, e.injective ?_⟩
        rw [← map_zpow, he, map_zpow, e.apply_symm_apply, hk]
      · rw [← hcard, ← Set.ncard_image_of_injective _ e.injective]
        congr 1
        ext y
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact (hne _ _).mp hq
        · intro hy; exact ⟨e.symm y, by rw [hne, e.apply_symm_apply]; exact hy, e.apply_symm_apply y⟩
      · rw [hne, hx]; exact hx₀
  · intro i j hij x hi hj
    rw [hne] at hi hj
    exact e.injective (by rw [hx]; exact h.inter i j hij _ hi hj)

/-- For a transitive permutation representation `ρ` with base point `x₀`, the left cosets of the
stabilizer of `x₀` are in equivariant bijection with `Ω`, via `wU ↦ ρ(w)(x₀)`. -/
noncomputable def quotientEquivOfTransitive (ρ : FreeGroup ι →* Perm Ω) (x₀ : Ω)
    (htrans : ∀ y, ∃ w, ρ w x₀ = y) : FreeGroup ι ⧸ stabPt ρ x₀ ≃ Ω :=
  Equiv.ofBijective
    (Quotient.lift (fun w => ρ w x₀) fun a b hab => by
      have : a⁻¹ * b ∈ stabPt ρ x₀ := QuotientGroup.leftRel_apply.mp hab
      rw [mem_stabPt, map_mul, map_inv, Perm.mul_apply, Perm.inv_eq_iff_eq] at this
      exact this.symm)
    ⟨fun p q => by
      induction p using QuotientGroup.induction_on with | H a =>
      induction q using QuotientGroup.induction_on with | H b =>
      intro hab
      apply QuotientGroup.eq.mpr
      change ρ a x₀ = ρ b x₀ at hab
      rw [mem_stabPt, map_mul, map_inv, Perm.mul_apply, Perm.inv_eq_iff_eq, hab],
    fun y => by
      obtain ⟨w, rfl⟩ := htrans y
      exact ⟨(w : FreeGroup ι ⧸ stabPt ρ x₀), rfl⟩⟩

theorem quotientEquivOfTransitive_mk (ρ : FreeGroup ι →* Perm Ω) (x₀ : Ω)
    (htrans : ∀ y, ∃ w, ρ w x₀ = y) (w : FreeGroup ι) :
    quotientEquivOfTransitive ρ x₀ htrans (w : FreeGroup ι ⧸ stabPt ρ x₀) = ρ w x₀ := rfl

/-- If `ρ` is transitive and satisfies Definition 1, then the stabilizer of the base point is a
loop subgroup. -/
theorem IsLoopRep.isLoopSubgroup {ρ : FreeGroup ι →* Perm Ω} {x₀ : Ω} {s : ι → ℕ}
    (h : IsLoopRep ρ x₀ s) (htrans : ∀ y, ∃ w, ρ w x₀ = y) :
    IsLoopSubgroup (stabPt ρ x₀) s := by
  refine h.of_equiv (quotientEquivOfTransitive ρ x₀ htrans) (fun w q => ?_) (by simp
    [quotientEquivOfTransitive_mk])
  induction q using QuotientGroup.induction_on with | H a =>
  change quotientEquivOfTransitive ρ x₀ htrans ((w * a : FreeGroup ι) : FreeGroup ι ⧸ _) = _
  simp [quotientEquivOfTransitive_mk]

end LoopSubgroups
