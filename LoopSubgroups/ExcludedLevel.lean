import LoopSubgroups.Excluded

/-!
# The level in the excluded case

After Proposition 18: "As a matter of fact, `s_1` is the level of the congruence subgroup
`B(Stab(U))`."
-/

open Matrix

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Γ_l ≤ B(Stab(U))` iff `s_{i₀} ∣ l`; hence `s_{i₀}` is the level of `B(Stab(U))`. -/
theorem Γ_le_image_Stab_iff {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) {i₀ : ι} (hs : ∀ i, i ≠ i₀ → s i = 1)
    (hr : 2 ≤ Fintype.card ι) (l : ℕ) :
    Γ l ≤ (Stab U).map B ↔ s i₀ ∣ l := by
  rw [image_Stab_eq_latticeStab hU hs]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i₀
    have hM : TauCeti.transvectionUnit hj.symm (l : ℤ) ∈ Γ (ι := ι) l := by
      rw [Γ, MonoidHom.mem_ker]
      ext a b
      simp
    have := h hM (Pi.single j 1)
    simp [TauCeti.coe_transvectionUnit_eq_one_add_single, hj.symm] at this
    exact_mod_cast this
  · intro hl M hM x
    have hM' : ∀ a b, ((M : Matrix ι ι ℤ) a b : ZMod l) = (1 : Matrix ι ι ℤ) a b := by
      intro a b
      have := congrArg (fun N : GL ι (ZMod l) => (N : Matrix ι ι (ZMod l)) a b)
        (MonoidHom.mem_ker.mp hM)
      simpa [Matrix.one_apply, apply_ite] using this
    have h1 : (((M : Matrix ι ι ℤ) *ᵥ x) i₀ : ZMod l) = (x i₀ : ZMod l) := by
      simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hM']
      simp [Matrix.one_apply]
    have hd : (s i₀ : ℤ) ∣ x i₀ - ((M : Matrix ι ι ℤ) *ᵥ x) i₀ :=
      (Int.natCast_dvd_natCast.mpr hl).trans ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1)
    rw [← dvd_add_right hd, sub_add_cancel]

end LoopSubgroups
