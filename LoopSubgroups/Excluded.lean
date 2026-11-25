import LoopSubgroups.Main
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# The excluded case (Section 9 of the paper)

Loop subgroups with exactly `r - 1` looplets: Remark 17 and Proposition 18.
-/

open scoped Pointwise
open Matrix

namespace LoopSubgroups

theorem mem_stabilizer_subgroup_iff {K : Type*} [Group K] {L : Subgroup K} {γ : MulAut K} :
    γ ∈ MulAction.stabilizer (MulAut K) L ↔ ∀ w, γ w ∈ L ↔ w ∈ L := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hL w
    conv_rhs => rw [← Subgroup.smul_mem_pointwise_smul_iff (a := γ), hL, MulAut.smul_def]
  · intro h
    ext w
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← h,
      MulAut.apply_inv_self]

/-- **Remark 17.** Let `φ : G → G'` be surjective with characteristic kernel, and `ψ` the induced
map `Aut(G) → Aut(G')`. If `H = φ⁻¹(H')`, then
`ψ(Stab_{Aut G}(H)) = Stab_{Aut G'}(H') ∩ ψ(Aut G)`. -/
theorem map_stabilizer_eq {G G' : Type*} [Group G] [Group G'] (φ : G →* G')
    (hφ : Function.Surjective φ) (_hchar : φ.ker.Characteristic) (ψ : MulAut G →* MulAut G')
    (hψ : ∀ γ x, ψ γ (φ x) = φ (γ x)) (H : Subgroup G) (H' : Subgroup G')
    (hH : H = H'.comap φ) :
    (MulAction.stabilizer (MulAut G) H).map ψ = MulAction.stabilizer (MulAut G') H' ⊓ ψ.range := by
  subst hH
  ext δ
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨mem_stabilizer_subgroup_iff.mpr fun y => ?_, γ, rfl⟩
    obtain ⟨x, rfl⟩ := hφ y
    rw [hψ]
    exact mem_stabilizer_subgroup_iff.mp hγ x
  · rintro ⟨hδ, γ, rfl⟩
    refine ⟨γ, mem_stabilizer_subgroup_iff.mpr fun x => ?_, rfl⟩
    simp only [Subgroup.mem_comap]
    rw [← hψ]
    exact mem_stabilizer_subgroup_iff.mp hδ (φ x)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `B` is surjective. (Used in the proof of Proposition 18.) -/
theorem B_surjective : Function.Surjective (B (ι := ι)) := by
  have hE : TauCeti.elementarySubgroup ι ℤ ≤ (B (ι := ι)).range := by
    rw [TauCeti.elementarySubgroup_le_iff]
    intro i j hij c
    have hgi : FreeGroup.of i ∈ avoiding j := Subgroup.subset_closure ⟨i, hij, rfl⟩
    have hu : FreeGroup.of i ^ c ∈ avoiding j := zpow_mem hgi c
    refine ⟨elemAut j _ hu, B_elemAut_eq_X hij hu c fun a => ?_⟩
    simp [count, Pi.single_apply]
  rw [TauCeti.elementarySubgroup_eq_ker_det_of_euclideanDomain] at hE
  intro M
  rcases Int.units_eq_one_or (Matrix.GeneralLinearGroup.det M) with h | h
  · exact hE h
  · have : Nonempty ι := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have h1 : (Matrix.GeneralLinearGroup.det M : ℤ) = 1 := by
        simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
      rw [h] at h1
      norm_num at h1
    obtain ⟨i⟩ := this
    have hT : Matrix.GeneralLinearGroup.det (T (R := ℤ) i) = -1 := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, T, Finset.prod_update_of_mem]
    have hTT : T (R := ℤ) i * T i = 1 := by
      ext a b
      simp only [T, Units.val_mul, diagonal_mul_diagonal, Units.val_one]
      rw [← diagonal_one, diagonal_apply, diagonal_apply]
      by_cases ha : a = i <;> simp [ha]
    obtain ⟨γ, hγ⟩ := hE (x := T i * M) (by simp [MonoidHom.mem_ker, map_mul, hT, h])
    refine ⟨invAut i * γ, ?_⟩
    rw [map_mul, hγ, B_invAut, ← mul_assoc, hTT, one_mul]

/-- The stabilizer `Stab_{GL_r(ℤ)}(U')` of the lattice `U' = {x ∈ ℤ^r | n ∣ x_{i₀}}`, acting on
column vectors. -/
def latticeStab (n : ℕ) (i₀ : ι) : Subgroup (GL ι ℤ) where
  carrier := {M | ∀ x : ι → ℤ, (n : ℤ) ∣ ((M : Matrix ι ι ℤ) *ᵥ x) i₀ ↔ (n : ℤ) ∣ x i₀}
  mul_mem' {a b} ha hb x := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, ← mulVec_mulVec] at *
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha x := by
    simp only [Set.mem_ofPred_eq] at *
    rw [← ha, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- The principal congruence subgroup `Γ_n` of level `n` in `GL_r(ℤ)`. -/
noncomputable def Γ (n : ℕ) : Subgroup (GL ι ℤ) :=
  (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod n))).ker

/-- In the excluded case, `U = {w | #_{g_{i₀}} w ≡ 0 mod s_{i₀}}`. -/
theorem IsLoopSubgroup.eq_of_looplets {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) {i₀ : ι} (hs : ∀ i, i ≠ i₀ → s i = 1) (w : FreeGroup ι) :
    w ∈ U ↔ (s i₀ : ℤ) ∣ count i₀ w := by
  classical
  have : Fintype (FreeGroup ι ⧸ U) := Fintype.ofFinite _
  set ρ := MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)
  set x₀ : FreeGroup ι ⧸ U := QuotientGroup.mk 1
  set σ := ρ (.of i₀)
  have hρ : ∀ v, ρ v = σ ^ count i₀ v := by
    intro v
    induction v using FreeGroup.induction_on with
    | one => simp
    | of i =>
      by_cases hi : i = i₀
      · subst hi; simp [σ]
      · rw [count_of, ite_eq_right_iff.mpr (fun h => absurd h.symm hi), zpow_zero]
        exact hU.eq_one_iff.mpr (hs i hi)
    | inv_of i ih => rw [map_inv, ih, count_inv, _root_.zpow_neg]
    | mul x y hx hy => rw [map_mul, hx, hy, count_mul, _root_.zpow_add]
  have hmem : w ∈ U ↔ ρ w x₀ = x₀ := by
    conv_lhs => rw [← stabPt_toPermHom (U := U)]
    exact mem_stabPt
  rw [hmem, hρ]
  by_cases hσ : σ = 1
  · have : s i₀ = 1 := hU.eq_one_iff.mp hσ
    simp [hσ, this]
  · have hc : σ.IsCycle := hU.isCycle hσ
    have hx : σ x₀ ≠ x₀ := Equiv.Perm.mem_support.mp (hU.mem_support hσ)
    have hn : ∀ m : ℕ, (σ ^ m) x₀ = x₀ ↔ (s i₀ : ℤ) ∣ m := by
      intro m
      rw [← hc.pow_eq_one_iff' hx, ← orderOf_dvd_iff_pow_eq_one, hc.orderOf,
        hU.card_support hσ, Int.natCast_dvd_natCast]
    obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg (count i₀ w)
    · rw [hm, zpow_natCast, hn]
    · rw [hm, _root_.zpow_neg, zpow_natCast, Int.dvd_neg, ← hn, Equiv.Perm.inv_eq_iff_eq, eq_comm]

/-- Every vector of exponent sums is realised by a word. -/
theorem exists_count_eq (x : ι → ℤ) : ∃ w : FreeGroup ι, ∀ i, count i w = x i := by
  have hx : Multiplicative.ofAdd x = ∏ j, Multiplicative.ofAdd (x j • Pi.single j (1 : ℤ)) := by
    rw [← ofAdd_sum]
    congr 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have : Multiplicative.ofAdd x ∈ (ab (ι := ι)).range := by
    rw [hx]
    refine Subgroup.prod_mem _ fun j _ => ⟨FreeGroup.of j ^ x j, ?_⟩
    rw [map_zpow, ab_of, ← ofAdd_zsmul]
  obtain ⟨w, hw⟩ := this
  exact ⟨w, fun i => by simp [count, hw]⟩

/-- **Proposition 18.** For the `s_1/1/…/1` loop subgroup (here with the non-looplet at an
arbitrary index `i₀`), `Γ_{s_1} ≤ B(Stab(U)) = Stab_{GL_r(ℤ)}(U')` where
`U' = {x ∈ ℤ^r | x_{i₀} ≡ 0 mod s_{i₀}}`. -/
theorem image_Stab_eq_latticeStab {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) {i₀ : ι} (hs : ∀ i, i ≠ i₀ → s i = 1) :
    (Stab U).map B = latticeStab (s i₀) i₀ := by
  have key : ∀ γ : MulAut (FreeGroup ι), ∀ w,
      (γ w ∈ U ↔ w ∈ U) ↔
        ((s i₀ : ℤ) ∣ (Bmat γ *ᵥ fun i => count i w) i₀ ↔ (s i₀ : ℤ) ∣ count i₀ w) := by
    intro γ w
    rw [← count_apply_aut, hU.eq_of_looplets hs, hU.eq_of_looplets hs]
  ext M
  constructor
  · rintro ⟨γ, hγ, rfl⟩ x
    obtain ⟨w, hw⟩ := exists_count_eq x
    have := (key γ w).mp (mem_Stab_iff.mp hγ w)
    have hw' : (fun i => count i w) = x := funext hw
    rwa [hw', hw] at this
  · intro hM
    obtain ⟨γ, rfl⟩ := B_surjective M
    refine ⟨γ, mem_Stab_iff.mpr fun w => (key γ w).mpr (hM _), rfl⟩

theorem Γ_le_image_Stab {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) {i₀ : ι} (hs : ∀ i, i ≠ i₀ → s i = 1) :
    Γ (s i₀) ≤ (Stab U).map B := by
  rw [image_Stab_eq_latticeStab hU hs]
  intro M hM x
  have hM' : ∀ a b, ((M : Matrix ι ι ℤ) a b : ZMod (s i₀)) = (1 : Matrix ι ι ℤ) a b := by
    intro a b
    have := congrArg (fun N : GL ι (ZMod (s i₀)) => (N : Matrix ι ι (ZMod (s i₀))) a b)
      (MonoidHom.mem_ker.mp hM)
    simpa [Matrix.one_apply, apply_ite] using this
  have : (((M : Matrix ι ι ℤ) *ᵥ x) i₀ : ZMod (s i₀)) = (x i₀ : ZMod (s i₀)) := by
    simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hM']
    simp [Matrix.one_apply]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, this]

end LoopSubgroups
