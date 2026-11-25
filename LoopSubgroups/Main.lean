import LoopSubgroups.UpperBound

/-!
# The main theorem (Theorem 1)

For a loop subgroup `U ≤ F_r`, `r ≥ 3`, with at most `r - 2` looplets,
`B(Stab_{Aut(F_r)}(U)) = {M ∈ GL_r(ℤ) | v · M ≡ v (mod 2)}`, where `v_i = 0` if `s_i` is odd and
`v_i = 1` if `s_i` is even. Equivalently, `B(Stab(U))` is a congruence subgroup of level 2 whose
image in `GL_r(ℤ/2ℤ)` is `S(v)`.
-/

open scoped Pointwise
open Equiv Equiv.Perm Matrix

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IsLoopSubgroup.signVec_eq {U : Subgroup (FreeGroup ι)} [Fintype (FreeGroup ι ⧸ U)]
    [DecidableEq (FreeGroup ι ⧸ U)] {s : ι → ℕ} (hU : IsLoopSubgroup U s) :
    signVec (MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)) = parityVec s := by
  funext i
  unfold signVec parityVec
  have := IsLoopRep.sign_eq hU (i := i)
  split_ifs at this ⊢ <;> simp_all

/-- **Theorem 1.** For an `s_1/…/s_r` loop subgroup `U ≤ F_r` with `r ≥ 3` and at most `r - 2`
looplets, the image of its stabilizer under `B : Aut(F_r) → GL_r(ℤ)` consists exactly of the
matrices `M` with `v · M ≡ v (mod 2)`, where `v_i = 0` for odd `s_i` and `v_i = 1` for even `s_i`.
-/
theorem image_Stab_eq {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    (Stab U).map B = (S (parityVec s)).comap reduce := by
  classical
  have : Fintype (FreeGroup ι ⧸ U) := Fintype.ofFinite _
  apply le_antisymm
  · have h16 := image_le_comap_S (U := U)
    rwa [hU.signVec_eq] at h16
  · have := comap_S_le_image hU hr hl
    rwa [image, stabPt_toPermHom] at this

/-- **Theorem 1**, first half of the formulation in Section 8: `B(Stab(U))` is a congruence
subgroup of level 2. (Lemma 14.) -/
theorem Γ₂_le_image_Stab {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    Γ₂ ≤ (Stab U).map B := by
  classical
  have : Fintype (FreeGroup ι ⧸ U) := Fintype.ofFinite _
  have := Γ₂_le_image hU hr hl
  rwa [image, stabPt_toPermHom] at this

/-- **Theorem 1**, second half of the formulation in Section 8: the image of `B(Stab(U))` in
`GL_r(ℤ/2ℤ)` is `S(v)`. -/
theorem map_reduce_image_Stab {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    ((Stab U).map B).map reduce = S (parityVec s) := by
  classical
  have : Fintype (FreeGroup ι ⧸ U) := Fintype.ofFinite _
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, image_Stab_eq hU hr hl]
  · have := S_le_map_image hU hr hl
    rwa [image, stabPt_toPermHom] at this

/-- **Theorem 1**, in the formulation of the introduction, with an integral row vector `v`:
`M ∈ B(Stab(U))` iff `v · M ≡ v (mod 2)` (entrywise). -/
theorem mem_image_Stab_iff {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) (M : GL ι ℤ) :
    M ∈ (Stab U).map B ↔
      ∀ j, (∑ i, (if Even (s i) then 1 else 0) * (M : Matrix ι ι ℤ) i j) ≡
        (if Even (s j) then 1 else 0) [ZMOD 2] := by
  rw [image_Stab_eq hU hr hl, Subgroup.mem_comap, mem_S, funext_iff]
  refine forall_congr' fun j => ?_
  change _ ↔ _ ≡ _ [ZMOD ((2 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast [apply_ite (Int.cast : ℤ → ZMod 2)]
  simp [vecMul, dotProduct, parityVec, reduce]

end LoopSubgroups
