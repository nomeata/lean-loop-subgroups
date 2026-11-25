module

public import LoopSubgroups.Main
public import LoopSubgroups.Excluded
public import LoopSubgroups.Matrix.Maximal

@[expose] public section

/-!
# Index two subgroups of `F_r` (thesis, Section "Index two subgroups of F_r")
-/

open Matrix

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- `v_i = 1` if `g_i ∉ U` and `v_i = 0` if `g_i ∈ U`. -/
noncomputable def indexTwoVec (U : Subgroup (FreeGroup ι)) : ι → ZMod 2 :=
  fun i => if FreeGroup.of i ∈ U then 0 else 1

/-- The linear form `w ↦ Σ_j #_{g_j}(w) v_j` modulo two. -/
private noncomputable def parityForm (U : Subgroup (FreeGroup ι)) (w : FreeGroup ι) : ZMod 2 :=
  indexTwoVec U ⬝ᵥ fun j => (count j w : ZMod 2)

/-- An index two subgroup is the kernel of the linear form given by `indexTwoVec`. -/
private theorem mem_iff_parityForm {U : Subgroup (FreeGroup ι)} (hU : U.index = 2)
    (w : FreeGroup ι) : w ∈ U ↔ parityForm U w = 0 := by
  induction w using FreeGroup.induction_on with
  | one => simp [parityForm]
  | of i =>
    have : parityForm U (FreeGroup.of i) = indexTwoVec U i := by
      simp [parityForm, dotProduct, count_of]
    rw [this, indexTwoVec]
    split_ifs with h <;> simp [h]
  | inv_of i ih =>
    rw [inv_mem_iff, ih]
    simp only [parityForm, count_inv, Int.cast_neg, dotProduct, mul_neg, Finset.sum_neg_distrib,
      neg_eq_zero]
  | mul x y hx hy =>
    rw [Subgroup.mul_mem_iff_of_index_two hU, hx, hy]
    simp only [parityForm, count_mul, Int.cast_add, ← Pi.add_def, dotProduct_add]
    generalize indexTwoVec U ⬝ᵥ (fun j => (count j x : ZMod 2)) = a
    generalize indexTwoVec U ⬝ᵥ (fun j => (count j y : ZMod 2)) = b
    revert a b; decide

private theorem parityForm_aut (U : Subgroup (FreeGroup ι)) (γ : MulAut (FreeGroup ι))
    (w : FreeGroup ι) :
    parityForm U (γ w) = (indexTwoVec U ᵥ* (reduce (B γ) : Matrix ι ι (ZMod 2))) ⬝ᵥ
      fun j => (count j w : ZMod 2) := by
  rw [parityForm, ← dotProduct_mulVec]
  congr 1
  ext j
  rw [congrFun (count_apply_aut γ w) j]
  simp [mulVec, dotProduct, B_apply]

/-- **Theorem (index two subgroups)**, integral form. -/
theorem image_Stab_of_index_two {U : Subgroup (FreeGroup ι)} (hU : U.index = 2) :
    (Stab U).map B = (S (indexTwoVec U)).comap reduce := by
  apply le_antisymm
  · rintro _ ⟨γ, hγ, rfl⟩
    rw [Subgroup.mem_comap, mem_S]
    ext i
    have h1 := (mem_Stab_iff.mp hγ (FreeGroup.of i))
    rw [mem_iff_parityForm hU, mem_iff_parityForm hU, parityForm_aut] at h1
    have h2 : parityForm U (FreeGroup.of i) = indexTwoVec U i := by
      simp [parityForm, dotProduct, count_of]
    rw [h2] at h1
    have h3 : (indexTwoVec U ᵥ* (reduce (B γ) : Matrix ι ι (ZMod 2))) ⬝ᵥ
        (fun j => (count j (FreeGroup.of i) : ZMod 2)) =
        (indexTwoVec U ᵥ* (reduce (B γ) : Matrix ι ι (ZMod 2))) i := by
      simp [dotProduct, count_of]
    rw [h3] at h1
    generalize (indexTwoVec U ᵥ* (reduce (B γ) : Matrix ι ι (ZMod 2))) i = a at h1 ⊢
    generalize indexTwoVec U i = b at h1 ⊢
    revert a b; decide
  · intro M hM
    obtain ⟨γ, rfl⟩ := B_surjective M
    refine ⟨γ, mem_Stab_iff.mpr fun w => ?_, rfl⟩
    rw [mem_iff_parityForm hU, mem_iff_parityForm hU, parityForm_aut, (mem_S.mp hM)]
    rfl

/-- **Theorem (index two subgroups)**: for `U < F_r` of index two,
`\overline{B(Stab(U))} = S(v)` with `v_i = 1` iff `g_i ∉ U`. -/
theorem map_reduce_image_Stab_of_index_two {U : Subgroup (FreeGroup ι)} (hU : U.index = 2) :
    ((Stab U).map B).map reduce = S (indexTwoVec U) := by
  rw [image_Stab_of_index_two hU, Subgroup.map_comap_eq_self_of_surjective reduce_surjective]

end LoopSubgroups
