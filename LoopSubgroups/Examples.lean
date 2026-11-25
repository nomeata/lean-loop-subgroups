import LoopSubgroups.Existence

/-!
# Examples and special cases

* The odd case (thesis, Theorem "oddcase"): if all loops are odd, `B(Stab(U)) = GL_r(ℤ)`.
* **Example 2**: the `3/3/1` loop subgroup of `F_3`, which has index 5; here `B(Stab(U))` is all of
  `GL_3(ℤ)`.
-/

open Matrix

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem S_zero : S (0 : ι → ZMod 2) = ⊤ := by
  ext M; simp [mem_S]

/-- If all loops are odd, the image of the stabilizer is all of `GL_r(ℤ)`. -/
theorem image_Stab_eq_top_of_odd {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) (hodd : ∀ i, Odd (s i)) :
    (Stab U).map B = ⊤ := by
  have : parityVec s = 0 := funext fun i => parityVec_eq_zero_iff.mpr (hodd i)
  rw [image_Stab_eq hU hr hl, this, S_zero, Subgroup.comap_top]

/-- The loop lengths `3/3/1` of Example 2. -/
def s331 : Fin 3 → ℕ := ![3, 3, 1]

/-- **Example 2.** The `3/3/1` loop subgroup of `F_3`. -/
example : IsLoopSubgroup (loopSubgroup s331) s331 :=
  isLoopSubgroup_loopSubgroup (by decide)

example : (loopSubgroup s331).index = 5 := by
  rw [index_loopSubgroup]; decide

/-- For the `3/3/1` loop subgroup, `B(Stab(U)) = GL_3(ℤ)`. -/
example : (Stab (loopSubgroup s331)).map B = ⊤ :=
  image_Stab_eq_top_of_odd (isLoopSubgroup_loopSubgroup (by decide)) (by simp) (by decide)
    (by decide)

end LoopSubgroups
