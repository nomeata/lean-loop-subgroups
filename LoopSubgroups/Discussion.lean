module

public import LoopSubgroups.Main
public import LoopSubgroups.Matrix.Maximal

@[expose] public section

/-!
# The index of `B(Stab(U))` (thesis, Section "Discussion and further directions")

No matter how large the index of the loop subgroup, the index of `B(Stab(U))` in `GL_r(ℤ)` is
bounded by `[GL_r(ℤ/2ℤ) : S(v)] = 2^r - 1`.
-/

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem index_image_Stab {U : Subgroup (FreeGroup ι)} [U.FiniteIndex] {s : ι → ℕ}
    (hU : IsLoopSubgroup U s) (hr : 3 ≤ Fintype.card ι)
    (hl : (Finset.univ.filter (s · = 1)).card + 2 ≤ Fintype.card ι) :
    ((Stab U).map B).index = if ∀ i, Odd (s i) then 1 else 2 ^ Fintype.card ι - 1 := by
  rw [image_Stab_eq hU hr hl, Subgroup.index_comap_of_surjective _ reduce_surjective]
  split_ifs with hodd
  · have : parityVec s = 0 := funext fun i => parityVec_eq_zero_iff.mpr (hodd i)
    rw [this, Subgroup.index_eq_one]
    ext M
    simp [mem_S]
  · refine index_S fun h => hodd fun i => parityVec_eq_zero_iff.mp ?_
    rw [h]; rfl

end LoopSubgroups
