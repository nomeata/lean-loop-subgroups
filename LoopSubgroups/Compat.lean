module

public import Mathlib
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

@[expose] public section

/-!
# Small lemmas about elementary matrices

Two facts used by the development that are not available in the pinned Tau Ceti release:

* `transvectionUnit_mulVec`: the action of `X_ij(c)` on column vectors;
* `elementarySubgroup_eq_ker_det_int` and `elementarySubgroup_eq_ker_det_zmod_two`: over `ℤ` and
  over `ℤ/2`, the elementary subgroup consists of the matrices of determinant one.
-/

open Matrix

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `X_ij(c)` adds `c` times the `j`-th coordinate to the `i`-th one. -/
theorem transvectionUnit_mulVec {A : Type*} [Ring A] {i j : ι} (hij : i ≠ j) (c : A)
    (v : ι → A) :
    (TauCeti.transvectionUnit hij c : Matrix ι ι A) *ᵥ v = Function.update v i (v i + c * v j) := by
  rw [TauCeti.coe_transvectionUnit_eq_one_add_single, add_mulVec, one_mulVec, single_mulVec]
  ext k
  rcases eq_or_ne k i with rfl | hk <;> simp [*]

/-- Over `ℤ`, the elementary subgroup is the kernel of the determinant. -/
theorem elementarySubgroup_eq_ker_det_int :
    TauCeti.elementarySubgroup ι ℤ = (Matrix.GeneralLinearGroup.det (n := ι) (R := ℤ)).ker := by
  rw [TauCeti.elementarySubgroup_eq_map_closure_range_toSpecialLinearGroup,
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top, ← MonoidHom.range_eq_map,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

/-- Over `ℤ/2`, every invertible matrix is elementary. -/
theorem mem_elementarySubgroup_zmod_two (g : GL ι (ZMod 2)) :
    g ∈ TauCeti.elementarySubgroup ι (ZMod 2) := by
  rw [TauCeti.elementarySubgroup_eq_map_closure_range_toSpecialLinearGroup,
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    ← MonoidHom.range_eq_map, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  exact Subsingleton.elim _ _

end LoopSubgroups
