import Mathlib
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Matrix groups used in the paper (Section 4 and 5)

* `X hij c` : the elementary matrix `X_ij(c) = 1 + c E_ij` (Tau Ceti's `transvectionUnit`);
  the paper's `X_ij` is `X hij 1` and `X_ij^2` is `X hij 2`.
* `T i` : the diagonal matrix with `-1` at position `i` and `1` elsewhere.
* `reduce` : reduction `GL_r(ℤ) → GL_r(ℤ/2ℤ)`.
* `Γ₂` : the principal congruence subgroup of level two.
* `S v` : the stabilizer of the row vector `v` under right multiplication.
-/

open Matrix

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The elementary matrix `X_ij(c)`, with ones on the diagonal and `c` at position `(i, j)`. -/
abbrev X {R : Type*} [CommRing R] {i j : ι} (hij : i ≠ j) (c : R) : GL ι R :=
  TauCeti.transvectionUnit hij c

/-- `T i = diag(1, …, 1, -1, 1, …, 1)` with the `-1` in row `i`. -/
def T {R : Type*} [CommRing R] (i : ι) : GL ι R where
  val := diagonal (Function.update 1 i (-1))
  inv := diagonal (Function.update 1 i (-1))
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext k
    by_cases hk : k = i <;> simp [hk]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext k
    by_cases hk : k = i <;> simp [hk]

/-- Reduction modulo two, `GL_r(ℤ) → GL_r(ℤ/2ℤ)`; we write `M̄` for `reduce M`. -/
noncomputable abbrev reduce : GL ι ℤ →* GL ι (ZMod 2) :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 2))

/-- The principal congruence subgroup of level two, `Γ₂ = {A ∈ GL_r(ℤ) | A ≡ 1 mod 2}`. -/
noncomputable def Γ₂ : Subgroup (GL ι ℤ) := (reduce (ι := ι)).ker

/-- `S(v) = {M ∈ GL_r(ℤ/2ℤ) | v · M = v}`, the stabilizer of the row vector `v`. -/
def S (v : ι → ZMod 2) : Subgroup (GL ι (ZMod 2)) where
  carrier := {M | v ᵥ* (M : Matrix ι ι (ZMod 2)) = v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, ← vecMul_vecMul] at *
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]

theorem mem_S {v : ι → ZMod 2} {M : GL ι (ZMod 2)} :
    M ∈ S v ↔ v ᵥ* (M : Matrix ι ι (ZMod 2)) = v := Iff.rfl

/-- The generators of `Γ₂` from Remark 6: squares of elementary matrices and the `T i`. -/
def gamma2Gens : Set (GL ι ℤ) :=
  {M | ∃ (i j : ι) (hij : i ≠ j), M = X hij 2} ∪ Set.range T

/-- The generators of `S(v)` from Lemma 8: the `X_ij` with `v_i = 0`, and the
"double elementary matrices" `X_ik X_jk` with `i, j, k` pairwise distinct and `v_i = v_j = 1`. -/
def stabGens (v : ι → ZMod 2) : Set (GL ι (ZMod 2)) :=
  {M | ∃ (i j : ι) (hij : i ≠ j), v i = 0 ∧ M = X hij 1} ∪
  {M | ∃ (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k), i ≠ j ∧ v i = 1 ∧ v j = 1 ∧
      M = X hik 1 * X hjk 1}

end LoopSubgroups
