module

public import LoopSubgroups.Matrix.Defs

@[expose] public section

/-!
# The map `B : Aut(F_r) → GL_r(ℤ)` and some automorphisms of free groups

* `ab` : the abelianization `F_r → ℤ^r`, `w ↦ (#_{g_i} w)_i`.
* `B` : **Definition 9**, `γ ↦ (#_{g_i} γ(g_j))_{i,j}`.
* `elemAut j u` : the automorphism `g_j ↦ u g_j`, `g_k ↦ g_k` (`k ≠ j`), for a word `u` not
  involving `g_j` (**Remark 4**).
* `invAut i` : the automorphism `τ_i` inverting `g_i`.
-/

open Matrix

set_option linter.unusedSectionVars false

namespace LoopSubgroups

variable {ι : Type*}

/-- The abelianization map `F_r → ℤ^r`, written multiplicatively. -/
def ab [DecidableEq ι] : FreeGroup ι →* Multiplicative (ι → ℤ) :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (Pi.single j 1)

/-- `#_{g_i} w`, the exponent sum of the generator `g_i` in the word `w`. -/
def count [DecidableEq ι] (i : ι) (w : FreeGroup ι) : ℤ := (ab w).toAdd i

section

variable [DecidableEq ι]

@[simp] theorem ab_of (j : ι) : ab (FreeGroup.of j) = Multiplicative.ofAdd (Pi.single j 1) := by
  simp [ab]

@[simp] theorem count_of (i j : ι) : count i (FreeGroup.of j) = if i = j then 1 else 0 := by
  simp [count, Pi.single_apply]

@[simp] theorem count_mul (i : ι) (v w : FreeGroup ι) : count i (v * w) = count i v + count i w :=
  by simp [count]

@[simp] theorem count_inv (i : ι) (w : FreeGroup ι) : count i w⁻¹ = - count i w := by
  simp [count]

@[simp] theorem count_one (i : ι) : count i (1 : FreeGroup ι) = 0 := by simp [count]

@[simp] theorem count_pow (i : ι) (w : FreeGroup ι) (n : ℕ) : count i (w ^ n) = n * count i w := by
  simp [count]

/-- Words in the commutator subgroup have exponent sum zero in each generator. -/
theorem count_eq_zero_of_mem_commutator {w : FreeGroup ι} (hw : w ∈ commutator (FreeGroup ι))
    (i : ι) : count i w = 0 := by
  have : w ∈ (ab (ι := ι)).ker := Group.Abelianization.commutator_le_ker ab hw
  rw [MonoidHom.mem_ker] at this
  simp [count, this]

end

variable [Fintype ι] [DecidableEq ι]

/-- The matrix `(#_{g_i} γ(g_j))_{i,j}`. -/
def Bmat (γ : MulAut (FreeGroup ι)) : Matrix ι ι ℤ :=
  Matrix.of fun i j => count i (γ (FreeGroup.of j))

@[simp] theorem Bmat_apply (γ : MulAut (FreeGroup ι)) (i j : ι) :
    Bmat γ i j = count i (γ (FreeGroup.of j)) := rfl

theorem count_apply_aut (γ : MulAut (FreeGroup ι)) (w : FreeGroup ι) :
    (fun i => count i (γ w)) = Bmat γ *ᵥ (fun i => count i w) := by
  let L : Multiplicative (ι → ℤ) →* Multiplicative (ι → ℤ) :=
    AddMonoidHom.toMultiplicative (Matrix.mulVecLin (Bmat γ)).toAddMonoidHom
  have key : (ab (ι := ι)).comp (γ : FreeGroup ι →* FreeGroup ι) = L.comp ab := by
    ext j : 1
    simp only [MonoidHom.comp_apply, ab_of, L, AddMonoidHom.toMultiplicative_apply_apply,
      toAdd_ofAdd, LinearMap.toAddMonoidHom_coe, mulVecLin_apply, mulVec_single_one]
    ext i
    simp [Bmat, count]
  have := congrArg (fun f => (f w).toAdd) key
  simpa [L, count] using this

theorem Bmat_mul (γ δ : MulAut (FreeGroup ι)) : Bmat (γ * δ) = Bmat γ * Bmat δ := by
  ext i j
  rw [Bmat_apply, MulAut.mul_apply, congrFun (count_apply_aut γ (δ (FreeGroup.of j))) i]
  simp [mulVec, dotProduct, Matrix.mul_apply]

theorem Bmat_one : Bmat (1 : MulAut (FreeGroup ι)) = 1 := by
  ext i j
  simp [Bmat, Matrix.one_apply]

/-- **Definition 9.** The map `B : Aut(F_r) → GL_r(ℤ)`, `γ ↦ (#_{g_i} γ(g_j))_{i,j}`, induced by
the abelianization. -/
def B : MulAut (FreeGroup ι) →* GL ι ℤ :=
  MonoidHom.toHomUnits
    { toFun := Bmat
      map_one' := Bmat_one
      map_mul' := Bmat_mul }

@[simp] theorem coe_B (γ : MulAut (FreeGroup ι)) : (B γ : Matrix ι ι ℤ) = Bmat γ := rfl

theorem B_apply (γ : MulAut (FreeGroup ι)) (i j : ι) :
    (B γ : Matrix ι ι ℤ) i j = count i (γ (FreeGroup.of j)) := rfl

/-! ### Automorphisms of the form `g_j ↦ u g_j` (Remark 4) -/

/-- The subgroup of words not involving the generator `g_j`. -/
def avoiding (j : ι) : Subgroup (FreeGroup ι) :=
  Subgroup.closure {w | ∃ k, k ≠ j ∧ w = FreeGroup.of k}

/-- A homomorphism fixing all generators but `g_j` fixes all words avoiding `g_j`. -/
theorem eq_self_of_mem_avoiding {j : ι} (f : FreeGroup ι →* FreeGroup ι)
    (hf : ∀ k, k ≠ j → f (FreeGroup.of k) = FreeGroup.of k) {u : FreeGroup ι}
    (hu : u ∈ avoiding j) : f u = u := by
  have : avoiding j ≤ MonoidHom.eqLocus f (MonoidHom.id _) := by
    rw [avoiding, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hf k hk
  exact this hu

/-- The endomorphism `g_j ↦ u g_j`, `g_k ↦ g_k` for `k ≠ j`. -/
def elemHom (j : ι) (u : FreeGroup ι) : FreeGroup ι →* FreeGroup ι :=
  FreeGroup.lift fun k => if k = j then u * FreeGroup.of j else FreeGroup.of k

@[simp] theorem elemHom_of_self (j : ι) (u : FreeGroup ι) :
    elemHom j u (FreeGroup.of j) = u * FreeGroup.of j := by simp [elemHom]

theorem elemHom_of_ne {j k : ι} (hk : k ≠ j) (u : FreeGroup ι) :
    elemHom j u (FreeGroup.of k) = FreeGroup.of k := by simp [elemHom, hk]

theorem elemHom_comp {j : ι} {u v : FreeGroup ι} (hu : u ∈ avoiding j) :
    (elemHom j v).comp (elemHom j u) = elemHom j (u * v) := by
  ext k : 1
  by_cases hk : k = j
  · subst hk
    simp [eq_self_of_mem_avoiding (elemHom k v) (fun l hl => elemHom_of_ne hl v) hu, mul_assoc]
  · simp [elemHom_of_ne hk]

theorem elemHom_one (j : ι) : elemHom j (1 : FreeGroup ι) = MonoidHom.id _ := by
  ext k : 1
  by_cases hk : k = j
  · subst hk; simp
  · simp [elemHom_of_ne hk]

/-- **Remark 4.** For `u` not involving `g_j`, the map `g_j ↦ u g_j`, `g_k ↦ g_k` (`k ≠ j`) is an
automorphism of the free group. -/
noncomputable def elemAut (j : ι) (u : FreeGroup ι) (hu : u ∈ avoiding j) : MulAut (FreeGroup ι) :=
  MulEquiv.ofBijective (elemHom j u) <| by
    have h1 := elemHom_comp (v := u⁻¹) hu
    have h2 := elemHom_comp (v := u) (inv_mem hu)
    simp only [mul_inv_cancel, inv_mul_cancel, elemHom_one] at h1 h2
    constructor
    · exact Function.LeftInverse.injective (g := elemHom j u⁻¹) fun x => by
        simpa using DFunLike.congr_fun h1 x
    · exact Function.RightInverse.surjective (g := elemHom j u⁻¹) fun x => by
        simpa using DFunLike.congr_fun h2 x

@[simp] theorem elemAut_apply (j : ι) (u : FreeGroup ι) (hu : u ∈ avoiding j) (w : FreeGroup ι) :
    elemAut j u hu w = elemHom j u w := rfl

/-- The image of `elemAut j u` under `B` is the identity plus the abelianization of `u` in
column `j`. -/
theorem B_elemAut (j : ι) (u : FreeGroup ι) (hu : u ∈ avoiding j) :
    (B (elemAut j u hu) : Matrix ι ι ℤ) =
      1 + Matrix.of fun a b => if b = j then count a u else 0 := by
  ext a b
  rw [B_apply, elemAut_apply]
  by_cases hb : b = j
  · subst hb; simp [Matrix.one_apply, add_comm]
  · simp [elemHom_of_ne hb, hb, Matrix.one_apply]

/-! ### The automorphism `τ_i` inverting `g_i` -/

/-- The endomorphism `g_i ↦ g_i⁻¹`, `g_k ↦ g_k` for `k ≠ i`. -/
def invHom (i : ι) : FreeGroup ι →* FreeGroup ι :=
  FreeGroup.lift fun k => if k = i then (FreeGroup.of i)⁻¹ else FreeGroup.of k

theorem invHom_invHom (i : ι) : (invHom i).comp (invHom i) = MonoidHom.id _ := by
  ext k : 1
  by_cases hk : k = i
  · subst hk; simp [invHom]
  · simp [invHom, hk]

/-- The automorphism `τ_i`, inverting the generator `g_i` and fixing the others. -/
noncomputable def invAut (i : ι) : MulAut (FreeGroup ι) :=
  MulEquiv.ofBijective (invHom i) <| by
    have h : ∀ x, invHom i (invHom i x) = x := fun x => by
      simpa using DFunLike.congr_fun (invHom_invHom i) x
    exact ⟨Function.LeftInverse.injective (g := invHom i) h,
      Function.RightInverse.surjective (g := invHom i) h⟩

theorem invAut_of_self (i : ι) : invAut i (FreeGroup.of i) = (FreeGroup.of i)⁻¹ := by
  simp [invAut, invHom]

theorem invAut_of_ne {i k : ι} (hk : k ≠ i) : invAut i (FreeGroup.of k) = FreeGroup.of k := by
  simp [invAut, invHom, hk]

theorem B_invAut (i : ι) : B (invAut i) = T i := by
  ext a b
  rw [B_apply]
  by_cases hb : b = i
  · subst hb
    simp [invAut_of_self, T, diagonal_apply, Function.update_apply]
    split_ifs <;> simp_all
  · simp only [invAut_of_ne hb, count_of, T, diagonal_apply, Function.update_apply]
    split_ifs <;> simp_all

end LoopSubgroups
