module

public import LoopSubgroups.FreeGroup

@[expose] public section

/-!
# Loop subgroups (Definition 1) and stabilizers

We fix the free group `FreeGroup ι` on the basis `g_i = FreeGroup.of i`. (The basis-independent
formulation is in `LoopSubgroups.Main`.)
-/

open scoped Pointwise
open Equiv

namespace LoopSubgroups

variable {ι : Type*}

/-- `Stab_{Aut(F_r)}(U)`, the stabilizer of `U` under the natural action of `Aut(F_r)` on
subgroups. -/
abbrev Stab (U : Subgroup (FreeGroup ι)) : Subgroup (MulAut (FreeGroup ι)) :=
  MulAction.stabilizer (MulAut (FreeGroup ι)) U

/-- **Definition 1**, for a permutation representation `ρ : F_r → Sym(X)` with base point `x₀`:
the action of each generator `g_i` is a single cycle of length `s_i` through `x₀` (or trivial,
when `s_i = 1`), and the non-trivial cycles meet only in `x₀`. -/
structure IsLoopRep {X : Type*} (ρ : FreeGroup ι →* Perm X) (x₀ : X) (s : ι → ℕ) : Prop where
  loop : ∀ i, (s i = 1 ∧ ρ (.of i) = 1) ∨
    ((ρ (.of i)).IsCycle ∧ {x | ρ (.of i) x ≠ x}.ncard = s i ∧ ρ (.of i) x₀ ≠ x₀)
  inter : ∀ i j, i ≠ j → ∀ x, ρ (.of i) x ≠ x → ρ (.of j) x ≠ x → x = x₀

/-- **Definition 1.** `U ≤ F_r` is an `s_1/…/s_r` loop subgroup (with respect to the basis
`g_i = FreeGroup.of i`) if the action of each `g_i` on the left cosets of `U` is a single cycle of
length `s_i` through the coset `U` (no non-trivial cycle if `s_i = 1`), and these cycles are
otherwise disjoint. -/
def IsLoopSubgroup (U : Subgroup (FreeGroup ι)) (s : ι → ℕ) : Prop :=
  IsLoopRep (MulAction.toPermHom (FreeGroup ι) (FreeGroup ι ⧸ U)) (QuotientGroup.mk 1) s

/-- The parity vector `v` of the main theorem: `v_i = 0` if `s_i` is odd and `1` if `s_i` is even. -/
def parityVec (s : ι → ℕ) : ι → ZMod 2 := fun i => if Even (s i) then 1 else 0

end LoopSubgroups
