module

public import LoopSubgroups.Compat
public import LoopSubgroups.Matrix.Defs

@[expose] public section

/-!
# Generators of the stabilizer `S(v)` of a row vector in `GL_r(ℤ/2ℤ)`

Lemma 8 of the paper.
-/

open Matrix

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Right multiplication of a row vector by `X_ij(c)` adds `c` times its `i`-th entry to its
`j`-th entry. -/
theorem X_vecMul {R : Type*} [CommRing R] {i j : ι} (hij : i ≠ j) (c : R) (w : ι → R) :
    w ᵥ* (X hij c : Matrix ι ι R) = Function.update w j (w j + w i * c) := by
  rw [TauCeti.coe_transvectionUnit_eq_one_add_single, vecMul_add, vecMul_one]
  ext k
  rcases eq_or_ne k j with rfl | hk
  · simp [*, vecMul, dotProduct, Matrix.single_apply]
  · simp [*, vecMul, dotProduct, Ne.symm hk]

/-- The generators of Lemma 8 lie in `S(v)`. -/
theorem stabGens_subset_S (v : ι → ZMod 2) : stabGens v ⊆ (S v : Set (GL ι (ZMod 2))) := by
  rintro M (⟨i, j, hij, hv, rfl⟩ | ⟨i, j, k, hik, hjk, hij, hi, hj, rfl⟩)
  · simp only [SetLike.mem_coe, mem_S, X_vecMul, hv]
    simp
  · simp only [SetLike.mem_coe, mem_S, Units.val_mul, ← vecMul_vecMul, X_vecMul]
    ext l
    rcases eq_or_ne l k with rfl | hl
    · simp [hjk, hi, hj]
      generalize v l = a; revert a; decide
    · simp [hl]

/-- `w'` is obtained from `w` by an element of the closure of the generators that fixes the
unit vectors `e_q` for `q ∈ s`. -/
def Reach (v : ι → ZMod 2) (s : Finset ι) (w w' : ι → ZMod 2) : Prop :=
  ∃ h ∈ Subgroup.closure (stabGens v),
    (∀ q ∈ s, (h : Matrix ι ι (ZMod 2)) *ᵥ Pi.single q 1 = Pi.single q 1) ∧
    (h : Matrix ι ι (ZMod 2)) *ᵥ w = w'

theorem Reach.refl (v : ι → ZMod 2) (s : Finset ι) (w : ι → ZMod 2) : Reach v s w w :=
  ⟨1, one_mem _, fun _ _ => by simp only [Units.val_one, one_mulVec], by simp⟩

theorem Reach.trans {v : ι → ZMod 2} {s : Finset ι} {w w' w'' : ι → ZMod 2}
    (h₁ : Reach v s w w') (h₂ : Reach v s w' w'') : Reach v s w w'' := by
  obtain ⟨h, hh, hs, rfl⟩ := h₁
  obtain ⟨g, hg, gs, rfl⟩ := h₂
  refine ⟨g * h, mul_mem hg hh, fun q hq => ?_, ?_⟩
  · rw [Units.val_mul, ← mulVec_mulVec, hs q hq, gs q hq]
  · rw [Units.val_mul, ← mulVec_mulVec]

theorem Reach.dotProduct_eq {v : ι → ZMod 2} {s : Finset ι} {w w' : ι → ZMod 2}
    (h : Reach v s w w') : v ⬝ᵥ w' = v ⬝ᵥ w := by
  obtain ⟨h, hh, -, rfl⟩ := h
  have : h ∈ S v := (Subgroup.closure_le _).2 (stabGens_subset_S v) hh
  rw [dotProduct_mulVec, mem_S.1 this]

theorem reach_X {v : ι → ZMod 2} {s : Finset ι} {i j : ι} (hij : i ≠ j) (hv : v i = 0)
    (hj : j ∉ s) (w : ι → ZMod 2) : Reach v s w (Function.update w i (w i + w j)) := by
  refine ⟨X hij 1, Subgroup.subset_closure (Or.inl ⟨i, j, hij, hv, rfl⟩), fun q hq => ?_, ?_⟩
  · have : q ≠ j := by rintro rfl; exact hj hq
    simp only [transvectionUnit_mulVec]
    simp [Pi.single_apply, Ne.symm this]
  · simp only [transvectionUnit_mulVec, one_mul]

theorem reach_XX {v : ι → ZMod 2} {s : Finset ι} {i j k : ι} (hik : i ≠ k) (hjk : j ≠ k)
    (hij : i ≠ j) (hi : v i = 1) (hj : v j = 1) (hk : k ∉ s) (w : ι → ZMod 2) :
    Reach v s w (Function.update (Function.update w j (w j + w k)) i (w i + w k)) := by
  refine ⟨X hik 1 * X hjk 1,
    Subgroup.subset_closure (Or.inr ⟨i, j, k, hik, hjk, hij, hi, hj, rfl⟩), fun q hq => ?_, ?_⟩
  · have : q ≠ k := by rintro rfl; exact hk hq
    simp only [Units.val_mul, ← mulVec_mulVec, transvectionUnit_mulVec]
    ext l
    simp only [Function.update_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · simp only [Units.val_mul, ← mulVec_mulVec, transvectionUnit_mulVec]
    simp [hij, Ne.symm hjk]

/-- `A = X_pk X_jk X_kp X_kj` acts on coordinates `(p, j, k)` by
`(a, b, c) ↦ (b + c, a + c, a + b + c)`; hence `A ^ 2` swaps coordinates `p` and `j`. -/
theorem swapElt_mulVec {p j k : ι} (hpk : p ≠ k) (hjk : j ≠ k) (hpj : p ≠ j)
    (x : ι → ZMod 2) :
    ((X hpk 1 * X hjk 1 * X hpk.symm 1 * X hjk.symm 1 : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))
      *ᵥ x = fun l => if l = p then x j + x k else if l = j then x p + x k
        else if l = k then x p + x j + x k else x l := by
  simp only [Units.val_mul, ← mulVec_mulVec, transvectionUnit_mulVec]
  ext l
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all <;> ring_nf <;> reduce_mod_char

/-- If `v_k = 0` and `v_p = v_j = 1`, swapping coordinates `p` and `j` is a reachable move. -/
theorem reach_swap {v : ι → ZMod 2} {s : Finset ι} {p j k : ι} (hpk : p ≠ k) (hjk : j ≠ k)
    (hpj : p ≠ j) (hk : v k = 0) (hp : v p = 1) (hj : v j = 1) (hps : p ∉ s) (hjs : j ∉ s)
    (w : ι → ZMod 2) : Reach v s w (fun l => w (Equiv.swap p j l)) := by
  set A : GL ι (ZMod 2) := X hpk 1 * X hjk 1 * X hpk.symm 1 * X hjk.symm 1 with hA
  have hA2 : ∀ x : ι → ZMod 2, ((A * A : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x =
      fun l => x (Equiv.swap p j l) := by
    intro x
    rw [Units.val_mul, ← mulVec_mulVec, hA, swapElt_mulVec hpk hjk hpj, swapElt_mulVec hpk hjk hpj]
    ext l
    simp only [Equiv.swap_apply_def]
    split_ifs <;> subst_vars <;> simp_all <;> ring_nf <;> reduce_mod_char
  have hmem : A ∈ Subgroup.closure (stabGens v) := by
    refine mul_mem (mul_mem ?_ ?_) ?_ <;> apply Subgroup.subset_closure
    · exact Or.inr ⟨p, j, k, hpk, hjk, hpj, hp, hj, rfl⟩
    · exact Or.inl ⟨k, p, hpk.symm, hk, rfl⟩
    · exact Or.inl ⟨k, j, hjk.symm, hk, rfl⟩
  refine ⟨A * A, mul_mem hmem hmem, fun q hq => ?_, hA2 w⟩
  rw [hA2]
  ext l
  have h1 : q ≠ p := by rintro rfl; exact hps hq
  have h2 : q ≠ j := by rintro rfl; exact hjs hq
  simp only [Equiv.swap_apply_def, Pi.single_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem ZMod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert x; decide

theorem card_support_lt {p i : ι} {w w' : ι → ZMod 2} (hsub : ∀ l, w' l ≠ 0 → w l ≠ 0)
    (hi : i ≠ p) (hwi : w i ≠ 0) (hw'i : w' i = 0) :
    (Finset.univ.filter fun l => l ≠ p ∧ w' l ≠ 0).card <
      (Finset.univ.filter fun l => l ≠ p ∧ w l ≠ 0).card := by
  apply Finset.card_lt_card
  refine ⟨fun l hl => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact ⟨hl.1, hsub l hl.2⟩
  · have := h (show i ∈ _ by simp [hi, hwi])
    simp [hw'i] at this

/-- A vector `w` with `w_p = 1` and `v ⬝ w = v_p` can be moved to `e_p` using only the column
`p ∉ s` (clearing the other entries of `w`). -/
theorem reach_stageB {v : ι → ZMod 2} {s : Finset ι} {p : ι} (hp : p ∉ s) (w : ι → ZMod 2)
    (hwp : w p = 1) (hvw : v ⬝ᵥ w = v p) : Reach v s w (Pi.single p 1) := by
  generalize hn : (Finset.univ.filter fun l => l ≠ p ∧ w l ≠ 0).card = n
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  by_cases hex : ∃ i, i ≠ p ∧ w i ≠ 0
  swap
  · push Not at hex
    have : w = Pi.single p 1 := by
      ext l
      rcases eq_or_ne l p with rfl | hl
      · simp [hwp]
      · simp [hl, hex l hl]
    rw [this]
    exact Reach.refl _ _ _
  obtain ⟨i, hip, hwi⟩ := hex
  have hwi1 := ZMod2_eq_one_of_ne_zero hwi
  rcases eq_or_ne (v i) 0 with hvi | hvi
  · have h1 := reach_X (s := s) hip hvi hp w
    refine h1.trans (ih _ ?_ _ ?_ ?_ rfl)
    · rw [← hn]
      apply card_support_lt (i := i) _ hip hwi
      · simp [hwi1, hwp]; decide
      · intro l hl
        rcases eq_or_ne l i with rfl | hli
        · exact hwi
        · simpa [hli] using hl
    · simp [hip.symm, hwp]
    · rw [h1.dotProduct_eq, hvw]
  · have hvi1 := ZMod2_eq_one_of_ne_zero hvi
    obtain ⟨i', hi'p, hi'i, hvi', hwi'⟩ : ∃ i', i' ≠ p ∧ i' ≠ i ∧ v i' = 1 ∧ w i' = 1 := by
      by_contra hcon
      push Not at hcon
      have hsum : v ⬝ᵥ w = v p * w p + v i * w i := by
        refine Fintype.sum_eq_add p i hip.symm fun x ⟨hxp, hxi⟩ => ?_
        rcases eq_or_ne (v x) 0 with h | h
        · simp [h]
        · have := hcon x hxp hxi (ZMod2_eq_one_of_ne_zero h)
          rcases eq_or_ne (w x) 0 with h' | h'
          · simp [h']
          · exact absurd (ZMod2_eq_one_of_ne_zero h') this
      rw [hvw, hwp, hvi1, hwi1] at hsum
      revert hsum; generalize v p = a; revert a; decide
    have h1 := reach_XX (s := s) hip hi'p hi'i.symm hvi1 hvi' hp w
    refine h1.trans (ih _ ?_ _ ?_ ?_ rfl)
    · rw [← hn]
      apply card_support_lt (i := i) _ hip hwi
      · simp [hwi1, hwp]; decide
      · intro l hl
        rcases eq_or_ne l i with rfl | hli
        · exact hwi
        rcases eq_or_ne l i' with rfl | hli'
        · simp [hwi']
        · simpa [hli, hli'] using hl
    · simp [hip.symm, hi'p.symm, hwp]
    · rw [h1.dotProduct_eq, hvw]

/-- The column `w = M e_p` of a matrix in `S(v)` whose columns in `s` are already unit vectors
can be moved to `e_p`, fixing the `e_q`, `q ∈ s`. -/
theorem reach_col (hι : 3 ≤ Fintype.card ι) {v : ι → ZMod 2} {s : Finset ι} {p : ι}
    (hp : p ∉ s) (w : ι → ZMod 2) (hj : ∃ j ∉ s, w j ≠ 0) (hvw : v ⬝ᵥ w = v p) :
    Reach v s w (Pi.single p 1) := by
  rcases eq_or_ne (w p) 0 with hwp | hwp
  swap
  · exact reach_stageB hp w (ZMod2_eq_one_of_ne_zero hwp) hvw
  obtain ⟨j, hjs, hwj⟩ := hj
  have hjp : j ≠ p := by rintro rfl; exact hwj hwp
  have hwj1 := ZMod2_eq_one_of_ne_zero hwj
  suffices ∃ w', Reach v s w w' ∧ w' p = 1 by
    obtain ⟨w', h1, h2⟩ := this
    exact h1.trans (reach_stageB hp w' h2 (by rw [h1.dotProduct_eq, hvw]))
  rcases eq_or_ne (v p) 0 with hvp | hvp
  · exact ⟨_, reach_X hjp.symm hvp hjs w, by simp [hwp, hwj1]⟩
  have hvp1 := ZMod2_eq_one_of_ne_zero hvp
  by_cases hk : ∃ k, k ≠ p ∧ k ≠ j ∧ v k = 1
  · obtain ⟨k, hkp, hkj, hvk⟩ := hk
    exact ⟨_, reach_XX hjp.symm hkj hkp.symm hvp1 hvk hjs w, by simp [hwp, hwj1]⟩
  push Not at hk
  have hvj : v j = 1 := by
    by_contra hvj
    have hvj0 : v j = 0 := by
      revert hvj; generalize v j = a; revert a; decide
    have hsum : v ⬝ᵥ w = v p * w p + v j * w j := by
      refine Fintype.sum_eq_add p j hjp.symm fun x ⟨hxp, hxj⟩ => ?_
      rcases eq_or_ne (v x) 0 with h | h
      · simp [h]
      · exact absurd (ZMod2_eq_one_of_ne_zero h) (hk x hxp hxj)
    rw [hvw, hwp, hvj0, hvp1] at hsum
    simp at hsum
  obtain ⟨k, hk'⟩ : ((Finset.univ.erase p).erase j).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (by simp [hjp]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk'
  have hvk : v k = 0 := by
    have := hk k hk'.2 hk'.1
    revert this; generalize v k = a; revert a; decide
  exact ⟨_, reach_swap hk'.2.symm hk'.1.symm hjp.symm hvk hvp1 hvj hp hjs w, by simp [hwj1]⟩

/-- **Lemma 8.** For `r ≥ 3`, `S(v)` is generated by the elementary matrices `X_ij` with
`i ≠ j`, `v_i = 0` and the double elementary matrices `X_ik X_jk` with `i, j, k` pairwise
distinct and `v_i = v_j = 1`.

(The paper states this without the hypothesis `r ≥ 3`, which is however needed: for `r = 2` and
`v = (1, 1)` the generating set is empty but `S(v)` contains the swap matrix. The paper only
applies it for `r ≥ 3`, and its proof uses a third index.) -/
theorem closure_stabGens (hι : 3 ≤ Fintype.card ι) (v : ι → ZMod 2) :
    Subgroup.closure (stabGens v) = S v := by
  refine le_antisymm ((Subgroup.closure_le _).2 (stabGens_subset_S v)) fun M hM => ?_
  have inv_cancel : ∀ (N : GL ι (ZMod 2)) (x : ι → ZMod 2),
      ((N⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ ((N : Matrix ι ι (ZMod 2)) *ᵥ x) = x := by
    intro N x
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  suffices key : ∀ n, ∀ s : Finset ι, (Finset.univ \ s).card = n → ∀ M ∈ S v,
      (∀ q ∈ s, (M : Matrix ι ι (ZMod 2)) *ᵥ Pi.single q 1 = Pi.single q 1) →
      M ∈ Subgroup.closure (stabGens v) from
    key _ ∅ rfl M hM (by simp)
  intro n
  induction n with
  | zero =>
    intro s hs M _ hMs
    have hs' : ∀ q, q ∈ s := by
      intro q; by_contra hq
      have : q ∈ Finset.univ \ s := by simp [hq]
      rw [Finset.card_eq_zero.1 hs] at this
      simp at this
    have : M = 1 := by
      ext a b
      have := congrFun (hMs b (hs' b)) a
      simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using this
    rw [this]
    exact one_mem _
  | succ n ih =>
    intro s hs M hM hMs
    obtain ⟨p, hp⟩ : (Finset.univ \ s).Nonempty := by
      rw [← Finset.card_pos, hs]; omega
    have hps : p ∉ s := by simpa using hp
    set w := (M : Matrix ι ι (ZMod 2)) *ᵥ Pi.single p 1 with hw
    have hj : ∃ j ∉ s, w j ≠ 0 := by
      by_contra hc
      push Not at hc
      have hsum : w = ∑ q ∈ s, w q • Pi.single q 1 := by
        ext l
        by_cases hl : l ∈ s
        · simp [Finset.sum_apply, Pi.single_apply, hl]
        · simp [Finset.sum_apply, Pi.single_apply, hl, hc l hl]
      have h1 : ((M⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w = w := by
        conv_lhs => rw [hsum]
        rw [Matrix.mulVec_sum]
        conv_rhs => rw [hsum]
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [mulVec_smul, ← hMs q hq, inv_cancel, hMs q hq]
      have h2 : ((M⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w = Pi.single p 1 := by
        rw [hw, inv_cancel]
      have := congrFun (h2.symm.trans h1) p
      rw [hc p hps] at this
      simp at this
    have hvw : v ⬝ᵥ w = v p := by
      rw [hw, dotProduct_mulVec, mem_S.1 hM]
      simp
    obtain ⟨h, hh, hhs, hhw⟩ := reach_col hι hps w hj hvw
    have hhM : h * M ∈ Subgroup.closure (stabGens v) := by
      refine ih (insert p s) ?_ (h * M)
        (mul_mem ((Subgroup.closure_le _).2 (stabGens_subset_S v) hh) hM) ?_
      · rw [Finset.sdiff_insert, Finset.card_erase_of_mem hp, hs]
        rfl
      · intro q hq
        rw [Units.val_mul, ← mulVec_mulVec]
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact hhw
        · rw [hMs q hq, hhs q hq]
    simpa using mul_mem (inv_mem hh) hhM

end LoopSubgroups
