module

public import LoopSubgroups.Compat
public import LoopSubgroups.Matrix.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

@[expose] public section

/-!
# Maximality and index of `S(v)` (thesis, Section "Maximality")
-/

open Matrix

namespace LoopSubgroups

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reduction `GL_r(ℤ) → GL_r(ℤ/2ℤ)` is surjective. -/
theorem reduce_surjective : Function.Surjective (reduce (ι := ι)) := by
  intro g
  have hg : g ∈ TauCeti.elementarySubgroup ι (ZMod 2) := mem_elementarySubgroup_zmod_two g
  have : TauCeti.elementarySubgroup ι (ZMod 2) ≤ (reduce (ι := ι)).range := by
    rw [TauCeti.elementarySubgroup_def, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    refine ⟨TauCeti.transvectionUnit hij (a.val : ℤ), ?_⟩
    simp [TauCeti.map_transvectionUnit]
  exact this hg

omit [Fintype ι] [DecidableEq ι] in
theorem mk_injective_zmod2 {a b : ι → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) :
    Projectivization.mk (ZMod 2) a ha = Projectivization.mk (ZMod 2) b hb ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ ha hb).1 h
  obtain rfl | rfl : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  · exact absurd (by simpa using hc.symm) ha
  · simpa using hc.symm

/-- `GL_r(ℤ/2ℤ)` acts 2-transitively on nonzero row vectors (via the 2-transitivity of `SL`
on projective space, which over `ℤ/2ℤ` is the set of nonzero vectors). -/
theorem exists_vecMul_eq_pair {u u' w w' : ι → ZMod 2} (hu : u ≠ 0) (hu' : u' ≠ 0) (hw : w ≠ 0)
    (hw' : w' ≠ 0) (huu' : u ≠ u') (hww' : w ≠ w') :
    ∃ g : GL ι (ZMod 2), u ᵥ* (g : Matrix ι ι (ZMod 2)) = w ∧
      u' ᵥ* (g : Matrix ι ι (ZMod 2)) = w' := by
  have h2 : ∀ {a b c d : Projectivization (ZMod 2) (ι → ZMod 2)}, a ≠ b → c ≠ d →
      ∃ g : SpecialLinearGroup ι (ZMod 2), g • a = c ∧ g • b = d :=
    MulAction.is_two_pretransitive_iff.1 inferInstance
  obtain ⟨g, h1, h1'⟩ := h2 (a := .mk _ u hu) (b := .mk _ u' hu') (c := .mk _ w hw)
    (d := .mk _ w' hw') (by rwa [Ne, mk_injective_zmod2]) (by rwa [Ne, mk_injective_zmod2])
  rw [Projectivization.smul_mk, mk_injective_zmod2] at h1 h1'
  refine ⟨nonsingInvUnit ((g : Matrix ι ι (ZMod 2))ᵀ) (by simp), ?_, ?_⟩
  · show u ᵥ* (g : Matrix ι ι (ZMod 2))ᵀ = w
    rw [vecMul_transpose, ← h1]; rfl
  · show u' ᵥ* (g : Matrix ι ι (ZMod 2))ᵀ = w'
    rw [vecMul_transpose, ← h1']; rfl

/-- Nonzero row vectors over `ℤ/2ℤ`. -/
def NZ (ι : Type*) := {v : ι → ZMod 2 // v ≠ 0}

/-- Constructor for `NZ`. -/
def NZ.mk {v : ι → ZMod 2} (hv : v ≠ 0) : NZ ι := ⟨v, hv⟩

theorem vecMul_inv_ne_zero (M : GL ι (ZMod 2)) {v : ι → ZMod 2} (hv : v ≠ 0) :
    v ᵥ* ((M⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) ≠ 0 := by
  intro h
  apply hv
  have := congrArg (· ᵥ* (M : Matrix ι ι (ZMod 2))) h
  simpa [vecMul_vecMul, ← Units.val_mul] using this

/-- `GL_r(ℤ/2ℤ)` acts on nonzero row vectors by `M • v = v · M⁻¹`. -/
instance : MulAction (GL ι (ZMod 2)) (NZ ι) where
  smul M x := ⟨x.1 ᵥ* ((M⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)), vecMul_inv_ne_zero M x.2⟩
  one_smul x := Subtype.ext (by show x.1 ᵥ* _ = _; simp)
  mul_smul M N x := Subtype.ext (by
    change x.1 ᵥ* (((M * N)⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) =
      (x.1 ᵥ* ((N⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))) ᵥ* ((M⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))
    simp [vecMul_vecMul, _root_.mul_inv_rev])

omit [Fintype ι] [DecidableEq ι] in
theorem NZ.ext_iff' {x y : NZ ι} : x = y ↔ x.1 = y.1 := Subtype.ext_iff

theorem NZ.smul_val (M : GL ι (ZMod 2)) (x : NZ ι) :
    (M • x).1 = x.1 ᵥ* ((M⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) := rfl

theorem stabilizer_NZ {v : ι → ZMod 2} (hv : v ≠ 0) :
    MulAction.stabilizer (GL ι (ZMod 2)) (NZ.mk hv) = S v := by
  ext M
  rw [MulAction.mem_stabilizer_iff, NZ.ext_iff', NZ.smul_val]
  exact (S v).inv_mem_iff

instance : MulAction.IsMultiplyPretransitive (GL ι (ZMod 2)) (NZ ι) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g, hg, hg'⟩ := exists_vecMul_eq_pair a.2 b.2 c.2 d.2
    (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
  exact ⟨g⁻¹, Subtype.ext (by simpa [NZ.smul_val] using hg),
    Subtype.ext (by simpa [NZ.smul_val] using hg')⟩

instance : MulAction.IsPretransitive (GL ι (ZMod 2)) (NZ ι) :=
  MulAction.isPretransitive_of_is_two_pretransitive

theorem card_NZ : Nat.card (NZ ι) = 2 ^ Fintype.card ι - 1 := by
  unfold NZ
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_pi]
  simp

/-- For `v ≠ 0`, `[GL_r(ℤ/2ℤ) : S(v)] = 2^r - 1`. (Used in the thesis' discussion.) -/
theorem index_S {v : ι → ZMod 2} (hv : v ≠ 0) : (S v).index = 2 ^ Fintype.card ι - 1 := by
  rw [← stabilizer_NZ hv, MulAction.index_stabilizer_of_transitive, card_NZ]

/-- **Lemma `max`.** For `v ≠ 0`, `S(v)` is a maximal subgroup of `GL_r(ℤ/2ℤ)`.
(The thesis assumes `r ≥ 3`; `r ≥ 2` suffices.) -/
theorem isCoatom_S (hr : 2 ≤ Fintype.card ι) {v : ι → ZMod 2} (hv : v ≠ 0) : IsCoatom (S v) := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hr
  have : Nontrivial (NZ ι) := ⟨⟨⟨Pi.single i 1, by simp⟩, ⟨Pi.single j 1, by simp⟩, by
    intro h
    have := congrFun (congrArg Subtype.val h) i
    simp [Ne.symm hij] at this⟩⟩
  have : MulAction.IsPreprimitive (GL ι (ZMod 2)) (NZ ι) :=
    MulAction.isPreprimitive_of_is_two_pretransitive inferInstance
  rw [← stabilizer_NZ hv]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := GL ι (ZMod 2)) (NZ.mk hv)

/-- **Lemma `stabconj`.** For `v ≠ 0`, `S(v)` is conjugate to `S(𝟙)`: `S(v) = N⁻¹ S(𝟙) N` for
any `N` with `𝟙 · N = v`. -/
theorem exists_S_eq_conj {v : ι → ZMod 2} (hv : v ≠ 0) :
    ∃ N : GL ι (ZMod 2), S v = (S 1).map (MulAut.conj N⁻¹).toMonoidHom := by
  have h1 : (1 : ι → ZMod 2) ≠ 0 := by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hv
    exact fun h => by simpa using congrFun h i
  obtain ⟨M, hM⟩ := MulAction.exists_smul_eq (GL ι (ZMod 2)) (NZ.mk h1) (NZ.mk hv)
  have hN : (1 : ι → ZMod 2) ᵥ* ((M⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) = v :=
    congrArg Subtype.val hM
  refine ⟨M⁻¹, ?_⟩
  rw [Subgroup.map_equiv_eq_comap_symm']
  ext A
  simp only [Subgroup.mem_comap, mem_S, MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, inv_inv,
    Units.val_mul, ← vecMul_vecMul, hN]
  constructor
  · intro h; rw [h, ← hN, vecMul_vecMul, ← Units.val_mul]; simp
  · intro h
    calc v ᵥ* (A : Matrix ι ι (ZMod 2))
        = (v ᵥ* (A : Matrix ι ι (ZMod 2)) ᵥ* (M : Matrix ι ι (ZMod 2))) ᵥ*
            ((M⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) := by
          rw [vecMul_vecMul _ (M : Matrix ι ι (ZMod 2)), ← Units.val_mul]; simp
      _ = v := by rw [h, hN]

end LoopSubgroups
