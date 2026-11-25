module

public import Mathlib

@[expose] public section

/-!
# The CosetProject algorithm (Algorithm `algo:cosetproject`)

This file formalizes the section "Second approach: CosetProject" of the thesis: the algorithm,
its termination, and its correctness.

## Coset tables

A *coset table* with rows `Q` for the free group `FreeGroup α` is a function
`C : Q → α × Bool → Q` (`CosetProject.Table Q α`). The columns are the letters `X = α × Bool`:
the generators `(a, true)` and their inverses `(a, false)`, as in Mathlib's `FreeGroup`.
In the notation of the thesis, `C k x = j` means `U_j = x · U_k` (left cosets, left action).

* `Table.IsPerm`: the two columns of every generator are mutually inverse maps.
* `Table.toHom`: such a table defines `FreeGroup α →* Perm Q`. `Table.trace` traces a word
  (from the right, because the action is a left action), and `Table.toHom_mk` says that tracing
  computes the action of the word. `Table.ofHom` and `Table.toHom_ofHom` give the converse.
* `Table.IsCosetTable C q₀ U`: `C` is a coset table of `U ≤ FreeGroup α` with base row `q₀`.
  This means that the action is transitive and that the stabilizer of `q₀` is `U`. The rows are
  then in bijection with the left cosets `FreeGroup α ⧸ U` (`Table.IsCosetTable.equivQuotient`).

## The algorithm

`cosetProject C R` takes a table `C` with rows `Fin n` and a list `R` of relators (words in the
letters). It returns a `State`: the modified table, and the set of rows marked as *merged*.
To loop over the letters `X` in a fixed order we need `[FinEnum α]`.

The thesis defines `Coincidence(i, j)` recursively. We implement it with an explicit stack of
pending calls (`coincidence s stack`):

* if the top pair `(a, b)` has `a = b`, we drop it. This is the test `C[i][g] ≠ C[j][g]` of
  the thesis;
* otherwise, let `i = min a b` and `j = max a b`. We replace every table entry `j` by `i`, mark
  row `j` as merged, and push the pairs `(C[i][g], C[j][g])` for all letters `g`. The pair of
  the first letter goes on top, so it is processed first, as in the recursive version. We also
  apply the replacement `j ↦ i` to the pairs that are already on the stack.

Why this is the same as the recursive version: after the nested call for the letter `g` returns,
the thesis reads the *current* entries `C[i][g']` and `C[j][g']` for the next letter `g'`.
Table entries change only by the replacements `j ↦ i` of nested calls. We apply the same
replacements to the waiting pairs, so the pair that we pop for `g'` is exactly the pair of
current entries that the recursive version reads. There are two small differences. First, we mark
row `j` as merged at the start of `Coincidence(i, j)`, not at the end; nothing reads the mark in
between. Second, a defensive test skips a pair whose larger entry is already merged. The
invariant (`Inv.stack_fix`) shows that this case never happens (case `case3` in the proof of
`coincidence_spec`). With this test, termination is easy: every merge marks a new row, so the
pair (number of unmerged rows, length of the stack) decreases lexicographically. This is the
termination argument of the thesis: each coset is removed at most once.

The main loop (`processRelators`, `cosetProject`) is the main loop of the thesis, with one change:
it checks whether row `i` is merged before *each* relator, not only once before all relators.
Row `i` can be merged into a smaller row while its relators are traced. The thesis then continues
to trace from the old row `i`, and a call of `Coincidence` with the merged row `i` as the smaller
argument would put `i` back into the table. (We did not find an example where this happens, in
a random search.) With the extra check, all table entries are unmerged rows at all times. The
skipped relators do not lose information, because the row that `i` was merged into is
processed with all relators.

## Correctness

Let `C` be a coset table of `U`, `N = ⟪R⟫` the normal closure of the relators, and
`π : F → F/⟪R⟫` the projection. `cosetProject_correct` says:

* row `0` is not merged;
* the non-merged rows are closed under the table;
* the table restricted to the non-merged rows is a coset table (bijective generator columns,
  transitive action) of `U ⊔ N = π⁻¹(π(U))`.

`cosetProject_correct'` gives the same subgroup as the preimage of the image of `U` in Mathlib's
`PresentedGroup`.

The proof follows the thesis. Write `i ≡ j` if `π(U_i) = π(U_j)`, i.e. `ρ w i = j` for some
`w ∈ N` (`projRel`; `ρ` is the action given by `C`). We describe the state of the algorithm with
a ghost function `f : Fin n → Fin n`: the composition of all replacements `j ↦ i` so far.
The invariant `Inv` says:

* `s.table k x = f (C k x)`: the current table is the original one, with every coset replaced by
  its current representative. Together with `f m ≡ m`, this is the invariant
  `π(U_{C[k][g]}) = π(g · U_k)` of the thesis;
* the pairs on the stack are `≡`-related. This is Case 1 (main loop) and Case 2 (nested calls)
  of the thesis;
* row `m` is merged if and only if `f m ≠ m`; also `f m ≤ m`;
* `Inv.cong`: if `f a = f b`, then `C a x` and `C b x` are related by the equivalence relation
  `≈` generated by the kernel of `f` and the pending pairs (`pend`). This is the relation `≈`
  of the thesis. It records that for every merged pair of rows, the comparison of the rows is
  done or still pending.

At the end the stack is empty. So the kernel of `f` is invariant under all generators, and the
main loop makes sure that it contains all pairs `(k, ρ r k)` for `r ∈ R`. The elements `w` with
`f (ρ w k) = f k` for all `k` thus form a normal subgroup that contains `R`, hence `N`. So the
kernel of `f` contains `≡`. This is the direction "`i ≡ j → i ≈ j`" of the thesis, which the
thesis proves by induction on the word `v` of a conjugate `v r v⁻¹`. The other direction follows
from the invariant. So the kernel of `f` is exactly `≡`, the non-merged rows are the
representatives `f m` of the `≡`-classes, and the final entry `f (C k x)` of a non-merged row `k`
represents the class of `x · U_k`.
-/

open Equiv Relation

namespace LoopSubgroups.CosetProject

variable {α : Type*} {Q : Type*}

/-! ### Coset tables -/

/-- A coset table with rows `Q` for the free group `FreeGroup α`: the entry `C k x` for a letter
`x = (a, b)` (the generator `a` if `b = true`, its inverse if `b = false`) is the row reached from
row `k` along `x`, i.e. `U_{C k x} = x · U_k` in the notation of the thesis. -/
def Table (Q : Type*) (α : Type*) := Q → α × Bool → Q

namespace Table

variable (C : Table Q α)

/-- Trace a word in the table, starting at row `k`. As `C k x` is the coset `x · U_k`, the word
`w = x₁ ⋯ xₘ` is traced from the right, and the result is the coset `w · U_k`
(see `toHom_mk`). -/
def trace (w : List (α × Bool)) (k : Q) : Q := w.foldr (fun x k => C k x) k

@[simp] lemma trace_nil (k : Q) : C.trace [] k = k := rfl

@[simp] lemma trace_cons (x : α × Bool) (w : List (α × Bool)) (k : Q) :
    C.trace (x :: w) k = C (C.trace w k) x := rfl

/-- The columns of the generator `a` and of its inverse are mutually inverse maps. -/
def IsPerm : Prop := ∀ k a b, C (C k (a, b)) (a, !b) = k

/-- The permutation of the rows given by the generator `a`. -/
def genPerm (h : C.IsPerm) (a : α) : Perm Q where
  toFun k := C k (a, true)
  invFun k := C k (a, false)
  left_inv k := h k a true
  right_inv k := h k a false

/-- A table with bijective generator columns defines an action of the free group. -/
def toHom (h : C.IsPerm) : FreeGroup α →* Perm Q := FreeGroup.lift (C.genPerm h)

/-- The action of a word is computed by tracing it in the table. -/
lemma toHom_mk (h : C.IsPerm) (w : List (α × Bool)) (k : Q) :
    C.toHom h (FreeGroup.mk w) k = C.trace w k := by
  rw [toHom, FreeGroup.lift_mk]
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨a, b⟩ := x
    simp only [List.map_cons, List.prod_cons, Perm.mul_apply, ih, trace_cons]
    cases b <;> rfl

lemma toHom_letter (h : C.IsPerm) (x : α × Bool) (k : Q) :
    C.toHom h (FreeGroup.mk [x]) k = C k x :=
  C.toHom_mk h [x] k

/-- Conversely, the table of an action of the free group. -/
def ofHom (ρ : FreeGroup α →* Perm Q) : Table Q α := fun k x => ρ (FreeGroup.mk [x]) k

lemma ofHom_isPerm (ρ : FreeGroup α →* Perm Q) : (ofHom ρ).IsPerm := by
  intro k a b
  simp only [ofHom, ← Perm.mul_apply, ← map_mul, FreeGroup.mul_mk]
  have h1 : FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := by
    rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
  have h2 : FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl
  cases b
  · rw [← FreeGroup.mul_mk, Bool.not_false, h1, h2]; simp
  · rw [← FreeGroup.mul_mk, Bool.not_true, h1, h2]; simp

lemma toHom_ofHom (ρ : FreeGroup α →* Perm Q) : (ofHom ρ).toHom (ofHom_isPerm ρ) = ρ := by
  apply FreeGroup.ext_hom
  intro a
  ext k
  exact (ofHom ρ).toHom_letter _ (a, true) k

/-- `C` is a coset table of the subgroup `U` with base row `q₀`: the generator columns are
bijective, the action is transitive, and the stabilizer of `q₀` is `U`. -/
structure IsCosetTable (q₀ : Q) (U : Subgroup (FreeGroup α)) : Prop where
  isPerm : C.IsPerm
  transitive : ∀ q, ∃ g, C.toHom isPerm g q₀ = q
  stabilizer_eq : (MulAction.stabilizer (Perm Q) q₀).comap (C.toHom isPerm) = U

lemma IsCosetTable.mem_iff {C : Table Q α} {q₀ : Q} {U : Subgroup (FreeGroup α)}
    (hC : C.IsCosetTable q₀ U) (g : FreeGroup α) : g ∈ U ↔ C.toHom hC.isPerm g q₀ = q₀ := by
  rw [← SetLike.ext_iff.mp hC.stabilizer_eq g]
  simp [MulAction.mem_stabilizer_iff, Perm.smul_def]

/-- The rows of a coset table of `U` correspond to the left cosets of `U`: the coset `g U`
corresponds to the row `g · q₀`. -/
noncomputable def IsCosetTable.equivQuotient {C : Table Q α} {q₀ : Q}
    {U : Subgroup (FreeGroup α)} (hC : C.IsCosetTable q₀ U) : FreeGroup α ⧸ U ≃ Q :=
  Equiv.ofBijective
    (Quotient.lift (fun g => C.toHom hC.isPerm g q₀) (by
      intro g g' hgg'
      have := QuotientGroup.leftRel_apply.mp hgg'
      rw [hC.mem_iff, map_mul, map_inv, Perm.mul_apply, Perm.inv_eq_iff_eq] at this
      exact this.symm))
    (by
      constructor
      · intro c c'
        induction c using QuotientGroup.induction_on with | H g => ?_
        induction c' using QuotientGroup.induction_on with | H g' => ?_
        intro hgg'
        apply QuotientGroup.eq.mpr
        rw [hC.mem_iff]
        change C.toHom hC.isPerm g q₀ = C.toHom hC.isPerm g' q₀ at hgg'
        simp [Perm.mul_apply, ← hgg']
      · intro q
        obtain ⟨g, hg⟩ := hC.transitive q
        exact ⟨QuotientGroup.mk g, hg⟩)

/-- Restrict a table to a set of rows that is closed under the table. -/
def restrict (p : Q → Prop) (h : ∀ k x, p k → p (C k x)) : Table {k // p k} α :=
  fun k x => ⟨C k x, h k x k.2⟩

end Table

/-! ### The algorithm -/

/-- Replace the coset number `j` by `i`. -/
def replace {n : ℕ} (j i : Fin n) (k : Fin n) : Fin n := if k = j then i else k

/-- The state of the algorithm: the current table, and which rows are marked as merged. -/
structure State (n : ℕ) (α : Type*) where
  table : Table (Fin n) α
  merged : Fin n → Bool

/-- The number of rows not marked as merged (part of the termination measure). -/
def State.unmergedCount {n : ℕ} (s : State n α) : ℕ :=
  (Finset.univ.filter fun k => s.merged k = false).card

lemma unmergedCount_lt {n : ℕ} (s : State n α) (t : Table (Fin n) α) (j : Fin n)
    (hj : s.merged j = false) :
    (State.mk t (Function.update s.merged j true)).unmergedCount < s.unmergedCount := by
  unfold State.unmergedCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j, by simp [hj], by simp⟩
  · intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    by_cases hk : k = j
    · subst hk; simp at h
    · simpa [Function.update_of_ne hk] using h

variable [FinEnum α]

/-- The set `X` of the generators and their inverses, as a list (in the order given by
`FinEnum α`). -/
def letters (α : Type*) [FinEnum α] : List (α × Bool) :=
  (FinEnum.toList α).flatMap fun a => [(a, true), (a, false)]

lemma mem_letters (x : α × Bool) : x ∈ letters α := by
  obtain ⟨a, b⟩ := x
  cases b <;> simp [letters]

/-- The first loop in the body of `Coincidence(i, j)`: replace `j` by `i` in all table entries;
and mark row `j` as merged. -/
def State.replace {n : ℕ} (s : State n α) (j i : Fin n) : State n α :=
  ⟨fun k x => CosetProject.replace j i (s.table k x), Function.update s.merged j true⟩

/-- The pairs `(C[i][g], C[j][g])`, `g ∈ X`, compared in the second loop of
`Coincidence(i, j)`. -/
def newPairs {n : ℕ} (C : Table (Fin n) α) (i j : Fin n) : List (Fin n × Fin n) :=
  (letters α).map fun x => (C i x, C j x)

/-- Apply the replacement `j ↦ i` to the pending pairs. -/
def replaceStack {n : ℕ} (j i : Fin n) (stack : List (Fin n × Fin n)) :
    List (Fin n × Fin n) :=
  stack.map (Prod.map (replace j i) (replace j i))

/-- The procedure `Coincidence` of Algorithm `algo:cosetproject`, with the recursion replaced by
an explicit stack of pending calls: `coincidence s [(i, j)]` runs `Coincidence(i, j)`.
See the module docstring for the correspondence. -/
def coincidence {n : ℕ} (s : State n α) : List (Fin n × Fin n) → State n α
  | [] => s
  | (a, b) :: rest =>
    if a = b then coincidence s rest
    else if _hj : s.merged (max a b) then coincidence s rest
    else
      let s' := s.replace (max a b) (min a b)
      coincidence s'
        (newPairs s'.table (min a b) (max a b) ++ replaceStack (max a b) (min a b) rest)
termination_by stack => (s.unmergedCount, stack.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (unmergedCount_lt s _ _ (by simpa using _hj))

/-- The body of the main loop for the coset `i`: trace every relator `w` from `i`; if this ends
in `j ≠ i`, call `Coincidence(i, j)`. Unlike the thesis, we check before *each* relator whether
row `i` has been merged in the meantime (see the module docstring). -/
def processRelators {n : ℕ} (i : Fin n) (s : State n α) : List (List (α × Bool)) → State n α
  | [] => s
  | w :: R =>
    if s.merged i then s
    else
      let j := s.table.trace w i
      processRelators i (if i ≠ j then coincidence s [(i, j)] else s) R

/-- **Algorithm `algo:cosetproject` (CosetProject).** Given the coset table `C` of a subgroup
`U ≤ FreeGroup α` (base row `0`) and relators `R`, compute the coset table of the image of `U`
in the quotient by `⟪R⟫`: it is the returned table, restricted to the rows that are not marked
as merged (`cosetProject_correct`). -/
def cosetProject {n : ℕ} (C : Table (Fin n) α) (R : List (List (α × Bool))) : State n α :=
  (List.finRange n).foldl (fun s i => processRelators i s R) ⟨C, fun _ => false⟩

/-! ### Correctness: the invariant -/

section Proof

variable {n : ℕ} (C₀ : Table (Fin n) α) (P : Fin n → Fin n → Prop)

/-- The relation generated by the kernel of `f` and the pending pairs: its equivalence closure is
the relation `≈` of the thesis. -/
def pend (f : Fin n → Fin n) (stack : List (Fin n × Fin n)) (u v : Fin n) : Prop :=
  f u = f v ∨ (u, v) ∈ stack

/-- The invariant of the algorithm, for the original table `C₀`, a relation `P` (`≡` of the
thesis), the current state `s`, the stack of pending coincidences, and the ghost function `f`
mapping each coset to its current representative (the composition of the replacements so far).
`table_eq` and `fP` together are the invariant `π(U_{C[k][g]}) = π(g · U_k)` of the thesis;
`stack_P` is Case 1 and Case 2 of the thesis; `cong` says that for any two cosets merged so far
the comparison of their rows is done or pending. -/
structure Inv (s : State n α) (stack : List (Fin n × Fin n)) (f : Fin n → Fin n) : Prop where
  idem : ∀ m, f (f m) = f m
  le : ∀ m, f m ≤ m
  merged_iff : ∀ m, s.merged m = false ↔ f m = m
  table_eq : ∀ k x, s.table k x = f (C₀ k x)
  fP : ∀ m, P (f m) m
  stack_fix : ∀ p ∈ stack, f p.1 = p.1 ∧ f p.2 = p.2
  stack_P : ∀ p ∈ stack, P p.1 p.2
  cong : ∀ a b x, f a = f b → EqvGen (pend f stack) (C₀ a x) (C₀ b x)

variable {C₀ P}

omit [FinEnum α] in
lemma eqvGen_of_le {β : Type*} {r p : β → β → Prop} (h : ∀ u v, r u v → EqvGen p u v)
    {a b : β} (hab : EqvGen r a b) : EqvGen p a b := by
  induction hab with
  | rel x y hxy => exact h x y hxy
  | refl x => exact .refl x
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

omit [FinEnum α] in
lemma eqvGen_pend_nil {f : Fin n → Fin n} {u v : Fin n} :
    EqvGen (pend f []) u v ↔ f u = f v := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => simpa [pend] using hxy
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    exact .rel _ _ (Or.inl h)

omit [FinEnum α] in
lemma replace_self {j i : Fin n} : replace j i j = i := by simp [replace]

omit [FinEnum α] in
lemma replace_of_ne {j i k : Fin n} (h : k ≠ j) : replace j i k = k := by simp [replace, h]

omit [FinEnum α] in
lemma replace_replace {j i k : Fin n} (hij : i ≠ j) :
    replace j i (replace j i k) = replace j i k := by
  by_cases hk : k = j
  · subst hk; rw [replace_self, replace_of_ne hij]
  · rw [replace_of_ne hk, replace_of_ne hk]

/-- One merge step of `Coincidence` preserves the invariant, and the relation `≈` grows. -/
lemma Inv.step (hP : Equivalence P) (hPC : ∀ a b x, P a b → P (C₀ a x) (C₀ b x))
    {s : State n α} {a b : Fin n} {rest : List (Fin n × Fin n)} {f : Fin n → Fin n}
    (h : Inv C₀ P s ((a, b) :: rest) f) {i j : Fin n} (hij : i < j)
    (hab : (a = i ∧ b = j) ∨ (a = j ∧ b = i)) :
    Inv C₀ P (s.replace j i) (newPairs (s.replace j i).table i j ++ replaceStack j i rest)
      (replace j i ∘ f) ∧
    ∀ u v, pend f ((a, b) :: rest) u v →
      EqvGen (pend (replace j i ∘ f) (newPairs (s.replace j i).table i j ++
        replaceStack j i rest)) u v := by
  have hne : i ≠ j := hij.ne
  have hfab := h.stack_fix (a, b) (by simp)
  have hPab := h.stack_P (a, b) (by simp)
  have hfi : f i = i := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  have hfj : f j = j := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  have hPij : P i j := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hPab
    · exact hP.symm hPab
  have hfix : ∀ u, f u = u → f (replace j i u) = replace j i u := by
    intro u hu
    by_cases huj : u = j
    · subst huj; rw [replace_self, hfi]
    · rw [replace_of_ne huj, hu]
  have hidem : ∀ m, (replace j i ∘ f) ((replace j i ∘ f) m) = (replace j i ∘ f) m := by
    intro m; simp only [Function.comp]; rw [hfix _ (h.idem m), replace_replace hne]
  have htab : ∀ k x, (s.replace j i).table k x = (replace j i ∘ f) (C₀ k x) := by
    intro k x; simp [State.replace, h.table_eq]
  have hPr : ∀ u, P (replace j i u) u := by
    intro u
    by_cases huj : u = j
    · subst huj; rw [replace_self]; exact hPij
    · rw [replace_of_ne huj]; exact hP.refl u
  have hrel : ∀ u, f u = u → (replace j i ∘ f) u = (replace j i ∘ f) (replace j i u) := by
    intro u hu
    simp only [Function.comp, hfix u hu, hu, replace_replace hne]
  set stack' := newPairs (s.replace j i).table i j ++ replaceStack j i rest with hstack'
  have hmono : ∀ u v, pend f ((a, b) :: rest) u v → EqvGen (pend (replace j i ∘ f) stack') u v := by
    rintro u v (huv | huv)
    · exact .rel _ _ (Or.inl (by simp [Function.comp, huv]))
    · rcases List.mem_cons.mp huv with huv | huv
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
        apply EqvGen.rel; left
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [Function.comp, hfi, hfj, replace_self, replace_of_ne hne]
      · have hfu := h.stack_fix (u, v) (by simp [huv])
        refine .trans _ _ _ (.rel _ _ (Or.inl (hrel u hfu.1))) (.trans _ _ _ ?_
          (.symm _ _ (.rel _ _ (Or.inl (hrel v hfu.2)))))
        apply EqvGen.rel; right
        rw [hstack', List.mem_append]; right
        exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
  refine ⟨⟨hidem, ?_, ?_, htab, ?_, ?_, ?_, ?_⟩, hmono⟩
  · -- le
    intro m
    simp only [Function.comp]
    refine le_trans ?_ (h.le m)
    by_cases hm : f m = j
    · rw [hm, replace_self]; exact hij.le
    · rw [replace_of_ne hm]
  · -- merged_iff
    intro m
    by_cases hmj : m = j
    · subst hmj
      simp only [State.replace, Function.update_self, Function.comp, hfj, replace_self]
      simp [hne]
    · simp only [State.replace, Function.update_of_ne hmj, Function.comp, h.merged_iff]
      constructor
      · intro hm; rw [hm, replace_of_ne hmj]
      · intro hm
        by_cases hfm : f m = j
        · rw [hfm, replace_self] at hm
          subst hm
          exact absurd (hfi.symm.trans hfm) hne
        · rwa [replace_of_ne hfm] at hm
  · -- fP
    intro m
    exact hP.trans (hPr (f m)) (h.fP m)
  · -- stack_fix
    intro p hp
    rw [hstack', List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp
      simp only [htab]
      exact ⟨hidem _, hidem _⟩
    · obtain ⟨⟨u, v⟩, huv, rfl⟩ := List.mem_map.mp hp
      have hfu := h.stack_fix (u, v) (by simp [huv])
      simp only [Prod.map, Function.comp]
      exact ⟨by rw [hfix u hfu.1, replace_replace hne], by rw [hfix v hfu.2, replace_replace hne]⟩
  · -- stack_P
    intro p hp
    rw [hstack', List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp
      simp only [htab, Function.comp]
      exact hP.trans (hPr _) (hP.trans (h.fP _) (hP.trans (hPC _ _ x hPij)
        (hP.symm (hP.trans (hPr _) (h.fP _)))))
    · obtain ⟨⟨u, v⟩, huv, rfl⟩ := List.mem_map.mp hp
      exact hP.trans (hPr u) (hP.trans (h.stack_P (u, v) (by simp [huv])) (hP.symm (hPr v)))
  · -- cong
    have key : ∀ x, EqvGen (pend (replace j i ∘ f) stack') (C₀ i x) (C₀ j x) := by
      intro x
      have hmem : ((s.replace j i).table i x, (s.replace j i).table j x) ∈ stack' := by
        rw [hstack', List.mem_append]; left
        exact List.mem_map.mpr ⟨x, mem_letters x, rfl⟩
      refine .trans _ _ _ (.rel _ _ (Or.inl ?_)) (.trans _ _ _ (.rel _ _ (Or.inr hmem))
        (.rel _ _ (Or.inl ?_)))
      · rw [htab, hidem]
      · rw [htab, hidem]
    intro a' b' x hab'
    by_cases hf : f a' = f b'
    · exact eqvGen_of_le hmono (h.cong a' b' x hf)
    · have hcase : (f a' = j ∧ f b' = i) ∨ (f a' = i ∧ f b' = j) := by
        simp only [Function.comp, replace] at hab'
        split_ifs at hab' <;> simp_all
      have hc1 : ∀ c, f c = i → EqvGen (pend (replace j i ∘ f) stack') (C₀ c x) (C₀ i x) :=
        fun c hc => eqvGen_of_le hmono (h.cong c i x (by rw [hc, hfi]))
      have hc2 : ∀ c, f c = j → EqvGen (pend (replace j i ∘ f) stack') (C₀ c x) (C₀ j x) :=
        fun c hc => eqvGen_of_le hmono (h.cong c j x (by rw [hc, hfj]))
      rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact .trans _ _ _ (hc2 a' ha) (.trans _ _ _ (.symm _ _ (key x)) (.symm _ _ (hc1 b' hb)))
      · exact .trans _ _ _ (hc1 a' ha) (.trans _ _ _ (key x) (.symm _ _ (hc2 b' hb)))

omit [FinEnum α] in
lemma Inv.unmerged_of_mem {s : State n α} {stack : List (Fin n × Fin n)} {f : Fin n → Fin n}
    (h : Inv C₀ P s stack f) {p : Fin n × Fin n} (hp : p ∈ stack) :
    s.merged p.1 = false ∧ s.merged p.2 = false :=
  ⟨(h.merged_iff _).mpr (h.stack_fix p hp).1, (h.merged_iff _).mpr (h.stack_fix p hp).2⟩

/-- `Coincidence` preserves the invariant, empties the stack, and identifies all pairs related
by `≈`. -/
theorem coincidence_spec (hP : Equivalence P) (hPC : ∀ a b x, P a b → P (C₀ a x) (C₀ b x))
    (s : State n α) (stack : List (Fin n × Fin n)) (f : Fin n → Fin n)
    (h : Inv C₀ P s stack f) :
    ∃ f', Inv C₀ P (coincidence s stack) [] f' ∧
      ∀ u v, EqvGen (pend f stack) u v → f' u = f' v := by
  induction s, stack using coincidence.induct generalizing f with
  | case1 s =>
    rw [coincidence]
    exact ⟨f, h, fun u v huv => eqvGen_pend_nil.mp huv⟩
  | case2 s b rest ih =>
    rw [coincidence]
    simp only [↓reduceIte]
    have hsub : ∀ u v, pend f ((b, b) :: rest) u v → EqvGen (pend f rest) u v := by
      rintro u v (huv | huv)
      · exact .rel _ _ (Or.inl huv)
      · rcases List.mem_cons.mp huv with huv | huv
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
          exact .refl _
        · exact .rel _ _ (Or.inr huv)
    have h' : Inv C₀ P s rest f :=
      { h with
        stack_fix := fun p hp => h.stack_fix p (List.mem_cons_of_mem _ hp)
        stack_P := fun p hp => h.stack_P p (List.mem_cons_of_mem _ hp)
        cong := fun a b x hab => eqvGen_of_le hsub (h.cong a b x hab) }
    obtain ⟨f', h1, h2⟩ := ih f h'
    exact ⟨f', h1, fun u v huv => h2 u v (eqvGen_of_le hsub huv)⟩
  | case3 s a b rest hab hj ih =>
    exfalso
    have := h.unmerged_of_mem (p := (a, b)) (by simp)
    rcases le_total a b with hle | hle
    · rw [max_eq_right hle] at hj; simp_all
    · rw [max_eq_left hle] at hj; simp_all
  | case4 s a b rest hab hj _ ih =>
    rw [coincidence]
    simp only [hab, ↓reduceIte, hj]
    have hab' : (a = min a b ∧ b = max a b) ∨ (a = max a b ∧ b = min a b) := by
      rcases le_total a b with hle | hle
      · left; simp [hle]
      · right; simp [hle]
    obtain ⟨h1, h2⟩ := h.step hP hPC (min_lt_max.mpr hab) hab'
    obtain ⟨f', h3, h4⟩ := ih _ h1
    exact ⟨f', h3, fun u v huv => h4 _ _ (eqvGen_of_le h2 huv)⟩

omit [FinEnum α] in
lemma Inv.ker_letter {s : State n α} {f : Fin n → Fin n} (h : Inv C₀ P s [] f) {a b : Fin n}
    (x : α × Bool) (hab : f a = f b) : f (C₀ a x) = f (C₀ b x) :=
  eqvGen_pend_nil.mp (h.cong a b x hab)

omit [FinEnum α] in
lemma Inv.ker_trace {s : State n α} {f : Fin n → Fin n} (h : Inv C₀ P s [] f) {a b : Fin n}
    (w : List (α × Bool)) (hab : f a = f b) : f (C₀.trace w a) = f (C₀.trace w b) := by
  induction w with
  | nil => exact hab
  | cons x w ih => exact h.ker_letter x ih

omit [FinEnum α] in
lemma Inv.trace_eq {s : State n α} {f : Fin n → Fin n} (h : Inv C₀ P s [] f)
    (w : List (α × Bool)) (k : Fin n) : f (s.table.trace w k) = f (C₀.trace w k) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [Table.trace_cons, h.table_eq, h.idem]
    exact h.ker_letter x ih

omit [FinEnum α] in
lemma Inv.trace_fix {s : State n α} {f : Fin n → Fin n} (h : Inv C₀ P s [] f)
    (w : List (α × Bool)) {k : Fin n} (hk : f k = k) :
    f (s.table.trace w k) = s.table.trace w k := by
  cases w with
  | nil => exact hk
  | cons x w => simp only [Table.trace_cons, h.table_eq, h.idem]

omit [FinEnum α] in
/-- If the kernel of `f` is contained in that of `f'`, every row fixed by `f'` (non-merged at the
later time) is fixed by `f` (non-merged at the earlier time). -/
lemma fix_of_ker {s s' : State n α} {f f' : Fin n → Fin n} (h : Inv C₀ P s [] f)
    (h' : Inv C₀ P s' [] f') (hker : ∀ u v, f u = f v → f' u = f' v) {i : Fin n}
    (hi : f' i = i) : f i = i := by
  have h1 : f' (f i) = i := by rw [hker _ _ (h.idem i), hi]
  have h2 := h'.le (f i)
  have h3 := h.le i
  rw [h1] at h2
  exact le_antisymm h3 h2

/-- The body of the main loop for row `i`: afterwards, if row `i` is not merged, every relator
traced from `i` (in the original table) ends in a coset with the same representative. -/
theorem processRelators_spec (hP : Equivalence P)
    (hPC : ∀ a b x, P a b → P (C₀ a x) (C₀ b x)) (i : Fin n) (R : List (List (α × Bool)))
    (hPR : ∀ r ∈ R, ∀ k, P (C₀.trace r k) k) (s : State n α) (f : Fin n → Fin n)
    (h : Inv C₀ P s [] f) :
    ∃ f', Inv C₀ P (processRelators i s R) [] f' ∧ (∀ u v, f u = f v → f' u = f' v) ∧
      (f' i = i → ∀ r ∈ R, f' (C₀.trace r i) = f' i) := by
  induction R generalizing s f with
  | nil => exact ⟨f, h, fun _ _ => id, by simp⟩
  | cons w R ih =>
    rw [processRelators]
    by_cases hm : s.merged i = true
    · simp only [hm, ↓reduceIte]
      refine ⟨f, h, fun _ _ => id, fun hi => ?_⟩
      have := (h.merged_iff i).mpr hi
      simp_all
    · simp only [hm, ↓reduceIte, Bool.false_eq_true]
      have hfi : f i = i := (h.merged_iff i).mp (by simpa using hm)
      set j := s.table.trace w i with hj
      have hfj : f j = j := h.trace_fix w hfi
      have hfjt : f j = f (C₀.trace w i) := h.trace_eq w i
      -- the state after tracing `w`, and the ghost function there
      obtain ⟨f₁, h₁, hker₁, hw₁⟩ : ∃ f₁, Inv C₀ P (if i ≠ j then coincidence s [(i, j)] else s)
          [] f₁ ∧ (∀ u v, f u = f v → f₁ u = f₁ v) ∧ f₁ (C₀.trace w i) = f₁ i := by
        by_cases hij : i = j
        · refine ⟨f, by simpa [← hij] using h, fun _ _ => id, ?_⟩
          rw [← hfjt, hfj, ← hij, hfi]
        · simp only [ne_eq, hij, not_false_eq_true, ↓reduceIte]
          have hPij : P i j := by
            have h1 : P j (C₀.trace w i) := by
              have := h.fP (C₀.trace w i)
              rwa [← hfjt, hfj] at this
            exact hP.symm (hP.trans h1 (hPR w (by simp) i))
          have hsub : ∀ u v, pend f [] u v → pend f [(i, j)] u v := by
            rintro u v (huv | huv)
            · exact Or.inl huv
            · simp at huv
          have h' : Inv C₀ P s [(i, j)] f :=
            { h with
              stack_fix := fun p hp => by
                simp only [List.mem_singleton] at hp; subst hp; exact ⟨hfi, hfj⟩
              stack_P := fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact hPij
              cong := fun a b x hab =>
                eqvGen_of_le (fun u v huv => .rel _ _ (hsub u v huv)) (h.cong a b x hab) }
          obtain ⟨f₁, h₁, h₂⟩ := coincidence_spec hP hPC s [(i, j)] f h'
          refine ⟨f₁, h₁, fun u v huv => h₂ u v (.rel _ _ (Or.inl huv)), ?_⟩
          rw [h₂ _ j (.rel _ _ (Or.inl (by rw [← hfjt, hfj])))]
          exact (h₂ i j (.rel _ _ (Or.inr (by simp)))).symm
      obtain ⟨f', h', hker', hR'⟩ := ih (fun r hr => hPR r (List.mem_cons_of_mem _ hr)) _ f₁ h₁
      refine ⟨f', h', fun u v huv => hker' u v (hker₁ u v huv), fun hi r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hker' _ _ hw₁
      · exact hR' hi r hr

/-- The main loop over a list of rows. -/
theorem foldl_spec (hP : Equivalence P)
    (hPC : ∀ a b x, P a b → P (C₀ a x) (C₀ b x)) (R : List (List (α × Bool)))
    (hPR : ∀ r ∈ R, ∀ k, P (C₀.trace r k) k) (L : List (Fin n)) (s : State n α)
    (f : Fin n → Fin n) (h : Inv C₀ P s [] f) :
    ∃ f', Inv C₀ P (L.foldl (fun s i => processRelators i s R) s) [] f' ∧
      (∀ u v, f u = f v → f' u = f' v) ∧
      ∀ i ∈ L, f' i = i → ∀ r ∈ R, f' (C₀.trace r i) = f' i := by
  induction L generalizing s f with
  | nil => exact ⟨f, h, fun _ _ => id, by simp⟩
  | cons i L ih =>
    obtain ⟨f₁, h₁, hker₁, hR₁⟩ := processRelators_spec hP hPC i R hPR s f h
    obtain ⟨f', h', hker', hR'⟩ := ih _ f₁ h₁
    refine ⟨f', h', fun u v huv => hker' u v (hker₁ u v huv), fun k hk hfk r hr => ?_⟩
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hker' _ _ (hR₁ (fix_of_ker h₁ h' hker' hfk) r hr)
    · exact hR' k hk hfk r hr

omit [FinEnum α] in
/-- The invariant holds at the start, with `f = id`. -/
lemma inv_init (hP : Equivalence P) : Inv C₀ P ⟨C₀, fun _ => false⟩ [] id where
  idem _ := rfl
  le _ := le_rfl
  merged_iff _ := by simp
  table_eq _ _ := rfl
  fP m := hP.refl m
  stack_fix := by simp
  stack_P := by simp
  cong a b x hab := by subst hab; exact .refl _

/-- The state at the end of the algorithm, for an abstract relation `P`. -/
theorem cosetProject_spec (hP : Equivalence P)
    (hPC : ∀ a b x, P a b → P (C₀ a x) (C₀ b x)) (R : List (List (α × Bool)))
    (hPR : ∀ r ∈ R, ∀ k, P (C₀.trace r k) k) :
    ∃ f, Inv C₀ P (cosetProject C₀ R) [] f ∧
      ∀ i, f i = i → ∀ r ∈ R, f (C₀.trace r i) = f i := by
  obtain ⟨f, h, -, hR⟩ := foldl_spec hP hPC R hPR (List.finRange n) _ _ (inv_init hP)
  exact ⟨f, h, fun i => hR i (List.mem_finRange i)⟩

end Proof

/-! ### Correctness: the main theorem -/

section Main

variable {n : ℕ}

omit [FinEnum α] in
/-- The relators, as a set of elements of the free group. -/
def relSet (R : List (List (α × Bool))) : Set (FreeGroup α) := {g | ∃ r ∈ R, FreeGroup.mk r = g}

omit [FinEnum α] in
/-- `a ≡ b` in the thesis: `π(U_a) = π(U_b)`, i.e. `b = w · a` for some `w ∈ N = ⟪R⟫`. -/
def projRel (ρ : FreeGroup α →* Perm Q) (N : Subgroup (FreeGroup α)) (a b : Q) : Prop :=
  ∃ g ∈ N, ρ g a = b

omit [FinEnum α] in
lemma projRel_equivalence (ρ : FreeGroup α →* Perm Q) (N : Subgroup (FreeGroup α)) :
    Equivalence (projRel ρ N) where
  refl a := ⟨1, N.one_mem, by simp⟩
  symm := by
    rintro a b ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, N.inv_mem hg, by simp [← Perm.mul_apply]⟩
  trans := by
    rintro a b c ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨g' * g, N.mul_mem hg' hg, by simp [Perm.mul_apply]⟩

/-- `g ∈ U ⊔ N` iff `h g ∈ U` for some `h ∈ N` (for normal `N`). -/
lemma mem_sup_normal_iff {G : Type*} [Group G] (U N : Subgroup G) [N.Normal] (g : G) :
    g ∈ U ⊔ N ↔ ∃ h ∈ N, h * g ∈ U := by
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul]
  constructor
  · rintro ⟨m, hm, u, hu, rfl⟩
    exact ⟨m⁻¹, N.inv_mem hm, by simpa [← mul_assoc] using hu⟩
  · rintro ⟨h, hh, hu⟩
    exact ⟨h⁻¹, N.inv_mem hh, h * g, hu, by simp [← mul_assoc]⟩

/-- **Correctness of CosetProject.** Let `C` be a coset table of `U ≤ FreeGroup α` with base row
`0` and `R` a list of relators. Then, in the output, row `0` is not merged, the non-merged rows
are closed under the table, and the table restricted to them is a coset table (bijective
generator columns, transitive) of `U ⊔ ⟪R⟫ = π⁻¹(π(U))`. -/
theorem cosetProject_correct [NeZero n] (C : Table (Fin n) α) (U : Subgroup (FreeGroup α))
    (hC : C.IsCosetTable 0 U) (R : List (List (α × Bool))) :
    ∃ (h0 : (cosetProject C R).merged 0 = false)
      (hcl : ∀ k x, (cosetProject C R).merged k = false →
        (cosetProject C R).merged ((cosetProject C R).table k x) = false),
      ((cosetProject C R).table.restrict (fun k => (cosetProject C R).merged k = false) hcl
        ).IsCosetTable ⟨0, h0⟩ (U ⊔ Subgroup.normalClosure (relSet R)) := by
  set ρ := C.toHom hC.isPerm with hρ
  set N := Subgroup.normalClosure (relSet R) with hN
  have hlet : ∀ k x, C k x = ρ (FreeGroup.mk [x]) k := fun k x => (C.toHom_letter _ x k).symm
  have hP := projRel_equivalence ρ N
  have hPC : ∀ a b x, projRel ρ N a b → projRel ρ N (C a x) (C b x) := by
    rintro a b x ⟨g, hg, rfl⟩
    refine ⟨FreeGroup.mk [x] * g * (FreeGroup.mk [x])⁻¹,
      Subgroup.normalClosure_normal.conj_mem _ hg _, ?_⟩
    simp [hlet, Perm.mul_apply, -FreeGroup.inv_mk]
  have hPR : ∀ r ∈ R, ∀ k, projRel ρ N (C.trace r k) k := by
    intro r hr k
    refine ⟨(FreeGroup.mk r)⁻¹, N.inv_mem (Subgroup.subset_normalClosure ⟨r, hr, rfl⟩), ?_⟩
    rw [← C.toHom_mk hC.isPerm, ← hρ, ← Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Perm.one_apply]
  obtain ⟨f, h, hR⟩ := cosetProject_spec hP hPC R hPR
  have hkerρ : ∀ g a b, f a = f b → f (ρ g a) = f (ρ g b) := by
    intro g a b hab
    rw [← FreeGroup.mk_toWord (x := g), hρ, C.toHom_mk, C.toHom_mk]
    exact h.ker_trace _ hab
  have hRall : ∀ r ∈ R, ∀ k, f (C.trace r k) = f k := by
    intro r hr k
    rw [h.ker_trace r (h.idem k).symm, hR (f k) (h.idem k) r hr, h.idem]
  let K : Subgroup (FreeGroup α) :=
    { carrier := {g | ∀ k, f (ρ g k) = f k}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb k
        simp only [Set.mem_ofPred_eq, map_mul, Perm.mul_apply] at ha hb ⊢
        rw [ha, hb]
      inv_mem' := by
        intro a ha k
        simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
        rw [← ha ((ρ a)⁻¹ k)]
        simp }
  have hK : K.Normal := ⟨fun g hg c k => by
    change f (ρ (c * g * c⁻¹) k) = f k
    simp only [map_mul, map_inv, Perm.mul_apply]
    rw [hkerρ c _ _ (hg ((ρ c)⁻¹ k))]
    simp⟩
  have hNK : N ≤ K := Subgroup.normalClosure_le_normal (by
    rintro _ ⟨r, hr, rfl⟩ k
    rw [hρ, C.toHom_mk]
    exact hRall r hr k)
  have hPf : ∀ a b, projRel ρ N a b ↔ f a = f b := by
    intro a b
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hNK hg a).symm
    · intro hab
      exact hP.trans (hP.symm (h.fP a)) (by rw [hab]; exact h.fP b)
  have h0 : f 0 = 0 := le_antisymm (h.le 0) (Fin.zero_le _)
  have hcl : ∀ k x, (cosetProject C R).merged k = false →
      (cosetProject C R).merged ((cosetProject C R).table k x) = false := by
    intro k x _
    rw [h.merged_iff, h.table_eq, h.idem]
  refine ⟨(h.merged_iff 0).mpr h0, hcl, ?_⟩
  set D := (cosetProject C R).table.restrict (fun k => (cosetProject C R).merged k = false) hcl
    with hD
  have hperm : D.IsPerm := by
    rintro ⟨k, hk⟩ a b
    apply Subtype.ext
    change (cosetProject C R).table ((cosetProject C R).table k (a, b)) (a, !b) = k
    rw [h.table_eq, h.table_eq, h.ker_letter (a, !b) (h.idem (C k (a, b))), hC.isPerm]
    exact (h.merged_iff k).mp hk
  have htrace : ∀ w k, (D.trace w k).val = f (C.trace w k.val) := by
    intro w k
    induction w with
    | nil => exact ((h.merged_iff _).mp k.2).symm
    | cons x w ih =>
      change (cosetProject C R).table (D.trace w k).val x = _
      rw [h.table_eq, ih, h.ker_letter x (h.idem _)]
      rfl
  have hhom : ∀ g k, (D.toHom hperm g k).val = f (ρ g k.val) := by
    intro g k
    rw [← FreeGroup.mk_toWord (x := g), D.toHom_mk, htrace, hρ, C.toHom_mk]
  refine ⟨hperm, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    obtain ⟨g, hg⟩ := hC.transitive k
    refine ⟨g, Subtype.ext ?_⟩
    rw [hhom]
    change f (ρ g 0) = k
    rw [hg]
    exact (h.merged_iff k).mp hk
  · ext g
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Perm.smul_def]
    rw [Subtype.ext_iff, hhom]
    change f (ρ g 0) = 0 ↔ _
    rw [mem_sup_normal_iff, ← h0, ← hPf]
    simp only [projRel, hC.mem_iff, map_mul, Perm.mul_apply, h0]
    rfl

omit [FinEnum α] in
/-- `U ⊔ ⟪R⟫` is the preimage of the image of `U` in the presented group `F/⟪R⟫`. -/
lemma sup_normalClosure_eq_comap (U : Subgroup (FreeGroup α)) (rels : Set (FreeGroup α)) :
    U ⊔ Subgroup.normalClosure rels =
      (U.map (PresentedGroup.mk rels)).comap (PresentedGroup.mk rels) := by
  rw [Subgroup.comap_map_eq]
  congr 1
  exact (QuotientGroup.ker_mk' _).symm

/-- **Correctness of CosetProject**, with the subgroup described as the preimage of the image
`π(U)` of `U` in Mathlib's `PresentedGroup`. -/
theorem cosetProject_correct' [NeZero n] (C : Table (Fin n) α) (U : Subgroup (FreeGroup α))
    (hC : C.IsCosetTable 0 U) (R : List (List (α × Bool))) :
    ∃ (h0 : (cosetProject C R).merged 0 = false)
      (hcl : ∀ k x, (cosetProject C R).merged k = false →
        (cosetProject C R).merged ((cosetProject C R).table k x) = false),
      ((cosetProject C R).table.restrict (fun k => (cosetProject C R).merged k = false) hcl
        ).IsCosetTable ⟨0, h0⟩
        ((U.map (PresentedGroup.mk (relSet R))).comap (PresentedGroup.mk (relSet R))) := by
  rw [← sup_normalClosure_eq_comap]
  exact cosetProject_correct C U hC R

end Main

end LoopSubgroups.CosetProject
