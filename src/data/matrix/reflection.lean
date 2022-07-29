/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.matrix.notation
import data.matrix.basic

/-!
# Lemmas for tuples `fin m → α` and concrete matrices `matrix (fin m) (fin n) α`

This file contains alternative definitions of common operators on vectors and matrices that expand
definitionally to the expected expression when evaluated on `![]` and `!![]` notation.

## Main definitionss

* `fin_vec.seq`
* `fin_vec.map`
* `fin_vec.map₂`
* `fin_vec.sum`
* `fin_vec.eta_expand`
* `matrix.transposeᵣ`
* `matrix.dot_productᵣ`
* `matrix.mulᵣ`
* `matrix.eta_expand`

## Main results

* `matrix.fin_eta`
* `matrix.mul_fin`

-/
namespace fin_vec
variables {m n : ℕ} {α β γ : Type*}

/-- Evaluate `fin_vec.seq f v = ![(f 0) (v 0), (f 1) (v 1), ...]` -/
def seq : Π {m}, (fin m → (α → β)) → (fin m → α) → fin m → β
| 0 f v := ![]
| (n + 1) f v := matrix.vec_cons (f 0 (v 0)) (seq (matrix.vec_tail f) (matrix.vec_tail v))

@[simp]
lemma seq_eq : Π {m} (f : fin m → (α → β)) (v : fin m → α),
  seq f v = (λ i, f i (v i))
| 0 f v := subsingleton.elim _ _
| (n + 1) f v := funext $ λ i, begin
  simp_rw [seq, seq_eq],
  refine i.cases _ (λ i, _),
  { refl },
  { simp only [matrix.cons_val_succ], refl },
end

example {f₁ f₂ : α → β} (a₁ a₂ : α) : seq ![f₁, f₂] ![a₁, a₂] = ![f₁ a₁, f₂ a₂] := rfl

/-- `fin_vec.map f v = ![f (v 0), f (v 1), ...]` -/
def map (f : α → β) {m} : (fin m → α) → fin m → β := seq (λ i, f)

@[simp]
lemma map_eq (f : α → β) {m} (v : fin m → α) : map f v = (f ∘ v) :=
seq_eq _ _

example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
(map_eq _ _).symm

/-- `map₂ f v w = ![f (v 0) (w 0), f (v 1) (w 1), ...]` -/
def map₂ (f : α → β → γ) (a : fin m → α) (b : fin m → β) : fin m → γ :=
seq (map f a) b

/-- Expand `v` to `![v 0, v 1, ...]` -/
def eta_expand {m} (v : fin m → α) : fin m → α := map id v

@[simp]
lemma eta_expand_eq {m} (v : fin m → α) : eta_expand v = v := map_eq id v

example {f : α → β} (a₁ a₂ : α) : eta_expand ![a₁, a₂] = ![a₁, a₂] := rfl
example {f : α → β} (a : fin 2 → α) : a = ![a 0, a 1] := (eta_expand_eq _).symm

/-- `∀` with better defeq for `∀ x : fin m → α, P x`. -/
def «forall» : Π {m} (P : (fin m → α) → Prop), Prop
| 0 P := P ![]
| (n + 1) P := ∀ x : α, «forall» (λ v, P (matrix.vec_cons x v))

lemma forall_iff : Π {m} (P : (fin m → α) → Prop), «forall» P ↔ ∀ x, P x
| 0 P := by simp only [«forall», fin.forall_fin_zero_pi, matrix.vec_empty]
| (n + 1) P := by simp only [«forall», forall_iff, fin.forall_fin_succ_pi, matrix.vec_cons]

example (P : (fin 2 → α) → Prop) : (∀ f, P f) ↔ (∀ a₀ a₁, P ![a₀, a₁]) := (forall_iff _).symm

/-- `∃` with better defeq for `∃ x : fin m → α, P x`. -/
def «exists» : Π {m} (P : (fin m → α) → Prop), Prop
| 0 P := P ![]
| (n + 1) P := ∃ x : α, «exists» (λ v, P (matrix.vec_cons x v))

lemma exists_iff : Π {m} (P : (fin m → α) → Prop), «exists» P ↔ ∃ x, P x
| 0 P := by simp only [«exists», fin.exists_fin_zero_pi, matrix.vec_empty]
| (n + 1) P := by simp only [«exists», exists_iff, fin.exists_fin_succ_pi, matrix.vec_cons]

example (P : (fin 2 → α) → Prop) : (∀ f, P f) ↔ (∀ a₀ a₁, P ![a₀, a₁]) := (forall_iff _).symm

/-- `finset.univ.sum` with better defeq for `fin` -/
def sum [has_add α] [has_zero α] : Π{m} (v : fin m → α), α
| 0 v := 0
| 1 v := v 0
| (n + 2) v := sum (v ∘ fin.cast_succ) + v (fin.last _)

open_locale big_operators

@[simp]
lemma sum_eq [add_comm_monoid α] : Π {m} (a : fin m → α),
  sum a = ∑ i, a i
| 0 a := rfl
| 1 a := (fintype.sum_unique a).symm
| (n + 2) a := by rw [fin.sum_univ_cast_succ, sum, sum_eq]

example [has_add α] [has_zero α] (a : fin 3 → α) : sum a = a 0 + a 1 + a 2 := rfl

end fin_vec

namespace matrix
variables {l m n : ℕ} {α β : Type*}

-- TODO[gh-6025]: make this an instance once safe to do so
def unique_of_empty_left {m n} [is_empty m] : unique (matrix m n α) :=
{ default := of is_empty_elim,
  uniq := λ a, matrix.ext is_empty_elim }

local attribute [instance] matrix.unique_of_empty_left

-- TODO[gh-6025]: make this an instance once safe to do so
def unique_of_empty_right {m n} [is_empty n] : unique (matrix m n α) :=
{ default := @of m n α (λ i, is_empty_elim),
  uniq := λ a, matrix.ext (λ i, is_empty_elim) }

/-- `∀` with better defeq for `∀ x : matrix (fin m) (fin n) α, P x`. -/
def «forall» : Π {m n} (P : (matrix (fin m) (fin n) α) → Prop), Prop
| 0 n P := P (of ![])
| (m + 1) n P := fin_vec.forall $ λ r, «forall» (λ A, P (of (matrix.vec_cons r A)))

lemma forall_iff : Π {m n} (P : (matrix (fin m) (fin n) α) → Prop), «forall» P ↔ ∀ x, P x
| 0 n P := by {simp only [«forall», unique.forall_iff], rw iff_iff_eq, congr}
| (m + 1) n P := begin
  simp only [«forall», fin_vec.forall_iff, forall_iff],
  exact iff.symm fin.forall_fin_succ_pi,
end

example (P : (matrix (fin 2) (fin 3) α) → Prop) :
  (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
(forall_iff _).symm

/--`∃` with better defeq for `∃ x : matrix (fin m) (fin n) α, P x`. -/
def «exists» : Π {m n} (P : (matrix (fin m) (fin n) α) → Prop), Prop
| 0 n P := P (of ![])
| (m + 1) n P := fin_vec.exists $ λ r, «exists» (λ A, P (of (matrix.vec_cons r A)))

lemma exists_iff : Π {m n} (P : (matrix (fin m) (fin n) α) → Prop), «exists» P ↔ ∃ x, P x
| 0 n P := by {simp only [«exists», unique.exists_iff], rw iff_iff_eq, congr}
| (m + 1) n P := begin
  simp only [«exists», fin_vec.exists_iff, exists_iff],
  exact iff.symm fin.exists_fin_succ_pi,
end

example (P : (matrix (fin 2) (fin 3) α) → Prop) :
  (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
(exists_iff _).symm

/-- `matrix.tranpose` with better defeq for `fin` -/
def transposeᵣ : Π {m n}, matrix (fin m) (fin n) α → matrix (fin n) (fin m) α
| _ 0 A := of ![]
| m (n + 1) A := of $ vec_cons (fin_vec.map (λ v : fin _ → α, v 0) A)
                               (transposeᵣ (A.minor id fin.succ))

@[simp]
lemma transposeᵣ_eq : Π {m n} (A : matrix (fin m) (fin n) α),
  transposeᵣ A = transpose A
| _ 0 A := subsingleton.elim _ _
| m (n + 1) A := matrix.ext $ λ i j, begin
  simp_rw [transposeᵣ, transposeᵣ_eq],
  refine i.cases _ (λ i, _),
  { dsimp, rw fin_vec.map_eq },
  { simp only [of_apply, matrix.cons_val_succ], refl },
end

example (a b c d : α) : transposeᵣ !![a, b; c, d] = !![a, c; b, d] := rfl

/-- `matrix.dot_product` with better defeq for `fin` -/
def dot_productᵣ [has_mul α] [has_add α] [has_zero α] {m} (a b : fin m → α) : α :=
fin_vec.sum $ fin_vec.map₂ (*) a b

@[simp]
lemma dot_productᵣ_eq [has_mul α] [add_comm_monoid α] {m} (a b : fin m → α) :
  dot_productᵣ a b = dot_product a b :=
by simp_rw [dot_productᵣ, dot_product, fin_vec.sum_eq, fin_vec.map₂, fin_vec.seq_eq, fin_vec.map_eq]

/-- `matrix.mul` with better defeq for `fin` -/
def mulᵣ [has_mul α] [has_add α] [has_zero α]
  (A : matrix (fin l) (fin m) α) (B : matrix (fin m) (fin n) α) :
  matrix (fin l) (fin n) α :=
of $ fin_vec.map (λ v₁, fin_vec.map (λ v₂, dot_productᵣ v₁ v₂) (transposeᵣ B)) A

@[simp]
lemma mulᵣ_eq [has_mul α] [add_comm_monoid α]
  (A : matrix (fin l) (fin m) α) (B : matrix (fin m) (fin n) α) :
  mulᵣ A B = A.mul B :=
begin
  simp [mulᵣ, function.comp, matrix.mul, matrix.transpose],
  refl,
end

example [add_comm_monoid α] [has_mul α]
  (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
  mulᵣ !![a₁₁, a₁₂, a₁₃;
          a₂₁, a₂₂, a₂₃;
          a₃₁, a₃₂, a₃₃] !![b₁₁, b₁₂, b₁₃;
                              b₂₁, b₂₂, b₂₃;
                              b₃₁, b₃₂, b₃₃] =
  !![a₁₁*b₁₁ + a₁₂*b₂₁ + a₁₃*b₃₁, a₁₁*b₁₂ + a₁₂*b₂₂ + a₁₃*b₃₂, a₁₁*b₁₃ + a₁₂*b₂₃ + a₁₃*b₃₃;
     a₂₁*b₁₁ + a₂₂*b₂₁ + a₂₃*b₃₁, a₂₁*b₁₂ + a₂₂*b₂₂ + a₂₃*b₃₂, a₂₁*b₁₃ + a₂₂*b₂₃ + a₂₃*b₃₃;
     a₃₁*b₁₁ + a₃₂*b₂₁ + a₃₃*b₃₁, a₃₁*b₁₂ + a₃₂*b₂₂ + a₃₃*b₃₂, a₃₁*b₁₃ + a₃₂*b₂₃ + a₃₃*b₃₃] :=
rfl

example (a b c d : α) : transposeᵣ !![a, b; c, d] = !![a, c; b, d] := rfl

/-- Expand `A` to `!![A 0 0, ...; ..., A m n]` -/
def eta_expand {m n} (A : matrix (fin m) (fin n) α) : matrix (fin m) (fin n) α :=
matrix.of (fin_vec.eta_expand (λ i, fin_vec.eta_expand (λ j, A i j)))

lemma eta_expand_eq {m n} (A : matrix (fin m) (fin n) α) :
  eta_expand A = A :=
by simp_rw [eta_expand, fin_vec.eta_expand_eq, matrix.of, equiv.refl_apply]

end matrix

/-! ### Helpers to invoke functions involving algebra at tactic time

It's not clear whether using `instance_cache` is a sensible choice here.
In particular, we need to use these tactics below when the algebraic instances are local variables
that aren't in the "real" instance cache (the one used by `tactic.reset_instance_cache`).
-/
namespace expr

/-- Produce a `has_one` instance for the type cached by `t`, such that `1 : expr` is the one of that
type. -/
meta def has_one (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × has_one expr) :=
do
  (t, one) ← t.mk_app `has_one.one [],
  pure (t, { one := one })

/-- Produce a `has_zero` instance for the type cached by `t`, such that `0 : expr` is the zero of
that type. -/
meta def has_zero (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × has_zero expr) :=
do
  (t, zero) ← t.mk_app `has_zero.zero [],
  pure (t, { zero := zero })

/-- Produce a `has_mul` instance for the type cached by `t`, such that `(*) : expr → expr → expr` is
the multiplication of that type. -/
meta def has_mul (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × has_mul expr) :=
do
  (t, mul) ← t.mk_app `has_mul.mul [],
  pure (t, { mul := λ a b, mul a b })

/-- Produce a `has_add` instance for the type cached by `t`, such that `(+) : expr → expr → expr` is
the addition of that type. -/
meta def has_add (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × has_add expr) :=
do
  (t, add) ← t.mk_app `has_add.add [],
  pure (t, { add := λ a b, add a b })

/-- Produce a `add_comm_monoid` instance for the type cached by `t`, such that the addition and
zero match `expr.has_add` and `expr.has_zero`. -/
meta def add_comm_monoid (t : tactic.instance_cache) :
  tactic (tactic.instance_cache × add_comm_monoid expr) :=
do
  (t, add) ← t.mk_app `has_add.add [],
  (t, zero) ← t.mk_app `has_zero.zero [],
  has_smul ← tactic.mk_app `has_smul [`(ℕ), t.α] >>= tactic.mk_instance,
  nsmul ← tactic.mk_mapp `has_smul.smul [none, some t.α, some has_smul],
  pure (t,
  { add := λ a b, add a b,
    zero := zero,
    add_assoc := false.elim (unchecked_cast trivial),
    zero_add := false.elim (unchecked_cast trivial),
    add_zero := false.elim (unchecked_cast trivial),
    nsmul := λ n b, nsmul `(n) b,
    nsmul_zero' := false.elim (unchecked_cast trivial),
    nsmul_succ' := false.elim (unchecked_cast trivial),
    add_comm := false.elim (unchecked_cast trivial) })

end expr

/-- Like `list.mmap` but for a vector. -/
def fin.mmap {α} {n : ℕ} {m : Type* → Type*} [monad m] (f : fin n → m α) : m (fin n → α) :=
vector.nth <$> vector.mmap f ⟨list.fin_range n, list.length_fin_range _⟩

/-! ### Lemmas with `auto_param`s

TODO: how can we eliminate all this boilerplate?
-/

namespace matrix

section fin_eta

/-- Prove a statement of the form `∀ A : matrix m n α, A = !![A 0 0, ...]`.
Returns the type of this statement and its proof. -/
meta def fin_eta.prove (m n : ℕ) : tactic (expr × expr) :=
do
  u ← tactic.mk_meta_univ,
  α ← tactic.mk_local' `α binder_info.implicit (expr.sort u.succ),
  A ← tactic.mk_local' `A binder_info.default
    (expr.const `matrix [level.zero, level.zero, u] `(fin %%`(m)) `(fin %%`(n)) α),
  let entries := λ (i : fin m) (j : fin n), A `(i) `(j),
  let entry_vals := pi_fin.to_pexpr (λ i, pi_fin.to_pexpr (λ j, to_pexpr $ entries i j)),
  let A_eta := (``(@matrix.of (fin %%`(m)) (fin %%`(n)) _).app entry_vals),
  A_eq ← tactic.to_expr ``(%%A = %%A_eta),
  t ← tactic.pis [α, A] A_eq,
  ((), pr) ← tactic.solve_aux t `[intros α A, exact (matrix.eta_expand_eq A).symm],
  pure (t, pr)

/-- Helper tactic used as an `auto_param` for `matrix.fin_eta` -/
meta def fin_eta.derive : tactic unit :=
do
  target@`(%%A' = %%A_eta) ← tactic.target,
  (expr.const `matrix ls, [`(fin %%m), `(fin %%n), α])
    ← expr.get_app_fn_args <$> tactic.infer_type A',
  some (m, n) ← pure (prod.mk <$> m.to_nat <*> n.to_nat) |
    fail!"Dimensions {m} {n} are not numerals",
  (t,pr) ← matrix.fin_eta.prove m n,

  tactic.unify target (t.instantiate_pis [α, A']),
  tactic.exact (pr α A')

theorem fin_eta {α} {m n : ℕ}
  (A : matrix (fin m) (fin n) α) {«![A 0 0, ...]» : matrix (fin m) (fin n) α}
  (h : A = «![A 0 0, ...]» . matrix.fin_eta.derive) : A = «![A 0 0, ...]» := h

example : true :=
begin
  let B : matrix (fin 20) (fin 20) ℕ := 0,
  have := matrix.fin_eta B,  -- 400 coefficients, but very fast
  have : B = B, by rw this,
  trivial,
end

end fin_eta

section mul_fin

/-- Choose a name suffix for a matrix index -/
private def name_suffix {m n : ℕ} : fin m → fin n → string :=
let chars := "₀₁₂₃₄₅₆₇₈₉".data in
if h : m ≤ 10 ∧ n ≤ 10
then (λ i j, ["₀₁₂₃₄₅₆₇₈₉".data.nth_le i (i.prop.trans_le h.1),
              "₀₁₂₃₄₅₆₇₈₉".data.nth_le j (j.prop.trans_le h.2)].as_string)
else (λ i j, "_" ++ to_string i ++ "_" ++ to_string j)

/-- `pi_fin.to_pexpr` but for matrices -/
meta def fin_to_pexpr {m n : ℕ} (A : matrix (fin m) (fin n) pexpr) : pexpr :=
``(@matrix.of (fin %%`(m)) (fin %%`(n)) _).app $
  pi_fin.to_pexpr (λ i : fin m, pi_fin.to_pexpr (λ j : fin n, A i j))

/-- This statement is defeq to `mul_fin`, but syntactically worse-/
theorem mul_fin_aux (l m n : ℕ) ⦃α⦄ [has_mul α] [add_comm_monoid α] :
  «forall» $ λ A : matrix (fin l) (fin m) α,
    «forall» $ λ B : matrix (fin m) (fin n) α,
      A.mul B = A.mulᵣ B :=
by simp_rw [forall_iff, mulᵣ_eq, eq_self_iff_true, forall_const]

/-- Prove a statement of the form
```
∀ α [has_mul α] [add_comm_monoid α] (a₁₁ ... aₗₘ b₁₁ ... bₘₙ : α),
   !![a₁₁ ⋱ aₗₘ] ⬝ !![b₁₁ ⋱ bₘₙ] = ![⋱]
```
Returns the type of this statement and its proof. -/
meta def mul_fin.prove (l m n : ℕ) : tactic (expr × expr) :=
do
  -- create all the binders, one for each coefficient
  u ← tactic.mk_meta_univ,
  α ← tactic.mk_local' `α binder_info.implicit (expr.sort u.succ),
  has_mul_α ← tactic.mk_app `has_mul [α] >>= tactic.mk_local' `_inst_1 binder_info.inst_implicit,
  add_comm_monoid_α ←
    tactic.mk_app `add_comm_monoid [α] >>= tactic.mk_local' `_inst_2 binder_info.inst_implicit,
  a ← (fin.mmap $ λ i : fin l, fin.mmap $ λ j : fin m,
      tactic.mk_local' ((`a).append_suffix (name_suffix i j)) binder_info.default α),
  b ← (fin.mmap $ λ i : fin m, fin.mmap $ λ j : fin n,
      tactic.mk_local' ((`b).append_suffix (name_suffix i j)) binder_info.default α),
  let a_flat := (list.fin_range l).bind (λ i, (list.fin_range m).map $ λ j, a i j),
  let b_flat := (list.fin_range m).bind (λ i, (list.fin_range n).map $ λ j, b i j),
  let args := [α, has_mul_α, add_comm_monoid_α] ++ a_flat ++ b_flat,

  -- build the matrices out of the coefficients
  let A := matrix.fin_to_pexpr (matrix.map a to_pexpr),
  let B := matrix.fin_to_pexpr (matrix.map b to_pexpr),
  -- get an instance cache holding all the instances needed for matrix multiplication. There must
  -- be a better way to do this.
  t ← tactic.mk_instance_cache α,
  has_add_α ← tactic.mk_app `has_add [α] >>= (λ t, prod.snd <$> @tactic.solve_aux unit t (do
  { tmp2 ← tactic.pose `_inst_2' none add_comm_monoid_α,
    tactic.reset_instance_cache,
    `[apply_instance] })),
  has_zero_α ← tactic.mk_app `has_zero [α] >>= (λ t, prod.snd <$> @tactic.solve_aux unit t (do
  { tmp2 ← tactic.pose `_inst_2' none add_comm_monoid_α,
    tactic.reset_instance_cache,
    `[apply_instance] })),
  let t := {inst := [
    (`has_mul, has_mul_α),
    (`has_add, has_add_α),
    (`has_zero, has_zero_α),
    (`add_comm_monoid, add_comm_monoid_α)].foldl (λ n x, n.insert x.1 x.2) t.inst,
     ..t},

  -- clever trick: create algebraic instances on `expr` so that we can use `matrix.mul` or
  -- `matrix.mulᵣ` to build the expression we want to end up with. It doesn't matter which we pick,
  -- but the typeclasses are easier to create for the latter.
  (t, has_mul_αe) ← expr.has_mul t,
  (t, has_add_αe) ← expr.has_add t,
  (t, has_zero_αe) ← expr.has_zero t,
  let ab := @matrix.mulᵣ _ _ _ _ has_mul_αe has_add_αe has_zero_αe a b,
  let AB := matrix.fin_to_pexpr (matrix.map ab to_pexpr),

  -- State and prove the equality, noting the RHS is defeq to `mulᵣ A B`.
  A_eq ← tactic.to_expr ``(@matrix.mul _ _ _ _ _ %%has_mul_α %%add_comm_monoid_α %%A %%B = %%AB),
  t ← tactic.pis args A_eq,
  let pr := (expr.const `matrix.mul_fin_aux [u]).mk_app [`(l), `(m), `(n)],
  -- This seems to create a metavariable then assign it, which ensures `pr` carries the right type.
  ((), pr) ← tactic.solve_aux t $ tactic.exact pr,

  pure (t, pr)

open_locale matrix


/-- Helper tactic used as an `auto_param` for `matrix.mul_fin` -/
meta def mul_fin.derive : tactic unit :=
do
  target@`(@matrix.mul (fin %%l) (fin %%m) (fin %%n) %%α %%_ %%i1 %%i2 %%A %%B = %%AB)
    ← tactic.target,
  some (l, m, n) ← pure (prod.mk <$> l.to_nat <*> (prod.mk <$> m.to_nat <*> n.to_nat)) |
    fail!"Dimensions {l}, {m} {n} are not numerals",
  (t,pr) ← mul_fin.prove l m n,
  tactic.apply (pr α i1 i2) {},
  tactic.done
  -- TODO: should we be extracting the coefficients manually so we can do a full invocation as
  -- something like:
  --   tactic.unify target (t.instantiate_pis [α, A']),
  --   tactic.exact (pr α A')


theorem mul_fin {α} [has_mul α] [add_comm_monoid α] {l m n : ℕ}
  {«![a₁₁ ⋱ aₗₘ]» : fin l → fin m → α}
  {«![b₁₁ ⋱ bₘₙ]» : fin m → fin n → α}
  {«![ab₁₁ ⋱ abₗₙ]» : fin l → fin n → α}
  (h : of «![a₁₁ ⋱ aₗₘ]» ⬝ of «![b₁₁ ⋱ bₘₙ]» = of «![ab₁₁ ⋱ abₗₙ]» . mul_fin.derive) :
    of «![a₁₁ ⋱ aₗₘ]» ⬝ of «![b₁₁ ⋱ bₘₙ]» = of «![ab₁₁ ⋱ abₗₙ]» := h

example {α} [add_comm_monoid α] [has_mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] ⬝ !![b₁₁, b₁₂;
                    b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                   a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
begin
  rw mul_fin,
end

example {α} [add_comm_monoid α] [has_mul α] (a₁₁ a₁₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂] ⬝ !![b₁₁, b₁₂;
                    b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;] :=
begin
  -- if we really need it, we can get the proof directly like this
  mul_fin.prove 1 2 2 >>= function.uncurry (tactic.assertv `h),
  specialize @h α _ _,

  rw mul_fin
end

end mul_fin

end matrix
