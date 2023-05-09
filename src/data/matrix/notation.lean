/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
import data.matrix.basic
import data.fin.vec_notation
import tactic.fin_cases
import algebra.big_operators.fin

/-!
# Matrix and vector notation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file includes `simp` lemmas for applying operations in `data.matrix.basic` to values built out
of the matrix notation `![a, b] = vec_cons a (vec_cons b vec_empty)` defined in
`data.fin.vec_notation`.

This also provides the new notation `!![a, b; c, d] = matrix.of ![![a, b], ![c, d]]`.
This notation also works for empty matrices; `!![,,,] : matrix (fin 0) (fin 3)` and
`!![;;;] : matrix (fin 3) (fin 0)`.

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

This file provide notation `!![a, b; c, d]` for matrices, which corresponds to
`matrix.of ![![a, b], ![c, d]]`.
A parser for `a, b; c, d`-style strings is provided as `matrix.entry_parser`, while
`matrix.notation` provides the hook for the `!!` notation.
Note that in lean 3 the pretty-printer will not show `!!` notation, instead showing the version
with `of ![![...]]`.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/

namespace matrix

universe u
variables {α : Type u} {o n m : ℕ} {m' n' o' : Type*}

open_locale matrix

/-- Matrices can be reflected whenever their entries can. We insert an `@id (matrix m' n' α)` to
prevent immediate decay to a function. -/
meta instance matrix.reflect [reflected_univ.{u}] [reflected_univ.{u_1}] [reflected_univ.{u_2}]
  [reflected _ α] [reflected _ m'] [reflected _ n']
  [h : has_reflect (m' → n' → α)] : has_reflect (matrix m' n' α) :=
λ m, (by reflect_name : reflected _ @id.{(max u_1 u_2 u) + 1}).subst₂
  ((by reflect_name : reflected _ @matrix.{u_1 u_2 u}).subst₃ `(_) `(_) `(_)) $
  by { dunfold matrix, exact h m }

section parser
open lean
open lean.parser
open interactive
open interactive.types

/-- Parse the entries of a matrix -/
meta def entry_parser {α : Type} (p : parser α) :
  parser (Σ m n, fin m → fin n → α) :=
do
  -- a list of lists if the matrix has at least one row, or the number of columns if the matrix has
  -- zero rows.
  let p : parser (list (list α) ⊕ ℕ) :=
    (sum.inl <$> (
      (pure [] <* tk ";").repeat_at_least 1 <|> -- empty rows
      (sep_by_trailing (tk ";") $ sep_by_trailing (tk ",") p)) <|>
    (sum.inr <$> list.length <$> many (tk ","))), -- empty columns
  which ← p,
  match which with
  | (sum.inl l) := do
    h :: tl ← pure l,
    let n := h.length,
    l : list (vector α n) ← l.mmap (λ row,
      if h : row.length = n then
        pure (⟨row, h⟩ : vector α n)
      else
        interaction_monad.fail "Rows must be of equal length"),
    pure ⟨l.length, n, λ i j, (l.nth_le _ i.prop).nth j⟩
  | (sum.inr n) :=
    pure ⟨0, n, fin_zero_elim⟩
  end

-- Lean can't find this instance without some help. We only need it available in `Type 0`, and it is
-- a massive amount of effort to make it universe-polymorphic.
@[instance] meta def sigma_sigma_fin_matrix_has_reflect {α : Type}
  [has_reflect α] [reflected _ α] :
  has_reflect (Σ (m n : ℕ), fin m → fin n → α) :=
@sigma.reflect.{0 0} _ _ ℕ (λ m, Σ n, fin m → fin n → α) _ _ _ $ λ i,
  @sigma.reflect.{0 0} _ _ ℕ _ _ _ _ (λ j, infer_instance)

/-- `!![a, b; c, d]` notation for matrices indexed by `fin m` and `fin n`. See the module docstring
for details. -/
@[user_notation]
meta def «notation» (_ : parse $ tk "!![")
  (val : parse (entry_parser (parser.pexpr 1) <* tk "]")) : parser pexpr :=
do
  let ⟨m, n, entries⟩ := val,
  let entry_vals := pi_fin.to_pexpr (pi_fin.to_pexpr ∘ entries),
  pure (``(@matrix.of (fin %%`(m)) (fin %%`(n)) _).app entry_vals)

end parser

variables (a b : ℕ)

/-- Use `![...]` notation for displaying a `fin`-indexed matrix, for example:

```
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
```
-/
instance [has_repr α] : has_repr (matrix (fin m) (fin n) α) :=
{ repr := λ f,
  "!![" ++ (string.intercalate "; " $ (list.fin_range m).map $ λ i,
    string.intercalate ", " $ (list.fin_range n).map (λ j, repr (f i j)))  ++ "]" }

@[simp] lemma cons_val' (v : n' → α) (B : fin m → n' → α) (i j) :
  vec_cons v B i j = vec_cons (v j) (λ i, B i j) i :=
by { refine fin.cases _ _ i; simp }

@[simp] lemma head_val' (B : fin m.succ → n' → α) (j : n') :
  vec_head (λ i, B i j) = vec_head B j := rfl

@[simp] lemma tail_val' (B : fin m.succ → n' → α) (j : n') :
  vec_tail (λ i, B i j) = λ i, vec_tail B i j :=
by { ext, simp [vec_tail] }

section dot_product

variables [add_comm_monoid α] [has_mul α]

@[simp] lemma dot_product_empty (v w : fin 0 → α) :
  dot_product v w = 0 := finset.sum_empty

@[simp] lemma cons_dot_product (x : α) (v : fin n → α) (w : fin n.succ → α) :
  dot_product (vec_cons x v) w = x * vec_head w + dot_product v (vec_tail w) :=
by simp [dot_product, fin.sum_univ_succ, vec_head, vec_tail]

@[simp] lemma dot_product_cons (v : fin n.succ → α) (x : α) (w : fin n → α) :
  dot_product v (vec_cons x w) = vec_head v * x + dot_product (vec_tail v) w :=
by simp [dot_product, fin.sum_univ_succ, vec_head, vec_tail]

@[simp] lemma cons_dot_product_cons (x : α) (v : fin n → α) (y : α) (w : fin n → α) :
  dot_product (vec_cons x v) (vec_cons y w) = x * y + dot_product v w :=
by simp

end dot_product

section col_row

@[simp] lemma col_empty (v : fin 0 → α) : col v = vec_empty :=
empty_eq _

@[simp] lemma col_cons (x : α) (u : fin m → α) :
  col (vec_cons x u) = vec_cons (λ _, x) (col u) :=
by { ext i j, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

@[simp] lemma row_empty : row (vec_empty : fin 0 → α) = λ _, vec_empty :=
by { ext, refl }

@[simp] lemma row_cons (x : α) (u : fin m → α) :
  row (vec_cons x u) = λ _, vec_cons x u :=
by { ext, refl }

end col_row

section transpose

@[simp] lemma transpose_empty_rows (A : matrix m' (fin 0) α) : Aᵀ = of ![] := empty_eq _

@[simp] lemma transpose_empty_cols (A : matrix (fin 0) m' α) : Aᵀ = of (λ i, ![]) :=
funext (λ i, empty_eq _)

@[simp] lemma cons_transpose (v : n' → α) (A : matrix (fin m) n' α) :
  (of (vec_cons v A))ᵀ = of (λ i, vec_cons (v i) (Aᵀ i)) :=
by { ext i j, refine fin.cases _ _ j; simp }

@[simp] lemma head_transpose (A : matrix m' (fin n.succ) α) :
  vec_head (of.symm Aᵀ) = vec_head ∘ (of.symm A) :=
rfl

@[simp] lemma tail_transpose (A : matrix m' (fin n.succ) α) :
  vec_tail (of.symm Aᵀ) = (vec_tail ∘ A)ᵀ :=
by { ext i j, refl }

end transpose

section mul

variables [semiring α]

@[simp] lemma empty_mul [fintype n'] (A : matrix (fin 0) n' α) (B : matrix n' o' α) :
  A ⬝ B = of ![] :=
empty_eq _

@[simp] lemma empty_mul_empty (A : matrix m' (fin 0) α) (B : matrix (fin 0) o' α) :
  A ⬝ B = 0 :=
rfl

@[simp] lemma mul_empty [fintype n'] (A : matrix m' n' α) (B : matrix n' (fin 0) α) :
  A ⬝ B = of (λ _, ![]) :=
funext (λ _, empty_eq _)

lemma mul_val_succ [fintype n']
  (A : matrix (fin m.succ) n' α) (B : matrix n' o' α) (i : fin m) (j : o') :
  (A ⬝ B) i.succ j = (of (vec_tail (of.symm A)) ⬝ B) i j := rfl

@[simp] lemma cons_mul [fintype n'] (v : n' → α) (A : fin m → n' → α) (B : matrix n' o' α) :
  of (vec_cons v A) ⬝ B = of (vec_cons (vec_mul v B) (of.symm (of A ⬝ B))) :=
by { ext i j, refine fin.cases _ _ i, { refl },  simp [mul_val_succ], }

end mul

section vec_mul

variables [semiring α]

@[simp] lemma empty_vec_mul (v : fin 0 → α) (B : matrix (fin 0) o' α) :
  vec_mul v B = 0 :=
rfl

@[simp] lemma vec_mul_empty [fintype n'] (v : n' → α) (B : matrix n' (fin 0) α) :
  vec_mul v B = ![] :=
empty_eq _

@[simp] lemma cons_vec_mul (x : α) (v : fin n → α) (B : fin n.succ → o' → α) :
  vec_mul (vec_cons x v) (of B) = x • (vec_head B) + vec_mul v (of $ vec_tail B) :=
by { ext i, simp [vec_mul] }

@[simp] lemma vec_mul_cons (v : fin n.succ → α) (w : o' → α) (B : fin n → o' → α) :
  vec_mul v (of $ vec_cons w B) = vec_head v • w + vec_mul (vec_tail v) (of B) :=
by { ext i, simp [vec_mul] }

@[simp] lemma cons_vec_mul_cons (x : α) (v : fin n → α) (w : o' → α) (B : fin n → o' → α) :
  vec_mul (vec_cons x v) (of $ vec_cons w B) = x • w + vec_mul v (of B) :=
by simp

end vec_mul

section mul_vec

variables [semiring α]

@[simp] lemma empty_mul_vec [fintype n'] (A : matrix (fin 0) n' α) (v : n' → α) :
  mul_vec A v = ![] :=
empty_eq _

@[simp] lemma mul_vec_empty (A : matrix m' (fin 0) α) (v : fin 0 → α) :
  mul_vec A v = 0 :=
rfl

@[simp] lemma cons_mul_vec [fintype n'] (v : n' → α) (A : fin m → n' → α) (w : n' → α) :
  mul_vec (of $ vec_cons v A) w = vec_cons (dot_product v w) (mul_vec (of A) w) :=
by { ext i, refine fin.cases _ _ i; simp [mul_vec] }

@[simp] lemma mul_vec_cons {α} [comm_semiring α] (A : m' → (fin n.succ) → α) (x : α)
  (v : fin n → α) :
  mul_vec (of A) (vec_cons x v) = (x • vec_head ∘ A) + mul_vec (of (vec_tail ∘ A)) v :=
by { ext i, simp [mul_vec, mul_comm] }

end mul_vec

section vec_mul_vec

variables [semiring α]

@[simp] lemma empty_vec_mul_vec (v : fin 0 → α) (w : n' → α) :
  vec_mul_vec v w = ![] :=
empty_eq _

@[simp] lemma vec_mul_vec_empty (v : m' → α) (w : fin 0 → α) :
  vec_mul_vec v w = λ _, ![] :=
funext (λ i, empty_eq _)

@[simp] lemma cons_vec_mul_vec (x : α) (v : fin m → α) (w : n' → α) :
  vec_mul_vec (vec_cons x v) w = vec_cons (x • w) (vec_mul_vec v w) :=
by { ext i, refine fin.cases _ _ i; simp [vec_mul_vec] }

@[simp] lemma vec_mul_vec_cons (v : m' → α) (x : α) (w : fin n → α) :
  vec_mul_vec v (vec_cons x w) = λ i, v i • vec_cons x w :=
by { ext i j, rw [vec_mul_vec_apply, pi.smul_apply, smul_eq_mul] }

end vec_mul_vec

section smul

variables [semiring α]

@[simp] lemma smul_mat_empty {m' : Type*} (x : α) (A : fin 0 → m' → α) : x • A = ![] := empty_eq _

@[simp] lemma smul_mat_cons (x : α) (v : n' → α) (A : fin m → n' → α) :
  x • vec_cons v A = vec_cons (x • v) (x • A) :=
by { ext i, refine fin.cases _ _ i; simp }

end smul

section submatrix

@[simp] lemma submatrix_empty (A : matrix m' n' α) (row : fin 0 → m') (col : o' → n') :
  submatrix A row col = ![] :=
empty_eq _

@[simp] lemma submatrix_cons_row (A : matrix m' n' α) (i : m') (row : fin m → m') (col : o' → n') :
  submatrix A (vec_cons i row) col = vec_cons (λ j, A i (col j)) (submatrix A row col) :=
by { ext i j, refine fin.cases _ _ i; simp [submatrix] }

end submatrix

section vec2_and_vec3

section one

variables [has_zero α] [has_one α]

lemma one_fin_two : (1 : matrix (fin 2) (fin 2) α) = !![1, 0; 0, 1] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma one_fin_three : (1 : matrix (fin 3) (fin 3) α) = !![1, 0, 0; 0, 1, 0; 0, 0, 1] :=
by { ext i j, fin_cases i; fin_cases j; refl }

end one

lemma eta_fin_two (A : matrix (fin 2) (fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma eta_fin_three (A : matrix (fin 3) (fin 3) α) :
  A = !![A 0 0, A 0 1, A 0 2;
         A 1 0, A 1 1, A 1 2;
         A 2 0, A 2 1, A 2 2] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma mul_fin_two [add_comm_monoid α] [has_mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] ⬝ !![b₁₁, b₁₂;
                    b₂₁, b₂₂] = !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
                                   a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
begin
  ext i j,
  fin_cases i; fin_cases j; simp [matrix.mul, dot_product, fin.sum_univ_succ]
end

lemma mul_fin_three [add_comm_monoid α] [has_mul α]
  (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
  !![a₁₁, a₁₂, a₁₃;
     a₂₁, a₂₂, a₂₃;
     a₃₁, a₃₂, a₃₃] ⬝ !![b₁₁, b₁₂, b₁₃;
                         b₂₁, b₂₂, b₂₃;
                         b₃₁, b₃₂, b₃₃] =
  !![a₁₁*b₁₁ + a₁₂*b₂₁ + a₁₃*b₃₁, a₁₁*b₁₂ + a₁₂*b₂₂ + a₁₃*b₃₂, a₁₁*b₁₃ + a₁₂*b₂₃ + a₁₃*b₃₃;
     a₂₁*b₁₁ + a₂₂*b₂₁ + a₂₃*b₃₁, a₂₁*b₁₂ + a₂₂*b₂₂ + a₂₃*b₃₂, a₂₁*b₁₃ + a₂₂*b₂₃ + a₂₃*b₃₃;
     a₃₁*b₁₁ + a₃₂*b₂₁ + a₃₃*b₃₁, a₃₁*b₁₂ + a₃₂*b₂₂ + a₃₃*b₃₂, a₃₁*b₁₃ + a₃₂*b₂₃ + a₃₃*b₃₃] :=
begin
  ext i j,
  fin_cases i; fin_cases j; simp [matrix.mul, dot_product, fin.sum_univ_succ, ←add_assoc],
end

lemma vec2_eq {a₀ a₁ b₀ b₁ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) :
  ![a₀, a₁] = ![b₀, b₁] :=
by subst_vars

lemma vec3_eq {a₀ a₁ a₂ b₀ b₁ b₂ : α} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
  ![a₀, a₁, a₂] = ![b₀, b₁, b₂] :=
by subst_vars

lemma vec2_add [has_add α] (a₀ a₁ b₀ b₁ : α) :
  ![a₀, a₁] + ![b₀, b₁] = ![a₀ + b₀, a₁ + b₁] :=
by rw [cons_add_cons, cons_add_cons, empty_add_empty]

lemma vec3_add [has_add α] (a₀ a₁ a₂ b₀ b₁ b₂ : α) :
  ![a₀, a₁, a₂] + ![b₀, b₁, b₂] = ![a₀ + b₀, a₁ + b₁, a₂ + b₂] :=
by rw [cons_add_cons, cons_add_cons, cons_add_cons, empty_add_empty]

lemma smul_vec2 {R : Type*} [has_smul R α] (x : R) (a₀ a₁ : α) :
  x • ![a₀, a₁] = ![x • a₀, x • a₁] :=
by rw [smul_cons, smul_cons, smul_empty]

lemma smul_vec3 {R : Type*} [has_smul R α] (x : R) (a₀ a₁ a₂ : α) :
  x • ![a₀, a₁, a₂] = ![x • a₀, x • a₁, x • a₂] :=
by rw [smul_cons, smul_cons, smul_cons, smul_empty]

variables [add_comm_monoid α] [has_mul α]

lemma vec2_dot_product' {a₀ a₁ b₀ b₁ : α} :
  ![a₀, a₁] ⬝ᵥ ![b₀, b₁] = a₀ * b₀ + a₁ * b₁ :=
by rw [cons_dot_product_cons, cons_dot_product_cons, dot_product_empty, add_zero]

@[simp] lemma vec2_dot_product (v w : fin 2 → α) :
  v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 :=
vec2_dot_product'

lemma vec3_dot_product' {a₀ a₁ a₂ b₀ b₁ b₂ : α} :
  ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ :=
by rw [cons_dot_product_cons, cons_dot_product_cons, cons_dot_product_cons,
       dot_product_empty, add_zero, add_assoc]

@[simp] lemma vec3_dot_product (v w : fin 3 → α) :
  v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 :=
vec3_dot_product'

end vec2_and_vec3

end matrix
