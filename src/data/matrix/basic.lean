/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
import algebra.pi_instances
/-!
# Matrices
-/
universes u v w

open_locale big_operators

@[nolint unused_arguments]
def matrix (m n : Type u) [fintype m] [fintype n] (α : Type v) : Type (max u v) :=
m → n → α

namespace matrix
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {α : Type v}

section ext
variables {M N : matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
⟨λ h, funext $ λ i, funext $ h i, λ h, by simp [h]⟩

@[ext] theorem ext : (∀ i j, M i j = N i j) → M = N :=
ext_iff.mp

end ext

def transpose (M : matrix m n α) : matrix n m α
| x y := M y x

localized "postfix `ᵀ`:1500 := matrix.transpose" in matrix

def col (w : m → α) : matrix m punit α
| x y := w x

def row (v : n → α) : matrix punit n α
| x y := v y

instance [inhabited α] : inhabited (matrix m n α) := pi.inhabited _
instance [has_add α] : has_add (matrix m n α) := pi.has_add
instance [add_semigroup α] : add_semigroup (matrix m n α) := pi.add_semigroup
instance [add_comm_semigroup α] : add_comm_semigroup (matrix m n α) := pi.add_comm_semigroup
instance [has_zero α] : has_zero (matrix m n α) := pi.has_zero
instance [add_monoid α] : add_monoid (matrix m n α) := pi.add_monoid
instance [add_comm_monoid α] : add_comm_monoid (matrix m n α) := pi.add_comm_monoid
instance [has_neg α] : has_neg (matrix m n α) := pi.has_neg
instance [add_group α] : add_group (matrix m n α) := pi.add_group
instance [add_comm_group α] : add_comm_group (matrix m n α) := pi.add_comm_group

@[simp] theorem zero_val [has_zero α] (i j) : (0 : matrix m n α) i j = 0 := rfl
@[simp] theorem neg_val [has_neg α] (M : matrix m n α) (i j) : (- M) i j = - M i j := rfl
@[simp] theorem add_val [has_add α] (M N : matrix m n α) (i j) : (M + N) i j = M i j + N i j := rfl

section diagonal
variables [decidable_eq n]

/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`. -/
def diagonal [has_zero α] (d : n → α) : matrix n n α := λ i j, if i = j then d i else 0

@[simp] theorem diagonal_val_eq [has_zero α] {d : n → α} (i : n) : (diagonal d) i i = d i :=
by simp [diagonal]

@[simp] theorem diagonal_val_ne [has_zero α] {d : n → α} {i j : n} (h : i ≠ j) :
  (diagonal d) i j = 0 := by simp [diagonal, h]

theorem diagonal_val_ne' [has_zero α] {d : n → α} {i j : n} (h : j ≠ i) :
  (diagonal d) i j = 0 := diagonal_val_ne h.symm

@[simp] theorem diagonal_zero [has_zero α] : (diagonal (λ _, 0) : matrix n n α) = 0 :=
by simp [diagonal]; refl

@[simp] lemma diagonal_transpose [has_zero α] (v : n → α) :
  (diagonal v)ᵀ = diagonal v :=
begin
  ext i j,
  by_cases h : i = j,
  { simp [h, transpose] },
  { simp [h, transpose, diagonal_val_ne' h] }
end

@[simp] theorem diagonal_add [add_monoid α] (d₁ d₂ : n → α) :
  diagonal d₁ + diagonal d₂ = diagonal (λ i, d₁ i + d₂ i) :=
by ext i j; by_cases h : i = j; simp [h]

section one
variables [has_zero α] [has_one α]

instance : has_one (matrix n n α) := ⟨diagonal (λ _, 1)⟩

@[simp] theorem diagonal_one : (diagonal (λ _, 1) : matrix n n α) = 1 := rfl

theorem one_val {i j} : (1 : matrix n n α) i j = if i = j then 1 else 0 := rfl

@[simp] theorem one_val_eq (i) : (1 : matrix n n α) i i = 1 := diagonal_val_eq i

@[simp] theorem one_val_ne {i j} : i ≠ j → (1 : matrix n n α) i j = 0 :=
diagonal_val_ne

theorem one_val_ne' {i j} : j ≠ i → (1 : matrix n n α) i j = 0 :=
diagonal_val_ne'

end one

section numeral

@[simp] lemma bit0_val [has_add α] (M : matrix m m α) (i : m) (j : m) :
  (bit0 M) i j = bit0 (M i j) := rfl

variables [add_monoid α] [has_one α]

lemma bit1_val (M : matrix n n α) (i : n) (j : n) :
  (bit1 M) i j = if i = j then bit1 (M i j) else bit0 (M i j) :=
by dsimp [bit1]; by_cases h : i = j; simp [h]

@[simp]
lemma bit1_val_eq (M : matrix n n α) (i : n) :
  (bit1 M) i i = bit1 (M i i) :=
by simp [bit1_val]

@[simp]
lemma bit1_val_ne (M : matrix n n α) {i j : n} (h : i ≠ j) :
  (bit1 M) i j = bit0 (M i j) :=
by simp [bit1_val, h]

end numeral

end diagonal

section dot_product

/-- `dot_product v w` is the sum of the entrywise products `v i * w i` -/
def dot_product [has_mul α] [add_comm_monoid α] (v w : m → α) : α :=
∑ i, v i * w i

lemma dot_product_assoc [semiring α] (u : m → α) (v : m → n → α) (w : n → α) :
  dot_product (λ j, dot_product u (λ i, v i j)) w = dot_product u (λ i, dot_product (v i) w) :=
by simpa [dot_product, finset.mul_sum, finset.sum_mul, mul_assoc] using finset.sum_comm

lemma dot_product_comm [comm_semiring α] (v w : m → α) :
  dot_product v w = dot_product w v :=
by simp_rw [dot_product, mul_comm]

@[simp] lemma dot_product_punit [add_comm_monoid α] [has_mul α] (v w : punit → α) :
  dot_product v w = v ⟨⟩ * w ⟨⟩ :=
by simp [dot_product]

@[simp] lemma dot_product_zero [semiring α] (v : m → α) : dot_product v 0 = 0 :=
by simp [dot_product]

@[simp] lemma dot_product_zero' [semiring α] (v : m → α) : dot_product v (λ _, 0) = 0 :=
dot_product_zero v

@[simp] lemma zero_dot_product [semiring α] (v : m → α) : dot_product 0 v = 0 :=
by simp [dot_product]

@[simp] lemma zero_dot_product' [semiring α] (v : m → α) : dot_product (λ _, (0 : α)) v = 0 :=
zero_dot_product v

@[simp] lemma add_dot_product [semiring α] (u v w : m → α) :
  dot_product (u + v) w = dot_product u w + dot_product v w :=
by simp [dot_product, add_mul, finset.sum_add_distrib]

@[simp] lemma dot_product_add [semiring α] (u v w : m → α) :
  dot_product u (v + w) = dot_product u v + dot_product u w :=
by simp [dot_product, mul_add, finset.sum_add_distrib]

@[simp] lemma diagonal_dot_product [decidable_eq m] [semiring α] (v w : m → α) (i : m) :
  dot_product (diagonal v i) w = v i * w i :=
have ∀ j ≠ i, diagonal v i j * w j = 0 := λ j hij, by simp [diagonal_val_ne' hij],
by convert finset.sum_eq_single i (λ j _, this j) _; simp

@[simp] lemma dot_product_diagonal [decidable_eq m] [semiring α] (v w : m → α) (i : m) :
  dot_product v (diagonal w i) = v i * w i :=
have ∀ j ≠ i, v j * diagonal w i j = 0 := λ j hij, by simp [diagonal_val_ne' hij],
by convert finset.sum_eq_single i (λ j _, this j) _; simp

@[simp] lemma dot_product_diagonal' [decidable_eq m] [semiring α] (v w : m → α) (i : m) :
  dot_product v (λ j, diagonal w j i) = v i * w i :=
have ∀ j ≠ i, v j * diagonal w j i = 0 := λ j hij, by simp [diagonal_val_ne hij],
by convert finset.sum_eq_single i (λ j _, this j) _; simp

@[simp] lemma neg_dot_product [ring α] (v w : m → α) : dot_product (-v) w = - dot_product v w :=
by simp [dot_product]

@[simp] lemma dot_product_neg [ring α] (v w : m → α) : dot_product v (-w) = - dot_product v w :=
by simp [dot_product]

@[simp] lemma smul_dot_product [semiring α] (x : α) (v w : m → α) :
  dot_product (x • v) w = x * dot_product v w :=
by simp [dot_product, finset.mul_sum, mul_assoc]

@[simp] lemma dot_product_smul [comm_semiring α] (x : α) (v w : m → α) :
  dot_product v (x • w) = x * dot_product v w :=
by simp [dot_product, finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

end dot_product

protected def mul [has_mul α] [add_comm_monoid α] (M : matrix l m α) (N : matrix m n α) :
  matrix l n α :=
λ i k, dot_product (λ j, M i j) (λ j, N j k)

localized "infixl ` ⬝ `:75 := matrix.mul" in matrix

theorem mul_val [has_mul α] [add_comm_monoid α] {M : matrix l m α} {N : matrix m n α} {i k} :
  (M ⬝ N) i k = ∑ j, M i j * N j k := rfl

instance [has_mul α] [add_comm_monoid α] : has_mul (matrix n n α) := ⟨matrix.mul⟩

@[simp] theorem mul_eq_mul [has_mul α] [add_comm_monoid α] (M N : matrix n n α) :
  M * N = M ⬝ N := rfl

theorem mul_val' [has_mul α] [add_comm_monoid α] {M N : matrix n n α} {i k} :
  (M ⬝ N) i k = dot_product (λ j, M i j) (λ j, N j k) := rfl

section semigroup
variables [semiring α]

protected theorem mul_assoc (L : matrix l m α) (M : matrix m n α) (N : matrix n o α) :
  (L ⬝ M) ⬝ N = L ⬝ (M ⬝ N) :=
by { ext, apply dot_product_assoc }

instance : semigroup (matrix n n α) :=
{ mul_assoc := matrix.mul_assoc, ..matrix.has_mul }

end semigroup

@[simp] theorem diagonal_neg [decidable_eq n] [add_group α] (d : n → α) :
  -diagonal d = diagonal (λ i, -d i) :=
by ext i j; by_cases i = j; simp [h]

section semiring
variables [semiring α]

@[simp] protected theorem mul_zero (M : matrix m n α) : M ⬝ (0 : matrix n o α) = 0 :=
by { ext i j, apply dot_product_zero }

@[simp] protected theorem zero_mul (M : matrix m n α) : (0 : matrix l m α) ⬝ M = 0 :=
by { ext i j, apply zero_dot_product }

protected theorem mul_add (L : matrix m n α) (M N : matrix n o α) : L ⬝ (M + N) = L ⬝ M + L ⬝ N :=
by { ext i j, apply dot_product_add }

protected theorem add_mul (L M : matrix l m α) (N : matrix m n α) : (L + M) ⬝ N = L ⬝ N + M ⬝ N :=
by { ext i j, apply add_dot_product }

@[simp] theorem diagonal_mul [decidable_eq m]
  (d : m → α) (M : matrix m n α) (i j) : (diagonal d).mul M i j = d i * M i j :=
diagonal_dot_product _ _ _

@[simp] theorem mul_diagonal [decidable_eq n]
  (d : n → α) (M : matrix m n α) (i j) : (M ⬝ diagonal d) i j = M i j * d j :=
by { rw ← diagonal_transpose, apply dot_product_diagonal }

@[simp] protected theorem one_mul [decidable_eq m] (M : matrix m n α) : (1 : matrix m m α) ⬝ M = M :=
by ext i j; rw [← diagonal_one, diagonal_mul, one_mul]

@[simp] protected theorem mul_one [decidable_eq n] (M : matrix m n α) : M ⬝ (1 : matrix n n α) = M :=
by ext i j; rw [← diagonal_one, mul_diagonal, mul_one]

instance [decidable_eq n] : monoid (matrix n n α) :=
{ one_mul := matrix.one_mul,
  mul_one := matrix.mul_one,
  ..matrix.has_one, ..matrix.semigroup }

instance [decidable_eq n] : semiring (matrix n n α) :=
{ mul_zero := matrix.mul_zero,
  zero_mul := matrix.zero_mul,
  left_distrib := matrix.mul_add,
  right_distrib := matrix.add_mul,
  ..matrix.add_comm_monoid,
  ..matrix.monoid }

@[simp] theorem diagonal_mul_diagonal [decidable_eq n] (d₁ d₂ : n → α) :
  (diagonal d₁) ⬝ (diagonal d₂) = diagonal (λ i, d₁ i * d₂ i) :=
by ext i j; by_cases i = j; simp [h]

theorem diagonal_mul_diagonal' [decidable_eq n] (d₁ d₂ : n → α) :
  diagonal d₁ * diagonal d₂ = diagonal (λ i, d₁ i * d₂ i) :=
diagonal_mul_diagonal _ _

lemma is_add_monoid_hom_mul_left (M : matrix l m α) :
  is_add_monoid_hom (λ x : matrix m n α, M ⬝ x) :=
{ to_is_add_hom := ⟨matrix.mul_add _⟩, map_zero := matrix.mul_zero _ }

lemma is_add_monoid_hom_mul_right (M : matrix m n α) :
  is_add_monoid_hom (λ x : matrix l m α, x ⬝ M) :=
{ to_is_add_hom := ⟨λ _ _, matrix.add_mul _ _ _⟩, map_zero := matrix.zero_mul _ }

protected lemma sum_mul {β : Type*} (s : finset β) (f : β → matrix l m α)
  (M : matrix m n α) : (∑ a in s, f a) ⬝ M = ∑ a in s, f a ⬝ M :=
(@finset.sum_hom _ _ _ _ _ s f (λ x, x ⬝ M)
/- This line does not type-check without `id` and `: _`. Lean did not recognize that two different
  `add_monoid` instances were def-eq -/
  (id (@is_add_monoid_hom_mul_right l _ _ _ _ _ _ _ M) : _)).symm

protected lemma mul_sum {β : Type*} (s : finset β) (f : β → matrix m n α)
  (M : matrix l m α) :  M ⬝ ∑ a in s, f a = ∑ a in s, M ⬝ f a :=
(@finset.sum_hom _ _ _ _ _ s f (λ x, M ⬝ x)
/- This line does not type-check without `id` and `: _`. Lean did not recognize that two different
  `add_monoid` instances were def-eq -/
  (id (@is_add_monoid_hom_mul_left _ _ n _ _ _ _ _ M) : _)).symm

@[simp]
lemma row_mul_col_val (v w : m → α) (i j) : (row v ⬝ col w) i j = dot_product v w :=
rfl

end semiring

section ring
variables [ring α]

@[simp] theorem neg_mul (M : matrix m n α) (N : matrix n o α) :
  (-M) ⬝ N = -(M ⬝ N) :=
by { ext, apply neg_dot_product }

@[simp] theorem mul_neg (M : matrix m n α) (N : matrix n o α) :
  M ⬝ (-N) = -(M ⬝ N) :=
by { ext, apply dot_product_neg }

end ring

instance [decidable_eq n] [ring α] : ring (matrix n n α) :=
{ ..matrix.semiring, ..matrix.add_comm_group }

instance [semiring α] : has_scalar α (matrix m n α) := pi.has_scalar
instance {β : Type w} [semiring α] [add_comm_monoid β] [semimodule α β] :
  semimodule α (matrix m n β) := pi.semimodule _ _ _

@[simp] lemma smul_val [semiring α] (a : α) (A : matrix m n α) (i : m) (j : n) : (a • A) i j = a * A i j := rfl

section semiring
variables [semiring α]

lemma smul_eq_diagonal_mul [decidable_eq m] (M : matrix m n α) (a : α) :
  a • M = diagonal (λ _, a) ⬝ M :=
by { ext, simp }

@[simp] lemma smul_mul (M : matrix m n α) (a : α) (N : matrix n l α) : (a • M) ⬝ N = a • M ⬝ N :=
by { ext, apply smul_dot_product }

@[simp] lemma mul_mul_left (M : matrix m n α) (N : matrix n o α) (a : α) :
  (λ i j, a * M i j) ⬝ N = a • (M ⬝ N) :=
begin
  simp only [←smul_val],
  simp,
end

/--
The ring homomorphism `α →+* matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [fintype n] [decidable_eq n] : α →+* matrix n n α :=
{ to_fun := λ a, a • 1,
  map_zero' := by simp,
  map_add' := by { intros, ext, simp [add_mul], },
  map_one' := by simp,
  map_mul' := by { intros, ext, simp [mul_assoc], }, }

section scalar

variable [decidable_eq n]

@[simp] lemma coe_scalar : (scalar n : α → matrix n n α) = λ a, a • 1 := rfl

lemma scalar_apply_eq (a : α) (i : n) :
  scalar n a i i = a :=
by simp only [coe_scalar, mul_one, one_val_eq, smul_val]

lemma scalar_apply_ne (a : α) (i j : n) (h : i ≠ j) :
  scalar n a i j = 0 :=
by simp only [h, coe_scalar, one_val_ne, ne.def, not_false_iff, smul_val, mul_zero]

end scalar

end semiring

section comm_semiring
variables [comm_semiring α]

lemma smul_eq_mul_diagonal [decidable_eq n] (M : matrix m n α) (a : α) :
  a • M = M ⬝ diagonal (λ _, a) :=
by { ext, simp [mul_comm] }

@[simp] lemma mul_smul (M : matrix m n α) (a : α) (N : matrix n l α) : M ⬝ (a • N) = a • M ⬝ N :=
by { ext, apply dot_product_smul }

@[simp] lemma mul_mul_right (M : matrix m n α) (N : matrix n o α) (a : α) :
  M ⬝ (λ i j, a * N i j) = a • (M ⬝ N) :=
begin
  simp only [←smul_val],
  simp,
end

end comm_semiring

section semiring
variables [semiring α]

def vec_mul_vec (w : m → α) (v : n → α) : matrix m n α
| x y := w x * v y

def mul_vec (M : matrix m n α) (v : n → α) : m → α
| i := dot_product (λ j, M i j) v

def vec_mul (v : m → α) (M : matrix m n α) : n → α
| j := dot_product v (λ i, M i j)

instance mul_vec.is_add_monoid_hom_left (v : n → α) :
  is_add_monoid_hom (λM:matrix m n α, mul_vec M v) :=
{ map_zero := by ext; simp [mul_vec]; refl,
  map_add :=
  begin
    intros x y,
    ext m,
    apply add_dot_product
  end }

lemma mul_vec_diagonal [decidable_eq m] (v w : m → α) (x : m) :
  mul_vec (diagonal v) w x = v x * w x :=
diagonal_dot_product v w x

lemma vec_mul_diagonal [decidable_eq m] (v w : m → α) (x : m) :
  vec_mul v (diagonal w) x = v x * w x :=
dot_product_diagonal' v w x

@[simp] lemma mul_vec_one [decidable_eq m] (v : m → α) : mul_vec 1 v = v :=
by { ext, rw [←diagonal_one, mul_vec_diagonal, one_mul] }

@[simp] lemma vec_mul_one [decidable_eq m] (v : m → α) : vec_mul v 1 = v :=
by { ext, rw [←diagonal_one, vec_mul_diagonal, mul_one] }

@[simp] lemma mul_vec_zero (A : matrix m n α) : mul_vec A 0 = 0 :=
by { ext, simp [mul_vec] }

@[simp] lemma vec_mul_zero (A : matrix m n α) : vec_mul 0 A = 0 :=
by { ext, simp [vec_mul] }

@[simp] lemma vec_mul_vec_mul (v : m → α) (M : matrix m n α) (N : matrix n o α) :
  vec_mul (vec_mul v M) N = vec_mul v (M ⬝ N) :=
by { ext, apply dot_product_assoc }

@[simp] lemma mul_vec_mul_vec (v : o → α) (M : matrix m n α) (N : matrix n o α) :
  mul_vec M (mul_vec N v) = mul_vec (M ⬝ N) v :=
by { ext, symmetry, apply dot_product_assoc }

lemma vec_mul_vec_eq (w : m → α) (v : n → α) :
  vec_mul_vec w v = (col w) ⬝ (row v) :=
by { ext i j, simp [vec_mul_vec, mul_val], refl }

variables [decidable_eq m] [decidable_eq n]

/--
`std_basis_matrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def std_basis_matrix (i : m) (j : n) (a : α) : matrix m n α :=
(λ i' j', if i' = i ∧ j' = j then a else 0)

@[simp] lemma smul_std_basis_matrix (i : m) (j : n) (a b : α) :
b • std_basis_matrix i j a = std_basis_matrix i j (b • a) :=
by { unfold std_basis_matrix, ext, dsimp, simp }

@[simp] lemma std_basis_matrix_zero (i : m) (j : n) :
std_basis_matrix i j (0 : α) = 0 :=
by { unfold std_basis_matrix, ext, simp }

lemma std_basis_matrix_add (i : m) (j : n) (a b : α) :
std_basis_matrix i j (a + b) = std_basis_matrix i j a + std_basis_matrix i j b :=
begin
  unfold std_basis_matrix, ext,
  split_ifs with h; simp [h],
end


lemma matrix_eq_sum_elementary (x : matrix n m α) :
x = ∑ (i : n) (j : m), std_basis_matrix i j (x i j) :=
begin
  ext, iterate 2 {rw finset.sum_apply},
  rw ← finset.sum_subset, swap 4, exact {i},
  { norm_num [std_basis_matrix] },
  { simp },
  intros, norm_num at a, norm_num,
  convert finset.sum_const_zero,
  ext, norm_num [std_basis_matrix],
  rw if_neg, tauto!,
end

-- TODO: tie this up with the `basis` machinery of linear algebra
-- this is not completely trivial because we are indexing by two types, instead of one

-- TODO: add `std_basis_vec`
lemma elementary_eq_basis_mul_basis (i : m) (j : n) :
std_basis_matrix i j 1 = vec_mul_vec (λ i', ite (i = i') 1 0) (λ j', ite (j = j') 1 0) :=
begin
  ext, norm_num [std_basis_matrix, vec_mul_vec],
  split_ifs; tauto,
end

@[elab_as_eliminator] protected lemma induction_on'
  {X : Type*} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X)
  (h_zero : M 0)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_elementary : ∀ i j x, M (std_basis_matrix i j x)) :
  M m :=
begin
  rw [matrix_eq_sum_elementary m, ← finset.sum_product'],
  apply finset.sum_induction _ _ h_add h_zero,
  { intros, apply h_elementary, }
end

@[elab_as_eliminator] protected lemma induction_on
  [nonempty n] {X : Type*} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_elementary : ∀ i j x, M (std_basis_matrix i j x)) :
  M m :=
matrix.induction_on' m
begin
  have i : n := classical.choice (by assumption),
  simpa using h_elementary i i 0,
end
h_add h_elementary

end semiring

section ring

variables [ring α]

lemma neg_vec_mul (v : m → α) (A : matrix m n α) : vec_mul (-v) A = - vec_mul v A :=
by { ext, apply neg_dot_product }

lemma vec_mul_neg (v : m → α) (A : matrix m n α) : vec_mul v (-A) = - vec_mul v A :=
by { ext, apply dot_product_neg }

lemma neg_mul_vec (v : n → α) (A : matrix m n α) : mul_vec (-A) v = - mul_vec A v :=
by { ext, apply neg_dot_product }

lemma mul_vec_neg (v : n → α) (A : matrix m n α) : mul_vec A (-v) = - mul_vec A v :=
by { ext, apply dot_product_neg }

end ring

section transpose

open_locale matrix

/--
  Tell `simp` what the entries are in a transposed matrix.

  Compare with `mul_val`, `diagonal_val_eq`, etc.
-/
@[simp] lemma transpose_val (M : matrix m n α) (i j) : M.transpose j i = M i j := rfl

@[simp] lemma transpose_transpose (M : matrix m n α) :
  Mᵀᵀ = M :=
by ext; refl

@[simp] lemma transpose_zero [has_zero α] : (0 : matrix m n α)ᵀ = 0 :=
by ext i j; refl

@[simp] lemma transpose_one [decidable_eq n] [has_zero α] [has_one α] : (1 : matrix n n α)ᵀ = 1 :=
begin
  ext i j,
  unfold has_one.one transpose,
  by_cases i = j,
  { simp only [h, diagonal_val_eq] },
  { simp only [diagonal_val_ne h, diagonal_val_ne (λ p, h (symm p))] }
end

@[simp] lemma transpose_add [has_add α] (M : matrix m n α) (N : matrix m n α) :
  (M + N)ᵀ = Mᵀ + Nᵀ  :=
by { ext i j, simp }

@[simp] lemma transpose_sub [add_comm_group α] (M : matrix m n α) (N : matrix m n α) :
  (M - N)ᵀ = Mᵀ - Nᵀ  :=
by { ext i j, simp }

@[simp] lemma transpose_mul [comm_ring α] (M : matrix m n α) (N : matrix n l α) :
  (M ⬝ N)ᵀ = Nᵀ ⬝ Mᵀ  :=
begin
  ext i j,
  apply dot_product_comm
end

@[simp] lemma transpose_smul [comm_ring α] (c : α)(M : matrix m n α) :
  (c • M)ᵀ = c • Mᵀ :=
by { ext i j, refl }

@[simp] lemma transpose_neg [comm_ring α] (M : matrix m n α) :
  (- M)ᵀ = - Mᵀ  :=
by ext i j; refl

end transpose

def minor (A : matrix m n α) (row : l → m) (col : o → n) : matrix l o α :=
λ i j, A (row i) (col j)

@[reducible]
def sub_left {m l r : nat} (A : matrix (fin m) (fin (l + r)) α) : matrix (fin m) (fin l) α :=
minor A id (fin.cast_add r)

@[reducible]
def sub_right {m l r : nat} (A : matrix (fin m) (fin (l + r)) α) : matrix (fin m) (fin r) α :=
minor A id (fin.nat_add l)

@[reducible]
def sub_up {d u n : nat} (A : matrix (fin (u + d)) (fin n) α) : matrix (fin u) (fin n) α :=
minor A (fin.cast_add d) id

@[reducible]
def sub_down {d u n : nat} (A : matrix (fin (u + d)) (fin n) α) : matrix (fin d) (fin n) α :=
minor A (fin.nat_add u) id

@[reducible]
def sub_up_right {d u l r : nat} (A: matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin u) (fin r) α :=
sub_up (sub_right A)

@[reducible]
def sub_down_right {d u l r : nat} (A : matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin d) (fin r) α :=
sub_down (sub_right A)

@[reducible]
def sub_up_left {d u l r : nat} (A : matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin u) (fin (l)) α :=
sub_up (sub_left A)

@[reducible]
def sub_down_left {d u l r : nat} (A: matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin d) (fin (l)) α :=
sub_down (sub_left A)

section row_col
/-!
### `row_col` section

Simplification lemmas for `matrix.row` and `matrix.col`.
-/
open_locale matrix

@[simp] lemma col_add [semiring α] (v w : m → α) : col (v + w) = col v + col w := by { ext, refl }
@[simp] lemma col_smul [semiring α] (x : α) (v : m → α) : col (x • v) = x • col v := by { ext, refl }
@[simp] lemma row_add [semiring α] (v w : m → α) : row (v + w) = row v + row w := by { ext, refl }
@[simp] lemma row_smul [semiring α] (x : α) (v : m → α) : row (x • v) = x • row v := by { ext, refl }

@[simp] lemma col_val (v : m → α) (i j) : matrix.col v i j = v i := rfl
@[simp] lemma row_val (v : m → α) (i j) : matrix.row v i j = v j := rfl

@[simp]
lemma transpose_col (v : m → α) : (matrix.col v).transpose = matrix.row v := by {ext, refl}
@[simp]
lemma transpose_row (v : m → α) : (matrix.row v).transpose = matrix.col v := by {ext, refl}

lemma row_vec_mul [semiring α] (M : matrix m n α) (v : m → α) :
  matrix.row (matrix.vec_mul v M) = matrix.row v ⬝ M := by {ext, refl}
lemma col_vec_mul [semiring α] (M : matrix m n α) (v : m → α) :
  matrix.col (matrix.vec_mul v M) = (matrix.row v ⬝ M)ᵀ := by {ext, refl}
lemma col_mul_vec [semiring α] (M : matrix m n α) (v : n → α) :
  matrix.col (matrix.mul_vec M v) = M ⬝ matrix.col v := by {ext, refl}
lemma row_mul_vec [semiring α] (M : matrix m n α) (v : n → α) :
  matrix.row (matrix.mul_vec M v) = (M ⬝ matrix.col v)ᵀ := by {ext, refl}

end row_col

end matrix

namespace ring_hom
variables {α β : Type*} [semiring α] [semiring β]
variables {m n o : Type u} [fintype m] [fintype n] [fintype o]

lemma map_matrix_mul (M : matrix m n α) (N : matrix n o α) (i : m) (j : o) (f : α →+* β) :
  f (matrix.mul M N i j) = matrix.mul (λ i j, f (M i j)) (λ i j, f (N i j)) i j :=
by simp [matrix.mul_val, ring_hom.map_sum]

end ring_hom
