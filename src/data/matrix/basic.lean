/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
import algebra.big_operators.pi
import algebra.module.pi
import algebra.module.linear_map
import algebra.big_operators.ring
import algebra.star.pi
import algebra.algebra.basic
import data.equiv.ring
import data.fintype.card
import data.matrix.dmatrix

/-!
# Matrices

This file defines basic properties of matrices.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/
universes u u' v w

open_locale big_operators
open dmatrix

/-- `matrix m n` is the type of matrices whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
def matrix (m : Type u) (n : Type u') (α : Type v) : Type (max u u' v) :=
m → n → α

variables {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variables {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace matrix

section ext
variables {M N : matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
⟨λ h, funext $ λ i, funext $ h i, λ h, by simp [h]⟩

@[ext] theorem ext : (∀ i j, M i j = N i j) → M = N :=
ext_iff.mp

end ext

/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`.

This is available in bundled forms as:
* `add_monoid_hom.map_matrix`
* `linear_map.map_matrix`
* `ring_hom.map_matrix`
* `alg_hom.map_matrix`
* `equiv.map_matrix`
* `add_equiv.map_matrix`
* `linear_equiv.map_matrix`
* `ring_equiv.map_matrix`
* `alg_equiv.map_matrix`
-/
def map (M : matrix m n α) (f : α → β) : matrix m n β := λ i j, f (M i j)

@[simp]
lemma map_apply {M : matrix m n α} {f : α → β} {i : m} {j : n} :
  M.map f i j = f (M i j) := rfl

@[simp]
lemma map_id (M : matrix m n α) : M.map id = M :=
by { ext, refl, }

@[simp]
lemma map_map {M : matrix m n α} {β γ : Type*} {f : α → β} {g : β → γ} :
  (M.map f).map g = M.map (g ∘ f) :=
by { ext, refl, }

/-- The transpose of a matrix. -/
def transpose (M : matrix m n α) : matrix n m α
| x y := M y x

localized "postfix `ᵀ`:1500 := matrix.transpose" in matrix

/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conj_transpose [has_star α] (M : matrix m n α) : matrix n m α :=
M.transpose.map star

localized "postfix `ᴴ`:1500 := matrix.conj_transpose" in matrix

/-- `matrix.col u` is the column matrix whose entries are given by `u`. -/
def col (w : m → α) : matrix m unit α
| x y := w x

/-- `matrix.row u` is the row matrix whose entries are given by `u`. -/
def row (v : n → α) : matrix unit n α
| x y := v y

instance [inhabited α] : inhabited (matrix m n α) := pi.inhabited _
instance [has_add α] : has_add (matrix m n α) := pi.has_add
instance [add_semigroup α] : add_semigroup (matrix m n α) := pi.add_semigroup
instance [add_comm_semigroup α] : add_comm_semigroup (matrix m n α) := pi.add_comm_semigroup
instance [has_zero α] : has_zero (matrix m n α) := pi.has_zero
instance [add_zero_class α] : add_zero_class (matrix m n α) := pi.add_zero_class
instance [add_monoid α] : add_monoid (matrix m n α) := pi.add_monoid
instance [add_comm_monoid α] : add_comm_monoid (matrix m n α) := pi.add_comm_monoid
instance [has_neg α] : has_neg (matrix m n α) := pi.has_neg
instance [has_sub α] : has_sub (matrix m n α) := pi.has_sub
instance [add_group α] : add_group (matrix m n α) := pi.add_group
instance [add_comm_group α] : add_comm_group (matrix m n α) := pi.add_comm_group
instance [unique α] : unique (matrix m n α) := pi.unique
instance [subsingleton α] : subsingleton (matrix m n α) := pi.subsingleton
instance [nonempty m] [nonempty n] [nontrivial α] : nontrivial (matrix m n α) :=
function.nontrivial

instance [has_scalar R α] : has_scalar R (matrix m n α) := pi.has_scalar
instance [has_scalar R α] [has_scalar S α] [smul_comm_class R S α] :
  smul_comm_class R S (matrix m n α) := pi.smul_comm_class
instance [has_scalar R S] [has_scalar R α] [has_scalar S α] [is_scalar_tower R S α] :
  is_scalar_tower R S (matrix m n α) := pi.is_scalar_tower
instance [monoid R] [mul_action R α] :
  mul_action R (matrix m n α) := pi.mul_action _
instance [monoid R] [add_monoid α] [distrib_mul_action R α] :
  distrib_mul_action R (matrix m n α) := pi.distrib_mul_action _
instance [semiring R] [add_comm_monoid α] [module R α] :
  module R (matrix m n α) := pi.module _ _ _

@[simp] lemma map_zero [has_zero α] [has_zero β] (f : α → β) (h : f 0 = 0) :
  (0 : matrix m n α).map f = 0 :=
by { ext, simp [h], }

lemma map_add [has_add α] [has_add β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)
  (M N : matrix m n α) : (M + N).map f = M.map f + N.map f :=
ext $ λ _ _, hf _ _

lemma map_sub [has_sub α] [has_sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
  (M N : matrix m n α) : (M - N).map f = M.map f - N.map f :=
ext $ λ _ _, hf _ _

lemma map_smul [has_scalar R α] [has_scalar R β] (f : α → β) (r : R)
  (hf : ∀ a, f (r • a) = r • f a) (M : matrix m n α) : (r • M).map f = r • (M.map f) :=
ext $ λ _ _, hf _

lemma _root_.is_smul_regular.matrix [has_scalar R S] {k : R} (hk : is_smul_regular S k) :
  is_smul_regular (matrix m n S) k :=
is_smul_regular.pi $ λ _, is_smul_regular.pi $ λ _, hk

lemma _root_.is_left_regular.matrix [has_mul α] {k : α} (hk : is_left_regular k) :
  is_smul_regular (matrix m n α) k :=
hk.is_smul_regular.matrix

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_empty_left [is_empty m] : subsingleton (matrix m n α) :=
⟨λ M N, by { ext, exact is_empty_elim i }⟩

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_empty_right [is_empty n] : subsingleton (matrix m n α) :=
⟨λ M N, by { ext, exact is_empty_elim j }⟩

end matrix

open_locale matrix

namespace matrix

section diagonal
variables [decidable_eq n]

/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`.

Note that bundled versions exist as:
* `matrix.diagonal_add_monoid_hom`
* `matrix.diagonal_linear_map`
* `matrix.diagonal_ring_hom`
* `matrix.diagonal_alg_hom`
-/
def diagonal [has_zero α] (d : n → α) : matrix n n α
| i j := if i = j then d i else 0

@[simp] theorem diagonal_apply_eq [has_zero α] {d : n → α} (i : n) : (diagonal d) i i = d i :=
by simp [diagonal]

@[simp] theorem diagonal_apply_ne [has_zero α] {d : n → α} {i j : n} (h : i ≠ j) :
  (diagonal d) i j = 0 := by simp [diagonal, h]

theorem diagonal_apply_ne' [has_zero α] {d : n → α} {i j : n} (h : j ≠ i) :
  (diagonal d) i j = 0 := diagonal_apply_ne h.symm

lemma diagonal_injective [has_zero α] : function.injective (diagonal : (n → α) → matrix n n α) :=
λ d₁ d₂ h, funext $ λ i, by simpa using matrix.ext_iff.mpr h i i

@[simp] theorem diagonal_zero [has_zero α] : (diagonal (λ _, 0) : matrix n n α) = 0 :=
by { ext, simp [diagonal] }

@[simp] lemma diagonal_transpose [has_zero α] (v : n → α) :
  (diagonal v)ᵀ = diagonal v :=
begin
  ext i j,
  by_cases h : i = j,
  { simp [h, transpose] },
  { simp [h, transpose, diagonal_apply_ne' h] }
end

@[simp] theorem diagonal_add [add_zero_class α] (d₁ d₂ : n → α) :
  diagonal d₁ + diagonal d₂ = diagonal (λ i, d₁ i + d₂ i) :=
by ext i j; by_cases h : i = j; simp [h]

@[simp] theorem diagonal_smul [monoid R] [add_monoid α] [distrib_mul_action R α] (r : R)
  (d : n → α) :
  diagonal (r • d) = r • diagonal d :=
by ext i j; by_cases h : i = j; simp [h]

variables (n α)

/-- `matrix.diagonal` as an `add_monoid_hom`. -/
@[simps]
def diagonal_add_monoid_hom [add_zero_class α] : (n → α) →+ matrix n n α :=
{ to_fun := diagonal,
  map_zero' := diagonal_zero,
  map_add' := λ x y, (diagonal_add x y).symm,}

variables (R)

/-- `matrix.diagonal` as a `linear_map`. -/
@[simps]
def diagonal_linear_map [semiring R] [add_comm_monoid α] [module R α] :
  (n → α) →ₗ[R] matrix n n α :=
{ map_smul' := diagonal_smul,
  .. diagonal_add_monoid_hom n α,}

variables {n α R}

@[simp] lemma diagonal_map [has_zero α] [has_zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
  (diagonal d).map f = diagonal (λ m, f (d m)) :=
by { ext, simp only [diagonal, map_apply], split_ifs; simp [h], }

@[simp] lemma diagonal_conj_transpose [semiring α] [star_ring α] (v : n → α) :
  (diagonal v)ᴴ = diagonal (star v) :=
begin
  rw [conj_transpose, diagonal_transpose, diagonal_map (star_zero _)],
  refl,
end

section one
variables [has_zero α] [has_one α]

instance : has_one (matrix n n α) := ⟨diagonal (λ _, 1)⟩

@[simp] theorem diagonal_one : (diagonal (λ _, 1) : matrix n n α) = 1 := rfl

theorem one_apply {i j} : (1 : matrix n n α) i j = if i = j then 1 else 0 := rfl

@[simp] theorem one_apply_eq (i) : (1 : matrix n n α) i i = 1 := diagonal_apply_eq i

@[simp] theorem one_apply_ne {i j} : i ≠ j → (1 : matrix n n α) i j = 0 :=
diagonal_apply_ne

theorem one_apply_ne' {i j} : j ≠ i → (1 : matrix n n α) i j = 0 :=
diagonal_apply_ne'

@[simp] lemma map_one [has_zero β] [has_one β]
  (f : α → β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
  (1 : matrix n n α).map f = (1 : matrix n n β) :=
by { ext, simp only [one_apply, map_apply], split_ifs; simp [h₀, h₁], }

lemma one_eq_pi_single {i j} : (1 : matrix n n α) i j = pi.single i 1 j :=
by simp only [one_apply, pi.single_apply, eq_comm]; congr -- deal with decidable_eq

end one

section numeral

@[simp] lemma bit0_apply [has_add α] (M : matrix m m α) (i : m) (j : m) :
  (bit0 M) i j = bit0 (M i j) := rfl

variables [add_monoid α] [has_one α]

lemma bit1_apply (M : matrix n n α) (i : n) (j : n) :
  (bit1 M) i j = if i = j then bit1 (M i j) else bit0 (M i j) :=
by dsimp [bit1]; by_cases h : i = j; simp [h]

@[simp]
lemma bit1_apply_eq (M : matrix n n α) (i : n) :
  (bit1 M) i i = bit1 (M i i) :=
by simp [bit1_apply]

@[simp]
lemma bit1_apply_ne (M : matrix n n α) {i j : n} (h : i ≠ j) :
  (bit1 M) i j = bit0 (M i j) :=
by simp [bit1_apply, h]

end numeral

end diagonal

section dot_product

variable [fintype m]

/-- `dot_product v w` is the sum of the entrywise products `v i * w i` -/
def dot_product [has_mul α] [add_comm_monoid α] (v w : m → α) : α :=
∑ i, v i * w i

lemma dot_product_assoc [fintype n] [non_unital_semiring α] (u : m → α) (w : n → α)
  (v : matrix m n α) :
  dot_product (λ j, dot_product u (λ i, v i j)) w = dot_product u (λ i, dot_product (v i) w) :=
by simpa [dot_product, finset.mul_sum, finset.sum_mul, mul_assoc] using finset.sum_comm

lemma dot_product_comm [comm_semiring α] (v w : m → α) :
  dot_product v w = dot_product w v :=
by simp_rw [dot_product, mul_comm]

@[simp] lemma dot_product_punit [add_comm_monoid α] [has_mul α] (v w : punit → α) :
  dot_product v w = v ⟨⟩ * w ⟨⟩ :=
by simp [dot_product]

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring α] (u v w : m → α)

@[simp] lemma dot_product_zero : dot_product v 0 = 0 := by simp [dot_product]

@[simp] lemma dot_product_zero' : dot_product v (λ _, 0) = 0 := dot_product_zero v

@[simp] lemma zero_dot_product : dot_product 0 v = 0 := by simp [dot_product]

@[simp] lemma zero_dot_product' : dot_product (λ _, (0 : α)) v = 0 := zero_dot_product v

@[simp] lemma add_dot_product : dot_product (u + v) w = dot_product u w + dot_product v w :=
by simp [dot_product, add_mul, finset.sum_add_distrib]

@[simp] lemma dot_product_add : dot_product u (v + w) = dot_product u v + dot_product u w :=
by simp [dot_product, mul_add, finset.sum_add_distrib]

end non_unital_non_assoc_semiring

section non_unital_non_assoc_semiring_decidable
variables [decidable_eq m] [non_unital_non_assoc_semiring α] (u v w : m → α)

@[simp] lemma diagonal_dot_product (i : m) : dot_product (diagonal v i) w = v i * w i :=
have ∀ j ≠ i, diagonal v i j * w j = 0 := λ j hij, by simp [diagonal_apply_ne' hij],
by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

@[simp] lemma dot_product_diagonal (i : m) : dot_product v (diagonal w i) = v i * w i :=
have ∀ j ≠ i, v j * diagonal w i j = 0 := λ j hij, by simp [diagonal_apply_ne' hij],
by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

@[simp] lemma dot_product_diagonal' (i : m) : dot_product v (λ j, diagonal w j i) = v i * w i :=
have ∀ j ≠ i, v j * diagonal w j i = 0 := λ j hij, by simp [diagonal_apply_ne hij],
by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

@[simp] lemma single_dot_product (x : α) (i : m) : dot_product (pi.single i x) v = x * v i :=
have ∀ j ≠ i, pi.single i x j * v j = 0 := λ j hij, by simp [pi.single_eq_of_ne hij],
by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

@[simp] lemma dot_product_single (x : α) (i : m) : dot_product v (pi.single i x) = v i * x :=
have ∀ j ≠ i, v j * pi.single i x j = 0 := λ j hij, by simp [pi.single_eq_of_ne hij],
by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

end non_unital_non_assoc_semiring_decidable

section ring
variables [ring α] (u v w : m → α)

@[simp] lemma neg_dot_product : dot_product (-v) w = - dot_product v w := by simp [dot_product]

@[simp] lemma dot_product_neg : dot_product v (-w) = - dot_product v w := by simp [dot_product]

@[simp] lemma sub_dot_product : dot_product (u - v) w = dot_product u w - dot_product v w :=
by simp [sub_eq_add_neg]

@[simp] lemma dot_product_sub : dot_product u (v - w) = dot_product u v - dot_product u w :=
by simp [sub_eq_add_neg]

end ring

section distrib_mul_action
variables [monoid R] [has_mul α] [add_comm_monoid α] [distrib_mul_action R α]

@[simp] lemma smul_dot_product [is_scalar_tower R α α] (x : R) (v w : m → α) :
  dot_product (x • v) w = x • dot_product v w :=
by simp [dot_product, finset.smul_sum, smul_mul_assoc]

@[simp] lemma dot_product_smul [smul_comm_class R α α] (x : R) (v w : m → α)  :
  dot_product v (x • w) = x • dot_product v w :=
by simp [dot_product, finset.smul_sum, mul_smul_comm]

end distrib_mul_action

section star_ring
variables [semiring α] [star_ring α] (v w : m → α)

lemma star_dot_product_star : dot_product (star v) (star w) = star (dot_product w v) :=
by simp [dot_product]

lemma star_dot_product : dot_product (star v) w = star (dot_product (star w) v) :=
by simp [dot_product]

lemma dot_product_star : dot_product v (star w) = star (dot_product w (star v)) :=
by simp [dot_product]

end star_ring

end dot_product

/-- `M ⬝ N` is the usual product of matrices `M` and `N`, i.e. we have that
`(M ⬝ N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `N`.
This is currently only defined when `m` is finite. -/
protected def mul [fintype m] [has_mul α] [add_comm_monoid α]
  (M : matrix l m α) (N : matrix m n α) : matrix l n α :=
λ i k, dot_product (λ j, M i j) (λ j, N j k)

localized "infixl ` ⬝ `:75 := matrix.mul" in matrix

theorem mul_apply [fintype m] [has_mul α] [add_comm_monoid α]
  {M : matrix l m α} {N : matrix m n α} {i k} : (M ⬝ N) i k = ∑ j, M i j * N j k := rfl

instance [fintype n] [has_mul α] [add_comm_monoid α] : has_mul (matrix n n α) := ⟨matrix.mul⟩

@[simp] theorem mul_eq_mul [fintype n] [has_mul α] [add_comm_monoid α] (M N : matrix n n α) :
  M * N = M ⬝ N := rfl

theorem mul_apply' [fintype m] [has_mul α] [add_comm_monoid α]
  {M : matrix l m α} {N : matrix m n α} {i k} : (M ⬝ N) i k = dot_product (λ j, M i j) (λ j, N j k)
  := rfl

@[simp] theorem diagonal_neg [decidable_eq n] [add_group α] (d : n → α) :
  -diagonal d = diagonal (λ i, -d i) :=
((diagonal_add_monoid_hom n α).map_neg d).symm

lemma sum_apply [add_comm_monoid α] (i : m) (j : n)
  (s : finset β) (g : β → matrix m n α) :
  (∑ c in s, g c) i j = ∑ c in s, g c i j :=
(congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring α]

@[simp] protected theorem mul_zero [fintype n] (M : matrix m n α) : M ⬝ (0 : matrix n o α) = 0 :=
by { ext i j, apply dot_product_zero }

@[simp] protected theorem zero_mul [fintype m] (M : matrix m n α) : (0 : matrix l m α) ⬝ M = 0 :=
by { ext i j, apply zero_dot_product }

protected theorem mul_add [fintype n] (L : matrix m n α) (M N : matrix n o α) :
  L ⬝ (M + N) = L ⬝ M + L ⬝ N := by { ext i j, apply dot_product_add }

protected theorem add_mul [fintype m] (L M : matrix l m α) (N : matrix m n α) :
  (L + M) ⬝ N = L ⬝ N + M ⬝ N := by { ext i j, apply add_dot_product }

instance [fintype n] : non_unital_non_assoc_semiring (matrix n n α) :=
{ mul := (*),
  add := (+),
  zero := 0,
  mul_zero := matrix.mul_zero,
  zero_mul := matrix.zero_mul,
  left_distrib := matrix.mul_add,
  right_distrib := matrix.add_mul,
  .. matrix.add_comm_monoid}

@[simp] theorem diagonal_mul [fintype m] [decidable_eq m]
  (d : m → α) (M : matrix m n α) (i j) : (diagonal d).mul M i j = d i * M i j :=
diagonal_dot_product _ _ _

@[simp] theorem mul_diagonal [fintype n] [decidable_eq n]
  (d : n → α) (M : matrix m n α) (i j) : (M ⬝ diagonal d) i j = M i j * d j :=
by { rw ← diagonal_transpose, apply dot_product_diagonal }

@[simp] theorem diagonal_mul_diagonal [fintype n] [decidable_eq n] (d₁ d₂ : n → α) :
  (diagonal d₁) ⬝ (diagonal d₂) = diagonal (λ i, d₁ i * d₂ i) :=
by ext i j; by_cases i = j; simp [h]

theorem diagonal_mul_diagonal' [fintype n] [decidable_eq n] (d₁ d₂ : n → α) :
  diagonal d₁ * diagonal d₂ = diagonal (λ i, d₁ i * d₂ i) :=
diagonal_mul_diagonal _ _

/-- Left multiplication by a matrix, as an `add_monoid_hom` from matrices to matrices. -/
@[simps] def add_monoid_hom_mul_left [fintype m] (M : matrix l m α) :
  matrix m n α →+ matrix l n α :=
{ to_fun := λ x, M ⬝ x,
  map_zero' := matrix.mul_zero _,
  map_add' := matrix.mul_add _ }

/-- Right multiplication by a matrix, as an `add_monoid_hom` from matrices to matrices. -/
@[simps] def add_monoid_hom_mul_right [fintype m] (M : matrix m n α) :
  matrix l m α →+ matrix l n α :=
{ to_fun := λ x, x ⬝ M,
  map_zero' := matrix.zero_mul _,
  map_add' := λ _ _, matrix.add_mul _ _ _ }

protected lemma sum_mul [fintype m] (s : finset β) (f : β → matrix l m α)
  (M : matrix m n α) : (∑ a in s, f a) ⬝ M = ∑ a in s, f a ⬝ M :=
(add_monoid_hom_mul_right M : matrix l m α →+ _).map_sum f s

protected lemma mul_sum [fintype m] (s : finset β) (f : β → matrix m n α)
  (M : matrix l m α) : M ⬝ ∑ a in s, f a = ∑ a in s, M ⬝ f a :=
(add_monoid_hom_mul_left M : matrix m n α →+ _).map_sum f s

end non_unital_non_assoc_semiring

section non_assoc_semiring
variables [non_assoc_semiring α]

@[simp] protected theorem one_mul [fintype m] [decidable_eq m] (M : matrix m n α) :
  (1 : matrix m m α) ⬝ M = M :=
by ext i j; rw [← diagonal_one, diagonal_mul, one_mul]

@[simp] protected theorem mul_one [fintype n] [decidable_eq n] (M : matrix m n α) :
  M ⬝ (1 : matrix n n α) = M :=
by ext i j; rw [← diagonal_one, mul_diagonal, mul_one]

instance [fintype n] [decidable_eq n] : non_assoc_semiring (matrix n n α) :=
{ one := 1,
  one_mul := matrix.one_mul,
  mul_one := matrix.mul_one,
  .. matrix.non_unital_non_assoc_semiring }

@[simp]
lemma map_mul [fintype n] {L : matrix m n α} {M : matrix n o α} [non_assoc_semiring β]
  {f : α →+* β} : (L ⬝ M).map f = L.map f ⬝ M.map f :=
by { ext, simp [mul_apply, ring_hom.map_sum], }

variables (α n)

/-- `matrix.diagonal` as a `ring_hom`. -/
@[simps]
def diagonal_ring_hom [fintype n] [decidable_eq n] : (n → α) →+* matrix n n α :=
{ to_fun := diagonal,
  map_one' := diagonal_one,
  map_mul' := λ _ _, (diagonal_mul_diagonal' _ _).symm,
  .. diagonal_add_monoid_hom n α }

end non_assoc_semiring

section non_unital_semiring
variables [non_unital_semiring α] [fintype m] [fintype n]

protected theorem mul_assoc (L : matrix l m α) (M : matrix m n α) (N : matrix n o α) :
  (L ⬝ M) ⬝ N = L ⬝ (M ⬝ N) :=
by { ext, apply dot_product_assoc }

instance : non_unital_semiring (matrix n n α) :=
{ mul_assoc := matrix.mul_assoc, ..matrix.non_unital_non_assoc_semiring }

end non_unital_semiring

section semiring
variables [semiring α]

instance [fintype n] [decidable_eq n] : semiring (matrix n n α) :=
{ ..matrix.non_unital_semiring, ..matrix.non_assoc_semiring }

end semiring

section ring
variables [ring α] [fintype n]

@[simp] theorem neg_mul (M : matrix m n α) (N : matrix n o α) :
  (-M) ⬝ N = -(M ⬝ N) :=
by { ext, apply neg_dot_product }

@[simp] theorem mul_neg (M : matrix m n α) (N : matrix n o α) :
  M ⬝ (-N) = -(M ⬝ N) :=
by { ext, apply dot_product_neg }

protected theorem sub_mul (M M' : matrix m n α) (N : matrix n o α) :
  (M - M') ⬝ N = M ⬝ N - M' ⬝ N :=
by rw [sub_eq_add_neg, matrix.add_mul, neg_mul, sub_eq_add_neg]

protected theorem mul_sub (M : matrix m n α) (N N' : matrix n o α) :
  M ⬝ (N - N') = M ⬝ N - M ⬝ N' :=
by rw [sub_eq_add_neg, matrix.mul_add, mul_neg, sub_eq_add_neg]

end ring

instance [fintype n] [decidable_eq n] [ring α] : ring (matrix n n α) :=
{ ..matrix.semiring, ..matrix.add_comm_group }

section semiring
variables [semiring α]

lemma smul_eq_diagonal_mul [fintype m] [decidable_eq m] (M : matrix m n α) (a : α) :
  a • M = diagonal (λ _, a) ⬝ M :=
by { ext, simp }

@[simp] lemma smul_mul [fintype n] [monoid R] [distrib_mul_action R α] [is_scalar_tower R α α]
  (a : R) (M : matrix m n α) (N : matrix n l α) :
  (a • M) ⬝ N = a • M ⬝ N :=
by { ext, apply smul_dot_product }

/-- This instance enables use with `smul_mul_assoc`. -/
instance semiring.is_scalar_tower [fintype n] [monoid R] [distrib_mul_action R α]
  [is_scalar_tower R α α] : is_scalar_tower R (matrix n n α) (matrix n n α) :=
⟨λ r m n, matrix.smul_mul r m n⟩

@[simp] lemma mul_smul [fintype n] [monoid R] [distrib_mul_action R α] [smul_comm_class R α α]
  (M : matrix m n α) (a : R) (N : matrix n l α) : M ⬝ (a • N) = a • M ⬝ N :=
by { ext, apply dot_product_smul }

/-- This instance enables use with `mul_smul_comm`. -/
instance semiring.smul_comm_class [fintype n] [monoid R] [distrib_mul_action R α]
  [smul_comm_class R α α] : smul_comm_class R (matrix n n α) (matrix n n α) :=
⟨λ r m n, (matrix.mul_smul m r n).symm⟩

@[simp] lemma mul_mul_left [fintype n] (M : matrix m n α) (N : matrix n o α) (a : α) :
  (λ i j, a * M i j) ⬝ N = a • (M ⬝ N) :=
smul_mul a M N

/--
The ring homomorphism `α →+* matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [decidable_eq n] [fintype n] : α →+* matrix n n α :=
{ to_fun := λ a, a • 1,
  map_one' := by simp,
  map_mul' := by { intros, ext, simp [mul_assoc], },
  .. (smul_add_hom α _).flip (1 : matrix n n α) }

section scalar

variables [decidable_eq n] [fintype n]

@[simp] lemma coe_scalar : (scalar n : α → matrix n n α) = λ a, a • 1 := rfl

lemma scalar_apply_eq (a : α) (i : n) :
  scalar n a i i = a :=
by simp only [coe_scalar, smul_eq_mul, mul_one, one_apply_eq, pi.smul_apply]

lemma scalar_apply_ne (a : α) (i j : n) (h : i ≠ j) :
  scalar n a i j = 0 :=
by simp only [h, coe_scalar, one_apply_ne, ne.def, not_false_iff, pi.smul_apply, smul_zero]

lemma scalar_inj [nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s :=
begin
  split,
  { intro h,
    inhabit n,
    rw [← scalar_apply_eq r (arbitrary n), ← scalar_apply_eq s (arbitrary n), h] },
  { rintro rfl, refl }
end

end scalar

end semiring

section comm_semiring
variables [comm_semiring α] [fintype n]

lemma smul_eq_mul_diagonal [decidable_eq n] (M : matrix m n α) (a : α) :
  a • M = M ⬝ diagonal (λ _, a) :=
by { ext, simp [mul_comm] }

@[simp] lemma mul_mul_right (M : matrix m n α) (N : matrix n o α) (a : α) :
  M ⬝ (λ i j, a * N i j) = a • (M ⬝ N) :=
mul_smul M a N

lemma scalar.commute [decidable_eq n] (r : α) (M : matrix n n α) : commute (scalar n r) M :=
by simp [commute, semiconj_by]

end comm_semiring

section algebra
variables [fintype n] [decidable_eq n]
variables [comm_semiring R] [semiring α] [semiring β] [algebra R α] [algebra R β]

instance : algebra R (matrix n n α) :=
{ commutes' := λ r x, begin
    ext, simp [matrix.scalar, matrix.mul_apply, matrix.one_apply, algebra.commutes, smul_ite], end,
  smul_def' := λ r x, begin ext, simp [matrix.scalar, algebra.smul_def'' r], end,
  ..((matrix.scalar n).comp (algebra_map R α)) }

lemma algebra_map_matrix_apply {r : R} {i j : n} :
  algebra_map R (matrix n n α) r i j = if i = j then algebra_map R α r else 0 :=
begin
  dsimp [algebra_map, algebra.to_ring_hom, matrix.scalar],
  split_ifs with h; simp [h, matrix.one_apply_ne],
end

lemma algebra_map_eq_diagonal (r : R) :
  algebra_map R (matrix n n α) r = diagonal (algebra_map R (n → α) r) :=
matrix.ext $ λ i j, algebra_map_matrix_apply

@[simp] lemma algebra_map_eq_smul (r : R) :
  algebra_map R (matrix n n R) r = r • (1 : matrix n n R) := rfl

lemma algebra_map_eq_diagonal_ring_hom :
  algebra_map R (matrix n n α) = (diagonal_ring_hom n α).comp (algebra_map R _) :=
ring_hom.ext algebra_map_eq_diagonal

@[simp] lemma map_algebra_map (r : R) (f : α → β) (hf : f 0 = 0)
  (hf₂ : f (algebra_map R α r) = algebra_map R β r) :
  (algebra_map R (matrix n n α) r).map f = algebra_map R (matrix n n β) r :=
begin
  rw [algebra_map_eq_diagonal, algebra_map_eq_diagonal, diagonal_map hf],
  congr' 1 with x,
  simp only [hf₂, pi.algebra_map_apply]
end

variables (R)

/-- `matrix.diagonal` as an `alg_hom`. -/
@[simps]
def diagonal_alg_hom : (n → α) →ₐ[R] matrix n n α :=
{ to_fun := diagonal,
  commutes' := λ r, (algebra_map_eq_diagonal r).symm,
  .. diagonal_ring_hom n α }

end algebra

end matrix

/-!
### Bundled versions of `matrix.map`
-/

namespace equiv

/-- The `equiv` between spaces of matrices induced by an `equiv` between their
coefficients. This is `matrix.map` as an `equiv`. -/
@[simps apply]
def map_matrix (f : α ≃ β) : matrix m n α ≃ matrix m n β :=
{ to_fun := λ M, M.map f,
  inv_fun := λ M, M.map f.symm,
  left_inv := λ M, matrix.ext $ λ _ _, f.symm_apply_apply _,
  right_inv := λ M, matrix.ext $ λ _ _, f.apply_symm_apply _, }

@[simp] lemma map_matrix_refl : (equiv.refl α).map_matrix = equiv.refl (matrix m n α) :=
rfl

@[simp] lemma map_matrix_symm (f : α ≃ β) :
  f.map_matrix.symm = (f.symm.map_matrix : matrix m n β ≃ _) :=
rfl

@[simp] lemma map_matrix_trans (f : α ≃ β) (g : β ≃ γ) :
  f.map_matrix.trans g.map_matrix = ((f.trans g).map_matrix : matrix m n α ≃ _) :=
rfl

end equiv

namespace add_monoid_hom
variables [add_zero_class α] [add_zero_class β] [add_zero_class γ]

/-- The `add_monoid_hom` between spaces of matrices induced by an `add_monoid_hom` between their
coefficients. This is `matrix.map` as an `add_monoid_hom`. -/
@[simps]
def map_matrix (f : α →+ β) : matrix m n α →+ matrix m n β :=
{ to_fun := λ M, M.map f,
  map_zero' := matrix.map_zero f f.map_zero,
  map_add' := matrix.map_add f f.map_add }

@[simp] lemma map_matrix_id : (add_monoid_hom.id α).map_matrix = add_monoid_hom.id (matrix m n α) :=
rfl

@[simp] lemma map_matrix_comp (f : β →+ γ) (g : α →+ β) :
  f.map_matrix.comp g.map_matrix = ((f.comp g).map_matrix : matrix m n α →+ _) :=
rfl

end add_monoid_hom

namespace add_equiv
variables [has_add α] [has_add β] [has_add γ]

/-- The `add_equiv` between spaces of matrices induced by an `add_equiv` between their
coefficients. This is `matrix.map` as an `add_equiv`. -/
@[simps apply]
def map_matrix (f : α ≃+ β) : matrix m n α ≃+ matrix m n β :=
{ to_fun := λ M, M.map f,
  inv_fun := λ M, M.map f.symm,
  map_add' := matrix.map_add f f.map_add,
  .. f.to_equiv.map_matrix }

@[simp] lemma map_matrix_refl : (add_equiv.refl α).map_matrix = add_equiv.refl (matrix m n α) :=
rfl

@[simp] lemma map_matrix_symm (f : α ≃+ β) :
  f.map_matrix.symm = (f.symm.map_matrix : matrix m n β ≃+ _) :=
rfl

@[simp] lemma map_matrix_trans (f : α ≃+ β) (g : β ≃+ γ) :
  f.map_matrix.trans g.map_matrix = ((f.trans g).map_matrix : matrix m n α ≃+ _) :=
rfl

end add_equiv

namespace linear_map
variables [semiring R] [add_comm_monoid α] [add_comm_monoid β] [add_comm_monoid γ]
variables [module R α] [module R β] [module R γ]

/-- The `linear_map` between spaces of matrices induced by a `linear_map` between their
coefficients. This is `matrix.map` as a `linear_map`. -/
@[simps]
def map_matrix (f : α →ₗ[R] β) : matrix m n α →ₗ[R] matrix m n β :=
{ to_fun := λ M, M.map f,
  map_add' := matrix.map_add f f.map_add,
  map_smul' := λ r, matrix.map_smul f r (f.map_smul r), }

@[simp] lemma map_matrix_id : linear_map.id.map_matrix = (linear_map.id : matrix m n α →ₗ[R] _) :=
rfl

@[simp] lemma map_matrix_comp (f : β →ₗ[R] γ) (g : α →ₗ[R] β) :
  f.map_matrix.comp g.map_matrix = ((f.comp g).map_matrix : matrix m n α →ₗ[R] _) :=
rfl

end linear_map

namespace linear_equiv
variables [semiring R] [add_comm_monoid α] [add_comm_monoid β] [add_comm_monoid γ]
variables [module R α] [module R β] [module R γ]

/-- The `linear_equiv` between spaces of matrices induced by an `linear_equiv` between their
coefficients. This is `matrix.map` as an `linear_equiv`. -/
@[simps apply]
def map_matrix (f : α ≃ₗ[R] β) : matrix m n α ≃ₗ[R] matrix m n β :=
{ to_fun := λ M, M.map f,
  inv_fun := λ M, M.map f.symm,
  .. f.to_equiv.map_matrix,
  .. f.to_linear_map.map_matrix }

@[simp] lemma map_matrix_refl :
  (linear_equiv.refl R α).map_matrix = linear_equiv.refl R (matrix m n α) :=
rfl

@[simp] lemma map_matrix_symm (f : α ≃ₗ[R] β) :
  f.map_matrix.symm = (f.symm.map_matrix : matrix m n β ≃ₗ[R] _) :=
rfl

@[simp] lemma map_matrix_trans (f : α ≃ₗ[R] β) (g : β ≃ₗ[R] γ) :
  f.map_matrix.trans g.map_matrix = ((f.trans g).map_matrix : matrix m n α ≃ₗ[R] _) :=
rfl

end linear_equiv

namespace ring_hom
variables [fintype m] [decidable_eq m]
variables [non_assoc_semiring α] [non_assoc_semiring β] [non_assoc_semiring γ]

/-- The `ring_hom` between spaces of square matrices induced by a `ring_hom` between their
coefficients. This is `matrix.map` as a `ring_hom`. -/
@[simps]
def map_matrix (f : α →+* β) : matrix m m α →+* matrix m m β :=
{ to_fun := λ M, M.map f,
  map_one' := by simp,
  map_mul' := λ L M, matrix.map_mul,
  .. f.to_add_monoid_hom.map_matrix }

@[simp] lemma map_matrix_id : (ring_hom.id α).map_matrix = ring_hom.id (matrix m m α) :=
rfl

@[simp] lemma map_matrix_comp (f : β →+* γ) (g : α →+* β) :
  f.map_matrix.comp g.map_matrix = ((f.comp g).map_matrix : matrix m m α →+* _) :=
rfl

end ring_hom

namespace ring_equiv
variables [fintype m] [decidable_eq m]
variables [non_assoc_semiring α] [non_assoc_semiring β] [non_assoc_semiring γ]

/-- The `ring_equiv` between spaces of square matrices induced by a `ring_equiv` between their
coefficients. This is `matrix.map` as a `ring_equiv`. -/
@[simps apply]
def map_matrix (f : α ≃+* β) : matrix m m α ≃+* matrix m m β :=
{ to_fun := λ M, M.map f,
  inv_fun := λ M, M.map f.symm,
  .. f.to_ring_hom.map_matrix,
  .. f.to_add_equiv.map_matrix }

@[simp] lemma map_matrix_refl :
  (ring_equiv.refl α).map_matrix = ring_equiv.refl (matrix m m α) :=
rfl

@[simp] lemma map_matrix_symm (f : α ≃+* β) :
  f.map_matrix.symm = (f.symm.map_matrix : matrix m m β ≃+* _) :=
rfl

@[simp] lemma map_matrix_trans (f : α ≃+* β) (g : β ≃+* γ) :
  f.map_matrix.trans g.map_matrix = ((f.trans g).map_matrix : matrix m m α ≃+* _) :=
rfl

end ring_equiv

namespace alg_hom
variables [fintype m] [decidable_eq m]
variables [comm_semiring R] [semiring α] [semiring β] [semiring γ]
variables [algebra R α] [algebra R β] [algebra R γ]

/-- The `alg_hom` between spaces of square matrices induced by a `alg_hom` between their
coefficients. This is `matrix.map` as a `alg_hom`. -/
@[simps]
def map_matrix (f : α →ₐ[R] β) : matrix m m α →ₐ[R] matrix m m β :=
{ to_fun := λ M, M.map f,
  commutes' := λ r, matrix.map_algebra_map r f f.map_zero (f.commutes r),
  .. f.to_ring_hom.map_matrix }

@[simp] lemma map_matrix_id : (alg_hom.id R α).map_matrix = alg_hom.id R (matrix m m α) :=
rfl

@[simp] lemma map_matrix_comp (f : β →ₐ[R] γ) (g : α →ₐ[R] β) :
  f.map_matrix.comp g.map_matrix = ((f.comp g).map_matrix : matrix m m α →ₐ[R] _) :=
rfl

end alg_hom

namespace alg_equiv
variables [fintype m] [decidable_eq m]
variables [comm_semiring R] [semiring α] [semiring β] [semiring γ]
variables [algebra R α] [algebra R β] [algebra R γ]

/-- The `alg_equiv` between spaces of square matrices induced by a `alg_equiv` between their
coefficients. This is `matrix.map` as a `alg_equiv`. -/
@[simps apply]
def map_matrix (f : α ≃ₐ[R] β) : matrix m m α ≃ₐ[R] matrix m m β :=
{ to_fun := λ M, M.map f,
  inv_fun := λ M, M.map f.symm,
  .. f.to_alg_hom.map_matrix,
  .. f.to_ring_equiv.map_matrix }

@[simp] lemma map_matrix_refl :
  alg_equiv.refl.map_matrix = (alg_equiv.refl : matrix m m α ≃ₐ[R] _) :=
rfl

@[simp] lemma map_matrix_symm (f : α ≃ₐ[R] β) :
  f.map_matrix.symm = (f.symm.map_matrix : matrix m m β ≃ₐ[R] _) :=
rfl

@[simp] lemma map_matrix_trans (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ) :
  f.map_matrix.trans g.map_matrix = ((f.trans g).map_matrix : matrix m m α ≃ₐ[R] _) :=
rfl

end alg_equiv

open_locale matrix

namespace matrix

/-- For two vectors `w` and `v`, `vec_mul_vec w v i j` is defined to be `w i * v j`.
    Put another way, `vec_mul_vec w v` is exactly `col w ⬝ row v`. -/
def vec_mul_vec [has_mul α] (w : m → α) (v : n → α) : matrix m n α
| x y := w x * v y

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring α]

/-- `mul_vec M v` is the matrix-vector product of `M` and `v`, where `v` is seen as a column matrix.
    Put another way, `mul_vec M v` is the vector whose entries
    are those of `M ⬝ col v` (see `col_mul_vec`). -/
def mul_vec [fintype n] (M : matrix m n α) (v : n → α) : m → α
| i := dot_product (λ j, M i j) v

/-- `vec_mul v M` is the vector-matrix product of `v` and `M`, where `v` is seen as a row matrix.
    Put another way, `vec_mul v M` is the vector whose entries
    are those of `row v ⬝ M` (see `row_vec_mul`). -/
def vec_mul [fintype m] (v : m → α) (M : matrix m n α) : n → α
| j := dot_product v (λ i, M i j)

/-- Left multiplication by a matrix, as an `add_monoid_hom` from vectors to vectors. -/
@[simps] def mul_vec.add_monoid_hom_left [fintype n] (v : n → α) : matrix m n α →+ m → α :=
{ to_fun := λ M, mul_vec M v,
  map_zero' := by ext; simp [mul_vec]; refl,
  map_add' := λ x y, by { ext m, apply add_dot_product } }

lemma mul_vec_diagonal [fintype m] [decidable_eq m] (v w : m → α) (x : m) :
  mul_vec (diagonal v) w x = v x * w x :=
diagonal_dot_product v w x

lemma vec_mul_diagonal [fintype m] [decidable_eq m] (v w : m → α) (x : m) :
  vec_mul v (diagonal w) x = v x * w x :=
dot_product_diagonal' v w x

/-- Associate the dot product of `mul_vec` to the left. -/
lemma dot_product_mul_vec [fintype n] [fintype m] [non_unital_semiring R]
  (v : m → R) (A : matrix m n R) (w : n → R) :
  dot_product v (mul_vec A w) = dot_product (vec_mul v A) w :=
by simp only [dot_product, vec_mul, mul_vec, finset.mul_sum, finset.sum_mul, mul_assoc];
   exact finset.sum_comm

@[simp] lemma mul_vec_zero [fintype n] (A : matrix m n α) : mul_vec A 0 = 0 :=
by { ext, simp [mul_vec] }

@[simp] lemma zero_vec_mul [fintype m] (A : matrix m n α) : vec_mul 0 A = 0 :=
by { ext, simp [vec_mul] }

@[simp] lemma zero_mul_vec [fintype n] (v : n → α) : mul_vec (0 : matrix m n α) v = 0 :=
by { ext, simp [mul_vec] }

@[simp] lemma vec_mul_zero [fintype m] (v : m → α) : vec_mul v (0 : matrix m n α) = 0 :=
by { ext, simp [vec_mul] }

lemma vec_mul_vec_eq (w : m → α) (v : n → α) :
  vec_mul_vec w v = (col w) ⬝ (row v) :=
by { ext i j, simp [vec_mul_vec, mul_apply], refl }

lemma smul_mul_vec_assoc [fintype n] [monoid R] [distrib_mul_action R α] [is_scalar_tower R α α]
  (a : R) (A : matrix m n α) (b : n → α) :
  (a • A).mul_vec b = a • (A.mul_vec b) :=
by { ext, apply smul_dot_product, }

lemma mul_vec_add [fintype n] (A : matrix m n α) (x y : n → α) :
  A.mul_vec (x + y) = A.mul_vec x + A.mul_vec y :=
by { ext, apply dot_product_add }

lemma add_mul_vec [fintype n] (A B : matrix m n α) (x : n → α) :
  (A + B).mul_vec x = A.mul_vec x + B.mul_vec x :=
by { ext, apply add_dot_product }

lemma vec_mul_add [fintype m] (A B : matrix m n α) (x : m → α) :
  vec_mul x (A + B) = vec_mul x A + vec_mul x B :=
by { ext, apply dot_product_add }

lemma add_vec_mul [fintype m] (A : matrix m n α) (x y : m → α) :
  vec_mul (x + y) A = vec_mul x A + vec_mul y A :=
by { ext, apply add_dot_product }

lemma vec_mul_smul [fintype n] [comm_semiring R] [semiring S] [algebra R S]
  (M : matrix n m S) (b : R) (v : n → S)  :
  M.vec_mul (b • v) = b • M.vec_mul v :=
by { ext i, simp only [vec_mul, dot_product, finset.smul_sum, pi.smul_apply, smul_mul_assoc] }

lemma mul_vec_smul [fintype n] [comm_semiring R] [semiring S] [algebra R S]
  (M : matrix m n S) (b : R) (v : n → S)  :
  M.mul_vec (b • v) = b • M.mul_vec v :=
by { ext i, simp only [mul_vec, dot_product, finset.smul_sum, pi.smul_apply, mul_smul_comm] }

end non_unital_non_assoc_semiring

section non_unital_semiring
variables [non_unital_semiring α] [fintype n]

@[simp] lemma vec_mul_vec_mul [fintype m] (v : m → α) (M : matrix m n α) (N : matrix n o α) :
  vec_mul (vec_mul v M) N = vec_mul v (M ⬝ N) :=
by { ext, apply dot_product_assoc }

@[simp] lemma mul_vec_mul_vec [fintype o] (v : o → α) (M : matrix m n α) (N : matrix n o α) :
  mul_vec M (mul_vec N v) = mul_vec (M ⬝ N) v :=
by { ext, symmetry, apply dot_product_assoc }

end non_unital_semiring

section non_assoc_semiring
variables [fintype m] [decidable_eq m] [non_assoc_semiring α]

@[simp] lemma one_mul_vec (v : m → α) : mul_vec 1 v = v :=
by { ext, rw [←diagonal_one, mul_vec_diagonal, one_mul] }

@[simp] lemma vec_mul_one (v : m → α) : vec_mul v 1 = v :=
by { ext, rw [←diagonal_one, vec_mul_diagonal, mul_one] }

end non_assoc_semiring

section ring

variables [ring α]

lemma neg_vec_mul [fintype m] (v : m → α) (A : matrix m n α) : vec_mul (-v) A = - vec_mul v A :=
by { ext, apply neg_dot_product }

lemma vec_mul_neg [fintype m] (v : m → α) (A : matrix m n α) : vec_mul v (-A) = - vec_mul v A :=
by { ext, apply dot_product_neg }

lemma neg_mul_vec [fintype n] (v : n → α) (A : matrix m n α) : mul_vec (-A) v = - mul_vec A v :=
by { ext, apply neg_dot_product }

lemma mul_vec_neg [fintype n] (v : n → α) (A : matrix m n α) : mul_vec A (-v) = - mul_vec A v :=
by { ext, apply dot_product_neg }

end ring

section comm_semiring

variables [comm_semiring α]

lemma mul_vec_smul_assoc [fintype n] (A : matrix m n α) (b : n → α) (a : α) :
  A.mul_vec (a • b) = a • (A.mul_vec b) :=
by { ext, apply dot_product_smul }

lemma mul_vec_transpose [fintype m] (A : matrix m n α) (x : m → α) :
  mul_vec Aᵀ x = vec_mul x A :=
by { ext, apply dot_product_comm }

lemma vec_mul_transpose [fintype n] (A : matrix m n α) (x : n → α) :
  vec_mul x Aᵀ = mul_vec A x :=
by { ext, apply dot_product_comm }

end comm_semiring

section transpose

open_locale matrix

/--
  Tell `simp` what the entries are in a transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp] lemma transpose_apply (M : matrix m n α) (i j) : M.transpose j i = M i j := rfl

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
  { simp only [h, diagonal_apply_eq] },
  { simp only [diagonal_apply_ne h, diagonal_apply_ne (λ p, h (symm p))] }
end

@[simp] lemma transpose_add [has_add α] (M : matrix m n α) (N : matrix m n α) :
  (M + N)ᵀ = Mᵀ + Nᵀ  :=
by { ext i j, simp }

@[simp] lemma transpose_sub [has_sub α] (M : matrix m n α) (N : matrix m n α) :
  (M - N)ᵀ = Mᵀ - Nᵀ  :=
by { ext i j, simp }

@[simp] lemma transpose_mul [comm_semiring α] [fintype n] (M : matrix m n α) (N : matrix n l α) :
  (M ⬝ N)ᵀ = Nᵀ ⬝ Mᵀ  :=
begin
  ext i j,
  apply dot_product_comm
end

@[simp] lemma transpose_smul {R : Type*} [has_scalar R α] (c : R) (M : matrix m n α) :
  (c • M)ᵀ = c • Mᵀ :=
by { ext i j, refl }

@[simp] lemma transpose_neg [has_neg α] (M : matrix m n α) :
  (- M)ᵀ = - Mᵀ  :=
by ext i j; refl

lemma transpose_map {f : α → β} {M : matrix m n α} : Mᵀ.map f = (M.map f)ᵀ :=
by { ext, refl }

end transpose

section conj_transpose

open_locale matrix

/--
  Tell `simp` what the entries are in a conjugate transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp] lemma conj_transpose_apply [has_star α] (M : matrix m n α) (i j) :
  M.conj_transpose j i = star (M i j) := rfl

@[simp] lemma conj_transpose_conj_transpose [has_involutive_star α] (M : matrix m n α) :
  Mᴴᴴ = M :=
by ext; simp

@[simp] lemma conj_transpose_zero [semiring α] [star_ring α] : (0 : matrix m n α)ᴴ = 0 :=
by ext i j; simp

@[simp] lemma conj_transpose_one [decidable_eq n] [semiring α] [star_ring α]:
  (1 : matrix n n α)ᴴ = 1 :=
by simp [conj_transpose]

@[simp] lemma conj_transpose_add
[semiring α] [star_ring α] (M : matrix m n α) (N : matrix m n α) :
  (M + N)ᴴ = Mᴴ + Nᴴ  := by ext i j; simp

@[simp] lemma conj_transpose_sub [ring α] [star_ring α] (M : matrix m n α) (N : matrix m n α) :
  (M - N)ᴴ = Mᴴ - Nᴴ  := by ext i j; simp

@[simp] lemma conj_transpose_smul [comm_monoid α] [star_monoid α] (c : α) (M : matrix m n α) :
  (c • M)ᴴ = (star c) • Mᴴ :=
by ext i j; simp [mul_comm]

@[simp] lemma conj_transpose_mul [fintype n] [semiring α] [star_ring α]
  (M : matrix m n α) (N : matrix n l α) : (M ⬝ N)ᴴ = Nᴴ ⬝ Mᴴ  := by ext i j; simp [mul_apply]

@[simp] lemma conj_transpose_neg [ring α] [star_ring α] (M : matrix m n α) :
  (- M)ᴴ = - Mᴴ  := by ext i j; simp

end conj_transpose

section star

/-- When `α` has a star operation, square matrices `matrix n n α` have a star
operation equal to `matrix.conj_transpose`. -/
instance [has_star α] : has_star (matrix n n α) := {star := conj_transpose}

lemma star_eq_conj_transpose [has_star α] (M : matrix m m α) : star M = Mᴴ := rfl

@[simp] lemma star_apply [has_star α] (M : matrix n n α) (i j) :
  (star M) i j = star (M j i) := rfl

instance [has_involutive_star α] : has_involutive_star (matrix n n α) :=
{ star_involutive := conj_transpose_conj_transpose }

/-- When `α` is a `*`-(semi)ring, `matrix.has_star` is also a `*`-(semi)ring. -/
instance [fintype n] [decidable_eq n] [semiring α] [star_ring α] : star_ring (matrix n n α) :=
{ star_add := conj_transpose_add,
  star_mul := conj_transpose_mul, }

/-- A version of `star_mul` for `⬝` instead of `*`. -/
lemma star_mul [fintype n] [semiring α] [star_ring α] (M N : matrix n n α) :
  star (M ⬝ N) = star N ⬝ star M := conj_transpose_mul _ _

end star

/-- Given maps `(r_reindex : l → m)` and  `(c_reindex : o → n)` reindexing the rows and columns of
a matrix `M : matrix m n α`, the matrix `M.minor r_reindex c_reindex : matrix l o α` is defined
by `(M.minor r_reindex c_reindex) i j = M (r_reindex i) (c_reindex j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved. -/
def minor (A : matrix m n α) (r_reindex : l → m) (c_reindex : o → n) : matrix l o α :=
λ i j, A (r_reindex i) (c_reindex j)

@[simp] lemma minor_apply (A : matrix m n α) (r_reindex : l → m) (c_reindex : o → n) (i j) :
  A.minor r_reindex c_reindex i j = A (r_reindex i) (c_reindex j) := rfl

@[simp] lemma minor_id_id (A : matrix m n α) :
  A.minor id id = A :=
ext $ λ _ _, rfl

@[simp] lemma minor_minor {l₂ o₂ : Type*} (A : matrix m n α)
  (r₁ : l → m) (c₁ : o → n) (r₂ : l₂ → l) (c₂ : o₂ → o) :
  (A.minor r₁ c₁).minor r₂ c₂ = A.minor (r₁ ∘ r₂) (c₁ ∘ c₂) :=
ext $ λ _ _, rfl

@[simp] lemma transpose_minor (A : matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
  (A.minor r_reindex c_reindex)ᵀ = Aᵀ.minor c_reindex r_reindex :=
ext $ λ _ _, rfl

@[simp] lemma conj_transpose_minor
  [has_star α] (A : matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
  (A.minor r_reindex c_reindex)ᴴ = Aᴴ.minor c_reindex r_reindex :=
ext $ λ _ _, rfl

lemma minor_add [has_add α] (A B : matrix m n α) :
  ((A + B).minor : (l → m) → (o → n) → matrix l o α) = A.minor + B.minor := rfl

lemma minor_neg [has_neg α] (A : matrix m n α) :
  ((-A).minor : (l → m) → (o → n) → matrix l o α) = -A.minor := rfl

lemma minor_sub [has_sub α] (A B : matrix m n α) :
  ((A - B).minor : (l → m) → (o → n) → matrix l o α) = A.minor - B.minor := rfl

@[simp]
lemma minor_zero [has_zero α] :
  ((0 : matrix m n α).minor : (l → m) → (o → n) → matrix l o α) = 0 := rfl

lemma minor_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α] (r : R)
  (A : matrix m n α) :
  ((r • A : matrix m n α).minor : (l → m) → (o → n) → matrix l o α) = r • A.minor := rfl

lemma minor_map (f : α → β) (e₁ : l → m) (e₂ : o → n) (A : matrix m n α) :
  (A.map f).minor e₁ e₂ = (A.minor e₁ e₂).map f := rfl

/-- Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexing map `e` is
  injective, then the resulting matrix is again diagonal. -/
lemma minor_diagonal [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α) (e : l → m)
  (he : function.injective e) :
  (diagonal d).minor e e = diagonal (d ∘ e) :=
ext $ λ i j, begin
  rw minor_apply,
  by_cases h : i = j,
  { rw [h, diagonal_apply_eq, diagonal_apply_eq], },
  { rw [diagonal_apply_ne h, diagonal_apply_ne (he.ne h)], },
end

lemma minor_one [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l → m)
  (he : function.injective e) :
  (1 : matrix m m α).minor e e = 1 :=
minor_diagonal _ e he

lemma minor_mul [fintype n] [fintype o] [semiring α] {p q : Type*}
  (M : matrix m n α) (N : matrix n p α)
  (e₁ : l → m) (e₂ : o → n) (e₃ : q → p) (he₂ : function.bijective e₂) :
  (M ⬝ N).minor e₁ e₃ = (M.minor e₁ e₂) ⬝ (N.minor e₂ e₃) :=
ext $ λ _ _, (he₂.sum_comp _).symm


/-! `simp` lemmas for `matrix.minor`s interaction with `matrix.diagonal`, `1`, and `matrix.mul` for
when the mappings are bundled. -/

@[simp]
lemma minor_diagonal_embedding [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α)
  (e : l ↪ m) :
  (diagonal d).minor e e = diagonal (d ∘ e) :=
minor_diagonal d e e.injective

@[simp]
lemma minor_diagonal_equiv [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α)
  (e : l ≃ m) :
  (diagonal d).minor e e = diagonal (d ∘ e) :=
minor_diagonal d e e.injective

@[simp]
lemma minor_one_embedding [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l ↪ m) :
  (1 : matrix m m α).minor e e = 1 :=
minor_one e e.injective

@[simp]
lemma minor_one_equiv [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l ≃ m) :
  (1 : matrix m m α).minor e e = 1 :=
minor_one e e.injective

lemma minor_mul_equiv [fintype n] [fintype o] [semiring α] {p q : Type*}
  (M : matrix m n α) (N : matrix n p α) (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p)  :
  (M ⬝ N).minor e₁ e₃ = (M.minor e₁ e₂) ⬝ (N.minor e₂ e₃) :=
minor_mul M N e₁ e₂ e₃ e₂.bijective

lemma mul_minor_one [fintype n] [fintype o] [semiring α] [decidable_eq o] (e₁ : n ≃ o) (e₂ : l → o)
  (M : matrix m n α) : M ⬝ (1 : matrix o o α).minor e₁ e₂ = minor M id (e₁.symm ∘ e₂) :=
begin
  let A := M.minor id e₁.symm,
  have : M = A.minor id e₁,
  { simp only [minor_minor, function.comp.right_id, minor_id_id, equiv.symm_comp_self], },
  rw [this, ←minor_mul_equiv],
  simp only [matrix.mul_one, minor_minor, function.comp.right_id, minor_id_id,
    equiv.symm_comp_self],
end

lemma one_minor_mul [fintype m] [fintype o] [semiring α] [decidable_eq o] (e₁ : l → o) (e₂ : m ≃ o)
  (M : matrix m n α) : ((1 : matrix o o α).minor e₁ e₂).mul M = minor M (e₂.symm ∘ e₁) id :=
begin
  let A := M.minor e₂.symm id,
  have : M = A.minor e₂ id,
  { simp only [minor_minor, function.comp.right_id, minor_id_id, equiv.symm_comp_self], },
  rw [this, ←minor_mul_equiv],
  simp only [matrix.one_mul, minor_minor, function.comp.right_id, minor_id_id,
    equiv.symm_comp_self],
end

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : matrix m n α ≃ matrix l o α :=
{ to_fun    := λ M, M.minor eₘ.symm eₙ.symm,
  inv_fun   := λ M, M.minor eₘ eₙ,
  left_inv  := λ M, by simp,
  right_inv := λ M, by simp, }

@[simp] lemma reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : matrix m n α) :
  reindex eₘ eₙ M = M.minor eₘ.symm eₙ.symm :=
rfl

@[simp] lemma reindex_refl_refl (A : matrix m n α) :
  reindex (equiv.refl _) (equiv.refl _) A = A :=
A.minor_id_id

@[simp] lemma reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
  (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : matrix l o α ≃ _) :=
rfl

@[simp] lemma reindex_trans {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o)
  (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) : (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) =
    (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : matrix m n α ≃ _) :=
equiv.ext $ λ A, (A.minor_minor eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm : _)

lemma transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : matrix m n α) :
  (reindex eₘ eₙ M)ᵀ = (reindex eₙ eₘ Mᵀ) :=
rfl

lemma conj_transpose_reindex [has_star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : matrix m n α) :
  (reindex eₘ eₙ M)ᴴ = (reindex eₙ eₘ Mᴴ) :=
rfl

/-- The left `n × l` part of a `n × (l+r)` matrix. -/
@[reducible]
def sub_left {m l r : nat} (A : matrix (fin m) (fin (l + r)) α) : matrix (fin m) (fin l) α :=
minor A id (fin.cast_add r)

/-- The right `n × r` part of a `n × (l+r)` matrix. -/
@[reducible]
def sub_right {m l r : nat} (A : matrix (fin m) (fin (l + r)) α) : matrix (fin m) (fin r) α :=
minor A id (fin.nat_add l)

/-- The top `u × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def sub_up {d u n : nat} (A : matrix (fin (u + d)) (fin n) α) : matrix (fin u) (fin n) α :=
minor A (fin.cast_add d) id

/-- The bottom `d × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def sub_down {d u n : nat} (A : matrix (fin (u + d)) (fin n) α) : matrix (fin d) (fin n) α :=
minor A (fin.nat_add u) id

/-- The top-right `u × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def sub_up_right {d u l r : nat} (A: matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin u) (fin r) α :=
sub_up (sub_right A)

/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def sub_down_right {d u l r : nat} (A : matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin d) (fin r) α :=
sub_down (sub_right A)

/-- The top-left `u × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def sub_up_left {d u l r : nat} (A : matrix (fin (u + d)) (fin (l + r)) α) :
  matrix (fin u) (fin (l)) α :=
sub_up (sub_left A)

/-- The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix. -/
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

@[simp] lemma col_add [has_add α] (v w : m → α) : col (v + w) = col v + col w := by { ext, refl }
@[simp] lemma col_smul [has_scalar R α] (x : R) (v : m → α) : col (x • v) = x • col v :=
by { ext, refl }
@[simp] lemma row_add [has_add α] (v w : m → α) : row (v + w) = row v + row w := by { ext, refl }
@[simp] lemma row_smul [has_scalar R α] (x : R) (v : m → α) : row (x • v) = x • row v :=
by { ext, refl }

@[simp] lemma col_apply (v : m → α) (i j) : matrix.col v i j = v i := rfl
@[simp] lemma row_apply (v : m → α) (i j) : matrix.row v i j = v j := rfl

@[simp]
lemma transpose_col (v : m → α) : (matrix.col v)ᵀ = matrix.row v := by { ext, refl }
@[simp]
lemma transpose_row (v : m → α) : (matrix.row v)ᵀ = matrix.col v := by { ext, refl }

@[simp]
lemma conj_transpose_col [has_star α] (v : m → α) : (col v)ᴴ = row (star v) := by { ext, refl }
@[simp]
lemma conj_transpose_row [has_star α] (v : m → α) : (row v)ᴴ = col (star v) := by { ext, refl }

lemma row_vec_mul [fintype m] [semiring α] (M : matrix m n α) (v : m → α) :
  matrix.row (matrix.vec_mul v M) = matrix.row v ⬝ M := by {ext, refl}
lemma col_vec_mul [fintype m] [semiring α] (M : matrix m n α) (v : m → α) :
  matrix.col (matrix.vec_mul v M) = (matrix.row v ⬝ M)ᵀ := by {ext, refl}
lemma col_mul_vec [fintype n] [semiring α] (M : matrix m n α) (v : n → α) :
  matrix.col (matrix.mul_vec M v) = M ⬝ matrix.col v := by {ext, refl}
lemma row_mul_vec [fintype n] [semiring α] (M : matrix m n α) (v : n → α) :
  matrix.row (matrix.mul_vec M v) = (M ⬝ matrix.col v)ᵀ := by {ext, refl}

@[simp]
lemma row_mul_col_apply [fintype m] [has_mul α] [add_comm_monoid α] (v w : m → α) (i j) :
  (row v ⬝ col w) i j = dot_product v w :=
rfl

end row_col

section update

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def update_row [decidable_eq n] (M : matrix n m α) (i : n) (b : m → α) : matrix n m α :=
function.update M i b

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def update_column [decidable_eq m] (M : matrix n m α) (j : m) (b : n → α) : matrix n m α :=
λ i, function.update (M i) j (b i)

variables {M : matrix n m α} {i : n} {j : m} {b : m → α} {c : n → α}

@[simp] lemma update_row_self [decidable_eq n] : update_row M i b i = b :=
function.update_same i b M

@[simp] lemma update_column_self [decidable_eq m] : update_column M j c i j = c i :=
function.update_same j (c i) (M i)

@[simp] lemma update_row_ne [decidable_eq n] {i' : n} (i_ne : i' ≠ i) :
  update_row M i b i' = M i' := function.update_noteq i_ne b M

@[simp] lemma update_column_ne [decidable_eq m] {j' : m} (j_ne : j' ≠ j) :
  update_column M j c i j' = M i j' := function.update_noteq j_ne (c i) (M i)

lemma update_row_apply [decidable_eq n] {i' : n} :
  update_row M i b i' j = if i' = i then b j else M i' j :=
begin
  by_cases i' = i,
  { rw [h, update_row_self, if_pos rfl] },
  { rwa [update_row_ne h, if_neg h] }
end

lemma update_column_apply [decidable_eq m] {j' : m} :
  update_column M j c i j' = if j' = j then c i else M i j' :=
begin
  by_cases j' = j,
  { rw [h, update_column_self, if_pos rfl] },
  { rwa [update_column_ne h, if_neg h] }
end

@[simp] lemma update_column_subsingleton [subsingleton m] (A : matrix n m R)
  (i : m) (b : n → R) :
  A.update_column i b = (col b).minor id (function.const m ()) :=
begin
  ext x y,
  simp [update_column_apply, subsingleton.elim i y]
end

@[simp] lemma update_row_subsingleton [subsingleton n] (A : matrix n m R)
  (i : n) (b : m → R)  :
  A.update_row i b = (row b).minor (function.const n ()) id :=
begin
  ext x y,
  simp [update_column_apply, subsingleton.elim i x]
end

lemma map_update_row [decidable_eq n] (f : α → β) :
  map (update_row M i b) f = update_row (M.map f) i (f ∘ b) :=
begin
  ext i' j',
  rw [update_row_apply, map_apply, map_apply, update_row_apply],
  exact apply_ite f _ _ _,
end

lemma map_update_column [decidable_eq m] (f : α → β) :
  map (update_column M j c) f = update_column (M.map f) j (f ∘ c) :=
begin
  ext i' j',
  rw [update_column_apply, map_apply, map_apply, update_column_apply],
  exact apply_ite f _ _ _,
end

lemma update_row_transpose [decidable_eq m] : update_row Mᵀ j c = (update_column M j c)ᵀ :=
begin
  ext i' j,
  rw [transpose_apply, update_row_apply, update_column_apply],
  refl
end

lemma update_column_transpose [decidable_eq n] : update_column Mᵀ i b = (update_row M i b)ᵀ :=
begin
  ext i' j,
  rw [transpose_apply, update_row_apply, update_column_apply],
  refl
end

lemma update_row_conj_transpose [decidable_eq m] [has_star α] :
  update_row Mᴴ j (star c) = (update_column M j c)ᴴ :=
begin
  rw [conj_transpose, conj_transpose, transpose_map, transpose_map, update_row_transpose,
    map_update_column],
  refl,
end

lemma update_column_conj_transpose [decidable_eq n] [has_star α] :
  update_column Mᴴ i (star b) = (update_row M i b)ᴴ :=
begin
  rw [conj_transpose, conj_transpose, transpose_map, transpose_map, update_column_transpose,
    map_update_row],
  refl,
end

@[simp] lemma update_row_eq_self [decidable_eq m]
  (A : matrix m n α) {i : m} :
  A.update_row i (A i) = A :=
function.update_eq_self i A

@[simp] lemma update_column_eq_self [decidable_eq n]
  (A : matrix m n α) {i : n} :
  A.update_column i (λ j, A j i) = A :=
funext $ λ j, function.update_eq_self i (A j)

end update

end matrix

namespace ring_hom
variables [fintype n] [semiring α] [semiring β]

lemma map_matrix_mul (M : matrix m n α) (N : matrix n o α) (i : m) (j : o) (f : α →+* β) :
  f (matrix.mul M N i j) = matrix.mul (λ i j, f (M i j)) (λ i j, f (N i j)) i j :=
by simp [matrix.mul_apply, ring_hom.map_sum]

lemma map_dot_product [semiring R] [semiring S] (f : R →+* S) (v w : n → R) :
  f (matrix.dot_product v w) = matrix.dot_product (f ∘ v) (f ∘ w) :=
by simp only [matrix.dot_product, f.map_sum, f.map_mul]

lemma map_vec_mul [semiring R] [semiring S]
  (f : R →+* S) (M : matrix n m R) (v : n → R) (i : m) :
  f (M.vec_mul v i) = ((M.map f).vec_mul (f ∘ v) i) :=
by simp only [matrix.vec_mul, matrix.map_apply, ring_hom.map_dot_product]

lemma map_mul_vec [semiring R] [semiring S]
  (f : R →+* S) (M : matrix m n R) (v : n → R) (i : m) :
  f (M.mul_vec v i) = ((M.map f).mul_vec (f ∘ v) i) :=
by simp only [matrix.mul_vec, matrix.map_apply, ring_hom.map_dot_product]

end ring_hom
