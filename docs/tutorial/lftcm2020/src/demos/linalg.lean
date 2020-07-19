import algebra.module
import algebra.pi_instances
import analysis.normed_space.real_inner_product
import data.matrix.notation
import linear_algebra.basic
import linear_algebra.bilinear_form
import linear_algebra.quadratic_form
import linear_algebra.finsupp
import tactic

/-
According to Wikipedia, everyone's favourite reliable source of knowledge,
linear algebra studies linear equations and linear maps, representing them
in vector spaces and through matrices.
So let us start with printing the representation of vector spaces in mathlib:
-/
-- import algebra.module

#print vector_space
-- abbreviation vector_space (R : Type u) (M : Type v) [field R] [add_comm_group M] := semimodule R M

/-
So vector spaces are represented by putting a `vector_space` typeclass
on a type `R` and `M`, where `R` has a field structure and `M` an additive commutative group.
And the comment helpfully explains that a `vector_space` is just a `module`,
except the scalar ring is a field.
-/

#print module
-- abbreviation module (R : Type u) (M : Type v) [ring R] [add_comm_group M] := semimodule R M

/-
When we print the definition of `module`, we see it is a special case of a `semimodule``.
Finally, we print the definition of `semimodule`:
-/

#print semimodule
-- class semimodule (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M]
-- extends distrib_mul_action R M := ...

/-
In other words: let `R` be a semiring and `M` have `0` and a commutative operator `+`,
then a semimodule structure over `R` on `M` has a scalar multiplication `•` (`has_scalar.smul`),
which satisfies the following identities:
-/
#check add_smul -- ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
#check smul_add -- ∀ (r : R) (x y : M), r • (x + y) = r • x + r • y
#check mul_smul -- ∀ (r s : R) (x : M), (r * s) • x = r • (s • x)
#check one_smul -- ∀ (x : M), 1 • x = x
#check zero_smul -- ∀ (x : M), 0 • x = 0
#check smul_zero -- ∀ (r : R), r • 0 = 0
/-
These equations define semimodules, modules and vector spaces. To save typing,
and because semimodules were introduced later, mathlib tends to use the word "module"
to refer to all three as long as this is not ambiguous.
-/

/-
The last two identities follow automatically from the previous if `M` has a negation operator,
turning it into an additive group, so the function `semimodule.of_core` does the proofs for you:
-/
#check semimodule.of_core

section module

/-
Typical examples of semimodules, modules and vector spaces:
-/
-- import algebra.pi_instances
variables {n : Type} [fintype n]
example : semimodule ℕ (n → ℕ) := infer_instance -- Or as mathematicians commonly know it: `ℕ^n`.
example : module ℤ (n → ℤ) := infer_instance
example : vector_space ℚ (n → ℚ) := infer_instance
example : semimodule ℚ (n → ℚ) := infer_instance -- A vector space is automatically a semimodule.

/- If you want a specifically `k`-dimensional module, use `fin k` as the `fintype`. -/
example {k : ℕ} : semimodule ℤ (fin k → ℤ) := infer_instance

variables {R M N : Type} [ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
example : module R R := infer_instance
example : module ℤ R := infer_instance
example : module R (M × N) := infer_instance
example : module R (M × N) := infer_instance

example {R' : Type} [comm_ring R'] (f : R →+* R') : module R R' := ring_hom.to_semimodule f

/- To explicitly construct elements of `fin k → R`, use the following notation: -/
-- import data.matrix.notation
example : fin 4 → ℤ := ![1, 2, -4, 3]

end module

section linear_map

variables {R M : Type} [comm_ring R] [add_comm_group M] [module R M]

/-
Maps between semimodules that respect `+` and `•` are called `linear_map`,
and an `R`-linear map from `M` to `N` has notation `M →ₗ[R] N`:
-/
#print linear_map

/- They are bundled, meaning we define them by giving the map and the proofs simultaneously: -/
def twice : M →ₗ[R] M :=
{ to_fun := λ x, (2 : R) • x,
  map_add' := λ x y, smul_add 2 x y,
  map_smul' := λ s x, smul_comm 2 s x }

/- Linear maps can be applied as if they were functions: -/
#check twice (![37, 42] : fin 2 → ℚ)

/- Some basic operations on linear maps: -/
-- import linear_algebra.basic
#check linear_map.comp -- composition
#check linear_map.has_zero -- 0
#check linear_map.has_add -- (+)
#check linear_map.has_scalar -- (•)

/-
A linear equivalence is an invertible linear map.
These are the correct notion of "isomorphism of modules".
-/
#print linear_equiv
/- The identity function is defined twice: once as linear map and once as linear equivalence. -/
#check linear_map.id
#check linear_equiv.refl

end linear_map

section submodule

variables {R M : Type} [comm_ring R] [add_comm_group M] [module R M]

/-
The submodules of a semimodule `M` are subsets of `M` (i.e. elements of `set M`)
that are closed under the module operations `0`, `+` and `•`.
Just like `vector_space` is defined to be a special case of `semimodule`,
`subspace` is defined to be a special case of `submodule`.
-/
#print submodule
#print subspace

/-
Note that the `ideal`s of a ring `R` are defined to be exactly the `R`-submodules of `R`.
This should save us a lot of re-definition work.
-/
#print ideal

/-
You can directly define a submodule by giving its carrier subset and proving that
the carrier is closed under each operation:
-/
def zero_submodule : submodule R M :=
{ carrier := {0},
  zero_mem' := by simp,
  add_mem' := by { intros x y hx hy, simp at hx hy, simp [hx, hy] },
  smul_mem' := by { intros r x hx, simp at hx, simp [hx] } }

/- There are many library functions for defining submodules: -/
variables (S T : submodule R M)
#check (twice.range : submodule R M) -- the image of `twice` in `M`
#check (twice.ker : submodule R M) -- the kernel of `twice` in `M`
#check submodule.span ℤ {(2 : ℤ)} -- also known as 2ℤ
#check S.map twice -- also known as {twice x | x ∈ S}
#check S.comap twice -- also known as {x | twice x ∈ S}

/- For submodule inclusion, we write `≤`: -/
#check S ≤ T
#check S < T
/- The zero submodule is written `⊥` and the whole module as a submodule is written `⊤`: -/
example {x : M} : x ∈ (⊥ : submodule R M) ↔ x = 0 := submodule.mem_bot R
example {x : M} : x ∈ (⊤ : submodule R M) := submodule.mem_top
/- Intersection and sum of submodules are usually written with the lattice operators `⊓` and `⊔`: -/
#check submodule.mem_inf -- x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T
#check submodule.mem_sup -- x ∈ S ⊔ T ↔ ∃ (y ∈ S) (z ∈ T), x = y + z

/- The embedding of a submodule in the ambient space, is called `subtype`: -/
#check submodule.subtype

/- Finally, we can take the quotient modulo a submodule: -/
#check (submodule.span ℤ {(2 : ℤ)}).quotient -- also known as ℤ / 2ℤ

end submodule

section forms

variables {n R : Type} [comm_ring R] [fintype n]

/- In addition to linear maps, there are bilinear forms, quadratic forms and sesquilinear forms. -/
-- import linear_algebra.bilinear_form
-- import linear_algebra.quadratic_form
#check bilin_form

/- Defining a bilinear form works similarly to defining a linear map: -/
def dot_product : bilin_form R (n → R) :=
{ bilin := λ x y, matrix.dot_product x y,
  bilin_add_left := matrix.add_dot_product,
  bilin_smul_left := matrix.smul_dot_product,
  bilin_add_right := matrix.dot_product_add,
  bilin_smul_right := matrix.dot_product_smul }

/- Some other constructions on forms: -/
#check bilin_form.to_quadratic_form
#check quadratic_form.associated
#check quadratic_form.has_scalar
#check quadratic_form.proj

end forms

section matrix

variables {m n R : Type} [fintype m] [fintype n] [comm_ring R]

/-
Matrices in mathlib are basically no more than a rectangular block of entries.
Under the hood, they are specified by a function taking a row and column,
and returning the entry at that index.
They are useful when you want to compute an invariant such as the determinant,
as these are typically noncomputable for linear maps.

A type of matrices `matrix m n α` requires that the types `m` and `n` of the indices
are `fintype`s, and there is no restriction on the type `α` of the entries.
-/
#print matrix

/-
Like vectors in `n → R`, matrices are typically indexed over `fin k`.
To define a matrix, you map the indexes to the entry:
-/
def example_matrix : matrix (fin 2) (fin 3) ℤ := λ i j, i + j
#eval example_matrix 1 2

/- Like vectors, we can use `![...]` notation to define matrices: -/
def other_example_matrix : matrix (fin 3) (fin 2) ℤ :=
![![0, 1],
  ![1, 2],
  ![2, 3]]

/- We have the 0 matrix and the sum of two matrices: -/
example (i j) : (0 : matrix m n R) i j = 0 := matrix.zero_val i j
example (A B : matrix m n R) (i j) : (A + B) i j = A i j + B i j := matrix.add_val A B i j

/-
Matrices have multiplication and transpose operators `matrix.mul` and `matrix.transpose`.
The following line allows `⬝` and `ᵀ` to stand for these two respectively:
-/
open_locale matrix

#check example_matrix ⬝ other_example_matrix
#check example_matrixᵀ

/- On square matrices, we have a semiring structure with `(*) = (⬝)` and `1` as the identity matrix. -/
#check matrix.semiring

/-
When working with matrices, a "vector" is always of the form `n → R`
where `n` is a `fintype`. The operations between matrices and vectors are defined.
-/
#check matrix.col -- turn a vector into a column matrix
#check matrix.row -- turn a vector into a row matrix
#check matrix.vec_mul_vec -- column vector times row vector

/-
You have to explicitly specify whether vectors are multiplied on the left or on the right:
-/
#check example_matrix.mul_vec -- (fin 3 → ℤ) → (fin 2 → ℤ), right multiplication
#check example_matrix.vec_mul -- (fin 2 → ℤ) → (fin 3 → ℤ), left multiplication

/- You can convert a matrix to a linear map, which acts by right multiplication of vectors. -/
variables {M N : Type} [add_comm_group M] [add_comm_group N] [module R M] [module R N]
#check matrix.eval -- matrix m n R → ((m → R) →ₗ[R] (n → R))

/-
Going between linear maps and matrices is an isomorphism,
as long as you have chosen a basis for each module.
-/
variables [decidable_eq m] [decidable_eq n]
variables {v : m → M} (v_is_basis : is_basis R v) {w : n → N} (w_is_basis : is_basis R w)
#check linear_equiv_matrix v_is_basis w_is_basis -- (M →ₗ[R] N) ≈ₗ[R] matrix m n R

/-
Invertible (i.e. nonsingular) matrices have an inverse operation `nonsing_inv`.

The notation `⁻¹` has been reserved for the more general pseudoinverse,
which unfortunately has not yet been defined.
-/
#check matrix.nonsing_inv

end matrix

section odds_and_ends

/- Other useful parts of the library: -/
-- import analysis.normed_space.real_inner_product
#print normed_space -- semimodule with a norm
#print inner_product_space -- normed space with an inner product in ℝ

#print finite_dimensional.findim -- the dimension of a space, as a natural number (infinity -> 0)
#print vector_space.dim -- the dimension of a space, as a cardinal

end odds_and_ends
