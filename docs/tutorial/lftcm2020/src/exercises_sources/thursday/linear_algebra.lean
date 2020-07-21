import analysis.normed_space.real_inner_product
import data.matrix.notation
import linear_algebra.bilinear_form
import linear_algebra.matrix
import tactic

universes u v

section exercise1

namespace semimodule

variables (R M : Type*) [comm_semiring R] [add_comm_monoid M] [semimodule R M]

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Exercise 1: defining modules and submodules
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- The endomorphisms of an `R`-semimodule `M` are the `R`-linear maps from `M` to `M`. -/
def End := M →ₗ[R] M
/-- The following line tells Lean we can apply `f : End R M` as if it was a function. -/
instance : has_coe_to_fun (End R M) := { F := λ _, M → M, coe := linear_map.to_fun }

/-- Endomorphisms inherit the pointwise addition operator from linear maps. -/
instance : add_comm_monoid (End R M) := linear_map.add_comm_monoid

/- Define the identity endomorphism `id`. -/
def End.id : End R M :=
sorry

/-
Show that the endomorphisms of `M` form a semimodule over `R`.

Hint: we can re-use the scalar multiplication of linear maps using the `refine` tactic:
```
refine { smul := linear_map.has_scalar.smul, .. },
```
This will fill in the `smul` field of the `semimodule` structure with the given value.
The remaining fields become goals that you can fill in yourself.

Hint: Prove the equalities using the semimodule structure on `M`.
If `f` and `g` are linear maps, the `ext` tactic turns the goal `f = g` into `∀ x, f x = g x`.
-/
instance : semimodule R (End R M) :=
begin
  sorry
end

variables {R M}

/- Bonus exercise: define the submodule of `End R M` consisting of the scalar multiplications.
That is, `f ∈ homothety R M` iff `f` is of the form `λ (x : M), s • x` for some `s : R`.

Hints:
  * You could specify the carrier subset and show it is closed under the operations.
  * You could instead use library functions: try `submodule.map` or `linear_map.range`.
-/
def homothety : submodule R (End R M) :=
sorry

end semimodule

end exercise1


section exercise2

namespace matrix

variables {m n R M : Type} [fintype m] [fintype n] [comm_ring R] [add_comm_group M] [module R M]

/- The following line allows us to write `⬝` (`\cdot`) and `ᵀ` (`\^T`) for
matrix multiplication and transpose. -/
open_locale matrix

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Exercise 2: working with matrices
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- Prove the following four lemmas, that were missing from `mathlib`.

Hints:
  * Look up the definition of `vec_mul` and `mul_vec`.
  * Search the library for useful lemmas about the function used in that definition.
-/
@[simp] lemma add_vec_mul (v w : m → R) (M : matrix m n R) :
  vec_mul (v + w) M = vec_mul v M + vec_mul w M :=
sorry

@[simp] lemma smul_vec_mul (x : R) (v : m → R) (M : matrix m n R) :
vec_mul (x • v) M = x • vec_mul v M :=
sorry

@[simp] lemma mul_vec_add (M : matrix m n R) (v w : n → R) :
  mul_vec M (v + w) = mul_vec M v + mul_vec M w :=
sorry

@[simp] lemma mul_vec_smul (M : matrix m n R) (x : R) (v : n → R) :
  mul_vec M (x • v) = x • mul_vec M v :=
sorry

/- Define the canonical map from bilinear forms to matrices.
We assume `R` has a basis `v` indexed by `ι`.

Hint: Follow your nose, the types will guide you.
A matrix `A : matrix ι ι R` is not much more than a function `ι → ι → R`,
and a bilinear form is not much more than a function `M → M → R`. -/
def bilin_form_to_matrix {ι : Type*} [fintype ι] (v : ι → M)
  (B : bilin_form R M) : matrix ι ι R :=
sorry

/-- Define the canonical map from matrices to bilinear forms.

For a matrix `A`, `to_bilin_form A` should take two vectors `v`, `w`
and multiply `A` by `v` on the left and `v` on the right.
-/
def matrix_to_bilin_form (A : matrix n n R) : bilin_form R (n → R) :=
sorry

/- Can you define a bilinear form directly that is equivalent to this matrix `A`?
Don't use `bilin_form_to_matrix`, give the map explicitly in the form `λ v w, _`.
Check your definition by putting your cursor on the lines starting with `#eval`.

Hints:
  * Use the `simp` tactic to simplify `(x + y) i` to `x i + y i` and `(s • x) i` to `s * x i`.
  * To deal with equalities containing many `+` and `*` symbols, use the `ring` tactic.
-/
def A : matrix (fin 2) (fin 2) R := ![![1, 0], ![-2, 1]]
def your_bilin_form : bilin_form R (fin 2 → R) :=
sorry

/- Check your definition here: -/
def v : fin 2 → ℤ := ![1, 3]
def w : fin 2 → ℤ := ![2, 4]
#eval matrix_to_bilin_form A v w
#eval your_bilin_form v w

end matrix

end exercise2

section exercise3

namespace pi

variables {n : Type*} [fintype n]

open matrix

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Exercise 3: inner product spaces
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/- Use the `dot_product` function to put an inner product on `n → R`.

Hints:
* Try the lemmas `finset.sum_nonneg`, `finset.sum_eq_zero_iff_of_nonneg`,
`mul_self_nonneg` and `mul_self_eq_zero`.
-/
noncomputable instance : inner_product_space (n → ℝ) :=
inner_product_space.of_core
sorry

end pi

end exercise3

section exercise4

namespace pi

variables (R n : Type) [comm_ring R] [fintype n] [decidable_eq n]

/- Enable sum and product notation with `∑` and `∏`. -/
open_locale big_operators

/- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  Exercise 4: basis and dimension
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -/

/-- The `i`'th vector in the standard basis of `n → R` is `1` at the `i`th entry
and `0` otherwise. -/
def std_basis (i : n) : (n → R) := λ j, if i = j then 1 else 0

/- Bonus exercise: Show the standard basis of `n → R` is a basis.
This is a difficult exercise, so feel free to skip some parts.

Hints for showing linear independence:
  * Try using the lemma `linear_independent_iff` or `linear_independent_iff'`.
  * To derive `f x = 0` from `h : f = 0`, use a tactic `have := congr_fun h x`.
  * Take a term out of a sum by combining `finset.insert_erase` and `finset.sum_insert`.

Hints for showing it spans the whole module:
  * To show equality of set-like terms, apply the `ext` tactic.
  * First show `x = ∑ i, x i • std_basis R n i`, then rewrite with this equality.
-/
lemma std_basis_is_basis : is_basis R (std_basis R n) :=
sorry

variables {K : Type} [field K]

/-
Conclude `n → K` is a finite dimensional vector space for each field `K`
and the dimension of `n → K` over `K` is the cardinality of `n`.
You don't need to complete `std_basis_is_basis` to prove these two lemmas.

Hint: search the library for appropriate lemmas.
-/
lemma finite_dimensional : finite_dimensional K (n → K) :=
sorry
lemma findim_eq : finite_dimensional.findim K (n → K) = fintype.card n :=
sorry

end pi

end exercise4

