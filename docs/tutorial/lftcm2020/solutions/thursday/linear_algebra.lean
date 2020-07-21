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
-- sorry
{ to_fun := λ x, x,
  map_add' := λ x y, rfl,
  map_smul' := λ s x, rfl }
-- sorry

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
-- sorry
  refine { smul := linear_map.has_scalar.smul, ..},
  { intros f, ext x, apply one_smul },
  { intros a b f, ext x, apply mul_smul },
  { intros a f g, ext x, apply smul_add },
  { intros a, ext x, apply smul_zero },
  { intros a b f, ext x, apply add_smul },
  { intros f, ext x, apply zero_smul }
  -- or:
  -- refine { smul := linear_map.has_scalar.smul, ..}; intros; ext; simp
  -- sorry
end

variables {R M}

/- Bonus exercise: define the submodule of `End R M` consisting of the scalar multiplications.
That is, `f ∈ homothety R M` iff `f` is of the form `λ (x : M), s • x` for some `s : R`.

Hints:
  * You could specify the carrier subset and show it is closed under the operations.
  * You could instead use library functions: try `submodule.map` or `linear_map.range`.
-/
def homothety : submodule R (End R M) :=
-- sorry
{ carrier := { f | ∃ (s : R), (∀ (x : M), f x = s • x) },
  zero_mem' := ⟨0, by simp⟩,
  add_mem' := λ f g hf hg, begin
    obtain ⟨r, hr⟩ := hf,
    obtain ⟨s, hs⟩ := hg,
    use r + s,
    intro x,
    simp [hr, hs, add_smul]
  end,
  smul_mem' := λ c f hf, begin
    obtain ⟨r, hr⟩ := hf,
    use c * r,
    simp [hr, mul_smul]
  end }

-- or:
def smulₗ (s : R) : End R M :=
{ to_fun := λ x, s • x,
  map_smul' := by simp [smul_comm],
  map_add' := by simp [smul_add] }

def to_homothety : R →ₗ[R] End R M :=
{ to_fun := smulₗ,
  map_smul' := by { intros, ext, simp [smulₗ, mul_smul] },
  map_add' := by { intros, ext, simp [smulₗ, add_smul] } }

def homothety' : submodule R (End R M) :=
linear_map.range to_homothety
-- sorry

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
-- sorry
by { ext, apply add_dot_product }
-- sorry

@[simp] lemma smul_vec_mul (x : R) (v : m → R) (M : matrix m n R) :
vec_mul (x • v) M = x • vec_mul v M :=
-- sorry
by { ext, apply smul_dot_product }
-- sorry

@[simp] lemma mul_vec_add (M : matrix m n R) (v w : n → R) :
  mul_vec M (v + w) = mul_vec M v + mul_vec M w :=
-- sorry
by { ext, apply dot_product_add }
-- sorry

@[simp] lemma mul_vec_smul (M : matrix m n R) (x : R) (v : n → R) :
  mul_vec M (x • v) = x • mul_vec M v :=
-- sorry
by { ext, apply dot_product_smul }
-- sorry

/- Define the canonical map from bilinear forms to matrices.
We assume `R` has a basis `v` indexed by `ι`.

Hint: Follow your nose, the types will guide you.
A matrix `A : matrix ι ι R` is not much more than a function `ι → ι → R`,
and a bilinear form is not much more than a function `M → M → R`. -/
def bilin_form_to_matrix {ι : Type*} [fintype ι] (v : ι → M)
  (B : bilin_form R M) : matrix ι ι R :=
-- sorry
λ i j, B (v i) (v j)
-- sorry

/-- Define the canonical map from matrices to bilinear forms.

For a matrix `A`, `to_bilin_form A` should take two vectors `v`, `w`
and multiply `A` by `v` on the left and `v` on the right.
-/
def matrix_to_bilin_form (A : matrix n n R) : bilin_form R (n → R) :=
-- sorry
{ bilin := λ v w, dot_product v (mul_vec A w),
  bilin_add_left := by { intros, rw [add_dot_product] },
  bilin_add_right := by { intros, rw [mul_vec_add, dot_product_add] },
  bilin_smul_left := by { intros, rw [smul_dot_product] },
  bilin_smul_right := by { intros, rw [mul_vec_smul, dot_product_smul] } }
-- sorry

/- Can you define a bilinear form directly that is equivalent to this matrix `A`?
Don't use `bilin_form_to_matrix`, give the map explicitly in the form `λ v w, _`.
Check your definition by putting your cursor on the lines starting with `#eval`.

Hints:
  * Use the `simp` tactic to simplify `(x + y) i` to `x i + y i` and `(s • x) i` to `s * x i`.
  * To deal with equalities containing many `+` and `*` symbols, use the `ring` tactic.
-/
def A : matrix (fin 2) (fin 2) R := ![![1, 0], ![-2, 1]]
def your_bilin_form : bilin_form R (fin 2 → R) :=
-- sorry
{ bilin := λ v w, v 0 * w 0 + v 1 * w 1 - 2 * v 1 * w 0,
  bilin_add_left := by { intros, simp, ring },
  bilin_add_right := by { intros, simp, ring },
  bilin_smul_left := by { intros, simp, ring },
  bilin_smul_right := by { intros, simp, ring } }
-- sorry

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
-- sorry
{ inner := dot_product,
  nonneg := λ x, finset.sum_nonneg (λ i _, mul_self_nonneg _),
  definite := λ x hx, funext (λ i, mul_self_eq_zero.mp
    ((finset.sum_eq_zero_iff_of_nonneg (λ i _, mul_self_nonneg (x i))).mp hx i (finset.mem_univ i))),
  comm := λ x y, dot_product_comm _ _,
  add_left := λ x y z, add_dot_product _ _ _,
  smul_left := λ s x y, smul_dot_product _ _ _ }
-- sorry

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
-- sorry
begin
  split,
  { apply linear_independent_iff'.mpr,
    intros s v hs i hi,
    have hs : s.sum (λ (i : n), v i • std_basis R n i) i = 0 := congr_fun hs i,
    unfold std_basis at hs,
    rw [←finset.insert_erase hi, finset.sum_insert (finset.not_mem_erase i s)] at hs,
    simpa using hs },
  { ext,
    simp only [submodule.mem_top, iff_true],
    rw (show x = ∑ i, x i • std_basis R n i, by { ext, simp [std_basis] }),
    refine submodule.sum_mem _ (λ i _, _),
    refine submodule.smul_mem _ _ _,
    apply submodule.subset_span,
    apply set.mem_range_self }
end
-- sorry

variables {K : Type} [field K]

/-
Conclude `n → K` is a finite dimensional vector space for each field `K`
and the dimension of `n → K` over `K` is the cardinality of `n`.
You don't need to complete `std_basis_is_basis` to prove these two lemmas.

Hint: search the library for appropriate lemmas.
-/
lemma finite_dimensional : finite_dimensional K (n → K) :=
-- sorry
finite_dimensional.of_finite_basis (std_basis_is_basis K n)
-- sorry
lemma findim_eq : finite_dimensional.findim K (n → K) = fintype.card n :=
-- sorry
finite_dimensional.findim_eq_card_basis (std_basis_is_basis K n)
-- sorry

end pi

end exercise4
