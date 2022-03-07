/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.pi_Lp
import analysis.normed_space.lp_space

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `pi_Lp 2`.

## Main definitions

- `euclidean_space 𝕜 n`: defined to be `pi_Lp 2 (n → 𝕜)` for any `fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space).

- `orthonormal_basis 𝕜 ι`: defined to be an isometry to Euclidean space from a given
  finite-dimensional innner product space, `E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι`.

- `basis.to_orthonormal_basis`: constructs an `orthonormal_basis` for a finite-dimensional
  Euclidean space from a `basis` which is `orthonormal`.

- `linear_isometry_equiv.of_inner_product_space`: provides an arbitrary isometry to Euclidean space
  from a given finite-dimensional inner product space, induced by choosing an arbitrary basis.

- `std_orthonormal_basis`: the canonical `orthonormal_basis` on `euclidean_space 𝕜 ι`

- `complex.isometry_euclidean`: standard isometry from `ℂ` to `euclidean_space ℝ (fin 2)`

This file develops the notion of a finite dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
`euclidean_space 𝕜 ι`. We define an `orthonormal_basis 𝕜 ι E` as a linear isometric equivalence
between `E` and `euclidean_space 𝕜 ι`. Then `std_orthonormal_basis` shows that such an equivalence
always exists if `E` is finite dimensional. We provide language for converting between a basis
that is orthonormal and an orthonormal basis (e.g. `basis.to_orthonormal_basis`). We show that
orthonormal bases for each summand in a direct sum of spaces can be combined into an orthonormal
basis for the the whole sum in `direct_sum.submodule_is_internal.subordinate_orthonormal_basis`. In
the last section, various properties of matrices are explored.

For consequences in infinite dimension (Hilbert bases, etc.), see the file
`analysis.inner_product_space.l2_space`.
-/

open real set filter is_R_or_C
open_locale big_operators uniformity topological_space nnreal ennreal complex_conjugate direct_sum

noncomputable theory

variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E]
variables {E' : Type*} [inner_product_space 𝕜 E']
variables {F : Type*} [inner_product_space ℝ F]
variables {F' : Type*} [inner_product_space ℝ F']
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 f` for the product space, which is endowed with the `L^2` norm.
-/
instance pi_Lp.inner_product_space {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, inner_product_space 𝕜 (f i)] : inner_product_space 𝕜 (pi_Lp 2 f) :=
{ inner := λ x y, ∑ i, inner (x i) (y i),
  norm_sq_eq_inner :=
  begin
    intro x,
    have h₁ : ∑ (i : ι), ∥x i∥ ^ (2 : ℕ) = ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { apply finset.sum_congr rfl,
      intros j hj,
      simp [←rpow_nat_cast] },
    have h₂ : 0 ≤ ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { rw [←h₁],
      exact finset.sum_nonneg (λ j (hj : j ∈ finset.univ), pow_nonneg (norm_nonneg (x j)) 2) },
    simp [norm, add_monoid_hom.map_sum, ←norm_sq_eq_inner],
    rw [←rpow_nat_cast ((∑ (i : ι), ∥x i∥ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) 2],
    rw [←rpow_mul h₂],
    norm_num [h₁],
  end,
  conj_sym :=
  begin
    intros x y,
    unfold inner,
    rw ring_hom.map_sum,
    apply finset.sum_congr rfl,
    rintros z -,
    apply inner_conj_sym,
  end,
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = (conj r) * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left] }

@[simp] lemma pi_Lp.inner_apply {ι : Type*} [fintype ι] {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x y : pi_Lp 2 f) :
  ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
rfl

lemma pi_Lp.norm_eq_of_L2 {ι : Type*} [fintype ι] {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x : pi_Lp 2 f) :
  ∥x∥ = sqrt (∑ (i : ι), ∥x i∥ ^ 2) :=
by { rw [pi_Lp.norm_eq_of_nat 2]; simp [sqrt_eq_rpow] }

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
@[reducible, nolint unused_arguments]
def euclidean_space (𝕜 : Type*) [is_R_or_C 𝕜]
  (n : Type*) [fintype n] : Type* := pi_Lp 2 (λ (i : n), 𝕜)

/-- The (forgetful) equivalence between `euclidean_space 𝕜 ι` and maps, `ι → 𝕜`:
backwards direction. -/
def to_euclidean_space [fintype ι] : (ι → 𝕜) ≃ euclidean_space 𝕜 ι := equiv.refl _

/-- The (forgetful) equivalence between `euclidean_space 𝕜 ι` and maps, `ι → 𝕜`:
forwards direction. -/
def of_euclidean_space [fintype ι]: euclidean_space 𝕜 ι ≃ (ι → 𝕜) := equiv.refl _

lemma euclidean_space.norm_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x : euclidean_space 𝕜 n) : ∥x∥ = real.sqrt (∑ (i : n), ∥x i∥ ^ 2) :=
pi_Lp.norm_eq_of_L2 x

variables [fintype ι]

section
local attribute [reducible] pi_Lp

instance : finite_dimensional 𝕜 (euclidean_space 𝕜 ι) := by apply_instance
instance : inner_product_space 𝕜 (euclidean_space 𝕜 ι) := by apply_instance

@[simp] lemma finrank_euclidean_space :
  finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 ι) = fintype.card ι := by simp

lemma finrank_euclidean_space_fin {n : ℕ} :
  finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 (fin n)) = n := by simp

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `pi_Lp 2` of the subspaces equipped with the `L2` inner product. -/
def direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family
  [decidable_eq ι] {V : ι → submodule 𝕜 E} (hV : direct_sum.submodule_is_internal V)
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  E ≃ₗᵢ[𝕜] pi_Lp 2 (λ i, V i) :=
begin
  let e₁ := direct_sum.linear_equiv_fun_on_fintype 𝕜 ι (λ i, V i),
  let e₂ := linear_equiv.of_bijective _ hV.injective hV.surjective,
  refine (e₂.symm.trans e₁).isometry_of_inner _,
  suffices : ∀ v w, ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫,
  { intros v₀ w₀,
    convert this (e₁ (e₂.symm v₀)) (e₁ (e₂.symm w₀));
    simp only [linear_equiv.symm_apply_apply, linear_equiv.apply_symm_apply] },
  intros v w,
  transitivity ⟪(∑ i, (V i).subtypeₗᵢ (v i)), ∑ i, (V i).subtypeₗᵢ (w i)⟫,
  { simp only [sum_inner, hV'.inner_right_fintype, pi_Lp.inner_apply] },
  { congr; simp }
end

@[simp] lemma direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply
  [decidable_eq ι] {V : ι → submodule 𝕜 E} (hV : direct_sum.submodule_is_internal V)
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ))
  (w : pi_Lp 2 (λ i, V i)) :
  (hV.isometry_L2_of_orthogonal_family hV').symm w = ∑ i, (w i : E) :=
begin
  classical,
  let e₁ := direct_sum.linear_equiv_fun_on_fintype 𝕜 ι (λ i, V i),
  let e₂ := linear_equiv.of_bijective _ hV.injective hV.surjective,
  suffices : ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i,
  { exact this (e₁.symm w) },
  intros v,
  simp [e₂, direct_sum.submodule_coe, direct_sum.to_module, dfinsupp.sum_add_hom_apply]
end

end

/-- The vector given in euclidean space by being `1 : 𝕜` at coordinate `i : ι` and `0 : 𝕜` at
all other coordinates. -/
def euclidean_space.single [decidable_eq ι] (i : ι) (a : 𝕜) :
  euclidean_space 𝕜 ι :=
pi.single i a

@[simp] theorem euclidean_space.single_apply [decidable_eq ι] (i : ι) (a : 𝕜) (j : ι) :
  (euclidean_space.single i a) j = ite (j = i) a 0 :=
pi.single_apply _ _ _

lemma euclidean_space.inner_single_left
  [decidable_eq ι] (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) :
    ⟪euclidean_space.single i (a : 𝕜), v⟫ = conj a * (v i) :=
by simp [apply_ite conj]

lemma euclidean_space.inner_single_right [decidable_eq ι]
  (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) :
  ⟪v, euclidean_space.single i (a : 𝕜)⟫ =  a * conj (v i) :=
by simp [apply_ite conj, mul_comm]

variables (ι 𝕜 E)

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching
`euclidean_space 𝕜 ι`. -/
structure orthonormal_basis := of_repr :: (repr : E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι)

variables {ι 𝕜 E}

namespace orthonormal_basis

instance : inhabited (orthonormal_basis ι 𝕜 (euclidean_space 𝕜 ι)) :=
⟨orthonormal_basis.of_repr (linear_isometry_equiv.refl 𝕜 (euclidean_space 𝕜 ι))⟩

/-- `b i` is the `i`th basis vector. -/
instance [decidable_eq ι] : has_coe_to_fun (orthonormal_basis ι 𝕜 E) (λ _, ι → E) :=
{ coe := λ (b : orthonormal_basis ι 𝕜 E) (i : ι),
b.repr.symm (euclidean_space.single i (1 : 𝕜)) }

@[simp] lemma coe_of_repr [decidable_eq ι] (e : E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι) :
  ⇑(orthonormal_basis.of_repr e) = λ i, e.symm (euclidean_space.single i (1 : 𝕜)) :=
rfl

@[simp] protected lemma repr_symm_single [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr.symm (euclidean_space.single i (1:𝕜)) = b i :=
rfl

@[simp] protected lemma repr_symm_single' [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr.symm (pi.single i (1:𝕜)) = b i :=
rfl

@[simp] protected lemma repr_self [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr (b i) = euclidean_space.single i (1:𝕜) :=
begin
  rw [← b.repr_symm_single i, linear_isometry_equiv.apply_symm_apply],
end

protected lemma repr_apply_apply [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) (v : E) (i : ι) :
  b.repr v i = ⟪b i, v⟫ :=
begin
  rw [← b.repr.inner_map_map (b i) v, b.repr_self i, euclidean_space.inner_single_left],
  simp only [one_mul, eq_self_iff_true, map_one],
end

@[simp]
protected lemma orthonormal [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) : orthonormal 𝕜 b :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self i, b.repr_self j],
  rw euclidean_space.inner_single_left,
  rw euclidean_space.single_apply,
  simp only [mul_boole, map_one],
end

/-- The `basis ι 𝕜 E` underlying the `orthonormal_basis` --/
protected def to_basis (b : orthonormal_basis ι 𝕜 E) : basis ι 𝕜 E :=
basis.of_equiv_fun b.repr.to_linear_equiv

@[simp] protected lemma coe_to_basis [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) :
  (⇑b.to_basis : ι → E) = ⇑b :=
begin
  change ⇑(basis.of_equiv_fun b.repr.to_linear_equiv) = b,
  ext j,
  rw basis.coe_of_equiv_fun,
  simp only [orthonormal_basis.repr_symm_single],
  congr,
end

@[simp] protected lemma coe_to_basis_repr (b : orthonormal_basis ι 𝕜 E) :
  b.to_basis.equiv_fun = b.repr.to_linear_equiv :=
begin
  change (basis.of_equiv_fun b.repr.to_linear_equiv).equiv_fun = b.repr.to_linear_equiv,
  ext x j,
  simp only [basis.of_equiv_fun_repr_apply, eq_self_iff_true,
    linear_isometry_equiv.coe_to_linear_equiv, basis.equiv_fun_apply],
end

protected lemma sum_repr_symm
  [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) (v : euclidean_space 𝕜 ι) :
  ∑ i , v i • b i = (b.repr.symm v) :=
by simpa using (b.to_basis.equiv_fun_symm_apply v).symm

/-- A basis that is orthonormal is an orthonormal basis. -/
def _root_.basis.to_orthonormal_basis (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  orthonormal_basis ι 𝕜 E :=
orthonormal_basis.of_repr $
linear_equiv.isometry_of_inner v.equiv_fun
begin
  intros x y,
  let p : euclidean_space 𝕜 ι := v.equiv_fun x,
  let q : euclidean_space 𝕜 ι := v.equiv_fun y,
  have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫,
  { simp [sum_inner, inner_smul_left, hv.inner_right_fintype] },
  convert key,
  { rw [← v.equiv_fun.symm_apply_apply x, v.equiv_fun_symm_apply] },
  { rw [← v.equiv_fun.symm_apply_apply y, v.equiv_fun_symm_apply] }
end

@[simp] lemma _root_.basis.coe_to_orthonormal_basis_repr (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  ((v.to_orthonormal_basis hv).repr : E → euclidean_space 𝕜 ι) = v.equiv_fun :=
rfl

@[simp] lemma _root_.basis.coe_to_orthonormal_basis_repr_symm
  (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  ((v.to_orthonormal_basis hv).repr.symm : euclidean_space 𝕜 ι → E) = v.equiv_fun.symm :=
rfl

@[simp] lemma _root_.basis.to_basis_to_orthonormal_basis (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  (v.to_orthonormal_basis hv).to_basis = v :=
by simp [basis.to_orthonormal_basis, orthonormal_basis.to_basis]

@[simp] lemma _root_.basis.coe_to_orthonormal_basis
  [decidable_eq ι] (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  (v.to_orthonormal_basis hv : ι → E) = (v : ι → E) :=
calc (v.to_orthonormal_basis hv : ι → E) = ((v.to_orthonormal_basis hv).to_basis : ι → E) :
  by rw orthonormal_basis.coe_to_basis
... = (v : ι → E) : by simp

variable {v : ι → E}

/-- A finite orthonormal set that spans is an orthonormal basis. -/
protected def mk (hon : orthonormal 𝕜 v) (hsp: submodule.span 𝕜 (set.range v) = ⊤):
  orthonormal_basis ι 𝕜 E :=
(basis.mk (orthonormal.linear_independent hon) hsp).to_orthonormal_basis (by rwa basis.coe_mk)

@[simp]
protected lemma coe_mk
  [decidable_eq ι] (hon : orthonormal 𝕜 v) (hsp: submodule.span 𝕜 (set.range v) = ⊤) :
  ⇑(orthonormal_basis.mk hon hsp) = v :=
by rw [orthonormal_basis.mk, _root_.basis.coe_to_orthonormal_basis, basis.coe_mk]

open submodule

/-- A finite orthonormal family of vectors whose span has trivial orthogonal complement is an
orthonormal basis. -/
protected def mk_of_orthogonal_eq_bot (hon : orthonormal 𝕜 v) (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) :
  orthonormal_basis ι 𝕜 E :=
orthonormal_basis.mk hon
begin
  haveI : finite_dimensional 𝕜 (span 𝕜 (range v)) :=
    finite_dimensional.span_of_finite 𝕜 (finite_range v),
  haveI : complete_space (span 𝕜 (range v)) := finite_dimensional.complete 𝕜 _,
  rwa orthogonal_eq_bot_iff at hsp,
end

@[simp] protected lemma coe_of_orthogonal_eq_bot_mk [decidable_eq ι] (hon : orthonormal 𝕜 v)
  (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) :
  ⇑(orthonormal_basis.mk_of_orthogonal_eq_bot hon hsp) = v :=
orthonormal_basis.coe_mk hon _

variable {ι' : Type*}
variables [fintype ι']

/-- `b.reindex (e : ι ≃ ι')` is an `orthonormal_basis` indexed by `ι'` -/
def reindex (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') : orthonormal_basis ι' 𝕜 E :=
orthonormal_basis.of_repr (b.repr.trans (linear_isometry_equiv.pi_Lp_congr_left e))

protected lemma reindex_apply
  [decidable_eq ι] [decidable_eq ι'] (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
  (b.reindex e) i' = b (e.symm i') :=
begin
  change (b.repr.trans (linear_isometry_equiv.pi_Lp_congr_left e)).symm
    (euclidean_space.single i' 1)
  = b.repr.symm (euclidean_space.single (e.symm i') 1),
  rw [linear_isometry_equiv.symm_trans, linear_isometry_equiv.trans_apply,
    linear_isometry_equiv.pi_Lp_congr_left_symm, euclidean_space.single],
  simp only [orthonormal_basis.repr_symm_single, linear_isometry_equiv.pi_Lp_congr_left_single],
  rw b.repr_symm_single',
end

@[simp] protected lemma coe_reindex
  [decidable_eq ι] [decidable_eq ι'] (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') :
  ⇑(b.reindex e) = ⇑b ∘ ⇑(e.symm) :=
funext (b.reindex_apply e)

@[simp] protected lemma reindex_repr
  (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
  ((b.reindex e).repr x) i' = (b.repr x) (e.symm i') :=
by { classical,
  rw [orthonormal_basis.repr_apply_apply, b.repr_apply_apply, orthonormal_basis.coe_reindex] }

protected lemma coe_reindex_repr
  (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') (x : E) :
  ((b.reindex e).repr x) = of_euclidean_space (b.repr x) ∘ (e.symm) :=
begin
  funext i,
  rw [b.reindex_repr, function.comp_app],
  congr,
end

end orthonormal_basis

/-- If `f : E ≃ₗᵢ[𝕜] E'` is a linear isometry of inner product spaces then an orthonormal basis `v`
of `E` determines a linear isometry `e : E' ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι`. This result states that
`e` may be obtained either by transporting `v` to `E'` or by composing with the linear isometry
`E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι` provided by `v`. -/
@[simp] lemma basis.map_isometry_euclidean_of_orthonormal (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v)
  (f : E ≃ₗᵢ[𝕜] E') :
  ((v.map f.to_linear_equiv).to_orthonormal_basis (hv.map_linear_isometry_equiv f)).repr =
    f.symm.trans (v.to_orthonormal_basis hv).repr :=
linear_isometry_equiv.to_linear_equiv_injective $ v.map_equiv_fun _

/-- `ℂ` is isometric to `ℝ²` with the Euclidean inner product. -/
def complex.isometry_euclidean : ℂ ≃ₗᵢ[ℝ] (euclidean_space ℝ (fin 2)) :=
(complex.basis_one_I.to_orthonormal_basis
begin
  rw orthonormal_iff_ite,
  intros i, fin_cases i;
  intros j; fin_cases j;
  simp [real_inner_eq_re_inner]
end).repr

@[simp] lemma complex.isometry_euclidean_symm_apply (x : euclidean_space ℝ (fin 2)) :
  complex.isometry_euclidean.symm x = (x 0) + (x 1) * I :=
begin
  convert complex.basis_one_I.equiv_fun_symm_apply x,
  { simpa },
  { simp },
end

lemma complex.isometry_euclidean_proj_eq_self (z : ℂ) :
  ↑(complex.isometry_euclidean z 0) + ↑(complex.isometry_euclidean z 1) * (I : ℂ) = z :=
by rw [← complex.isometry_euclidean_symm_apply (complex.isometry_euclidean z),
  complex.isometry_euclidean.symm_apply_apply z]

@[simp] lemma complex.isometry_euclidean_apply_zero (z : ℂ) :
  complex.isometry_euclidean z 0 = z.re :=
by { conv_rhs { rw ← complex.isometry_euclidean_proj_eq_self z }, simp }

@[simp] lemma complex.isometry_euclidean_apply_one (z : ℂ) :
  complex.isometry_euclidean z 1 = z.im :=
by { conv_rhs { rw ← complex.isometry_euclidean_proj_eq_self z }, simp }

/-- The isometry between `ℂ` and a two-dimensional real inner product space given by a basis. -/
def complex.isometry_of_orthonormal {v : basis (fin 2) ℝ F} (hv : orthonormal ℝ v) : ℂ ≃ₗᵢ[ℝ] F :=
complex.isometry_euclidean.trans (v.to_orthonormal_basis hv).repr.symm

@[simp] lemma complex.map_isometry_of_orthonormal {v : basis (fin 2) ℝ F} (hv : orthonormal ℝ v)
  (f : F ≃ₗᵢ[ℝ] F') :
  complex.isometry_of_orthonormal (hv.map_linear_isometry_equiv f) =
    (complex.isometry_of_orthonormal hv).trans f :=
by simp [complex.isometry_of_orthonormal, linear_isometry_equiv.trans_assoc]

lemma complex.isometry_of_orthonormal_symm_apply
  {v : basis (fin 2) ℝ F} (hv : orthonormal ℝ v) (f : F) :
  (complex.isometry_of_orthonormal hv).symm f = (v.coord 0 f : ℂ) + (v.coord 1 f : ℂ) * I :=
by simp [complex.isometry_of_orthonormal]

lemma complex.isometry_of_orthonormal_apply
  {v : basis (fin 2) ℝ F} (hv : orthonormal ℝ v) (z : ℂ) :
  complex.isometry_of_orthonormal hv z = z.re • v 0 + z.im • v 1 :=
by simp [complex.isometry_of_orthonormal, (dec_trivial : (finset.univ : finset (fin 2)) = {0, 1})]

open finite_dimensional

/-! ### Existence of orthonormal basis, etc. -/

section finite_dimensional

variables {v : set E}

variables {A : ι → submodule 𝕜 E}

/-- Given an internal direct sum decomposition of a module `M`, and an orthonormal basis for each
of the components of the direct sum, the disjoint union of these orthonormal bases is an
orthonormal basis for `M`. -/
noncomputable def direct_sum.submodule_is_internal.collected_orthonormal_basis
  (hV : @orthogonal_family 𝕜 _ _ _ _ (λ i, A i) _ (λ i, (A i).subtypeₗᵢ))
  [decidable_eq ι] (hV_sum : direct_sum.submodule_is_internal (λ i, A i)) {α : ι → Type*}
  [Π i, fintype (α i)] [Π i, decidable_eq (α i)]
  (v_family : Π i, orthonormal_basis (α i) 𝕜 (A i)) :
  orthonormal_basis (Σ i, α i) 𝕜 E :=
(hV_sum.collected_basis (λ i, (v_family i).to_basis)).to_orthonormal_basis $
by simpa using hV.orthonormal_sigma_orthonormal
  (show (∀ i, orthonormal 𝕜 (v_family i).to_basis), by simp)

lemma direct_sum.submodule_is_internal.collected_orthonormal_basis_mem [decidable_eq ι]
  (h : direct_sum.submodule_is_internal A) {α : ι → Type*}
  [Π i, fintype (α i)] [Π i, decidable_eq (α i)]
  (hV : @orthogonal_family 𝕜 _ _ _ _ (λ i, A i) _ (λ i, (A i).subtypeₗᵢ))
  (v : Π i, orthonormal_basis (α i) 𝕜 (A i)) (a : Σ i, α i) :
  h.collected_orthonormal_basis hV v a ∈ A a.1 :=
by simp [direct_sum.submodule_is_internal.collected_orthonormal_basis]

variables [finite_dimensional 𝕜 E]

-- move this
lemma _root_.linear_independent.finite {K : Type*} {V : Type*} [division_ring K] [add_comm_group V]
  [module K V] [finite_dimensional K V] {b : set V} (h : linear_independent K (λ (x:b), (x:V))) :
  b.finite :=
cardinal.lt_omega_iff_finite.mp (finite_dimensional.lt_omega_of_linear_independent h)

/-- In a finite-dimensional `inner_product_space`, any orthonormal subset can be extended to an
orthonormal basis. -/
lemma _root_.orthonormal.exists_orthonormal_basis_extension
   [decidable_eq E] (hv : orthonormal 𝕜 (coe : v → E)) :
  ∃ {u : finset E} (b : orthonormal_basis u 𝕜 E), v ⊆ u ∧ ⇑b = coe :=
begin
  obtain ⟨u₀, hu₀s, hu₀, hu₀_max⟩ := exists_maximal_orthonormal hv,
  rw maximal_orthonormal_iff_orthogonal_complement_eq_bot hu₀ at hu₀_max,
  have hu₀_finite : u₀.finite := hu₀.linear_independent.finite,
  let u : finset E := hu₀_finite.to_finset,
  let fu : ↥u ≃ ↥u₀ := equiv.cast (congr_arg coe_sort hu₀_finite.coe_to_finset),
  have hfu : (coe : u → E) = (coe : u₀ → E) ∘ fu := by { ext, simp },
  have hu : orthonormal 𝕜 (coe : u → E) := by simpa [hfu] using hu₀.comp _ fu.injective,
  refine ⟨u, orthonormal_basis.mk_of_orthogonal_eq_bot hu _, _, _⟩,
  { simpa using hu₀_max },
  { simpa using hu₀s },
  { simp },
end

variables (𝕜 E)

/-- A finite-dimensional inner product space admits an orthonormal basis. -/
lemma _root_.exists_orthonormal_basis [decidable_eq E] :
  ∃ (w : finset E) (b : orthonormal_basis w 𝕜 E), ⇑b = (coe : w → E) :=
let ⟨w, hw, hw', hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormal_basis_extension in
⟨w, hw, hw''⟩

/-- Index for an arbitrary orthonormal basis on a finite-dimensional `inner_product_space`. -/
def orthonormal_basis_index [decidable_eq E] : finset E :=
classical.some (exists_orthonormal_basis 𝕜 E)

/-- A finite-dimensional `inner_product_space` has an orthonormal basis. -/
def std_orthonormal_basis [decidable_eq E] :
  orthonormal_basis (orthonormal_basis_index 𝕜 E) 𝕜 E :=
classical.some (classical.some_spec (exists_orthonormal_basis 𝕜 E))

@[simp] lemma coe_std_orthonormal_basis [decidable_eq E]:
  ⇑(std_orthonormal_basis 𝕜 E) = coe :=
classical.some_spec (classical.some_spec (exists_orthonormal_basis 𝕜 E))

variables {𝕜 E}

/-- An `n`-dimensional `inner_product_space` has an orthonormal basis indexed by `fin n`. -/
def fin_std_orthonormal_basis {n : ℕ} [decidable_eq E] (hn : finrank 𝕜 E = n) :
  orthonormal_basis (fin n) 𝕜 E :=
have h : fintype.card (orthonormal_basis_index 𝕜 E) = n,
by rw [← finrank_eq_card_basis (std_orthonormal_basis 𝕜 E).to_basis, hn],
(std_orthonormal_basis 𝕜 E).reindex (fintype.equiv_fin_of_card_eq h)

section subordinate_orthonormal_basis
open direct_sum
variables {n : ℕ} (hn : finrank 𝕜 E = n) [decidable_eq ι]
  {V : ι → submodule 𝕜 E} (hV : submodule_is_internal V)

/-- Exhibit a bijection between `fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`.  This should not be accessed directly, but only via the subsequent API. -/
@[irreducible] def direct_sum.submodule_is_internal.sigma_orthonormal_basis_index_equiv
  [decidable_eq E]
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  (Σ i, orthonormal_basis_index 𝕜 (V i)) ≃ fin n :=
let b := hV.collected_orthonormal_basis hV' (λ i, (std_orthonormal_basis 𝕜 (V i))) in
fintype.equiv_fin_of_card_eq $ (finite_dimensional.finrank_eq_card_basis b.to_basis).symm.trans hn

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. -/
@[irreducible] def direct_sum.submodule_is_internal.subordinate_orthonormal_basis
  [decidable_eq E]
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  orthonormal_basis (fin n) 𝕜 E :=
((hV.collected_orthonormal_basis hV' (λ i, (std_orthonormal_basis 𝕜 (V i)))).reindex
  (hV.sigma_orthonormal_basis_index_equiv hn hV'))

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. This function
provides the mapping by which it is subordinate. -/
def direct_sum.submodule_is_internal.subordinate_orthonormal_basis_index [decidable_eq E]
  (a : fin n) (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) : ι :=
((hV.sigma_orthonormal_basis_index_equiv hn hV').symm a).1

/-- The basis constructed in `orthogonal_family.subordinate_orthonormal_basis` is subordinate to
the `orthogonal_family` in question. -/
lemma direct_sum.submodule_is_internal.subordinate_orthonormal_basis_subordinate [decidable_eq E]
  (a : fin n) (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  (hV.subordinate_orthonormal_basis hn hV' a) ∈
  V (hV.subordinate_orthonormal_basis_index hn a hV') :=
by simpa only [direct_sum.submodule_is_internal.subordinate_orthonormal_basis,
  orthonormal_basis.coe_reindex]
  using hV.collected_orthonormal_basis_mem hV' (λ i, (std_orthonormal_basis 𝕜 (V i)))
    ((hV.sigma_orthonormal_basis_index_equiv hn hV').symm a)

attribute [irreducible] direct_sum.submodule_is_internal.subordinate_orthonormal_basis_index

end subordinate_orthonormal_basis

end finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.from_orthogonal_span_singleton
  [decidable_eq E] (n : ℕ) [fact (finrank 𝕜 E = n + 1)] {v : E} (hv : v ≠ 0) :
  orthonormal_basis (fin n) 𝕜 (𝕜 ∙ v)ᗮ :=
(fin_std_orthonormal_basis (finrank_orthogonal_span_singleton hv))

section matrix

open_locale matrix

variables {n m : ℕ}

local notation `⟪`x`, `y`⟫ₘ` := @inner 𝕜 (euclidean_space 𝕜 (fin m)) _ x y
local notation `⟪`x`, `y`⟫ₙ` := @inner 𝕜 (euclidean_space 𝕜 (fin n)) _ x y

/-- The inner product of a row of A and a row of B is an entry of B ⬝ Aᴴ. -/
lemma inner_matrix_row_row (A B : matrix (fin n) (fin m) 𝕜) (i j : (fin n)) :
  ⟪A i, B j⟫ₘ = (B ⬝ Aᴴ) j i := by {simp only [inner, matrix.mul_apply, star_ring_end_apply,
    matrix.conj_transpose_apply,mul_comm]}

/-- The inner product of a column of A and a column of B is an entry of Aᴴ ⬝ B -/
lemma inner_matrix_col_col (A B : matrix (fin n) (fin m) 𝕜) (i j : (fin m)) :
  ⟪Aᵀ i, Bᵀ j⟫ₙ = (Aᴴ ⬝ B) i j := rfl

end matrix
