/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.pi_Lp

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

- `complex.isometry_euclidean`: standard isometry from `ℂ` to `euclidean_space ℝ (fin 2)`

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
    have h₂ : 0 ≤ ∑ (i : ι), ∥x i∥ ^ (2 : ℝ) :=
      finset.sum_nonneg (λ j hj, rpow_nonneg_of_nonneg (norm_nonneg (x j)) 2),
    simp only [norm, add_monoid_hom.map_sum, ← norm_sq_eq_inner, one_div],
    rw [← rpow_nat_cast ((∑ (i : ι), ∥x i∥ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) 2, ← rpow_mul h₂],
    norm_num,
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
by { rw [euclidean_space.single, ← pi.single_apply i a j] }

lemma euclidean_space.inner_single_left [decidable_eq ι] (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) :
  ⟪euclidean_space.single i (a : 𝕜), v⟫ = conj a * (v i) :=
by simp [apply_ite conj]

lemma euclidean_space.inner_single_right [decidable_eq ι] (i : ι) (a : 𝕜)
  (v : euclidean_space 𝕜 ι) :
  ⟪v, euclidean_space.single i (a : 𝕜)⟫ =  a * conj (v i) :=
by simp [apply_ite conj, mul_comm]

variables (ι 𝕜 E)

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching
`euclidean_space 𝕜 ι`. -/
structure orthonormal_basis := of_repr :: (repr : E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι)

variables {ι 𝕜 E}

namespace orthonormal_basis

instance : inhabited (orthonormal_basis ι 𝕜 (euclidean_space 𝕜 ι)) :=
⟨of_repr (linear_isometry_equiv.refl 𝕜 (euclidean_space 𝕜 ι))⟩

/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (orthonormal_basis ι 𝕜 E) (λ _, ι → E) :=
{ coe := λ b i, by classical; exact b.repr.symm (euclidean_space.single i (1 : 𝕜)) }

@[simp] protected lemma repr_symm_single [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr.symm (euclidean_space.single i (1:𝕜)) = b i :=
by { classical, congr, simp, }

@[simp] protected lemma repr_self [decidable_eq ι] (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr (b i) = euclidean_space.single i (1:𝕜) :=
by rw [← b.repr_symm_single i, linear_isometry_equiv.apply_symm_apply]

protected lemma repr_apply_apply (b : orthonormal_basis ι 𝕜 E) (v : E) (i : ι) :
  b.repr v i = ⟪b i, v⟫ :=
begin
  classical,
  rw [← b.repr.inner_map_map (b i) v, b.repr_self i, euclidean_space.inner_single_left],
  simp only [one_mul, eq_self_iff_true, map_one],
end

@[simp]
protected lemma orthonormal (b : orthonormal_basis ι 𝕜 E) : orthonormal 𝕜 b :=
begin
  classical,
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

@[simp] protected lemma coe_to_basis (b : orthonormal_basis ι 𝕜 E) :
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

protected lemma sum_repr_symm (b : orthonormal_basis ι 𝕜 E) (v : euclidean_space 𝕜 ι) :
  ∑ i , v i • b i = (b.repr.symm v) :=
by { classical, simpa using (b.to_basis.equiv_fun_symm_apply v).symm }

variable {v : ι → E}

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

@[simp] lemma _root_.basis.coe_to_orthonormal_basis (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  (v.to_orthonormal_basis hv : ι → E) = (v : ι → E) :=
calc (v.to_orthonormal_basis hv : ι → E) = ((v.to_orthonormal_basis hv).to_basis : ι → E) :
  by { classical, rw orthonormal_basis.coe_to_basis }
... = (v : ι → E) : by simp

/-- An orthonormal set that spans is an orthonormal basis -/
protected def mk (hon : orthonormal 𝕜 v) (hsp: submodule.span 𝕜 (set.range v) = ⊤):
  orthonormal_basis ι 𝕜 E :=
(basis.mk (orthonormal.linear_independent hon) hsp).to_orthonormal_basis (by rwa basis.coe_mk)

@[simp]
protected lemma coe_mk (hon : orthonormal 𝕜 v) (hsp: submodule.span 𝕜 (set.range v) = ⊤) :
  ⇑(orthonormal_basis.mk hon hsp) = v :=
by classical; rw [orthonormal_basis.mk, _root_.basis.coe_to_orthonormal_basis, basis.coe_mk]

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

/-- Given a natural number `n` equal to the `finrank` of a finite-dimensional inner product space,
there exists an isometry from the space to `euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.of_inner_product_space
  [finite_dimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n) :
  E ≃ₗᵢ[𝕜] (euclidean_space 𝕜 (fin n)) :=
((fin_std_orthonormal_basis hn).to_orthonormal_basis
  (fin_std_orthonormal_basis_orthonormal hn)).repr

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.from_orthogonal_span_singleton
  (n : ℕ) [fact (finrank 𝕜 E = n + 1)] {v : E} (hv : v ≠ 0) :
  (𝕜 ∙ v)ᗮ ≃ₗᵢ[𝕜] (euclidean_space 𝕜 (fin n)) :=
linear_isometry_equiv.of_inner_product_space (finrank_orthogonal_span_singleton hv)

section linear_isometry

variables {V : Type*} [inner_product_space 𝕜 V] [finite_dimensional 𝕜 V]

variables {S : submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}

open finite_dimensional

/-- Let `S` be a subspace of a finite-dimensional complex inner product space `V`.  A linear
isometry mapping `S` into `V` can be extended to a full isometry of `V`.

TODO:  The case when `S` is a finite-dimensional subspace of an infinite-dimensional `V`.-/
noncomputable def linear_isometry.extend (L : S →ₗᵢ[𝕜] V): V →ₗᵢ[𝕜] V :=
begin
  -- Build an isometry from Sᗮ to L(S)ᗮ through euclidean_space
  let d := finrank 𝕜 Sᗮ,
  have dim_S_perp : finrank 𝕜 Sᗮ = d := rfl,
  let LS := L.to_linear_map.range,
  have E : Sᗮ ≃ₗᵢ[𝕜] LSᗮ,
  { have dim_LS_perp : finrank 𝕜 LSᗮ = d,
    calc  finrank 𝕜 LSᗮ = finrank 𝕜 V - finrank 𝕜 LS : by simp only
        [← LS.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
      ...               = finrank 𝕜 V - finrank 𝕜 S : by simp only
        [linear_map.finrank_range_of_inj L.injective]
      ...               = finrank 𝕜 Sᗮ : by simp only
        [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
      ...               = d : dim_S_perp,
    let BS := ((fin_std_orthonormal_basis dim_S_perp).to_orthonormal_basis
      (fin_std_orthonormal_basis_orthonormal dim_S_perp)),
    let BLS := ((fin_std_orthonormal_basis dim_LS_perp).to_orthonormal_basis
      (fin_std_orthonormal_basis_orthonormal dim_LS_perp)),
    exact BS.repr.trans BLS.repr.symm },
  let L3 := (LS)ᗮ.subtypeₗᵢ.comp E.to_linear_isometry,
  -- Project onto S and Sᗮ
  haveI : complete_space S := finite_dimensional.complete 𝕜 S,
  haveI : complete_space V := finite_dimensional.complete 𝕜 V,
  let p1 := (orthogonal_projection S).to_linear_map,
  let p2 := (orthogonal_projection Sᗮ).to_linear_map,
  -- Build a linear map from the isometries on S and Sᗮ
  let M := L.to_linear_map.comp p1 + L3.to_linear_map.comp p2,
  -- Prove that M is an isometry
  have M_norm_map : ∀ (x : V), ∥M x∥ = ∥x∥,
  { intro x,
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x),
    { simp only [linear_map.add_apply, linear_map.comp_apply, linear_map.comp_apply,
      linear_isometry.coe_to_linear_map]},
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪ L (p1 x), L3 (p2 x) ⟫ = 0,
    { have Lp1x : L (p1 x) ∈ L.to_linear_map.range := L.to_linear_map.mem_range_self (p1 x),
      have Lp2x : L3 (p2 x) ∈ (L.to_linear_map.range)ᗮ,
      { simp only [L3, linear_isometry.coe_comp, function.comp_app, submodule.coe_subtypeₗᵢ,
          ← submodule.range_subtype (LSᗮ)],
        apply linear_map.mem_range_self},
      apply submodule.inner_right_of_mem_orthogonal Lp1x Lp2x},
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), norm_sq_eq_add_norm_sq_projection x S],
    simp only [sq, Mx_decomp],
    rw norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth,
    simp only [linear_isometry.norm_map, p1, p2, continuous_linear_map.to_linear_map_eq_coe,
      add_left_inj, mul_eq_mul_left_iff, norm_eq_zero, true_or, eq_self_iff_true,
      continuous_linear_map.coe_coe, submodule.coe_norm, submodule.coe_eq_zero] },
  exact { to_linear_map := M, norm_map' := M_norm_map },
end

lemma linear_isometry.extend_apply (L : S →ₗᵢ[𝕜] V) (s : S):
  L.extend s = L s :=
begin
  haveI : complete_space S := finite_dimensional.complete 𝕜 S,
  simp only [linear_isometry.extend, continuous_linear_map.to_linear_map_eq_coe,
    ←linear_isometry.coe_to_linear_map],
  simp only [add_right_eq_self, linear_isometry.coe_to_linear_map,
    linear_isometry_equiv.coe_to_linear_isometry, linear_isometry.coe_comp, function.comp_app,
    orthogonal_projection_mem_subspace_eq_self, linear_map.coe_comp, continuous_linear_map.coe_coe,
    submodule.coe_subtype, linear_map.add_apply, submodule.coe_eq_zero,
    linear_isometry_equiv.map_eq_zero_iff, submodule.coe_subtypeₗᵢ,
    orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
    submodule.orthogonal_orthogonal, submodule.coe_mem],
end

end linear_isometry

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
