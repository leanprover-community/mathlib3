/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.pi_Lp
import linear_algebra.finite_dimensional
import linear_algebra.unitary_group

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `pi_Lp 2`.

This file develops the notion of a finite dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
`E`. We define an `orthonormal_basis 𝕜 ι E` as a linear isometric equivalence
between `E` and `euclidean_space 𝕜 ι`. Then `std_orthonormal_basis` shows that such an equivalence
always exists if `E` is finite dimensional. We provide language for converting between a basis
that is orthonormal and an orthonormal basis (e.g. `basis.to_orthonormal_basis`). We show that
orthonormal bases for each summand in a direct sum of spaces can be combined into an orthonormal
basis for the the whole sum in `direct_sum.submodule_is_internal.subordinate_orthonormal_basis`. In
the last section, various properties of matrices are explored.

## Main definitions

- `euclidean_space 𝕜 n`: defined to be `pi_Lp 2 (n → 𝕜)` for any `fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space).

- `orthonormal_basis 𝕜 ι`: defined to be an isometry to Euclidean space from a given
  finite-dimensional innner product space, `E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι`.

- `basis.to_orthonormal_basis`: constructs an `orthonormal_basis` for a finite-dimensional
  Euclidean space from a `basis` which is `orthonormal`.

- `orthonormal.exists_orthonormal_basis_extension`: provides an existential result of an
  `orthonormal_basis` extending a given orthonormal set

- `exists_orthonormal_basis`: provides an orthonormal basis on a finite dimensional vector space

- `std_orthonormal_basis`: provides an arbitrarily-chosen `orthonormal_basis` of a given finite
  dimensional inner product space

For consequences in infinite dimension (Hilbert bases, etc.), see the file
`analysis.inner_product_space.l2_space`.

-/

open real set filter is_R_or_C submodule function
open_locale big_operators uniformity topology nnreal ennreal complex_conjugate direct_sum

noncomputable theory

variables {ι : Type*} {ι' : Type*}
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
{ to_normed_add_comm_group := infer_instance,
  inner := λ x y, ∑ i, inner (x i) (y i),
  norm_sq_eq_inner := λ x,
    by simp only [pi_Lp.norm_sq_eq_of_L2, add_monoid_hom.map_sum, ← norm_sq_eq_inner, one_div],
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

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
@[reducible, nolint unused_arguments]
def euclidean_space (𝕜 : Type*) [is_R_or_C 𝕜]
  (n : Type*) [fintype n] : Type* := pi_Lp 2 (λ (i : n), 𝕜)

lemma euclidean_space.nnnorm_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x : euclidean_space 𝕜 n) : ‖x‖₊ = nnreal.sqrt (∑ i, ‖x i‖₊ ^ 2) :=
pi_Lp.nnnorm_eq_of_L2 x

lemma euclidean_space.norm_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x : euclidean_space 𝕜 n) : ‖x‖ = real.sqrt (∑ i, ‖x i‖ ^ 2) :=
by simpa only [real.coe_sqrt, nnreal.coe_sum] using congr_arg (coe : ℝ≥0 → ℝ) x.nnnorm_eq

lemma euclidean_space.dist_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x y : euclidean_space 𝕜 n) : dist x y = (∑ i, dist (x i) (y i) ^ 2).sqrt :=
(pi_Lp.dist_eq_of_L2 x y : _)

lemma euclidean_space.nndist_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x y : euclidean_space 𝕜 n) : nndist x y = (∑ i, nndist (x i) (y i) ^ 2).sqrt :=
(pi_Lp.nndist_eq_of_L2 x y : _)

lemma euclidean_space.edist_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x y : euclidean_space 𝕜 n) : edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) :=
(pi_Lp.edist_eq_of_L2 x y : _)

variables [fintype ι]

section
local attribute [reducible] pi_Lp

instance : finite_dimensional 𝕜 (euclidean_space 𝕜 ι) := by apply_instance
instance : inner_product_space 𝕜 (euclidean_space 𝕜 ι) := by apply_instance

@[simp] lemma finrank_euclidean_space :
  finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 ι) = fintype.card ι := by simp

lemma finrank_euclidean_space_fin {n : ℕ} :
  finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 (fin n)) = n := by simp

lemma euclidean_space.inner_eq_star_dot_product (x y : euclidean_space 𝕜 ι) :
  ⟪x, y⟫ = matrix.dot_product (star $ pi_Lp.equiv _ _ x) (pi_Lp.equiv _ _ y) := rfl

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `pi_Lp 2` of the subspaces equipped with the `L2` inner product. -/
def direct_sum.is_internal.isometry_L2_of_orthogonal_family
  [decidable_eq ι] {V : ι → submodule 𝕜 E} (hV : direct_sum.is_internal V)
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  E ≃ₗᵢ[𝕜] pi_Lp 2 (λ i, V i) :=
begin
  let e₁ := direct_sum.linear_equiv_fun_on_fintype 𝕜 ι (λ i, V i),
  let e₂ := linear_equiv.of_bijective (direct_sum.coe_linear_map V) hV,
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

@[simp] lemma direct_sum.is_internal.isometry_L2_of_orthogonal_family_symm_apply
  [decidable_eq ι] {V : ι → submodule 𝕜 E} (hV : direct_sum.is_internal V)
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ))
  (w : pi_Lp 2 (λ i, V i)) :
  (hV.isometry_L2_of_orthogonal_family hV').symm w = ∑ i, (w i : E) :=
begin
  classical,
  let e₁ := direct_sum.linear_equiv_fun_on_fintype 𝕜 ι (λ i, V i),
  let e₂ := linear_equiv.of_bijective (direct_sum.coe_linear_map V) hV,
  suffices : ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i,
  { exact this (e₁.symm w) },
  intros v,
  simp [e₂, direct_sum.coe_linear_map, direct_sum.to_module, dfinsupp.sum_add_hom_apply]
end

end

variables (ι 𝕜)

-- TODO : This should be generalized to `pi_Lp` with finite dimensional factors.
/-- `pi_Lp.linear_equiv` upgraded to a continuous linear map between `euclidean_space 𝕜 ι`
and `ι → 𝕜`. -/
@[simps] def euclidean_space.equiv :
  euclidean_space 𝕜 ι ≃L[𝕜] (ι → 𝕜) :=
(pi_Lp.linear_equiv 2 𝕜 (λ i : ι, 𝕜)).to_continuous_linear_equiv

variables {ι 𝕜}

-- TODO : This should be generalized to `pi_Lp`.
/-- The projection on the `i`-th coordinate of `euclidean_space 𝕜 ι`, as a linear map. -/
@[simps] def euclidean_space.projₗ (i : ι) :
  euclidean_space 𝕜 ι →ₗ[𝕜] 𝕜 :=
(linear_map.proj i).comp (pi_Lp.linear_equiv 2 𝕜 (λ i : ι, 𝕜) : euclidean_space 𝕜 ι →ₗ[𝕜] ι → 𝕜)

-- TODO : This should be generalized to `pi_Lp`.
/-- The projection on the `i`-th coordinate of `euclidean_space 𝕜 ι`,
as a continuous linear map. -/
@[simps] def euclidean_space.proj (i : ι) :
  euclidean_space 𝕜 ι →L[𝕜] 𝕜 :=
⟨euclidean_space.projₗ i, continuous_apply i⟩

-- TODO : This should be generalized to `pi_Lp`.
/-- The vector given in euclidean space by being `1 : 𝕜` at coordinate `i : ι` and `0 : 𝕜` at
all other coordinates. -/
def euclidean_space.single [decidable_eq ι] (i : ι) (a : 𝕜) :
  euclidean_space 𝕜 ι :=
(pi_Lp.equiv _ _).symm (pi.single i a)

@[simp] lemma pi_Lp.equiv_single [decidable_eq ι] (i : ι) (a : 𝕜) :
  pi_Lp.equiv _ _ (euclidean_space.single i a) = pi.single i a := rfl

@[simp] lemma pi_Lp.equiv_symm_single [decidable_eq ι] (i : ι) (a : 𝕜) :
  (pi_Lp.equiv _ _).symm (pi.single i a) = euclidean_space.single i a := rfl

@[simp] theorem euclidean_space.single_apply [decidable_eq ι] (i : ι) (a : 𝕜) (j : ι) :
  (euclidean_space.single i a) j = ite (j = i) a 0 :=
by { rw [euclidean_space.single, pi_Lp.equiv_symm_apply, ← pi.single_apply i a j] }

lemma euclidean_space.inner_single_left [decidable_eq ι] (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) :
  ⟪euclidean_space.single i (a : 𝕜), v⟫ = conj a * (v i) :=
by simp [apply_ite conj]

lemma euclidean_space.inner_single_right [decidable_eq ι] (i : ι) (a : 𝕜)
  (v : euclidean_space 𝕜 ι) :
  ⟪v, euclidean_space.single i (a : 𝕜)⟫ =  a * conj (v i) :=
by simp [apply_ite conj, mul_comm]

lemma euclidean_space.pi_Lp_congr_left_single [decidable_eq ι] {ι' : Type*} [fintype ι']
  [decidable_eq ι'] (e : ι' ≃ ι) (i' : ι') :
  linear_isometry_equiv.pi_Lp_congr_left 2 𝕜 𝕜 e (euclidean_space.single i' (1:𝕜)) =
    euclidean_space.single (e i') (1:𝕜) :=
begin
  ext i,
  simpa using if_congr e.symm_apply_eq rfl rfl
end

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

@[simp] lemma coe_of_repr [decidable_eq ι] (e : E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι) :
  ⇑(orthonormal_basis.of_repr e) = λ i, e.symm (euclidean_space.single i (1 : 𝕜)) :=
begin
  rw coe_fn,
  unfold has_coe_to_fun.coe,
  funext,
  congr,
  simp only [eq_iff_true_of_subsingleton],
end

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
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self i, b.repr_self j,
    euclidean_space.inner_single_left, euclidean_space.single_apply, map_one, one_mul],
end

/-- The `basis ι 𝕜 E` underlying the `orthonormal_basis` -/
protected def to_basis (b : orthonormal_basis ι 𝕜 E) : basis ι 𝕜 E :=
basis.of_equiv_fun b.repr.to_linear_equiv

@[simp] protected lemma coe_to_basis (b : orthonormal_basis ι 𝕜 E) :
  (⇑b.to_basis : ι → E) = ⇑b :=
begin
  change ⇑(basis.of_equiv_fun b.repr.to_linear_equiv) = b,
  ext j,
  classical,
  rw basis.coe_of_equiv_fun,
  congr,
end

@[simp] protected lemma coe_to_basis_repr (b : orthonormal_basis ι 𝕜 E) :
  b.to_basis.equiv_fun = b.repr.to_linear_equiv :=
begin
  change (basis.of_equiv_fun b.repr.to_linear_equiv).equiv_fun = b.repr.to_linear_equiv,
  ext x j,
  simp only [basis.of_equiv_fun_repr_apply, linear_isometry_equiv.coe_to_linear_equiv,
    basis.equiv_fun_apply],
end

@[simp] protected lemma coe_to_basis_repr_apply (b : orthonormal_basis ι 𝕜 E) (x : E) (i : ι) :
  b.to_basis.repr x i = b.repr x i :=
by {rw [← basis.equiv_fun_apply, orthonormal_basis.coe_to_basis_repr,
      linear_isometry_equiv.coe_to_linear_equiv]}

protected lemma sum_repr (b : orthonormal_basis ι 𝕜 E) (x : E) :
  ∑ i, b.repr x i • b i = x :=
by { simp_rw [← b.coe_to_basis_repr_apply, ← b.coe_to_basis], exact b.to_basis.sum_repr x }

protected lemma sum_repr_symm (b : orthonormal_basis ι 𝕜 E) (v : euclidean_space 𝕜 ι) :
  ∑ i , v i • b i = (b.repr.symm v) :=
by { simpa using (b.to_basis.equiv_fun_symm_apply v).symm }

protected lemma sum_inner_mul_inner (b : orthonormal_basis ι 𝕜 E) (x y : E) :
  ∑ i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ :=
begin
  have := congr_arg (@innerSL 𝕜 _ _ _ x) (b.sum_repr y),
  rw map_sum at this,
  convert this,
  ext i,
  rw [smul_hom_class.map_smul, b.repr_apply_apply, mul_comm],
  refl,
end

protected lemma orthogonal_projection_eq_sum {U : submodule 𝕜 E} [complete_space U]
  (b : orthonormal_basis ι 𝕜 U) (x : E) :
  orthogonal_projection U x = ∑ i, ⟪(b i : E), x⟫ • b i :=
by simpa only [b.repr_apply_apply, inner_orthogonal_projection_eq_of_mem_left]
  using (b.sum_repr (orthogonal_projection U x)).symm

/-- Mapping an orthonormal basis along a `linear_isometry_equiv`. -/
protected def map {G : Type*} [inner_product_space 𝕜 G] (b : orthonormal_basis ι 𝕜 E)
  (L : E ≃ₗᵢ[𝕜] G) :
  orthonormal_basis ι 𝕜 G :=
{ repr := L.symm.trans b.repr }

@[simp] protected lemma map_apply {G : Type*} [inner_product_space 𝕜 G]
  (b : orthonormal_basis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) (i : ι) :
  b.map L i = L (b i) := rfl

@[simp] protected lemma to_basis_map {G : Type*} [inner_product_space 𝕜 G]
  (b : orthonormal_basis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) :
  (b.map L).to_basis = b.to_basis.map L.to_linear_equiv :=
rfl

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

variable {v : ι → E}

/-- A finite orthonormal set that spans is an orthonormal basis -/
protected def mk (hon : orthonormal 𝕜 v) (hsp: ⊤ ≤ submodule.span 𝕜 (set.range v)):
  orthonormal_basis ι 𝕜 E :=
(basis.mk (orthonormal.linear_independent hon) hsp).to_orthonormal_basis (by rwa basis.coe_mk)

@[simp]
protected lemma coe_mk (hon : orthonormal 𝕜 v) (hsp: ⊤ ≤ submodule.span 𝕜 (set.range v)) :
  ⇑(orthonormal_basis.mk hon hsp) = v :=
by classical; rw [orthonormal_basis.mk, _root_.basis.coe_to_orthonormal_basis, basis.coe_mk]

/-- Any finite subset of a orthonormal family is an `orthonormal_basis` for its span. -/
protected def span [decidable_eq E] {v' : ι' → E} (h : orthonormal 𝕜 v') (s : finset ι') :
  orthonormal_basis s 𝕜 (span 𝕜 (s.image v' : set E)) :=
let
  e₀' : basis s 𝕜 _ := basis.span (h.linear_independent.comp (coe : s → ι') subtype.coe_injective),
  e₀ : orthonormal_basis s 𝕜 _ := orthonormal_basis.mk
    begin
      convert orthonormal_span (h.comp (coe : s → ι') subtype.coe_injective),
      ext,
      simp [e₀', basis.span_apply],
    end e₀'.span_eq.ge,
  φ : span 𝕜 (s.image v' : set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ (coe : s → ι'))) :=
    linear_isometry_equiv.of_eq _ _
    begin
      rw [finset.coe_image, image_eq_range],
      refl
    end
in
e₀.map φ.symm

@[simp] protected lemma span_apply [decidable_eq E]
  {v' : ι' → E} (h : orthonormal 𝕜 v') (s : finset ι') (i : s) :
  (orthonormal_basis.span h s i : E) = v' i :=
by simp only [orthonormal_basis.span, basis.span_apply, linear_isometry_equiv.of_eq_symm,
              orthonormal_basis.map_apply, orthonormal_basis.coe_mk,
              linear_isometry_equiv.coe_of_eq_apply]

open submodule

/-- A finite orthonormal family of vectors whose span has trivial orthogonal complement is an
orthonormal basis. -/
protected def mk_of_orthogonal_eq_bot (hon : orthonormal 𝕜 v) (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) :
  orthonormal_basis ι 𝕜 E :=
orthonormal_basis.mk hon
begin
  refine eq.ge _,
  haveI : finite_dimensional 𝕜 (span 𝕜 (range v)) :=
    finite_dimensional.span_of_finite 𝕜 (finite_range v),
  haveI : complete_space (span 𝕜 (range v)) := finite_dimensional.complete 𝕜 _,
  rwa orthogonal_eq_bot_iff at hsp,
end

@[simp] protected lemma coe_of_orthogonal_eq_bot_mk (hon : orthonormal 𝕜 v)
  (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) :
  ⇑(orthonormal_basis.mk_of_orthogonal_eq_bot hon hsp) = v :=
orthonormal_basis.coe_mk hon _

variables [fintype ι']

/-- `b.reindex (e : ι ≃ ι')` is an `orthonormal_basis` indexed by `ι'` -/
def reindex (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') : orthonormal_basis ι' 𝕜 E :=
orthonormal_basis.of_repr (b.repr.trans (linear_isometry_equiv.pi_Lp_congr_left 2 𝕜 𝕜 e))

protected lemma reindex_apply (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
  (b.reindex e) i' = b (e.symm i') :=
begin
  classical,
  dsimp [reindex, orthonormal_basis.has_coe_to_fun],
  rw coe_of_repr,
  dsimp,
  rw [← b.repr_symm_single, linear_isometry_equiv.pi_Lp_congr_left_symm,
    euclidean_space.pi_Lp_congr_left_single],
end

@[simp] protected lemma coe_reindex (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') :
  ⇑(b.reindex e) = ⇑b ∘ ⇑(e.symm) :=
funext (b.reindex_apply e)

@[simp] protected lemma repr_reindex
  (b : orthonormal_basis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
  (b.reindex e).repr x i' = b.repr x (e.symm i') :=
by { classical,
  rw [orthonormal_basis.repr_apply_apply, b.repr_apply_apply, orthonormal_basis.coe_reindex] }

end orthonormal_basis

/-- `![1, I]` is an orthonormal basis for `ℂ` considered as a real inner product space. -/
def complex.orthonormal_basis_one_I : orthonormal_basis (fin 2) ℝ ℂ :=
(complex.basis_one_I.to_orthonormal_basis
begin
  rw orthonormal_iff_ite,
  intros i, fin_cases i;
  intros j; fin_cases j;
  simp [real_inner_eq_re_inner]
end)

@[simp] lemma complex.orthonormal_basis_one_I_repr_apply (z : ℂ) :
  complex.orthonormal_basis_one_I.repr z =  ![z.re, z.im] :=
rfl

@[simp] lemma complex.orthonormal_basis_one_I_repr_symm_apply (x : euclidean_space ℝ (fin 2)) :
  complex.orthonormal_basis_one_I.repr.symm x = (x 0) + (x 1) * I :=
rfl

@[simp] lemma complex.to_basis_orthonormal_basis_one_I :
  complex.orthonormal_basis_one_I.to_basis = complex.basis_one_I :=
basis.to_basis_to_orthonormal_basis _ _

@[simp] lemma complex.coe_orthonormal_basis_one_I :
  (complex.orthonormal_basis_one_I : (fin 2) → ℂ) = ![1, I] :=
by simp [complex.orthonormal_basis_one_I]

/-- The isometry between `ℂ` and a two-dimensional real inner product space given by a basis. -/
def complex.isometry_of_orthonormal (v : orthonormal_basis (fin 2) ℝ F) : ℂ ≃ₗᵢ[ℝ] F :=
complex.orthonormal_basis_one_I.repr.trans v.repr.symm

@[simp] lemma complex.map_isometry_of_orthonormal (v : orthonormal_basis (fin 2) ℝ F)
  (f : F ≃ₗᵢ[ℝ] F') :
  complex.isometry_of_orthonormal (v.map f) =
    (complex.isometry_of_orthonormal v).trans f :=
by simp [complex.isometry_of_orthonormal, linear_isometry_equiv.trans_assoc, orthonormal_basis.map]

lemma complex.isometry_of_orthonormal_symm_apply
  (v : orthonormal_basis (fin 2) ℝ F) (f : F) :
  (complex.isometry_of_orthonormal v).symm f
  = (v.to_basis.coord 0 f : ℂ) + (v.to_basis.coord 1 f : ℂ) * I :=
by simp [complex.isometry_of_orthonormal]

lemma complex.isometry_of_orthonormal_apply
  (v : orthonormal_basis (fin 2) ℝ F) (z : ℂ) :
  complex.isometry_of_orthonormal v z = z.re • v 0 + z.im • v 1 :=
by simp [complex.isometry_of_orthonormal, ← v.sum_repr_symm]

open finite_dimensional

/-! ### Matrix representation of an orthonormal basis with respect to another -/

section to_matrix
variables [decidable_eq ι]

section
variables (a b : orthonormal_basis ι 𝕜 E)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is a unitary matrix. -/
lemma orthonormal_basis.to_matrix_orthonormal_basis_mem_unitary :
  a.to_basis.to_matrix b ∈ matrix.unitary_group ι 𝕜 :=
begin
  rw matrix.mem_unitary_group_iff',
  ext i j,
  convert a.repr.inner_map_map (b i) (b j),
  rw orthonormal_iff_ite.mp b.orthonormal i j,
  refl,
end

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` has
unit length. -/
@[simp] lemma orthonormal_basis.det_to_matrix_orthonormal_basis :
  ‖a.to_basis.det b‖ = 1 :=
begin
  have : (norm_sq (a.to_basis.det b) : 𝕜) = 1,
  { simpa [is_R_or_C.mul_conj]
      using (matrix.det_of_mem_unitary (a.to_matrix_orthonormal_basis_mem_unitary b)).2 },
  norm_cast at this,
  rwa [← sqrt_norm_sq_eq_norm, sqrt_eq_one],
end

end

section real
variables (a b : orthonormal_basis ι ℝ F)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is an orthogonal matrix. -/
lemma orthonormal_basis.to_matrix_orthonormal_basis_mem_orthogonal :
  a.to_basis.to_matrix b ∈ matrix.orthogonal_group ι ℝ :=
a.to_matrix_orthonormal_basis_mem_unitary b

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` is ±1. -/
lemma orthonormal_basis.det_to_matrix_orthonormal_basis_real :
  a.to_basis.det b = 1 ∨ a.to_basis.det b = -1 :=
begin
  rw ← sq_eq_one_iff,
  simpa [unitary, sq] using matrix.det_of_mem_unitary (a.to_matrix_orthonormal_basis_mem_unitary b)
end

end real

end to_matrix

/-! ### Existence of orthonormal basis, etc. -/

section finite_dimensional

variables {v : set E}

variables {A : ι → submodule 𝕜 E}

/-- Given an internal direct sum decomposition of a module `M`, and an orthonormal basis for each
of the components of the direct sum, the disjoint union of these orthonormal bases is an
orthonormal basis for `M`. -/
noncomputable def direct_sum.is_internal.collected_orthonormal_basis
  (hV : @orthogonal_family 𝕜 _ _ _ _ (λ i, A i) _ (λ i, (A i).subtypeₗᵢ))
  [decidable_eq ι] (hV_sum : direct_sum.is_internal (λ i, A i)) {α : ι → Type*}
  [Π i, fintype (α i)] (v_family : Π i, orthonormal_basis (α i) 𝕜 (A i)) :
  orthonormal_basis (Σ i, α i) 𝕜 E :=
(hV_sum.collected_basis (λ i, (v_family i).to_basis)).to_orthonormal_basis $
by simpa using hV.orthonormal_sigma_orthonormal
  (show (∀ i, orthonormal 𝕜 (v_family i).to_basis), by simp)

lemma direct_sum.is_internal.collected_orthonormal_basis_mem [decidable_eq ι]
  (h : direct_sum.is_internal A) {α : ι → Type*}
  [Π i, fintype (α i)] (hV : @orthogonal_family 𝕜 _ _ _ _ (λ i, A i) _ (λ i, (A i).subtypeₗᵢ))
  (v : Π i, orthonormal_basis (α i) 𝕜 (A i)) (a : Σ i, α i) :
  h.collected_orthonormal_basis hV v a ∈ A a.1 :=
by simp [direct_sum.is_internal.collected_orthonormal_basis]

variables [finite_dimensional 𝕜 E]

/-- In a finite-dimensional `inner_product_space`, any orthonormal subset can be extended to an
orthonormal basis. -/
lemma _root_.orthonormal.exists_orthonormal_basis_extension (hv : orthonormal 𝕜 (coe : v → E)) :
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

lemma _root_.orthonormal.exists_orthonormal_basis_extension_of_card_eq
  {ι : Type*} [fintype ι] (card_ι : finrank 𝕜 E = fintype.card ι) {v : ι → E} {s : set ι}
  (hv : orthonormal 𝕜 (s.restrict v)) :
  ∃ b : orthonormal_basis ι 𝕜 E, ∀ i ∈ s, b i = v i :=
begin
  have hsv : injective (s.restrict v) := hv.linear_independent.injective,
  have hX : orthonormal 𝕜 (coe : set.range (s.restrict v) → E),
  { rwa orthonormal_subtype_range hsv },
  obtain ⟨Y, b₀, hX, hb₀⟩ := hX.exists_orthonormal_basis_extension,
  have hιY : fintype.card ι = Y.card,
  { refine (card_ι.symm.trans _),
    exact finite_dimensional.finrank_eq_card_finset_basis b₀.to_basis },
  have hvsY : s.maps_to v Y := (s.maps_to_image v).mono_right (by rwa ← range_restrict),
  have hsv' : set.inj_on v s,
  { rw set.inj_on_iff_injective,
    exact hsv },
  obtain ⟨g, hg⟩ := hvsY.exists_equiv_extend_of_card_eq hιY hsv',
  use b₀.reindex g.symm,
  intros i hi,
  { simp [hb₀, hg i hi] },
end

variables (𝕜 E)

/-- A finite-dimensional inner product space admits an orthonormal basis. -/
lemma _root_.exists_orthonormal_basis :
  ∃ (w : finset E) (b : orthonormal_basis w 𝕜 E), ⇑b = (coe : w → E) :=
let ⟨w, hw, hw', hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormal_basis_extension in
⟨w, hw, hw''⟩

/-- A finite-dimensional `inner_product_space` has an orthonormal basis. -/
@[irreducible] def std_orthonormal_basis : orthonormal_basis (fin (finrank 𝕜 E)) 𝕜 E :=
begin
  let b := classical.some (classical.some_spec $ exists_orthonormal_basis 𝕜 E),
  rw [finrank_eq_card_basis b.to_basis],
  exact b.reindex (fintype.equiv_fin_of_card_eq rfl),
end

/-- An orthonormal basis of `ℝ` is made either of the vector `1`, or of the vector `-1`. -/
lemma orthonormal_basis_one_dim (b : orthonormal_basis ι ℝ ℝ) :
  ⇑b = (λ _, (1 : ℝ)) ∨ ⇑b = (λ _, (-1 : ℝ)) :=
begin
  haveI : unique ι, from b.to_basis.unique,
  have : b default = 1 ∨ b default = - 1,
  { have : ‖b default‖ = 1, from b.orthonormal.1 _,
    rwa [real.norm_eq_abs, abs_eq (zero_le_one : (0 : ℝ) ≤ 1)] at this },
  rw eq_const_of_unique b,
  refine this.imp _ _; simp,
end

variables {𝕜 E}

section subordinate_orthonormal_basis
open direct_sum
variables {n : ℕ} (hn : finrank 𝕜 E = n) [decidable_eq ι]
  {V : ι → submodule 𝕜 E} (hV : is_internal V)

/-- Exhibit a bijection between `fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`.  This should not be accessed directly, but only via the subsequent API. -/
@[irreducible] def direct_sum.is_internal.sigma_orthonormal_basis_index_equiv
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  (Σ i, fin (finrank 𝕜 (V i))) ≃ fin n :=
let b := hV.collected_orthonormal_basis hV' (λ i, (std_orthonormal_basis 𝕜 (V i))) in
fintype.equiv_fin_of_card_eq $ (finite_dimensional.finrank_eq_card_basis b.to_basis).symm.trans hn

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. -/
@[irreducible] def direct_sum.is_internal.subordinate_orthonormal_basis
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  orthonormal_basis (fin n) 𝕜 E :=
((hV.collected_orthonormal_basis hV' (λ i, (std_orthonormal_basis 𝕜 (V i)))).reindex
  (hV.sigma_orthonormal_basis_index_equiv hn hV'))

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. This function
provides the mapping by which it is subordinate. -/
@[irreducible] def direct_sum.is_internal.subordinate_orthonormal_basis_index
  (a : fin n) (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) : ι :=
((hV.sigma_orthonormal_basis_index_equiv hn hV').symm a).1

/-- The basis constructed in `orthogonal_family.subordinate_orthonormal_basis` is subordinate to
the `orthogonal_family` in question. -/
lemma direct_sum.is_internal.subordinate_orthonormal_basis_subordinate
  (a : fin n) (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  (hV.subordinate_orthonormal_basis hn hV' a) ∈
  V (hV.subordinate_orthonormal_basis_index hn a hV') :=
by simpa only [direct_sum.is_internal.subordinate_orthonormal_basis,
  orthonormal_basis.coe_reindex, direct_sum.is_internal.subordinate_orthonormal_basis_index]
  using hV.collected_orthonormal_basis_mem hV' (λ i, (std_orthonormal_basis 𝕜 (V i)))
    ((hV.sigma_orthonormal_basis_index_equiv hn hV').symm a)

end subordinate_orthonormal_basis

end finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def orthonormal_basis.from_orthogonal_span_singleton
  (n : ℕ) [fact (finrank 𝕜 E = n + 1)] {v : E} (hv : v ≠ 0) :
  orthonormal_basis (fin n) 𝕜 (𝕜 ∙ v)ᗮ :=
(std_orthonormal_basis _ _).reindex $ fin_congr $ finrank_orthogonal_span_singleton hv

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
        [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left],
    exact (std_orthonormal_basis 𝕜 Sᗮ).repr.trans
      ((std_orthonormal_basis 𝕜 LSᗮ).reindex $ fin_congr dim_LS_perp).repr.symm },
  let L3 := (LS)ᗮ.subtypeₗᵢ.comp E.to_linear_isometry,
  -- Project onto S and Sᗮ
  haveI : complete_space S := finite_dimensional.complete 𝕜 S,
  haveI : complete_space V := finite_dimensional.complete 𝕜 V,
  let p1 := (orthogonal_projection S).to_linear_map,
  let p2 := (orthogonal_projection Sᗮ).to_linear_map,
  -- Build a linear map from the isometries on S and Sᗮ
  let M := L.to_linear_map.comp p1 + L3.to_linear_map.comp p2,
  -- Prove that M is an isometry
  have M_norm_map : ∀ (x : V), ‖M x‖ = ‖x‖,
  { intro x,
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x),
    { simp only [linear_map.add_apply, linear_map.comp_apply, linear_map.comp_apply,
      linear_isometry.coe_to_linear_map]},
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪ L (p1 x), L3 (p2 x) ⟫ = 0,
    { have Lp1x : L (p1 x) ∈ L.to_linear_map.range :=
        linear_map.mem_range_self L.to_linear_map (p1 x),
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
