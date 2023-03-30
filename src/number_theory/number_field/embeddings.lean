/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/

import analysis.complex.polynomial
import field_theory.minpoly.is_integrally_closed
import number_theory.number_field.basic
import ring_theory.norm
import topology.instances.complex


/-!
# Embeddings of number fields
This file defines the embeddings of a number field into an algebraic closed field.

## Main Results
* `number_field.embeddings.range_eval_eq_root_set_minpoly`: let `x ∈ K` with `K` number field and
  let `A` be an algebraic closed field of char. 0, then the images of `x` by the embeddings of `K`
   in `A` are exactly the roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `number_field.embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags
number field, embeddings, places, infinite places
-/

open_locale classical

namespace number_field.embeddings

section fintype

open finite_dimensional

variables (K : Type*) [field K] [number_field K]
variables (A : Type*) [field A] [char_zero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : fintype (K →+* A) := fintype.of_equiv (K →ₐ[ℚ] A)
ring_hom.equiv_rat_alg_hom.symm

variables [is_alg_closed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
lemma card : fintype.card (K →+* A) = finrank ℚ K :=
by rw [fintype.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, alg_hom.card]

instance : nonempty (K →+* A) :=
begin
  rw [← fintype.card_pos_iff, number_field.embeddings.card K A],
  exact finite_dimensional.finrank_pos,
end

end fintype

section roots

open set polynomial

variables (K A : Type*) [field K] [number_field K]
  [field A] [algebra ℚ A] [is_alg_closed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
lemma range_eval_eq_root_set_minpoly : range (λ φ : K →+* A, φ x) = (minpoly ℚ x).root_set A :=
begin
  convert (number_field.is_algebraic K).range_eval_eq_root_set_minpoly A x using 1,
  ext a,
  exact ⟨λ ⟨φ, hφ⟩, ⟨φ.to_rat_alg_hom, hφ⟩, λ ⟨φ, hφ⟩, ⟨φ.to_ring_hom, hφ⟩⟩,
end

end roots

section bounded

open finite_dimensional polynomial set

variables {K : Type*} [field K] [number_field K]
variables {A : Type*} [normed_field A] [is_alg_closed A] [normed_algebra ℚ A]

lemma coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
  ‖(minpoly ℚ x).coeff i‖ ≤ (max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2) :=
begin
  have hx := is_separable.is_integral ℚ x,
  rw [← norm_algebra_map' A, ← coeff_map (algebra_map ℚ A)],
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx) (is_alg_closed.splits_codomain _)
    (minpoly.nat_degree_le hx) (λ z hz, _) i,
  classical, rw ← multiset.mem_to_finset at hz,
  obtain ⟨φ, rfl⟩ := (range_eval_eq_root_set_minpoly K A x).symm.subset hz,
  exact h φ,
end

variables (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
lemma finite_of_norm_le (B : ℝ) :
  {x : K | is_integral ℤ x ∧ ∀ φ : K →+* A, ‖φ x‖ ≤ B}.finite :=
begin
  let C := nat.ceil ((max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2)),
  have := bUnion_roots_finite (algebra_map ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C),
  refine this.subset (λ x hx, _), simp_rw mem_Union,
  have h_map_ℚ_minpoly := minpoly.is_integrally_closed_eq_field_fractions' ℚ hx.1,
  refine ⟨_, ⟨_, λ i, _⟩, mem_root_set.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval ℤ x⟩⟩,
  { rw [← (minpoly.monic hx.1).nat_degree_map (algebra_map ℤ ℚ), ← h_map_ℚ_minpoly],
    exact minpoly.nat_degree_le (is_integral_of_is_scalar_tower hx.1) },
  rw [mem_Icc, ← abs_le, ← @int.cast_le ℝ],
  refine (eq.trans_le _ $ coeff_bdd_of_norm_le hx.2 i).trans (nat.le_ceil _),
  rw [h_map_ℚ_minpoly, coeff_map, eq_int_cast, int.norm_cast_rat, int.norm_eq_abs, int.cast_abs],
end

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
lemma pow_eq_one_of_norm_eq_one {x : K}
  (hxi : is_integral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
  ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @set.infinite.exists_ne_map_eq_of_maps_to _ _ _ _
    ((^) x : ℕ → K) set.infinite_univ _ (finite_of_norm_le K A (1:ℝ)),
  { wlog hlt : b < a,
    { exact this hxi hx b a habne.symm h.symm (habne.lt_or_lt.resolve_right hlt) },
    refine ⟨a - b, tsub_pos_of_lt hlt, _⟩,
    rw [← nat.sub_add_cancel hlt.le, pow_add, mul_left_eq_self₀] at h,
    refine h.resolve_right (λ hp, _),
    specialize hx (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom,
    rw [pow_eq_zero hp, map_zero, norm_zero] at hx, norm_num at hx },
  { exact λ a _, ⟨hxi.pow a, λ φ, by simp only [hx φ, norm_pow, one_pow, map_pow]⟩ },
end

end bounded

end number_field.embeddings

section place

variables {K : Type*} [field K] {A : Type*} [normed_division_ring A] [nontrivial A] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def number_field.place : absolute_value K ℝ :=
(is_absolute_value.to_absolute_value (norm : A → ℝ)).comp φ.injective

@[simp]
lemma number_field.place_apply (x : K) : (number_field.place φ) x = norm (φ x) := rfl

end place

namespace number_field.complex_embedding

open complex number_field

open_locale complex_conjugate

variables {K : Type*} [field K]

/-- The conjugate of a complex embedding as a complex embedding. -/
@[reducible] def conjugate (φ : K →+* ℂ) : K →+* ℂ := star φ

@[simp]
lemma conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) := rfl

lemma place_conjugate (φ : K →+* ℂ) : place (conjugate φ) = place φ :=
by { ext, simp only [place_apply, norm_eq_abs, abs_conj, conjugate_coe_eq] }

/-- A embedding into `ℂ` is real if it is fixed by complex conjugation. -/
@[reducible] def is_real (φ : K →+* ℂ) : Prop := is_self_adjoint φ

lemma is_real_iff {φ : K →+* ℂ} : is_real φ ↔ conjugate φ = φ := is_self_adjoint_iff

/-- A real embedding as a ring homomorphism from `K` to `ℝ` . -/
def is_real.embedding {φ : K →+* ℂ} (hφ : is_real φ) : K →+* ℝ :=
{ to_fun := λ x, (φ x).re,
  map_one' := by simp only [map_one, one_re],
  map_mul' := by simp only [complex.eq_conj_iff_im.mp (ring_hom.congr_fun hφ _), map_mul, mul_re,
  mul_zero, tsub_zero, eq_self_iff_true, forall_const],
  map_zero' := by simp only [map_zero, zero_re],
  map_add' := by simp only [map_add, add_re, eq_self_iff_true, forall_const], }

@[simp]
lemma is_real.coe_embedding_apply {φ : K →+* ℂ} (hφ : is_real φ) (x : K) :
  (hφ.embedding x : ℂ) = φ x :=
begin
  ext, { refl, },
  { rw [of_real_im, eq_comm, ← complex.eq_conj_iff_im],
    rw is_real at hφ,
    exact ring_hom.congr_fun hφ x, },
end

lemma is_real.place_embedding {φ : K →+* ℂ} (hφ : is_real φ) :
  place hφ.embedding = place φ :=
by { ext x, simp only [place_apply, real.norm_eq_abs, ←abs_of_real, norm_eq_abs,
  hφ.coe_embedding_apply x], }

lemma is_real_conjugate_iff {φ : K →+* ℂ} :
  is_real (conjugate φ) ↔ is_real φ := is_self_adjoint.star_iff

end number_field.complex_embedding

section infinite_place

open number_field

variables (K : Type*) [field K]

/-- An infinite place of a number field `K` is a place associated to a complex embedding. -/
def number_field.infinite_place := { w : absolute_value K ℝ  // ∃ φ : K →+* ℂ, place φ = w}

instance [number_field K] : nonempty (number_field.infinite_place K) := set.range.nonempty _

variables {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
noncomputable def number_field.infinite_place.mk (φ : K →+* ℂ) : number_field.infinite_place K :=
⟨place φ, ⟨φ, rfl⟩⟩

namespace number_field.infinite_place

open number_field

instance : has_coe_to_fun (infinite_place K) (λ _, K → ℝ) := { coe := λ w, w.1 }

instance : monoid_with_zero_hom_class (infinite_place K) K ℝ :=
{ coe := λ w x, w.1 x,
  coe_injective' := λ _ _ h, subtype.eq (absolute_value.ext (λ x, congr_fun h x)),
  map_mul := λ w _ _, w.1.map_mul _ _,
  map_one := λ w, w.1.map_one,
  map_zero := λ w, w.1.map_zero, }

instance : nonneg_hom_class (infinite_place K) K ℝ :=
{ coe :=  λ w x, w x,
  coe_injective' := λ _ _ h, subtype.eq (absolute_value.ext (λ x, congr_fun h x)),
  map_nonneg := λ w x, w.1.nonneg _ }

lemma coe_mk (φ : K →+* ℂ) : ⇑(mk φ) = place φ := rfl

lemma apply (φ : K →+* ℂ) (x : K) : (mk φ) x = complex.abs (φ x) := rfl

/-- For an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
noncomputable def embedding (w : infinite_place K) : K →+* ℂ := (w.2).some

@[simp]
lemma mk_embedding (w : infinite_place K) :
  mk (embedding w) = w :=
subtype.ext (w.2).some_spec

@[simp]
lemma abs_embedding (w : infinite_place K) (x : K) :
  complex.abs (embedding w x) = w x := congr_fun (congr_arg coe_fn w.2.some_spec) x

lemma eq_iff_eq (x : K) (r : ℝ) :
  (∀ w : infinite_place K, w x = r) ↔ (∀ φ : K →+* ℂ, ‖φ x‖ = r) :=
⟨λ hw φ, hw (mk φ), λ hφ ⟨w, ⟨φ, rfl⟩⟩, hφ φ⟩

lemma le_iff_le (x : K) (r : ℝ) :
  (∀ w : infinite_place K, w x ≤ r) ↔ (∀ φ : K →+* ℂ, ‖φ x‖ ≤ r) :=
⟨λ hw φ, hw (mk φ), λ hφ ⟨w, ⟨φ, rfl⟩⟩, hφ φ⟩

lemma pos_iff {w : infinite_place K} {x : K} : 0 < w x ↔ x ≠ 0 := absolute_value.pos_iff w.1

@[simp]
lemma mk_conjugate_eq (φ : K →+* ℂ) :
  mk (complex_embedding.conjugate φ) = mk φ :=
begin
  ext x,
  exact congr_fun (congr_arg coe_fn (complex_embedding.place_conjugate φ)) x,
end

@[simp]
lemma mk_eq_iff {φ ψ : K →+* ℂ} :
  mk φ = mk ψ ↔ φ = ψ ∨ complex_embedding.conjugate φ = ψ :=
begin
  split,
  { -- We prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform continuous, thus it is either the
    -- inclusion or the complex conjugation using complex.uniform_continuous_ring_hom_eq_id_or_conj
    intro h₀,
    obtain ⟨j, hiφ⟩ := φ.injective.has_left_inverse,
    let ι := ring_equiv.of_left_inverse hiφ,
    have hlip : lipschitz_with 1 (ring_hom.comp ψ ι.symm.to_ring_hom),
    { change lipschitz_with 1 (ψ ∘ ι.symm),
      apply lipschitz_with.of_dist_le_mul,
      intros x y,
      rw [nonneg.coe_one, one_mul, normed_field.dist_eq, ← map_sub, ← map_sub],
      apply le_of_eq,
      suffices : ‖φ ((ι.symm) (x - y))‖ = ‖ψ ((ι.symm) (x - y))‖,
      { rw [← this, ← ring_equiv.of_left_inverse_apply hiφ _ , ring_equiv.apply_symm_apply ι _],
        refl, },
      exact congr_fun (congr_arg coe_fn h₀) _, },
    cases (complex.uniform_continuous_ring_hom_eq_id_or_conj φ.field_range hlip.uniform_continuous),
    { left, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, },
    { right, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, }},
  { rintros (⟨h⟩ | ⟨h⟩),
    { exact congr_arg mk h, },
    { rw ← mk_conjugate_eq,
      exact congr_arg mk h, }},
end

/-- An infinite place is real if it is defined by a real embedding. -/
def is_real (w : infinite_place K) : Prop :=
  ∃ φ : K →+* ℂ, complex_embedding.is_real φ ∧ mk φ = w

/-- An infinite place is complex if it is defined by a complex (ie. not real) embedding. -/
def is_complex (w : infinite_place K) : Prop :=
  ∃ φ : K →+* ℂ, ¬ complex_embedding.is_real φ ∧ mk φ = w

@[simp]
lemma _root_.number_field.complex_embeddings.is_real.embedding_mk {φ : K →+* ℂ}
  (h : complex_embedding.is_real φ) :
  embedding (mk φ) = φ :=
begin
  have := mk_eq_iff.mp (mk_embedding (mk φ)).symm,
  rwa [complex_embedding.is_real_iff.mp h, or_self, eq_comm] at this,
end

lemma is_real_iff {w : infinite_place K} :
  is_real w ↔ complex_embedding.is_real (embedding w) :=
begin
  split,
  { rintros ⟨φ, ⟨hφ, rfl⟩⟩,
    rwa _root_.number_field.complex_embeddings.is_real.embedding_mk hφ, },
  { exact λ h, ⟨embedding w, h, mk_embedding w⟩, },
end

lemma is_complex_iff {w : infinite_place K} :
  is_complex w ↔ ¬ complex_embedding.is_real (embedding w) :=
begin
  split,
  { rintros ⟨φ, ⟨hφ, rfl⟩⟩,
    contrapose! hφ,
    cases mk_eq_iff.mp (mk_embedding (mk φ)),
    { rwa ← h, },
    { rw ← complex_embedding.is_real_conjugate_iff at hφ,
      rwa ← h, }},
  { exact λ h, ⟨embedding w, h, mk_embedding w⟩, },
end

lemma not_is_real_iff_is_complex {w : infinite_place K} :
  ¬ is_real w ↔ is_complex w :=
by rw [is_complex_iff, is_real_iff]

/-- For `w` a real infinite place, return the corresponding embedding as a morphism `K →+* ℝ`. -/
noncomputable def is_real.embedding {w : infinite_place K} (hw : is_real w) : K →+* ℝ :=
(is_real_iff.mp hw).embedding

@[simp]
lemma is_real.place_embedding_apply {w : infinite_place K} (hw : is_real w) (x : K):
  place (is_real.embedding hw) x = w x :=
begin
  rw [is_real.embedding, complex_embedding.is_real.place_embedding, ← coe_mk],
  exact congr_fun (congr_arg coe_fn (mk_embedding w)) x,
end

variable (K)

/-- The map from real embeddings to real infinite places as an equiv -/
noncomputable def mk_real :
  {φ : K →+* ℂ // complex_embedding.is_real φ} ≃ {w : infinite_place K // is_real w} :=
{ to_fun := subtype.map mk (λ φ hφ, ⟨φ, hφ, rfl⟩),
  inv_fun :=  λ w, ⟨w.1.embedding, is_real_iff.1 w.2⟩,
  left_inv := λ φ, subtype.ext_iff.2 (number_field.complex_embeddings.is_real.embedding_mk φ.2),
  right_inv := λ w, subtype.ext_iff.2 (mk_embedding w.1), }

/-- The map from nonreal embeddings to complex infinite places -/
noncomputable def mk_complex :
  {φ : K →+* ℂ // ¬ complex_embedding.is_real φ} → {w : infinite_place K // is_complex w} :=
subtype.map mk (λ φ hφ, ⟨φ, hφ, rfl⟩)

lemma mk_complex_embedding (φ : {φ : K →+* ℂ // ¬ complex_embedding.is_real φ}) :
  ((mk_complex K φ) : infinite_place K).embedding = φ ∨
    ((mk_complex K φ) : infinite_place K).embedding = complex_embedding.conjugate φ :=
begin
  rw [@eq_comm _ _ ↑φ, @eq_comm _ _ (complex_embedding.conjugate ↑φ), ← mk_eq_iff, mk_embedding],
  refl,
end

@[simp]
lemma mk_real_coe (φ : {φ : K →+* ℂ // complex_embedding.is_real φ}) :
  (mk_real K φ : infinite_place K) = mk (φ : K →+* ℂ) := rfl

@[simp]
lemma mk_complex_coe (φ : {φ : K →+* ℂ // ¬ complex_embedding.is_real φ}) :
  (mk_complex K φ : infinite_place K) = mk (φ : K →+* ℂ) := rfl

@[simp]
lemma mk_real.apply (φ : {φ : K →+* ℂ // complex_embedding.is_real φ}) (x : K) :
  mk_real K φ x = complex.abs (φ x) := apply φ x

@[simp]
lemma mk_complex.apply (φ : {φ : K →+* ℂ // ¬ complex_embedding.is_real φ}) (x : K) :
  mk_complex K φ x = complex.abs (φ x) := apply φ x

variable [number_field K]

lemma mk_complex.filter (w : { w : infinite_place K // w.is_complex }) :
  finset.univ.filter (λ φ, mk_complex K φ = w) =
    { ⟨w.1.embedding, is_complex_iff.1 w.2⟩,
      ⟨complex_embedding.conjugate w.1.embedding,
        complex_embedding.is_real_conjugate_iff.not.2 (is_complex_iff.1 w.2)⟩ } :=
begin
  ext φ,
  simp_rw [finset.mem_filter, subtype.val_eq_coe, finset.mem_insert, finset.mem_singleton,
    @subtype.ext_iff_val (infinite_place K), @subtype.ext_iff_val (K →+* ℂ), @eq_comm _ φ.val,
    ← mk_eq_iff, mk_embedding, @eq_comm _ _ w.val],
  simpa only [finset.mem_univ, true_and],
end

lemma mk_complex.filter_card (w : { w : infinite_place K // w.is_complex }) :
  (finset.univ.filter (λ φ, mk_complex K φ = w)).card = 2 :=
begin
  rw mk_complex.filter,
  exact finset.card_doubleton
    (subtype.mk_eq_mk.not.2 $ ne_comm.1 $
      complex_embedding.is_real_iff.not.1 $ is_complex_iff.1 w.2),
end

noncomputable instance number_field.infinite_place.fintype : fintype (infinite_place K) :=
set.fintype_range _

/-- The infinite part of the product formula : for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where
`‖·‖_w` is the normalized absolute value for `w`.  -/
lemma prod_eq_abs_norm (x : K) :
  finset.univ.prod (λ w : infinite_place K, ite (w.is_real) (w x) ((w x) ^ 2)) =
    abs (algebra.norm ℚ x) :=
begin
  convert (congr_arg complex.abs (@algebra.norm_eq_prod_embeddings ℚ _ _ _ _ ℂ _ _ _ _ _ x)).symm,
  { rw [map_prod, ← equiv.prod_comp' ring_hom.equiv_rat_alg_hom (λ f, complex.abs (f x))
      (λ φ, complex.abs (φ x)) (λ _, by simpa only [ring_hom.equiv_rat_alg_hom_apply])],
    dsimp only,
    conv { to_rhs, congr, skip, funext,
      rw ( by simp only [if_t_t] : complex.abs (f x) =
        ite (complex_embedding.is_real f) (complex.abs (f x)) (complex.abs (f x))) },
    rw [finset.prod_ite, finset.prod_ite],
    refine congr (congr_arg has_mul.mul _) _,
    { rw [← finset.prod_subtype_eq_prod_filter, ← finset.prod_subtype_eq_prod_filter],
      convert (equiv.prod_comp' (mk_real K) (λ φ, complex.abs (φ x)) (λ w, w x) _).symm,
      any_goals { ext, simp only [finset.mem_subtype, finset.mem_univ], },
      exact λ φ, mk_real.apply K φ x, },
    { rw [finset.filter_congr (λ (w : infinite_place K) _, @not_is_real_iff_is_complex K _ w),
        ← finset.prod_subtype_eq_prod_filter, ← finset.prod_subtype_eq_prod_filter],
      convert finset.prod_fiberwise finset.univ (λ φ, mk_complex K φ) (λ φ, complex.abs (φ x)),
      any_goals
      { ext, simp only [finset.mem_subtype, finset.mem_univ, not_is_real_iff_is_complex], },
      { ext w,
        rw [@finset.prod_congr _ _ _ _ _ (λ φ, w x) _ (eq.refl _)
          (λ φ hφ, (mk_complex.apply K φ x).symm.trans
          (congr_fun (congr_arg coe_fn (finset.mem_filter.1 hφ).2) x)), finset.prod_const,
          mk_complex.filter_card K w],
        refl, }}},
  { rw [eq_rat_cast, ← complex.abs_of_real, complex.of_real_rat_cast], },
end

open fintype

lemma card_real_embeddings :
  card {φ : K →+* ℂ // complex_embedding.is_real φ} = card {w : infinite_place K // is_real w} :=
by convert (fintype.of_equiv_card (mk_real K)).symm

lemma card_complex_embeddings :
  card {φ : K →+* ℂ // ¬ complex_embedding.is_real φ} =
    2 * card {w : infinite_place K // is_complex w} :=
begin
  rw [fintype.card, fintype.card, mul_comm, ← algebra.id.smul_eq_mul, ← finset.sum_const],
  conv { to_rhs, congr, skip, funext, rw ← mk_complex.filter_card K x },
  simp_rw finset.card_eq_sum_ones,
  exact (finset.sum_fiberwise finset.univ (λ φ, mk_complex K φ) (λ φ, 1)).symm
end

end number_field.infinite_place

end infinite_place
