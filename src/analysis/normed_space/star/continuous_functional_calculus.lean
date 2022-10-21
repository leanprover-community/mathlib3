/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import analysis.normed_space.star.gelfand_duality
import topology.algebra.star_subalgebra
import analysis.normed_space.star.induced

.

@[norm_cast] lemma algebra_map.coe_star {R A : Type*} [comm_semiring R] [star_ring R] [semiring A]
  [star_ring A] [algebra R A] [star_module R A] (a : R) : (↑(star a) : A) = star ↑a :=
algebra_map_star_comm a

namespace alg_hom

variables {F 𝕜 A : Type*}
variables [normed_field 𝕜] [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]
local notation `↑ₐ` := algebra_map 𝕜 A

lemma norm_apply_le_self_mul_norm_one [alg_hom_class F 𝕜 A 𝕜] (f : F) (a : A) :
  ∥f a∥ ≤ ∥a∥ * ∥(1 : A)∥ :=
spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum f _)

lemma norm_apply_le_self [norm_one_class A] [alg_hom_class F 𝕜 A 𝕜] (f : F) (a : A) : ∥f a∥ ≤ ∥a∥ :=
spectrum.norm_le_norm_of_mem (apply_mem_spectrum f _)

end alg_hom

namespace is_unit

-- this will likely behave badly if the expected type is not known because `M` can't be inferred.
-- is this too simple to keep as a lemma?
@[to_additive]
lemma submonoid_coe {S M : Type*} [set_like S M] [monoid M] [submonoid_class S M] {s : S}
  {m : s} (hm : is_unit m) : is_unit (m : M) :=
hm.map (submonoid_class.subtype s)

end is_unit

namespace subring

instance to_semi_normed_ring {R : Type*} [semi_normed_ring R] (S : subring R) :
  semi_normed_ring S :=
semi_normed_ring.induced S R S.subtype

instance to_normed_ring {R : Type*} [normed_ring R] (S : subring R) : normed_ring S :=
normed_ring.induced S R S.subtype subtype.coe_injective

instance to_semi_normed_comm_ring {R : Type*} [semi_normed_comm_ring R] (S : subring R) :
  semi_normed_comm_ring S :=
{ mul_comm := mul_comm, .. (infer_instance : semi_normed_ring S) }

instance to_normed_comm_ring {R : Type*} [normed_comm_ring R] (S : subring R) :
  normed_comm_ring S :=
{ mul_comm := mul_comm, .. (infer_instance : normed_ring S) }

end subring

namespace subalgebra

instance to_normed_algebra {𝕜 A : Type*} [semi_normed_ring A] [normed_field 𝕜] [normed_algebra 𝕜 A]
  (S : subalgebra 𝕜 A) : normed_algebra 𝕜 S :=
normed_algebra.induced 𝕜 S A S.val

.

end subalgebra

namespace star_subalgebra

section arbitrary_topological_star_subalg

variables {R : Type*} [comm_semiring R] [star_ring R]
variables {A : Type*} [topological_space A] [semiring A]
variables [algebra R A] [star_ring A] [star_module R A]
variables [topological_semiring A] [has_continuous_star A]

-- this is wrong in `topology/algebra/star_subalgebra`
lemma topological_closure_minimal' (s : star_subalgebra R A)
  {t : star_subalgebra R A} (h : s ≤ t) (ht : is_closed (t : set A)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

-- obviously this holds for arbitrary `star_subalgebra`s
lemma topological_closure_mono :
  monotone (topological_closure : star_subalgebra R A → star_subalgebra R A) :=
λ S₁ S₂ h, topological_closure_minimal' S₁ (h.trans $ le_topological_closure S₂)
  (is_closed_topological_closure S₂)

end arbitrary_topological_star_subalg

instance to_semiring {R A} [comm_semiring R] [star_ring R] [semiring A] [star_ring A]
  [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  semiring S := S.to_subalgebra.to_semiring
instance to_comm_semiring {R A} [comm_semiring R] [star_ring R] [comm_semiring A] [star_ring A]
  [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  comm_semiring S := S.to_subalgebra.to_comm_semiring
instance to_ring {R A} [comm_ring R] [star_ring R] [ring A] [star_ring A]
  [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  ring S := S.to_subalgebra.to_ring
instance to_comm_ring {R A} [comm_ring R] [star_ring R] [comm_ring A] [star_ring A]
  [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  comm_ring S := S.to_subalgebra.to_comm_ring

instance to_semi_normed_ring {R A} [comm_ring R] [star_ring R] [semi_normed_ring A]
  [star_ring A] [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  semi_normed_ring S := semi_normed_ring.induced S A S.subtype
instance to_normed_ring {R A} [comm_ring R] [star_ring R] [normed_ring A]
  [star_ring A] [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  normed_ring S := normed_ring.induced S A S.subtype subtype.coe_injective
instance to_semi_normed_comm_ring {R A} [comm_ring R] [star_ring R] [semi_normed_comm_ring A]
  [star_ring A] [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  semi_normed_comm_ring S := { mul_comm := mul_comm, .. (infer_instance : semi_normed_ring S) }
instance to_normed_comm_ring {R A} [comm_ring R] [star_ring R] [normed_comm_ring A]
  [star_ring A] [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  normed_comm_ring S := { mul_comm := mul_comm, .. (infer_instance : normed_ring S) }

-- this we can make into a `cstar_ring.induced` result
instance to_cstar_ring {R A} [comm_ring R] [star_ring R] [normed_ring A]
  [star_ring A] [cstar_ring A] [algebra R A] [star_module R A] (S : star_subalgebra R A) :
  cstar_ring S :=
{ norm_star_mul_self :=
  begin
    intros x,
    unfold norm,
    rw [map_mul, map_star, cstar_ring.norm_star_mul_self],
  end }


instance to_normed_algebra {𝕜 A} [normed_field 𝕜] [star_ring 𝕜] [semi_normed_ring A]
  [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A] (S : star_subalgebra 𝕜 A) :
  normed_algebra 𝕜 S :=
normed_algebra.induced 𝕜 S A S.subtype

end star_subalgebra

namespace spectrum

section ring

open_locale pointwise
open set

variables {R : Type*} {A : Type*}
variables [comm_ring R] [ring A] [algebra R A]

local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

variables (R)

lemma zero_mem_iff {a : A} : (0 : R) ∈ σ a ↔ ¬is_unit a :=
by rw [mem_iff, map_zero, zero_sub, is_unit.neg_iff]

lemma zero_not_mem_iff {a : A} : (0 : R) ∉ σ a ↔ is_unit a :=
by rw [zero_mem_iff, not_not]

variables {R}

lemma add_mem_iff' {a : A} {r s : R} :
  r + s ∈ spectrum R a ↔ r ∈ spectrum R (- algebra_map R A s + a) :=
by simp only [mem_iff, sub_neg_eq_add, ←sub_sub, map_add]

lemma singleton_add_eq (a : A) (r : R) : {r} + (σ a) = σ (↑ₐr + a) :=
ext $ λ x,
  by rw [singleton_add, image_add_left, mem_preimage, add_comm, add_mem_iff', map_neg, neg_neg]

lemma neg_eq (a : A) : -(σ a) = σ (-a) :=
begin
  ext,
  rw [mem_neg, mem_iff, map_neg, ←is_unit.neg_iff, sub_eq_add_neg, neg_add, neg_neg, ←sub_eq_add_neg],
  exact iff.rfl,
end

lemma singleton_sub_eq (a : A) (r : R) :
  {r} - (σ a) = σ (↑ₐr - a) :=
by rw [sub_eq_add_neg, neg_eq, singleton_add_eq, sub_eq_add_neg]

-- it would be nice to state this for `subalgebra_class`, but we don't have such a thing yet
lemma subset_subalgebra {S : subalgebra R A} (a : S) : spectrum R (a : A) ⊆ spectrum R a :=
compl_subset_compl.2 (λ _, is_unit.map S.val)

-- this is why it would be nice if it was registered for `subalgebra_class`.
lemma subset_star_subalgebra [star_ring R] [star_ring A] [star_module R A] {S : star_subalgebra R A}
  (a : S) : spectrum R (a : A) ⊆ spectrum R a :=
compl_subset_compl.2 (λ _, is_unit.map S.subtype)

end ring

section field

open_locale pointwise polynomial
open set polynomial spectrum

variables {𝕜 : Type*} {A : Type*}
variables [field 𝕜] [ring A] [algebra 𝕜 A]

local notation `σ` := spectrum 𝕜

lemma pow_image_subset (a : A) (n : ℕ) : (λ x, x ^ n) '' (σ a) ⊆ σ (a ^ n) :=
by simpa only [eval_pow, eval_X, aeval_X_pow] using subset_polynomial_aeval a (X ^ n : 𝕜[X])

-- the `nontrivial A` can be moved into the proof instead of as a hypothesis
/-- In this version of the spectral mapping theorem, we assume the spectrum
is nonempty instead of assuming the degree of the polynomial is positive. -/
lemma map_polynomial_aeval_of_nonempty' [is_alg_closed 𝕜] (a : A) (p : 𝕜[X])
  (hnon : (σ a).nonempty) : σ (aeval a p) = (λ k, eval k p) '' (σ a) :=
begin
  nontriviality A,
  refine or.elim (le_or_gt (degree p) 0) (λ h, _) (map_polynomial_aeval_of_degree_pos a p),
  { rw eq_C_of_degree_le_zero h,
    simp only [set.image_congr, eval_C, aeval_C, scalar_eq, set.nonempty.image_const hnon] },
end

lemma map_pow_of_pos [is_alg_closed 𝕜] (a : A) {n : ℕ} (hn : 0 < n) :
  σ (a ^ n) = (λ x, x ^ n) '' (σ a) :=
by simpa only [aeval_X_pow, eval_pow, eval_X] using
  map_polynomial_aeval_of_degree_pos a (X ^ n : 𝕜[X]) (by { rw_mod_cast degree_X_pow, exact hn })

lemma map_pow_of_nonempty [is_alg_closed 𝕜] {a : A} (ha : (σ a).nonempty) (n : ℕ) :
  σ (a ^ n) = (λ x, x ^ n) '' (σ a) :=
by simpa only [aeval_X_pow, eval_pow, eval_X] using map_polynomial_aeval_of_nonempty' a (X ^ n) ha

end field

section banach_algebra

open_locale ennreal nnreal

section normed_field

variables {𝕜 A : Type*}
variables [normed_field 𝕜] [proper_space 𝕜]
variables [normed_ring A] [normed_algebra 𝕜 A] [complete_space A]

lemma exists_nnnorm_eq_spectral_radius_of_nonempty {a : A} (ha : (spectrum 𝕜 a).nonempty) :
  ∃ k ∈ spectrum 𝕜 a, (∥k∥₊ : ℝ≥0∞) = spectral_radius 𝕜 a :=
begin
  obtain ⟨k, hk, h⟩ := (spectrum.is_compact a).exists_forall_ge ha continuous_nnnorm.continuous_on,
  exact ⟨k, hk, le_antisymm (le_supr₂ k hk) (supr₂_le $ by exact_mod_cast h)⟩,
end

lemma spectral_radius_lt_of_forall_lt_of_nonempty {a : A} (ha : (spectrum 𝕜 a).nonempty) {r : ℝ≥0}
  (hr : ∀ k ∈ spectrum 𝕜 a, ∥k∥₊ < r) : spectral_radius 𝕜 a < r :=
Sup_image.symm.trans_lt $ ((spectrum.is_compact a).Sup_lt_iff_of_continuous ha
  (ennreal.continuous_coe.comp continuous_nnnorm).continuous_on (r : ℝ≥0∞)).mpr
  (by exact_mod_cast hr)

end normed_field

section complex

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
local notation `σ` := spectrum ℂ

lemma exists_nnnorm_eq_spectral_radius [nontrivial A] (a : A) :
  ∃ z ∈ spectrum ℂ a, (∥z∥₊ : ℝ≥0∞) = spectral_radius ℂ a :=
exists_nnnorm_eq_spectral_radius_of_nonempty (spectrum.nonempty a)

lemma spectral_radius_lt_of_forall_lt [nontrivial A] (a : A) {r : ℝ≥0}
  (hr : ∀ z ∈ spectrum ℂ a, ∥z∥₊ < r) : spectral_radius ℂ a < r :=
spectral_radius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr

open_locale polynomial
open polynomial

/-- The **spectral mapping theorem** for polynomials in a Banach algebra over `ℂ`. -/
lemma map_polynomial_aeval (a : A) (p : ℂ[X]) : σ (aeval a p) = (λ k, eval k p) '' (σ a) :=
by { nontriviality A, exact map_polynomial_aeval_of_nonempty' a p (spectrum.nonempty a) }

/-- A specialization of the spectral mapping theorem for polynomials in a Banach algebra over `ℂ`
to monic monomials. -/
protected lemma map_pow (a : A) (n : ℕ) : σ (a ^ n) = (λ x, x ^ n) '' (σ a) :=
by simpa only [aeval_X_pow, eval_pow, eval_X] using map_polynomial_aeval a (X ^ n)

end complex

end banach_algebra

end spectrum

namespace star_subalgebra

section c_star_algebra

section generic

variables (A : Type*) [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]
variables (a : A) [is_star_normal a]

noncomputable instance : normed_comm_ring (star_subalgebra.elemental_algebra ℂ a) :=
{ mul_comm := mul_comm, .. (infer_instance : normed_ring _) }

instance : complete_space (star_subalgebra.elemental_algebra ℂ a) :=
is_closed_closure.complete_space_coe

-- helpful to short-circuit type class inference
noncomputable instance : normed_algebra ℂ (star_subalgebra.elemental_algebra ℂ a) :=
infer_instance

end generic

section commutative

open weak_dual weak_dual.character_space

/-
we need to show that if `a : A` and `ha : is_unit a` then
`is_unit ⟨a, self_mem_elemental_algebra a⟩`

we also need to show that `elemental_algebra` is unchanged under linear perturbations.
-/
variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]
variables {a : A} [is_star_normal a] (S : star_subalgebra ℂ A)

localized "attribute [instance] complex.partial_order complex.strict_ordered_comm_ring
  complex.star_ordered_ring" in c_star_algebra

-- this will be superseded by a later result, or will it? Maybe not.
lemma foo₁ : is_unit (star a * a) ↔ is_unit (star a) ∧ is_unit a :=
commute.is_unit_mul_iff (star_comm_self' a)

lemma foo₃ : spectrum ℂ (star a * a) ⊆ set.Icc (0 : ℂ) (∥star a * a∥) :=
begin
  nontriviality A,
  set a' : elemental_algebra ℂ a := ⟨a, self_mem_elemental_algebra ℂ a⟩,
  refine (spectrum.subset_star_subalgebra (star a' * a')).trans _,
  rw [←spectrum.gelfand_transform_eq, continuous_map.spectrum_eq_range],
  rintro - ⟨φ, rfl⟩,
  rw [gelfand_transform_apply_apply, map_mul, map_star, ←star_ring_end_apply, mul_comm,
    is_R_or_C.mul_conj, is_R_or_C.norm_sq_eq_def', sq, ←cstar_ring.norm_star_mul_self, ←map_star,
    ←map_mul],
  exact ⟨complex.zero_le_real.2 (norm_nonneg _),
    complex.real_le_real.2 (alg_hom.norm_apply_le_self φ (star a' * a'))⟩,
end

.
open_locale pointwise ennreal nnreal

example (a b c : ℂ) : {a} - set.Icc b c = set.Icc (a - c) (a - b) :=
set.singleton_sub.trans (set.image_const_sub_Icc a b c)

.
namespace complex

lemma eq_coe_re_of_real_le {r : ℝ} {z : ℂ} (hz : (r : ℂ) ≤ z) : z = z.re :=
by { ext, refl, simp only [←(complex.le_def.1 hz).2, complex.zero_im, complex.of_real_im] }

lemma eq_coe_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ↑∥z∥ :=
by rw [eq_coe_re_of_real_le hz, is_R_or_C.norm_of_real, real.norm_of_nonneg (complex.le_def.2 hz).1]

end complex

lemma is_unit_of_is_unit (h : is_unit (star a * a)) :
  is_unit ((⟨star a, star_self_mem_elemental_algebra ℂ a⟩ : elemental_algebra ℂ a) * ⟨a, self_mem_elemental_algebra ℂ a⟩ ) :=
begin
  nontriviality A,
  set a' : elemental_algebra ℂ a := ⟨a, self_mem_elemental_algebra ℂ a⟩,
  have h₁ : (∥star a * a∥₊ : ℂ) ≠ 0,
  { simpa only [coe_nnnorm, coe_coe, complex.of_real_eq_zero, ne.def]
    using norm_ne_zero_iff.2 h.ne_zero },
  set u : units (elemental_algebra ℂ a) := units.map (algebra_map ℂ (elemental_algebra ℂ a)).to_monoid_hom (units.mk0 _ h₁),
  refine ⟨u.unit_of_nearby _ _, rfl⟩,
  simp only [complex.abs_of_real, map_inv₀, units.coe_map, units.coe_inv, ring_hom.coe_monoid_hom,
    ring_hom.to_monoid_hom_eq_coe, units.coe_mk0, units.coe_map_inv, norm_algebra_map', coe_nnnorm,
    inv_inv, complex.norm_eq_abs, abs_norm_eq_norm, subtype.val_eq_coe, coe_coe],
  have h₂ : ∀ z ∈ spectrum ℂ ((↑(∥star a * a∥ : ℂ) : A) - star a * a), ∥z∥₊ < ∥star a * a∥₊,
  { intros z hz,
    change (coe : ℂ → A) with algebra_map ℂ A at hz,
    rw [←spectrum.singleton_sub_eq, set.singleton_sub] at hz,
    have h₃ : z ∈ set.Icc (0 : ℂ) (∥star a * a∥),
    { replace hz := set.image_subset _ foo₃ hz,
      rwa [set.image_const_sub_Icc, sub_self, sub_zero] at hz },
    refine lt_of_le_of_ne (complex.real_le_real.1 $ complex.eq_coe_norm_of_nonneg h₃.1 ▸ h₃.2) _,
    { intros hz',
      replace hz' := congr_arg (λ (x : ℝ≥0), ((x : ℝ) : ℂ)) hz',
      simp only [coe_nnnorm] at hz',
      rw ←complex.eq_coe_norm_of_nonneg h₃.1 at hz',
      obtain ⟨w, hw₁, hw₂⟩ := hz,
      refine (spectrum.zero_not_mem_iff ℂ).mpr h _,
      rw [hz', sub_eq_self] at hw₂,
      rwa hw₂ at hw₁ } },
  { exact ennreal.coe_lt_coe.1
    (calc (∥star a' * a' - (↑(∥star a * a∥ : ℂ) : elemental_algebra ℂ a)∥₊ : ℝ≥0∞)
        = ∥(↑(∥star a * a∥ : ℂ) : A) - star a * a∥₊ : by { rw [←nnnorm_neg, neg_sub], refl }
    ... = spectral_radius ℂ ((↑(∥star a * a∥ : ℂ) : A) - star a * a)
        : begin
            refine (is_self_adjoint.spectral_radius_eq_nnnorm _).symm,
            rw [is_self_adjoint, star_sub, star_mul, star_star, ←algebra_map.coe_star,
              is_R_or_C.star_def, is_R_or_C.conj_of_real],
          end
    ... < ∥star a * a∥₊ : spectrum.spectral_radius_lt_of_forall_lt _ h₂ ) },
end

.

lemma is_unit_of_is_unit₂ (h : is_unit a) :
  is_unit (⟨a, self_mem_elemental_algebra ℂ a⟩ : elemental_algebra ℂ a) :=
(is_unit.mul_iff.1 $ is_unit_of_is_unit $
  (show commute (star a) a, from star_comm_self' a).is_unit_mul_iff.2 ⟨h.star, h⟩).2

.

lemma is_unit_unit_inv_mem (h : is_unit a) : (↑h.unit⁻¹ : A) ∈ elemental_algebra ℂ a :=
begin
  have h' := is_unit_of_is_unit₂ h,
  convert (↑h'.unit⁻¹ : elemental_algebra ℂ a).prop using 1,
  exact left_inv_eq_right_inv h.unit.inv_mul (congr_arg coe h'.unit.mul_inv),
end

#exit
lemma is_unit_of_is_unit₃ (x : A) (h : is_unit x) :
  is_unit (⟨x, self_mem_elemental_algebra ℂ x⟩ : elemental_algebra ℂ x) :=
begin
  set x' : elemental_algebra ℂ x := ⟨x, self_mem_elemental_algebra ℂ x⟩,
  have hx := h.star.mul h,
  haveI := (is_self_adjoint.star_mul_self x).is_star_normal,
  have hx' := is_unit_of_is_unit₂ hx,
end

/- this is superseded by `foo₃`.
lemma foo₂ : spectrum ℂ (star a * a) ⊆ coe '' (set.Icc (0 : ℝ) ∥star a * a∥) :=
begin
  nontriviality A,
  set a' : elemental_algebra ℂ a := ⟨a, self_mem_elemental_algebra ℂ a⟩,
  refine (spectrum.subset_star_subalgebra (star a' * a')).trans _,
  rw [←spectrum.gelfand_transform_eq, continuous_map.spectrum_eq_range],
  rintro - ⟨φ, rfl⟩,
  rw [gelfand_transform_apply_apply ℂ (elemental_algebra ℂ a), map_mul, map_star],
  refine ⟨is_R_or_C.norm_sq (φ a'), ⟨is_R_or_C.norm_sq_nonneg _, _⟩, _⟩,
  rw [is_R_or_C.norm_sq_eq_def', sq, ←cstar_ring.norm_star_mul_self, ←map_star, ←map_mul],
  exact alg_hom.norm_apply_le_self φ (star a' * a'),
  rw [←is_R_or_C.mul_conj, mul_comm, star_ring_end_apply],
end
-/

lemma is_unit_of_is_unit (h : is_unit a) :
  is_unit (⟨a, self_mem_elemental_algebra ℂ a⟩ : elemental_algebra ℂ a) :=
begin
/-
  nontriviality A,
  set a' : elemental_algebra ℂ a := ⟨a, self_mem_elemental_algebra ℂ a⟩,
  have ha := foo₁.mpr ⟨h.star, h⟩,
  replace ha : (0 : ℂ) ∉ spectrum ℂ (star a * a),
    from spectrum.not_mem_iff.mpr (by simpa only [map_zero, zero_sub, is_unit.neg_iff] using ha),
  by_contra ha',
  erw [←is_unit.neg_iff, ←zero_sub, ← map_zero (algebra_map ℂ (elemental_algebra ℂ a)),
    ←spectrum.mem_iff, ←spectrum.gelfand_transform_eq, continuous_map.spectrum_eq_range] at ha',
  obtain ⟨φ, hφ⟩ := ha',
  rw [gelfand_transform_apply_apply] at hφ,
  change ↥(character_space ℂ ↥(elemental_algebra ℂ a)) at φ,
  have hφ'' := alg_hom.apply_mem_spectrum φ (algebra_map ℂ (elemental_algebra ℂ a) (∥star a' * a'∥ : ℂ) - star a' * a'),
  rw [←spectrum.singleton_sub_eq, set.singleton_sub] at hφ'',
  rcases hφ'' with ⟨z, hz₁, hz₂⟩,
  rw [map_sub, map_mul, hφ, alg_hom_class.commutes, mul_zero] at hz₂,
  --have := spectrum.norm_le_norm_of_mem hφ'',
  --simp at hφ'', -/
  sorry
end
end commutative

#exit

lemma elemental_algebra_le_of_mem (b : adjoin ℂ ({a} : set A)) :
  elemental_algebra ℂ (b : A) ≤ elemental_algebra ℂ a :=
begin
  refine topological_closure_minimal' _ _ _,
  sorry,
  sorry,
end


#exit

noncomputable def foo : character_space ℂ (elemental_algebra ℂ a) → spectrum ℂ a :=
λ φ,
{ val := φ ⟨a, self_mem_elemental_algebra ℂ a⟩,
  property :=
  begin
    have := alg_hom.apply_mem_spectrum φ
      (⟨a, self_mem_elemental_algebra ℂ a⟩),
  end }

end c_star_algebra


end star_subalgebra
