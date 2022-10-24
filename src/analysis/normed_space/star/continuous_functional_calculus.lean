/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import analysis.normed_space.star.gelfand_duality
import topology.algebra.star_subalgebra
import analysis.normed_space.star.induced

.

namespace continuous_map

variables {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
variables (𝕜 : Type*) [comm_semiring 𝕜]
variables (A : Type*) [topological_space A] [semiring A] [topological_semiring A] [star_ring A]
variables [has_continuous_star A] [algebra 𝕜 A]

/-- The functorial map taking `f : C(X, Y)` to `C(Y, A) →⋆ₐ[𝕜] C(X, A)` given by pre-composition
with the continuous function `f`. See `continuous_map.comp_monoid_hom'` and
`continuous_map.comp_add_monoid_hom'`, `continuous_map.comp_right_alg_hom` for bundlings of
pre-composition into a `monoid_hom`, an `add_monoid_hom` and an `alg_hom`, respectively, under
suitable assumptions on `A`. -/
@[simps] def comp_star_alg_hom' (f : C(X, Y)) : C(Y, A) →⋆ₐ[𝕜] C(X, A) :=
{ to_fun := λ g, g.comp f,
  map_one' := one_comp _,
  map_mul' := λ _ _, rfl,
  map_zero' := zero_comp _,
  map_add' := λ _ _, rfl,
  commutes' := λ _, rfl,
  map_star' := λ _, rfl }

/-- `continuous_map.comp_star_alg_hom'` sends the identity continuous map to the identity
`star_alg_hom` -/
lemma comp_star_alg_hom'_id :
  comp_star_alg_hom' 𝕜 A (continuous_map.id X) = star_alg_hom.id 𝕜 C(X, A) :=
star_alg_hom.ext $ λ _, continuous_map.ext $ λ _, rfl

/-- `continuous_map.comp_star_alg_hom` is functorial. -/
lemma comp_star_alg_hom'_comp (g : C(Y, Z)) (f : C(X, Y)) :
  comp_star_alg_hom' 𝕜 A (g.comp f) = (comp_star_alg_hom' 𝕜 A f).comp (comp_star_alg_hom' 𝕜 A g) :=
star_alg_hom.ext $ λ _, continuous_map.ext $ λ _, rfl

end continuous_map

namespace homeomorph

variables {X Y : Type*} [topological_space X] [topological_space Y]
variables (𝕜 : Type*) [comm_semiring 𝕜]
variables (A : Type*) [topological_space A] [semiring A] [topological_semiring A] [star_ring A]
variables [has_continuous_star A] [algebra 𝕜 A]

@[simps] def comp_star_alg_equiv (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) :=
{ to_fun := λ g, g.comp f,
  inv_fun := λ g, g.comp f.symm,
  left_inv := λ g, by simp only [continuous_map.comp_assoc, to_continuous_map_comp_symm,
    continuous_map.comp_id],
  right_inv := λ g, by simp only [continuous_map.comp_assoc, symm_comp_to_continuous_map,
    continuous_map.comp_id],
  map_smul' := λ k a, map_smul (f.to_continuous_map.comp_star_alg_hom' 𝕜 A) k a,
  .. (f.to_continuous_map.comp_star_alg_hom' 𝕜 A) }

end homeomorph

namespace non_unital_star_alg_hom

variables {F R A B : Type*} [monoid R] [has_star A] [has_star B] [non_unital_non_assoc_semiring A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R A] [distrib_mul_action R B]
variables [non_unital_star_alg_hom_class F R A B]

instance  : has_coe_t F (A →⋆ₙₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_smul' := map_smul f,
    map_zero' := map_zero f,
    map_add' := map_add f,
    map_mul' := map_mul f,
    map_star' := map_star f } }

@[simp, protected] lemma coe_coe (f : F) : ⇑(f : A →⋆ₙₐ[R] B) = f := rfl

end non_unital_star_alg_hom

namespace star_alg_hom
variables {F R A B : Type*} [comm_semiring R] [semiring A] [algebra R A] [has_star A] [semiring B]
variables [algebra R B] [has_star B] [star_alg_hom_class F R A B]

instance  : has_coe_t F (A →⋆ₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_one' := map_one f,
    commutes' := alg_hom_class.commutes f,
    ..(f : A →⋆ₙₐ[R] B) } }

@[simp, protected] lemma coe_coe (f : F) : ⇑(f : A →⋆ₐ[R] B) = f := rfl

end star_alg_hom

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

section arbitrary

variables {R : Type*} [comm_semiring R] [star_ring R]
variables {A : Type*} [semiring A] [algebra R A] [star_ring A] [star_module R A]

lemma adjoin_le {S : star_subalgebra R A} {s : set A} (hs : s ⊆ S) : adjoin R s ≤ S :=
star_subalgebra.gc.l_le hs

lemma adjoin_le_iff {S : star_subalgebra R A} {s : set A} : adjoin R s ≤ S ↔ s ⊆ S :=
star_subalgebra.gc _ _

@[simps]
def inclusion (S₁ S₂ : star_subalgebra R A) (h : S₁ ≤ S₂) : S₁ →⋆ₐ[R] S₂ :=
{ to_fun := subtype.map id h,
  map_one' := rfl,
  map_mul' := λ x y, rfl,
  map_zero' := rfl,
  map_add' := λ x y, rfl,
  commutes' := λ z, rfl,
  map_star' := λ x, rfl }

end arbitrary

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

section ring_topological_star_subalg

variables {R : Type*} [comm_ring R] [star_ring R]
variables {A : Type*} [topological_space A] [ring A]
variables [algebra R A] [star_ring A] [star_module R A]
variables [topological_ring A] [has_continuous_star A]
variables {B : Type*} [topological_space B] [ring B]
variables [algebra R B] [star_ring B] [star_module R B]
variables [topological_ring B] [has_continuous_star B]
-- why are elemental albgeras required to be `ring`s?

lemma elemental_algebra_le_of_mem (S : star_subalgebra R A) (hS : is_closed (S : set A)) (a : A)
  (ha : a ∈ S) : elemental_algebra R a ≤ S :=
topological_closure_minimal' _ (adjoin_le $ set.singleton_subset_iff.2 ha) hS

lemma elemental_algebra_closed (x : A) : is_closed (elemental_algebra R x : set A) :=
is_closed_closure

/-- The coercion from an elemental algebra to the full algebra as a `closed_embedding`. -/
def closed_embedding.coe_elemental_algebra (x : A) :
  closed_embedding (coe : elemental_algebra R x → A) :=
{ induced := rfl,
  inj := subtype.coe_injective,
  closed_range :=
  begin
    convert elemental_algebra_closed x,
    exact set.ext (λ y, ⟨by {rintro ⟨y, rfl⟩, exact y.prop}, λ hy, ⟨⟨y, hy⟩, rfl⟩⟩),
  end }

/-- The `star_subalgebra.inclusion` into a star subalgebra as an `embedding`. -/
def embedding_inclusion {S₁ S₂ : star_subalgebra R A} (h : S₁ ≤ S₂) :
  embedding (inclusion S₁ S₂ h) :=
{ induced := eq.symm induced_compose,
  inj := subtype.map_injective h function.injective_id }

/-- The `star_subalgebra.inclusion` into a closed star subalgebra as a `closed_embedding`. -/
def closed_embedding_inclusion {S₁ S₂ : star_subalgebra R A} (h : S₁ ≤ S₂)
  (hS₁ : is_closed (S₁ : set A)) :
  closed_embedding (inclusion S₁ S₂ h) :=
{ closed_range := is_closed_induced_iff.2
    ⟨S₁, hS₁, by { convert (set.range_subtype_map id _).symm, rw set.image_id, refl }⟩,
  .. embedding_inclusion h }

-- this seems hard to make about `star_alg_hom_class`
lemma ext_star_alg_hom_topological_closure [t2_space B] {S : star_subalgebra R A}
  {φ ψ : S.topological_closure →⋆ₐ[R] B} (hφ : continuous φ) (hψ : continuous ψ)
  (h : φ.comp (inclusion _ _ (le_topological_closure S))
    = ψ.comp (inclusion _ _ (le_topological_closure S))) :
  φ = ψ :=
begin
  rw fun_like.ext'_iff,
  have : dense (set.range $ inclusion _ _ (le_topological_closure S)),
  { refine embedding_subtype_coe.to_inducing.dense_iff.2 (λ x, _),
    convert (show ↑x ∈ closure (S : set A), from x.prop),
    rw ←set.range_comp,
    exact set.ext (λ y, ⟨by { rintro ⟨y, rfl⟩, exact y.prop }, λ hy, ⟨⟨y, hy⟩, rfl⟩⟩), },
  refine continuous.ext_on this hφ hψ _,
  rintro _ ⟨x, rfl⟩,
  simpa only using fun_like.congr_fun h x,
end

lemma ext_star_alg_hom_class_topological_closure [t2_space B] {F : Type*} {S : star_subalgebra R A}
  [star_alg_hom_class F R S.topological_closure B] {φ ψ : F} (hφ : continuous φ) (hψ : continuous ψ)
  (h : ∀ x : S, φ ((inclusion _ _ (le_topological_closure S) x))
    = ψ ((inclusion _ _ (le_topological_closure S)) x)) :
  φ = ψ :=
begin
  have : (φ : S.topological_closure →⋆ₐ[R] B) = (ψ : S.topological_closure →⋆ₐ[R] B),
  { refine ext_star_alg_hom_topological_closure hφ hψ (star_alg_hom.ext _);
    simpa only [star_alg_hom.coe_comp, star_alg_hom.coe_coe] using h },
  simpa only [fun_like.ext'_iff, star_alg_hom.coe_coe],
end

end ring_topological_star_subalg

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

open_locale pointwise ennreal nnreal

open weak_dual weak_dual.character_space

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]
variables (a : A) [is_star_normal a] (S : star_subalgebra ℂ A)

noncomputable instance : normed_comm_ring (star_subalgebra.elemental_algebra ℂ a) :=
{ mul_comm := mul_comm, .. (infer_instance : normed_ring _) }

instance (x : A) : complete_space (star_subalgebra.elemental_algebra ℂ x) :=
is_closed_closure.complete_space_coe

-- helpful to short-circuit type class inference
noncomputable instance : normed_algebra ℂ (star_subalgebra.elemental_algebra ℂ a) :=
infer_instance

localized "attribute [instance] complex.partial_order complex.strict_ordered_comm_ring
  complex.star_ordered_ring" in c_star_algebra

-- this is just a stepping stone to the main theorem
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

variables {a}
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
    { replace hz := set.image_subset _ (foo₃ a) hz,
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

/-- For `a : A` which is invertible in `A`, the inverse lies in any unital C⋆-subalgebra `S`
containing `a`. -/
lemma is_unit_coe_inv_mem {S : star_subalgebra ℂ A} (hS : is_closed (S : set A)) {x : A}
  (h : is_unit x) (hxS : x ∈ S) : ↑h.unit⁻¹ ∈ S :=
begin
  have hx := h.star.mul h,
  suffices this : (↑hx.unit⁻¹ : A) ∈ S,
  { rw [←one_mul (↑h.unit⁻¹ : A), ←hx.unit.inv_mul, mul_assoc, is_unit.unit_spec, mul_assoc,
      h.mul_coe_inv, mul_one],
    exact mul_mem this (star_mem hxS) },
  refine elemental_algebra_le_of_mem S hS _ (mul_mem (star_mem hxS) hxS) _,
  haveI := (is_self_adjoint.star_mul_self x).is_star_normal,
  have hx' := is_unit_of_is_unit₂ hx,
  convert (↑hx'.unit⁻¹ : elemental_algebra ℂ (star x * x)).prop using 1,
  exact left_inv_eq_right_inv hx.unit.inv_mul (congr_arg coe hx'.unit.mul_inv),
end

/-- For a unital C⋆-subalgebra `S` of `A` and `x : S`, if `↑x : A` is invertible in `A`, then
`x` is invertible in `S`. -/
lemma coe_is_unit {S : star_subalgebra ℂ A} (hS : is_closed (S : set A)) {x : S} :
  is_unit (x : A) ↔ is_unit x :=
begin
  refine ⟨λ hx, ⟨⟨x, ⟨(↑hx.unit⁻¹ : A), is_unit_coe_inv_mem hS hx x.prop⟩, _, _⟩, rfl⟩,
    λ hx, hx.map S.subtype⟩,
  exacts [subtype.coe_injective hx.mul_coe_inv, subtype.coe_injective hx.coe_inv_mul],
end

/-- **Spectral permanence**. The spectrum of an element is invariant of the C⋆-algebra in which
it is contained. -/
lemma spectrum_eq {S : star_subalgebra ℂ A} (hS : is_closed (S : set A)) (x : S) :
  spectrum ℂ x = spectrum ℂ (x : A) :=
set.ext $ λ _, not_iff_not.2 (coe_is_unit hS).symm

variables (a)

noncomputable def foo : character_space ℂ (elemental_algebra ℂ a) → spectrum ℂ a :=
λ φ,
{ val := φ ⟨a, self_mem_elemental_algebra ℂ a⟩,
  property := by simpa only [spectrum_eq (elemental_algebra_closed a)
    ⟨a, self_mem_elemental_algebra ℂ a⟩]
    using alg_hom.apply_mem_spectrum φ (⟨a, self_mem_elemental_algebra ℂ a⟩) }

noncomputable instance foobar : star_alg_hom_class (character_space ℂ A) ℂ A ℂ :=
{ coe := λ f, (f : A → ℂ),
  map_star := λ f, map_star f,
  .. character_space.alg_hom_class }

lemma foo_injective : function.injective (foo a) :=
begin
  intros φ ψ h,
  simp only [foo, subtype.mk_eq_mk] at h,
  refine ext_star_alg_hom_class_topological_closure (map_continuous φ) (map_continuous ψ) (λ x, _),
  refine adjoin_induction' ℂ x _ _ _ _ _,
  { intros y hy, rw set.mem_singleton_iff at hy, simp_rw hy, exact h },
  { intros z, simp only [alg_hom_class.commutes] },
  { intros x y hx hy,
  calc φ (inclusion _ _ (le_topological_closure (adjoin ℂ {a})) (x + y))
        = φ (inclusion _ _ (le_topological_closure (adjoin ℂ {a})) x
            + inclusion _ _ (le_topological_closure (adjoin ℂ {a})) y)
    : rfl
    ... = ψ (inclusion _ _ (le_topological_closure (adjoin ℂ {a})) x
            + inclusion _ _ (le_topological_closure (adjoin ℂ {a})) y)
        : by rw [map_add φ, hx, hy, ←map_add ψ]
    ... = ψ (inclusion _ _ (le_topological_closure (adjoin ℂ {a})) (x + y))
    : rfl },
  { intros x y hx hy, simp only [map_mul, hx, hy] },
  { intros x hx, simp only [map_star, hx] },
end

.

lemma foo_surjective : function.surjective (foo a) :=
begin
  rintros ⟨z, hz⟩,
  have hz' := hz,
  set a' : elemental_algebra ℂ a := ⟨a, self_mem_elemental_algebra ℂ a⟩,
  have haa' : a = a' := rfl,
  rw [haa', ←spectrum_eq (elemental_algebra_closed a) a', ←spectrum.gelfand_transform_eq a',
    continuous_map.spectrum_eq_range] at hz',
  obtain ⟨φ, rfl⟩ := hz',
  use φ,
  simp only [gelfand_transform_apply_apply],
  ext1,
  refl,
end

lemma foo_continuous : continuous (foo a) :=
begin
  rw continuous_induced_rng,
  have : (coe : spectrum ℂ a → ℂ) ∘ (foo a) = (λ φ, φ ⟨a, self_mem_elemental_algebra ℂ a⟩),
  exact funext (λ φ, rfl),
  rw this,
  exact map_continuous (gelfand_transform ℂ (elemental_algebra ℂ a) ⟨a, self_mem_elemental_algebra ℂ a⟩) ,
end

noncomputable def foo_homeo : character_space ℂ (elemental_algebra ℂ a) ≃ₜ spectrum ℂ a :=
@continuous.homeo_of_equiv_compact_to_t2 _ _ _ _ _ _
  (equiv.of_bijective (foo a) ⟨foo_injective a, foo_surjective a⟩) (foo_continuous a)

noncomputable def continuous_functional_calculus :
  C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental_algebra ℂ a :=
((foo_homeo a).comp_star_alg_equiv ℂ ℂ).trans (gelfand_star_transform (elemental_algebra ℂ a)).symm

lemma continuous_functional_calculus_map_id :
  continuous_functional_calculus a ((continuous_map.id ℂ).restrict (spectrum ℂ a)) =
    ⟨a, self_mem_elemental_algebra ℂ a⟩ :=
star_alg_equiv.symm_apply_apply _ _

end c_star_algebra


end star_subalgebra
