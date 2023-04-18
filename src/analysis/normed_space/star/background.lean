import analysis.normed_space.star.continuous_functional_calculus

open_locale nnreal

instance : complete_space ℝ≥0 := is_closed_Ici.complete_space_coe

instance continuous_map.has_trivial_star {X R : Type*} [topological_space X]
  [topological_space R] [has_star R] [has_continuous_star R] [has_trivial_star R] :
  has_trivial_star C(X, R) :=
{ star_trivial := λ _, continuous_map.ext $ λ _, star_trivial _ }

namespace non_unital_star_alg_hom_class

variables {F R A B : Type*} [monoid R]
variables [non_unital_ring A] [distrib_mul_action R A] [partial_order A] [star_ordered_ring A]
variables [non_unital_ring B] [distrib_mul_action R B] [partial_order B] [star_ordered_ring B]

@[priority 100]
instance [non_unital_star_alg_hom_class F R A B] : order_hom_class F A B :=
{ coe := λ f, f,
  coe_injective' := fun_like.coe_injective,
  map_rel := λ f a b h,
  begin
    rw [←sub_nonneg] at h ⊢,
    obtain ⟨x, hx⟩ := (star_ordered_ring.nonneg_iff (b-a)).1 h,
    refine (star_ordered_ring.nonneg_iff _).2 ⟨f x, _⟩,
    rw [←map_sub, hx, map_mul, map_star]
  end }

attribute [nolint dangerous_instance] non_unital_star_alg_hom_class.order_hom_class

end non_unital_star_alg_hom_class

section star_alg_hom_restrict

@[simps]
def star_alg_hom.restrict_scalars (R : Type*) {S A B : Type*} [comm_semiring R] [comm_semiring S]
  [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B]
  [is_scalar_tower R S A] [is_scalar_tower R S B] [has_star A] [has_star B] (f : A →⋆ₐ[S] B) :
  A →⋆ₐ[R] B :=
{ to_fun := f,
  map_star' := map_star f,
  .. f.to_alg_hom.restrict_scalars R }

theorem star_alg_hom.restrict_scalars_injective (R : Type*) {S A B : Type*} [comm_semiring R]
  [comm_semiring S] [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B]
  [algebra R A] [algebra R B] [is_scalar_tower R S A] [is_scalar_tower R S B] [has_star A]
  [has_star B] :
  function.injective (star_alg_hom.restrict_scalars R : (A →⋆ₐ[S] B) → (A →⋆ₐ[R] B)) :=
λ f g h, star_alg_hom.ext $ λ x, show f.restrict_scalars R x = g.restrict_scalars R x,
  from fun_like.congr_fun h x

-- we could probably do this with much more relaxed typeclass assumptions, but let's just not
@[simps]
def star_alg_equiv.restrict_scalars (R : Type*) {S A B : Type*} [comm_semiring R] [comm_semiring S]
  [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B]
  [is_scalar_tower R S A] [is_scalar_tower R S B] [has_star A] [has_star B] (f : A ≃⋆ₐ[S] B) :
  A ≃⋆ₐ[R] B :=
{ to_fun := f,
  map_smul' := map_smul ((f : A →⋆ₐ[S] B).restrict_scalars R),
  .. (f : A →⋆ₐ[S] B).restrict_scalars R,
  .. f }

theorem star_alg_equiv.restrict_scalars_injective (R : Type*) {S A B : Type*} [comm_semiring R]
  [comm_semiring S] [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B]
  [algebra R A] [algebra R B] [is_scalar_tower R S A] [is_scalar_tower R S B] [has_star A]
  [has_star B] :
  function.injective (star_alg_equiv.restrict_scalars R : (A ≃⋆ₐ[S] B) → (A ≃⋆ₐ[R] B)) :=
λ f g h, star_alg_equiv.ext $ λ x, show f.restrict_scalars R x = g.restrict_scalars R x,
  from fun_like.congr_fun h x

end star_alg_hom_restrict


section algebra_complex_to_real

instance is_scalar_tower.complex_to_real {M E : Type*} [add_comm_group M] [module ℂ M]
  [add_comm_group E] [module ℂ E] [has_smul M E] [is_scalar_tower ℂ M E] : is_scalar_tower ℝ M E :=
{ smul_assoc := λ x _ _, (smul_assoc (x : ℂ) _ _ : _) }

instance algebra.complex_to_real {A : Type*} [ring A] [algebra ℂ A] : algebra ℝ A :=
restrict_scalars.algebra ℝ ℂ A

example {A : Type*} [ring A] [algebra ℂ A] : algebra ℝ≥0 A := infer_instance

end algebra_complex_to_real

namespace spectrum

section algebra

variables {A : Type*} [ring A]

lemma mem_real_iff_complex [algebra ℂ A] {a : A} {r : ℝ} :
  r ∈ spectrum ℝ a ↔ (r : ℂ) ∈ spectrum ℂ a :=
by simpa only [spectrum.mem_iff, algebra.algebra_map_eq_smul_one]

lemma mem_nnreal_iff_real [algebra ℝ A] {a : A} {r : ℝ≥0} :
  r ∈ spectrum ℝ≥0 a ↔ (r : ℝ) ∈ spectrum ℝ a :=
by simpa only [spectrum.mem_iff, algebra.algebra_map_eq_smul_one]

lemma mem_nnreal_iff_complex [algebra ℂ A] {a : A} {r : ℝ≥0} :
  r ∈ spectrum ℝ≥0 a ↔ (r : ℂ) ∈ spectrum ℂ a :=
mem_nnreal_iff_real.trans mem_real_iff_complex

lemma real_eq_preimage_coe_complex [algebra ℂ A] (a : A) : spectrum ℝ a = coe ⁻¹' spectrum ℂ a :=
set.ext $ λ x, mem_real_iff_complex

lemma nnreal_eq_preimage_coe_real [algebra ℝ A] (a : A) : spectrum ℝ≥0 a = coe ⁻¹' spectrum ℝ a :=
set.ext $ λ x, mem_nnreal_iff_real

lemma nnreal_eq_preimage_coe_complex [algebra ℂ A] (a : A) :
  spectrum ℝ≥0 a = coe ⁻¹' spectrum ℂ a :=
set.ext $ λ x, mem_nnreal_iff_complex

open_locale complex_order
lemma _root_.complex.Ici_zero_eq_range_coe : set.Ici (0 : ℂ) = set.range (coe : ℝ≥0 → ℂ) :=
begin
  refine set.ext (λ x, ⟨λ hx, _, _⟩),
  { lift x to ℝ using complex.of_real_im x.re ▸ congr_arg complex.im
      (complex.eq_re_of_real_le hx),
    lift x to ℝ≥0 using complex.zero_le_real.1 hx,
    exact ⟨x, rfl⟩ },
  { rintro ⟨x, rfl⟩,
    exact complex.zero_le_real.2 x.prop }
end

end algebra

section analysis

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]

lemma real_is_compact (a : A) : is_compact (spectrum ℝ a) :=
(real_eq_preimage_coe_complex a).symm ▸
  complex.isometry_of_real.closed_embedding.is_compact_preimage (spectrum.is_compact a)

lemma nnreal_is_compact (a : A) : is_compact (spectrum ℝ≥0 a) :=
(nnreal_eq_preimage_coe_real a).symm ▸
  (show isometry (coe : ℝ≥0 → ℝ), from isometry_subtype_coe).closed_embedding.is_compact_preimage
  (real_is_compact a)

instance compact_space (a : A) : compact_space (spectrum ℂ a) :=
is_compact_iff_compact_space.1 (spectrum.is_compact a)
instance real_compact_space (a : A) : compact_space (spectrum ℝ a) :=
is_compact_iff_compact_space.1 (real_is_compact a)
instance nnreal_compact_space (a : A) : compact_space (spectrum ℝ≥0 a) :=
is_compact_iff_compact_space.1 (nnreal_is_compact a)

end analysis

end spectrum

@[simps]
def continuous_map.restrict_star_alg_hom {X : Type*} (R A : Type*) [topological_space X]
  [comm_semiring R] [star_ring R] [topological_space A] [semiring A] [topological_semiring A]
  [algebra R A] [star_ring A] [star_module R A] [has_continuous_star A] (s : set X) :
  C(X, A) →⋆ₐ[R] C(s, A) :=
{ to_fun := continuous_map.restrict s,
  map_one' := rfl,
  map_mul' := λ f g, rfl,
  map_zero' := rfl,
  map_add' := λ f g, rfl,
  commutes' := λ r, rfl,
  map_star' := λ f, rfl }

section spectrum_apply_subset_semiring

namespace alg_hom
variables {F R A B : Type*} [comm_semiring R] [ring A] [algebra R A] [ring B] [algebra R B]
variables [alg_hom_class F R A B]
local notation `σ` := spectrum R
local notation `↑ₐ` := algebra_map R A

lemma mem_resolvent_set_apply' (φ : F) {a : A} {r : R} (h : r ∈ resolvent_set R a) :
  r ∈ resolvent_set R ((φ : A → B) a) :=
by simpa only [map_sub, alg_hom_class.commutes] using h.map φ

lemma spectrum_apply_subset' (φ : F) (a : A) : σ ((φ : A → B) a) ⊆ σ a :=
λ _, mt (mem_resolvent_set_apply' φ)
end alg_hom

end spectrum_apply_subset_semiring

section bifunctor

@[simps]
def continuous_map.comp_star_alg_hom (X : Type*) {R B C : Type*} [topological_space X]
  [comm_semiring R] [semiring B] [algebra R B] [has_star B] [topological_space B]
  [topological_semiring B] [has_continuous_star B] [semiring C] [algebra R C] [has_star C]
  [topological_space C] [topological_semiring C] [has_continuous_star C] (φ : B →⋆ₐ[R] C)
  (hφ : continuous φ) : C(X, B) →⋆ₐ[R] C(X, C) :=
{ to_fun := λ f, (⟨φ, hφ⟩ : C(B, C)).comp f,
  map_one' := continuous_map.ext $ λ _, map_one φ,
  map_mul' := λ f g, continuous_map.ext $ λ x, map_mul φ (f x) (g x),
  map_zero' := continuous_map.ext $ λ _, map_zero φ,
  map_add' := λ f g, continuous_map.ext $ λ x, map_add φ (f x) (g x),
  commutes' := λ r, continuous_map.ext $ λ x, alg_hom_class.commutes φ r,
  map_star' := λ f, continuous_map.ext $ λ x, map_star φ (f x) }

end bifunctor

-- should this be for `is_R_or_C`?
@[simps]
noncomputable def star_alg_hom.real_complex : ℝ →⋆ₐ[ℝ] ℂ :=
{ to_fun := algebra_map_clm ℝ ℂ,
  map_star' := λ r, (is_R_or_C.conj_of_real r).symm,
  commutes' := λ r, rfl,
  ..algebra_map ℝ ℂ }

section cfc

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]
variables (a : A) [is_star_normal a] (S : star_subalgebra ℂ A)

open star_subalgebra

lemma alg_equiv.spectrum_eq {F R A B : Type*} [comm_semiring R] [ring A] [ring B] [algebra R A]
  [algebra R B] [alg_equiv_class F R A B] (f : F) (a : A) :
  spectrum R (f a) = spectrum R a :=
set.subset.antisymm (alg_hom.spectrum_apply_subset' _ _) $
  by simpa only [alg_equiv.coe_alg_hom, alg_equiv.coe_coe_symm_apply_coe_apply]
  using alg_hom.spectrum_apply_subset' (f : A ≃ₐ[R] B).symm (f a)

@[priority 100]
instance star_alg_equiv_class.to_alg_equiv_class {F R A B : Type*} [comm_semiring R] [ring A]
  [ring B] [algebra R A] [algebra R B] [has_star A] [has_star B] [star_alg_equiv_class F R A B] :
  alg_equiv_class F R A B :=
{ coe := λ f, f,
  inv := λ f, equiv_like.inv f,
  .. star_alg_equiv_class.to_ring_equiv_class F R A B,
  .. star_alg_equiv_class.star_alg_hom_class F R A B }

end cfc
