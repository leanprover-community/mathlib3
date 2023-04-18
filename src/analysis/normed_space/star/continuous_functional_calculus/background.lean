import analysis.normed_space.star.spectrum

open_locale nnreal

section prereqs

instance : complete_space ℝ≥0 := is_closed_Ici.complete_space_coe

instance is_scalar_tower.complex_to_real {M E : Type*} [add_comm_group M] [module ℂ M]
  [add_comm_group E] [module ℂ E] [has_smul M E] [is_scalar_tower ℂ M E] : is_scalar_tower ℝ M E :=
{ smul_assoc := λ x _ _, (smul_assoc (x : ℂ) _ _ : _) }

instance algebra.complex_to_real {A : Type*} [ring A] [algebra ℂ A] : algebra ℝ A :=
restrict_scalars.algebra ℝ ℂ A

@[simp]
lemma is_self_adjoint_star_hom_apply {F R S : Type*} [has_star R] [has_star S]
  [star_hom_class F R S] [has_trivial_star R] (f : F) (x : R) : is_self_adjoint (f x) :=
(is_self_adjoint.all x).star_hom_apply f

instance self_adjoint.is_star_normal {R : Type*} [non_unital_ring R] [star_ring R]
  (x : self_adjoint R) : is_star_normal (x : R) :=
x.prop.is_star_normal

/-- `complex.re` as a bundled continuous map. -/
@[simps]
def continuous_map.complex_re : C(ℂ, ℝ) := continuous_map.mk complex.re complex.continuous_re

/-- `complex.im` as a bundled continuous map. -/
@[simps]
def continuous_map.complex_im : C(ℂ, ℝ) := continuous_map.mk complex.im complex.continuous_im

/-- Range of an `star_alg_hom` as a star subalgebra. -/
protected def star_alg_hom.range {R A B : Type*} [comm_semiring R] [star_ring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [has_star A] [star_ring B] [star_module R B]
  (φ : A →⋆ₐ[R] B) : star_subalgebra R B :=
{ carrier := set.range φ,
  star_mem' := by { rintro _ ⟨b, rfl⟩, exact ⟨star b, map_star φ b⟩ },
  .. φ.to_alg_hom.range }

lemma star_alg_hom.range_eq_map_top {R A B : Type*} [comm_semiring R] [star_ring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [star_ring A] [star_ring B]
  [star_module R A] [star_module R B]
  (φ : A →⋆ₐ[R] B) : φ.range = (⊤ : star_subalgebra R A).map φ :=
star_subalgebra.ext $ λ x,
  ⟨by { rintro ⟨a, ha⟩, exact ⟨a, by simp only [star_subalgebra.top_to_subalgebra], ha⟩ },
   by { rintro ⟨a, -, ha⟩, exact ⟨a, ha⟩ }⟩

lemma star_subalgebra.map_topological_closure_le {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [star_ring A] [star_ring B]
  [star_module R A] [star_module R B] [topological_space A] [topological_semiring A]
  [has_continuous_star A] [topological_space B] [topological_semiring B] [has_continuous_star B]
  (S : star_subalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : is_closed_map φ) :
  (S.map φ).topological_closure ≤ S.topological_closure.map φ :=
is_closed_map.closure_image_subset hφ _

lemma star_subalgebra.topological_closure_map_le {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [star_ring A] [star_ring B]
  [star_module R A] [star_module R B] [topological_space A] [topological_semiring A]
  [has_continuous_star A] [topological_space B] [topological_semiring B] [has_continuous_star B]
  (S : star_subalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : continuous φ) :
  S.topological_closure.map φ ≤ (S.map φ).topological_closure :=
image_closure_subset_closure_image hφ

lemma star_subalgebra.map_topological_closure {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [star_ring A] [star_ring B]
  [star_module R A] [star_module R B] [topological_space A] [topological_semiring A]
  [has_continuous_star A] [topological_space B] [topological_semiring B] [has_continuous_star B]
  (S : star_subalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : closed_embedding φ) :
  (S.map φ).topological_closure = S.topological_closure.map φ :=
le_antisymm (S.map_topological_closure_le φ hφ.is_closed_map)
  (S.topological_closure_map_le φ hφ.continuous)
-- would be nice if `closed_embedding.closure_image_eq` worked out of the box for this.

/-- Restriction of the codomain of a `star_alg_hom` to a star subalgebra containing the range. -/
protected def star_alg_hom.cod_restrict {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [star_ring B] [star_module R B]
  (f : A →⋆ₐ[R] B) (S : star_subalgebra R B) (hf : ∀ x, f x ∈ S) : A →⋆ₐ[R] S :=
{ map_star' := λ x, subtype.ext (map_star f x),
  .. alg_hom.cod_restrict f.to_alg_hom S.to_subalgebra hf }

/-- Restriction of the codomain of a `star_alg_hom` to its range. -/
def star_alg_hom.range_restrict {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [star_ring B] [star_module R B]
  (f : A →⋆ₐ[R] B) : A →⋆ₐ[R] f.range :=
star_alg_hom.cod_restrict f _ (λ x, ⟨x, rfl⟩)

/-- The `star_alg_equiv` onto the range corresponding to an injective `star_alg_hom`. -/
noncomputable def star_alg_equiv.of_injective {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [star_ring B] [star_module R B]
  (f : A →⋆ₐ[R] B) (hf : function.injective f) : A ≃⋆ₐ[R] f.range :=
{ to_fun := f.range_restrict,
  map_star' := λ a, subtype.ext (map_star f a),
  map_smul' := λ r a, subtype.ext (map_smul f r a),
  .. alg_equiv.of_injective (f : A →ₐ[R] B) hf, }

lemma star_alg_equiv.isometry {F A B : Type*} [normed_ring A] [normed_algebra ℂ A]
  [complete_space A] [star_ring A] [cstar_ring A] [normed_ring B] [normed_algebra ℂ B]
  [complete_space B] [star_ring B] [cstar_ring B] [star_alg_equiv_class F ℂ A B] (φ : F) :
  isometry φ :=
begin
  refine add_monoid_hom_class.isometry_of_norm φ
    (λ x, le_antisymm (star_alg_hom.norm_apply_le φ x) _),
  set φ' : A ≃⋆ₐ[ℂ] B :=
  { to_fun := φ,
    inv_fun := equiv_like.inv φ,
    left_inv := equiv_like.left_inv φ,
    right_inv := equiv_like.right_inv φ,
    map_smul' := map_smul φ,
    .. (φ : A →⋆ₐ[ℂ] B) },
  nth_rewrite 0 ←star_alg_equiv.symm_apply_apply φ' x,
  simpa only [star_alg_hom.coe_coe] using star_alg_hom.norm_apply_le (φ'.symm : B →⋆ₐ[ℂ] A) (φ x),
end

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

section spectrum_apply_subset_semiring

namespace alg_hom -- these just need to be generalized in mathlib.
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

instance continuous_map.has_trivial_star {X R : Type*} [topological_space X]
  [topological_space R] [has_star R] [has_continuous_star R] [has_trivial_star R] :
  has_trivial_star C(X, R) :=
{ star_trivial := λ _, continuous_map.ext $ λ _, star_trivial _ }

end prereqs
