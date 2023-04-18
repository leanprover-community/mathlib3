import analysis.normed_space.star.continuous_functional_calculus.background
import analysis.normed_space.star.continuous_functional_calculus.polynomial
import topology.tietze_extension -- only needed in one place
import topology.metric_space.emetric_paracompact -- only needed in one place

open_locale polynomial
open polynomial

/-!
## Definitions
-/

/-- A `continuous_functional_calculus_class R a` is a star algebra homomorphism from the continuous
`R`-valued functions defined on the spectrum of `a : A` into the algebra `A` which is in addiiton
continuous and extends the polynomial functional calculus. More precisely, this latter statement
is encapsulated in -/
@[ext]
class continuous_functional_calculus_class (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) :=
(to_star_alg_hom : C(spectrum R a, R) →⋆ₐ[R] A)
(hom_continuous : continuous to_star_alg_hom)
(hom_map_X : to_star_alg_hom (to_continuous_map_on_alg_hom (spectrum R a) X) = a)

instance {𝕜 A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A] [algebra 𝕜 A]
  [topological_space A] [t2_space A] [star_module 𝕜 A] {a : A} [compact_space (spectrum 𝕜 a)] :
  subsingleton (continuous_functional_calculus_class 𝕜 a) :=
subsingleton.intro (λ h₁ h₂, h₁.ext h₂ $
  continuous_map.star_alg_hom_ext_map_X h₁.to_star_alg_hom h₂.to_star_alg_hom
  h₁.hom_continuous h₂.hom_continuous $ h₁.hom_map_X.trans h₂.hom_map_X.symm)

/-- This extends `continuous_functional_calculus_class R a` with the property that
`continuous_functional_calculus_class.to_star_alg_hom` is injective. -/
@[ext]
class continuous_functional_calculus_injective_class (R : Type*) {A : Type*} [comm_semiring R]
  [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A]
  [star_ring A] [topological_space A] [algebra R A] (a : A)
  extends continuous_functional_calculus_class R a :=
(hom_injective : function.injective to_star_alg_hom)

/-- This extends `continuous_functional_calculus_class R a` with the property that
`continuous_functional_calculus_class.to_star_alg_hom` is an isometry. -/
@[ext]
class continuous_functional_calculus_isometry_class (R : Type*) {A : Type*} [comm_semiring R]
  [star_ring R] [metric_space R] [topological_semiring R] [has_continuous_star R] [ring A]
  [star_ring A] [metric_space A] [algebra R A] (a : A) [compact_space (spectrum R a)] :=
(to_star_alg_hom : C(spectrum R a, R) →⋆ₐ[R] A)
(hom_isometry : isometry to_star_alg_hom)
(hom_map_X : to_star_alg_hom (to_continuous_map_on_alg_hom (spectrum R a) X) = a)

@[priority 100]
instance continuous_functional_calculus_isometry_class.to_continuous_functional_calculus_injective_class
  (R : Type*) {A : Type*} [comm_semiring R] [star_ring R] [metric_space R] [topological_semiring R]
  [has_continuous_star R] [ring A] [star_ring A] [metric_space A] [algebra R A] (a : A)
  [compact_space (spectrum R a)] [h : continuous_functional_calculus_isometry_class R a] :
  continuous_functional_calculus_injective_class R a :=
{ to_star_alg_hom := h.to_star_alg_hom,
  hom_continuous := h.hom_isometry.continuous,
  hom_map_X := h.hom_map_X,
  hom_injective := h.hom_isometry.injective }

/-- This extends `continuous_functional_calculus_class R a` with the spectral mapping property for
`continuous_functional_calculus_class.to_star_alg_hom`. -/
@[ext]
class continuous_functional_calculus_spectrum_class (R : Type*) {A : Type*} [comm_semiring R]
  [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A]
  [star_ring A] [topological_space A] [algebra R A] (a : A)
  extends continuous_functional_calculus_class R a :=
(hom_map_spectrum : ∀ f, spectrum R (to_star_alg_hom f) = set.range f)

/-- The `star_alg_hom` underlying an instance of the continuous functional calculus. -/
def cfc₁ {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [continuous_functional_calculus_class R a] :
  C(spectrum R a, R) →⋆ₐ[R] A :=
continuous_functional_calculus_class.to_star_alg_hom

section -- needs explicit universes?
universes u v

/-- This is `cfc₁` composed with the natural star algebra homomorphism from `C(R, R)` into
`C(spectrum R a, R)` given by precompostion with the embedding of `spectrum R a` into `R`.

While `cfc₁` is necessary in order to have some of the key properties (e.g., uniqueness of the
continuous funcitonal calculus, injectivity, mapping into the `elemental_star_algebra`, etc.), it
is expected that this version will be more useful in practice. In particular, it will naturally
allow for iterated applications of the continuous functional calculus, and one can use existing
continuous functions with it, as opposed to continually needing to bundle some continuous function
into the type `C(spectrum R a, R)`.

Throughout the API, we duplicate lemmas for both versions. -/
def cfc₂ {R : Type u} {A : Type v} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  C(R, R) →⋆ₐ[R] A :=
cfc₁.comp (continuous_map.comp_star_alg_hom' R R $ (continuous_map.id R).restrict $ spectrum R a)

end

/-!
## Basic properties
-/

lemma cfc₂_eq_of_eq_on {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  {f g : C(R, R)} (h : (spectrum R a).eq_on f g) : cfc₂ a f = cfc₂ a g :=
begin
  simp only [cfc₂, star_alg_hom.coe_comp, function.comp],
  exact congr_arg _ (continuous_map.ext $ λ x, h x.prop),
end

@[continuity]
lemma cfc₁_continuous (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  continuous ⇑(cfc₁ : C(spectrum R a, R) →⋆ₐ[R] A) :=
continuous_functional_calculus_class.hom_continuous

@[simp]
lemma cfc₁_map_X (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  cfc₁ (X.to_continuous_map_on $ spectrum R a) = a :=
continuous_functional_calculus_class.hom_map_X

@[simp]
lemma cfc₂_map_X {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  cfc₂ a (X : R[X]).to_continuous_map = a :=
cfc₁_map_X R a

@[simp]
lemma cfc₁_map_C {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] (r : R) :
  cfc₁ ((C r).to_continuous_map_on $ spectrum R a) = algebra_map R A r :=
(cfc₁.to_alg_hom.comp (to_continuous_map_on_alg_hom $ spectrum R a)).commutes' r

@[simp]
lemma cfc₂_map_C {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] (r : R) :
  cfc₂ a (C r).to_continuous_map = algebra_map R A r :=
cfc₁_map_C a r

/-- The continuous functional calculus extends the polynomial functional calculus. -/
lemma cfc₁_comp_to_continuous_map_on_alg_hom (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  cfc₁.to_alg_hom.comp (to_continuous_map_on_alg_hom $ spectrum R a) = aeval a :=
by simpa only [aeval_X_left, alg_hom.coe_comp, star_alg_hom.coe_to_alg_hom, function.comp_app,
  to_continuous_map_on_alg_hom_apply, cfc₁_map_X]
  using (aeval_alg_hom (cfc₁.to_alg_hom.comp $ to_continuous_map_on_alg_hom (spectrum R a)) X).symm

/-- The continuous functional calculus extends the polynomial functional calculus. -/
lemma cfc₁_map_polynomial {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  (p : R[X]) : cfc₁ (p.to_continuous_map_on $ spectrum R a) = aeval a p :=
fun_like.congr_fun (cfc₁_comp_to_continuous_map_on_alg_hom R a) p

/-- The continuous functional calculus extends the polynomial functional calculus. -/
lemma cfc₂_map_polynomial {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  (p : R[X]) : cfc₂ a p.to_continuous_map = aeval a p :=
cfc₁_map_polynomial a p

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
lemma cfc₁_range_le (𝕜 : Type*) {A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A]
  [topological_space A] [algebra 𝕜 A] [star_module 𝕜 A] [topological_ring A]
  [has_continuous_star A] (a : A) [continuous_functional_calculus_class 𝕜 a]
  [compact_space (spectrum 𝕜 a)] :
  (cfc₁ : C(spectrum 𝕜 a, 𝕜) →⋆ₐ[𝕜] A).range ≤ elemental_star_algebra 𝕜 a :=
begin
  rw [star_alg_hom.range_eq_map_top, ←polynomial_functions.star_closure_topological_closure],
  refine (star_subalgebra.topological_closure_map_le _ _ (cfc₁_continuous 𝕜 a)).trans _,
  refine (star_subalgebra.topological_closure_mono _),
  rw [polynomial_functions.star_closure_eq_adjoin_X, star_alg_hom.map_adjoin],
  refine star_subalgebra.adjoin_le _,
  simp only [set.image_singleton, set.singleton_subset_iff, to_continuous_map_on_alg_hom_apply, cfc₁_map_X],
  exact star_subalgebra.self_mem_adjoin_singleton 𝕜 a,
end

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
lemma cfc₁_mem_elemental_star_algebra {𝕜 A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A]
  [topological_space A] [algebra 𝕜 A] [star_module 𝕜 A] [topological_ring A]
  [has_continuous_star A] {a : A} [continuous_functional_calculus_class 𝕜 a]
  [compact_space (spectrum 𝕜 a)] (f : C(spectrum 𝕜 a, 𝕜)) :
  cfc₁ f ∈ elemental_star_algebra 𝕜 a :=
cfc₁_range_le 𝕜 a ⟨f, rfl⟩

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
lemma cfc₂_mem_elemental_star_algebra {𝕜 A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A]
  [topological_space A] [algebra 𝕜 A] [star_module 𝕜 A] [topological_ring A]
  [has_continuous_star A] (a : A) [continuous_functional_calculus_class 𝕜 a]
  [compact_space (spectrum 𝕜 a)] (f : C(𝕜, 𝕜)) :
  cfc₂ a f ∈ elemental_star_algebra 𝕜 a :=
cfc₁_mem_elemental_star_algebra _

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
lemma cfc₂_range_le (𝕜 : Type*) {A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A]
  [topological_space A] [algebra 𝕜 A] [star_module 𝕜 A] [topological_ring A]
  [has_continuous_star A] (a : A) [continuous_functional_calculus_class 𝕜 a]
  [compact_space (spectrum 𝕜 a)] :
  (cfc₂ a : C(𝕜, 𝕜) →⋆ₐ[𝕜] A).range ≤ elemental_star_algebra 𝕜 a :=
by { rintros _ ⟨f, rfl⟩, exact cfc₂_mem_elemental_star_algebra a f }


/-- Any images under the continuous functional calculus commute. -/
@[simp]
lemma cfc₁_commute {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [continuous_functional_calculus_class R a]
  (f g : C(spectrum R a, R)) : commute (cfc₁ f) (cfc₁ g) :=
(commute.all f g).map cfc₁

/-- Any images under the continuous functional calculus commute. -/
lemma cfc₂_commute {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  (f g : C(R, R)) : commute (cfc₂ a f) (cfc₂ a g) :=
cfc₁_commute _ _

/-- Any image under the continuous functional calculus is normal. -/
instance cfc₁.is_star_normal {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [continuous_functional_calculus_class R a]
  (f : C(spectrum R a, R)) : is_star_normal (cfc₁ f) :=
{ star_comm_self := by simpa only [map_star] using cfc₁_commute (star f) f }

/-- Any image under the continuous functional calculus is normal. -/
instance is_star_normal.cfc₂ {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  (f : C(R, R)) : is_star_normal (cfc₂ a f) :=
{ star_comm_self := by simpa only [map_star] using cfc₂_commute a (star f) f }

/-!
## Properties of special classes
-/

@[simp]
lemma cfc₁_injective (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_injective_class R a] :
  function.injective ⇑(cfc₁ : C(spectrum R a, R) →⋆ₐ[R] A) :=
continuous_functional_calculus_injective_class.hom_injective

lemma cfc₂_eq_iff_eq_on {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_injective_class R a]
  {f g : C(R, R)} : cfc₂ a f = cfc₂ a g ↔ (spectrum R a).eq_on f g :=
begin
  refine ⟨λ h, _, λ h, cfc₂_eq_of_eq_on a h⟩,
  have := λ x hx, fun_like.congr_fun (cfc₁_injective R a h) ⟨x, hx⟩,
  exact this,
end

@[simp]
lemma cfc₁_isometry (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [metric_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [metric_space A] [algebra R A] (a : A) [compact_space (spectrum R a)]
  [continuous_functional_calculus_isometry_class R a] :
  isometry ⇑(cfc₁ : C(spectrum R a, R) →⋆ₐ[R] A) :=
continuous_functional_calculus_isometry_class.hom_isometry

/-- For an isometric continuous functional calculus for `a` over `is_R_or_C 𝕜`, the range is
precisely the `elemental_star_algebra` generated by `a`. -/
lemma cfc₁_range {𝕜 A : Type*} [is_R_or_C 𝕜] [normed_ring A]
  [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A] [normed_star_group A]
  {a : A} [compact_space (spectrum 𝕜 a)] [continuous_functional_calculus_isometry_class 𝕜 a] :
  (cfc₁ : C(spectrum 𝕜 a, 𝕜) →⋆ₐ[𝕜] A).range = elemental_star_algebra 𝕜 a :=
begin
  rw [star_alg_hom.range_eq_map_top, ←polynomial_functions.star_closure_topological_closure,
    ←star_subalgebra.map_topological_closure _ _ (cfc₁_isometry 𝕜 a).closed_embedding,
    polynomial_functions.star_closure_eq_adjoin_X, star_alg_hom.map_adjoin],
  congr,
  rw [set.image_singleton, to_continuous_map_on_alg_hom_apply, cfc₁_map_X]
end

-- this is the only direct result where we need the `topology.tietze_extension`
-- and also `topology.metric_space.emetric_paracompact` for `normal_space` instance.
lemma cfc₂_range {𝕜 A : Type*} [is_R_or_C 𝕜] [normed_ring A]
  [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A] [normed_star_group A]
  {a : A} [compact_space (spectrum 𝕜 a)] [continuous_functional_calculus_isometry_class 𝕜 a] :
  (cfc₂ a : C(𝕜, 𝕜) →⋆ₐ[𝕜] A).range = elemental_star_algebra 𝕜 a :=
begin
  refine le_antisymm (cfc₂_range_le 𝕜 a) _,
  rw [←cfc₁_range],
  rintro - ⟨f, rfl⟩,
  have hspec := (is_compact_iff_compact_space.mpr (‹_› : compact_space (spectrum 𝕜 a))).is_closed,
  obtain ⟨f_re', hf_re⟩ := (continuous_map.comp
    ⟨is_R_or_C.re, is_R_or_C.continuous_re⟩ f).exists_restrict_eq_of_closed hspec,
  obtain ⟨f_im', hf_im⟩ := (continuous_map.comp
    ⟨is_R_or_C.im, is_R_or_C.continuous_im⟩ f).exists_restrict_eq_of_closed hspec,
  refine ⟨(@is_R_or_C.of_real_clm 𝕜 _ : C(ℝ, 𝕜)).comp f_re' +
    @is_R_or_C.I 𝕜 _ • (@is_R_or_C.of_real_clm 𝕜 _ : C(ℝ, 𝕜)).comp f_im', _⟩,
  rw [cfc₂, star_alg_hom.coe_comp, function.comp_apply],
  congr,
  ext x,
  apply is_R_or_C.ext;
  simp only [continuous_map.comp_star_alg_hom'_apply, continuous_map.restrict_apply, continuous_map.add_apply,
    continuous_map.coe_coe, is_R_or_C.of_real_clm_apply, continuous_map.coe_smul, continuous_map.coe_comp, pi.smul_apply,
    algebra.id.smul_eq_mul, map_add, is_R_or_C.of_real_re, is_R_or_C.I_mul_re, is_R_or_C.of_real_im, neg_zero,
    add_zero, zero_add, function.comp_apply, is_R_or_C.mul_im, mul_zero],
  { exact fun_like.congr_fun hf_re x },
  { rw ←is_R_or_C.I_im' (f x),
    congr,
    exact fun_like.congr_fun hf_im x },
end

/-- For an isometric continuous functional calculus for `a` over `is_R_or_C 𝕜`, the range is
precisely the `elemental_star_algebra` generated by `a`. -/
lemma cfc₁_exists_of_mem_elemental_star_algebra {𝕜 A : Type*} [is_R_or_C 𝕜] [normed_ring A]
  [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A] [normed_star_group A]
  {a : A} [compact_space (spectrum 𝕜 a)] [continuous_functional_calculus_isometry_class 𝕜 a]
  {x : A} (hx : x ∈ elemental_star_algebra 𝕜 a) :
  ∃ f : C(spectrum 𝕜 a, 𝕜), cfc₁ f = x :=
by rwa ←cfc₁_range at hx

lemma cfc₂_exists_of_mem_elemental_star_algebra {𝕜 A : Type*} [is_R_or_C 𝕜] [normed_ring A]
  [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A] [normed_star_group A]
  {a : A} [compact_space (spectrum 𝕜 a)] [continuous_functional_calculus_isometry_class 𝕜 a]
  {x : A} (hx : x ∈ elemental_star_algebra 𝕜 a) :
  ∃ f : C(𝕜, 𝕜), cfc₂ a f = x :=
by rwa ←cfc₂_range at hx

lemma cfc₁_map_spectrum (R : Type*) {A : Type*} [comm_semiring R]
  [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A]
  [star_ring A] [topological_space A] [algebra R A] (a : A)
  [continuous_functional_calculus_spectrum_class R a] (f : C(spectrum R a, R)) :
  spectrum R (cfc₁ f) = set.range f :=
continuous_functional_calculus_spectrum_class.hom_map_spectrum f

lemma cfc₂_map_spectrum {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_spectrum_class R a]
  (f : C(R, R)) : (spectrum R a).maps_to f (spectrum R (cfc₂ a f)) :=
begin
  rw [cfc₂, star_alg_hom.coe_comp, function.comp_apply, cfc₁_map_spectrum],
  exact λ x hx, ⟨⟨x, hx⟩, rfl⟩,
end

lemma cfc₂_map_spectrum' {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_spectrum_class R a]
  (f : C(R, R)) : spectrum R (cfc₂ a f) = f '' spectrum R a :=
begin
  rw [cfc₂, star_alg_hom.coe_comp, function.comp_apply, cfc₁_map_spectrum],
  ext,
  split,
  { rintro ⟨x, rfl⟩,
    exact ⟨x, x.prop, rfl⟩ },
  { rintro ⟨x, hx, rfl⟩,
    exact ⟨⟨x, hx⟩, rfl⟩ },
end

-- this is not a terrible version, but presumably we will want something better.
-- the `cfc₂_comp` version is pretty nice.
lemma cfc₁_comp {R A : Type*} [is_R_or_C R] [ring A] [star_ring A] [topological_space A]
  [t2_space A] [algebra R A] [star_module R A] (a : A) [continuous_functional_calculus_class R a]
  (f : C(spectrum R a, R)) [continuous_functional_calculus_class R (cfc₁ f)]
  (g : C(spectrum R (cfc₁ f), R)) (h : ∀ x, f x ∈ spectrum R (cfc₁ f))
  [compact_space (spectrum R (cfc₁ f))] :
  let f' : C(spectrum R a, spectrum R (cfc₁ f)) :=
    ⟨λ x, ⟨f x, h x⟩, by refine (map_continuous f).subtype_mk (λ x, h x)⟩ in
  cfc₁ (g.comp f') = cfc₁ g :=
begin
  let f' : C(spectrum R a, spectrum R (cfc₁ f)) :=
    ⟨λ x, ⟨f x, h x⟩, by refine (map_continuous f).subtype_mk (λ x, h x)⟩,
  let cfc₃ : continuous_functional_calculus_class R (cfc₁ f) :=
  { to_star_alg_hom := cfc₁.comp (f'.comp_star_alg_hom' R R),
    hom_continuous := continuous_functional_calculus_class.hom_continuous.comp f'.continuous_comp_left,
    hom_map_X :=
    begin
    simp only [star_alg_hom.coe_comp, function.comp_apply],
    congr' 1,
    ext,
    simp only [continuous_map.comp_star_alg_hom'_apply, continuous_map.comp_apply, eval_X, continuous_map.coe_mk,
  to_continuous_map_on_apply, subtype.coe_mk, to_continuous_map_apply, to_continuous_map_on_alg_hom_apply],
    end },
  exact fun_like.congr_fun ((continuous_functional_calculus_class.ext_iff _ _).mp
    (subsingleton.elim cfc₃ ‹_›)) g,
end

lemma cfc₂_comp {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_spectrum_class R a]
  (f g : C(R, R)) [continuous_functional_calculus_class R (cfc₂ a f)]
  [subsingleton (continuous_functional_calculus_class R (cfc₂ a f))] :
  cfc₂ a (g.comp f) = cfc₂ (cfc₂ a f) g :=
begin
  let f' : C(spectrum R a, spectrum R (cfc₂ a f)) := ⟨λ r, ⟨f r, cfc₂_map_spectrum a f r.prop⟩,
    ((map_continuous f).comp continuous_induced_dom).subtype_mk (λ x, cfc₂_map_spectrum a f x.prop)⟩,
  let cfc₃ : C(spectrum R (cfc₂ a f), R) →⋆ₐ[R] A := cfc₁.comp (f'.comp_star_alg_hom' R R),
  let this : continuous_functional_calculus_class R (cfc₂ a f) :=
  { to_star_alg_hom := cfc₃,
    hom_continuous := continuous_functional_calculus_class.hom_continuous.comp f'.continuous_comp_left,
    hom_map_X :=
    begin
      simp only [cfc₃, cfc₂, star_alg_hom.coe_comp, function.comp_apply],
      congr' 1,
      ext x,
      simp only [to_continuous_map_on_alg_hom_apply, continuous_map.comp_star_alg_hom'_apply, continuous_map.comp_apply,
  continuous_map.coe_mk, to_continuous_map_on_apply, subtype.coe_mk, to_continuous_map_apply, eval_X,
  continuous_map.comp_star_alg_hom'_apply, continuous_map.restrict_apply, continuous_map.coe_id, id.def],
    end },
  exact fun_like.congr_fun ((continuous_functional_calculus_class.ext_iff _ _).mp
    (subsingleton.elim this ‹_›)) (g.restrict (spectrum R (cfc₂ a f))),
end


/-!
## Restriction of the spectrum

Suppose that `A` is an `S`-algebra and `S` is an `R`-algebra. For `a : A`, what is the relationship
between `spectrum R a` and `spectrum S a`? Of course, these live in different places, and in general
the relationship is `spectrum R a = algebra_map R S ⁻¹' spectrum S a`. One might wonder under what
conditions one has `algebra_map R S '' spectrum R a = spectrum S a`. We provide a predicate here
called `spectrum_restricts` which takes an `a : A` and a function `f : S → R` and says that
`f ∘ algebra_map R S = id` and the restriction of `algebra_map R S ∘ f` to `spectrum S a` is the
identity. Of course, this forces `algebra_map R S` to be a ring embedding, and also this is
sufficient to guarantee `algebra_map R S '' spectrum R a = spectrum S a`.

This predicate is useful for restricting a continuous functional calculus over the ring `S` to one
over the ring `R`.
-/

lemma spectrum.algebra_map_mem_iff (R S : Type*) {A : Type*} [comm_semiring R] [comm_semiring S] [ring A]
  [algebra R S] [algebra R A] [algebra S A] [is_scalar_tower R S A] {a : A} {r : R} :
  algebra_map R S r ∈ spectrum S a ↔ r ∈ spectrum R a :=
by simp only [spectrum.mem_iff, algebra.algebra_map_eq_smul_one, smul_assoc, one_smul]

alias spectrum.algebra_map_mem_iff ↔ spectrum.of_algebra_map_mem spectrum.algebra_map_mem

lemma spectrum.preimage_algebra_map {R S A : Type*} [comm_semiring R] [comm_semiring S] [ring A]
  [algebra R S] [algebra R A] [algebra S A] [is_scalar_tower R S A] {a : A} :
  algebra_map R S ⁻¹' spectrum S a = spectrum R a :=
set.ext $ λ _, spectrum.algebra_map_mem_iff _ _

/-- Given an element `a : A` of an `S`-algebra, where `S` is itself an `R`-algebra, we say that
the spectrum of `a` restricts via a function `f : S → R` if `f` is a left inverse of
`algebra_map R S`, and `f` is a right inverse of `algebra_map R S` on `spectrum S a`.

This is the predicate which allows us to restrict a continuous functional calculus on over `S` to a
continuous functional calculus over `R`. -/
structure spectrum_restricts {R S : Type*} {A : Type*} [comm_semiring R] [comm_semiring S] [ring A]
  [algebra R S] [algebra R A] [algebra S A] (a : A) (f : S → R) : Prop :=
(right_inv_on : (spectrum S a).right_inv_on f (algebra_map R S))
(left_inv : function.left_inverse f (algebra_map R S))

lemma spectrum_restricts.algebra_map_image {R S : Type*} {A : Type*} [comm_semiring R]
  [comm_semiring S] [ring A] [algebra R S] [algebra R A] [algebra S A] [is_scalar_tower R S A]
  {a : A} {f : S → R} (h : spectrum_restricts a f) :
  algebra_map R S '' spectrum R a = spectrum S a :=
begin
  refine set.eq_of_subset_of_subset _ (λ s hs, ⟨f s, _⟩),
  simpa only [spectrum.preimage_algebra_map] using
    (spectrum S a).image_preimage_subset (algebra_map R S),
  exact ⟨spectrum.of_algebra_map_mem R S ((h.right_inv_on hs).symm ▸ hs), h.right_inv_on hs⟩,
end

lemma spectrum_restricts.image {R S : Type*} {A : Type*} [comm_semiring R]
  [comm_semiring S] [ring A] [algebra R S] [algebra R A] [algebra S A] [is_scalar_tower R S A]
  {a : A} {f : S → R} (h : spectrum_restricts a f) :
  f '' spectrum S a = spectrum R a :=
by simp only [←h.algebra_map_image, set.image_image, h.left_inv _, set.image_id']

lemma spectrum_restricts.is_compact {R S : Type*} {A : Type*} [comm_semiring R]
  [topological_space R] [comm_semiring S] [topological_space S] [ring A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] {a : A} {f : S → R} (hf : continuous f)
  (h : spectrum_restricts a f) (ha : is_compact (spectrum S a)) :
  is_compact (spectrum R a) :=
h.image ▸ ha.image hf

-- not an instance because it would never trigger
lemma spectrum_restricts.compact_space {R S : Type*} {A : Type*} [comm_semiring R]
  [topological_space R] [comm_semiring S] [topological_space S] [ring A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] {a : A} {f : S → R} (hf : continuous f)
  (h : spectrum_restricts a f) (h' : compact_space (spectrum S a)) :
  compact_space (spectrum R a) :=
is_compact_iff_compact_space.mp (h.is_compact hf $ is_compact_iff_compact_space.mpr h')

lemma spectrum_restricts.apply_mem {R S : Type*} {A : Type*} [comm_semiring R] [comm_semiring S]
  [ring A] [algebra R S] [algebra R A] [algebra S A] [is_scalar_tower R S A] {a : A} {f : S → R}
  (h : spectrum_restricts a f) {s : S} (hs : s ∈ spectrum S a) : f s ∈ spectrum R a :=
h.image ▸ ⟨s, hs, rfl⟩

lemma spectrum_restricts.subset_preimage {R S : Type*} {A : Type*} [comm_semiring R]
  [comm_semiring S] [ring A] [algebra R S] [algebra R A] [algebra S A] [is_scalar_tower R S A]
  {a : A} {f : S → R} (h : spectrum_restricts a f) :
  spectrum S a ⊆ f ⁻¹' spectrum R a :=
h.image ▸ (spectrum S a).subset_preimage_image f

lemma is_self_adjoint.spectrum_restricts {A : Type*} [normed_ring A] [normed_algebra ℂ A]
  [complete_space A] [star_ring A] [cstar_ring A] [star_module ℂ A] {a : A}
  (ha : is_self_adjoint a) : spectrum_restricts a continuous_map.complex_re :=
{ right_inv_on := λ x hx, (ha.mem_spectrum_eq_re hx).symm,
  left_inv := complex.of_real_re, }

/-- `algebra_map R A` as a `star_alg_hom` when `A` is a star algebra over `R`. -/
@[simps]
def star_alg_hom.of_id (R : Type*) (A : Type*) [comm_semiring R] [star_ring R]
  [semiring A] [algebra R A] [star_semigroup A] [star_module R A] : R →⋆ₐ[R] A :=
{ to_fun := algebra_map R A,
  map_star' := algebra_map_star_comm,
  .. algebra.of_id R A }

/-!
### Restricting the continuous functional calculus to smaller rings

Suppose that `a : A` has a continuous functional calculus over some ring `S` (e.g., `ℂ`). Suppose
also that `R` is a subring of `S` and that the `S`-spectrum of `a` is contained in this subring `R`
(e..g, `R` is `ℝ` and `a` is self-adjoint). Then it is natural to want a continuous functional
calculus for `a` over the smaller ring `R` instead. In this section, we show that this can be done
assuming `spectrum_restricts a f` for a given continuous map `f : C(S, R)`. Each variant of the
continuous functional calculus can also be restricted, where only for
`continuous_functional_calculus_isometry_class` do we also requrie that `algebra_map R S` is an
isometry. In addition we show that if `spectrum_restricts a f`, then `spectrum_restricts (cfc₁ g) f`
for any `g : C(spectrum R a, R)`.

None of the definitions in this section are instances because they wouldn't fire due to the
`spectrum_restricts` hypothesis. However, they are all `reducible` so they are suitable for
transferring to your favorite applicable setting.
-/

section univs
universes u v w

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[simps]
def spectrum_restricts.star_alg_hom {R : Type u} {S : Type v} {A : Type w} [comm_semiring R]
  [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [topological_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [topological_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  (φ : C(spectrum S a, S) →⋆ₐ[S] A) (f : C(S, R)) (h : spectrum_restricts a f) :
  C(spectrum R a, R) →⋆ₐ[R] A :=
((φ.restrict_scalars R).comp (continuous_map.comp_star_alg_hom (spectrum S a)
  (star_alg_hom.of_id R S) (algebra_map_clm R S).continuous)).comp
  (continuous_map.comp_star_alg_hom' R R
    ⟨(subtype.map f h.subset_preimage), (map_continuous f).subtype_map h.subset_preimage⟩)

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[reducible]
def spectrum_restricts.cfc
  {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [topological_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [topological_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  [continuous_functional_calculus_class S a] (f : C(S, R)) (h : spectrum_restricts a f) :
  continuous_functional_calculus_class R a :=
{ to_star_alg_hom := h.star_alg_hom cfc₁ f,
  hom_continuous := ((cfc₁_continuous S a).comp $ continuous_map.continuous_comp _).comp
    (continuous_map.continuous_comp_left _),
  hom_map_X :=
  begin
    simp only [spectrum_restricts.star_alg_hom_apply, polynomial.to_continuous_map_on_alg_hom_apply],
    convert cfc₁_map_X S a,
    ext x,
    simp only [polynomial.eval_X, subtype.map_coe, polynomial.to_continuous_map_on_apply,
      continuous_map.coe_mk, continuous_map.comp_apply, polynomial.to_continuous_map_apply,
      star_alg_hom.of_id_apply],
    exact h.right_inv_on x.prop,
  end }

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. If the spectrum is preserved
over the larger ring, then it is over the smaller ring as well. -/
@[reducible]
def spectrum_restricts.cfc_spectrum
  {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [topological_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [topological_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  [continuous_functional_calculus_spectrum_class S a] (f : C(S, R)) (h : spectrum_restricts a f) :
  continuous_functional_calculus_spectrum_class R a :=
{ hom_map_spectrum := λ g,
  begin
    simp only [spectrum_restricts.star_alg_hom_apply, ←@spectrum.preimage_algebra_map R S,
      cfc₁_map_spectrum],
    ext x,
    split,
    { rintro ⟨y, hy⟩,
      have := congr_arg f hy,
      simp only [continuous_map.coe_mk, continuous_map.comp_apply, star_alg_hom.of_id_apply] at this,
      rw [h.left_inv _, h.left_inv _] at this,
      exact ⟨_, this⟩ },
    { rintro ⟨y, rfl⟩,
      rw [set.mem_preimage],
      refine ⟨⟨algebra_map R S y, spectrum.algebra_map_mem R S y.prop⟩, _⟩,
      simp only [continuous_map.coe_mk, continuous_map.comp_apply, star_alg_hom.of_id_apply],
      congr,
      exact subtype.ext (h.left_inv y), }
  end,
  .. h.cfc f }

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. If the map is injective
over the larger ring, then it is over the smaller ring as well. -/
@[reducible]
def spectrum_restricts.cfc_injective
  {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [topological_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [topological_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  [continuous_functional_calculus_injective_class S a] (f : C(S, R)) (h : spectrum_restricts a f) :
  continuous_functional_calculus_injective_class R a :=
{ hom_injective := λ g₁ g₂ hg,
  begin
    simp only [spectrum_restricts.star_alg_hom_apply] at hg,
    replace hg := cfc₁_injective S a hg,
    ext x,
    have := congr_arg f (fun_like.congr_fun hg ⟨algebra_map R S x, spectrum.algebra_map_mem R S x.prop⟩),
    simp only [continuous_map.coe_mk, continuous_map.comp_apply, star_alg_hom.of_id_apply] at this,
    rw [h.left_inv _, h.left_inv _] at this,
    convert this;
    exact subtype.ext (h.left_inv _).symm,
  end,
  .. h.cfc f }

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. If the map is isometric
over the larger ring, then it is over the smaller ring as well, assuming the `algebra_map` between
these rings is an isometry. -/
@[reducible]
def spectrum_restricts.cfc_isometry
  {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [star_ring R]
  [metric_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [metric_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [metric_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  [compact_space (spectrum S a)] [compact_space (spectrum R a)]
  [continuous_functional_calculus_isometry_class S a] (f : C(S, R)) (h : spectrum_restricts a f)
  (h_isom : isometry (algebra_map R S)) :
  continuous_functional_calculus_isometry_class R a :=
{ hom_isometry :=
  begin
    simp only [isometry_iff_dist_eq],
    simp only [spectrum_restricts.star_alg_hom_apply, (cfc₁_isometry S a).dist_eq],
    intros g₁ g₂,
    refine le_antisymm _ _,
    { rw continuous_map.dist_le dist_nonneg,
      intro x,
      simp only [continuous_map.coe_mk, continuous_map.comp_apply, star_alg_hom.of_id_apply],
      rw [h_isom.dist_eq],
      exact continuous_map.dist_apply_le_dist _ },
    { rw continuous_map.dist_le dist_nonneg,
      intro x,
      obtain ⟨y, y_mem, hy⟩ := (h.image.symm ▸ x.prop : (x : R) ∈ f '' spectrum S a),
      lift y to spectrum S a using y_mem,
      convert continuous_map.dist_apply_le_dist y using 1,
      simp only [continuous_map.coe_mk, continuous_map.comp_apply, star_alg_hom.of_id_apply],
      rw [h_isom.dist_eq],
      congr;
      exact subtype.ext hy.symm, }
  end,
  .. h.cfc f }

.

/-- If the spectrum of `a` restricts from `S` to `R`, then so does `cfc₁ g` for any
`g : C(spectrum R a, R)`. You should use this lemma manually to prove the spectrum restriction
result for continuous functional calculi whenever you use one of the definitions above to create an
instance.

Tou can use this to prove that, for exmaple, the spectrum (in `ℂ`) of the image of a positive
operator is nonnegative. -/
lemma spectrum_restricts.cfc_spectrum_restricts
  {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [topological_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [topological_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  [continuous_functional_calculus_spectrum_class S a] (f : C(S, R)) (h : spectrum_restricts a f)
  (g : C(spectrum R a, R)) :
  spectrum_restricts (@cfc₁ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfc f) g) f :=
{ right_inv_on :=
  begin
    letI := h.cfc_spectrum f,
    intros s hs,
    simp only [cfc₁, spectrum_restricts.star_alg_hom_apply] at hs,
    rw [←cfc₁, cfc₁_map_spectrum] at hs,
    obtain ⟨x, hx⟩ := hs,
    simp only [continuous_map.coe_mk, continuous_map.comp_apply, star_alg_hom.of_id_apply] at hx,
    nth_rewrite 0 ←hx,
    rwa h.left_inv,
  end,
  left_inv := h.left_inv }

end univs
