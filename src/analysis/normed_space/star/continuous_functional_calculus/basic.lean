import analysis.normed_space.star.continuous_functional_calculus.background
import analysis.normed_space.star.continuous_functional_calculus.polynomial
import topology.tietze_extension -- only needed in one place
import topology.metric_space.emetric_paracompact -- only needed in one place

open_locale polynomial
open polynomial

/-!
## Definitions
-/

/-- This class exists because under modest hypotheses, we can get a `subsingleton` instance for
this class. -/
@[ext]
class cfc_core_class (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) :=
(to_star_alg_hom : C(spectrum R a, R) →⋆ₐ[R] A)
(hom_continuous : continuous to_star_alg_hom)
(hom_map_X : to_star_alg_hom (to_continuous_map_on_alg_hom (spectrum R a) X) = a)

-- Question: do we want to make this a `uniform_embedding`?

/-- A `cfc_class R a` is a star algebra homomorphism from the continuous
`R`-valued functions defined on the spectrum of `a : A` into the algebra `A` which is in addiiton
continuous and extends the polynomial functional calculus. More precisely, this latter statement
is encapsulated in -/
@[ext]
class cfc_class (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) :=
(to_star_alg_hom : C(spectrum R a, R) →⋆ₐ[R] A)
(hom_closed_embedding : closed_embedding to_star_alg_hom)
(hom_map_X : to_star_alg_hom (to_continuous_map_on_alg_hom (spectrum R a) X) = a)
(hom_map_spectrum : ∀ f, spectrum R (to_star_alg_hom f) = set.range f)

@[priority 100] -- see note [lower instance priority]
instance cfc_class.to_cfc_core_class (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_class R a] :
  cfc_core_class R a :=
{ hom_continuous := (‹_› : cfc_class R a).hom_closed_embedding.continuous,
  .. (‹_› : cfc_class R a) }

instance {𝕜 A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A] [algebra 𝕜 A]
  [topological_space A] [t2_space A] [star_module 𝕜 A] {a : A} [compact_space (spectrum 𝕜 a)] :
  subsingleton (cfc_core_class 𝕜 a) :=
subsingleton.intro (λ h₁ h₂, h₁.ext h₂ $
  continuous_map.star_alg_hom_ext_map_X h₁.to_star_alg_hom h₂.to_star_alg_hom
  h₁.hom_continuous h₂.hom_continuous $ h₁.hom_map_X.trans h₂.hom_map_X.symm)

/-- The `star_alg_hom` underlying an instance of the continuous functional calculus. -/
def cfc₁ {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [cfc_core_class R a] :
  C(spectrum R a, R) →⋆ₐ[R] A :=
cfc_core_class.to_star_alg_hom

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
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] :
  C(R, R) →⋆ₐ[R] A :=
cfc₁.comp (continuous_map.comp_star_alg_hom' R R $ (continuous_map.id R).restrict $ spectrum R a)

end

/-!
## Basic properties
-/

lemma cfc₂_eq_of_eq_on {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_class R a]
  {f g : C(R, R)} (h : (spectrum R a).eq_on f g) : cfc₂ a f = cfc₂ a g :=
begin
  simp only [cfc₂, star_alg_hom.coe_comp, function.comp],
  exact congr_arg _ (continuous_map.ext $ λ x, h x.prop),
end

@[continuity]
lemma cfc₁_closed_embedding (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_class R a] :
  closed_embedding ⇑(cfc₁ : C(spectrum R a, R) →⋆ₐ[R] A) :=
cfc_class.hom_closed_embedding

@[continuity]
lemma cfc₁_continuous (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] :
  continuous ⇑(cfc₁ : C(spectrum R a, R) →⋆ₐ[R] A) :=
cfc_core_class.hom_continuous

-- `cfc₂_closed_embedding`? Is it true in general? Maybe not without Tietze?

@[continuity]
lemma cfc₂_continuous (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] :
  continuous ⇑(cfc₂ a : C(R, R) →⋆ₐ[R] A) :=
(cfc₁_continuous R a).comp $ continuous_map.continuous_comp_left _

lemma X_to_continuous_map (R : Type*) [semiring R] [topological_space R] [topological_semiring R] :
  (X : R[X]).to_continuous_map = continuous_map.id R :=
by ext; simp only [to_continuous_map_apply, eval_X, continuous_map.id_apply]

@[simp]
lemma cfc₁_map_X (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] :
  cfc₁ (X.to_continuous_map_on $ spectrum R a) = a :=
cfc_core_class.hom_map_X

@[simp]
lemma cfc₁_map_id (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] :
  cfc₁ ((continuous_map.id R).restrict $ spectrum R a) = a :=
by { convert cfc₁_map_X R a, rw X_to_continuous_map R }

@[simp]
lemma cfc₂_map_X {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] :
  cfc₂ a (X : R[X]).to_continuous_map = a :=
cfc₁_map_X R a

@[simp]
lemma cfc₂_map_id (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] :
  cfc₂ a (continuous_map.id R) = a :=
cfc₁_map_id R a

@[simp]
lemma cfc₁_map_C {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] (r : R) :
  cfc₁ ((C r).to_continuous_map_on $ spectrum R a) = algebra_map R A r :=
(cfc₁.to_alg_hom.comp (to_continuous_map_on_alg_hom $ spectrum R a)).commutes' r

@[simp]
lemma cfc₂_map_C {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] (r : R) :
  cfc₂ a (C r).to_continuous_map = algebra_map R A r :=
cfc₁_map_C a r

/-- The continuous functional calculus extends the polynomial functional calculus. -/
lemma cfc₁_comp_to_continuous_map_on_alg_hom (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a] :
  cfc₁.to_alg_hom.comp (to_continuous_map_on_alg_hom $ spectrum R a) = aeval a :=
by simpa only [aeval_X_left, alg_hom.coe_comp, star_alg_hom.coe_to_alg_hom, function.comp_app,
  to_continuous_map_on_alg_hom_apply, cfc₁_map_X]
  using (aeval_alg_hom (cfc₁.to_alg_hom.comp $ to_continuous_map_on_alg_hom (spectrum R a)) X).symm

/-- The continuous functional calculus extends the polynomial functional calculus. -/
lemma cfc₁_map_polynomial {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a]
  (p : R[X]) : cfc₁ (p.to_continuous_map_on $ spectrum R a) = aeval a p :=
fun_like.congr_fun (cfc₁_comp_to_continuous_map_on_alg_hom R a) p

/-- The continuous functional calculus extends the polynomial functional calculus. -/
lemma cfc₂_map_polynomial {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a]
  (p : R[X]) : cfc₂ a p.to_continuous_map = aeval a p :=
cfc₁_map_polynomial a p

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
lemma cfc₁_range_le (𝕜 : Type*) {A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A]
  [topological_space A] [algebra 𝕜 A] [star_module 𝕜 A] [topological_ring A]
  [has_continuous_star A] (a : A) [cfc_core_class 𝕜 a]
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
  [has_continuous_star A] {a : A} [cfc_core_class 𝕜 a]
  [compact_space (spectrum 𝕜 a)] (f : C(spectrum 𝕜 a, 𝕜)) :
  cfc₁ f ∈ elemental_star_algebra 𝕜 a :=
cfc₁_range_le 𝕜 a ⟨f, rfl⟩

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
lemma cfc₂_mem_elemental_star_algebra {𝕜 A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A]
  [topological_space A] [algebra 𝕜 A] [star_module 𝕜 A] [topological_ring A]
  [has_continuous_star A] (a : A) [cfc_core_class 𝕜 a]
  [compact_space (spectrum 𝕜 a)] (f : C(𝕜, 𝕜)) :
  cfc₂ a f ∈ elemental_star_algebra 𝕜 a :=
cfc₁_mem_elemental_star_algebra _

/-- The range of the continuous functional calculus is contained in the `elemental_star_algebra`
generated by the element. -/
lemma cfc₂_range_le (𝕜 : Type*) {A : Type*} [is_R_or_C 𝕜] [ring A] [star_ring A]
  [topological_space A] [algebra 𝕜 A] [star_module 𝕜 A] [topological_ring A]
  [has_continuous_star A] (a : A) [cfc_core_class 𝕜 a]
  [compact_space (spectrum 𝕜 a)] :
  (cfc₂ a : C(𝕜, 𝕜) →⋆ₐ[𝕜] A).range ≤ elemental_star_algebra 𝕜 a :=
by { rintros _ ⟨f, rfl⟩, exact cfc₂_mem_elemental_star_algebra a f }


/-- Any images under the continuous functional calculus commute. -/
@[simp]
lemma cfc₁_commute {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [cfc_core_class R a]
  (f g : C(spectrum R a, R)) : commute (cfc₁ f) (cfc₁ g) :=
(commute.all f g).map cfc₁

/-- Any images under the continuous functional calculus commute. -/
lemma cfc₂_commute {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a]
  (f g : C(R, R)) : commute (cfc₂ a f) (cfc₂ a g) :=
cfc₁_commute _ _

/-- Any image under the continuous functional calculus is normal. -/
instance cfc₁.is_star_normal {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [cfc_core_class R a]
  (f : C(spectrum R a, R)) : is_star_normal (cfc₁ f) :=
{ star_comm_self := by simpa only [map_star] using cfc₁_commute (star f) f }

/-- Any image under the continuous functional calculus is normal. -/
instance is_star_normal.cfc₂ {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_core_class R a]
  (f : C(R, R)) : is_star_normal (cfc₂ a f) :=
{ star_comm_self := by simpa only [map_star] using cfc₂_commute a (star f) f }

/-!
## Properties of special classes
-/

@[simp]
lemma cfc₁_injective (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_class R a] :
  function.injective ⇑(cfc₁ : C(spectrum R a, R) →⋆ₐ[R] A) :=
(cfc₁_closed_embedding R a).inj

lemma cfc₂_eq_iff_eq_on {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_class R a]
  {f g : C(R, R)} : cfc₂ a f = cfc₂ a g ↔ (spectrum R a).eq_on f g :=
begin
  refine ⟨λ h, _, λ h, cfc₂_eq_of_eq_on a h⟩,
  have := λ x hx, fun_like.congr_fun (cfc₁_injective R a h) ⟨x, hx⟩,
  exact this,
end

/-- For an isometric continuous functional calculus for `a` over `is_R_or_C 𝕜`, the range is
precisely the `elemental_star_algebra` generated by `a`. -/
lemma cfc₁_range {𝕜 A : Type*} [is_R_or_C 𝕜] [normed_ring A]
  [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A] [normed_star_group A]
  {a : A} [compact_space (spectrum 𝕜 a)] [cfc_class 𝕜 a] :
  (cfc₁ : C(spectrum 𝕜 a, 𝕜) →⋆ₐ[𝕜] A).range = elemental_star_algebra 𝕜 a :=
begin
  rw [star_alg_hom.range_eq_map_top, ←polynomial_functions.star_closure_topological_closure,
    ←star_subalgebra.map_topological_closure _ _ (cfc₁_closed_embedding 𝕜 a),
    polynomial_functions.star_closure_eq_adjoin_X, star_alg_hom.map_adjoin],
  congr,
  rw [set.image_singleton, to_continuous_map_on_alg_hom_apply, cfc₁_map_X]
end

-- this is the only direct result where we need the `topology.tietze_extension`
-- and also `topology.metric_space.emetric_paracompact` for `normal_space` instance.
lemma cfc₂_range {𝕜 A : Type*} [is_R_or_C 𝕜] [normed_ring A]
  [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A] [normed_star_group A]
  {a : A} [compact_space (spectrum 𝕜 a)] [cfc_class 𝕜 a] :
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
  {a : A} [compact_space (spectrum 𝕜 a)] [cfc_class 𝕜 a]
  {x : A} (hx : x ∈ elemental_star_algebra 𝕜 a) :
  ∃ f : C(spectrum 𝕜 a, 𝕜), cfc₁ f = x :=
by rwa ←cfc₁_range at hx

lemma cfc₂_exists_of_mem_elemental_star_algebra {𝕜 A : Type*} [is_R_or_C 𝕜] [normed_ring A]
  [star_ring A] [normed_algebra 𝕜 A] [star_module 𝕜 A] [normed_star_group A]
  {a : A} [compact_space (spectrum 𝕜 a)] [cfc_class 𝕜 a]
  {x : A} (hx : x ∈ elemental_star_algebra 𝕜 a) :
  ∃ f : C(𝕜, 𝕜), cfc₂ a f = x :=
by rwa ←cfc₂_range at hx

lemma cfc₁_map_spectrum (R : Type*) {A : Type*} [comm_semiring R]
  [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A]
  [star_ring A] [topological_space A] [algebra R A] (a : A)
  [cfc_class R a] (f : C(spectrum R a, R)) :
  spectrum R (cfc₁ f) = set.range f :=
cfc_class.hom_map_spectrum f

lemma cfc₂_map_spectrum {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_class R a]
  (f : C(R, R)) : (spectrum R a).maps_to f (spectrum R (cfc₂ a f)) :=
begin
  rw [cfc₂, star_alg_hom.coe_comp, function.comp_apply, cfc₁_map_spectrum],
  exact λ x hx, ⟨⟨x, hx⟩, rfl⟩,
end

lemma cfc₂_map_spectrum' {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_class R a]
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
/-
lemma cfc₁_comp {R A : Type*} [is_R_or_C R] [ring A] [star_ring A] [topological_space A]
  [t2_space A] [algebra R A] [star_module R A] (a : A) [cfc_class R a]
  (f : C(spectrum R a, R)) [cfc_class R (cfc₁ f)]
  (g : C(spectrum R (cfc₁ f), R)) (h : ∀ x, f x ∈ spectrum R (cfc₁ f))
  [compact_space (spectrum R (cfc₁ f))] :
  let f' : C(spectrum R a, spectrum R (cfc₁ f)) :=
    ⟨λ x, ⟨f x, h x⟩, by refine (map_continuous f).subtype_mk (λ x, h x)⟩ in
  cfc₁ (g.comp f') = cfc₁ g :=
begin
  let f' : C(spectrum R a, spectrum R (cfc₁ f)) :=
    ⟨λ x, ⟨f x, h x⟩, by refine (map_continuous f).subtype_mk (λ x, h x)⟩,
  let cfc₃ : cfc_class R (cfc₁ f) :=
  { to_star_alg_hom := cfc₁.comp (f'.comp_star_alg_hom' R R),
    hom_continuous := cfc_class.hom_continuous.comp f'.continuous_comp_left,
    hom_map_X :=
    begin
    simp only [star_alg_hom.coe_comp, function.comp_apply],
    congr' 1,
    ext,
    simp only [continuous_map.comp_star_alg_hom'_apply, continuous_map.comp_apply, eval_X, continuous_map.coe_mk,
  to_continuous_map_on_apply, subtype.coe_mk, to_continuous_map_apply, to_continuous_map_on_alg_hom_apply],
    end },
  exact fun_like.congr_fun ((cfc_class.ext_iff _ _).mp
    (subsingleton.elim cfc₃ ‹_›)) g,
end
-/

lemma cfc₂_comp {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [cfc_class R a]
  (f g : C(R, R)) [cfc_core_class R (cfc₂ a f)]
  [subsingleton (cfc_core_class R (cfc₂ a f))] :
  cfc₂ a (g.comp f) = cfc₂ (cfc₂ a f) g :=
begin
  let f' : C(spectrum R a, spectrum R (cfc₂ a f)) := ⟨λ r, ⟨f r, cfc₂_map_spectrum a f r.prop⟩,
    ((map_continuous f).comp continuous_induced_dom).subtype_mk (λ x, cfc₂_map_spectrum a f x.prop)⟩,
  let cfc₃ : C(spectrum R (cfc₂ a f), R) →⋆ₐ[R] A := cfc₁.comp (f'.comp_star_alg_hom' R R),
  let this : cfc_core_class R (cfc₂ a f) :=
  { to_star_alg_hom := cfc₃,
    hom_continuous := cfc_class.hom_closed_embedding.continuous.comp f'.continuous_comp_left,
    hom_map_X :=
    begin
      simp only [cfc₃, cfc₂, star_alg_hom.coe_comp, function.comp_apply],
      congr' 1,
      ext x,
      simp only [to_continuous_map_on_alg_hom_apply, continuous_map.comp_star_alg_hom'_apply, continuous_map.comp_apply,
  continuous_map.coe_mk, to_continuous_map_on_apply, subtype.coe_mk, to_continuous_map_apply, eval_X,
  continuous_map.comp_star_alg_hom'_apply, continuous_map.restrict_apply, continuous_map.coe_id, id.def],
    end },
  exact fun_like.congr_fun ((cfc_core_class.ext_iff _ _).mp
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

lemma spectrum.algebra_map_mem_iff (R S : Type*) {A : Type*} [comm_semiring R] [comm_semiring S]
  [ring A] [algebra R S] [algebra R A] [algebra S A] [is_scalar_tower R S A] {a : A} {r : R} :
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
class spectrum_restricts {R S : Type*} {A : Type*} [comm_semiring R] [comm_semiring S] [ring A]
  [algebra R S] [algebra R A] [algebra S A] (a : A) (f : S → R) : Prop :=
(right_inv_on : (spectrum S a).right_inv_on f (algebra_map R S))
(left_inv : function.left_inverse f (algebra_map R S))

-- not an instance because reasons.
lemma spectrum_restricts_of_subset_range_algebra_map {R S : Type*} {A : Type*} [comm_semiring R]
  [comm_semiring S] [ring A] [algebra R S] [algebra R A] [algebra S A] (a : A) (f : S → R)
  (hf : function.left_inverse f (algebra_map R S))
  (h : spectrum S a ⊆ set.range (algebra_map R S)) :
  spectrum_restricts a f :=
{ right_inv_on := λ s hs, by { obtain ⟨r, rfl⟩ := h hs, rw hf r },
  left_inv := hf }

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
instance spectrum_restricts.compact_space {R S : Type*} {A : Type*} [comm_semiring R]
  [topological_space R] [comm_semiring S] [topological_space S] [ring A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] {a : A} (f : C(S, R))
  [h : spectrum_restricts a f] [h' : compact_space (spectrum S a)] :
  compact_space (spectrum R a) :=
is_compact_iff_compact_space.mp $ h.is_compact (map_continuous f) $
  is_compact_iff_compact_space.mpr h'

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
(φ.restrict_scalars R).comp $ (continuous_map.comp_star_alg_hom (spectrum S a)
  (star_alg_hom.of_id R S) (algebra_map_clm R S).continuous).comp
  (continuous_map.comp_star_alg_hom' R R
    ⟨(subtype.map f h.subset_preimage), (map_continuous f).subtype_map h.subset_preimage⟩)

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[reducible]
def spectrum_restricts.cfc_core
  {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [topological_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [topological_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  [cfc_core_class S a] (f : C(S, R)) (h : spectrum_restricts a f) :
  cfc_core_class R a :=
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

-- note: the hypotheses `[metric_space R] [metric_space S] [compact_space (spectrum S a)]
-- [complete_space R] (h_isom : isometry (algebra_map R S)) are probably too strong, but they make
-- the proof that it is a `closed_embedding` significantly easier, and they apply in the cases we
-- care about most.

/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. If the spectrum is preserved
over the larger ring, then it is over the smaller ring as well. -/
@[reducible]
def spectrum_restricts.cfc
  {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [star_ring R]
  [metric_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [metric_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [topological_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  [cfc_class S a] [compact_space (spectrum S a)] [complete_space R] (f : C(S, R))
  (h : spectrum_restricts a f) (h_isom : isometry (algebra_map R S)) :
  cfc_class R a :=
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
  hom_closed_embedding :=
  begin
    refine closed_embedding.comp (cfc₁_closed_embedding S a) _,
    simp only [alg_hom.coe_to_ring_hom, star_alg_hom.coe_to_alg_hom, star_alg_hom.comp_apply,
      continuous_map.comp_star_alg_hom'_apply, continuous_map.comp_star_alg_hom_apply],
    refine isometry.closed_embedding _,
    simp only [isometry_iff_dist_eq],
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
  .. h.cfc_core f }

/-- If the spectrum of `a` restricts from `S` to `R`, then so does `cfc₁ g` for any
`g : C(spectrum R a, R)`. You should use this lemma manually to prove the spectrum restriction
result for continuous functional calculi whenever you use one of the definitions above to create an
instance.

Tou can use this to prove that, for exmaple, the spectrum (in `ℂ`) of the image of a positive
operator is nonnegative. -/
lemma spectrum_restricts.cfc_spectrum_restricts
  {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [star_ring R]
  [metric_space R] [topological_semiring R] [has_continuous_star R]
  [comm_semiring S] [star_ring S] [metric_space S] [topological_semiring S]
  [has_continuous_star S] [ring A] [star_ring A] [topological_space A] [algebra R S] [algebra R A]
  [algebra S A] [is_scalar_tower R S A] [star_module R S] [has_continuous_smul R S] {a : A}
  [cfc_class S a] [compact_space (spectrum S a)] [complete_space R] (f : C(S, R))
  (h : spectrum_restricts a f) (h_isom : isometry (algebra_map R S)) (g : C(spectrum R a, R)) :
  spectrum_restricts (@cfc₁ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfc_core f) g) f :=
{ right_inv_on :=
  begin
    letI := h.cfc f,
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

section complex_to_real

noncomputable instance cfc_core.complex_to_real
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℂ A] {a : A}
  [cfc_core_class ℂ a] [h : spectrum_restricts a continuous_map.complex_re] :
  cfc_core_class ℝ a :=
h.cfc_core _

noncomputable instance cfc.complex_to_real
  {A : Type*} [ring A] [star_ring A] [metric_space A] [algebra ℂ A] {a : A}
  [compact_space (spectrum ℂ a)] [cfc_class ℂ a]
  [h : spectrum_restricts a continuous_map.complex_re] :
  cfc_class ℝ a :=
h.cfc _ (algebra_map_isometry ℝ ℂ)

instance cfc_spectrum_restricts.complex_to_real
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℂ A] {a : A}
  [cfc_class ℂ a] [compact_space (spectrum ℂ a)]
  [h : spectrum_restricts a continuous_map.complex_re] (g : C(spectrum ℝ a, ℝ)) :
  spectrum_restricts (@cfc₁ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfc_core continuous_map.complex_re) g)
    continuous_map.complex_re :=
h.cfc_spectrum_restricts _ (algebra_map_isometry ℝ ℂ) g

instance cfc_spectrum_restricts.complex_to_real'
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℂ A] {a : A}
  [cfc_class ℂ a] [compact_space (spectrum ℂ a)]
  [h : spectrum_restricts a continuous_map.complex_re] (g : C(ℝ, ℝ)) :
  spectrum_restricts (@cfc₂ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfc_core continuous_map.complex_re) g)
    continuous_map.complex_re :=
begin
  rw [cfc₂, star_alg_hom.coe_comp, function.comp_apply],
  apply_instance,
end

end complex_to_real

section real_to_nnreal
open_locale nnreal

instance : star_ring ℝ≥0 :=
{ star := id,
  star_involutive := λ _, rfl,
  star_mul := mul_comm,
  star_add := λ _ _, rfl }

instance : has_trivial_star ℝ≥0 :=
{ star_trivial := λ _, rfl }

instance : has_continuous_star ℝ≥0 :=
{ continuous_star := continuous_id }

instance : star_module ℝ≥0 ℝ :=
{ star_smul := by simp only [star_trivial, eq_self_iff_true, forall_const] }

/-- `to_nnreal` as a bundled continuous map. -/
noncomputable def continuous_map.to_nnreal : C(ℝ, ℝ≥0) :=
⟨real.to_nnreal,
 (@continuous_induced_rng ℝ≥0 ℝ _ coe real.to_nnreal _ _).mpr (continuous_id'.max continuous_const)⟩

noncomputable instance cfc_core.real_to_nnreal
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A] {a : A}
  [compact_space (spectrum ℝ a)] [cfc_core_class ℝ a]
  [h : spectrum_restricts a continuous_map.to_nnreal] :
  cfc_core_class ℝ≥0 a :=
h.cfc_core _

noncomputable instance cfc.real_to_nnreal
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A] {a : A}
  [compact_space (spectrum ℝ a)] [cfc_class ℝ a]
  [h : spectrum_restricts a continuous_map.to_nnreal] :
  cfc_class ℝ≥0 a :=
h.cfc _ isometry_subtype_coe

instance cfc_spectrum_restricts.real_to_nnreal
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A] {a : A}
  [cfc_class ℝ a] [compact_space (spectrum ℝ a)]
  [h : spectrum_restricts a continuous_map.to_nnreal] (g : C(spectrum ℝ≥0 a, ℝ≥0)) :
  spectrum_restricts (@cfc₁ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfc_core continuous_map.to_nnreal) g)
    continuous_map.to_nnreal :=
h.cfc_spectrum_restricts _ isometry_subtype_coe g

instance cfc_spectrum_restricts.real_to_nnreal'
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A] {a : A}
  [cfc_class ℝ a] [compact_space (spectrum ℝ a)]
  [h : spectrum_restricts a continuous_map.to_nnreal] (g : C(ℝ≥0, ℝ≥0)) :
  spectrum_restricts (@cfc₂ _ _ _ _ _ _ _ _ _ _ _ _ (h.cfc_core continuous_map.to_nnreal) g)
    continuous_map.to_nnreal :=
begin
  rw [cfc₂, star_alg_hom.coe_comp, function.comp_apply],
  apply_instance,
end

end real_to_nnreal


-- this is the instance you would need to add in order to get things to work if you had an algebra
-- over `ℂ` instead of one over `ℝ` in what follows. Of course, for C⋆-algebras we already have
-- a proof of this (or rather, it follows easily), but for matrices you could provide it
-- separately.
/-
instance self_adjoint.spectrum_restricts {A : Type*} [ring A] [star_ring A] [topological_space A]
  [algebra ℂ A] {a : self_adjoint A} : spectrum_restricts (a : A) continuous_map.complex_re :=
sorry
-/

lemma cfc₂_real_is_self_adjoint
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A]
  (a : A) [cfc_class ℝ a] (f : C(ℝ, ℝ)) :
  is_self_adjoint (cfc₂ a f) :=
show star _ = _, by rw [←map_star, star_trivial]

-- composition still works as long as we have propositinal equality of the intermediate elements.
lemma self_adjoint.cfc₂_comp
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A]
  (a b : self_adjoint A) (f g : C(ℝ, ℝ))
  [cfc_class ℝ (a : A)]
  [subsingleton (cfc_core_class ℝ (cfc₂ (a : A) f))]
  -- alternatively: [compact_space (spectrum ℝ (cfc₂ (a : A) f))] [t2_space A]
  [h' : cfc_class ℝ (b : A)]
  (h : cfc₂ (a : A) f = b) :
  cfc₂ (a : A) (g.comp f) = cfc₂ (b : A) g :=
begin
  letI : cfc_class ℝ (cfc₂ (a : A) f),
    from cast (by rw h) h',
  rw cfc₂_comp (a : A) f g,
  congr' 3,
  simp only [cast_heq],
end

lemma self_adjoint.cfc₂_comp_coe_mk
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A]
  (a : self_adjoint A) (f g : C(ℝ, ℝ))
  [Π b : self_adjoint A, cfc_class ℝ (b : A)]
  [subsingleton (cfc_core_class ℝ (cfc₂ (a : A) f))]
  -- alternatively: [compact_space (spectrum ℝ (cfc₂ (a : A) f))] [t2_space A]
  (h := cfc₂_real_is_self_adjoint (a : A) f) :
  cfc₂ (a : A) (g.comp f) = cfc₂ ((⟨cfc₂ (a : A) f, h⟩ : self_adjoint A) : A) g :=
self_adjoint.cfc₂_comp a _ f g rfl

@[simps]
def cfcℝ {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A] [star_module ℝ A]
  (a : self_adjoint A) [cfc_class ℝ (a : A)] :
  C(ℝ, ℝ) →L[ℝ] self_adjoint A :=
{ to_fun := λ f, ⟨cfc₂ (a : A) f, cfc₂_real_is_self_adjoint a f⟩,
  map_add' := λ f g, subtype.ext (by simp only [subtype.coe_mk, add_subgroup.coe_add, map_add]),
  map_smul' := λ r f, subtype.ext $
    by simp only [map_smul, ring_hom.id_apply, self_adjoint.coe_smul, subtype.coe_mk],
  cont := continuous_induced_rng.mpr (cfc₂_continuous ℝ a) }

lemma cfcℝ_comp
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A] [star_module ℝ A]
  (a : self_adjoint A) (f g : C(ℝ, ℝ))
  [Π b : self_adjoint A, cfc_class ℝ (b : A)]
  [h : Π b : self_adjoint A, subsingleton (cfc_core_class ℝ (b : A))] :
  cfcℝ a (g.comp f) = cfcℝ (cfcℝ a f) g :=
begin
  ext,
  simp only [cfcℝ_apply_coe],
  haveI : subsingleton (cfc_core_class ℝ (cfc₂ (a : A) f)),
    simpa only using h ⟨cfc₂ (a : A) f, cfc₂_real_is_self_adjoint a f⟩,
  refine self_adjoint.cfc₂_comp _ _ _ _ rfl,
end

section selfadjoint

variables
  {A : Type*} [ring A] [star_ring A] [topological_space A] [algebra ℝ A] [star_module ℝ A]
  [Π b : self_adjoint A, cfc_class ℝ (b : A)]
  [Π b : self_adjoint A, subsingleton (cfc_core_class ℝ (b : A))]

lemma coe_cfcℝ_commute (a : self_adjoint A) (f g : C(ℝ, ℝ)) :
  commute (cfcℝ a f : A) (cfcℝ a g) :=
by simpa only [cfcℝ_apply_coe] using cfc₂_commute (a : A) f g

lemma cfcℝ_map_X (a : self_adjoint A) :
  cfcℝ a (X.to_continuous_map) = a :=
subtype.ext (by rw [cfcℝ_apply_coe, cfc₂_map_X])

lemma cfcℝ_map_id (a : self_adjoint A) :
  cfcℝ a (continuous_map.id ℝ) = a :=
by rw [←X_to_continuous_map, cfcℝ_map_X]

lemma cfcℝ_X_pow (a : self_adjoint A) (n : ℕ) :
  cfcℝ a (X.to_continuous_map ^ n) = a ^ n :=
begin
  ext,
  rw [cfcℝ_apply_coe, ←to_continuous_map_alg_hom_apply, map_pow, to_continuous_map_alg_hom_apply,
    cfc₂_map_X, self_adjoint.coe_pow],
end

lemma cfcℝ_pow_comm (a : self_adjoint A) (n : ℕ) (f : C(ℝ, ℝ)) :
  cfcℝ (a ^ n) f = cfcℝ a (f.comp (X ^ n : ℝ[X]).to_continuous_map) :=
by { rw [←to_continuous_map_alg_hom_apply, map_pow, cfcℝ_comp, ←cfcℝ_X_pow], refl }

lemma cfcℝ_smul_comm (a : self_adjoint A) (r : ℝ) (f : C(ℝ, ℝ)) :
  cfcℝ (r • a) f = cfcℝ a (f.comp (r • continuous_map.id ℝ)) :=
by rw [cfcℝ_comp, map_smul, cfcℝ_map_id]

.

lemma cfcℝ_one (f : C(ℝ, ℝ)) : cfcℝ (1 : self_adjoint A) f = (f 1) • 1 :=
begin
  ext,
  rw [cfcℝ_apply_coe, self_adjoint.coe_smul],
  nth_rewrite_rhs 0 self_adjoint.coe_one,
  have := map_one ((cfc₂ ((1 : self_adjoint A) : A) : C(ℝ, ℝ) →⋆ₐ[ℝ] A)),
  rw [←this, ←map_smul],
  refine cfc₂_eq_of_eq_on _ _,
  simp only [continuous_map.coe_smul, continuous_map.coe_one, self_adjoint.coe_one],
  nontriviality A,
  rw [spectrum.one_eq, set.eq_on_singleton],
  simp only [pi.smul_apply, pi.one_apply, algebra.id.smul_eq_mul, mul_one],
end

lemma cfcℝ_neg_comm (a : self_adjoint A) (f : C(ℝ, ℝ)) :
  cfcℝ (-a) f = cfcℝ a (f.comp (-(continuous_map.id ℝ))) :=
by rw [cfcℝ_comp, map_neg, cfcℝ_map_id]

noncomputable instance self_adjoint.has_pos_part : has_pos_part (self_adjoint A) :=
{ pos := λ a, cfcℝ a (continuous_map.id ℝ ⊔ 0) }

lemma self_adjoint.pos_part_def (a : self_adjoint A) :
  a⁺ = cfcℝ a (continuous_map.id ℝ ⊔ 0) := rfl

lemma self_adjoint.coe_pos_part (a : self_adjoint A) :
  (↑(a⁺) : A) = cfc₂ (a : A) (continuous_map.id ℝ ⊔ 0) :=
rfl

noncomputable instance self_adjoint.has_neg_part : has_neg_part (self_adjoint A) :=
{ neg := λ a, cfcℝ a ((-(continuous_map.id ℝ)) ⊔ 0) }

lemma self_adjoint.neg_part_def (a : self_adjoint A) :
  a⁻ = cfcℝ a ((-(continuous_map.id ℝ)) ⊔ 0) := rfl

lemma self_adjoint.coe_neg_part (a : self_adjoint A) :
  (↑(a⁻) : A) = cfc₂ (a : A) ((-(continuous_map.id ℝ)) ⊔ 0) := rfl

lemma self_adjoint.neg_part_neg (a : self_adjoint A) : (-a)⁻ = a⁺ :=
begin
  rw [self_adjoint.neg_part_def, self_adjoint.pos_part_def, cfcℝ_neg_comm],
  congr,
  ext x,
  simp only [continuous_map.comp_apply, continuous_map.neg_apply, continuous_map.id_apply,
    continuous_map.sup_apply, neg_neg, continuous_map.zero_apply],
end

lemma self_adjoint.pos_part_neg (a : self_adjoint A) : (-a)⁺ = a⁻ :=
by simpa only [neg_neg] using (self_adjoint.neg_part_neg (-a)).symm

instance {X Y : Type*} [topological_space X] [topological_space Y] [has_add Y]
  [has_continuous_add Y] [partial_order Y] [covariant_class Y Y (+) (≤)] :
  covariant_class C(X, Y) C(X, Y) (+) (≤) :=
{ elim := λ f g h h' x, add_le_add_left (h' x) _ }

lemma self_adjoint.pos_part_sub_neg_part (a : self_adjoint A) : a⁺ - a⁻ = a :=
begin
  simp only [self_adjoint.neg_part_def, self_adjoint.pos_part_def, ←map_sub],
  simp only [sub_eq_add_neg, neg_sup_eq_neg_inf_neg, neg_neg, neg_zero],
  rw [add_comm, inf_add_sup, add_zero, cfcℝ_map_id],
end

-- it is essential to use coercions here because `self_adjoint A` can't have a `has_mul` instance
-- should we define a partial multiplication on `self_adjoint A`? I think not, but maybe.
lemma self_adjoint.pos_part_mul_neg_part (a : self_adjoint A) : (↑(a⁺) : A) * ↑(a⁻) = 0 :=
begin
  simp only [self_adjoint.pos_part_def, self_adjoint.neg_part_def, cfcℝ_apply_coe, ←map_mul],
  convert map_zero (cfc₂ (a : A)),
  ext x,
  simp only [continuous_map.mul_apply, continuous_map.sup_apply, continuous_map.id_apply,
    continuous_map.zero_apply, continuous_map.neg_apply, mul_eq_zero, max_eq_right_iff,
    right.neg_nonpos_iff],
  exact le_total _ _,
end

-- it is essential to use coercions here because `self_adjoint A` can't have a `has_mul` instance
lemma self_adjoint.neg_part_mul_pos_part (a : self_adjoint A) : (↑(a⁻) : A) * ↑(a⁺) = 0 :=
by { convert self_adjoint.pos_part_mul_neg_part a using 1, exact (coe_cfcℝ_commute _ _ _) }

.

end selfadjoint

namespace spectrum


open_locale nnreal

@[protect_proj]
structure is_positive {A : Type*} [ring A] [has_star A] [algebra ℝ A] (a : A) : Prop :=
(is_self_adjoint : is_self_adjoint a)
(spectrum_nonneg : ∀ x ∈ spectrum ℝ a, (0 : ℝ) ≤ x)

/-- This class exists because it is not possible to prove using the existence of the continuous
functional calculus alone. One needs to use in an essential way that the continuous functional
calculus is an isometry, and we cannot use that fact in all the places where we want the
continuous functional calculus because in those places we do not have a metric structure. However,
we still want to develop the calculus for positive elements in as general a way as possible. -/
class is_positive_add_class (A : Type*) [ring A] [has_star A] [algebra ℝ A] : Prop :=
(add' : ∀ {a b : A} (ha : is_positive a) (hb : is_positive b), is_positive (a + b))

alias is_positive_add_class.add' ← is_positive.add

section
open_locale pointwise
-- note: `spectrum.smul_eq_smul` does not need the `nontrivial` hypothesis.
theorem smul_eq_smul' {𝕜 : Type*} {A : Type*} [field 𝕜] [ring A] [algebra 𝕜 A] -- [nontrivial A]
  (k : 𝕜) (a : A) (ha : (spectrum 𝕜 a).nonempty) :
spectrum 𝕜 (k • a) = k • spectrum 𝕜 a :=
begin
  nontriviality A,
  exact spectrum.smul_eq_smul k a ha,
end
end

lemma is_positive.nnreal_smul {A : Type*} [ring A] [algebra ℝ A] [star_add_monoid A]
  [star_module ℝ A] (r : ℝ≥0) {a : A} (ha : is_positive a) : is_positive (r • a) :=
begin
  refine ⟨(is_self_adjoint.all (r : ℝ)).smul ha.is_self_adjoint, _⟩,
  nontriviality A,
  by_cases hr : r = 0,
  simp only [hr, zero_smul, zero_eq, set.mem_singleton_iff, forall_eq],
  have u := is_unit.mk0 (r : ℝ) (nnreal.coe_ne_zero.mpr hr),
  rw [nnreal.smul_def, ←u.coe_unit', ←units.smul_def, unit_smul_eq_smul],
  rintro _ ⟨x, hx, rfl⟩,
  rw [units.smul_def, u.coe_unit'],
  exact mul_nonneg r.prop (ha.spectrum_nonneg x hx),
end

lemma is_positive.real_smul {A : Type*} [ring A] [algebra ℝ A] [star_add_monoid A]
  [star_module ℝ A] {r : ℝ} (hr : 0 ≤ r) {a : A} (ha : is_positive a) : is_positive (r • a) :=
ha.nnreal_smul ⟨r, hr⟩

lemma is_positive.zero {A : Type*} [ring A] [algebra ℝ A] [star_add_monoid A] [star_module ℝ A] :
  is_positive (0 : A) :=
begin
  refine ⟨is_self_adjoint_zero A, _⟩,
  nontriviality A,
  simp only [zero_eq, set.mem_singleton_iff, forall_eq],
end

lemma is_positive.one {A : Type*} [ring A] [algebra ℝ A] [star_ring A] [star_module ℝ A] :
  is_positive (1 : A) :=
begin
  refine ⟨is_self_adjoint_one A, _⟩,
  nontriviality A,
  simp only [one_eq, set.mem_singleton_iff, forall_eq, zero_le_one],
end

.

lemma is_positive_tfae (A : Type*) [ring A] [star_ring A] [topological_space A] [algebra ℝ A]
  [star_module ℝ A] [Π b : self_adjoint A, cfc_class ℝ (b : A)]
  [Π b : self_adjoint A, subsingleton (cfc_core_class ℝ (b : A))] (a : A) :
  tfae [is_positive a, ∃ x : self_adjoint A, (x ^ 2 : A) = a, ∃ x : A, star x * x = a] :=
begin
  tfae_have : 1 → 2,
  { intro ha,
    lift a to ↥(self_adjoint A) using ha.is_self_adjoint,
    use cfcℝ a ⟨real.sqrt⟩,
    rw [←self_adjoint.coe_pow, ←subtype.ext_iff, ←cfcℝ_X_pow, ←cfcℝ_comp],
    nth_rewrite_rhs 0 [←cfcℝ_map_id a],
    ext x,
    simp only [continuous_map.pow_apply, continuous_map.comp_apply, continuous_map.coe_mk,
      to_continuous_map_apply, eval_X, continuous_map.id_apply],
    sorry, },
  tfae_have : 2 → 3,
  { sorry },
  tfae_have : 3 → 1,
  { sorry },
  tfae_finish,
end

#exit

def star_ordered_ring.positive (A : Type*) [non_unital_semiring A] [partial_order A] [star_ordered_ring A] :
  add_submonoid A :=
{ carrier := {a : A | 0 ≤ a},
  add_mem' := λ a b,
  begin
    simp only [set.mem_set_of, star_ordered_ring.nonneg_iff],
    exact add_mem,
  end,
  zero_mem' := le_rfl }


/-
instance {α β : Type*} [topological_space α] [topological_space β] [is_empty α] :
  subsingleton C(α, β) :=
fun_like.coe_injective.subsingleton
-- actually, we should be able to get a `unique` instance here

lemma is_positive.cfc₂_dist_eq_Inf {A : Type*} [ring A] [star_ring A] [metric_space A]
  [algebra ℝ A] [star_module ℝ A] {a : A} (ha : is_positive a) [compact_space (spectrum ℝ a)]
  [continuous_functional_calculus_isometry_class ℝ a] :
  dist a 0 = Inf {C : ℝ | 0 ≤ C ∧ ∀ x ∈ spectrum ℝ a, x ≤ C} :=
begin
  nth_rewrite 0 [←cfc₂_map_id ℝ a],
  rw self_adjoint.cfc₂_dist_eq,
  congr,
  ext C,
  simp only [continuous_map.id_apply, real.norm_eq_abs, and.congr_right_iff],
  intros C,
  refine ⟨λ h x hx, _, λ h x hx, _⟩,
  { obtain ⟨x, rfl⟩ := ha.spectrum_subset hx,
    have := h _ hx,
    rwa [abs_of_nonneg (show 0 ≤ algebra_map ℝ≥0 ℝ x, from x.prop)] at this },
  { obtain ⟨x, rfl⟩ := ha.spectrum_subset hx,
    have := h _ hx,
    rwa [abs_of_nonneg (show 0 ≤ algebra_map ℝ≥0 ℝ x, from x.prop)] },
end

-- works even for normal operators, likely useless
lemma _root_.is_self_adjoint.spectrum_nonempty
  {A : Type*} [ring A] [star_ring A] [metric_space A] [algebra ℝ A] [star_module ℝ A]
  {a : A} (ha : is_self_adjoint a) [compact_space (spectrum ℝ a)]
  [continuous_functional_calculus_isometry_class ℝ a] [nontrivial A] :
  (spectrum ℝ a).nonempty :=
begin
  rw set.nonempty_iff_ne_empty,
  intro h,
  have : cfc₂ a (1 : C(ℝ, ℝ)) = cfc₂ a (0 : C(ℝ, ℝ)),
    from cfc₂_eq_of_eq_on a (λ r hr, by { rw h at hr, exact false.elim hr }),
  exact one_ne_zero (by rwa [map_one, map_zero] at this),
end

lemma foo (X : set ℝ) [compact_space X] {c : ℝ} (hc : ‖(continuous_map.id ℝ).restrict X‖ ≤ c) :
  ‖(continuous_map.id ℝ).restrict X - algebra_map ℝ C(X, ℝ) c‖ ≤ c ↔ ∀ x : X, 0 ≤ (x : ℝ) :=
begin
  /- unfreezingI {cases is_empty_or_nonempty X with h h},
  sorry { have : (continuous_map.id ℝ).restrict X - algebra_map ℝ C(X, ℝ) c = 0 := subsingleton.elim _ _,
    simp only [this, is_empty.forall_iff, iff_true, norm_zero],
    exact (norm_nonneg _).trans hc },
  have : nontrivial C(X, ℝ) := infer_instance, -/
  rw continuous_map.norm_le _ ((norm_nonneg _).trans hc),
  refine forall_congr (λ x, _),
  simp only [continuous_map.sub_apply, continuous_map.restrict_apply, continuous_map.id_apply,
    _root_.algebra_map_apply, algebra.id.smul_eq_mul, mul_one, real.norm_eq_abs],
  rw abs_le,
  refine ⟨λ h, _, λ h, _⟩,
  linarith,
  split,
  rwa [le_sub_iff_add_le, neg_add_self],
end

lemma is_self_adjoint.dist_sub_algebra_map_le_iff
  {A : Type*} [ring A] [star_ring A] [metric_space A] [algebra ℝ A] [star_module ℝ A]
  (a : A) (ha : is_self_adjoint a) [compact_space (spectrum ℝ (a : A))]
  [continuous_functional_calculus_isometry_class ℝ (a : A)]
  {x : ℝ} (hx : dist (a : A) 0 ≤ x) :
  (dist (a - algebra_map ℝ A x : A) 0 ≤ x) ↔ spectrum ℝ (a : A) ⊆ set.range (algebra_map ℝ≥0 ℝ) :=
begin
  casesI subsingleton_or_nontrivial A with hA hA,
  simp only [(subsingleton.elim _ _ : (a : A) - algebra_map ℝ A x = a), hx, of_subsingleton,
    set.empty_subset],
  refine ⟨λ h, _, _⟩,
  { have : cfc₂ a ((continuous_map.id ℝ) - algebra_map ℝ C(ℝ, ℝ) x) = a - algebra_map ℝ A x,
      by rw [map_sub, cfc₂_map_id, alg_hom_class.commutes],
    rw [←this, self_adjoint.cfc₂_dist_eq] at h,
    rw cInf_le_iff _ _ at h,
    { intros y hy,
      have : x - y ≤ x,
      refine h (x - y) (λ C (hC : _ ∧ _), _), },
    { exact ⟨0, λ C hC, hC.1⟩ },
    { have hsa : is_compact (spectrum ℝ a) := is_compact_iff_compact_space.mpr ‹_›,
      obtain ⟨z, _, hz⟩ := hsa.exists_forall_ge ha.spectrum_nonempty
        ((map_continuous (continuous_map.id ℝ - algebra_map ℝ C(ℝ, ℝ) x)).norm.continuous_on),
      exact ⟨max _ 0, ⟨le_max_right _ _,  λ y hy, (hz y hy).trans (le_max_left _ _)⟩⟩ } },
  { sorry }
end
-/
