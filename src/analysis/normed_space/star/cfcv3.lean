import analysis.normed_space.star.background
import analysis.normed_space.star.polynomial


.
set_option old_structure_cmd true

section prereqs

-- I think this goes in analysis.normed_space.star.spectrum
-- also we need a `star_alg_equiv_class.to_star_alg_equiv` declaration.
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

end prereqs

open_locale nnreal
local notation `C⋆(` a `)` := elemental_star_algebra ℂ a

section cfc_class

open_locale polynomial
open polynomial


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

-- this class should be satisfied by matrices.
@[ext]
class continuous_functional_calculus_injective_class (R : Type*) {A : Type*} [comm_semiring R]
  [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A]
  [star_ring A] [topological_space A] [algebra R A] (a : A)
  extends continuous_functional_calculus_class R a :=
(hom_injective : function.injective to_star_alg_hom)

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

@[ext]
class continuous_functional_calculus_spectrum_class (R : Type*) {A : Type*} [comm_semiring R]
  [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A]
  [star_ring A] [topological_space A] [algebra R A] (a : A)
  extends continuous_functional_calculus_class R a :=
(hom_map_spectrum : ∀ f, spectrum R (to_star_alg_hom f) = set.range f)

def cfc₁ {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [continuous_functional_calculus_class R a] :
  C(spectrum R a, R) →⋆ₐ[R] A :=
(‹_› : continuous_functional_calculus_class R a).to_star_alg_hom

lemma cfc₁_commute {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [continuous_functional_calculus_class R a]
  (f g : C(spectrum R a, R)) : commute (cfc₁ f) (cfc₁ g) :=
(commute.all f g).map cfc₁

instance is_star_normal.cfc₁ {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] {a : A} [continuous_functional_calculus_class R a]
  (f : C(spectrum R a, R)) : is_star_normal (cfc₁ f) :=
{ star_comm_self := by simpa only [map_star] using cfc₁_commute (star f) f }

@[simp]
lemma cfc₁_map_X (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  cfc₁ (X.to_continuous_map_on $ spectrum R a) = a :=
(‹_› : continuous_functional_calculus_class R a).hom_map_X

@[simp]
lemma cfc₁_map_C {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] (r : R) :
  cfc₁ ((C r).to_continuous_map_on $ spectrum R a) = algebra_map R A r :=
(cfc₁.to_alg_hom.comp (to_continuous_map_on_alg_hom $ spectrum R a)).commutes' r

lemma cfc₁_comp_to_continuous_map_on_alg_hom (R : Type*) {A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  cfc₁.to_alg_hom.comp (to_continuous_map_on_alg_hom $ spectrum R a) = aeval a :=
by simpa only [aeval_X_left, alg_hom.coe_comp, star_alg_hom.coe_to_alg_hom, function.comp_app,
  to_continuous_map_on_alg_hom_apply, cfc₁_map_X]
  using (aeval_alg_hom (cfc₁.to_alg_hom.comp $ to_continuous_map_on_alg_hom (spectrum R a)) X).symm

lemma cfc₁_map_polynomial {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  (p : R[X]) : cfc₁ (p.to_continuous_map_on $ spectrum R a) = aeval a p :=
fun_like.congr_fun (cfc₁_comp_to_continuous_map_on_alg_hom R a) p

lemma cfc₁_map_spectrum (R : Type*) {A : Type*} [comm_semiring R]
  [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A]
  [star_ring A] [topological_space A] [algebra R A] (a : A)
  [continuous_functional_calculus_spectrum_class R a] (f : C(spectrum R a, R)) :
  spectrum R (cfc₁ f) = set.range f :=
continuous_functional_calculus_spectrum_class.hom_map_spectrum f

section
universes u v
def cfc₂ {R : Type u} {A : Type v} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  C(R, R) →⋆ₐ[R] A :=
cfc₁.comp (continuous_map.restrict_star_alg_hom R R $ spectrum R a)
end

lemma cfc₂_eq_of_eq_on {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  {f g : C(R, R)} (h : (spectrum R a).eq_on f g) : cfc₂ a f = cfc₂ a g :=
begin
  simp only [cfc₂, star_alg_hom.coe_comp, function.comp],
  exact congr_arg _ (continuous_map.ext $ λ x, h x.prop),
end

@[simp]
lemma cfc₂_map_X {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] :
  cfc₂ a (X : R[X]).to_continuous_map = a :=
cfc₁_map_X R a

@[simp]
lemma cfc₂_map_C {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a] (r : R) :
  cfc₂ a (C r).to_continuous_map = algebra_map R A r :=
cfc₁_map_C a r

lemma cfc₂_map_polynomial {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  (p : R[X]) : cfc₂ a p.to_continuous_map = aeval a p :=
cfc₁_map_polynomial a p

lemma cfc₂_commute {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  (f g : C(R, R)) : commute (cfc₂ a f) (cfc₂ a g) :=
cfc₁_commute _ _

instance is_star_normal.cfc₂ {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_class R a]
  (f : C(R, R)) : is_star_normal (cfc₂ a f) :=
{ star_comm_self := by simpa only [map_star] using cfc₂_commute a (star f) f }

-- here we need the `spectrum_class`
lemma cfc₂_map_spectrum {R A : Type*} [comm_semiring R] [star_ring R]
  [topological_space R] [topological_semiring R] [has_continuous_star R] [ring A] [star_ring A]
  [topological_space A] [algebra R A] (a : A) [continuous_functional_calculus_spectrum_class R a]
  (f : C(R, R)) : (spectrum R a).maps_to f (spectrum R (cfc₂ a f)) :=
begin
  rw [cfc₂, star_alg_hom.coe_comp, function.comp_apply, cfc₁_map_spectrum],
  exact λ x hx, ⟨⟨x, hx⟩, rfl⟩,
end

-- this is not a terrible version, but presumably we will want something better.
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
  continuous_map.restrict_star_alg_hom_apply, continuous_map.restrict_apply],
    end },
  exact fun_like.congr_fun ((continuous_functional_calculus_class.ext_iff _ _).mp
    (subsingleton.elim this ‹_›)) (g.restrict (spectrum R (cfc₂ a f))),
end

-- nice the specialized lemma just works out of the box. If we give a subsingleton instance for `R = ℝ≥0`
-- then it will work too.
lemma cfc₂_comp' {R A : Type*} [is_R_or_C R] [ring A] [star_ring A] [topological_space A] [t2_space A]
  [algebra R A] [star_module R A] (a : A) [continuous_functional_calculus_spectrum_class R a]
  (f g : C(R, R)) [continuous_functional_calculus_class R (cfc₂ a f)] [compact_space (spectrum R (cfc₂ a f))] :
  cfc₂ a (g.comp f) = cfc₂ (cfc₂ a f) g :=
cfc₂_comp a f g

section standard_cfc

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]
variables [complete_space A] (a : A) [is_star_normal a]

noncomputable instance is_star_normal.continuous_functional_calculus_isometry_class :
  continuous_functional_calculus_isometry_class ℂ a :=
{ to_star_alg_hom := C⋆(a).subtype.comp (continuous_functional_calculus a),
  hom_isometry := isometry_subtype_coe.comp
    (@star_alg_equiv.isometry _ _ _ _ _ _ _ _ _ _ _ _ _ star_alg_equiv.star_alg_equiv_class $
    continuous_functional_calculus a),
  hom_map_X :=
  begin
    convert congr_arg coe (continuous_functional_calculus_map_id a),
    simp only [star_alg_hom.comp_apply, star_alg_hom.coe_coe, star_subalgebra.subtype_apply],
    congr' 2,
    exact continuous_map.ext (λ _, eval_X),
  end }

noncomputable instance is_star_normal.continuous_functional_calculus_spectrum_class :
  continuous_functional_calculus_spectrum_class ℂ a :=
{ to_star_alg_hom := C⋆(a).subtype.comp (continuous_functional_calculus a),
  hom_map_spectrum := λ f,
  begin
    simp only [star_subalgebra.coe_subtype, star_alg_hom.coe_coe, star_alg_hom.comp_apply],
    rw [←star_subalgebra.spectrum_eq (elemental_star_algebra.is_closed ℂ a), alg_equiv.spectrum_eq,
      continuous_map.spectrum_eq_range],
  end,
  .. continuous_functional_calculus_isometry_class.to_continuous_functional_calculus_injective_class ℂ a }

-- just checking it works!
example (f g : C(ℂ, ℂ)) : cfc₂ a (g.comp f) = cfc₂ (cfc₂ a f) g := cfc₂_comp a f g

end standard_cfc

.
/-- Range of an `star_alg_hom` as a star subalgebra. -/
protected def star_alg_hom.range {R A B : Type*} [comm_semiring R] [star_ring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] [has_star A] [star_ring B] [star_module R B]
  (φ : A →⋆ₐ[R] B) : star_subalgebra R B :=
{ carrier := set.range φ,
  star_mem' := by { rintro _ ⟨b, rfl⟩, exact ⟨star b, map_star φ b⟩ },
  .. φ.to_alg_hom.range }

protected def star_alg_hom.cod_restrict {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [star_ring B] [star_module R B]
  (f : A →⋆ₐ[R] B) (S : star_subalgebra R B) (hf : ∀ x, f x ∈ S) : A →⋆ₐ[R] S :=
{ map_star' := λ x, subtype.ext (map_star f x),
  .. alg_hom.cod_restrict f.to_alg_hom S.to_subalgebra hf }

def star_alg_hom.range_restrict {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [star_ring B] [star_module R B]
  (f : A →⋆ₐ[R] B) : A →⋆ₐ[R] f.range :=
star_alg_hom.cod_restrict f _ (λ x, ⟨x, rfl⟩)

#lint

#exit

noncomputable def star_alg_equiv.of_injective {R A B : Type*} [comm_semiring R] [star_ring R]
  [semiring A] [semiring B] [algebra R A] [algebra R B] [has_star A] [star_ring B] [star_module R B]
  (f : A →⋆ₐ[R] B) (hf : function.injective f) : A ≃⋆ₐ[R] f.range :=
{ to_fun := f.range_restrict,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  map_mul' := _,
  map_add' := _,
  commutes' := _ }

end cfc_class
