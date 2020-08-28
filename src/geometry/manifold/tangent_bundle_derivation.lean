import geometry.manifold.algebra.smooth_functions
import ring_theory.derivation
import geometry.manifold.temporary_to_be_removed

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

open_locale manifold

@[reducible] def smooth_map_at (x : M) := C∞(I, M; 𝕜)

notation `C∞(` I `, `x`)` := smooth_map_at I x

namespace smooth_map_at

variables {I} {M}

instance {x : M} : module C∞(I, x) 𝕜 :=
{ smul := λ f k, f x * k,
  one_smul := λ k, one_mul k,
  mul_smul := λ f g k, mul_assoc _ _ _,
  smul_add := λ f g k, mul_add _ _ _,
  smul_zero := λ f, mul_zero _,
  add_smul := λ f g k, add_mul _ _ _,
  zero_smul := λ f, zero_mul _ }

@[simp] lemma smul_def (x : M) (k : 𝕜) (f : C∞(I, x)) :
  f • k = (f x) • k := rfl

instance {x : M} :
  is_scalar_tower 𝕜 C∞(I, x) 𝕜 :=
{ smul_assoc := λ h f k, by simp only [smul_def, smooth_map.smul_apply, algebra.id.smul_eq_mul,
    mul_assoc] }

end smooth_map_at

variables (I)

@[reducible] def point_derivation (x : M) := derivation 𝕜 C∞(I, x) 𝕜

variables (M)

section

open finite_dimensional classical

variables [finite_dimensional 𝕜 E]

@[reducible] def tangent_bundle_derivation := Σ x : M, point_derivation I x

variables {I} {M}

@[reducible] def tangent_bundle_derivation.proj : tangent_bundle_derivation I M → M := λ v, v.1

section

def dir_deriv (f : E → 𝕜) (a : E) (v : E) := deriv (λ t : 𝕜, f (a + t • v)) 0

end

open_locale big_operators classical

namespace tangent_bundle_derivation

def chart : (local_homeomorph M H) → (local_equiv (tangent_bundle_derivation I M) (model_prod H E)) :=
λ e,
{ to_fun := λ vₓ, ⟨e vₓ.1,
    ∑ w : (↑(some (exists_is_basis_finset 𝕜 E)) : set E), (vₓ.2 (⟨λ x : M, ((some_spec
    (exists_is_basis_finset 𝕜 E)).repr ∘ I ∘ e) x w, sorry⟩)) • (w : E)⟩,
  inv_fun := λ ⟨x, v⟩, ⟨e.symm x, ⟨⟨λ f, dir_deriv (f ∘ e.symm ∘ I.symm) (I x) v,
    sorry, sorry⟩, sorry⟩⟩,
  source := proj⁻¹' e.source,
  target := e.target.prod set.univ,
  map_source' := λ x h, begin sorry end,
  map_target' := λ y h, begin sorry end,
  left_inv' := λ x h, begin sorry end,
  right_inv' := λ y h, begin sorry end }

def charted_space_core : charted_space_core (model_prod H E) (tangent_bundle_derivation I M) :=
{ atlas := (chart)'' (atlas H M),
  chart_at := λ x, chart (chart_at H (proj x)),
  mem_chart_source := λ x, begin sorry end,
  chart_mem_atlas := λ x, begin sorry end,
  open_source := λ e f he hf, begin sorry end,
  continuous_to_fun := λ e f he hf, begin sorry, end }

instance : topological_space (tangent_bundle_derivation I M) :=
(charted_space_core).to_topological_space

instance : charted_space (model_prod H E) (tangent_bundle_derivation I M) :=
(charted_space_core).to_charted_space

instance : smooth_manifold_with_corners I.tangent (tangent_bundle_derivation I M) :=
{ compatible := begin
    rintros f g ⟨f1, ⟨f2, rfl⟩, f3, ⟨⟨f', hf', hf2⟩, rfl⟩, hf⟩ ⟨g1, ⟨g2, rfl⟩, g3, ⟨⟨g', hg', hg2⟩, rfl⟩, hg⟩,
    dsimp at *,
    simp only [set.mem_singleton_iff] at *,
    induction hf2,
    induction hg2,
    have h := has_groupoid.compatible (times_cont_diff_groupoid ⊤ I) hf' hg',
    sorry,
  end }

def inv_chart (e : local_homeomorph (tangent_bundle_derivation I M) (model_prod H E))
  (h : ∀ v w : tangent_bundle_derivation I M, v.proj = w.proj ↔ (e v).1 = (e w).1)
  (h2 : (prod.snd)'' e.target = set.univ) :
  (local_homeomorph M H) :=
{
  to_fun := λ x, (e ⟨x, 0⟩).1,
  inv_fun := λ x, (e.symm ⟨x, 0⟩).1,
  source := (proj)'' e.source,
  target := (prod.fst)'' e.target,
  map_source' := λ x, by { rintro ⟨a, ha, hb⟩,
    simp only [set.mem_image, exists_and_distrib_right, exists_eq_right, prod.exists],
    use (e a).2,
    have h' : (e ⟨x, 0⟩).fst = (e a).fst := by { apply (h _ _).1, symmetry, exact hb, },
    rw [h', prod.mk.eta],
    exact e.map_source ha },
  map_target' := λ x, by {
    intro h',
    simp only [set.mem_image],
    rcases h' with ⟨v, hv1, hv2⟩,
    use (e.symm v),
    have h1 := e.map_target hv1,
    refine ⟨e.map_target hv1, _⟩,
    have h3 : (⟨x, 0⟩ : H × E) ∈ e.target := by { by_contradiction,
      have aa : prod.fst v ∈ (prod.fst)'' e.target := set.mem_image_of_mem prod.fst hv1,
      rw hv2 at aa,
      clear hv1 hv2 h,
      sorry, },
    have h4 : (e (e.symm v)).fst = (e (e.symm (⟨x, 0⟩ : H × E))).fst := by { rw e.right_inv hv1, rw e.right_inv h3, exact hv2 },
    apply (h _ _).2,
    exact h4,
  },
  left_inv' := sorry,
  right_inv' := sorry,
  open_source := sorry,
  open_target := sorry,
  continuous_to_fun := sorry,
  continuous_inv_fun := sorry,
}

end tangent_bundle_derivation

/-instance : has_add (tangent_bundle_derivation I M) :=
{ add := λ v w, sigma.mk v.1 (v.2 + w.2) }-/

variables {I M}

def tangent_space_inclusion {x : M} (v : point_derivation I x) : tangent_bundle_derivation I M :=
sigma.mk x v

end

section

namespace point_derivation

variables {I} {M} {x y : M} {v w : point_derivation I x} (f g : C∞(I, M; 𝕜)) (r : 𝕜)

lemma coe_injective (h : ⇑v = w) : v = w := derivation.coe_injective h

@[ext] theorem ext (h : ∀ f, v f = w f) : v = w := coe_injective (funext h)

variables {u : point_derivation I y}

theorem hext (h1 : x = y) (h2 : ∀ f, v f = u f) : v == u :=
by { cases h1, rw heq_iff_eq, ext, exact h2 f }

end point_derivation

end

section

variables {I} {M} {X Y : vector_field_derivation I M} (f g : C∞(I, M; 𝕜)) (r : 𝕜)

namespace vector_field_derivation

instance : has_coe_to_fun (vector_field_derivation I M) := ⟨_, λ X, X.to_linear_map.to_fun⟩

instance has_coe_to_derivation :
  has_coe (vector_field_derivation I M) (derivation 𝕜 C∞(I, M; 𝕜) C∞(I, M; 𝕜)) :=
⟨to_derivation⟩

instance has_coe_to_linear_map :
  has_coe (vector_field_derivation I M) (C∞(I, M; 𝕜) →ₗ[𝕜] C∞(I, M; 𝕜)) :=
  ⟨λ X, X.to_linear_map⟩

@[simp] lemma to_fun_eq_coe : X.to_fun = ⇑X := rfl


@[simp, norm_cast]
lemma coe_linear_map (X : vector_field_derivation I M) :
  ⇑(X : C∞(I, M; 𝕜) →ₗ[𝕜] C∞(I, M; 𝕜)) = X := rfl

lemma coe_injective (h : ⇑X = Y) : X = Y :=
by { cases X, cases Y, congr', exact derivation.coe_injective h }

@[ext] theorem ext (h : ∀ f, X f = Y f) : X = Y :=
coe_injective $ funext h

variables (X Y)

@[simp] lemma map_add : X (f + g) = X f + X g := derivation.map_add _ _ _
@[simp] lemma map_zero : X 0 = 0 := derivation.map_zero _
@[simp] lemma map_smul : X (r • f) = r • X f := derivation.map_smul _ _ _
@[simp] lemma leibniz : X (f * g) = f • X g + g • X f := derivation.leibniz _ _ _
@[simp] lemma map_one_eq_zero : X 1 = 0 := derivation.map_one_eq_zero _
@[simp] lemma map_neg : X (-f) = -X f := derivation.map_neg _ _
@[simp] lemma map_sub : X (f - g) = X f - X g := derivation.map_sub _ _ _

instance : has_zero (vector_field_derivation I M) := ⟨⟨(0 : derivation 𝕜 C∞(I, M; 𝕜) C∞(I, M; 𝕜))⟩⟩
instance : inhabited (vector_field_derivation I M) := ⟨0⟩

instance : add_comm_group (vector_field_derivation I M) :=
{ add := λ X Y, ⟨X + Y⟩,
  add_assoc := λ X Y Z, ext $ λ a, add_assoc _ _ _,
  zero_add := λ X, ext $ λ a, zero_add _,
  add_zero := λ X, ext $ λ a, add_zero _,
  add_comm := λ X Y, ext $ λ a, add_comm _ _,
  neg := λ X, ⟨-X⟩,
  add_left_neg := λ X, ext $ λ a, add_left_neg _,
  ..vector_field_derivation.has_zero }

@[simp] lemma add_apply : (X + Y) f = X f + Y f := rfl
@[simp] lemma zero_apply : (0 : vector_field_derivation I M) f = 0 := rfl

instance : has_bracket (vector_field_derivation I M) :=
{ bracket := λ X Y, ⟨⁅X, Y⁆⟩ }

@[simp] lemma commutator_to_derivation_coe : ⁅X, Y⁆.to_derivation = ⁅X, Y⁆ := rfl

@[simp] lemma commutator_coe_derivation :
  ⇑⁅X, Y⁆ = (⁅X, Y⁆ : derivation 𝕜 C∞(I, M; 𝕜) C∞(I, M; 𝕜)) := rfl

@[simp] lemma commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f) :=
by rw [commutator_coe_derivation, derivation.commutator_apply]; refl

instance : lie_ring (vector_field_derivation I M) :=
{ add_lie := λ X Y Z, by { ext1 f, simp only [commutator_apply, add_apply, map_add], ring, },
  lie_add := λ X Y Z, by { ext1 f, simp only [commutator_apply, add_apply, map_add], ring },
  lie_self := λ X, by { ext1 f, simp only [commutator_apply, zero_apply, sub_self] },
  jacobi := λ X Y Z, by { ext1 f, simp only [commutator_apply, add_apply, map_sub,
    zero_apply], ring }, }

instance : has_scalar 𝕜 (vector_field_derivation I M) :=
{ smul := λ k X, ⟨k • X⟩ }

instance kmodule : module 𝕜 (vector_field_derivation I M) :=
semimodule.of_core $
{ mul_smul := λ r s X, ext $ λ b, mul_smul _ _ _,
  one_smul := λ X, ext $ λ b, one_smul 𝕜 _,
  smul_add := λ r X Y, ext $ λ b, smul_add _ _ _,
  add_smul := λ r s X, ext $ λ b, add_smul _ _ _,
  ..vector_field_derivation.has_scalar }

@[simp] lemma smul_apply : (r • X) f = r • X f := rfl

instance : lie_algebra 𝕜 (vector_field_derivation I M) :=
{ lie_smul := λ X Y Z, by { ext1 f, simp only [commutator_apply, smul_apply, map_smul, smul_sub] },
  ..vector_field_derivation.kmodule, }

def eval (X : vector_field_derivation I M) (x : M) : point_derivation I x :=
{ to_fun := λ f, (X f) x,
  map_add' := λ f g, by { rw map_add, refl },
  map_smul' := λ f g, by { rw [map_smul, algebra.id.smul_eq_mul], refl },
  leibniz' := λ h k, by { dsimp only [], rw [leibniz, algebra.id.smul_eq_mul], refl } }

@[simp] lemma eval_apply (x : M) : X.eval x f = (X f) x := rfl

@[simp] lemma eval_add (x : M) :
  (X + Y).eval x = X.eval x + Y.eval x :=
by ext f; simp only [derivation.add_apply, add_apply, eval_apply, smooth_map.add_apply]

/- to be moved -/
@[simp] lemma ring_commutator.apply {α : Type*} {R : Type*} [ring R] (f g : α → R) (a : α) :
  ⁅f, g⁆ a = ⁅f a, g a⁆ :=
by simp only [ring_commutator.commutator, pi.mul_apply, pi.sub_apply]

/- instance : has_coe_to_fun (vector_field_derivation I M) := ⟨_, λ X, eval X⟩ polymorphysm of coercions to functions is not possible? -/

end vector_field_derivation

variables {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

def fdifferential (f : C∞(I, M; I', M')) (x : M) (v : point_derivation I x) : (point_derivation I' (f x)) :=
{ to_fun := λ g, v (g.comp f),
  map_add' := λ g h, by { rw smooth_map.add_comp, sorry, sorry},
  map_smul' := λ k g, by { sorry },
  leibniz' := λ f g, by {dsimp only [], sorry}, } /-TODO: change it so that it is a linear map -/

localized "notation `fd` := fdifferential" in manifold

lemma apply_fdifferential (f : C∞(I, M; I', M')) (x : M) (v : point_derivation I x) (g : C∞(I', M'; 𝕜)) :
  fd f x v g = v (g.comp f) := rfl

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']

@[simp] lemma fdifferential_comp (g : C∞(I', M'; I'', M'')) (f : C∞(I, M; I', M')) (x : M) :
  (fd g (f x)) ∘ (fd f x) = fd (g.comp f) x :=
by { ext, simp only [apply_fdifferential], refl }

end
