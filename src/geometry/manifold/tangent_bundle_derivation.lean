import geometry.manifold.algebra.smooth_functions
import ring_theory.derivation
import geometry.manifold.temporary_to_be_removed

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

open_locale manifold

def module_point_derivation (x : M) : module C∞(I, M; 𝕜) 𝕜 :=
{ smul := λ f k, f x * k,
  one_smul := λ k, one_mul k,
  mul_smul := λ f g k, mul_assoc _ _ _,
  smul_add := λ f g k, mul_add _ _ _,
  smul_zero := λ f, mul_zero _,
  add_smul := λ f g k, add_mul _ _ _,
  zero_smul := λ f, zero_mul _ }

def compatible_semimodule_tangent_space (x : M) :
  @compatible_semimodule 𝕜 C∞(I, M; 𝕜) _ _ _ 𝕜 _ (module_point_derivation I M x) _ :=
{ compatible_smul := λ h k, rfl, }

@[reducible] def point_derivation (x : M) :=
  @derivation 𝕜 C∞(I, M; 𝕜) _ _ _ 𝕜 _ (module_point_derivation I M x) _
  (compatible_semimodule_tangent_space I M x)

def tangent_bundle_derivation := Σ x : M, point_derivation I M x

/-instance : has_add (tangent_bundle_derivation I M) :=
{ add := λ v w, sigma.mk v.1 (v.2 + w.2) }-/

variables {I M}

def tangent_space_inclusion {x : M} (v : point_derivation I M x) : tangent_bundle_derivation I M :=
sigma.mk x v

/- Something weird is happening. Does not find the instance of smooth manifolds with corners.
Moreover if I define it as a reducible def .eval does not work... It also takes very long time to
typecheck -/

section

namespace point_derivation

variables {I} {M} {x y : M} {v w : point_derivation I M x} (f g : C∞(I, M; 𝕜)) (r : 𝕜)

lemma coe_injective (h : ⇑v = w) : v = w :=
@derivation.coe_injective 𝕜 _ C∞(I, M; 𝕜) _ _ 𝕜 _ (module_point_derivation I M x) _
(compatible_semimodule_tangent_space I M x) v w h

@[ext] theorem ext (h : ∀ f, v f = w f) : v = w :=
coe_injective $ funext h

variables {u : point_derivation I M y}

theorem hext (h1 : x = y) (h2 : ∀ f, v f = u f) : v == u :=
begin
  cases h1,
  rw heq_iff_eq at *,
  ext,
  exact h2 f,
end

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

def eval (X : vector_field_derivation I M) (x : M) : point_derivation I M x :=
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

def fdifferential (f : C∞(I, M; I', M')) (x : M) (v : point_derivation I M x) : (point_derivation I' M' (f x)) :=
{ to_fun := λ g, v (g.comp f),
  map_add' := λ g h, by { rw smooth_map.add_comp, },
  map_smul' := λ k g, by { rw smooth_map.smul_comp, },
  leibniz' := λ f g, by {dsimp only [], sorry}, } /-TODO: change it so that it is a linear map -/

localized "notation `fd` := fdifferential" in manifold

lemma apply_fdifferential (f : C∞(I, M; I', M')) (x : M) (v : point_derivation I M x) (g : C∞(I', M'; 𝕜)) :
  fd f x v g = v (g.comp f) := rfl

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']

@[simp] lemma fdifferential_comp (g : C∞(I', M'; I'', M'')) (f : C∞(I, M; I', M')) (x : M) :
  (fd g (f x)) ∘ (fd f x) = fd (g.comp f) x :=
by { ext, simp only [apply_fdifferential], refl }

end
