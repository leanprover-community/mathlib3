/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.add_torsor
import analysis.normed_space.linear_isometry
import linear_algebra.affine_space.affine_subspace

/-!
# Affine isometries

In this file we define `affine_isometry 𝕜 P P₂` to be an affine isometric embedding of normed
add-torsors `P` into `P₂` over normed `𝕜`-spaces and `affine_isometry_equiv` to be an affine
isometric equivalence between `P` and `P₂`.

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `linear_isometry` and `affine_map` theories.

Since many elementary properties don't require `∥x∥ = 0 → x = 0` we initially set up the theory for
`semi_normed_add_torsor` and specialize to `normed_add_torsor` only when needed.

## Notation

We introduce the notation `P →ᵃⁱ[𝕜] P₂` for `affine_isometry 𝕜 P P₂`, and `P ≃ᵃⁱ[𝕜] P₂` for
`affine_isometry_equiv 𝕜 P P₂`.  In contrast with the notation `→ₗᵢ` for linear isometries, `≃ᵢ`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `→ᵃ` is an affine map, since `→ₐ` has been taken by
algebra-homomorphisms.)

-/
open function set

variables (𝕜 : Type*) {V V₁ V₂ V₃ V₄ : Type*} {P₁ : Type*} (P P₂ : Type*) {P₃ P₄ : Type*}
    [normed_field 𝕜]
  [semi_normed_group V] [normed_group V₁] [semi_normed_group V₂] [semi_normed_group V₃]
    [semi_normed_group V₄]
  [semi_normed_space 𝕜 V] [normed_space 𝕜 V₁] [semi_normed_space 𝕜 V₂] [semi_normed_space 𝕜 V₃]
    [semi_normed_space 𝕜 V₄]
  [pseudo_metric_space P] [metric_space P₁] [pseudo_metric_space P₂] [pseudo_metric_space P₃]
    [pseudo_metric_space P₄]
  [semi_normed_add_torsor V P] [normed_add_torsor V₁ P₁] [semi_normed_add_torsor V₂ P₂]
    [semi_normed_add_torsor V₃ P₃] [semi_normed_add_torsor V₄ P₄]

include V V₂

/-- An `𝕜`-affine isometric embedding of one normed add-torsor over a normed `𝕜`-space into
another. -/
structure affine_isometry extends P →ᵃ[𝕜] P₂ :=
(norm_map : ∀ x : V, ∥linear x∥ = ∥x∥)

omit V V₂
variables {𝕜 P P₂}

-- `→ᵃᵢ` would be more consistent with the linear isometry notation, but it is uglier
notation P ` →ᵃⁱ[`:25 𝕜:25 `] `:0 P₂:0 := affine_isometry 𝕜 P P₂

namespace affine_isometry
variables (f : P →ᵃⁱ[𝕜] P₂)

/-- The underlying linear map of an affine isometry is in fact a linear isometry. -/
protected def linear_isometry : V →ₗᵢ[𝕜] V₂ :=
{ norm_map' := f.norm_map,
  .. f.linear }

@[simp] lemma linear_eq_linear_isometry : f.linear = f.linear_isometry.to_linear_map :=
by { ext, refl }

include V V₂
instance : has_coe_to_fun (P →ᵃⁱ[𝕜] P₂) := ⟨_, λ f, f.to_fun⟩
omit V V₂

@[simp] lemma coe_to_affine_map : ⇑f.to_affine_map = f := rfl

include V V₂
lemma to_affine_map_injective : injective (to_affine_map : (P →ᵃⁱ[𝕜] P₂) → (P →ᵃ[𝕜] P₂))
| ⟨f, _⟩ ⟨g, _⟩ rfl := rfl

lemma coe_fn_injective : @injective (P →ᵃⁱ[𝕜] P₂) (P → P₂) coe_fn :=
affine_map.coe_fn_injective.comp to_affine_map_injective

@[ext] lemma ext {f g : P →ᵃⁱ[𝕜] P₂} (h : ∀ x, f x = g x) : f = g :=
coe_fn_injective $ funext h
omit V V₂

end affine_isometry

namespace linear_isometry
variables (f : V →ₗᵢ[𝕜] V₂)

/-- Reinterpret a linear isometry as an affine isometry. -/
def to_affine_isometry : V →ᵃⁱ[𝕜] V₂ :=
{ norm_map := f.norm_map,
  .. f.to_linear_map.to_affine_map }

@[simp] lemma coe_to_affine_isometry : ⇑(f.to_affine_isometry : V →ᵃⁱ[𝕜] V₂) = f := rfl

@[simp] lemma to_affine_isometry_linear_isometry : f.to_affine_isometry.linear_isometry = f :=
by { ext, refl }

-- somewhat arbitrary choice of simp direction
@[simp] lemma to_affine_isometry_to_affine_map :
  f.to_affine_isometry.to_affine_map = f.to_linear_map.to_affine_map :=
rfl

end linear_isometry

namespace affine_isometry

/-- We use `f₁` when we need the domain to be a `normed_space`. -/
variables (f : P →ᵃⁱ[𝕜] P₂) (f₁ : P₁ →ᵃⁱ[𝕜] P₂)

@[simp] lemma map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linear_isometry v +ᵥ f p :=
f.to_affine_map.map_vadd p v

@[simp] lemma map_vsub (p1 p2 : P) : f.linear_isometry (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
f.to_affine_map.linear_map_vsub p1 p2

@[simp] lemma dist_map (x y : P) : dist (f x) (f y) = dist x y :=
by rw [dist_eq_norm_vsub V₂, dist_eq_norm_vsub V, ← map_vsub, f.linear_isometry.norm_map]

@[simp] lemma nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by simp [nndist_dist]

@[simp] lemma edist_map (x y : P) : edist (f x) (f y) = edist x y := by simp [edist_dist]

protected lemma isometry : isometry f := f.edist_map

protected lemma injective : injective f₁ := f₁.isometry.injective

@[simp] lemma map_eq_iff {x y : P₁} : f₁ x = f₁ y ↔ x = y := f₁.injective.eq_iff

lemma map_ne {x y : P₁} (h : x ≠ y) : f₁ x ≠ f₁ y := f₁.injective.ne h

protected lemma lipschitz : lipschitz_with 1 f := f.isometry.lipschitz

protected lemma antilipschitz : antilipschitz_with 1 f := f.isometry.antilipschitz

@[continuity] protected lemma continuous : continuous f := f.isometry.continuous

lemma ediam_image (s : set P) : emetric.diam (f '' s) = emetric.diam s :=
f.isometry.ediam_image s

lemma ediam_range : emetric.diam (range f) = emetric.diam (univ : set P) :=
f.isometry.ediam_range

lemma diam_image (s : set P) : metric.diam (f '' s) = metric.diam s :=
f.isometry.diam_image s

lemma diam_range : metric.diam (range f) = metric.diam (univ : set P) :=
f.isometry.diam_range

@[simp] lemma comp_continuous_iff {α : Type*} [topological_space α] {g : α → P} :
  continuous (f ∘ g) ↔ continuous g :=
f.isometry.comp_continuous_iff

include V
/-- The identity affine isometry. -/
def id : P →ᵃⁱ[𝕜] P := ⟨affine_map.id 𝕜 P, λ x, rfl⟩

@[simp] lemma coe_id : ⇑(id : P →ᵃⁱ[𝕜] P) = id := rfl

@[simp] lemma id_apply (x : P) : (affine_isometry.id : P →ᵃⁱ[𝕜] P) x = x := rfl

@[simp] lemma id_to_affine_map : (id.to_affine_map : P →ᵃ[𝕜] P) = affine_map.id 𝕜 P := rfl

instance : inhabited (P →ᵃⁱ[𝕜] P) := ⟨id⟩

include V₂ V₃
/-- Composition of affine isometries. -/
def comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : P →ᵃⁱ[𝕜] P₃ :=
⟨g.to_affine_map.comp f.to_affine_map, λ x, (g.norm_map _).trans (f.norm_map _)⟩

@[simp] lemma coe_comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) :
  ⇑(g.comp f) = g ∘ f :=
rfl

omit V V₂ V₃

@[simp] lemma id_comp : (id : P₂ →ᵃⁱ[𝕜] P₂).comp f = f := ext $ λ x, rfl

@[simp] lemma comp_id : f.comp id = f := ext $ λ x, rfl

include V V₂ V₃ V₄
lemma comp_assoc (f : P₃ →ᵃⁱ[𝕜] P₄) (g : P₂ →ᵃⁱ[𝕜] P₃) (h : P →ᵃⁱ[𝕜] P₂) :
  (f.comp g).comp h = f.comp (g.comp h) :=
rfl
omit V₂ V₃ V₄

instance : monoid (P →ᵃⁱ[𝕜] P) :=
{ one := id,
  mul := comp,
  mul_assoc := comp_assoc,
  one_mul := id_comp,
  mul_one := comp_id }

@[simp] lemma coe_one : ⇑(1 : P →ᵃⁱ[𝕜] P) = id := rfl
@[simp] lemma coe_mul (f g : P →ᵃⁱ[𝕜] P) : ⇑(f * g) = f ∘ g := rfl

end affine_isometry

-- remark: by analogy with the `linear_isometry` file from which this is adapted, there should
-- follow here a section defining an "inclusion" affine isometry from `p : affine_subspace 𝕜 P`
-- into `P`; we omit this for now

variables (𝕜 P P₂)
include V V₂

/-- A affine isometric equivalence between two normed vector spaces. -/
structure affine_isometry_equiv extends P ≃ᵃ[𝕜] P₂ :=
(norm_map : ∀ x, ∥linear x∥ = ∥x∥)

variables {𝕜 P P₂}
omit V V₂

-- `≃ᵃᵢ` would be more consistent with the linear isometry equiv notation, but it is uglier
notation P ` ≃ᵃⁱ[`:25 𝕜:25 `] `:0 P₂:0 := affine_isometry_equiv 𝕜 P P₂

namespace affine_isometry_equiv

variables (e : P ≃ᵃⁱ[𝕜] P₂)

/-- The underlying linear equiv of an affine isometry equiv is in fact a linear isometry equiv. -/
protected def linear_isometry_equiv : V ≃ₗᵢ[𝕜] V₂ :=
{ norm_map' := e.norm_map,
  .. e.linear }

@[simp] lemma linear_eq_linear_isometry : e.linear = e.linear_isometry_equiv.to_linear_equiv :=
by { ext, refl }

include V V₂
instance : has_coe_to_fun (P ≃ᵃⁱ[𝕜] P₂) := ⟨_, λ f, f.to_fun⟩

@[simp] lemma coe_mk (e : P ≃ᵃ[𝕜] P₂) (he : ∀ x, ∥e.linear x∥ = ∥x∥) :
  ⇑(mk e he) = e :=
rfl

@[simp] lemma coe_to_affine_equiv (e : P ≃ᵃⁱ[𝕜] P₂) : ⇑e.to_affine_equiv = e := rfl

lemma to_affine_equiv_injective : injective (to_affine_equiv : (P ≃ᵃⁱ[𝕜] P₂) → (P ≃ᵃ[𝕜] P₂))
| ⟨e, _⟩ ⟨_, _⟩ rfl := rfl

@[ext] lemma ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : ∀ x, e x = e' x) : e = e' :=
to_affine_equiv_injective $ affine_equiv.ext h
omit V V₂

/-- Reinterpret a `affine_isometry_equiv` as a `affine_isometry`. -/
def to_affine_isometry : P →ᵃⁱ[𝕜] P₂ := ⟨e.1.to_affine_map, e.2⟩

@[simp] lemma coe_to_affine_isometry : ⇑e.to_affine_isometry = e := rfl

/-- Construct an affine isometry equivalence by verifying the relation between the map and its
linear part at one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear isometry
equivalence `e' : V₁ ≃ᵢₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
  P₁ ≃ᵃⁱ[𝕜] P₂ :=
{ norm_map := e'.norm_map,
  .. affine_equiv.mk' e e'.to_linear_equiv p h }

@[simp] lemma coe_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) : ⇑(mk' e e' p h) = e := rfl
@[simp] lemma linear_isometry_equiv_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) :
  (mk' e e' p h).linear_isometry_equiv = e' := by { ext, refl }

end affine_isometry_equiv

namespace linear_isometry_equiv
variables (e : V ≃ₗᵢ[𝕜] V₂)

/-- Reinterpret a linear isometry equiv as an affine isometry equiv. -/
def to_affine_isometry_equiv  : V ≃ᵃⁱ[𝕜] V₂ :=
{ norm_map := e.norm_map,
  .. e.to_linear_equiv.to_affine_equiv }

@[simp] lemma coe_to_affine_isometry_equiv : ⇑(e.to_affine_isometry_equiv : V ≃ᵃⁱ[𝕜] V₂) = e := rfl

@[simp] lemma to_affine_isometry_equiv_linear_isometry_equiv :
  e.to_affine_isometry_equiv.linear_isometry_equiv = e :=
by { ext, refl }

-- somewhat arbitrary choice of simp direction
@[simp] lemma to_affine_isometry_equiv_to_affine_equiv :
  e.to_affine_isometry_equiv.to_affine_equiv = e.to_linear_equiv.to_affine_equiv :=
rfl

-- somewhat arbitrary choice of simp direction
@[simp] lemma to_affine_isometry_equiv_to_affine_isometry :
  e.to_affine_isometry_equiv.to_affine_isometry = e.to_linear_isometry.to_affine_isometry :=
rfl

end linear_isometry_equiv

namespace affine_isometry_equiv
variables (e : P ≃ᵃⁱ[𝕜] P₂)

protected lemma isometry : isometry e := e.to_affine_isometry.isometry

/-- Reinterpret a `affine_isometry_equiv` as an `isometric`. -/
def to_isometric : P ≃ᵢ P₂ := ⟨e.to_affine_equiv.to_equiv, e.isometry⟩

@[simp] lemma coe_to_isometric : ⇑e.to_isometric = e := rfl

include V V₂
lemma range_eq_univ (e : P ≃ᵃⁱ[𝕜] P₂) : set.range e = set.univ :=
by { rw ← coe_to_isometric, exact isometric.range_eq_univ _, }
omit V V₂

/-- Reinterpret a `affine_isometry_equiv` as an `homeomorph`. -/
def to_homeomorph : P ≃ₜ P₂ := e.to_isometric.to_homeomorph

@[simp] lemma coe_to_homeomorph : ⇑e.to_homeomorph = e := rfl

protected lemma continuous : continuous e := e.isometry.continuous
protected lemma continuous_at {x} : continuous_at e x := e.continuous.continuous_at
protected lemma continuous_on {s} : continuous_on e s := e.continuous.continuous_on

protected lemma continuous_within_at {s x} : continuous_within_at e s x :=
e.continuous.continuous_within_at

variables (𝕜 P)
include V

/-- Identity map as a `affine_isometry_equiv`. -/
def refl : P ≃ᵃⁱ[𝕜] P := ⟨affine_equiv.refl 𝕜 P, λ x, rfl⟩

variables {𝕜 P}

instance : inhabited (P ≃ᵃⁱ[𝕜] P) := ⟨refl 𝕜 P⟩

@[simp] lemma coe_refl : ⇑(refl 𝕜 P) = id := rfl
@[simp] lemma to_affine_equiv_refl : (refl 𝕜 P).to_affine_equiv = affine_equiv.refl 𝕜 P := rfl
@[simp] lemma to_isometric_refl : (refl 𝕜 P).to_isometric = isometric.refl P := rfl
@[simp] lemma to_homeomorph_refl : (refl 𝕜 P).to_homeomorph = homeomorph.refl P := rfl
omit V

/-- The inverse `affine_isometry_equiv`. -/
def symm : P₂ ≃ᵃⁱ[𝕜] P :=
{ norm_map := e.linear_isometry_equiv.symm.norm_map,
  .. e.to_affine_equiv.symm }

@[simp] lemma apply_symm_apply (x : P₂) : e (e.symm x) = x := e.to_affine_equiv.apply_symm_apply x
@[simp] lemma symm_apply_apply (x : P) : e.symm (e x) = x := e.to_affine_equiv.symm_apply_apply x
@[simp] lemma symm_symm : e.symm.symm = e := ext $ λ x, rfl

@[simp] lemma to_affine_equiv_symm : e.to_affine_equiv.symm = e.symm.to_affine_equiv := rfl
@[simp] lemma to_isometric_symm : e.to_isometric.symm = e.symm.to_isometric := rfl
@[simp] lemma to_homeomorph_symm : e.to_homeomorph.symm = e.symm.to_homeomorph := rfl

include V₃
/-- Composition of `affine_isometry_equiv`s as a `affine_isometry_equiv`. -/
def trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃ :=
⟨e.to_affine_equiv.trans e'.to_affine_equiv, λ x, (e'.norm_map _).trans (e.norm_map _)⟩

include V V₂
@[simp] lemma coe_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl
omit V V₂ V₃

@[simp] lemma trans_refl : e.trans (refl 𝕜 P₂) = e := ext $ λ x, rfl
@[simp] lemma refl_trans : (refl 𝕜 P).trans e = e := ext $ λ x, rfl
@[simp] lemma trans_symm : e.trans e.symm = refl 𝕜 P := ext e.symm_apply_apply
@[simp] lemma symm_trans : e.symm.trans e = refl 𝕜 P₂ := ext e.apply_symm_apply

include V V₂ V₃
@[simp] lemma coe_symm_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) :
  ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
rfl

include V₄
lemma trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄) :
  ePP₂.trans (eP₂G.trans eGG') = (ePP₂.trans eP₂G).trans eGG' :=
rfl
omit V₂ V₃ V₄

/-- The group of affine isometries of a `normed_add_torsor`, `P`. -/
instance : group (P ≃ᵃⁱ[𝕜] P) :=
{ mul := λ e₁ e₂, e₂.trans e₁,
  one := refl _ _,
  inv := symm,
  one_mul := trans_refl,
  mul_one := refl_trans,
  mul_assoc := λ _ _ _, trans_assoc _ _ _,
  mul_left_inv := trans_symm }

@[simp] lemma coe_one : ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id := rfl
@[simp] lemma coe_mul (e e' : P ≃ᵃⁱ[𝕜] P) : ⇑(e * e') = e ∘ e' := rfl
@[simp] lemma coe_inv (e : P ≃ᵃⁱ[𝕜] P) : ⇑(e⁻¹) = e.symm := rfl

omit V

@[simp] lemma map_vadd (p : P) (v : V) : e (v +ᵥ p) = e.linear_isometry_equiv v +ᵥ e p :=
e.to_affine_isometry.map_vadd p v

@[simp] lemma map_vsub (p1 p2 : P) : e.linear_isometry_equiv (p1 -ᵥ p2) = e p1 -ᵥ e p2 :=
e.to_affine_isometry.map_vsub p1 p2

@[simp] lemma dist_map (x y : P) : dist (e x) (e y) = dist x y :=
e.to_affine_isometry.dist_map x y

@[simp] lemma edist_map (x y : P) : edist (e x) (e y) = edist x y :=
e.to_affine_isometry.edist_map x y

protected lemma bijective : bijective e := e.1.bijective
protected lemma injective : injective e := e.1.injective
protected lemma surjective : surjective e := e.1.surjective

@[simp] lemma map_eq_iff {x y : P} : e x = e y ↔ x = y := e.injective.eq_iff

lemma map_ne {x y : P} (h : x ≠ y) : e x ≠ e y := e.injective.ne h

protected lemma lipschitz : lipschitz_with 1 e := e.isometry.lipschitz

protected lemma antilipschitz : antilipschitz_with 1 e := e.isometry.antilipschitz

@[simp] lemma ediam_image (s : set P) : emetric.diam (e '' s) = emetric.diam s :=
e.isometry.ediam_image s

@[simp] lemma diam_image (s : set P) : metric.diam (e '' s) = metric.diam s :=
e.isometry.diam_image s

variables {α : Type*} [topological_space α]

@[simp] lemma comp_continuous_on_iff {f : α → P} {s : set α} :
  continuous_on (e ∘ f) s ↔ continuous_on f s :=
e.isometry.comp_continuous_on_iff

@[simp] lemma comp_continuous_iff {f : α → P} :
  continuous (e ∘ f) ↔ continuous f :=
e.isometry.comp_continuous_iff

section constructions

variables (𝕜)
/-- The map `v ↦ v +ᵥ p` as an affine isometric equivalence between `V` and `P`. -/
def vadd_const (p : P) : V ≃ᵃⁱ[𝕜] P :=
{ norm_map := λ x, rfl,
  .. affine_equiv.vadd_const 𝕜 p }
variables {𝕜}

include V
@[simp] lemma coe_vadd_const (p : P) : ⇑(vadd_const 𝕜 p) = λ v, v +ᵥ p := rfl

@[simp] lemma coe_vadd_const_symm (p : P) : ⇑(vadd_const 𝕜 p).symm = λ p', p' -ᵥ p :=
rfl

@[simp] lemma vadd_const_to_affine_equiv (p : P) :
  (vadd_const 𝕜 p).to_affine_equiv = affine_equiv.vadd_const 𝕜 p :=
rfl
omit V

variables (𝕜)
/-- `p' ↦ p -ᵥ p'` as an affine isometric equivalence. -/
def const_vsub (p : P) : P ≃ᵃⁱ[𝕜] V :=
{ norm_map := norm_neg,
  .. affine_equiv.const_vsub 𝕜 p }
variables {𝕜}

include V
@[simp] lemma coe_const_vsub (p : P) : ⇑(const_vsub 𝕜 p) = (-ᵥ) p := rfl

@[simp] lemma symm_const_vsub (p : P) :
  (const_vsub 𝕜 p).symm
  = (linear_isometry_equiv.neg 𝕜).to_affine_isometry_equiv.trans (vadd_const 𝕜 p) :=
by { ext, refl }
omit V

variables (𝕜 P)
/-- Translation by `v` (that is, the map `p ↦ v +ᵥ p`) as an affine isometric automorphism of `P`.
-/
def const_vadd (v : V) : P ≃ᵃⁱ[𝕜] P :=
{ norm_map := λ x, rfl,
  .. affine_equiv.const_vadd 𝕜 P v }
variables {𝕜 P}

@[simp] lemma coe_const_vadd (v : V) : ⇑(const_vadd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (+ᵥ) v := rfl

@[simp] lemma const_vadd_zero : const_vadd 𝕜 P (0:V) = refl 𝕜 P := ext $ zero_vadd V

include 𝕜 V
/-- The map `g` from `V` to `V₂` corresponding to a map `f` from `P` to `P₂`, at a base point `p`,
is an isometry if `f` is one. -/
lemma vadd_vsub {f : P → P₂} (hf : isometry f) {p : P} {g : V → V₂}
  (hg : ∀ v, g v = f (v +ᵥ p) -ᵥ f p) : isometry g :=
begin
  convert (vadd_const 𝕜 (f p)).symm.isometry.comp (hf.comp (vadd_const 𝕜 p).isometry),
  exact funext hg
end
omit 𝕜

variables (𝕜)
/-- Point reflection in `x` as an affine isometric automorphism. -/
def point_reflection (x : P) : P ≃ᵃⁱ[𝕜] P := (const_vsub 𝕜 x).trans (vadd_const 𝕜 x)
variables {𝕜}

lemma point_reflection_apply (x y : P) : (point_reflection 𝕜 x) y = x -ᵥ y +ᵥ x := rfl

@[simp] lemma point_reflection_to_affine_equiv (x : P) :
  (point_reflection 𝕜 x).to_affine_equiv = affine_equiv.point_reflection 𝕜 x := rfl

@[simp] lemma point_reflection_self (x : P) : point_reflection 𝕜 x x = x :=
affine_equiv.point_reflection_self 𝕜 x

lemma point_reflection_involutive (x : P) : function.involutive (point_reflection 𝕜 x) :=
equiv.point_reflection_involutive x

@[simp] lemma point_reflection_symm (x : P) : (point_reflection 𝕜 x).symm = point_reflection 𝕜 x :=
to_affine_equiv_injective $ affine_equiv.point_reflection_symm 𝕜 x

@[simp] lemma dist_point_reflection_fixed (x y : P) :
  dist (point_reflection 𝕜 x y) x = dist y x :=
by rw [← (point_reflection 𝕜 x).dist_map y x, point_reflection_self]

lemma dist_point_reflection_self' (x y : P) :
  dist (point_reflection 𝕜 x y) y = ∥bit0 (x -ᵥ y)∥ :=
by rw [point_reflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, bit0]

lemma dist_point_reflection_self (x y : P) :
  dist (point_reflection 𝕜 x y) y = ∥(2:𝕜)∥ * dist x y :=
by rw [dist_point_reflection_self', ← two_smul' 𝕜 (x -ᵥ y), norm_smul, ← dist_eq_norm_vsub V]

lemma point_reflection_fixed_iff [invertible (2:𝕜)] {x y : P} :
  point_reflection 𝕜 x y = y ↔ y = x :=
affine_equiv.point_reflection_fixed_iff_of_module 𝕜

variables [semi_normed_space ℝ V]

lemma dist_point_reflection_self_real (x y : P) :
  dist (point_reflection ℝ x y) y = 2 * dist x y :=
by { rw [dist_point_reflection_self, real.norm_two] }

@[simp] lemma point_reflection_midpoint_left (x y : P) :
  point_reflection ℝ (midpoint ℝ x y) x = y :=
affine_equiv.point_reflection_midpoint_left x y

@[simp] lemma point_reflection_midpoint_right (x y : P) :
  point_reflection ℝ (midpoint ℝ x y) y = x :=
affine_equiv.point_reflection_midpoint_right x y

end constructions

end affine_isometry_equiv

namespace affine_isometry

open finite_dimensional affine_map

variables [finite_dimensional 𝕜 V₁] [finite_dimensional 𝕜 V₂]

/-- A affine isometry between finite dimensional spaces of equal dimension can be upgraded
    to an affine isometry equivalence. -/
noncomputable def to_affine_isometry_equiv [inhabited P₁]
  (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : P₁ ≃ᵃⁱ[𝕜] P₂ :=
affine_isometry_equiv.mk' li (li.linear_isometry.to_linear_isometry_equiv h) (arbitrary P₁)
  (λ p, by simp)

@[simp] lemma coe_to_affine_isometry_equiv [inhabited P₁]
  (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
  (li.to_affine_isometry_equiv h : P₁ → P₂) = li := rfl

@[simp] lemma to_affine_isometry_equiv_apply [inhabited P₁]
  (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) :
  (li.to_affine_isometry_equiv h) x = li x := rfl

end affine_isometry

include V V₂
/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
lemma affine_map.continuous_linear_iff {f : P →ᵃ[𝕜] P₂} :
  continuous f.linear ↔ continuous f :=
begin
  inhabit P,
  have : (f.linear : V → V₂) =
    (affine_isometry_equiv.vadd_const 𝕜 $ f $ default P).to_homeomorph.symm ∘ f ∘
      (affine_isometry_equiv.vadd_const 𝕜 $ default P).to_homeomorph,
  { ext v, simp },
  rw this,
  simp only [homeomorph.comp_continuous_iff, homeomorph.comp_continuous_iff'],
end
