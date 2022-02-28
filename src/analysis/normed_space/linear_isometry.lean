/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis, Heather Macbeth
-/
import analysis.normed.group.basic
import topology.algebra.module.basic
import linear_algebra.basis

/-!
# (Semi-)linear isometries

In this file we define `linear_isometry σ₁₂ E E₂` (notation: `E →ₛₗᵢ[σ₁₂] E₂`) to be a semilinear
isometric embedding of `E` into `E₂` and `linear_isometry_equiv` (notation: `E ≃ₛₗᵢ[σ₁₂] E₂`) to be
a semilinear isometric equivalence between `E` and `E₂`.  The notation for the associated purely
linear concepts is `E →ₗᵢ[R] E₂`, `E ≃ₗᵢ[R] E₂`, and `E →ₗᵢ⋆[R] E₂`, `E ≃ₗᵢ⋆[R] E₂` for
the star-linear versions.

We also prove some trivial lemmas and provide convenience constructors.

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory for `semi_normed_group` and we specialize to `normed_group` when needed.
-/
open function set

variables {R R₂ R₃ R₄ E E₂ E₃ E₄ F : Type*} [semiring R] [semiring R₂] [semiring R₃] [semiring R₄]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R} {σ₁₄ : R →+* R₄}
  {σ₄₁ : R₄ →+* R} {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₄₂ : R₄ →+* R₂}
  {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃}
  [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  [ring_hom_inv_pair σ₁₃ σ₃₁] [ring_hom_inv_pair σ₃₁ σ₁₃]
  [ring_hom_inv_pair σ₂₃ σ₃₂] [ring_hom_inv_pair σ₃₂ σ₂₃]
  [ring_hom_inv_pair σ₁₄ σ₄₁] [ring_hom_inv_pair σ₄₁ σ₁₄]
  [ring_hom_inv_pair σ₂₄ σ₄₂] [ring_hom_inv_pair σ₄₂ σ₂₄]
  [ring_hom_inv_pair σ₃₄ σ₄₃] [ring_hom_inv_pair σ₄₃ σ₃₄]
  [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [ring_hom_comp_triple σ₁₂ σ₂₄ σ₁₄]
  [ring_hom_comp_triple σ₂₃ σ₃₄ σ₂₄] [ring_hom_comp_triple σ₁₃ σ₃₄ σ₁₄]
  [ring_hom_comp_triple σ₃₂ σ₂₁ σ₃₁] [ring_hom_comp_triple σ₄₂ σ₂₁ σ₄₁]
  [ring_hom_comp_triple σ₄₃ σ₃₂ σ₄₂] [ring_hom_comp_triple σ₄₃ σ₃₁ σ₄₁]
  [semi_normed_group E] [semi_normed_group E₂] [semi_normed_group E₃] [semi_normed_group E₄]
  [module R E] [module R₂ E₂] [module R₃ E₃] [module R₄ E₄]
  [normed_group F] [module R F]

/-- A `σ₁₂`-semilinear isometric embedding of a normed `R`-module into an `R₂`-module. -/
structure linear_isometry (σ₁₂ : R →+* R₂) (E E₂ : Type*) [semi_normed_group E]
  [semi_normed_group E₂] [module R E] [module R₂ E₂] extends E →ₛₗ[σ₁₂] E₂ :=
(norm_map' : ∀ x, ∥to_linear_map x∥ = ∥x∥)

notation E ` →ₛₗᵢ[`:25 σ₁₂:25 `] `:0 E₂:0 := linear_isometry σ₁₂ E E₂
notation E ` →ₗᵢ[`:25 R:25 `] `:0 E₂:0 := linear_isometry (ring_hom.id R) E E₂
notation E ` →ₗᵢ⋆[`:25 R:25 `] `:0 E₂:0 := linear_isometry (star_ring_end R) E E₂

namespace linear_isometry

/-- We use `f₁` when we need the domain to be a `normed_space`. -/
variables (f : E →ₛₗᵢ[σ₁₂] E₂) (f₁ : F →ₛₗᵢ[σ₁₂] E₂)

lemma to_linear_map_injective : injective (to_linear_map : (E →ₛₗᵢ[σ₁₂] E₂) → (E →ₛₗ[σ₁₂] E₂))
| ⟨f, _⟩ ⟨g, _⟩ rfl := rfl

@[simp] lemma to_linear_map_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} :
  f.to_linear_map = g.to_linear_map ↔ f = g := to_linear_map_injective.eq_iff

instance : add_monoid_hom_class (E →ₛₗᵢ[σ₁₂] E₂) E E₂ :=
{ coe := λ e, e.to_fun,
  coe_injective' := λ f g h, to_linear_map_injective (fun_like.coe_injective h),
  map_add := λ f, map_add f.to_linear_map,
  map_zero := λ f, map_zero f.to_linear_map }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly.
-/
instance : has_coe_to_fun (E →ₛₗᵢ[σ₁₂] E₂) (λ _, E → E₂) := ⟨λ f, f.to_fun⟩

@[simp] lemma coe_to_linear_map : ⇑f.to_linear_map = f := rfl

lemma coe_injective : @injective (E →ₛₗᵢ[σ₁₂] E₂) (E → E₂) coe_fn :=
fun_like.coe_injective

@[ext] lemma ext {f g : E →ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

protected lemma congr_arg {f : E →ₛₗᵢ[σ₁₂] E₂} : Π {x x' : E}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : E →ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E) : f x = g x := h ▸ rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_linear_map.map_zero

@[simp] lemma map_add (x y : E) : f (x + y) = f x + f y := f.to_linear_map.map_add x y

@[simp] lemma map_neg (x : E) : f (- x) = - f x := f.to_linear_map.map_neg x

@[simp] lemma map_sub (x y : E) : f (x - y) = f x - f y := f.to_linear_map.map_sub x y

@[simp] lemma map_smulₛₗ (c : R) (x : E) : f (c • x) = σ₁₂ c • f x := f.to_linear_map.map_smulₛₗ c x

@[simp] lemma map_smul [module R E₂] (f : E →ₗᵢ[R] E₂) (c : R) (x : E) : f (c • x) = c • f x :=
f.to_linear_map.map_smul c x

@[simp] lemma norm_map (x : E) : ∥f x∥ = ∥x∥ := f.norm_map' x

@[simp] lemma nnnorm_map (x : E) : nnnorm (f x) = nnnorm x := nnreal.eq $ f.norm_map x

protected lemma isometry : isometry f :=
f.to_linear_map.to_add_monoid_hom.isometry_of_norm f.norm_map

@[simp] lemma is_complete_image_iff {s : set E} : is_complete (f '' s) ↔ is_complete s :=
is_complete_image_iff f.isometry.uniform_inducing

lemma is_complete_map_iff [ring_hom_surjective σ₁₂] {p : submodule R E} :
  is_complete (p.map f.to_linear_map : set E₂) ↔ is_complete (p : set E) :=
f.is_complete_image_iff

instance complete_space_map [ring_hom_surjective σ₁₂] (p : submodule R E) [complete_space p] :
  complete_space (p.map f.to_linear_map) :=
(f.is_complete_map_iff.2 $ complete_space_coe_iff_is_complete.1 ‹_›).complete_space_coe

@[simp] lemma dist_map (x y : E) : dist (f x) (f y) = dist x y := f.isometry.dist_eq x y
@[simp] lemma edist_map (x y : E) : edist (f x) (f y) = edist x y := f.isometry.edist_eq x y

protected lemma injective : injective f₁ := f₁.isometry.injective

@[simp] lemma map_eq_iff {x y : F} : f₁ x = f₁ y ↔ x = y := f₁.injective.eq_iff

lemma map_ne {x y : F} (h : x ≠ y) : f₁ x ≠ f₁ y := f₁.injective.ne h

protected lemma lipschitz : lipschitz_with 1 f := f.isometry.lipschitz

protected lemma antilipschitz : antilipschitz_with 1 f := f.isometry.antilipschitz

@[continuity] protected lemma continuous : continuous f := f.isometry.continuous

lemma ediam_image (s : set E) : emetric.diam (f '' s) = emetric.diam s :=
f.isometry.ediam_image s

lemma ediam_range : emetric.diam (range f) = emetric.diam (univ : set E) :=
f.isometry.ediam_range

lemma diam_image (s : set E) : metric.diam (f '' s) = metric.diam s :=
f.isometry.diam_image s

lemma diam_range : metric.diam (range f) = metric.diam (univ : set E) :=
f.isometry.diam_range

/-- Interpret a linear isometry as a continuous linear map. -/
def to_continuous_linear_map : E →SL[σ₁₂] E₂ := ⟨f.to_linear_map, f.continuous⟩

lemma to_continuous_linear_map_injective :
  function.injective (to_continuous_linear_map : _ → E →SL[σ₁₂] E₂) :=
λ x y h, coe_injective (congr_arg _ h : ⇑x.to_continuous_linear_map = _)

@[simp] lemma to_continuous_linear_map_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} :
  f.to_continuous_linear_map = g.to_continuous_linear_map ↔ f = g :=
to_continuous_linear_map_injective.eq_iff

@[simp] lemma coe_to_continuous_linear_map : ⇑f.to_continuous_linear_map = f := rfl

@[simp] lemma comp_continuous_iff {α : Type*} [topological_space α] {g : α → E} :
  continuous (f ∘ g) ↔ continuous g :=
f.isometry.comp_continuous_iff

/-- The identity linear isometry. -/
def id : E →ₗᵢ[R] E := ⟨linear_map.id, λ x, rfl⟩

@[simp] lemma coe_id : ((id : E →ₗᵢ[R] E) : E → E) = _root_.id := rfl

@[simp] lemma id_apply (x : E) : (id : E →ₗᵢ[R] E) x = x := rfl

@[simp] lemma id_to_linear_map : (id.to_linear_map : E →ₗ[R] E) = linear_map.id := rfl

instance : inhabited (E →ₗᵢ[R] E) := ⟨id⟩

/-- Composition of linear isometries. -/
def comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : E →ₛₗᵢ[σ₁₃] E₃ :=
⟨g.to_linear_map.comp f.to_linear_map, λ x, (g.norm_map _).trans (f.norm_map _)⟩

include σ₁₃
@[simp] lemma coe_comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) :
  ⇑(g.comp f) = g ∘ f :=
rfl
omit σ₁₃

@[simp] lemma id_comp : (id : E₂ →ₗᵢ[R₂] E₂).comp f = f := ext $ λ x, rfl

@[simp] lemma comp_id : f.comp id = f := ext $ λ x, rfl

include σ₁₃ σ₂₄ σ₁₄
lemma comp_assoc (f : E₃ →ₛₗᵢ[σ₃₄] E₄) (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (h : E →ₛₗᵢ[σ₁₂] E₂) :
  (f.comp g).comp h = f.comp (g.comp h) :=
rfl
omit σ₁₃ σ₂₄ σ₁₄

instance : monoid (E →ₗᵢ[R] E) :=
{ one := id,
  mul := comp,
  mul_assoc := comp_assoc,
  one_mul := id_comp,
  mul_one := comp_id }

@[simp] lemma coe_one : ((1 : E →ₗᵢ[R] E) : E → E) = _root_.id := rfl
@[simp] lemma coe_mul (f g : E →ₗᵢ[R] E) : ⇑(f * g) = f ∘ g := rfl

lemma one_def : (1 : E →ₗᵢ[R] E) = id := rfl
lemma mul_def (f g : E →ₗᵢ[R] E) : (f * g : E →ₗᵢ[R] E) = f.comp g := rfl

end linear_isometry

/-- Construct a `linear_isometry` from a `linear_map` satisfying `isometry`. -/
def linear_map.to_linear_isometry (f : E →ₛₗ[σ₁₂] E₂) (hf : isometry f) : E →ₛₗᵢ[σ₁₂] E₂ :=
{ norm_map' := by { simp_rw [←dist_zero_right, ←f.map_zero], exact λ x, hf.dist_eq x _ },
  .. f }

namespace submodule

variables {R' : Type*} [ring R'] [module R' E] (p : submodule R' E)

/-- `submodule.subtype` as a `linear_isometry`. -/
def subtypeₗᵢ : p →ₗᵢ[R'] E := ⟨p.subtype, λ x, rfl⟩

@[simp] lemma coe_subtypeₗᵢ : ⇑p.subtypeₗᵢ = p.subtype := rfl

@[simp] lemma subtypeₗᵢ_to_linear_map : p.subtypeₗᵢ.to_linear_map = p.subtype := rfl

/-- `submodule.subtype` as a `continuous_linear_map`. -/
def subtypeL : p →L[R'] E := p.subtypeₗᵢ.to_continuous_linear_map

@[simp] lemma coe_subtypeL : (p.subtypeL : p →ₗ[R'] E) = p.subtype := rfl

@[simp] lemma coe_subtypeL' : ⇑p.subtypeL = p.subtype := rfl

@[simp] lemma range_subtypeL : p.subtypeL.range = p :=
range_subtype _

@[simp] lemma ker_subtypeL : p.subtypeL.ker = ⊥ :=
ker_subtype _

end submodule

/-- A semilinear isometric equivalence between two normed vector spaces. -/
structure linear_isometry_equiv (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [ring_hom_inv_pair σ₁₂ σ₂₁]
  [ring_hom_inv_pair σ₂₁ σ₁₂] (E E₂ : Type*) [semi_normed_group E] [semi_normed_group E₂]
  [module R E] [module R₂ E₂] extends E ≃ₛₗ[σ₁₂] E₂ :=
(norm_map' : ∀ x, ∥to_linear_equiv x∥ = ∥x∥)

notation E ` ≃ₛₗᵢ[`:25 σ₁₂:25 `] `:0 E₂:0 := linear_isometry_equiv σ₁₂ E E₂
notation E ` ≃ₗᵢ[`:25 R:25 `] `:0 E₂:0 := linear_isometry_equiv (ring_hom.id R) E E₂
notation E ` ≃ₗᵢ⋆[`:25 R:25 `] `:0 E₂:0 :=
  linear_isometry_equiv (star_ring_end R) E E₂

namespace linear_isometry_equiv

variables (e : E ≃ₛₗᵢ[σ₁₂] E₂)

include σ₂₁

lemma to_linear_equiv_injective : injective (to_linear_equiv : (E ≃ₛₗᵢ[σ₁₂] E₂) → (E ≃ₛₗ[σ₁₂] E₂))
| ⟨e, _⟩ ⟨_, _⟩ rfl := rfl

@[simp] lemma to_linear_equiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
  f.to_linear_equiv = g.to_linear_equiv ↔ f = g :=
to_linear_equiv_injective.eq_iff

instance : add_monoid_hom_class (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ :=
{ coe := λ e, e.to_fun,
  coe_injective' := λ f g h, to_linear_equiv_injective (fun_like.coe_injective h),
  map_add := λ f, map_add f.to_linear_equiv,
  map_zero := λ f, map_zero f.to_linear_equiv }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly.
-/
instance : has_coe_to_fun (E ≃ₛₗᵢ[σ₁₂] E₂) (λ _, E → E₂) := ⟨λ f, f.to_fun⟩

lemma coe_injective : @function.injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E → E₂) coe_fn :=
fun_like.coe_injective

@[simp] lemma coe_mk (e : E ≃ₛₗ[σ₁₂] E₂) (he : ∀ x, ∥e x∥ = ∥x∥) :
  ⇑(mk e he) = e :=
rfl

@[simp] lemma coe_to_linear_equiv (e : E ≃ₛₗᵢ[σ₁₂] E₂) : ⇑e.to_linear_equiv = e := rfl

@[ext] lemma ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, e x = e' x) : e = e' :=
to_linear_equiv_injective $ linear_equiv.ext h

protected lemma congr_arg {f : E ≃ₛₗᵢ[σ₁₂] E₂} : Π {x x' : E}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : E ≃ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E) : f x = g x := h ▸ rfl

/-- Construct a `linear_isometry_equiv` from a `linear_equiv` and two inequalities:
`∀ x, ∥e x∥ ≤ ∥x∥` and `∀ y, ∥e.symm y∥ ≤ ∥y∥`. -/
def of_bounds (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : ∀ x, ∥e x∥ ≤ ∥x∥) (h₂ : ∀ y, ∥e.symm y∥ ≤ ∥y∥) :
  E ≃ₛₗᵢ[σ₁₂] E₂ :=
⟨e, λ x, le_antisymm (h₁ x) $ by simpa only [e.symm_apply_apply] using h₂ (e x)⟩

@[simp] lemma norm_map (x : E) : ∥e x∥ = ∥x∥ := e.norm_map' x

/-- Reinterpret a `linear_isometry_equiv` as a `linear_isometry`. -/
def to_linear_isometry : E →ₛₗᵢ[σ₁₂] E₂ := ⟨e.1, e.2⟩

lemma to_linear_isometry_injective :
  function.injective (to_linear_isometry : _ → E →ₛₗᵢ[σ₁₂] E₂) :=
λ x y h, coe_injective (congr_arg _ h : ⇑x.to_linear_isometry = _)

@[simp] lemma to_linear_isometry_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
  f.to_linear_isometry = g.to_linear_isometry ↔ f = g :=
to_linear_isometry_injective.eq_iff

@[simp] lemma coe_to_linear_isometry : ⇑e.to_linear_isometry = e := rfl

protected lemma isometry : isometry e := e.to_linear_isometry.isometry

/-- Reinterpret a `linear_isometry_equiv` as an `isometric`. -/
def to_isometric : E ≃ᵢ E₂ := ⟨e.to_linear_equiv.to_equiv, e.isometry⟩

lemma to_isometric_injective :
  function.injective (to_isometric : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ᵢ E₂) :=
λ x y h, coe_injective (congr_arg _ h : ⇑x.to_isometric = _)

@[simp] lemma to_isometric_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
  f.to_isometric = g.to_isometric ↔ f = g :=
to_isometric_injective.eq_iff

@[simp] lemma coe_to_isometric : ⇑e.to_isometric = e := rfl

lemma range_eq_univ (e : E ≃ₛₗᵢ[σ₁₂] E₂) : set.range e = set.univ :=
by { rw ← coe_to_isometric, exact isometric.range_eq_univ _, }

/-- Reinterpret a `linear_isometry_equiv` as an `homeomorph`. -/
def to_homeomorph : E ≃ₜ E₂ := e.to_isometric.to_homeomorph

lemma to_homeomorph_injective :
  function.injective (to_homeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₜ E₂) :=
λ x y h, coe_injective (congr_arg _ h : ⇑x.to_homeomorph = _)

@[simp] lemma to_homeomorph_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
  f.to_homeomorph = g.to_homeomorph ↔ f = g :=
to_homeomorph_injective.eq_iff

@[simp] lemma coe_to_homeomorph : ⇑e.to_homeomorph = e := rfl

protected lemma continuous : continuous e := e.isometry.continuous
protected lemma continuous_at {x} : continuous_at e x := e.continuous.continuous_at
protected lemma continuous_on {s} : continuous_on e s := e.continuous.continuous_on

protected lemma continuous_within_at {s x} : continuous_within_at e s x :=
e.continuous.continuous_within_at

/-- Interpret a `linear_isometry_equiv` as a continuous linear equiv. -/
def to_continuous_linear_equiv : E ≃SL[σ₁₂] E₂ :=
{ .. e.to_linear_isometry.to_continuous_linear_map,
  .. e.to_homeomorph }

lemma to_continuous_linear_equiv_injective :
  function.injective (to_continuous_linear_equiv : _ → E ≃SL[σ₁₂] E₂) :=
λ x y h, coe_injective (congr_arg _ h : ⇑x.to_continuous_linear_equiv = _)

@[simp] lemma to_continuous_linear_equiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
  f.to_continuous_linear_equiv = g.to_continuous_linear_equiv ↔ f = g :=
to_continuous_linear_equiv_injective.eq_iff

@[simp] lemma coe_to_continuous_linear_equiv : ⇑e.to_continuous_linear_equiv = e := rfl

omit σ₂₁

variables (R E)

/-- Identity map as a `linear_isometry_equiv`. -/
def refl : E ≃ₗᵢ[R] E := ⟨linear_equiv.refl R E, λ x, rfl⟩

variables {R E}

instance : inhabited (E ≃ₗᵢ[R] E) := ⟨refl R E⟩

@[simp] lemma coe_refl : ⇑(refl R E) = id := rfl

/-- The inverse `linear_isometry_equiv`. -/
def symm : E₂ ≃ₛₗᵢ[σ₂₁] E :=
⟨e.to_linear_equiv.symm,
  λ x, (e.norm_map _).symm.trans $ congr_arg norm $ e.to_linear_equiv.apply_symm_apply x⟩

@[simp] lemma apply_symm_apply (x : E₂) : e (e.symm x) = x := e.to_linear_equiv.apply_symm_apply x
@[simp] lemma symm_apply_apply (x : E) : e.symm (e x) = x := e.to_linear_equiv.symm_apply_apply x
@[simp] lemma map_eq_zero_iff {x : E} : e x = 0 ↔ x = 0 := e.to_linear_equiv.map_eq_zero_iff
@[simp] lemma symm_symm : e.symm.symm = e := ext $ λ x, rfl

@[simp] lemma to_linear_equiv_symm : e.to_linear_equiv.symm = e.symm.to_linear_equiv := rfl
@[simp] lemma to_isometric_symm : e.to_isometric.symm = e.symm.to_isometric := rfl
@[simp] lemma to_homeomorph_symm : e.to_homeomorph.symm = e.symm.to_homeomorph := rfl

include σ₃₁ σ₃₂
/-- Composition of `linear_isometry_equiv`s as a `linear_isometry_equiv`. -/
def trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃ :=
⟨e.to_linear_equiv.trans e'.to_linear_equiv, λ x, (e'.norm_map _).trans (e.norm_map _)⟩

include σ₁₃ σ₂₁
@[simp] lemma coe_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
rfl

@[simp] lemma trans_apply (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E) :
  (e₁.trans e₂ : E ≃ₛₗᵢ[σ₁₃] E₃) c = e₂ (e₁ c) :=
rfl

@[simp] lemma to_linear_equiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
  (e.trans e').to_linear_equiv = e.to_linear_equiv.trans e'.to_linear_equiv :=
rfl

omit σ₁₃ σ₂₁ σ₃₁ σ₃₂

@[simp] lemma trans_refl : e.trans (refl R₂ E₂) = e := ext $ λ x, rfl
@[simp] lemma refl_trans : (refl R E).trans e = e := ext $ λ x, rfl
@[simp] lemma self_trans_symm : e.trans e.symm = refl R E := ext e.symm_apply_apply
@[simp] lemma symm_trans_self : e.symm.trans e = refl R₂ E₂ := ext e.apply_symm_apply
@[simp] lemma symm_comp_self : e.symm ∘ e = id := funext e.symm_apply_apply
@[simp] lemma self_comp_symm : e ∘ e.symm = id := e.symm.symm_comp_self

include σ₁₃ σ₂₁ σ₃₂ σ₃₁
@[simp] lemma symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
  (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
rfl

lemma coe_symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
  ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
rfl

include σ₁₄ σ₄₁ σ₄₂ σ₄₃ σ₂₄
lemma trans_assoc (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄) :
  eEE₂.trans (eE₂E₃.trans eE₃E₄) = (eEE₂.trans eE₂E₃).trans eE₃E₄ :=
rfl
omit σ₂₁ σ₃₁ σ₄₁ σ₃₂ σ₄₂ σ₄₃ σ₁₃ σ₂₄ σ₁₄

instance : group (E ≃ₗᵢ[R] E) :=
{ mul := λ e₁ e₂, e₂.trans e₁,
  one := refl _ _,
  inv := symm,
  one_mul := trans_refl,
  mul_one := refl_trans,
  mul_assoc := λ _ _ _, trans_assoc _ _ _,
  mul_left_inv := self_trans_symm }

@[simp] lemma coe_one : ⇑(1 : E ≃ₗᵢ[R] E) = id := rfl
@[simp] lemma coe_mul (e e' : E ≃ₗᵢ[R] E) : ⇑(e * e') = e ∘ e' := rfl
@[simp] lemma coe_inv (e : E ≃ₗᵢ[R] E) : ⇑(e⁻¹) = e.symm := rfl

lemma one_def : (1 : E ≃ₗᵢ[R] E) = refl _ _ := rfl
lemma mul_def (e e' : E ≃ₗᵢ[R] E) : (e * e' : E ≃ₗᵢ[R] E) = e'.trans e := rfl
lemma inv_def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm := rfl

/-! Lemmas about mixing the group structure with definitions. Because we have multiple ways to
express `linear_isometry_equiv.refl`, `linear_isometry_equiv.symm`, and
`linear_isometry_equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it
after simp.

This copies the approach used by the lemmas near `equiv.perm.trans_one`. -/

@[simp] lemma trans_one : e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e := trans_refl _
@[simp] lemma one_trans : (1 : E ≃ₗᵢ[R] E).trans e = e := refl_trans _
@[simp] lemma refl_mul (e : E ≃ₗᵢ[R] E) : (refl _ _) * e = e := trans_refl _
@[simp] lemma mul_refl (e : E ≃ₗᵢ[R] E) : e * (refl _ _) = e := refl_trans _

include σ₂₁

/-- Reinterpret a `linear_isometry_equiv` as a `continuous_linear_equiv`. -/
instance : has_coe_t (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂) :=
⟨λ e, ⟨e.to_linear_equiv, e.continuous, e.to_isometric.symm.continuous⟩⟩

instance : has_coe_t (E ≃ₛₗᵢ[σ₁₂] E₂) (E →SL[σ₁₂] E₂) := ⟨λ e, ↑(e : E ≃SL[σ₁₂] E₂)⟩

@[simp] lemma coe_coe : ⇑(e : E ≃SL[σ₁₂] E₂) = e := rfl

@[simp] lemma coe_coe' : ((e : E ≃SL[σ₁₂] E₂) : E →SL[σ₁₂] E₂) = e := rfl

@[simp] lemma coe_coe'' : ⇑(e : E →SL[σ₁₂] E₂) = e := rfl

omit σ₂₁

@[simp] lemma map_zero : e 0 = 0 := e.1.map_zero

@[simp] lemma map_add (x y : E) : e (x + y) = e x + e y := e.1.map_add x y

@[simp] lemma map_sub (x y : E) : e (x - y) = e x - e y := e.1.map_sub x y

@[simp] lemma map_smulₛₗ (c : R) (x : E) : e (c • x) = σ₁₂ c • e x := e.1.map_smulₛₗ c x

@[simp] lemma map_smul [module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E) : e (c • x) = c • e x :=
e.1.map_smul c x

@[simp] lemma nnnorm_map (x : E) : nnnorm (e x) = nnnorm x := e.to_linear_isometry.nnnorm_map x

@[simp] lemma dist_map (x y : E) : dist (e x) (e y) = dist x y :=
e.to_linear_isometry.dist_map x y

@[simp] lemma edist_map (x y : E) : edist (e x) (e y) = edist x y :=
e.to_linear_isometry.edist_map x y

protected lemma bijective : bijective e := e.1.bijective
protected lemma injective : injective e := e.1.injective
protected lemma surjective : surjective e := e.1.surjective

@[simp] lemma map_eq_iff {x y : E} : e x = e y ↔ x = y := e.injective.eq_iff

lemma map_ne {x y : E} (h : x ≠ y) : e x ≠ e y := e.injective.ne h

protected lemma lipschitz : lipschitz_with 1 e := e.isometry.lipschitz

protected lemma antilipschitz : antilipschitz_with 1 e := e.isometry.antilipschitz

@[simp] lemma ediam_image (s : set E) : emetric.diam (e '' s) = emetric.diam s :=
e.isometry.ediam_image s

@[simp] lemma diam_image (s : set E) : metric.diam (e '' s) = metric.diam s :=
e.isometry.diam_image s

variables {α : Type*} [topological_space α]

@[simp] lemma comp_continuous_on_iff {f : α → E} {s : set α} :
  continuous_on (e ∘ f) s ↔ continuous_on f s :=
e.isometry.comp_continuous_on_iff

@[simp] lemma comp_continuous_iff {f : α → E} :
  continuous (e ∘ f) ↔ continuous f :=
e.isometry.comp_continuous_iff

instance complete_space_map (p : submodule R E) [complete_space p] :
  complete_space (p.map (e.to_linear_equiv : E →ₛₗ[σ₁₂] E₂)) :=
e.to_linear_isometry.complete_space_map p

include σ₂₁
/-- Construct a linear isometry equiv from a surjective linear isometry. -/
noncomputable def of_surjective (f : F →ₛₗᵢ[σ₁₂] E₂)
  (hfr : function.surjective f) :
  F ≃ₛₗᵢ[σ₁₂] E₂ :=
{ norm_map' := f.norm_map,
  .. linear_equiv.of_bijective f.to_linear_map f.injective hfr }

@[simp] lemma coe_of_surjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : function.surjective f) :
  ⇑(linear_isometry_equiv.of_surjective f hfr) = f :=
by { ext, refl }

omit σ₂₁

variables (R)
/-- The negation operation on a normed space `E`, considered as a linear isometry equivalence. -/
def neg : E ≃ₗᵢ[R] E :=
{ norm_map' := norm_neg,
  .. linear_equiv.neg R }

variables {R}
@[simp] lemma coe_neg : (neg R : E → E) = λ x, -x := rfl

@[simp] lemma symm_neg : (neg R : E ≃ₗᵢ[R] E).symm = neg R := rfl

variables (R E E₂ E₃)

/-- The natural equivalence `(E × E₂) × E₃ ≃ E × (E₂ × E₃)` is a linear isometry. -/
noncomputable def prod_assoc [module R E₂] [module R E₃] : (E × E₂) × E₃ ≃ₗᵢ[R] E × E₂ × E₃ :=
{ to_fun    := equiv.prod_assoc E E₂ E₃,
  inv_fun   := (equiv.prod_assoc E E₂ E₃).symm,
  map_add'  := by simp,
  map_smul' := by simp,
  norm_map' :=
    begin
      rintros ⟨⟨e, f⟩, g⟩,
      simp only [linear_equiv.coe_mk, equiv.prod_assoc_apply, prod.norm_def, max_assoc],
    end,
  .. equiv.prod_assoc E E₂ E₃, }

@[simp] lemma coe_prod_assoc [module R E₂] [module R E₃] :
  (prod_assoc R E E₂ E₃ : (E × E₂) × E₃ → E × E₂ × E₃) = equiv.prod_assoc E E₂ E₃ :=
rfl

@[simp] lemma coe_prod_assoc_symm [module R E₂] [module R E₃] :
  ((prod_assoc R E E₂ E₃).symm : E × E₂ × E₃ → (E × E₂) × E₃) = (equiv.prod_assoc E E₂ E₃).symm :=
rfl

end linear_isometry_equiv

/-- Two linear isometries are equal if they are equal on basis vectors. -/
lemma basis.ext_linear_isometry {ι : Type*} (b : basis ι R E) {f₁ f₂ : E →ₛₗᵢ[σ₁₂] E₂}
  (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
linear_isometry.to_linear_map_injective $ b.ext h

include σ₂₁

/-- Two linear isometric equivalences are equal if they are equal on basis vectors. -/
lemma basis.ext_linear_isometry_equiv {ι : Type*} (b : basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂}
  (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
linear_isometry_equiv.to_linear_equiv_injective $ b.ext' h

omit σ₂₁
