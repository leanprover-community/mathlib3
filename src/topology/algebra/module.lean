/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov
-/
import topology.algebra.ring
import topology.uniform_space.uniform_embedding
import ring_theory.algebra
import linear_algebra.projection

/-!
# Theory of topological modules and continuous linear maps.

We define classes `topological_semimodule`, `topological_module` and `topological_vector_spaces`,
as extensions of the corresponding algebraic classes where the algebraic operations are continuous.

We also define continuous linear maps, as linear maps between topological modules which are
continuous. The set of continuous linear maps between the topological `R`-modules `M` and `M₂` is
denoted by `M →L[R] M₂`.

Continuous linear equivalences are denoted by `M ≃L[R] M₂`.

## Implementation notes

Topological vector spaces are defined as an `abbreviation` for topological modules,
if the base ring is a field. This has as advantage that topological vector spaces are completely
transparent for type class inference, which means that all instances for topological modules
are immediately picked up for vector spaces as well.
A cosmetic disadvantage is that one can not extend topological vector spaces.
The solution is to extend `topological_module` instead.
-/

open filter
open_locale topological_space big_operators

universes u v w u'

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A topological semimodule, over a semiring which is also a topological space, is a
semimodule in which scalar multiplication is continuous. In applications, R will be a topological
semiring and M a topological additive semigroup, but this is not needed for the definition -/
class topological_semimodule (R : Type u) (M : Type v)
  [semiring R] [topological_space R]
  [topological_space M] [add_comm_monoid M]
  [semimodule R M] : Prop :=
(continuous_smul : continuous (λp : R × M, p.1 • p.2))
end prio

section

variables {R : Type u} {M : Type v}
[semiring R] [topological_space R]
[topological_space M] [add_comm_monoid M]
[semimodule R M] [topological_semimodule R M]

lemma continuous_smul : continuous (λp:R×M, p.1 • p.2) :=
topological_semimodule.continuous_smul

lemma continuous.smul {α : Type*} [topological_space α] {f : α → R} {g : α → M}
  (hf : continuous f) (hg : continuous g) : continuous (λp, f p • g p) :=
continuous_smul.comp (hf.prod_mk hg)

lemma tendsto_smul {c : R} {x : M} : tendsto (λp:R×M, p.fst • p.snd) (𝓝 (c, x)) (𝓝 (c • x)) :=
continuous_smul.tendsto _

lemma filter.tendsto.smul {α : Type*} {l : filter α} {f : α → R} {g : α → M} {c : R} {x : M}
  (hf : tendsto f l (𝓝 c)) (hg : tendsto g l (𝓝 x)) : tendsto (λ a, f a • g a) l (𝓝 (c • x)) :=
tendsto_smul.comp (hf.prod_mk_nhds hg)

end

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A topological module, over a ring which is also a topological space, is a module in which
scalar multiplication is continuous. In applications, `R` will be a topological ring and `M` a
topological additive group, but this is not needed for the definition -/
class topological_module (R : Type u) (M : Type v)
  [ring R] [topological_space R]
  [topological_space M] [add_comm_group M]
  [module R M]
  extends topological_semimodule R M : Prop

/-- A topological vector space is a topological module over a field. -/
abbreviation topological_vector_space (R : Type u) (M : Type v)
  [field R] [topological_space R]
  [topological_space M] [add_comm_group M] [module R M] :=
topological_module R M
end prio

section

variables {R : Type*} {M : Type*}
[ring R] [topological_space R]
[topological_space M] [add_comm_group M]
[module R M] [topological_module R M]

/-- Scalar multiplication by a unit is a homeomorphism from a
topological module onto itself. -/
protected def homeomorph.smul_of_unit (a : units R) : M ≃ₜ M :=
{ to_fun    := λ x, (a : R) • x,
  inv_fun   := λ x, ((a⁻¹ : units R) : R) • x,
  right_inv := λ x, calc (a : R) • ((a⁻¹ : units R) : R) • x = x :
                 by rw [smul_smul, units.mul_inv, one_smul],
  left_inv  := λ x, calc ((a⁻¹ : units R) : R) • (a : R) • x = x :
                 by rw [smul_smul, units.inv_mul, one_smul],
  continuous_to_fun  := continuous_const.smul continuous_id,
  continuous_inv_fun := continuous_const.smul continuous_id }

lemma is_open_map_smul_of_unit (a : units R) : is_open_map (λ (x : M), (a : R) • x) :=
(homeomorph.smul_of_unit a).is_open_map

lemma is_closed_map_smul_of_unit (a : units R) : is_closed_map (λ (x : M), (a : R) • x) :=
(homeomorph.smul_of_unit a).is_closed_map

/-- If `M` is a topological module over `R` and `0` is a limit of invertible elements of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior. See also
`submodule.eq_top_of_nonempty_interior` for a `normed_space` version. -/
lemma submodule.eq_top_of_nonempty_interior' [topological_add_monoid M]
  (h : nhds_within (0:R) {x | is_unit x} ≠ ⊥)
  (s : submodule R M) (hs : (interior (s:set M)).nonempty) :
  s = ⊤ :=
begin
  rcases hs with ⟨y, hy⟩,
  refine (submodule.eq_top_iff'.2 $ λ x, _),
  rw [mem_interior_iff_mem_nhds] at hy,
  have : tendsto (λ c:R, y + c • x) (nhds_within 0 {x | is_unit x}) (𝓝 (y + (0:R) • x)),
    from tendsto_const_nhds.add ((tendsto_nhds_within_of_tendsto_nhds tendsto_id).smul
      tendsto_const_nhds),
  rw [zero_smul, add_zero] at this,
  rcases nonempty_of_mem_sets h (inter_mem_sets (mem_map.1 (this hy)) self_mem_nhds_within)
    with ⟨_, hu, u, rfl⟩,
  have hy' : y ∈ ↑s := mem_of_nhds hy,
  exact (s.smul_mem_iff' _).1 ((s.add_mem_iff_right hy').1 hu)
end

end

section

variables {R : Type*} {M : Type*} {a : R}
[field R] [topological_space R]
[topological_space M] [add_comm_group M]
[vector_space R M] [topological_vector_space R M]


/-- Scalar multiplication by a non-zero field element is a
homeomorphism from a topological vector space onto itself. -/
protected def homeomorph.smul_of_ne_zero (ha : a ≠ 0) : M ≃ₜ M :=
{.. homeomorph.smul_of_unit (units.mk0 a ha)}

lemma is_open_map_smul_of_ne_zero (ha : a ≠ 0) : is_open_map (λ (x : M), a • x) :=
(homeomorph.smul_of_ne_zero ha).is_open_map

lemma is_closed_map_smul_of_ne_zero (ha : a ≠ 0) : is_closed_map (λ (x : M), a • x) :=
(homeomorph.smul_of_ne_zero ha).is_closed_map

end

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure continuous_linear_map
  (R : Type*) [semiring R]
  (M : Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : Type*) [topological_space M₂] [add_comm_monoid M₂]
  [semimodule R M] [semimodule R M₂]
  extends linear_map R M M₂ :=
(cont : continuous to_fun)

notation M ` →L[`:25 R `] ` M₂ := continuous_linear_map R M M₂

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological ring `R`. -/
@[nolint has_inhabited_instance]
structure continuous_linear_equiv
  (R : Type*) [semiring R]
  (M : Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : Type*) [topological_space M₂] [add_comm_monoid M₂]
  [semimodule R M] [semimodule R M₂]
  extends linear_equiv R M M₂ :=
(continuous_to_fun  : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

notation M ` ≃L[`:50 R `] ` M₂ := continuous_linear_equiv R M M₂

namespace continuous_linear_map

section semiring
/- Properties that hold for non-necessarily commutative semirings. -/

variables
{R : Type*} [semiring R]
{M : Type*} [topological_space M] [add_comm_monoid M]
{M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_monoid M₄]
[semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]

/-- Coerce continuous linear maps to linear maps. -/
instance : has_coe (M →L[R] M₂) (M →ₗ[R] M₂) := ⟨to_linear_map⟩

/-- Coerce continuous linear maps to functions. -/
-- see Note [function coercion]
instance to_fun : has_coe_to_fun $ M →L[R] M₂ := ⟨λ _, M → M₂, λ f, f⟩

protected lemma continuous (f : M →L[R] M₂) : continuous f := f.2

@[ext] theorem ext {f g : M →L[R] M₂} (h : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr' 1; ext x; apply h

theorem ext_iff {f g : M →L[R] M₂} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, by rw h, by ext⟩

variables (c : R) (f g : M →L[R] M₂) (h : M₂ →L[R] M₃) (x y z : M)

-- make some straightforward lemmas available to `simp`.
@[simp] lemma map_zero : f (0 : M) = 0 := (to_linear_map _).map_zero
@[simp] lemma map_add  : f (x + y) = f x + f y := (to_linear_map _).map_add _ _
@[simp] lemma map_smul : f (c • x) = c • f x := (to_linear_map _).map_smul _ _

@[simp, norm_cast] lemma coe_coe : ((f : M →ₗ[R] M₂) : (M → M₂)) = (f : M → M₂) := rfl

/-- The continuous map that is constantly zero. -/
instance: has_zero (M →L[R] M₂) := ⟨⟨0, continuous_const⟩⟩
instance : inhabited (M →L[R] M₂) := ⟨0⟩

@[simp] lemma zero_apply : (0 : M →L[R] M₂) x = 0 := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : M →L[R] M₂) : M →ₗ[R] M₂) = 0 := rfl
/- no simp attribute on the next line as simp does not always simplify `0 x` to `0`
when `0` is the zero function, while it does for the zero continuous linear map,
and this is the most important property we care about. -/
@[norm_cast] lemma coe_zero' : ((0 : M →L[R] M₂) : M → M₂) = 0 := rfl

section

variables (R M)

/-- the identity map as a continuous linear map. -/
def id : M →L[R] M :=
⟨linear_map.id, continuous_id⟩

end

instance : has_one (M →L[R] M) := ⟨id R M⟩

lemma id_apply : id R M x = x := rfl
@[simp, norm_cast] lemma coe_id : (id R M : M →ₗ[R] M) = linear_map.id := rfl
@[simp, norm_cast] lemma coe_id' : (id R M : M → M) = _root_.id := rfl

@[simp] lemma one_apply : (1 : M →L[R] M) x = x := rfl

section add
variables [topological_add_monoid M₂]

instance : has_add (M →L[R] M₂) :=
⟨λ f g, ⟨f + g, f.2.add g.2⟩⟩

@[simp] lemma add_apply : (f + g) x = f x + g x := rfl
@[simp, norm_cast] lemma coe_add : (((f + g) : M →L[R] M₂) : M →ₗ[R] M₂) = (f : M →ₗ[R] M₂) + g := rfl
@[norm_cast] lemma coe_add' : (((f + g) : M →L[R] M₂) : M → M₂) = (f : M → M₂) + g := rfl

instance : add_comm_monoid (M →L[R] M₂) :=
by { refine {zero := 0, add := (+), ..}; intros; ext;
  apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm] }

lemma sum_apply {ι : Type*} (t : finset ι) (f : ι → M →L[R] M₂) (b : M) :
  (∑ d in t, f d) b = ∑ d in t, f d b :=
begin
  haveI : is_add_monoid_hom (λ (g : M →L[R] M₂), g b) :=
    { map_add := λ f g, continuous_linear_map.add_apply f g b, map_zero := by simp },
  exact (finset.sum_hom t (λ g : M →L[R] M₂, g b)).symm
end

end add

/-- Composition of bounded linear maps. -/
def comp (g : M₂ →L[R] M₃) (f : M →L[R] M₂) : M →L[R] M₃ :=
⟨linear_map.comp g.to_linear_map f.to_linear_map, g.2.comp f.2⟩

@[simp, norm_cast] lemma coe_comp : ((h.comp f) : (M →ₗ[R] M₃)) = (h : M₂ →ₗ[R] M₃).comp f := rfl
@[simp, norm_cast] lemma coe_comp' : ((h.comp f) : (M → M₃)) = (h : M₂ → M₃) ∘ f := rfl

@[simp] theorem comp_id : f.comp (id R M) = f :=
ext $ λ x, rfl

@[simp] theorem id_comp : (id R M₂).comp f = f :=
ext $ λ x, rfl

@[simp] theorem comp_zero : f.comp (0 : M₃ →L[R] M) = 0 :=
by { ext, simp }

@[simp] theorem zero_comp : (0 : M₂ →L[R] M₃).comp f = 0 :=
by { ext, simp }

@[simp] lemma comp_add [topological_add_monoid M₂] [topological_add_monoid M₃]
  (g : M₂ →L[R] M₃) (f₁ f₂ : M →L[R] M₂) :
  g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
by { ext, simp }

@[simp] lemma add_comp [topological_add_monoid M₃]
  (g₁ g₂ : M₂ →L[R] M₃) (f : M →L[R] M₂) :
  (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
by { ext, simp }

theorem comp_assoc (h : M₃ →L[R] M₄) (g : M₂ →L[R] M₃) (f : M →L[R] M₂) :
  (h.comp g).comp f = h.comp (g.comp f) :=
rfl

instance : has_mul (M →L[R] M) := ⟨comp⟩

lemma mul_def (f g : M →L[R] M) : f * g = f.comp g := rfl

@[simp] lemma coe_mul (f g : M →L[R] M) : ⇑(f * g) = f ∘ g := rfl

lemma mul_apply (f g : M →L[R] M) (x : M) : (f * g) x = f (g x) := rfl

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod (f₁ : M →L[R] M₂) (f₂ : M →L[R] M₃) : M →L[R] (M₂ × M₃) :=
{ cont := f₁.2.prod_mk f₂.2,
  ..f₁.to_linear_map.prod f₂.to_linear_map }

@[simp, norm_cast] lemma coe_prod (f₁ : M →L[R] M₂) (f₂ : M →L[R] M₃) :
  (f₁.prod f₂ : M →ₗ[R] M₂ × M₃) = linear_map.prod f₁ f₂ :=
rfl

@[simp, norm_cast] lemma prod_apply (f₁ : M →L[R] M₂) (f₂ : M →L[R] M₃) (x : M) :
  f₁.prod f₂ x = (f₁ x, f₂ x) :=
rfl

/-- Kernel of a continuous linear map. -/
def ker (f : M →L[R] M₂) : submodule R M := (f : M →ₗ[R] M₂).ker

@[norm_cast] lemma ker_coe : (f : M →ₗ[R] M₂).ker = f.ker := rfl

@[simp] lemma mem_ker {f : M →L[R] M₂} {x} : x ∈ f.ker ↔ f x = 0 := linear_map.mem_ker

lemma is_closed_ker [t1_space M₂] : is_closed (f.ker : set M) :=
continuous_iff_is_closed.1 f.cont _ is_closed_singleton

@[simp] lemma apply_ker (x : f.ker) : f x = 0 := mem_ker.1 x.2

lemma is_complete_ker {M' : Type*} [uniform_space M'] [complete_space M'] [add_comm_monoid M']
  [semimodule R M'] [t1_space M₂] (f : M' →L[R] M₂) :
  is_complete (f.ker : set M') :=
f.is_closed_ker.is_complete

instance complete_space_ker {M' : Type*} [uniform_space M'] [complete_space M'] [add_comm_monoid M']
  [semimodule R M'] [t1_space M₂] (f : M' →L[R] M₂) :
  complete_space f.ker :=
f.is_closed_ker.complete_space_coe

@[simp] lemma ker_prod (f : M →L[R] M₂) (g : M →L[R] M₃) :
  ker (f.prod g) = ker f ⊓ ker g :=
linear_map.ker_prod f g

/-- Range of a continuous linear map. -/
def range (f : M →L[R] M₂) : submodule R M₂ := (f : M →ₗ[R] M₂).range

lemma range_coe : (f.range : set M₂) = set.range f := linear_map.range_coe _
lemma mem_range {f : M →L[R] M₂} {y} : y ∈ f.range ↔ ∃ x, f x = y := linear_map.mem_range

lemma range_prod_le (f : M →L[R] M₂) (g : M →L[R] M₃) :
  range (f.prod g) ≤ (range f).prod (range g) :=
(f : M →ₗ[R] M₂).range_prod_le g

/-- Restrict codomain of a continuous linear map. -/
def cod_restrict (f : M →L[R] M₂) (p : submodule R M₂) (h : ∀ x, f x ∈ p) :
  M →L[R] p :=
{ cont := continuous_subtype_mk h f.continuous,
  to_linear_map := (f : M →ₗ[R] M₂).cod_restrict p h}

@[norm_cast] lemma coe_cod_restrict (f : M →L[R] M₂) (p : submodule R M₂) (h : ∀ x, f x ∈ p) :
  (f.cod_restrict p h : M →ₗ[R] p) = (f : M →ₗ[R] M₂).cod_restrict p h :=
rfl

@[simp] lemma coe_cod_restrict_apply (f : M →L[R] M₂) (p : submodule R M₂) (h : ∀ x, f x ∈ p) (x) :
  (f.cod_restrict p h x : M₂) = f x :=
rfl

@[simp] lemma ker_cod_restrict (f : M →L[R] M₂) (p : submodule R M₂) (h : ∀ x, f x ∈ p) :
  ker (f.cod_restrict p h) = ker f :=
(f : M →ₗ[R] M₂).ker_cod_restrict p h

/-- Embedding of a submodule into the ambient space as a continuous linear map. -/
def subtype_val (p : submodule R M) : p →L[R] M :=
{ cont := continuous_subtype_val,
  to_linear_map := p.subtype }

@[simp, norm_cast] lemma coe_subtype_val (p : submodule R M) :
  (subtype_val p : p →ₗ[R] M) = p.subtype :=
rfl

@[simp, norm_cast] lemma subtype_val_apply (p : submodule R M) (x : p) :
  (subtype_val p : p → M) x = x :=
rfl

variables (R M M₂)

/-- `prod.fst` as a `continuous_linear_map`. -/
def fst : M × M₂ →L[R] M :=
{ cont := continuous_fst, to_linear_map := linear_map.fst R M M₂ }

/-- `prod.snd` as a `continuous_linear_map`. -/
def snd : M × M₂ →L[R] M₂ :=
{ cont := continuous_snd, to_linear_map := linear_map.snd R M M₂ }

variables {R M M₂}

@[simp, norm_cast] lemma coe_fst : (fst R M M₂ : M × M₂ →ₗ[R] M) = linear_map.fst R M M₂ := rfl

@[simp, norm_cast] lemma coe_fst' : (fst R M M₂ : M × M₂ → M) = prod.fst := rfl

@[simp, norm_cast] lemma coe_snd : (snd R M M₂ : M × M₂ →ₗ[R] M₂) = linear_map.snd R M M₂ := rfl

@[simp, norm_cast] lemma coe_snd' : (snd R M M₂ : M × M₂ → M₂) = prod.snd := rfl

@[simp] lemma fst_prod_snd : (fst R M M₂).prod (snd R M M₂) = id R (M × M₂) := ext $ λ ⟨x, y⟩, rfl

/-- `prod.map` of two continuous linear maps. -/
def prod_map (f₁ : M →L[R] M₂) (f₂ : M₃ →L[R] M₄) : (M × M₃) →L[R] (M₂ × M₄) :=
(f₁.comp (fst R M M₃)).prod (f₂.comp (snd R M M₃))

@[simp, norm_cast] lemma coe_prod_map (f₁ : M →L[R] M₂) (f₂ : M₃ →L[R] M₄) :
  (f₁.prod_map f₂ : (M × M₃) →ₗ[R] (M₂ × M₄)) = ((f₁ : M →ₗ[R] M₂).prod_map (f₂ : M₃ →ₗ[R] M₄)) :=
rfl

@[simp, norm_cast] lemma coe_prod_map' (f₁ : M →L[R] M₂) (f₂ : M₃ →L[R] M₄) :
  ⇑(f₁.prod_map f₂) = prod.map f₁ f₂ :=
rfl

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
def coprod [topological_add_monoid M₃] (f₁ : M →L[R] M₃) (f₂ : M₂ →L[R] M₃) :
  (M × M₂) →L[R] M₃ :=
⟨linear_map.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩

@[norm_cast, simp] lemma coe_coprod [topological_add_monoid M₃]
  (f₁ : M →L[R] M₃) (f₂ : M₂ →L[R] M₃) :
  (f₁.coprod f₂ : (M × M₂) →ₗ[R] M₃) = linear_map.coprod f₁ f₂ :=
rfl

@[simp] lemma coprod_apply [topological_add_monoid M₃] (f₁ : M →L[R] M₃) (f₂ : M₂ →L[R] M₃) (x) :
  f₁.coprod f₂ x = f₁ x.1 + f₂ x.2 := rfl

variables [topological_space R] [topological_semimodule R M₂]

/-- The linear map `λ x, c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`) -/
def smul_right (c : M →L[R] R) (f : M₂) : M →L[R] M₂ :=
{ cont := c.2.smul continuous_const,
  ..c.to_linear_map.smul_right f }

@[simp]
lemma smul_right_apply {c : M →L[R] R} {f : M₂} {x : M} :
  (smul_right c f : M → M₂) x = (c : M → R) x • f :=
rfl

@[simp]
lemma smul_right_one_one (c : R →L[R] M₂) : smul_right 1 ((c : R → M₂) 1) = c :=
by ext; simp [-continuous_linear_map.map_smul, (continuous_linear_map.map_smul _ _ _).symm]

@[simp]
lemma smul_right_one_eq_iff {f f' : M₂} :
  smul_right (1 : R →L[R] R) f = smul_right 1 f' ↔ f = f' :=
⟨λ h, have (smul_right (1 : R →L[R] R) f : R → M₂) 1 = (smul_right (1 : R →L[R] R) f' : R → M₂) 1,
        by rw h,
      by simp at this; assumption,
  by cc⟩

lemma smul_right_comp [topological_semimodule R R] {x : M₂} {c : R} :
  (smul_right 1 x : R →L[R] M₂).comp (smul_right 1 c : R →L[R] R) = smul_right 1 (c • x) :=
by { ext, simp [mul_smul] }

end semiring

section ring

variables
{R : Type*} [ring R]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_group M₄]
[semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]

variables (c : R) (f g : M →L[R] M₂) (h : M₂ →L[R] M₃) (x y z : M)

@[simp] lemma map_neg  : f (-x) = - (f x) := (to_linear_map _).map_neg _
@[simp] lemma map_sub  : f (x - y) = f x - f y := (to_linear_map _).map_sub _ _
@[simp] lemma sub_apply' (x : M) : ((f : M →ₗ[R] M₂) - g) x = f x - g x := rfl

lemma range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : ker f ⊔ ker g = ⊤) :
  range (f.prod g) = (range f).prod (range g) :=
linear_map.range_prod_eq h

section
variables [topological_add_group M₂]

instance : has_neg (M →L[R] M₂) := ⟨λ f, ⟨-f, f.2.neg⟩⟩

@[simp] lemma neg_apply : (-f) x = - (f x) := rfl

@[simp, norm_cast] lemma coe_neg : (((-f) : M →L[R] M₂) : M →ₗ[R] M₂) = -(f : M →ₗ[R] M₂) := rfl
@[norm_cast] lemma coe_neg' : (((-f) : M →L[R] M₂) : M → M₂) = -(f : M → M₂) := rfl

instance : add_comm_group (M →L[R] M₂) :=
by { refine {zero := 0, add := (+), neg := has_neg.neg, ..}; intros; ext;
  apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm] }

lemma sub_apply (x : M) : (f - g) x = f x - g x := rfl
@[simp, norm_cast] lemma coe_sub : (((f - g) : M →L[R] M₂) : M →ₗ[R] M₂) = (f : M →ₗ[R] M₂) - g := rfl
@[simp, norm_cast] lemma coe_sub' : (((f - g) : M →L[R] M₂) : M → M₂) = (f : M → M₂) - g := rfl

end

instance [topological_add_group M] : ring (M →L[R] M) :=
{ mul := (*),
  one := 1,
  mul_one := λ _, ext $ λ _, rfl,
  one_mul := λ _, ext $ λ _, rfl,
  mul_assoc := λ _ _ _, ext $ λ _, rfl,
  left_distrib := λ _ _ _, ext $ λ _, map_add _ _ _,
  right_distrib := λ _ _ _, ext $ λ _, linear_map.add_apply _ _ _,
  ..continuous_linear_map.add_comm_group }

lemma smul_right_one_pow [topological_space R]
  [topological_add_group R] [topological_semimodule R R] (c : R) (n : ℕ) :
  (smul_right 1 c : R →L[R] R)^n = smul_right 1 (c^n) :=
begin
  induction n with n ihn,
  { ext, simp },
  { rw [pow_succ, ihn, mul_def, smul_right_comp, smul_eq_mul, pow_succ'] }
end

/-- Given a right inverse `f₂ : M₂ →L[R] M` to `f₁ : M →L[R] M₂`,
`proj_ker_of_right_inverse f₁ f₂ h` is the projection `M →L[R] f₁.ker` along `f₂.range`. -/
def proj_ker_of_right_inverse [topological_add_group M] (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) :
  M →L[R] f₁.ker :=
(id R M - f₂.comp f₁).cod_restrict f₁.ker $ λ x, by simp [h (f₁ x)]

@[simp] lemma coe_proj_ker_of_right_inverse_apply [topological_add_group M]
  (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : function.right_inverse f₂ f₁) (x : M) :
  (f₁.proj_ker_of_right_inverse f₂ h x : M) = x - f₂ (f₁ x) :=
rfl

@[simp] lemma proj_ker_of_right_inverse_apply_idem [topological_add_group M]
  (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : function.right_inverse f₂ f₁) (x : f₁.ker) :
  f₁.proj_ker_of_right_inverse f₂ h x = x :=
subtype.ext_iff_val.2 $ by simp

@[simp] lemma proj_ker_of_right_inverse_comp_inv [topological_add_group M]
  (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : function.right_inverse f₂ f₁) (y : M₂) :
  f₁.proj_ker_of_right_inverse f₂ h (f₂ y) = 0 :=
subtype.ext_iff_val.2 $ by simp [h y]

end ring

section comm_ring

variables
{R : Type*} [comm_ring R] [topological_space R]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
[module R M] [module R M₂] [module R M₃] [topological_module R M₃]

instance : has_scalar R (M →L[R] M₃) :=
⟨λ c f, ⟨c • f, continuous_const.smul f.2⟩⟩

variables (c : R) (h : M₂ →L[R] M₃) (f g : M →L[R] M₂) (x y z : M)

@[simp] lemma smul_comp : (c • h).comp f = c • (h.comp f) := rfl

variable [topological_module R M₂]

@[simp] lemma smul_apply : (c • f) x = c • (f x) := rfl
@[simp, norm_cast] lemma coe_apply : (((c • f) : M →L[R] M₂) : M →ₗ[R] M₂) = c • (f : M →ₗ[R] M₂) := rfl
@[norm_cast] lemma coe_apply' : (((c • f) : M →L[R] M₂) : M → M₂) = c • (f : M → M₂) := rfl

@[simp] lemma comp_smul : h.comp (c • f) = c • (h.comp f) := by { ext, simp }

variable [topological_add_group M₂]

instance : module R (M →L[R] M₂) :=
{ smul_zero := λ _, ext $ λ _, smul_zero _,
  zero_smul := λ _, ext $ λ _, zero_smul _ _,
  one_smul  := λ _, ext $ λ _, one_smul _ _,
  mul_smul  := λ _ _ _, ext $ λ _, mul_smul _ _ _,
  add_smul  := λ _ _ _, ext $ λ _, add_smul _ _ _,
  smul_add  := λ _ _ _, ext $ λ _, smul_add _ _ _ }

instance : algebra R (M₂ →L[R] M₂) :=
algebra.of_semimodule' (λ c f, ext $ λ x, rfl) (λ c f, ext $ λ x, f.map_smul c x)

end comm_ring

end continuous_linear_map

namespace continuous_linear_equiv

section add_comm_monoid

variables {R : Type*} [semiring R]
{M : Type*} [topological_space M] [add_comm_monoid M]
{M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_monoid M₄]
[semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]

/-- A continuous linear equivalence induces a continuous linear map. -/
def to_continuous_linear_map (e : M ≃L[R] M₂) : M →L[R] M₂ :=
{ cont := e.continuous_to_fun,
  ..e.to_linear_equiv.to_linear_map }

/-- Coerce continuous linear equivs to continuous linear maps. -/
instance : has_coe (M ≃L[R] M₂) (M →L[R] M₂) := ⟨to_continuous_linear_map⟩

/-- Coerce continuous linear equivs to maps. -/
-- see Note [function coercion]
instance : has_coe_to_fun (M ≃L[R] M₂) := ⟨λ _, M → M₂, λ f, f⟩

@[simp] theorem coe_def_rev (e : M ≃L[R] M₂) : e.to_continuous_linear_map = e := rfl

@[simp] theorem coe_apply (e : M ≃L[R] M₂) (b : M) : (e : M →L[R] M₂) b = e b := rfl

@[norm_cast] lemma coe_coe (e : M ≃L[R] M₂) : ((e : M →L[R] M₂) : M → M₂) = e := rfl

@[ext] lemma ext {f g : M ≃L[R] M₂} (h : (f : M → M₂) = g) : f = g :=
begin
  cases f; cases g,
  simp only,
  ext x,
  induction h,
  refl
end

/-- A continuous linear equivalence induces a homeomorphism. -/
def to_homeomorph (e : M ≃L[R] M₂) : M ≃ₜ M₂ := { ..e }

-- Make some straightforward lemmas available to `simp`.
@[simp] lemma map_zero (e : M ≃L[R] M₂) : e (0 : M) = 0 := (e : M →L[R] M₂).map_zero
@[simp] lemma map_add (e : M ≃L[R] M₂) (x y : M) : e (x + y) = e x + e y :=
(e : M →L[R] M₂).map_add x y
@[simp] lemma map_smul (e : M ≃L[R] M₂) (c : R) (x : M) : e (c • x) = c • (e x) :=
(e : M →L[R] M₂).map_smul c x
@[simp] lemma map_eq_zero_iff (e : M ≃L[R] M₂) {x : M} : e x = 0 ↔ x = 0 :=
e.to_linear_equiv.map_eq_zero_iff

protected lemma continuous (e : M ≃L[R] M₂) : continuous (e : M → M₂) :=
e.continuous_to_fun

protected lemma continuous_on (e : M ≃L[R] M₂) {s : set M} : continuous_on (e : M → M₂) s :=
e.continuous.continuous_on

protected lemma continuous_at (e : M ≃L[R] M₂) {x : M} : continuous_at (e : M → M₂) x :=
e.continuous.continuous_at

protected lemma continuous_within_at (e : M ≃L[R] M₂) {s : set M} {x : M} :
  continuous_within_at (e : M → M₂) s x :=
e.continuous.continuous_within_at

lemma comp_continuous_on_iff
  {α : Type*} [topological_space α] (e : M ≃L[R] M₂) (f : α → M) (s : set α) :
  continuous_on (e ∘ f) s ↔ continuous_on f s :=
e.to_homeomorph.comp_continuous_on_iff _ _

lemma comp_continuous_iff
  {α : Type*} [topological_space α] (e : M ≃L[R] M₂) (f : α → M) :
  continuous (e ∘ f) ↔ continuous f :=
e.to_homeomorph.comp_continuous_iff _

/-- An extensionality lemma for `R ≃L[R] M`. -/
lemma ext₁ [topological_space R] {f g : R ≃L[R] M} (h : f 1 = g 1) : f = g :=
ext $ funext $ λ x, mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

section
variables (R M)

/-- The identity map as a continuous linear equivalence. -/
@[refl] protected def refl : M ≃L[R] M :=
{ continuous_to_fun := continuous_id,
  continuous_inv_fun := continuous_id,
  .. linear_equiv.refl R M }
end

@[simp, norm_cast] lemma coe_refl :
  (continuous_linear_equiv.refl R M : M →L[R] M) = continuous_linear_map.id R M := rfl

@[simp, norm_cast] lemma coe_refl' :
  (continuous_linear_equiv.refl R M : M → M) = id := rfl

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence-/
@[symm] protected def symm (e : M ≃L[R] M₂) : M₂ ≃L[R] M :=
{ continuous_to_fun := e.continuous_inv_fun,
  continuous_inv_fun := e.continuous_to_fun,
  .. e.to_linear_equiv.symm }

@[simp] lemma symm_to_linear_equiv (e : M ≃L[R] M₂) :
  e.symm.to_linear_equiv = e.to_linear_equiv.symm :=
by { ext, refl }

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans] protected def trans (e₁ : M ≃L[R] M₂) (e₂ : M₂ ≃L[R] M₃) : M ≃L[R] M₃ :=
{ continuous_to_fun := e₂.continuous_to_fun.comp e₁.continuous_to_fun,
  continuous_inv_fun := e₁.continuous_inv_fun.comp e₂.continuous_inv_fun,
  .. e₁.to_linear_equiv.trans e₂.to_linear_equiv }

@[simp] lemma trans_to_linear_equiv (e₁ : M ≃L[R] M₂) (e₂ : M₂ ≃L[R] M₃) :
  (e₁.trans e₂).to_linear_equiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv :=
by { ext, refl }

/-- Product of two continuous linear equivalences. The map comes from `equiv.prod_congr`. -/
def prod (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) : (M × M₃) ≃L[R] (M₂ × M₄) :=
{ continuous_to_fun := e.continuous_to_fun.prod_map e'.continuous_to_fun,
  continuous_inv_fun := e.continuous_inv_fun.prod_map e'.continuous_inv_fun,
  .. e.to_linear_equiv.prod e'.to_linear_equiv }

@[simp, norm_cast] lemma prod_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (x) :
  e.prod e' x = (e x.1, e' x.2) := rfl

@[simp, norm_cast] lemma coe_prod (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) :
  (e.prod e' : (M × M₃) →L[R] (M₂ × M₄)) = (e : M →L[R] M₂).prod_map (e' : M₃ →L[R] M₄) :=
rfl

theorem bijective (e : M ≃L[R] M₂) : function.bijective e := e.to_linear_equiv.to_equiv.bijective
theorem injective (e : M ≃L[R] M₂) : function.injective e := e.to_linear_equiv.to_equiv.injective
theorem surjective (e : M ≃L[R] M₂) : function.surjective e := e.to_linear_equiv.to_equiv.surjective

@[simp] theorem apply_symm_apply (e : M ≃L[R] M₂) (c : M₂) : e (e.symm c) = c := e.1.6 c
@[simp] theorem symm_apply_apply (e : M ≃L[R] M₂) (b : M) : e.symm (e b) = b := e.1.5 b

@[simp] theorem coe_comp_coe_symm (e : M ≃L[R] M₂) :
  (e : M →L[R] M₂).comp (e.symm : M₂ →L[R] M) = continuous_linear_map.id R M₂ :=
continuous_linear_map.ext e.apply_symm_apply

@[simp] theorem coe_symm_comp_coe (e : M ≃L[R] M₂) :
  (e.symm : M₂ →L[R] M).comp (e : M →L[R] M₂) = continuous_linear_map.id R M :=
continuous_linear_map.ext e.symm_apply_apply

lemma symm_comp_self (e : M ≃L[R] M₂) :
  (e.symm : M₂ → M) ∘ (e : M → M₂) = id :=
by{ ext x, exact symm_apply_apply e x }

lemma self_comp_symm (e : M ≃L[R] M₂) :
  (e : M → M₂) ∘ (e.symm : M₂ → M) = id :=
by{ ext x, exact apply_symm_apply e x }

@[simp] lemma symm_comp_self' (e : M ≃L[R] M₂) :
  ((e.symm : M₂ →L[R] M) : M₂ → M) ∘ ((e : M →L[R] M₂) : M → M₂) = id :=
symm_comp_self e

@[simp] lemma self_comp_symm' (e : M ≃L[R] M₂) :
  ((e : M →L[R] M₂) : M → M₂) ∘ ((e.symm : M₂ →L[R] M) : M₂ → M) = id :=
self_comp_symm e

@[simp] theorem symm_symm (e : M ≃L[R] M₂) : e.symm.symm = e :=
by { ext x, refl }

theorem symm_symm_apply (e : M ≃L[R] M₂) (x : M) : e.symm.symm x = e x :=
rfl

lemma symm_apply_eq (e : M ≃L[R] M₂) {x y} : e.symm x = y ↔ x = e y :=
e.to_linear_equiv.symm_apply_eq

lemma eq_symm_apply (e : M ≃L[R] M₂) {x y} : y = e.symm x ↔ e y = x :=
e.to_linear_equiv.eq_symm_apply

/-- Create a `continuous_linear_equiv` from two `continuous_linear_map`s that are
inverse of each other. -/
def equiv_of_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h₁ : function.left_inverse f₂ f₁)
  (h₂ : function.right_inverse f₂ f₁) :
  M ≃L[R] M₂ :=
{ to_fun := f₁,
  continuous_to_fun := f₁.continuous,
  inv_fun := f₂,
  continuous_inv_fun := f₂.continuous,
  left_inv := h₁,
  right_inv := h₂,
  .. f₁ }

@[simp] lemma equiv_of_inverse_apply (f₁ : M →L[R] M₂) (f₂ h₁ h₂ x) :
  equiv_of_inverse f₁ f₂ h₁ h₂ x = f₁ x :=
rfl

@[simp] lemma symm_equiv_of_inverse (f₁ : M →L[R] M₂) (f₂ h₁ h₂) :
  (equiv_of_inverse f₁ f₂ h₁ h₂).symm = equiv_of_inverse f₂ f₁ h₂ h₁ :=
rfl

end add_comm_monoid

section add_comm_group

variables {R : Type*} [semiring R]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_group M₄]
[semimodule R M] [semimodule R M₂] [semimodule R M₃] [semimodule R M₄]

variables [topological_add_group M₄]

/-- Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
def skew_prod (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) :
  (M × M₃) ≃L[R] M₂ × M₄ :=
{ continuous_to_fun := (e.continuous_to_fun.comp continuous_fst).prod_mk
    ((e'.continuous_to_fun.comp continuous_snd).add $ f.continuous.comp continuous_fst),
  continuous_inv_fun := (e.continuous_inv_fun.comp continuous_fst).prod_mk
    (e'.continuous_inv_fun.comp $ continuous_snd.sub $ f.continuous.comp $
      e.continuous_inv_fun.comp continuous_fst),
.. e.to_linear_equiv.skew_prod e'.to_linear_equiv ↑f  }

@[simp] lemma skew_prod_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
  e.skew_prod e' f x = (e x.1, e' x.2 + f x.1) := rfl

@[simp] lemma skew_prod_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
  (e.skew_prod e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) := rfl

end add_comm_group

section ring

variables {R : Type*} [ring R]
{M : Type*} [topological_space M] [add_comm_group M] [semimodule R M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂] [semimodule R M₂]

@[simp] lemma map_sub (e : M ≃L[R] M₂) (x y : M) : e (x - y) = e x - e y :=
(e : M →L[R] M₂).map_sub x y

@[simp] lemma map_neg (e : M ≃L[R] M₂) (x : M) : e (-x) = -e x := (e : M →L[R] M₂).map_neg x

section
variables (R) [topological_space R] [topological_module R R]

/-- Continuous linear equivalences `R ≃L[R] R` are enumerated by `units R`. -/
def units_equiv_aut : units R ≃ (R ≃L[R] R) :=
{ to_fun := λ u, equiv_of_inverse
    (continuous_linear_map.smul_right 1 ↑u)
    (continuous_linear_map.smul_right 1 ↑u⁻¹)
    (λ x, by simp) (λ x, by simp),
  inv_fun := λ e, ⟨e 1, e.symm 1,
    by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply],
    by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, apply_symm_apply]⟩,
  left_inv := λ u, units.ext $ by simp,
  right_inv := λ e, ext₁ $ by simp }

variable {R}

@[simp] lemma units_equiv_aut_apply (u : units R) (x : R) : units_equiv_aut R u x = x * u := rfl

@[simp] lemma units_equiv_aut_apply_symm (u : units R) (x : R) :
  (units_equiv_aut R u).symm x = x * ↑u⁻¹ := rfl

@[simp] lemma units_equiv_aut_symm_apply (e : R ≃L[R] R) :
  ↑((units_equiv_aut R).symm e) = e 1 :=
rfl

end

variables [topological_add_group M]

open continuous_linear_map (id fst snd subtype_val mem_ker)

/-- A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
def equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : function.right_inverse f₂ f₁) :
  M ≃L[R] M₂ × f₁.ker :=
equiv_of_inverse (f₁.prod (f₁.proj_ker_of_right_inverse f₂ h)) (f₂.coprod (subtype_val f₁.ker))
  (λ x, by simp)
  (λ ⟨x, y⟩, by simp [h x])

@[simp] lemma fst_equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) (x : M) :
  (equiv_of_right_inverse f₁ f₂ h x).1 = f₁ x := rfl

@[simp] lemma snd_equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) (x : M) :
  ((equiv_of_right_inverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) := rfl

@[simp] lemma equiv_of_right_inverse_symm_apply (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) (y : M₂ × f₁.ker) :
  (equiv_of_right_inverse f₁ f₂ h).symm y = f₂ y.1 + y.2 := rfl

end ring

end continuous_linear_equiv

namespace submodule

variables
{R : Type*} [ring R]
{M : Type*} [topological_space M] [add_comm_group M] [module R M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂] [module R M₂]

open continuous_linear_map

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def closed_complemented (p : submodule R M) : Prop := ∃ f : M →L[R] p, ∀ x : p, f x = x

lemma closed_complemented.has_closed_complement {p : submodule R M} [t1_space p]
  (h : closed_complemented p) :
  ∃ (q : submodule R M) (hq : is_closed (q : set M)), is_compl p q :=
exists.elim h $ λ f hf, ⟨f.ker, f.is_closed_ker, linear_map.is_compl_of_proj hf⟩

protected lemma closed_complemented.is_closed [topological_add_group M] [t1_space M]
  {p : submodule R M} (h : closed_complemented p) :
  is_closed (p : set M) :=
begin
  rcases h with ⟨f, hf⟩,
  have : ker (id R M - (subtype_val p).comp f) = p := linear_map.ker_id_sub_eq_of_proj hf,
  exact this ▸ (is_closed_ker _)
end

@[simp] lemma closed_complemented_bot : closed_complemented (⊥ : submodule R M) :=
⟨0, λ x, by simp only [zero_apply, eq_zero_of_bot_submodule x]⟩

@[simp] lemma closed_complemented_top : closed_complemented (⊤ : submodule R M) :=
⟨(id R M).cod_restrict ⊤ (λ x, trivial), λ x, subtype.ext_iff_val.2 $ by simp⟩

end submodule

lemma continuous_linear_map.closed_complemented_ker_of_right_inverse {R : Type*} [ring R]
  {M : Type*} [topological_space M] [add_comm_group M]
  {M₂ : Type*} [topological_space M₂] [add_comm_group M₂] [module R M] [module R M₂]
  [topological_add_group M] (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) :
  f₁.ker.closed_complemented :=
⟨f₁.proj_ker_of_right_inverse f₂ h, f₁.proj_ker_of_right_inverse_apply_idem f₂ h⟩
