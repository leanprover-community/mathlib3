/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import data.set.Union_lift
import topology.homeomorph

/-!
# Continuous bundled maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the type `continuous_map` of continuous bundled maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/

open function

/-- The type of continuous maps from `α` to `β`.

When possible, instead of parametrizing results over `(f : C(α, β))`,
you should parametrize over `{F : Type*} [continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `continuous_map_class`. -/
@[protect_proj]
structure continuous_map (α β : Type*) [topological_space α] [topological_space β] :=
(to_fun             : α → β)
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')

notation `C(` α `, ` β `)` := continuous_map α β

section
set_option old_structure_cmd true
/-- `continuous_map_class F α β` states that `F` is a type of continuous maps.

You should extend this class when you extend `continuous_map`. -/
class continuous_map_class (F : Type*) (α β : out_param $ Type*) [topological_space α]
  [topological_space β]
  extends fun_like F α (λ _, β) :=
(map_continuous (f : F) : continuous f)

end

export continuous_map_class (map_continuous)

attribute [continuity] map_continuous

section continuous_map_class
variables {F α β : Type*} [topological_space α] [topological_space β] [continuous_map_class F α β]
include β

lemma map_continuous_at (f : F) (a : α) : continuous_at f a := (map_continuous f).continuous_at

lemma map_continuous_within_at (f : F) (s : set α) (a : α) : continuous_within_at f s a :=
(map_continuous f).continuous_within_at

instance : has_coe_t F C(α, β) := ⟨λ f, { to_fun := f, continuous_to_fun := map_continuous f }⟩

end continuous_map_class

/-! ### Continuous maps-/

namespace continuous_map
variables {α β γ δ : Type*} [topological_space α] [topological_space β] [topological_space γ]
  [topological_space δ]

instance : continuous_map_class C(α, β) α β :=
{ coe := continuous_map.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_continuous := continuous_map.continuous_to_fun }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (C(α, β)) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : C(α, β)} : f.to_fun = (f : α → β) := rfl

-- this must come after the coe_to_fun definition
initialize_simps_projections continuous_map (to_fun → apply)

@[protected, simp, norm_cast]
lemma coe_coe {F : Type*} [continuous_map_class F α β] (f : F) : ⇑(f : C(α, β)) = f := rfl

@[ext] lemma ext {f g : C(α, β)} (h : ∀ a, f a = g a) : f = g := fun_like.ext _ _ h

/-- Copy of a `continuous_map` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : C(α, β)) (f' : α → β) (h : f' = f) : C(α, β) :=
{ to_fun := f',
  continuous_to_fun := h.symm ▸ f.continuous_to_fun }

@[simp] lemma coe_copy (f : C(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : C(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables {α β} {f g : C(α, β)}

/-- Deprecated. Use `map_continuous` instead. -/
protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun
@[continuity] lemma continuous_set_coe (s : set C(α, β)) (f : s) : continuous f := f.1.continuous

/-- Deprecated. Use `map_continuous_at` instead. -/
protected lemma continuous_at (f : C(α, β)) (x : α) : continuous_at f x :=
f.continuous.continuous_at

/-- Deprecated. Use `fun_like.congr_fun` instead. -/
protected lemma congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x := H ▸ rfl
/-- Deprecated. Use `fun_like.congr_arg` instead. -/
protected lemma congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y := h ▸ rfl

lemma coe_injective : @function.injective (C(α, β)) (α → β) coe_fn :=
λ f g h, by cases f; cases g; congr'

@[simp] lemma coe_mk (f : α → β) (h : continuous f) :
  ⇑(⟨f, h⟩ : C(α, β)) = f := rfl

lemma map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y := h.map f.2

section
variables (α β)

/--
The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
def equiv_fn_of_discrete [discrete_topology α] : C(α, β) ≃ (α → β) :=
⟨(λ f, f), (λ f, ⟨f, continuous_of_discrete_topology⟩),
  λ f, by { ext, refl, }, λ f, by { ext, refl, }⟩

end

variables (α)

/-- The identity as a continuous map. -/
protected def id : C(α, α) := ⟨id⟩

@[simp] lemma coe_id : ⇑(continuous_map.id α) = id := rfl

/-- The constant map as a continuous map. -/
def const (b : β) : C(α, β) := ⟨const α b⟩

@[simp] lemma coe_const (b : β) : ⇑(const α b) = function.const α b := rfl

instance [inhabited β] : inhabited C(α, β) :=
⟨const α default⟩

variables {α}

@[simp] lemma id_apply (a : α) : continuous_map.id α a = a := rfl
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) := ⟨f ∘ g⟩

@[simp] lemma coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g := rfl
@[simp] lemma comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) := rfl
@[simp] lemma comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma id_comp (f : C(α, β)) : (continuous_map.id _).comp f = f := ext $ λ _, rfl
@[simp] lemma comp_id (f : C(α, β)) : f.comp (continuous_map.id _) = f := ext $ λ _, rfl
@[simp] lemma const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c := ext $ λ _, rfl
@[simp] lemma comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b) :=
ext $ λ _, rfl

lemma cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : surjective g) :
  f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
⟨λ h, ext $ hg.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : injective f) :
  f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
⟨λ h, ext $ λ a, hf $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

instance [nonempty α] [nontrivial β] : nontrivial C(α, β) :=
⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β in
    ⟨const _ b₁, const _ b₂, λ h, hb $ fun_like.congr_fun h $ classical.arbitrary α⟩⟩

section prod

variables {α₁ α₂ β₁ β₂ : Type*}
          [topological_space α₁] [topological_space α₂]
          [topological_space β₁] [topological_space β₂]

/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
def prod_mk (f : C(α, β₁)) (g : C(α, β₂)) :
  C(α, β₁ × β₂) :=
{ to_fun := (λ x, (f x, g x)),
  continuous_to_fun := continuous.prod_mk f.continuous g.continuous }

/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
@[simps] def prod_map (f : C(α₁, α₂)) (g : C(β₁, β₂)) :
  C(α₁ × β₁, α₂ × β₂) :=
{ to_fun := prod.map f g,
  continuous_to_fun := continuous.prod_map f.continuous g.continuous }

@[simp] lemma prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) :
  (prod_mk f g) a = (f a, g a) := rfl

end prod

section pi

variables {I A : Type*} {X : I → Type*}
          [topological_space A] [∀ i, topological_space (X i)]

/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : Π i, C(A, X i)) : C(A, Π i, X i) :=
{ to_fun := λ (a : A) (i : I), f i a, }

@[simp] lemma pi_eval (f : Π i, C(A, X i)) (a : A) :
  (pi f) a = λ i : I, (f i) a := rfl

end pi

section restrict

variables (s : set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) := ⟨f ∘ coe⟩

@[simp] lemma coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = f ∘ coe := rfl

@[simp] lemma restrict_apply (f : C(α, β)) (s : set α) (x : s) : f.restrict s x = f x := rfl

@[simp] lemma restrict_apply_mk (f : C(α, β)) (s : set α) (x : α) (hx : x ∈ s) :
  f.restrict s ⟨x, hx⟩ = f x :=
rfl

/-- The restriction of a continuous map to the preimage of a set. -/
@[simps]
def restrict_preimage (f : C(α, β)) (s : set β) : C(f ⁻¹' s, s) :=
⟨s.restrict_preimage f, continuous_iff_continuous_at.mpr $ λ x, f.2.continuous_at.restrict_preimage⟩

end restrict

section gluing

variables {ι : Type*}
  (S : ι → set α)
  (φ : Π i : ι, C(S i, β))
  (hφ : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : ∀ x : α, ∃ i, S i ∈ nhds x)

include hφ hS

/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
noncomputable def lift_cover : C(α, β) :=
begin
  have H : (⋃ i, S i) = set.univ,
  { rw set.eq_univ_iff_forall,
    intros x,
    rw set.mem_Union,
    obtain ⟨i, hi⟩ := hS x,
    exact ⟨i, mem_of_mem_nhds hi⟩ },
  refine ⟨set.lift_cover S (λ i, φ i) hφ H, continuous_subtype_nhds_cover hS _⟩,
  intros i,
  convert (φ i).continuous,
  ext x,
  exact set.lift_cover_coe x,
end

variables {S φ hφ hS}

@[simp] lemma lift_cover_coe {i : ι} (x : S i) : lift_cover S φ hφ hS x = φ i x :=
set.lift_cover_coe _

@[simp] lemma lift_cover_restrict {i : ι} : (lift_cover S φ hφ hS).restrict (S i) = φ i :=
ext $ lift_cover_coe

omit hφ hS

variables (A : set (set α))
  (F : Π (s : set α) (hi : s ∈ A), C(s, β))
  (hF : ∀ s (hs : s ∈ A) t (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
    F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ nhds x)

include hF hA

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def lift_cover' : C(α, β) :=
begin
  let S : A → set α := coe,
  let F : Π i : A, C(i, β) := λ i, F i i.prop,
  refine lift_cover S F (λ i j, hF i i.prop j j.prop) _,
  intros x,
  obtain ⟨s, hs, hsx⟩ := hA x,
  exact ⟨⟨s, hs⟩, hsx⟩
end

variables {A F hF hA}

@[simp] lemma lift_cover_coe' {s : set α} {hs : s ∈ A} (x : s) :
  lift_cover' A F hF hA x = F s hs x :=
let x' : (coe : A → set α) ⟨s, hs⟩ := x in lift_cover_coe x'

@[simp] lemma lift_cover_restrict' {s : set α} {hs : s ∈ A} :
  (lift_cover' A F hF hA).restrict s = F s hs :=
ext $ lift_cover_coe'

end gluing

end continuous_map

namespace homeomorph
variables {α β γ : Type*} [topological_space α] [topological_space β] [topological_space γ]
variables (f : α ≃ₜ β) (g : β ≃ₜ γ)

/-- The forward direction of a homeomorphism, as a bundled continuous map. -/
@[simps]
def to_continuous_map (e : α ≃ₜ β) : C(α, β) := ⟨e⟩

/--`homeomorph.to_continuous_map` as a coercion. -/
instance : has_coe (α ≃ₜ β) C(α, β) := ⟨homeomorph.to_continuous_map⟩

lemma to_continuous_map_as_coe : f.to_continuous_map = f := rfl

@[simp] lemma coe_refl : (homeomorph.refl α : C(α, α)) = continuous_map.id α := rfl

@[simp] lemma coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f := rfl

/-- Left inverse to a continuous map from a homeomorphism, mirroring `equiv.symm_comp_self`. -/
@[simp] lemma symm_comp_to_continuous_map :
  (f.symm : C(β, α)).comp (f : C(α, β)) = continuous_map.id α :=
by rw [← coe_trans, self_trans_symm, coe_refl]

/-- Right inverse to a continuous map from a homeomorphism, mirroring `equiv.self_comp_symm`. -/
@[simp] lemma to_continuous_map_comp_symm :
  (f : C(α, β)).comp (f.symm : C(β, α)) = continuous_map.id β :=
by rw [← coe_trans, symm_trans_self, coe_refl]

end homeomorph
