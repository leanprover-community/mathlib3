/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import data.set.Union_lift
import topology.homeomorph

/-!
# Continuous bundled map

In this file we define the type `continuous_map` of continuous bundled maps.
-/

/-- Bundled continuous maps. -/
@[protect_proj]
structure continuous_map (α : Type*) (β : Type*)
[topological_space α] [topological_space β] :=
(to_fun             : α → β)
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')

notation `C(` α `, ` β `)` := continuous_map α β

namespace continuous_map

attribute [continuity] continuous_map.continuous_to_fun

variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

instance : has_coe_to_fun (C(α, β)) (λ _, α → β) := ⟨continuous_map.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : C(α, β)} : f.to_fun = (f : α → β) := rfl

variables {α β} {f g : continuous_map α β}

@[continuity] protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun
@[continuity] lemma continuous_set_coe (s : set C(α, β)) (f : s) : continuous f :=
by { cases f, rw @coe_fn_coe_base', continuity }

protected lemma continuous_at (f : C(α, β)) (x : α) : continuous_at f x :=
f.continuous.continuous_at

protected lemma continuous_within_at (f : C(α, β)) (s : set α) (x : α) :
  continuous_within_at f s x :=
f.continuous.continuous_within_at

protected lemma congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x := H ▸ rfl
protected lemma congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y := h ▸ rfl

@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

lemma ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨continuous_map.congr_fun, ext⟩

instance [inhabited β] : inhabited C(α, β) :=
⟨{ to_fun := λ _, default, }⟩

lemma coe_inj ⦃f g : C(α, β)⦄ (h : (f : α → β) = g) : f = g :=
by cases f; cases g; cases h; refl

@[simp] lemma coe_mk (f : α → β) (h : continuous f) :
  ⇑(⟨f, h⟩ : continuous_map α β) = f := rfl

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

/-- The identity as a continuous map. -/
def id : C(α, α) := ⟨id⟩

@[simp] lemma id_coe : (id : α → α) = _root_.id := rfl
lemma id_apply (a : α) : id a = a := rfl

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) := ⟨f ∘ g⟩

@[simp] lemma comp_coe (f : C(β, γ)) (g : C(α, β)) : (comp f g : α → γ) = f ∘ g := rfl
lemma comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) := rfl

@[simp] lemma id_comp (f : C(β, γ)) : id.comp f = f := by { ext, refl }
@[simp] lemma comp_id (f : C(α, β)) : f.comp id = f := by { ext, refl }

/-- Constant map as a continuous map -/
def const (b : β) : C(α, β) := ⟨λ x, b⟩

@[simp] lemma const_coe (b : β) : (const b : α → β) = (λ x, b) := rfl
lemma const_apply (b : β) (a : α) : const b a = b := rfl

instance [h : nonempty α] [nontrivial β] : nontrivial C(α, β) :=
{ exists_pair_ne := begin
    obtain ⟨b₁, b₂, hb⟩ := exists_pair_ne β,
    refine ⟨const b₁, const b₂, _⟩,
    contrapose! hb,
    change const b₁ h.some = const b₂ h.some,
    simp [hb]
  end }

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
def prod_map (f : C(α₁, α₂)) (g : C(β₁, β₂)) :
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

/--
The forward direction of a homeomorphism, as a bundled continuous map.
-/
@[simps]
def homeomorph.to_continuous_map {α β : Type*} [topological_space α] [topological_space β]
  (e : α ≃ₜ β) : C(α, β) := ⟨e⟩
