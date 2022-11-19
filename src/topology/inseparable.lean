/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury G. Kudryashov
-/
import topology.continuous_on
import data.setoid.basic
import tactic.tfae
import order.upper_lower

/-!
# Inseparable points in a topological space

In this file we define

* `specializes` (notation: `x ⤳ y`) : a relation saying that `𝓝 x ≤ 𝓝 y`;

* `inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `inseparable_setoid X`: same relation, as a `setoid`;

* `separation_quotient X`: the quotient of `X` by its `inseparable_setoid`.

We also prove various basic properties of the relation `inseparable`.

## Notations

- `x ⤳ y`: notation for `specializes x y`;
- `x ~ y` is used as a local notation for `inseparable x y`;
- `𝓝 x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/

open set filter function
open_locale topological_space filter

variables {X Y Z α ι : Type*} {π : ι → Type*} [topological_space X] [topological_space Y]
  [topological_space Z] [∀ i, topological_space (π i)] {x y z : X} {s : set X} {f : X → Y}

/-!
### `specializes` relation
-/

/-- `x` specializes to `y` (notation: `x ⤳ y`) if either of the following equivalent properties
hold:

* `𝓝 x ≤ 𝓝 y`; this property is used as the definition;
* `pure x ≤ 𝓝 y`; in other words, any neighbourhood of `y` contains `x`;
* `y ∈ closure {x}`;
* `closure {y} ⊆ closure {x}`;
* for any closed set `s` we have `x ∈ s → y ∈ s`;
* for any open set `s` we have `y ∈ s → x ∈ s`;
* `y` is a cluster point of the filter `pure x = 𝓟 {x}`.

This relation defines a `preorder` on `X`. If `X` is a T₀ space, then this preorder is a partial
order. If `X` is a T₁ space, then this partial order is trivial : `x ⤳ y ↔ x = y`. -/
def specializes (x y : X) : Prop := 𝓝 x ≤ 𝓝 y

infix ` ⤳ `:300 := specializes

/-- A collection of equivalent definitions of `x ⤳ y`. The public API is given by `iff` lemmas
below. -/
lemma specializes_tfae (x y : X) :
  tfae [x ⤳ y,
    pure x ≤ 𝓝 y,
    ∀ s : set X, is_open s → y ∈ s → x ∈ s,
    ∀ s : set X, is_closed s → x ∈ s → y ∈ s,
    y ∈ closure ({x} : set X),
    closure ({y} : set X) ⊆ closure {x},
    cluster_pt y (pure x)] :=
begin
  tfae_have : 1 → 2, from (pure_le_nhds _).trans,
  tfae_have : 2 → 3, from λ h s hso hy, h (hso.mem_nhds hy),
  tfae_have : 3 → 4, from λ h s hsc hx, of_not_not $ λ hy, h sᶜ hsc.is_open_compl hy hx,
  tfae_have : 4 → 5, from λ h, h _ is_closed_closure (subset_closure $ mem_singleton _),
  tfae_have : 6 ↔ 5, from is_closed_closure.closure_subset_iff.trans singleton_subset_iff,
  tfae_have : 5 ↔ 7, by rw [mem_closure_iff_cluster_pt, principal_singleton],
  tfae_have : 5 → 1,
  { refine λ h, (nhds_basis_opens _).ge_iff.2 _,
    rintro s ⟨hy, ho⟩,
    rcases mem_closure_iff.1 h s ho hy with ⟨z, hxs, (rfl : z = x)⟩,
    exact ho.mem_nhds hxs },
  tfae_finish
end

lemma specializes_iff_nhds : x ⤳ y ↔ 𝓝 x ≤ 𝓝 y := iff.rfl
lemma specializes_iff_pure : x ⤳ y ↔ pure x ≤ 𝓝 y := (specializes_tfae x y).out 0 1

alias specializes_iff_nhds ↔ specializes.nhds_le_nhds _
alias specializes_iff_pure ↔ specializes.pure_le_nhds _

lemma specializes_iff_forall_open : x ⤳ y ↔ ∀ s : set X, is_open s → y ∈ s → x ∈ s :=
(specializes_tfae x y).out 0 2

lemma specializes.mem_open (h : x ⤳ y) (hs : is_open s) (hy : y ∈ s) : x ∈ s :=
specializes_iff_forall_open.1 h s hs hy

lemma is_open.not_specializes (hs : is_open s) (hx : x ∉ s) (hy : y ∈ s) : ¬ x ⤳ y :=
λ h, hx $ h.mem_open hs hy

lemma specializes_iff_forall_closed : x ⤳ y ↔ ∀ s : set X, is_closed s → x ∈ s → y ∈ s :=
(specializes_tfae x y).out 0 3

lemma specializes.mem_closed (h : x ⤳ y) (hs : is_closed s) (hx : x ∈ s) : y ∈ s :=
specializes_iff_forall_closed.1 h s hs hx

lemma is_closed.not_specializes (hs : is_closed s) (hx : x ∈ s) (hy : y ∉ s) : ¬ x ⤳ y :=
λ h, hy $ h.mem_closed hs hx

lemma specializes_iff_mem_closure : x ⤳ y ↔ y ∈ closure ({x} : set X) :=
(specializes_tfae x y).out 0 4

alias specializes_iff_mem_closure ↔ specializes.mem_closure _

lemma specializes_iff_closure_subset :
  x ⤳ y ↔ closure ({y} : set X) ⊆ closure {x} :=
(specializes_tfae x y).out 0 5

alias specializes_iff_closure_subset ↔ specializes.closure_subset _

lemma filter.has_basis.specializes_iff {ι} {p : ι → Prop} {s : ι → set X}
  (h : (𝓝 y).has_basis p s) :
  x ⤳ y ↔ ∀ i, p i → x ∈ s i :=
specializes_iff_pure.trans h.ge_iff

lemma specializes_rfl : x ⤳ x := le_rfl

@[refl] lemma specializes_refl (x : X) : x ⤳ x := specializes_rfl

@[trans] lemma specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z := le_trans

lemma specializes_of_nhds_within (h₁ : 𝓝[s] x ≤ 𝓝[s] y) (h₂ : x ∈ s) : x ⤳ y :=
specializes_iff_pure.2 $
calc pure x ≤ 𝓝[s] x : le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
        ... ≤ 𝓝[s] y : h₁
        ... ≤ 𝓝 y    : inf_le_left

lemma specializes.map_of_continuous_at (h : x ⤳ y) (hy : continuous_at f y) : f x ⤳ f y :=
specializes_iff_pure.2 $ λ s hs, mem_pure.2 $ mem_preimage.1 $ mem_of_mem_nhds $ hy.mono_left h hs

lemma specializes.map (h : x ⤳ y) (hf : continuous f) : f x ⤳ f y :=
h.map_of_continuous_at hf.continuous_at

lemma inducing.specializes_iff (hf : inducing f) : f x ⤳ f y ↔ x ⤳ y :=
by simp only [specializes_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
  mem_preimage]

lemma subtype_specializes_iff {p : X → Prop} (x y : subtype p) : x ⤳ y ↔ (x : X) ⤳ y :=
inducing_coe.specializes_iff.symm

@[simp] lemma specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} :
  (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂ :=
by simp only [specializes, nhds_prod_eq, prod_le_prod]

lemma specializes.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂) :
  (x₁, y₁) ⤳ (x₂, y₂) :=
specializes_prod.2 ⟨hx, hy⟩

@[simp] lemma specializes_pi {f g : Π i, π i} : f ⤳ g ↔ ∀ i, f i ⤳ g i :=
by simp only [specializes, nhds_pi, pi_le_pi]

lemma not_specializes_iff_exists_open : ¬ x ⤳ y ↔ ∃ (S : set X), is_open S ∧ y ∈ S ∧ x ∉ S :=
by { rw [specializes_iff_forall_open], push_neg, refl }

lemma not_specializes_iff_exists_closed : ¬ x ⤳ y ↔ ∃ (S : set X), is_closed S ∧ x ∈ S ∧ y ∉ S :=
by { rw [specializes_iff_forall_closed], push_neg, refl }

variable (X)

/-- Specialization forms a preorder on the topological space. -/
def specialization_preorder : preorder X :=
{ le := λ x y, y ⤳ x,
  lt := λ x y, y ⤳ x ∧ ¬(x ⤳ y),
  .. preorder.lift (order_dual.to_dual ∘ 𝓝) }

variable {X}

local attribute [instance] specialization_preorder

/-- A continuous function is monotone with respect to the specialization preorders on the domain and
the codomain. -/
lemma continuous.specialization_monotone (hf : continuous f) : monotone f :=
λ x y h, h.map hf

lemma closure_singleton_eq_Iic (x : X) : closure {x} = Iic x :=
ext $ λ _, specializes_iff_mem_closure.symm

/-- A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `x ⤳ y`. -/
def stable_under_specialization (s : set X) : Prop :=
∀ ⦃x y⦄, x ⤳ y → x ∈ s → y ∈ s

/-- A subset `S` of a topological space is stable under specialization
if `x ∈ S → y ∈ S` for all `y ⤳ x`. -/
def stable_under_generalization (s : set X) : Prop :=
∀ ⦃x y⦄, y ⤳ x → x ∈ s → y ∈ s

example {s : set X} : stable_under_specialization s ↔ is_lower_set s := iff.rfl
example {s : set X} : stable_under_generalization s ↔ is_upper_set s := iff.rfl

lemma is_closed.stable_under_specialization {s : set X} (hs : is_closed s) :
  stable_under_specialization s :=
λ x y e, e.mem_closed hs

lemma is_open.stable_under_generalization {s : set X} (hs : is_open s) :
  stable_under_generalization s :=
λ x y e, e.mem_open hs

@[simp]
lemma stable_under_specialization_compl_iff {s : set X} :
  stable_under_specialization sᶜ ↔ stable_under_generalization s :=
is_lower_set_compl

@[simp]
lemma stable_under_generalization_compl_iff {s : set X} :
  stable_under_generalization sᶜ ↔ stable_under_specialization s :=
is_upper_set_compl

alias stable_under_specialization_compl_iff ↔ _ stable_under_generalization.compl
alias stable_under_generalization_compl_iff ↔ _ stable_under_specialization.compl

lemma stable_under_specialization_sUnion (S : set (set X))
  (H : ∀ s ∈ S, stable_under_specialization s) : stable_under_specialization (⋃₀ S) :=
is_lower_set_sUnion H

lemma stable_under_specialization_sInter (S : set (set X))
  (H : ∀ s ∈ S, stable_under_specialization s) : stable_under_specialization (⋂₀ S) :=
is_lower_set_sInter H

lemma stable_under_generalization_sUnion (S : set (set X))
  (H : ∀ s ∈ S, stable_under_generalization s) : stable_under_generalization (⋃₀ S) :=
is_upper_set_sUnion H

lemma stable_under_generalization_sInter (S : set (set X))
  (H : ∀ s ∈ S, stable_under_generalization s) : stable_under_generalization (⋂₀ S) :=
is_upper_set_sInter H

lemma stable_under_specialization_Union {ι : Sort*} (S : ι → set X)
  (H : ∀ i, stable_under_specialization (S i)) : stable_under_specialization (⋃ i, S i) :=
is_lower_set_Union H

lemma stable_under_specialization_Inter {ι : Sort*} (S : ι → set X)
  (H : ∀ i, stable_under_specialization (S i)) : stable_under_specialization (⋂ i, S i) :=
is_lower_set_Inter H

lemma stable_under_generalization_Union {ι : Sort*} (S : ι → set X)
  (H : ∀ i, stable_under_generalization (S i)) : stable_under_generalization (⋃ i, S i) :=
is_upper_set_Union H

lemma stable_under_generalization_Inter {ι : Sort*} (S : ι → set X)
  (H : ∀ i, stable_under_generalization (S i)) : stable_under_generalization (⋂ i, S i) :=
is_upper_set_Inter H

lemma Union_closure_singleton_eq_iff {s : set X} :
  (⋃ x ∈ s, closure {x}) = s ↔ stable_under_specialization s :=
show _ ↔ is_lower_set s, by simp only [closure_singleton_eq_Iic, ← lower_closure_eq,
  coe_lower_closure_eq_Union_Iic]

lemma stable_under_specialization_iff_eq_Union {s : set X} :
  stable_under_specialization s ↔ (⋃ x ∈ s, closure {x}) = s :=
Union_closure_singleton_eq_iff.symm

alias stable_under_specialization_iff_eq_Union ↔ stable_under_specialization.Union_eq _

/-- A set is stable under specialization iff it is a union of closed sets. -/
lemma stable_under_specialization_iff_exists_sUnion_eq {s : set X} :
  stable_under_specialization s ↔ ∃ (S : set (set X)), (∀ s ∈ S, is_closed s) ∧ ⋃₀ S = s :=
begin
  refine ⟨λ H, ⟨(λ x : X, closure {x}) '' s, _, _⟩, λ ⟨S, hS, e⟩, e ▸
    stable_under_specialization_sUnion S (λ x hx, (hS x hx).stable_under_specialization)⟩,
  { rintros _ ⟨_, _, rfl⟩, exact is_closed_closure },
  { conv_rhs { rw ← H.Union_eq }, simp }
end

/-- A set is stable under generalization iff it is an intersection of open sets. -/
lemma stable_under_generalization_iff_exists_sInter_eq {s : set X} :
  stable_under_generalization s ↔ ∃ (S : set (set X)), (∀ s ∈ S, is_open s) ∧ ⋂₀ S = s :=
begin
  refine ⟨_, λ ⟨S, hS, e⟩, e ▸
    stable_under_generalization_sInter S (λ x hx, (hS x hx).stable_under_generalization)⟩,
  rw [← stable_under_specialization_compl_iff, stable_under_specialization_iff_exists_sUnion_eq],
  exact λ ⟨S, h₁, h₂⟩, ⟨has_compl.compl '' S, λ s ⟨t, ht, e⟩, e ▸ (h₁ t ht).is_open_compl,
    compl_injective ((sUnion_eq_compl_sInter_compl S).symm.trans h₂)⟩
end

lemma stable_under_specialization.preimage {s : set Y}
  (hs : stable_under_specialization s) (hf : continuous f) :
  stable_under_specialization (f ⁻¹' s) :=
is_lower_set.preimage hs hf.specialization_monotone

lemma stable_under_generalization.preimage {s : set Y}
  (hs : stable_under_generalization s) (hf : continuous f) :
  stable_under_generalization (f ⁻¹' s) :=
is_upper_set.preimage hs hf.specialization_monotone

/-- A map `f` between topological spaces is specializing if specializations lifts along `f`,
i.e. for each `f x' ⤳ y` there is some `x` with `x' ⤳ x` whose image is `y`. -/
def specializing_map (f : X → Y) : Prop :=
relation.fibration (flip (⤳)) (flip (⤳)) f

/-- A map `f` between topological spaces is generalizing if generalizations lifts along `f`,
i.e. for each `y ⤳ f x'` there is some `x ⤳ x'` whose image is `y`. -/
def generalizing_map (f : X → Y) : Prop :=
relation.fibration (⤳) (⤳) f

lemma specializing_map_iff_closure_singleton_subset :
  specializing_map f ↔ ∀ x, closure {f x} ⊆ f '' closure {x} :=
by simpa only [specializing_map, relation.fibration, flip, specializes_iff_mem_closure]

alias specializing_map_iff_closure_singleton_subset ↔ specializing_map.closure_singleton_subset _

lemma specializing_map.stable_under_specialization_image (hf : specializing_map f)
  {s : set X} (hs : stable_under_specialization s) : stable_under_specialization (f '' s) :=
is_lower_set.image_fibration hf hs

alias specializing_map.stable_under_specialization_image ← stable_under_specialization.image

lemma specializing_map_iff_image_singleton_stable_under_specialization :
  specializing_map f ↔ ∀ x, stable_under_specialization (f '' closure {x}) :=
by simpa only [closure_singleton_eq_Iic] using relation.fibration_iff_is_lower_set_image_Iic

lemma specializing_map_iff_stable_under_specialization_image :
  specializing_map f ↔ ∀ s, stable_under_specialization s → stable_under_specialization (f '' s) :=
relation.fibration_iff_is_lower_set_image

lemma specializing_map_iff_closure_singleton (hf : continuous f) :
  specializing_map f ↔ ∀ x, f '' closure {x} = closure {f x} :=
by simpa only [closure_singleton_eq_Iic] using
  relation.fibration_iff_image_Iic hf.specialization_monotone

lemma specializing_map_iff_is_closed_image_closure_singleton (hf : continuous f) :
  specializing_map f ↔ ∀ x, is_closed (f '' closure {x}) :=
begin
  refine ⟨λ h x, _, λ h, specializing_map_iff_image_singleton_stable_under_specialization.mpr
    (λ x, (h x).stable_under_specialization)⟩,
  rw (specializing_map_iff_closure_singleton hf).mp h x,
  exact is_closed_closure
end

lemma is_closed_map.specializing_map (hf : is_closed_map f) : specializing_map f :=
specializing_map_iff_image_singleton_stable_under_specialization.mpr $
  λ x, (hf _ is_closed_closure).stable_under_specialization

lemma inducing.specializing_map (hf : inducing f) (h : stable_under_specialization (range f)) :
  specializing_map f :=
by { intros x y e, obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩, exact ⟨_, hf.specializes_iff.mp e, rfl⟩ }

lemma inducing.generalizing_map (hf : inducing f) (h : stable_under_generalization (range f)) :
  generalizing_map f :=
by { intros x y e, obtain ⟨y, rfl⟩ := h e ⟨x, rfl⟩, exact ⟨_, hf.specializes_iff.mp e, rfl⟩ }

lemma open_embedding.generalizing_map (hf : open_embedding f) : generalizing_map f :=
hf.to_inducing.generalizing_map hf.open_range.stable_under_generalization

lemma specializing_map.stable_under_specialization_range (h : specializing_map f) :
  stable_under_specialization (range f) :=
@image_univ _ _ f ▸ is_closed_univ.stable_under_specialization.image h

lemma generalizing_map.stable_under_generalization_image (hf : generalizing_map f) {s : set X}
  (hs : stable_under_generalization s) : stable_under_generalization (f '' s) :=
is_upper_set.image_fibration hf hs

lemma generalizing_map_iff_stable_under_generalization_image :
  generalizing_map f ↔ ∀ s, stable_under_generalization s → stable_under_generalization (f '' s) :=
relation.fibration_iff_is_upper_set_image

alias generalizing_map.stable_under_generalization_image ← stable_under_generalization.image

lemma generalizing_map.stable_under_generalization_range (h : generalizing_map f) :
  stable_under_generalization (range f) :=
@image_univ _ _ f ▸ is_open_univ.stable_under_generalization.image h

/-!
### `inseparable` relation
-/

/-- Two points `x` and `y` in a topological space are `inseparable` if any of the following
equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_open`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_closed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.
-/
def inseparable (x y : X) : Prop := 𝓝 x = 𝓝 y

local infix ` ~ ` := inseparable

lemma inseparable_def : x ~ y ↔ 𝓝 x = 𝓝 y := iff.rfl

lemma inseparable_iff_specializes_and : x ~ y ↔ x ⤳ y ∧ y ⤳ x := le_antisymm_iff

lemma inseparable.specializes (h : x ~ y) : x ⤳ y := h.le

lemma inseparable.specializes' (h : x ~ y) : y ⤳ x := h.ge

lemma specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x ~ y := le_antisymm h₁ h₂

lemma inseparable_iff_forall_open : x ~ y ↔ ∀ s : set X, is_open s → (x ∈ s ↔ y ∈ s) :=
by simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and_distrib,
  ← iff_def, iff.comm]

lemma not_inseparable_iff_exists_open : ¬(x ~ y) ↔ ∃ s : set X, is_open s ∧ xor (x ∈ s) (y ∈ s) :=
by simp [inseparable_iff_forall_open, ← xor_iff_not_iff]

lemma inseparable_iff_forall_closed : x ~ y ↔ ∀ s : set X, is_closed s → (x ∈ s ↔ y ∈ s) :=
by simp only [inseparable_iff_specializes_and, specializes_iff_forall_closed, ← forall_and_distrib,
  ← iff_def]

lemma inseparable_iff_mem_closure :
  x ~ y ↔ x ∈ closure ({y} : set X) ∧ y ∈ closure ({x} : set X) :=
inseparable_iff_specializes_and.trans $ by simp only [specializes_iff_mem_closure, and_comm]

lemma inseparable_iff_closure_eq : x ~ y ↔ closure ({x} : set X) = closure {y} :=
by simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset,
  ← subset_antisymm_iff, eq_comm]

lemma inseparable_of_nhds_within_eq (hx : x ∈ s) (hy : y ∈ s) (h : 𝓝[s] x = 𝓝[s] y) : x ~ y :=
(specializes_of_nhds_within h.le hx).antisymm (specializes_of_nhds_within h.ge hy)

lemma inducing.inseparable_iff (hf : inducing f) : f x ~ f y ↔ x ~ y :=
by simp only [inseparable_iff_specializes_and, hf.specializes_iff]

lemma subtype_inseparable_iff {p : X → Prop} (x y : subtype p) : x ~ y ↔ (x : X) ~ y :=
inducing_coe.inseparable_iff.symm

@[simp] lemma inseparable_prod {x₁ x₂ : X} {y₁ y₂ : Y} :
  (x₁, y₁) ~ (x₂, y₂) ↔ x₁ ~ x₂ ∧ y₁ ~ y₂ :=
by simp only [inseparable, nhds_prod_eq, prod_inj]

lemma inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ x₂) (hy : y₁ ~ y₂) :
  (x₁, y₁) ~ (x₂, y₂) :=
inseparable_prod.2 ⟨hx, hy⟩

@[simp] lemma inseparable_pi {f g : Π i, π i} : f ~ g ↔ ∀ i, f i ~ g i :=
by simp only [inseparable, nhds_pi, funext_iff, pi_inj]

namespace inseparable

@[refl] lemma refl (x : X) : x ~ x := eq.refl (𝓝 x)

lemma rfl : x ~ x := refl x

@[symm] lemma symm (h : x ~ y) : y ~ x := h.symm

@[trans] lemma trans (h₁ : x ~ y) (h₂ : y ~ z) : x ~ z := h₁.trans h₂

lemma nhds_eq (h : x ~ y) : 𝓝 x = 𝓝 y := h

lemma mem_open_iff (h : x ~ y) (hs : is_open s) : x ∈ s ↔ y ∈ s :=
inseparable_iff_forall_open.1 h s hs

lemma mem_closed_iff (h : x ~ y) (hs : is_closed s) : x ∈ s ↔ y ∈ s :=
inseparable_iff_forall_closed.1 h s hs

lemma map_of_continuous_at (h : x ~ y) (hx : continuous_at f x) (hy : continuous_at f y) :
  f x ~ f y :=
(h.specializes.map_of_continuous_at hy).antisymm (h.specializes'.map_of_continuous_at hx)

lemma map (h : x ~ y) (hf : continuous f) : f x ~ f y :=
h.map_of_continuous_at hf.continuous_at hf.continuous_at

end inseparable

lemma is_closed.not_inseparable (hs : is_closed s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ~ y :=
λ h, hy $ (h.mem_closed_iff hs).1 hx

lemma is_open.not_inseparable (hs : is_open s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ~ y :=
λ h, hy $ (h.mem_open_iff hs).1 hx

/-!
### Separation quotient

In this section we define the quotient of a topological space by the `inseparable` relation.
-/

variable (X)

/-- A `setoid` version of `inseparable`, used to define the `separation_quotient`. -/
def inseparable_setoid : setoid X :=
{ r := (~),
  .. setoid.comap 𝓝 ⊥ }

/-- The quotient of a topological space by its `inseparable_setoid`. This quotient is guaranteed to
be a T₀ space. -/
@[derive topological_space]
def separation_quotient := quotient (inseparable_setoid X)

variables {X} {t : set (separation_quotient X)}

namespace separation_quotient

/-- The natural map from a topological space to its separation quotient. -/
def mk : X → separation_quotient X := quotient.mk'

lemma quotient_map_mk : quotient_map (mk : X → separation_quotient X) :=
quotient_map_quot_mk

lemma continuous_mk : continuous (mk : X → separation_quotient X) :=
continuous_quot_mk

@[simp] lemma mk_eq_mk : mk x = mk y ↔ x ~ y := quotient.eq'

lemma surjective_mk : surjective (mk : X → separation_quotient X) :=
surjective_quot_mk _

@[simp] lemma range_mk : range (mk : X → separation_quotient X) = univ :=
surjective_mk.range_eq

instance [nonempty X] : nonempty (separation_quotient X) := nonempty.map mk ‹_›
instance [inhabited X] : inhabited (separation_quotient X) := ⟨mk default⟩
instance [subsingleton X] : subsingleton (separation_quotient X) := surjective_mk.subsingleton

lemma preimage_image_mk_open (hs : is_open s) : mk ⁻¹' (mk '' s) = s :=
begin
  refine subset.antisymm _ (subset_preimage_image _ _),
  rintro x ⟨y, hys, hxy⟩,
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys
end

lemma is_open_map_mk : is_open_map (mk : X → separation_quotient X) :=
λ s hs, quotient_map_mk.is_open_preimage.1 $ by rwa preimage_image_mk_open hs

lemma preimage_image_mk_closed (hs : is_closed s) : mk ⁻¹' (mk '' s) = s :=
begin
  refine subset.antisymm _ (subset_preimage_image _ _),
  rintro x ⟨y, hys, hxy⟩,
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys
end

lemma inducing_mk : inducing (mk : X → separation_quotient X) :=
⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk)
  (λ s hs, ⟨mk '' s, is_open_map_mk s hs, preimage_image_mk_open hs⟩)⟩

lemma is_closed_map_mk : is_closed_map (mk : X → separation_quotient X) :=
inducing_mk.is_closed_map $ by { rw [range_mk], exact is_closed_univ }

@[simp] lemma comap_mk_nhds_mk : comap mk (𝓝 (mk x)) = 𝓝 x :=
(inducing_mk.nhds_eq_comap _).symm

@[simp] lemma comap_mk_nhds_set_image : comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s :=
(inducing_mk.nhds_set_eq_comap _).symm

lemma map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x) :=
by rw [← comap_mk_nhds_mk, map_comap_of_surjective surjective_mk]

lemma map_mk_nhds_set : map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s) :=
by rw [← comap_mk_nhds_set_image, map_comap_of_surjective surjective_mk]

lemma comap_mk_nhds_set : comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t) :=
by conv_lhs { rw [← image_preimage_eq t surjective_mk, comap_mk_nhds_set_image] }

lemma preimage_mk_closure : mk ⁻¹' (closure t) = closure (mk ⁻¹' t) :=
is_open_map_mk.preimage_closure_eq_closure_preimage continuous_mk t

lemma preimage_mk_interior : mk ⁻¹' (interior t) = interior (mk ⁻¹' t) :=
is_open_map_mk.preimage_interior_eq_interior_preimage continuous_mk t

lemma preimage_mk_frontier : mk ⁻¹' (frontier t) = frontier (mk ⁻¹' t) :=
is_open_map_mk.preimage_frontier_eq_frontier_preimage continuous_mk t

lemma image_mk_closure : mk '' closure s = closure (mk '' s) :=
(image_closure_subset_closure_image continuous_mk).antisymm $
  is_closed_map_mk.closure_image_subset _

end separation_quotient
