/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import topology.algebra.constructions
import topology.homeomorph
import group_theory.group_action.basic
import topology.bases
import topology.support

/-!
# Monoid actions continuous in the second variable

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define class `has_continuous_const_smul`. We say `has_continuous_const_smul Γ T` if
`Γ` acts on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`has_continuous_smul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `has_continuous_const_smul Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `properly_discontinuous_smul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.

## Main results

* `is_open_map_quotient_mk_mul` : The quotient map by a group action is open.
* `t2_space_of_properly_discontinuous_smul_of_t2_space` : The quotient by a discontinuous group
  action of a locally compact t2 space is t2.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/

open_locale topology pointwise

open filter set topological_space

local attribute [instance] mul_action.orbit_rel

/-- Class `has_continuous_const_smul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras.

Note that both `has_continuous_const_smul α α` and `has_continuous_const_smul αᵐᵒᵖ α` are
weaker versions of `has_continuous_mul α`. -/
class has_continuous_const_smul (Γ : Type*) (T : Type*) [topological_space T] [has_smul Γ T]
 : Prop :=
(continuous_const_smul : ∀ γ : Γ, continuous (λ x : T, γ • x))

/-- Class `has_continuous_const_vadd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of additive actions,
including (semi)modules and algebras.

Note that both `has_continuous_const_vadd α α` and `has_continuous_const_vadd αᵐᵒᵖ α` are
weaker versions of `has_continuous_add α`. -/
class has_continuous_const_vadd (Γ : Type*) (T : Type*) [topological_space T]
  [has_vadd Γ T] : Prop :=
(continuous_const_vadd : ∀ γ : Γ, continuous (λ x : T, γ +ᵥ x))

attribute [to_additive] has_continuous_const_smul

export has_continuous_const_smul (continuous_const_smul)

export has_continuous_const_vadd (continuous_const_vadd)

variables {M α β : Type*}

section has_smul
variables [topological_space α] [has_smul M α] [has_continuous_const_smul M α]

@[to_additive]
lemma filter.tendsto.const_smul {f : β → α} {l : filter β} {a : α} (hf : tendsto f l (𝓝 a))
  (c : M) :
  tendsto (λ x, c • f x) l (𝓝 (c • a)) :=
((continuous_const_smul _).tendsto _).comp hf

variables [topological_space β] {f : β → M} {g : β → α} {b : β} {s : set β}

@[to_additive]
lemma continuous_within_at.const_smul (hg : continuous_within_at g s b) (c : M) :
  continuous_within_at (λ x, c • g x) s b :=
hg.const_smul c

@[to_additive]
lemma continuous_at.const_smul (hg : continuous_at g b) (c : M) :
  continuous_at (λ x, c • g x) b :=
hg.const_smul c

@[to_additive]
lemma continuous_on.const_smul (hg : continuous_on g s) (c : M) :
  continuous_on (λ x, c • g x) s :=
λ x hx, (hg x hx).const_smul c

@[continuity, to_additive]
lemma continuous.const_smul (hg : continuous g) (c : M) :
  continuous (λ x, c • g x) :=
(continuous_const_smul _).comp hg

/-- If a scalar is central, then its right action is continuous when its left action is. -/
@[to_additive "If an additive action is central, then its right action is continuous when its left
action is."]
instance has_continuous_const_smul.op [has_smul Mᵐᵒᵖ α] [is_central_scalar M α] :
  has_continuous_const_smul Mᵐᵒᵖ α :=
⟨ mul_opposite.rec $ λ c, by simpa only [op_smul_eq_smul] using continuous_const_smul c ⟩

@[to_additive] instance mul_opposite.has_continuous_const_smul :
  has_continuous_const_smul M αᵐᵒᵖ :=
⟨λ c, mul_opposite.continuous_op.comp $ mul_opposite.continuous_unop.const_smul c⟩

@[to_additive] instance : has_continuous_const_smul M αᵒᵈ := ‹has_continuous_const_smul M α›

@[to_additive] instance order_dual.has_continuous_const_smul' : has_continuous_const_smul Mᵒᵈ α :=
‹has_continuous_const_smul M α›

@[to_additive]
instance [has_smul M β] [has_continuous_const_smul M β] :
  has_continuous_const_smul M (α × β) :=
⟨λ _, (continuous_fst.const_smul _).prod_mk (continuous_snd.const_smul _)⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*} [∀ i, topological_space (γ i)] [Π i, has_smul M (γ i)]
  [∀ i, has_continuous_const_smul M (γ i)] : has_continuous_const_smul M (Π i, γ i) :=
⟨λ _, continuous_pi $ λ i, (continuous_apply i).const_smul _⟩

@[to_additive]
lemma is_compact.smul {α β} [has_smul α β] [topological_space β]
  [has_continuous_const_smul α β] (a : α) {s : set β}
  (hs : is_compact s) : is_compact (a • s) := hs.image (continuous_id'.const_smul a)

end has_smul

section monoid

variables [topological_space α]
variables [monoid M] [mul_action M α] [has_continuous_const_smul M α]

@[to_additive] instance units.has_continuous_const_smul : has_continuous_const_smul Mˣ α :=
{ continuous_const_smul := λ m, (continuous_const_smul (m : M) : _) }

@[to_additive]
lemma smul_closure_subset (c : M) (s : set α) : c • closure s ⊆ closure (c • s) :=
((set.maps_to_image _ _).closure $ continuous_id.const_smul c).image_subset

@[to_additive]
lemma smul_closure_orbit_subset (c : M) (x : α) :
  c • closure (mul_action.orbit M x) ⊆ closure (mul_action.orbit M x) :=
(smul_closure_subset c _).trans $ closure_mono $ mul_action.smul_orbit_subset _ _

end monoid

section group

variables {G : Type*} [topological_space α] [group G] [mul_action G α]
  [has_continuous_const_smul G α]

@[to_additive]
lemma tendsto_const_smul_iff {f : β → α} {l : filter β} {a : α} (c : G) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
⟨λ h, by simpa only [inv_smul_smul] using h.const_smul c⁻¹,
  λ h, h.const_smul _⟩

variables [topological_space β] {f : β → α} {b : β}  {s : set β}

@[to_additive]
lemma continuous_within_at_const_smul_iff (c : G) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
tendsto_const_smul_iff c

@[to_additive]
lemma continuous_on_const_smul_iff (c : G) : continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
forall₂_congr $ λ b hb, continuous_within_at_const_smul_iff c

@[to_additive]
lemma continuous_at_const_smul_iff (c : G) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
tendsto_const_smul_iff c

@[to_additive]
lemma continuous_const_smul_iff (c : G) :
  continuous (λ x, c • f x) ↔ continuous f :=
by simp only [continuous_iff_continuous_at, continuous_at_const_smul_iff]

/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
@[to_additive] def homeomorph.smul (γ : G) : α ≃ₜ α :=
{ to_equiv := mul_action.to_perm γ,
  continuous_to_fun  := continuous_const_smul γ,
  continuous_inv_fun := continuous_const_smul γ⁻¹ }

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
add_decl_doc homeomorph.vadd

@[to_additive]
lemma is_open_map_smul (c : G) : is_open_map (λ x : α, c • x) :=
(homeomorph.smul c).is_open_map

@[to_additive] lemma is_open.smul {s : set α} (hs : is_open s) (c : G) : is_open (c • s) :=
is_open_map_smul c s hs

@[to_additive]
lemma is_closed_map_smul (c : G) : is_closed_map (λ x : α, c • x) :=
(homeomorph.smul c).is_closed_map

@[to_additive] lemma is_closed.smul {s : set α} (hs : is_closed s) (c : G) : is_closed (c • s) :=
is_closed_map_smul c s hs

@[to_additive] lemma closure_smul (c : G) (s : set α) : closure (c • s) = c • closure s :=
((homeomorph.smul c).image_closure s).symm

@[to_additive] lemma dense.smul (c : G) {s : set α} (hs : dense s) : dense (c • s) :=
by rw [dense_iff_closure_eq] at ⊢ hs; rw [closure_smul, hs, smul_set_univ]

@[to_additive] lemma interior_smul (c : G) (s : set α) : interior (c • s) = c • interior s :=
((homeomorph.smul c).image_interior s).symm

end group

section group_with_zero

variables {G₀ : Type*} [topological_space α] [group_with_zero G₀] [mul_action G₀ α]
  [has_continuous_const_smul G₀ α]

lemma tendsto_const_smul_iff₀ {f : β → α} {l : filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
tendsto_const_smul_iff (units.mk0 c hc)

variables [topological_space β] {f : β → α} {b : β} {c : G₀} {s : set β}

lemma continuous_within_at_const_smul_iff₀ (hc : c ≠ 0) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
tendsto_const_smul_iff (units.mk0 c hc)

lemma continuous_on_const_smul_iff₀ (hc : c ≠ 0) :
  continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
continuous_on_const_smul_iff (units.mk0 c hc)

lemma continuous_at_const_smul_iff₀ (hc : c ≠ 0) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
continuous_at_const_smul_iff (units.mk0 c hc)

lemma continuous_const_smul_iff₀ (hc : c ≠ 0) :
  continuous (λ x, c • f x) ↔ continuous f :=
continuous_const_smul_iff (units.mk0 c hc)

/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
protected def homeomorph.smul_of_ne_zero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
homeomorph.smul (units.mk0 c hc)

lemma is_open_map_smul₀ {c : G₀} (hc : c ≠ 0) : is_open_map (λ x : α, c • x) :=
(homeomorph.smul_of_ne_zero c hc).is_open_map

lemma is_open.smul₀ {c : G₀} {s : set α} (hs : is_open s) (hc : c ≠ 0) : is_open (c • s) :=
is_open_map_smul₀ hc s hs

lemma interior_smul₀ {c : G₀} (hc : c ≠ 0) (s : set α) : interior (c • s) = c • interior s :=
((homeomorph.smul_of_ne_zero c hc).image_interior s).symm

lemma closure_smul₀ {E} [has_zero E] [mul_action_with_zero G₀ E] [topological_space E]
  [t1_space E] [has_continuous_const_smul G₀ E] (c : G₀) (s : set E) :
  closure (c • s) = c • closure s :=
begin
  rcases eq_or_ne c 0 with rfl|hc,
  { rcases eq_empty_or_nonempty s with rfl|hs,
    { simp },
    { rw [zero_smul_set hs, zero_smul_set hs.closure], exact closure_singleton } },
  { exact ((homeomorph.smul_of_ne_zero c hc).image_closure s).symm }
end

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
lemma is_closed_map_smul_of_ne_zero {c : G₀} (hc : c ≠ 0) : is_closed_map (λ x : α, c • x) :=
(homeomorph.smul_of_ne_zero c hc).is_closed_map

lemma is_closed.smul_of_ne_zero {c : G₀} {s : set α} (hs : is_closed s) (hc : c ≠ 0) :
  is_closed (c • s) :=
is_closed_map_smul_of_ne_zero hc s hs

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
lemma is_closed_map_smul₀ {𝕜 M : Type*} [division_ring 𝕜] [add_comm_monoid M] [topological_space M]
  [t1_space M] [module 𝕜 M] [has_continuous_const_smul 𝕜 M] (c : 𝕜) :
  is_closed_map (λ x : M, c • x) :=
begin
  rcases eq_or_ne c 0 with (rfl|hne),
  { simp only [zero_smul], exact is_closed_map_const },
  { exact (homeomorph.smul_of_ne_zero c hne).is_closed_map },
end

lemma is_closed.smul₀ {𝕜 M : Type*} [division_ring 𝕜] [add_comm_monoid M] [topological_space M]
  [t1_space M] [module 𝕜 M] [has_continuous_const_smul 𝕜 M] (c : 𝕜) {s : set M} (hs : is_closed s) :
  is_closed (c • s) :=
is_closed_map_smul₀ c s hs

lemma has_compact_mul_support.comp_smul {β : Type*} [has_one β] {f : α → β}
  (h : has_compact_mul_support f) {c : G₀} (hc : c ≠ 0) :
  has_compact_mul_support (λ x, f (c • x)) :=
h.comp_homeomorph (homeomorph.smul_of_ne_zero c hc)

lemma has_compact_support.comp_smul {β : Type*} [has_zero β] {f : α → β}
  (h : has_compact_support f) {c : G₀} (hc : c ≠ 0) :
  has_compact_support (λ x, f (c • x)) :=
h.comp_homeomorph (homeomorph.smul_of_ne_zero c hc)

attribute [to_additive has_compact_support.comp_smul] has_compact_mul_support.comp_smul

end group_with_zero

namespace is_unit

variables [monoid M] [topological_space α] [mul_action M α] [has_continuous_const_smul M α]

lemma tendsto_const_smul_iff {f : β → α} {l : filter β} {a : α} {c : M} (hc : is_unit c) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
let ⟨u, hu⟩ := hc in hu ▸ tendsto_const_smul_iff u

variables [topological_space β] {f : β → α} {b : β} {c : M} {s : set β}

lemma continuous_within_at_const_smul_iff (hc : is_unit c) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
let ⟨u, hu⟩ := hc in hu ▸ continuous_within_at_const_smul_iff u

lemma continuous_on_const_smul_iff (hc : is_unit c) :
  continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
let ⟨u, hu⟩ := hc in hu ▸ continuous_on_const_smul_iff u

lemma continuous_at_const_smul_iff (hc : is_unit c) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
let ⟨u, hu⟩ := hc in hu ▸ continuous_at_const_smul_iff u

lemma continuous_const_smul_iff (hc : is_unit c) :
  continuous (λ x, c • f x) ↔ continuous f :=
let ⟨u, hu⟩ := hc in hu ▸ continuous_const_smul_iff u

lemma is_open_map_smul (hc : is_unit c) : is_open_map (λ x : α, c • x) :=
let ⟨u, hu⟩ := hc in hu ▸ is_open_map_smul u

lemma is_closed_map_smul (hc : is_unit c) : is_closed_map (λ x : α, c • x) :=
let ⟨u, hu⟩ := hc in hu ▸ is_closed_map_smul u

end is_unit

/-- Class `properly_discontinuous_smul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class properly_discontinuous_smul (Γ : Type*) (T : Type*) [topological_space T]
  [has_smul Γ T] : Prop :=
(finite_disjoint_inter_image : ∀ {K L : set T}, is_compact K → is_compact L →
  set.finite {γ : Γ | (((•) γ) '' K) ∩ L ≠ ∅ })

/-- Class `properly_discontinuous_vadd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class properly_discontinuous_vadd (Γ : Type*) (T : Type*) [topological_space T]
  [has_vadd Γ T] : Prop :=
(finite_disjoint_inter_image : ∀ {K L : set T}, is_compact K → is_compact L →
  set.finite {γ : Γ | (((+ᵥ) γ) '' K) ∩ L ≠ ∅ })

attribute [to_additive] properly_discontinuous_smul

variables {Γ : Type*} [group Γ] {T : Type*} [topological_space T] [mul_action Γ T]

/-- A finite group action is always properly discontinuous. -/
@[priority 100, to_additive "A finite group action is always properly discontinuous."]
instance finite.to_properly_discontinuous_smul [finite Γ] : properly_discontinuous_smul Γ T :=
{ finite_disjoint_inter_image := λ _ _ _ _, set.to_finite _}

export properly_discontinuous_smul (finite_disjoint_inter_image)

export properly_discontinuous_vadd (finite_disjoint_inter_image)

/-- The quotient map by a group action is open, i.e. the quotient by a group action is an open
  quotient. -/
@[to_additive "The quotient map by a group action is open, i.e. the quotient by a group
action is an open quotient. "]
lemma is_open_map_quotient_mk_mul [has_continuous_const_smul Γ T] :
  is_open_map (quotient.mk : T → quotient (mul_action.orbit_rel Γ T)) :=
begin
  intros U hU,
  rw [is_open_coinduced, mul_action.quotient_preimage_image_eq_union_mul U],
  exact is_open_Union (λ γ, (homeomorph.smul γ).is_open_map U hU)
end

/-- The quotient by a discontinuous group action of a locally compact t2 space is t2. -/
@[priority 100, to_additive "The quotient by a discontinuous group action of a locally compact t2
space is t2."]
instance t2_space_of_properly_discontinuous_smul_of_t2_space [t2_space T] [locally_compact_space T]
  [has_continuous_const_smul Γ T] [properly_discontinuous_smul Γ T] :
  t2_space (quotient (mul_action.orbit_rel Γ T)) :=
begin
  set Q := quotient (mul_action.orbit_rel Γ T),
  rw t2_space_iff_nhds,
  let f : T → Q := quotient.mk,
  have f_op : is_open_map f := is_open_map_quotient_mk_mul,
  rintros ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ ≠ f y₀),
  show ∃ (U ∈ 𝓝 (f x₀)) (V ∈ 𝓝 (f y₀)), _,
  have hx₀y₀ : x₀ ≠ y₀ := ne_of_apply_ne _ hxy,
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀ := not_exists.mp (mt quotient.sound hxy.symm : _),
  obtain ⟨K₀, L₀, K₀_in, L₀_in, hK₀, hL₀, hK₀L₀⟩ := t2_separation_compact_nhds hx₀y₀,
  let bad_Γ_set := {γ : Γ | (((•) γ) '' K₀) ∩ L₀ ≠ ∅ },
  have bad_Γ_finite : bad_Γ_set.finite := finite_disjoint_inter_image hK₀ hL₀,
  choose u v hu hv u_v_disjoint using λ γ, t2_separation_nhds (hγx₀y₀ γ),
  let U₀₀ := ⋂ γ ∈ bad_Γ_set, ((•) γ) ⁻¹' (u γ),
  let U₀ := U₀₀ ∩ K₀,
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, v γ,
  let V₀ := V₀₀ ∩ L₀,
  have U_nhds : f '' U₀ ∈ 𝓝 (f x₀),
  { apply f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr $ λ γ hγ, _) K₀_in),
    exact (continuous_const_smul _).continuous_at (hu γ) },
  have V_nhds : f '' V₀ ∈ 𝓝 (f y₀),
    from f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr $ λ γ hγ, hv γ) L₀_in),
  refine ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, mul_action.disjoint_image_image_iff.2 _⟩,
  rintros x ⟨x_in_U₀₀, x_in_K₀⟩ γ,
  by_cases H : γ ∈ bad_Γ_set,
  { exact λ h, (u_v_disjoint γ).le_bot ⟨mem_Inter₂.mp x_in_U₀₀ γ H, mem_Inter₂.mp h.1 γ H⟩ },
  { rintros ⟨-, h'⟩,
    simp only [image_smul, not_not, mem_set_of_eq, ne.def] at H,
    exact eq_empty_iff_forall_not_mem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩ },
end

/-- The quotient of a second countable space by a group action is second countable. -/
@[to_additive "The quotient of a second countable space by an additive group action is second
countable."]
theorem has_continuous_const_smul.second_countable_topology [second_countable_topology T]
  [has_continuous_const_smul Γ T] :
  second_countable_topology (quotient (mul_action.orbit_rel Γ T)) :=
topological_space.quotient.second_countable_topology is_open_map_quotient_mk_mul

section nhds

section mul_action

variables {G₀ : Type*} [group_with_zero G₀] [mul_action G₀ α]
  [topological_space α] [has_continuous_const_smul G₀ α]

/-- Scalar multiplication preserves neighborhoods. -/
lemma set_smul_mem_nhds_smul {c : G₀} {s : set α} {x : α} (hs : s ∈ 𝓝 x) (hc : c ≠ 0) :
  c • s ∈ 𝓝 (c • x : α) :=
begin
  rw mem_nhds_iff at hs ⊢,
  obtain ⟨U, hs', hU, hU'⟩ := hs,
  exact ⟨c • U, set.smul_set_mono hs', hU.smul₀ hc, set.smul_mem_smul_set hU'⟩,
end

lemma set_smul_mem_nhds_smul_iff {c : G₀} {s : set α} {x : α} (hc : c ≠ 0) :
  c • s ∈ 𝓝 (c • x : α) ↔ s ∈ 𝓝 x :=
begin
  refine ⟨λ h, _, λ h, set_smul_mem_nhds_smul h hc⟩,
  rw [←inv_smul_smul₀ hc x, ←inv_smul_smul₀ hc s],
  exact set_smul_mem_nhds_smul h (inv_ne_zero hc),
end

end mul_action

section distrib_mul_action

variables {G₀ : Type*} [group_with_zero G₀] [add_monoid α] [distrib_mul_action G₀ α]
  [topological_space α] [has_continuous_const_smul G₀ α]

lemma set_smul_mem_nhds_zero_iff {s : set α} {c : G₀} (hc : c ≠ 0) :
  c • s ∈ 𝓝 (0 : α) ↔ s ∈ 𝓝 (0 : α) :=
begin
  refine iff.trans _ (set_smul_mem_nhds_smul_iff hc),
  rw smul_zero,
end

end distrib_mul_action

end nhds
