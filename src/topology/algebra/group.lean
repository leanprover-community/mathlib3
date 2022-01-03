/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import group_theory.quotient_group
import order.filter.pointwise
import topology.algebra.monoid
import topology.homeomorph
import topology.compacts

/-!
# Theory of topological groups

This file defines the following typeclasses:

* `topological_group`, `topological_add_group`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `has_continuous_sub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `has_continuous_sub` from `topological_group` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `homeomorph` versions of several `equiv`s: `homeomorph.mul_left`,
`homeomorph.mul_right`, `homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/

open classical set filter topological_space function
open_locale classical topological_space filter pointwise

universes u v w x
variables {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section continuous_mul_group

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/

variables [topological_space G] [group G] [has_continuous_mul G]

/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive "Addition from the left in a topological additive group as a homeomorphism."]
protected def homeomorph.mul_left (a : G) : G ≃ₜ G :=
{ continuous_to_fun  := continuous_const.mul continuous_id,
  continuous_inv_fun := continuous_const.mul continuous_id,
  .. equiv.mul_left a }

@[simp, to_additive]
lemma homeomorph.coe_mul_left (a : G) : ⇑(homeomorph.mul_left a) = (*) a := rfl

@[to_additive]
lemma homeomorph.mul_left_symm (a : G) : (homeomorph.mul_left a).symm = homeomorph.mul_left a⁻¹ :=
by { ext, refl }

@[to_additive]
lemma is_open_map_mul_left (a : G) : is_open_map (λ x, a * x) :=
(homeomorph.mul_left a).is_open_map

@[to_additive]
lemma is_closed_map_mul_left (a : G) : is_closed_map (λ x, a * x) :=
(homeomorph.mul_left a).is_closed_map

/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive "Addition from the right in a topological additive group as a homeomorphism."]
protected def homeomorph.mul_right (a : G) :
  G ≃ₜ G :=
{ continuous_to_fun  := continuous_id.mul continuous_const,
  continuous_inv_fun := continuous_id.mul continuous_const,
  .. equiv.mul_right a }

@[simp, to_additive]
lemma homeomorph.coe_mul_right (a : G) : ⇑(homeomorph.mul_right a) = λ g, g * a := rfl

@[to_additive]
lemma homeomorph.mul_right_symm (a : G) :
  (homeomorph.mul_right a).symm = homeomorph.mul_right a⁻¹ :=
by { ext, refl }

@[to_additive]
lemma is_open_map_mul_right (a : G) : is_open_map (λ x, x * a) :=
(homeomorph.mul_right a).is_open_map

@[to_additive]
lemma is_closed_map_mul_right (a : G) : is_closed_map (λ x, x * a) :=
(homeomorph.mul_right a).is_closed_map

@[to_additive]
lemma is_open_map_div_right (a : G) : is_open_map (λ x, x / a) :=
by simpa only [div_eq_mul_inv] using is_open_map_mul_right (a⁻¹)

@[to_additive]
lemma is_closed_map_div_right (a : G) : is_closed_map (λ x, x / a) :=
by simpa only [div_eq_mul_inv] using is_closed_map_mul_right (a⁻¹)

@[to_additive]
lemma discrete_topology_of_open_singleton_one (h : is_open ({1} : set G)) : discrete_topology G :=
begin
  rw ← singletons_open_iff_discrete,
  intro g,
  suffices : {g} = (λ (x : G), g⁻¹ * x) ⁻¹' {1},
  { rw this, exact (continuous_mul_left (g⁻¹)).is_open_preimage _ h, },
  simp only [mul_one, set.preimage_mul_left_singleton, eq_self_iff_true,
    inv_inv, set.singleton_eq_singleton_iff],
end

@[to_additive]
lemma discrete_topology_iff_open_singleton_one : discrete_topology G ↔ is_open ({1} : set G) :=
⟨λ h, forall_open_iff_discrete.mpr h {1}, discrete_topology_of_open_singleton_one⟩

end continuous_mul_group

/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `submonoid.top_closure_mul_self_eq` in
`topology.algebra.monoid`.
-/

section pointwise
variables [topological_space α] [group α] [has_continuous_mul α] {s t : set α}

@[to_additive]
lemma is_open.mul_left (ht : is_open t) :  is_open (s * t) :=
begin
  rw ←Union_mul_left_image,
  exact is_open_Union (λ a, is_open_Union $ λ ha, is_open_map_mul_left a t ht),
end

@[to_additive]
lemma is_open.mul_right (hs : is_open s) : is_open (s * t) :=
begin
  rw ←Union_mul_right_image,
  exact is_open_Union (λ a, is_open_Union $ λ ha, is_open_map_mul_right a s hs),
end

@[to_additive]
lemma subset_interior_mul_left : interior s * t ⊆ interior (s * t) :=
interior_maximal (set.mul_subset_mul_right interior_subset) is_open_interior.mul_right

@[to_additive]
lemma subset_interior_mul_right : s * interior t ⊆ interior (s * t) :=
interior_maximal (set.mul_subset_mul_left interior_subset) is_open_interior.mul_left

@[to_additive]
lemma subset_interior_mul : interior s * interior t ⊆ interior (s * t) :=
(set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

end pointwise

section topological_group

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `λ x y, x * y⁻¹` (resp., subtraction) is continuous.
-/

/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class topological_add_group (G : Type u) [topological_space G] [add_group G]
  extends has_continuous_add G : Prop :=
(continuous_neg : continuous (λa:G, -a))

/-- A topological group is a group in which the multiplication and inversion operations are
continuous. -/
@[to_additive]
class topological_group (G : Type*) [topological_space G] [group G]
  extends has_continuous_mul G : Prop :=
(continuous_inv : continuous (has_inv.inv : G → G))

variables [topological_space G] [group G] [topological_group G]

export topological_group (continuous_inv)
export topological_add_group (continuous_neg)

@[to_additive]
lemma continuous_on_inv {s : set G} : continuous_on has_inv.inv s :=
continuous_inv.continuous_on

@[to_additive]
lemma continuous_within_at_inv {s : set G} {x : G} : continuous_within_at has_inv.inv s x :=
continuous_inv.continuous_within_at

@[to_additive]
lemma continuous_at_inv {x : G} : continuous_at has_inv.inv x :=
continuous_inv.continuous_at

@[to_additive]
lemma tendsto_inv (a : G) : tendsto has_inv.inv (𝓝 a) (𝓝 (a⁻¹)) :=
continuous_at_inv

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `tendsto.inv'`. -/
@[to_additive]
lemma filter.tendsto.inv {f : α → G} {l : filter α} {y : G} (h : tendsto f l (𝓝 y)) :
  tendsto (λ x, (f x)⁻¹) l (𝓝 y⁻¹) :=
(continuous_inv.tendsto y).comp h

variables [topological_space α] {f : α → G} {s : set α} {x : α}

@[continuity, to_additive]
lemma continuous.inv (hf : continuous f) : continuous (λx, (f x)⁻¹) :=
continuous_inv.comp hf

@[to_additive]
lemma continuous_at.inv (hf : continuous_at f x) : continuous_at (λ x, (f x)⁻¹) x :=
continuous_at_inv.comp hf

@[to_additive]
lemma continuous_on.inv (hf : continuous_on f s) : continuous_on (λx, (f x)⁻¹) s :=
continuous_inv.comp_continuous_on hf

@[to_additive]
lemma continuous_within_at.inv (hf : continuous_within_at f s x) :
  continuous_within_at (λ x, (f x)⁻¹) s x :=
hf.inv

section ordered_comm_group

variables [topological_space H] [ordered_comm_group H] [topological_group H]

@[to_additive] lemma tendsto_inv_nhds_within_Ioi {a : H} :
  tendsto has_inv.inv (𝓝[>] a) (𝓝[<] (a⁻¹)) :=
(continuous_inv.tendsto a).inf $ by simp [tendsto_principal_principal]

@[to_additive] lemma tendsto_inv_nhds_within_Iio {a : H} :
  tendsto has_inv.inv (𝓝[<] a) (𝓝[>] (a⁻¹)) :=
(continuous_inv.tendsto a).inf $ by simp [tendsto_principal_principal]

@[to_additive] lemma tendsto_inv_nhds_within_Ioi_inv {a : H} :
  tendsto has_inv.inv (𝓝[>] (a⁻¹)) (𝓝[<] a) :=
by simpa only [inv_inv] using @tendsto_inv_nhds_within_Ioi _ _ _ _ (a⁻¹)

@[to_additive] lemma tendsto_inv_nhds_within_Iio_inv {a : H} :
  tendsto has_inv.inv (𝓝[<] (a⁻¹)) (𝓝[>] a) :=
by simpa only [inv_inv] using @tendsto_inv_nhds_within_Iio _ _ _ _ (a⁻¹)

@[to_additive] lemma tendsto_inv_nhds_within_Ici {a : H} :
  tendsto has_inv.inv (𝓝[≥] a) (𝓝[≤] (a⁻¹)) :=
(continuous_inv.tendsto a).inf $ by simp [tendsto_principal_principal]

@[to_additive] lemma tendsto_inv_nhds_within_Iic {a : H} :
  tendsto has_inv.inv (𝓝[≤] a) (𝓝[≥] (a⁻¹)) :=
(continuous_inv.tendsto a).inf $ by simp [tendsto_principal_principal]

@[to_additive] lemma tendsto_inv_nhds_within_Ici_inv {a : H} :
  tendsto has_inv.inv (𝓝[≥] (a⁻¹)) (𝓝[≤] a) :=
by simpa only [inv_inv] using @tendsto_inv_nhds_within_Ici _ _ _ _ (a⁻¹)

@[to_additive] lemma tendsto_inv_nhds_within_Iic_inv {a : H} :
  tendsto has_inv.inv (𝓝[≤] (a⁻¹)) (𝓝[≥] a) :=
by simpa only [inv_inv] using @tendsto_inv_nhds_within_Iic _ _ _ _ (a⁻¹)

end ordered_comm_group

@[instance, to_additive]
instance [topological_space H] [group H] [topological_group H] :
  topological_group (G × H) :=
{ continuous_inv := continuous_inv.prod_map continuous_inv }

@[to_additive]
instance pi.topological_group {C : β → Type*} [∀ b, topological_space (C b)]
  [∀ b, group (C b)] [∀ b, topological_group (C b)] : topological_group (Π b, C b) :=
{ continuous_inv := continuous_pi (λ i, (continuous_apply i).inv) }

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def homeomorph.inv : G ≃ₜ G :=
{ continuous_to_fun  := continuous_inv,
  continuous_inv_fun := continuous_inv,
  .. equiv.inv G }

@[to_additive]
lemma nhds_one_symm : comap has_inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
((homeomorph.inv G).comap_nhds_eq _).trans (congr_arg nhds one_inv)

/-- The map `(x, y) ↦ (x, xy)` as a homeomorphism. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a homeomorphism.
This is a shear mapping."]
protected def homeomorph.shear_mul_right : G × G ≃ₜ G × G :=
{ continuous_to_fun  := continuous_fst.prod_mk continuous_mul,
  continuous_inv_fun := continuous_fst.prod_mk $ continuous_fst.inv.mul continuous_snd,
  .. equiv.prod_shear (equiv.refl _) equiv.mul_left }

@[simp, to_additive]
lemma homeomorph.shear_mul_right_coe :
  ⇑(homeomorph.shear_mul_right G) = λ z : G × G, (z.1, z.1 * z.2) :=
rfl

@[simp, to_additive]
lemma homeomorph.shear_mul_right_symm_coe :
  ⇑(homeomorph.shear_mul_right G).symm = λ z : G × G, (z.1, z.1⁻¹ * z.2) :=
rfl

variables {G}

@[to_additive]
lemma is_open.inv {s : set G} (hs : is_open s) : is_open s⁻¹ := hs.preimage continuous_inv

@[to_additive]
lemma is_closed.inv {s : set G} (hs : is_closed s) : is_closed s⁻¹ := hs.preimage continuous_inv

namespace subgroup

@[to_additive] instance (S : subgroup G) :
  topological_group S :=
{ continuous_inv :=
  begin
    rw embedding_subtype_coe.to_inducing.continuous_iff,
    exact continuous_subtype_coe.inv
  end,
  ..S.to_submonoid.has_continuous_mul }

end subgroup

@[to_additive]
lemma inv_closure (s : set G) : (closure s)⁻¹ = closure s⁻¹ :=
(homeomorph.inv G).preimage_closure s

/-- The (topological-space) closure of a subgroup of a space `M` with `has_continuous_mul` is
itself a subgroup. -/
@[to_additive "The (topological-space) closure of an additive subgroup of a space `M` with
`has_continuous_add` is itself an additive subgroup."]
def subgroup.topological_closure (s : subgroup G) : subgroup G :=
{ carrier := closure (s : set G),
  inv_mem' := λ g m, by simpa [←mem_inv, inv_closure] using m,
  ..s.to_submonoid.topological_closure }

@[simp, to_additive] lemma subgroup.topological_closure_coe {s : subgroup G} :
  (s.topological_closure : set G) = closure s :=
rfl

@[to_additive]
instance subgroup.topological_closure_topological_group (s : subgroup G) :
  topological_group (s.topological_closure) :=
{ continuous_inv :=
  begin
    apply continuous_induced_rng,
    change continuous (λ p : s.topological_closure, (p : G)⁻¹),
    continuity,
  end
  ..s.to_submonoid.topological_closure_has_continuous_mul}

@[to_additive] lemma subgroup.subgroup_topological_closure (s : subgroup G) :
  s ≤ s.topological_closure :=
subset_closure

@[to_additive] lemma subgroup.is_closed_topological_closure (s : subgroup G) :
  is_closed (s.topological_closure : set G) :=
by convert is_closed_closure

@[to_additive] lemma subgroup.topological_closure_minimal
  (s : subgroup G) {t : subgroup G} (h : s ≤ t) (ht : is_closed (t : set G)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

@[to_additive] lemma dense_range.topological_closure_map_subgroup [group H] [topological_space H]
  [topological_group H] {f : G →* H} (hf : continuous f) (hf' : dense_range f) {s : subgroup G}
  (hs : s.topological_closure = ⊤) :
  (s.map f).topological_closure = ⊤ :=
begin
  rw set_like.ext'_iff at hs ⊢,
  simp only [subgroup.topological_closure_coe, subgroup.coe_top, ← dense_iff_closure_eq] at hs ⊢,
  exact hf'.dense_image hf hs
end

@[to_additive exists_nhds_half_neg]
lemma exists_nhds_split_inv {s : set G} (hs : s ∈ 𝓝 (1 : G)) :
  ∃ V ∈ 𝓝 (1 : G), ∀ (v ∈ V) (w ∈ V), v / w ∈ s :=
have ((λp : G × G, p.1 * p.2⁻¹) ⁻¹' s) ∈ 𝓝 ((1, 1) : G × G),
  from continuous_at_fst.mul continuous_at_snd.inv (by simpa),
by simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage]
  using this

@[to_additive]
lemma nhds_translation_mul_inv (x : G) : comap (λ y : G, y * x⁻¹) (𝓝 1) = 𝓝 x :=
((homeomorph.mul_right x⁻¹).comap_nhds_eq 1).trans $ show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x, by simp

@[simp, to_additive] lemma map_mul_left_nhds (x y : G) : map ((*) x) (𝓝 y) = 𝓝 (x * y) :=
(homeomorph.mul_left x).map_nhds_eq y

@[to_additive] lemma map_mul_left_nhds_one (x : G) : map ((*) x) (𝓝 1) = 𝓝 x := by simp

@[to_additive]
lemma topological_group.ext {G : Type*} [group G] {t t' : topological_space G}
  (tg : @topological_group G t _) (tg' : @topological_group G t' _)
  (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
eq_of_nhds_eq_nhds $ λ x, by
  rw [← @nhds_translation_mul_inv G t _ _ x , ← @nhds_translation_mul_inv G t' _ _ x , ← h]

@[to_additive]
lemma topological_group.of_nhds_aux {G : Type*} [group G] [topological_space G]
  (hinv : tendsto (λ (x : G), x⁻¹) (𝓝 1) (𝓝 1))
  (hleft : ∀ (x₀ : G), 𝓝 x₀ = map (λ (x : G), x₀ * x) (𝓝 1))
  (hconj : ∀ (x₀ : G), map (λ (x : G), x₀ * x * x₀⁻¹) (𝓝 1) ≤ 𝓝 1) : continuous (λ x : G, x⁻¹) :=
begin
  rw continuous_iff_continuous_at,
  rintros x₀,
  have key : (λ x, (x₀*x)⁻¹) = (λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹) ∘ (λ x, x⁻¹),
    by {ext ; simp[mul_assoc] },
  calc map (λ x, x⁻¹) (𝓝 x₀)
      = map (λ x, x⁻¹) (map (λ x, x₀*x) $ 𝓝 1) : by rw hleft
  ... = map (λ x, (x₀*x)⁻¹) (𝓝 1) : by rw filter.map_map
  ... = map (((λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹)) ∘ (λ x, x⁻¹)) (𝓝 1) : by rw key
  ... = map ((λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹)) _ : by rw ← filter.map_map
  ... ≤ map ((λ x, x₀⁻¹ * x) ∘ λ x, x₀ * x * x₀⁻¹) (𝓝 1) : map_mono hinv
  ... = map (λ x, x₀⁻¹ * x) (map (λ x, x₀ * x * x₀⁻¹) (𝓝 1)) : filter.map_map
  ... ≤ map (λ x, x₀⁻¹ * x) (𝓝 1) : map_mono (hconj x₀)
  ... = 𝓝 x₀⁻¹ : (hleft _).symm
end

@[to_additive]
lemma topological_group.of_nhds_one' {G : Type u} [group G] [topological_space G]
  (hmul : tendsto (uncurry ((*) : G → G → G)) ((𝓝 1) ×ᶠ 𝓝 1) (𝓝 1))
  (hinv : tendsto (λ x : G, x⁻¹) (𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : G, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1))
  (hright : ∀ x₀ : G, 𝓝 x₀ = map (λ x, x*x₀) (𝓝 1)) : topological_group G :=
begin
  refine { continuous_mul := (has_continuous_mul.of_nhds_one hmul hleft hright).continuous_mul,
           continuous_inv := topological_group.of_nhds_aux hinv hleft _ },
  intros x₀,
  suffices : map (λ (x : G), x₀ * x * x₀⁻¹) (𝓝 1) = 𝓝 1, by simp [this, le_refl],
  rw [show (λ x, x₀ * x * x₀⁻¹) = (λ x, x₀ * x) ∘ λ x, x*x₀⁻¹, by {ext, simp [mul_assoc] },
      ← filter.map_map, ← hright, hleft x₀⁻¹, filter.map_map],
  convert map_id,
  ext,
  simp
end

@[to_additive]
lemma topological_group.of_nhds_one {G : Type u} [group G] [topological_space G]
  (hmul : tendsto (uncurry ((*) : G → G → G)) ((𝓝 1) ×ᶠ 𝓝 1) (𝓝 1))
  (hinv : tendsto (λ x : G, x⁻¹) (𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : G, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1))
  (hconj : ∀ x₀ : G, tendsto (λ x, x₀*x*x₀⁻¹) (𝓝 1) (𝓝 1)) : topological_group G :=
 { continuous_mul := begin
    rw continuous_iff_continuous_at,
    rintros ⟨x₀, y₀⟩,
    have key : (λ (p : G × G), x₀ * p.1 * (y₀ * p.2)) =
      ((λ x, x₀*y₀*x) ∘ (uncurry (*)) ∘ (prod.map (λ x, y₀⁻¹*x*y₀) id)),
      by { ext, simp [uncurry, prod.map, mul_assoc] },
    specialize hconj y₀⁻¹, rw inv_inv at hconj,
    calc map (λ (p : G × G), p.1 * p.2) (𝓝 (x₀, y₀))
        = map (λ (p : G × G), p.1 * p.2) ((𝓝 x₀) ×ᶠ 𝓝 y₀)
            : by rw nhds_prod_eq
    ... = map (λ (p : G × G), x₀ * p.1 * (y₀ * p.2)) ((𝓝 1) ×ᶠ (𝓝 1))
            : by rw [hleft x₀, hleft y₀, prod_map_map_eq, filter.map_map]
    ... = map (((λ x, x₀*y₀*x) ∘ (uncurry (*))) ∘ (prod.map (λ x, y₀⁻¹*x*y₀) id))((𝓝 1) ×ᶠ (𝓝 1))
            : by rw key
    ... = map ((λ x, x₀*y₀*x) ∘ (uncurry (*))) ((map  (λ x, y₀⁻¹*x*y₀) $ 𝓝 1) ×ᶠ (𝓝 1))
            : by rw [← filter.map_map, ← prod_map_map_eq', map_id]
    ... ≤ map ((λ x, x₀*y₀*x) ∘ (uncurry (*))) ((𝓝 1) ×ᶠ (𝓝 1))
            : map_mono (filter.prod_mono hconj $ le_refl _)
    ... = map (λ x, x₀*y₀*x) (map (uncurry (*)) ((𝓝 1) ×ᶠ (𝓝 1)))   : by rw filter.map_map
    ... ≤ map (λ x, x₀*y₀*x) (𝓝 1)   : map_mono hmul
    ... = 𝓝 (x₀*y₀)   : (hleft _).symm
  end,
  continuous_inv := topological_group.of_nhds_aux hinv hleft hconj}

@[to_additive]
lemma topological_group.of_comm_of_nhds_one {G : Type u} [comm_group G] [topological_space G]
  (hmul : tendsto (uncurry ((*) : G → G → G)) ((𝓝 1) ×ᶠ 𝓝 1) (𝓝 1))
  (hinv : tendsto (λ x : G, x⁻¹) (𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : G, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1)) : topological_group G :=
topological_group.of_nhds_one hmul hinv hleft (by simpa using tendsto_id)

end topological_group

section quotient_topological_group
variables [topological_space G] [group G] [topological_group G] (N : subgroup G) (n : N.normal)

@[to_additive]
instance quotient_group.quotient.topological_space {G : Type*} [group G] [topological_space G]
  (N : subgroup G) : topological_space (G ⧸ N) :=
quotient.topological_space

open quotient_group

@[to_additive]
lemma quotient_group.is_open_map_coe : is_open_map (coe : G → G ⧸ N) :=
begin
  intros s s_op,
  change is_open ((coe : G → G ⧸ N) ⁻¹' (coe '' s)),
  rw quotient_group.preimage_image_coe N s,
  exact is_open_Union (λ n, (continuous_mul_right _).is_open_preimage s s_op)
end

@[to_additive]
instance topological_group_quotient [N.normal] : topological_group (G ⧸ N) :=
{ continuous_mul := begin
    have cont : continuous ((coe : G → G ⧸ N) ∘ (λ (p : G × G), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul,
    have quot : quotient_map (λ p : G × G, ((p.1 : G ⧸ N), (p.2 : G ⧸ N))),
    { apply is_open_map.to_quotient_map,
      { exact (quotient_group.is_open_map_coe N).prod (quotient_group.is_open_map_coe N) },
      { exact continuous_quot_mk.prod_map continuous_quot_mk },
      { exact (surjective_quot_mk _).prod_map (surjective_quot_mk _) } },
    exact (quotient_map.continuous_iff quot).2 cont,
  end,
  continuous_inv := begin
    have : continuous ((coe : G → G ⧸ N) ∘ (λ (a : G), a⁻¹)) :=
      continuous_quot_mk.comp continuous_inv,
    convert continuous_quotient_lift _ this,
  end }

end quotient_topological_group

/-- A typeclass saying that `λ p : G × G, p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class has_continuous_sub (G : Type*) [topological_space G] [has_sub G] : Prop :=
(continuous_sub : continuous (λ p : G × G, p.1 - p.2))

/-- A typeclass saying that `λ p : G × G, p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `group_with_zero`. -/
@[to_additive]
class has_continuous_div (G : Type*) [topological_space G] [has_div G] : Prop :=
(continuous_div' : continuous (λ p : G × G, p.1 / p.2))

@[priority 100, to_additive] -- see Note [lower instance priority]
instance topological_group.to_has_continuous_div [topological_space G] [group G]
  [topological_group G] : has_continuous_div G :=
⟨by { simp only [div_eq_mul_inv], exact continuous_fst.mul continuous_snd.inv }⟩

export has_continuous_sub (continuous_sub)
export has_continuous_div (continuous_div')

section has_continuous_div

variables [topological_space G] [has_div G] [has_continuous_div G]

@[to_additive sub]
lemma filter.tendsto.div' {f g : α → G} {l : filter α} {a b : G} (hf : tendsto f l (𝓝 a))
  (hg : tendsto g l (𝓝 b)) : tendsto (λ x, f x / g x) l (𝓝 (a / b)) :=
(continuous_div'.tendsto (a, b)).comp (hf.prod_mk_nhds hg)

@[to_additive const_sub]
lemma filter.tendsto.const_div' (b : G) {c : G} {f : α → G} {l : filter α}
  (h : tendsto f l (𝓝 c)) : tendsto (λ k : α, b / f k) l (𝓝 (b / c)) :=
tendsto_const_nhds.div' h

@[to_additive sub_const]
lemma filter.tendsto.div_const' (b : G) {c : G} {f : α → G} {l : filter α}
  (h : tendsto f l (𝓝 c)) : tendsto (λ k : α, f k / b) l (𝓝 (c / b)) :=
h.div' tendsto_const_nhds

variables [topological_space α] {f g : α → G} {s : set α} {x : α}

@[continuity, to_additive sub] lemma continuous.div' (hf : continuous f) (hg : continuous g) :
  continuous (λ x, f x / g x) :=
continuous_div'.comp (hf.prod_mk hg : _)

@[to_additive continuous_sub_left]
lemma continuous_div_left' (a : G) : continuous (λ b : G, a / b) :=
continuous_const.div' continuous_id

@[to_additive continuous_sub_right]
lemma continuous_div_right' (a : G) : continuous (λ b : G, b / a) :=
continuous_id.div' continuous_const

@[to_additive sub]
lemma continuous_at.div' {f g : α → G} {x : α} (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λx, f x / g x) x :=
hf.div' hg

@[to_additive sub]
lemma continuous_within_at.div' (hf : continuous_within_at f s x)
  (hg : continuous_within_at g s x) :
  continuous_within_at (λ x, f x / g x) s x :=
hf.div' hg

@[to_additive sub]
lemma continuous_on.div' (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λx, f x / g x) s :=
λ x hx, (hf x hx).div' (hg x hx)

end has_continuous_div

@[to_additive]
lemma nhds_translation_div [topological_space G] [group G] [topological_group G] (x : G) :
  comap (λy:G, y / x) (𝓝 1) = 𝓝 x :=
by simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

/-- additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class add_group_with_zero_nhd (G : Type u) extends add_comm_group G :=
(Z [] : filter G)
(zero_Z : pure 0 ≤ Z)
(sub_Z : tendsto (λp:G×G, p.1 - p.2) (Z ×ᶠ Z) Z)

section filter_mul

section
variables (G) [topological_space G] [group G] [topological_group G]

@[to_additive]
lemma topological_group.t1_space (h : @is_closed G _ {1}) : t1_space G :=
⟨assume x, by { convert is_closed_map_mul_right x _ h, simp }⟩

@[to_additive]
lemma topological_group.regular_space [t1_space G] : regular_space G :=
⟨assume s a hs ha,
 let f := λ p : G × G, p.1 * (p.2)⁻¹ in
 have hf : continuous f := continuous_fst.mul continuous_snd.inv,
 -- a ∈ -s implies f (a, 1) ∈ -s, and so (a, 1) ∈ f⁻¹' (-s);
 -- and so can find t₁ t₂ open such that a ∈ t₁ × t₂ ⊆ f⁻¹' (-s)
 let ⟨t₁, t₂, ht₁, ht₂, a_mem_t₁, one_mem_t₂, t_subset⟩ :=
   is_open_prod_iff.1 ((is_open_compl_iff.2 hs).preimage hf) a (1:G) (by simpa [f]) in
 begin
   use [s * t₂, ht₂.mul_left, λ x hx, ⟨x, 1, hx, one_mem_t₂, mul_one _⟩],
   rw [nhds_within, inf_principal_eq_bot, mem_nhds_iff],
   refine ⟨t₁, _, ht₁, a_mem_t₁⟩,
   rintros x hx ⟨y, z, hy, hz, yz⟩,
   have : x * z⁻¹ ∈ sᶜ := (prod_subset_iff.1 t_subset) x hx z hz,
   have : x * z⁻¹ ∈ s, rw ← yz, simpa,
   contradiction
 end⟩

local attribute [instance] topological_group.regular_space

@[to_additive]
lemma topological_group.t2_space [t1_space G] : t2_space G := regular_space.t2_space G

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/

variables [topological_space G] [group G] [topological_group G]

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `KV ⊆ U`. -/
@[to_additive "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of
`0` such that `K + V ⊆ U`."]
lemma compact_open_separated_mul {K U : set G} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ V : set G, is_open V ∧ (1 : G) ∈ V ∧ K * V ⊆ U :=
begin
  let W : G → set G := λ x, (λ y, x * y) ⁻¹' U,
  have h1W : ∀ x, is_open (W x) := λ x, hU.preimage (continuous_mul_left x),
  have h2W : ∀ x ∈ K, (1 : G) ∈ W x := λ x hx, by simp only [mem_preimage, mul_one, hKU hx],
  choose V hV using λ x : K, exists_open_nhds_one_mul_subset ((h1W x).mem_nhds (h2W x.1 x.2)),
  let X : K → set G := λ x, (λ y, (x : G)⁻¹ * y) ⁻¹' (V x),
  obtain ⟨t, ht⟩ : ∃ t : finset ↥K, K ⊆ ⋃ i ∈ t, X i,
  { refine hK.elim_finite_subcover X (λ x, (hV x).1.preimage (continuous_mul_left x⁻¹)) _,
    intros x hx, rw [mem_Union], use ⟨x, hx⟩, rw [mem_preimage], convert (hV _).2.1,
    simp only [mul_left_inv, subtype.coe_mk] },
  refine ⟨⋂ x ∈ t, V x, is_open_bInter (finite_mem_finset _) (λ x hx, (hV x).1), _, _⟩,
  { simp only [mem_Inter], intros x hx, exact (hV x).2.1 },
  rintro _ ⟨x, y, hx, hy, rfl⟩, simp only [mem_Inter] at hy,
  have := ht hx, simp only [mem_Union, mem_preimage] at this, rcases this with ⟨z, h1z, h2z⟩,
  have : (z : G)⁻¹ * x * y ∈ W z := (hV z).2.2 (mul_mem_mul h2z (hy z h1z)),
  rw [mem_preimage] at this, convert this using 1, simp only [mul_assoc, mul_inv_cancel_left]
end

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive "A compact set is covered by finitely many left additive translates of a set
  with non-empty interior."]
lemma compact_covered_by_mul_left_translates {K V : set G} (hK : is_compact K)
  (hV : (interior V).nonempty) : ∃ t : finset G, K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V :=
begin
  obtain ⟨t, ht⟩ : ∃ t : finset G, K ⊆ ⋃ x ∈ t, interior (((*) x) ⁻¹' V),
  { refine hK.elim_finite_subcover (λ x, interior $ ((*) x) ⁻¹' V) (λ x, is_open_interior) _,
    cases hV with g₀ hg₀,
    refine λ g hg, mem_Union.2 ⟨g₀ * g⁻¹, _⟩,
    refine preimage_interior_subset_interior_preimage (continuous_const.mul continuous_id) _,
    rwa [mem_preimage, inv_mul_cancel_right] },
  exact ⟨t, subset.trans ht $ bUnion_mono $ λ g hg, interior_subset⟩
end

/-- Every locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[priority 100, to_additive separable_locally_compact_add_group.sigma_compact_space]
instance separable_locally_compact_group.sigma_compact_space
  [separable_space G] [locally_compact_space G] : sigma_compact_space G :=
begin
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G),
  refine ⟨⟨λ n, (λ x, x * dense_seq G n) ⁻¹' L, _, _⟩⟩,
  { intro n, exact (homeomorph.mul_right _).compact_preimage.mpr hLc },
  { refine Union_eq_univ_iff.2 (λ x, _),
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (dense_seq G) ∩ (λ y, x * y) ⁻¹' L).nonempty,
    { rw [← (homeomorph.mul_left x).apply_symm_apply 1] at hL1,
      exact (dense_range_dense_seq G).inter_nhds_nonempty
        ((homeomorph.mul_left x).continuous.continuous_at $ hL1) },
    exact ⟨n, hn⟩ }
end

/-- Every separated topological group in which there exists a compact set with nonempty interior
is locally compact. -/
@[to_additive] lemma topological_space.positive_compacts.locally_compact_space_of_group
  [t2_space G] (K : positive_compacts G) :
  locally_compact_space G :=
begin
  refine locally_compact_of_compact_nhds (λ x, _),
  obtain ⟨y, hy⟩ : ∃ y, y ∈ interior K.1 := K.2.2,
  let F := homeomorph.mul_left (x * y⁻¹),
  refine ⟨F '' K.1, _, is_compact.image K.2.1 F.continuous⟩,
  suffices : F.symm ⁻¹' K.1 ∈ 𝓝 x, by { convert this, apply equiv.image_eq_preimage },
  apply continuous_at.preimage_mem_nhds F.symm.continuous.continuous_at,
  have : F.symm x = y, by simp [F, homeomorph.mul_left_symm],
  rw this,
  exact mem_interior_iff_mem_nhds.1 hy
end

end

section
variables [topological_space G] [comm_group G] [topological_group G]

@[to_additive]
lemma nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
filter_eq $ set.ext $ assume s,
begin
  rw [← nhds_translation_mul_inv x, ← nhds_translation_mul_inv y, ← nhds_translation_mul_inv (x*y)],
  split,
  { rintros ⟨t, ht, ts⟩,
    rcases exists_nhds_one_split ht with ⟨V, V1, h⟩,
    refine ⟨(λa, a * x⁻¹) ⁻¹' V, (λa, a * y⁻¹) ⁻¹' V,
            ⟨V, V1, subset.refl _⟩, ⟨V, V1, subset.refl _⟩, _⟩,
    rintros a ⟨v, w, v_mem, w_mem, rfl⟩,
    apply ts,
    simpa [mul_comm, mul_assoc, mul_left_comm] using h (v * x⁻¹) v_mem (w * y⁻¹) w_mem },
  { rintros ⟨a, c, ⟨b, hb, ba⟩, ⟨d, hd, dc⟩, ac⟩,
    refine ⟨b ∩ d, inter_mem hb hd, assume v, _⟩,
    simp only [preimage_subset_iff, mul_inv_rev, mem_preimage] at *,
    rintros ⟨vb, vd⟩,
    refine ac ⟨v * y⁻¹, y, _, _, _⟩,
    { rw ← mul_assoc _ _ _ at vb, exact ba _ vb },
    { apply dc y, rw mul_right_inv, exact mem_of_mem_nhds hd },
    { simp only [inv_mul_cancel_right] } }
end

/-- On a topological group, `𝓝 : G → filter G` can be promoted to a `mul_hom`. -/
@[to_additive "On an additive topological group, `𝓝 : G → filter G` can be promoted to an
`add_hom`.", simps]
def nhds_mul_hom : mul_hom G (filter G) :=
{ to_fun := 𝓝,
  map_mul' := λ_ _, nhds_mul _ _ }

end

end filter_mul

instance additive.topological_add_group {G} [h : topological_space G]
  [group G] [topological_group G] : @topological_add_group (additive G) h _ :=
{ continuous_neg := @continuous_inv G _ _ _ }

instance multiplicative.topological_group {G} [h : topological_space G]
  [add_group G] [topological_add_group G] : @topological_group (multiplicative G) h _ :=
{ continuous_inv := @continuous_neg G _ _ _ }

namespace units

variables [monoid α] [topological_space α] [has_continuous_mul α] [monoid β] [topological_space β]
  [has_continuous_mul β]

instance : topological_group (units α) :=
{ continuous_inv := continuous_induced_rng ((continuous_unop.comp (continuous_snd.comp
    (@continuous_embed_product α _ _))).prod_mk (continuous_op.comp continuous_coe)) }

/-- The topological group isomorphism between the units of a product of two monoids, and the product
    of the units of each monoid. -/
def homeomorph.prod_units : homeomorph (units (α × β)) (units α × units β) :=
{ continuous_to_fun  :=
  begin
    apply continuous.prod_mk,
    { refine continuous_induced_rng ((continuous_fst.comp units.continuous_coe).prod_mk _),
      refine continuous_op.comp (continuous_fst.comp _),
      simp_rw units.inv_eq_coe_inv,
      exact units.continuous_coe.comp continuous_inv, },
    { refine continuous_induced_rng ((continuous_snd.comp units.continuous_coe).prod_mk _),
      simp_rw units.coe_map_inv,
      exact continuous_op.comp (continuous_snd.comp (units.continuous_coe.comp continuous_inv)), }
  end,
  continuous_inv_fun :=
  begin
    refine continuous_induced_rng (continuous.prod_mk _ _),
    { exact (units.continuous_coe.comp continuous_fst).prod_mk
        (units.continuous_coe.comp continuous_snd), },
    { refine continuous_op.comp
        (units.continuous_coe.comp $ continuous_induced_rng $ continuous.prod_mk _ _),
      { exact (units.continuous_coe.comp (continuous_inv.comp continuous_fst)).prod_mk
          (units.continuous_coe.comp (continuous_inv.comp continuous_snd)) },
      { exact continuous_op.comp ((units.continuous_coe.comp continuous_fst).prod_mk
            (units.continuous_coe.comp continuous_snd)) }}
  end,
  ..mul_equiv.prod_units }

end units

/-!
### Lattice of group topologies
We define a type class `group_topology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → group_topology β`.

The additive version `add_group_topology α` and corresponding results are provided as well.
-/

/-- A group topology on a group `α` is a topology for which multiplication and inversion
are continuous. -/
structure group_topology (α : Type u) [group α]
  extends topological_space α, topological_group α : Type u

/-- An additive group topology on an additive group `α` is a topology for which addition and
  negation are continuous. -/
structure add_group_topology (α : Type u) [add_group α]
  extends topological_space α, topological_add_group α : Type u

attribute [to_additive] group_topology

namespace group_topology

variables [group α]

/-- A version of the global `continuous_mul` suitable for dot notation. -/
@[to_additive]
lemma continuous_mul' (g : group_topology α) :
  by haveI := g.to_topological_space; exact continuous (λ p : α × α, p.1 * p.2) :=
begin
  letI := g.to_topological_space,
  haveI := g.to_topological_group,
  exact continuous_mul,
end

/-- A version of the global `continuous_inv` suitable for dot notation. -/
@[to_additive]
lemma continuous_inv' (g : group_topology α) :
  by haveI := g.to_topological_space; exact continuous (has_inv.inv : α → α) :=
begin
  letI := g.to_topological_space,
  haveI := g.to_topological_group,
  exact continuous_inv,
end

@[to_additive]
lemma to_topological_space_injective :
  function.injective (to_topological_space : group_topology α → topological_space α):=
λ f g h, by { cases f, cases g, congr' }

@[ext, to_additive]
lemma ext' {f g : group_topology α} (h : f.is_open = g.is_open) : f = g :=
to_topological_space_injective $ topological_space_eq h

/-- The ordering on group topologies on the group `γ`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
@[to_additive]
instance : partial_order (group_topology α) :=
partial_order.lift to_topological_space to_topological_space_injective

@[simp, to_additive] lemma to_topological_space_le {x y : group_topology α} :
  x.to_topological_space ≤ y.to_topological_space ↔ x ≤ y := iff.rfl

@[to_additive]
instance : has_top (group_topology α) :=
⟨{to_topological_space := ⊤,
  continuous_mul       := continuous_top,
  continuous_inv       := continuous_top}⟩

@[simp, to_additive] lemma to_topological_space_top :
  (⊤ : group_topology α).to_topological_space = ⊤ := rfl

@[to_additive]
instance : has_bot (group_topology α) :=
⟨{to_topological_space := ⊥,
  continuous_mul       := by continuity,
  continuous_inv       := continuous_bot}⟩

@[simp, to_additive] lemma to_topological_space_bot :
  (⊥ : group_topology α).to_topological_space = ⊥ := rfl

@[to_additive]
instance : bounded_order (group_topology α) :=
{ top := ⊤,
  le_top := λ x, show x.to_topological_space ≤ ⊤, from le_top,
  bot := ⊥,
  bot_le := λ x, show ⊥ ≤ x.to_topological_space, from bot_le }

@[to_additive]
instance : has_inf (group_topology α) :=
{ inf := λ x y,
  { to_topological_space := x.to_topological_space ⊓ y.to_topological_space,
    continuous_mul := continuous_inf_rng
      (continuous_inf_dom_left₂ x.continuous_mul') (continuous_inf_dom_right₂ y.continuous_mul'),
    continuous_inv := continuous_inf_rng
      (continuous_inf_dom_left x.continuous_inv') (continuous_inf_dom_right y.continuous_inv') } }

@[simp, to_additive]
lemma to_topological_space_inf (x y : group_topology α) :
  (x ⊓ y).to_topological_space = x.to_topological_space ⊓ y.to_topological_space := rfl

@[to_additive]
instance : semilattice_inf (group_topology α) :=
to_topological_space_injective.semilattice_inf _ to_topological_space_inf

@[to_additive]
instance : inhabited (group_topology α) := ⟨⊤⟩

local notation `cont` := @continuous _ _
@[to_additive "Infimum of a collection of additive group topologies"]
instance : has_Inf (group_topology α) :=
{ Inf := λ S,
  { to_topological_space := Inf (to_topological_space '' S),
    continuous_mul       := continuous_Inf_rng begin
      rintros _ ⟨⟨t, tr⟩, haS, rfl⟩, resetI,
      exact continuous_Inf_dom₂
        (set.mem_image_of_mem to_topological_space haS)
        (set.mem_image_of_mem to_topological_space haS) continuous_mul,
    end,
    continuous_inv       := continuous_Inf_rng begin
      rintros _ ⟨⟨t, tr⟩, haS, rfl⟩, resetI,
      exact continuous_Inf_dom (set.mem_image_of_mem to_topological_space haS) continuous_inv,
    end, } }

@[simp, to_additive]
lemma to_topological_space_Inf (s : set (group_topology α)) :
  (Inf s).to_topological_space = Inf (to_topological_space '' s) := rfl

@[simp, to_additive]
lemma to_topological_space_infi {ι} (s : ι → group_topology α) :
  (⨅ i, s i).to_topological_space = ⨅ i, (s i).to_topological_space :=
congr_arg Inf (range_comp _ _).symm

/-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of group topologies is the topology generated by all their open sets
(which is a group topology).

The supremum of two group topologies `s` and `t` is the infimum of the family of all group
topologies contained in the intersection of `s` and `t`. -/
@[to_additive]
instance : complete_semilattice_Inf (group_topology α) :=
{ Inf_le := λ S a haS, to_topological_space_le.1 $ Inf_le ⟨a, haS, rfl⟩,
  le_Inf :=
  begin
    intros S a hab,
    apply topological_space.complete_lattice.le_Inf,
    rintros _ ⟨b, hbS, rfl⟩,
    exact hab b hbS,
  end,
  ..group_topology.has_Inf,
  ..group_topology.partial_order }

@[to_additive]
instance : complete_lattice (group_topology α) :=
{ inf := (⊓),
  top := ⊤,
  bot := ⊥,
  ..group_topology.bounded_order,
  ..group_topology.semilattice_inf,
  ..complete_lattice_of_complete_semilattice_Inf _ }

/--  Given `f : α → β` and a topology on `α`, the coinduced group topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological group. -/
@[to_additive "Given `f : α → β` and a topology on `α`, the coinduced additive group topology on `β`
is the finest topology such that `f` is continuous and `β` is a topological additive group."]
def coinduced {α β : Type*} [t : topological_space α] [group β] (f : α → β) :
  group_topology β :=
Inf {b : group_topology β | (topological_space.coinduced f t) ≤ b.to_topological_space}

@[to_additive]
lemma coinduced_continuous {α β : Type*} [t : topological_space α] [group β]
  (f : α → β) : cont t (coinduced f).to_topological_space f :=
begin
  rw continuous_iff_coinduced_le,
  refine le_Inf _,
  rintros _ ⟨t', ht', rfl⟩,
  exact ht',
end

end group_topology
