/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import group_theory.group_action.conj_act
import group_theory.quotient_group
import order.filter.pointwise
import topology.algebra.monoid
import topology.compact_open
import topology.sets.compacts
import topology.algebra.constructions

/-!
# Topological groups

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

@[to_additive is_open.left_add_coset]
lemma is_open.left_coset {U : set G} (h : is_open U) (x : G) : is_open (left_coset x U) :=
is_open_map_mul_left x _ h

@[to_additive]
lemma is_closed_map_mul_left (a : G) : is_closed_map (λ x, a * x) :=
(homeomorph.mul_left a).is_closed_map

@[to_additive is_closed.left_add_coset]
lemma is_closed.left_coset {U : set G} (h : is_closed U) (x : G) : is_closed (left_coset x U) :=
is_closed_map_mul_left x _ h

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

@[to_additive is_open.right_add_coset]
lemma is_open.right_coset {U : set G} (h : is_open U) (x : G) : is_open (right_coset U x) :=
is_open_map_mul_right x _ h

@[to_additive]
lemma is_closed_map_mul_right (a : G) : is_closed_map (λ x, x * a) :=
(homeomorph.mul_right a).is_closed_map

@[to_additive is_closed.right_add_coset]
lemma is_closed.right_coset {U : set G} (h : is_closed U) (x : G) : is_closed (right_coset U x) :=
is_closed_map_mul_right x _ h

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
### `has_continuous_inv` and `has_continuous_neg`
-/

/-- Basic hypothesis to talk about a topological additive group. A topological additive group
over `M`, for example, is obtained by requiring the instances `add_group M` and
`has_continuous_add M` and `has_continuous_neg M`. -/
class has_continuous_neg (G : Type u) [topological_space G] [has_neg G] : Prop :=
(continuous_neg : continuous (λ a : G, -a))

/-- Basic hypothesis to talk about a topological group. A topological group over `M`, for example,
is obtained by requiring the instances `group M` and `has_continuous_mul M` and
`has_continuous_inv M`. -/
@[to_additive]
class has_continuous_inv (G : Type u) [topological_space G] [has_inv G] : Prop :=
(continuous_inv : continuous (λ a : G, a⁻¹))

export has_continuous_inv (continuous_inv)
export has_continuous_neg (continuous_neg)

section continuous_inv

variables [topological_space G] [has_inv G] [has_continuous_inv G]

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

@[to_additive]
instance [topological_space H] [has_inv H] [has_continuous_inv H] : has_continuous_inv (G × H) :=
⟨(continuous_inv.comp continuous_fst).prod_mk (continuous_inv.comp continuous_snd)⟩

variable {ι : Type*}

@[to_additive]
instance pi.has_continuous_inv {C : ι → Type*} [∀ i, topological_space (C i)]
  [∀ i, has_inv (C i)] [∀ i, has_continuous_inv (C i)] : has_continuous_inv (Π i, C i) :=
{ continuous_inv := continuous_pi (λ i, continuous.inv (continuous_apply i)) }

/-- A version of `pi.has_continuous_inv` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_inv` for non-dependent functions. -/
@[to_additive "A version of `pi.has_continuous_neg` for non-dependent functions. It is needed
because sometimes Lean fails to use `pi.has_continuous_neg` for non-dependent functions."]
instance pi.has_continuous_inv' : has_continuous_inv (ι → G) :=
pi.has_continuous_inv

@[priority 100, to_additive]
instance has_continuous_inv_of_discrete_topology [topological_space H]
  [has_inv H] [discrete_topology H] : has_continuous_inv H :=
⟨continuous_of_discrete_topology⟩

section pointwise_limits

variables (G₁ G₂ : Type*) [topological_space G₂] [t2_space G₂]

@[to_additive] lemma is_closed_set_of_map_inv [has_inv G₁] [has_inv G₂] [has_continuous_inv G₂] :
  is_closed {f : G₁ → G₂ | ∀ x, f x⁻¹ = (f x)⁻¹ } :=
begin
  simp only [set_of_forall],
  refine is_closed_Inter (λ i, is_closed_eq (continuous_apply _) (continuous_apply _).inv),
end

end pointwise_limits

instance additive.has_continuous_neg [h : topological_space H] [has_inv H]
  [has_continuous_inv H] : @has_continuous_neg (additive H) h _ :=
{ continuous_neg := @continuous_inv H _ _ _ }

instance multiplicative.has_continuous_inv [h : topological_space H] [has_neg H]
  [has_continuous_neg H] : @has_continuous_inv (multiplicative H) h _ :=
{ continuous_inv := @continuous_neg H _ _ _ }

end continuous_inv

section continuous_involutive_inv
variables [topological_space G] [has_involutive_inv G] [has_continuous_inv G] {s : set G}

@[to_additive] lemma is_compact.inv (hs : is_compact s) : is_compact s⁻¹ :=
by { rw [← image_inv], exact hs.image continuous_inv }

variables (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def homeomorph.inv (G : Type*) [topological_space G] [has_involutive_inv G]
  [has_continuous_inv G] : G ≃ₜ G :=
{ continuous_to_fun  := continuous_inv,
  continuous_inv_fun := continuous_inv,
  .. equiv.inv G }

@[to_additive] lemma is_open_map_inv : is_open_map (has_inv.inv : G → G) :=
(homeomorph.inv _).is_open_map

@[to_additive] lemma is_closed_map_inv : is_closed_map (has_inv.inv : G → G) :=
(homeomorph.inv _).is_closed_map

variables {G}

@[to_additive] lemma is_open.inv (hs : is_open s) : is_open s⁻¹ := hs.preimage continuous_inv
@[to_additive] lemma is_closed.inv (hs : is_closed s) : is_closed s⁻¹ := hs.preimage continuous_inv
@[to_additive] lemma inv_closure : ∀ s : set G, (closure s)⁻¹ = closure s⁻¹ :=
(homeomorph.inv G).preimage_closure

end continuous_involutive_inv

section lattice_ops

variables {ι' : Sort*} [has_inv G] [has_inv H] {ts : set (topological_space G)}
  (h : Π t ∈ ts, @has_continuous_inv G t _) {ts' : ι' → topological_space G}
  (h' : Π i, @has_continuous_inv G (ts' i) _) {t₁ t₂ : topological_space G}
  (h₁ : @has_continuous_inv G t₁ _) (h₂ : @has_continuous_inv G t₂ _)
  {t : topological_space H} [has_continuous_inv H]


@[to_additive] lemma has_continuous_inv_Inf :
  @has_continuous_inv G (Inf ts) _ :=
{ continuous_inv := continuous_Inf_rng (λ t ht, continuous_Inf_dom ht
  (@has_continuous_inv.continuous_inv G t _ (h t ht))) }

include h'

@[to_additive] lemma has_continuous_inv_infi :
  @has_continuous_inv G (⨅ i, ts' i) _ :=
by {rw ← Inf_range, exact has_continuous_inv_Inf (set.forall_range_iff.mpr h')}

omit h'

include h₁ h₂

@[to_additive] lemma has_continuous_inv_inf :
  @has_continuous_inv G (t₁ ⊓ t₂) _ :=
by {rw inf_eq_infi, refine has_continuous_inv_infi (λ b, _), cases b; assumption}

end lattice_ops

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
  extends has_continuous_add G, has_continuous_neg G : Prop

/-- A topological group is a group in which the multiplication and inversion operations are
continuous.

When you declare an instance that does not already have a `uniform_space` instance,
you should also provide an instance of `uniform_space` and `uniform_group` using
`topological_group.to_uniform_space` and `topological_group_is_uniform`. -/
@[to_additive]
class topological_group (G : Type*) [topological_space G] [group G]
  extends has_continuous_mul G, has_continuous_inv G : Prop

section conj

instance conj_act.units_has_continuous_const_smul {M} [monoid M] [topological_space M]
  [has_continuous_mul M] :
  has_continuous_const_smul (conj_act Mˣ) M :=
⟨λ m, (continuous_const.mul continuous_id).mul continuous_const⟩

/-- we slightly weaken the type class assumptions here so that it will also apply to `ennreal`, but
we nevertheless leave it in the `topological_group` namespace. -/

variables [topological_space G] [has_inv G] [has_mul G] [has_continuous_mul G]

/-- Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are continuous. -/
@[to_additive "Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are
continuous."]
lemma topological_group.continuous_conj_prod [has_continuous_inv G] :
  continuous (λ g : G × G, g.fst * g.snd * g.fst⁻¹) :=
continuous_mul.mul (continuous_inv.comp continuous_fst)

/-- Conjugation by a fixed element is continuous when `mul` is continuous. -/
@[to_additive "Conjugation by a fixed element is continuous when `add` is continuous."]
lemma topological_group.continuous_conj (g : G) : continuous (λ (h : G), g * h * g⁻¹) :=
(continuous_mul_right g⁻¹).comp (continuous_mul_left g)

/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive "Conjugation acting on fixed element of the additive group is continuous when both
  `add` and `neg` are continuous."]
lemma topological_group.continuous_conj' [has_continuous_inv G]
  (h : G) : continuous (λ (g : G), g * h * g⁻¹) :=
(continuous_mul_right h).mul continuous_inv

end conj

variables [topological_space G] [group G] [topological_group G]
[topological_space α] {f : α → G} {s : set α} {x : α}

section zpow

@[continuity, to_additive]
lemma continuous_zpow : ∀ z : ℤ, continuous (λ a : G, a ^ z)
| (int.of_nat n) := by simpa using continuous_pow n
| -[1+n] := by simpa using (continuous_pow (n + 1)).inv

instance add_group.has_continuous_const_smul_int {A} [add_group A] [topological_space A]
  [topological_add_group A] : has_continuous_const_smul ℤ A := ⟨continuous_zsmul⟩

instance add_group.has_continuous_smul_int {A} [add_group A] [topological_space A]
  [topological_add_group A] : has_continuous_smul ℤ A :=
⟨continuous_uncurry_of_discrete_topology continuous_zsmul⟩

@[continuity, to_additive]
lemma continuous.zpow {f : α → G} (h : continuous f) (z : ℤ) :
  continuous (λ b, (f b) ^ z) :=
(continuous_zpow z).comp h

@[to_additive]
lemma continuous_on_zpow {s : set G} (z : ℤ) : continuous_on (λ x, x ^ z) s :=
(continuous_zpow z).continuous_on

@[to_additive]
lemma continuous_at_zpow (x : G) (z : ℤ) : continuous_at (λ x, x ^ z) x :=
(continuous_zpow z).continuous_at

@[to_additive]
lemma filter.tendsto.zpow {α} {l : filter α} {f : α → G} {x : G} (hf : tendsto f l (𝓝 x)) (z : ℤ) :
  tendsto (λ x, f x ^ z) l (𝓝 (x ^ z)) :=
(continuous_at_zpow _ _).tendsto.comp hf

@[to_additive]
lemma continuous_within_at.zpow {f : α → G} {x : α} {s : set α} (hf : continuous_within_at f s x)
  (z : ℤ) : continuous_within_at (λ x, f x ^ z) s x :=
hf.zpow z

@[to_additive]
lemma continuous_at.zpow {f : α → G} {x : α} (hf : continuous_at f x) (z : ℤ) :
  continuous_at (λ x, f x ^ z) x :=
hf.zpow z

@[to_additive continuous_on.zsmul]
lemma continuous_on.zpow {f : α → G} {s : set α} (hf : continuous_on f s) (z : ℤ) :
  continuous_on (λ x, f x ^ z) s :=
λ x hx, (hf x hx).zpow z

end zpow

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

open mul_opposite

@[to_additive]
instance [group α] [has_continuous_inv α] : has_continuous_inv αᵐᵒᵖ :=
{ continuous_inv := continuous_induced_rng $ (@continuous_inv α _ _ _).comp continuous_unop }

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [group α] [topological_group α] :
  topological_group αᵐᵒᵖ := { }

variable (G)

@[to_additive]
lemma nhds_one_symm : comap has_inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
((homeomorph.inv G).comap_nhds_eq _).trans (congr_arg nhds inv_one)

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

/-- The (topological-space) closure of a subgroup of a space `M` with `has_continuous_mul` is
itself a subgroup. -/
@[to_additive "The (topological-space) closure of an additive subgroup of a space `M` with
`has_continuous_add` is itself an additive subgroup."]
def subgroup.topological_closure (s : subgroup G) : subgroup G :=
{ carrier := closure (s : set G),
  inv_mem' := λ g m, by simpa [←set.mem_inv, inv_closure] using m,
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

/-- The topological closure of a normal subgroup is normal.-/
@[to_additive "The topological closure of a normal additive subgroup is normal."]
lemma subgroup.is_normal_topological_closure {G : Type*} [topological_space G] [group G]
  [topological_group G] (N : subgroup G) [N.normal] :
  (subgroup.topological_closure N).normal :=
{ conj_mem := λ n hn g,
  begin
    apply mem_closure_of_continuous (topological_group.continuous_conj g) hn,
    intros m hm,
    exact subset_closure (subgroup.normal.conj_mem infer_instance m hm g),
  end }

@[to_additive] lemma mul_mem_connected_component_one {G : Type*} [topological_space G]
  [mul_one_class G] [has_continuous_mul G] {g h : G} (hg : g ∈ connected_component (1 : G))
  (hh : h ∈ connected_component (1 : G)) : g * h ∈ connected_component (1 : G) :=
begin
  rw connected_component_eq hg,
  have hmul: g ∈ connected_component (g*h),
  { apply continuous.image_connected_component_subset (continuous_mul_left g),
    rw ← connected_component_eq hh,
    exact ⟨(1 : G), mem_connected_component, by simp only [mul_one]⟩ },
  simpa [← connected_component_eq hmul] using (mem_connected_component)
end

@[to_additive] lemma inv_mem_connected_component_one {G : Type*} [topological_space G] [group G]
  [topological_group G] {g : G} (hg : g ∈ connected_component (1 : G)) :
  g⁻¹ ∈ connected_component (1 : G) :=
begin
  rw ← inv_one,
  exact continuous.image_connected_component_subset continuous_inv _
    ((set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)
end

/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive "The connected component of 0 is a subgroup of `G`."]
def subgroup.connected_component_of_one (G : Type*) [topological_space G] [group G]
  [topological_group G] : subgroup G :=
{ carrier  := connected_component (1 : G),
  one_mem' := mem_connected_component,
  mul_mem' := λ g h hg hh, mul_mem_connected_component_one hg hh,
  inv_mem' := λ g hg, inv_mem_connected_component_one hg }

/-- If a subgroup of a topological group is commutative, then so is its topological closure. -/
@[to_additive "If a subgroup of an additive topological group is commutative, then so is its
topological closure."]
def subgroup.comm_group_topological_closure [t2_space G] (s : subgroup G)
  (hs : ∀ (x y : s), x * y = y * x) : comm_group s.topological_closure :=
{ ..s.topological_closure.to_group,
  ..s.to_submonoid.comm_monoid_topological_closure hs }

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
            : map_mono (filter.prod_mono hconj $ le_rfl)
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

section div_in_topological_group
variables [group G] [topological_space G] [topological_group G]

/-- A version of `homeomorph.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive /-" A version of `homeomorph.add_left a (-b)` that is defeq to `a - b`. "-/,
  simps {simp_rhs := tt}]
def homeomorph.div_left (x : G) : G ≃ₜ G :=
{ continuous_to_fun := continuous_const.div' continuous_id,
  continuous_inv_fun := continuous_inv.mul continuous_const,
  .. equiv.div_left x }

@[to_additive] lemma is_open_map_div_left (a : G) : is_open_map ((/) a) :=
(homeomorph.div_left _).is_open_map

@[to_additive] lemma is_closed_map_div_left (a : G) : is_closed_map ((/) a) :=
(homeomorph.div_left _).is_closed_map

/-- A version of `homeomorph.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive /-" A version of `homeomorph.add_right (-a) b` that is defeq to `b - a`. "-/,
  simps {simp_rhs := tt}]
def homeomorph.div_right (x : G) : G ≃ₜ G :=
{ continuous_to_fun := continuous_id.div' continuous_const,
  continuous_inv_fun := continuous_id.mul continuous_const,
  .. equiv.div_right x }

@[to_additive]
lemma is_open_map_div_right (a : G) : is_open_map (λ x, x / a) :=
(homeomorph.div_right a).is_open_map

@[to_additive]
lemma is_closed_map_div_right (a : G) : is_closed_map (λ x, x / a) :=
(homeomorph.div_right a).is_closed_map

@[to_additive]
lemma tendsto_div_nhds_one_iff
  {α : Type*} {l : filter α} {x : G} {u : α → G} :
  tendsto (λ n, u n / x) l (𝓝 1) ↔ tendsto u l (𝓝 x) :=
begin
  have A : tendsto (λ (n : α), x) l (𝓝 x) := tendsto_const_nhds,
  exact ⟨λ h, by simpa using h.mul A, λ h, by simpa using h.div' A⟩
end

@[to_additive] lemma nhds_translation_div (x : G) : comap (/ x) (𝓝 1) = 𝓝 x :=
by simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

end div_in_topological_group

/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `submonoid.top_closure_mul_self_eq` in
`topology.algebra.monoid`.
-/

section has_continuous_mul
variables [topological_space α] [group α] [has_continuous_mul α] {s t : set α}

@[to_additive] lemma is_open.mul_left (ht : is_open t) : is_open (s * t) :=
by { rw ←Union_mul_left_image, exact is_open_bUnion (λ a ha, is_open_map_mul_left a t ht) }

@[to_additive] lemma is_open.mul_right (hs : is_open s) : is_open (s * t) :=
by { rw ←Union_mul_right_image, exact is_open_bUnion (λ a ha, is_open_map_mul_right a s hs) }

@[to_additive] lemma subset_interior_mul_left : interior s * t ⊆ interior (s * t) :=
interior_maximal (set.mul_subset_mul_right interior_subset) is_open_interior.mul_right

@[to_additive] lemma subset_interior_mul_right : s * interior t ⊆ interior (s * t) :=
interior_maximal (set.mul_subset_mul_left interior_subset) is_open_interior.mul_left

@[to_additive] lemma subset_interior_mul : interior s * interior t ⊆ interior (s * t) :=
(set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

end has_continuous_mul

section topological_group
variables [topological_space α] [group α] [topological_group α] {s t : set α}

@[to_additive] lemma is_open.div_left (ht : is_open t) : is_open (s / t) :=
by { rw ←Union_div_left_image, exact is_open_bUnion (λ a ha, is_open_map_div_left a t ht) }

@[to_additive] lemma is_open.div_right (hs : is_open s) : is_open (s / t) :=
by { rw ←Union_div_right_image, exact is_open_bUnion (λ a ha, is_open_map_div_right a s hs) }

@[to_additive] lemma subset_interior_div_left : interior s / t ⊆ interior (s / t) :=
interior_maximal (div_subset_div_right interior_subset) is_open_interior.div_right

@[to_additive] lemma subset_interior_div_right : s / interior t ⊆ interior (s / t) :=
interior_maximal (div_subset_div_left interior_subset) is_open_interior.div_left

@[to_additive] lemma subset_interior_div : interior s / interior t ⊆ interior (s / t) :=
(div_subset_div_left interior_subset).trans subset_interior_div_left

@[to_additive] lemma is_open.mul_closure (hs : is_open s) (t : set α) : s * closure t = s * t :=
begin
  refine (mul_subset_iff.2 $ λ a ha b hb, _).antisymm (mul_subset_mul_left subset_closure),
  rw mem_closure_iff at hb,
  have hbU : b ∈ s⁻¹ * {a * b} := ⟨a⁻¹, a * b, set.inv_mem_inv.2 ha, rfl, inv_mul_cancel_left _ _⟩,
  obtain ⟨_, ⟨c, d, hc, (rfl : d = _), rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU,
  exact ⟨c⁻¹, _, hc, hcs, inv_mul_cancel_left _ _⟩,
end

@[to_additive] lemma is_open.closure_mul (ht : is_open t) (s : set α) : closure s * t = s * t :=
by rw [←inv_inv (closure s * t), mul_inv_rev, inv_closure, ht.inv.mul_closure, mul_inv_rev, inv_inv,
  inv_inv]

@[to_additive] lemma is_open.div_closure (hs : is_open s) (t : set α) : s / closure t = s / t :=
by simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]

@[to_additive] lemma is_open.closure_div (ht : is_open t) (s : set α) : closure s / t = s / t :=
by simp_rw [div_eq_mul_inv, ht.inv.closure_mul]

end topological_group

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

@[to_additive]
lemma topological_group.t2_space [t1_space G] : t2_space G :=
@regular_space.t2_space G _ (topological_group.regular_space G)

variables {G} (S : subgroup G) [subgroup.normal S] [is_closed (S : set G)]

@[to_additive]
instance subgroup.regular_quotient_of_is_closed
  (S : subgroup G) [subgroup.normal S] [is_closed (S : set G)] : regular_space (G ⧸ S) :=
begin
  suffices : t1_space (G ⧸ S), { exact @topological_group.regular_space _ _ _ _ this, },
  have hS : is_closed (S : set G) := infer_instance,
  rw ← quotient_group.ker_mk S at hS,
  exact topological_group.t1_space (G ⧸ S) ((quotient_map_quotient_mk.is_closed_preimage).mp hS),
end

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/

variables [topological_space G] [group G] [topological_group G]

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `K * V ⊆ U`. -/
@[to_additive "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of
`0` such that `K + V ⊆ U`."]
lemma compact_open_separated_mul_right {K U : set G} (hK : is_compact K) (hU : is_open U)
  (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), K * V ⊆ U :=
begin
  apply hK.induction_on,
  { exact ⟨univ, by simp⟩ },
  { rintros s t hst ⟨V, hV, hV'⟩,
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩ },
  { rintros s t  ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩,
    use [V ∩ W, inter_mem V_in W_in],
    rw union_mul,
    exact union_subset ((mul_subset_mul_left (V.inter_subset_left W)).trans hV')
                       ((mul_subset_mul_left (V.inter_subset_right W)).trans hW') },
  { intros x hx,
    have := tendsto_mul (show U ∈ 𝓝 (x * 1), by simpa using hU.mem_nhds (hKU hx)),
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this,
    rcases this with ⟨t, ht, s, hs, h⟩,
    rw [← image_subset_iff, image_mul_prod] at h,
    exact ⟨t, mem_nhds_within_of_mem_nhds ht, s, hs, h⟩ }
end

open mul_opposite

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of
`0` such that `V + K ⊆ U`."]
lemma compact_open_separated_mul_left {K U : set G} (hK : is_compact K) (hU : is_open U)
  (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U :=
begin
  rcases compact_open_separated_mul_right (hK.image continuous_op) (op_homeomorph.is_open_map U hU)
    (image_subset op hKU) with ⟨V, (hV : V ∈ 𝓝 (op (1 : G))), hV' : op '' K * V ⊆ op '' U⟩,
  refine ⟨op ⁻¹' V, continuous_op.continuous_at hV, _⟩,
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'
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
  exact ⟨t, subset.trans ht $ Union₂_mono $ λ g hg, interior_subset⟩
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
  obtain ⟨y, hy⟩ := K.interior_nonempty,
  let F := homeomorph.mul_left (x * y⁻¹),
  refine ⟨F '' K, _, K.compact.image F.continuous⟩,
  suffices : F.symm ⁻¹' K ∈ 𝓝 x, by { convert this, apply equiv.image_eq_preimage },
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
def nhds_mul_hom : G →ₙ* (filter G) :=
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

section quotient
variables [group G] [topological_space G] [topological_group G] {Γ : subgroup G}

@[to_additive]
instance quotient_group.has_continuous_const_smul : has_continuous_const_smul G (G ⧸ Γ) :=
{ continuous_const_smul := λ g₀, begin
    apply continuous_coinduced_dom,
    change continuous (λ g : G, quotient_group.mk (g₀ * g)),
    exact continuous_coinduced_rng.comp (continuous_mul_left g₀),
  end }

@[to_additive]
lemma quotient_group.continuous_smul₁ (x : G ⧸ Γ) : continuous (λ g : G, g • x) :=
begin
  obtain ⟨g₀, rfl⟩ : ∃ g₀, quotient_group.mk g₀ = x,
  { exact @quotient.exists_rep _ (quotient_group.left_rel Γ) x },
  change continuous (λ g, quotient_group.mk (g * g₀)),
  exact continuous_coinduced_rng.comp (continuous_mul_right g₀)
end

@[to_additive]
instance quotient_group.has_continuous_smul [locally_compact_space G] :
  has_continuous_smul G (G ⧸ Γ) :=
{ continuous_smul := begin
    let F : G × G ⧸ Γ → G ⧸ Γ := λ p, p.1 • p.2,
    change continuous F,
    have H : continuous (F ∘ (λ p : G × G, (p.1, quotient_group.mk p.2))),
    { change continuous (λ p : G × G, quotient_group.mk (p.1 * p.2)),
      refine continuous_coinduced_rng.comp continuous_mul },
    exact quotient_map.continuous_lift_prod_right quotient_map_quotient_mk H,
  end }

end quotient

namespace units

open mul_opposite (continuous_op continuous_unop)

variables [monoid α] [topological_space α] [has_continuous_mul α] [monoid β] [topological_space β]
  [has_continuous_mul β]

@[to_additive] instance : topological_group αˣ :=
{ continuous_inv := continuous_induced_rng ((continuous_unop.comp
    (@continuous_embed_product α _ _).snd).prod_mk (continuous_op.comp continuous_coe)) }

/-- The topological group isomorphism between the units of a product of two monoids, and the product
    of the units of each monoid. -/
def homeomorph.prod_units : homeomorph (α × β)ˣ (αˣ × βˣ) :=
{ continuous_to_fun  :=
  begin
    show continuous (λ i : (α × β)ˣ, (map (monoid_hom.fst α β) i, map (monoid_hom.snd α β) i)),
    refine continuous.prod_mk _ _,
    { refine continuous_induced_rng ((continuous_fst.comp units.continuous_coe).prod_mk _),
      refine mul_opposite.continuous_op.comp (continuous_fst.comp _),
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

section lattice_ops

variables {ι : Sort*} [group G] [group H] {ts : set (topological_space G)}
  (h : ∀ t ∈ ts, @topological_group G t _) {ts' : ι → topological_space G}
  (h' : ∀ i, @topological_group G (ts' i) _) {t₁ t₂ : topological_space G}
  (h₁ : @topological_group G t₁ _) (h₂ : @topological_group G t₂ _)
  {t : topological_space H} [topological_group H] {F : Type*}
  [monoid_hom_class F G H] (f : F)

@[to_additive] lemma topological_group_Inf :
  @topological_group G (Inf ts) _ :=
{ continuous_inv := @has_continuous_inv.continuous_inv G (Inf ts) _
    (@has_continuous_inv_Inf _ _ _
      (λ t ht, @topological_group.to_has_continuous_inv G t _ (h t ht))),
  continuous_mul := @has_continuous_mul.continuous_mul G (Inf ts) _
    (@has_continuous_mul_Inf _ _ _
      (λ t ht, @topological_group.to_has_continuous_mul G t _ (h t ht))) }

include h'

@[to_additive] lemma topological_group_infi :
  @topological_group G (⨅ i, ts' i) _ :=
by {rw ← Inf_range, exact topological_group_Inf (set.forall_range_iff.mpr h')}

omit h'

include h₁ h₂

@[to_additive] lemma topological_group_inf :
  @topological_group G (t₁ ⊓ t₂) _ :=
by {rw inf_eq_infi, refine topological_group_infi (λ b, _), cases b; assumption}

omit h₁ h₂

@[to_additive] lemma topological_group_induced :
  @topological_group G (t.induced f) _ :=
{ continuous_inv :=
    begin
      letI : topological_space G := t.induced f,
      refine continuous_induced_rng _,
      simp_rw [function.comp, map_inv],
      exact continuous_inv.comp (continuous_induced_dom : continuous f)
    end,
  continuous_mul := @has_continuous_mul.continuous_mul G (t.induced f) _
    (@has_continuous_mul_induced G H _ _ t _ _ _ f) }

end lattice_ops

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
