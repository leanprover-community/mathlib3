/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import topology.algebra.ordered.basic
import algebra.order.with_zero

/-!
# The topology on linearly ordered commutative groups with zero

Let `Γ₀` be a linearly ordered commutative group to which we have adjoined a zero element.
Then `Γ₀` may naturally be endowed with a topology that turns `Γ₀` into a topological monoid.
Neighborhoods of zero are sets containing `{γ | γ < γ₀}` for some invertible element `γ₀`
and every invertible element is open.
In particular the topology is the following:
"a subset `U ⊆ Γ₀` is open if `0 ∉ U` or if there is an invertible
`γ₀ ∈ Γ₀ such that {γ | γ < γ₀} ⊆ U`", but this fact is not proven here since the neighborhoods
description is what is actually useful.

We prove this topology is ordered and regular (in addition to be compatible with the monoid
structure).

All this is useful to extend a valuation to a completion. This is an abstract version of how the
absolute value (resp. `p`-adic absolute value) on `ℚ` is extended to `ℝ` (resp. `ℚₚ`).

## Implementation notes

This topology is not defined as an instance since it may not be the desired topology on
a linearly ordered commutative group with zero. You can locally activate this topology using
`local attribute [instance] linear_ordered_comm_group_with_zero.topological_space`
All other instances will (`ordered_topology`, `regular_space`, `has_continuous_mul`) then follow.

-/

open_locale topological_space
open topological_space filter set

namespace linear_ordered_comm_group_with_zero

variables (Γ₀ : Type*) [linear_ordered_comm_group_with_zero Γ₀]

/-- The neighbourhoods around γ ∈ Γ₀, used in the definition of the topology on Γ₀.
These neighbourhoods are defined as follows:
A set s is a neighbourhood of 0 if there is an invertible γ₀ ∈ Γ₀ such that {γ | γ < γ₀} ⊆ s.
If γ ≠ 0, then every set that contains γ is a neighbourhood of γ. -/
def nhds_fun (x : Γ₀) : filter Γ₀ :=
if x = 0 then ⨅ (γ₀ : units Γ₀), principal {γ | γ < γ₀} else pure x

/-- The topology on a linearly ordered commutative group with a zero element adjoined.
A subset U is open if 0 ∉ U or if there is an invertible element γ₀ such that {γ | γ < γ₀} ⊆ U. -/
protected def topological_space : topological_space Γ₀ :=
topological_space.mk_of_nhds (nhds_fun Γ₀)

local attribute [instance] linear_ordered_comm_group_with_zero.topological_space

/-- The neighbourhoods {γ | γ < γ₀} of 0 form a directed set indexed by the invertible 
elements γ₀. -/
lemma directed_lt : directed (≥) (λ γ₀ : units Γ₀, principal {γ : Γ₀ | γ < γ₀}) :=
begin
  intros γ₁ γ₂,
  use linear_order.min γ₁ γ₂ ; dsimp only,
  split ; rw [ge_iff_le, principal_mono] ; intros x x_in,
  { calc x < ↑(linear_order.min γ₁ γ₂) : x_in
        ... ≤ γ₁ : min_le_left γ₁ γ₂ },
  { calc x < ↑(linear_order.min γ₁ γ₂) : x_in
        ... ≤ γ₂ : min_le_right γ₁ γ₂ }
end

-- We need two auxilliary lemmas to show that nhds_fun accurately describes the neighbourhoods
-- coming from the topology (that is defined in terms of nhds_fun).

/-- At all points of a linearly ordered commutative group with a zero element adjoined,
the pure filter is smaller than the filter given by nhds_fun. -/
lemma pure_le_nhds_fun : pure ≤ nhds_fun Γ₀ :=
λ x, by { by_cases hx : x = 0; simp [hx, nhds_fun] }

/-- For every point Γ₀, and every “neighbourhood” s of it (described by nhds_fun), there is a
smaller “neighbourhood” t ⊆ s, such that s is a “neighbourhood“ of all the points in t. -/
lemma nhds_fun_ok (x : Γ₀) {s} (s_in : s ∈ nhds_fun Γ₀ x) :
  (∃ t ∈ nhds_fun Γ₀ x, t ⊆ s ∧ ∀ y ∈ t, s ∈ nhds_fun Γ₀ y) :=
begin
  by_cases hx : x = 0,
  { simp only [hx, nhds_fun, exists_prop, if_true, eq_self_iff_true] at s_in ⊢,
    cases (mem_infi_of_directed (directed_lt Γ₀) _).mp s_in with γ₀ h,
    use {γ : Γ₀ | γ < γ₀},
    rw mem_principal at h,
    split,
    { apply mem_infi_of_mem γ₀,
      rw mem_principal },
    { refine ⟨h, λ y y_in, _⟩,
      by_cases hy : y = 0,
      { simp only [hy, if_true, eq_self_iff_true],
        apply mem_infi_of_mem γ₀,
        rwa mem_principal },
      { simp [hy, h y_in] } } },
  { simp only [hx, nhds_fun, exists_prop, if_false, mem_pure] at s_in ⊢,
    refine ⟨{x}, mem_singleton _, singleton_subset_iff.2 s_in, λ y y_in, _⟩,
    simpa [mem_singleton_iff.mp y_in, hx] }
end

variables  {Γ₀}

/-- The neighbourhood filter of an invertible element consists of all sets containing that 
element. -/
lemma nhds_coe_units (γ : units Γ₀) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀) :=
calc 𝓝 (γ : Γ₀) = nhds_fun Γ₀ γ : nhds_mk_of_nhds (nhds_fun Γ₀) γ (pure_le_nhds_fun Γ₀)
                                                   (nhds_fun_ok Γ₀)
              ... = pure (γ : Γ₀) : if_neg γ.ne_zero

/-- The neighbourhood filter of a nonzero element consists of all sets containing that 
element. -/
@[simp] lemma nhds_of_ne_zero (γ : Γ₀) (h : γ ≠ 0) :
  𝓝 γ = pure γ :=
nhds_coe_units (units.mk0 _ h)

/-- If γ is an invertible element of a linearly ordered group with zero element adjoined,
then {γ} is a neighbourhood of γ. -/
lemma singleton_nhds_of_units (γ : units Γ₀) : ({γ} : set Γ₀) ∈ 𝓝 (γ : Γ₀) :=
by simp

/-- If γ is a nonzero element of a linearly ordered group with zero element adjoined,
then {γ} is a neighbourhood of γ. -/
lemma singleton_nhds_of_ne_zero (γ : Γ₀) (h : γ ≠ 0) : ({γ} : set Γ₀) ∈ 𝓝 (γ : Γ₀) :=
by simp [h]

/-- If U is a neighbourhood of 0 in a linearly ordered group with zero element adjoined,
then there exists an invertible element γ₀ such that {γ | γ < γ₀} ⊆ U. -/
lemma has_basis_nhds_zero :
  has_basis (𝓝 (0 : Γ₀)) (λ _, true) (λ γ₀ : units Γ₀, {γ : Γ₀ | γ < γ₀}) :=
⟨begin
  intro U,
  rw nhds_mk_of_nhds (nhds_fun Γ₀) 0 (pure_le_nhds_fun Γ₀) (nhds_fun_ok Γ₀),
  simp only [nhds_fun, if_true, eq_self_iff_true, exists_true_left],
  simp_rw [mem_infi_of_directed (directed_lt Γ₀), mem_principal]
end⟩

/-- If γ is an invertible element of a linearly ordered group with zero element adjoined,
then {x | x < γ} is a neighbourhood of 0. -/
lemma nhds_zero_of_units (γ : units Γ₀) : {x : Γ₀ | x < γ} ∈ 𝓝 (0 : Γ₀) :=
by { rw has_basis_nhds_zero.mem_iff, use γ, simp }

lemma tendsto_zero {α : Type*} {F : filter α} {f : α → Γ₀} :
  tendsto f F (𝓝 (0 : Γ₀)) ↔ ∀ γ₀ : units Γ₀, { x : α | f x < γ₀ } ∈ F :=
by simpa using has_basis_nhds_zero.tendsto_right_iff

/-- If γ is a nonzero element of a linearly ordered group with zero element adjoined,
then {x | x < γ} is a neighbourhood of 0. -/
lemma nhds_zero_of_ne_zero (γ : Γ₀) (h : γ ≠ 0) : {x : Γ₀ | x < γ} ∈ 𝓝 (0 : Γ₀) :=
nhds_zero_of_units (units.mk0 _ h)

lemma has_basis_nhds_units (γ : units Γ₀) :
  has_basis (𝓝 (γ : Γ₀)) (λ i : unit, true) (λ i, {γ}) :=
begin
  rw nhds_of_ne_zero _ γ.ne_zero,
  exact has_basis_pure γ
end

lemma has_basis_nhds_of_ne_zero {x : Γ₀} (h : x ≠ 0) :
  has_basis (𝓝 x) (λ i : unit, true) (λ i, {x}) :=
has_basis_nhds_units (units.mk0 x h)

lemma tendsto_units {α : Type*} {F : filter α} {f : α → Γ₀} {γ₀ : units Γ₀} :
  tendsto f F (𝓝 (γ₀ : Γ₀)) ↔ { x : α | f x = γ₀ } ∈ F :=
begin
  rw (has_basis_nhds_units γ₀).tendsto_right_iff,
  simpa
end

lemma tendsto_of_ne_zero {α : Type*} {F : filter α} {f : α → Γ₀} {γ : Γ₀} (h : γ ≠ 0) :
  tendsto f F (𝓝 γ) ↔ { x : α | f x = γ } ∈ F :=
@tendsto_units _ _ _ F f (units.mk0 γ h)

variable (Γ₀)

/-- The topology on a linearly ordered group with zero element adjoined
is compatible with the order structure. -/
@[priority 100]
instance ordered_topology : order_closed_topology Γ₀ :=
{ is_closed_le' :=
  begin
    rw ← is_open_compl_iff,
    show is_open {p : Γ₀ × Γ₀ | ¬p.fst ≤ p.snd},
    simp only [not_le],
    rw is_open_iff_mem_nhds,
    rintros ⟨a,b⟩ hab,
    change b < a at hab,
    have ha : a ≠ 0 := ne_zero_of_lt hab,
    rw [nhds_prod_eq, mem_prod_iff],
    by_cases hb : b = 0,
    { subst b,
      use [{a}, singleton_nhds_of_ne_zero _ ha, {x : Γ₀ | x < a}, nhds_zero_of_ne_zero _ ha],
      intros p p_in,
      cases mem_prod.1 p_in with h1 h2,
      rw mem_singleton_iff at h1,
      change p.2 < p.1,
      rwa h1 },
    { use [{a}, singleton_nhds_of_ne_zero _ ha, {b}, singleton_nhds_of_ne_zero _ hb],
      intros p p_in,
      cases mem_prod.1 p_in with h1 h2,
      rw mem_singleton_iff at h1 h2,
      change p.2 < p.1,
      rwa [h1, h2] }
  end }

/-- The topology on a linearly ordered group with zero element adjoined is T₃ (aka regular). -/
@[priority 100]
instance regular_space : regular_space Γ₀ :=
begin
  haveI : t1_space Γ₀ := t2_space.t1_space,
  split,
  intros s x s_closed x_not_in_s,
  by_cases hx : x = 0,
  { refine ⟨s, _, subset.rfl, _⟩,
    { subst x,
      rw is_open_iff_mem_nhds,
      intros y hy,
      by_cases hy' : y = 0, { subst y, contradiction },
      simpa [hy'] },
    { erw inf_eq_bot_iff,
      use sᶜ,
      simp only [exists_prop, mem_principal],
      exact ⟨s_closed.compl_mem_nhds x_not_in_s, ⟨s, subset.refl s, by simp⟩⟩ } },
  { simp only [nhds_within, inf_eq_bot_iff, exists_prop, mem_principal],
    exact ⟨{x}ᶜ, is_open_compl_iff.mpr is_closed_singleton, by rwa subset_compl_singleton_iff,
           {x}, singleton_nhds_of_ne_zero x hx, {x}ᶜ, by simp [subset.refl]⟩ }
end

/-- The topology on a linearly ordered group with zero element adjoined makes it a topological
monoid. -/
@[priority 100]
instance : has_continuous_mul Γ₀ :=
⟨begin
  have common : ∀ y ≠ (0 : Γ₀), continuous_at (λ (p : Γ₀ × Γ₀), p.fst * p.snd) (0, y),
  { intros y hy,
    set γ := units.mk0 y hy,
    suffices : tendsto (λ (p : Γ₀ × Γ₀), p.fst * p.snd) ((𝓝 0).prod (𝓝 γ)) (𝓝 0),
    by simpa [continuous_at, nhds_prod_eq],
    suffices : ∀ (γ' : units Γ₀), ∃ (γ''  : units Γ₀), ∀ (a b : Γ₀), a < γ'' → b = y → a * b < γ',
    { rw (has_basis_nhds_zero.prod $ has_basis_nhds_units γ).tendsto_iff has_basis_nhds_zero,
      simpa },
    intros γ',
    use γ⁻¹*γ',
    rintros a b ha hb,
    rw [hb, mul_comm],
    rw [units.coe_mul] at ha,
    simpa using inv_mul_lt_of_lt_mul₀ ha },
  rw continuous_iff_continuous_at,
  rintros ⟨x, y⟩,
  by_cases hx : x = 0; by_cases hy : y = 0,
  { suffices : tendsto (λ (p : Γ₀ × Γ₀), p.fst * p.snd) (𝓝 (0, 0)) (𝓝 0),
    by simpa [hx, hy, continuous_at],
    suffices : ∀ (γ : units Γ₀), ∃ (γ' : units Γ₀), ∀ (a b : Γ₀), a < γ' → b < γ' → a * b < γ,
    by simpa [nhds_prod_eq, has_basis_nhds_zero.prod_self.tendsto_iff has_basis_nhds_zero],
    intros γ,
    rcases exists_square_le γ with ⟨γ', h⟩,
    use γ',
    intros a b ha hb,
    calc a*b < γ'*γ' : mul_lt_mul₀ ha hb
    ... ≤ γ : by exact_mod_cast h },
  { rw hx,
    exact common y hy },
  { rw hy,
    have : (λ (p : Γ₀ × Γ₀), p.fst * p.snd) =
           (λ (p : Γ₀ × Γ₀), p.fst * p.snd) ∘ (λ p : Γ₀ × Γ₀, (p.2, p.1)),
    by { ext, rw [mul_comm] },
    rw this,
    apply continuous_at.comp _ continuous_swap.continuous_at,
    exact common x hx },
  { change tendsto _ _ _,
    rw [nhds_prod_eq],
    rw ((has_basis_nhds_of_ne_zero hx).prod (has_basis_nhds_of_ne_zero hy)).tendsto_iff
       (has_basis_nhds_of_ne_zero $ mul_ne_zero hx hy),
    suffices : ∀ (a b : Γ₀), a = x → b = y → a * b = x * y, by simpa,
    rintros a b rfl rfl,
    refl },
end⟩

end linear_ordered_comm_group_with_zero
