/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.order.basic
import topology.algebra.group.basic

/-!
# Topology on a linear ordered additive commutative group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a linear ordered additive commutative group with order topology is a
topological group. We also prove continuity of `abs : G → G` and provide convenience lemmas like
`continuous_at.abs`.
-/

open set filter
open_locale topology filter

variables {α G : Type*} [topological_space G] [linear_ordered_add_comm_group G] [order_topology G]
variables {l : filter α} {f g : α → G}

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_add_comm_group.topological_add_group : topological_add_group G :=
{ continuous_add :=
    begin
      refine continuous_iff_continuous_at.2 _,
      rintro ⟨a, b⟩,
      refine linear_ordered_add_comm_group.tendsto_nhds.2 (λ ε ε0, _),
      rcases dense_or_discrete 0 ε with (⟨δ, δ0, δε⟩|⟨h₁, h₂⟩),
      { -- If there exists `δ ∈ (0, ε)`, then we choose `δ`-nhd of `a` and `(ε-δ)`-nhd of `b`
        filter_upwards [(eventually_abs_sub_lt a δ0).prod_nhds
          (eventually_abs_sub_lt b (sub_pos.2 δε))],
        rintros ⟨x, y⟩ ⟨hx : |x - a| < δ, hy : |y - b| < ε - δ⟩,
        rw [add_sub_add_comm],
        calc |x - a + (y - b)| ≤ |x - a| + |y - b| : abs_add _ _
        ... < δ + (ε - δ) : add_lt_add hx hy
        ... = ε : add_sub_cancel'_right _ _ },
      { -- Otherwise `ε`-nhd of each point `a` is `{a}`
        have hε : ∀ {x y}, |x - y| < ε → x = y,
        { intros x y h,
          simpa [sub_eq_zero] using h₂ _ h },
        filter_upwards [(eventually_abs_sub_lt a ε0).prod_nhds (eventually_abs_sub_lt b ε0)],
        rintros ⟨x, y⟩ ⟨hx : |x - a| < ε, hy : |y - b| < ε⟩,
        simpa [hε hx, hε hy] }
    end,
  continuous_neg := continuous_iff_continuous_at.2 $ λ a,
    linear_ordered_add_comm_group.tendsto_nhds.2 $ λ ε ε0,
      (eventually_abs_sub_lt a ε0).mono $ λ x hx, by rwa [neg_sub_neg, abs_sub_comm] }

@[continuity]
lemma continuous_abs : continuous (abs : G → G) := continuous_id.max continuous_neg

protected lemma filter.tendsto.abs {a : G} (h : tendsto f l (𝓝 a)) :
  tendsto (λ x, |f x|) l (𝓝 (|a|)) :=
(continuous_abs.tendsto _).comp h

lemma tendsto_zero_iff_abs_tendsto_zero (f : α → G) :
  tendsto f l (𝓝 0) ↔ tendsto (abs ∘ f) l (𝓝 0) :=
begin
  refine ⟨λ h, (abs_zero : |(0 : G)| = 0) ▸ h.abs, λ h, _⟩,
  have : tendsto (λ a, -|f a|) l (𝓝 0) := (neg_zero : -(0 : G) = 0) ▸ h.neg,
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le this h
    (λ x, neg_abs_le_self $ f x) (λ x, le_abs_self $ f x),
end

variables [topological_space α] {a : α} {s : set α}

protected lemma continuous.abs (h : continuous f) : continuous (λ x, |f x|) := continuous_abs.comp h

protected lemma continuous_at.abs (h : continuous_at f a) : continuous_at (λ x, |f x|) a := h.abs

protected lemma continuous_within_at.abs (h : continuous_within_at f s a) :
  continuous_within_at (λ x, |f x|) s a := h.abs

protected lemma continuous_on.abs (h : continuous_on f s) : continuous_on (λ x, |f x|) s :=
λ x hx, (h x hx).abs

lemma tendsto_abs_nhds_within_zero : tendsto (abs : G → G) (𝓝[≠] 0) (𝓝[>] 0) :=
(continuous_abs.tendsto' (0 : G) 0 abs_zero).inf $ tendsto_principal_principal.2 $ λ x, abs_pos.2
