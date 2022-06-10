/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.extreme
import topology.algebra.order.basic

/-!
# To move
-/

open filter set topological_space
open_locale topological_space

variables {𝕜 E F : Type*}

section ordered_semiring
variables [ordered_semiring 𝕜] [add_comm_monoid E] [add_comm_monoid F] [module 𝕜 E] [module 𝕜 F]

lemma segment_prod_subset (x y : E × F) : segment 𝕜 x y ⊆ segment 𝕜 x.1 y.1 ×ˢ segment 𝕜 x.2 y.2 :=
begin
  rintro z ⟨a, b, ha, hb, hab, hz⟩,
  exact ⟨⟨a, b, ha, hb, hab, congr_arg prod.fst hz⟩, a, b, ha, hb, hab, congr_arg prod.snd hz⟩,
end

lemma open_segment_prod_subset (x y : E × F) :
  open_segment 𝕜 x y ⊆ open_segment 𝕜 x.1 y.1 ×ˢ open_segment 𝕜 x.2 y.2 :=
begin
  rintro z ⟨a, b, ha, hb, hab, hz⟩,
  exact ⟨⟨a, b, ha, hb, hab, congr_arg prod.fst hz⟩, a, b, ha, hb, hab, congr_arg prod.snd hz⟩,
end

lemma extreme_points_prod (s : set E) (t : set F) :
  extreme_points 𝕜 (s ×ˢ t) = extreme_points 𝕜 s ×ˢ extreme_points 𝕜 t :=
begin
  ext,
  refine iff.trans (and_congr_right $ λ hx, ⟨λ h, _, λ h, _⟩) (and_and_and_comm _ _ _ _),
  split,
  { rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩,
    refine (h (mk_mem_prod hx₁ hx.2) (mk_mem_prod hx₂ hx.2) _).imp
      (congr_arg prod.fst) (congr_arg prod.fst),
    refine ⟨a, b, ha, hb, hab, prod.ext hx' _⟩,
    simp_rw [prod.smul_mk, prod.mk_add_mk, convex.combo_self hab] },
  { rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩,
    refine (h (mk_mem_prod hx.1 hx₁) (mk_mem_prod hx.1 hx₂) _).imp
      (congr_arg prod.snd) (congr_arg prod.snd),
    refine ⟨a, b, ha, hb, hab, prod.ext _ hx'⟩,
    simp_rw [prod.smul_mk, prod.mk_add_mk, convex.combo_self hab] },
  { rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩,
    simp_rw prod.ext_iff,
    exact (and_and_and_comm _ _ _ _).1
     ⟨h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congr_arg prod.fst hx'⟩,
      h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congr_arg prod.snd hx'⟩⟩ }
end

end ordered_semiring

section
variables [linear_ordered_field 𝕜] [topological_space 𝕜] [first_countable_topology 𝕜]
  [order_topology 𝕜] [add_comm_group E] [topological_space E] [has_continuous_add E] [module 𝕜 E]
  [has_continuous_smul 𝕜 E] {s t : set E}

-- Prop 8.5
lemma is_extreme.subset_frontier (h : is_extreme 𝕜 s t) (hts : t ⊂ s) : t ⊆ frontier s :=
begin
  rintro x hx,
  obtain ⟨y, hys, hyt⟩ := not_subset_iff_exists_mem_not_mem.1 hts.2,
  rw frontier_eq_closure_inter_closure,
  refine ⟨subset_closure $ hts.1 hx, _⟩,
  obtain ⟨u, -, hu₁, hu⟩ := exists_seq_strict_anti_tendsto (1 : 𝕜),
  let z : ℕ → E := λ n, u n • x + (1 - u n) • y,
  have hz : tendsto z at_top (𝓝 x),
  { convert (hu.smul_const x).add ((hu.const_sub 1).smul_const y) using 2,
    rw [one_smul, sub_self, zero_smul, add_zero] },
  refine mem_closure_of_tendsto hz (eventually_of_forall $ λ n hn, hyt (h.2 hys hn hx _).1),
  have hu₀ : 0 < u n := zero_lt_one.trans (hu₁ _),
  refine ⟨(u n - 1) / u n, 1 / u n, div_pos (sub_pos_of_lt $ hu₁ _) hu₀, one_div_pos.2 hu₀, _, _⟩,
  { rw [←add_div, sub_add_cancel, div_self hu₀.ne'] },
  rw [smul_add, one_div, inv_smul_smul₀ hu₀.ne', add_left_comm, ←mul_smul, ←add_smul,
    inv_mul_eq_div, ←add_div, ←neg_sub, neg_add_self, zero_div, zero_smul, add_zero],
end

end
