/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import algebra.archimedean
import algebra.iterate_hom
import order.iterate

/-!
# Bounded functions and archimedean additive groups

In this file we prove a few lemmas about functions with bounded (above or below) range taking values
in an archimedean additive commutative group. These lemmas are used in the construction of a
conditionally complete lattice structure on `circle_deg1_lift`. They are stated for any archimedean
additive commutative group instead of `ℝ` (a) because we can do it, so why not?  (b) because this
way we can use the `order_dual` trick to get lemmas about `bdd_below` from lemmas about `bdd_above`.
-/

open set

variables {α β G : Type*} [ordered_add_comm_group G] [archimedean G] [preorder β]

/-- Let `G` be an additive commutative archimedean group `G`. Let `f a`, `a : α` be a family of
monotone functions `f a : G → β` taking values in a preordered type. Suppose that for some `x > 0`,
`f a (y + x)` is bounded above by some monotone function of `f a y`, and the estimate is uniform in
`a` and `y`. Then the predicate “the range of `λ a, f a y` is bounded above” does not depend
actually on `y`: for any two `y z : G`, the corresponding statements are equivalent. -/
lemma bdd_above_iff_of_mono_of_map_add_le {f : α → G → β} {x : G} (hx : 0 < x) {g : β → β}
  (hf_mono : ∀ a, monotone (f a)) (hg_mono : monotone g)
  (hfg : ∀ a y, f a (y + x) ≤ g (f a y)) (y z : G) :
  bdd_above (range $ λ a, f a y) ↔ bdd_above (range $ λ a, f a z) :=
begin
  suffices : ∀ y z, bdd_above (range $ λ a, f a y) → bdd_above (range $ λ a, f a z),
    from ⟨this y z, this z y⟩,
  clear y z, rintros y z ⟨b, hb⟩, simp only [mem_upper_bounds, forall_range_iff] at hb,
  rcases archimedean.arch (z - y) hx with ⟨m, hm⟩,
  refine ⟨g^[m] b, _⟩,
  rintro _ ⟨a, rfl⟩,
  calc f a z ≤ f a (y + m • x)   : hf_mono a (sub_le_iff_le_add'.1 hm)
         ... = f a ((+ x)^[m] y) : by rw add_right_iterate
         ... ≤ (g^[m] (f a y))   : hg_mono.le_iterate_comp_of_le (hfg a) _ _
         ... ≤ (g^[m] b)         : hg_mono.iterate m (hb a)
end

/-- Let `G` be an additive commutative archimedean group `G`. Let `f a`, `a : α` be a family of
monotone functions `f a : G → β` taking values in a preordered type. Suppose that for some `x > 0`,
`f a (y + x)` is bounded above by some monotone function of `f a y`, and the estimate is uniform in
`a` and `y`. Then the predicate `p y` defined as “the range of `λ a, f a y` is bounded above” does
not actually depend on `y`: the statements `∀ y, p y` and `∃ y, p y` are equivalent. -/
lemma forall_bdd_above_iff_exists_of_mono_of_map_add_le {f : α → G → β} {x : G} (hx : 0 < x)
  {g : β → β} (hf_mono : ∀ a, monotone (f a)) (hg_mono : monotone g)
  (hfg : ∀ a y, f a (y + x) ≤ g (f a y)) :
  (∀ y, bdd_above (range $ λ a, f a y)) ↔ (∃ y, bdd_above (range $ λ a, f a y)) :=
⟨λ H, ⟨0, H 0⟩, λ ⟨y, hy⟩ z, (bdd_above_iff_of_mono_of_map_add_le hx hf_mono hg_mono hfg _ _).1 hy⟩

/-- Let `G` be an additive commutative archimedean group `G`. Let `f a`, `a : α` be a family of
monotone functions `f a : G → β` taking values in a preordered type. Suppose that for some `x > 0`,
`f a (y - x)` is bounded below by some monotone function of `f a y`, and the estimate is uniform in
`a` and `y`. Then the predicate “the range of `λ a, f a y` is bounded below” does not depend
actually on `y`: for any two `y z : G`, the corresponding statements are equivalent. -/
lemma bdd_below_iff_of_mono_of_map_add_le {f : α → G → β} {x : G} (hx : 0 < x) {g : β → β}
  (hf_mono : ∀ a, monotone (f a)) (hg_mono : monotone g)
  (hfg : ∀ a y, g (f a y) ≤ f a (y - x)) (y z : G) :
  bdd_below (range $ λ a, f a y) ↔ bdd_below (range $ λ a, f a z) :=
@bdd_above_iff_of_mono_of_map_add_le α (order_dual β) (order_dual G) _ _ _ f (-x) (neg_pos.2 hx) g
  (λ a, (hf_mono a).order_dual) hg_mono.order_dual (by simpa only [← sub_eq_add_neg]) _ _

/-- Let `G` be an additive commutative archimedean group `G`. Let `f a`, `a : α` be a family of
monotone functions `f a : G → β` taking values in a preordered type. Suppose that for some `x > 0`,
`f a (y - x)` is bounded below by some monotone function of `f a y`, and the estimate is uniform in
`a` and `y`. Then the predicate `p y` defined as “the range of `λ a, f a y` is bounded below” does
not actually depend on `y`: the statements `∀ y, p y` and `∃ y, p y` are equivalent. -/
lemma forall_bdd_below_iff_exists_of_mono_of_map_add_le {f : α → G → β} {x : G} (hx : 0 < x)
  {g : β → β} (hf_mono : ∀ a, monotone (f a)) (hg_mono : monotone g)
  (hfg : ∀ a y, g (f a y) ≤ f a (y - x)) :
  (∀ y, bdd_below (range $ λ a, f a y)) ↔ (∃ y, bdd_below (range $ λ a, f a y)) :=
⟨λ H, ⟨0, H 0⟩, λ ⟨y, hy⟩ z, (bdd_below_iff_of_mono_of_map_add_le hx hf_mono hg_mono hfg _ _).1 hy⟩
