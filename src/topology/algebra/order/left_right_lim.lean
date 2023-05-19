/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.order.basic
import topology.algebra.order.left_right

/-!
# Left and right limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the (strict) left and right limits of a function.

* `left_lim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `right_lim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).

We develop a comprehensive API for monotone functions. Notably,

* `monotone.continuous_at_iff_left_lim_eq_right_lim` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `monotone.countable_not_continuous_at` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

We also port the API to antitone functions.

## TODO

Prove corresponding stronger results for strict_mono and strict_anti functions.
-/

open set filter
open_locale topology

section

variables {α β : Type*} [linear_order α] [topological_space β]

/-- Let `f : α → β` be a function from a linear order `α` to a topological_space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `left_lim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the function has no left
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
@[irreducible] noncomputable def function.left_lim (f : α → β) (a : α) : β :=
begin
  classical,
  haveI : nonempty β := ⟨f a⟩,
  letI : topological_space α := preorder.topology α,
  exact if (𝓝[<] a = ⊥) ∨ ¬(∃ y, tendsto f (𝓝[<] a) (𝓝 y)) then f a
    else lim (𝓝[<] a) f
end

/-- Let `f : α → β` be a function from a linear order `α` to a topological_space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `right_lim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the function has no right
limit, , we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def function.right_lim (f : α → β) (a : α) : β :=
@function.left_lim αᵒᵈ β  _ _ f a

open function

lemma left_lim_eq_of_tendsto
  [hα : topological_space α] [h'α : order_topology α] [t2_space β]
  {f : α → β} {a : α} {y : β} (h : 𝓝[<] a ≠ ⊥) (h' : tendsto f (𝓝[<] a) (𝓝 y)) :
  left_lim f a = y :=
begin
  have h'' : ∃ y, tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩,
  rw [h'α.topology_eq_generate_intervals] at h h' h'',
  simp only [left_lim, h, h'', not_true, or_self, if_false],
  haveI := ne_bot_iff.2 h,
  exact h'.lim_eq,
end

lemma left_lim_eq_of_eq_bot [hα : topological_space α] [h'α : order_topology α]
  (f : α → β) {a : α} (h : 𝓝[<] a = ⊥) :
  left_lim f a = f a :=
begin
  rw [h'α.topology_eq_generate_intervals] at h,
  simp [left_lim, ite_eq_left_iff, h],
end

end

open function

namespace monotone

variables {α β : Type*} [linear_order α] [conditionally_complete_linear_order β]
[topological_space β] [order_topology β] {f : α → β} (hf : monotone f) {x y : α}
include hf

lemma left_lim_eq_Sup [topological_space α] [order_topology α] (h : 𝓝[<] x ≠ ⊥) :
  left_lim f x = Sup (f '' (Iio x)) :=
left_lim_eq_of_tendsto h (hf.tendsto_nhds_within_Iio x)

lemma left_lim_le (h : x ≤ y) : left_lim f x ≤ f y :=
begin
  letI : topological_space α := preorder.topology α,
  haveI : order_topology α := ⟨rfl⟩,
  rcases eq_or_ne (𝓝[<] x) ⊥ with h'|h',
  { simpa [left_lim, h'] using hf h },
  haveI A : ne_bot (𝓝[<] x) := ne_bot_iff.2 h',
  rw left_lim_eq_Sup hf h',
  refine cSup_le _ _,
  { simp only [nonempty_image_iff],
    exact (forall_mem_nonempty_iff_ne_bot.2 A) _ self_mem_nhds_within },
  { simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
    assume z hz,
    exact hf (hz.le.trans h) },
end

lemma le_left_lim (h : x < y) : f x ≤ left_lim f y :=
begin
  letI : topological_space α := preorder.topology α,
  haveI : order_topology α := ⟨rfl⟩,
  rcases eq_or_ne (𝓝[<] y) ⊥ with h'|h',
  { rw left_lim_eq_of_eq_bot _ h', exact hf h.le },
  rw left_lim_eq_Sup hf h',
  refine le_cSup ⟨f y, _⟩ (mem_image_of_mem _ h),
  simp only [upper_bounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_set_of_eq],
  assume z hz,
  exact hf hz.le
end

@[mono] protected lemma left_lim : monotone (left_lim f) :=
begin
  assume x y h,
  rcases eq_or_lt_of_le h with rfl|hxy,
  { exact le_rfl },
  { exact (hf.left_lim_le le_rfl).trans (hf.le_left_lim hxy) }
end

lemma le_right_lim (h : x ≤ y) : f x ≤ right_lim f y :=
hf.dual.left_lim_le h

lemma right_lim_le (h : x < y) : right_lim f x ≤ f y :=
hf.dual.le_left_lim h

@[mono] protected lemma right_lim : monotone (right_lim f) :=
λ x y h, hf.dual.left_lim h

lemma left_lim_le_right_lim (h : x ≤ y) : left_lim f x ≤ right_lim f y :=
(hf.left_lim_le le_rfl).trans (hf.le_right_lim h)

lemma right_lim_le_left_lim (h : x < y) : right_lim f x ≤ left_lim f y :=
begin
  letI : topological_space α := preorder.topology α,
  haveI : order_topology α := ⟨rfl⟩,
  rcases eq_or_ne (𝓝[<] y) ⊥ with h'|h',
  { simp [left_lim, h'],
    exact right_lim_le hf h },
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).nonempty :=
    forall_mem_nonempty_iff_ne_bot.2 (ne_bot_iff.2 h') (Ioo x y)
      (Ioo_mem_nhds_within_Iio ⟨h, le_refl _⟩),
  calc right_lim f x ≤ f a : hf.right_lim_le xa
  ... ≤ left_lim f y : hf.le_left_lim ay
end

variables [topological_space α] [order_topology α]

lemma tendsto_left_lim (x : α) : tendsto f (𝓝[<] x) (𝓝 (left_lim f x)) :=
begin
  rcases eq_or_ne (𝓝[<] x) ⊥ with h'|h',
  { simp [h'] },
  rw left_lim_eq_Sup hf h',
  exact hf.tendsto_nhds_within_Iio x
end

lemma tendsto_left_lim_within (x : α) : tendsto f (𝓝[<] x) (𝓝[≤] (left_lim f x)) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within f (hf.tendsto_left_lim x),
  filter_upwards [self_mem_nhds_within] with y hy using hf.le_left_lim hy,
end

lemma tendsto_right_lim (x : α) :
  tendsto f (𝓝[>] x) (𝓝 (right_lim f x)) :=
hf.dual.tendsto_left_lim x

lemma tendsto_right_lim_within (x : α) :
  tendsto f (𝓝[>] x) (𝓝[≥] (right_lim f x)) :=
hf.dual.tendsto_left_lim_within x

/-- A monotone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
lemma continuous_within_at_Iio_iff_left_lim_eq  :
  continuous_within_at f (Iio x) x ↔ left_lim f x = f x :=
begin
  rcases eq_or_ne (𝓝[<] x) ⊥ with h'|h',
  { simp [left_lim_eq_of_eq_bot f h', continuous_within_at, h'] },
  haveI : (𝓝[Iio x] x).ne_bot := ne_bot_iff.2 h',
  refine ⟨λ h, tendsto_nhds_unique (hf.tendsto_left_lim x) h.tendsto, λ h, _⟩,
  have := hf.tendsto_left_lim x,
  rwa h at this,
end

/-- A monotone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
lemma continuous_within_at_Ioi_iff_right_lim_eq :
  continuous_within_at f (Ioi x) x ↔ right_lim f x = f x :=
hf.dual.continuous_within_at_Iio_iff_left_lim_eq

/-- A monotone function is continuous at a point if and only if its left and right limits
coincide. -/
lemma continuous_at_iff_left_lim_eq_right_lim :
  continuous_at f x ↔ left_lim f x = right_lim f x :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have A : left_lim f x = f x,
      from (hf.continuous_within_at_Iio_iff_left_lim_eq).1 h.continuous_within_at,
    have B : right_lim f x = f x,
      from (hf.continuous_within_at_Ioi_iff_right_lim_eq).1 h.continuous_within_at,
    exact A.trans B.symm },
  { have h' : left_lim f x = f x,
    { apply le_antisymm (left_lim_le hf (le_refl _)),
      rw h,
      exact le_right_lim hf (le_refl _) },
    refine continuous_at_iff_continuous_left'_right'.2 ⟨_, _⟩,
    { exact hf.continuous_within_at_Iio_iff_left_lim_eq.2 h' },
    { rw h at h',
      exact hf.continuous_within_at_Ioi_iff_right_lim_eq.2 h' } },
end

/-- In a second countable space, the set of points where a monotone function is not right-continuous
is at most countable. Superseded by `countable_not_continuous_at` which gives the two-sided
version. -/
lemma countable_not_continuous_within_at_Ioi [topological_space.second_countable_topology β] :
  set.countable {x | ¬(continuous_within_at f (Ioi x) x)} :=
begin
  /- If `f` is not continuous on the right at `x`, there is an interval `(f x, z x)` which is not
  reached by `f`. This gives a family of disjoint open intervals in `β`. Such a family can only
  be countable as `β` is second-countable. -/
  nontriviality α,
  let s := {x | ¬(continuous_within_at f (Ioi x) x)},
  have : ∀ x, x ∈ s → ∃ z, f x < z ∧ ∀ y, x < y → z ≤ f y,
  { rintros x (hx : ¬(continuous_within_at f (Ioi x) x)),
    contrapose! hx,
    refine tendsto_order.2 ⟨λ m hm, _, λ u hu, _⟩,
    { filter_upwards [self_mem_nhds_within] with y hy using hm.trans_le (hf (le_of_lt hy)) },
    rcases hx u hu with ⟨v, xv, fvu⟩,
    have : Ioo x v ∈ 𝓝[>] x, from Ioo_mem_nhds_within_Ioi ⟨le_refl _, xv⟩,
    filter_upwards [this] with y hy,
    apply (hf hy.2.le).trans_lt fvu },
  -- choose `z x` such that `f` does not take the values in `(f x, z x)`.
  choose! z hz using this,
  have I : inj_on f s,
  { apply strict_mono_on.inj_on,
    assume x hx y hy hxy,
    calc f x < z x : (hz x hx).1
    ... ≤ f y : (hz x hx).2 y hxy },
  -- show that `f s` is countable by arguing that a disjoint family of disjoint open intervals
  -- (the intervals `(f x, z x)`) is at most countable.
  have fs_count : (f '' s).countable,
  { have A : (f '' s).pairwise_disjoint (λ x, Ioo x (z (inv_fun_on f s x))),
    { rintros _ ⟨u, us, rfl⟩ _ ⟨v, vs, rfl⟩ huv,
      wlog hle : u ≤ v generalizing u v,
      { exact (this v vs u us huv.symm (le_of_not_le hle)).symm },
      have hlt : u < v, from hle.lt_of_ne (ne_of_apply_ne _ huv),
      apply disjoint_iff_forall_ne.2,
      rintros a ha b hb rfl,
      simp only [I.left_inv_on_inv_fun_on us, I.left_inv_on_inv_fun_on vs] at ha hb,
      exact lt_irrefl _ ((ha.2.trans_le ((hz u us).2 v hlt)).trans hb.1) },
    apply set.pairwise_disjoint.countable_of_Ioo A,
    rintros _ ⟨y, ys, rfl⟩,
    simpa only [I.left_inv_on_inv_fun_on ys] using (hz y ys).1 },
  exact maps_to.countable_of_inj_on (maps_to_image f s) I fs_count,
end

/-- In a second countable space, the set of points where a monotone function is not left-continuous
is at most countable. Superseded by `countable_not_continuous_at` which gives the two-sided
version. -/
lemma countable_not_continuous_within_at_Iio [topological_space.second_countable_topology β] :
  set.countable {x | ¬(continuous_within_at f (Iio x) x)} :=
hf.dual.countable_not_continuous_within_at_Ioi

/-- In a second countable space, the set of points where a monotone function is not continuous
is at most countable. -/
lemma countable_not_continuous_at [topological_space.second_countable_topology β] :
  set.countable {x | ¬(continuous_at f x)} :=
begin
  apply (hf.countable_not_continuous_within_at_Ioi.union
         hf.countable_not_continuous_within_at_Iio).mono _,
  refine compl_subset_compl.1 _,
  simp only [compl_union],
  rintros x ⟨hx, h'x⟩,
  simp only [mem_set_of_eq, not_not, mem_compl_iff] at hx h'x ⊢,
  exact continuous_at_iff_continuous_left'_right'.2 ⟨h'x, hx⟩
end

end monotone

namespace antitone

variables {α β : Type*} [linear_order α] [conditionally_complete_linear_order β]
[topological_space β] [order_topology β] {f : α → β} (hf : antitone f) {x y : α}
include hf

lemma le_left_lim (h : x ≤ y) : f y ≤ left_lim f x :=
hf.dual_right.left_lim_le h

lemma left_lim_le (h : x < y) : left_lim f y ≤ f x :=
hf.dual_right.le_left_lim h

@[mono] protected lemma left_lim : antitone (left_lim f) :=
hf.dual_right.left_lim

lemma right_lim_le (h : x ≤ y) : right_lim f y ≤ f x :=
hf.dual_right.le_right_lim h

lemma le_right_lim (h : x < y) : f y ≤ right_lim f x :=
hf.dual_right.right_lim_le h

@[mono] protected lemma right_lim : antitone (right_lim f) :=
hf.dual_right.right_lim

lemma right_lim_le_left_lim (h : x ≤ y) : right_lim f y ≤ left_lim f x :=
hf.dual_right.left_lim_le_right_lim h

lemma left_lim_le_right_lim (h : x < y) : left_lim f y ≤ right_lim f x :=
hf.dual_right.right_lim_le_left_lim h

variables [topological_space α] [order_topology α]

lemma tendsto_left_lim (x : α) : tendsto f (𝓝[<] x) (𝓝 (left_lim f x)) :=
hf.dual_right.tendsto_left_lim x

lemma tendsto_left_lim_within (x : α) : tendsto f (𝓝[<] x) (𝓝[≥] (left_lim f x)) :=
hf.dual_right.tendsto_left_lim_within x

lemma tendsto_right_lim (x : α) :
  tendsto f (𝓝[>] x) (𝓝 (right_lim f x)) :=
hf.dual_right.tendsto_right_lim x

lemma tendsto_right_lim_within (x : α) :
  tendsto f (𝓝[>] x) (𝓝[≤] (right_lim f x)) :=
hf.dual_right.tendsto_right_lim_within x

/-- An antitone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
lemma continuous_within_at_Iio_iff_left_lim_eq  :
  continuous_within_at f (Iio x) x ↔ left_lim f x = f x :=
hf.dual_right.continuous_within_at_Iio_iff_left_lim_eq

/-- An antitone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
lemma continuous_within_at_Ioi_iff_right_lim_eq :
  continuous_within_at f (Ioi x) x ↔ right_lim f x = f x :=
hf.dual_right.continuous_within_at_Ioi_iff_right_lim_eq

/-- An antitone function is continuous at a point if and only if its left and right limits
coincide. -/
lemma continuous_at_iff_left_lim_eq_right_lim :
  continuous_at f x ↔ left_lim f x = right_lim f x :=
hf.dual_right.continuous_at_iff_left_lim_eq_right_lim

/-- In a second countable space, the set of points where an antitone function is not continuous
is at most countable. -/
lemma countable_not_continuous_at [topological_space.second_countable_topology β] :
  set.countable {x | ¬(continuous_at f x)} :=
hf.dual_right.countable_not_continuous_at

end antitone
