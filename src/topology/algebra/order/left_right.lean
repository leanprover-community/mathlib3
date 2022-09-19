/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.continuous_on
import topology.algebra.order.basic

/-!
# Left and right continuity

In this file we prove a few lemmas about left and right continuous functions:

* `continuous_within_at_Ioi_iff_Ici`: two definitions of right continuity
  (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuous_within_at_Iio_iff_Iic`: two definitions of left continuity
  (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuous_at_iff_continuous_left_right`, `continuous_at_iff_continuous_left'_right'` :
  a function is continuous at `a` if and only if it is left and right continuous at `a`.

We also define the (strict) left and right limits of a function and prove some properties:
* `left_lim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `right_lim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).
* `monotone.left_lim_eq_right_lim_iff_continuous_at` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `monotone.countable_not_continuous_at` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

## Tags

left continuous, right continuous
-/

open set filter
open_locale topological_space

section partial_order

variables {α β : Type*} [topological_space α] [partial_order α] [topological_space β]

lemma continuous_within_at_Ioi_iff_Ici {a : α} {f : α → β} :
  continuous_within_at f (Ioi a) a ↔ continuous_within_at f (Ici a) a :=
by simp only [← Ici_diff_left, continuous_within_at_diff_self]

lemma continuous_within_at_Iio_iff_Iic {a : α} {f : α → β} :
  continuous_within_at f (Iio a) a ↔ continuous_within_at f (Iic a) a :=
@continuous_within_at_Ioi_iff_Ici αᵒᵈ _ ‹topological_space α› _ _ _ f

end partial_order

section topological_space

variables {α β : Type*} [topological_space α] [linear_order α] [topological_space β]

lemma nhds_left'_le_nhds_ne (a : α) :
  𝓝[<] a ≤ 𝓝[≠] a :=
nhds_within_mono a (λ y hy, ne_of_lt hy)

lemma nhds_right'_le_nhds_ne (a : α) :
  𝓝[>] a ≤ 𝓝[≠] a :=
nhds_within_mono a (λ y hy, ne_of_gt hy)

lemma nhds_left_sup_nhds_right (a : α) :
  𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a :=
by rw [← nhds_within_union, Iic_union_Ici, nhds_within_univ]

lemma nhds_left'_sup_nhds_right (a : α) :
  𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a :=
by rw [← nhds_within_union, Iio_union_Ici, nhds_within_univ]

lemma nhds_left_sup_nhds_right' (a : α) :
  𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a :=
by rw [← nhds_within_union, Iic_union_Ioi, nhds_within_univ]

lemma nhds_left'_sup_nhds_right' (a : α) :
  𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a :=
by rw [← nhds_within_union, Iio_union_Ioi]

lemma continuous_at_iff_continuous_left_right {a : α} {f : α → β} :
  continuous_at f a ↔ continuous_within_at f (Iic a) a ∧ continuous_within_at f (Ici a) a :=
by simp only [continuous_within_at, continuous_at, ← tendsto_sup, nhds_left_sup_nhds_right]

lemma continuous_at_iff_continuous_left'_right' {a : α} {f : α → β} :
  continuous_at f a ↔ continuous_within_at f (Iio a) a ∧ continuous_within_at f (Ioi a) a :=
by rw [continuous_within_at_Ioi_iff_Ici, continuous_within_at_Iio_iff_Iic,
  continuous_at_iff_continuous_left_right]

end topological_space

section left_right_lim

section

variables {α β : Type*} [linear_order α] [topological_space β]

/-- Let `f : α → β` be a function from a linear order `α` to a topological_space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `left_lim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left, we use `f a` instead to
guarantee a good behavior in most cases. -/
@[irreducible] noncomputable def left_lim (f : α → β) (a : α) : β :=
begin
  classical,
  haveI : nonempty β := ⟨f a⟩,
  letI : topological_space α := preorder.topology α,
  exact if (𝓝[<] a) = ⊥ then f a else lim (𝓝[<] a) f
end

/-- Let `f : α → β` be a function from a linear order `α` to a topological_space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `right_lim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left, we use `f a` instead to
guarantee a good behavior in most cases. -/
noncomputable def right_lim (f : α → β) (a : α) : β :=
@left_lim αᵒᵈ β  _ _ f a

lemma left_lim_eq_of_ne_bot [hα : topological_space α] [h'α : order_topology α]
  (f : α → β) {a : α} (h : 𝓝[<] a ≠ ⊥) :
  left_lim f a = @lim _ _ _ ⟨f a⟩ (𝓝[<] a) f :=
begin
  rw [h'α.topology_eq_generate_intervals] at h ⊢,
  simp [left_lim, ite_eq_right_iff, h],
end

lemma left_lim_eq_of_eq_bot [hα : topological_space α] [h'α : order_topology α]
  (f : α → β) {a : α} (h : 𝓝[<] a = ⊥) :
  left_lim f a = f a :=
begin
  rw [h'α.topology_eq_generate_intervals] at h,
  simp [left_lim, ite_eq_left_iff, h],
end

end

namespace monotone

variables {α β : Type*} [linear_order α] [conditionally_complete_linear_order β]
[topological_space β] [order_topology β]
{f : α → β} (hf : monotone f)  {x y : α}
include hf

lemma left_lim_eq_Sup [topological_space α] [order_topology α] (h : 𝓝[<] x ≠ ⊥) :
  left_lim f x = (Sup (f '' (Iio x))) :=
begin
  haveI : ne_bot (𝓝[<] x) := ne_bot_iff.2 h,
  rw left_lim_eq_of_ne_bot f h,
  exact (hf.tendsto_nhds_within_Iio x).lim_eq,
end

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
  { simpa only [left_lim, h', eq_self_iff_true, if_true] using hf h.le },
  rw left_lim_eq_Sup hf h',
  refine le_cSup ⟨f y, _⟩ (mem_image_of_mem _ h),
  simp only [upper_bounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_set_of_eq],
  assume z hz,
  exact hf hz.le
end

lemma left_lim_le_left_lim (h : x ≤ y) : left_lim f x ≤ left_lim f y :=
begin
  rcases eq_or_lt_of_le h with rfl|hxy,
  { exact le_rfl },
  { exact (hf.left_lim_le le_rfl).trans (hf.le_left_lim hxy) }
end

lemma le_right_lim (h : x ≤ y) : f x ≤ right_lim f y :=
@left_lim_le αᵒᵈ βᵒᵈ _ _ _ _ f hf.dual y x h

lemma right_lim_le (h : x < y) : right_lim f x ≤ f y :=
@le_left_lim αᵒᵈ βᵒᵈ _ _ _ _ f hf.dual y x h

lemma right_lim_le_right_lim (h : x ≤ y) : right_lim f x ≤ right_lim f y :=
@left_lim_le_left_lim αᵒᵈ βᵒᵈ _ _ _ _ f hf.dual y x h

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

lemma tendsto_right_lim (x : α) :
  tendsto f (𝓝[>] x) (𝓝 (right_lim f x)) :=
@monotone.tendsto_left_lim αᵒᵈ βᵒᵈ _ _ _ _ f hf.dual _ _ x

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
@continuous_within_at_Iio_iff_left_lim_eq αᵒᵈ βᵒᵈ _ _ _ _ f hf.dual x _ _

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

open function

/-- In a second countable space, the set of points where a monotone function is not right-continuous
is at most countable. Superseded by `countable_not_continuous_at` which gives the two-sided
version. -/
lemma countable_not_continuous_within_at_Ioi [topological_space.second_countable_topology β] :
  set.countable {x | ¬(continuous_within_at f (Ioi x) x)} :=
begin
  /- If `f` is not continuous on the right at `x`, there is an inverval `(f x, z x)` which is not
  reached by `f`. This gives a family of disjoint open intervals in `β`. Such a family can only
  be countable as `β` is second-countable. -/
  nontriviality α,
  inhabit α,
  haveI : nonempty β := ⟨f default⟩,
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
      wlog h'uv : u ≤ v := le_total u v using [u v, v u] tactic.skip,
      { rcases eq_or_lt_of_le h'uv with rfl|h''uv,
        { exact (huv rfl).elim },
        apply disjoint_iff_forall_ne.2,
        rintros a ha b hb rfl,
        simp [I.left_inv_on_inv_fun_on us, I.left_inv_on_inv_fun_on vs] at ha hb,
        exact lt_irrefl _ ((ha.2.trans_le ((hz u us).2 v h''uv)).trans hb.1) },
      { assume hu hv h'uv,
        exact (this hv hu h'uv.symm).symm } },
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
@monotone.countable_not_continuous_within_at_Ioi αᵒᵈ βᵒᵈ _ _ _ _ f hf.dual _ _ _

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
  simp only [mem_compl_eq, mem_set_of_eq, not_not] at hx h'x ⊢,
  exact continuous_at_iff_continuous_left'_right'.2 ⟨h'x, hx⟩
end

end monotone

end left_right_lim
