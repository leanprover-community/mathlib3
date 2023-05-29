/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anatole Dedecker
-/
import topology.algebra.order.extend_from
import topology.algebra.order.compact
import topology.algebra.order.t5
import topology.local_extr

/-!
# Rolle's Theorem (topological part)

In this file we prove the purely topological part of Rolle's Theorem: namely, that a function that
is continuous on an interval $[a, b]$, $a<b$, has a local extremum at a point $x ∈ (a, b)$ provided
that $f(a)=f(b)$. We also prove several variations of this statement.

In `analysis.calculus.local_extr.rolle` we use these lemmas to prove several versions of Rolle's
Theorem from calculus.

## Keywords

local minimum, local maximum, extremum, Rolle's Theorem
-/

open filter set
open_locale topology

variables {α β : Type*}
  [conditionally_complete_linear_order α] [densely_ordered α]
  [topological_space α] [order_topology α]
  [conditionally_complete_linear_order β] [topological_space β] [order_topology β]
  {f : α → β} {a b : α} {l : β}

/-- A continuous function on a closed interval with `f a = f b` takes either its maximum or its
minimum value at a point in the interior of the interval. -/
lemma exists_Ioo_extr_on_Icc (hab : a < b) (hfc : continuous_on f (Icc a b)) (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, is_extr_on f (Icc a b) c :=
begin
  have ne : (Icc a b).nonempty, from nonempty_Icc.2 (le_of_lt hab),
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x,
    from is_compact_Icc.exists_forall_le ne hfc,
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C,
    from is_compact_Icc.exists_forall_ge ne hfc,
  by_cases hc : f c = f a,
  { by_cases hC : f C = f a,
    { have : ∀ x ∈ Icc a b, f x = f a,
        from λ x hx, le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx),
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases exists_between hab with ⟨c', hc'⟩,
      refine ⟨c', hc', or.inl _⟩,
      assume x hx,
      rw [mem_set_of_eq, this x hx, ← hC],
      exact Cge c' ⟨le_of_lt hc'.1, le_of_lt hc'.2⟩ },
    { refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 $ mt _ hC, lt_of_le_of_ne Cmem.2 $ mt _ hC⟩, or.inr Cge⟩,
      exacts [λ h, by rw h, λ h, by rw [h, hfI]] } },
  { refine ⟨c, ⟨lt_of_le_of_ne cmem.1 $ mt _ hc, lt_of_le_of_ne cmem.2 $ mt _ hc⟩, or.inl cle⟩,
      exacts [λ h, by rw h, λ h, by rw [h, hfI]] }
end

/-- A continuous function on a closed interval with `f a = f b` has a local extremum at some
point of the corresponding open interval. -/
lemma exists_local_extr_Ioo (hab : a < b) (hfc : continuous_on f (Icc a b)) (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, is_local_extr f c :=
let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc hab hfc hfI
in ⟨c, cmem, hc.is_local_extr $ Icc_mem_nhds cmem.1 cmem.2⟩

/-- If a function `f` is continuous on an open interval and tends to the same value at its
endpoints, then it has an extremum on this open interval. -/
lemma exists_extr_on_Ioo_of_tendsto (hab : a < b) (hfc : continuous_on f (Ioo a b))
  (ha : tendsto f (𝓝[>] a) (𝓝 l)) (hb : tendsto f (𝓝[<] b) (𝓝 l)) :
  ∃ c ∈ Ioo a b, is_extr_on f (Ioo a b) c :=
begin
  have h : eq_on (extend_from (Ioo a b) f) f (Ioo a b) := extend_from_extends hfc,
  obtain ⟨c, hc, hfc⟩ : ∃ c ∈ Ioo a b, is_extr_on (extend_from (Ioo a b) f) (Icc a b) c :=
    exists_Ioo_extr_on_Icc hab (continuous_on_Icc_extend_from_Ioo hab.ne hfc ha hb)
      ((eq_lim_at_left_extend_from_Ioo hab ha).trans (eq_lim_at_right_extend_from_Ioo hab hb).symm),
  exact ⟨c, hc, (hfc.on_subset Ioo_subset_Icc_self).congr h (h hc)⟩
end

/-- If a function `f` is continuous on an open interval and tends to the same value at its
endpoints, then it has a local extremum on this open interval. -/
lemma exists_is_local_extr_Ioo_of_tendsto (hab : a < b) (hfc : continuous_on f (Ioo a b))
  (ha : tendsto f (𝓝[>] a) (𝓝 l)) (hb : tendsto f (𝓝[<] b) (𝓝 l)) :
  ∃ c ∈ Ioo a b, is_local_extr f c :=
let ⟨c, cmem, hc⟩ := exists_extr_on_Ioo_of_tendsto hab hfc ha hb
in ⟨c, cmem, hc.is_local_extr $ Ioo_mem_nhds cmem.1 cmem.2⟩
