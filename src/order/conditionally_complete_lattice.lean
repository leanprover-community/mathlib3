/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.set.intervals.ord_connected

/-!
# Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset s
has a least upper bound and a greatest lower bound, denoted below by Sup s and Inf s.
Typical examples are real, nat, int with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates bdd_above and bdd_below to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of Sup and Inf
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix Inf and Sup in the statements by c, giving cInf and cSup. For instance,
Inf_le is a statement in complete lattices ensuring Inf s ≤ x, while cInf_le is the same
statement in conditionally complete lattices with an additional assumption that s is
bounded below.
-/

set_option old_structure_cmd true

open set

variables {α β : Type*} {ι : Sort*}

section

/-!
Extension of Sup and Inf from a preorder `α` to `with_top α` and `with_bot α`
-/

open_locale classical

noncomputable instance {α : Type*} [preorder α] [has_Sup α] : has_Sup (with_top α) :=
⟨λ S, if ⊤ ∈ S then ⊤ else
  if bdd_above (coe ⁻¹' S : set α) then ↑(Sup (coe ⁻¹' S : set α)) else ⊤⟩

noncomputable instance {α : Type*} [has_Inf α] : has_Inf (with_top α) :=
⟨λ S, if S ⊆ {⊤} then ⊤ else ↑(Inf (coe ⁻¹' S : set α))⟩

noncomputable instance {α : Type*} [has_Sup α] : has_Sup (with_bot α) :=
⟨(@with_top.has_Inf (order_dual α) _).Inf⟩

noncomputable instance {α : Type*} [preorder α] [has_Inf α] : has_Inf (with_bot α) :=
⟨(@with_top.has_Sup (order_dual α) _ _).Sup⟩

@[simp]
theorem with_top.cInf_empty {α : Type*} [has_Inf α] : Inf (∅ : set (with_top α)) = ⊤ :=
if_pos $ set.empty_subset _

@[simp]
theorem with_bot.cSup_empty {α : Type*} [has_Sup α] : Sup (∅ : set (with_bot α)) = ⊥ :=
if_pos $ set.empty_subset _

end -- section

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class conditionally_complete_lattice (α : Type*) extends lattice α, has_Sup α, has_Inf α :=
(le_cSup : ∀s a, bdd_above s → a ∈ s → a ≤ Sup s)
(cSup_le : ∀ s a, set.nonempty s → a ∈ upper_bounds s → Sup s ≤ a)
(cInf_le : ∀s a, bdd_below s → a ∈ s → Inf s ≤ a)
(le_cInf : ∀s a, set.nonempty s → a ∈ lower_bounds s → a ≤ Inf s)

/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class conditionally_complete_linear_order (α : Type*)
  extends conditionally_complete_lattice α, linear_order α

/-- A conditionally complete linear order with `bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class conditionally_complete_linear_order_bot (α : Type*)
  extends conditionally_complete_linear_order α, order_bot α :=
(cSup_empty : Sup ∅ = ⊥)

/- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/

@[priority 100] -- see Note [lower instance priority]
instance conditionally_complete_lattice_of_complete_lattice [complete_lattice α]:
  conditionally_complete_lattice α :=
{ le_cSup := by intros; apply le_Sup; assumption,
  cSup_le := by intros; apply Sup_le; assumption,
  cInf_le := by intros; apply Inf_le; assumption,
  le_cInf := by intros; apply le_Inf; assumption,
  ..‹complete_lattice α› }

@[priority 100] -- see Note [lower instance priority]
instance conditionally_complete_linear_order_of_complete_linear_order [complete_linear_order α]:
  conditionally_complete_linear_order α :=
{ ..conditionally_complete_lattice_of_complete_lattice, .. ‹complete_linear_order α› }

section
open_locale classical

/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible] noncomputable def well_founded.conditionally_complete_linear_order_with_bot
  {α : Type*} [i : linear_order α] (h : well_founded ((<) : α → α → Prop))
  (c : α) (hc : c = h.min set.univ ⟨c, mem_univ c⟩) :
  conditionally_complete_linear_order_bot α :=
{ sup := max,
  le_sup_left := le_max_left,
  le_sup_right := le_max_right,
  sup_le := λ a b c, max_le,
  inf := min,
  inf_le_left := min_le_left,
  inf_le_right := min_le_right,
  le_inf := λ a b c, le_min,
  Inf := λ s, if hs : s.nonempty then h.min s hs else c,
  cInf_le := begin
    assume s a hs has,
    have s_ne : s.nonempty := ⟨a, has⟩,
    simpa [s_ne] using not_lt.1 (h.not_lt_min s s_ne has),
  end,
  le_cInf := begin
    assume s a hs has,
    simp only [hs, dif_pos],
    exact has (h.min_mem s hs),
  end,
  Sup := λ s, if hs : (upper_bounds s).nonempty then h.min _ hs else c,
  le_cSup := begin
    assume s a hs has,
    have h's : (upper_bounds s).nonempty := hs,
    simp only [h's, dif_pos],
    exact h.min_mem _ h's has,
  end,
  cSup_le := begin
    assume s a hs has,
    have h's : (upper_bounds s).nonempty := ⟨a, has⟩,
    simp only [h's, dif_pos],
    simpa using h.not_lt_min _ h's has,
  end,
  bot := c,
  bot_le := λ x, by convert not_lt.1 (h.not_lt_min set.univ ⟨c, mem_univ c⟩ (mem_univ x)),
  cSup_empty := begin
    have : (set.univ : set α).nonempty := ⟨c, mem_univ c⟩,
    simp only [this, dif_pos, upper_bounds_empty],
    exact hc.symm
  end,
  .. i }

end

section order_dual

instance (α : Type*) [conditionally_complete_lattice α] :
  conditionally_complete_lattice (order_dual α) :=
{ le_cSup := @conditionally_complete_lattice.cInf_le α _,
  cSup_le := @conditionally_complete_lattice.le_cInf α _,
  le_cInf := @conditionally_complete_lattice.cSup_le α _,
  cInf_le := @conditionally_complete_lattice.le_cSup α _,
  ..order_dual.has_Inf α,
  ..order_dual.has_Sup α,
  ..order_dual.lattice α }

instance (α : Type*) [conditionally_complete_linear_order α] :
  conditionally_complete_linear_order (order_dual α) :=
{ ..order_dual.conditionally_complete_lattice α,
  ..order_dual.linear_order α }

end order_dual

section conditionally_complete_lattice
variables [conditionally_complete_lattice α] {s t : set α} {a b : α}

theorem le_cSup (h₁ : bdd_above s) (h₂ : a ∈ s) : a ≤ Sup s :=
conditionally_complete_lattice.le_cSup s a h₁ h₂

theorem cSup_le (h₁ : s.nonempty) (h₂ : ∀b∈s, b ≤ a) : Sup s ≤ a :=
conditionally_complete_lattice.cSup_le s a h₁ h₂

theorem cInf_le (h₁ : bdd_below s) (h₂ : a ∈ s) : Inf s ≤ a :=
conditionally_complete_lattice.cInf_le s a h₁ h₂

theorem le_cInf (h₁ : s.nonempty) (h₂ : ∀b∈s, a ≤ b) : a ≤ Inf s :=
conditionally_complete_lattice.le_cInf s a h₁ h₂

theorem le_cSup_of_le (_ : bdd_above s) (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_cSup ‹bdd_above s› hb)

theorem cInf_le_of_le (_ : bdd_below s) (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (cInf_le ‹bdd_below s› hb) h

theorem cSup_le_cSup (_ : bdd_above t) (_ : s.nonempty) (h : s ⊆ t) : Sup s ≤ Sup t :=
cSup_le ‹_› (assume (a) (ha : a ∈ s), le_cSup ‹bdd_above t› (h ha))

theorem cInf_le_cInf (_ : bdd_below t) (_ : s.nonempty) (h : s ⊆ t) : Inf t ≤ Inf s :=
le_cInf ‹_› (assume (a) (ha : a ∈ s), cInf_le ‹bdd_below t› (h ha))

lemma is_lub_cSup (ne : s.nonempty) (H : bdd_above s) : is_lub s (Sup s) :=
⟨assume x, le_cSup H, assume x, cSup_le ne⟩

lemma is_lub_csupr [nonempty ι] {f : ι → α} (H : bdd_above (range f)) :
  is_lub (range f) (⨆ i, f i) :=
is_lub_cSup (range_nonempty f) H

lemma is_lub_csupr_set {f : β → α} {s : set β} (H : bdd_above (f '' s)) (Hne : s.nonempty) :
  is_lub (f '' s) (⨆ i : s, f i) :=
by { rw ← Sup_image', exact is_lub_cSup (Hne.image _) H }

lemma is_glb_cInf (ne : s.nonempty) (H : bdd_below s) : is_glb s (Inf s) :=
⟨assume x, cInf_le H, assume x, le_cInf ne⟩

lemma is_glb_cinfi [nonempty ι] {f : ι → α} (H : bdd_below (range f)) :
  is_glb (range f) (⨅ i, f i) :=
is_glb_cInf (range_nonempty f) H

lemma is_glb_cinfi_set {f : β → α} {s : set β} (H : bdd_below (f '' s)) (Hne : s.nonempty) :
  is_glb (f '' s) (⨅ i : s, f i) :=
@is_lub_csupr_set (order_dual α) _ _ _ _ H Hne

lemma is_lub.cSup_eq (H : is_lub s a) (ne : s.nonempty) : Sup s = a :=
(is_lub_cSup ne ⟨a, H.1⟩).unique H

lemma is_lub.csupr_eq [nonempty ι] {f : ι → α} (H : is_lub (range f) a) : (⨆ i, f i) = a :=
H.cSup_eq (range_nonempty f)

lemma is_lub.csupr_set_eq {s : set β} {f : β → α} (H : is_lub (f '' s) a) (Hne : s.nonempty) :
  (⨆ i : s, f i) = a :=
is_lub.cSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- A greatest element of a set is the supremum of this set. -/
lemma is_greatest.cSup_eq (H : is_greatest s a) : Sup s = a :=
H.is_lub.cSup_eq H.nonempty

lemma is_greatest.Sup_mem (H : is_greatest s a) : Sup s ∈ s :=
H.cSup_eq.symm ▸ H.1

lemma is_glb.cInf_eq (H : is_glb s a) (ne : s.nonempty) : Inf s = a :=
(is_glb_cInf ne ⟨a, H.1⟩).unique H

lemma is_glb.cinfi_eq [nonempty ι] {f : ι → α} (H : is_glb (range f) a) : (⨅ i, f i) = a :=
H.cInf_eq (range_nonempty f)

lemma is_glb.cinfi_set_eq {s : set β} {f : β → α} (H : is_glb (f '' s) a) (Hne : s.nonempty) :
  (⨅ i : s, f i) = a :=
is_glb.cInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- A least element of a set is the infimum of this set. -/
lemma is_least.cInf_eq (H : is_least s a) : Inf s = a :=
H.is_glb.cInf_eq H.nonempty

lemma is_least.Inf_mem (H : is_least s a) : Inf s ∈ s :=
H.cInf_eq.symm ▸ H.1

lemma subset_Icc_cInf_cSup (hb : bdd_below s) (ha : bdd_above s) :
  s ⊆ Icc (Inf s) (Sup s) :=
λ x hx, ⟨cInf_le hb hx, le_cSup ha hx⟩

theorem cSup_le_iff (hb : bdd_above s) (ne : s.nonempty) : Sup s ≤ a ↔ (∀b ∈ s, b ≤ a) :=
is_lub_le_iff (is_lub_cSup ne hb)

theorem le_cInf_iff (hb : bdd_below s) (ne : s.nonempty) : a ≤ Inf s ↔ (∀b ∈ s, a ≤ b) :=
le_is_glb_iff (is_glb_cInf ne hb)

lemma cSup_lower_bounds_eq_cInf {s : set α} (h : bdd_below s) (hs : s.nonempty) :
  Sup (lower_bounds s) = Inf s :=
(is_lub_cSup h $ hs.mono $ λ x hx y hy, hy hx).unique (is_glb_cInf hs h).is_lub

lemma cInf_upper_bounds_eq_cSup {s : set α} (h : bdd_above s) (hs : s.nonempty) :
  Inf (upper_bounds s) = Sup s :=
(is_glb_cInf h $ hs.mono $ λ x hx y hy, hy hx).unique (is_lub_cSup hs h).is_glb

lemma not_mem_of_lt_cInf {x : α} {s : set α} (h : x < Inf s) (hs : bdd_below s) : x ∉ s :=
λ hx, lt_irrefl _ (h.trans_le (cInf_le hs hx))

lemma not_mem_of_cSup_lt {x : α} {s : set α} (h : Sup s < x) (hs : bdd_above s) : x ∉ s :=
@not_mem_of_lt_cInf (order_dual α) _ x s h hs

/--Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `Sup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem cSup_eq_of_forall_le_of_forall_lt_exists_gt (_ : s.nonempty)
  (_ : ∀a∈s, a ≤ b) (H : ∀w, w < b → (∃a∈s, w < a)) : Sup s = b :=
have bdd_above s := ⟨b, by assumption⟩,
have (Sup s < b) ∨ (Sup s = b) := lt_or_eq_of_le (cSup_le ‹_› ‹∀a∈s, a ≤ b›),
have ¬(Sup s < b) :=
  assume: Sup s < b,
  let ⟨a, _, _⟩ := (H (Sup s) ‹Sup s < b›) in  /- a ∈ s, Sup s < a-/
  have Sup s < Sup s := lt_of_lt_of_le ‹Sup s < a› (le_cSup ‹bdd_above s› ‹a ∈ s›),
  show false, by finish [lt_irrefl (Sup s)],
show Sup s = b, by finish

/--Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `Inf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cInf_eq_of_forall_ge_of_forall_gt_exists_lt (_ : s.nonempty) (_ : ∀a∈s, b ≤ a)
  (H : ∀w, b < w → (∃a∈s, a < w)) : Inf s = b :=
@cSup_eq_of_forall_le_of_forall_lt_exists_gt (order_dual α) _ _ _ ‹_› ‹_› ‹_›

/--b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
lemma lt_cSup_of_lt (_ : bdd_above s) (_ : a ∈ s) (_ : b < a) : b < Sup s :=
lt_of_lt_of_le ‹b < a› (le_cSup ‹bdd_above s› ‹a ∈ s›)

/--Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
lemma cInf_lt_of_lt (_ : bdd_below s) (_ : a ∈ s) (_ : a < b) : Inf s < b :=
@lt_cSup_of_lt (order_dual α) _ _ _ _ ‹_› ‹_› ‹_›

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
lemma exists_between_of_forall_le (sne : s.nonempty) (tne : t.nonempty)
  (hst : ∀ (x ∈ s) (y ∈ t), x ≤ y) :
  (upper_bounds s ∩ lower_bounds t).nonempty :=
⟨Inf t, λ x hx, le_cInf tne $ hst x hx, λ y hy, cInf_le (sne.mono hst) hy⟩

/--The supremum of a singleton is the element of the singleton-/
@[simp] theorem cSup_singleton (a : α) : Sup {a} = a :=
is_greatest_singleton.cSup_eq

/--The infimum of a singleton is the element of the singleton-/
@[simp] theorem cInf_singleton (a : α) : Inf {a} = a :=
is_least_singleton.cInf_eq

/--If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cInf_le_cSup (hb : bdd_below s) (ha : bdd_above s) (ne : s.nonempty) : Inf s ≤ Sup s :=
is_glb_le_is_lub (is_glb_cInf ne hb) (is_lub_cSup ne ha) ne

/--The sup of a union of two sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem cSup_union (hs : bdd_above s) (sne : s.nonempty) (ht : bdd_above t) (tne : t.nonempty) :
  Sup (s ∪ t) = Sup s ⊔ Sup t :=
((is_lub_cSup sne hs).union (is_lub_cSup tne ht)).cSup_eq sne.inl

/--The inf of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cInf_union (hs : bdd_below s) (sne : s.nonempty) (ht : bdd_below t) (tne : t.nonempty) :
  Inf (s ∪ t) = Inf s ⊓ Inf t :=
@cSup_union (order_dual α) _ _ _ hs sne ht tne

/--The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le (_ : bdd_above s) (_ : bdd_above t) (hst : (s ∩ t).nonempty) :
  Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
begin
  apply cSup_le hst, simp only [le_inf_iff, and_imp, set.mem_inter_eq], intros b _ _, split,
  apply le_cSup ‹bdd_above s› ‹b ∈ s›,
  apply le_cSup ‹bdd_above t› ‹b ∈ t›
end

/--The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter (_ : bdd_below s) (_ : bdd_below t) (hst : (s ∩ t).nonempty) :
  Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
@cSup_inter_le (order_dual α) _ _ _ ‹_› ‹_› hst

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert (hs : bdd_above s) (sne : s.nonempty) : Sup (insert a s) = a ⊔ Sup s :=
((is_lub_cSup sne hs).insert a).cSup_eq (insert_nonempty a s)

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert (hs : bdd_below s) (sne : s.nonempty) : Inf (insert a s) = a ⊓ Inf s :=
@cSup_insert (order_dual α) _ _ _ hs sne

@[simp] lemma cInf_Icc (h : a ≤ b) : Inf (Icc a b) = a :=
(is_glb_Icc h).cInf_eq (nonempty_Icc.2 h)

@[simp] lemma cInf_Ici : Inf (Ici a) = a := is_least_Ici.cInf_eq

@[simp] lemma cInf_Ico (h : a < b) : Inf (Ico a b) = a :=
(is_glb_Ico h).cInf_eq (nonempty_Ico.2 h)

@[simp] lemma cInf_Ioc [densely_ordered α] (h : a < b) : Inf (Ioc a b) = a :=
(is_glb_Ioc h).cInf_eq (nonempty_Ioc.2 h)

@[simp] lemma cInf_Ioi [no_top_order α] [densely_ordered α] : Inf (Ioi a) = a :=
cInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (λ _, le_of_lt)
  (λ w hw, by simpa using exists_between hw)

@[simp] lemma cInf_Ioo [densely_ordered α] (h : a < b) : Inf (Ioo a b) = a :=
(is_glb_Ioo h).cInf_eq (nonempty_Ioo.2 h)

@[simp] lemma cSup_Icc (h : a ≤ b) : Sup (Icc a b) = b :=
(is_lub_Icc h).cSup_eq (nonempty_Icc.2 h)

@[simp] lemma cSup_Ico [densely_ordered α] (h : a < b) : Sup (Ico a b) = b :=
(is_lub_Ico h).cSup_eq (nonempty_Ico.2 h)

@[simp] lemma cSup_Iic : Sup (Iic a) = a := is_greatest_Iic.cSup_eq

@[simp] lemma cSup_Iio [no_bot_order α] [densely_ordered α] : Sup (Iio a) = a :=
cSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (λ _, le_of_lt)
  (λ w hw, by simpa [and_comm] using exists_between hw)

@[simp] lemma cSup_Ioc (h : a < b) : Sup (Ioc a b) = b :=
(is_lub_Ioc h).cSup_eq (nonempty_Ioc.2 h)

@[simp] lemma cSup_Ioo [densely_ordered α] (h : a < b) : Sup (Ioo a b) = b :=
(is_lub_Ioo h).cSup_eq (nonempty_Ioo.2 h)

/--The indexed supremum of a function is bounded above by a uniform bound-/
lemma csupr_le [nonempty ι] {f : ι → α} {c : α} (H : ∀x, f x ≤ c) : supr f ≤ c :=
cSup_le (range_nonempty f) (by rwa forall_range_iff)

/--The indexed supremum of a function is bounded below by the value taken at one point-/
lemma le_csupr {f : ι → α} (H : bdd_above (range f)) (c : ι) : f c ≤ supr f :=
le_cSup H (mem_range_self _)

lemma le_csupr_of_le {f : ι → α} (H : bdd_above (range f)) (c : ι) (h : a ≤ f c) : a ≤ supr f :=
le_trans h (le_csupr H c)

/--The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
lemma csupr_le_csupr {f g : ι → α} (B : bdd_above (range g)) (H : ∀x, f x ≤ g x) :
  supr f ≤ supr g :=
begin
  casesI is_empty_or_nonempty ι,
  { rw [supr_of_empty', supr_of_empty'] },
  { exact csupr_le (λ x, le_csupr_of_le B x (H x)) },
end

/--The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
lemma cinfi_le_cinfi {f g : ι → α} (B : bdd_below (range f)) (H : ∀x, f x ≤ g x) :
  infi f ≤ infi g :=
@csupr_le_csupr (order_dual α) _ _ _ _ B H

/--The indexed minimum of a function is bounded below by a uniform lower bound-/
lemma le_cinfi [nonempty ι] {f : ι → α} {c : α} (H : ∀x, c ≤ f x) : c ≤ infi f :=
@csupr_le (order_dual α) _ _ _ _ _ H

/--The indexed infimum of a function is bounded above by the value taken at one point-/
lemma cinfi_le {f : ι → α} (H : bdd_below (range f)) (c : ι) : infi f ≤ f c :=
@le_csupr (order_dual α) _ _ _ H c

lemma cinfi_le_of_le {f : ι → α} (H : bdd_below (range f)) (c : ι) (h : f c ≤ a) : infi f ≤ a :=
@le_csupr_of_le (order_dual α) _ _ _ _ H c h

@[simp] theorem csupr_const [hι : nonempty ι] {a : α} : (⨆ b:ι, a) = a :=
by rw [supr, range_const, cSup_singleton]

@[simp] theorem cinfi_const [hι : nonempty ι] {a : α} : (⨅ b:ι, a) = a :=
@csupr_const (order_dual α) _ _ _ _

theorem supr_unique [unique ι] {s : ι → α} : (⨆ i, s i) = s (default ι) :=
have ∀ i, s i = s (default ι) := λ i, congr_arg s (unique.eq_default i),
by simp only [this, csupr_const]

theorem infi_unique [unique ι] {s : ι → α} : (⨅ i, s i) = s (default ι) :=
@supr_unique (order_dual α) _ _ _ _

@[simp] theorem supr_unit {f : unit → α} : (⨆ x, f x) = f () :=
by { convert supr_unique, apply_instance }

@[simp] theorem infi_unit {f : unit → α} : (⨅ x, f x) = f () :=
@supr_unit (order_dual α) _ _

@[simp] lemma csupr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
by haveI := unique_prop hp; exact supr_unique

@[simp] lemma cinfi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
@csupr_pos (order_dual α) _ _ _ hp

lemma csupr_set {s : set β} {f : β → α} : (⨆ x : s, f x) = Sup (f '' s) :=
begin
  rw supr,
  congr,
  ext,
  rw [mem_image, mem_range, set_coe.exists],
  simp_rw [subtype.coe_mk, exists_prop],
end

lemma cinfi_set {s : set β} {f : β → α} : (⨅ x : s, f x) = Inf (f '' s) :=
@csupr_set (order_dual α) _ _ _ _

/--Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `supr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csupr_eq_of_forall_le_of_forall_lt_exists_gt [nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
  (h₂ : ∀ w, w < b → (∃ i, w < f i)) : (⨆ (i : ι), f i) = b :=
cSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_range_iff.mpr h₁)
  (λ w hw, exists_range_iff.mpr $ h₂ w hw)

/--Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `infi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cinfi_eq_of_forall_ge_of_forall_gt_exists_lt [nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
  (h₂ : ∀ w, b < w → (∃ i, f i < w)) : (⨅ (i : ι), f i) = b :=
@csupr_eq_of_forall_le_of_forall_lt_exists_gt (order_dual α) _ _ _ _ ‹_› ‹_› ‹_›

/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
lemma monotone.csupr_mem_Inter_Icc_of_antitone [nonempty β] [semilattice_sup β]
  {f g : β → α} (hf : monotone f) (hg : antitone g) (h : f ≤ g) :
  (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
begin
  inhabit β,
  refine mem_Inter.2 (λ n, ⟨le_csupr ⟨g $ default β, forall_range_iff.2 $ λ m, _⟩ _,
    csupr_le $ λ m, _⟩); exact hf.forall_le_of_antitone hg h _ _
end

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
lemma csupr_mem_Inter_Icc_of_antitone_Icc [nonempty β] [semilattice_sup β]
  {f g : β → α} (h : antitone (λ n, Icc (f n) (g n))) (h' : ∀ n, f n ≤ g n) :
  (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
monotone.csupr_mem_Inter_Icc_of_antitone (λ m n hmn, ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
  (λ m n hmn, ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

lemma finset.nonempty.sup'_eq_cSup_image {s : finset β} (hs : s.nonempty) (f : β → α) :
  s.sup' hs f = Sup (f '' s) :=
eq_of_forall_ge_iff $ λ a,
  by simp [cSup_le_iff (s.finite_to_set.image f).bdd_above (hs.to_set.image f)]

lemma finset.nonempty.sup'_id_eq_cSup {s : finset α} (hs : s.nonempty) :
  s.sup' hs id = Sup s :=
by rw [hs.sup'_eq_cSup_image, image_id]

end conditionally_complete_lattice

instance pi.conditionally_complete_lattice {ι : Type*} {α : Π i : ι, Type*}
  [Π i, conditionally_complete_lattice (α i)] :
  conditionally_complete_lattice (Π i, α i) :=
{ le_cSup := λ s f ⟨g, hg⟩ hf i, le_cSup ⟨g i, set.forall_range_iff.2 $ λ ⟨f', hf'⟩, hg hf' i⟩
    ⟨⟨f, hf⟩, rfl⟩,
  cSup_le := λ s f hs hf i, cSup_le (by haveI := hs.to_subtype; apply range_nonempty) $
    λ b ⟨⟨g, hg⟩, hb⟩, hb ▸ hf hg i,
  cInf_le := λ s f ⟨g, hg⟩ hf i, cInf_le ⟨g i, set.forall_range_iff.2 $ λ ⟨f', hf'⟩, hg hf' i⟩
    ⟨⟨f, hf⟩, rfl⟩,
  le_cInf := λ s f hs hf i, le_cInf (by haveI := hs.to_subtype; apply range_nonempty) $
    λ b ⟨⟨g, hg⟩, hb⟩, hb ▸ hf hg i,
  .. pi.lattice, .. pi.has_Sup, .. pi.has_Inf }

section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α] {s t : set α} {a b : α}

lemma finset.nonempty.cSup_eq_max' {s : finset α} (h : s.nonempty) : Sup ↑s = s.max' h :=
eq_of_forall_ge_iff $ λ a, (cSup_le_iff s.bdd_above h.to_set).trans (s.max'_le_iff h).symm

lemma finset.nonempty.cInf_eq_min' {s : finset α} (h : s.nonempty) : Inf ↑s = s.min' h :=
@finset.nonempty.cSup_eq_max' (order_dual α) _ s h

lemma finset.nonempty.cSup_mem {s : finset α} (h : s.nonempty) : Sup (s : set α) ∈ s :=
by { rw h.cSup_eq_max', exact s.max'_mem _ }

lemma finset.nonempty.cInf_mem {s : finset α} (h : s.nonempty) : Inf (s : set α) ∈ s :=
@finset.nonempty.cSup_mem (order_dual α) _ _ h

lemma set.nonempty.cSup_mem (h : s.nonempty) (hs : finite s) : Sup s ∈ s :=
by { lift s to finset α using hs, exact finset.nonempty.cSup_mem h }

lemma set.nonempty.cInf_mem (h : s.nonempty) (hs : finite s) : Inf s ∈ s :=
@set.nonempty.cSup_mem (order_dual α) _ _ h hs

lemma set.finite.cSup_lt_iff (hs : finite s) (h : s.nonempty) : Sup s < a ↔ ∀ x ∈ s, x < a :=
⟨λ h x hx, (le_cSup hs.bdd_above hx).trans_lt h, λ H, H _ $ h.cSup_mem hs⟩

lemma set.finite.lt_cInf_iff (hs : finite s) (h : s.nonempty) : a < Inf s ↔ ∀ x ∈ s, a < x :=
@set.finite.cSup_lt_iff (order_dual α) _ _ _ hs h

/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
lemma exists_lt_of_lt_cSup (hs : s.nonempty) (hb : b < Sup s) : ∃a∈s, b < a :=
begin
  classical, contrapose! hb,
  exact cSup_le hs hb
end

/--
Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
lemma exists_lt_of_lt_csupr [nonempty ι] {f : ι → α} (h : b < supr f) :
  ∃i, b < f i :=
let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_cSup (range_nonempty f) h in ⟨i, h⟩

/--When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
lemma exists_lt_of_cInf_lt (hs : s.nonempty) (hb : Inf s < b) : ∃a∈s, a < b :=
@exists_lt_of_lt_cSup (order_dual α) _ _ _ hs hb

/--
Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
lemma exists_lt_of_cinfi_lt [nonempty ι] {f : ι → α} (h : infi f < a) :
  (∃i, f i < a) :=
@exists_lt_of_lt_csupr (order_dual α) _ _ _ _ _ h

/--Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem cSup_eq_of_is_forall_le_of_forall_le_imp_ge (_ : s.nonempty)
  (h_is_ub : ∀ a ∈ s, a ≤ b) (h_b_le_ub : ∀ub, (∀ a ∈ s, a ≤ ub) → (b ≤ ub)) : Sup s = b :=
le_antisymm
  (show Sup s ≤ b, from cSup_le ‹s.nonempty› h_is_ub)
  (show b ≤ Sup s, from h_b_le_ub _ $ assume a, le_cSup ⟨b, h_is_ub⟩)

open function
variables [is_well_order α (<)]

lemma Inf_eq_argmin_on (hs : s.nonempty) : Inf s = argmin_on id (@is_well_order.wf α (<) _) s hs :=
is_least.cInf_eq ⟨argmin_on_mem _ _ _ _, λ a ha, argmin_on_le id _ _ ha⟩

lemma is_least_Inf (hs : s.nonempty) : is_least s (Inf s) :=
by { rw Inf_eq_argmin_on hs, exact ⟨argmin_on_mem _ _ _ _, λ a ha, argmin_on_le id _ _ ha⟩ }

lemma le_cInf_iff' (hs : s.nonempty) : b ≤ Inf s ↔ b ∈ lower_bounds s :=
le_is_glb_iff (is_least_Inf hs).is_glb

lemma Inf_mem (hs : s.nonempty) : Inf s ∈ s := (is_least_Inf hs).1

end conditionally_complete_linear_order

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `nonempty`/`set.nonempty` assumptions.
-/

section conditionally_complete_linear_order_bot

variables [conditionally_complete_linear_order_bot α]

lemma cSup_empty : (Sup ∅ : α) = ⊥ :=
conditionally_complete_linear_order_bot.cSup_empty

lemma csupr_of_empty [is_empty ι] (f : ι → α) : (⨆ i, f i) = ⊥ :=
by rw [supr_of_empty', cSup_empty]

@[simp] lemma csupr_false (f : false → α) : (⨆ i, f i) = ⊥ := csupr_of_empty f

lemma is_lub_cSup' {s : set α} (hs : bdd_above s) : is_lub s (Sup s) :=
begin
  rcases eq_empty_or_nonempty s with (rfl|hne),
  { simp only [cSup_empty, is_lub_empty] },
  { exact is_lub_cSup hne hs }
end

lemma cSup_le_iff' {s : set α} (hs : bdd_above s) {a : α} : Sup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
is_lub_le_iff (is_lub_cSup' hs)

lemma cSup_le' {s : set α} {a : α} (h : a ∈ upper_bounds s) : Sup s ≤ a :=
(cSup_le_iff' ⟨a, h⟩).2 h

lemma exists_lt_of_lt_cSup' {s : set α} {a : α} (h : a < Sup s) : ∃ b ∈ s, a < b :=
by { contrapose! h, exact cSup_le' h }

lemma csupr_le_iff' {f : ι → α} (h : bdd_above (range f)) {a : α} :
  (⨆ i, f i) ≤ a ↔ ∀ i, f i ≤ a :=
(cSup_le_iff' h).trans forall_range_iff

lemma csupr_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆ i, f i) ≤ a :=
cSup_le' $ forall_range_iff.2 h

lemma exists_lt_of_lt_csupr' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i :=
by { contrapose! h, exact csupr_le' h }

end conditionally_complete_linear_order_bot

namespace with_top
open_locale classical

variables [conditionally_complete_linear_order_bot α]

/-- The Sup of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
lemma is_lub_Sup' {β : Type*} [conditionally_complete_lattice β]
  {s : set (with_top β)} (hs : s.nonempty) : is_lub s (Sup s) :=
begin
  split,
  { show ite _ _ _ ∈ _,
    split_ifs,
    { intros _ _, exact le_top },
    { rintro (⟨⟩|a) ha,
      { contradiction },
      apply some_le_some.2,
      exact le_cSup h_1 ha },
    { intros _ _, exact le_top } },
  { show ite _ _ _ ∈ _,
    split_ifs,
    { rintro (⟨⟩|a) ha,
      { exact _root_.le_refl _ },
      { exact false.elim (not_top_le_coe a (ha h)) } },
    { rintro (⟨⟩|b) hb,
      { exact le_top },
      refine some_le_some.2 (cSup_le _ _),
      { rcases hs with ⟨⟨⟩|b, hb⟩,
        { exact absurd hb h },
        { exact ⟨b, hb⟩ } },
      { intros a ha, exact some_le_some.1 (hb ha) } },
    { rintro (⟨⟩|b) hb,
      { exact _root_.le_refl _ },
      { exfalso, apply h_1, use b, intros a ha, exact some_le_some.1 (hb ha) } } }
end

lemma is_lub_Sup (s : set (with_top α)) : is_lub s (Sup s) :=
begin
  cases s.eq_empty_or_nonempty with hs hs,
  { rw hs,
    show is_lub ∅ (ite _ _ _),
    split_ifs,
    { cases h },
    { rw [preimage_empty, cSup_empty], exact is_lub_empty },
    { exfalso, apply h_1, use ⊥, rintro a ⟨⟩ } },
  exact is_lub_Sup' hs,
end

/-- The Inf of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
lemma is_glb_Inf' {β : Type*} [conditionally_complete_lattice β]
  {s : set (with_top β)} (hs : bdd_below s) : is_glb s (Inf s) :=
begin
  split,
  { show ite _ _ _ ∈ _,
    split_ifs,
    { intros a ha, exact top_le_iff.2 (set.mem_singleton_iff.1 (h ha)) },
    { rintro (⟨⟩|a) ha,
      { exact le_top },
      refine some_le_some.2 (cInf_le _ ha),
      rcases hs with ⟨⟨⟩|b, hb⟩,
      { exfalso,
        apply h,
        intros c hc,
        rw [mem_singleton_iff, ←top_le_iff],
        exact hb hc },
      use b,
      intros c hc,
      exact some_le_some.1 (hb hc) } },
  { show ite _ _ _ ∈ _,
    split_ifs,
    { intros _ _, exact le_top },
    { rintro (⟨⟩|a) ha,
      { exfalso, apply h, intros b hb, exact set.mem_singleton_iff.2 (top_le_iff.1 (ha hb)) },
      { refine some_le_some.2 (le_cInf _ _),
        { classical, contrapose! h,
          rintros (⟨⟩|a) ha,
          { exact mem_singleton ⊤ },
          { exact (h ⟨a, ha⟩).elim }},
        { intros b hb,
          rw ←some_le_some,
          exact ha hb } } } }
end

lemma is_glb_Inf (s : set (with_top α)) : is_glb s (Inf s) :=
begin
  by_cases hs : bdd_below s,
  { exact is_glb_Inf' hs },
  { exfalso, apply hs, use ⊥, intros _ _, exact bot_le },
end

noncomputable instance : complete_linear_order (with_top α) :=
{ Sup := Sup, le_Sup := assume s, (is_lub_Sup s).1, Sup_le := assume s, (is_lub_Sup s).2,
  Inf := Inf, le_Inf := assume s, (is_glb_Inf s).2, Inf_le := assume s, (is_glb_Inf s).1,
  .. with_top.linear_order, ..with_top.lattice, ..with_top.order_top, ..with_top.order_bot }

lemma coe_Sup {s : set α} (hb : bdd_above s) : (↑(Sup s) : with_top α) = (⨆a∈s, ↑a) :=
begin
  cases s.eq_empty_or_nonempty with hs hs,
  { rw [hs, cSup_empty], simp only [set.mem_empty_eq, supr_bot, supr_false], refl },
  apply le_antisymm,
  { refine (coe_le_iff.2 $ assume b hb, cSup_le hs $ assume a has, coe_le_coe.1 $ hb ▸ _),
    exact (le_supr_of_le a $ le_supr_of_le has $ _root_.le_refl _) },
  { exact (supr_le $ assume a, supr_le $ assume ha, coe_le_coe.2 $ le_cSup hb ha) }
end

lemma coe_Inf {s : set α} (hs : s.nonempty) : (↑(Inf s) : with_top α) = (⨅a∈s, ↑a) :=
let ⟨x, hx⟩ := hs in
have (⨅a∈s, ↑a : with_top α) ≤ x, from infi_le_of_le x $ infi_le_of_le hx $ _root_.le_refl _,
let ⟨r, r_eq, hr⟩ := le_coe_iff.1 this in
le_antisymm
  (le_infi $ assume a, le_infi $ assume ha, coe_le_coe.2 $ cInf_le (order_bot.bdd_below s) ha)
  begin
    refine (r_eq.symm ▸ coe_le_coe.2 $ le_cInf hs $ assume a has, coe_le_coe.1 $ _),
    refine (r_eq ▸ infi_le_of_le a _),
    exact (infi_le_of_le has $ _root_.le_refl _),
  end

end with_top

namespace monotone
variables [preorder α] [conditionally_complete_lattice β] {f : α → β} (h_mono : monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`Sup` and `Inf`. -/

lemma le_cSup_image {s : set α} {c : α} (hcs : c ∈ s) (h_bdd : bdd_above s) :
  f c ≤ Sup (f '' s) :=
le_cSup (map_bdd_above h_mono h_bdd) (mem_image_of_mem f hcs)

lemma cSup_image_le {s : set α} (hs : s.nonempty) {B : α} (hB: B ∈ upper_bounds s) :
  Sup (f '' s) ≤ f B :=
cSup_le (nonempty.image f hs) (h_mono.mem_upper_bounds_image hB)

lemma cInf_image_le {s : set α} {c : α} (hcs : c ∈ s) (h_bdd : bdd_below s) :
  Inf (f '' s) ≤ f c :=
@le_cSup_image (order_dual α) (order_dual β) _ _ _ (λ x y hxy, h_mono hxy) _ _ hcs h_bdd

lemma le_cInf_image {s : set α} (hs : s.nonempty) {B : α} (hB: B ∈ lower_bounds s) :
  f B ≤ Inf (f '' s) :=
@cSup_image_le (order_dual α) (order_dual β) _ _ _ (λ x y hxy, h_mono hxy) _ hs _ hB

end monotone

namespace galois_connection

variables {γ : Type*} [conditionally_complete_lattice α] [conditionally_complete_lattice β]
  [nonempty ι] {l : α → β} {u : β → α}

lemma l_cSup (gc : galois_connection l u) {s : set α} (hne : s.nonempty)
  (hbdd : bdd_above s) :
  l (Sup s) = ⨆ x : s, l x :=
eq.symm $ is_lub.csupr_set_eq (gc.is_lub_l_image $ is_lub_cSup hne hbdd) hne

lemma l_cSup' (gc : galois_connection l u) {s : set α} (hne : s.nonempty) (hbdd : bdd_above s) :
  l (Sup s) = Sup (l '' s) :=
by rw [gc.l_cSup hne hbdd, csupr_set]

lemma l_csupr (gc : galois_connection l u) {f : ι → α}
  (hf : bdd_above (range f)) :
  l (⨆ i, f i) = ⨆ i, l (f i) :=
by rw [supr, gc.l_cSup (range_nonempty _) hf, supr_range']

lemma l_csupr_set (gc : galois_connection l u) {s : set γ} {f : γ → α}
  (hf : bdd_above (f '' s)) (hne : s.nonempty) :
  l (⨆ i : s, f i) = ⨆ i : s, l (f i) :=
by { haveI := hne.to_subtype, rw image_eq_range at hf, exact gc.l_csupr hf }

lemma u_cInf (gc : galois_connection l u) {s : set β} (hne : s.nonempty)
  (hbdd : bdd_below s) :
  u (Inf s) = ⨅ x : s, u x :=
gc.dual.l_cSup hne hbdd

lemma u_cInf' (gc : galois_connection l u) {s : set β} (hne : s.nonempty) (hbdd : bdd_below s) :
  u (Inf s) = Inf (u '' s) :=
gc.dual.l_cSup' hne hbdd

lemma u_cinfi (gc : galois_connection l u) {f : ι → β}
  (hf : bdd_below (range f)) :
  u (⨅ i, f i) = ⨅ i, u (f i) :=
gc.dual.l_csupr hf

lemma u_cinfi_set (gc : galois_connection l u) {s : set γ} {f : γ → β}
  (hf : bdd_below (f '' s)) (hne : s.nonempty) :
  u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
gc.dual.l_csupr_set hf hne

end galois_connection

namespace order_iso

variables {γ : Type*} [conditionally_complete_lattice α] [conditionally_complete_lattice β]
  [nonempty ι]

lemma map_cSup (e : α ≃o β) {s : set α} (hne : s.nonempty) (hbdd : bdd_above s) :
  e (Sup s) = ⨆ x : s, e x :=
e.to_galois_connection.l_cSup hne hbdd

lemma map_cSup' (e : α ≃o β) {s : set α} (hne : s.nonempty) (hbdd : bdd_above s) :
  e (Sup s) = Sup (e '' s) :=
e.to_galois_connection.l_cSup' hne hbdd

lemma map_csupr (e : α ≃o β) {f : ι → α} (hf : bdd_above (range f)) :
  e (⨆ i, f i) = ⨆ i, e (f i) :=
e.to_galois_connection.l_csupr hf

lemma map_csupr_set (e : α ≃o β) {s : set γ} {f : γ → α}
  (hf : bdd_above (f '' s)) (hne : s.nonempty) :
  e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
e.to_galois_connection.l_csupr_set hf hne

lemma map_cInf (e : α ≃o β) {s : set α} (hne : s.nonempty) (hbdd : bdd_below s) :
  e (Inf s) = ⨅ x : s, e x :=
e.dual.map_cSup hne hbdd

lemma map_cInf' (e : α ≃o β) {s : set α} (hne : s.nonempty) (hbdd : bdd_below s) :
  e (Inf s) = Inf (e '' s) :=
e.dual.map_cSup' hne hbdd

lemma map_cinfi (e : α ≃o β) {f : ι → α} (hf : bdd_below (range f)) :
  e (⨅ i, f i) = ⨅ i, e (f i) :=
e.dual.map_csupr hf

lemma map_cinfi_set (e : α ≃o β) {s : set γ} {f : γ → α}
  (hf : bdd_below (f '' s)) (hne : s.nonempty) :
  e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
e.dual.map_csupr_set hf hne

end order_iso

/-!
### Relation between `Sup` / `Inf` and `finset.sup'` / `finset.inf'`

Like the `Sup` of a `conditionally_complete_lattice`, `finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/

namespace finset

lemma sup'_eq_cSup_image [conditionally_complete_lattice β] (s : finset α) (H) (f : α → β) :
  s.sup' H f = Sup (f '' s) :=
begin
  apply le_antisymm,
  { refine (finset.sup'_le _ _ $ λ a ha, _),
    refine le_cSup ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩,
    rintros i ⟨j, hj, rfl⟩,
    exact finset.le_sup' _ hj },
  { apply cSup_le ((coe_nonempty.mpr H).image _),
    rintros _ ⟨a, ha, rfl⟩,
    exact finset.le_sup' _ ha, }
end

lemma inf'_eq_cInf_image [conditionally_complete_lattice β] (s : finset α) (H) (f : α → β) :
  s.inf' H f = Inf (f '' s) :=
@sup'_eq_cSup_image _ (order_dual β) _ _ _ _

lemma sup'_id_eq_cSup [conditionally_complete_lattice α] (s : finset α) (H) :
  s.sup' H id = Sup s :=
by rw [sup'_eq_cSup_image s H, set.image_id]

lemma inf'_id_eq_cInf [conditionally_complete_lattice α] (s : finset α) (H) :
  s.inf' H id = Inf s :=
@sup'_id_eq_cSup (order_dual α) _ _ _

end finset

section with_top_bot

/-!
### Complete lattice structure on `with_top (with_bot α)`

If `α` is a `conditionally_complete_lattice`, then we show that `with_top α` and `with_bot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `with_top (with_bot α)` naturally inherits the structure of a complete lattice. Note that
for α a conditionally complete lattice, `Sup` and `Inf` both return junk values
for sets which are empty or unbounded. The extension of `Sup` to `with_top α` fixes
the unboundedness problem and the extension to `with_bot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals [-∞, ∞] are a complete lattice.
-/

open_locale classical

/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance with_top.conditionally_complete_lattice
  {α : Type*} [conditionally_complete_lattice α] :
  conditionally_complete_lattice (with_top α) :=
{ le_cSup := λ S a hS haS, (with_top.is_lub_Sup' ⟨a, haS⟩).1 haS,
  cSup_le := λ S a hS haS, (with_top.is_lub_Sup' hS).2 haS,
  cInf_le := λ S a hS haS, (with_top.is_glb_Inf' hS).1 haS,
  le_cInf := λ S a hS haS, (with_top.is_glb_Inf' ⟨a, haS⟩).2 haS,
  ..with_top.lattice,
  ..with_top.has_Sup,
  ..with_top.has_Inf }

/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance with_bot.conditionally_complete_lattice
  {α : Type*} [conditionally_complete_lattice α] :
  conditionally_complete_lattice (with_bot α) :=
{ le_cSup := (@with_top.conditionally_complete_lattice (order_dual α) _).cInf_le,
  cSup_le := (@with_top.conditionally_complete_lattice (order_dual α) _).le_cInf,
  cInf_le := (@with_top.conditionally_complete_lattice (order_dual α) _).le_cSup,
  le_cInf := (@with_top.conditionally_complete_lattice (order_dual α) _).cSup_le,
  ..with_bot.lattice,
  ..with_bot.has_Sup,
  ..with_bot.has_Inf }

/-- Adding a bottom and a top to a conditionally complete lattice gives a bounded lattice-/
noncomputable instance with_top.with_bot.bounded_lattice {α : Type*}
  [conditionally_complete_lattice α] : bounded_lattice (with_top (with_bot α)) :=
{ ..with_top.order_bot,
  ..with_top.order_top,
  ..conditionally_complete_lattice.to_lattice _ }

noncomputable instance with_top.with_bot.complete_lattice {α : Type*}
  [conditionally_complete_lattice α] : complete_lattice (with_top (with_bot α)) :=
{ le_Sup := λ S a haS, (with_top.is_lub_Sup' ⟨a, haS⟩).1 haS,
  Sup_le := λ S a ha,
    begin
      cases S.eq_empty_or_nonempty with h,
      { show ite _ _ _ ≤ a,
        split_ifs,
        { rw h at h_1, cases h_1 },
        { convert bot_le, convert with_bot.cSup_empty, rw h, refl },
        { exfalso, apply h_2, use ⊥, rw h, rintro b ⟨⟩ } },
      { refine (with_top.is_lub_Sup' h).2 ha }
    end,
  Inf_le := λ S a haS,
    show ite _ _ _ ≤ a,
    begin
      split_ifs,
      { cases a with a, exact _root_.le_refl _,
        cases (h haS); tauto },
      { cases a,
        { exact le_top },
        { apply with_top.some_le_some.2, refine cInf_le _ haS, use ⊥, intros b hb, exact bot_le } }
    end,
  le_Inf := λ S a haS, (with_top.is_glb_Inf' ⟨a, haS⟩).2 haS,
  ..with_top.has_Inf,
  ..with_top.has_Sup,
  ..with_top.with_bot.bounded_lattice }

noncomputable instance with_top.with_bot.complete_linear_order {α : Type*}
  [conditionally_complete_linear_order α] : complete_linear_order (with_top (with_bot α)) :=
{ .. with_top.with_bot.complete_lattice,
  .. with_top.linear_order }

end with_top_bot

section subtype
variables (s : set α)

/-! ### Subtypes of conditionally complete linear orders

In this section we give conditions on a subset of a conditionally complete linear order, to ensure
that the subtype is itself conditionally complete.

We check that an `ord_connected` set satisfies these conditions.

TODO There are several possible variants; the `conditionally_complete_linear_order` could be changed
to `conditionally_complete_linear_order_bot` or `complete_linear_order`.
-/

open_locale classical

section has_Sup
variables [has_Sup α]

/-- `has_Sup` structure on a nonempty subset `s` of an object with `has_Sup`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subset_has_Sup [inhabited s] : has_Sup s := {Sup := λ t,
if ht : Sup (coe '' t : set α) ∈ s then ⟨Sup (coe '' t : set α), ht⟩ else default s}

local attribute [instance] subset_has_Sup

@[simp] lemma subset_Sup_def [inhabited s] :
  @Sup s _ = λ t,
  if ht : Sup (coe '' t : set α) ∈ s then ⟨Sup (coe '' t : set α), ht⟩ else default s :=
rfl

lemma subset_Sup_of_within [inhabited s] {t : set s} (h : Sup (coe '' t : set α) ∈ s) :
  Sup (coe '' t : set α) = (@Sup s _ t : α) :=
by simp [dif_pos h]

end has_Sup

section has_Inf
variables [has_Inf α]

/-- `has_Inf` structure on a nonempty subset `s` of an object with `has_Inf`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subset_has_Inf [inhabited s] : has_Inf s := {Inf := λ t,
if ht : Inf (coe '' t : set α) ∈ s then ⟨Inf (coe '' t : set α), ht⟩ else default s}

local attribute [instance] subset_has_Inf

@[simp] lemma subset_Inf_def [inhabited s] :
  @Inf s _ = λ t,
  if ht : Inf (coe '' t : set α) ∈ s then ⟨Inf (coe '' t : set α), ht⟩ else default s :=
rfl

lemma subset_Inf_of_within [inhabited s] {t : set s} (h : Inf (coe '' t : set α) ∈ s) :
  Inf (coe '' t : set α) = (@Inf s _ t : α) :=
by simp [dif_pos h]

end has_Inf

variables [conditionally_complete_linear_order α]

local attribute [instance] subset_has_Sup
local attribute [instance] subset_has_Inf

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `Sup` of all its nonempty bounded-above subsets, and
the `Inf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def subset_conditionally_complete_linear_order [inhabited s]
  (h_Sup : ∀ {t : set s} (ht : t.nonempty) (h_bdd : bdd_above t), Sup (coe '' t : set α) ∈ s)
  (h_Inf : ∀ {t : set s} (ht : t.nonempty) (h_bdd : bdd_below t), Inf (coe '' t : set α) ∈ s) :
  conditionally_complete_linear_order s :=
{ le_cSup := begin
    rintros t c h_bdd hct,
    -- The following would be a more natural way to finish, but gives a "deep recursion" error:
    -- simpa [subset_Sup_of_within (h_Sup t)] using
    --   (strict_mono_coe s).monotone.le_cSup_image hct h_bdd,
    have := (subtype.mono_coe s).le_cSup_image hct h_bdd,
    rwa subset_Sup_of_within s (h_Sup ⟨c, hct⟩ h_bdd) at this,
  end,
  cSup_le := begin
    rintros t B ht hB,
    have := (subtype.mono_coe s).cSup_image_le ht hB,
    rwa subset_Sup_of_within s (h_Sup ht ⟨B, hB⟩) at this,
  end,
  le_cInf := begin
    intros t B ht hB,
    have := (subtype.mono_coe s).le_cInf_image ht hB,
    rwa subset_Inf_of_within s (h_Inf ht ⟨B, hB⟩) at this,
  end,
  cInf_le := begin
    rintros t c h_bdd hct,
    have := (subtype.mono_coe s).cInf_image_le hct h_bdd,
    rwa subset_Inf_of_within s (h_Inf ⟨c, hct⟩ h_bdd) at this,
  end,
  ..subset_has_Sup s,
  ..subset_has_Inf s,
  ..distrib_lattice.to_lattice s,
  ..(infer_instance : linear_order s) }

section ord_connected

/-- The `Sup` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
lemma Sup_within_of_ord_connected
  {s : set α} [hs : ord_connected s] ⦃t : set s⦄ (ht : t.nonempty) (h_bdd : bdd_above t) :
  Sup (coe '' t : set α) ∈ s :=
begin
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht,
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upper_bounds t := h_bdd,
  refine hs.out c.2 B.2 ⟨_, _⟩,
  { exact (subtype.mono_coe s).le_cSup_image hct ⟨B, hB⟩ },
  { exact (subtype.mono_coe s).cSup_image_le ⟨c, hct⟩ hB },
end

/-- The `Inf` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
lemma Inf_within_of_ord_connected
  {s : set α} [hs : ord_connected s] ⦃t : set s⦄ (ht : t.nonempty) (h_bdd : bdd_below t) :
  Inf (coe '' t : set α) ∈ s :=
begin
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht,
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lower_bounds t := h_bdd,
  refine hs.out B.2 c.2 ⟨_, _⟩,
  { exact (subtype.mono_coe s).le_cInf_image ⟨c, hct⟩ hB },
  { exact (subtype.mono_coe s).cInf_image_le hct ⟨B, hB⟩ },
end

/-- A nonempty `ord_connected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ord_connected_subset_conditionally_complete_linear_order
  [inhabited s] [ord_connected s] :
  conditionally_complete_linear_order s :=
subset_conditionally_complete_linear_order s Sup_within_of_ord_connected Inf_within_of_ord_connected

end ord_connected

end subtype
