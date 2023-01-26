/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import order.bounds.basic
import order.well_founded
import data.set.intervals.basic
import data.set.lattice

/-!
# Theory of conditionally complete lattices.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `Sup s` and `Inf s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates `bdd_above` and `bdd_below` to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of `Sup` and `Inf`
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `Inf` and `Sup` in the statements by `c`, giving `cInf` and `cSup`.
For instance, `Inf_le` is a statement in complete lattices ensuring `Inf s ≤ x`,
while `cInf_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/

set_option old_structure_cmd true

open function order_dual set

variables {α β γ : Type*} {ι : Sort*}

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
⟨(@with_top.has_Inf αᵒᵈ _).Inf⟩

noncomputable instance {α : Type*} [preorder α] [has_Inf α] : has_Inf (with_bot α) :=
⟨(@with_top.has_Sup αᵒᵈ _ _).Sup⟩

@[simp]
theorem with_top.cInf_empty {α : Type*} [has_Inf α] : Inf (∅ : set (with_top α)) = ⊤ :=
if_pos $ set.empty_subset _

@[simp]
theorem with_top.cinfi_empty {α : Type*} [is_empty ι] [has_Inf α] (f : ι → with_top α) :
  (⨅ i, f i) = ⊤ :=
by rw [infi, range_eq_empty, with_top.cInf_empty]

lemma with_top.coe_Inf' [has_Inf α] {s : set α} (hs : s.nonempty) :
  ↑(Inf s) = (Inf (coe '' s) : with_top α) :=
begin
  obtain ⟨x, hx⟩ := hs,
  change _ = ite _ _ _,
  split_ifs,
  { cases h (mem_image_of_mem _ hx) },
  { rw preimage_image_eq,
    exact option.some_injective _ },
end

@[norm_cast] lemma with_top.coe_infi [nonempty ι] [has_Inf α] (f : ι → α) :
  ↑(⨅ i, f i) = (⨅ i, f i : with_top α) :=
by rw [infi, infi, with_top.coe_Inf' (range_nonempty f), range_comp]

theorem with_top.coe_Sup' [preorder α] [has_Sup α] {s : set α} (hs : bdd_above s) :
  ↑(Sup s) = (Sup (coe '' s) : with_top α) :=
begin
  change _ = ite _ _ _,
  rw [if_neg, preimage_image_eq, if_pos hs],
  { exact option.some_injective _ },
  { rintro ⟨x, h, ⟨⟩⟩ },
end

@[norm_cast] lemma with_top.coe_supr [preorder α] [has_Sup α] (f : ι → α)
  (h : bdd_above (set.range f)) :
  ↑(⨆ i, f i) = (⨆ i, f i : with_top α) :=
by rw [supr, supr, with_top.coe_Sup' h, range_comp]

@[simp]
theorem with_bot.cSup_empty {α : Type*} [has_Sup α] : Sup (∅ : set (with_bot α)) = ⊥ :=
if_pos $ set.empty_subset _

@[simp]
theorem with_bot.csupr_empty {α : Type*} [is_empty ι] [has_Sup α] (f : ι → with_bot α) :
  (⨆ i, f i) = ⊥ :=
@with_top.cinfi_empty _ αᵒᵈ _ _ _

@[norm_cast] lemma with_bot.coe_Sup' [has_Sup α] {s : set α} (hs : s.nonempty) :
  ↑(Sup s) = (Sup (coe '' s) : with_bot α) :=
@with_top.coe_Inf' αᵒᵈ _ _ hs

@[norm_cast] lemma with_bot.coe_supr [nonempty ι] [has_Sup α] (f : ι → α) :
  ↑(⨆ i, f i) = (⨆ i, f i : with_bot α) :=
@with_top.coe_infi αᵒᵈ _ _ _ _

@[norm_cast] theorem with_bot.coe_Inf' [preorder α] [has_Inf α] {s : set α} (hs : bdd_below s) :
  ↑(Inf s) = (Inf (coe '' s) : with_bot α) :=
@with_top.coe_Sup' αᵒᵈ _ _ _ hs

@[norm_cast] lemma with_bot.coe_infi [preorder α] [has_Inf α] (f : ι → α)
  (h : bdd_below (set.range f)) :
  ↑(⨅ i, f i) = (⨅ i, f i : with_bot α) :=
@with_top.coe_supr αᵒᵈ _ _ _ _ h

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
(le_cSup : ∀ s a, bdd_above s → a ∈ s → a ≤ Sup s)
(cSup_le : ∀ s a, set.nonempty s → a ∈ upper_bounds s → Sup s ≤ a)
(cInf_le : ∀ s a, bdd_below s → a ∈ s → Inf s ≤ a)
(le_cInf : ∀ s a, set.nonempty s → a ∈ lower_bounds s → a ≤ Inf s)

/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class conditionally_complete_linear_order (α : Type*)
  extends conditionally_complete_lattice α, linear_order α renaming max → sup min → inf

/-- A conditionally complete linear order with `bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
@[ancestor conditionally_complete_linear_order has_bot]
class conditionally_complete_linear_order_bot (α : Type*)
  extends conditionally_complete_linear_order α, has_bot α :=
(bot_le : ∀ x : α, ⊥ ≤ x)
(cSup_empty : Sup ∅ = ⊥)

@[priority 100]  -- see Note [lower instance priority]
instance conditionally_complete_linear_order_bot.to_order_bot
  [h : conditionally_complete_linear_order_bot α] : order_bot α :=
{ ..h }

/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/
@[priority 100] -- see Note [lower instance priority]
instance complete_lattice.to_conditionally_complete_lattice [complete_lattice α] :
  conditionally_complete_lattice α :=
{ le_cSup := by intros; apply le_Sup; assumption,
  cSup_le := by intros; apply Sup_le; assumption,
  cInf_le := by intros; apply Inf_le; assumption,
  le_cInf := by intros; apply le_Inf; assumption,
  ..‹complete_lattice α› }

@[priority 100] -- see Note [lower instance priority]
instance complete_linear_order.to_conditionally_complete_linear_order_bot {α : Type*}
  [complete_linear_order α] :
  conditionally_complete_linear_order_bot α :=
{ cSup_empty := Sup_empty,
  ..complete_lattice.to_conditionally_complete_lattice, .. ‹complete_linear_order α› }

section
open_locale classical

/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible] noncomputable def is_well_order.conditionally_complete_linear_order_bot
  (α : Type*) [i₁ : linear_order α] [i₂ : order_bot α] [h : is_well_order α (<)] :
  conditionally_complete_linear_order_bot α :=
{ Inf := λ s, if hs : s.nonempty then h.wf.min s hs else ⊥,
  cInf_le := λ s a hs has, begin
    have s_ne : s.nonempty := ⟨a, has⟩,
    simpa [s_ne] using not_lt.1 (h.wf.not_lt_min s s_ne has),
  end,
  le_cInf := λ s a hs has, begin
    simp only [hs, dif_pos],
    exact has (h.wf.min_mem s hs),
  end,
  Sup := λ s, if hs : (upper_bounds s).nonempty then h.wf.min _ hs else ⊥,
  le_cSup := λ s a hs has, begin
    have h's : (upper_bounds s).nonempty := hs,
    simp only [h's, dif_pos],
    exact h.wf.min_mem _ h's has,
  end,
  cSup_le := λ s a hs has, begin
    have h's : (upper_bounds s).nonempty := ⟨a, has⟩,
    simp only [h's, dif_pos],
    simpa using h.wf.not_lt_min _ h's has,
  end,
  cSup_empty := by simpa using eq_bot_iff.2 (not_lt.1 $ h.wf.not_lt_min _ _ $ mem_univ ⊥),
  ..i₁, ..i₂, ..linear_order.to_lattice }

end

section order_dual

instance (α : Type*) [conditionally_complete_lattice α] : conditionally_complete_lattice αᵒᵈ :=
{ le_cSup := @conditionally_complete_lattice.cInf_le α _,
  cSup_le := @conditionally_complete_lattice.le_cInf α _,
  le_cInf := @conditionally_complete_lattice.cSup_le α _,
  cInf_le := @conditionally_complete_lattice.le_cSup α _,
  ..order_dual.has_Inf α,
  ..order_dual.has_Sup α,
  ..order_dual.lattice α }

instance (α : Type*) [conditionally_complete_linear_order α] :
  conditionally_complete_linear_order αᵒᵈ :=
{ ..order_dual.conditionally_complete_lattice α,
  ..order_dual.linear_order α }

end order_dual

/-- Create a `conditionally_complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a nonempty set which is bounded above. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`conditionally_complete_lattice` instance as
```
instance : conditionally_complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf
  ..conditionally_complete_lattice_of_Sup my_T _ }
```
-/
def conditionally_complete_lattice_of_Sup (α : Type*) [H1 : partial_order α]
  [H2 : has_Sup α]
  (bdd_above_pair : ∀ a b : α, bdd_above ({a, b} : set α))
  (bdd_below_pair : ∀ a b : α, bdd_below ({a, b} : set α))
  (is_lub_Sup : ∀ s : set α, bdd_above s → s.nonempty → is_lub s (Sup s)) :
  conditionally_complete_lattice α :=
{ sup := λ a b, Sup {a, b},
  le_sup_left := λ a b, (is_lub_Sup {a, b} (bdd_above_pair a b)
    (insert_nonempty _ _)).1 (mem_insert _ _),
  le_sup_right := λ a b, (is_lub_Sup {a, b} (bdd_above_pair a b)
    (insert_nonempty _ _)).1 (mem_insert_of_mem _ (mem_singleton _)),
  sup_le := λ a b c hac hbc, (is_lub_Sup {a, b} (bdd_above_pair a b)
    (insert_nonempty _ _)).2 (forall_insert_of_forall (forall_eq.mpr hbc) hac),
  inf := λ a b, Sup (lower_bounds {a, b}),
  inf_le_left := λ a b, (is_lub_Sup (lower_bounds {a, b})
    (nonempty.bdd_above_lower_bounds ⟨a, mem_insert _ _⟩) (bdd_below_pair a b)).2
    (λ c hc, hc $ mem_insert _ _),
  inf_le_right := λ a b, (is_lub_Sup (lower_bounds {a, b})
    (nonempty.bdd_above_lower_bounds ⟨a, mem_insert _ _⟩)
    (bdd_below_pair a b)).2 (λ c hc, hc $ mem_insert_of_mem _ (mem_singleton _)),
  le_inf := λ c a b hca hcb, (is_lub_Sup (lower_bounds {a, b})
    (nonempty.bdd_above_lower_bounds ⟨a, mem_insert _ _⟩)
    ⟨c, forall_insert_of_forall (forall_eq.mpr hcb) hca⟩).1
    (forall_insert_of_forall (forall_eq.mpr hcb) hca),
  Inf := λ s, Sup (lower_bounds s),
  cSup_le := λ s a hs ha, (is_lub_Sup s ⟨a, ha⟩ hs).2 ha,
  le_cSup := λ s a hs ha, (is_lub_Sup s hs ⟨a, ha⟩).1 ha,
  cInf_le := λ s a hs ha, (is_lub_Sup (lower_bounds s)
    (nonempty.bdd_above_lower_bounds ⟨a, ha⟩) hs).2 (λ b hb, hb ha),
  le_cInf := λ s a hs ha, (is_lub_Sup (lower_bounds s) hs.bdd_above_lower_bounds ⟨a, ha⟩).1 ha,
  .. H1, .. H2 }

/-- Create a `conditionally_complete_lattice_of_Inf` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a nonempty set which is bounded below. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`conditionally_complete_lattice` instance as
```
instance : conditionally_complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup
  ..conditionally_complete_lattice_of_Inf my_T _ }
```
-/
def conditionally_complete_lattice_of_Inf (α : Type*) [H1 : partial_order α]
  [H2 : has_Inf α]
  (bdd_above_pair : ∀ a b : α, bdd_above ({a, b} : set α))
  (bdd_below_pair : ∀ a b : α, bdd_below ({a, b} : set α))
  (is_glb_Inf : ∀ s : set α, bdd_below s → s.nonempty → is_glb s (Inf s)) :
  conditionally_complete_lattice α :=
{ inf := λ a b, Inf {a, b},
  inf_le_left := λ a b, (is_glb_Inf {a, b} (bdd_below_pair a b)
    (insert_nonempty _ _)).1 (mem_insert _ _),
  inf_le_right := λ a b, (is_glb_Inf {a, b} (bdd_below_pair a b)
    (insert_nonempty _ _)).1 (mem_insert_of_mem _ (mem_singleton _)),
  le_inf := λ c a b hca hcb, (is_glb_Inf {a, b} (bdd_below_pair a b)
    (insert_nonempty _ _)).2 (forall_insert_of_forall (forall_eq.mpr hcb) hca),
  sup := λ a b, Inf (upper_bounds {a, b}),
  le_sup_left := λ a b, (is_glb_Inf (upper_bounds {a, b})
    (nonempty.bdd_below_upper_bounds ⟨a, mem_insert _ _⟩) (bdd_above_pair a b)).2
    (λ c hc, hc $ mem_insert _ _),
  le_sup_right := λ a b, (is_glb_Inf (upper_bounds {a, b})
    (nonempty.bdd_below_upper_bounds ⟨a, mem_insert _ _⟩)
    (bdd_above_pair a b)).2 (λ c hc, hc $ mem_insert_of_mem _ (mem_singleton _)),
  sup_le := λ a b c hac hbc, (is_glb_Inf (upper_bounds {a, b})
    (nonempty.bdd_below_upper_bounds ⟨a, mem_insert _ _⟩)
    ⟨c, forall_insert_of_forall (forall_eq.mpr hbc) hac⟩).1
    (forall_insert_of_forall (forall_eq.mpr hbc) hac),
  Sup := λ s, Inf (upper_bounds s),
  le_cInf := λ s a hs ha, (is_glb_Inf s ⟨a, ha⟩ hs).2 ha,
  cInf_le := λ s a hs ha, (is_glb_Inf s hs ⟨a, ha⟩).1 ha,
  le_cSup := λ s a hs ha, (is_glb_Inf (upper_bounds s)
    (nonempty.bdd_below_upper_bounds ⟨a, ha⟩) hs).2 (λ b hb, hb ha),
  cSup_le := λ s a hs ha, (is_glb_Inf (upper_bounds s) hs.bdd_below_upper_bounds ⟨a, ha⟩).1 ha,
  .. H1, .. H2 }

/--
A version of `conditionally_complete_lattice_of_Sup` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `Inf` explicitly. -/
def conditionally_complete_lattice_of_lattice_of_Sup (α : Type*) [H1 : lattice α]
  [H2 : has_Sup α]
  (is_lub_Sup : ∀ s : set α, bdd_above s → s.nonempty → is_lub s (Sup s)) :
  conditionally_complete_lattice α :=
{ ..H1, ..conditionally_complete_lattice_of_Sup α
  (λ a b, ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
  (λ a b, ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
  is_lub_Sup }

/--
A version of `conditionally_complete_lattice_of_Inf` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `Sup` explicitly. -/
def conditionally_complete_lattice_of_lattice_of_Inf (α : Type*) [H1 : lattice α]
  [H2 : has_Inf α]
  (is_glb_Inf : ∀ s : set α, bdd_below s → s.nonempty → is_glb s (Inf s)) :
  conditionally_complete_lattice α :=
{ ..H1, ..conditionally_complete_lattice_of_Inf α
  (λ a b, ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
  (λ a b, ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
  is_glb_Inf }

section conditionally_complete_lattice
variables [conditionally_complete_lattice α] {s t : set α} {a b : α}

theorem le_cSup (h₁ : bdd_above s) (h₂ : a ∈ s) : a ≤ Sup s :=
conditionally_complete_lattice.le_cSup s a h₁ h₂

theorem cSup_le (h₁ : s.nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : Sup s ≤ a :=
conditionally_complete_lattice.cSup_le s a h₁ h₂

theorem cInf_le (h₁ : bdd_below s) (h₂ : a ∈ s) : Inf s ≤ a :=
conditionally_complete_lattice.cInf_le s a h₁ h₂

theorem le_cInf (h₁ : s.nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ Inf s :=
conditionally_complete_lattice.le_cInf s a h₁ h₂

theorem le_cSup_of_le (hs : bdd_above s) (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_cSup hs hb)

theorem cInf_le_of_le (hs : bdd_below s) (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (cInf_le hs hb) h

theorem cSup_le_cSup (ht : bdd_above t) (hs : s.nonempty) (h : s ⊆ t) : Sup s ≤ Sup t :=
cSup_le hs (λ a ha, le_cSup ht (h ha))

theorem cInf_le_cInf (ht : bdd_below t) (hs : s.nonempty) (h : s ⊆ t) : Inf t ≤ Inf s :=
le_cInf hs (λ a ha, cInf_le ht (h ha))

theorem le_cSup_iff (h : bdd_above s) (hs : s.nonempty) :
  a ≤ Sup s ↔ ∀ b, b ∈ upper_bounds s → a ≤ b :=
⟨λ h b hb, le_trans h (cSup_le hs hb), λ hb, hb _ (λ x, le_cSup h)⟩

theorem cInf_le_iff (h : bdd_below s) (hs : s.nonempty) :
  Inf s ≤ a ↔ ∀ b ∈ lower_bounds s, b ≤ a :=
⟨λ h b hb, le_trans (le_cInf hs hb) h, λ hb, hb _ (λ x, cInf_le h)⟩

lemma is_lub_cSup (ne : s.nonempty) (H : bdd_above s) : is_lub s (Sup s) :=
⟨λ x, le_cSup H, λ x, cSup_le ne⟩

lemma is_lub_csupr [nonempty ι] {f : ι → α} (H : bdd_above (range f)) :
  is_lub (range f) (⨆ i, f i) :=
is_lub_cSup (range_nonempty f) H

lemma is_lub_csupr_set {f : β → α} {s : set β} (H : bdd_above (f '' s)) (Hne : s.nonempty) :
  is_lub (f '' s) (⨆ i : s, f i) :=
by { rw ← Sup_image', exact is_lub_cSup (Hne.image _) H }

lemma is_glb_cInf (ne : s.nonempty) (H : bdd_below s) : is_glb s (Inf s) :=
⟨λ x, cInf_le H, λ x, le_cInf ne⟩

lemma is_glb_cinfi [nonempty ι] {f : ι → α} (H : bdd_below (range f)) :
  is_glb (range f) (⨅ i, f i) :=
is_glb_cInf (range_nonempty f) H

lemma is_glb_cinfi_set {f : β → α} {s : set β} (H : bdd_below (f '' s)) (Hne : s.nonempty) :
  is_glb (f '' s) (⨅ i : s, f i) :=
@is_lub_csupr_set αᵒᵈ _ _ _ _ H Hne

lemma csupr_le_iff [nonempty ι] {f : ι → α} {a : α} (hf : bdd_above (range f)) :
  supr f ≤ a ↔ ∀ i, f i ≤ a :=
(is_lub_le_iff $ is_lub_csupr hf).trans forall_range_iff

lemma le_cinfi_iff [nonempty ι] {f : ι → α} {a : α} (hf : bdd_below (range f)) :
  a ≤ infi f ↔ ∀ i, a ≤ f i :=
(le_is_glb_iff $ is_glb_cinfi hf).trans forall_range_iff

lemma csupr_set_le_iff {ι : Type*} {s : set ι} {f : ι → α} {a : α} (hs : s.nonempty)
  (hf : bdd_above (f '' s)) :
  (⨆ i : s, f i) ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
(is_lub_le_iff $ is_lub_csupr_set hf hs).trans ball_image_iff

lemma le_cinfi_set_iff {ι : Type*} {s : set ι} {f : ι → α} {a : α} (hs : s.nonempty)
  (hf : bdd_below (f '' s)) :
  a ≤ (⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
(le_is_glb_iff $ is_glb_cinfi_set hf hs).trans ball_image_iff

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

theorem cSup_le_iff (hb : bdd_above s) (hs : s.nonempty) : Sup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
is_lub_le_iff (is_lub_cSup hs hb)

theorem le_cInf_iff (hb : bdd_below s) (hs : s.nonempty) : a ≤ Inf s ↔ ∀ b ∈ s, a ≤ b :=
le_is_glb_iff (is_glb_cInf hs hb)

lemma cSup_lower_bounds_eq_cInf {s : set α} (h : bdd_below s) (hs : s.nonempty) :
  Sup (lower_bounds s) = Inf s :=
(is_lub_cSup h $ hs.mono $ λ x hx y hy, hy hx).unique (is_glb_cInf hs h).is_lub

lemma cInf_upper_bounds_eq_cSup {s : set α} (h : bdd_above s) (hs : s.nonempty) :
  Inf (upper_bounds s) = Sup s :=
(is_glb_cInf h $ hs.mono $ λ x hx y hy, hy hx).unique (is_lub_cSup hs h).is_glb

lemma not_mem_of_lt_cInf {x : α} {s : set α} (h : x < Inf s) (hs : bdd_below s) : x ∉ s :=
λ hx, lt_irrefl _ (h.trans_le (cInf_le hs hx))

lemma not_mem_of_cSup_lt {x : α} {s : set α} (h : Sup s < x) (hs : bdd_above s) : x ∉ s :=
@not_mem_of_lt_cInf αᵒᵈ _ x s h hs

/--Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `Sup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem cSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.nonempty)
  (H : ∀ a ∈ s, a ≤ b) (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : Sup s = b :=
eq_of_le_of_not_lt (cSup_le hs H) $ λ hb, let ⟨a, ha, ha'⟩ := H' _ hb in
  lt_irrefl _ $ ha'.trans_le $ le_cSup ⟨b, H⟩ ha

/--Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `Inf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cInf_eq_of_forall_ge_of_forall_gt_exists_lt : s.nonempty → (∀ a ∈ s, b ≤ a) →
  (∀ w, b < w → ∃ a ∈ s, a < w) → Inf s = b :=
@cSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _

/--b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
lemma lt_cSup_of_lt (hs : bdd_above s) (ha : a ∈ s) (h : b < a) : b < Sup s :=
lt_of_lt_of_le h (le_cSup hs ha)

/--Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
lemma cInf_lt_of_lt : bdd_below s → a ∈ s → a < b → Inf s < b :=
@lt_cSup_of_lt αᵒᵈ _ _ _ _

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
lemma exists_between_of_forall_le (sne : s.nonempty) (tne : t.nonempty)
  (hst : ∀ (x ∈ s) (y ∈ t), x ≤ y) : (upper_bounds s ∩ lower_bounds t).nonempty :=
⟨Inf t, λ x hx, le_cInf tne $ hst x hx, λ y hy, cInf_le (sne.mono hst) hy⟩

/--The supremum of a singleton is the element of the singleton-/
@[simp] theorem cSup_singleton (a : α) : Sup {a} = a :=
is_greatest_singleton.cSup_eq

/--The infimum of a singleton is the element of the singleton-/
@[simp] theorem cInf_singleton (a : α) : Inf {a} = a :=
is_least_singleton.cInf_eq

@[simp] theorem cSup_pair (a b : α) : Sup {a, b} = a ⊔ b :=
(@is_lub_pair _ _ a b).cSup_eq (insert_nonempty _ _)

@[simp] theorem cInf_pair (a b : α) : Inf {a, b} = a ⊓ b :=
(@is_glb_pair _ _ a b).cInf_eq (insert_nonempty _ _)

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
@cSup_union αᵒᵈ _ _ _ hs sne ht tne

/--The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le (hs : bdd_above s) (ht : bdd_above t) (hst : (s ∩ t).nonempty) :
  Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
cSup_le hst $ λ x hx, le_inf (le_cSup hs hx.1) (le_cSup ht hx.2)

/--The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter : bdd_below s → bdd_below t → (s ∩ t).nonempty →
  Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
@cSup_inter_le αᵒᵈ _ _ _

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert (hs : bdd_above s) (sne : s.nonempty) : Sup (insert a s) = a ⊔ Sup s :=
((is_lub_cSup sne hs).insert a).cSup_eq (insert_nonempty a s)

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert (hs : bdd_below s) (sne : s.nonempty) : Inf (insert a s) = a ⊓ Inf s :=
@cSup_insert αᵒᵈ _ _ _ hs sne

@[simp] lemma cInf_Icc (h : a ≤ b) : Inf (Icc a b) = a :=
(is_glb_Icc h).cInf_eq (nonempty_Icc.2 h)

@[simp] lemma cInf_Ici : Inf (Ici a) = a := is_least_Ici.cInf_eq

@[simp] lemma cInf_Ico (h : a < b) : Inf (Ico a b) = a :=
(is_glb_Ico h).cInf_eq (nonempty_Ico.2 h)

@[simp] lemma cInf_Ioc [densely_ordered α] (h : a < b) : Inf (Ioc a b) = a :=
(is_glb_Ioc h).cInf_eq (nonempty_Ioc.2 h)

@[simp] lemma cInf_Ioi [no_max_order α] [densely_ordered α] : Inf (Ioi a) = a :=
cInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (λ _, le_of_lt)
  (λ w hw, by simpa using exists_between hw)

@[simp] lemma cInf_Ioo [densely_ordered α] (h : a < b) : Inf (Ioo a b) = a :=
(is_glb_Ioo h).cInf_eq (nonempty_Ioo.2 h)

@[simp] lemma cSup_Icc (h : a ≤ b) : Sup (Icc a b) = b :=
(is_lub_Icc h).cSup_eq (nonempty_Icc.2 h)

@[simp] lemma cSup_Ico [densely_ordered α] (h : a < b) : Sup (Ico a b) = b :=
(is_lub_Ico h).cSup_eq (nonempty_Ico.2 h)

@[simp] lemma cSup_Iic : Sup (Iic a) = a := is_greatest_Iic.cSup_eq

@[simp] lemma cSup_Iio [no_min_order α] [densely_ordered α] : Sup (Iio a) = a :=
cSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (λ _, le_of_lt)
  (λ w hw, by simpa [and_comm] using exists_between hw)

@[simp] lemma cSup_Ioc (h : a < b) : Sup (Ioc a b) = b :=
(is_lub_Ioc h).cSup_eq (nonempty_Ioc.2 h)

@[simp] lemma cSup_Ioo [densely_ordered α] (h : a < b) : Sup (Ioo a b) = b :=
(is_lub_Ioo h).cSup_eq (nonempty_Ioo.2 h)

/--The indexed supremum of a function is bounded above by a uniform bound-/
lemma csupr_le [nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : supr f ≤ c :=
cSup_le (range_nonempty f) (by rwa forall_range_iff)

/--The indexed supremum of a function is bounded below by the value taken at one point-/
lemma le_csupr {f : ι → α} (H : bdd_above (range f)) (c : ι) : f c ≤ supr f :=
le_cSup H (mem_range_self _)

lemma le_csupr_of_le {f : ι → α} (H : bdd_above (range f)) (c : ι) (h : a ≤ f c) : a ≤ supr f :=
le_trans h (le_csupr H c)

/--The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
lemma csupr_mono {f g : ι → α} (B : bdd_above (range g)) (H : ∀ x, f x ≤ g x) :
  supr f ≤ supr g :=
begin
  casesI is_empty_or_nonempty ι,
  { rw [supr_of_empty', supr_of_empty'] },
  { exact csupr_le (λ x, le_csupr_of_le B x (H x)) },
end

lemma le_csupr_set {f : β → α} {s : set β}
  (H : bdd_above (f '' s)) {c : β} (hc : c ∈ s) : f c ≤ ⨆ i : s, f i :=
(le_cSup H $ mem_image_of_mem f hc).trans_eq Sup_image'

/--The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
lemma cinfi_mono {f g : ι → α} (B : bdd_below (range f)) (H : ∀ x, f x ≤ g x) :
  infi f ≤ infi g :=
@csupr_mono αᵒᵈ _ _ _ _ B H

/--The indexed minimum of a function is bounded below by a uniform lower bound-/
lemma le_cinfi [nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ infi f :=
@csupr_le αᵒᵈ _ _ _ _ _ H

/--The indexed infimum of a function is bounded above by the value taken at one point-/
lemma cinfi_le {f : ι → α} (H : bdd_below (range f)) (c : ι) : infi f ≤ f c :=
@le_csupr αᵒᵈ _ _ _ H c

lemma cinfi_le_of_le {f : ι → α} (H : bdd_below (range f)) (c : ι) (h : f c ≤ a) : infi f ≤ a :=
@le_csupr_of_le αᵒᵈ _ _ _ _ H c h

lemma cinfi_set_le {f : β → α} {s : set β}
  (H : bdd_below (f '' s)) {c : β} (hc : c ∈ s) : (⨅ i : s, f i) ≤ f c :=
@le_csupr_set αᵒᵈ _ _ _ _ H _ hc

@[simp] theorem csupr_const [hι : nonempty ι] {a : α} : (⨆ b : ι, a) = a :=
by rw [supr, range_const, cSup_singleton]

@[simp] theorem cinfi_const [hι : nonempty ι] {a : α} : (⨅ b:ι, a) = a := @csupr_const αᵒᵈ _ _ _ _

@[simp] theorem supr_unique [unique ι] {s : ι → α} : (⨆ i, s i) = s default :=
have ∀ i, s i = s default := λ i, congr_arg s (unique.eq_default i),
by simp only [this, csupr_const]

@[simp] theorem infi_unique [unique ι] {s : ι → α} : (⨅ i, s i) = s default :=
@supr_unique αᵒᵈ _ _ _ _

@[simp] lemma csupr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
by haveI := unique_prop hp; exact supr_unique

@[simp] lemma cinfi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
@csupr_pos αᵒᵈ _ _ _ hp

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
@csupr_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _ ‹_› ‹_› ‹_›

/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
lemma monotone.csupr_mem_Inter_Icc_of_antitone [semilattice_sup β]
  {f g : β → α} (hf : monotone f) (hg : antitone g) (h : f ≤ g) :
  (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
begin
  refine mem_Inter.2 (λ n, _),
  haveI : nonempty β := ⟨n⟩,
  have : ∀ m, f m ≤ g n := λ m, hf.forall_le_of_antitone hg h m n,
  exact ⟨le_csupr ⟨g $ n, forall_range_iff.2 this⟩ _, csupr_le this⟩
end

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
lemma csupr_mem_Inter_Icc_of_antitone_Icc [semilattice_sup β]
  {f g : β → α} (h : antitone (λ n, Icc (f n) (g n))) (h' : ∀ n, f n ≤ g n) :
  (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
monotone.csupr_mem_Inter_Icc_of_antitone (λ m n hmn, ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
  (λ m n hmn, ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

/--Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem cSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.nonempty)
  (h_is_ub : ∀ a ∈ s, a ≤ b) (h_b_le_ub : ∀ub, (∀ a ∈ s, a ≤ ub) → (b ≤ ub)) : Sup s = b :=
(cSup_le hs h_is_ub).antisymm (h_b_le_ub _ $ λ a, le_cSup ⟨b, h_is_ub⟩)

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

/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
lemma exists_lt_of_lt_cSup (hs : s.nonempty) (hb : b < Sup s) : ∃ a ∈ s, b < a :=
by { contrapose! hb, exact cSup_le hs hb }

/--
Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
lemma exists_lt_of_lt_csupr [nonempty ι] {f : ι → α} (h : b < supr f) : ∃ i, b < f i :=
let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_cSup (range_nonempty f) h in ⟨i, h⟩

/--When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
lemma exists_lt_of_cInf_lt (hs : s.nonempty) (hb : Inf s < b) : ∃ a ∈ s, a < b :=
@exists_lt_of_lt_cSup αᵒᵈ _ _ _ hs hb

/--
Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
lemma exists_lt_of_cinfi_lt [nonempty ι] {f : ι → α} (h : infi f < a) : ∃ i, f i < a :=
@exists_lt_of_lt_csupr αᵒᵈ _ _ _ _ _ h

open function
variables [is_well_order α (<)]

lemma Inf_eq_argmin_on (hs : s.nonempty) :
  Inf s = argmin_on id (@is_well_founded.wf α (<) _) s hs :=
is_least.cInf_eq ⟨argmin_on_mem _ _ _ _, λ a ha, argmin_on_le id _ _ ha⟩

lemma is_least_Inf (hs : s.nonempty) : is_least s (Inf s) :=
by { rw Inf_eq_argmin_on hs, exact ⟨argmin_on_mem _ _ _ _, λ a ha, argmin_on_le id _ _ ha⟩ }

lemma le_cInf_iff' (hs : s.nonempty) : b ≤ Inf s ↔ b ∈ lower_bounds s :=
le_is_glb_iff (is_least_Inf hs).is_glb

lemma Inf_mem (hs : s.nonempty) : Inf s ∈ s := (is_least_Inf hs).1

lemma infi_mem [nonempty ι] (f : ι → α) : infi f ∈ range f := Inf_mem (range_nonempty f)

lemma monotone_on.map_Inf {β : Type*} [conditionally_complete_lattice β] {f : α → β}
  (hf : monotone_on f s) (hs : s.nonempty) : f (Inf s) = Inf (f '' s) :=
(hf.map_is_least (is_least_Inf hs)).cInf_eq.symm

lemma monotone.map_Inf {β : Type*} [conditionally_complete_lattice β] {f : α → β} (hf : monotone f)
  (hs : s.nonempty) : f (Inf s) = Inf (f '' s) :=
(hf.map_is_least (is_least_Inf hs)).cInf_eq.symm

end conditionally_complete_linear_order

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `nonempty`/`set.nonempty` assumptions.
-/

section conditionally_complete_linear_order_bot

variables [conditionally_complete_linear_order_bot α]

@[simp] lemma cSup_empty : (Sup ∅ : α) = ⊥ :=
conditionally_complete_linear_order_bot.cSup_empty

@[simp] lemma csupr_of_empty [is_empty ι] (f : ι → α) : (⨆ i, f i) = ⊥ :=
by rw [supr_of_empty', cSup_empty]

@[simp] lemma csupr_false (f : false → α) : (⨆ i, f i) = ⊥ := csupr_of_empty f

@[simp] lemma cInf_univ : Inf (univ : set α) = ⊥ := is_least_univ.cInf_eq

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

theorem le_cSup_iff' {s : set α} {a : α} (h : bdd_above s) :
  a ≤ Sup s ↔ ∀ b, b ∈ upper_bounds s → a ≤ b :=
⟨λ h b hb, le_trans h (cSup_le' hb), λ hb, hb _ (λ x, le_cSup h)⟩

lemma le_csupr_iff' {s : ι → α} {a : α} (h : bdd_above (range s)) :
  a ≤ supr s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b :=
by simp [supr, h, le_cSup_iff', upper_bounds]

theorem le_cInf_iff'' {s : set α} {a : α} (ne : s.nonempty) :
  a ≤ Inf s ↔ ∀ (b : α), b ∈ s → a ≤ b :=
le_cInf_iff ⟨⊥, λ a _, bot_le⟩ ne

theorem le_cinfi_iff' [nonempty ι] {f : ι → α} {a : α} :
  a ≤ infi f ↔ ∀ i, a ≤ f i :=
le_cinfi_iff ⟨⊥, λ a _, bot_le⟩

theorem cInf_le' {s : set α} {a : α} (h : a ∈ s) : Inf s ≤ a :=
cInf_le ⟨⊥, λ a _, bot_le⟩ h

theorem cinfi_le' (f : ι → α) (i : ι) : infi f ≤ f i :=
cinfi_le ⟨⊥, λ a _, bot_le⟩ _

lemma exists_lt_of_lt_cSup' {s : set α} {a : α} (h : a < Sup s) : ∃ b ∈ s, a < b :=
by { contrapose! h, exact cSup_le' h }

lemma csupr_le_iff' {f : ι → α} (h : bdd_above (range f)) {a : α} :
  (⨆ i, f i) ≤ a ↔ ∀ i, f i ≤ a :=
(cSup_le_iff' h).trans forall_range_iff

lemma csupr_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆ i, f i) ≤ a :=
cSup_le' $ forall_range_iff.2 h

lemma exists_lt_of_lt_csupr' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i :=
by { contrapose! h, exact csupr_le' h }

lemma csupr_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : bdd_above (range g))
  (h : ∀ i, ∃ i', f i ≤ g i') : supr f ≤ supr g :=
csupr_le' $ λ i, exists.elim (h i) (le_csupr_of_le hg)

lemma cInf_le_cInf' {s t : set α} (h₁ : t.nonempty) (h₂ : t ⊆ s) : Inf s ≤ Inf t :=
cInf_le_cInf (order_bot.bdd_below s) h₁ h₂

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
      { exact le_rfl },
      { exact false.elim (not_top_le_coe a (ha h)) } },
    { rintro (⟨⟩|b) hb,
      { exact le_top },
      refine some_le_some.2 (cSup_le _ _),
      { rcases hs with ⟨⟨⟩|b, hb⟩,
        { exact absurd hb h },
        { exact ⟨b, hb⟩ } },
      { intros a ha, exact some_le_some.1 (hb ha) } },
    { rintro (⟨⟩|b) hb,
      { exact le_rfl },
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
{ Sup := Sup, le_Sup := λ s, (is_lub_Sup s).1, Sup_le := λ s, (is_lub_Sup s).2,
  Inf := Inf, le_Inf := λ s, (is_glb_Inf s).2, Inf_le := λ s, (is_glb_Inf s).1,
  .. with_top.linear_order, ..with_top.lattice, ..with_top.order_top, ..with_top.order_bot }

/-- A version of `with_top.coe_Sup'` with a more convenient but less general statement. -/
@[norm_cast] lemma coe_Sup {s : set α} (hb : bdd_above s) :
  ↑(Sup s) = (⨆ a ∈ s, ↑a : with_top α) :=
by rw [coe_Sup' hb, Sup_image]

/-- A version of `with_top.coe_Inf'` with a more convenient but less general statement. -/
@[norm_cast] lemma coe_Inf {s : set α} (hs : s.nonempty) :
  ↑(Inf s) = (⨅ a ∈ s, ↑a : with_top α) :=
by rw [coe_Inf' hs, Inf_image]

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
@le_cSup_image αᵒᵈ βᵒᵈ _ _ _ (λ x y hxy, h_mono hxy) _ _ hcs h_bdd

lemma le_cInf_image {s : set α} (hs : s.nonempty) {B : α} (hB: B ∈ lower_bounds s) :
  f B ≤ Inf (f '' s) :=
@cSup_image_le αᵒᵈ βᵒᵈ _ _ _ (λ x y hxy, h_mono hxy) _ hs _ hB

end monotone

namespace galois_connection
variables [conditionally_complete_lattice α] [conditionally_complete_lattice β] [nonempty ι]
  {l : α → β} {u : β → α}

lemma l_cSup (gc : galois_connection l u) {s : set α} (hne : s.nonempty)
  (hbdd : bdd_above s) :
  l (Sup s) = ⨆ x : s, l x :=
eq.symm $ is_lub.csupr_set_eq (gc.is_lub_l_image $ is_lub_cSup hne hbdd) hne

lemma l_cSup' (gc : galois_connection l u) {s : set α} (hne : s.nonempty) (hbdd : bdd_above s) :
  l (Sup s) = Sup (l '' s) :=
by rw [gc.l_cSup hne hbdd, Sup_image']

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
variables [conditionally_complete_lattice α] [conditionally_complete_lattice β] [nonempty ι]

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
### Supremum/infimum of `set.image2`

A collection of lemmas showing what happens to the suprema/infima of `s` and `t` when mapped under
a binary function whose partial evaluations are lower/upper adjoints of Galois connections.
-/

section
variables [conditionally_complete_lattice α] [conditionally_complete_lattice β]
  [conditionally_complete_lattice γ] {f : α → β → γ} {s : set α} {t : set β}

variables {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

lemma cSup_image2_eq_cSup_cSup (h₁ : ∀ b, galois_connection (swap l b) (u₁ b))
  (h₂ : ∀ a, galois_connection (l a) (u₂ a))
  (hs₀ : s.nonempty) (hs₁ : bdd_above s) (ht₀ : t.nonempty) (ht₁ : bdd_above t) :
  Sup (image2 l s t) = l (Sup s) (Sup t) :=
begin
  refine eq_of_forall_ge_iff (λ c, _),
  rw [cSup_le_iff (hs₁.image2 (λ _, (h₁ _).monotone_l) (λ _, (h₂ _).monotone_l) ht₁)
    (hs₀.image2 ht₀), forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, cSup_le_iff ht₁ ht₀],
  simp_rw [←(h₂ _).le_iff_le, (h₁ _).le_iff_le, cSup_le_iff hs₁ hs₀],
end

lemma cSup_image2_eq_cSup_cInf (h₁ : ∀ b, galois_connection (swap l b) (u₁ b))
  (h₂ : ∀ a, galois_connection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
  s.nonempty → bdd_above s → t.nonempty → bdd_below t → Sup (image2 l s t) = l (Sup s) (Inf t) :=
@cSup_image2_eq_cSup_cSup _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cSup_image2_eq_cInf_cSup (h₁ : ∀ b, galois_connection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
  (h₂ : ∀ a, galois_connection (l a) (u₂ a)) :
  s.nonempty → bdd_below s → t.nonempty → bdd_above t → Sup (image2 l s t) = l (Inf s) (Sup t) :=
@cSup_image2_eq_cSup_cSup αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cSup_image2_eq_cInf_cInf (h₁ : ∀ b, galois_connection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
  (h₂ : ∀ a, galois_connection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
  s.nonempty → bdd_below s → t.nonempty → bdd_below t → Sup (image2 l s t) = l (Inf s) (Inf t) :=
@cSup_image2_eq_cSup_cSup αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cInf_image2_eq_cInf_cInf (h₁ : ∀ b, galois_connection (l₁ b) (swap u b))
  (h₂ : ∀ a, galois_connection (l₂ a) (u a)) :
  s.nonempty → bdd_below s → t.nonempty → bdd_below t →
  Inf (image2 u s t) = u (Inf s) (Inf t) :=
@cSup_image2_eq_cSup_cSup αᵒᵈ βᵒᵈ γᵒᵈ _ _ _ _ _ _ l₁ l₂ (λ _, (h₁ _).dual) (λ _, (h₂ _).dual)

lemma cInf_image2_eq_cInf_cSup (h₁ : ∀ b, galois_connection (l₁ b) (swap u b))
  (h₂ : ∀ a, galois_connection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
  s.nonempty → bdd_below s → t.nonempty → bdd_above t → Inf (image2 u s t) = u (Inf s) (Sup t) :=
@cInf_image2_eq_cInf_cInf _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cInf_image2_eq_cSup_cInf (h₁ : ∀ b, galois_connection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
  (h₂ : ∀ a, galois_connection (l₂ a) (u a)) :
  s.nonempty → bdd_above s → t.nonempty → bdd_below t → Inf (image2 u s t) = u (Sup s) (Inf t) :=
@cInf_image2_eq_cInf_cInf αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂

lemma cInf_image2_eq_cSup_cSup (h₁ : ∀ b, galois_connection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
  (h₂ : ∀ a, galois_connection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
  s.nonempty →  bdd_above s → t.nonempty → bdd_above t → Inf (image2 u s t) = u (Sup s) (Sup t) :=
@cInf_image2_eq_cInf_cInf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂

end

section with_top_bot

/-!
### Complete lattice structure on `with_top (with_bot α)`

If `α` is a `conditionally_complete_lattice`, then we show that `with_top α` and `with_bot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `with_top (with_bot α)` and `with_bot (with_top α)` naturally inherit the structure of a
complete lattice. Note that for `α` a conditionally complete lattice, `Sup` and `Inf` both return
junk values for sets which are empty or unbounded. The extension of `Sup` to `with_top α` fixes
the unboundedness problem and the extension to `with_bot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals `[-∞, ∞]` are a complete linear order.
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
{ le_cSup := (@with_top.conditionally_complete_lattice αᵒᵈ _).cInf_le,
  cSup_le := (@with_top.conditionally_complete_lattice αᵒᵈ _).le_cInf,
  cInf_le := (@with_top.conditionally_complete_lattice αᵒᵈ _).le_cSup,
  le_cInf := (@with_top.conditionally_complete_lattice αᵒᵈ _).cSup_le,
  ..with_bot.lattice,
  ..with_bot.has_Sup,
  ..with_bot.has_Inf }

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
      { cases a with a, exact le_rfl,
        cases (h haS); tauto },
      { cases a,
        { exact le_top },
        { apply with_top.some_le_some.2, refine cInf_le _ haS, use ⊥, intros b hb, exact bot_le } }
    end,
  le_Inf := λ S a haS, (with_top.is_glb_Inf' ⟨a, haS⟩).2 haS,
  ..with_top.has_Inf,
  ..with_top.has_Sup,
  ..with_top.bounded_order,
  ..with_top.lattice }


noncomputable instance with_top.with_bot.complete_linear_order {α : Type*}
  [conditionally_complete_linear_order α] : complete_linear_order (with_top (with_bot α)) :=
{ .. with_top.with_bot.complete_lattice,
  .. with_top.linear_order }

noncomputable instance with_bot.with_top.complete_lattice {α : Type*}
  [conditionally_complete_lattice α] : complete_lattice (with_bot (with_top α)) :=
{ le_Sup := (@with_top.with_bot.complete_lattice αᵒᵈ _).Inf_le,
  Sup_le := (@with_top.with_bot.complete_lattice αᵒᵈ _).le_Inf,
  Inf_le := (@with_top.with_bot.complete_lattice αᵒᵈ _).le_Sup,
  le_Inf := (@with_top.with_bot.complete_lattice αᵒᵈ _).Sup_le,
  ..with_bot.has_Inf,
  ..with_bot.has_Sup,
  ..with_bot.bounded_order,
  ..with_bot.lattice }

noncomputable instance with_bot.with_top.complete_linear_order {α : Type*}
  [conditionally_complete_linear_order α] : complete_linear_order (with_bot (with_top α)) :=
{ .. with_bot.with_top.complete_lattice,
  .. with_bot.linear_order }

lemma with_top.supr_coe_eq_top {ι : Sort*} {α : Type*} [conditionally_complete_linear_order_bot α]
  (f : ι → α) : (⨆ x, (f x : with_top α)) = ⊤ ↔ ¬ bdd_above (set.range f) :=
begin
  rw [supr_eq_top, not_bdd_above_iff],
  refine ⟨λ hf r, _, λ hf a ha, _⟩,
  { rcases hf r (with_top.coe_lt_top r) with ⟨i, hi⟩,
    exact ⟨f i, ⟨i, rfl⟩, with_top.coe_lt_coe.mp hi⟩ },
  { rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩,
    exact ⟨i, by simpa only [with_top.coe_untop _ ha.ne] using with_top.coe_lt_coe.mpr hi⟩ },
end

lemma with_top.supr_coe_lt_top {ι : Sort*} {α : Type*} [conditionally_complete_linear_order_bot α]
  (f : ι → α) : (⨆ x, (f x : with_top α)) < ⊤ ↔ bdd_above (set.range f) :=
lt_top_iff_ne_top.trans $ (with_top.supr_coe_eq_top f).not.trans not_not

end with_top_bot

-- Guard against import creep
assert_not_exists multiset
