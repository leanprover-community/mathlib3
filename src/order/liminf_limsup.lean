/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl

Defines the Liminf/Limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `f.Limsup` (`f.Liminf`) where `f` is a filter taking values in a conditionally complete
lattice. `f.Limsup` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`f.Liminf`). To work with the Limsup along a function `u` use `(f.map u).Limsup`.

Usually, one defines the Limsup as `Inf (Sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `Inf_n (Sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `Limsup (λx, 1/x)` on ℝ. Then
there is no guarantee that the quantity above really decreases (the value of the `Sup` beforehand is
not really well defined, as one can not use ∞), so that the Inf could be anything. So one can not
use this `Inf Sup ...` definition in conditionally complete lattices, and one has to use the
following less tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.

We use cLimsup in theorems in conditionally complete lattices, and Limsup for the corresponding
theorems in complete lattices (usually with less assumptions).

-/

import order.filter order.conditionally_complete_lattice order.bounds
open lattice filter set

variables {α : Type*} {β : Type*}
namespace filter

section relation

/-- `f.is_bounded (≺)`: the filter `f` is eventually bounded w.r.t. the relation `≺`, i.e.
eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `≤` or `≥`. -/
def is_bounded (r : α → α → Prop) (f : filter α) := ∃b, {x | r x b} ∈ f.sets

def is_bounded_under (r : α → α → Prop) (f : filter β) (u : β → α) := (f.map u).is_bounded r

variables {r : α → α → Prop} {f g : filter α}

/-- `f` is eventually bounded if and only if, there exists an admissible set on which it is
bounded. -/
lemma is_bounded_iff : f.is_bounded r ↔ (∃s∈f.sets, ∃b, s ⊆ {x | r x b}) :=
iff.intro
  (assume ⟨b, hb⟩, ⟨{a | r a b}, hb, b, subset.refl _⟩)
  (assume ⟨s, hs, b, hb⟩, ⟨b, mem_sets_of_superset hs hb⟩)

/-- A bounded function `u` is in particular eventually bounded. -/
lemma is_bounded_under_of {f : filter β} {u : β → α} :
  (∃b, ∀x, r (u x) b) → f.is_bounded_under r u
| ⟨b, hb⟩ := ⟨b, show {x | r (u x) b} ∈ f.sets, from univ_mem_sets' hb⟩

lemma is_bounded_bot : is_bounded r ⊥ ↔ nonempty α :=
by simp [is_bounded, exists_true_iff_nonempty]

lemma is_bounded_top : is_bounded r ⊤ ↔ (∃t, ∀x, r x t) :=
by simp [is_bounded, eq_univ_iff_forall]

lemma is_bounded_principal (s : set α) : is_bounded r (principal s) ↔ (∃t, ∀x∈s, r x t) :=
by simp [is_bounded, subset_def]

lemma is_bounded_sup [is_trans α r] (hr : ∀b₁ b₂, ∃b, r b₁ b ∧ r b₂ b) :
  is_bounded r f → is_bounded r g → is_bounded r (f ⊔ g)
| ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ := let ⟨b, rb₁b, rb₂b⟩ := hr b₁ b₂ in
  ⟨b, mem_sup_sets.2 ⟨
    mem_sets_of_superset h₁ $ assume x rxb₁, show r x b, from trans rxb₁ rb₁b,
    mem_sets_of_superset h₂ $ assume x rxb₂, show r x b, from trans rxb₂ rb₂b⟩⟩

lemma is_bounded_of_le (h : f ≤ g) : is_bounded r g → is_bounded r f
| ⟨b, hb⟩ := ⟨b, h hb⟩

lemma is_bounded_under_of_is_bounded {q : β → β → Prop} {u : α → β}
  (hf : ∀a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) : f.is_bounded r → f.is_bounded_under q u
| ⟨b, h⟩ := ⟨u b, show {x : α | q (u x) (u b)} ∈ f.sets, from mem_sets_of_superset h $ assume a, hf _ _⟩

/-- `is_cobounded (≺) f` states that filter `f` is not tend to infinite w.r.t. `≺`. This is also
called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.is_cobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀a, {n | a ≤ n} ∈ f.sets`
would not work as well in this case.
-/
def is_cobounded (r : α → α → Prop) (f : filter α) := ∃b, ∀a, {x | r x a} ∈ f.sets → r b a

def is_cobounded_under (r : α → α → Prop) (f : filter β) (u : β → α) := (f.map u).is_cobounded r

/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter.-/
lemma is_cobounded.mk [is_trans α r] (a : α) (h : ∀s∈f.sets, ∃x∈s, r a x) : f.is_cobounded r :=
⟨a, assume y s, let ⟨x, h₁, h₂⟩ := h _ s in trans h₂ h₁⟩

/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
lemma is_cobounded_of_is_bounded [is_trans α r] (hf : f ≠ ⊥) :
  f.is_bounded r → f.is_cobounded (flip r)
| ⟨a, ha⟩ := ⟨a, assume b hb,
  have {x : α | r x a ∧ r b x} ∈ f.sets, from inter_mem_sets ha hb,
  let ⟨x, rxa, rbx⟩ := inhabited_of_mem_sets hf this in
  show r b a, from trans rbx rxa⟩

lemma is_cobounded_bot : is_cobounded r ⊥ ↔ (∃b, ∀x, r b x) :=
by simp [is_cobounded]

lemma is_cobounded_top : is_cobounded r ⊤ ↔ nonempty α :=
by simp [is_cobounded, eq_univ_iff_forall, exists_true_iff_nonempty] {contextual := tt}

lemma is_cobounded_principal (s : set α) :
  (principal s).is_cobounded r↔ (∃b, ∀a, (∀x∈s, r x a) → r b a) :=
by simp [is_cobounded, subset_def]

lemma is_cobounded_of_le (h : f ≤ g) : f.is_cobounded r → g.is_cobounded r
| ⟨b, hb⟩ := ⟨b, assume a ha, hb a (h ha)⟩

end relation

instance is_trans_le [preorder α] : is_trans α (≤) := ⟨assume a b c, le_trans⟩
instance is_trans_ge [preorder α] : is_trans α (≥) := ⟨assume a b c h₁ h₂, le_trans h₂ h₁⟩

lemma is_cobounded_le_of_bot [order_bot α] {f : filter α} : f.is_cobounded (≤) :=
⟨⊥, assume a h, bot_le⟩
lemma is_cobounded_ge_of_top [order_top α] {f : filter α} : f.is_cobounded (≥) :=
⟨⊤, assume a h, le_top⟩
lemma is_bounded_le_of_top [order_top α] {f : filter α} : f.is_bounded (≤) :=
⟨⊤, univ_mem_sets' $ assume a, le_top⟩
lemma is_bounded_ge_of_bot [order_bot α] {f : filter α} : f.is_bounded (≥) :=
⟨⊥, univ_mem_sets' $ assume a, bot_le⟩

lemma is_bounded_under_sup [semilattice_sup α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≤) u → f.is_bounded_under (≤) v → f.is_bounded_under (≤) (λa, u a ⊔ v a)
| ⟨bu, (hu : {x | u x ≤ bu} ∈ f.sets)⟩ ⟨bv, (hv : {x | v x ≤ bv} ∈ f.sets)⟩ :=
  ⟨bu ⊔ bv, show {x | u x ⊔ v x ≤ bu ⊔ bv} ∈ f.sets,
    by filter_upwards [hu, hv] assume x, sup_le_sup⟩

lemma is_bounded_under_inf [semilattice_inf α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≥) u → f.is_bounded_under (≥) v → f.is_bounded_under (≥) (λa, u a ⊓ v a)
| ⟨bu, (hu : {x | u x ≥ bu} ∈ f.sets)⟩ ⟨bv, (hv : {x | v x ≥ bv} ∈ f.sets)⟩ :=
  ⟨bu ⊓ bv, show {x | u x ⊓ v x ≥ bu ⊓ bv} ∈ f.sets,
    by filter_upwards [hu, hv] assume x, inf_le_inf⟩

meta def is_bounded_default : tactic unit :=
tactic.applyc ``is_cobounded_le_of_bot <|>
tactic.applyc ``is_cobounded_ge_of_top <|>
tactic.applyc ``is_bounded_le_of_top <|>
tactic.applyc ``is_bounded_ge_of_bot


section conditionally_complete_lattice
variables [conditionally_complete_lattice α]

def Limsup (f : filter α) : α := Inf {a | {n | n ≤ a} ∈ f.sets}
def Liminf (f : filter α) : α := Sup {a | {n | a ≤ n} ∈ f.sets}

def limsup (f : filter β) (u : β → α) : α := (f.map u).Limsup
def liminf (f : filter β) (u : β → α) : α := (f.map u).Liminf

section
variables {f : filter β} {u : β → α}
theorem limsup_eq : f.limsup u = Inf {a:α | {n | u n ≤ a} ∈ f.sets} := rfl
theorem liminf_eq : f.liminf u = Sup {a:α | {n | a ≤ u n} ∈ f.sets} := rfl
end

theorem Limsup_le_of_le {f : filter α} {a} :
  f.is_cobounded (≤) → {n | n ≤ a} ∈ f.sets → f.Limsup ≤ a := cInf_le
theorem le_Liminf_of_le {f : filter α} {a} :
   f.is_cobounded (≥) → {n | a ≤ n} ∈ f.sets → a ≤ f.Liminf := le_cSup

theorem le_Limsup_of_le {f : filter α} {a}
  (hf : f.is_bounded (≤)) (h : ∀b, {n : α | n ≤ b} ∈ f.sets → a ≤ b) : a ≤ f.Limsup :=
le_cInf (ne_empty_iff_exists_mem.2 hf) h

theorem Liminf_le_of_le {f : filter α} {a}
  (hf : f.is_bounded (≥)) (h : ∀b, {n : α | b ≤ n} ∈ f.sets → b ≤ a) : f.Liminf ≤ a :=
cSup_le (ne_empty_iff_exists_mem.2 hf) h

theorem Liminf_le_Limsup {f : filter α}
  (hf : f ≠ ⊥) (h₁ : f.is_bounded (≤)) (h₂ : f.is_bounded (≥)) : f.Liminf ≤ f.Limsup :=
Liminf_le_of_le h₂ $ assume a₀ ha₀, le_Limsup_of_le h₁ $ assume a₁ ha₁, show a₀ ≤ a₁, from
  have {b | a₀ ≤ b ∧ b ≤ a₁} ∈ f.sets, from inter_mem_sets ha₀ ha₁,
  let ⟨b, hb₀, hb₁⟩ := inhabited_of_mem_sets hf this in
  le_trans hb₀ hb₁

lemma Liminf_le_Liminf {f g : filter α}
  (hf : f.is_bounded (≥) . is_bounded_default) (hg : g.is_cobounded (≥) . is_bounded_default)
  (h : ∀a, {n : α | a ≤ n} ∈ f.sets → {n : α | a ≤ n} ∈ g.sets) : f.Liminf ≤ g.Liminf :=
let ⟨a, ha⟩ := hf in cSup_le_cSup hg (ne_empty_of_mem ha) h

lemma Limsup_le_Limsup {f g : filter α}
  (hf : f.is_cobounded (≤) . is_bounded_default) (hg : g.is_bounded (≤) . is_bounded_default)
  (h : ∀a, {n : α | n ≤ a} ∈ g.sets → {n : α | n ≤ a} ∈ f.sets) : f.Limsup ≤ g.Limsup :=
let ⟨a, ha⟩ := hg in cInf_le_cInf hf (ne_empty_of_mem ha) h

lemma Limsup_le_Limsup_of_le {f g : filter α} (h : f ≤ g)
  (hf : f.is_cobounded (≤) . is_bounded_default) (hg : g.is_bounded (≤) . is_bounded_default) :
  f.Limsup ≤ g.Limsup :=
Limsup_le_Limsup hf hg (assume a ha, h ha)

lemma Liminf_le_Liminf_of_le {f g : filter α} (h : g ≤ f)
  (hf : f.is_bounded (≥) . is_bounded_default) (hg : g.is_cobounded (≥) . is_bounded_default) :
  f.Liminf ≤ g.Liminf :=
Liminf_le_Liminf hf hg (assume a ha, h ha)

lemma limsup_le_limsup [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : {a | u a ≤ v a} ∈ f.sets)
  (hu : f.is_cobounded_under (≤) u . is_bounded_default)
  (hv : f.is_bounded_under (≤) v . is_bounded_default) :
  f.limsup u ≤ f.limsup v :=
Limsup_le_Limsup hu hv $ assume b (hb : {a | v a ≤ b} ∈ f.sets), show {a | u a ≤ b} ∈ f.sets,
  by filter_upwards [h, hb] assume a, le_trans

lemma liminf_le_liminf [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : {a | u a ≤ v a} ∈ f.sets)
  (hu : f.is_bounded_under (≥) u . is_bounded_default)
  (hv : f.is_cobounded_under (≥) v . is_bounded_default) :
  f.liminf u ≤ f.liminf v :=
Liminf_le_Liminf hu hv $ assume b (hb : {a | b ≤ u a} ∈ f.sets), show {a | b ≤ v a} ∈ f.sets,
  by filter_upwards [hb, h] assume a, le_trans

theorem Limsup_principal {s : set α} (h : bdd_above s) (hs : s ≠ ∅) :
  (principal s).Limsup = Sup s :=
by simp [Limsup]; exact cInf_lower_bounds_eq_cSup h hs

theorem Liminf_principal {s : set α} (h : bdd_below s) (hs : s ≠ ∅) :
  (principal s).Liminf = Inf s :=
by simp [Liminf]; exact cSup_upper_bounds_eq_cInf h hs

end conditionally_complete_lattice

section complete_lattice
variables [complete_lattice α]

@[simp] theorem Limsup_bot : (⊥ : filter α).Limsup = ⊥ :=
bot_unique $ Inf_le $ by simp

@[simp] theorem Liminf_bot : (⊥ : filter α).Liminf = ⊤ :=
top_unique $ le_Sup $ by simp

@[simp] theorem Limsup_top : (⊤ : filter α).Limsup = ⊤ :=
top_unique $ le_Inf $
  by simp [eq_univ_iff_forall]; exact assume b hb, (top_unique $ hb _)

@[simp] theorem Liminf_top : (⊤ : filter α).Liminf = ⊥ :=
bot_unique $ Sup_le $
  by simp [eq_univ_iff_forall]; exact assume b hb, (bot_unique $ hb _)

theorem Limsup_eq_infi_Sup {f : filter α} : f.Limsup = ⨅s∈f.sets, Sup s :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, Inf_le $ show {n : α | n ≤ Sup s} ∈ f.sets,
    by filter_upwards [hs] assume a, le_Sup)
  (le_Inf $ assume a (ha : {n : α | n ≤ a} ∈ f.sets),
    infi_le_of_le _ $ infi_le_of_le ha $ Sup_le $ assume b, id)

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_infi_supr {f : filter β} {u : β → α} : f.limsup u = ⨅s∈f.sets, ⨆a∈s, u a :=
calc f.limsup u = ⨅s∈(f.map u).sets, Sup s : Limsup_eq_infi_Sup
  ... = ⨅s∈f.sets, ⨆a∈s, u a :
    le_antisymm
      (le_infi $ assume s, le_infi $ assume hs,
        infi_le_of_le (u '' s) $ infi_le_of_le (image_mem_map hs) $ le_of_eq Sup_image)
      (le_infi $ assume s, le_infi $ assume (hs : u ⁻¹' s ∈ f.sets),
        infi_le_of_le _ $ infi_le_of_le hs $ supr_le $ assume a, supr_le $ assume ha, le_Sup ha)

theorem Liminf_eq_supr_Inf {f : filter α} : f.Liminf = ⨆s∈f.sets, Inf s :=
le_antisymm
  (Sup_le $ assume a (ha : {n : α | a ≤ n} ∈ f.sets),
    le_supr_of_le _ $ le_supr_of_le ha $ le_Inf $ assume b, id)
  (supr_le $ assume s, supr_le $ assume hs, le_Sup $ show {n : α | Inf s ≤ n} ∈ f.sets,
    by filter_upwards [hs] assume a, Inf_le)

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_supr_infi {f : filter β} {u : β → α} : f.liminf u = ⨆s∈f.sets, ⨅a∈s, u a :=
calc f.liminf u = ⨆s∈(f.map u).sets, Inf s : Liminf_eq_supr_Inf
  ... = ⨆s∈f.sets, ⨅a∈s, u a :
    le_antisymm
      (supr_le $ assume s, supr_le $ assume (hs : u ⁻¹' s ∈ f.sets),
        le_supr_of_le _ $ le_supr_of_le hs $ le_infi $ assume a, le_infi $ assume ha, Inf_le ha)
      (supr_le $ assume s, supr_le $ assume hs,
        le_supr_of_le (u '' s) $ le_supr_of_le (image_mem_map hs) $ ge_of_eq Inf_image)

end complete_lattice

end filter
