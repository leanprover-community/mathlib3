/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl
-/
import order.filter.partial
import order.filter.at_top_bot

/-!
# liminfs and limsups of functions and filters

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
use this `Inf Sup ...` definition in conditionally complete lattices, and one has to use a less
tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/

open filter set

variables {α : Type*} {β : Type*}
namespace filter

section relation

/-- `f.is_bounded (≺)`: the filter `f` is eventually bounded w.r.t. the relation `≺`, i.e.
eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `≤` or `≥`. -/
def is_bounded (r : α → α → Prop) (f : filter α) := ∃ b, ∀ᶠ x in f, r x b

/-- `f.is_bounded_under (≺) u`: the image of the filter `f` under `u` is eventually bounded w.r.t.
the relation `≺`, i.e. eventually, it is bounded by some uniform bound. -/
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
| ⟨b, hb⟩ := ⟨b, show ∀ᶠ x in f, r (u x) b, from eventually_of_forall _ hb⟩

lemma is_bounded_bot : is_bounded r ⊥ ↔ nonempty α :=
by simp [is_bounded, exists_true_iff_nonempty]

lemma is_bounded_top : is_bounded r ⊤ ↔ (∃t, ∀x, r x t) :=
by simp [is_bounded, eq_univ_iff_forall]

lemma is_bounded_principal (s : set α) : is_bounded r (principal s) ↔ (∃t, ∀x∈s, r x t) :=
by simp [is_bounded, subset_def]

lemma is_bounded_sup [is_trans α r] (hr : ∀b₁ b₂, ∃b, r b₁ b ∧ r b₂ b) :
  is_bounded r f → is_bounded r g → is_bounded r (f ⊔ g)
| ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ := let ⟨b, rb₁b, rb₂b⟩ := hr b₁ b₂ in
  ⟨b, eventually_sup.mpr ⟨h₁.mono (λ x h, trans h rb₁b), h₂.mono (λ x h, trans h rb₂b)⟩⟩

lemma is_bounded_of_le (h : f ≤ g) : is_bounded r g → is_bounded r f
| ⟨b, hb⟩ := ⟨b, h hb⟩

lemma is_bounded_under_of_is_bounded {q : β → β → Prop} {u : α → β}
  (hf : ∀a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) : f.is_bounded r → f.is_bounded_under q u
| ⟨b, h⟩ := ⟨u b, show ∀ᶠ x in f, q (u x) (u b), from h.mono (λ x, hf x b)⟩

/-- `is_cobounded (≺) f` states that the filter `f` does not tend to infinity w.r.t. `≺`. This is
also called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.is_cobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀ a, ∀ᶠ n in f, a ≤ n`
would not work as well in this case.
-/
def is_cobounded (r : α → α → Prop) (f : filter α) := ∃b, ∀a, (∀ᶠ x in f, r x a) → r b a

/-- `is_cobounded_under (≺) f u` states that the image of the filter `f` under the map `u` does not
tend to infinity w.r.t. `≺`. This is also called frequently bounded. Will be usually instantiated
with `≤` or `≥`. -/
def is_cobounded_under (r : α → α → Prop) (f : filter β) (u : β → α) := (f.map u).is_cobounded r

/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter.-/
lemma is_cobounded.mk [is_trans α r] (a : α) (h : ∀s∈f, ∃x∈s, r a x) : f.is_cobounded r :=
⟨a, assume y s, let ⟨x, h₁, h₂⟩ := h _ s in trans h₂ h₁⟩

/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
lemma is_cobounded_of_is_bounded [is_trans α r] (hf : f ≠ ⊥) :
  f.is_bounded r → f.is_cobounded (flip r)
| ⟨a, ha⟩ := ⟨a, assume b hb,
  have ∀ᶠ x in f, r x a ∧ r b x, from ha.and hb,
  let ⟨x, rxa, rbx⟩ := nonempty_of_mem_sets hf this in
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

@[nolint ge_or_gt] -- see Note [nolint_ge]
instance is_trans_ge [preorder α] : is_trans α (≥) := ⟨assume a b c h₁ h₂, le_trans h₂ h₁⟩

lemma is_cobounded_le_of_bot [order_bot α] {f : filter α} : f.is_cobounded (≤) :=
⟨⊥, assume a h, bot_le⟩

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma is_cobounded_ge_of_top [order_top α] {f : filter α} : f.is_cobounded (≥) :=
⟨⊤, assume a h, le_top⟩

lemma is_bounded_le_of_top [order_top α] {f : filter α} : f.is_bounded (≤) :=
⟨⊤, eventually_of_forall _ $ λ _, le_top⟩

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma is_bounded_ge_of_bot [order_bot α] {f : filter α} : f.is_bounded (≥) :=
⟨⊥, eventually_of_forall _ $ λ _, bot_le⟩

lemma is_bounded_under_sup [semilattice_sup α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≤) u → f.is_bounded_under (≤) v → f.is_bounded_under (≤) (λa, u a ⊔ v a)
| ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩ ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ :=
  ⟨bu ⊔ bv, show ∀ᶠ x in f, u x ⊔ v x ≤ bu ⊔ bv,
    by filter_upwards [hu, hv] assume x, sup_le_sup⟩

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma is_bounded_under_inf [semilattice_inf α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≥) u → f.is_bounded_under (≥) v → f.is_bounded_under (≥) (λa, u a ⊓ v a)
| ⟨bu, (hu : ∀ᶠ x in f, u x ≥ bu)⟩ ⟨bv, (hv : ∀ᶠ x in f, v x ≥ bv)⟩ :=
  ⟨bu ⊓ bv, show ∀ᶠ x in f, u x ⊓ v x ≥ bu ⊓ bv,
    by filter_upwards [hu, hv] assume x, inf_le_inf⟩

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `is_bounded_default` in the statements,
in the form `(hf : f.is_bounded (≥) . is_bounded_default)`. -/
meta def is_bounded_default : tactic unit :=
tactic.applyc ``is_cobounded_le_of_bot <|>
tactic.applyc ``is_cobounded_ge_of_top <|>
tactic.applyc ``is_bounded_le_of_top <|>
tactic.applyc ``is_bounded_ge_of_bot


section conditionally_complete_lattice
variables [conditionally_complete_lattice α]

/-- The `Limsup` of a filter `f` is the infimum of the `a` such that, eventually for `f`,
holds `x ≤ a`. -/
def Limsup (f : filter α) : α := Inf { a | ∀ᶠ n in f, n ≤ a }

/-- The `Liminf` of a filter `f` is the supremum of the `a` such that, eventually for `f`,
holds `x ≥ a`. -/
def Liminf (f : filter α) : α := Sup { a | ∀ᶠ n in f, a ≤ n }

/-- The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that,
eventually for `f`, holds `u x ≤ a`. -/
def limsup (f : filter β) (u : β → α) : α := (f.map u).Limsup

/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that,
eventually for `f`, holds `u x ≥ a`. -/
def liminf (f : filter β) (u : β → α) : α := (f.map u).Liminf

section
variables {f : filter β} {u : β → α}
theorem limsup_eq : f.limsup u = Inf { a | ∀ᶠ n in f, u n ≤ a } := rfl
theorem liminf_eq : f.liminf u = Sup { a | ∀ᶠ n in f, a ≤ u n } := rfl
end

theorem Limsup_le_of_le {f : filter α} {a}
  (hf : f.is_cobounded (≤) . is_bounded_default) (h : ∀ᶠ n in f, n ≤ a) : f.Limsup ≤ a :=
cInf_le hf h

theorem le_Liminf_of_le {f : filter α} {a}
  (hf : f.is_cobounded (≥) . is_bounded_default) (h : ∀ᶠ n in f, a ≤ n) : a ≤ f.Liminf :=
le_cSup hf h

theorem le_Limsup_of_le {f : filter α} {a}
  (hf : f.is_bounded (≤) . is_bounded_default) (h : ∀ b, (∀ᶠ n in f, n ≤ b) → a ≤ b) :
  a ≤ f.Limsup :=
le_cInf hf h

theorem Liminf_le_of_le {f : filter α} {a}
  (hf : f.is_bounded (≥) . is_bounded_default) (h : ∀ b, (∀ᶠ n in f, b ≤ n) → b ≤ a) :
  f.Liminf ≤ a :=
cSup_le hf h

theorem Liminf_le_Limsup {f : filter α} (hf : f ≠ ⊥)
  (h₁ : f.is_bounded (≤) . is_bounded_default) (h₂ : f.is_bounded (≥) . is_bounded_default) :
  f.Liminf ≤ f.Limsup :=
Liminf_le_of_le h₂ $ assume a₀ ha₀, le_Limsup_of_le h₁ $ assume a₁ ha₁, show a₀ ≤ a₁, from
  have ∀ᶠ b in f, a₀ ≤ b ∧ b ≤ a₁, from ha₀.and ha₁,
  let ⟨b, hb₀, hb₁⟩ := nonempty_of_mem_sets hf this in
  le_trans hb₀ hb₁

lemma Liminf_le_Liminf {f g : filter α}
  (hf : f.is_bounded (≥) . is_bounded_default) (hg : g.is_cobounded (≥) . is_bounded_default)
  (h : ∀ a, (∀ᶠ n in f, a ≤ n) → ∀ᶠ n in g, a ≤ n) : f.Liminf ≤ g.Liminf :=
cSup_le_cSup hg hf h

lemma Limsup_le_Limsup {f g : filter α}
  (hf : f.is_cobounded (≤) . is_bounded_default) (hg : g.is_bounded (≤) . is_bounded_default)
  (h : ∀ a, (∀ᶠ n in g, n ≤ a) → ∀ᶠ n in f, n ≤ a) : f.Limsup ≤ g.Limsup :=
cInf_le_cInf hf hg h

lemma Limsup_le_Limsup_of_le {f g : filter α} (h : f ≤ g)
  (hf : f.is_cobounded (≤) . is_bounded_default) (hg : g.is_bounded (≤) . is_bounded_default) :
  f.Limsup ≤ g.Limsup :=
Limsup_le_Limsup hf hg (assume a ha, h ha)

lemma Liminf_le_Liminf_of_le {f g : filter α} (h : g ≤ f)
  (hf : f.is_bounded (≥) . is_bounded_default) (hg : g.is_cobounded (≥) . is_bounded_default) :
  f.Liminf ≤ g.Liminf :=
Liminf_le_Liminf hf hg (assume a ha, h ha)

lemma limsup_le_limsup {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a ≤ v a)
  (hu : f.is_cobounded_under (≤) u . is_bounded_default)
  (hv : f.is_bounded_under (≤) v . is_bounded_default) :
  f.limsup u ≤ f.limsup v :=
Limsup_le_Limsup hu hv $ assume b (hb : ∀ᶠ a in f, v a ≤ b), show ∀ᶠ a in f, u a ≤ b,
  by filter_upwards [h, hb] assume a, le_trans

lemma liminf_le_liminf {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a ≤ v a)
  (hu : f.is_bounded_under (≥) u . is_bounded_default)
  (hv : f.is_cobounded_under (≥) v . is_bounded_default) :
  f.liminf u ≤ f.liminf v :=
Liminf_le_Liminf hu hv $ assume b (hb : ∀ᶠ a in f, b ≤ u a), show ∀ᶠ a in f, b ≤ v a,
  by filter_upwards [hb, h] assume a, le_trans

theorem Limsup_principal {s : set α} (h : bdd_above s) (hs : s.nonempty) :
  (principal s).Limsup = Sup s :=
by simp [Limsup]; exact cInf_upper_bounds_eq_cSup h hs

theorem Liminf_principal {s : set α} (h : bdd_below s) (hs : s.nonempty) :
  (principal s).Liminf = Inf s :=
by simp [Liminf]; exact cSup_lower_bounds_eq_cInf h hs

lemma limsup_congr {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a = v a) : limsup f u = limsup f v :=
begin
  rw limsup_eq,
  congr,
  ext b,
  exact eventually_congr (h.mono $ λ x hx, by simp [hx])
end

lemma liminf_congr {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a = v a) : liminf f u = liminf f v :=
begin
  rw liminf_eq,
  congr,
  ext b,
  exact eventually_congr (h.mono $ λ x hx, by simp [hx])
end

lemma limsup_const {α : Type*} [conditionally_complete_lattice β] {f : filter α} (hf : f ≠ ⊥)
  (b : β) : limsup f (λ x, b) = b :=
begin
  rw limsup_eq,
  apply le_antisymm,
  { refine cInf_le ⟨b, λ a ha, _⟩ (by simp [le_refl]),
    obtain ⟨n, hn⟩ : ∃ n, b ≤ a := eventually.exists ha hf,
    exact hn },
  { refine le_cInf ⟨b, by simp [le_refl]⟩ (λ a ha, _),
    obtain ⟨n, hn⟩ : ∃ n, b ≤ a := eventually.exists ha hf,
    exact hn }
end

lemma liminf_const {α : Type*} [conditionally_complete_lattice β] {f : filter α} (hf : f ≠ ⊥)
  (b : β) : liminf f (λ x, b) = b :=
begin
  rw liminf_eq,
  apply le_antisymm,
  { refine cSup_le ⟨b, by simp [le_refl]⟩ (λ a ha, _),
    obtain ⟨n, hn⟩ : ∃ n, a ≤ b := eventually.exists ha hf,
    exact hn },
  { refine le_cSup ⟨b, λ a ha, _⟩ (by simp [le_refl]),
    obtain ⟨n, hn⟩ : ∃ n, a ≤ b := eventually.exists ha hf,
    exact hn }
end


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

lemma liminf_le_limsup {f : filter β} (hf : f ≠ ⊥) {u : β → α}  : liminf f u ≤ limsup f u :=
  Liminf_le_Limsup (map_ne_bot hf) is_bounded_le_of_top is_bounded_ge_of_bot

theorem Limsup_eq_infi_Sup {f : filter α} : f.Limsup = ⨅ s ∈ f, Sup s :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, Inf_le $ show ∀ᶠ n in f, n ≤ Sup s,
    by filter_upwards [hs] assume a, le_Sup)
  (le_Inf $ assume a (ha : ∀ᶠ n in f, n ≤ a),
    infi_le_of_le _ $ infi_le_of_le ha $ Sup_le $ assume b, id)

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_infi_supr {f : filter β} {u : β → α} : f.limsup u = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
calc f.limsup u = ⨅ s ∈ (f.map u), Sup s : Limsup_eq_infi_Sup
  ... = ⨅ s ∈ f, ⨆ a ∈ s, u a :
    le_antisymm
      (le_infi $ assume s, le_infi $ assume hs,
        infi_le_of_le (u '' s) $ infi_le_of_le (image_mem_map hs) $ le_of_eq Sup_image)
      (le_infi $ assume s, le_infi $ assume (hs : u ⁻¹' s ∈ f),
        infi_le_of_le _ $ infi_le_of_le hs $ supr_le $ assume a, supr_le $ assume ha, le_Sup ha)

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma limsup_eq_infi_supr_of_nat {u : ℕ → α} : limsup at_top u = ⨅n:ℕ, ⨆i≥n, u i :=
calc
  limsup at_top u = ⨅ s ∈ at_top, ⨆n∈s, u n : limsup_eq_infi_supr
  ... = ⨅ n, ⨆i≥n, u i :
    le_antisymm
      (le_infi $ assume n, infi_le_of_le {i | i ≥ n} $ infi_le_of_le
        (mem_at_top _)
        (supr_le_supr $ assume i, supr_le_supr_const (by simp)))
      (le_infi $ assume s, le_infi $ assume hs,
        let ⟨n, hn⟩ := mem_at_top_sets.1 hs in
        infi_le_of_le n $ supr_le_supr $ assume i, supr_le_supr_const (hn i))

theorem Liminf_eq_supr_Inf {f : filter α} : f.Liminf = ⨆ s ∈ f, Inf s :=
le_antisymm
  (Sup_le $ assume a (ha : ∀ᶠ n in f, a ≤ n),
    le_supr_of_le _ $ le_supr_of_le ha $ le_Inf $ assume b, id)
  (supr_le $ assume s, supr_le $ assume hs, le_Sup $ show ∀ᶠ n in f, Inf s ≤ n,
    by filter_upwards [hs] assume a, Inf_le)

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_supr_infi {f : filter β} {u : β → α} : f.liminf u = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
calc f.liminf u = ⨆ s ∈ f.map u, Inf s : Liminf_eq_supr_Inf
  ... = ⨆ s ∈ f, ⨅a∈s, u a :
    le_antisymm
      (supr_le $ assume s, supr_le $ assume (hs : u ⁻¹' s ∈ f),
        le_supr_of_le _ $ le_supr_of_le hs $ le_infi $ assume a, le_infi $ assume ha, Inf_le ha)
      (supr_le $ assume s, supr_le $ assume hs,
        le_supr_of_le (u '' s) $ le_supr_of_le (image_mem_map hs) $ ge_of_eq Inf_image)

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma liminf_eq_supr_infi_of_nat {u : ℕ → α} : liminf at_top u = ⨆n:ℕ, ⨅i≥n, u i :=
calc
  liminf at_top u = ⨆ s ∈ at_top, ⨅ n ∈ s, u n : liminf_eq_supr_infi
  ... = ⨆n:ℕ, ⨅i≥n, u i :
    le_antisymm
      (supr_le $ assume s, supr_le $ assume hs,
        let ⟨n, hn⟩ := mem_at_top_sets.1 hs in
        le_supr_of_le n $ infi_le_infi $ assume i, infi_le_infi_const (hn _) )
      (supr_le $ assume n, le_supr_of_le {i | n ≤ i} $
        le_supr_of_le
          (mem_at_top _)
          (infi_le_infi $ assume i, infi_le_infi_const (by simp)))

end complete_lattice

section conditionally_complete_linear_order

lemma eventually_lt_of_lt_liminf {f : filter α} [conditionally_complete_linear_order β]
  {u : α → β} {b : β} (h : b < liminf f u) (hu : f.is_bounded_under (≥) u . is_bounded_default) :
  ∀ᶠ a in f, b < u a :=
begin
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β) (hc : c ∈ {c : β | ∀ᶠ (n : α) in f, c ≤ u n}), b < c :=
    exists_lt_of_lt_cSup hu h,
  exact hc.mono (λ x hx, lt_of_lt_of_le hbc hx)
end

lemma eventually_lt_of_limsup_lt {f : filter α} [conditionally_complete_linear_order β]
  {u : α → β} {b : β} (h : limsup f u < b) (hu : f.is_bounded_under (≤) u . is_bounded_default) :
  ∀ᶠ a in f, u a < b :=
begin
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β) (hc : c ∈ {c : β | ∀ᶠ (n : α) in f, u n ≤ c}), c < b :=
    exists_lt_of_cInf_lt hu h,
  exact hc.mono (λ x hx, lt_of_le_of_lt hx hbc)
end

end conditionally_complete_linear_order

end filter
