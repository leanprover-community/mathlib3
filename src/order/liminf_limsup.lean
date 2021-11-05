/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
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
open_locale filter

variables {α β ι : Type*}
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
  (assume ⟨s, hs, b, hb⟩, ⟨b, mem_of_superset hs hb⟩)

/-- A bounded function `u` is in particular eventually bounded. -/
lemma is_bounded_under_of {f : filter β} {u : β → α} :
  (∃b, ∀x, r (u x) b) → f.is_bounded_under r u
| ⟨b, hb⟩ := ⟨b, show ∀ᶠ x in f, r (u x) b, from eventually_of_forall hb⟩

lemma is_bounded_bot : is_bounded r ⊥ ↔ nonempty α :=
by simp [is_bounded, exists_true_iff_nonempty]

lemma is_bounded_top : is_bounded r ⊤ ↔ (∃t, ∀x, r x t) :=
by simp [is_bounded, eq_univ_iff_forall]

lemma is_bounded_principal (s : set α) : is_bounded r (𝓟 s) ↔ (∃t, ∀x∈s, r x t) :=
by simp [is_bounded, subset_def]

lemma is_bounded_sup [is_trans α r] (hr : ∀b₁ b₂, ∃b, r b₁ b ∧ r b₂ b) :
  is_bounded r f → is_bounded r g → is_bounded r (f ⊔ g)
| ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ := let ⟨b, rb₁b, rb₂b⟩ := hr b₁ b₂ in
  ⟨b, eventually_sup.mpr ⟨h₁.mono (λ x h, trans h rb₁b), h₂.mono (λ x h, trans h rb₂b)⟩⟩

lemma is_bounded.mono (h : f ≤ g) : is_bounded r g → is_bounded r f
| ⟨b, hb⟩ := ⟨b, h hb⟩

lemma is_bounded_under.mono {f g : filter β} {u : β → α} (h : f ≤ g) :
  g.is_bounded_under r u → f.is_bounded_under r u :=
λ hg, hg.mono (map_mono h)

lemma is_bounded.is_bounded_under {q : β → β → Prop} {u : α → β}
  (hf : ∀a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) : f.is_bounded r → f.is_bounded_under q u
| ⟨b, h⟩ := ⟨u b, show ∀ᶠ x in f, q (u x) (u b), from h.mono (λ x, hf x b)⟩

lemma not_is_bounded_under_of_tendsto_at_top [nonempty α] [semilattice_sup α]
  [preorder β] [no_top_order β] {f : α → β} (hf : tendsto f at_top at_top) :
  ¬ is_bounded_under (≤) at_top f :=
begin
  rintro ⟨b, hb⟩,
  rw eventually_map at hb,
  obtain ⟨b', h⟩ := no_top b,
  have hb' := (tendsto_at_top.mp hf) b',
  have : {x : α | f x ≤ b} ∩ {x : α | b' ≤ f x} = ∅ :=
    eq_empty_of_subset_empty (λ x hx, (not_le_of_lt h) (le_trans hx.2 hx.1)),
  exact at_top.empty_not_mem (this ▸ filter.inter_mem hb hb' : ∅ ∈ (at_top : filter α)),
end

lemma not_is_bounded_under_of_tendsto_at_bot [nonempty α] [semilattice_sup α]
  [preorder β] [no_bot_order β] {f : α → β} (hf : tendsto f at_top at_bot) :
  ¬ is_bounded_under (≥) at_top f :=
begin
  rintro ⟨b, hb⟩,
  rw eventually_map at hb,
  obtain ⟨b', h⟩ := no_bot b,
  have hb' := (tendsto_at_bot.mp hf) b',
  have : {x : α | b ≤ f x} ∩ {x : α | f x ≤ b'} = ∅ :=
    eq_empty_of_subset_empty (λ x hx, (not_le_of_lt h) (le_trans hx.1 hx.2)),
  exact at_top.empty_not_mem (this ▸ filter.inter_mem hb hb' : ∅ ∈ (at_top : filter α)),
end

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
lemma is_bounded.is_cobounded_flip [is_trans α r] [ne_bot f] :
  f.is_bounded r → f.is_cobounded (flip r)
| ⟨a, ha⟩ := ⟨a, assume b hb,
  let ⟨x, rxa, rbx⟩ := (ha.and hb).exists in
  show r b a, from trans rbx rxa⟩

lemma is_bounded.is_cobounded_ge [preorder α] [ne_bot f] (h : f.is_bounded (≤)) :
  f.is_cobounded (≥) :=
h.is_cobounded_flip

lemma is_bounded.is_cobounded_le [preorder α] [ne_bot f] (h : f.is_bounded (≥)) :
  f.is_cobounded (≤) :=
h.is_cobounded_flip

lemma is_cobounded_bot : is_cobounded r ⊥ ↔ (∃b, ∀x, r b x) :=
by simp [is_cobounded]

lemma is_cobounded_top : is_cobounded r ⊤ ↔ nonempty α :=
by simp [is_cobounded, eq_univ_iff_forall, exists_true_iff_nonempty] {contextual := tt}

lemma is_cobounded_principal (s : set α) :
  (𝓟 s).is_cobounded r ↔ (∃b, ∀a, (∀x∈s, r x a) → r b a) :=
by simp [is_cobounded, subset_def]

lemma is_cobounded.mono (h : f ≤ g) : f.is_cobounded r → g.is_cobounded r
| ⟨b, hb⟩ := ⟨b, assume a ha, hb a (h ha)⟩

end relation

lemma is_cobounded_le_of_bot [order_bot α] {f : filter α} : f.is_cobounded (≤) :=
⟨⊥, assume a h, bot_le⟩

lemma is_cobounded_ge_of_top [order_top α] {f : filter α} : f.is_cobounded (≥) :=
⟨⊤, assume a h, le_top⟩

lemma is_bounded_le_of_top [order_top α] {f : filter α} : f.is_bounded (≤) :=
⟨⊤, eventually_of_forall $ λ _, le_top⟩

lemma is_bounded_ge_of_bot [order_bot α] {f : filter α} : f.is_bounded (≥) :=
⟨⊥, eventually_of_forall $ λ _, bot_le⟩

lemma is_bounded_under_sup [semilattice_sup α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≤) u → f.is_bounded_under (≤) v → f.is_bounded_under (≤) (λa, u a ⊔ v a)
| ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩ ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ :=
  ⟨bu ⊔ bv, show ∀ᶠ x in f, u x ⊔ v x ≤ bu ⊔ bv,
    by filter_upwards [hu, hv] assume x, sup_le_sup⟩

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

theorem Liminf_le_Limsup {f : filter α} [ne_bot f]
  (h₁ : f.is_bounded (≤) . is_bounded_default) (h₂ : f.is_bounded (≥) . is_bounded_default) :
  f.Liminf ≤ f.Limsup :=
Liminf_le_of_le h₂ $ assume a₀ ha₀, le_Limsup_of_le h₁ $ assume a₁ ha₁,
  show a₀ ≤ a₁, from let ⟨b, hb₀, hb₁⟩ := (ha₀.and ha₁).exists in le_trans hb₀ hb₁

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
  (h : u ≤ᶠ[f] v)
  (hu : f.is_cobounded_under (≤) u . is_bounded_default)
  (hv : f.is_bounded_under (≤) v . is_bounded_default) :
  f.limsup u ≤ f.limsup v :=
Limsup_le_Limsup hu hv $ assume b, h.trans

lemma liminf_le_liminf {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a ≤ v a)
  (hu : f.is_bounded_under (≥) u . is_bounded_default)
  (hv : f.is_cobounded_under (≥) v . is_bounded_default) :
  f.liminf u ≤ f.liminf v :=
@limsup_le_limsup (order_dual β) α _ _ _ _ h hv hu

lemma limsup_le_limsup_of_le {α β} [conditionally_complete_lattice β] {f g : filter α} (h : f ≤ g)
  {u : α → β} (hf : f.is_cobounded_under (≤) u . is_bounded_default)
  (hg : g.is_bounded_under (≤) u . is_bounded_default) :
  f.limsup u ≤ g.limsup u :=
Limsup_le_Limsup_of_le (map_mono h) hf hg

lemma liminf_le_liminf_of_le {α β} [conditionally_complete_lattice β] {f g : filter α} (h : g ≤ f)
  {u : α → β} (hf : f.is_bounded_under (≥) u . is_bounded_default)
  (hg : g.is_cobounded_under (≥) u . is_bounded_default) :
  f.liminf u ≤ g.liminf u :=
Liminf_le_Liminf_of_le (map_mono h) hf hg

theorem Limsup_principal {s : set α} (h : bdd_above s) (hs : s.nonempty) :
  (𝓟 s).Limsup = Sup s :=
by simp [Limsup]; exact cInf_upper_bounds_eq_cSup h hs

theorem Liminf_principal {s : set α} (h : bdd_below s) (hs : s.nonempty) :
  (𝓟 s).Liminf = Inf s :=
@Limsup_principal (order_dual α) _ s h hs

lemma limsup_congr {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a = v a) : limsup f u = limsup f v :=
begin
  rw limsup_eq,
  congr' with b,
  exact eventually_congr (h.mono $ λ x hx, by simp [hx])
end

lemma liminf_congr {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a = v a) : liminf f u = liminf f v :=
@limsup_congr (order_dual β) _ _ _ _ _ h

lemma limsup_const {α : Type*} [conditionally_complete_lattice β] {f : filter α} [ne_bot f]
  (b : β) : limsup f (λ x, b) = b :=
by simpa only [limsup_eq, eventually_const] using cInf_Ici

lemma liminf_const {α : Type*} [conditionally_complete_lattice β] {f : filter α} [ne_bot f]
  (b : β) : liminf f (λ x, b) = b :=
@limsup_const (order_dual β) α _ f _ b

lemma liminf_le_limsup {f : filter β} [ne_bot f] {u : β → α}
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  liminf f u ≤ limsup f u :=
Liminf_le_Limsup h h'

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

/-- Same as limsup_const applied to `⊥` but without the `ne_bot f` assumption -/
lemma limsup_const_bot {f : filter β} : limsup f (λ x : β, (⊥ : α)) = (⊥ : α) :=
begin
  rw [limsup_eq, eq_bot_iff],
  exact Inf_le (eventually_of_forall (λ x, le_refl _)),
end

/-- Same as limsup_const applied to `⊤` but without the `ne_bot f` assumption -/
lemma liminf_const_top {f : filter β} : liminf f (λ x : β, (⊤ : α)) = (⊤ : α) :=
@limsup_const_bot (order_dual α) β _ _

theorem has_basis.Limsup_eq_infi_Sup {ι} {p : ι → Prop} {s} {f : filter α} (h : f.has_basis p s) :
  f.Limsup = ⨅ i (hi : p i), Sup (s i) :=
le_antisymm
  (le_binfi $ λ i hi, Inf_le $ h.eventually_iff.2 ⟨i, hi, λ x, le_Sup⟩)
  (le_Inf $ assume a ha, let ⟨i, hi, ha⟩ := h.eventually_iff.1 ha in
    infi_le_of_le _ $ infi_le_of_le hi $ Sup_le ha)

theorem has_basis.Liminf_eq_supr_Inf {p : ι → Prop} {s : ι → set α} {f : filter α}
  (h : f.has_basis p s) : f.Liminf = ⨆ i (hi : p i), Inf (s i) :=
@has_basis.Limsup_eq_infi_Sup (order_dual α) _ _ _ _ _ h

theorem Limsup_eq_infi_Sup {f : filter α} : f.Limsup = ⨅ s ∈ f, Sup s :=
f.basis_sets.Limsup_eq_infi_Sup

theorem Liminf_eq_supr_Inf {f : filter α} : f.Liminf = ⨆ s ∈ f, Inf s :=
@Limsup_eq_infi_Sup (order_dual α) _ _

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_infi_supr {f : filter β} {u : β → α} : f.limsup u = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
(f.basis_sets.map u).Limsup_eq_infi_Sup.trans $
  by simp only [Sup_image, id]

lemma limsup_eq_infi_supr_of_nat {u : ℕ → α} : limsup at_top u = ⨅ n : ℕ, ⨆ i ≥ n, u i :=
(at_top_basis.map u).Limsup_eq_infi_Sup.trans $
  by simp only [Sup_image, infi_const]; refl

lemma limsup_eq_infi_supr_of_nat' {u : ℕ → α} : limsup at_top u = ⨅ n : ℕ, ⨆ i : ℕ, u (i + n) :=
by simp only [limsup_eq_infi_supr_of_nat, supr_ge_eq_supr_nat_add]

theorem has_basis.limsup_eq_infi_supr {p : ι → Prop} {s : ι → set β} {f : filter β} {u : β → α}
  (h : f.has_basis p s) : f.limsup u = ⨅ i (hi : p i), ⨆ a ∈ s i, u a :=
(h.map u).Limsup_eq_infi_Sup.trans $ by simp only [Sup_image, id]

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_supr_infi {f : filter β} {u : β → α} : f.liminf u = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
@limsup_eq_infi_supr (order_dual α) β _ _ _

lemma liminf_eq_supr_infi_of_nat {u : ℕ → α} : liminf at_top u = ⨆ n : ℕ, ⨅ i ≥ n, u i :=
@limsup_eq_infi_supr_of_nat (order_dual α) _ u

lemma liminf_eq_supr_infi_of_nat' {u : ℕ → α} : liminf at_top u = ⨆ n : ℕ, ⨅ i : ℕ, u (i + n) :=
@limsup_eq_infi_supr_of_nat' (order_dual α) _ _

theorem has_basis.liminf_eq_supr_infi {p : ι → Prop} {s : ι → set β} {f : filter β} {u : β → α}
  (h : f.has_basis p s) : f.liminf u = ⨆ i (hi : p i), ⨅ a ∈ s i, u a :=
@has_basis.limsup_eq_infi_supr (order_dual α) _ _ _ _ _ _ _ h

@[simp] lemma liminf_nat_add (f : ℕ → α) (k : ℕ) :
  at_top.liminf (λ i, f (i + k)) = at_top.liminf f :=
by { simp_rw liminf_eq_supr_infi_of_nat, exact supr_infi_ge_nat_add f k }

@[simp] lemma limsup_nat_add (f : ℕ → α) (k : ℕ) :
  at_top.limsup (λ i, f (i + k)) = at_top.limsup f :=
@liminf_nat_add (order_dual α) _ f k

lemma liminf_le_of_frequently_le' {α β} [complete_lattice β]
  {f : filter α} {u : α → β} {x : β} (h : ∃ᶠ a in f, u a ≤ x) :
  f.liminf u ≤ x :=
begin
  rw liminf_eq,
  refine Sup_le (λ b hb, _),
  have hbx : ∃ᶠ a in f, b ≤ x,
  { revert h,
    rw [←not_imp_not, not_frequently, not_frequently],
    exact λ h, hb.mp (h.mono (λ a hbx hba hax, hbx (hba.trans hax))), },
  exact hbx.exists.some_spec,
end

lemma le_limsup_of_frequently_le' {α β} [complete_lattice β]
  {f : filter α} {u : α → β} {x : β} (h : ∃ᶠ a in f, x ≤ u a) :
  x ≤ f.limsup u :=
@liminf_le_of_frequently_le' _ (order_dual β) _ _ _ _ h

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
@eventually_lt_of_lt_liminf _ (order_dual β) _ _ _ _ h hu

lemma le_limsup_of_frequently_le {α β} [conditionally_complete_linear_order β] {f : filter α}
  {u : α → β}  {b : β} (hu_le : ∃ᶠ x in f, b ≤ u x)
  (hu : f.is_bounded_under (≤) u . is_bounded_default) :
  b ≤ f.limsup u :=
begin
  revert hu_le,
  rw [←not_imp_not, not_frequently],
  simp_rw ←lt_iff_not_ge,
  exact λ h, eventually_lt_of_limsup_lt h hu,
end

lemma liminf_le_of_frequently_le  {α β} [conditionally_complete_linear_order β] {f : filter α}
  {u : α → β}  {b : β} (hu_le : ∃ᶠ x in f, u x ≤ b)
  (hu : f.is_bounded_under (≥) u . is_bounded_default) :
  f.liminf u ≤ b :=
@le_limsup_of_frequently_le _ (order_dual β) _ f u b hu_le hu

lemma frequently_lt_of_lt_limsup {α β} [conditionally_complete_linear_order β] {f : filter α}
  {u : α → β}  {b : β}
  (hu : f.is_cobounded_under (≤) u . is_bounded_default) (h : b < f.limsup u) :
  ∃ᶠ x in f, b < u x :=
begin
  contrapose! h,
  apply Limsup_le_of_le hu,
  simpa using h,
end

lemma frequently_lt_of_liminf_lt {α β} [conditionally_complete_linear_order β] {f : filter α}
  {u : α → β}  {b : β}
  (hu : f.is_cobounded_under (≥) u . is_bounded_default) (h : f.liminf u < b) :
  ∃ᶠ x in f, u x < b :=
@frequently_lt_of_lt_limsup _ (order_dual β) _ f u b hu h

end conditionally_complete_linear_order

end filter

section order
open filter

lemma galois_connection.l_limsup_le {α β γ} [conditionally_complete_lattice β]
  [conditionally_complete_lattice γ] {f : filter α} {v : α → β}
  {l : β → γ} {u : γ → β} (gc : galois_connection l u)
  (hlv : f.is_bounded_under (≤) (λ x, l (v x)) . is_bounded_default)
  (hv_co : f.is_cobounded_under (≤) v . is_bounded_default) :
  l (f.limsup v) ≤ f.limsup (λ x, l (v x)) :=
begin
  refine le_Limsup_of_le hlv (λ c hc, _),
  rw filter.eventually_map at hc,
  simp_rw (gc _ _) at hc ⊢,
  exact Limsup_le_of_le hv_co hc,
end

lemma order_iso.limsup_apply {γ} [conditionally_complete_lattice β]
  [conditionally_complete_lattice γ] {f : filter α} {u : α → β} (g : β ≃o γ)
  (hu : f.is_bounded_under (≤) u . is_bounded_default)
  (hu_co : f.is_cobounded_under (≤) u . is_bounded_default)
  (hgu : f.is_bounded_under (≤) (λ x, g (u x)) . is_bounded_default)
  (hgu_co : f.is_cobounded_under (≤) (λ x, g (u x)) . is_bounded_default) :
  g (f.limsup u) = f.limsup (λ x, g (u x)) :=
begin
  refine le_antisymm (g.to_galois_connection.l_limsup_le hgu hu_co) _,
  rw [←(g.symm.symm_apply_apply (f.limsup (λ (x : α), g (u x)))), g.symm_symm],
  refine g.monotone _,
  have hf : u = λ i, g.symm (g (u i)), from funext (λ i, (g.symm_apply_apply (u i)).symm),
  nth_rewrite 0 hf,
  refine g.symm.to_galois_connection.l_limsup_le _ hgu_co,
  simp_rw g.symm_apply_apply,
  exact hu,
end

lemma order_iso.liminf_apply {γ} [conditionally_complete_lattice β]
  [conditionally_complete_lattice γ] {f : filter α} {u : α → β} (g : β ≃o γ)
  (hu : f.is_bounded_under (≥) u . is_bounded_default)
  (hu_co : f.is_cobounded_under (≥) u . is_bounded_default)
  (hgu : f.is_bounded_under (≥) (λ x, g (u x)) . is_bounded_default)
  (hgu_co : f.is_cobounded_under (≥) (λ x, g (u x)) . is_bounded_default) :
  g (f.liminf u) = f.liminf (λ x, g (u x)) :=
@order_iso.limsup_apply α (order_dual β) (order_dual γ) _ _ f u g.dual hu hu_co hgu hgu_co

end order
