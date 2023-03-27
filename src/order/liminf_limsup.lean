/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
import order.filter.cofinite
import order.hom.complete_lattice

/-!
# liminfs and limsups of functions and filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Defines the Liminf/Limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `Limsup f` (`Liminf f`) where `f` is a filter taking values in a conditionally complete
lattice. `Limsup f` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`Liminf f`). To work with the Limsup along a function `u` use `Limsup (map u f)`.

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

variables {α β γ ι : Type*}
namespace filter

section relation

/-- `f.is_bounded (≺)`: the filter `f` is eventually bounded w.r.t. the relation `≺`, i.e.
eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `≤` or `≥`. -/
def is_bounded (r : α → α → Prop) (f : filter α) := ∃ b, ∀ᶠ x in f, r x b

/-- `f.is_bounded_under (≺) u`: the image of the filter `f` under `u` is eventually bounded w.r.t.
the relation `≺`, i.e. eventually, it is bounded by some uniform bound. -/
def is_bounded_under (r : α → α → Prop) (f : filter β) (u : β → α) := (map u f).is_bounded r

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

lemma is_bounded_under.mono_le [preorder β] {l : filter α} {u v : α → β}
  (hu : is_bounded_under (≤) l u) (hv : v ≤ᶠ[l] u) : is_bounded_under (≤) l v :=
hu.imp $ λ b hb, (eventually_map.1 hb).mp $ hv.mono $ λ x, le_trans

lemma is_bounded_under.mono_ge [preorder β] {l : filter α} {u v : α → β}
  (hu : is_bounded_under (≥) l u) (hv : u ≤ᶠ[l] v) : is_bounded_under (≥) l v :=
@is_bounded_under.mono_le α βᵒᵈ _ _ _ _ hu hv

lemma is_bounded_under_const [is_refl α r] {l : filter β} {a : α} : is_bounded_under r l (λ _, a) :=
⟨a, eventually_map.2 $ eventually_of_forall $ λ _, refl _⟩

lemma is_bounded.is_bounded_under {q : β → β → Prop} {u : α → β}
  (hf : ∀a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) : f.is_bounded r → f.is_bounded_under q u
| ⟨b, h⟩ := ⟨u b, show ∀ᶠ x in f, q (u x) (u b), from h.mono (λ x, hf x b)⟩

lemma not_is_bounded_under_of_tendsto_at_top [preorder β] [no_max_order β] {f : α → β}
  {l : filter α} [l.ne_bot] (hf : tendsto f l at_top) :
  ¬ is_bounded_under (≤) l f :=
begin
  rintro ⟨b, hb⟩,
  rw eventually_map at hb,
  obtain ⟨b', h⟩ := exists_gt b,
  have hb' := (tendsto_at_top.mp hf) b',
  have : {x : α | f x ≤ b} ∩ {x : α | b' ≤ f x} = ∅ :=
    eq_empty_of_subset_empty (λ x hx, (not_le_of_lt h) (le_trans hx.2 hx.1)),
  exact (nonempty_of_mem (hb.and hb')).ne_empty this
end

lemma not_is_bounded_under_of_tendsto_at_bot [preorder β] [no_min_order β] {f : α → β}
  {l : filter α} [l.ne_bot](hf : tendsto f l at_bot) :
  ¬ is_bounded_under (≥) l f :=
@not_is_bounded_under_of_tendsto_at_top α βᵒᵈ _ _ _ _ _ hf

lemma is_bounded_under.bdd_above_range_of_cofinite [semilattice_sup β] {f : α → β}
  (hf : is_bounded_under (≤) cofinite f) : bdd_above (range f) :=
begin
  rcases hf with ⟨b, hb⟩,
  haveI : nonempty β := ⟨b⟩,
  rw [← image_univ, ← union_compl_self {x | f x ≤ b}, image_union, bdd_above_union],
  exact ⟨⟨b, ball_image_iff.2 $ λ x, id⟩, (hb.image f).bdd_above⟩
end

lemma is_bounded_under.bdd_below_range_of_cofinite [semilattice_inf β] {f : α → β}
  (hf : is_bounded_under (≥) cofinite f) : bdd_below (range f) :=
@is_bounded_under.bdd_above_range_of_cofinite α βᵒᵈ _ _ hf

lemma is_bounded_under.bdd_above_range [semilattice_sup β] {f : ℕ → β}
  (hf : is_bounded_under (≤) at_top f) : bdd_above (range f) :=
by { rw ← nat.cofinite_eq_at_top at hf, exact hf.bdd_above_range_of_cofinite }

lemma is_bounded_under.bdd_below_range [semilattice_inf β] {f : ℕ → β}
  (hf : is_bounded_under (≥) at_top f) : bdd_below (range f) :=
@is_bounded_under.bdd_above_range βᵒᵈ _ _ hf

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
def is_cobounded_under (r : α → α → Prop) (f : filter β) (u : β → α) := (map u f).is_cobounded r

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

lemma is_cobounded_le_of_bot [preorder α] [order_bot α] {f : filter α} : f.is_cobounded (≤) :=
⟨⊥, assume a h, bot_le⟩

lemma is_cobounded_ge_of_top [preorder α] [order_top α] {f : filter α} : f.is_cobounded (≥) :=
⟨⊤, assume a h, le_top⟩

lemma is_bounded_le_of_top [preorder α] [order_top α] {f : filter α} : f.is_bounded (≤) :=
⟨⊤, eventually_of_forall $ λ _, le_top⟩

lemma is_bounded_ge_of_bot [preorder α] [order_bot α] {f : filter α} : f.is_bounded (≥) :=
⟨⊥, eventually_of_forall $ λ _, bot_le⟩

@[simp] lemma _root_.order_iso.is_bounded_under_le_comp [preorder α] [preorder β] (e : α ≃o β)
  {l : filter γ} {u : γ → α} :
  is_bounded_under (≤) l (λ x, e (u x)) ↔ is_bounded_under (≤) l u :=
e.surjective.exists.trans $ exists_congr $ λ a, by simp only [eventually_map, e.le_iff_le]

@[simp] lemma _root_.order_iso.is_bounded_under_ge_comp [preorder α] [preorder β] (e : α ≃o β)
  {l : filter γ} {u : γ → α} :
  is_bounded_under (≥) l (λ x, e (u x)) ↔ is_bounded_under (≥) l u :=
e.dual.is_bounded_under_le_comp

@[simp, to_additive]
lemma is_bounded_under_le_inv [ordered_comm_group α] {l : filter β} {u : β → α} :
  is_bounded_under (≤) l (λ x, (u x)⁻¹) ↔ is_bounded_under (≥) l u :=
(order_iso.inv α).is_bounded_under_ge_comp

@[simp, to_additive]
lemma is_bounded_under_ge_inv [ordered_comm_group α] {l : filter β} {u : β → α} :
  is_bounded_under (≥) l (λ x, (u x)⁻¹) ↔ is_bounded_under (≤) l u :=
(order_iso.inv α).is_bounded_under_le_comp

lemma is_bounded_under.sup [semilattice_sup α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≤) u → f.is_bounded_under (≤) v → f.is_bounded_under (≤) (λa, u a ⊔ v a)
| ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩ ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ :=
  ⟨bu ⊔ bv, show ∀ᶠ x in f, u x ⊔ v x ≤ bu ⊔ bv,
    by filter_upwards [hu, hv] with _ using sup_le_sup⟩

@[simp] lemma is_bounded_under_le_sup [semilattice_sup α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≤) (λ a, u a ⊔ v a) ↔ f.is_bounded_under (≤) u ∧ f.is_bounded_under (≤) v :=
⟨λ h, ⟨h.mono_le $ eventually_of_forall $ λ _, le_sup_left,
  h.mono_le $ eventually_of_forall $ λ _, le_sup_right⟩, λ h, h.1.sup h.2⟩

lemma is_bounded_under.inf [semilattice_inf α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≥) u → f.is_bounded_under (≥) v → f.is_bounded_under (≥) (λa, u a ⊓ v a) :=
@is_bounded_under.sup αᵒᵈ β _ _ _ _

@[simp] lemma is_bounded_under_ge_inf [semilattice_inf α] {f : filter β} {u v : β → α} :
  f.is_bounded_under (≥) (λ a, u a ⊓ v a) ↔ f.is_bounded_under (≥) u ∧ f.is_bounded_under (≥) v :=
@is_bounded_under_le_sup αᵒᵈ _ _ _ _ _

lemma is_bounded_under_le_abs [linear_ordered_add_comm_group α] {f : filter β} {u : β → α} :
  f.is_bounded_under (≤) (λ a, |u a|) ↔ f.is_bounded_under (≤) u ∧ f.is_bounded_under (≥) u :=
is_bounded_under_le_sup.trans $ and_congr iff.rfl is_bounded_under_le_neg

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
def limsup (u : β → α) (f : filter β) : α := Limsup (map u f)

/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that,
eventually for `f`, holds `u x ≥ a`. -/
def liminf (u : β → α) (f : filter β) : α := Liminf (map u f)

/-- The `blimsup` of a function `u` along a filter `f`, bounded by a predicate `p`, is the infimum
of the `a` such that, eventually for `f`, `u x ≤ a` whenever `p x` holds. -/
def blimsup (u : β → α) (f : filter β) (p : β → Prop) :=
Inf { a | ∀ᶠ x in f, p x → u x ≤ a }

/-- The `bliminf` of a function `u` along a filter `f`, bounded by a predicate `p`, is the supremum
of the `a` such that, eventually for `f`, `a ≤ u x` whenever `p x` holds. -/
def bliminf (u : β → α) (f : filter β) (p : β → Prop) :=
Sup { a | ∀ᶠ x in f, p x → a ≤ u x }

section

variables {f : filter β} {u : β → α} {p : β → Prop}

theorem limsup_eq : limsup u f = Inf { a | ∀ᶠ n in f, u n ≤ a } := rfl

theorem liminf_eq : liminf u f = Sup { a | ∀ᶠ n in f, a ≤ u n } := rfl

theorem blimsup_eq : blimsup u f p = Inf { a | ∀ᶠ x in f, p x → u x ≤ a } := rfl

theorem bliminf_eq : bliminf u f p = Sup { a | ∀ᶠ x in f, p x → a ≤ u x } := rfl

end

@[simp] lemma blimsup_true (f : filter β) (u : β → α) :
  blimsup u f (λ x, true) = limsup u f :=
by simp [blimsup_eq, limsup_eq]

@[simp] lemma bliminf_true (f : filter β) (u : β → α) :
  bliminf u f (λ x, true) = liminf u f :=
by simp [bliminf_eq, liminf_eq]

lemma blimsup_eq_limsup_subtype {f : filter β} {u : β → α} {p : β → Prop} :
  blimsup u f p = limsup (u ∘ (coe : {x | p x} → β)) (comap coe f) :=
begin
  simp only [blimsup_eq, limsup_eq, function.comp_app, eventually_comap, set_coe.forall,
    subtype.coe_mk, mem_set_of_eq],
  congr,
  ext a,
  exact eventually_congr (eventually_of_forall
    (λ x, ⟨λ hx y hy hxy, hxy.symm ▸ (hx (hxy ▸ hy)), λ hx hx', hx x hx' rfl⟩)),
end

lemma bliminf_eq_liminf_subtype {f : filter β} {u : β → α} {p : β → Prop} :
  bliminf u f p = liminf (u ∘ (coe : {x | p x} → β)) (comap coe f) :=
@blimsup_eq_limsup_subtype αᵒᵈ β _ f u p

theorem Limsup_le_of_le {f : filter α} {a}
  (hf : f.is_cobounded (≤) . is_bounded_default) (h : ∀ᶠ n in f, n ≤ a) : Limsup f ≤ a :=
cInf_le hf h

theorem le_Liminf_of_le {f : filter α} {a}
  (hf : f.is_cobounded (≥) . is_bounded_default) (h : ∀ᶠ n in f, a ≤ n) : a ≤ Liminf f :=
le_cSup hf h

theorem limsup_le_of_le {f : filter β} {u : β → α} {a}
  (hf : f.is_cobounded_under (≤) u . is_bounded_default) (h : ∀ᶠ n in f, u n ≤ a) :
  limsup u f ≤ a :=
cInf_le hf h

theorem le_liminf_of_le {f : filter β} {u : β → α} {a}
  (hf : f.is_cobounded_under (≥) u . is_bounded_default) (h : ∀ᶠ n in f, a ≤ u n) :
    a ≤ liminf u f :=
le_cSup hf h

theorem le_Limsup_of_le {f : filter α} {a}
  (hf : f.is_bounded (≤) . is_bounded_default) (h : ∀ b, (∀ᶠ n in f, n ≤ b) → a ≤ b) :
  a ≤ Limsup f :=
le_cInf hf h

theorem Liminf_le_of_le {f : filter α} {a}
  (hf : f.is_bounded (≥) . is_bounded_default) (h : ∀ b, (∀ᶠ n in f, b ≤ n) → b ≤ a) :
  Liminf f ≤ a :=
cSup_le hf h

theorem le_limsup_of_le {f : filter β} {u : β → α} {a}
  (hf : f.is_bounded_under (≤) u . is_bounded_default) (h : ∀ b, (∀ᶠ n in f, u n ≤ b) → a ≤ b) :
  a ≤ limsup u f :=
le_cInf hf h

theorem liminf_le_of_le {f : filter β} {u : β → α} {a}
  (hf : f.is_bounded_under (≥) u . is_bounded_default) (h : ∀ b, (∀ᶠ n in f, b ≤ u n) → b ≤ a) :
  liminf u f ≤ a :=
cSup_le hf h

theorem Liminf_le_Limsup {f : filter α} [ne_bot f]
  (h₁ : f.is_bounded (≤) . is_bounded_default) (h₂ : f.is_bounded (≥) . is_bounded_default) :
  Liminf f ≤ Limsup f :=
Liminf_le_of_le h₂ $ assume a₀ ha₀, le_Limsup_of_le h₁ $ assume a₁ ha₁,
  show a₀ ≤ a₁, from let ⟨b, hb₀, hb₁⟩ := (ha₀.and ha₁).exists in le_trans hb₀ hb₁

lemma liminf_le_limsup {f : filter β} [ne_bot f] {u : β → α}
  (h : f.is_bounded_under (≤) u . is_bounded_default)
  (h' : f.is_bounded_under (≥) u . is_bounded_default) :
  liminf u f ≤ limsup u f :=
Liminf_le_Limsup h h'

lemma Limsup_le_Limsup {f g : filter α}
  (hf : f.is_cobounded (≤) . is_bounded_default) (hg : g.is_bounded (≤) . is_bounded_default)
  (h : ∀ a, (∀ᶠ n in g, n ≤ a) → ∀ᶠ n in f, n ≤ a) : Limsup f ≤ Limsup g :=
cInf_le_cInf hf hg h

lemma Liminf_le_Liminf {f g : filter α}
  (hf : f.is_bounded (≥) . is_bounded_default) (hg : g.is_cobounded (≥) . is_bounded_default)
  (h : ∀ a, (∀ᶠ n in f, a ≤ n) → ∀ᶠ n in g, a ≤ n) : Liminf f ≤ Liminf g :=
cSup_le_cSup hg hf h

lemma limsup_le_limsup {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : u ≤ᶠ[f] v)
  (hu : f.is_cobounded_under (≤) u . is_bounded_default)
  (hv : f.is_bounded_under (≤) v . is_bounded_default) :
  limsup u f ≤ limsup v f :=
Limsup_le_Limsup hu hv $ assume b, h.trans

lemma liminf_le_liminf {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a ≤ v a)
  (hu : f.is_bounded_under (≥) u . is_bounded_default)
  (hv : f.is_cobounded_under (≥) v . is_bounded_default) :
  liminf u f ≤ liminf v f :=
@limsup_le_limsup βᵒᵈ α _ _ _ _ h hv hu

lemma Limsup_le_Limsup_of_le {f g : filter α} (h : f ≤ g)
  (hf : f.is_cobounded (≤) . is_bounded_default) (hg : g.is_bounded (≤) . is_bounded_default) :
  Limsup f ≤ Limsup g :=
Limsup_le_Limsup hf hg (assume a ha, h ha)

lemma Liminf_le_Liminf_of_le {f g : filter α} (h : g ≤ f)
  (hf : f.is_bounded (≥) . is_bounded_default) (hg : g.is_cobounded (≥) . is_bounded_default) :
  Liminf f ≤ Liminf g :=
Liminf_le_Liminf hf hg (assume a ha, h ha)

lemma limsup_le_limsup_of_le {α β} [conditionally_complete_lattice β] {f g : filter α} (h : f ≤ g)
  {u : α → β} (hf : f.is_cobounded_under (≤) u . is_bounded_default)
  (hg : g.is_bounded_under (≤) u . is_bounded_default) :
  limsup u f ≤ limsup u g :=
Limsup_le_Limsup_of_le (map_mono h) hf hg

lemma liminf_le_liminf_of_le {α β} [conditionally_complete_lattice β] {f g : filter α} (h : g ≤ f)
  {u : α → β} (hf : f.is_bounded_under (≥) u . is_bounded_default)
  (hg : g.is_cobounded_under (≥) u . is_bounded_default) :
  liminf u f ≤ liminf u g :=
Liminf_le_Liminf_of_le (map_mono h) hf hg

theorem Limsup_principal {s : set α} (h : bdd_above s) (hs : s.nonempty) :
  Limsup (𝓟 s) = Sup s :=
by simp [Limsup]; exact cInf_upper_bounds_eq_cSup h hs

theorem Liminf_principal {s : set α} (h : bdd_below s) (hs : s.nonempty) :
  Liminf (𝓟 s) = Inf s :=
@Limsup_principal αᵒᵈ _ s h hs

lemma limsup_congr {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a = v a) : limsup u f = limsup v f :=
begin
  rw limsup_eq,
  congr' with b,
  exact eventually_congr (h.mono $ λ x hx, by simp [hx])
end

lemma blimsup_congr {f : filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
  blimsup u f p = blimsup v f p :=
begin
  rw blimsup_eq,
  congr' with b,
  refine eventually_congr (h.mono $ λ x hx, ⟨λ h₁ h₂, _, λ h₁ h₂, _⟩),
  { rw ← hx h₂, exact h₁ h₂, },
  { rw hx h₂, exact h₁ h₂, },
end

lemma bliminf_congr {f : filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
  bliminf u f p = bliminf v f p :=
@blimsup_congr αᵒᵈ _ _ _ _ _ _ h

lemma liminf_congr {α : Type*} [conditionally_complete_lattice β] {f : filter α} {u v : α → β}
  (h : ∀ᶠ a in f, u a = v a) : liminf u f = liminf v f :=
@limsup_congr βᵒᵈ _ _ _ _ _ h

lemma limsup_const {α : Type*} [conditionally_complete_lattice β] {f : filter α} [ne_bot f]
  (b : β) : limsup (λ x, b) f = b :=
by simpa only [limsup_eq, eventually_const] using cInf_Ici

lemma liminf_const {α : Type*} [conditionally_complete_lattice β] {f : filter α} [ne_bot f]
  (b : β) : liminf (λ x, b) f = b :=
@limsup_const βᵒᵈ α _ f _ b


end conditionally_complete_lattice

section complete_lattice
variables [complete_lattice α]

@[simp] theorem Limsup_bot : Limsup (⊥ : filter α) = ⊥ :=
bot_unique $ Inf_le $ by simp

@[simp] theorem Liminf_bot : Liminf (⊥ : filter α) = ⊤ :=
top_unique $ le_Sup $ by simp

@[simp] theorem Limsup_top : Limsup (⊤ : filter α) = ⊤ :=
top_unique $ le_Inf $
  by simp [eq_univ_iff_forall]; exact assume b hb, (top_unique $ hb _)

@[simp] theorem Liminf_top : Liminf (⊤ : filter α) = ⊥ :=
bot_unique $ Sup_le $
  by simp [eq_univ_iff_forall]; exact assume b hb, (bot_unique $ hb _)

@[simp] lemma blimsup_false {f : filter β} {u : β → α} :
  blimsup u f (λ x, false) = ⊥ :=
by simp [blimsup_eq]

@[simp] lemma bliminf_false {f : filter β} {u : β → α} :
  bliminf u f (λ x, false) = ⊤ :=
by simp [bliminf_eq]

/-- Same as limsup_const applied to `⊥` but without the `ne_bot f` assumption -/
lemma limsup_const_bot {f : filter β} : limsup (λ x : β, (⊥ : α)) f = (⊥ : α) :=
begin
  rw [limsup_eq, eq_bot_iff],
  exact Inf_le (eventually_of_forall (λ x, le_rfl)),
end

/-- Same as limsup_const applied to `⊤` but without the `ne_bot f` assumption -/
lemma liminf_const_top {f : filter β} : liminf (λ x : β, (⊤ : α)) f = (⊤ : α) :=
@limsup_const_bot αᵒᵈ β _ _

theorem has_basis.Limsup_eq_infi_Sup {ι} {p : ι → Prop} {s} {f : filter α} (h : f.has_basis p s) :
  Limsup f = ⨅ i (hi : p i), Sup (s i) :=
le_antisymm
  (le_infi₂ $ λ i hi, Inf_le $ h.eventually_iff.2 ⟨i, hi, λ x, le_Sup⟩)
  (le_Inf $ assume a ha, let ⟨i, hi, ha⟩ := h.eventually_iff.1 ha in
    infi₂_le_of_le _ hi $ Sup_le ha)

theorem has_basis.Liminf_eq_supr_Inf {p : ι → Prop} {s : ι → set α} {f : filter α}
  (h : f.has_basis p s) : Liminf f = ⨆ i (hi : p i), Inf (s i) :=
@has_basis.Limsup_eq_infi_Sup αᵒᵈ _ _ _ _ _ h

theorem Limsup_eq_infi_Sup {f : filter α} : Limsup f = ⨅ s ∈ f, Sup s :=
f.basis_sets.Limsup_eq_infi_Sup

theorem Liminf_eq_supr_Inf {f : filter α} : Liminf f = ⨆ s ∈ f, Inf s :=
@Limsup_eq_infi_Sup αᵒᵈ _ _

theorem limsup_le_supr {f : filter β} {u : β → α} : limsup u f ≤ ⨆ n, u n :=
limsup_le_of_le (by is_bounded_default) (eventually_of_forall (le_supr u))

theorem infi_le_liminf {f : filter β} {u : β → α} : (⨅ n, u n) ≤ liminf u f :=
le_liminf_of_le (by is_bounded_default) (eventually_of_forall (infi_le u))

/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_infi_supr {f : filter β} {u : β → α} : limsup u f = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
(f.basis_sets.map u).Limsup_eq_infi_Sup.trans $
  by simp only [Sup_image, id]

lemma limsup_eq_infi_supr_of_nat {u : ℕ → α} : limsup u at_top = ⨅ n : ℕ, ⨆ i ≥ n, u i :=
(at_top_basis.map u).Limsup_eq_infi_Sup.trans $
  by simp only [Sup_image, infi_const]; refl

lemma limsup_eq_infi_supr_of_nat' {u : ℕ → α} : limsup u at_top = ⨅ n : ℕ, ⨆ i : ℕ, u (i + n) :=
by simp only [limsup_eq_infi_supr_of_nat, supr_ge_eq_supr_nat_add]

theorem has_basis.limsup_eq_infi_supr {p : ι → Prop} {s : ι → set β} {f : filter β} {u : β → α}
  (h : f.has_basis p s) : limsup u f = ⨅ i (hi : p i), ⨆ a ∈ s i, u a :=
(h.map u).Limsup_eq_infi_Sup.trans $ by simp only [Sup_image, id]

lemma blimsup_congr' {f : filter β} {p q : β → Prop} {u : β → α}
  (h : ∀ᶠ x in f, u x ≠ ⊥ → (p x ↔ q x)) :
  blimsup u f p = blimsup u f q :=
begin
  simp only [blimsup_eq],
  congr,
  ext a,
  refine eventually_congr (h.mono $ λ b hb, _),
  cases eq_or_ne (u b) ⊥ with hu hu, { simp [hu], },
  rw hb hu,
end

lemma bliminf_congr' {f : filter β} {p q : β → Prop} {u : β → α}
  (h : ∀ᶠ x in f, u x ≠ ⊤ → (p x ↔ q x)) :
  bliminf u f p = bliminf u f q :=
@blimsup_congr' αᵒᵈ β _ _ _ _ _ h

lemma blimsup_eq_infi_bsupr {f : filter β} {p : β → Prop} {u : β → α} :
  blimsup u f p = ⨅ s ∈ f, ⨆ b (hb : p b ∧ b ∈ s), u b :=
begin
  refine le_antisymm (Inf_le_Inf _) (infi_le_iff.mpr $ λ a ha, le_Inf_iff.mpr $ λ a' ha', _),
  { rintros - ⟨s, rfl⟩,
    simp only [mem_set_of_eq, le_infi_iff],
    conv { congr, funext, rw imp.swap, },
    refine eventually_imp_distrib_left.mpr (λ h, eventually_iff_exists_mem.2 ⟨s, h, λ x h₁ h₂, _⟩),
    exact @le_supr₂ α β (λ b, p b ∧ b ∈ s) _ (λ b hb, u b) x ⟨h₂, h₁⟩, },
  { obtain ⟨s, hs, hs'⟩ := eventually_iff_exists_mem.mp ha',
    simp_rw imp.swap at hs',
    exact (le_infi_iff.mp (ha s) hs).trans (by simpa only [supr₂_le_iff, and_imp]), },
end

lemma blimsup_eq_infi_bsupr_of_nat {p : ℕ → Prop} {u : ℕ → α} :
  blimsup u at_top p = ⨅ i, ⨆ j (hj : p j ∧ i ≤ j), u j :=
by simp only [blimsup_eq_limsup_subtype, mem_preimage, mem_Ici, function.comp_app, cinfi_pos,
  supr_subtype, (at_top_basis.comap (coe : {x | p x} → ℕ)).limsup_eq_infi_supr, mem_set_of_eq,
  subtype.coe_mk, supr_and]

/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_supr_infi {f : filter β} {u : β → α} : liminf u f = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
@limsup_eq_infi_supr αᵒᵈ β _ _ _

lemma liminf_eq_supr_infi_of_nat {u : ℕ → α} : liminf u at_top = ⨆ n : ℕ, ⨅ i ≥ n, u i :=
@limsup_eq_infi_supr_of_nat αᵒᵈ _ u

lemma liminf_eq_supr_infi_of_nat' {u : ℕ → α} : liminf u at_top = ⨆ n : ℕ, ⨅ i : ℕ, u (i + n) :=
@limsup_eq_infi_supr_of_nat' αᵒᵈ _ _

theorem has_basis.liminf_eq_supr_infi {p : ι → Prop} {s : ι → set β} {f : filter β} {u : β → α}
  (h : f.has_basis p s) : liminf u f = ⨆ i (hi : p i), ⨅ a ∈ s i, u a :=
@has_basis.limsup_eq_infi_supr αᵒᵈ _ _ _ _ _ _ _ h

lemma bliminf_eq_supr_binfi {f : filter β} {p : β → Prop} {u : β → α} :
  bliminf u f p = ⨆ s ∈ f, ⨅ b (hb : p b ∧ b ∈ s), u b :=
@blimsup_eq_infi_bsupr αᵒᵈ β _ f p u

lemma bliminf_eq_supr_binfi_of_nat {p : ℕ → Prop} {u : ℕ → α} :
  bliminf u at_top p = ⨆ i, ⨅ j (hj : p j ∧ i ≤ j), u j :=
@blimsup_eq_infi_bsupr_of_nat αᵒᵈ _ p u

lemma limsup_eq_Inf_Sup {ι R : Type*} (F : filter ι) [complete_lattice R] (a : ι → R) :
  limsup a F = Inf ((λ I, Sup (a '' I)) '' F.sets) :=
begin
  refine le_antisymm _ _,
  { rw limsup_eq,
    refine Inf_le_Inf (λ x hx, _),
    rcases (mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩,
    filter_upwards [I_mem_F] with i hi,
    exact hI ▸ le_Sup (mem_image_of_mem _ hi), },
  { refine le_Inf_iff.mpr (λ b hb, Inf_le_of_le (mem_image_of_mem _ $ filter.mem_sets.mpr hb)
      $ Sup_le _),
    rintros _ ⟨_, h, rfl⟩,
    exact h, },
end

lemma liminf_eq_Sup_Inf {ι R : Type*} (F : filter ι) [complete_lattice R] (a : ι → R) :
  liminf a F = Sup ((λ I, Inf (a '' I)) '' F.sets) :=
@filter.limsup_eq_Inf_Sup ι (order_dual R) _ _ a

@[simp] lemma liminf_nat_add (f : ℕ → α) (k : ℕ) :
  liminf (λ i, f (i + k)) at_top = liminf f at_top :=
by { simp_rw liminf_eq_supr_infi_of_nat, exact supr_infi_ge_nat_add f k }

@[simp] lemma limsup_nat_add (f : ℕ → α) (k : ℕ) :
  limsup (λ i, f (i + k)) at_top = limsup f at_top :=
@liminf_nat_add αᵒᵈ _ f k

lemma liminf_le_of_frequently_le' {α β} [complete_lattice β]
  {f : filter α} {u : α → β} {x : β} (h : ∃ᶠ a in f, u a ≤ x) :
  liminf u f ≤ x :=
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
  x ≤ limsup u f :=
@liminf_le_of_frequently_le' _ βᵒᵈ _ _ _ _ h

/-- If `f : α → α` is a morphism of complete lattices, then the limsup of its iterates of any
`a : α` is a fixed point. -/
@[simp] lemma complete_lattice_hom.apply_limsup_iterate (f : complete_lattice_hom α α) (a : α) :
  f (limsup (λ n, f^[n] a) at_top) = limsup (λ n, f^[n] a) at_top :=
begin
  rw [limsup_eq_infi_supr_of_nat', map_infi],
  simp_rw [_root_.map_supr, ← function.comp_apply f, ← function.iterate_succ' f, ← nat.add_succ],
  conv_rhs { rw infi_split _ ((<) (0 : ℕ)), },
  simp only [not_lt, le_zero_iff, infi_infi_eq_left, add_zero, infi_nat_gt_zero_eq, left_eq_inf],
  refine (infi_le (λ i, ⨆ j, (f^[j + (i + 1)]) a) 0).trans _,
  simp only [zero_add, function.comp_app, supr_le_iff],
  exact λ i, le_supr (λ i, (f^[i] a)) (i + 1),
end

/-- If `f : α → α` is a morphism of complete lattices, then the liminf of its iterates of any
`a : α` is a fixed point. -/
lemma complete_lattice_hom.apply_liminf_iterate (f : complete_lattice_hom α α) (a : α) :
  f (liminf (λ n, f^[n] a) at_top) = liminf (λ n, f^[n] a) at_top :=
(complete_lattice_hom.dual f).apply_limsup_iterate _
variables {f g : filter β} {p q : β → Prop} {u v : β → α}

lemma blimsup_mono (h : ∀ x, p x → q x) :
  blimsup u f p ≤ blimsup u f q :=
Inf_le_Inf $ λ a ha, ha.mono $ by tauto

lemma bliminf_antitone (h : ∀ x, p x → q x) :
  bliminf u f q ≤ bliminf u f p :=
Sup_le_Sup $ λ a ha, ha.mono $ by tauto

lemma mono_blimsup' (h : ∀ᶠ x in f, p x → u x ≤ v x) :
  blimsup u f p ≤ blimsup v f p :=
Inf_le_Inf $ λ a ha, (ha.and h).mono $ λ x hx hx', (hx.2 hx').trans (hx.1 hx')

lemma mono_blimsup (h : ∀ x, p x → u x ≤ v x) :
  blimsup u f p ≤ blimsup v f p :=
mono_blimsup' $ eventually_of_forall h

lemma mono_bliminf' (h : ∀ᶠ x in f, p x → u x ≤ v x) :
  bliminf u f p ≤ bliminf v f p :=
Sup_le_Sup $ λ a ha, (ha.and h).mono $ λ x hx hx', (hx.1 hx').trans (hx.2 hx')

lemma mono_bliminf (h : ∀ x, p x → u x ≤ v x) :
  bliminf u f p ≤ bliminf v f p :=
mono_bliminf' $ eventually_of_forall h

lemma bliminf_antitone_filter (h : f ≤ g) :
  bliminf u g p ≤ bliminf u f p :=
Sup_le_Sup $ λ a ha, ha.filter_mono h

lemma blimsup_monotone_filter (h : f ≤ g) :
  blimsup u f p ≤ blimsup u g p :=
Inf_le_Inf $ λ a ha, ha.filter_mono h

@[simp] lemma blimsup_and_le_inf :
  blimsup u f (λ x, p x ∧ q x) ≤ blimsup u f p ⊓ blimsup u f q :=
le_inf (blimsup_mono $ by tauto) (blimsup_mono $ by tauto)

@[simp] lemma bliminf_sup_le_and :
  bliminf u f p ⊔ bliminf u f q ≤ bliminf u f (λ x, p x ∧ q x) :=
@blimsup_and_le_inf αᵒᵈ β _ f p q u

/-- See also `filter.blimsup_or_eq_sup`. -/
@[simp] lemma blimsup_sup_le_or :
  blimsup u f p ⊔ blimsup u f q ≤ blimsup u f (λ x, p x ∨ q x) :=
sup_le (blimsup_mono $ by tauto) (blimsup_mono $ by tauto)

/-- See also `filter.bliminf_or_eq_inf`. -/
@[simp] lemma bliminf_or_le_inf :
  bliminf u f (λ x, p x ∨ q x) ≤ bliminf u f p ⊓ bliminf u f q :=
@blimsup_sup_le_or αᵒᵈ β _ f p q u

lemma order_iso.apply_blimsup [complete_lattice γ] (e : α ≃o γ) :
  e (blimsup u f p) = blimsup (e ∘ u) f p :=
begin
  simp only [blimsup_eq, map_Inf, function.comp_app],
  congr,
  ext c,
  obtain ⟨a, rfl⟩ := e.surjective c,
  simp,
end

lemma order_iso.apply_bliminf [complete_lattice γ] (e : α ≃o γ) :
  e (bliminf u f p) = bliminf (e ∘ u) f p :=
@order_iso.apply_blimsup αᵒᵈ β γᵒᵈ _ f p u _ e.dual

lemma Sup_hom.apply_blimsup_le [complete_lattice γ] (g : Sup_hom α γ) :
  g (blimsup u f p) ≤ blimsup (g ∘ u) f p :=
begin
  simp only [blimsup_eq_infi_bsupr],
  refine ((order_hom_class.mono g).map_infi₂_le _).trans _,
  simp only [_root_.map_supr],
end

lemma Inf_hom.le_apply_bliminf [complete_lattice γ] (g : Inf_hom α γ) :
  bliminf (g ∘ u) f p ≤ g (bliminf u f p) :=
@Sup_hom.apply_blimsup_le αᵒᵈ β γᵒᵈ _ f p u _ g.dual

end complete_lattice

section complete_distrib_lattice

variables [complete_distrib_lattice α] {f : filter β} {p q : β → Prop} {u : β → α}

@[simp] lemma blimsup_or_eq_sup :
  blimsup u f (λ x, p x ∨ q x) = blimsup u f p ⊔ blimsup u f q :=
begin
  refine le_antisymm _ blimsup_sup_le_or,
  simp only [blimsup_eq, Inf_sup_eq, sup_Inf_eq, le_infi₂_iff, mem_set_of_eq],
  refine λ a' ha' a ha, Inf_le ((ha.and ha').mono $ λ b h hb, _),
  exact or.elim hb (λ hb, le_sup_of_le_left $ h.1 hb) (λ hb, le_sup_of_le_right $ h.2 hb),
end

@[simp] lemma bliminf_or_eq_inf :
  bliminf u f (λ x, p x ∨ q x) = bliminf u f p ⊓ bliminf u f q :=
@blimsup_or_eq_sup αᵒᵈ β _ f p q u

lemma sup_limsup [ne_bot f] (a : α) :
  a ⊔ limsup u f = limsup (λ x, a ⊔ u x) f :=
begin
  simp only [limsup_eq_infi_supr, supr_sup_eq, sup_binfi_eq],
  congr, ext s, congr, ext hs, congr,
  exact (bsupr_const (nonempty_of_mem hs)).symm,
end

lemma inf_liminf [ne_bot f] (a : α) :
  a ⊓ liminf u f = liminf (λ x, a ⊓ u x) f :=
@sup_limsup αᵒᵈ β _ f _ _ _

lemma sup_liminf (a : α) :
  a ⊔ liminf u f = liminf (λ x, a ⊔ u x) f :=
begin
  simp only [liminf_eq_supr_infi],
  rw [sup_comm, bsupr_sup (⟨univ, univ_mem⟩ : ∃ (i : set β), i ∈ f)],
  simp_rw [binfi_sup_eq, @sup_comm _ _ a],
end

lemma inf_limsup (a : α) :
  a ⊓ limsup u f = limsup (λ x, a ⊓ u x) f :=
@sup_liminf αᵒᵈ β _ f _ _

end complete_distrib_lattice

section complete_boolean_algebra

variables [complete_boolean_algebra α] (f : filter β) (u : β → α)

lemma limsup_compl :
  (limsup u f)ᶜ = liminf (compl ∘ u) f :=
by simp only [limsup_eq_infi_supr, liminf_eq_supr_infi, compl_infi, compl_supr]

lemma liminf_compl :
  (liminf u f)ᶜ = limsup (compl ∘ u) f :=
by simp only [limsup_eq_infi_supr, liminf_eq_supr_infi, compl_infi, compl_supr]

lemma limsup_sdiff (a : α) :
  (limsup u f) \ a = limsup (λ b, (u b) \ a) f :=
begin
  simp only [limsup_eq_infi_supr, sdiff_eq],
  rw binfi_inf (⟨univ, univ_mem⟩ : ∃ (i : set β), i ∈ f),
  simp_rw [inf_comm, inf_bsupr_eq, inf_comm],
end

lemma liminf_sdiff [ne_bot f] (a : α) :
  (liminf u f) \ a = liminf (λ b, (u b) \ a) f :=
by simp only [sdiff_eq, @inf_comm _ _ _ aᶜ, inf_liminf]

lemma sdiff_limsup [ne_bot f] (a : α) :
  a \ limsup u f = liminf (λ b, a \ u b) f :=
begin
  rw ← compl_inj_iff,
  simp only [sdiff_eq, liminf_compl, (∘), compl_inf, compl_compl, sup_limsup],
end

lemma sdiff_liminf (a : α) :
  a \ liminf u f = limsup (λ b, a \ u b) f :=
begin
  rw ← compl_inj_iff,
  simp only [sdiff_eq, limsup_compl, (∘), compl_inf, compl_compl, sup_liminf],
end

end complete_boolean_algebra

section set_lattice

variables {p : ι → Prop} {s : ι → set α}

lemma cofinite.blimsup_set_eq :
  blimsup s cofinite p = { x | { n | p n ∧ x ∈ s n }.infinite } :=
begin
  simp only [blimsup_eq, le_eq_subset, eventually_cofinite, not_forall, Inf_eq_sInter, exists_prop],
  ext x,
  refine ⟨λ h, _, λ hx t h, _⟩;
  contrapose! h,
  { simp only [mem_sInter, mem_set_of_eq, not_forall, exists_prop],
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩, },
  { exact hx.mono (λ i hi, ⟨hi.1, λ hit, h (hit hi.2)⟩), },
end

lemma cofinite.bliminf_set_eq :
  bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.finite } :=
begin
  rw ← compl_inj_iff,
  simpa only [bliminf_eq_supr_binfi, compl_infi, compl_supr, ← blimsup_eq_infi_bsupr,
    cofinite.blimsup_set_eq],
end

/-- In other words, `limsup cofinite s` is the set of elements lying inside the family `s`
infinitely often. -/
lemma cofinite.limsup_set_eq :
  limsup s cofinite = { x | { n | x ∈ s n }.infinite } :=
by simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and]

/-- In other words, `liminf cofinite s` is the set of elements lying outside the family `s`
finitely often. -/
lemma cofinite.liminf_set_eq :
  liminf s cofinite = { x | { n | x ∉ s n }.finite } :=
by simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and]

lemma exists_forall_mem_of_has_basis_mem_blimsup
  {l : filter β} {b : ι → set β} {q : ι → Prop} (hl : l.has_basis q b)
  {u : β → set α} {p : β → Prop} {x : α} (hx : x ∈ blimsup u l p) :
  ∃ f : {i | q i} → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i :=
begin
  rw blimsup_eq_infi_bsupr at hx,
  simp only [supr_eq_Union, infi_eq_Inter, mem_Inter, mem_Union, exists_prop] at hx,
  choose g hg hg' using hx,
  refine ⟨λ (i : {i | q i}), g (b i) (hl.mem_of_mem i.2), λ i, ⟨_, _⟩⟩,
  { exact hg' (b i) (hl.mem_of_mem i.2), },
  { exact hg (b i) (hl.mem_of_mem i.2), },
end

lemma exists_forall_mem_of_has_basis_mem_blimsup'
  {l : filter β} {b : ι → set β} (hl : l.has_basis (λ _, true) b)
  {u : β → set α} {p : β → Prop} {x : α} (hx : x ∈ blimsup u l p) :
  ∃ f : ι → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i :=
begin
  obtain ⟨f, hf⟩ := exists_forall_mem_of_has_basis_mem_blimsup hl hx,
  exact ⟨λ i, f ⟨i, trivial⟩, λ i, hf ⟨i, trivial⟩⟩,
end

end set_lattice

section conditionally_complete_linear_order

lemma frequently_lt_of_lt_Limsup {f : filter α} [conditionally_complete_linear_order α] {a : α}
  (hf : f.is_cobounded (≤) . is_bounded_default) (h : a < Limsup f) : ∃ᶠ n in f, a < n :=
begin
  contrapose! h,
  simp only [not_frequently, not_lt] at h,
  exact Limsup_le_of_le hf h,
end

lemma frequently_lt_of_Liminf_lt {f : filter α} [conditionally_complete_linear_order α] {a : α}
  (hf : f.is_cobounded (≥) . is_bounded_default) (h : Liminf f < a) : ∃ᶠ n in f, n < a :=
@frequently_lt_of_lt_Limsup (order_dual α) f _ a hf h

lemma eventually_lt_of_lt_liminf {f : filter α} [conditionally_complete_linear_order β]
  {u : α → β} {b : β} (h : b < liminf u f) (hu : f.is_bounded_under (≥) u . is_bounded_default) :
  ∀ᶠ a in f, b < u a :=
begin
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β) (hc : c ∈ {c : β | ∀ᶠ (n : α) in f, c ≤ u n}), b < c :=
    exists_lt_of_lt_cSup hu h,
  exact hc.mono (λ x hx, lt_of_lt_of_le hbc hx)
end

lemma eventually_lt_of_limsup_lt {f : filter α} [conditionally_complete_linear_order β]
  {u : α → β} {b : β} (h : limsup u f < b) (hu : f.is_bounded_under (≤) u . is_bounded_default) :
  ∀ᶠ a in f, u a < b :=
@eventually_lt_of_lt_liminf _ βᵒᵈ _ _ _ _ h hu

lemma le_limsup_of_frequently_le {α β} [conditionally_complete_linear_order β] {f : filter α}
  {u : α → β}  {b : β} (hu_le : ∃ᶠ x in f, b ≤ u x)
  (hu : f.is_bounded_under (≤) u . is_bounded_default) :
  b ≤ limsup u f :=
begin
  revert hu_le,
  rw [←not_imp_not, not_frequently],
  simp_rw ←lt_iff_not_ge,
  exact λ h, eventually_lt_of_limsup_lt h hu,
end

lemma liminf_le_of_frequently_le  {α β} [conditionally_complete_linear_order β] {f : filter α}
  {u : α → β}  {b : β} (hu_le : ∃ᶠ x in f, u x ≤ b)
  (hu : f.is_bounded_under (≥) u . is_bounded_default) :
  liminf u f ≤ b :=
@le_limsup_of_frequently_le _ βᵒᵈ _ f u b hu_le hu

lemma frequently_lt_of_lt_limsup {α β} [conditionally_complete_linear_order β] {f : filter α}
  {u : α → β}  {b : β}
  (hu : f.is_cobounded_under (≤) u . is_bounded_default) (h : b < limsup u f) :
  ∃ᶠ x in f, b < u x :=
begin
  contrapose! h,
  apply Limsup_le_of_le hu,
  simpa using h,
end

lemma frequently_lt_of_liminf_lt {α β} [conditionally_complete_linear_order β] {f : filter α}
  {u : α → β}  {b : β}
  (hu : f.is_cobounded_under (≥) u . is_bounded_default) (h : liminf u f < b) :
  ∃ᶠ x in f, u x < b :=
@frequently_lt_of_lt_limsup _ βᵒᵈ _ f u b hu h

end conditionally_complete_linear_order

end filter

section order
open filter

lemma monotone.is_bounded_under_le_comp [nonempty β] [linear_order β] [preorder γ]
  [no_max_order γ] {g : β → γ} {f : α → β} {l : filter α} (hg : monotone g)
  (hg' : tendsto g at_top at_top) :
  is_bounded_under (≤) l (g ∘ f) ↔ is_bounded_under (≤) l f :=
begin
  refine ⟨_, λ h, h.is_bounded_under hg⟩,
  rintro ⟨c, hc⟩, rw eventually_map at hc,
  obtain ⟨b, hb⟩ : ∃ b, ∀ a ≥ b, c < g a := eventually_at_top.1 (hg'.eventually_gt_at_top c),
  exact ⟨b, hc.mono $ λ x hx, not_lt.1 (λ h, (hb _ h.le).not_le hx)⟩
end

lemma monotone.is_bounded_under_ge_comp [nonempty β] [linear_order β] [preorder γ]
  [no_min_order γ] {g : β → γ} {f : α → β} {l : filter α} (hg : monotone g)
  (hg' : tendsto g at_bot at_bot) :
  is_bounded_under (≥) l (g ∘ f) ↔ is_bounded_under (≥) l f :=
hg.dual.is_bounded_under_le_comp hg'

lemma antitone.is_bounded_under_le_comp [nonempty β] [linear_order β] [preorder γ]
  [no_max_order γ] {g : β → γ} {f : α → β} {l : filter α} (hg : antitone g)
  (hg' : tendsto g at_bot at_top) :
  is_bounded_under (≤) l (g ∘ f) ↔ is_bounded_under (≥) l f :=
hg.dual_right.is_bounded_under_ge_comp hg'

lemma antitone.is_bounded_under_ge_comp [nonempty β] [linear_order β] [preorder γ]
  [no_min_order γ] {g : β → γ} {f : α → β} {l : filter α} (hg : antitone g)
  (hg' : tendsto g at_top at_bot) :
  is_bounded_under (≥) l (g ∘ f) ↔ is_bounded_under (≤) l f :=
hg.dual_right.is_bounded_under_le_comp hg'

lemma galois_connection.l_limsup_le [conditionally_complete_lattice β]
  [conditionally_complete_lattice γ] {f : filter α} {v : α → β}
  {l : β → γ} {u : γ → β} (gc : galois_connection l u)
  (hlv : f.is_bounded_under (≤) (λ x, l (v x)) . is_bounded_default)
  (hv_co : f.is_cobounded_under (≤) v . is_bounded_default) :
  l (limsup v f) ≤ limsup (λ x, l (v x)) f :=
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
  g (limsup u f) = limsup (λ x, g (u x)) f :=
begin
  refine le_antisymm (g.to_galois_connection.l_limsup_le hgu hu_co) _,
  rw [←(g.symm.symm_apply_apply $ limsup (λ x, g (u x)) f), g.symm_symm],
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
  g (liminf u f) = liminf (λ x, g (u x)) f :=
@order_iso.limsup_apply α βᵒᵈ γᵒᵈ _ _ f u g.dual hu hu_co hgu hgu_co

end order
