/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import data.sum.order
import order.initial_seg
import set_theory.cardinal.basic

/-!
# Ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `ordinal`: the type of ordinals (in a given universe)
* `ordinal.type r`: given a well-founded order `r`, this is the corresponding ordinal
* `ordinal.typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the ordinal
  corresponding to all elements smaller than `a`.
* `enum r o h`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
  the ordinal corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using ordinals up to `type r`.
* `ordinal.card o`: the cardinality of an ordinal `o`.
* `ordinal.lift` lifts an ordinal in universe `u` to an ordinal in universe `max u v`.
  For a version registering additionally that this is an initial segment embedding, see
  `ordinal.lift.initial_seg`.
  For a version regiserting that it is a principal segment embedding if `u < v`, see
  `ordinal.lift.principal_seg`.
* `ordinal.omega` or `ω` is the order type of `ℕ`. This definition is universe polymorphic:
  `ordinal.omega.{u} : ordinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. The main properties of addition
  (and the other operations on ordinals) are stated and proved in `ordinal_arithmetic.lean`. Here,
  we only introduce it and prove its basic properties to deduce the fact that the order on ordinals
  is total (and well founded).
* `succ o` is the successor of the ordinal `o`.
* `cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality.
  It is the canonical way to represent a cardinal with an ordinal.

A conditionally complete linear order with bot structure is registered on ordinals, where `⊥` is
`0`, the ordinal corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notations

* `ω` is a notation for the first infinite ordinal in the locale `ordinal`.
-/

noncomputable theory

open function cardinal set equiv order
open_locale classical cardinal initial_seg

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Well order on an arbitrary type -/

section well_ordering_thm
parameter {σ : Type u}
open function

theorem nonempty_embedding_to_cardinal : nonempty (σ ↪ cardinal.{u}) :=
(embedding.total _ _).resolve_left $ λ ⟨⟨f, hf⟩⟩,
  let g : σ → cardinal.{u} := inv_fun f in
  let ⟨x, (hx : g x = 2 ^ sum g)⟩ := inv_fun_surjective hf (2 ^ sum g) in
  have g x ≤ sum g, from le_sum.{u u} g x,
  not_le_of_gt (by rw hx; exact cantor _) this

/-- An embedding of any type to the set of cardinals. -/
def embedding_to_cardinal : σ ↪ cardinal.{u} := classical.choice nonempty_embedding_to_cardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def well_ordering_rel : σ → σ → Prop := embedding_to_cardinal ⁻¹'o (<)

instance well_ordering_rel.is_well_order : is_well_order σ well_ordering_rel :=
(rel_embedding.preimage _ _).is_well_order

instance is_well_order.subtype_nonempty : nonempty {r // is_well_order σ r} :=
⟨⟨well_ordering_rel, infer_instance⟩⟩

end well_ordering_thm

/-! ### Definition of ordinals -/

/-- Bundled structure registering a well order on a type. Ordinals will be defined as a quotient
of this type. -/
structure Well_order : Type (u+1) :=
(α : Type u)
(r : α → α → Prop)
(wo : is_well_order α r)

attribute [instance] Well_order.wo

namespace Well_order

instance : inhabited Well_order := ⟨⟨pempty, _, empty_relation.is_well_order⟩⟩

@[simp] lemma eta (o : Well_order) : mk o.α o.r o.wo = o := by { cases o, refl }

end Well_order

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance ordinal.is_equivalent : setoid Well_order :=
{ r     := λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≃r s),
  iseqv := ⟨λ ⟨α, r, _⟩, ⟨rel_iso.refl _⟩,
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, ⟨e.symm⟩,
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

/-- `ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
def ordinal : Type (u + 1) := quotient ordinal.is_equivalent

instance has_well_founded_out (o : ordinal) : has_well_founded o.out.α := ⟨o.out.r, o.out.wo.wf⟩

instance linear_order_out (o : ordinal) : linear_order o.out.α :=
is_well_order.linear_order o.out.r

instance is_well_order_out_lt (o : ordinal) : is_well_order o.out.α (<) :=
o.out.wo

namespace ordinal

/- ### Basic properties of the order type -/

/-- The order type of a well order is an ordinal. -/
def type (r : α → α → Prop) [wo : is_well_order α r] : ordinal :=
⟦⟨α, r, wo⟩⟧

instance : has_zero ordinal := ⟨type $ @empty_relation pempty⟩
instance : inhabited ordinal := ⟨0⟩
instance : has_one ordinal := ⟨type $ @empty_relation punit⟩

/-- The order type of an element inside a well order. For the embedding as a principal segment, see
`typein.principal_seg`. -/
def typein (r : α → α → Prop) [is_well_order α r] (a : α) : ordinal :=
type (subrel r {b | r b a})

@[simp] theorem type_def' (w : Well_order) : ⟦w⟧ = type w.r :=
by { cases w, refl }

@[simp] theorem type_def (r) [wo : is_well_order α r] : (⟦⟨α, r, wo⟩⟧ : ordinal) = type r :=
rfl

@[simp] lemma type_out (o : ordinal) : ordinal.type o.out.r = o :=
by rw [ordinal.type, Well_order.eta, quotient.out_eq]

theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] : type r = type s ↔ nonempty (r ≃r s) :=
quotient.eq

theorem _root_.rel_iso.ordinal_type_eq {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (h : r ≃r s) : type r = type s :=
type_eq.2 ⟨h⟩

@[simp] theorem type_lt (o : ordinal) : type ((<) : o.out.α → o.out.α → Prop) = o :=
(type_def' _).symm.trans $ quotient.out_eq o

theorem type_eq_zero_of_empty (r) [is_well_order α r] [is_empty α] : type r = 0 :=
(rel_iso.rel_iso_of_is_empty r _).ordinal_type_eq

@[simp] theorem type_eq_zero_iff_is_empty [is_well_order α r] : type r = 0 ↔ is_empty α :=
⟨λ h, let ⟨s⟩ := type_eq.1 h in s.to_equiv.is_empty, @type_eq_zero_of_empty α r _⟩

theorem type_ne_zero_iff_nonempty [is_well_order α r] : type r ≠ 0 ↔ nonempty α := by simp

theorem type_ne_zero_of_nonempty (r) [is_well_order α r] [h : nonempty α] : type r ≠ 0 :=
type_ne_zero_iff_nonempty.2 h

theorem type_pempty : type (@empty_relation pempty) = 0 := rfl
theorem type_empty : type (@empty_relation empty) = 0 := type_eq_zero_of_empty _

theorem type_eq_one_of_unique (r) [is_well_order α r] [unique α] : type r = 1 :=
(rel_iso.rel_iso_of_unique_of_irrefl r _).ordinal_type_eq

@[simp] theorem type_eq_one_iff_unique [is_well_order α r] : type r = 1 ↔ nonempty (unique α) :=
⟨λ h, let ⟨s⟩ := type_eq.1 h in ⟨s.to_equiv.unique⟩, λ ⟨h⟩, @type_eq_one_of_unique α r _ h⟩

theorem type_punit : type (@empty_relation punit) = 1 := rfl
theorem type_unit : type (@empty_relation unit) = 1 := rfl

@[simp] theorem out_empty_iff_eq_zero {o : ordinal} : is_empty o.out.α ↔ o = 0 :=
by rw [←@type_eq_zero_iff_is_empty o.out.α (<), type_lt]

lemma eq_zero_of_out_empty (o : ordinal) [h : is_empty o.out.α] : o = 0 :=
out_empty_iff_eq_zero.1 h

instance is_empty_out_zero : is_empty (0 : ordinal).out.α := out_empty_iff_eq_zero.2 rfl

@[simp] theorem out_nonempty_iff_ne_zero {o : ordinal} : nonempty o.out.α ↔ o ≠ 0 :=
by rw [←@type_ne_zero_iff_nonempty o.out.α (<), type_lt]

lemma ne_zero_of_out_nonempty (o : ordinal) [h : nonempty o.out.α] : o ≠ 0 :=
out_nonempty_iff_ne_zero.1 h

protected lemma one_ne_zero : (1 : ordinal) ≠ 0 := type_ne_zero_of_nonempty _

instance : nontrivial ordinal.{u} := ⟨⟨1, 0, ordinal.one_ne_zero⟩⟩

@[simp] theorem type_preimage {α β : Type u} (r : α → α → Prop) [is_well_order α r] (f : β ≃ α) :
  type (f ⁻¹'o r) = type r :=
(rel_iso.preimage f r).ordinal_type_eq

@[elab_as_eliminator] theorem induction_on {C : ordinal → Prop}
  (o : ordinal) (H : ∀ α r [is_well_order α r], by exactI C (type r)) : C o :=
quot.induction_on o $ λ ⟨α, r, wo⟩, @H α r wo

/-! ### The order on ordinals -/

instance : partial_order ordinal :=
{ le := λ a b, quotient.lift_on₂ a b (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≼i s)) $
    λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
    propext ⟨
      λ ⟨h⟩, ⟨(initial_seg.of_iso f.symm).trans $
        h.trans (initial_seg.of_iso g)⟩,
      λ ⟨h⟩, ⟨(initial_seg.of_iso f).trans $
        h.trans (initial_seg.of_iso g.symm)⟩⟩,
  lt := λ a b, quotient.lift_on₂ a b (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≺i s)) $
    λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
    by exactI propext ⟨
      λ ⟨h⟩, ⟨principal_seg.equiv_lt f.symm $
        h.lt_le (initial_seg.of_iso g)⟩,
      λ ⟨h⟩, ⟨principal_seg.equiv_lt f $
        h.lt_le (initial_seg.of_iso g.symm)⟩⟩,
  le_refl := quot.ind $ by exact λ ⟨α, r, wo⟩, ⟨initial_seg.refl _⟩,
  le_trans := λ a b c, quotient.induction_on₃ a b c $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂ a b $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩, by exactI
      ⟨λ ⟨f⟩, ⟨⟨f⟩, λ ⟨g⟩, (f.lt_le g).irrefl⟩,
      λ ⟨⟨f⟩, h⟩, sum.rec_on f.lt_or_eq (λ g, ⟨g⟩)
      (λ g, (h ⟨initial_seg.of_iso g.symm⟩).elim)⟩,
  le_antisymm := λ a b,
    quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨h₁⟩ ⟨h₂⟩,
    by exactI quot.sound ⟨initial_seg.antisymm h₁ h₂⟩ }

/-- Ordinal less-equal is defined such that
  well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an initial segment of `s`. -/
add_decl_doc ordinal.partial_order.le

/-- Ordinal less-than is defined such that
  well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a principal segment of `s`. -/
add_decl_doc ordinal.partial_order.lt

theorem type_le_iff {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r ≤ type s ↔ nonempty (r ≼i s) := iff.rfl

theorem type_le_iff' {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] : type r ≤ type s ↔ nonempty (r ↪r s) :=
⟨λ ⟨f⟩, ⟨f⟩, λ ⟨f⟩, ⟨f.collapse⟩⟩

theorem _root_.initial_seg.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (h : r ≼i s) : type r ≤ type s := ⟨h⟩

theorem _root_.rel_embedding.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (h : r ↪r s) : type r ≤ type s := ⟨h.collapse⟩

@[simp] theorem type_lt_iff {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r < type s ↔ nonempty (r ≺i s) := iff.rfl

theorem _root_.principal_seg.ordinal_type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (h : r ≺i s) : type r < type s := ⟨h⟩

protected theorem zero_le (o : ordinal) : 0 ≤ o :=
induction_on o $ λ α r _, by exactI (initial_seg.of_is_empty _ r).ordinal_type_le

instance : order_bot ordinal := ⟨0, ordinal.zero_le⟩

@[simp] lemma bot_eq_zero : (⊥ : ordinal) = 0 := rfl

@[simp] protected theorem le_zero {o : ordinal} : o ≤ 0 ↔ o = 0 := le_bot_iff
protected theorem pos_iff_ne_zero {o : ordinal} : 0 < o ↔ o ≠ 0 := bot_lt_iff_ne_bot
protected theorem not_lt_zero (o : ordinal) : ¬ o < 0 := not_lt_bot
theorem eq_zero_or_pos : ∀ a : ordinal, a = 0 ∨ 0 < a := eq_bot_or_bot_lt

instance : zero_le_one_class ordinal := ⟨ordinal.zero_le _⟩

instance ne_zero.one : ne_zero (1 : ordinal) := ⟨ordinal.one_ne_zero⟩

/-- Given two ordinals `α ≤ β`, then `initial_seg_out α β` is the initial segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def initial_seg_out {α β : ordinal} (h : α ≤ β) :
  initial_seg ((<) : α.out.α → α.out.α → Prop) ((<) : β.out.α → β.out.α → Prop) :=
begin
  change α.out.r ≼i β.out.r,
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice
end

/-- Given two ordinals `α < β`, then `principal_seg_out α β` is the principal segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def principal_seg_out {α β : ordinal} (h : α < β) :
  principal_seg ((<) : α.out.α → α.out.α → Prop) ((<) : β.out.α → β.out.α → Prop) :=
begin
  change α.out.r ≺i β.out.r,
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice
end

theorem typein_lt_type (r : α → α → Prop) [is_well_order α r] (a : α) : typein r a < type r :=
⟨principal_seg.of_element _ _⟩

theorem typein_lt_self {o : ordinal} (i : o.out.α) : typein (<) i < o :=
by { simp_rw ←type_lt o, apply typein_lt_type }

@[simp] theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : r ≺i s) :
  typein s f.top = type r :=
eq.symm $ quot.sound ⟨rel_iso.of_surjective
  (rel_embedding.cod_restrict _ f f.lt_top)
  (λ ⟨a, h⟩, by rcases f.down.1 h with ⟨b, rfl⟩; exact ⟨b, rfl⟩)⟩

@[simp] theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : r ≼i s) (a : α) :
  ordinal.typein s (f a) = ordinal.typein r a :=
eq.symm $ quotient.sound ⟨rel_iso.of_surjective
  (rel_embedding.cod_restrict _
    ((subrel.rel_embedding _ _).trans f)
    (λ ⟨x, h⟩, by rw [rel_embedding.trans_apply]; exact f.to_rel_embedding.map_rel_iff.2 h))
  (λ ⟨y, h⟩, by rcases f.init h with ⟨a, rfl⟩;
    exact ⟨⟨a, f.to_rel_embedding.map_rel_iff.1 h⟩, subtype.eq $ rel_embedding.trans_apply _ _ _⟩)⟩

@[simp] theorem typein_lt_typein (r : α → α → Prop) [is_well_order α r]
  {a b : α} : typein r a < typein r b ↔ r a b :=
⟨λ ⟨f⟩, begin
  have : f.top.1 = a,
  { let f' := principal_seg.of_element r a,
    let g' := f.trans (principal_seg.of_element r b),
    have : g'.top = f'.top, {rw subsingleton.elim f' g'},
    exact this },
  rw ← this, exact f.top.2
end, λ h, ⟨principal_seg.cod_restrict _
  (principal_seg.of_element r a)
  (λ x, @trans _ r _ _ _ _ x.2 h) h⟩⟩

theorem typein_surj (r : α → α → Prop) [is_well_order α r]
  {o} (h : o < type r) : ∃ a, typein r a = o :=
induction_on o (λ β s _ ⟨f⟩, by exactI ⟨f.top, typein_top _⟩) h

lemma typein_injective (r : α → α → Prop) [is_well_order α r] : injective (typein r) :=
injective_of_increasing r (<) (typein r) (λ x y, (typein_lt_typein r).2)

@[simp] theorem typein_inj (r : α → α → Prop) [is_well_order α r]
  {a b} : typein r a = typein r b ↔ a = b :=
(typein_injective r).eq_iff

/-! ### Enumerating elements in a well-order with ordinals. -/

/-- `enum r o h` is the `o`-th element of `α` ordered by `r`.
  That is, `enum` maps an initial segment of the ordinals, those
  less than the order type of `r`, to the elements of `α`. -/
def enum (r : α → α → Prop) [is_well_order α r] (o) : o < type r → α :=
quot.rec_on o (λ ⟨β, s, _⟩ h, (classical.choice h).top) $
λ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨h⟩, begin
  resetI, refine funext (λ (H₂ : type t < type r), _),
  have H₁ : type s < type r, {rwa type_eq.2 ⟨h⟩},
  have : ∀ {o e} (H : o < type r), @@eq.rec
   (λ (o : ordinal), o < type r → α)
   (λ (h : type s < type r), (classical.choice h).top)
     e H = (classical.choice H₁).top, {intros, subst e},
  exact (this H₂).trans (principal_seg.top_eq h
    (classical.choice H₁) (classical.choice H₂))
end

theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : s ≺i r)
  {h : type s < type r} : enum r (type s) h = f.top :=
principal_seg.top_eq (rel_iso.refl _) _ _

@[simp] theorem enum_typein (r : α → α → Prop) [is_well_order α r] (a : α) :
  enum r (typein r a) (typein_lt_type r a) = a :=
enum_type (principal_seg.of_element r a)

@[simp] theorem typein_enum (r : α → α → Prop) [is_well_order α r]
  {o} (h : o < type r) : typein r (enum r o h) = o :=
let ⟨a, e⟩ := typein_surj r h in
by clear _let_match; subst e; rw enum_typein

theorem enum_lt_enum {r : α → α → Prop} [is_well_order α r]
  {o₁ o₂ : ordinal} (h₁ : o₁ < type r) (h₂ : o₂ < type r) :
  r (enum r o₁ h₁) (enum r o₂ h₂) ↔ o₁ < o₂ :=
by rw [← typein_lt_typein r, typein_enum, typein_enum]

lemma rel_iso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (f : r ≃r s) (o : ordinal) : ∀(hr : o < type r) (hs : o < type s),
  f (enum r o hr) = enum s o hs :=
begin
  refine induction_on o _, rintros γ t wo ⟨g⟩ ⟨h⟩,
  resetI, rw [enum_type g, enum_type (principal_seg.lt_equiv g f)], refl
end

lemma rel_iso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (f : r ≃r s) (o : ordinal) (hr : o < type r) :
  f (enum r o hr) =
  enum s o (by {convert hr using 1, apply quotient.sound, exact ⟨f.symm⟩ }) :=
rel_iso_enum' _ _ _ _

theorem lt_wf : @well_founded ordinal (<) :=
⟨λ a, induction_on a $ λ α r wo, by exactI
suffices ∀ a, acc (<) (typein r a), from
⟨_, λ o h, let ⟨a, e⟩ := typein_surj r h in e ▸ this a⟩,
λ a, acc.rec_on (wo.wf.apply a) $ λ x H IH, ⟨_, λ o h, begin
  rcases typein_surj r (lt_trans h (typein_lt_type r _)) with ⟨b, rfl⟩,
  exact IH _ ((typein_lt_typein r).1 h)
end⟩⟩

instance : has_well_founded ordinal := ⟨(<), lt_wf⟩

/-- Reformulation of well founded induction on ordinals as a lemma that works with the
`induction` tactic, as in `induction i using ordinal.induction with i IH`. -/
lemma induction {p : ordinal.{u} → Prop} (i : ordinal.{u})
  (h : ∀ j, (∀ k, k < j → p k) → p j) : p i :=
lt_wf.induction i h

/-- Principal segment version of the `typein` function, embedding a well order into
  ordinals as a principal segment. -/
def typein.principal_seg {α : Type u} (r : α → α → Prop) [is_well_order α r] :
  @principal_seg α ordinal.{u} r (<) :=
⟨rel_embedding.of_monotone (typein r)
  (λ a b, (typein_lt_typein r).2), type r, λ b,
    ⟨λ h, ⟨enum r _ h, typein_enum r h⟩,
    λ ⟨a, e⟩, e ▸ typein_lt_type _ _⟩⟩

@[simp] theorem typein.principal_seg_coe (r : α → α → Prop) [is_well_order α r] :
  (typein.principal_seg r : α → ordinal) = typein r := rfl

/-! ### Cardinality of ordinals -/

/-- The cardinal of an ordinal is the cardinality of any type on which a relation with that order
type is defined. -/
def card : ordinal → cardinal := quotient.map Well_order.α $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, ⟨e.to_equiv⟩

@[simp] theorem card_type (r : α → α → Prop) [is_well_order α r] : card (type r) = #α := rfl

@[simp] lemma card_typein {r : α → α → Prop} [wo : is_well_order α r] (x : α) :
  #{y // r y x} = (typein r x).card :=
rfl

theorem card_le_card {o₁ o₂ : ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
induction_on o₁ $ λ α r _, induction_on o₂ $ λ β s _ ⟨⟨⟨f, _⟩, _⟩⟩, ⟨f⟩

@[simp] theorem card_zero : card 0 = 0 := rfl

@[simp] theorem card_eq_zero {o} : card o = 0 ↔ o = 0 :=
⟨induction_on o $ λ α r _ h, begin
  haveI := cardinal.mk_eq_zero_iff.1 h,
  apply type_eq_zero_of_empty
end, λ e, by simp only [e, card_zero]⟩

@[simp] theorem card_one : card 1 = 1 := rfl

/-! ### Lifting ordinals to a higher universe -/

/-- The universe lift operation for ordinals, which embeds `ordinal.{u}` as
  a proper initial segment of `ordinal.{v}` for `v > u`. For the initial segment version,
  see `lift.initial_seg`. -/
def lift (o : ordinal.{v}) : ordinal.{max v u} :=
quotient.lift_on o (λ w, type $ ulift.down ⁻¹'o w.r) $
  λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨f⟩, quot.sound ⟨(rel_iso.preimage equiv.ulift r).trans $
    f.trans (rel_iso.preimage equiv.ulift s).symm⟩

@[simp] theorem type_ulift (r : α → α → Prop) [is_well_order α r] :
  type (ulift.down ⁻¹'o r) = lift.{v} (type r) :=
rfl

theorem _root_.rel_iso.ordinal_lift_type_eq {α : Type u} {β : Type v}
  {r : α → α → Prop} {s : β → β → Prop} [is_well_order α r] [is_well_order β s] (f : r ≃r s) :
  lift.{v} (type r) = lift.{u} (type s) :=
((rel_iso.preimage equiv.ulift r).trans $
  f.trans (rel_iso.preimage equiv.ulift s).symm).ordinal_type_eq

@[simp] theorem type_lift_preimage {α : Type u} {β : Type v} (r : α → α → Prop) [is_well_order α r]
  (f : β ≃ α) : lift.{u} (type (f ⁻¹'o r)) = lift.{v} (type r) :=
(rel_iso.preimage f r).ordinal_lift_type_eq

/-- `lift.{(max u v) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp] theorem lift_umax : lift.{(max u v) u} = lift.{v u} :=
funext $ λ a, induction_on a $ λ α r _,
quotient.sound ⟨(rel_iso.preimage equiv.ulift r).trans (rel_iso.preimage equiv.ulift r).symm⟩

/-- `lift.{(max v u) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp] theorem lift_umax' : lift.{(max v u) u} = lift.{v u} := lift_umax

/-- An ordinal lifted to a lower or equal universe equals itself. -/
@[simp] theorem lift_id' (a : ordinal) : lift a = a :=
induction_on a $ λ α r _, quotient.sound ⟨rel_iso.preimage equiv.ulift r⟩

/-- An ordinal lifted to the same universe equals itself. -/
@[simp] theorem lift_id : ∀ a, lift.{u u} a = a := lift_id'.{u u}

/-- An ordinal lifted to the zero universe equals itself. -/
@[simp] theorem lift_uzero (a : ordinal.{u}) : lift.{0} a = a := lift_id'.{0 u} a

@[simp] theorem lift_lift (a : ordinal) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
induction_on a $ λ α r _,
quotient.sound ⟨(rel_iso.preimage equiv.ulift _).trans $
  (rel_iso.preimage equiv.ulift _).trans (rel_iso.preimage equiv.ulift _).symm⟩

theorem lift_type_le {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{max v w} (type r) ≤ lift.{max u w} (type s) ↔ nonempty (r ≼i s) :=
⟨λ ⟨f⟩, ⟨(initial_seg.of_iso (rel_iso.preimage equiv.ulift r).symm).trans $
    f.trans (initial_seg.of_iso (rel_iso.preimage equiv.ulift s))⟩,
 λ ⟨f⟩, ⟨(initial_seg.of_iso (rel_iso.preimage equiv.ulift r)).trans $
    f.trans (initial_seg.of_iso (rel_iso.preimage equiv.ulift s).symm)⟩⟩

theorem lift_type_eq {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{max v w} (type r) = lift.{max u w} (type s) ↔ nonempty (r ≃r s) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨(rel_iso.preimage equiv.ulift r).symm.trans $
    f.trans (rel_iso.preimage equiv.ulift s)⟩,
 λ ⟨f⟩, ⟨(rel_iso.preimage equiv.ulift r).trans $
    f.trans (rel_iso.preimage equiv.ulift s).symm⟩⟩

theorem lift_type_lt {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{max v w} (type r) < lift.{max u w} (type s) ↔ nonempty (r ≺i s) :=
by haveI := @rel_embedding.is_well_order _ _ (@equiv.ulift.{max v w} α ⁻¹'o r)
     r (rel_iso.preimage equiv.ulift.{max v w} r) _;
   haveI := @rel_embedding.is_well_order _ _ (@equiv.ulift.{max u w} β ⁻¹'o s)
     s (rel_iso.preimage equiv.ulift.{max u w} s) _; exact
⟨λ ⟨f⟩, ⟨(f.equiv_lt (rel_iso.preimage equiv.ulift r).symm).lt_le
    (initial_seg.of_iso (rel_iso.preimage equiv.ulift s))⟩,
 λ ⟨f⟩, ⟨(f.equiv_lt (rel_iso.preimage equiv.ulift r)).lt_le
    (initial_seg.of_iso (rel_iso.preimage equiv.ulift s).symm)⟩⟩

@[simp] theorem lift_le {a b : ordinal} : lift.{u v} a ≤ lift b ↔ a ≤ b :=
induction_on a $ λ α r _, induction_on b $ λ β s _, by { rw ← lift_umax, exactI lift_type_le }

@[simp] theorem lift_inj {a b : ordinal} : lift a = lift b ↔ a = b :=
by simp only [le_antisymm_iff, lift_le]

@[simp] theorem lift_lt {a b : ordinal} : lift a < lift b ↔ a < b :=
by simp only [lt_iff_le_not_le, lift_le]

@[simp] theorem lift_zero : lift 0 = 0 := type_eq_zero_of_empty _
@[simp] theorem lift_one : lift 1 = 1 := type_eq_one_of_unique _

@[simp] theorem lift_card (a) : (card a).lift = card (lift a) :=
induction_on a $ λ α r _, rfl

theorem lift_down' {a : cardinal.{u}} {b : ordinal.{max u v}}
  (h : card b ≤ a.lift) : ∃ a', lift a' = b :=
let ⟨c, e⟩ := cardinal.lift_down h in
cardinal.induction_on c (λ α, induction_on b $ λ β s _ e', begin
  resetI,
  rw [card_type, ← cardinal.lift_id'.{(max u v) u} (#β),
      ← cardinal.lift_umax.{u v}, lift_mk_eq.{u (max u v) (max u v)}] at e',
  cases e' with f,
  have g := rel_iso.preimage f s,
  haveI := (g : ⇑f ⁻¹'o s ↪r s).is_well_order,
  have := lift_type_eq.{u (max u v) (max u v)}.2 ⟨g⟩,
  rw [lift_id, lift_umax.{u v}] at this,
  exact ⟨_, this⟩
end) e

theorem lift_down {a : ordinal.{u}} {b : ordinal.{max u v}}
  (h : b ≤ lift a) : ∃ a', lift a' = b :=
@lift_down' (card a) _ (by rw lift_card; exact card_le_card h)

theorem le_lift_iff {a : ordinal.{u}} {b : ordinal.{max u v}} :
  b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
⟨λ h, let ⟨a', e⟩ := lift_down h in ⟨a', e, lift_le.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : ordinal.{u}} {b : ordinal.{max u v}} :
  b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
⟨λ h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
      ⟨a', e, lift_lt.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_lt.2 h⟩

/-- Initial segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as an initial segment when `u ≤ v`. -/
def lift.initial_seg : @initial_seg ordinal.{u} ordinal.{max u v} (<) (<) :=
⟨⟨⟨lift.{v}, λ a b, lift_inj.1⟩, λ a b, lift_lt⟩,
  λ a b h, lift_down (le_of_lt h)⟩

@[simp] theorem lift.initial_seg_coe : (lift.initial_seg : ordinal → ordinal) = lift := rfl

/-! ### The first infinite ordinal `omega` -/

/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega : ordinal.{u} := lift $ @type ℕ (<) _

localized "notation (name := ordinal.omega) `ω` := ordinal.omega" in ordinal

/-- Note that the presence of this lemma makes `simp [omega]` form a loop. -/
@[simp] theorem type_nat_lt : @type ℕ (<) _ = ω := (lift_id _).symm

@[simp] theorem card_omega : card ω = ℵ₀ := rfl

@[simp] theorem lift_omega : lift ω = ω := lift_lift _

/-!
### Definition and first properties of addition on ordinals

In this paragraph, we introduce the addition on ordinals, and prove just enough properties to
deduce that the order on ordinals is total (and therefore well-founded). Further properties of
the addition, together with properties of the other operations, are proved in
`ordinal_arithmetic.lean`.
-/

/-- `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. -/
instance : has_add ordinal.{u} :=
⟨λ o₁ o₂, quotient.lift_on₂ o₁ o₂
  (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, by exactI type (sum.lex r s)) $
  λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
  quot.sound ⟨rel_iso.sum_lex_congr f g⟩⟩

instance : add_monoid_with_one ordinal.{u} :=
{ add       := (+),
  zero      := 0,
  one       := 1,
  zero_add  := λ o, induction_on o $ λ α r _, eq.symm $ quotient.sound
    ⟨⟨(empty_sum pempty α).symm, λ a b, sum.lex_inr_inr⟩⟩,
  add_zero  := λ o, induction_on o $ λ α r _, eq.symm $ quotient.sound
    ⟨⟨(sum_empty α pempty).symm, λ a b, sum.lex_inl_inl⟩⟩,
  add_assoc := λ o₁ o₂ o₃, quotient.induction_on₃ o₁ o₂ o₃ $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩, quot.sound
    ⟨⟨sum_assoc _ _ _, λ a b,
    begin rcases a with ⟨a|a⟩|a; rcases b with ⟨b|b⟩|b;
      simp only [sum_assoc_apply_inl_inl, sum_assoc_apply_inl_inr, sum_assoc_apply_inr,
        sum.lex_inl_inl, sum.lex_inr_inr, sum.lex.sep, sum.lex_inr_inl] end⟩⟩ }

@[simp] theorem card_add (o₁ o₂ : ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
induction_on o₁ $ λ α r _, induction_on o₂ $ λ β s _, rfl

@[simp] theorem type_sum_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop)
  [is_well_order α r] [is_well_order β s] : type (sum.lex r s) = type r + type s := rfl

@[simp] theorem card_nat (n : ℕ) : card.{u} n = n :=
by induction n; [refl, simp only [card_add, card_one, nat.cast_succ, *]]

instance add_covariant_class_le : covariant_class ordinal.{u} ordinal.{u} (+) (≤) :=
⟨λ c a b h, begin
  revert h c, exact (
  induction_on a $ λ α₁ r₁ _, induction_on b $ λ α₂ r₂ _ ⟨⟨⟨f, fo⟩, fi⟩⟩ c,
  induction_on c $ λ β s _,
  ⟨⟨⟨(embedding.refl _).sum_map f,
    λ a b, match a, b with
      | sum.inl a, sum.inl b := sum.lex_inl_inl.trans sum.lex_inl_inl.symm
      | sum.inl a, sum.inr b := by apply iff_of_true; apply sum.lex.sep
      | sum.inr a, sum.inl b := by apply iff_of_false; exact sum.lex_inr_inl
      | sum.inr a, sum.inr b := sum.lex_inr_inr.trans $ fo.trans sum.lex_inr_inr.symm
      end⟩,
    λ a b H, match a, b, H with
      | _,         sum.inl b, _ := ⟨sum.inl b, rfl⟩
      | sum.inl a, sum.inr b, H := (sum.lex_inr_inl H).elim
      | sum.inr a, sum.inr b, H := let ⟨w, h⟩ := fi _ _ (sum.lex_inr_inr.1 H) in
          ⟨sum.inr w, congr_arg sum.inr h⟩
    end⟩⟩)
end⟩

instance add_swap_covariant_class_le : covariant_class ordinal.{u} ordinal.{u} (swap (+)) (≤) :=
⟨λ c a b h, begin
  revert h c, exact (
  induction_on a $ λ α₁ r₁ hr₁, induction_on b $ λ α₂ r₂ hr₂ ⟨⟨⟨f, fo⟩, fi⟩⟩ c,
  induction_on c $ λ β s hs, by exactI
  @rel_embedding.ordinal_type_le _ _ (sum.lex r₁ s) (sum.lex r₂ s) _ _
  ⟨f.sum_map (embedding.refl _), λ a b, begin
    split; intro H,
    { cases a with a a; cases b with b b; cases H; constructor; [rwa ← fo, assumption] },
    { cases H; constructor; [rwa fo, assumption] }
  end⟩)
end⟩

theorem le_add_right (a b : ordinal) : a ≤ a + b :=
by simpa only [add_zero] using add_le_add_left (ordinal.zero_le b) a

theorem le_add_left (a b : ordinal) : a ≤ b + a :=
by simpa only [zero_add] using add_le_add_right (ordinal.zero_le b) a

instance : linear_order ordinal :=
{ le_total     := λ a b,
    match lt_or_eq_of_le (le_add_left b a), lt_or_eq_of_le (le_add_right a b) with
    | or.inr h, _ := by rw h; exact or.inl (le_add_right _ _)
    | _, or.inr h := by rw h; exact or.inr (le_add_left _ _)
    | or.inl h₁, or.inl h₂ := induction_on a (λ α₁ r₁ _,
      induction_on b $ λ α₂ r₂ _ ⟨f⟩ ⟨g⟩, begin
        resetI,
        rw [← typein_top f, ← typein_top g, le_iff_lt_or_eq,
            le_iff_lt_or_eq, typein_lt_typein, typein_lt_typein],
        rcases trichotomous_of (sum.lex r₁ r₂) g.top f.top with h|h|h;
        [exact or.inl (or.inl h), {left, right, rw h}, exact or.inr (or.inl h)]
      end) h₁ h₂
    end,
  decidable_le := classical.dec_rel _,
  ..ordinal.partial_order }

instance : well_founded_lt ordinal := ⟨lt_wf⟩
instance : is_well_order ordinal (<) := { }

instance : conditionally_complete_linear_order_bot ordinal :=
is_well_order.conditionally_complete_linear_order_bot _

@[simp] lemma max_zero_left : ∀ a : ordinal, max 0 a = a := max_bot_left
@[simp] lemma max_zero_right : ∀ a : ordinal, max a 0 = a := max_bot_right
@[simp] lemma max_eq_zero {a b : ordinal} : max a b = 0 ↔ a = 0 ∧ b = 0 := max_eq_bot

@[simp] theorem Inf_empty : Inf (∅ : set ordinal) = 0 :=
dif_neg not_nonempty_empty

/- ### Successor order properties -/

private theorem succ_le_iff' {a b : ordinal} : a + 1 ≤ b ↔ a < b :=
⟨lt_of_lt_of_le (induction_on a $ λ α r _, ⟨⟨⟨⟨λ x, sum.inl x, λ _ _, sum.inl.inj⟩,
  λ _ _, sum.lex_inl_inl⟩,
  sum.inr punit.star, λ b, sum.rec_on b
    (λ x, ⟨λ _, ⟨x, rfl⟩, λ _, sum.lex.sep _ _⟩)
    (λ x, sum.lex_inr_inr.trans ⟨false.elim, λ ⟨x, H⟩, sum.inl_ne_inr H⟩)⟩⟩),
induction_on a $ λ α r hr, induction_on b $ λ β s hs ⟨⟨f, t, hf⟩⟩, begin
  haveI := hs,
  refine ⟨⟨@rel_embedding.of_monotone (α ⊕ punit) β _ _ _ _ (sum.rec _ _) (λ a b, _), λ a b, _⟩⟩,
  { exact f }, { exact λ _, t },
  { rcases a with a|_; rcases b with b|_,
    { simpa only [sum.lex_inl_inl] using f.map_rel_iff.2 },
    { intro _, rw hf, exact ⟨_, rfl⟩ },
    { exact false.elim ∘ sum.lex_inr_inl },
    { exact false.elim ∘ sum.lex_inr_inr.1 } },
  { rcases a with a|_,
    { intro h, have := @principal_seg.init _ _ _ _ _ ⟨f, t, hf⟩ _ _ h,
      cases this with w h, exact ⟨sum.inl w, h⟩ },
    { intro h, cases (hf b).1 h with w h, exact ⟨sum.inl w, h⟩ } }
end⟩

instance : no_max_order ordinal := ⟨λ a, ⟨_, succ_le_iff'.1 le_rfl⟩⟩

instance : succ_order ordinal.{u} := succ_order.of_succ_le_iff (λ o, o + 1) (λ a b, succ_le_iff')

@[simp] theorem add_one_eq_succ (o : ordinal) : o + 1 = succ o := rfl

@[simp] theorem succ_zero : succ (0 : ordinal) = 1 := zero_add 1
@[simp] theorem succ_one : succ (1 : ordinal) = 2 := rfl

theorem add_succ (o₁ o₂ : ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
(add_assoc _ _ _).symm

theorem one_le_iff_pos {o : ordinal} : 1 ≤ o ↔ 0 < o :=
by rw [← succ_zero, succ_le_iff]

theorem one_le_iff_ne_zero {o : ordinal} : 1 ≤ o ↔ o ≠ 0 :=
by rw [one_le_iff_pos, ordinal.pos_iff_ne_zero]

theorem succ_pos (o : ordinal) : 0 < succ o := bot_lt_succ o
theorem succ_ne_zero (o : ordinal) : succ o ≠ 0 := ne_of_gt $ succ_pos o
theorem lt_one_iff_zero {a : ordinal} : a < 1 ↔ a = 0 := by simpa using @lt_succ_bot_iff _ _ _ a _ _
theorem le_one_iff {a : ordinal} : a ≤ 1 ↔ a = 0 ∨ a = 1 :=
by simpa using @le_succ_bot_iff _ _ _ a _

@[simp] theorem card_succ (o : ordinal) : card (succ o) = card o + 1 :=
by simp only [←add_one_eq_succ, card_add, card_one]

theorem nat_cast_succ (n : ℕ) : ↑n.succ = succ (n : ordinal) := rfl

instance unique_Iio_one : unique (Iio (1 : ordinal)) :=
{ default := ⟨0, zero_lt_one⟩,
  uniq := λ a, subtype.ext $ lt_one_iff_zero.1 a.prop }

instance unique_out_one : unique (1 : ordinal).out.α :=
{ default := enum (<) 0 (by simp),
  uniq := λ a, begin
    rw ←enum_typein (<) a,
    unfold default,
    congr,
    rw ←lt_one_iff_zero,
    apply typein_lt_self
  end }

theorem one_out_eq (x : (1 : ordinal).out.α) : x = enum (<) 0 (by simp) := unique.eq_default x

/-! ### Extra properties of typein and enum -/

@[simp] theorem typein_one_out (x : (1 : ordinal).out.α) : typein (<) x = 0 :=
by rw [one_out_eq x, typein_enum]

@[simp] lemma typein_le_typein (r : α → α → Prop) [is_well_order α r] {x x' : α} :
  typein r x ≤ typein r x' ↔ ¬r x' x :=
by rw [←not_lt, typein_lt_typein]

@[simp] lemma typein_le_typein' (o : ordinal) {x x' : o.out.α} :
  typein (<) x ≤ typein (<) x' ↔ x ≤ x' :=
by { rw typein_le_typein, exact not_lt }

@[simp] lemma enum_le_enum (r : α → α → Prop) [is_well_order α r] {o o' : ordinal}
  (ho : o < type r) (ho' : o' < type r) : ¬r (enum r o' ho') (enum r o ho) ↔ o ≤ o' :=
by rw [←@not_lt _ _ o' o, enum_lt_enum ho']

@[simp] lemma enum_le_enum' (a : ordinal) {o o' : ordinal}
  (ho : o < type (<)) (ho' : o' < type (<)) : enum (<) o ho ≤ @enum a.out.α (<) _ o' ho' ↔ o ≤ o' :=
by rw [←enum_le_enum (<), ←not_lt]

theorem enum_zero_le {r : α → α → Prop} [is_well_order α r] (h0 : 0 < type r) (a : α) :
  ¬ r a (enum r 0 h0) :=
by { rw [←enum_typein r a, enum_le_enum r], apply ordinal.zero_le }

theorem enum_zero_le' {o : ordinal} (h0 : 0 < o) (a : o.out.α) :
  @enum o.out.α (<) _ 0 (by rwa type_lt) ≤ a :=
by { rw ←not_lt, apply enum_zero_le }

theorem le_enum_succ {o : ordinal} (a : (succ o).out.α) :
  a ≤ @enum (succ o).out.α (<) _ o (by { rw type_lt, exact lt_succ o }) :=
by { rw [←enum_typein (<) a, enum_le_enum', ←lt_succ_iff], apply typein_lt_self }

@[simp] theorem enum_inj {r : α → α → Prop} [is_well_order α r] {o₁ o₂ : ordinal} (h₁ : o₁ < type r)
  (h₂ : o₂ < type r) : enum r o₁ h₁ = enum r o₂ h₂ ↔ o₁ = o₂ :=
⟨λ h, begin
  by_contra hne,
  cases lt_or_gt_of_ne hne with hlt hlt;
    apply (is_well_order.is_irrefl r).1,
    { rwa [←@enum_lt_enum α r _ o₁ o₂ h₁ h₂, h] at hlt },
    { change _ < _ at hlt, rwa [←@enum_lt_enum α r _ o₂ o₁ h₂ h₁, h] at hlt }
end, λ h, by simp_rw h⟩

/-- A well order `r` is order isomorphic to the set of ordinals smaller than `type r`. -/
@[simps] def enum_iso (r : α → α → Prop) [is_well_order α r] : subrel (<) (< type r) ≃r r :=
{ to_fun := λ x, enum r x.1 x.2,
  inv_fun := λ x, ⟨typein r x, typein_lt_type r x⟩,
  left_inv := λ ⟨o, h⟩, subtype.ext_val (typein_enum _ _),
  right_inv := λ h, enum_typein _ _,
  map_rel_iff' := by { rintros ⟨a, _⟩ ⟨b, _⟩, apply enum_lt_enum } }

/-- The order isomorphism between ordinals less than `o` and `o.out.α`. -/
@[simps] noncomputable def enum_iso_out (o : ordinal) : set.Iio o ≃o o.out.α :=
{ to_fun := λ x, enum (<) x.1 $ by { rw type_lt, exact x.2 },
  inv_fun := λ x, ⟨typein (<) x, typein_lt_self x⟩,
  left_inv := λ ⟨o', h⟩, subtype.ext_val (typein_enum _ _),
  right_inv := λ h, enum_typein _ _,
  map_rel_iff' := by { rintros ⟨a, _⟩ ⟨b, _⟩, apply enum_le_enum' } }

/-- `o.out.α` is an `order_bot` whenever `0 < o`. -/
def out_order_bot_of_pos {o : ordinal} (ho : 0 < o) : order_bot o.out.α :=
⟨_, enum_zero_le' ho⟩

theorem enum_zero_eq_bot {o : ordinal} (ho : 0 < o) :
  enum (<) 0 (by rwa type_lt) = by { haveI H := out_order_bot_of_pos ho, exact ⊥ } :=
rfl

/-! ### Universal ordinal -/

/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
@[nolint check_univs] -- intended to be used with explicit universe parameters
def univ : ordinal.{max (u + 1) v} := lift.{v (u+1)} (@type ordinal (<) _)

theorem univ_id : univ.{u (u+1)} = @type ordinal (<) _ := lift_id _

@[simp] theorem lift_univ : lift.{w} univ.{u v} = univ.{u (max v w)} := lift_lift _

theorem univ_umax : univ.{u (max (u+1) v)} = univ.{u v} := congr_fun lift_umax _

/-- Principal segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as a principal segment when `u < v`. -/
def lift.principal_seg : @principal_seg ordinal.{u} ordinal.{max (u+1) v} (<) (<) :=
⟨↑lift.initial_seg.{u (max (u+1) v)}, univ.{u v}, begin
  refine λ b, induction_on b _, introsI β s _,
  rw [univ, ← lift_umax], split; intro h,
  { rw ← lift_id (type s) at h ⊢,
    cases lift_type_lt.1 h with f, cases f with f a hf,
    existsi a, revert hf,
    apply induction_on a, introsI α r _ hf,
    refine lift_type_eq.{u (max (u+1) v) (max (u+1) v)}.2
      ⟨(rel_iso.of_surjective (rel_embedding.of_monotone _ _) _).symm⟩,
    { exact λ b, enum r (f b) ((hf _).2 ⟨_, rfl⟩) },
    { refine λ a b h, (typein_lt_typein r).1 _,
      rw [typein_enum, typein_enum],
      exact f.map_rel_iff.2 h },
    { intro a', cases (hf _).1 (typein_lt_type _ a') with b e,
      existsi b, simp, simp [e] } },
  { cases h with a e, rw [← e],
    apply induction_on a, introsI α r _,
    exact lift_type_lt.{u (u+1) (max (u+1) v)}.2
      ⟨typein.principal_seg r⟩ }
end⟩

@[simp] theorem lift.principal_seg_coe :
  (lift.principal_seg.{u v} : ordinal → ordinal) = lift.{max (u+1) v} := rfl

@[simp] theorem lift.principal_seg_top : lift.principal_seg.top = univ := rfl

theorem lift.principal_seg_top' :
  lift.principal_seg.{u (u+1)}.top = @type ordinal (<) _ :=
by simp only [lift.principal_seg_top, univ_id]

end ordinal

/-! ### Representing a cardinal with an ordinal -/

namespace cardinal
open ordinal

@[simp] theorem mk_ordinal_out (o : ordinal) : #(o.out.α) = o.card :=
(ordinal.card_type _).symm.trans $ by rw ordinal.type_lt

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. For the order-embedding version, see `ord.order_embedding`. -/
def ord (c : cardinal) : ordinal :=
let F := λ α : Type u, ⨅ r : {r // is_well_order α r}, @type α r.1 r.2 in
quot.lift_on c F
begin
  suffices : ∀ {α β}, α ≈ β → F α ≤ F β,
  from λ α β h, (this h).antisymm (this (setoid.symm h)),
  rintros α β ⟨f⟩,
  refine le_cinfi_iff'.2 (λ i, _),
  haveI := @rel_embedding.is_well_order _ _ (f ⁻¹'o i.1) _ ↑(rel_iso.preimage f i.1) i.2,
  exact (cinfi_le' _ (subtype.mk (⇑f ⁻¹'o i.val)
    (@rel_embedding.is_well_order _ _  _ _ ↑(rel_iso.preimage f i.1) i.2))).trans_eq
    (quot.sound ⟨rel_iso.preimage f i.1⟩)
end

lemma ord_eq_Inf (α : Type u) : ord (#α) = ⨅ r : {r // is_well_order α r}, @type α r.1 r.2 :=
rfl

theorem ord_eq (α) : ∃ (r : α → α → Prop) [wo : is_well_order α r], ord (#α) = @type α r wo :=
let ⟨r, wo⟩ := infi_mem (λ r : {r // is_well_order α r}, @type α r.1 r.2) in ⟨r.1, r.2, wo.symm⟩

theorem ord_le_type (r : α → α → Prop) [h : is_well_order α r] : ord (#α) ≤ type r :=
cinfi_le' _ (subtype.mk r h)

theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card :=
induction_on c $ λ α, ordinal.induction_on o $ λ β s _,
let ⟨r, _, e⟩ := ord_eq α in begin
  resetI, simp only [card_type], split; intro h,
  { rw e at h, exact let ⟨f⟩ := h in ⟨f.to_embedding⟩ },
  { cases h with f,
    have g := rel_embedding.preimage f s,
    haveI := rel_embedding.is_well_order g,
    exact le_trans (ord_le_type _) g.ordinal_type_le }
end

theorem gc_ord_card : galois_connection ord card := λ _ _, ord_le

theorem lt_ord {c o} : o < ord c ↔ o.card < c := gc_ord_card.lt_iff_lt

@[simp] theorem card_ord (c) : (ord c).card = c :=
quotient.induction_on c $ λ α,
let ⟨r, _, e⟩ := ord_eq α in by simp only [mk_def, e, card_type]

/-- Galois coinsertion between `cardinal.ord` and `ordinal.card`. -/
def gci_ord_card : galois_coinsertion ord card :=
gc_ord_card.to_galois_coinsertion $ λ c, c.card_ord.le

theorem ord_card_le (o : ordinal) : o.card.ord ≤ o := gc_ord_card.l_u_le _

lemma lt_ord_succ_card (o : ordinal) : o < (succ o.card).ord := lt_ord.2 $ lt_succ _

@[mono] theorem ord_strict_mono : strict_mono ord := gci_ord_card.strict_mono_l
@[mono] theorem ord_mono : monotone ord := gc_ord_card.monotone_l

@[simp] theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ := gci_ord_card.l_le_l_iff
@[simp] theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ := ord_strict_mono.lt_iff_lt
@[simp] theorem ord_zero : ord 0 = 0 := gc_ord_card.l_bot

@[simp] theorem ord_nat (n : ℕ) : ord n = n :=
(ord_le.2 (card_nat n).ge).antisymm begin
  induction n with n IH,
  { apply ordinal.zero_le },
  { exact succ_le_of_lt (IH.trans_lt $ ord_lt_ord.2 $ nat_cast_lt.2 (nat.lt_succ_self n)) }
end

@[simp] theorem ord_one : ord 1 = 1 :=
by simpa using ord_nat 1

@[simp] theorem lift_ord (c) : (ord c).lift = ord (lift c) :=
begin
  refine le_antisymm (le_of_forall_lt (λ a ha, _)) _,
  { rcases ordinal.lt_lift_iff.1 ha with ⟨a, rfl, h⟩,
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← ordinal.lift_lt] },
  { rw [ord_le, ← lift_card, card_ord] }
end

lemma mk_ord_out (c : cardinal) : #c.ord.out.α = c := by simp

lemma card_typein_lt (r : α → α → Prop) [is_well_order α r] (x : α)
  (h : ord (#α) = type r) : card (typein r x) < #α :=
by { rw [←lt_ord, h], apply typein_lt_type }

lemma card_typein_out_lt (c : cardinal) (x : c.ord.out.α) : card (typein (<) x) < c :=
by { rw ←lt_ord, apply typein_lt_self }

lemma ord_injective : injective ord :=
by { intros c c' h, rw [←card_ord c, ←card_ord c', h] }

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
def ord.order_embedding : cardinal ↪o ordinal :=
rel_embedding.order_embedding_of_lt_embedding
  (rel_embedding.of_monotone cardinal.ord $ λ a b, cardinal.ord_lt_ord.2)

@[simp] theorem ord.order_embedding_coe :
  (ord.order_embedding : cardinal → ordinal) = ord := rfl

/-- The cardinal `univ` is the cardinality of ordinal `univ`, or
  equivalently the cardinal of `ordinal.{u}`, or `cardinal.{u}`,
  as an element of `cardinal.{v}` (when `u < v`). -/
@[nolint check_univs] -- intended to be used with explicit universe parameters
def univ := lift.{v (u+1)} (#ordinal)

theorem univ_id : univ.{u (u+1)} = #ordinal := lift_id _

@[simp] theorem lift_univ : lift.{w} univ.{u v} = univ.{u (max v w)} := lift_lift _

theorem univ_umax : univ.{u (max (u+1) v)} = univ.{u v} := congr_fun lift_umax _

theorem lift_lt_univ (c : cardinal) : lift.{(u+1) u} c < univ.{u (u+1)} :=
by simpa only [lift.principal_seg_coe, lift_ord, lift_succ, ord_le, succ_le_iff] using le_of_lt
  (lift.principal_seg.{u (u+1)}.lt_top (succ c).ord)

theorem lift_lt_univ' (c : cardinal) : lift.{(max (u+1) v) u} c < univ.{u v} :=
by simpa only [lift_lift, lift_univ, univ_umax] using
  lift_lt.{_ (max (u+1) v)}.2 (lift_lt_univ c)

@[simp] theorem ord_univ : ord univ.{u v} = ordinal.univ.{u v} :=
le_antisymm (ord_card_le _) $ le_of_forall_lt $ λ o h,
lt_ord.2 begin
  rcases lift.principal_seg.{u v}.down.1
    (by simpa only [lift.principal_seg_coe] using h) with ⟨o', rfl⟩,
  simp only [lift.principal_seg_coe], rw [← lift_card],
  apply lift_lt_univ'
end

theorem lt_univ {c} : c < univ.{u (u+1)} ↔ ∃ c', c = lift.{(u+1) u} c' :=
⟨λ h, begin
  have := ord_lt_ord.2 h,
  rw ord_univ at this,
  cases lift.principal_seg.{u (u+1)}.down.1
    (by simpa only [lift.principal_seg_top]) with o e,
  have := card_ord c,
  rw [← e, lift.principal_seg_coe, ← lift_card] at this,
  exact ⟨_, this.symm⟩
end, λ ⟨c', e⟩, e.symm ▸ lift_lt_univ _⟩

theorem lt_univ' {c} : c < univ.{u v} ↔ ∃ c', c = lift.{(max (u+1) v) u} c' :=
⟨λ h, let ⟨a, e, h'⟩ := lt_lift_iff.1 h in begin
  rw [← univ_id] at h',
  rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩,
  exact ⟨c', by simp only [e.symm, lift_lift]⟩
end, λ ⟨c', e⟩, e.symm ▸ lift_lt_univ' _⟩

theorem small_iff_lift_mk_lt_univ {α : Type u} :
  small.{v} α ↔ cardinal.lift (#α) < univ.{v (max u (v + 1))} :=
begin
  rw lt_univ',
  split,
  { rintro ⟨β, e⟩,
    exact ⟨#β, lift_mk_eq.{u _ (v + 1)}.2 e⟩ },
  { rintro ⟨c, hc⟩,
    exact ⟨⟨c.out, lift_mk_eq.{u _ (v + 1)}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩ }
end

end cardinal

namespace ordinal

@[simp] theorem card_univ : card univ = cardinal.univ := rfl

@[simp] theorem nat_le_card {o} {n : ℕ} : (n : cardinal) ≤ card o ↔ (n : ordinal) ≤ o :=
by rw [← cardinal.ord_le, cardinal.ord_nat]

@[simp] theorem nat_lt_card {o} {n : ℕ} : (n : cardinal) < card o ↔ (n : ordinal) < o :=
by { rw [←succ_le_iff, ←succ_le_iff, ←nat_succ, nat_le_card], refl }

@[simp] theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
lt_iff_lt_of_le_iff_le nat_le_card

@[simp] theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp] theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n :=
by simp only [le_antisymm_iff, card_le_nat, nat_le_card]

@[simp] theorem type_fintype (r : α → α → Prop) [is_well_order α r] [fintype α] :
  type r = fintype.card α :=
by rw [←card_eq_nat, card_type, mk_fintype]

theorem type_fin (n : ℕ) : @type (fin n) (<) _ = n := by simp

end ordinal
