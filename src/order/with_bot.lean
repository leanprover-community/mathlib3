/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.bounded_order
import data.option.n_ary

/-!
# `with_bot`, `with_top`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Adding a `bot` or a `top` to an order.

## Main declarations

* `with_<top/bot> α`: Equips `option α` with the order on `α` plus `none` as the top/bottom element.

 -/

variables {α β γ δ : Type*}

/-- Attach `⊥` to a type. -/
def with_bot (α : Type*) := option α

namespace with_bot

variables {a b : α}

meta instance [has_to_format α] : has_to_format (with_bot α) :=
{ to_format := λ x,
  match x with
  | none := "⊥"
  | (some x) := to_fmt x
  end }

instance [has_repr α] : has_repr (with_bot α) :=
⟨λ o, match o with | none := "⊥" | (some a) := "↑" ++ repr a end⟩

instance : has_coe_t α (with_bot α) := ⟨some⟩
instance : has_bot (with_bot α) := ⟨none⟩

meta instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (with_bot α)
| ⊥ := `(⊥)
| (a : α) := `(coe : α → with_bot α).subst `(a)

instance : inhabited (with_bot α) := ⟨⊥⟩

open function

lemma coe_injective : injective (coe : α → with_bot α) := option.some_injective _
@[norm_cast] lemma coe_inj : (a : with_bot α) = b ↔ a = b := option.some_inj

protected lemma «forall» {p : with_bot α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x := option.forall
protected lemma «exists» {p : with_bot α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x := option.exists

lemma none_eq_bot : (none : with_bot α) = (⊥ : with_bot α) := rfl
lemma some_eq_coe (a : α) : (some a : with_bot α) = (↑a : with_bot α) := rfl

@[simp] lemma bot_ne_coe : ⊥ ≠ (a : with_bot α) .
@[simp] lemma coe_ne_bot : (a : with_bot α) ≠ ⊥ .

/-- Recursor for `with_bot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_eliminator]
def rec_bot_coe {C : with_bot α → Sort*} (h₁ : C ⊥) (h₂ : Π (a : α), C a) :
  Π (n : with_bot α), C n :=
option.rec h₁ h₂

@[simp] lemma rec_bot_coe_bot {C : with_bot α → Sort*} (d : C ⊥) (f : Π (a : α), C a) :
  @rec_bot_coe _ C d f ⊥ = d := rfl
@[simp] lemma rec_bot_coe_coe {C : with_bot α → Sort*} (d : C ⊥) (f : Π (a : α), C a)
  (x : α) : @rec_bot_coe _ C d f ↑x = f x := rfl

/-- Specialization of `option.get_or_else` to values in `with_bot α` that respects API boundaries.
-/
def unbot' (d : α) (x : with_bot α) : α := rec_bot_coe d id x

@[simp] lemma unbot'_bot {α} (d : α) : unbot' d ⊥ = d := rfl
@[simp] lemma unbot'_coe {α} (d x : α) : unbot' d x = x := rfl

@[norm_cast] lemma coe_eq_coe : (a : with_bot α) = b ↔ a = b := option.some_inj

lemma unbot'_eq_iff {d y : α} {x : with_bot α} : unbot' d x = y ↔ x = y ∨ x = ⊥ ∧ y = d :=
by induction x using with_bot.rec_bot_coe; simp [@eq_comm _ d, coe_eq_coe]

@[simp]
theorem unbot'_eq_self_iff {d : α} {x : with_bot α} : unbot' d x = d ↔ x = d ∨ x = ⊥ :=
by simp [unbot'_eq_iff]

theorem unbot'_eq_unbot'_iff {d : α} {x y : with_bot α} :
  unbot' d x = unbot' d y ↔ x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d :=
by induction y using with_bot.rec_bot_coe; simp [unbot'_eq_iff, or_comm, coe_eq_coe]

/-- Lift a map `f : α → β` to `with_bot α → with_bot β`. Implemented using `option.map`. -/
def map (f : α → β) : with_bot α → with_bot β := option.map f

@[simp] lemma map_bot (f : α → β) : map f ⊥ = ⊥ := rfl
@[simp] lemma map_coe (f : α → β) (a : α) : map f a = f a := rfl

lemma map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
  map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
option.map_comm h _

lemma ne_bot_iff_exists {x : with_bot α} : x ≠ ⊥ ↔ ∃ (a : α), ↑a = x := option.ne_none_iff_exists

/-- Deconstruct a `x : with_bot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : Π (x : with_bot α), x ≠ ⊥ → α
| ⊥        h := absurd rfl h
| (some x) h := x

@[simp] lemma coe_unbot (x : with_bot α) (h : x ≠ ⊥) : (x.unbot h : with_bot α) = x :=
by { cases x, simpa using h, refl, }

@[simp] lemma unbot_coe (x : α) (h : (x : with_bot α) ≠ ⊥ := coe_ne_bot) :
  (x : with_bot α).unbot h = x := rfl

instance can_lift : can_lift (with_bot α) α coe (λ r, r ≠ ⊥) :=
{ prf := λ x h, ⟨x.unbot h, coe_unbot _ _⟩ }

section has_le
variables [has_le α]

@[priority 10]
instance : has_le (with_bot α) := ⟨λ o₁ o₂ : option α, ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b⟩

@[simp] lemma some_le_some : @has_le.le (with_bot α) _ (some a) (some b) ↔ a ≤ b := by simp [(≤)]
@[simp, norm_cast] lemma coe_le_coe : (a : with_bot α) ≤ b ↔ a ≤ b := some_le_some

@[simp] lemma none_le {a : with_bot α} : @has_le.le (with_bot α) _ none a :=
λ b h, option.no_confusion h

instance : order_bot (with_bot α) := { bot_le := λ a, none_le, ..with_bot.has_bot }

instance [order_top α] : order_top (with_bot α) :=
{ top := some ⊤,
  le_top := λ o a ha, by cases ha; exact ⟨_, rfl, le_top⟩ }

instance [order_top α] : bounded_order (with_bot α) :=
{ ..with_bot.order_top, ..with_bot.order_bot }

lemma not_coe_le_bot (a : α) : ¬ (a : with_bot α) ≤ ⊥ :=
λ h, let ⟨b, hb, _⟩ := h _ rfl in option.not_mem_none _ hb

lemma coe_le : ∀ {o : option α}, b ∈ o → ((a : with_bot α) ≤ o ↔ a ≤ b) | _ rfl := coe_le_coe

lemma coe_le_iff : ∀ {x : with_bot α}, ↑a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
| (some a) := by simp [some_eq_coe, coe_eq_coe]
| none     := iff_of_false (not_coe_le_bot _) $ by simp [none_eq_bot]

lemma le_coe_iff : ∀ {x : with_bot α}, x ≤ b ↔ ∀ a, x = ↑a → a ≤ b
| (some b) := by simp [some_eq_coe, coe_eq_coe]
| none     := by simp [none_eq_bot]

protected lemma _root_.is_max.with_bot (h : is_max a) : is_max (a : with_bot α)
| none _ := bot_le
| (some b) hb := some_le_some.2 $ h $ some_le_some.1 hb

end has_le

section has_lt
variables [has_lt α]

@[priority 10]
instance : has_lt (with_bot α) := ⟨λ o₁ o₂ : option α, ∃ b ∈ o₂, ∀ a ∈ o₁, a < b⟩

@[simp] lemma some_lt_some : @has_lt.lt (with_bot α) _ (some a) (some b) ↔ a < b := by simp [(<)]
@[simp, norm_cast] lemma coe_lt_coe : (a : with_bot α) < b ↔ a < b := some_lt_some

@[simp] lemma none_lt_some (a : α) : @has_lt.lt (with_bot α) _ none (some a) :=
⟨a, rfl, λ b hb, (option.not_mem_none _ hb).elim⟩
lemma bot_lt_coe (a : α) : (⊥ : with_bot α) < a := none_lt_some a

@[simp] lemma not_lt_none (a : with_bot α) : ¬ @has_lt.lt (with_bot α) _ a none :=
λ ⟨_, h, _⟩, option.not_mem_none _ h

lemma lt_iff_exists_coe : ∀ {a b : with_bot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
| a (some b) := by simp [some_eq_coe, coe_eq_coe]
| a none     := iff_of_false (not_lt_none _) $ by simp [none_eq_bot]

lemma lt_coe_iff : ∀ {x : with_bot α}, x < b ↔ ∀ a, x = ↑a → a < b
| (some b) := by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
| none     := by simp [none_eq_bot, bot_lt_coe]

/-- A version of `bot_lt_iff_ne_bot` for `with_bot` that only requires `has_lt α`, not
`partial_order α`. -/
protected theorem bot_lt_iff_ne_bot : ∀ {x : with_bot α}, ⊥ < x ↔ x ≠ ⊥
| ⊥ := iff_of_false (with_bot.not_lt_none _) (λ h, h rfl)
| (x : α) := by simp [bot_lt_coe]

end has_lt

instance [preorder α] : preorder (with_bot α) :=
{ le          := (≤),
  lt          := (<),
  lt_iff_le_not_le := by { intros, cases a; cases b; simp [lt_iff_le_not_le]; simp [(<), (≤)] },
  le_refl     := λ o a ha, ⟨a, ha, le_rfl⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ a ha,
    let ⟨b, hb, ab⟩ := h₁ a ha, ⟨c, hc, bc⟩ := h₂ b hb in
    ⟨c, hc, le_trans ab bc⟩ }

instance [partial_order α] : partial_order (with_bot α) :=
{ le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₁ with a,
    { cases o₂ with b, {refl},
      rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩,
      rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end,
  .. with_bot.preorder }

lemma coe_strict_mono [preorder α] : strict_mono (coe : α → with_bot α) := λ a b, some_lt_some.2
lemma coe_mono [preorder α] : monotone (coe : α → with_bot α) := λ a b, coe_le_coe.2

lemma monotone_iff [preorder α] [preorder β] {f : with_bot α → β} :
  monotone f ↔ monotone (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
⟨λ h, ⟨h.comp with_bot.coe_mono, λ x, h bot_le⟩,
  λ h, with_bot.forall.2 ⟨with_bot.forall.2 ⟨λ _, le_rfl, λ x _, h.2 x⟩,
  λ x, with_bot.forall.2 ⟨λ h, (not_coe_le_bot _ h).elim, λ y hle, h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[simp] lemma monotone_map_iff [preorder α] [preorder β] {f : α → β} :
  monotone (with_bot.map f) ↔ monotone f :=
monotone_iff.trans $ by simp [monotone]

alias monotone_map_iff ↔ _ _root_.monotone.with_bot_map

lemma strict_mono_iff [preorder α] [preorder β] {f : with_bot α → β} :
  strict_mono f ↔ strict_mono (f ∘ coe : α → β) ∧ ∀ x : α, f ⊥ < f x :=
⟨λ h, ⟨h.comp with_bot.coe_strict_mono, λ x, h (bot_lt_coe _)⟩,
  λ h, with_bot.forall.2 ⟨with_bot.forall.2 ⟨flip absurd (lt_irrefl _), λ x _, h.2 x⟩,
  λ x, with_bot.forall.2 ⟨λ h, (not_lt_bot h).elim, λ y hle, h.1 (coe_lt_coe.1 hle)⟩⟩⟩

@[simp] lemma strict_mono_map_iff [preorder α] [preorder β] {f : α → β} :
  strict_mono (with_bot.map f) ↔ strict_mono f :=
strict_mono_iff.trans $ by simp [strict_mono, bot_lt_coe]

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_bot_map

lemma map_le_iff [preorder α] [preorder β] (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
  ∀ (a b : with_bot α), a.map f ≤ b.map f ↔ a ≤ b
| ⊥       _       := by simp only [map_bot, bot_le]
| (a : α) ⊥       := by simp only [map_coe, map_bot, coe_ne_bot, not_coe_le_bot _]
| (a : α) (b : α) := by simpa only [map_coe, coe_le_coe] using mono_iff

lemma le_coe_unbot' [preorder α] : ∀ (a : with_bot α) (b : α), a ≤ a.unbot' b
| (a : α) b := le_rfl
| ⊥       b := bot_le

lemma unbot'_bot_le_iff [has_le α] [order_bot α] {a : with_bot α} {b : α} :
  a.unbot' ⊥ ≤ b ↔ a ≤ b :=
by cases a; simp [none_eq_bot, some_eq_coe]

lemma unbot'_lt_iff [has_lt α] {a : with_bot α} {b c : α} (ha : a ≠ ⊥) :
  a.unbot' b < c ↔ a < c :=
begin
  lift a to α using ha,
  rw [unbot'_coe, coe_lt_coe]
end

instance [semilattice_sup α] : semilattice_sup (with_bot α) :=
{ sup          := option.lift_or_get (⊔),
  le_sup_left  := λ o₁ o₂ a ha,
    by cases ha; cases o₂; simp [option.lift_or_get],
  le_sup_right := λ o₁ o₂ a ha,
    by cases ha; cases o₁; simp [option.lift_or_get],
  sup_le       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases o₁ with b; cases o₂ with c; cases ha,
    { exact h₂ a rfl },
    { exact h₁ a rfl },
    { rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩,
      simp at h₂,
      exact ⟨d, rfl, sup_le h₁' h₂⟩ }
  end,
  ..with_bot.order_bot,
  ..with_bot.partial_order }

lemma coe_sup [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_bot α) = a ⊔ b := rfl

instance [semilattice_inf α] : semilattice_inf (with_bot α) :=
{ inf          := option.map₂ (⊓),
  inf_le_left  := λ o₁ o₂ a ha, begin
    rcases option.mem_map₂_iff.1 ha with ⟨a, b, (rfl : _ = _), (rfl : _ = _), rfl⟩,
    exact ⟨_, rfl, inf_le_left⟩
  end,
  inf_le_right := λ o₁ o₂ a ha, begin
    rcases option.mem_map₂_iff.1 ha with ⟨a, b, (rfl : _ = _), (rfl : _ = _), rfl⟩,
    exact ⟨_, rfl, inf_le_right⟩
  end,
  le_inf       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases ha,
    rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩,
    rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩,
    exact ⟨_, rfl, le_inf ab ac⟩
  end,
  ..with_bot.order_bot,
  ..with_bot.partial_order }

lemma coe_inf [semilattice_inf α] (a b : α) : ((a ⊓ b : α) : with_bot α) = a ⊓ b := rfl

instance [lattice α] : lattice (with_bot α) :=
{ ..with_bot.semilattice_sup, ..with_bot.semilattice_inf }

instance [distrib_lattice α] : distrib_lattice (with_bot α) :=
{ le_sup_inf := λ o₁ o₂ o₃,
  match o₁, o₂, o₃ with
  | ⊥, ⊥, ⊥ := le_rfl
  | ⊥, ⊥, (a₁ : α) := le_rfl
  | ⊥, (a₁ : α), ⊥ := le_rfl
  | ⊥, (a₁ : α), (a₃ : α) := le_rfl
  | (a₁ : α), ⊥, ⊥ := inf_le_left
  | (a₁ : α), ⊥, (a₃ : α) := inf_le_left
  | (a₁ : α), (a₂ : α), ⊥ := inf_le_right
  | (a₁ : α), (a₂ : α), (a₃ : α) := coe_le_coe.mpr le_sup_inf
  end,
  ..with_bot.lattice }

instance decidable_le [has_le α] [@decidable_rel α (≤)] : @decidable_rel (with_bot α) (≤)
| none x := is_true $ λ a h, option.no_confusion h
| (some x) (some y) :=
  if h : x ≤ y
  then is_true (some_le_some.2 h)
  else is_false $ by simp *
| (some x) none := is_false $ λ h, by rcases h x rfl with ⟨y, ⟨_⟩, _⟩

instance decidable_lt [has_lt α] [@decidable_rel α (<)] : @decidable_rel (with_bot α) (<)
| none (some x) := is_true $ by existsi [x,rfl]; rintros _ ⟨⟩
| (some x) (some y) :=
  if h : x < y
  then is_true $ by simp *
  else is_false $ by simp *
| x none := is_false $ by rintro ⟨a,⟨⟨⟩⟩⟩

instance is_total_le [has_le α] [is_total α (≤)] : is_total (with_bot α) (≤) :=
⟨λ a b, match a, b with
  | none  , _      := or.inl bot_le
  | _     , none   := or.inr bot_le
  | some x, some y := (total_of (≤) x y).imp some_le_some.2 some_le_some.2
  end⟩

instance [linear_order α] : linear_order (with_bot α) := lattice.to_linear_order _

@[norm_cast] -- this is not marked simp because the corresponding with_top lemmas are used
lemma coe_min [linear_order α] (x y : α) : ((min x y : α) : with_bot α) = min x y := rfl

@[norm_cast] -- this is not marked simp because the corresponding with_top lemmas are used
lemma coe_max [linear_order α] (x y : α) : ((max x y : α) : with_bot α) = max x y := rfl

lemma well_founded_lt [preorder α] (h : @well_founded α (<)) : @well_founded (with_bot α) (<) :=
have acc_bot : acc ((<) : with_bot α → with_bot α → Prop) ⊥ :=
  acc.intro _ (λ a ha, (not_le_of_gt ha bot_le).elim),
⟨λ a, option.rec_on a acc_bot (λ a, acc.intro _ (λ b, option.rec_on b (λ _, acc_bot)
(λ b, well_founded.induction h b
  (show ∀ b : α, (∀ c, c < b → (c : with_bot α) < a →
      acc ((<) : with_bot α → with_bot α → Prop) c) → (b : with_bot α) < a →
        acc ((<) : with_bot α → with_bot α → Prop) b,
  from λ b ih hba, acc.intro _ (λ c, option.rec_on c (λ _, acc_bot)
    (λ c hc, ih _ (some_lt_some.1 hc) (lt_trans hc hba)))))))⟩

instance [has_lt α] [densely_ordered α] [no_min_order α] : densely_ordered (with_bot α) :=
⟨ λ a b,
  match a, b with
  | a,      none   := λ h : a < ⊥, (not_lt_none _ h).elim
  | none,   some b := λ h, let ⟨a, ha⟩ := exists_lt b in ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
  | some a, some b := λ h, let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h) in
    ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩
  end⟩

lemma lt_iff_exists_coe_btwn [preorder α] [densely_ordered α] [no_min_order α] {a b : with_bot α} :
  a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
⟨λ h, let ⟨y, hy⟩ := exists_between h, ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1 in ⟨x, hx.1 ▸ hy⟩,
 λ ⟨x, hx⟩, lt_trans hx.1 hx.2⟩

instance [has_le α] [no_top_order α] [nonempty α] : no_top_order (with_bot α) :=
⟨begin
  apply rec_bot_coe,
  { exact ‹nonempty α›.elim (λ a, ⟨a, not_coe_le_bot a⟩) },
  { intro a,
    obtain ⟨b, h⟩ := exists_not_le a,
    exact ⟨b, by rwa coe_le_coe⟩ }
end⟩

instance [has_lt α] [no_max_order α] [nonempty α] : no_max_order (with_bot α) :=
⟨begin
  apply with_bot.rec_bot_coe,
  { apply ‹nonempty α›.elim,
    exact λ a, ⟨a, with_bot.bot_lt_coe a⟩, },
  { intro a,
    obtain ⟨b, ha⟩ := exists_gt a,
    exact ⟨b, with_bot.coe_lt_coe.mpr ha⟩, }
end⟩

end with_bot

--TODO(Mario): Construct using order dual on with_bot
/-- Attach `⊤` to a type. -/
def with_top (α : Type*) := option α

namespace with_top

variables {a b : α}

meta instance [has_to_format α] : has_to_format (with_top α) :=
{ to_format := λ x,
  match x with
  | none := "⊤"
  | (some x) := to_fmt x
  end }

instance [has_repr α] : has_repr (with_top α) :=
⟨λ o, match o with | none := "⊤" | (some a) := "↑" ++ repr a end⟩

instance : has_coe_t α (with_top α) := ⟨some⟩
instance : has_top (with_top α) := ⟨none⟩

meta instance {α : Type} [reflected _ α] [has_reflect α] : has_reflect (with_top α)
| ⊤ := `(⊤)
| (a : α) := `(coe : α → with_top α).subst `(a)

instance : inhabited (with_top α) := ⟨⊤⟩

protected lemma «forall» {p : with_top α → Prop} : (∀ x, p x) ↔ p ⊤ ∧ ∀ x : α, p x := option.forall
protected lemma «exists» {p : with_top α → Prop} : (∃ x, p x) ↔ p ⊤ ∨ ∃ x : α, p x := option.exists

lemma none_eq_top : (none : with_top α) = (⊤ : with_top α) := rfl
lemma some_eq_coe (a : α) : (some a : with_top α) = (↑a : with_top α) := rfl

@[simp] lemma top_ne_coe : ⊤ ≠ (a : with_top α) .
@[simp] lemma coe_ne_top : (a : with_top α) ≠ ⊤ .

/-- Recursor for `with_top` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_eliminator]
def rec_top_coe {C : with_top α → Sort*} (h₁ : C ⊤) (h₂ : Π (a : α), C a) :
  Π (n : with_top α), C n :=
option.rec h₁ h₂

@[simp] lemma rec_top_coe_top {C : with_top α → Sort*} (d : C ⊤) (f : Π (a : α), C a) :
  @rec_top_coe _ C d f ⊤ = d := rfl
@[simp] lemma rec_top_coe_coe {C : with_top α → Sort*} (d : C ⊤) (f : Π (a : α), C a)
  (x : α) : @rec_top_coe _ C d f ↑x = f x := rfl

/-- `with_top.to_dual` is the equivalence sending `⊤` to `⊥` and any `a : α` to `to_dual a : αᵒᵈ`.
See `with_top.to_dual_bot_equiv` for the related order-iso.
-/
protected def to_dual : with_top α ≃ with_bot αᵒᵈ := equiv.refl _
/-- `with_top.of_dual` is the equivalence sending `⊤` to `⊥` and any `a : αᵒᵈ` to `of_dual a : α`.
See `with_top.to_dual_bot_equiv` for the related order-iso.
-/
protected def of_dual : with_top αᵒᵈ ≃ with_bot α := equiv.refl _
/-- `with_bot.to_dual` is the equivalence sending `⊥` to `⊤` and any `a : α` to `to_dual a : αᵒᵈ`.
See `with_bot.to_dual_top_equiv` for the related order-iso.
-/
protected def _root_.with_bot.to_dual : with_bot α ≃ with_top αᵒᵈ := equiv.refl _
/-- `with_bot.of_dual` is the equivalence sending `⊥` to `⊤` and any `a : αᵒᵈ` to `of_dual a : α`.
See `with_bot.to_dual_top_equiv` for the related order-iso.
-/
protected def _root_.with_bot.of_dual : with_bot αᵒᵈ ≃ with_top α := equiv.refl _

@[simp] lemma to_dual_symm_apply (a : with_bot αᵒᵈ) :
  with_top.to_dual.symm a = a.of_dual := rfl
@[simp] lemma of_dual_symm_apply (a : with_bot α) :
  with_top.of_dual.symm a = a.to_dual := rfl

@[simp] lemma to_dual_apply_top : with_top.to_dual (⊤ : with_top α) = ⊥ := rfl
@[simp] lemma of_dual_apply_top : with_top.of_dual (⊤ : with_top α) = ⊥ := rfl

open order_dual

@[simp] lemma to_dual_apply_coe (a : α) : with_top.to_dual (a : with_top α) = to_dual a := rfl
@[simp] lemma of_dual_apply_coe (a : αᵒᵈ) : with_top.of_dual (a : with_top αᵒᵈ) = of_dual a := rfl

/-- Specialization of `option.get_or_else` to values in `with_top α` that respects API boundaries.
-/
def untop' (d : α) (x : with_top α) : α := rec_top_coe d id x

@[simp] lemma untop'_top {α} (d : α) : untop' d ⊤ = d := rfl
@[simp] lemma untop'_coe {α} (d x : α) : untop' d x = x := rfl

@[norm_cast] lemma coe_eq_coe : (a : with_top α) = b ↔ a = b := option.some_inj

lemma untop'_eq_iff {d y : α} {x : with_top α} : untop' d x = y ↔ x = y ∨ x = ⊤ ∧ y = d :=
with_bot.unbot'_eq_iff

@[simp] theorem untop'_eq_self_iff {d : α} {x : with_top α} : untop' d x = d ↔ x = d ∨ x = ⊤ :=
with_bot.unbot'_eq_self_iff

theorem untop'_eq_untop'_iff {d : α} {x y : with_top α} :
  untop' d x = untop' d y ↔ x = y ∨ x = d ∧ y = ⊤ ∨ x = ⊤ ∧ y = d :=
with_bot.unbot'_eq_unbot'_iff

/-- Lift a map `f : α → β` to `with_top α → with_top β`. Implemented using `option.map`. -/
def map (f : α → β) : with_top α → with_top β := option.map f

@[simp] lemma map_top (f : α → β) : map f ⊤ = ⊤ := rfl
@[simp] lemma map_coe (f : α → β) (a : α) : map f a = f a := rfl

lemma map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
  map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
option.map_comm h _

lemma map_to_dual (f : αᵒᵈ → βᵒᵈ) (a : with_bot α) :
  map f (with_bot.to_dual a) = a.map (to_dual ∘ f) := rfl
lemma map_of_dual (f : α → β) (a : with_bot αᵒᵈ) :
  map f (with_bot.of_dual a) = a.map (of_dual ∘ f) := rfl

lemma to_dual_map (f : α → β) (a : with_top α) :
  with_top.to_dual (map f a) = with_bot.map (to_dual ∘ f ∘ of_dual) a.to_dual := rfl
lemma of_dual_map (f : αᵒᵈ → βᵒᵈ) (a : with_top αᵒᵈ) :
  with_top.of_dual (map f a) = with_bot.map (of_dual ∘ f ∘ to_dual) a.of_dual := rfl

lemma ne_top_iff_exists {x : with_top α} : x ≠ ⊤ ↔ ∃ (a : α), ↑a = x := option.ne_none_iff_exists

/-- Deconstruct a `x : with_top α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : Π (x : with_top α), x ≠ ⊤ → α :=
with_bot.unbot

@[simp] lemma coe_untop (x : with_top α) (h : x ≠ ⊤) : (x.untop h : with_top α) = x :=
with_bot.coe_unbot x h

@[simp] lemma untop_coe (x : α) (h : (x : with_top α) ≠ ⊤ := coe_ne_top) :
  (x : with_top α).untop h = x := rfl

instance can_lift : can_lift (with_top α) α coe (λ r, r ≠ ⊤) :=
{ prf := λ x h, ⟨x.untop h, coe_untop _ _⟩ }

section has_le
variables [has_le α]

@[priority 10]
instance : has_le (with_top α) := ⟨λ o₁ o₂ : option α, ∀ a ∈ o₂, ∃ b ∈ o₁, b ≤ a⟩

lemma to_dual_le_iff {a : with_top α} {b : with_bot αᵒᵈ} :
  with_top.to_dual a ≤ b ↔ with_bot.of_dual b ≤ a := iff.rfl
lemma le_to_dual_iff {a : with_bot αᵒᵈ} {b : with_top α} :
  a ≤ with_top.to_dual b ↔ b ≤ with_bot.of_dual a := iff.rfl
@[simp] lemma to_dual_le_to_dual_iff {a b : with_top α} :
  with_top.to_dual a ≤ with_top.to_dual b ↔ b ≤ a := iff.rfl

lemma of_dual_le_iff {a : with_top αᵒᵈ} {b : with_bot α} :
  with_top.of_dual a ≤ b ↔ with_bot.to_dual b ≤ a := iff.rfl
lemma le_of_dual_iff {a : with_bot α} {b : with_top αᵒᵈ} :
  a ≤ with_top.of_dual b ↔ b ≤ with_bot.to_dual a := iff.rfl
@[simp] lemma of_dual_le_of_dual_iff {a b : with_top αᵒᵈ} :
  with_top.of_dual a ≤ with_top.of_dual b ↔ b ≤ a := iff.rfl

@[simp, norm_cast] lemma coe_le_coe : (a : with_top α) ≤ b ↔ a ≤ b :=
by simp only [←to_dual_le_to_dual_iff, to_dual_apply_coe, with_bot.coe_le_coe, to_dual_le_to_dual]

@[simp] lemma some_le_some : @has_le.le (with_top α) _ (some a) (some b) ↔ a ≤ b := coe_le_coe
@[simp] lemma le_none {a : with_top α} : @has_le.le (with_top α) _ a none :=
to_dual_le_to_dual_iff.mp with_bot.none_le

instance : order_top (with_top α) := { le_top := λ a, le_none, .. with_top.has_top }

instance [order_bot α] : order_bot (with_top α) :=
{ bot := some ⊥,
  bot_le := λ o a ha, by cases ha; exact ⟨_, rfl, bot_le⟩ }

instance [order_bot α] : bounded_order (with_top α) :=
{ ..with_top.order_top, ..with_top.order_bot }

lemma not_top_le_coe (a : α) : ¬ (⊤ : with_top α) ≤ ↑a := with_bot.not_coe_le_bot (to_dual a)

lemma le_coe : ∀ {o : option α}, a ∈ o → (@has_le.le (with_top α) _ o b ↔ a ≤ b) | _ rfl :=
coe_le_coe

lemma le_coe_iff {x : with_top α} : x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b :=
by simpa [←to_dual_le_to_dual_iff, with_bot.coe_le_iff]

lemma coe_le_iff {x : with_top α} : ↑a ≤ x ↔ ∀ b, x = ↑b → a ≤ b :=
begin
  simp only [←to_dual_le_to_dual_iff, to_dual_apply_coe, with_bot.le_coe_iff, order_dual.forall,
             to_dual_le_to_dual],
  exact forall₂_congr (λ _ _, iff.rfl)
end

protected lemma _root_.is_min.with_top (h : is_min a) : is_min (a : with_top α) :=
begin
  -- defeq to is_max_to_dual_iff.mp (is_max.with_bot _), but that breaks API boundary
  intros _ hb,
  rw ←to_dual_le_to_dual_iff at hb,
  simpa [to_dual_le_iff] using (is_max.with_bot h : is_max (to_dual a : with_bot αᵒᵈ)) hb
end

end has_le

section has_lt
variables [has_lt α]

@[priority 10]
instance : has_lt (with_top α) := ⟨λ o₁ o₂ : option α, ∃ b ∈ o₁, ∀ a ∈ o₂, b < a⟩

lemma to_dual_lt_iff {a : with_top α} {b : with_bot αᵒᵈ} :
  with_top.to_dual a < b ↔ with_bot.of_dual b < a := iff.rfl
lemma lt_to_dual_iff {a : with_bot αᵒᵈ} {b : with_top α} :
  a < with_top.to_dual b ↔ b < with_bot.of_dual a := iff.rfl
@[simp] lemma to_dual_lt_to_dual_iff {a b : with_top α} :
  with_top.to_dual a < with_top.to_dual b ↔ b < a := iff.rfl

lemma of_dual_lt_iff {a : with_top αᵒᵈ} {b : with_bot α} :
  with_top.of_dual a < b ↔ with_bot.to_dual b < a := iff.rfl
lemma lt_of_dual_iff {a : with_bot α} {b : with_top αᵒᵈ} :
  a < with_top.of_dual b ↔ b < with_bot.to_dual a := iff.rfl
@[simp] lemma of_dual_lt_of_dual_iff {a b : with_top αᵒᵈ} :
  with_top.of_dual a < with_top.of_dual b ↔ b < a := iff.rfl

end has_lt

end with_top

namespace with_bot

open order_dual

@[simp] lemma to_dual_symm_apply (a : with_top αᵒᵈ) : with_bot.to_dual.symm a = a.of_dual := rfl
@[simp] lemma of_dual_symm_apply (a : with_top α) : with_bot.of_dual.symm a = a.to_dual := rfl

@[simp] lemma to_dual_apply_bot : with_bot.to_dual (⊥ : with_bot α) = ⊤ := rfl
@[simp] lemma of_dual_apply_bot : with_bot.of_dual (⊥ : with_bot α) = ⊤ := rfl
@[simp] lemma to_dual_apply_coe (a : α) : with_bot.to_dual (a : with_bot α) = to_dual a := rfl
@[simp] lemma of_dual_apply_coe (a : αᵒᵈ) : with_bot.of_dual (a : with_bot αᵒᵈ) = of_dual a := rfl

lemma map_to_dual (f : αᵒᵈ → βᵒᵈ) (a : with_top α) :
  with_bot.map f (with_top.to_dual a) = a.map (to_dual ∘ f) := rfl
lemma map_of_dual (f : α → β) (a : with_top αᵒᵈ) :
  with_bot.map f (with_top.of_dual a) = a.map (of_dual ∘ f) := rfl
lemma to_dual_map (f : α → β) (a : with_bot α) :
  with_bot.to_dual (with_bot.map f a) = map (to_dual ∘ f ∘ of_dual) a.to_dual := rfl
lemma of_dual_map (f : αᵒᵈ → βᵒᵈ) (a : with_bot αᵒᵈ) :
  with_bot.of_dual (with_bot.map f a) = map (of_dual ∘ f ∘ to_dual) a.of_dual := rfl

section has_le

variables [has_le α] {a b : α}

lemma to_dual_le_iff {a : with_bot α} {b : with_top αᵒᵈ} :
  with_bot.to_dual a ≤ b ↔ with_top.of_dual b ≤ a := iff.rfl
lemma le_to_dual_iff {a : with_top αᵒᵈ} {b : with_bot α} :
  a ≤ with_bot.to_dual b ↔ b ≤ with_top.of_dual a := iff.rfl
@[simp] lemma to_dual_le_to_dual_iff {a b : with_bot α} :
  with_bot.to_dual a ≤ with_bot.to_dual b ↔ b ≤ a := iff.rfl

lemma of_dual_le_iff {a : with_bot αᵒᵈ} {b : with_top α} :
  with_bot.of_dual a ≤ b ↔ with_top.to_dual b ≤ a := iff.rfl
lemma le_of_dual_iff {a : with_top α} {b : with_bot αᵒᵈ} :
  a ≤ with_bot.of_dual b ↔ b ≤ with_top.to_dual a := iff.rfl
@[simp] lemma of_dual_le_of_dual_iff {a b : with_bot αᵒᵈ} :
  with_bot.of_dual a ≤ with_bot.of_dual b ↔ b ≤ a := iff.rfl

end has_le

section has_lt

variables [has_lt α] {a b : α}

lemma to_dual_lt_iff {a : with_bot α} {b : with_top αᵒᵈ} :
  with_bot.to_dual a < b ↔ with_top.of_dual b < a := iff.rfl
lemma lt_to_dual_iff {a : with_top αᵒᵈ} {b : with_bot α} :
  a < with_bot.to_dual b ↔ b < with_top.of_dual a := iff.rfl
@[simp] lemma to_dual_lt_to_dual_iff {a b : with_bot α} :
  with_bot.to_dual a < with_bot.to_dual b ↔ b < a := iff.rfl

lemma of_dual_lt_iff {a : with_bot αᵒᵈ} {b : with_top α} :
  with_bot.of_dual a < b ↔ with_top.to_dual b < a := iff.rfl
lemma lt_of_dual_iff {a : with_top α} {b : with_bot αᵒᵈ} :
  a < with_bot.of_dual b ↔ b < with_top.to_dual a := iff.rfl
@[simp] lemma of_dual_lt_of_dual_iff {a b : with_bot αᵒᵈ} :
  with_bot.of_dual a < with_bot.of_dual b ↔ b < a := iff.rfl

end has_lt

end with_bot

namespace with_top

section has_lt
variables [has_lt α] {a b : α}

open order_dual

@[simp, norm_cast] lemma coe_lt_coe : (a : with_top α) < b ↔ a < b :=
by simp only [←to_dual_lt_to_dual_iff, to_dual_apply_coe, with_bot.coe_lt_coe, to_dual_lt_to_dual]
@[simp] lemma some_lt_some : @has_lt.lt (with_top α) _ (some a) (some b) ↔ a < b := coe_lt_coe

lemma coe_lt_top (a : α) : (a : with_top α) < ⊤ :=
by simpa [←to_dual_lt_to_dual_iff] using with_bot.bot_lt_coe _
@[simp] lemma some_lt_none (a : α) : @has_lt.lt (with_top α) _ (some a) none := coe_lt_top a

@[simp] lemma not_none_lt (a : with_top α) : ¬ @has_lt.lt (with_top α) _ none a :=
begin
  rw [←to_dual_lt_to_dual_iff],
  exact with_bot.not_lt_none _
end

lemma lt_iff_exists_coe {a b : with_top α} : a < b ↔ ∃ p : α, a = p ∧ ↑p < b :=
begin
  rw [←to_dual_lt_to_dual_iff, with_bot.lt_iff_exists_coe, order_dual.exists],
  exact exists_congr (λ _, and_congr_left' iff.rfl)
end

lemma coe_lt_iff {x : with_top α} : ↑a < x ↔ ∀ b, x = ↑b → a < b :=
begin
  simp only [←to_dual_lt_to_dual_iff, with_bot.lt_coe_iff, to_dual_apply_coe, order_dual.forall,
              to_dual_lt_to_dual],
  exact forall₂_congr (λ _ _, iff.rfl)
end

/-- A version of `lt_top_iff_ne_top` for `with_top` that only requires `has_lt α`, not
`partial_order α`. -/
protected theorem lt_top_iff_ne_top {x : with_top α} : x < ⊤ ↔ x ≠ ⊤ :=
@with_bot.bot_lt_iff_ne_bot αᵒᵈ _ x

end has_lt

instance [preorder α] : preorder (with_top α) :=
{ le          := (≤),
  lt          := (<),
  lt_iff_le_not_le := by simp [←to_dual_lt_to_dual_iff, lt_iff_le_not_le],
  le_refl     := λ _, to_dual_le_to_dual_iff.mp le_rfl,
  le_trans    := λ _ _ _, by { simp_rw [←to_dual_le_to_dual_iff], exact function.swap le_trans } }

instance [partial_order α] : partial_order (with_top α) :=
{ le_antisymm := λ _ _, by { simp_rw [←to_dual_le_to_dual_iff], exact function.swap le_antisymm },
  .. with_top.preorder }

lemma coe_strict_mono [preorder α] : strict_mono (coe : α → with_top α) := λ a b, some_lt_some.2
lemma coe_mono [preorder α] : monotone (coe : α → with_top α) := λ a b, coe_le_coe.2

lemma monotone_iff [preorder α] [preorder β] {f : with_top α → β} :
  monotone f ↔ monotone (f ∘ coe : α → β) ∧ ∀ x : α, f x ≤ f ⊤ :=
⟨λ h, ⟨h.comp with_top.coe_mono, λ x, h le_top⟩,
  λ h, with_top.forall.2 ⟨with_top.forall.2 ⟨λ _, le_rfl, λ x h, (not_top_le_coe _ h).elim⟩,
  λ x, with_top.forall.2 ⟨λ _, h.2 x, λ y hle, h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[simp] lemma monotone_map_iff [preorder α] [preorder β] {f : α → β} :
  monotone (with_top.map f) ↔ monotone f :=
monotone_iff.trans $ by simp [monotone]

alias monotone_map_iff ↔ _ _root_.monotone.with_top_map

lemma strict_mono_iff [preorder α] [preorder β] {f : with_top α → β} :
  strict_mono f ↔ strict_mono (f ∘ coe : α → β) ∧ ∀ x : α, f x < f ⊤ :=
⟨λ h, ⟨h.comp with_top.coe_strict_mono, λ x, h (coe_lt_top _)⟩,
  λ h, with_top.forall.2 ⟨with_top.forall.2 ⟨flip absurd (lt_irrefl _), λ x h, (not_top_lt h).elim⟩,
  λ x, with_top.forall.2 ⟨λ _, h.2 x, λ y hle, h.1 (coe_lt_coe.1 hle)⟩⟩⟩

@[simp] lemma strict_mono_map_iff [preorder α] [preorder β] {f : α → β} :
  strict_mono (with_top.map f) ↔ strict_mono f :=
strict_mono_iff.trans $ by simp [strict_mono, coe_lt_top]

alias strict_mono_map_iff ↔ _ _root_.strict_mono.with_top_map

lemma map_le_iff [preorder α] [preorder β] (f : α → β)
  (a b : with_top α) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
  a.map f ≤ b.map f ↔ a ≤ b :=
begin
  rw [←to_dual_le_to_dual_iff, to_dual_map, to_dual_map, with_bot.map_le_iff,
      to_dual_le_to_dual_iff],
  simp [mono_iff]
end

instance [semilattice_inf α] : semilattice_inf (with_top α) :=
{ inf          := option.lift_or_get (⊓),
  inf_le_left  := λ o₁ o₂ a ha,
    by cases ha; cases o₂; simp [option.lift_or_get],
  inf_le_right := λ o₁ o₂ a ha,
    by cases ha; cases o₁; simp [option.lift_or_get],
  le_inf       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases o₂ with b; cases o₃ with c; cases ha,
    { exact h₂ a rfl },
    { exact h₁ a rfl },
    { rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩,
      simp at h₂,
      exact ⟨d, rfl, le_inf h₁' h₂⟩ }
  end,
  ..with_top.partial_order }

lemma coe_inf [semilattice_inf α] (a b : α) : ((a ⊓ b : α) : with_top α) = a ⊓ b := rfl

instance [semilattice_sup α] : semilattice_sup (with_top α) :=
{ sup          := option.map₂ (⊔),
  le_sup_left  := λ o₁ o₂ a ha, begin
    rcases option.mem_map₂_iff.1 ha with ⟨a, b, (rfl : _ = _), (rfl : _ = _), rfl⟩,
    exact ⟨_, rfl, le_sup_left⟩
  end,
  le_sup_right := λ o₁ o₂ a ha, begin
    rcases option.mem_map₂_iff.1 ha with ⟨a, b, (rfl : _ = _), (rfl : _ = _), rfl⟩,
    exact ⟨_, rfl, le_sup_right⟩
  end,
  sup_le       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases ha,
    rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩,
    rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩,
    exact ⟨_, rfl, sup_le ab ac⟩
  end,
  ..with_top.partial_order }

lemma coe_sup [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_top α) = a ⊔ b := rfl

instance [lattice α] : lattice (with_top α) :=
{ ..with_top.semilattice_sup, ..with_top.semilattice_inf }

instance [distrib_lattice α] : distrib_lattice (with_top α) :=
{ le_sup_inf := λ o₁ o₂ o₃,
  match o₁, o₂, o₃ with
  | ⊤, o₂, o₃ := le_rfl
  | (a₁ : α), ⊤, ⊤ := le_rfl
  | (a₁ : α), ⊤, (a₃ : α) := le_rfl
  | (a₁ : α), (a₂ : α), ⊤ := le_rfl
  | (a₁ : α), (a₂ : α), (a₃ : α) := coe_le_coe.mpr le_sup_inf
  end,
  ..with_top.lattice }

instance decidable_le [has_le α] [@decidable_rel α (≤)] : @decidable_rel (with_top α) (≤) :=
λ _ _, decidable_of_decidable_of_iff (with_bot.decidable_le _ _) (to_dual_le_to_dual_iff)

instance decidable_lt [has_lt α] [@decidable_rel α (<)] : @decidable_rel (with_top α) (<) :=
λ _ _, decidable_of_decidable_of_iff (with_bot.decidable_lt _ _) (to_dual_lt_to_dual_iff)

instance is_total_le [has_le α] [is_total α (≤)] : is_total (with_top α) (≤) :=
⟨λ _ _, by { simp_rw ←to_dual_le_to_dual_iff, exact total_of _ _ _ }⟩

instance [linear_order α] : linear_order (with_top α) := lattice.to_linear_order _

@[simp, norm_cast]
lemma coe_min [linear_order α] (x y : α) : (↑(min x y) : with_top α) = min x y := rfl

@[simp, norm_cast]
lemma coe_max [linear_order α] (x y : α) : (↑(max x y) : with_top α) = max x y := rfl

lemma well_founded_lt [preorder α] (h : @well_founded α (<)) : @well_founded (with_top α) (<) :=
have acc_some : ∀ a : α, acc ((<) : with_top α → with_top α → Prop) (some a) :=
λ a, acc.intro _ (well_founded.induction h a
  (show ∀ b, (∀ c, c < b → ∀ d : with_top α, d < some c → acc (<) d) →
    ∀ y : with_top α, y < some b → acc (<) y,
  from λ b ih c, option.rec_on c (λ hc, (not_lt_of_ge le_top hc).elim)
    (λ c hc, acc.intro _ (ih _ (some_lt_some.1 hc))))),
⟨λ a, option.rec_on a (acc.intro _ (λ y, option.rec_on y (λ h, (lt_irrefl _ h).elim)
  (λ _ _, acc_some _))) acc_some⟩

open order_dual

lemma well_founded_gt [preorder α] (h : @well_founded α (>)) : @well_founded (with_top α) (>) :=
⟨λ a, begin
  -- ideally, use rel_hom_class.acc, but that is defined later
  have : acc (<) a.to_dual := well_founded.apply (with_bot.well_founded_lt h) _,
  revert this,
  generalize ha : a.to_dual = b, intro ac,
  induction ac with _ H IH generalizing a, subst ha,
  exact ⟨_, λ a' h, IH (a'.to_dual) (to_dual_lt_to_dual.mpr h) _ rfl⟩
end⟩

lemma _root_.with_bot.well_founded_gt [preorder α] (h : @well_founded α (>)) :
  @well_founded (with_bot α) (>) :=
⟨λ a, begin
  -- ideally, use rel_hom_class.acc, but that is defined later
  have : acc (<) a.to_dual := well_founded.apply (with_top.well_founded_lt h) _,
  revert this,
  generalize ha : a.to_dual = b, intro ac,
  induction ac with _ H IH generalizing a, subst ha,
  exact ⟨_, λ a' h, IH (a'.to_dual) (to_dual_lt_to_dual.mpr h) _ rfl⟩
end⟩

instance trichotomous.lt [preorder α] [is_trichotomous α (<)] : is_trichotomous (with_top α) (<) :=
⟨begin
  rintro (a | _) (b | _),
  iterate 3 { simp },
  simpa [option.some_inj] using @trichotomous _ (<) _ a b
end⟩

instance is_well_order.lt [preorder α] [h : is_well_order α (<)] : is_well_order (with_top α) (<) :=
{ wf := well_founded_lt h.wf }

instance trichotomous.gt [preorder α] [is_trichotomous α (>)] : is_trichotomous (with_top α) (>) :=
⟨begin
  rintro (a | _) (b | _),
  iterate 3 { simp },
  simpa [option.some_inj] using @trichotomous _ (>) _ a b
end⟩

instance is_well_order.gt [preorder α] [h : is_well_order α (>)] : is_well_order (with_top α) (>) :=
{ wf := well_founded_gt h.wf }

instance _root_.with_bot.trichotomous.lt [preorder α] [h : is_trichotomous α (<)] :
  is_trichotomous (with_bot α) (<) :=
@with_top.trichotomous.gt αᵒᵈ _ h

instance _root_.with_bot.is_well_order.lt [preorder α] [h : is_well_order α (<)] :
  is_well_order (with_bot α) (<) :=
@with_top.is_well_order.gt αᵒᵈ _ h

instance _root_.with_bot.trichotomous.gt [preorder α] [h : is_trichotomous α (>)] :
  is_trichotomous (with_bot α) (>) :=
@with_top.trichotomous.lt αᵒᵈ _ h

instance _root_.with_bot.is_well_order.gt [preorder α] [h : is_well_order α (>)] :
  is_well_order (with_bot α) (>) :=
@with_top.is_well_order.lt αᵒᵈ _ h

instance [has_lt α] [densely_ordered α] [no_max_order α] : densely_ordered (with_top α) :=
order_dual.densely_ordered (with_bot αᵒᵈ)

lemma lt_iff_exists_coe_btwn [preorder α] [densely_ordered α] [no_max_order α] {a b : with_top α} :
  a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
⟨λ h, let ⟨y, hy⟩ := exists_between h, ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2 in ⟨x, hx.1 ▸ hy⟩,
 λ ⟨x, hx⟩, lt_trans hx.1 hx.2⟩

instance [has_le α] [no_bot_order α] [nonempty α] : no_bot_order (with_top α) :=
order_dual.no_bot_order (with_bot αᵒᵈ)

instance [has_lt α] [no_min_order α] [nonempty α] : no_min_order (with_top α) :=
order_dual.no_min_order (with_bot αᵒᵈ)

end with_top
