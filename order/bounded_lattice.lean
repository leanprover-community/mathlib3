/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Defines bounded lattice type class hierarchy.

Includes the Prop and fun instances.
-/

import order.lattice data.option
       tactic.pi_instances

set_option old_structure_cmd true

universes u v

namespace lattice
variable {α : Type u}

/-- Typeclass for the `⊤` (`\top`) notation -/
class has_top (α : Type u) := (top : α)
/-- Typeclass for the `⊥` (`\bot`) notation -/
class has_bot (α : Type u) := (bot : α)

notation `⊤` := has_top.top _
notation `⊥` := has_bot.bot _

/-- An `order_top` is a partial order with a maximal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_top (α : Type u) extends has_top α, partial_order α :=
(le_top : ∀ a : α, a ≤ ⊤)

section order_top
variables [order_top α] {a b : α}

@[simp] theorem le_top : a ≤ ⊤ :=
order_top.le_top a

theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
le_antisymm le_top h

-- TODO: delete in favor of the next?
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
⟨assume eq, eq.symm ▸ le_refl ⊤, top_unique⟩

@[simp] theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
⟨top_unique, λ h, h.symm ▸ le_refl ⊤⟩

@[simp] theorem not_top_lt : ¬ ⊤ < a :=
assume h, lt_irrefl a (lt_of_le_of_lt le_top h)

theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
top_le_iff.1 $ h₂ ▸ h

end order_top

theorem order_top.ext_top {α} {A B : order_top α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) :
  (by haveI := A; exact ⊤ : α) = ⊤ :=
top_unique $ by rw ← H; apply le_top

theorem order_top.ext {α} {A B : order_top α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  haveI this := partial_order.ext H,
  have tt := order_top.ext_top H,
  cases A; cases B; injection this; congr'
end

/-- An `order_bot` is a partial order with a minimal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_bot (α : Type u) extends has_bot α, partial_order α :=
(bot_le : ∀ a : α, ⊥ ≤ a)

section order_bot
variables [order_bot α] {a b : α}

@[simp] theorem bot_le : ⊥ ≤ a := order_bot.bot_le a

theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
le_antisymm h bot_le

-- TODO: delete?
theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
⟨assume eq, eq.symm ▸ le_refl ⊥, bot_unique⟩

@[simp] theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
⟨bot_unique, assume h, h.symm ▸ le_refl ⊥⟩

@[simp] theorem not_lt_bot : ¬ a < ⊥ :=
assume h, lt_irrefl a (lt_of_lt_of_le h bot_le)

theorem neq_bot_of_le_neq_bot {a b : α} (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
assume ha, hb $ bot_unique $ ha ▸ hab

theorem eq_bot_mono (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ :=
le_bot_iff.1 $ h₂ ▸ h

end order_bot

theorem order_bot.ext_bot {α} {A B : order_bot α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) :
  (by haveI := A; exact ⊥ : α) = ⊥ :=
bot_unique $ by rw ← H; apply bot_le

theorem order_bot.ext {α} {A B : order_bot α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  haveI this := partial_order.ext H,
  have tt := order_bot.ext_bot H,
  cases A; cases B; injection this; congr'
end

/-- A `semilattice_sup_top` is a semilattice with top and join. -/
class semilattice_sup_top (α : Type u) extends order_top α, semilattice_sup α

section semilattice_sup_top
variables [semilattice_sup_top α] {a : α}

@[simp] theorem top_sup_eq : ⊤ ⊔ a = ⊤ :=
sup_of_le_left le_top

@[simp] theorem sup_top_eq : a ⊔ ⊤ = ⊤ :=
sup_of_le_right le_top

end semilattice_sup_top

/-- A `semilattice_sup_bot` is a semilattice with bottom and join. -/
class semilattice_sup_bot (α : Type u) extends order_bot α, semilattice_sup α

section semilattice_sup_bot
variables [semilattice_sup_bot α] {a b : α}

@[simp] theorem bot_sup_eq : ⊥ ⊔ a = a :=
sup_of_le_right bot_le

@[simp] theorem sup_bot_eq : a ⊔ ⊥ = a :=
sup_of_le_left bot_le

@[simp] theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ (a = ⊥ ∧ b = ⊥) :=
by rw [eq_bot_iff, sup_le_iff]; simp

end semilattice_sup_bot

instance nat.semilattice_sup_bot : semilattice_sup_bot ℕ :=
{ bot := 0, bot_le := nat.zero_le, .. nat.distrib_lattice }

/-- A `semilattice_inf_top` is a semilattice with top and meet. -/
class semilattice_inf_top (α : Type u) extends order_top α, semilattice_inf α

section semilattice_inf_top
variables [semilattice_inf_top α] {a b : α}

@[simp] theorem top_inf_eq : ⊤ ⊓ a = a :=
inf_of_le_right le_top

@[simp] theorem inf_top_eq : a ⊓ ⊤ = a :=
inf_of_le_left le_top

@[simp] theorem inf_eq_top_iff : a ⊓ b = ⊤ ↔ (a = ⊤ ∧ b = ⊤) :=
by rw [eq_top_iff, le_inf_iff]; simp

end semilattice_inf_top

/-- A `semilattice_inf_bot` is a semilattice with bottom and meet. -/
class semilattice_inf_bot (α : Type u) extends order_bot α, semilattice_inf α

section semilattice_inf_bot
variables [semilattice_inf_bot α] {a : α}

@[simp] theorem bot_inf_eq : ⊥ ⊓ a = ⊥ :=
inf_of_le_left bot_le

@[simp] theorem inf_bot_eq : a ⊓ ⊥ = ⊥ :=
inf_of_le_right bot_le

end semilattice_inf_bot

/- Bounded lattices -/

/-- A bounded lattice is a lattice with a top and bottom element,
  denoted `⊤` and `⊥` respectively. This allows for the interpretation
  of all finite suprema and infima, taking `inf ∅ = ⊤` and `sup ∅ = ⊥`. -/
class bounded_lattice (α : Type u) extends lattice α, order_top α, order_bot α

instance semilattice_inf_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_inf_top α :=
{ le_top := assume x, @le_top α _ x, ..bl }

instance semilattice_inf_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_inf_bot α :=
{ bot_le := assume x, @bot_le α _ x, ..bl }

instance semilattice_sup_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_sup_top α :=
{ le_top := assume x, @le_top α _ x, ..bl }

instance semilattice_sup_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_sup_bot α :=
{ bot_le := assume x, @bot_le α _ x, ..bl }

theorem bounded_lattice.ext {α} {A B : bounded_lattice α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  haveI H1 : @bounded_lattice.to_lattice α A =
             @bounded_lattice.to_lattice α B := lattice.ext H,
  haveI H2 := order_bot.ext H,
  haveI H3 : @bounded_lattice.to_order_top α A =
             @bounded_lattice.to_order_top α B := order_top.ext H,
  have tt := order_bot.ext_bot H,
  cases A; cases B; injection H1; injection H2; injection H3; congr'
end

/-- A bounded distributive lattice is exactly what it sounds like. -/
class bounded_distrib_lattice α extends distrib_lattice α, bounded_lattice α

lemma inf_eq_bot_iff_le_compl {α : Type u} [bounded_distrib_lattice α] {a b c : α}
  (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) : a ⊓ b = ⊥ ↔ a ≤ c :=
⟨assume : a ⊓ b = ⊥,
  calc a ≤ a ⊓ (b ⊔ c) : by simp [h₁]
    ... = (a ⊓ b) ⊔ (a ⊓ c) : by simp [inf_sup_left]
    ... ≤ c : by simp [this, inf_le_right],
  assume : a ≤ c,
  bot_unique $
    calc a ⊓ b ≤ b ⊓ c : by rw [inf_comm]; exact inf_le_inf (le_refl _) this
      ... = ⊥ : h₂⟩

/- Prop instance -/
instance bounded_lattice_Prop : bounded_lattice Prop :=
{ lattice.bounded_lattice .
  le           := λa b, a → b,
  le_refl      := assume _, id,
  le_trans     := assume a b c f g, g ∘ f,
  le_antisymm  := assume a b Hab Hba, propext ⟨Hab, Hba⟩,

  sup          := or,
  le_sup_left  := @or.inl,
  le_sup_right := @or.inr,
  sup_le       := assume a b c, or.rec,

  inf          := and,
  inf_le_left  := @and.left,
  inf_le_right := @and.right,
  le_inf       := assume a b c Hab Hac Ha, and.intro (Hab Ha) (Hac Ha),

  top          := true,
  le_top       := assume a Ha, true.intro,

  bot          := false,
  bot_le       := @false.elim }

section logic
variable [preorder α]

theorem monotone_and {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λx, p x ∧ q x) :=
assume a b h, and.imp (m_p h) (m_q h)
-- Note: by finish [monotone] doesn't work

theorem monotone_or {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λx, p x ∨ q x) :=
assume a b h, or.imp (m_p h) (m_q h)
end logic

/- Function lattices -/

/- TODO:
 * build up the lattice hierarchy for `fun`-functor piecewise. semilattic_*, bounded_lattice, lattice ...
 * can this be generalized to the dependent function space?
-/
instance pi.bounded_lattice {α : Type u} {β : Type v} [bounded_lattice β] :
  bounded_lattice (α → β) :=
by pi_instance

end lattice

def with_bot (α : Type*) := option α

namespace with_bot
variable {α : Type u}
open lattice

instance : has_coe_t α (with_bot α) := ⟨some⟩
instance has_bot : has_bot (with_bot α) := ⟨none⟩

lemma none_eq_bot : (none : with_bot α) = (⊥ : with_bot α) := rfl
lemma some_eq_coe (a : α) : (some a : with_bot α) = (↑a : with_bot α) := rfl

theorem coe_eq_coe {a b : α} : (a : with_bot α) = b ↔ a = b :=
by rw [← option.some.inj_eq a b]; refl

instance partial_order [partial_order α] : partial_order (with_bot α) :=
{ le          := λ o₁ o₂ : option α, ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b,
  le_refl     := λ o a ha, ⟨a, ha, le_refl _⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ a ha,
    let ⟨b, hb, ab⟩ := h₁ a ha, ⟨c, hc, bc⟩ := h₂ b hb in
    ⟨c, hc, le_trans ab bc⟩,
  le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₁ with a,
    { cases o₂ with b, {refl},
      rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩,
      rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end }

instance order_bot [partial_order α] : order_bot (with_bot α) :=
{ bot_le := λ a a' h, option.no_confusion h,
  ..with_bot.partial_order, ..with_bot.has_bot }

@[simp] theorem coe_le_coe [partial_order α] {a b : α} :
  (a : with_bot α) ≤ b ↔ a ≤ b :=
⟨λ h, by rcases h a rfl with ⟨_, ⟨⟩, h⟩; exact h,
 λ h a' e, option.some_inj.1 e ▸ ⟨b, rfl, h⟩⟩

@[simp] theorem some_le_some [partial_order α] {a b : α} :
  @has_le.le (with_bot α) _ (some a) (some b) ↔ a ≤ b := coe_le_coe

theorem coe_le [partial_order α] {a b : α} :
  ∀ {o : option α}, b ∈ o → ((a : with_bot α) ≤ o ↔ a ≤ b)
| _ rfl := coe_le_coe

@[simp] theorem some_lt_some [partial_order α] {a b : α} :
  @has_lt.lt (with_bot α) _ (some a) (some b) ↔ a < b :=
(and_congr some_le_some (not_congr some_le_some))
  .trans lt_iff_le_not_le.symm

lemma coe_lt_coe [partial_order α] {a b : α} : (a : with_bot α) < b ↔ a < b := some_lt_some

lemma bot_lt_some [partial_order α] (a : α) : (⊥ : with_bot α) < some a :=
lt_of_le_of_ne bot_le (λ h, option.no_confusion h)

lemma bot_lt_coe [partial_order α] (a : α) : (⊥ : with_bot α) < a := bot_lt_some a

instance linear_order [linear_order α] : linear_order (with_bot α) :=
{ le_total := λ o₁ o₂, begin
    cases o₁ with a, {exact or.inl bot_le},
    cases o₂ with b, {exact or.inr bot_le},
    simp [le_total]
  end,
  ..with_bot.partial_order }

instance decidable_linear_order [decidable_linear_order α] : decidable_linear_order (with_bot α) :=
{ decidable_le := λ a b, begin
    cases a with a,
    { exact is_true bot_le },
    cases b with b,
    { exact is_false (mt (le_antisymm bot_le) (by simp)) },
    { exact decidable_of_iff _ some_le_some }
  end,
  ..with_bot.linear_order }

instance semilattice_sup [semilattice_sup α] : semilattice_sup_bot (with_bot α) :=
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
  ..with_bot.order_bot }

instance semilattice_inf [semilattice_inf α] : semilattice_inf_bot (with_bot α) :=
{ inf          := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a ⊓ b)),
  inf_le_left  := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, inf_le_left⟩
  end,
  inf_le_right := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, inf_le_right⟩
  end,
  le_inf       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases ha,
    rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩,
    rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩,
    exact ⟨_, rfl, le_inf ab ac⟩
  end,
  ..with_bot.order_bot }

instance lattice [lattice α] : lattice (with_bot α) :=
{ ..with_bot.semilattice_sup, ..with_bot.semilattice_inf }

theorem lattice_eq_DLO [decidable_linear_order α] :
  lattice.lattice_of_decidable_linear_order = @with_bot.lattice α _ :=
lattice.ext $ λ x y, iff.rfl

theorem sup_eq_max [decidable_linear_order α] (x y : with_bot α) : x ⊔ y = max x y :=
by rw [← sup_eq_max, lattice_eq_DLO]

theorem inf_eq_min [decidable_linear_order α] (x y : with_bot α) : x ⊓ y = min x y :=
by rw [← inf_eq_min, lattice_eq_DLO]

instance order_top [order_top α] : order_top (with_bot α) :=
{ top := some ⊤,
  le_top := λ o a ha, by cases ha; exact ⟨_, rfl, le_top⟩,
  ..with_bot.partial_order }

instance bounded_lattice [bounded_lattice α] : bounded_lattice (with_bot α) :=
{ ..with_bot.lattice, ..with_bot.order_top, ..with_bot.order_bot }

lemma well_founded_lt [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_bot α → with_bot α → Prop) :=
have acc_bot : acc ((<) : with_bot α → with_bot α → Prop) ⊥ :=
  acc.intro _ (λ a ha, (not_le_of_gt ha bot_le).elim),
⟨λ a, option.rec_on a acc_bot (λ a, acc.intro _ (λ b, option.rec_on b (λ _, acc_bot)
(λ b, well_founded.induction h b
  (show ∀ b : α, (∀ c, c < b → (c : with_bot α) < a →
      acc ((<) : with_bot α → with_bot α → Prop) c) → (b : with_bot α) < a →
        acc ((<) : with_bot α → with_bot α → Prop) b,
  from λ b ih hba, acc.intro _ (λ c, option.rec_on c (λ _, acc_bot)
    (λ c hc, ih _ (some_lt_some.1 hc) (lt_trans hc hba)))))))⟩

instance densely_ordered [partial_order α] [densely_ordered α] [no_bot_order α] :
  densely_ordered (with_bot α) :=
⟨ assume a b,
  match a, b with
  | a,      none   := assume h : a < ⊥, (not_lt_bot h).elim
  | none,   some b := assume h, let ⟨a, ha⟩ := no_bot b in ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
  | some a, some b := assume h, let ⟨a, ha₁, ha₂⟩ := dense (coe_lt_coe.1 h) in
    ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩
  end⟩

end with_bot

--TODO(Mario): Construct using order dual on with_bot
def with_top (α : Type*) := option α

namespace with_top
variable {α : Type u}
open lattice

instance : has_coe_t α (with_top α) := ⟨some⟩
instance has_top : has_top (with_top α) := ⟨none⟩

lemma none_eq_top : (none : with_top α) = (⊤ : with_top α) := rfl
lemma some_eq_coe (a : α) : (some a : with_top α) = (↑a : with_top α) := rfl

theorem coe_eq_coe {a b : α} : (a : with_top α) = b ↔ a = b :=
by rw [← option.some.inj_eq a b]; refl

@[simp] theorem top_ne_coe [partial_order α] {a : α} : ⊤ ≠ (a : with_top α) .
@[simp] theorem coe_ne_top [partial_order α] {a : α} : (a : with_top α) ≠ ⊤ .

instance partial_order [partial_order α] : partial_order (with_top α) :=
{ le          := λ o₁ o₂ : option α, ∀ b ∈ o₂, ∃ a ∈ o₁, a ≤ b,
  le_refl     := λ o a ha, ⟨a, ha, le_refl _⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ c hc,
    let ⟨b, hb, bc⟩ := h₂ c hc, ⟨a, ha, ab⟩ := h₁ b hb in
    ⟨a, ha, le_trans ab bc⟩,
  le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₂ with b,
    { cases o₁ with a, {refl},
      rcases h₂ a rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ b rfl with ⟨a, ⟨⟩, h₁'⟩,
      rcases h₂ a rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end }

instance order_top [partial_order α] : order_top (with_top α) :=
{ le_top := λ a a' h, option.no_confusion h,
  ..with_top.partial_order, .. with_top.has_top }

@[simp] theorem coe_le_coe [partial_order α] {a b : α} :
  (a : with_top α) ≤ b ↔ a ≤ b :=
⟨λ h, by rcases h b rfl with ⟨_, ⟨⟩, h⟩; exact h,
 λ h a' e, option.some_inj.1 e ▸ ⟨a, rfl, h⟩⟩

@[simp] theorem some_le_some [partial_order α] {a b : α} :
  @has_le.le (with_top α) _ (some a) (some b) ↔ a ≤ b := coe_le_coe

theorem le_coe [partial_order α] {a b : α} :
  ∀ {o : option α}, a ∈ o →
  (@has_le.le (with_top α) _ o b ↔ a ≤ b)
| _ rfl := coe_le_coe

theorem le_coe_iff [partial_order α] (b : α) : ∀(x : with_top α), x ≤ b ↔ (∃a:α, x = a ∧ a ≤ b)
| (some a) := by simp [some_eq_coe, coe_eq_coe]
| none     := by simp [none_eq_top]

theorem coe_le_iff [partial_order α] (a : α) : ∀(x : with_top α), ↑a ≤ x ↔ (∀b:α, x = ↑b → a ≤ b)
| (some b) := by simp [some_eq_coe, coe_eq_coe]
| none     := by simp [none_eq_top]

theorem lt_iff_exists_coe [partial_order α] : ∀(a b : with_top α), a < b ↔ (∃p:α, a = p ∧ ↑p < b)
| (some a) b := by simp [some_eq_coe, coe_eq_coe]
| none     b := by simp [none_eq_top]

@[simp] theorem some_lt_some [partial_order α] {a b : α} :
  @has_lt.lt (with_top α) _ (some a) (some b) ↔ a < b :=
(and_congr some_le_some (not_congr some_le_some))
  .trans lt_iff_le_not_le.symm

lemma coe_lt_coe [partial_order α] {a b : α} : (a : with_top α) < b ↔ a < b := some_lt_some

lemma coe_lt_top [partial_order α] (a : α) : (a : with_top α) < ⊤ :=
lt_of_le_of_ne le_top (λ h, option.no_confusion h)

lemma not_top_le_coe [partial_order α] (a : α) : ¬ (⊤:with_top α) ≤ ↑a :=
assume h, (lt_irrefl ⊤ (lt_of_le_of_lt h (coe_lt_top a))).elim

instance linear_order [linear_order α] : linear_order (with_top α) :=
{ le_total := λ o₁ o₂, begin
    cases o₁ with a, {exact or.inr le_top},
    cases o₂ with b, {exact or.inl le_top},
    simp [le_total]
  end,
  ..with_top.partial_order }

instance decidable_linear_order [decidable_linear_order α] : decidable_linear_order (with_top α) :=
{ decidable_le := λ a b, begin
    cases b with b,
    { exact is_true le_top },
    cases a with a,
    { exact is_false (mt (le_antisymm le_top) (by simp)) },
    { exact decidable_of_iff _ some_le_some }
  end,
  ..with_top.linear_order }

instance semilattice_inf [semilattice_inf α] : semilattice_inf_top (with_top α) :=
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
  ..with_top.order_top }

lemma coe_inf [semilattice_inf α] (a b : α) : ((a ⊓ b : α) : with_top α) = a ⊓ b := rfl

instance semilattice_sup [semilattice_sup α] : semilattice_sup_top (with_top α) :=
{ sup          := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a ⊔ b)),
  le_sup_left  := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, le_sup_left⟩
  end,
  le_sup_right := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, le_sup_right⟩
  end,
  sup_le       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases ha,
    rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩,
    rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩,
    exact ⟨_, rfl, sup_le ab ac⟩
  end,
  ..with_top.order_top }

lemma coe_sup [semilattice_sup α] (a b : α) : ((a ⊔ b : α) : with_top α) = a ⊔ b := rfl

instance lattice [lattice α] : lattice (with_top α) :=
{ ..with_top.semilattice_sup, ..with_top.semilattice_inf }

theorem lattice_eq_DLO [decidable_linear_order α] :
  lattice.lattice_of_decidable_linear_order = @with_top.lattice α _ :=
lattice.ext $ λ x y, iff.rfl

theorem sup_eq_max [decidable_linear_order α] (x y : with_top α) : x ⊔ y = max x y :=
by rw [← sup_eq_max, lattice_eq_DLO]

theorem inf_eq_min [decidable_linear_order α] (x y : with_top α) : x ⊓ y = min x y :=
by rw [← inf_eq_min, lattice_eq_DLO]

instance order_bot [order_bot α] : order_bot (with_top α) :=
{ bot := some ⊥,
  bot_le := λ o a ha, by cases ha; exact ⟨_, rfl, bot_le⟩,
  ..with_top.partial_order }

instance bounded_lattice [bounded_lattice α] : bounded_lattice (with_top α) :=
{ ..with_top.lattice, ..with_top.order_top, ..with_top.order_bot }

lemma well_founded_lt {α : Type*} [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_top α → with_top α → Prop) :=
have acc_some : ∀ a : α, acc ((<) : with_top α → with_top α → Prop) (some a) :=
λ a, acc.intro _ (well_founded.induction h a
  (show ∀ b, (∀ c, c < b → ∀ d : with_top α, d < some c → acc (<) d) →
    ∀ y : with_top α, y < some b → acc (<) y,
  from λ b ih c, option.rec_on c (λ hc, (not_lt_of_ge lattice.le_top hc).elim)
    (λ c hc, acc.intro _ (ih _ (some_lt_some.1 hc))))),
⟨λ a, option.rec_on a (acc.intro _ (λ y, option.rec_on y (λ h, (lt_irrefl _ h).elim)
  (λ _ _, acc_some _))) acc_some⟩

instance densely_ordered [partial_order α] [densely_ordered α] [no_top_order α] :
  densely_ordered (with_top α) :=
⟨ assume a b,
  match a, b with
  | none,   a   := assume h : ⊤ < a, (not_top_lt h).elim
  | some a, none := assume h, let ⟨b, hb⟩ := no_top a in ⟨b, coe_lt_coe.2 hb, coe_lt_top b⟩
  | some a, some b := assume h, let ⟨a, ha₁, ha₂⟩ := dense (coe_lt_coe.1 h) in
    ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩
  end⟩

end with_top

namespace order_dual
open lattice
variable (α : Type*)

instance [has_bot α] : has_top (order_dual α) := ⟨(⊥ : α)⟩
instance [has_top α] : has_bot (order_dual α) := ⟨(⊤ : α)⟩

instance [order_bot α] : order_top (order_dual α) :=
{ le_top := @bot_le α _,
  .. order_dual.partial_order α, .. order_dual.lattice.has_top α }

instance [order_top α] : order_bot (order_dual α) :=
{ bot_le := @le_top α _,
  .. order_dual.partial_order α, .. order_dual.lattice.has_bot α }

instance [semilattice_inf_bot α] : semilattice_sup_top (order_dual α) :=
{ .. order_dual.lattice.semilattice_sup α, .. order_dual.lattice.order_top α }

instance [semilattice_inf_top α] : semilattice_sup_bot (order_dual α) :=
{ .. order_dual.lattice.semilattice_sup α, .. order_dual.lattice.order_bot α }

instance [semilattice_sup_bot α] : semilattice_inf_top (order_dual α) :=
{ .. order_dual.lattice.semilattice_inf α, .. order_dual.lattice.order_top α }

instance [semilattice_sup_top α] : semilattice_inf_bot (order_dual α) :=
{ .. order_dual.lattice.semilattice_inf α, .. order_dual.lattice.order_bot α }

instance [bounded_lattice α] : bounded_lattice (order_dual α) :=
{ .. order_dual.lattice.lattice α, .. order_dual.lattice.order_top α, .. order_dual.lattice.order_bot α }

end order_dual