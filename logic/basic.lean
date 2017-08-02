/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Theorems that require decidability hypotheses are in the namespace "decidable".
Classical versions are in the namespace "classical".

Note: in the presence of automation, this whole file may be unnecessary. On the other hand,
maybe it is useful for writing automation.
-/

/-
    miscellany

    TODO: move elsewhere
-/

section miscellany

universes u v
variables {α : Type u} {β : Type v}

theorem eq_iff_le_and_le {α : Type u} [partial_order α] {a b : α} : a = b ↔ (a ≤ b ∧ b ≤ a) :=
⟨assume eq, eq ▸ ⟨le_refl a, le_refl a⟩, assume ⟨ab, ba⟩, le_antisymm ab ba⟩

@[simp] theorem prod.mk.inj_iff {α : Type u} {β : Type v} {a₁ a₂ : α} {b₁ b₂ : β} :
  (a₁, b₁) = (a₂, b₂) ↔ (a₁ = a₂ ∧ b₁ = b₂) :=
⟨prod.mk.inj, by cc⟩

@[simp] theorem prod.forall {α : Type u} {β : Type v} {p : α × β → Prop} :
  (∀x, p x) ↔ (∀a b, p (a, b)) :=
⟨assume h a b, h (a, b), assume h ⟨a, b⟩, h a b⟩

@[simp] theorem prod.exists {α : Type u} {β : Type v} {p : α × β → Prop} :
  (∃x, p x) ↔ (∃a b, p (a, b)) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

@[simp] theorem set_of_subset_set_of {p q : α → Prop} : {a | p a} ⊆ {a | q a} = (∀a, p a → q a) := rfl


end miscellany

/-
    propositional connectives
-/

section propositional
variables {a b c d : Prop}

/- implies -/

theorem implies_self (h : a) : a := h

theorem implies_intro (h : a) (h₂ : b) : a := h

theorem implies_false_iff (a : Prop) : (a → false) ↔ ¬ a := iff.rfl

/- not -/

theorem {u} not_elim {A : Sort u} (H1 : ¬a) (H2 : a) : A := absurd H2 H1

theorem not_not_of_not_implies : ¬(a → b) → ¬¬a :=
mt not_elim

theorem not_of_not_implies : ¬(a → b) → ¬b :=
mt implies_intro

theorem dec_em (p : Prop) [decidable p] : p ∨ ¬p := decidable.em p

theorem by_contradiction {p} [decidable p] : (¬p → false) → p :=
decidable.by_contradiction

theorem not_not_iff [decidable a] : ¬¬a ↔ a :=
iff.intro by_contradiction not_not_intro

theorem not_not_elim [decidable a] : ¬¬a → a :=
by_contradiction

theorem of_not_implies [decidable a] (h : ¬ (a → b)) : a :=
by_contradiction (not_not_of_not_implies h)

/- and -/

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
mt and.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) :=
mt and.right

theorem and_implies_left (h : a → b) : a ∧ c → b ∧ c :=
and_implies h implies_self

theorem and_implies_right (h : a → b) : c ∧ a → c ∧ b :=
and_implies implies_self h

theorem and_of_and_of_implies_of_implies (h₁ : a ∧ b) (h₂ : a → c) (h₃ : b → d) : c ∧ d :=
and_implies h₂ h₃ h₁

theorem and_of_and_of_imp_left (h₁ : a ∧ c) (h : a → b) : b ∧ c :=
and_implies_left h h₁

theorem and_of_and_of_imp_right (h₁ : c ∧ a) (h : a → b) : c ∧ b :=
and_implies_right h h₁

theorem and_imp_iff (a b c : Prop) : (a ∧ b → c) ↔ (a → b → c) :=
iff.intro (λ h a b, h ⟨a, b⟩) and.rec

theorem and_not_self_iff (a : Prop) : a ∧ ¬ a ↔ false :=
iff.intro (assume h, (h.right) (h.left)) (assume h, h.elim)

theorem not_and_self_iff (a : Prop) : ¬ a ∧ a ↔ false :=
iff.intro (assume ⟨hna, ha⟩, hna ha) false.elim

/- or -/

theorem or_of_or_of_implies_of_implies (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d :=
or.imp h₂ h₃ h₁

theorem or_of_or_of_implies_left (h₁ : a ∨ c) (h : a → b) : b ∨ c :=
or.imp_left h h₁

theorem or_of_or_of_implies_right (h₁ : c ∨ a) (h : a → b) : c ∨ b :=
or.imp_right h h₁

theorem or.elim3 (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
or.elim h ha (assume h₂, or.elim h₂ hb hc)

theorem or_resolve_right (h₁ : a ∨ b) (h₂ : ¬a) : b :=
or.elim h₁ (not_elim h₂) implies_self

theorem or_resolve_left (h₁ : a ∨ b) (h₂ : ¬b) : a :=
or_resolve_right h₁.symm h₂

theorem or_implies_distrib (a b c : Prop) : ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c)) :=
iff.intro
  (λh, and.intro (implies.trans or.inl h) (implies.trans or.inr h))
  (and.rec or.rec)

theorem or_iff_or (h1 : a ↔ c) (h2 : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
iff.intro (or.imp (iff.mp h1) (iff.mp h2)) (or.imp (iff.mpr h1) (iff.mpr h2))

theorem or_of_not_implies {a b : Prop} [decidable a] (h : ¬ a → b) : a ∨ b :=
dite _ or.inl (or.inr ∘ h)

theorem or_of_not_implies' {a b : Prop} [decidable b] (h : ¬ b → a) : a ∨ b :=
dite _ or.inr (or.inl ∘ h)

theorem not_imp_iff_not_imp {a b : Prop} [decidable a] :
  (¬ a → ¬ b) ↔ (b → a) :=
⟨assume h hb, by_contradiction $ assume na, h na hb, mt⟩

/- distributivity -/

theorem and_distrib (a b c : Prop) : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
iff.intro
  (and.rec (λh, or.imp (and.intro h) (and.intro h)))
  (or.rec (and_implies_right or.inl) (and_implies_right or.inr))

theorem and_distrib_right (a b c : Prop) : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) :=
iff.trans (iff.trans and.comm (and_distrib c a b)) (or_iff_or and.comm and.comm)

theorem or_distrib (a b c : Prop) : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
iff.intro
  (or.rec (λh, and.intro (or.inl h) (or.inl h)) (and_implies or.inr or.inr))
  (and.rec (or.rec (implies.trans or.inl implies_intro)
           (implies.trans and.intro or.imp_right)))

theorem or_distrib_right (a b c : Prop) : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
iff.trans (iff.trans or.comm (or_distrib c a b))
          (and_congr or.comm or.comm)

/- iff -/

theorem implies_iff {a : Prop} (n : Prop) (ha : a) : (a → b) ↔ b :=
iff.intro (λf, f ha) implies_intro

theorem not_or_of_implies [decidable a] (h : a → b) : ¬ a ∨ b :=
if ha : a then or.inr (h ha) else or.inl ha

theorem implies_of_not_or (h : ¬ a ∨ b) (ha : a) : b :=
or.elim h (assume hna, absurd ha hna) id

theorem implies_iff_not_or [decidable a] : (a → b) ↔ (¬ a ∨ b) :=
⟨not_or_of_implies, implies_of_not_or⟩

theorem not_implies_of_and_not (h : a ∧ ¬ b) : ¬ (a → b) :=
assume h₁, and.right h (h₁ (and.left h))

theorem and_not_of_not_implies [decidable a] (h : ¬ (a → b)) : a ∧ ¬ b :=
⟨of_not_implies h, not_of_not_implies h⟩

theorem not_implies_iff [decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
⟨and_not_of_not_implies, not_implies_of_and_not⟩

theorem peirce (a b : Prop) [decidable a] : ((a → b) → a) → a :=
if ha : a then λ h, ha else λ h, h (λ h', absurd h' ha)

theorem peirce' {a : Prop} (H : ∀ b : Prop, (a → b) → a) : a := H _ id

/- de morgan's laws -/

theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

theorem not_or_not_of_not_and [decidable a] (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
if ha : a then
  or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
else
  or.inl ha

theorem not_or_not_of_not_and' [decidable b] (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
if hb : b then
  or.inl (show ¬ a, from assume ha, h ⟨ha, hb⟩)
else
  or.inr hb

theorem not_and_iff [decidable a] : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
iff.intro not_or_not_of_not_and not_and_of_not_or_not

theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
assume h₁, or.elim h₁ (assume ha, and.left h ha) (assume hb, and.right h hb)

theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

theorem not_or_iff : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
iff.intro not_and_not_of_not_or not_or_of_not_and_not

theorem or_iff_not_and_not [decidable a] [decidable b] :
  a ∨ b ↔ ¬ (¬a ∧ ¬b) :=
by rewrite [←not_or_iff, not_not_iff]

theorem and_iff_not_or_not [decidable a] [decidable b] :
  a ∧ b ↔ ¬ (¬ a ∨ ¬ b) :=
by rewrite [←not_and_iff, not_not_iff]

/- other identities -/

theorem or_imp_iff_and_imp {a b c : Prop} : ((a ∨ b) → c) ↔ ((a → c) ∧ (b → c)) :=
⟨assume h, ⟨assume ha, h (or.inl ha), assume hb, h (or.inr hb)⟩,
  assume ⟨ha, hb⟩, or.rec ha hb⟩

end propositional

/-
  quantifiers
-/

section quantifiers
universe variable u
variables {α : Type u} {p q : α → Prop} {b : Prop}

theorem forall_of_forall (h : ∀ x, (p x → q x)) (h₁ : ∀ x, p x) : ∀ x, q x :=
assume x, h x (h₁ x)

theorem exists_of_exists (h : ∀ x, (p x → q x)) (h₁ : ∃ x, p x) : ∃ x, q x :=
match h₁ with ⟨x, hpx⟩ := ⟨x, h x hpx⟩ end

theorem forall_implies_of_exists_implies (h : (∃ x, p x) → b) : ∀ x, p x → b :=
assume x, assume hpx, h ⟨x, hpx⟩

theorem exists_implies_of_forall_implies (h : ∀ x, p x → b) : (∃ x, p x) → b :=
Exists.rec h

theorem exists_implies_distrib (p : α → Prop) (b : Prop) : ((∃ x, p x) → b) ↔ (∀ x, p x → b) :=
iff.intro forall_implies_of_exists_implies exists_implies_of_forall_implies

--theorem forall_not_of_not_exists (h : ¬ ∃ x, p x) : ∀ x, ¬ p x :=
--forall_implies_of_exists_implies h

theorem not_exists_of_forall_not (h : ∀ x, ¬ p x) : ¬ ∃ x, p x :=
exists_implies_of_forall_implies h

theorem not_exists_iff {p : α → Prop} : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
exists_implies_distrib p false

theorem exists_not_of_not_forall [decidable (∃ x, ¬ p x)] [∀ x, decidable (p x)]
  (h : ¬ ∀ x, p x) : ∃ x, ¬ p x :=
by_contradiction
  (assume h₁, h (assume x, by_contradiction (assume hnpx, h₁ ⟨x, hnpx⟩)))

theorem not_forall_of_exists_not (h : ∃ x, ¬ p x) : ¬ ∀ x, p x :=
assume h₁, match h with ⟨x, hnpx⟩ := hnpx (h₁ x) end

theorem not_forall_iff {p : α → Prop}
    [decidable (∃ x, ¬ p x)] [∀ x, decidable (p x)] :
  (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro exists_not_of_not_forall not_forall_of_exists_not

theorem forall_true_iff : (∀ x : α, true) ↔ true :=
iff_true_intro (λ h, trivial)

@[simp] theorem forall_p_iff_p (α : Type u) [inhabited α] (p : Prop) : (∀ x : α, p) ↔ p :=
iff.intro (λ h, h (inhabited.default α)) (λ hp x, hp)

@[simp] theorem exists_p_iff_p (α : Type u) [inhabited α] (p : Prop) : (∃ x : α, p) ↔ p :=
iff.intro (Exists.rec (λ x (hpx : p), hpx)) (λ hp, ⟨default α, hp⟩)

theorem forall_and_distrib (p q : α → Prop) : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h, ⟨(assume x, (h x).left), (assume x, (h x).right)⟩)
  (assume h x, ⟨h.left x, h.right x⟩)

theorem exists_or_distrib (p q : α → Prop) : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
  (assume ⟨x, hpq⟩, or.elim hpq (assume hpx, or.inl (exists.intro x hpx))
                               (assume hqx, or.inr (exists.intro x hqx)))
  (assume hepq,
    or.elim hepq
      (assume hepx,
         match hepx : _ → ∃ x, p x ∨ q x with ⟨x, hpx⟩  := ⟨x, or.inl hpx⟩ end)
      (assume ⟨x, hqx⟩, ⟨x, or.inr hqx⟩))

@[simp] theorem exists_and_distrib_left {q : Prop} {p : α → Prop} :
  (∃x, q ∧ p x) ↔ q ∧ (∃x, p x) :=
⟨assume ⟨x, hq, hp⟩, ⟨hq, x, hp⟩, assume ⟨hq, x, hp⟩, ⟨x, hq, hp⟩⟩

theorem forall_eq {α : Type u} {p : α → Prop} {a' : α} : (∀a, a = a' → p a) ↔ p a' :=
⟨assume h, h a' rfl, assume h a eq, eq.symm ▸ h⟩

theorem forall_or_distrib_left {q : Prop} {p : α → Prop} [decidable q] :
  (∀x, q ∨ p x) ↔ q ∨ (∀x, p x) :=
⟨assume h, if hq : q then or.inl hq else or.inr $ assume x, or.resolve_left (h x) hq,
  assume h x, or.imp_right (assume : ∀x, p x, this x) h⟩

@[simp] theorem exists_prop_iff (p q : Prop) : (∃ h : p, q) ↔ p ∧ q :=
iff.intro
  begin intro h', cases h', split, repeat { assumption } end
  begin intro h', cases h', split, repeat { assumption } end

end quantifiers

/- classical versions -/

namespace classical
universe variable u
variables {α : Type u} {p : α → Prop}

local attribute [instance] prop_decidable

theorem exists_not_of_not_forall (h : ¬ ∀ x, p x) : ∃ x, ¬ p x :=
exists_not_of_not_forall h

theorem not_forall_iff : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := not_forall_iff

theorem forall_or_distrib_left {q : Prop} {p : α → Prop} :
  (∀x, q ∨ p x) ↔ q ∨ (∀x, p x) :=
forall_or_distrib_left

end classical

/-
   bounded quantifiers
-/

section bounded_quantifiers
universe variable u
variables {α : Type u} {r p q : α → Prop} {b : Prop}

theorem bexists.elim {b : Prop} (h : ∃ x : α, ∃ h : p x, q x) (h' : ∀ (a : α), p a → q a → b) :
  b :=
exists.elim h (λ a h₁, exists.elim h₁ (h' a))

theorem bexists.intro (a : α) (h₁ : p a) (h₂ : q a) : ∃ x, ∃ h : p x, q x :=
exists.intro a (exists.intro h₁ h₂)

theorem bforall_congr (h : ∀ x (hrx : r x), p x ↔ q x) :
  (∀ x (hrx : r x), p x) ↔ (∀ x (hrx : r x), q x) :=
begin
  apply forall_congr,
  intro x,
  apply forall_congr,
  apply h
end

theorem bexists_congr (h : ∀ x (hrx : r x), p x ↔ q x) :
  (∃ x (hrx : r x), p x) ↔ (∃ x (hrx : r x), q x) :=
begin
  apply exists_congr,
  intros,
  apply exists_congr,
  apply h
end

theorem bforall_of_bforall (h : ∀ x (hrx : r x), (p x → q x)) (h₁ : ∀ x (hrx : r x), p x) :
  ∀ x (hrx : r x), q x :=
assume x, assume hrx, h x hrx (h₁ x hrx)

theorem bexists_of_bexists {α : Type} {p q : α → Prop}
    (h : ∀ x, (p x → q x)) (h₁ : ∃ x, p x) : ∃ x, q x :=
match h₁ with ⟨x, hpx⟩ := ⟨x, h x hpx⟩ end

theorem bforall_of_forall (h : ∀ x, p x) : ∀ x (hrx : r x), p x :=
λ x hrx, h x

theorem forall_of_bforall (h : ∀ x (ht : true), p x) : ∀ x, p x :=
λ x, h x trivial

theorem bexists_of_exists (h : ∃ x, p x) : ∃ x (ht : true), p x :=
match h with ⟨x, hpx⟩ := ⟨x, trivial, hpx⟩ end

theorem exists_of_bexists (h : ∃ x (hrx : r x), p x) : ∃ x, p x :=
match h with ⟨x, hrx, hpx⟩ := ⟨x, hpx⟩ end

theorem bforall_implies_of_bexists_implies (h : (∃ x (hrx : r x), p x) → b) :
  ∀ x (hrx : r x), p x → b :=
λ x hrx hpx, h ⟨x, hrx, hpx⟩

theorem bexists_implies_of_bforall_implies (h : ∀ x (hrx : r x), p x → b) :
  (∃ x (hrx : r x), p x) → b :=
assume ⟨x, hrx, hpx⟩, h x hrx hpx

theorem bexists_implies_distrib (r p : α → Prop) (b : Prop) :
  ((∃ x (hrx : r x), p x) → b) ↔ (∀ x (hrx : r x), p x → b) :=
iff.intro bforall_implies_of_bexists_implies bexists_implies_of_bforall_implies

theorem bforall_not_of_not_bexists (h : ¬ ∃ x (hrx : r x), p x) : ∀ x (hrx : r x), ¬ p x :=
bforall_implies_of_bexists_implies h

theorem not_bexists_of_bforall_not (h : ∀ x (hrx : r x), ¬ p x) : ¬ ∃ x (hrx : r x), p x :=
bexists_implies_of_bforall_implies h

theorem not_bexists_iff_bforall_not (r p : α → Prop) :
  (¬ ∃ x (hrx : r x) , p x) ↔ (∀ x (h : r x), ¬ p x) :=
bexists_implies_distrib r p false

theorem bexists_not_of_not_bforall
    [decidable (∃ x (hrx : r x), ¬ p x)] [∀ x, decidable (p x)]
  (h : ¬ ∀ x (hrx : r x), p x) : ∃ x (hr : r x), ¬ p x :=
by_contradiction
  (assume h₁, h (assume x, assume hrx, by_contradiction (assume hnpx, h₁ ⟨x, hrx, hnpx⟩)))

theorem not_bforall_of_bexists_not (h : ∃ x (hrx : r x), ¬ p x) : ¬ ∀ x (hrx : r x), p x :=
assume h₁, match h with ⟨x, hrx, hnpx⟩ := hnpx (h₁ x hrx) end

theorem not_bforall_iff_bexists_not (r p : α → Prop)
    [decidable (∃ x (hrx : r x), ¬ p x)] [∀ x, decidable (p x)] :
  (¬ ∀ x (hrx : r x), p x) ↔ (∃ x (hrx : r x), ¬ p x) :=
iff.intro bexists_not_of_not_bforall not_bforall_of_bexists_not

theorem bforall_true_iff (r : α → Prop): (∀ x (hrx : r x), true) ↔ true :=
iff_true_intro (λ h hrx, trivial)

theorem bforall_and_distrib : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h, ⟨(assume x, (h x).left), (assume x, (h x).right)⟩)
  (assume h x, ⟨h.left x, h.right x⟩)

theorem bexists_or_distrib (r p q : α → Prop) :
  (∃ x (hrx : r x), p x ∨ q x) ↔ (∃ x (hrx : r x), p x) ∨ (∃ x (hrx : r x), q x) :=
iff.intro
  (assume ⟨x, hrx, hpq⟩, or.elim hpq (assume hpx, or.inl (exists.intro x (exists.intro hrx hpx)))
                               (assume hqx, or.inr (exists.intro x (exists.intro hrx hqx))))
  (assume hepq,
    or.elim hepq
      (assume hepx,
         match hepx : _ → ∃ x (hrx : r x), p x ∨ q x with ⟨x, hrx, hpx⟩ := ⟨x, hrx, or.inl hpx⟩ end)
      (assume ⟨x, hrx, hqx⟩, ⟨x, hrx, or.inr hqx⟩))

end bounded_quantifiers

namespace classical
universe variable u
variables {α : Type u} {r p : α → Prop}

local attribute [instance] prop_decidable
theorem bexists_not_of_not_bforall (h : ¬ ∀ x (hrx : r x), p x) : ∃ x (hr : r x), ¬ p x :=
bexists_not_of_not_bforall h

theorem not_bforall_iff_bexists_not (r p : α → Prop) :
  (¬ ∀ x (hrx : r x), p x) ↔ (∃ x (hrx : r x), ¬ p x) :=
not_bforall_iff_bexists_not r p

end classical
