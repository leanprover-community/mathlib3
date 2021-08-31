/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.alias
import tactic.lint

/-!
# Lemmas about inequalities

This file contains some lemmas about `≤`/`≥`/`<`/`>`, and `cmp`.

* We simplify `a ≥ b` and `a > b` to `b ≤ a` and `b < a`, respectively. This way we can formulate
  all lemmas using `≤`/`<` avoiding duplication.

* In some cases we introduce dot syntax aliases so that, e.g., from
  `(hab : a ≤ b) (hbc : b ≤ c) (hbc' : b < c)` one can prove `hab.trans hbc : a ≤ c` and
  `hab.trans_lt hbc' : a < c`.
-/

universe u
variables {α : Type u}

alias le_trans        ← has_le.le.trans
alias lt_of_le_of_lt  ← has_le.le.trans_lt
alias le_antisymm     ← has_le.le.antisymm
alias lt_of_le_of_ne  ← has_le.le.lt_of_ne
alias lt_of_le_not_le ← has_le.le.lt_of_not_le
alias lt_or_eq_of_le  ← has_le.le.lt_or_eq
alias decidable.lt_or_eq_of_le ← has_le.le.lt_or_eq_dec

alias le_of_lt        ← has_lt.lt.le
alias lt_trans        ← has_lt.lt.trans
alias lt_of_lt_of_le  ← has_lt.lt.trans_le
alias ne_of_lt        ← has_lt.lt.ne
alias lt_asymm        ← has_lt.lt.asymm has_lt.lt.not_lt

alias le_of_eq        ← eq.le

attribute [nolint decidable_classical] has_le.le.lt_or_eq_dec

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl [preorder α] {x : α} : x ≤ x := le_refl x

namespace eq
/--
If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`,
because `le` is used almost exclusively in mathlib.
-/
protected lemma ge [preorder α] {x y : α} (h : x = y) : y ≤ x := h.symm.le

lemma trans_le [preorder α] {x y z : α} (h1 : x = y) (h2 : y ≤ z) : x ≤ z := h1.le.trans h2

lemma not_lt [partial_order α] {x y : α} (h : x = y) : ¬(x < y) := λ h', h'.ne h

lemma not_gt [partial_order α] {x y : α} (h : x = y) : ¬(y < x) := h.symm.not_lt

end eq

namespace has_le.le

@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma ge [has_le α] {x y : α} (h : x ≤ y) : y ≥ x := h

lemma trans_eq [preorder α] {x y z : α} (h1 : x ≤ y) (h2 : y = z) : x ≤ z := h1.trans h2.le

lemma lt_iff_ne [partial_order α] {x y : α} (h : x ≤ y) : x < y ↔ x ≠ y := ⟨λ h, h.ne, h.lt_of_ne⟩

lemma le_iff_eq [partial_order α] {x y : α} (h : x ≤ y) : y ≤ x ↔ y = x :=
⟨λ h', h'.antisymm h, eq.le⟩

lemma lt_or_le [linear_order α] {a b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
(lt_or_ge a c).imp id $ λ hc, le_trans hc h

lemma le_or_lt [linear_order α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
(le_or_gt a c).imp id $ λ hc, lt_of_lt_of_le hc h

lemma le_or_le [linear_order α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b :=
(h.le_or_lt c).elim or.inl (λ h, or.inr $ le_of_lt h)

end has_le.le

namespace has_lt.lt

@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma gt [has_lt α] {x y : α} (h : x < y) : y > x := h
protected lemma false [preorder α] {x : α} : x < x → false := lt_irrefl x

lemma ne' [preorder α] {x y : α} (h : x < y) : y ≠ x := h.ne.symm

lemma lt_or_lt [linear_order α] {x y : α} (h : x < y) (z : α) : x < z ∨ z < y :=
(lt_or_ge z y).elim or.inr (λ hz, or.inl $ h.trans_le hz)

end has_lt.lt

namespace ge
@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma le [has_le α] {x y : α} (h : x ≥ y) : y ≤ x := h
end ge

namespace gt
@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma lt [has_lt α] {x y : α} (h : x > y) : y < x := h
end gt

@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem ge_of_eq [preorder α] {a b : α} (h : a = b) : a ≥ b :=
h.ge

@[simp, nolint ge_or_gt] -- see Note [nolint_ge]
lemma ge_iff_le [preorder α] {a b : α} : a ≥ b ↔ b ≤ a := iff.rfl
@[simp, nolint ge_or_gt] -- see Note [nolint_ge]
lemma gt_iff_lt [preorder α] {a b : α} : a > b ↔ b < a := iff.rfl

lemma not_le_of_lt [preorder α] {a b : α} (h : a < b) : ¬ b ≤ a :=
(le_not_le_of_lt h).right

alias not_le_of_lt ← has_lt.lt.not_le

lemma not_lt_of_le [preorder α] {a b : α} (h : a ≤ b) : ¬ b < a
| hab := hab.not_le h

alias not_lt_of_le ← has_le.le.not_lt

-- See Note [decidable namespace]
protected lemma decidable.le_iff_eq_or_lt [partial_order α] [@decidable_rel α (≤)]
  {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
decidable.le_iff_lt_or_eq.trans or.comm

lemma le_iff_eq_or_lt [partial_order α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
le_iff_lt_or_eq.trans or.comm

lemma lt_iff_le_and_ne [partial_order α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
⟨λ h, ⟨le_of_lt h, ne_of_lt h⟩, λ ⟨h1, h2⟩, h1.lt_of_ne h2⟩

-- See Note [decidable namespace]
protected lemma decidable.eq_iff_le_not_lt [partial_order α] [@decidable_rel α (≤)]
  {a b : α} : a = b ↔ a ≤ b ∧ ¬ a < b :=
⟨λ h, ⟨h.le, h ▸ lt_irrefl _⟩, λ ⟨h₁, h₂⟩, h₁.antisymm $
  decidable.by_contradiction $ λ h₃, h₂ (h₁.lt_of_not_le h₃)⟩

lemma eq_iff_le_not_lt [partial_order α] {a b : α} : a = b ↔ a ≤ b ∧ ¬ a < b :=
by haveI := classical.dec; exact decidable.eq_iff_le_not_lt

lemma eq_or_lt_of_le [partial_order α] {a b : α} (h : a ≤ b) : a = b ∨ a < b :=
h.lt_or_eq.symm

alias decidable.eq_or_lt_of_le ← has_le.le.eq_or_lt_dec
alias eq_or_lt_of_le ← has_le.le.eq_or_lt

attribute [nolint decidable_classical] has_le.le.eq_or_lt_dec

lemma ne.le_iff_lt [partial_order α] {a b : α} (h : a ≠ b) : a ≤ b ↔ a < b :=
⟨λ h', lt_of_le_of_ne h' h, λ h, h.le⟩

-- See Note [decidable namespace]
protected lemma decidable.ne_iff_lt_iff_le [partial_order α] [@decidable_rel α (≤)]
  {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
⟨λ h, decidable.by_cases le_of_eq (le_of_lt ∘ h.mp), λ h, ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[simp] lemma ne_iff_lt_iff_le [partial_order α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
by haveI := classical.dec; exact decidable.ne_iff_lt_iff_le

lemma lt_of_not_ge' [linear_order α] {a b : α} (h : ¬ b ≤ a) : a < b :=
((le_total _ _).resolve_right h).lt_of_not_le h

lemma lt_iff_not_ge' [linear_order α] {x y : α} : x < y ↔ ¬ y ≤ x :=
⟨not_le_of_gt, lt_of_not_ge'⟩

lemma ne.lt_or_lt [linear_order α] {a b : α} (h : a ≠ b) : a < b ∨ b < a :=
lt_or_gt_of_ne h

lemma not_lt_iff_eq_or_lt [linear_order α] {a b : α} : ¬ a < b ↔ a = b ∨ b < a :=
not_lt.trans $ decidable.le_iff_eq_or_lt.trans $ or_congr eq_comm iff.rfl

lemma exists_ge_of_linear [linear_order α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
match le_total a b with
| or.inl h := ⟨_, h, le_rfl⟩
| or.inr h := ⟨_, le_rfl, h⟩
end

lemma lt_imp_lt_of_le_imp_le {β} [linear_order α] [preorder β] {a b : α} {c d : β}
  (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
lt_of_not_ge' $ λ h', (H h').not_lt h

lemma le_imp_le_iff_lt_imp_lt {β} [linear_order α] [linear_order β] {a b : α} {c d : β} :
  (a ≤ b → c ≤ d) ↔ (d < c → b < a) :=
⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

lemma lt_iff_lt_of_le_iff_le' {β} [preorder α] [preorder β] {a b : α} {c d : β}
  (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
lt_iff_le_not_le.trans $ (and_congr H' (not_congr H)).trans lt_iff_le_not_le.symm

lemma lt_iff_lt_of_le_iff_le {β} [linear_order α] [linear_order β] {a b : α} {c d : β}
  (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c :=
not_le.symm.trans $ (not_congr H).trans $ not_le

lemma le_iff_le_iff_lt_iff_lt {β} [linear_order α] [linear_order β] {a b : α} {c d : β} :
  (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
⟨lt_iff_lt_of_le_iff_le, λ H, not_lt.symm.trans $ (not_congr H).trans $ not_lt⟩

lemma eq_of_forall_le_iff [partial_order α] {a b : α}
  (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
le_antisymm ((H _).1 (le_refl _)) ((H _).2 (le_refl _))

lemma le_of_forall_le [preorder α] {a b : α}
  (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
H _ (le_refl _)

lemma le_of_forall_le' [preorder α] {a b : α}
  (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a :=
H _ (le_refl _)

lemma le_of_forall_lt [linear_order α] {a b : α}
  (H : ∀ c, c < a → c < b) : a ≤ b :=
le_of_not_lt $ λ h, lt_irrefl _ (H _ h)

lemma forall_lt_iff_le [linear_order α] {a b : α} :
  (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
⟨le_of_forall_lt, λ h c hca, lt_of_lt_of_le hca h⟩

lemma le_of_forall_lt' [linear_order α] {a b : α}
  (H : ∀ c, a < c → b < c) : b ≤ a :=
le_of_not_lt $ λ h, lt_irrefl _ (H _ h)

lemma forall_lt_iff_le' [linear_order α] {a b : α} :
  (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
⟨le_of_forall_lt', λ h c hac, lt_of_le_of_lt h hac⟩

lemma eq_of_forall_ge_iff [partial_order α] {a b : α}
  (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
le_antisymm ((H _).2 (le_refl _)) ((H _).1 (le_refl _))

/-- monotonicity of `≤` with respect to `→` -/
lemma le_implies_le_of_le_of_le {a b c d : α} [preorder α] (h₀ : c ≤ a) (h₁ : b ≤ d) :
  a ≤ b → c ≤ d :=
assume h₂ : a ≤ b,
calc  c
    ≤ a : h₀
... ≤ b : h₂
... ≤ d : h₁

/-- Like `cmp`, but uses a `≤` on the type instead of `<`. Given two elements
`x` and `y`, returns a three-way comparison result `ordering`. -/
def cmp_le {α} [has_le α] [@decidable_rel α (≤)] (x y : α) : ordering :=
if x ≤ y then
  if y ≤ x then ordering.eq else ordering.lt
else ordering.gt

theorem cmp_le_swap {α} [has_le α] [is_total α (≤)] [@decidable_rel α (≤)] (x y : α) :
  (cmp_le x y).swap = cmp_le y x :=
begin
  by_cases xy : x ≤ y; by_cases yx : y ≤ x; simp [cmp_le, *, ordering.swap],
  cases not_or xy yx (total_of _ _ _)
end

theorem cmp_le_eq_cmp {α} [preorder α] [is_total α (≤)]
  [@decidable_rel α (≤)] [@decidable_rel α (<)] (x y : α) : cmp_le x y = cmp x y :=
begin
  by_cases xy : x ≤ y; by_cases yx : y ≤ x;
    simp [cmp_le, lt_iff_le_not_le, *, cmp, cmp_using],
  cases not_or xy yx (total_of _ _ _)
end

namespace ordering

/-- `compares o a b` means that `a` and `b` have the ordering relation
  `o` between them, assuming that the relation `a < b` is defined -/
@[simp] def compares [has_lt α] : ordering → α → α → Prop
| lt a b := a < b
| eq a b := a = b
| gt a b := a > b

theorem compares_swap [has_lt α] {a b : α} {o : ordering} :
  o.swap.compares a b ↔ o.compares b a :=
by { cases o, exacts [iff.rfl, eq_comm, iff.rfl] }

alias compares_swap ↔ ordering.compares.of_swap ordering.compares.swap

theorem swap_eq_iff_eq_swap {o o' : ordering} : o.swap = o' ↔ o = o'.swap :=
⟨λ h, by rw [← swap_swap o, h], λ h, by rw [← swap_swap o', h]⟩

theorem compares.eq_lt [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = lt ↔ a < b)
| lt a b h := ⟨λ _, h, λ _, rfl⟩
| eq a b h := ⟨λ h, by injection h, λ h', (ne_of_lt h' h).elim⟩
| gt a b h := ⟨λ h, by injection h, λ h', (lt_asymm h h').elim⟩

theorem compares.ne_lt [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o ≠ lt ↔ b ≤ a)
| lt a b h := ⟨absurd rfl, λ h', (not_le_of_lt h h').elim⟩
| eq a b h := ⟨λ _, ge_of_eq h, λ _ h, by injection h⟩
| gt a b h := ⟨λ _, le_of_lt h, λ _ h, by injection h⟩

theorem compares.eq_eq [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = eq ↔ a = b)
| lt a b h := ⟨λ h, by injection h, λ h', (ne_of_lt h h').elim⟩
| eq a b h := ⟨λ _, h, λ _, rfl⟩
| gt a b h := ⟨λ h, by injection h, λ h', (ne_of_gt h h').elim⟩

theorem compares.eq_gt [preorder α] {o} {a b : α} (h : compares o a b) : (o = gt ↔ b < a) :=
swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt

theorem compares.ne_gt [preorder α] {o} {a b : α} (h : compares o a b) : (o ≠ gt ↔ a ≤ b) :=
(not_congr swap_eq_iff_eq_swap.symm).trans h.swap.ne_lt

theorem compares.le_total [preorder α] {a b : α} :
  ∀ {o}, compares o a b → a ≤ b ∨ b ≤ a
| lt h := or.inl (le_of_lt h)
| eq h := or.inl (le_of_eq h)
| gt h := or.inr (le_of_lt h)

theorem compares.le_antisymm [preorder α] {a b : α} :
  ∀ {o}, compares o a b → a ≤ b → b ≤ a → a = b
| lt h _ hba := (not_le_of_lt h hba).elim
| eq h _ _   := h
| gt h hab _ := (not_le_of_lt h hab).elim

theorem compares.inj [preorder α] {o₁} :
  ∀ {o₂} {a b : α}, compares o₁ a b → compares o₂ a b → o₁ = o₂
| lt a b h₁ h₂ := h₁.eq_lt.2 h₂
| eq a b h₁ h₂ := h₁.eq_eq.2 h₂
| gt a b h₁ h₂ := h₁.eq_gt.2 h₂

theorem compares_iff_of_compares_impl {β : Type*} [linear_order α] [preorder β] {a b : α}
  {a' b' : β} (h : ∀ {o}, compares o a b → compares o a' b') (o) :
  compares o a b ↔ compares o a' b' :=
begin
  refine ⟨h, λ ho, _⟩,
  cases lt_trichotomy a b with hab hab,
  { change compares ordering.lt a b at hab,
    rwa [ho.inj (h hab)] },
  { cases hab with hab hab,
    { change compares ordering.eq a b at hab,
      rwa [ho.inj (h hab)] },
    { change compares ordering.gt a b at hab,
      rwa [ho.inj (h hab)] } }
end

theorem swap_or_else (o₁ o₂) : (or_else o₁ o₂).swap = or_else o₁.swap o₂.swap :=
by cases o₁; try {refl}; cases o₂; refl

theorem or_else_eq_lt (o₁ o₂) : or_else o₁ o₂ = lt ↔ o₁ = lt ∨ (o₁ = eq ∧ o₂ = lt) :=
by cases o₁; cases o₂; exact dec_trivial

end ordering

theorem cmp_compares [linear_order α] (a b : α) : (cmp a b).compares a b :=
begin
  unfold cmp cmp_using,
  by_cases a < b; simp [h],
  by_cases h₂ : b < a; simp [h₂, gt],
  exact (decidable.lt_or_eq_of_le (le_of_not_gt h₂)).resolve_left h
end

theorem cmp_swap [preorder α] [@decidable_rel α (<)] (a b : α) : (cmp a b).swap = cmp b a :=
begin
  unfold cmp cmp_using,
  by_cases a < b; by_cases h₂ : b < a; simp [h, h₂, gt, ordering.swap],
  exact lt_asymm h h₂
end

/-- Generate a linear order structure from a preorder and `cmp` function. -/
def linear_order_of_compares [preorder α] (cmp : α → α → ordering)
  (h : ∀ a b, (cmp a b).compares a b) :
  linear_order α :=
{ le_antisymm := λ a b, (h a b).le_antisymm,
  le_total := λ a b, (h a b).le_total,
  decidable_le := λ a b, decidable_of_iff _ (h a b).ne_gt,
  decidable_lt := λ a b, decidable_of_iff _ (h a b).eq_lt,
  decidable_eq := λ a b, decidable_of_iff _ (h a b).eq_eq,
  .. ‹preorder α› }

variables [linear_order α] (x y : α)

@[simp] lemma cmp_eq_lt_iff : cmp x y = ordering.lt ↔ x < y :=
ordering.compares.eq_lt (cmp_compares x y)

@[simp] lemma cmp_eq_eq_iff : cmp x y = ordering.eq ↔ x = y :=
ordering.compares.eq_eq (cmp_compares x y)

@[simp] lemma cmp_eq_gt_iff : cmp x y = ordering.gt ↔ y < x :=
ordering.compares.eq_gt (cmp_compares x y)

@[simp] lemma cmp_self_eq_eq : cmp x x = ordering.eq :=
by rw cmp_eq_eq_iff

variables {x y} {β : Type*} [linear_order β] {x' y' : β}

lemma cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x' :=
by { split, rw [←cmp_swap _ y, ←cmp_swap _ y'], cc,
  rw [←cmp_swap _ x, ←cmp_swap _ x'], cc, }

lemma lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x < y ↔ x' < y' :=
by rw [←cmp_eq_lt_iff, ←cmp_eq_lt_iff, h]

lemma le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x ≤ y ↔ x' ≤ y' :=
by { rw [←not_lt, ←not_lt], apply not_congr,
  apply lt_iff_lt_of_cmp_eq_cmp, rwa cmp_eq_cmp_symm }
