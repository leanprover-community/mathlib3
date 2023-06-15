/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro
-/
import computability.halting

/-!
# Strong reducibility and degrees.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notations

This file uses the local notation `⊕'` for `sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/

universes u v w
open function

/--
`p` is many-one reducible to `q` if there is a computable function translating questions about `p`
to questions about `q`.
-/
def many_one_reducible {α β} [primcodable α] [primcodable β] (p : α → Prop) (q : β → Prop) :=
∃ f, computable f ∧ ∀ a, p a ↔ q (f a)

infix ` ≤₀ `:1000 := many_one_reducible

theorem many_one_reducible.mk {α β} [primcodable α] [primcodable β] {f : α → β} (q : β → Prop)
  (h : computable f) : (λ a, q (f a)) ≤₀ q := ⟨f, h, λ a, iff.rfl⟩

@[refl]
theorem many_one_reducible_refl {α} [primcodable α] (p : α → Prop) :
  p ≤₀ p := ⟨id, computable.id, by simp⟩

@[trans]
theorem many_one_reducible.trans {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ q → q ≤₀ r → p ≤₀ r
| ⟨f, c₁, h₁⟩ ⟨g, c₂, h₂⟩ := ⟨g ∘ f, c₂.comp c₁,
  λ a, ⟨λ h, by rwa [←h₂, ←h₁], λ h, by rwa [h₁, h₂]⟩⟩

theorem reflexive_many_one_reducible {α} [primcodable α] :
  reflexive (@many_one_reducible α α _ _) :=
many_one_reducible_refl

theorem transitive_many_one_reducible {α} [primcodable α] :
  transitive (@many_one_reducible α α _ _) :=
λ p q r, many_one_reducible.trans

/--
`p` is one-one reducible to `q` if there is an injective computable function translating questions
about `p` to questions about `q`.
-/
def one_one_reducible {α β} [primcodable α] [primcodable β] (p : α → Prop) (q : β → Prop) :=
∃ f, computable f ∧ injective f ∧ ∀ a, p a ↔ q (f a)

infix ` ≤₁ `:1000 := one_one_reducible

theorem one_one_reducible.mk {α β} [primcodable α] [primcodable β] {f : α → β} (q : β → Prop)
  (h : computable f) (i : injective f) : (λ a, q (f a)) ≤₁ q := ⟨f, h, i, λ a, iff.rfl⟩

@[refl]
theorem one_one_reducible_refl {α} [primcodable α] (p : α → Prop) :
  p ≤₁ p := ⟨id, computable.id, injective_id, by simp⟩

@[trans]
theorem one_one_reducible.trans {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₁ q → q ≤₁ r → p ≤₁ r
| ⟨f, c₁, i₁, h₁⟩ ⟨g, c₂, i₂, h₂⟩ := ⟨g ∘ f, c₂.comp c₁, i₂.comp i₁,
  λ a, ⟨λ h, by rwa [←h₂, ←h₁], λ h, by rwa [h₁, h₂]⟩⟩

theorem one_one_reducible.to_many_one {α β} [primcodable α] [primcodable β]
  {p : α → Prop} {q : β → Prop} : p ≤₁ q → p ≤₀ q
| ⟨f, c, i, h⟩ := ⟨f, c, h⟩

theorem one_one_reducible.of_equiv {α β} [primcodable α] [primcodable β]
    {e : α ≃ β} (q : β → Prop) (h : computable e) :
  (q ∘ e) ≤₁ q :=
one_one_reducible.mk _ h e.injective

theorem one_one_reducible.of_equiv_symm {α β} [primcodable α] [primcodable β]
    {e : α ≃ β} (q : β → Prop) (h : computable e.symm) :
  q ≤₁ (q ∘ e) :=
by convert one_one_reducible.of_equiv _ h; funext; simp

theorem reflexive_one_one_reducible {α} [primcodable α] :
  reflexive (@one_one_reducible α α _ _) :=
one_one_reducible_refl

theorem transitive_one_one_reducible {α} [primcodable α] :
  transitive (@one_one_reducible α α _ _) :=
λ p q r, one_one_reducible.trans

namespace computable_pred
variables {α : Type*} {β : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable σ]
open computable

theorem computable_of_many_one_reducible
  {p : α → Prop} {q : β → Prop}
  (h₁ : p ≤₀ q) (h₂ : computable_pred q) : computable_pred p :=
begin
  rcases h₁ with ⟨f, c, hf⟩,
  rw [show p = λ a, q (f a), from set.ext hf],
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩,
  exact ⟨by apply_instance, by simpa using hg.comp c⟩
end

theorem computable_of_one_one_reducible
  {p : α → Prop} {q : β → Prop}
  (h : p ≤₁ q) : computable_pred q → computable_pred p :=
computable_of_many_one_reducible h.to_many_one

end computable_pred

/-- `p` and `q` are many-one equivalent if each one is many-one reducible to the other. -/
def many_one_equiv {α β} [primcodable α] [primcodable β]
  (p : α → Prop) (q : β → Prop) := p ≤₀ q ∧ q ≤₀ p

/-- `p` and `q` are one-one equivalent if each one is one-one reducible to the other. -/
def one_one_equiv {α β} [primcodable α] [primcodable β]
  (p : α → Prop) (q : β → Prop) := p ≤₁ q ∧ q ≤₁ p

@[refl]
theorem many_one_equiv_refl {α} [primcodable α] (p : α → Prop) : many_one_equiv p p :=
⟨many_one_reducible_refl _, many_one_reducible_refl _⟩

@[symm]
theorem many_one_equiv.symm {α β} [primcodable α] [primcodable β]
  {p : α → Prop} {q : β → Prop} : many_one_equiv p q → many_one_equiv q p := and.swap

@[trans]
theorem many_one_equiv.trans {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop} :
  many_one_equiv p q → many_one_equiv q r → many_one_equiv p r
| ⟨pq, qp⟩ ⟨qr, rq⟩ := ⟨pq.trans qr, rq.trans qp⟩

theorem equivalence_of_many_one_equiv {α} [primcodable α] :
  equivalence (@many_one_equiv α α _ _) :=
⟨many_one_equiv_refl, λ x y, many_one_equiv.symm, λ x y z, many_one_equiv.trans⟩

@[refl]
theorem one_one_equiv_refl {α} [primcodable α] (p : α → Prop) : one_one_equiv p p :=
⟨one_one_reducible_refl _, one_one_reducible_refl _⟩

@[symm]
theorem one_one_equiv.symm {α β} [primcodable α] [primcodable β]
  {p : α → Prop} {q : β → Prop} : one_one_equiv p q → one_one_equiv q p := and.swap

@[trans]
theorem one_one_equiv.trans {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop} :
  one_one_equiv p q → one_one_equiv q r → one_one_equiv p r
| ⟨pq, qp⟩ ⟨qr, rq⟩ := ⟨pq.trans qr, rq.trans qp⟩

theorem equivalence_of_one_one_equiv {α} [primcodable α] : equivalence (@one_one_equiv α α _ _) :=
⟨one_one_equiv_refl, λ x y, one_one_equiv.symm, λ x y z, one_one_equiv.trans⟩

theorem one_one_equiv.to_many_one {α β} [primcodable α] [primcodable β]
  {p : α → Prop} {q : β → Prop} : one_one_equiv p q → many_one_equiv p q
| ⟨pq, qp⟩ := ⟨pq.to_many_one, qp.to_many_one⟩

/-- a computable bijection -/
def equiv.computable {α β} [primcodable α] [primcodable β] (e : α ≃ β) :=
computable e ∧ computable e.symm

theorem equiv.computable.symm {α β} [primcodable α] [primcodable β] {e : α ≃ β} :
  e.computable → e.symm.computable := and.swap

theorem equiv.computable.trans {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {e₁ : α ≃ β} {e₂ : β ≃ γ} :
  e₁.computable → e₂.computable → (e₁.trans e₂).computable
| ⟨l₁, r₁⟩ ⟨l₂, r₂⟩ := ⟨l₂.comp l₁, r₁.comp r₂⟩

theorem computable.eqv (α) [denumerable α] : (denumerable.eqv α).computable :=
⟨computable.encode, computable.of_nat _⟩

theorem computable.equiv₂ (α β) [denumerable α] [denumerable β] :
  (denumerable.equiv₂ α β).computable :=
(computable.eqv _).trans (computable.eqv _).symm

theorem one_one_equiv.of_equiv {α β} [primcodable α] [primcodable β]
  {e : α ≃ β} (h : e.computable) {p} : one_one_equiv (p ∘ e) p :=
⟨one_one_reducible.of_equiv _ h.1, one_one_reducible.of_equiv_symm _ h.2⟩

theorem many_one_equiv.of_equiv {α β} [primcodable α] [primcodable β]
  {e : α ≃ β} (h : e.computable) {p} : many_one_equiv (p ∘ e) p :=
(one_one_equiv.of_equiv h).to_many_one

theorem many_one_equiv.le_congr_left {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (h : many_one_equiv p q) : p ≤₀ r ↔ q ≤₀ r := ⟨h.2.trans, h.1.trans⟩

theorem many_one_equiv.le_congr_right {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (h : many_one_equiv q r) : p ≤₀ q ↔ p ≤₀ r := ⟨λ h', h'.trans h.1, λ h', h'.trans h.2⟩

theorem one_one_equiv.le_congr_left {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (h : one_one_equiv p q) : p ≤₁ r ↔ q ≤₁ r := ⟨h.2.trans, h.1.trans⟩

theorem one_one_equiv.le_congr_right {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (h : one_one_equiv q r) : p ≤₁ q ↔ p ≤₁ r := ⟨λ h', h'.trans h.1, λ h', h'.trans h.2⟩

theorem many_one_equiv.congr_left {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (h : many_one_equiv p q) : many_one_equiv p r ↔ many_one_equiv q r :=
and_congr h.le_congr_left h.le_congr_right

theorem many_one_equiv.congr_right {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (h : many_one_equiv q r) : many_one_equiv p q ↔ many_one_equiv p r :=
and_congr h.le_congr_right h.le_congr_left

theorem one_one_equiv.congr_left {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (h : one_one_equiv p q) : one_one_equiv p r ↔ one_one_equiv q r :=
and_congr h.le_congr_left h.le_congr_right

theorem one_one_equiv.congr_right {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (h : one_one_equiv q r) : one_one_equiv p q ↔ one_one_equiv p r :=
and_congr h.le_congr_right h.le_congr_left

@[simp] lemma ulower.down_computable {α} [primcodable α] : (ulower.equiv α).computable :=
⟨primrec.ulower_down.to_comp, primrec.ulower_up.to_comp⟩

lemma many_one_equiv_up {α} [primcodable α] {p : α → Prop} : many_one_equiv (p ∘ ulower.up) p :=
many_one_equiv.of_equiv ulower.down_computable.symm

local infix ` ⊕' `:1001 := sum.elim

open nat.primrec

theorem one_one_reducible.disjoin_left {α β} [primcodable α] [primcodable β]
  {p : α → Prop} {q : β → Prop} : p ≤₁ p ⊕' q :=
⟨sum.inl, computable.sum_inl, λ x y, sum.inl.inj_iff.1, λ a, iff.rfl⟩

theorem one_one_reducible.disjoin_right {α β} [primcodable α] [primcodable β]
  {p : α → Prop} {q : β → Prop} : q ≤₁ p ⊕' q :=
⟨sum.inr, computable.sum_inr, λ x y, sum.inr.inj_iff.1, λ a, iff.rfl⟩

theorem disjoin_many_one_reducible {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ≤₀ r → q ≤₀ r → p ⊕' q ≤₀ r
| ⟨f, c₁, h₁⟩ ⟨g, c₂, h₂⟩ := ⟨sum.elim f g,
  computable.id.sum_cases (c₁.comp computable.snd).to₂ (c₂.comp computable.snd).to₂,
  λ x, by cases x; [apply h₁, apply h₂]⟩

theorem disjoin_le {α β γ} [primcodable α] [primcodable β] [primcodable γ]
  {p : α → Prop} {q : β → Prop} {r : γ → Prop} : p ⊕' q ≤₀ r ↔ p ≤₀ r ∧ q ≤₀ r :=
⟨λ h, ⟨one_one_reducible.disjoin_left.to_many_one.trans h,
  one_one_reducible.disjoin_right.to_many_one.trans h⟩,
 λ ⟨h₁, h₂⟩, disjoin_many_one_reducible h₁ h₂⟩

variables {α : Type u} [primcodable α] [inhabited α]
variables {β : Type v} [primcodable β] [inhabited β]
variables {γ : Type w} [primcodable γ] [inhabited γ]

/--
Computable and injective mapping of predicates to sets of natural numbers.
-/
def to_nat (p : set α) : set ℕ :=
{ n | p ((encodable.decode α n).get_or_else default) }

@[simp]
lemma to_nat_many_one_reducible {p : set α} : to_nat p ≤₀ p :=
⟨λ n, (encodable.decode α n).get_or_else default,
 computable.option_get_or_else computable.decode (computable.const _),
 λ _, iff.rfl⟩

@[simp]
lemma many_one_reducible_to_nat {p : set α} : p ≤₀ to_nat p :=
⟨encodable.encode, computable.encode, by simp [to_nat, set_of]⟩

@[simp]
lemma many_one_reducible_to_nat_to_nat {p : set α} {q : set β} :
  to_nat p ≤₀ to_nat q ↔ p ≤₀ q :=
⟨λ h, many_one_reducible_to_nat.trans (h.trans to_nat_many_one_reducible),
 λ h, to_nat_many_one_reducible.trans (h.trans many_one_reducible_to_nat)⟩

@[simp]
lemma to_nat_many_one_equiv {p : set α} : many_one_equiv (to_nat p) p :=
by simp [many_one_equiv]

@[simp]
lemma many_one_equiv_to_nat (p : set α) (q : set β) :
  many_one_equiv (to_nat p) (to_nat q) ↔ many_one_equiv p q :=
by simp [many_one_equiv]

/-- A many-one degree is an equivalence class of sets up to many-one equivalence. -/
def many_one_degree : Type :=
quotient (⟨many_one_equiv, equivalence_of_many_one_equiv⟩ : setoid (set ℕ))

namespace many_one_degree

/-- The many-one degree of a set on a primcodable type. -/
def of (p : α → Prop) : many_one_degree :=
quotient.mk' (to_nat p)

@[elab_as_eliminator]
protected lemma ind_on {C : many_one_degree → Prop} (d : many_one_degree)
  (h : ∀ p : set ℕ, C (of p)) : C d :=
quotient.induction_on' d h

/--
Lifts a function on sets of natural numbers to many-one degrees.
-/
@[elab_as_eliminator, reducible]
protected def lift_on {φ} (d : many_one_degree) (f : set ℕ → φ)
  (h : ∀ p q, many_one_equiv p q → f p = f q) : φ :=
quotient.lift_on' d f h

@[simp]
protected lemma lift_on_eq {φ} (p : set ℕ) (f : set ℕ → φ)
    (h : ∀ p q, many_one_equiv p q → f p = f q) :
  (of p).lift_on f h = f p :=
rfl

/--
Lifts a binary function on sets of natural numbers to many-one degrees.
-/
@[elab_as_eliminator, reducible, simp]
protected def lift_on₂ {φ} (d₁ d₂ : many_one_degree) (f : set ℕ → set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, many_one_equiv p₁ p₂ → many_one_equiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) :
  φ :=
d₁.lift_on (λ p, d₂.lift_on (f p) (λ q₁ q₂ hq, h _ _ _ _ (by refl) hq))
begin
  intros p₁ p₂ hp,
  induction d₂ using many_one_degree.ind_on,
  apply h,
  assumption,
  refl,
end

@[simp]
protected lemma lift_on₂_eq {φ} (p q : set ℕ) (f : set ℕ → set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, many_one_equiv p₁ p₂ → many_one_equiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) :
  (of p).lift_on₂ (of q) f h = f p q :=
rfl

@[simp] lemma of_eq_of {p : α → Prop} {q : β → Prop} : of p = of q ↔ many_one_equiv p q :=
by simp [of, quotient.eq']

instance : inhabited many_one_degree := ⟨of (∅ : set ℕ)⟩

/--
For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one reducible to the
sets in `d₂`.
-/
instance : has_le many_one_degree :=
⟨λ d₁ d₂, many_one_degree.lift_on₂ d₁ d₂ (≤₀) $
  λ p₁ p₂ q₁ q₂ hp hq, propext ((hp.le_congr_left).trans (hq.le_congr_right))⟩

@[simp] lemma of_le_of {p : α → Prop} {q : β → Prop} : of p ≤ of q ↔ p ≤₀ q :=
many_one_reducible_to_nat_to_nat

private lemma le_refl (d : many_one_degree) : d ≤ d :=
by induction d using many_one_degree.ind_on; simp

private lemma le_antisymm {d₁ d₂ : many_one_degree} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ :=
begin
  induction d₁ using many_one_degree.ind_on,
  induction d₂ using many_one_degree.ind_on,
  intros hp hq,
  simp only [*, many_one_equiv, of_le_of, of_eq_of, true_and] at *
end

private lemma le_trans {d₁ d₂ d₃ : many_one_degree} :
  d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ :=
begin
  induction d₁ using many_one_degree.ind_on,
  induction d₂ using many_one_degree.ind_on,
  induction d₃ using many_one_degree.ind_on,
  apply many_one_reducible.trans
end

instance : partial_order many_one_degree :=
{ le := (≤),
  le_refl := le_refl,
  le_trans := λ _ _ _, le_trans,
  le_antisymm := λ _ _, le_antisymm }

/-- The join of two degrees, induced by the disjoint union of two underlying sets. -/
instance : has_add many_one_degree :=
⟨λ d₁ d₂, d₁.lift_on₂ d₂ (λ a b, of (a ⊕' b))
  begin
    rintros a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩,
    rw of_eq_of,
    exact ⟨disjoin_many_one_reducible
        (hl₁.trans one_one_reducible.disjoin_left.to_many_one)
        (hl₂.trans one_one_reducible.disjoin_right.to_many_one),
      disjoin_many_one_reducible
        (hr₁.trans one_one_reducible.disjoin_left.to_many_one)
        (hr₂.trans one_one_reducible.disjoin_right.to_many_one)⟩
  end⟩

@[simp] lemma add_of (p : set α) (q : set β) : of (p ⊕' q) = of p + of q :=
of_eq_of.mpr
  ⟨disjoin_many_one_reducible
    (many_one_reducible_to_nat.trans one_one_reducible.disjoin_left.to_many_one)
    (many_one_reducible_to_nat.trans one_one_reducible.disjoin_right.to_many_one),
   disjoin_many_one_reducible
    (to_nat_many_one_reducible.trans one_one_reducible.disjoin_left.to_many_one)
    (to_nat_many_one_reducible.trans one_one_reducible.disjoin_right.to_many_one)⟩

@[simp] protected theorem add_le {d₁ d₂ d₃ : many_one_degree} :
  d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃ :=
begin
  induction d₁ using many_one_degree.ind_on,
  induction d₂ using many_one_degree.ind_on,
  induction d₃ using many_one_degree.ind_on,
  simpa only [← add_of, of_le_of] using disjoin_le
end

@[simp] protected theorem le_add_left (d₁ d₂ : many_one_degree) : d₁ ≤ d₁ + d₂ :=
(many_one_degree.add_le.1 (by refl)).1

@[simp] protected theorem le_add_right (d₁ d₂ : many_one_degree) : d₂ ≤ d₁ + d₂ :=
(many_one_degree.add_le.1 (by refl)).2

instance : semilattice_sup many_one_degree :=
{ sup := (+),
  le_sup_left := many_one_degree.le_add_left,
  le_sup_right := many_one_degree.le_add_right,
  sup_le := λ a b c h₁ h₂, many_one_degree.add_le.2 ⟨h₁, h₂⟩,
  ..many_one_degree.partial_order }

end many_one_degree
