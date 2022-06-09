/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import set_theory.cardinal.finite

/-!
# Finite types

This module defines a finiteness predicate on types called `finite`.
A type is `finite` if it is equivalent to `fin n` for some `n`, and
otherwise it is `infinite` (see `finite_or_infinite`). This predicate is
a `class`, and finiteness proofs are given as instances.

The `finite` predicate has no computational relevance and, being
`Prop`-valued, gets to enjoy proof irrelevance -- it represents the mere fact
that the type is finite.
While the `fintype` class also represents finiteness of a type, a key
difference is that a `fintype` instance represents finiteness in a
computable way: it gives a concrete algorithm to produce a `finset` whose
elements enumerate the terms of the given type. As such, one generally
relies on congruence lemmas when rewriting expressions involving
`fintype` instances.

Every `fintype` instance automatically gives a `finite` instance, but not
vice versa. Every `fintype` instance should be computable since they are meant
for computation. If it's not possible to write a computable `fintype` instance,
one should prefer writing a `finite` instance instead.

The cardinality of a finite type `α` is given by `nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `finite` instance
for the type. (Note: we could have defined a `finite.card` that required you to
supply a `finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

## Main definitions

* `finite α` denotes that `α` is a finite type.
* `finite.of_fintype` creates a `finite` instance from a `fintype` instance.
* `fintype.of_finite` noncomputably creates a `fintype` instance from a `finite` instance.
* `finite_or_infinite` is that every type is either `finite` or `infinite`.

## Implementation notes

The definition of `finite α` is not just `nonempty (fintype α)` since `fintype` requires
that `α : Type*`, and the definition in this module allows for `α : Sort*`. This means
we can write the instance `finite.prop`.

There is an apparent duplication of many `fintype` instances in this module,
however they follow a pattern: if a `fintype` instance depends on `decidable`
instances or other `fintype` instances, then we need to "lower" the instance
to be a `finite` instance by removing the `decidable` instances and switching
the `fintype` instances to `finite` instances. These are precisely the ones
that cannot be inferred using `finite.of_fintype'`. (However, when using
`open_locale classical` or the `classical` tactic the instances relying only
on `decidable` instances will give `finite` instances.) In the future we might
consider writing automation to create these "lowered" instances.

Theorems about `nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `set_theory.cardinal.finite` module.

## Tags

finiteness, finite types

-/

noncomputable theory
open_locale classical

variables {α β γ : Type*}

/-- A type is `finite` if it is in bijective correspondence to some
`fin n`.

While this could be defined as `nonempty (fintype α)`, it is defined
in this way to allow there to be `finite` instances for propositions.
-/
class inductive finite (α : Sort*) : Prop
| intro {n : ℕ} : α ≃ fin n → finite

lemma finite.exists_equiv_fin (α : Sort*) [h : finite α] : ∃ (n : ℕ), nonempty (α ≃ fin n) :=
by { casesI h with n f, exact ⟨n, ⟨f⟩⟩ }

lemma finite.of_equiv (α : Sort*) {β : Sort*} [h : finite α] (f : α ≃ β) : finite β :=
by { casesI h with n e, exact finite.intro (f.symm.trans e) }

lemma finite_iff {α β : Sort*} (f : α ≃ β) : finite α ↔ finite β :=
⟨λ _, by exactI finite.of_equiv _ f, λ _, by exactI finite.of_equiv _ f.symm⟩

lemma finite.of_fintype {α : Type*} (h : fintype α) : finite α := ⟨fintype.equiv_fin α⟩

/-- For efficiency reasons, we want `finite` instances to have higher
priority than ones coming from `fintype` instances. -/
@[priority 900]
instance finite.of_fintype' (α : Type*) [fintype α] : finite α := finite.of_fintype ‹_›

/-- There is (noncomputably) an equivalence between a finite type `α` and `fin (nat.card α)`. -/
def finite.equiv_fin (α : Type*) [finite α] : α ≃ fin (nat.card α) :=
begin
  have := (finite.exists_equiv_fin α).some_spec.some,
  rwa nat.card_eq_of_equiv_fin this,
end

/-- Similar to `finite.equiv_fin` but with control over the term used for the cardinality. -/
def finite.equiv_fin_of_card_eq [finite α] {n : ℕ} (h : nat.card α = n) : α ≃ fin n :=
by { subst h, apply finite.equiv_fin }

/-- Noncomputably get a `fintype` instance from a `finite` instance. This is not an
instance because we want `fintype` instances to be useful for computations. -/
def fintype.of_finite (α : Type*) [finite α] : fintype α :=
fintype.of_equiv _ (finite.equiv_fin α).symm

lemma finite_iff_nonempty_fintype (α : Type*) :
  finite α ↔ nonempty (fintype α) :=
⟨λ _, by exactI ⟨fintype.of_finite α⟩, λ ⟨_⟩, by exactI infer_instance⟩

lemma finite_or_infinite (α : Type*) :
  finite α ∨ infinite α :=
begin
  casesI fintype_or_infinite α,
  { exact or.inl infer_instance },
  { exact or.inr infer_instance }
end

lemma not_finite (α : Type*) [h1 : infinite α] [h2 : finite α] : false :=
by { haveI := fintype.of_finite α, exact not_fintype α }

lemma finite.of_not_infinite {α : Type*} (h : ¬ infinite α) : finite α :=
finite.of_fintype (fintype_of_not_infinite h)

lemma infinite.of_not_finite {α : Type*} (h : ¬ finite α) : infinite α :=
⟨λ h', h (finite.of_fintype h')⟩

lemma not_infinite_iff_finite {α : Type*} : ¬ infinite α ↔ finite α :=
⟨finite.of_not_infinite, λ h h', by exactI not_finite α⟩

lemma not_finite_iff_infinite {α : Type*} : ¬ finite α ↔ infinite α :=
not_infinite_iff_finite.not_right.symm

lemma nat.card_eq (α : Type*) :
  nat.card α = if h : finite α then by exactI @fintype.card α (fintype.of_finite α) else 0 :=
begin
  casesI finite_or_infinite α,
  { haveI := fintype.of_finite α,
    simp only [*, nat.card_eq_fintype_card, dif_pos],
    congr, },
  { simp [*, not_finite_iff_infinite.mpr h] },
end

lemma finite.card_pos_iff [finite α] :
  0 < nat.card α ↔ nonempty α :=
begin
  haveI := fintype.of_finite α,
  simp only [nat.card_eq_fintype_card],
  exact fintype.card_pos_iff,
end

@[nolint instance_priority]
instance finite.prop (p : Prop) : finite p :=
if h : p
then ⟨(equiv.prop_equiv_punit h).trans (by simpa using fintype.equiv_fin punit)⟩
else ⟨(equiv.prop_equiv_pempty h).trans (by simpa using fintype.equiv_fin pempty)⟩

namespace finite

lemma exists_max [finite α] [nonempty α] [linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x ≤ f x₀ :=
by { haveI := fintype.of_finite α, exact fintype.exists_max f }

lemma exists_min [finite α] [nonempty α] [linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x₀ ≤ f x :=
by { haveI := fintype.of_finite α, exact fintype.exists_min f }

instance {α : Sort*} [finite α] : finite (plift α) := finite.of_equiv _ equiv.plift.symm

lemma of_bijective {α β : Sort*} [finite α] (f : α → β) (H : function.bijective f) : finite β :=
finite.of_equiv _ (equiv.of_bijective _ H)

lemma of_surjective {α β : Sort*} [finite α] (f : α → β) (H : function.surjective f) : finite β :=
begin
  haveI := fintype.of_finite (plift α),
  rw [← equiv.surjective_comp equiv.plift f, ← equiv.comp_surjective _ equiv.plift.symm] at H,
  haveI := fintype.of_surjective _ H,
  exact finite.of_equiv _ equiv.plift,
end

lemma of_injective {α β : Sort*} [finite β] (f : α → β) (H : function.injective f) : finite α :=
begin
  haveI := fintype.of_finite (plift β),
  rw [← equiv.injective_comp equiv.plift f, ← equiv.comp_injective _ equiv.plift.symm] at H,
  haveI := fintype.of_injective _ H,
  exact finite.of_equiv _ equiv.plift,
end

lemma card_eq [finite α] [finite β] : nat.card α = nat.card β ↔ nonempty (α ≃ β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp [fintype.card_eq] }

lemma of_subsingleton {α : Sort*} [subsingleton α] : finite α := finite.of_equiv _ equiv.plift

@[priority 100] -- see Note [lower instance priority]
instance of_is_empty {α : Sort*} [is_empty α] : finite α := finite.of_equiv _ equiv.plift

lemma card_le_one_iff_subsingleton [finite α] : nat.card α ≤ 1 ↔ subsingleton α :=
by { haveI := fintype.of_finite α, simp [fintype.card_le_one_iff_subsingleton] }

lemma one_lt_card_iff_nontrivial [finite α] : 1 < nat.card α ↔ nontrivial α :=
by { haveI := fintype.of_finite α, simp [fintype.one_lt_card_iff_nontrivial] }

lemma one_lt_card [finite α] [h : nontrivial α] : 1 < nat.card α :=
one_lt_card_iff_nontrivial.mpr h

@[simp] lemma card_option [finite α] : nat.card (option α) = nat.card α + 1 :=
by { haveI := fintype.of_finite α, simp }

lemma prod_left (β) [finite (α × β)] [nonempty β] : finite α :=
of_surjective (prod.fst : α × β → α) prod.fst_surjective

lemma prod_right (α) [finite (α × β)] [nonempty α] : finite β :=
of_surjective (prod.snd : α × β → β) prod.snd_surjective

instance [finite α] : finite (ulift α) :=
by { haveI := fintype.of_finite α, apply_instance }

instance [finite α] [finite β] : finite (α ⊕ β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, apply_instance }

lemma sum_left (β) [finite (α ⊕ β)] : finite α :=
of_injective (sum.inl : α → α ⊕ β) sum.inl_injective

lemma sum_right (α) [finite (α ⊕ β)] : finite β :=
of_injective (sum.inr : β → α ⊕ β) sum.inr_injective

lemma card_sum [finite α] [finite β] : nat.card (α ⊕ β) = nat.card α + nat.card β :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp }

lemma card_le_of_injective [finite β] (f : α → β) (hf : function.injective f) :
  nat.card α ≤ nat.card β :=
by { haveI := fintype.of_finite β, haveI := fintype.of_injective f hf,
     simpa using fintype.card_le_of_injective f hf }

lemma card_le_of_embedding [finite β] (f : α ↪ β) : nat.card α ≤ nat.card β :=
card_le_of_injective _ f.injective

lemma card_le_of_surjective [finite α] (f : α → β) (hf : function.surjective f) :
  nat.card β ≤ nat.card α :=
by { haveI := fintype.of_finite α, haveI := fintype.of_surjective f hf,
     simpa using fintype.card_le_of_surjective f hf }

lemma card_eq_zero_iff [finite α] : nat.card α = 0 ↔ is_empty α :=
by { haveI := fintype.of_finite α, simp [fintype.card_eq_zero_iff] }

end finite

instance subtype.finite {α : Sort*} [finite α] {p : α → Prop} : finite {x // p x} :=
begin
  haveI := fintype.of_finite (plift α),
  exact finite.of_equiv _ (equiv.subtype_equiv_of_subtype equiv.plift),
end

theorem finite.card_subtype_le [finite α] (p : α → Prop) :
  nat.card {x // p x} ≤ nat.card α :=
by { haveI := fintype.of_finite α, simpa using fintype.card_subtype_le p }

theorem finite.card_subtype_lt [finite α] {p : α → Prop} {x : α} (hx : ¬ p x) :
  nat.card {x // p x} < nat.card α :=
by { haveI := fintype.of_finite α, simpa using fintype.card_subtype_lt hx }

instance pi.finite {α : Sort*} {β : α → Sort*} [finite α] [∀ a, finite (β a)] : finite (Π a, β a) :=
begin
  haveI := fintype.of_finite (plift α),
  haveI := λ a, fintype.of_finite (plift (β a)),
  exact finite.of_equiv (Π (a : plift α), plift (β (equiv.plift a)))
    (equiv.Pi_congr equiv.plift (λ _, equiv.plift)),
end

instance vector.finite {α : Type*} [finite α] {n : ℕ} : finite (vector α n) :=
by { haveI := fintype.of_finite α, apply_instance }

instance quot.finite {α : Sort*} [finite α] (r : α → α → Prop) : finite (quot r) :=
finite.of_surjective _ (surjective_quot_mk r)

instance quotient.finite {α : Sort*} [finite α] (s : setoid α) : finite (quotient s) :=
quot.finite _

instance equiv.finite_left {α β : Sort*} [finite α] : finite (α ≃ β) :=
begin
  casesI is_empty_or_nonempty (α ≃ β) with _ h,
  { apply_instance },
  { refine h.elim (λ f, _),
    haveI := finite.of_equiv _ f,
    haveI := fintype.of_finite (plift α),
    haveI := fintype.of_finite (plift β),
    exact finite.of_equiv _ (equiv.equiv_congr equiv.plift equiv.plift), },
end

instance equiv.finite_right {α β : Sort*} [finite β] : finite (α ≃ β) :=
finite.of_equiv _ ⟨equiv.symm, equiv.symm, equiv.symm_symm, equiv.symm_symm⟩

instance function.embedding.finite {α β : Sort*} [finite β] : finite (α ↪ β) :=
begin
  casesI is_empty_or_nonempty (α ↪ β) with _ h,
  { apply_instance, },
  { refine h.elim (λ f, _),
    haveI := finite.of_injective _ f.injective,
    haveI := fintype.of_finite (plift α),
    haveI := fintype.of_finite (plift β),
    exact finite.of_equiv _ (equiv.embedding_congr equiv.plift equiv.plift), },
end

instance [finite α] {n : ℕ} : finite (sym α n) :=
by { haveI := fintype.of_finite α, apply_instance }
