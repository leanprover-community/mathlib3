/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.finset.basic
import data.multiset.quot

/-!
# Quotients indexed by a `finset`

In this file, we define lifting and recursion principle for quotients indexed by a `finset`.
-/

namespace finset
variables {ι : Type*} [decidable_eq ι] {α : ι → Type*} [S : Π i, setoid (α i)] {β : Sort*}
include S

/-- Given a collection of setoids indexed by a type `ι`, a finset `s` of indices, and a function
  that for each `i ∈ s` gives a term of the corresponding quotient type, then there is a
  corresponding term in the quotient of the product of the setoids indexed by `s`. -/
def quotient_choice {s : finset ι} (q : Π i ∈ s, quotient (S i)) :
  @quotient (Π i ∈ s, α i) pi_setoid :=
multiset.quotient_choice q

theorem quotient_choice_mk {s : finset ι} (a : Π i ∈ s, α i) :
  quotient_choice (λ i h, ⟦a i h⟧) = ⟦a⟧ :=
multiset.quotient_choice_mk a

/-- Lift a function on `Π i ∈ s, α i` to `Π i ∈ s, quotient (S i)`. -/
def quotient_lift_on {s : finset ι} (q : Π i ∈ s, quotient (S i)) (f : (Π i ∈ s, α i) → β)
  (h : ∀ (a b : Π i ∈ s, α i), (∀ i (hi : i ∈ s), a i hi ≈ b i hi) → f a = f b) : β :=
multiset.quotient_lift_on q f h

/-- Lift a function on `Π i ∈ s, α i` to `Π i ∈ s, quotient (S i)`. -/
def quotient_lift {s : finset ι} (f : (Π i ∈ s, α i) → β)
  (h : ∀ (a b : Π i ∈ s, α i), (∀ i (hi : i ∈ s), a i hi ≈ b i hi) → f a = f b)
  (q : Π i ∈ s, quotient (S i)) : β :=
quotient_lift_on q f h

@[simp] lemma quotient_lift_on_empty (q : Π i ∈ (∅ : finset ι), quotient (S i)) :
  @quotient_lift_on _ _ _ _ β _ q = λ f h, f (λ i hi, hi.elim) :=
rfl

@[simp] lemma quotient_lift_on_mk {s : finset ι} (a : Π i ∈ s, α i) :
  @quotient_lift_on _ _ _ _ β _ (λ i hi, ⟦a i hi⟧) = λ f h, f a :=
multiset.quotient_lift_on_mk a

@[simp] lemma quotient_lift_empty (f : (Π i ∈ (∅ : finset ι), α i) → β) (h) :
  quotient_lift f h = (λ q, f (λ i hi, hi.elim)) :=
rfl

@[simp] lemma quotient_lift_mk {s : finset ι} (f : (Π i ∈ s, α i) → β)
  (h : ∀ (a b : Π i ∈ s, α i), (∀ i (hi : i ∈ s), a i hi ≈ b i hi) → f a = f b)
  (a : Π i ∈ s, α i) : quotient_lift f h (λ i hi, ⟦a i hi⟧) = f a :=
multiset.quotient_lift_mk f h a

/-- Choice-free induction principle for quotients indexed by a `finset`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_ind {s : finset ι} {C : (Π i ∈ s, quotient (S i)) → Prop}
  (f : ∀ a : Π i ∈ s, α i, C (λ i hi, ⟦a i hi⟧)) (q : Π i ∈ s, quotient (S i)) : C q :=
multiset.quotient_ind f q

/-- Choice-free induction principle for quotients indexed by a `finset`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_induction_on {s : finset ι}
  {C : (Π i ∈ s, quotient (S i)) → Prop}
  (q : Π i ∈ s, quotient (S i)) (f : ∀ a : Π i ∈ s, α i, C (λ i hi, ⟦a i hi⟧)) :
  C q :=
quotient_ind f q

/-- Recursion principle for quotients indexed by a `finset`. -/
@[elab_as_eliminator] def quotient_rec_on {s : finset ι}
  {C : (Π i ∈ s, quotient (S i)) → Sort*}
  (q : Π i ∈ s, quotient (S i))
  (f : Π a : Π i ∈ s, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ s, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
    (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
      C (λ i hi, ⟦b i hi⟧)) = f b) :
  C q :=
multiset.quotient_rec_on q f h

/-- Recursion principle for quotients indexed by a `finset`. -/
@[elab_as_eliminator] def quotient_rec {s : finset ι} {C : (Π i ∈ s, quotient (S i)) → Sort*}
  (f : Π a : Π i ∈ s, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ s, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
    (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
      C (λ i hi, ⟦b i hi⟧)) = f b)
  (q : Π i ∈ s, quotient (S i)) :
  C q :=
quotient_rec_on q f h

/-- Recursion principle for quotients indexed by a `finset`. -/
@[elab_as_eliminator] def quotient_hrec_on {s : finset ι} {C : (Π i ∈ s, quotient (S i)) → Sort*}
  (q : Π i ∈ s, quotient (S i))
  (f : Π a : Π i ∈ s, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ s, α i) (h : ∀ i hi, a i hi ≈ b i hi), f a == f b) :
  C q :=
quotient_rec_on q f (λ a b p, eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))

@[simp] lemma quotient_rec_mk {s : finset ι} {C : (Π i ∈ s, quotient (S i)) → Sort*}
  (f : Π a : Π i ∈ s, α i, C (λ i hi, ⟦a i hi⟧))
  (h) (a : Π i ∈ s, α i) :
  @quotient_rec _ _ _ _ _ C f h (λ i hi, ⟦a i hi⟧) = f a :=
multiset.quotient_rec_mk f h a

@[simp] lemma quotient_rec_on_mk {s : finset ι} {C : (Π i ∈ s, quotient (S i)) → Sort*}
  (a : Π i ∈ s, α i) :
  @quotient_rec_on _ _ _ _ _ C (λ i hi, ⟦a i hi⟧) = λ f h, f a :=
multiset.quotient_rec_on_mk a

end finset
