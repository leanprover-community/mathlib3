/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.finset.quot
import data.fintype.basic

/-!
# Quotients indexed by a finite type

In this file, we define lifting and recursion principle for quotients indexed by a finite type.

## Main definitions

* `fintype.quotient_lift`: Given a fintype `ι`. A function on `Π i : ι, α i` which respects setoid
  `S i` for each `i` can be lifted to a function on `Π i : ι, quotient (S i)`.
* `fintype.quotient_rec`: Recursion principle for quotients indexed by a finite type. It is the
  dependent version of `finset.quotient_lift`.
-/

namespace fintype
variables {ι : Type*} [fintype ι] [decidable_eq ι] {α : ι → Sort*} [S : Π i, setoid (α i)]
  {β : Sort*}
include S

/-- Given a collection of setoids indexed by a fintype `ι` and a function that for each `i : ι`
  gives a term of the corresponding quotient type, then there is corresponding term in the quotient
  of the product of the setoids. -/
def quotient_choice (q : Π i, quotient (S i)) :
  @quotient (Π i, α i) pi_setoid :=
finset.quotient_lift_on (λ i (hi : i ∈ (⊤ : finset ι)), q i) (λ a, ⟦λ i, a i (finset.mem_univ _)⟧)
  (λ a₁ a₂ ha, quotient.sound (λ i, ha i _))

theorem quotient_choice_mk (a : Π i, α i) :
  quotient_choice (λ i, ⟦a i⟧) = ⟦a⟧ :=
by { dsimp [quotient_choice], rw [finset.quotient_lift_on_mk (λ i hi, a i)], }

alias quotient_choice ← _root_.quotient.fin_choice

lemma _root_.quotient.fin_choice_eq (a : Π i, α i) :
  quotient.fin_choice (λ i, ⟦a i⟧) = ⟦a⟧ :=
quotient_choice_mk a

/-- Lift a function on `Π i, α i` to a function on `Π i, quotient (S i)`. -/
def quotient_lift_on (q : Π i, quotient (S i)) (f : (Π i, α i) → β)
  (h : ∀ (a b : Π i, α i), (∀ i, a i ≈ b i) → f a = f b) : β :=
quotient.lift f h (quotient_choice q)

/-- Lift a function on `Π i, α i` to a function on `Π i, quotient (S i)`. -/
def quotient_lift (f : (Π i, α i) → β)
  (h : ∀ (a b : Π i, α i), (∀ i, a i ≈ b i) → f a = f b)
  (q : Π i, quotient (S i)) : β :=
quotient_lift_on q f h

@[simp] lemma quotient_lift_on_empty [e : is_empty ι] (q : Π i, quotient (S i)) :
  @quotient_lift_on _ _ _ _ _ β q = λ f h, f e.elim :=
begin
  ext f h, dsimp [quotient_lift_on],
  induction quotient_choice q using quotient.ind,
  exact h _ _ e.elim,
end

@[simp] lemma quotient_lift_on_mk (a : Π i, α i) :
  @quotient_lift_on _ _ _ _ _ β (λ i, ⟦a i⟧) = λ f h, f a :=
by { ext f h, dsimp [quotient_lift_on], rw [quotient_choice_mk], refl, }

@[simp] lemma quotient_lift_empty [e : is_empty ι] (f : (Π i ∈ (∅ : finset ι), α i) → β) (h) :
  quotient_lift f h = (λ q, f e.elim) :=
by { ext f h, dsimp [quotient_lift], rw [quotient_lift_on_empty] }

@[simp] lemma quotient_lift_mk (f : (Π i, α i) → β)
  (h : ∀ (a b : Π i, α i), (∀ i, a i ≈ b i) → f a = f b)
  (a : Π i, α i) : quotient_lift f h (λ i, ⟦a i⟧) = f a :=
by { dsimp [quotient_lift], rw [quotient_lift_on_mk] }

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `quotient.induction_on_pi` for the general version assuming `classical.choice`. -/
@[nolint decidable_classical fintype_finite, elab_as_eliminator]
lemma quotient_ind {C : (Π i, quotient (S i)) → Prop}
  (f : ∀ a : Π i, α i, C (λ i, ⟦a i⟧)) (q : Π i, quotient (S i)) : C q :=
@finset.quotient_ind _ _ _ _ _ (λ q, C (λ i, q i (finset.mem_univ _))) (λ a, f _) (λ i hi, q i)

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `quotient.induction_on_pi` for the general version assuming `classical.choice`. -/
@[nolint decidable_classical fintype_finite, elab_as_eliminator]
lemma quotient_induction_on {C : (Π i, quotient (S i)) → Prop}
  (q : Π i, quotient (S i)) (f : ∀ a : Π i, α i, C (λ i, ⟦a i⟧)) :
  C q :=
quotient_ind f q

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_eliminator] def quotient_rec_on {C : (Π i, quotient (S i)) → Sort*}
  (q : Π i, quotient (S i))
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i), (eq.rec (f a)
    (funext (λ i, quotient.sound (h i)) : (λ i, ⟦a i⟧) = (λ i, ⟦b i⟧)) : C (λ i, ⟦b i⟧)) = f b) :
  C q :=
@finset.quotient_rec_on _ _ _ _ _ (λ q, C (λ i, q i (finset.mem_univ _)))
  (λ i hi, q i) (λ a, f (λ i, a i _))
  (λ a b H, by { simp_rw [← h _ _ (λ i, H i (finset.mem_univ _))],
    exact eq_of_heq ((eq_rec_heq _ _).trans (eq_rec_heq _ _).symm), })

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_eliminator] def quotient_rec {C : (Π i, quotient (S i)) → Sort*}
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i), (eq.rec (f a)
    (funext (λ i, quotient.sound (h i)) : (λ i, ⟦a i⟧) = (λ i, ⟦b i⟧)) : C (λ i, ⟦b i⟧)) = f b)
  (q : Π i, quotient (S i)) :
  C q :=
quotient_rec_on q f h

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_eliminator] def quotient_hrec_on {C : (Π i, quotient (S i)) → Sort*}
  (q : Π i, quotient (S i))
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i), f a == f b) :
  C q :=
quotient_rec_on q f (λ a b p, eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))

@[simp] lemma quotient_rec_mk {C : (Π i, quotient (S i)) → Sort*}
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h) (a : Π i, α i) :
  @quotient_rec _ _ _ _ _ C f h (λ i, ⟦a i⟧) = f a :=
finset.quotient_rec_mk _ _ _

@[simp] lemma quotient_rec_on_mk {C : (Π i, quotient (S i)) → Sort*}
  (a : Π i, α i) :
  @quotient_rec_on _ _ _ _ _ C (λ i, ⟦a i⟧) = λ f h, f a :=
by { ext f h, exact quotient_rec_mk _ _ _ }

end fintype
