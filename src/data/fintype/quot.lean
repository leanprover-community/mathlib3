/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.finset.quot
import data.fintype.basic

/-!
# Quotients indexed by a finite type
-/

namespace fintype
variables {ι : Type*} [fintype ι] [decidable_eq ι] {α : ι → Type*} [s : Π i, setoid (α i)]
  {β : Sort*}
include s

def quotient_lift_on (q : Π i, quotient (s i)) (f : (Π i, α i) → β)
  (h : ∀ (a b : Π i, α i), (∀ i, a i ≈ b i) → f a = f b) : β :=
finset.quotient_lift_on (λ i hi, q i) (λ a, f (λ i, a i (finset.mem_univ _)))
  (λ a b H, h _ _ (λ i, H i (finset.mem_univ _)))

def quotient_lift (f : (Π i, α i) → β)
  (h : ∀ (a b : Π i, α i), (∀ i, a i ≈ b i) → f a = f b)
  (q : Π i, quotient (s i)) : β :=
quotient_lift_on q f h

@[simp] lemma quotient_lift_on_empty [e : is_empty ι] (q : Π i, quotient (s i)) :
  @quotient_lift_on _ _ _ _ _ β q = λ f h, f e.elim :=
begin
  ext f h, dsimp [quotient_lift_on],
  transitivity
    finset.quotient_lift_on (λ i ∈ ∅, q i) (λ (a : Π i ∈ ∅, α i), f (λ i, e.elim i)) (λ _ _ _, rfl),
  { congr', { exact finset.univ_eq_empty }, { rw [finset.univ_eq_empty] },
    { rw [← finset.univ_eq_empty, heq_iff_eq], ext a, congr, } },
  { rw [finset.quotient_lift_on_empty] }
end

@[simp] lemma quotient_lift_on_mk (a : Π i, α i) :
  @quotient_lift_on _ _ _ _ _ β (λ i, ⟦a i⟧) = λ f h, f a :=
by { ext f h, dsimp [quotient_lift_on], rw [finset.quotient_lift_on_mk] }

@[simp] lemma quotient_lift_empty [e : is_empty ι] (f : (Π i ∈ (∅ : finset ι), α i) → β) (h) :
  quotient_lift f h = (λ q, f e.elim) :=
by { ext f h, dsimp [quotient_lift], rw [quotient_lift_on_empty] }

@[simp] lemma quotient_lift_mk (f : (Π i, α i) → β)
  (h : ∀ (a b : Π i, α i), (∀ i, a i ≈ b i) → f a = f b)
  (a : Π i, α i) : quotient_lift f h (λ i, ⟦a i⟧) = f a :=
by { dsimp [quotient_lift], rw [quotient_lift_on_mk] }

/-- A choice-free induction principle for quotients indexed by a finite type.
  See `quotient.induction_on_pi` for the general version using `classical.choice`. -/
@[nolint decidable_classical fintype_finite, elab_as_eliminator]
lemma quotient_ind {C : (Π i, quotient (s i)) → Prop}
  (f : ∀ a : Π i, α i, C (λ i, ⟦a i⟧)) (q : Π i, quotient (s i)) : C q :=
@finset.quotient_ind _ _ _ _ _ (λ q, C (λ i, q i (finset.mem_univ _))) (λ a, f _) (λ i hi, q i)

/-- A choice-free induction principle for quotients indexed by a finite type.
  See `quotient.induction_on_pi` for the general version using `classical.choice`. -/
@[nolint decidable_classical fintype_finite, elab_as_eliminator]
lemma quotient_induction_on {C : (Π i, quotient (s i)) → Prop}
  (q : Π i, quotient (s i)) (f : ∀ a : Π i, α i, C (λ i, ⟦a i⟧)) :
  C q :=
quotient_ind f q

@[elab_as_eliminator] def quotient_rec_on {C : (Π i, quotient (s i)) → Sort*}
  (q : Π i, quotient (s i))
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i), (eq.rec (f a)
    (funext (λ i, quotient.sound (h i)) : (λ i, ⟦a i⟧) = (λ i, ⟦b i⟧)) : C (λ i, ⟦b i⟧)) = f b) :
  C q :=
@finset.quotient_rec_on _ _ _ _ _ (λ q, C (λ i, q i (finset.mem_univ _)))
  (λ i hi, q i) (λ a, f (λ i, a i (finset.mem_univ _)))
  (λ a b H, by { simp_rw [← h _ _ (λ i, H i (finset.mem_univ _)), ← heq_iff_eq],
    exact (eq_rec_heq _ _).trans (eq_rec_heq _ _).symm, })

@[elab_as_eliminator] def quotient_rec {C : (Π i, quotient (s i)) → Sort*}
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i), (eq.rec (f a)
    (funext (λ i, quotient.sound (h i)) : (λ i, ⟦a i⟧) = (λ i, ⟦b i⟧)) : C (λ i, ⟦b i⟧)) = f b)
  (q : Π i, quotient (s i)) :
  C q :=
quotient_rec_on q f h

@[elab_as_eliminator] def quotient_hrec_on {C : (Π i, quotient (s i)) → Sort*}
  (q : Π i, quotient (s i))
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i), f a == f b) :
  C q :=
quotient_rec_on q f (λ a b p, eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))

@[simp] lemma quotient_rec_mk {C : (Π i, quotient (s i)) → Sort*}
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h) (a : Π i, α i) :
  @quotient_rec _ _ _ _ _ C f h (λ i, ⟦a i⟧) = f a :=
finset.quotient_rec_mk _ _ _

@[simp] lemma quotient_rec_on_mk {C : (Π i, quotient (s i)) → Sort*}
  (a : Π i, α i) :
  @quotient_rec_on _ _ _ _ _ C (λ i, ⟦a i⟧) = λ f h, f a :=
by { ext f h, exact quotient_rec_mk _ _ _ }

end fintype
