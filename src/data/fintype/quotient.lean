/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yuyang Zhao
-/
import data.list.pi
import data.fintype.basic

/-!
# Quotients of families indexed by a finite type

This file proves some basic facts and defines lifting and recursion principle for quotients indexed
by a finite type.

## Main definitions

* `fintype.quotient_choice_equiv`: A finite family of quotients is equivalent to a quotient of
  finite families.
* `fintype.quotient_lift_on`: Given a fintype `ι`. A function on `Π i : ι, α i` which respects
  setoid `S i` for each `i` can be lifted to a function on `Π i : ι, quotient (S i)`.
* `fintype.quotient_rec_on`: Recursion principle for quotients indexed by a finite type. It is the
  dependent version of `fintype.quotient_lift_on`.
-/

namespace list
variables {ι : Type*} [decidable_eq ι] {α : ι → Sort*} [S : Π i, setoid (α i)] {β : Sort*}
include S

/-- Given a collection of setoids indexed by a type `ι`, a list `l` of indices, and a function that
  for each `i ∈ l` gives a term of the corresponding quotient type, then there is a corresponding
  term in the quotient of the product of the setoids indexed by `l`. -/
def quotient_choice : Π {l : list ι},
  (Π i ∈ l, quotient (S i)) → @quotient (Π i ∈ l, α i) pi_setoid
| []       q := ⟦λ i, false.elim⟧
| (i :: l) q := quotient.lift_on₂ (q i (mem_cons_self _ _))
    (quotient_choice (λ j hj, q j (mem_cons_of_mem _ hj)))
    (λ a l, ⟦pi.cons a l⟧)
    (λ _ _ _ _ ha hl, quotient.sound (pi.forall_rel_cons_ext (λ _, (≈)) ha hl))

theorem quotient_choice_mk : ∀ {l : list ι}
  (a : Π i ∈ l, α i), quotient_choice (λ i h, ⟦a i h⟧) = ⟦a⟧
| []       f := quotient.sound (λ i hi, hi.elim)
| (i :: l) f := begin
  rw [quotient_choice, quotient_choice_mk],
  exact congr_arg quotient.mk (pi.cons_eta f),
end

/-- Choice-free induction principle for quotients indexed by a `list`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_ind : Π {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Prop}
  (f : ∀ a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧)) (q : Π i ∈ l, quotient (S i)), C q
| []     C f q := cast (congr_arg _ (funext₂ (λ i hi, hi.elim))) (f (λ i hi, hi.elim))
| (i::l) C f q := begin
  rw [← pi.cons_eta q],
  induction (q i (mem_cons_self _ _)) using quotient.ind,
  refine @quotient_ind _ (λ q, C (pi.cons ⟦a⟧ q)) _ (λ j hj, q j (mem_cons_of_mem _ hj)),
  intros as,
  rw [← pi.map_cons a as],
  exact f _,
end

end list

namespace fintype
variables {ι : Type*} [fintype ι] [dec : decidable_eq ι] {α : ι → Sort*} [S : Π i, setoid (α i)]
  {β : Sort*}
include dec S

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `quotient.induction_on_pi` for the general version assuming `classical.choice`. -/
@[nolint decidable_classical fintype_finite, elab_as_eliminator]
lemma quotient_ind {C : (Π i, quotient (S i)) → Prop}
  (f : ∀ a : Π i, α i, C (λ i, ⟦a i⟧)) (q : Π i, quotient (S i)) : C q :=
begin
  have : ∀ {m : multiset ι} (C : (Π i ∈ m, quotient (S i)) → Prop)
    (f : ∀ a : Π i ∈ m, α i, C (λ i hi, ⟦a i hi⟧)) (q : Π i ∈ m, quotient (S i)), C q,
  { intros m C, induction m using quotient.ind, exact list.quotient_ind, },
  exact this (λ q, C (λ i, q i (finset.mem_univ _))) (λ a, f _) (λ i hi, q i),
end

/-- Choice-free induction principle for quotients indexed by a finite type.
  See `quotient.induction_on_pi` for the general version assuming `classical.choice`. -/
@[nolint decidable_classical fintype_finite, elab_as_eliminator]
lemma quotient_induction_on {C : (Π i, quotient (S i)) → Prop}
  (q : Π i, quotient (S i)) (f : ∀ a : Π i, α i, C (λ i, ⟦a i⟧)) :
  C q :=
quotient_ind f q

/-- Given a collection of setoids indexed by a fintype `ι` and a function that for each `i : ι`
  gives a term of the corresponding quotient type, then there is corresponding term in the quotient
  of the product of the setoids. -/
def quotient_choice (q : Π i, quotient (S i)) :
  @quotient (Π i, α i) pi_setoid :=
begin
  let := equiv.subtype_quotient_equiv_quotient_subtype (λ l : list ι, ∀ i, i ∈ l)
    (λ s : multiset ι, ∀ i, i ∈ s) (λ i, iff.rfl) (λ _ _, iff.rfl) ⟨_, finset.mem_univ⟩,
  refine this.lift_on
    (λ l, (list.quotient_choice (λ i ∈ l.1, q i)).map (λ a i, a i (l.2 i)) (λ _ _ h i, h i _)) _,
  intros _ _ _, dsimp,
  refine quotient_ind (λ a, _) q,
  simp_rw [list.quotient_choice_mk, quotient.map_mk]
end

theorem quotient_choice_mk (a : Π i, α i) :
  quotient_choice (λ i, ⟦a i⟧) = ⟦a⟧ :=
begin
  dsimp [quotient_choice],
  obtain ⟨l, hl⟩ := (finset.univ.val : multiset ι).exists_rep,
  simp_rw [← hl, equiv.subtype_quotient_equiv_quotient_subtype_mk, list.quotient_choice_mk],
  refl,
end

alias quotient_choice ← _root_.quotient.fin_choice

lemma _root_.quotient.fin_choice_eq (a : Π i, α i) :
  quotient.fin_choice (λ i, ⟦a i⟧) = ⟦a⟧ :=
quotient_choice_mk a

/-- Lift a function on `Π i, α i` to a function on `Π i, quotient (S i)`. -/
def quotient_lift_on (q : Π i, quotient (S i)) (f : (Π i, α i) → β)
  (h : ∀ (a b : Π i, α i), (∀ i, a i ≈ b i) → f a = f b) : β :=
quotient.lift f h (quotient_choice q)

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

/-- `quotient_choice` as an equivalence. -/
@[simps] def quotient_choice_equiv {l : list ι} :
  (Π i, quotient (S i)) ≃ @quotient (Π i, α i) pi_setoid :=
{ to_fun := quotient_choice,
  inv_fun := λ q i, q.map (λ a, a i) (λ _ _ ha, ha i),
  left_inv := λ q, by
    { refine quotient_induction_on q (λ a, _), rw [quotient_choice_mk], refl },
  right_inv := λ q, by { induction q using quotient.ind, exact quotient_choice_mk _ } }

section quotient_rec
variables {C : (Π i, quotient (S i)) → Sort*} (f : ∀ a : Π i, α i, C (λ i, ⟦a i⟧))

omit dec S

@[reducible]
private def quotient_rec.indep (a : Π i, α i) : psigma C := ⟨λ i, ⟦a i⟧, f a⟩

variables (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i),
  (eq.rec (f a) (funext (λ i, quotient.sound (h i)) : (λ i, ⟦a i⟧) = (λ i, ⟦b i⟧)) :
    C (λ i, ⟦b i⟧)) = f b)

private lemma quotient_rec.indep_coherent :
  ∀ a b : Π i, α i, (∀ i, a i ≈ b i) →
    quotient_rec.indep f a = quotient_rec.indep f b :=
λ a b e, psigma.eq (funext (λ i, quotient.sound (e i))) (h a b e)

include h dec

private lemma quotient_rec.lift_indep_pr1 (q : Π i, quotient (S i)) :
  (quotient_lift_on q (quotient_rec.indep f) (quotient_rec.indep_coherent f h)).1 = q :=
quotient_ind (λ a, funext (λ i, by rw [quotient_lift_on_mk])) q

end quotient_rec

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_eliminator] def quotient_rec_on {C : (Π i, quotient (S i)) → Sort*}
  (q : Π i, quotient (S i))
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i),
    (eq.rec (f a) (funext (λ i, quotient.sound (h i)) : (λ i, ⟦a i⟧) = (λ i, ⟦b i⟧)) :
      C (λ i, ⟦b i⟧)) = f b) :
  C q :=
eq.rec_on (quotient_rec.lift_indep_pr1 f h q)
  ((quotient_lift_on q (quotient_rec.indep f) (quotient_rec.indep_coherent f h)).2)

/-- Recursion principle for quotients indexed by a finite type. -/
@[elab_as_eliminator] def quotient_hrec_on {C : (Π i, quotient (S i)) → Sort*}
  (q : Π i, quotient (S i))
  (f : Π a : Π i, α i, C (λ i, ⟦a i⟧))
  (h : ∀ (a b : Π i, α i) (h : ∀ i, a i ≈ b i), f a == f b) :
  C q :=
quotient_rec_on q f (λ a b p, eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))

@[simp] lemma quotient_rec_on_mk {C : (Π i, quotient (S i)) → Sort*}
  (a : Π i, α i) :
  @quotient_rec_on _ _ _ _ _ C (λ i, ⟦a i⟧) = λ f h, f a :=
begin
  ext f h, dsimp [quotient_rec_on], refine eq_of_heq ((eq_rec_heq _ _).trans _),
  rw [quotient_lift_on_mk a],
end

@[simp] lemma quotient_hrec_on_mk {C : (Π i, quotient (S i)) → Sort*}
  (a : Π i, α i) :
  @quotient_hrec_on _ _ _ _ _ C (λ i, ⟦a i⟧) = λ f h, f a :=
by { ext f h, dsimp [quotient_hrec_on], rw [quotient_rec_on_mk], }

end fintype
