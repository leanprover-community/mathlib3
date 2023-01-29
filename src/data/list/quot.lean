/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import data.list.basic
import data.quot

/-!
# Quotients indexed by a `list`

In this file, we define lifting and recursion principle for quotients indexed by a `list`.

## Main definitions

* `list.quotient_lift`: Given `l : list ι`. A function on `Π i ∈ l, α i` which respects setoid `S i`
  for each `i` in `l` can be lifted to a function on `Π i ∈ l, quotient (S i)`.
* `list.quotient_rec`: Recursion principle for quotients indexed by a `list`. It is the dependent
  version of `list.quotient_lift`.
-/

namespace list
variables {ι : Type*} [dec : decidable_eq ι] {α : ι → Sort*} [S : Π i, setoid (α i)] {β : Sort*}

include dec

namespace pi_mem_cons

/-- A constructor for `Π j ∈ (i :: l), α j`, by giving the value at `i` and a function on `l`.

The inverse functions are `pi_mem_cons.head` and `pi_mem_cons.tail`.
-/
def cons {i : ι} {l : list ι} (h : α i) (t : Π j ∈ l, α j) :
  Π j ∈ (i :: l), α j :=
λ j hj, if H : j = i then (congr_arg α H).mpr h else t j (hj.resolve_left H)

omit dec

/-- `pi_mem_cons.head f` gives the value of `f : Π j ∈ (i :: l), α j` at `i`. -/
def head {i : ι} {l : list ι} (f : Π j ∈ (i :: l), α j) :
  α i :=
f i (mem_cons_self _ _)

/-- `pi_mem_cons.tail f` restricts `f : Π j ∈ (i :: l), α j` to `l`. -/
def tail {i : ι} {l : list ι} (f : Π j ∈ (i :: l), α j) :
  Π j ∈ l, α j :=
λ j hj, f j (mem_cons_of_mem _ hj)

include dec

@[simp] lemma eta {i : ι} {l : list ι} (f : Π j ∈ (i :: l), α j) :
  cons (head f) (tail f) = f :=
by { ext j hj, dsimp [cons], split_ifs with H, { cases H, refl }, { refl } }

@[simp] lemma head_cons {i : ι} {l : list ι} (h : α i) (t : Π j ∈ l, α j) :
  head (cons h t) = h :=
by simp [head, cons]

lemma tail_cons {i : ι} {l : list ι} (hl : (i :: l).nodup) (h : α i) (t : Π j ∈ l, α j) :
  tail (cons h t) = t :=
by { ext j hj, obtain ⟨hl, _⟩ := pairwise_cons.mp hl, simpa [tail, cons, (hl j hj).symm] }

@[simp] lemma cons_apply {i : ι} {l : list ι} (h : α i) (t : Π j ∈ l, α j)
  {α' : ι → Sort*} (f : ∀ ⦃j⦄, α j → α' j):
  cons (f h) (λ j hj, f (t j hj)) = λ j hj, f ((cons h t) j hj) :=
by { ext j hj, dsimp [cons], split_ifs with H, { cases H, refl }, { refl }, }

include S

lemma setoid_congr {i : ι} {l : list ι} {h₁ h₂ : α i} {t₁ t₂ : Π j ∈ l, α j}
  (hh : h₁ ≈ h₂) (ht : ∀ (i : ι) (hi : i ∈ l), t₁ i hi ≈ t₂ i hi) :
  ∀ j hj, cons h₁ t₁ j hj ≈ cons h₂ t₂ j hj :=
by { intros j hj, dsimp [cons], split_ifs with H, { cases H, exact hh }, { exact ht _ _, } }

end pi_mem_cons

include S

/-- Given a collection of setoids indexed by a type `ι`, a list `l` of indices, and a function that
  for each `i ∈ l` gives a term of the corresponding quotient type, then there is a corresponding
  term in the quotient of the product of the setoids indexed by `l`. -/
def quotient_choice : Π {l : list ι},
  (Π i ∈ l, quotient (S i)) → @quotient (Π i ∈ l, α i) pi_setoid
| []       q := ⟦λ i, false.elim⟧
| (i :: l) q := quotient.lift_on₂ (@pi_mem_cons.head _ _ _ _ q)
    (quotient_choice (pi_mem_cons.tail q))
    (λ a l, ⟦pi_mem_cons.cons a l⟧)
    (λ _ _ _ _ ha hl, quotient.sound (pi_mem_cons.setoid_congr ha hl))

theorem quotient_choice_mk : ∀ {l : list ι}
  (a : Π i ∈ l, α i), quotient_choice (λ i h, ⟦a i h⟧) = ⟦a⟧
| []       f := quotient.sound (λ i hi, hi.elim)
| (i :: l) f := begin
  rw [quotient_choice, pi_mem_cons.tail, quotient_choice_mk],
  exact congr_arg quotient.mk (pi_mem_cons.eta f),
end

/-- Lift a function on `Π i ∈ l, α i` to a function on `Π i ∈ l, quotient (S i)`. -/
def quotient_lift {l : list ι} (f : (Π i ∈ l, α i) → β)
  (h : ∀ (a b : Π i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b)
  (q : Π i ∈ l, quotient (S i)) : β :=
quotient.lift f h (quotient_choice q)

/-- Lift a function on `Π i ∈ l, α i` to a function on `Π i ∈ l, quotient (S i)`. -/
def quotient_lift_on {l : list ι} (q : Π i ∈ l, quotient (S i)) (f : (Π i ∈ l, α i) → β)
  (h : ∀ (a b : Π i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b) : β :=
quotient_lift f h q

@[simp] lemma quotient_lift_nil (f : (Π i ∈ ([] : list ι), α i) → β) (h) :
  quotient_lift f h = λ q, f (λ i hi, hi.elim) :=
rfl

@[simp] lemma quotient_lift_mk {l : list ι} (f : (Π i ∈ l, α i) → β)
  (h : ∀ (a b : Π i ∈ l, α i), (∀ i (hi : i ∈ l), a i hi ≈ b i hi) → f a = f b)
  (a : Π i ∈ l, α i) : quotient_lift f h (λ i hi, ⟦a i hi⟧) = f a :=
by { dsimp [quotient_lift], rw [quotient_choice_mk], refl }

@[simp] lemma quotient_lift_on_nil (q : Π i ∈ ([] : list ι), quotient (S i)) :
  @quotient_lift_on _ _ _ _ β _ q = λ f h, f (λ i hi, hi.elim) :=
rfl

@[simp] lemma quotient_lift_on_mk {l : list ι} (a : Π i ∈ l, α i) :
  @quotient_lift_on _ _ _ _ β _ (λ i hi, ⟦a i hi⟧) = λ f h, f a :=
by { ext f h, exact quotient_lift_mk f h a, }

/-- Choice-free induction principle for quotients indexed by a `list`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_ind : Π {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Prop}
  (f : ∀ a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧)) (q : Π i ∈ l, quotient (S i)), C q
| []     C f q := cast (congr_arg _ (funext₂ (λ i hi, hi.elim))) (f (λ i hi, hi.elim))
| (i::l) C f q := begin
  rw [← pi_mem_cons.eta q],
  induction (pi_mem_cons.head q) using quotient.ind,
  refine @quotient_ind _ (λ q, C (pi_mem_cons.cons ⟦a⟧ q)) _ (pi_mem_cons.tail q),
  intros as,
  rw [pi_mem_cons.cons_apply a as],
  exact f _,
end

/-- Choice-free induction principle for quotients indexed by a `list`. -/
@[nolint decidable_classical, elab_as_eliminator]
lemma quotient_induction_on {l : list ι}
  {C : (Π i ∈ l, quotient (S i)) → Prop}
  (q : Π i ∈ l, quotient (S i)) (f : ∀ a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧)) :
  C q :=
quotient_ind f q

/-- `quotient_choice` as an equivalence. -/
def quotient_choice_equiv {l : list ι} :
  (Π i ∈ l, quotient (S i)) ≃ @quotient (Π i ∈ l, α i) pi_setoid :=
{ to_fun := quotient_choice,
  inv_fun := λ q, quotient.lift_on q (λ a i hi, ⟦a i hi⟧)
    (λ a₁ a₂ ha, funext₂ (λ i hi, quotient.sound (ha i hi))),
  left_inv := λ q, by
    { refine quotient_induction_on q (λ a, _), ext i hi, dsimp, rw [quotient_choice_mk], refl },
  right_inv := λ q, by { induction q using quotient.ind, exact quotient_choice_mk _ } }

omit S

section quotient_rec
variables {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (f : ∀ a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))

omit dec

attribute [reducible]
private def quotient_rec_indep
  (a : Π i ∈ l, α i) : psigma C :=
⟨λ i hi, ⟦a i hi⟧, f a⟩

variables (h : ∀ (a b : Π i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
  (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
    C (λ i hi, ⟦b i hi⟧)) = f b)

private lemma quotient_rec_indep_coherent :
  ∀ a b : Π i ∈ l, α i, (∀ i hi, a i hi ≈ b i hi) →
    quotient_rec_indep f a = quotient_rec_indep f b :=
λ a b e, psigma.eq (funext₂ (λ i hi, quotient.sound (e i hi))) (h a b e)

include h dec

private lemma quotient_rec_lift_indep_pr1 (q : Π i ∈ l, quotient (S i)) :
  (quotient_lift (quotient_rec_indep f) (quotient_rec_indep_coherent f h) q).1 = q :=
quotient_ind (λ a, funext₂ (λ i hi, by rw [quotient_lift_mk])) q

end quotient_rec

/-- Recursion principle for quotients indexed by a `list`. -/
@[elab_as_eliminator] def quotient_rec {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (f : Π a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
    (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
      C (λ i hi, ⟦b i hi⟧)) = f b)
  (q : Π i ∈ l, quotient (S i)) :
  C q :=
eq.rec_on (quotient_rec_lift_indep_pr1 f h q)
  ((quotient_lift (quotient_rec_indep f) (quotient_rec_indep_coherent f h) q).2)

/-- Recursion principle for quotients indexed by a `list`. -/
@[elab_as_eliminator] def quotient_rec_on {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (q : Π i ∈ l, quotient (S i))
  (f : Π a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
    (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
      C (λ i hi, ⟦b i hi⟧)) = f b) :
  C q :=
quotient_rec f h q

/-- Recursion principle for quotients indexed by a `list`. -/
@[elab_as_eliminator] def quotient_hrec_on {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (q : Π i ∈ l, quotient (S i))
  (f : Π a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))
  (h : ∀ (a b : Π i ∈ l, α i) (h : ∀ i hi, a i hi ≈ b i hi), f a == f b) :
  C q :=
quotient_rec_on q f (λ a b p, eq_of_heq ((eq_rec_heq _ (f a)).trans (h a b p)))

@[simp] lemma quotient_rec_mk {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (f : Π a : Π i ∈ l, α i, C (λ i hi, ⟦a i hi⟧))
  (h) (a : Π i ∈ l, α i) :
  @quotient_rec _ _ _ _ _ C f h (λ i hi, ⟦a i hi⟧) = f a :=
begin
  dsimp [quotient_rec], refine eq_of_heq ((eq_rec_heq _ _).trans _),
  rw [quotient_lift_mk (quotient_rec_indep f) (quotient_rec_indep_coherent f h) a],
end

@[simp] lemma quotient_rec_on_mk {l : list ι} {C : (Π i ∈ l, quotient (S i)) → Sort*}
  (a : Π i ∈ l, α i) :
  @quotient_rec_on _ _ _ _ _ C (λ i hi, ⟦a i hi⟧) = λ f h, f a :=
by { ext f h, exact quotient_rec_mk _ _ _, }

include S

lemma quotient_lift_inj {l : list ι} (f₁ f₂ : (Π i ∈ l, α i) → β) (h₁ h₂) :
  quotient_lift f₁ h₁ = quotient_lift f₂ h₂ → f₁ = f₂ :=
λ h, funext $ λ _, by rw [← quotient_lift_mk f₁ h₁, ← quotient_lift_mk f₂ h₂, h]

lemma quotient_lift_inj_iff {l : list ι} (f₁ f₂ : (Π i ∈ l, α i) → β) (h₁ h₂) :
  quotient_lift f₁ h₁ = quotient_lift f₂ h₂ ↔ f₁ = f₂ :=
⟨quotient_lift_inj _ _ h₁ h₂, λ h, by simp_rw [h]⟩

section helper_lemmas
omit dec S

lemma pi_mem_eq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  (Π i ∈ l₁, α i) = (Π i ∈ l₂, α i) :=
pi_congr (λ _, by rw [hl])

lemma fun_pi_mem_eq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  ((Π i ∈ l₁, α i) → β) = ((Π i ∈ l₂, α i) → β) :=
by rw [pi_mem_eq hl]

/-- A helper function to tell lean the motive. -/
-- @[elab_as_eliminator]
def mem_rec (C : (ι → Prop) → Sort*)
  {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂)
  (h : C (∈ l₁)) : C (∈ l₂) :=
by { convert h, simp_rw [hl] }

end helper_lemmas

-- TODO: `simp_rw [hl]` fails in these 3 lemmas.
-- Can lean compute the motive? Or maybe a tactic (extension) is needed?
-- Or there are some better proofs?
-- (This may because of the order of arguments of `has_mem.mem`?)

lemma quotient_choice_heq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  @quotient_choice _ _ α _ l₁ == @quotient_choice _ _ α _ l₂ :=
begin
  ext1, { exact pi_mem_eq hl }, intros q₁ q₂,
  apply list.quotient_induction_on q₂,
  apply list.quotient_induction_on q₁,
  simp_rw [quotient_choice_mk],
  apply mem_rec (λ meml₂,
    ∀ (a₁ : Π i ∈ l₁, α i) (a₂ : Π i, meml₂ i → α i),
        (λ i hi, ⟦a₁ i hi⟧) == (λ i hi, ⟦a₂ i hi⟧) → ⟦a₁⟧ == ⟦a₂⟧) hl,
  intros a₁ a₂ ha, rw [heq_iff_eq] at *,
  simp_rw [← quotient_choice_mk, ha],
end

lemma quotient_lift_on_heq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  @quotient_lift_on _ _ α _ β l₁ == @quotient_lift_on _ _ α _ β l₂ :=
begin
  ext1, { exact pi_mem_eq hl }, intros q₁ q₂,
  apply list.quotient_induction_on q₂,
  apply list.quotient_induction_on q₁,
  simp_rw [quotient_lift_on_mk],
  apply mem_rec (λ meml₂,
    ∀ (a₁ : Π i ∈ l₁, α i) (a₂ : Π i, meml₂ i → α i),
        (λ i hi, ⟦a₁ i hi⟧) == (λ i hi, ⟦a₂ i hi⟧) →
      (λ (f : (Π i ∈ l₁, α i) → β)
          (h : ∀ (a b : Π i ∈ l₁, α i), (∀ i hi, a i hi ≈ b i hi) → f a = f b), f a₁) ==
        (λ (f : (Π i, meml₂ i → α i) → β)
          (h : ∀ (a b : Π i, meml₂ i → α i), (∀ i hi, a i hi ≈ b i hi) → f a = f b), f a₂)) hl,
  intros a₁ a₂ ha, rw [heq_iff_eq] at *,
  ext f h, apply h, exact λ i hi, quotient.exact (congr_fun₂ ha i hi),
end

lemma quotient_rec_on_heq {l₁ l₂ : list ι} (hl : ∀ i, i ∈ l₁ ↔ i ∈ l₂) :
  @quotient_rec_on _ _ α _ l₁ == @quotient_rec_on _ _ α _ l₂ :=
begin
  ext1, { exact fun_pi_mem_eq hl }, intros C₁ C₂ hC,
  ext1, { exact pi_mem_eq hl }, intros q₁ q₂,
  apply list.quotient_induction_on q₂,
  apply list.quotient_induction_on q₁,
  simp_rw [quotient_rec_on_mk],
  revert C₁ C₂ hC,
  apply mem_rec (λ meml₂,
    ∀ (C₁ : (Π i ∈ l₁, quotient (S i)) → Sort*)
      (C₂ : (Π i, meml₂ i → quotient (S i)) → Sort*),
      C₁ == C₂ →
    ∀ (a₁ : Π i ∈ l₁, α i) (a₂ : Π i, meml₂ i → α i),
      (λ i hi, ⟦a₁ i hi⟧) == (λ i hi, ⟦a₂ i hi⟧) →
      (λ (f : Π (a : Π i ∈ l₁, α i), C₁ (λ i hi, ⟦a i hi⟧))
        (h : ∀ (a b : Π i ∈ l₁, α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
          (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
          C₁ (λ i hi, ⟦b i hi⟧)) = f b),
        f a₁) ==
      (λ (f : Π (a : Π i, meml₂ i → α i), C₂ (λ i hi, ⟦a i hi⟧))
        (h : ∀ (a b : Π i, meml₂ i → α i) (h : ∀ i hi, a i hi ≈ b i hi), (eq.rec (f a)
          (funext₂ (λ i hi, quotient.sound (h i hi)) : (λ i hi, ⟦a i hi⟧) = (λ i hi, ⟦b i hi⟧)) :
          C₂ (λ i hi, ⟦b i hi⟧)) = f b),
        f a₂)) hl,
  intros C₁ C₂ hC, cases hC,
  intros a₁ a₂ ha, rw [heq_iff_eq] at *,
  ext1, { refl }, intros f _ hf, cases hf,
  ext1, { refl }, intros h _ _,
  exact heq_of_eq_rec_left _ (h a₁ a₂ $ λ i hi, quotient.exact (congr_fun₂ ha i hi)),
end

end list
