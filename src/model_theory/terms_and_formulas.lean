/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import model_theory.basic

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language.term` is defined so that `L.term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `first_order.language.formula` is defined so that `L.formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `first_order.language.sentence` is a formula with no free variables.
* A `first_order.language.theory` is a set of sentences.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

universes u v

namespace first_order
namespace language

variables {L : language.{u v}} {M N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
open_locale first_order
open Structure

variable (L)
/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive term (α : Type) : Type u
| var {} : ∀ (a : α), term
| func {} : ∀ {l : ℕ} (f : L.functions l) (ts : fin l → term), term
export term

variable {L}

/-- Relabels a term's variables along a particular function. -/
@[simp] def term.relabel {α β : Type} (g : α → β) : L.term α → L.term β
| (var i) := var (g i)
| (func f ts) := func f (λ i, (ts i).relabel)

instance {α : Type} [inhabited α] : inhabited (L.term α) :=
⟨var default⟩

instance {α} : has_coe L.const (L.term α) :=
⟨λ c, func c fin_zero_elim⟩

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
@[simp] def realize_term {α : Type} (v : α → M) :
  ∀ (t : L.term α), M
| (var k)         := v k
| (func f ts)     := fun_map f (λ i, realize_term (ts i))

@[simp] lemma realize_term_relabel {α β : Type} (g : α → β) (v : β → M) (t : L.term α) :
  realize_term v (t.relabel g) = realize_term (v ∘ g) t :=
begin
  induction t with _ n f ts ih,
  { refl, },
  { simp [ih] }
end

@[simp] lemma hom.realize_term {α : Type} (v : α → M)
  (t : L.term α) (g : M →[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
begin
  induction t,
  { refl },
  { rw [realize_term, realize_term, g.map_fun],
    refine congr rfl _,
    ext x,
    simp [t_ih x], },
end

@[simp] lemma embedding.realize_term {α : Type}  (v : α → M)
  (t : L.term α) (g : M ↪[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
g.to_hom.realize_term v t

@[simp] lemma equiv.realize_term {α : Type}  (v : α → M)
  (t : L.term α) (g : M ≃[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
g.to_hom.realize_term v t

variable (L)
/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive bounded_formula (α : Type) : ℕ → Type (max u v)
| bd_falsum {} {n} : bounded_formula n
| bd_equal {n} (t₁ t₂ : L.term (α ⊕ fin n)) : bounded_formula n
| bd_rel {n l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) : bounded_formula n
| bd_imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
| bd_all {n} (f : bounded_formula (n+1)) : bounded_formula n

export bounded_formula

instance {α : Type} {n : ℕ} : inhabited (L.bounded_formula α n) :=
⟨bd_falsum⟩

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible] def formula (α : Type) := L.bounded_formula α 0

/-- A sentence is a formula with no free variables. -/
@[reducible] def sentence           := L.formula pempty

/-- A theory is a set of sentences. -/
@[reducible] def theory := set L.sentence

variables {L} {α : Type}

section formula
variable {n : ℕ}

@[simps] instance : has_bot (L.bounded_formula α n) := ⟨bd_falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[reducible] def bd_not (φ : L.bounded_formula α n) : L.bounded_formula α n :=
  bd_imp φ ⊥

@[simps] instance : has_top (L.bounded_formula α n) := ⟨bd_not bd_falsum⟩

@[simps] instance : has_inf (L.bounded_formula α n) := ⟨λ f g, bd_not (bd_imp f (bd_not g))⟩

@[simps] instance : has_sup (L.bounded_formula α n) := ⟨λ f g, bd_imp (bd_not f) g⟩

/-- Relabels a bounded formula's variables along a particular function. -/
@[simp] def bounded_formula.relabel {α β : Type} (g : α → β) :
  ∀ {n : ℕ}, L.bounded_formula α n → L.bounded_formula β n
| n bd_falsum := bd_falsum
| n (bd_equal t₁ t₂) := bd_equal (t₁.relabel (sum.elim (sum.inl ∘ g) sum.inr))
    (t₂.relabel (sum.elim (sum.inl ∘ g) sum.inr))
| n (bd_rel R ts) := bd_rel R ((term.relabel (sum.elim (sum.inl ∘ g) sum.inr)) ∘ ts)
| n (bd_imp f₁ f₂) := bd_imp f₁.relabel f₂.relabel
| n (bd_all f) := bd_all f.relabel

namespace formula

/-- The equality of two terms as a first-order formula. -/
def equal (t₁ t₂ : L.term α) : (L.formula α) :=
bd_equal (t₁.relabel sum.inl) (t₂.relabel sum.inl)

/-- The graph of a function as a first-order formula. -/
def graph (f : L.functions n) : L.formula (fin (n + 1)) :=
equal (func f (λ i, var i)) (var n)

end formula
end formula

variable {L}

instance nonempty_bounded_formula {α : Type} (n : ℕ) : nonempty $ L.bounded_formula α n :=
  nonempty.intro (by constructor)

variables (M)

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[simp] def realize_bounded_formula :
  ∀ {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M), Prop
| _ bd_falsum  v     xs := false
| _ (bd_equal t₁ t₂) v xs := realize_term (sum.elim v xs) t₁ = realize_term (sum.elim v xs) t₂
| _ (bd_rel R ts)   v   xs := rel_map R (λ i, realize_term (sum.elim v xs) (ts i))
| _ (bd_imp f₁ f₂)  v xs := realize_bounded_formula f₁ v xs → realize_bounded_formula f₂ v xs
| _ (bd_all f)     v   xs := ∀(x : M), realize_bounded_formula f v (fin.cons x xs)

@[simp] lemma realize_not {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M) :
  realize_bounded_formula M (bd_not f) v xs = ¬ realize_bounded_formula M f v xs :=
rfl

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[reducible] def realize_formula (f : L.formula α) (v : α → M) : Prop :=
realize_bounded_formula M f v fin_zero_elim

/-- A sentence can be evaluated as true or false in a structure. -/
@[reducible] def realize_sentence (φ : L.sentence) : Prop :=
realize_formula M φ pempty.elim

variable {M}

@[simp] lemma realize_bounded_formula_relabel {α β : Type} {n : ℕ}
  (g : α → β) (v : β → M) (xs : fin n → M) (φ : L.bounded_formula α n) :
  realize_bounded_formula M (φ.relabel g) v xs ↔ realize_bounded_formula M φ (v ∘ g) xs :=
begin
  have h : ∀ (m : ℕ) (xs' : fin m → M), sum.elim v xs' ∘
    sum.elim (sum.inl ∘ g) sum.inr = sum.elim (v ∘ g) xs',
  { intros m xs',
    ext x,
    cases x;
    simp, },
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp [h _ xs] },
  { simp [h _ xs] },
  { simp [ih1, ih2] },
  { simp [ih3] }
end

@[simp] lemma equiv.realize_bounded_formula {α : Type} {n : ℕ}  (v : α → M)
  (xs : fin n → M) (φ : L.bounded_formula α n) (g : M ≃[L] N) :
  realize_bounded_formula N φ (g ∘ v) (g ∘ xs) ↔ realize_bounded_formula M φ v xs :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp only [realize_bounded_formula, ← sum.comp_elim, equiv.realize_term, g.injective.eq_iff] },
  { simp only [realize_bounded_formula, ← sum.comp_elim, equiv.realize_term, g.map_rel], },
  { rw [realize_bounded_formula, ih1, ih2, realize_bounded_formula] },
  { rw [realize_bounded_formula, realize_bounded_formula],
    split,
    { intros h a,
      have h' := h (g a),
      rw [← fin.comp_cons, ih3] at h',
      exact h' },
    { intros h a,
      have h' := h (g.symm a),
      rw [← ih3, fin.comp_cons, g.apply_symm_apply] at h',
      exact h' }}
end

@[simp] lemma realize_formula_relabel {α β : Type}
  (g : α → β) (v : β → M) (φ : L.formula α) :
  realize_formula M (φ.relabel g) v ↔ realize_formula M φ (v ∘ g) :=
by rw [realize_formula, realize_formula, realize_bounded_formula_relabel]

@[simp] lemma realize_formula_equiv {α : Type}  (v : α → M) (φ : L.formula α)
  (g : M ≃[L] N) :
  realize_formula N φ (g ∘ v) ↔ realize_formula M φ v :=
begin
  rw [realize_formula, realize_formula, ← equiv.realize_bounded_formula v fin_zero_elim φ g,
    iff_eq_eq],
  exact congr rfl (funext fin_zero_elim),
end

@[simp]
lemma realize_equal {α : Type*} (t₁ t₂ : L.term α) (x : α → M) :
  realize_formula M (formula.equal t₁ t₂) x ↔ realize_term x t₁ = realize_term x t₂ :=
by simp [formula.equal, realize_formula]

@[simp]
lemma realize_graph {l : ℕ} (f : L.functions l) (x : fin l → M) (y : M) :
  realize_formula M (formula.graph f) (fin.snoc x y) ↔ fun_map f x = y :=
begin
  simp only [formula.graph, realize_term, fin.coe_eq_cast_succ, realize_equal, fin.snoc_cast_succ],
  rw [fin.coe_nat_eq_last, fin.snoc_last],
end

end language
end first_order
