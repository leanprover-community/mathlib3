/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.list.prod_sigma
import data.set.prod
import logic.equiv.fin
import model_theory.language_map

/-!
# Basics on First-Order Syntax

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language.term` is defined so that `L.term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `first_order.language.formula` is defined so that `L.formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `first_order.language.sentence` is a formula with no free variables.
* A `first_order.language.Theory` is a set of sentences.
* The variables of terms and formulas can be relabelled with `first_order.language.term.relabel`,
`first_order.language.bounded_formula.relabel`, and `first_order.language.formula.relabel`.
* Given an operation on terms and an operation on relations,
  `first_order.language.bounded_formula.map_term_rel` gives an operation on formulas.
* `first_order.language.bounded_formula.cast_le` adds more `fin`-indexed variables.
* `first_order.language.bounded_formula.lift_at` raises the indexes of the `fin`-indexed variables
above a particular index.
* `first_order.language.term.subst` and `first_order.language.bounded_formula.subst` substitute
variables with given terms.
* Language maps can act on syntactic objects with functions such as
`first_order.language.Lhom.on_formula`.
* `first_order.language.term.constants_vars_equiv` and
`first_order.language.bounded_formula.constants_vars_equiv` switch terms and formulas between having
constants in the language and having extra variables indexed by the same type.

## Implementation Notes
* Formulas use a modified version of de Bruijn variables. Specifically, a `L.bounded_formula α n`
is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
indexed by `fin n`, which can. For any `φ : L.bounded_formula α (n + 1)`, we define the formula
`∀' φ : L.bounded_formula α n` by universally quantifying over the variable indexed by
`n : fin (n + 1)`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

universes u v w u' v'

namespace first_order
namespace language

variables (L : language.{u v}) {L' : language}
variables {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variables {α : Type u'} {β : Type v'} {γ : Type*}
open_locale first_order
open Structure fin

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive term (α : Type u') : Type (max u u')
| var {} : ∀ (a : α), term
| func {} : ∀ {l : ℕ} (f : L.functions l) (ts : fin l → term), term
export term

variable {L}

namespace term

open finset

/-- The `finset` of variables used in a given term. -/
@[simp] def var_finset [decidable_eq α] : L.term α → finset α
| (var i) := {i}
| (func f ts) := univ.bUnion (λ i, (ts i).var_finset)

/-- The `finset` of variables from the left side of a sum used in a given term. -/
@[simp] def var_finset_left [decidable_eq α] : L.term (α ⊕ β) → finset α
| (var (sum.inl i)) := {i}
| (var (sum.inr i)) := ∅
| (func f ts) := univ.bUnion (λ i, (ts i).var_finset_left)

/-- Relabels a term's variables along a particular function. -/
@[simp] def relabel (g : α → β) : L.term α → L.term β
| (var i) := var (g i)
| (func f ts) := func f (λ i, (ts i).relabel)

lemma relabel_id (t : L.term α) :
  t.relabel id = t :=
begin
  induction t with _ _ _ _ ih,
  { refl, },
  { simp [ih] },
end

@[simp] lemma relabel_id_eq_id :
  (term.relabel id : L.term α → L.term α) = id :=
funext relabel_id

@[simp] lemma relabel_relabel (f : α → β) (g : β → γ) (t : L.term α) :
  (t.relabel f).relabel g = t.relabel (g ∘ f) :=
begin
  induction t with _ _ _ _ ih,
  { refl, },
  { simp [ih] },
end

@[simp] lemma relabel_comp_relabel (f : α → β) (g : β → γ) :
  (term.relabel g ∘ term.relabel f : L.term α → L.term γ) = term.relabel (g ∘ f) :=
funext (relabel_relabel f g)

/-- Relabels a term's variables along a bijection. -/
@[simps] def relabel_equiv (g : α ≃ β) : L.term α ≃ L.term β :=
⟨relabel g, relabel g.symm, λ t, by simp, λ t, by simp⟩

/-- Restricts a term to use only a set of the given variables. -/
def restrict_var [decidable_eq α] : Π (t : L.term α) (f : t.var_finset → β), L.term β
| (var a) f := var (f ⟨a, mem_singleton_self a⟩)
| (func F ts) f := func F (λ i, (ts i).restrict_var
  (f ∘ set.inclusion (subset_bUnion_of_mem _ (mem_univ i))))

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrict_var_left [decidable_eq α] {γ : Type*} :
  Π (t : L.term (α ⊕ γ)) (f : t.var_finset_left → β), L.term (β ⊕ γ)
| (var (sum.inl a)) f := var (sum.inl (f ⟨a, mem_singleton_self a⟩))
| (var (sum.inr a)) f := var (sum.inr a)
| (func F ts) f := func F (λ i, (ts i).restrict_var_left
  (f ∘ set.inclusion (subset_bUnion_of_mem _ (mem_univ i))))

end term

/-- The representation of a constant symbol as a term. -/
def constants.term (c : L.constants) : (L.term α) :=
func c default

/-- Applies a unary function to a term. -/
def functions.apply₁ (f : L.functions 1) (t : L.term α) : L.term α := func f ![t]

/-- Applies a binary function to two terms. -/
def functions.apply₂ (f : L.functions 2) (t₁ t₂ : L.term α) : L.term α := func f ![t₁, t₂]

namespace term

/-- Sends a term with constants to a term with extra variables. -/
@[simp] def constants_to_vars : L[[γ]].term α → L.term (γ ⊕ α)
| (var a) := var (sum.inr a)
| (@func _ _ 0 f ts) := sum.cases_on f (λ f, func f (λ i, (ts i).constants_to_vars))
    (λ c, var (sum.inl c))
| (@func _ _ (n + 1) f ts) := sum.cases_on f (λ f, func f (λ i, (ts i).constants_to_vars))
    (λ c, is_empty_elim c)

/-- Sends a term with extra variables to a term with constants. -/
@[simp] def vars_to_constants : L.term (γ ⊕ α) → L[[γ]].term α
| (var (sum.inr a)) := var a
| (var (sum.inl c)) := constants.term (sum.inr c)
| (func f ts) := func (sum.inl f) (λ i, (ts i).vars_to_constants)

/-- A bijection between terms with constants and terms with extra variables. -/
@[simps] def constants_vars_equiv : L[[γ]].term α ≃ L.term (γ ⊕ α) :=
⟨constants_to_vars, vars_to_constants, begin
  intro t,
  induction t with _ n f _ ih,
  { refl },
  { cases n,
    { cases f,
      { simp [constants_to_vars, vars_to_constants, ih] },
      { simp [constants_to_vars, vars_to_constants, constants.term] } },
    { cases f,
      { simp [constants_to_vars, vars_to_constants, ih] },
      { exact is_empty_elim f } } }
end, begin
  intro t,
  induction t with x n f _ ih,
  { cases x;
    refl },
  { cases n;
    { simp [vars_to_constants, constants_to_vars, ih] } }
end⟩

/-- A bijection between terms with constants and terms with extra variables. -/
def constants_vars_equiv_left : L[[γ]].term (α ⊕ β) ≃ L.term ((γ ⊕ α) ⊕ β) :=
constants_vars_equiv.trans (relabel_equiv (equiv.sum_assoc _ _ _)).symm

@[simp] lemma constants_vars_equiv_left_apply (t : L[[γ]].term (α ⊕ β)) :
  constants_vars_equiv_left t = (constants_to_vars t).relabel (equiv.sum_assoc _ _ _).symm :=
rfl

@[simp] lemma constants_vars_equiv_left_symm_apply (t : L.term ((γ ⊕ α) ⊕ β)) :
  constants_vars_equiv_left.symm t = vars_to_constants (t.relabel (equiv.sum_assoc _ _ _)) :=
rfl

instance inhabited_of_var [inhabited α] : inhabited (L.term α) :=
⟨var default⟩

instance inhabited_of_constant [inhabited L.constants] : inhabited (L.term α) :=
⟨(default : L.constants).term⟩

/-- Raises all of the `fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def lift_at {n : ℕ} (n' m : ℕ) : L.term (α ⊕ fin n) → L.term (α ⊕ fin (n + n')) :=
relabel (sum.map id (λ i, if ↑i < m then fin.cast_add n' i else fin.add_nat n' i))

/-- Substitutes the variables in a given term with terms. -/
@[simp] def subst : L.term α → (α → L.term β) → L.term β
| (var a) tf := tf a
| (func f ts) tf := (func f (λ i, (ts i).subst tf))

end term

localized "prefix (name := language.term.var) `&`:max :=
  first_order.language.term.var ∘ sum.inr" in first_order

namespace Lhom

/-- Maps a term's symbols along a language map. -/
@[simp] def on_term (φ : L →ᴸ L') : L.term α → L'.term α
| (var i) := var i
| (func f ts) := func (φ.on_function f) (λ i, on_term (ts i))

@[simp] lemma id_on_term :
  ((Lhom.id L).on_term : L.term α → L.term α) = id :=
begin
  ext t,
  induction t with _ _ _ _ ih,
  { refl },
  { simp_rw [on_term, ih],
    refl, },
end

@[simp] lemma comp_on_term {L'' : language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
  ((φ.comp ψ).on_term : L.term α → L''.term α) = φ.on_term ∘ ψ.on_term :=
begin
  ext t,
  induction t with _ _ _ _ ih,
  { refl },
  { simp_rw [on_term, ih],
    refl, },
end

end Lhom

/-- Maps a term's symbols along a language equivalence. -/
@[simps] def Lequiv.on_term (φ : L ≃ᴸ L') : L.term α ≃ L'.term α :=
{ to_fun := φ.to_Lhom.on_term,
  inv_fun := φ.inv_Lhom.on_term,
  left_inv := by rw [function.left_inverse_iff_comp, ← Lhom.comp_on_term, φ.left_inv,
    Lhom.id_on_term],
  right_inv := by rw [function.right_inverse_iff_comp, ← Lhom.comp_on_term, φ.right_inv,
    Lhom.id_on_term] }

variables (L) (α)
/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive bounded_formula : ℕ → Type (max u v u')
| falsum {} {n} : bounded_formula n
| equal {n} (t₁ t₂ : L.term (α ⊕ fin n)) : bounded_formula n
| rel {n l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) : bounded_formula n
| imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
| all {n} (f : bounded_formula (n+1)) : bounded_formula n

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible] def formula := L.bounded_formula α 0

/-- A sentence is a formula with no free variables. -/
@[reducible] def sentence := L.formula empty

/-- A theory is a set of sentences. -/
@[reducible] def Theory := set L.sentence

variables {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def relations.bounded_formula {l : ℕ} (R : L.relations n) (ts : fin n → L.term (α ⊕ fin l)) :
  L.bounded_formula α l := bounded_formula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def relations.bounded_formula₁ (r : L.relations 1) (t : L.term (α ⊕ fin n)) :
  L.bounded_formula α n :=
r.bounded_formula ![t]

/-- Applies a binary relation to two terms as a bounded formula. -/
def relations.bounded_formula₂ (r : L.relations 2) (t₁ t₂ : L.term (α ⊕ fin n)) :
  L.bounded_formula α n :=
r.bounded_formula ![t₁, t₂]

/-- The equality of two terms as a bounded formula. -/
def term.bd_equal (t₁ t₂ : L.term (α ⊕ fin n)) : (L.bounded_formula α n) :=
bounded_formula.equal t₁ t₂

/-- Applies a relation to terms as a bounded formula. -/
def relations.formula (R : L.relations n) (ts : fin n → L.term α) :
  L.formula α := R.bounded_formula (λ i, (ts i).relabel sum.inl)

/-- Applies a unary relation to a term as a formula. -/
def relations.formula₁ (r : L.relations 1) (t : L.term α) :
  L.formula α :=
r.formula ![t]

/-- Applies a binary relation to two terms as a formula. -/
def relations.formula₂ (r : L.relations 2) (t₁ t₂ : L.term α) :
  L.formula α :=
r.formula ![t₁, t₂]

/-- The equality of two terms as a first-order formula. -/
def term.equal (t₁ t₂ : L.term α) : (L.formula α) :=
(t₁.relabel sum.inl).bd_equal (t₂.relabel sum.inl)

namespace bounded_formula

instance : inhabited (L.bounded_formula α n) :=
⟨falsum⟩

instance : has_bot (L.bounded_formula α n) := ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[pattern] protected def not (φ : L.bounded_formula α n) : L.bounded_formula α n := φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[pattern] protected def ex (φ : L.bounded_formula α (n + 1)) : L.bounded_formula α n :=
  φ.not.all.not

instance : has_top (L.bounded_formula α n) := ⟨bounded_formula.not ⊥⟩

instance : has_inf (L.bounded_formula α n) := ⟨λ f g, (f.imp g.not).not⟩

instance : has_sup (L.bounded_formula α n) := ⟨λ f g, f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.bounded_formula α n) := φ.imp ψ ⊓ ψ.imp φ

open finset

/-- The `finset` of variables used in a given formula. -/
@[simp] def free_var_finset [decidable_eq α] :
  ∀ {n}, L.bounded_formula α n → finset α
| n falsum := ∅
| n (equal t₁ t₂) := t₁.var_finset_left ∪ t₂.var_finset_left
| n (rel R ts) := univ.bUnion (λ i, (ts i).var_finset_left)
| n (imp f₁ f₂) := f₁.free_var_finset ∪ f₂.free_var_finset
| n (all f) := f.free_var_finset

/-- Casts `L.bounded_formula α m` as `L.bounded_formula α n`, where `m ≤ n`. -/
@[simp] def cast_le : ∀ {m n : ℕ} (h : m ≤ n), L.bounded_formula α m → L.bounded_formula α n
| m n h falsum := falsum
| m n h (equal t₁ t₂) := equal (t₁.relabel (sum.map id (fin.cast_le h)))
    (t₂.relabel (sum.map id (fin.cast_le h)))
| m n h (rel R ts) := rel R (term.relabel (sum.map id (fin.cast_le h)) ∘ ts)
| m n h (imp f₁ f₂) := (f₁.cast_le h).imp (f₂.cast_le h)
| m n h (all f) := (f.cast_le (add_le_add_right h 1)).all

@[simp] lemma cast_le_rfl {n} (h : n ≤ n) (φ : L.bounded_formula α n) :
  φ.cast_le h = φ :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp [fin.cast_le_of_eq], },
  { simp [fin.cast_le_of_eq], },
  { simp [fin.cast_le_of_eq, ih1, ih2], },
  { simp [fin.cast_le_of_eq, ih3], },
end

@[simp] lemma cast_le_cast_le {k m n} (km : k ≤ m) (mn : m ≤ n) (φ : L.bounded_formula α k) :
  (φ.cast_le km).cast_le mn = φ.cast_le (km.trans mn) :=
begin
  revert m n,
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3;
  intros m n km mn,
  { refl },
  { simp },
  { simp only [cast_le, eq_self_iff_true, heq_iff_eq, true_and],
    rw [← function.comp.assoc, relabel_comp_relabel],
    simp },
  { simp [ih1, ih2] },
  { simp only [cast_le, ih3] }
end

@[simp] lemma cast_le_comp_cast_le {k m n} (km : k ≤ m) (mn : m ≤ n) :
  (bounded_formula.cast_le mn ∘ bounded_formula.cast_le km :
    L.bounded_formula α k → L.bounded_formula α n) =
    bounded_formula.cast_le (km.trans mn) :=
funext (cast_le_cast_le km mn)

/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrict_free_var [decidable_eq α] : Π {n : ℕ} (φ : L.bounded_formula α n)
  (f : φ.free_var_finset → β), L.bounded_formula β n
| n falsum f := falsum
| n (equal t₁ t₂) f := equal
  (t₁.restrict_var_left (f ∘ set.inclusion (subset_union_left _ _)))
  (t₂.restrict_var_left (f ∘ set.inclusion (subset_union_right _ _)))
| n (rel R ts) f := rel R (λ i, (ts i).restrict_var_left
  (f ∘ set.inclusion (subset_bUnion_of_mem _ (mem_univ i))))
| n (imp φ₁ φ₂) f :=
  (φ₁.restrict_free_var (f ∘ set.inclusion (subset_union_left _ _))).imp
  (φ₂.restrict_free_var (f ∘ set.inclusion (subset_union_right _ _)))
| n (all φ) f := (φ.restrict_free_var f).all

/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {n}, L.bounded_formula α n → L.formula α
| 0 φ := φ
| (n + 1) φ := φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {n}, L.bounded_formula α n → L.formula α
| 0 φ := φ
| (n + 1) φ := φ.ex.exs

/-- Maps bounded formulas along a map of terms and a map of relations. -/
def map_term_rel {g : ℕ → ℕ}
  (ft : ∀ n, L.term (α ⊕ fin n) → L'.term (β ⊕ fin (g n)))
  (fr : ∀ n, L.relations n → L'.relations n)
  (h : ∀ n, L'.bounded_formula β (g (n + 1)) → L'.bounded_formula β (g n + 1)) :
  ∀ {n}, L.bounded_formula α n → L'.bounded_formula β (g n)
| n falsum := falsum
| n (equal t₁ t₂) := equal (ft _ t₁) (ft _ t₂)
| n (rel R ts) := rel (fr _ R) (λ i, ft _ (ts i))
| n (imp φ₁ φ₂) := φ₁.map_term_rel.imp φ₂.map_term_rel
| n (all φ) := (h n φ.map_term_rel).all

/-- Raises all of the `fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def lift_at : ∀ {n : ℕ} (n' m : ℕ), L.bounded_formula α n → L.bounded_formula α (n + n') :=
λ n n' m φ, φ.map_term_rel (λ k t, t.lift_at n' m) (λ _, id)
  (λ _, cast_le (by rw [add_assoc, add_comm 1, add_assoc]))

@[simp] lemma map_term_rel_map_term_rel {L'' : language}
  (ft : ∀ n, L.term (α ⊕ fin n) → L'.term (β ⊕ fin n))
  (fr : ∀ n, L.relations n → L'.relations n)
  (ft' : ∀ n, L'.term (β ⊕ fin n) → L''.term (γ ⊕ fin n))
  (fr' : ∀ n, L'.relations n → L''.relations n)
  {n} (φ : L.bounded_formula α n) :
  (φ.map_term_rel ft fr (λ _, id)).map_term_rel ft' fr' (λ _, id) =
    φ.map_term_rel (λ _, (ft' _) ∘ (ft _)) (λ _, (fr' _) ∘ (fr _)) (λ _, id) :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp [map_term_rel] },
  { simp [map_term_rel] },
  { simp [map_term_rel, ih1, ih2] },
  { simp [map_term_rel, ih3], }
end

@[simp] lemma map_term_rel_id_id_id {n} (φ : L.bounded_formula α n) :
  φ.map_term_rel (λ _, id) (λ _, id) (λ _, id) = φ :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp [map_term_rel] },
  { simp [map_term_rel] },
  { simp [map_term_rel, ih1, ih2] },
  { simp [map_term_rel, ih3], }
end

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps] def map_term_rel_equiv (ft : ∀ n, L.term (α ⊕ fin n) ≃ L'.term (β ⊕ fin n))
  (fr : ∀ n, L.relations n ≃ L'.relations n) {n} :
  L.bounded_formula α n ≃ L'.bounded_formula β n :=
⟨map_term_rel (λ n, ft n) (λ n, fr n) (λ _, id),
  map_term_rel (λ n, (ft n).symm) (λ n, (fr n).symm) (λ _, id),
  λ φ, by simp, λ φ, by simp⟩

/-- A function to help relabel the variables in bounded formulas. -/
def relabel_aux (g : α → β ⊕ fin n) (k : ℕ) :
  α ⊕ fin k → β ⊕ fin (n + k) :=
sum.map id fin_sum_fin_equiv ∘ equiv.sum_assoc _ _ _ ∘ sum.map g id

@[simp] lemma sum_elim_comp_relabel_aux {m : ℕ} {g : α → (β ⊕ fin n)}
  {v : β → M} {xs : fin (n + m) → M} :
  sum.elim v xs ∘ relabel_aux g m =
    sum.elim (sum.elim v (xs ∘ cast_add m) ∘ g) (xs ∘ nat_add n) :=
begin
  ext x,
  cases x,
  { simp only [bounded_formula.relabel_aux, function.comp_app, sum.map_inl, sum.elim_inl],
    cases g x with l r;
    simp },
  { simp [bounded_formula.relabel_aux] }
end

@[simp] lemma relabel_aux_sum_inl (k : ℕ) :
  relabel_aux (sum.inl : α → α ⊕ fin n) k =
  sum.map id (nat_add n) :=
begin
  ext x,
  cases x;
  { simp [relabel_aux] },
end

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → (β ⊕ fin n)) {k} (φ : L.bounded_formula α k) :
  L.bounded_formula β (n + k) :=
φ.map_term_rel (λ _ t, t.relabel (relabel_aux g _)) (λ _, id)
  (λ _, cast_le (ge_of_eq (add_assoc _ _ _)))

/-- Relabels a bounded formula's free variables along a bijection. -/
def relabel_equiv (g : α ≃ β) {k} :
  L.bounded_formula α k ≃ L.bounded_formula β k :=
map_term_rel_equiv (λ n, term.relabel_equiv (g.sum_congr (_root_.equiv.refl _)))
  (λ n, _root_.equiv.refl _)

@[simp] lemma relabel_falsum (g : α → (β ⊕ fin n)) {k} :
  (falsum : L.bounded_formula α k).relabel g = falsum :=
rfl

@[simp] lemma relabel_bot (g : α → (β ⊕ fin n)) {k} :
  (⊥ : L.bounded_formula α k).relabel g = ⊥ :=
rfl

@[simp] lemma relabel_imp (g : α → (β ⊕ fin n)) {k} (φ ψ : L.bounded_formula α k) :
  (φ.imp ψ).relabel g = (φ.relabel g).imp (ψ.relabel g) :=
rfl

@[simp] lemma relabel_not (g : α → (β ⊕ fin n)) {k} (φ : L.bounded_formula α k) :
  φ.not.relabel g = (φ.relabel g).not :=
by simp [bounded_formula.not]

@[simp] lemma relabel_all (g : α → (β ⊕ fin n)) {k} (φ : L.bounded_formula α (k + 1)) :
  φ.all.relabel g = (φ.relabel g).all :=
begin
  rw [relabel, map_term_rel, relabel],
  simp,
end

@[simp] lemma relabel_ex (g : α → (β ⊕ fin n)) {k} (φ : L.bounded_formula α (k + 1)) :
  φ.ex.relabel g = (φ.relabel g).ex :=
by simp [bounded_formula.ex]

@[simp] lemma relabel_sum_inl (φ : L.bounded_formula α n) :
  (φ.relabel sum.inl : L.bounded_formula α (0 + n)) =
  φ.cast_le (ge_of_eq (zero_add n)) :=
begin
  simp only [relabel, relabel_aux_sum_inl],
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp [fin.nat_add_zero, cast_le_of_eq, map_term_rel] },
  { simp [fin.nat_add_zero, cast_le_of_eq, map_term_rel] },
  { simp [map_term_rel, ih1, ih2], },
  { simp [map_term_rel, ih3, cast_le], },
end

/-- Substitutes the variables in a given formula with terms. -/
@[simp] def subst {n : ℕ} (φ : L.bounded_formula α n) (f : α → L.term β) : L.bounded_formula β n :=
φ.map_term_rel (λ _ t, t.subst (sum.elim (term.relabel sum.inl ∘ f) (var ∘ sum.inr)))
  (λ _, id) (λ _, id)

/-- A bijection sending formulas with constants to formulas with extra variables. -/
def constants_vars_equiv : L[[γ]].bounded_formula α n ≃ L.bounded_formula (γ ⊕ α) n :=
map_term_rel_equiv (λ _, term.constants_vars_equiv_left) (λ _, equiv.sum_empty _ _)

/-- Turns the extra variables of a bounded formula into free variables. -/
@[simp] def to_formula : ∀ {n : ℕ}, L.bounded_formula α n → L.formula (α ⊕ fin n)
| n falsum := falsum
| n (equal t₁ t₂) := t₁.equal t₂
| n (rel R ts) := R.formula ts
| n (imp φ₁ φ₂) := φ₁.to_formula.imp φ₂.to_formula
| n (all φ) := (φ.to_formula.relabel
  (sum.elim (sum.inl ∘ sum.inl) (sum.map sum.inr id ∘ fin_sum_fin_equiv.symm))).all

variables {l : ℕ} {φ ψ : L.bounded_formula α l} {θ : L.bounded_formula α l.succ}
variables {v : α → M} {xs : fin l → M}

/-- An atomic formula is either equality or a relation symbol applied to terms.
  Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive is_atomic : L.bounded_formula α n → Prop
| equal (t₁ t₂ : L.term (α ⊕ fin n)) : is_atomic (bd_equal t₁ t₂)
| rel {l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) :
    is_atomic (R.bounded_formula ts)

lemma not_all_is_atomic (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.all.is_atomic :=
λ con, by cases con

lemma not_ex_is_atomic (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.ex.is_atomic :=
λ con, by cases con

lemma is_atomic.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_atomic)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_atomic :=
is_atomic.rec_on h (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

lemma is_atomic.lift_at {k m : ℕ} (h : is_atomic φ) : (φ.lift_at k m).is_atomic :=
is_atomic.rec_on h (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

lemma is_atomic.cast_le {h : l ≤ n} (hφ : is_atomic φ) :
  (φ.cast_le h).is_atomic :=
is_atomic.rec_on hφ (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive is_qf : L.bounded_formula α n → Prop
| falsum : is_qf falsum
| of_is_atomic {φ} (h : is_atomic φ) : is_qf φ
| imp {φ₁ φ₂} (h₁ : is_qf φ₁) (h₂ : is_qf φ₂) : is_qf (φ₁.imp φ₂)

lemma is_atomic.is_qf {φ : L.bounded_formula α n} : is_atomic φ → is_qf φ :=
is_qf.of_is_atomic

lemma is_qf_bot : is_qf (⊥ : L.bounded_formula α n) :=
is_qf.falsum

lemma is_qf.not {φ : L.bounded_formula α n} (h : is_qf φ) :
  is_qf φ.not :=
h.imp is_qf_bot

lemma is_qf.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_qf)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_qf :=
is_qf.rec_on h is_qf_bot (λ _ h, (h.relabel f).is_qf) (λ _ _ _ _ h1 h2, h1.imp h2)

lemma is_qf.lift_at {k m : ℕ} (h : is_qf φ) : (φ.lift_at k m).is_qf :=
is_qf.rec_on h is_qf_bot (λ _ ih, ih.lift_at.is_qf) (λ _ _ _ _ ih1 ih2, ih1.imp ih2)

lemma is_qf.cast_le {h : l ≤ n} (hφ : is_qf φ) :
  (φ.cast_le h).is_qf :=
is_qf.rec_on hφ is_qf_bot (λ _ ih, ih.cast_le.is_qf) (λ _ _ _ _ ih1 ih2, ih1.imp ih2)

lemma not_all_is_qf (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.all.is_qf :=
λ con, begin
  cases con with _ con,
  exact (φ.not_all_is_atomic con),
end

lemma not_ex_is_qf (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.ex.is_qf :=
λ con, begin
  cases con with _ con _ _ con,
  { exact (φ.not_ex_is_atomic con) },
  { exact not_all_is_qf _ con }
end

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive is_prenex : ∀ {n}, L.bounded_formula α n → Prop
| of_is_qf {n} {φ : L.bounded_formula α n} (h : is_qf φ) : is_prenex φ
| all {n} {φ : L.bounded_formula α (n + 1)} (h : is_prenex φ) : is_prenex φ.all
| ex {n} {φ : L.bounded_formula α (n + 1)} (h : is_prenex φ) : is_prenex φ.ex

lemma is_qf.is_prenex {φ : L.bounded_formula α n} : is_qf φ → is_prenex φ :=
is_prenex.of_is_qf

lemma is_atomic.is_prenex {φ : L.bounded_formula α n} (h : is_atomic φ) : is_prenex φ :=
h.is_qf.is_prenex

lemma is_prenex.induction_on_all_not {P : ∀ {n}, L.bounded_formula α n → Prop}
  {φ : L.bounded_formula α n}
  (h : is_prenex φ)
  (hq : ∀ {m} {ψ : L.bounded_formula α m}, ψ.is_qf → P ψ)
  (ha : ∀ {m} {ψ : L.bounded_formula α (m + 1)}, P ψ → P ψ.all)
  (hn : ∀ {m} {ψ : L.bounded_formula α m}, P ψ → P ψ.not) :
  P φ :=
is_prenex.rec_on h (λ _ _, hq) (λ _ _ _, ha) (λ _ _ _ ih, hn (ha (hn ih)))

lemma is_prenex.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_prenex)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_prenex :=
is_prenex.rec_on h
  (λ _ _ h, (h.relabel f).is_prenex)
  (λ _ _ _ h, by simp [h.all])
  (λ _ _ _ h, by simp [h.ex])

lemma is_prenex.cast_le (hφ : is_prenex φ) :
  ∀ {n} {h : l ≤ n}, (φ.cast_le h).is_prenex :=
is_prenex.rec_on hφ
  (λ _ _ ih _ _, ih.cast_le.is_prenex)
  (λ _ _ _ ih _ _, ih.all)
  (λ _ _ _ ih _ _, ih.ex)

lemma is_prenex.lift_at {k m : ℕ} (h : is_prenex φ) : (φ.lift_at k m).is_prenex :=
is_prenex.rec_on h
  (λ _ _ ih, ih.lift_at.is_prenex)
  (λ _ _ _ ih, ih.cast_le.all)
  (λ _ _ _ ih, ih.cast_le.ex)

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.to_prenex_imp_right ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def to_prenex_imp_right :
  ∀ {n}, L.bounded_formula α n → L.bounded_formula α n → L.bounded_formula α n
| n φ (bounded_formula.ex ψ) := ((φ.lift_at 1 n).to_prenex_imp_right ψ).ex
| n φ (all ψ) := ((φ.lift_at 1 n).to_prenex_imp_right ψ).all
| n φ ψ := φ.imp ψ

lemma is_qf.to_prenex_imp_right {φ : L.bounded_formula α n} :
  Π {ψ : L.bounded_formula α n}, is_qf ψ → (φ.to_prenex_imp_right ψ = φ.imp ψ)
| _ is_qf.falsum := rfl
| _ (is_qf.of_is_atomic (is_atomic.equal _ _)) := rfl
| _ (is_qf.of_is_atomic (is_atomic.rel _ _)) := rfl
| _ (is_qf.imp is_qf.falsum _) := rfl
| _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _) := rfl
| _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _) := rfl
| _ (is_qf.imp (is_qf.imp _ _) _) := rfl

lemma is_prenex_to_prenex_imp_right {φ ψ : L.bounded_formula α n}
  (hφ : is_qf φ) (hψ : is_prenex ψ) :
  is_prenex (φ.to_prenex_imp_right ψ) :=
begin
  induction hψ with _ _ hψ _ _ _ ih1 _ _ _ ih2,
  { rw hψ.to_prenex_imp_right,
    exact (hφ.imp hψ).is_prenex },
  { exact (ih1 hφ.lift_at).all },
  { exact (ih2 hφ.lift_at).ex }
end

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.to_prenex_imp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def to_prenex_imp :
  ∀ {n}, L.bounded_formula α n → L.bounded_formula α n → L.bounded_formula α n
| n (bounded_formula.ex φ) ψ := (φ.to_prenex_imp (ψ.lift_at 1 n)).all
| n (all φ) ψ := (φ.to_prenex_imp (ψ.lift_at 1 n)).ex
| _ φ ψ := φ.to_prenex_imp_right ψ

lemma is_qf.to_prenex_imp : Π {φ ψ : L.bounded_formula α n}, φ.is_qf →
  φ.to_prenex_imp ψ = φ.to_prenex_imp_right ψ
| _ _ is_qf.falsum := rfl
| _ _ (is_qf.of_is_atomic (is_atomic.equal _ _)) := rfl
| _ _ (is_qf.of_is_atomic (is_atomic.rel _ _)) := rfl
| _ _ (is_qf.imp is_qf.falsum _) := rfl
| _ _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _) := rfl
| _ _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _) := rfl
| _ _ (is_qf.imp (is_qf.imp _ _) _) := rfl

lemma is_prenex_to_prenex_imp {φ ψ : L.bounded_formula α n}
  (hφ : is_prenex φ) (hψ : is_prenex ψ) :
  is_prenex (φ.to_prenex_imp ψ) :=
begin
  induction hφ with _ _ hφ _ _ _ ih1 _ _ _ ih2,
  { rw hφ.to_prenex_imp,
    exact is_prenex_to_prenex_imp_right hφ hψ },
  { exact (ih1 hψ.lift_at).ex },
  { exact (ih2 hψ.lift_at).all }
end

/-- For any bounded formula `φ`, `φ.to_prenex` is a semantically-equivalent formula in prenex normal
  form. -/
def to_prenex : ∀ {n}, L.bounded_formula α n → L.bounded_formula α n
| _ falsum        := ⊥
| _ (equal t₁ t₂) := t₁.bd_equal t₂
| _ (rel R ts)    := rel R ts
| _ (imp f₁ f₂)   := f₁.to_prenex.to_prenex_imp f₂.to_prenex
| _ (all f)       := f.to_prenex.all

lemma to_prenex_is_prenex (φ : L.bounded_formula α n) :
  φ.to_prenex.is_prenex :=
bounded_formula.rec_on φ
  (λ _, is_qf_bot.is_prenex)
  (λ _ _ _, (is_atomic.equal _ _).is_prenex)
  (λ _ _ _ _, (is_atomic.rel _ _).is_prenex)
  (λ _ _ _ h1 h2, is_prenex_to_prenex_imp h1 h2)
  (λ _ _, is_prenex.all)

end bounded_formula

namespace Lhom
open bounded_formula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp] def on_bounded_formula (g : L →ᴸ L') :
  ∀ {k : ℕ}, L.bounded_formula α k → L'.bounded_formula α k
| k falsum := falsum
| k (equal t₁ t₂) := (g.on_term t₁).bd_equal (g.on_term t₂)
| k (rel R ts) := (g.on_relation R).bounded_formula (g.on_term ∘ ts)
| k (imp f₁ f₂) := (on_bounded_formula f₁).imp (on_bounded_formula f₂)
| k (all f) := (on_bounded_formula f).all

@[simp] lemma id_on_bounded_formula :
  ((Lhom.id L).on_bounded_formula : L.bounded_formula α n → L.bounded_formula α n) = id :=
begin
  ext f,
  induction f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { rw [on_bounded_formula, Lhom.id_on_term, id.def, id.def, id.def, bd_equal] },
  { rw [on_bounded_formula, Lhom.id_on_term],
    refl, },
  { rw [on_bounded_formula, ih1, ih2, id.def, id.def, id.def] },
  { rw [on_bounded_formula, ih3, id.def, id.def] }
end

@[simp] lemma comp_on_bounded_formula {L'' : language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
  ((φ.comp ψ).on_bounded_formula : L.bounded_formula α n → L''.bounded_formula α n) =
    φ.on_bounded_formula ∘ ψ.on_bounded_formula :=
begin
  ext f,
  induction f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp only [on_bounded_formula, comp_on_term, function.comp_app],
    refl, },
  { simp only [on_bounded_formula, comp_on_relation, comp_on_term, function.comp_app],
    refl },
  { simp only [on_bounded_formula, function.comp_app, ih1, ih2, eq_self_iff_true, and_self], },
  { simp only [ih3, on_bounded_formula, function.comp_app] }
end

/-- Maps a formula's symbols along a language map. -/
def on_formula (g : L →ᴸ L') : L.formula α → L'.formula α :=
g.on_bounded_formula

/-- Maps a sentence's symbols along a language map. -/
def on_sentence (g : L →ᴸ L') : L.sentence → L'.sentence :=
g.on_formula

/-- Maps a theory's symbols along a language map. -/
def on_Theory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
g.on_sentence '' T

@[simp] lemma mem_on_Theory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.sentence} :
  φ ∈ g.on_Theory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.on_sentence φ₀ = φ :=
set.mem_image _ _ _

end Lhom

namespace Lequiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps] def on_bounded_formula (φ : L ≃ᴸ L') :
  L.bounded_formula α n ≃ L'.bounded_formula α n :=
{ to_fun := φ.to_Lhom.on_bounded_formula,
  inv_fun := φ.inv_Lhom.on_bounded_formula,
  left_inv := by rw [function.left_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.left_inv,
    Lhom.id_on_bounded_formula],
  right_inv := by rw [function.right_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.right_inv,
    Lhom.id_on_bounded_formula] }

lemma on_bounded_formula_symm (φ : L ≃ᴸ L') :
  (φ.on_bounded_formula.symm : L'.bounded_formula α n ≃ L.bounded_formula α n) =
    φ.symm.on_bounded_formula :=
rfl

/-- Maps a formula's symbols along a language equivalence. -/
def on_formula (φ : L ≃ᴸ L') :
  L.formula α ≃ L'.formula α :=
φ.on_bounded_formula

@[simp] lemma on_formula_apply (φ : L ≃ᴸ L') :
  (φ.on_formula : L.formula α → L'.formula α) = φ.to_Lhom.on_formula :=
rfl

@[simp] lemma on_formula_symm (φ : L ≃ᴸ L') :
  (φ.on_formula.symm : L'.formula α ≃ L.formula α) = φ.symm.on_formula :=
rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps] def on_sentence (φ : L ≃ᴸ L') :
  L.sentence ≃ L'.sentence :=
φ.on_formula

end Lequiv

localized "infix (name := term.bd_equal)
  ` =' `:88 := first_order.language.term.bd_equal" in first_order
  -- input \~- or \simeq
localized "infixr (name := bounded_formula.imp)
  ` ⟹ `:62 := first_order.language.bounded_formula.imp" in first_order
  -- input \==>
localized "prefix (name := bounded_formula.all)
  `∀'`:110 := first_order.language.bounded_formula.all" in first_order
localized "prefix (name := bounded_formula.not)
  `∼`:max := first_order.language.bounded_formula.not" in first_order
  -- input \~, the ASCII character ~ has too low precedence
localized "infix (name := bounded_formula.iff)
  ` ⇔ `:61 := first_order.language.bounded_formula.iff" in first_order -- input \<=>
localized "prefix (name := bounded_formula.ex)
  `∃'`:110 := first_order.language.bounded_formula.ex" in first_order -- input \ex

namespace formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.formula α → L.formula β :=
@bounded_formula.relabel _ _ _ 0 (sum.inl ∘ g) 0

/-- The graph of a function as a first-order formula. -/
def graph (f : L.functions n) : L.formula (fin (n + 1)) :=
equal (var 0) (func f (λ i, var i.succ))

/-- The negation of a formula. -/
protected def not (φ : L.formula α) : L.formula α := φ.not

/-- The implication between formulas, as a formula. -/
protected def imp : L.formula α → L.formula α → L.formula α := bounded_formula.imp

/-- The biimplication between formulas, as a formula. -/
protected def iff (φ ψ : L.formula α) : L.formula α := φ.iff ψ

lemma is_atomic_graph (f : L.functions n) : (graph f).is_atomic :=
bounded_formula.is_atomic.equal _ _

/-- A bijection sending formulas to sentences with constants. -/
def equiv_sentence : L.formula α ≃ L[[α]].sentence :=
(bounded_formula.constants_vars_equiv.trans
  (bounded_formula.relabel_equiv (equiv.sum_empty _ _))).symm

lemma equiv_sentence_not (φ : L.formula α) :
  equiv_sentence φ.not = (equiv_sentence φ).not :=
rfl

lemma equiv_sentence_inf (φ ψ : L.formula α) :
  equiv_sentence (φ ⊓ ψ) = equiv_sentence φ ⊓ equiv_sentence ψ :=
rfl

end formula

namespace relations

variable (r : L.relations 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.sentence := ∀' r.bounded_formula₂ &0 &0

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.sentence := ∀' ∼ (r.bounded_formula₂ &0 &0)

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.sentence := ∀' ∀' (r.bounded_formula₂ &0 &1 ⟹ r.bounded_formula₂ &1 &0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.sentence :=
  ∀' ∀' (r.bounded_formula₂ &0 &1 ⟹ (r.bounded_formula₂ &1 &0 ⟹ term.bd_equal &0 &1))

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.sentence :=
  ∀' ∀' ∀' (r.bounded_formula₂ &0 &1 ⟹ r.bounded_formula₂ &1 &2 ⟹ r.bounded_formula₂ &0 &2)

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.sentence :=
  ∀' ∀' (r.bounded_formula₂ &0 &1 ⊔ r.bounded_formula₂ &1 &0)

end relations

section cardinality

variable (L)

/-- A sentence indicating that a structure has `n` distinct elements. -/
protected def sentence.card_ge (n) : L.sentence :=
(((((list.fin_range n).product (list.fin_range n)).filter (λ ij : _ × _, ij.1 ≠ ij.2)).map
  (λ (ij : _ × _), ∼ ((& ij.1).bd_equal (& ij.2)))).foldr (⊓) ⊤).exs

/-- A theory indicating that a structure is infinite. -/
def infinite_theory : L.Theory := set.range (sentence.card_ge L)

/-- A theory that indicates a structure is nonempty. -/
def nonempty_theory : L.Theory := {sentence.card_ge L 1}

/-- A theory indicating that each of a set of constants is distinct. -/
def distinct_constants_theory (s : set α) : L[[α]].Theory :=
(λ ab : α × α, (((L.con ab.1).term.equal (L.con ab.2).term).not)) '' (s ×ˢ s ∩ (set.diagonal α)ᶜ)

variables {L} {α}

open set

lemma monotone_distinct_constants_theory :
  monotone (L.distinct_constants_theory : set α → L[[α]].Theory) :=
λ s t st, (image_subset _ (inter_subset_inter_left _ (prod_mono st st)))

lemma directed_distinct_constants_theory :
  directed (⊆) (L.distinct_constants_theory : set α → L[[α]].Theory) :=
monotone.directed_le monotone_distinct_constants_theory

lemma distinct_constants_theory_eq_Union (s : set α) :
  L.distinct_constants_theory s = ⋃ (t : finset s), L.distinct_constants_theory
    (t.map (function.embedding.subtype (λ x, x ∈ s))) :=
begin
  classical,
  simp only [distinct_constants_theory],
  rw [← image_Union, ← Union_inter],
  refine congr rfl (congr (congr rfl _) rfl),
  ext ⟨i, j⟩,
  simp only [prod_mk_mem_set_prod_eq, finset.coe_map, function.embedding.coe_subtype, mem_Union,
    mem_image, finset.mem_coe, subtype.exists, subtype.coe_mk, exists_and_distrib_right,
    exists_eq_right],
  refine ⟨λ h, ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, _⟩, ⟨h.2, _⟩⟩, _⟩,
  { simp },
  { simp },
  { rintros ⟨t, ⟨is, _⟩, ⟨js, _⟩⟩,
    exact ⟨is, js⟩ }
end

end cardinality

end language
end first_order
