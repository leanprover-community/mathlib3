/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.satisfiability

/-!
# Ordered First-Ordered Structures
This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions
* `first_order.language.order` is the language consisting of a single relation representing `≤`.
* `first_order.language.order_Structure` is the structure on an ordered type, assigning the symbol
representing `≤` to the actual relation `≤`.
* `first_order.language.is_ordered` points out a specific symbol in a language as representing `≤`.
* `first_order.language.ordered_structure` indicates that the `≤` symbol in an ordered language
is interpreted as the actual relation `≤` in a particular structure.
* `first_order.language.linear_order_theory` and similar define the theories of preorders,
partial orders, and linear orders.
* `first_order.language.DLO` defines the theory of dense linear orders without endpoints, a
particularly useful example in model theory.

## Main Results
* `partial_order`s model the theory of partial orders, `linear_order`s model the theory of
linear orders, and dense linear orders without endpoints model `Theory.DLO`.

-/

universes u v w w'

namespace first_order
namespace language
open_locale first_order
open Structure category_theory

variables {L : language.{u v}} {α : Type w} {M : Type w'} {n : ℕ}

/-- The language consisting of a single relation representing `≤`. -/
protected def order : language :=
language.mk₂ empty empty empty empty unit

/-- The `language.order.Structure` on an ordered type, assigning the symbol representing `≤` to the
  actual relation `≤`. This can be taken as a local instance when there are no local instances
  converting first-order structures to order instances. -/
def order_Structure [has_le M] : language.order.Structure M :=
Structure.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, (≤))

namespace order

instance : is_relational (language.order) := language.is_relational_mk₂

instance : subsingleton (language.order.relations n) :=
language.subsingleton_mk₂_relations

end order

/-- A language is ordered if it has a symbol representing `≤`. -/
class is_ordered (L : language.{u v}) := (le_symb : L.relations 2)

export is_ordered (le_symb)

section is_ordered

variables [is_ordered L]

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`. -/
def term.le (t₁ t₂ : L.term (α ⊕ fin n)) : L.bounded_formula α n :=
le_symb.bounded_formula₂ t₁ t₂

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ < t₂`. -/
def term.lt (t₁ t₂ : L.term (α ⊕ fin n)) : L.bounded_formula α n :=
(t₁.le t₂) ⊓ ∼ (t₂.le t₁)

variables (L M)

/-- The `has_le` instance defining `≤` to be the relation represented by the `≤` symbol in an
  ordered language. This can be taken as a local instance when there are no local instances
  converting order instances into `L`-structures. -/
def is_ordered.has_le [L.Structure M] : has_le M :=
⟨λ a b, rel_map (le_symb : L.relations 2) ![a,b]⟩

instance bundled_has_le {M : bundled L.Structure} : has_le M :=
is_ordered.has_le L M

instance Model.has_le {T : L.Theory} {M : T.Model} : has_le M :=
is_ordered.has_le L M

/-- The language homomorphism sending the unique symbol `≤` of `language.order` to `≤` in an ordered
 language. -/
def order_Lhom : language.order →ᴸ L :=
Lhom.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, le_symb)

end is_ordered

instance : is_ordered language.order := ⟨punit.star⟩

@[simp] lemma order.forall_relations {P : Π {n : ℕ} (R : language.order.relations n), Prop} :
  (∀ {n : ℕ} (R : language.order.relations n), P R) ↔ P le_symb :=
begin
  refine ⟨λ h, h le_symb, λ h, _⟩,
  rintro (_ | _ | _ | n) ⟨_⟩,
  exact h,
end

@[simp] lemma order_Lhom_le_symb [L.is_ordered] :
  (order_Lhom L).on_relation le_symb = (le_symb : L.relations 2) := rfl

@[simp]
lemma order_Lhom_order : order_Lhom language.order = Lhom.id language.order :=
Lhom.funext (subsingleton.elim _ _) (subsingleton.elim _ _)

instance : is_ordered (L.sum language.order) := ⟨sum.inr is_ordered.le_symb⟩

section
variables (L) [is_ordered L]

/-- The theory of preorders. -/
def preorder_theory : L.Theory :=
{le_symb.reflexive, le_symb.transitive}

/-- The theory of partial orders. -/
def partial_order_theory : L.Theory :=
{le_symb.reflexive, le_symb.antisymmetric, le_symb.transitive}

/-- The theory of linear orders. -/
def linear_order_theory : L.Theory :=
{le_symb.reflexive, le_symb.antisymmetric, le_symb.transitive, le_symb.total}

/-- A sentence indicating that an order has no top element:
$\forall x, \exists y, \neg y \le x$.   -/
def no_top_order_sentence : L.sentence := ∀' ∃' ∼ ((&1).le &0)

/-- A sentence indicating that an order has no bottom element:
$\forall x, \exists y, \neg x \le y$. -/
def no_bot_order_sentence : L.sentence := ∀' ∃' ∼ ((&0).le &1)

/-- A sentence indicating that an order is dense:
$\forall x, \forall y, x < y \to \exists z, x < z \wedge z < y$. -/
def densely_ordered_sentence : L.sentence :=
∀' ∀' (((&0).lt &1) ⟹ (∃' (((&0).lt &2) ⊓ ((&2).lt &1))))

/-- The theory of dense linear orders without endpoints. -/
def DLO : L.Theory :=
L.linear_order_theory ∪
  {L.no_top_order_sentence, L.no_bot_order_sentence, L.densely_ordered_sentence}

end

variables (L M)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
class ordered_structure [is_ordered L] [has_le M] [L.Structure M] : Prop :=
(rel_map_le_symb : ∀ x : fin 2 → M, rel_map (le_symb : L.relations 2) x ↔ x 0 ≤ x 1)

variables {L M}

export ordered_structure (rel_map_le_symb)

attribute [simp] rel_map_le_symb

instance ordered_structure.is_expansion_on
  [is_ordered L] [has_le M] [language.order.Structure M] [L.Structure M]
  [language.order.ordered_structure M] [L.ordered_structure M] :
  Lhom.is_expansion_on (order_Lhom L) M :=
begin
  refine ⟨λ _ f _, is_empty_elim f, _⟩,
  rw order.forall_relations,
  intro x,
  exact eq_iff_iff.2 ((rel_map_le_symb _).trans (rel_map_le_symb _).symm)
end

section ordered_structure
variables [is_ordered L] [L.Structure M]

@[simp] lemma term.realize_le [has_le M] [L.ordered_structure M]
  {t₁ t₂ : L.term (α ⊕ fin n)} {v : α → M} {xs : fin n → M} :
  (t₁.le t₂).realize v xs ↔ t₁.realize (sum.elim v xs) ≤ t₂.realize (sum.elim v xs) :=
by simp [term.le]

@[simp] lemma term.realize_lt [preorder M] [L.ordered_structure M]
  {t₁ t₂ : L.term (α ⊕ fin n)} {v : α → M} {xs : fin n → M} :
  (t₁.lt t₂).realize v xs ↔ t₁.realize (sum.elim v xs) < t₂.realize (sum.elim v xs) :=
by simp [term.lt, lt_iff_le_not_le]

end ordered_structure

section has_le_to_structure

local attribute [instance] language.order_Structure

instance ordered_structure_has_le [has_le M] :
  ordered_structure language.order M :=
⟨λ _, iff.rfl⟩

end has_le_to_structure

/-- If `is_ordered.has_le` is used to generate a `has_le` instance on an `L.Structure`, then the
  resulting `≤` relations agree, making this an `L.ordered_structure`. -/
@[priority 100] instance is_ordered.has_le_ordered_structure
  [is_ordered L] {M : Type*} [L.Structure M] :
  @ordered_structure L M _ (is_ordered.has_le L M) _ :=
begin
  letI := is_ordered.has_le L M,
  refine ⟨λ x, _⟩,
  have hx : x = ![x 0, x 1],
  { rw [function.funext_iff, fin.forall_fin_two],
    refine ⟨rfl, rfl⟩ },
  rw hx,
  refl,
end

section has_le
variables [has_le M] [is_ordered L] [L.Structure M] [L.ordered_structure M]

theorem realize_no_top_order_iff : M ⊨ L.no_top_order_sentence ↔ no_top_order M :=
begin
  simp only [no_top_order_sentence, sentence.realize, formula.realize, bounded_formula.realize_all,
    bounded_formula.realize_ex, bounded_formula.realize_not, realize, term.realize_le,
    sum.elim_inr],
  refine ⟨λ h, ⟨λ a, h a⟩, _⟩,
  introsI h a,
  exact exists_not_le a,
end

@[simp] lemma realize_no_top_order [h : no_top_order M] : M ⊨ L.no_top_order_sentence :=
realize_no_top_order_iff.2 h

theorem realize_no_bot_order_iff : M ⊨ L.no_bot_order_sentence ↔ no_bot_order M :=
begin
  simp only [no_bot_order_sentence, sentence.realize, formula.realize, bounded_formula.realize_all,
    bounded_formula.realize_ex, bounded_formula.realize_not, realize, term.realize_le,
    sum.elim_inr],
  refine ⟨λ h, ⟨λ a, h a⟩, _⟩,
  introsI h a,
  exact exists_not_ge a,
end

@[simp] lemma realize_no_bot_order [h : no_bot_order M] : M ⊨ L.no_bot_order_sentence :=
realize_no_bot_order_iff.2 h

end has_le

section preorder

variables [preorder M] [is_ordered L] [L.Structure M] [L.ordered_structure M]

instance model_preorder :
  M ⊨ L.preorder_theory :=
begin
  simp only [preorder_theory, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, forall_eq,
    relations.realize_transitive, rel_map_le_symb],
  exact ⟨le_refl, λ _ _ _, le_trans⟩
end

theorem realize_densely_ordered_iff :
  M ⊨ L.densely_ordered_sentence ↔ densely_ordered M :=
begin
  simp only [densely_ordered_sentence, sentence.realize, formula.realize,
    bounded_formula.realize_imp, bounded_formula.realize_all, realize, term.realize_lt,
    sum.elim_inr, bounded_formula.realize_ex, bounded_formula.realize_inf],
  refine ⟨λ h, ⟨λ a b ab, h a b ab⟩, _⟩,
  introsI h a b ab,
  exact exists_between ab,
end

@[simp] lemma realize_densely_ordered [h : densely_ordered M] :
  M ⊨ L.densely_ordered_sentence :=
realize_densely_ordered_iff.2 h

end preorder

instance model_partial_order
  [partial_order M] [is_ordered L] [L.Structure M] [L.ordered_structure M] :
  M ⊨ L.partial_order_theory :=
begin
  simp only [partial_order_theory, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    forall_eq, relations.realize_transitive, rel_map_le_symb],
  exact ⟨le_refl, λ _ _, le_antisymm, λ _ _ _, le_trans⟩,
end

section linear_order

variables [linear_order M] [is_ordered L] [L.Structure M] [L.ordered_structure M]

instance model_linear_order :
  M ⊨ L.linear_order_theory :=
begin
  simp only [linear_order_theory, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    relations.realize_transitive, forall_eq, relations.realize_total, rel_map_le_symb],
  exact ⟨le_refl, λ _ _, le_antisymm, λ _ _ _, le_trans, le_total⟩,
end

theorem model_DLO_iff :
  M ⊨ L.DLO ↔ no_top_order M ∧ no_bot_order M ∧ densely_ordered M :=
begin
  rw [DLO, Theory.model_union_iff],
  simp only [language.model_linear_order, true_and],
  simp only [Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, realize_no_top_order_iff, realize_no_bot_order_iff, realize_densely_ordered_iff],
end

variable (L)

/-- This shows that a densely linear ordered `language.order.Structure` without endpoints models the
  theory of dense linear orders without endpoints. This can be taken as a local instance when it
  will not create a loop. -/
lemma model_DLO [a : no_top_order M] [b : no_bot_order M] [c : densely_ordered M] :
  M ⊨ L.DLO :=
model_DLO_iff.2 ⟨a, b, c⟩

/-- This shows that a model of the theory of dense linear orders without endpoints has no top
  element. This can be taken as a local instance when it will not create a loop. -/
lemma no_top_order_of_model_DLO [h : M ⊨ L.DLO] :
  no_top_order M :=
(model_DLO_iff.1 h).1

/-- This shows that a model of the theory of dense linear orders without endpoints has no maximal
  element. This can be taken as a local instance when it will not create a loop. -/
lemma no_max_order_of_model_DLO [h : M ⊨ L.DLO] :
  no_max_order M :=
(no_top_order_iff_no_max_order _).1 L.no_top_order_of_model_DLO

/-- This shows that a model of the theory of dense linear orders without endpoints has no bottom
  element. This can be taken as a local instance when it will not create a loop. -/
lemma no_bot_order_of_model_DLO [h : M ⊨ L.DLO] :
  no_bot_order M :=
(model_DLO_iff.1 h).2.1

/-- This shows that a model of the theory of dense linear orders without endpoints has no minimal
  element. This can be taken as a local instance when it will not create a loop. -/
lemma no_min_order_of_model_DLO [h : M ⊨ L.DLO] :
  no_min_order M :=
(no_bot_order_iff_no_min_order _).1 L.no_bot_order_of_model_DLO

/-- This shows that a model of the theory of dense linear orders without endpoints is densely
  ordered. This can be taken as a local instance when it will not create a loop. -/
lemma densely_ordered_of_model_DLO [h : M ⊨ L.DLO] :
  densely_ordered M :=
(model_DLO_iff.1 h).2.2

end linear_order

end language
end first_order
