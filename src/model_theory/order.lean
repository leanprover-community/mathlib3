/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.satisfiability
import order.countable_dense_linear_order
import data.set.intervals.infinite

/-!
# Ordered First-Ordered Structures
This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions
* `first_order.language.order` is the language consisting of a single relation representing `≤`.
* `first_order.language.order_Structure` is the structure on an ordered type, assigning the symbol
representing `≤` to the actual relation `≤`.
* `first_order.language.is_ordered` points out a specific symbol in a language as representing `≤`.
* `first_order.language.is_ordered_structure` indicates that a structure over a
* `first_order.language.linear_order_theory` and similar define the theories of preorders,
partial orders, and linear orders.
* `first_order.language.DLO` defines the theory of dense linear orders without endpoints, a
particularly useful example in model theory.

## Main Results
* `partial_order`s model the theory of partial orders, `linear_order`s model the theory of
linear orders, and dense linear orders without endpoints model `DLO`.
* `first_order.language.aleph_0_categorical_DLO`: The theory of dense linear orders without
endpoints is `ℵ₀`-categorical, meaning that there is a unique countable model up to isomorphism.
* `first_order.language.DLO_complete`: As a direct consequence of categoricity, the theory of dense
linear orders without endpoints is complete.

## Implementation Notes
* First-order structures in ordered languages can give rise to order instances, and order instances
can give rise to first-order structure. Care should be taken not to create a loop, so neither
direction is a global instance.

-/

universes u v w w'

namespace first_order
namespace language
open_locale first_order
open category_theory Structure cardinal

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

@[simp] lemma card_eq_one : language.order.card = 1 :=
by simp [language.order]

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

variable (L)

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

namespace Theory

variables {L} [is_ordered L]

lemma preorder_subset_partial_order : L.preorder_theory ⊆ L.partial_order_theory :=
λ φ hφ, begin
  simp only [preorder_theory, set.mem_insert_iff, set.mem_singleton_iff] at hφ,
  simp only [partial_order_theory, set.mem_insert_iff, set.mem_singleton_iff],
  exact hφ.elim (or.intro_left _) (or.intro_right _ ∘ or.intro_right _),
end

lemma partial_order_subset_linear_order : L.partial_order_theory ⊆ L.linear_order_theory :=
λ φ hφ, begin
  simp only [linear_order_theory, set.mem_insert_iff, set.mem_singleton_iff],
  simp only [partial_order_theory, set.mem_insert_iff, set.mem_singleton_iff] at hφ,
  exact hφ.elim (or.intro_left _) (or.intro_right _ ∘ or.imp_right (or.intro_left _)),
end

lemma linear_order_subset_DLO : L.linear_order_theory ⊆ L.DLO :=
set.subset_union_left _ _

variables [L.Structure M]

instance model_preorder_of_partial_order [h : M ⊨ L.partial_order_theory] : M ⊨ L.preorder_theory :=
Theory.model.mono h preorder_subset_partial_order

instance model_partial_order_of_linear_order [h : M ⊨ L.linear_order_theory] :
  M ⊨ L.partial_order_theory :=
Theory.model.mono h partial_order_subset_linear_order

instance model_linear_order_of_DLO [h : M ⊨ L.DLO] :
  M ⊨ L.linear_order_theory :=
Theory.model.mono h linear_order_subset_DLO

end Theory

variables (L M)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
class is_ordered_structure [is_ordered L] [has_le M] [L.Structure M] : Prop :=
(rel_map_le_symb : ∀ x : fin 2 → M, rel_map (le_symb : L.relations 2) x ↔ x 0 ≤ x 1)

variables {L M}

export is_ordered_structure (rel_map_le_symb)

attribute [simp] rel_map_le_symb

instance is_ordered_structure.is_expansion_on
  [is_ordered L] [has_le M] [language.order.Structure M] [L.Structure M]
  [language.order.is_ordered_structure M] [L.is_ordered_structure M] :
  Lhom.is_expansion_on (order_Lhom L) M :=
begin
  refine ⟨λ _ f _, is_empty_elim f, _⟩,
  rw order.forall_relations,
  intro x,
  exact eq_iff_iff.2 ((rel_map_le_symb _).trans (rel_map_le_symb _).symm)
end

section is_ordered_structure
variables [is_ordered L] [L.Structure M]

@[simp] lemma term.realize_le [has_le M] [L.is_ordered_structure M]
  {t₁ t₂ : L.term (α ⊕ fin n)} {v : α → M} {xs : fin n → M} :
  (t₁.le t₂).realize v xs ↔ t₁.realize (sum.elim v xs) ≤ t₂.realize (sum.elim v xs) :=
by simp [term.le]

@[simp] lemma term.realize_lt [preorder M] [L.is_ordered_structure M]
  {t₁ t₂ : L.term (α ⊕ fin n)} {v : α → M} {xs : fin n → M} :
  (t₁.lt t₂).realize v xs ↔ t₁.realize (sum.elim v xs) < t₂.realize (sum.elim v xs) :=
by simp [term.lt, lt_iff_le_not_le]

end is_ordered_structure

section has_le_to_structure

local attribute [instance] language.order_Structure

instance is_ordered_structure_has_le [has_le M] :
  is_ordered_structure language.order M :=
⟨λ _, iff.rfl⟩

end has_le_to_structure

/-- If `is_ordered.has_le` is used to generate a `has_le` instance on an `L.Structure`, then the
  resulting `≤` relations agree, making this an `L.is_ordered_structure`. -/
@[priority 100] instance is_ordered.has_le_is_ordered_structure [is_ordered L] {M : Type*} [L.Structure M] :
  @is_ordered_structure L M _ (is_ordered.has_le L M) _ :=
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
variables [has_le M] [is_ordered L] [L.Structure M] [L.is_ordered_structure M]

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

variables [preorder M] [is_ordered L] [L.Structure M] [L.is_ordered_structure M]

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
  [partial_order M] [is_ordered L] [L.Structure M] [L.is_ordered_structure M] :
  M ⊨ L.partial_order_theory :=
begin
  simp only [partial_order_theory, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    forall_eq, relations.realize_transitive, rel_map_le_symb],
  exact ⟨le_refl, λ _ _, le_antisymm, λ _ _ _, le_trans⟩,
end

section linear_order

variables [linear_order M] [is_ordered L] [L.Structure M] [L.is_ordered_structure M]

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

section

variables (L) [is_ordered L] [L.Structure M]

/-- Given a model of the theory of preorders, induces a `preorder` structure. Can be used as a local
  instance in the absence of other local instances converting between first-order structure and
  order instances. -/
def induced_preorder [M ⊨ L.preorder_theory] : preorder M :=
{ le_refl := relations.realize_reflexive.1
      (L.preorder_theory.realize_sentence_of_mem (set.mem_insert _ _)),
  le_trans := relations.realize_transitive.1
      (L.preorder_theory.realize_sentence_of_mem (set.mem_insert_of_mem _ (set.mem_singleton _))),
  .. is_ordered.has_le L M }

/-- Given a model of the theory of partial orders, induces a `partial_order` structure. Can be used
  as a local instance in the absence of other local instances converting between first-order
  structure and order instances. -/
def induced_partial_order [M ⊨ L.partial_order_theory] : partial_order M :=
{ le_antisymm := relations.realize_antisymmetric.1
      (L.partial_order_theory.realize_sentence_of_mem (set.mem_insert_of_mem _ (set.mem_insert _ _))),
  .. induced_preorder L }

/-- Given a model of the theory of linear orders, induces a `linear_order` structure. Can be used
  as a local instance in the absence of other local instances converting between first-order
  structure and order instances. -/
def induced_linear_order [M ⊨ L.linear_order_theory]
  [h : decidable_rel (λ a b : M, rel_map (le_symb : L.relations 2) ![a,b])] :
  linear_order M :=
{ decidable_le := h,
  le_total := relations.realize_total.1
      (L.linear_order_theory.realize_sentence_of_mem (set.mem_insert_of_mem _
        (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_singleton _))))),
  .. induced_partial_order L }

end

/-- An equivalence between `language.order` isomorphisms and order isomorphisms. -/
def order.equiv_equiv_order_iso
  {N : Type*} [language.order.Structure M] [language.order.Structure N] [has_le M] [has_le N]
  [language.order.is_ordered_structure M] [language.order.is_ordered_structure N] :
  (M ≃[language.order] N) ≃ (M ≃o N) :=
begin
  refine ⟨λ f, ⟨f, λ a b, _⟩, λ f, _, _, _⟩,
  { have h := f.map_rel le_symb (![a,b]),
    exact (rel_map_le_symb (f ∘ ![a, b])).symm.trans (h.trans (rel_map_le_symb _)) },
  { refine ⟨f, λ n F x, is_empty_elim F, _⟩,
    rw order.forall_relations,
    intro x,
    simp only [rel_map_le_symb, equiv.to_fun_as_coe, function.comp_app],
    exact f.map_rel_iff, },
  { intro f,
    ext,
    refl, },
  { intro f,
    ext,
    refl, },
end

section
open Theory

theorem DLO_is_satisfiable : language.order.DLO.is_satisfiable :=
begin
  letI : language.order.Structure ℚ := language.order_Structure,
  haveI : ℚ ⊨ language.order.DLO := language.order.model_DLO,
  exact ⟨Model.of language.order.DLO ℚ⟩,
end

local attribute [instance] no_min_order_of_model_DLO no_max_order_of_model_DLO
  densely_ordered_of_model_DLO encodable.of_countable

/-- The theory of dense linear orders without endpoints is `ℵ₀`-categorical. -/
theorem aleph_0_categorical_DLO :
  cardinal.aleph_0.categorical language.order.DLO :=
begin
  classical,
  intros M N hM hN,
  letI : linear_order M := language.order.induced_linear_order,
  letI : linear_order N := language.order.induced_linear_order,
  haveI : countable M := mk_le_aleph_0_iff.1 (le_of_eq hM),
  haveI : countable N := mk_le_aleph_0_iff.1 (le_of_eq hN),
  exact order.equiv_equiv_order_iso.nonempty_congr.2 (order.iso_of_countable_dense M N),
end

/-- The theory of dense linear orders without endpoints is complete. -/
theorem DLO_is_complete :
  language.order.DLO.is_complete :=
begin
  classical,
  refine aleph_0_categorical_DLO.is_complete _ _ le_rfl _ DLO_is_satisfiable (λ M, _),
  { simp only [language.order.card_eq_one, lift_one, lift_aleph_0],
    exact cardinal.one_le_aleph_0 },
  { letI : linear_order M := language.order.induced_linear_order,
    exact no_min_order.infinite }
end

end

end language
end first_order
