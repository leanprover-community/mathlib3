/-
Copyright (c) 2021. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich (modified for mathlib by Hunter Monroe)
 -/

import measure_theory.measurable_space
import measure_theory.measure_space

/-!
This file defines the basic concepts in probability theory.
probability_space: a measure_space where the measure has a value of 1.
event: a set that is measurable (defined based upon the measurable space),
Pr[E]: the probability of an event.
-/

open measure_theory measurable_space
open_locale big_operators classical

namespace probability_theory

/- An event is a measurable set in a measurable space that has a probability measure. Note:
the definition below does not require that the measurable_space have volume one. -/
@[derive [has_union,has_emptyc,has_compl, has_sdiff,has_union,has_inter,boolean_algebra]]
def event (Ω : Type*) [measurable_space Ω] : Type* := {x : set Ω // measurable_set x}

/- A probability space is a measure space with volume one. -/
class probability_space (α : Type*) extends measure_space α := (volume_univ : volume (set.univ) = 1)

export probability_space (volume_univ)

@[simp]
lemma probability_space.univ_one' {α:Type*} (Pα:probability_space α):
  (@measure_theory.measure_space.volume α Pα.to_measure_space) (@set.univ α) = 1 :=
begin
  rw ← measure_theory.coe_to_outer_measure,
  rw ← measure_theory.outer_measure.measure_of_eq_coe,
  simp,
  rw probability_space.volume_univ,
end

lemma event_val_eq_coe {Ω : Type*} [probability_space Ω]
  (X : event Ω) : X.val =
  (@coe (subtype (@measurable_set Ω _)) (set Ω) _ X) :=
  by refl

lemma event.eq {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  A.val = B.val → A = B := subtype.eq

def event_mem {Ω : Type*} [P : probability_space Ω] (a : Ω) (E : event Ω) : Prop :=
  a ∈ E.val

/- The weight of an event is ≤1. -/
lemma prob_le_1 {Ω : Type*} [probability_space Ω] (S : set Ω) :
  volume S ≤ 1 :=
begin
  have A3 : volume S ≤ volume set.univ := volume.mono (set.subset_univ _),
  rw volume_univ at A3,
  exact A3,
end

/- The probability of an event is not infinite. -/
lemma prob_not_infinite {Ω : Type*} [probability_space Ω] (S : set Ω) :
  (volume S) ≠ ⊤ :=
begin
  have A1 : volume S ≤ 1,
  {  apply prob_le_1,},
  intro A2,
  rw A2 at A1,
  have A3 : (1 : ennreal)=⊤,
  { apply complete_linear_order.le_antisymm,
  { apply (ennreal.complete_linear_order.le_top),},
  { apply A1,}},
  have A4 : (1 : ennreal) ≠ (⊤ : ennreal),
  { apply ennreal.one_ne_top,},
  rw A3 at A4,
  apply A4,
  refl,
end

/- Probabilities are non-negative real numbers. -/
lemma prob_nnreal {Ω : Type*} [probability_space Ω] (S : set Ω) :
   ↑((volume S).to_nnreal) = volume S :=
begin
  apply ennreal.coe_to_nnreal,
  apply prob_not_infinite,
end

/- The probability of an event is equal to its measure. -/
def event_prob {Ω : Type*} [probability_space Ω] (E : event Ω) : nnreal :=
  (volume E.val).to_nnreal

/- Pr[E] is the probability of an event. -/
notation `Pr[`E`]` := event_prob E

lemma event_prob_def {Ω : Type*} [probability_space Ω] (E : event Ω) :
  ↑(Pr[E]) = (volume E.val) := by
begin
  unfold event_prob,
  apply prob_nnreal,
end

lemma to_nnreal_almost_monotonic (a b : ennreal) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
  a ≤ b →a.to_nnreal ≤ b.to_nnreal :=
begin
  exact (ennreal.to_real_le_to_real ha hb).mpr
end

lemma event_prob_mono1 {Ω : Type*} [probability_space Ω] (E F : event Ω) :
  volume E.val ≤ volume F.val →
  Pr[E] ≤ Pr[F] :=
begin
  unfold event_prob,
  intro A1,
  apply to_nnreal_almost_monotonic,
  apply prob_not_infinite,
  apply prob_not_infinite,
  apply A1,
end

lemma event_prob_mono2 {Ω : Type*} [probability_space Ω] (E F : event Ω) :
  (E.val ⊆ F.val) →
  Pr[E] ≤ Pr[F] :=
begin
  intro A1,
  apply event_prob_mono1,
  apply volume.mono,
  apply A1,
end

/- The event universe consists of all outcomes. -/
def event_univ (Ω : Type*) [measurable_space Ω] : event Ω := ⊤

@[simp]
lemma event_univ_val_def {Ω : Type*} [probability_space Ω] :
  (event_univ Ω).val = set.univ := by exact rfl

/- The probability of the event universe is 1. -/
@[simp]
lemma Pr_event_univ {Ω : Type*} [probability_space Ω] :
  Pr[event_univ Ω] = 1 :=
begin
  have A1 : ↑(Pr[event_univ Ω]) = (1 : ennreal),
  { rw event_prob_def,
    apply volume_univ,},
  simp at A1,
  apply A1
end

/- The probability (Pr) of an event is ≤1. -/
@[simp]
lemma Pr_le_one {Ω : Type*} [probability_space Ω] {E : event Ω} : Pr[E] ≤ 1 :=
begin
  have A1 : Pr[E] ≤ Pr[event_univ Ω],
  { apply event_prob_mono2,
    rw event_univ_val_def,
    rw set.subset_def,simp,},
  rw Pr_event_univ at A1,
  apply A1,
end

/- The empty event has weight zero. -/
def event_empty (Ω : Type*) [measurable_space Ω] : event Ω :=
  { val := ∅,
  property := measurable_set.empty,}

/- Every probability space has the empty event, corresponding to the empty set. -/
@[simp]
lemma event_empty_val_def {Ω : Type*} [probability_space Ω] :
  (event_empty Ω).val = ∅ := rfl

/- Every probability space has the empty event, corresponding to the empty set. -/
@[simp]
lemma event_empty_val_def2 {Ω : Type*} [probability_space Ω] :
  (@has_emptyc.emptyc (event Ω) _).val = ∅ := rfl

/- The probability of an empty event is zero. -/
@[simp]
lemma Pr_event_empty {Ω : Type*} [probability_space Ω] : Pr[event_empty Ω] = 0 :=
begin
  have A1 : ↑(Pr[event_empty Ω]) = (0 : ennreal),
  rw event_prob_def,
  apply volume.empty,
  simp at A1,
  apply A1
end

/- The probability of the empty set is zero. -/
@[simp]
lemma Pr_event_empty' {Ω : Type*} [probability_space Ω] : Pr[(∅ : event Ω)] = 0 := Pr_event_empty

def event_const (Ω : Type*) [probability_space Ω] (P : Prop) : event Ω :=
  { val := {ω : Ω|P},
  property := measurable_set.const P,}

@[simp]
lemma event_const_val_def {Ω : Type*} [probability_space Ω] (P : Prop) :
  (event_const _ P).val = {ω : Ω|P} := rfl

lemma event_const_true_eq_univ {Ω : Type*} [probability_space Ω] (P : Prop) : P →
(event_const _ P) = event_univ Ω :=
begin
  intro A1,
  apply event.eq,
  simp [A1],
end

lemma event_const_false_eq_empty {Ω : Type*} [probability_space Ω] (P : Prop) : ¬P →
(event_const _ P) = event_empty Ω :=
begin
  intro A1,
  apply event.eq,
  simp [A1],
end

lemma Pr_event_const_true {Ω : Type*} [probability_space Ω] (P : Prop) : P →
Pr[(event_const Ω P)] = 1 :=
begin
  intro A1,
  rw event_const_true_eq_univ,
  apply Pr_event_univ,
  exact A1,
end

lemma Pr_event_const_false {Ω : Type*} [probability_space Ω] (P : Prop) : ¬P →
Pr[(event_const Ω P)] = 0 :=
begin
  intro A1,
  rw event_const_false_eq_empty,
  apply Pr_event_empty,
  exact A1,
end

/- The "and" of two events is their intersection. -/
def measurable_inter {Ω : Type*} [measurable_space Ω] (A B : event Ω) : event Ω :=
  { val :=A.val ∩ B.val,
  property := measurable_set.inter A.property B.property,}

@[simp]
lemma measurable_inter_val_def {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (measurable_inter A B).val= A.val ∩ B.val := rfl

@[simp]
lemma measurable_inter_val_def2 {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (A ∩ B).val= A.val ∩ B.val := rfl

/- The weight of the eand of two events is their intersection. -/
@[simp]
lemma eand_val_def {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∩ B).val = A.val ∩ B.val := by refl

/- Event intersection eand is commutative. -/
lemma eand_comm {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∩ B) = (B ∩ A) :=
begin
  apply event.eq,
  simp [set.inter_comm],
end

/- Event intersection eand is associative. -/
lemma eand_assoc {Ω : Type*} [probability_space Ω] (A B C : event Ω) :
  ((A ∩ B) ∩ C) = (A ∩ (B ∩ C)) :=
begin
  apply event.eq,
  simp [set.inter_assoc],
end

lemma eand_eq_self_of_subset_left {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A.val ⊆ B.val) →
  (A ∩ B) = A :=
begin
  intro A1,
  apply event.eq,
  simp,
  apply set.inter_eq_self_of_subset_left,
  exact A1,
end

lemma eand_eq_self_of_subset_right {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (B.val ⊆ A.val) →
  (A ∩ B) = B :=
begin
  intro A1,
  rw eand_comm,
  apply eand_eq_self_of_subset_left,
  exact A1,
end

lemma Pr_eand_le_left {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∩ B]≤ Pr[A] :=
begin
  apply event_prob_mono2,
  rw eand_val_def,
  apply set.inter_subset_left,
end

lemma Pr_eand_le_right {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∩ B]≤ Pr[B] :=
begin
  rw eand_comm,
  apply Pr_eand_le_left,
end

lemma Pr_eand_le_min {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∩ B]≤ min Pr[A]  Pr[B] :=
begin
  apply le_min,
  { apply Pr_eand_le_left,},
  { apply Pr_eand_le_right,}
end

/- The union of two events. -/
def measurable_union {Ω : Type*} [measurable_space Ω] (A B : event Ω) : event Ω :=
  {  val :=A.val ∪  B.val,
  property := measurable_set.union A.property B.property,}

@[simp]
lemma measurable_union_val_def {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (measurable_union A B).val=A.val ∪ B.val := rfl

@[simp]
lemma measurable_union_val_def2 {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (A ∪ B).val = A.val ∪ B.val := rfl

@[simp]
lemma eor_val_def {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∪ B).val = A.val ∪ B.val := by refl

/- The or of two events eor is commutative. -/
lemma eor_comm {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∪ B) = (B ∪ A) := is_commutative.comm A B

/- The probability of an event is less than the probability of eor of that event
with another event. -/
lemma Pr_le_eor_left {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A] ≤ Pr[A ∪ B] :=
begin
  apply event_prob_mono2,
  simp,
end

/- The probability of an event is less than the probability of eor of that event
with another event. -/
lemma Pr_le_eor_right {Ω : Type*} [probability_space Ω] (A B : event Ω) :
   Pr[B] ≤ Pr[A ∪ B] :=
begin
  rw eor_comm,
  apply Pr_le_eor_left,
end

lemma add_finite (a b : ennreal) : (a ≠ ⊤) → (b ≠ ⊤) → (a + b ≠ ⊤) :=by finish

/- The probability of the eor of two events is less than the sum of their probabilities. -/
lemma Pr_le_eor_sum {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∪ B]≤ Pr[A] + Pr[B] :=
begin
  have A1 : ↑(Pr[A ∪ B])≤ (Pr[A] : ennreal) + (Pr[B] : ennreal),
  { repeat {rw event_prob_def},
    simp,
    apply measure_theory.outer_measure.union,},
  have A2 : ↑(Pr[A ∪ B])≤ ((Pr[A] + Pr[B]) : ennreal) → Pr[A ∪ B]≤ Pr[A] + Pr[B],
  { apply to_nnreal_almost_monotonic,
  {   rw event_prob_def,
      apply prob_not_infinite,},
  {   apply add_finite,
      rw event_prob_def,
      apply prob_not_infinite,
      rw event_prob_def,
      apply prob_not_infinite,}},
  apply A2,
  apply A1,
end

/- The probability of disjoint events is their sum. -/
lemma Pr_disjoint_eor {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  disjoint A.val B.val → Pr[A ∪ B] = Pr[A] + Pr[B] :=
begin
  intro A1,
  have A2 : ↑(Pr[A ∪ B])= (Pr[A] : ennreal) + (Pr[B] : ennreal),
  { repeat {rw event_prob_def},
    simp,
    apply measure_theory.measure_union,
    apply A1,
    apply A.property,
    apply B.property,},
  have A3 : ((Pr[A ∪ B]) : ennreal).to_nnreal= ((Pr[A] : ennreal) + (Pr[B] : ennreal)).to_nnreal,
    rw A2,
  simp at A3,
  apply A3,
end

@[simp]
lemma enot_val_def {Ω : Type*} [probability_space Ω] (A : event Ω) :
  (Aᶜ).val = (A.val)ᶜ := by refl

/- Double negation elimination by the complement of the complement of an event. -/
@[simp]
lemma enot_enot_eq_self {Ω : Type*} [probability_space Ω] (A : event Ω) : Aᶜᶜ = (A) :=
begin
  apply event.eq,
  simp,
end

/- Set difference is defined for events. -/
@[simp]
lemma has_sdiff_event_val {α : Type*} [measurable_space α] (E F : event α) :
  (E \ F).val = E.val \ F.val := rfl

/- TODO is it possible to used the derived instance via has_compl -/
instance event_subtype_has_neg {α : Type*} [M : measurable_space α] : has_neg (subtype
  (@measurable_set α M)) := { neg := λ E, ⟨ E.valᶜ, measurable_set.compl E.property⟩,}

lemma event_neg_def {α : Type*} [M : measurable_space α] {E : event α} :
    Eᶜ = ⟨ E.valᶜ, measurable_set.compl E.property⟩ :=rfl

@[simp]
lemma event_compl_val_def {α : Type*} [M : measurable_space α] {E : event α} :
    (Eᶜ).val = (E.val)ᶜ :=rfl

@[simp]
lemma event_neg_val_def {α : Type*} [M : probability_space α] {E : event α} :
    (Eᶜ).val = (E.val)ᶜ := rfl

@[simp]
lemma em_event {Ω : Type*} [probability_space Ω] (A : event Ω) :
    (A ∪ Aᶜ) = event_univ _ :=
begin
  apply event.eq,
  simp,
end

/- The complement of the "or" is the "and" of the complements. -/
lemma compl_eor_eq_compl_eand_compl {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∪ B)ᶜ = (Aᶜ ∩ Bᶜ) := begin
  apply event.eq,
  simp,
end

/- The probability of an event and its complement is 1. -/
lemma Pr_add_enot_eq_1 {Ω : Type*} [probability_space Ω] (A : event Ω) :
  Pr[A] + Pr[Aᶜ] = 1 :=
begin
  have A1 : disjoint (A.val) (Aᶜ).val,
  { unfold disjoint,
    rw enot_val_def,
    simp,
     },
  have A2 : (A ∪ Aᶜ ) = event_univ _,
  { apply em_event,},
  have A3 : Pr[A ∪ Aᶜ] = Pr[event_univ _],
    rw A2,
  rw Pr_event_univ at A3,
  rw Pr_disjoint_eor at A3,
  apply A3,
  apply A1,
end

lemma nnreal_add_sub_right (a b c:nnreal):a + b = c → c - b = a :=
begin
  intro A1,
  have A2:(a + b) - b = a,
  { apply nnreal.add_sub_cancel,},
  rw A1 at A2,
  exact A2,
end

lemma nnreal_add_sub_left (a b c:nnreal) : a + b = c → c - a = b :=
begin
  intro A1,
  apply nnreal_add_sub_right,
  rw nnreal.comm_semiring.add_comm,
  exact A1,
end

lemma Pr_one_minus_eq_not {Ω:Type*} {p:probability_space Ω} (A:event Ω):
  1 - Pr[A] = Pr[Aᶜ] :=
begin
  have h:  Pr[A] + Pr[Aᶜ] = 1,
  begin
    apply Pr_add_enot_eq_1,
  end,
  apply nnreal_add_sub_left,
  exact h,
end

lemma Pr_one_minus_not_eq {Ω:Type*} {p:probability_space Ω} (A:event Ω):
  1 - Pr[Aᶜ] = Pr[A] :=
begin
  apply nnreal_add_sub_right,
  apply Pr_add_enot_eq_1,
end

lemma nnreal.le_sub_add {a b c:nnreal} : b ≤ c → c ≤ a →
  a ≤ a - b + c :=
begin
  repeat {rw ← nnreal.coe_le_coe},
  repeat {rw nnreal.coe_add},
  intros A1 A2,
  repeat {rw nnreal.coe_sub},
  linarith,
  apply le_trans A1 A2,
end

lemma nnreal_le_sub_add' {a b:nnreal} : a ≤ a - b + b :=
begin
  cases decidable.em (b ≤ a),
  { apply nnreal.le_sub_add,
    apply le_refl _,
    apply h },
  { have h2:a≤ b,
    { apply le_of_not_ge h }, rw nnreal.sub_eq_zero,
    rw zero_add,
    apply h2,
    apply h2 },
end

lemma Pr_not_ge_of_Pr_le {Ω:Type*} {p:probability_space Ω} (A:event Ω) (δ:nnreal):
  Pr[A] ≤ δ → Pr[Aᶜ] ≥ 1 - δ :=
begin
  intros h1,
  rw ← Pr_one_minus_eq_not,
  simp,
  have h2:1 - Pr[A] + Pr[A] ≤ 1 - Pr[A] + δ,
  { exact add_le_add_left h1 (1 - Pr[A]),},
  apply le_trans _ h2,
  apply nnreal_le_sub_add',
end

lemma em_event_cond {Ω:Type*} {p:probability_space Ω} (A B:event Ω): (A ∩ B ∪ A ∩ Bᶜ) = A :=
begin
  apply event.eq,
  simp [set.inter_union_compl],
end

lemma disjoint_inter_compl {α:Type*} (A B C:set α):disjoint (A ∩ B) (C∩ Bᶜ) :=
begin
  apply set.disjoint_of_subset_left (set.inter_subset_right A B),
  apply set.disjoint_of_subset_right (set.inter_subset_right C Bᶜ),
  simp [disjoint_iff],
end

lemma Pr_em {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
  Pr[A ∩ B] + Pr[A ∩ Bᶜ] = Pr[A] :=
begin
  rw ← Pr_disjoint_eor,
  rw em_event_cond,
  simp [disjoint_inter_compl],
end

lemma Pr_diff {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
    A.val ⊆ B.val →
    Pr[B ∩ Aᶜ] = Pr[B] - Pr[A] :=
begin
  intro A1,
  have A2:Pr[B ∩ A] + Pr[B ∩ Aᶜ] = Pr[B],
    apply Pr_em,
  have A3:(B ∩ A) = A,
    apply eand_eq_self_of_subset_right,
    apply A1,
  rw A3 at A2,
  symmetry,
  apply nnreal_add_sub_left,
  exact A2,
end

/- Define the equivalance of two events. -/
def event_eqv {Ω:Type*} {p:probability_space Ω} (A B:event Ω):event Ω := A ∩ B ∪ Aᶜ ∩ Bᶜ

infixr `=ₑ`:100 := event_eqv

lemma event_eqv_def {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
    (A =ₑ B) = ((A ∩ B) ∪ ((Aᶜ) ∩ (Bᶜ))) := rfl

lemma eor_partition {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
  (A ∪ B) = ((A ∩ Bᶜ) ∪ (A ∩ B) ∪ (Aᶜ ∩ B)) :=
begin
  apply event.eq,
  simp,
  ext ω,split;intros A1;simp at A1;simp [A1],
    cases A1 with A1 A1; simp [A1],
    rw or_comm,
    apply classical.em,
    apply classical.em,
    cases A1 with A1 A1,
      tauto,
    cases A1 with A1 A1,
    simp [A1],
end

lemma Pr_eor_partition {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
  Pr[A ∪ B] = Pr[A ∩ Bᶜ] + Pr[A ∩ B] + Pr[Aᶜ ∩ B] :=
begin
  rw eor_partition A B,
  rw Pr_disjoint_eor,
  rw Pr_disjoint_eor,
  simp,
  rw set.disjoint_left,
  intros ω A1,
  simp at A1,
  simp [A1],
  simp,
  split;
  {rw set.disjoint_left,
  intros ω A1,
  simp at A1,
  simp [A1]},
end

lemma Pr_eor_plus_eand {Ω:Type*}  {p:probability_space Ω} (A B:event Ω):
  Pr[A ∪ B] + Pr[A ∩ B] = Pr[A] + Pr[B] :=
begin
  rw ← Pr_em A B,
  rw ← Pr_em B A,
  rw eand_comm B A,
  rw eand_comm B (Aᶜ),
  rw Pr_eor_partition A B,
  ring,
end

lemma Pr_eor_eq_minus_eand {Ω:Type*}  {p:probability_space Ω} (A B:event Ω):
  Pr[A ∪ B] = Pr[A] + Pr[B] - Pr[A ∩ B] :=
begin
  rw ← Pr_eor_plus_eand,
  rw nnreal.add_sub_cancel,
end

lemma Pr_eor_eq_minus_eand_real {Ω:Type*}  {p:probability_space Ω} (A B:event Ω):
  (Pr[A ∪ B]:real) = (Pr[A]:real) + (Pr[B]:real) - (Pr[A ∩ B]:real) :=
begin
  have A1:Pr[A ∪ B] + Pr[A ∩ B] = (Pr[A] + Pr[B]),
  {apply Pr_eor_plus_eand},
  rw ← nnreal.coe_eq at A1,
  repeat {rw nnreal.coe_add at A1},
  linarith,
end

def eall_encodable {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):event Ω :=
  { val:=(⋂ b:β, (A b).val),
  property := measurable_set.Inter (λ b:β, (A b).property),}

/- The definition of has_eall.eall_val enforces that the eall function implements intersection.
The proof of measurability is left to the implementer. -/
@[class]
structure has_eall (Ω β:Type*) (p:probability_space Ω) :=
  (eall:(β → event Ω) → event Ω)
  (eall_val:∀ (f:β → event Ω), (⋂ (b:β), (f b).val) = (eall f).val)

@[class]
structure has_eall_in (Ω β γ:Type*) (p:probability_space Ω) :=
  (eall_in:γ → (β → event Ω) → event Ω)
  (as_set:γ → (set β))
  (eall_in_val:∀ (g:γ) (f:β → event Ω), (⋂ b ∈ (as_set g), (f b).val) = (eall_in g f).val)

notation `∀ᵣ` binders ` in ` A, r:(scoped f, has_eall_in.eall_in A f) := r

instance has_eall_encodable {Ω β:Type*} {p:probability_space Ω} [encodable β]:has_eall Ω β p :=
  { eall := λ (A:β → event Ω), eall_encodable A,
  eall_val := begin
    simp [eall_encodable],
  end,}

notation `∀ᵣ` binders `, ` r:(scoped f, has_eall.eall f) := r

@[simp]
lemma eall_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):
  (eall_encodable A).val = (⋂ b:β, (A b).val) := rfl

lemma eall_binder_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):
  (∀ᵣ x, A x) = (eall_encodable A):= rfl

@[simp]
lemma eall_binder_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):
  (∀ᵣ x, A x).val = (⋂ b:β, (A b).val) := rfl

def to_set_of_sets {Ω:Type*} {p:probability_space Ω} (A:set (event Ω)):set (set Ω) :=
  (set.image (λ a:event Ω, a.val) A)

lemma all_measurable_to_set_of_sets {Ω:Type*} {p:probability_space Ω} (A:set (event Ω))
  (a∈ (to_set_of_sets A)):measurable_set a :=
begin
  unfold to_set_of_sets at H,
  simp at H,
  cases H with x H,
  cases H with A1 A2,
  subst a,
  exact x.property,
end

lemma countable_to_set_of_sets {Ω:Type*} {p:probability_space Ω} {A:set (event Ω)}:
  (set.countable A)→ (set.countable (to_set_of_sets A)) :=
begin
  unfold to_set_of_sets,
  intro A1,
  apply set.countable.image,
  apply A1,
end

def eall_set {Ω:Type*} {p:probability_space Ω} (A:set (event Ω)) (cA:set.countable A):event Ω:=
{ val:=set.sInter (to_set_of_sets A),
  property:=measurable_set.sInter (countable_to_set_of_sets cA) (all_measurable_to_set_of_sets A),}

def eall_finset_val {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event Ω):set Ω :=  ⋂ s∈ S, (A s).val

lemma eall_finset_val_measurable {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event Ω):measurable_set (eall_finset_val S A) :=
begin
  unfold eall_finset_val,
  apply finset.measurable_set_bInter,
  intros,
  apply (A b).property,
end

def eall_finset {Ω β:Type*} {p:probability_space Ω}
  (S:finset β)
  (A:β → event Ω):event Ω :=
  { val:=eall_finset_val S A,
    property:=eall_finset_val_measurable S A,}

instance has_eall_in.finset {Ω β:Type*} {p:probability_space Ω}:has_eall_in Ω β (finset β) p :=
{ eall_in := (λ S f, eall_finset S f),
  as_set := (λ (S:finset β), ↑S),
  eall_in_val := begin
    simp [eall_finset, eall_finset_val],
  end}

@[simp]
lemma eall_finset_val_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event Ω):(eall_finset S A).val = ⋂ s∈ S, (A s).val := rfl

lemma has_eall_in_finset_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event Ω):
  (∀ᵣ s in S, A s) = (eall_finset S A) := rfl

@[simp]
lemma has_eall_in_finset_val_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event Ω):
  (∀ᵣ s in S, A s).val = ⋂ s∈ S, (A s).val := rfl

@[simp]
lemma has_eall_in_finset_val_def2 {Ω β:Type*} {p:probability_space Ω} {S:finset β} {A:β → event Ω}:
  (has_eall_in.eall_in S A).val = ⋂ s∈ S, (A s).val := rfl

@[simp]
lemma has_eall_in_finset_val_def3 {Ω β:Type*} {p:probability_space Ω} {S:finset β} {A:β → event Ω}:
  @has_coe.coe (event Ω) (set Ω) (coe_subtype) (has_eall_in.eall_in S A) = ⋂ s∈ S, (A s).val := rfl

lemma has_eall_in_insert {Ω β:Type*} {p:probability_space Ω} [decidable_eq β] {T:finset β}
  {b:β} {E:β → event Ω}:
  (∀ᵣ b' in (insert b T), E b') = ((E b) ∩ (∀ᵣ b' in T, E b')) :=
begin
  apply event.eq,
  simp,
end

def eall_fintype {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event Ω):event Ω := eall_finset finset.univ A

instance has_eall.fintype {Ω β:Type*} {p:probability_space Ω} [F:fintype β]:has_eall Ω β p :=
{ eall := (λ A, eall_fintype F A),
  eall_val := by simp [eall_fintype],}

lemma eall_fintype_eq_eall_finset {Ω β:Type*} {p:probability_space Ω}
  [F:fintype β] (A:β → event Ω):(∀ᵣ b, A b) = eall_finset finset.univ A := rfl

lemma eall_fintype_def {Ω β:Type*} {p:probability_space Ω} (F:fintype β) {A:β → event Ω}:
  (eall_fintype F A) = (∀ᵣ b, A b) := rfl

@[simp]
lemma eall_fintype_val_def {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event Ω):(eall_fintype F A).val = ⋂ (s:β), (A s).val :=
begin
  unfold eall_fintype,
  simp,
end

end probability_theory
