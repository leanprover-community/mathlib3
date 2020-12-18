/-
Copyright (c) 2020 Chris A. Upshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris A. Upshaw.

Type class hierarchy for Heyting algebras.
-/
import

import order.bounded_lattice

set_option old_structure_cmd true

/-- Set / lattice complement -/
class has_compl (α : Type*) := (compl : α → α)

export has_compl (compl)

postfix `ᶜ`:(max+1) := compl

universes u v
variables {α : Type u} {w x y z : α}

class has_internal_imp (α : Type*) :=
  (imp : α → α → α)

infixr ` ⟶ `:60 := has_internal_imp.imp

/-- A heyting algebra is a bounded distributive lattice with a
  internal implication right adjoint to the meet. Equivently it is a
  bounded distributive lattice with a psudo-complement `ᶜ` such that
  `x ⊓ xᶜ = ⊥`, but not nessarily `x ⊔ xᶜ = ⊤`.
  This is a generalization of the logic of propositions, or
  the powerset lattice.-/
class heyting_algebra α extends bounded_distrib_lattice α, has_compl α, has_internal_imp α :=
  (imp_adjoint : ∀ a b c : α, a ⊓ b ≤ c ↔ a ≤ b ⟶ c)
  (compl_from_imp : ∀ a : α, aᶜ = (a ⟶ ⊥))

export heyting_algebra (imp_adjoint compl_from_imp)

section heyting_algebra
variables [heyting_algebra α]

@[simp] lemma imp_refl : x ⟶ x = ⊤ :=
  begin
    rw le_antisymm_iff,
    split,
      {exact le_top},
      {
        rw ← imp_adjoint,
        exact inf_le_right
      },
  end

lemma imp_mp : x ⊓ (x ⟶ y) ≤ y :=
  begin
    rw inf_comm,
    rw imp_adjoint,
    reflexivity,
  end

lemma le_imp : x ≤ (y ⟶ x) :=
  begin
    rw ← imp_adjoint,
    exact inf_le_left,
  end

@[simp]
lemma imp_mp_simp : x ⊓ (x ⟶ y) = x ⊓ y :=
  le_antisymm (le_inf inf_le_left imp_mp) (inf_le_inf (le_refl x) le_imp)

lemma imp_app : (x ⟶ y) ⊓ x ≤ y :=
  begin
    rw inf_comm,
    exact imp_mp
  end

@[simp]
lemma imp_app_simp : (x ⟶ y) ⊓ x = y ⊓ x:=
  le_antisymm (le_inf imp_app inf_le_right) (inf_le_inf le_imp rfl.ge)

@[simp]
lemma inf_compl_eq_bot : x ⊓ xᶜ = ⊥ :=
  begin
    rw compl_from_imp,
    exact imp_mp_simp.trans inf_bot_eq,
  end

@[simp] theorem compl_inf_eq_bot : xᶜ ⊓ x = ⊥ :=
  eq.trans inf_comm inf_compl_eq_bot

-- if x has a boolean complement it is unique
theorem compl_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : xᶜ = y :=
  begin
    rw compl_from_imp,
    apply le_antisymm,
    {
      transitivity (⊤ ⊓ (x ⟶ ⊥)),
      have h : (x ⟶ ⊥) = ⊤ ⊓ (x ⟶ ⊥):= top_inf_eq.symm,
      rw ← h,
      reflexivity,
      rw ← s,
      rw inf_sup_right,
      apply sup_le,
      transitivity ⊥,
      apply imp_mp,
      exact bot_le,
      apply inf_le_left,
    },

    {
      rw ← imp_adjoint,
      rw inf_comm,
      rw i,
    }

  end
end heyting_algebra

instance has_internal_imp_prop : has_internal_imp Prop := ⟨λ x y, x → y⟩

lemma imp_adjoint_prop (a b c : Prop) : (a ⊓ b ≤ c) ↔ (a ≤ b ⟶ c) :=
  begin
    unfold has_internal_imp.imp,
    simp,
    split; intros iff_hyp hyp; try {intro hyp_b}; apply iff_hyp;
      try {cases hyp}; try {split}; assumption
  end

instance heyting_algebra_prop : heyting_algebra Prop :=
  {
    compl := not,
    imp_adjoint := imp_adjoint_prop,
    compl_from_imp := λ a, rfl,
    ..has_internal_imp_prop,
    ..bounded_distrib_lattice_Prop
  }

instance pi.heyting_algebra {α : Type u} {β : Type v} [heyting_algebra β] :
  heyting_algebra (α → β) :=
  begin
    pi_instance,
    intros,
    simp only [],
    transitivity ∀ i, (a i) ⊓ (b i) ≤ c i,
    {
      have inf_unfolded : ∀ i : α, (a ⊓ b) i = a i ⊓ b i := λ i, begin simp end,
      split; intros hyp i;
        try { rw inf_unfolded i}; try {rw ← inf_unfolded i};
        exact hyp i,
    },
    symmetry,
    transitivity (∀ i : α, a i ≤ heyting_algebra.imp (b i) (c i)),
    {
      have h : ∀ x : α → β, a ≤ x ↔ ∀ i, a i ≤ x i,
        {
          unfold_projs,
          intros, split; intros a_le_x; apply a_le_x,
        },
      rw h,
    },
    have h : ∀ p q : α → Prop, (∀ i, p i ↔ q i) → ((∀ i, p i) ↔ (∀ i, q i))
      := λ p q hyp, begin finish end,
    rw h, clear h,
    intros,
    symmetry,
    apply heyting_algebra.imp_adjoint,
  end
