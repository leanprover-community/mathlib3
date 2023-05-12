/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice
import data.fintype.card

/-!
# Birkhoff's representation theorem
-/

section
variables {α : Type*} [preorder α] [finite α]

@[priority 100] -- See note [lower instance priority]
instance finite.to_well_founded_lt : well_founded_lt α := ⟨finite.preorder.well_founded_lt⟩
@[priority 100] -- See note [lower instance priority]
instance finite.to_well_founded_gt : well_founded_gt α := ⟨finite.preorder.well_founded_gt⟩

end

open finset order_dual

variables {ι α : Type*}

/-! ### Irreducible and prime elements -/

section semilattice_sup
variables [semilattice_sup α] {a : α}

/-- A sup-irreducible element is a non-bottom element which isn't the supremum of anything smaller.
-/
def sup_irred (a : α) : Prop := ¬ is_min a ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
def sup_prime (a : α) : Prop := ¬ is_min a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

lemma sup_irred.not_is_min (ha : sup_irred a) : ¬ is_min a := ha.1
lemma sup_prime.not_is_min (ha : sup_prime a) : ¬ is_min a := ha.1
lemma is_min.not_sup_irred (ha : is_min a) : ¬ sup_irred a := λ h, h.1 ha
lemma is_min.not_sup_prime (ha : is_min a) : ¬ sup_prime a := λ h, h.1 ha

@[simp] lemma not_sup_irred : ¬ sup_irred a ↔ is_min a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a :=
begin
  rw [sup_irred, not_and_distrib],
  push_neg,
  rw exists₂_congr,
  simp [@eq_comm _ _ a] { contextual := tt },
end

@[simp] lemma not_sup_prime : ¬ sup_prime a ↔ is_min a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬ a ≤ b ∧ ¬ a ≤ c :=
by { rw [sup_prime, not_and_distrib], push_neg, refl }

protected lemma sup_prime.sup_irred : sup_prime a → sup_irred a :=
and.imp_right $ λ h b c ha, by simpa [←ha] using h ha.ge

variables [order_bot α] {s : finset ι} {f : ι → α}

@[simp] lemma not_sup_irred_bot : ¬ sup_irred (⊥ : α) := is_min_bot.not_sup_irred
@[simp] lemma not_sup_prime_bot : ¬ sup_prime (⊥ : α) := is_min_bot.not_sup_prime

lemma sup_irred.ne_bot (ha : sup_irred a) : a ≠ ⊥ := by { rintro rfl, exact not_sup_irred_bot ha }
lemma sup_prime.ne_bot (ha : sup_prime a) : a ≠ ⊥ := by { rintro rfl, exact not_sup_prime_bot ha }

lemma sup_irred.finset_sup (ha : sup_irred a) (h : s.sup f = a) : ∃ i ∈ s, f i = a :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simpa [ha.ne_bot] using h.symm },
  simp only [exists_prop, exists_mem_insert] at ⊢ ih,
  rw sup_insert at h,
  exact (ha.2 h).imp_right ih,
end

lemma sup_prime.finset_sup (ha : sup_prime a) (h : a ≤ s.sup f) : ∃ i ∈ s, a ≤ f i :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simpa [ha.ne_bot] using h },
  simp only [exists_prop, exists_mem_insert] at ⊢ ih,
  rw sup_insert at h,
  exact (ha.2 h).imp_right ih,
end

variables [well_founded_lt α]

/-- In a well-founded lattice, any element is the supremum of finitely many sup-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/
lemma exists_sup_irred_decomposition (a : α) :
  ∃ s : finset α, s.sup id = a ∧ ∀ ⦃b⦄, b ∈ s → sup_irred b :=
begin
  classical,
  apply well_founded_lt.induction a _,
  clear a,
  rintro a ih,
  by_cases ha : sup_irred a,
  { exact ⟨{a}, by simp [ha]⟩ },
  rw not_sup_irred at ha,
  obtain ha | ⟨b, c, rfl, hb, hc⟩ := ha,
  { exact ⟨∅, by simp [ha.eq_bot]⟩ },
  obtain ⟨s, rfl, hs⟩ := ih _ hb,
  obtain ⟨t, rfl, ht⟩ := ih _ hc,
  exact ⟨s ∪ t, sup_union, forall_mem_union.2 ⟨hs, ht⟩⟩,
end

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α] {a : α}

/-- An inf-irreducible element is a non-top element which isn't the infimum of anything bigger. -/
def inf_irred (a : α) : Prop := ¬ is_max a ∧ ∀ ⦃b c⦄, b ⊓ c = a → b = a ∨ c = a

/-- An inf-prime element is a non-top element which isn't bigger than the infimum of anything
bigger. -/
def inf_prime (a : α) : Prop := ¬ is_max a ∧ ∀ ⦃b c⦄, b ⊓ c ≤ a → b ≤ a ∨ c ≤ a

@[simp] lemma is_max.not_inf_irred (ha : is_max a) : ¬ inf_irred a := λ h, h.1 ha
@[simp] lemma is_max.not_inf_prime (ha : is_max a) : ¬ inf_prime a := λ h, h.1 ha

@[simp] lemma not_inf_irred : ¬ inf_irred a ↔ is_max a ∨ ∃ b c, b ⊓ c = a ∧ a < b ∧ a < c :=
@not_sup_irred αᵒᵈ _ _

@[simp] lemma not_inf_prime : ¬ inf_prime a ↔ is_max a ∨ ∃ b c, b ⊓ c ≤ a ∧ ¬ b ≤ a ∧ ¬ c ≤ a :=
@not_sup_prime αᵒᵈ _ _

protected lemma inf_prime.inf_irred : inf_prime a → inf_irred a :=
and.imp_right $ λ h b c ha, by simpa [←ha] using h ha.le

variables [order_top α] {s : finset ι} {f : ι → α}

@[simp] lemma not_inf_irred_top : ¬ inf_irred (⊤ : α) := is_max_top.not_inf_irred
@[simp] lemma not_inf_prime_top : ¬ inf_prime (⊤ : α) := is_max_top.not_inf_prime

lemma inf_irred.ne_top (ha : inf_irred a) : a ≠ ⊤ := by { rintro rfl, exact not_inf_irred_top ha }
lemma inf_prime.ne_top (ha : inf_prime a) : a ≠ ⊤ := by { rintro rfl, exact not_inf_prime_top ha }

lemma inf_irred.finset_inf : inf_irred a → s.inf f = a → ∃ i ∈ s, f i = a :=
@sup_irred.finset_sup _ αᵒᵈ _ _ _ _ _

lemma inf_prime.finset_inf : inf_prime a → s.inf f ≤ a → ∃ i ∈ s, f i ≤ a :=
@sup_prime.finset_sup _ αᵒᵈ _ _ _ _ _

variables [well_founded_gt α]

/-- In a cowell-founded lattice, any element is the infimum of finitely many inf-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/
lemma exists_inf_irred_decomposition (a : α) :
  ∃ s : finset α, s.inf id = a ∧ ∀ ⦃b⦄, b ∈ s → inf_irred b :=
@exists_sup_irred_decomposition αᵒᵈ _ _ _ _

end semilattice_inf

section distrib_lattice
variables [distrib_lattice α] {a b c : α}

@[simp] lemma sup_prime_iff_sup_irred : sup_prime a ↔ sup_irred a :=
⟨sup_prime.sup_irred, and.imp_right $ λ h b c,
  by { simp_rw [←inf_eq_left, inf_sup_left], exact @h _ _ }⟩

@[simp] lemma inf_prime_iff_inf_irred : inf_prime a ↔ inf_irred a :=
⟨inf_prime.inf_irred, and.imp_right $ λ h b c,
  by { simp_rw [←sup_eq_left, sup_inf_left], exact @h _ _ }⟩

alias sup_prime_iff_sup_irred ↔ _ sup_irred.sup_prime
alias inf_prime_iff_inf_irred ↔ _ inf_irred.inf_prime

attribute [protected] sup_irred.sup_prime inf_irred.inf_prime

end distrib_lattice

section linear_order
variables [linear_order α] {a : α}

@[simp] protected lemma sup_prime_iff_not_is_min : sup_prime a ↔ ¬ is_min a :=
and_iff_left $ by simp

@[simp] protected lemma sup_irred_iff_not_is_min : sup_irred a ↔ ¬ is_min a :=
and_iff_left $ λ _ _, by simpa only [sup_eq_max, max_eq_iff] using or.imp and.left and.left

@[simp] protected lemma inf_prime_iff_not_is_max : inf_prime a ↔ ¬ is_max a :=
and_iff_left $ by simp

@[simp] protected lemma inf_irred_iff_not_is_max : inf_irred a ↔ ¬ is_max a :=
and_iff_left $ λ _ _, by simpa only [inf_eq_min, min_eq_iff] using or.imp and.left and.left

end linear_order
