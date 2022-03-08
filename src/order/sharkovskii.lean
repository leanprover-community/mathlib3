/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.equiv.transfer_instance
import data.nat.basic
import data.sum.order
import number_theory.padics.padic_norm
import order.lexicographic

/-!
# The Sharkovskii ordering of natural numbers
-/

open nat order_dual submonoid sum

section mathlib
variables {α β : Type*}

lemma padic_val_nat_pow_self {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : padic_val_nat p (p ^ n) = n :=
begin
  sorry,
end

lemma nat.mem_powers_iff {a n : ℕ}  (hn : n ≠ 0) : a ∈ powers n ↔ n ^ padic_val_nat n a = a :=
begin
  refine ⟨_, λ h, ⟨_, h⟩⟩,
  rintro ⟨m, rfl⟩,
  obtain _ | _ | n := n,
  { exact (hn rfl).elim },
  { simp_rw one_pow },
  { rw padic_val_nat_pow_self le_add_self }
end

instance powers.decidable_mem_nat : ∀ n, decidable_pred (∈ powers n)
| 0 := λ x, decidable_of_iff (x = 0 ∨ x = 1) begin
  split,
  { rintro (rfl | rfl),
    { exact ⟨1, zero_pow zero_lt_one⟩ },
    { exact ⟨0, pow_zero _⟩ } },
  { rintro ⟨_ | n, rfl⟩; simp }
end
| m@(n + 1) := λ x,
  decidable_of_iff' (m ^ padic_val_nat m x = x) (nat.mem_powers_iff n.succ_ne_zero)

lemma to_lex_mono [partial_order α] [preorder β] : monotone (@to_lex (α × β)) :=
begin
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
  obtain rfl | ha := eq_or_ne a₁ a₂,
  refine prod.lex.right _ _,
  sorry,
  exact prod.lex.left _ _ (h.1.lt_of_ne ha),
end

lemma to_lex_strict_mono [partial_order α] [partial_order β] : strict_mono (@to_lex (α × β)) :=
begin
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
  obtain rfl | ha := eq_or_ne a₁ a₂,
  refine prod.lex.right _ _,
  sorry,
  exact prod.lex.left _ _ (h.le.1.lt_of_ne ha),
end

instance lex.inhabited [inhabited α] : inhabited (lex α) := ⟨to_lex default⟩
instance lex.nontrivial [nontrivial α] : nontrivial (lex α) := of_lex.nontrivial
-- instance lex.infinite [infinite α] : infinite (lex α) := of_lex.infinite

instance prod.lex.order_bot [partial_order α] [preorder β] [order_bot α] [order_bot β] :
  order_bot (α ×ₗ β) :=
⟨to_lex (⊥, ⊥), λ ⟨a, b⟩, to_lex_mono bot_le⟩

instance prod.lex.order_top [partial_order α] [preorder β] [order_top α] [order_top β] :
  order_top (α ×ₗ β) :=
⟨to_lex (⊤, ⊤), λ ⟨a, b⟩, to_lex_mono le_top⟩

instance prod.lex.bounded_order [partial_order α] [preorder β] [bounded_order α] [bounded_order β] :
  bounded_order (α ×ₗ β) :=
{ ..prod.lex.order_bot, ..prod.lex.order_top }

end mathlib

/-- The Sharkovskii ordering of the natural numbers.-/
@[derive [inhabited, linear_order, bounded_order]]
def sharkovskii := ℕ ×ₗ ℕ ⊕ₗ order_dual ℕ

attribute [pattern] to_dual
namespace sharkovskii

/-- Turn a natural with the Sharkovskii ordering into the corresponding natural. -/
@[simp] def to_nat : sharkovskii → ℕ
| (inlₗ ab) := 2 ^ (of_lex ab).1 * (2 * (of_lex ab).2 + 3)
| (inrₗ (to_dual 0)) := 0
| (inrₗ (to_dual $ succ n)) := 2^n

@[simp] lemma to_nat_bot : to_nat ⊥ = 3 := rfl
@[simp] lemma to_nat_top : to_nat ⊤ = 0 := rfl

/-- Turn a natural into the corresponding natural with the Sharkovskii ordering. -/
@[simp] def of_nat : ℕ → sharkovskii
| 0 := inrₗ (to_dual 0)
| m@(n + 1) := if m ∈ powers 2
  then inrₗ $ to_dual $ padic_val_nat 2 m + 1
  else inlₗ (padic_val_nat 2 m, m / 2 ^ padic_val_nat 2 m)

lemma of_nat_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
  of_nat n = if n ∈ powers 2
    then inrₗ $ to_dual (padic_val_nat 2 n) + 1
    else inlₗ (padic_val_nat 2 n, n / 2 ^ padic_val_nat 2 n) :=
begin
  cases n,
  { exact (hn rfl).elim },
  { refl }
end

lemma of_nat_of_mem_powers {n : ℕ} (hn : n ∈ powers 2) :
  of_nat n = inrₗ (to_dual $ padic_val_nat 2 n + 1) :=
begin
  cases n,
  { sorry },
  { exact if_pos hn }
end

@[simp] lemma of_nat_two_pow (n : ℕ) : of_nat (2 ^ n) = inrₗ (to_dual $ n + 1) :=
begin
  refine (of_nat_of_mem_powers _).trans _,
  sorry,
  rw padic_val_nat.prime_pow,
end

@[simp] lemma of_nat_to_nat : ∀ n : sharkovskii, of_nat n.to_nat = n
| (inlₗ ab) := begin
  simp only [to_nat],
  sorry,
end
| (inrₗ $ to_dual 0) := rfl
| (inrₗ $ to_dual $ succ n) := by rw [to_nat, of_nat_two_pow]

@[simp] lemma to_nat_of_nat : ∀ n, (of_nat n).to_nat = n
| 0 := rfl
| (succ n) := begin
    unfold of_nat,
    split_ifs,
    { exact (nat.mem_powers_iff two_ne_zero).1 h },
    change _ * _ = _,
    sorry
  end

/-- The equivalence between the naturals with the Sharkovskii ordering and the naturals. -/
@[simps] def equiv_nat : sharkovskii ≃ ℕ :=
{ to_fun := to_nat,
  inv_fun := of_nat,
  left_inv := of_nat_to_nat,
  right_inv := to_nat_of_nat }

lemma double_order_left' :
  ∀ {a b : sharkovskii}, a < b → of_nat (2 * a.to_nat) < of_nat (2 * b.to_nat)
| (inlₗ a) (inlₗ b) h :=
  begin
    have := lex.inl_lt_inl_iff.1 h,
  end
| (inlₗ ⟨_, _⟩) (inrₗ _) _ := _
| (inrₗ _) (inrₗ _) _ := _

end sharkovskii
