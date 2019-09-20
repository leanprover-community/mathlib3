/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Minchao Wu
-/

import computability.halting 

/-!
# Strong reducibility and degrees.
This file defines the many-one reduction and one-one reduction on set ℕ.
## Notations
This file uses the local notation `⊕` for `disjoin`.
## Implementation notes

## References

## Tags
computability, reducibility, reduction
-/
open function

def many_one_reducible {α} [primcodable α] (p q : α → Prop) := 
∃ f, computable f ∧ ∀ a, p a ↔ q (f a)

infix ` ≤₀ `:1000 := many_one_reducible

def one_one_reducible {α} [primcodable α] (p q : α → Prop) := 
∃ f, computable f ∧ injective f ∧ ∀ a, p a ↔ q (f a)

infix ` ≤₁ `:1000 := one_one_reducible

theorem reflexive_many_one_reducible {α} [primcodable α] : reflexive (@many_one_reducible α _) := 
λ p, ⟨id, computable.id, by simp⟩

theorem transitive_many_one_reducible {α} [primcodable α] : transitive (@many_one_reducible α _) := 
λ p q r ⟨f, c₁, h₁⟩ ⟨g, c₂, h₂⟩, 
⟨g ∘ f, computable.comp c₂ c₁, λ a, 
  ⟨λ h, by { rwa [←h₂, ←h₁] }, 
   λ h, by { rwa [h₁, h₂] }⟩⟩

theorem reflexive_one_one_reducible {α} [primcodable α] : reflexive (@one_one_reducible α _) := 
λ p, ⟨id, computable.id, injective_id, by simp⟩

theorem transitive_one_one_reducible {α} [primcodable α] : transitive (@one_one_reducible α _) := 
λ p q r ⟨f, c₁, i₁, h₁⟩ ⟨g, c₂, i₂, h₂⟩, 
⟨g ∘ f, computable.comp c₂ c₁, injective_comp i₂ i₁, λ a,
  ⟨λ h, by { rwa [←h₂, ←h₁] }, 
   λ h, by { rwa [h₁, h₂] }⟩⟩

namespace computable_pred
variables {α : Type*} {σ : Type*}
variables [primcodable α] [primcodable σ]
open computable

theorem computable_of_many_one_reducible
  {p q : α → Prop} 
  (h₁ : p ≤₀ q) (h₂ : computable_pred q) : computable_pred p := 
  begin
    rcases h₁ with ⟨f, c, hf⟩,
    rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩, split, 
    { apply computable.of_eq (cond (comp hg c) (const tt) (const ff)),
      intro, cases heq : g (f n), repeat { simp [hf, heq] },
      { intro, cases heq : g (f a), 
        { left, simp [hf, heq] },
        { right, simp [hf, heq] } } }
  end

theorem computable_of_one_one_reducible
  {p q : α → Prop} 
  (h₁ : p ≤₁ q) (h₂ : computable_pred q) : computable_pred p := 
  by { rcases h₁ with ⟨f, c, hinj, hf⟩, apply computable_of_many_one_reducible ⟨f, c, hf⟩ h₂ }

end computable_pred

def many_one_equiv {α} [primcodable α] (p q : α → Prop) := p ≤₀ q ∧ q ≤₀ p

def one_one_equiv {α} [primcodable α] (p q : α → Prop) := p ≤₁ q ∧ q ≤₁ p

theorem equivalence_of_many_one_equiv {α} [primcodable α] : equivalence (@many_one_equiv α _) :=
⟨λ x,⟨reflexive_many_one_reducible _, reflexive_many_one_reducible _⟩,  
 λ x y h, ⟨h.2, h.1⟩, 
 λ x y z h₁ h₂, ⟨transitive_many_one_reducible h₁.1 h₂.1, transitive_many_one_reducible h₂.2 h₁.2⟩⟩

theorem equivalence_of_one_one_equiv {α} [primcodable α] : equivalence (@one_one_equiv α _) :=
⟨λ x,⟨reflexive_one_one_reducible _, reflexive_one_one_reducible _⟩,  
 λ x y h, ⟨h.2, h.1⟩, 
 λ x y z h₁ h₂, ⟨transitive_one_one_reducible h₁.1 h₂.1, transitive_one_one_reducible h₂.2 h₁.2⟩⟩

def many_one_equiv_setoid {α} [primcodable α] : setoid (set α) := 
⟨many_one_equiv, @equivalence_of_many_one_equiv α _⟩

local attribute [instance] many_one_equiv_setoid

def many_one_degree {α} [primcodable α] := quotient (@many_one_equiv_setoid α _)

def disjoin (p q : set ℕ) : set ℕ  := (λ x, 2 * x) '' p ∪ (λ x, 2 * x + 1) '' q

local infix ` ⊕ `:1001 := disjoin

theorem mem_disjoin_left {p q : set ℕ} {n : ℕ} (h₁ : ¬nat.bodd n) (h₂ : (p ⊕ q) n) : p (nat.div2 n) :=
begin
  cases h₂,
  { rcases h₂ with ⟨w, hl, hr⟩, rw ←hr, dsimp, rw ←nat.bit0_val, simpa [nat.div2_bit0] using hl },
  { rcases h₂ with ⟨w, hl, hr⟩, rw ←hr at h₁, simp at h₁, contradiction }
end

theorem mem_disjoin_right {p q : set ℕ} {n : ℕ} (h₁ : nat.bodd n) (h₂ : (p ⊕ q) n) : q (nat.div2 n) :=
begin
  cases h₂,
  { rcases h₂ with ⟨w, hl, hr⟩, rw ←hr at h₁, simp at h₁, contradiction },
  { rcases h₂ with ⟨w, hl, hr⟩, rw ←hr, dsimp, rw ←nat.bit1_val, simpa [nat.div2_bit1] using hl }
end

namespace nat.primrec

lemma add1 : primrec (nat.unpaired (λ x y, nat.succ y)) :=
by simp [primrec₂.unpaired, primrec.comp₂ primrec.succ primrec₂.right]

lemma double : primrec (λ n, 2 * n) :=
begin
  rw primrec.nat_iff, 
  apply nat.primrec.of_eq (prec1 0 add1),
  intro n, induction n with k ih, 
  { simp }, 
  { simpa [*, nat.mul_succ, nat.add_succ] using ih }
end

lemma double_succ : primrec (λ n, 2 * n + 1) :=
begin
  rw primrec.nat_iff, 
  apply nat.primrec.of_eq (prec1 1 add1),
  intro n, induction n with k ih,
  { simp },
  { simpa [*, nat.mul_succ, nat.add_succ] using ih }
end

end nat.primrec

open nat.primrec

theorem many_one_reducible_of_disjoin_left {p q r : ℕ → Prop} : 
  p ≤₀ q → p ≤₀ q ⊕ r := λ ⟨f, hc, hf⟩, 
⟨λ x, 2 * f x, by { exact computable.comp (primrec.to_comp double) hc }, 
 λ a, ⟨λ h, by { left, use f a, exact ⟨(hf a).1 h, by simp⟩ },
       λ h, begin 
              cases h, 
              { rcases h with ⟨b, hbl, hbr⟩, 
                rw [hf, ← nat.eq_of_mul_eq_mul_left _ hbr], 
                exact hbl, exact dec_trivial }, 
              { rcases h with ⟨b, hbl, hbr⟩, exfalso, apply nat.two_mul_ne_two_mul_add_one hbr.symm } 
            end⟩⟩

theorem many_one_reducible_of_disjoin_right {p q r : ℕ → Prop} : 
  p ≤₀ r → p ≤₀ q ⊕ r := λ ⟨f, hc, hf⟩,  
⟨λ a, (2 * f a + 1), by { exact computable.comp (primrec.to_comp double_succ) hc },
 λ a, ⟨λ h, by { right, use f a, exact ⟨(hf a).1 h, by simp⟩ },
       λ h, begin 
              cases h, 
              { rcases h with ⟨b, hbl, hbr⟩, exfalso, apply nat.two_mul_ne_two_mul_add_one hbr }, 
              { rcases h with ⟨b, hbl, hbr⟩,
                simp only [add_left_inj, add_comm] at hbr,
                rw [hf, ←nat.eq_of_mul_eq_mul_left _ hbr], 
                exact hbl, exact dec_trivial } 
            end⟩⟩

theorem disjoin_many_one_reducible {p q r : ℕ → Prop} (h₁ : p ≤₀ r) (h₂ : q ≤₀ r) : p ⊕ q ≤₀ r :=
begin
  rcases h₁ with ⟨f₁, hl₁, hr₁⟩,
  rcases h₂ with ⟨f₂, hl₂, hr₂⟩,
  use (λ x, cond (nat.bodd x) (f₂ (nat.div2 x)) (f₁ (nat.div2 x))), constructor, 
  { exact computable.cond (primrec.to_comp primrec.nat_bodd) 
          (computable.comp hl₂ (primrec.to_comp (primrec.comp primrec.nat_div2 primrec.id))) 
          (computable.comp hl₁ (primrec.to_comp (primrec.comp primrec.nat_div2 primrec.id))) },
  { intro a, constructor, 
   { intro h, cases heq : nat.bodd a, 
     { dsimp, rw ←hr₁, apply mem_disjoin_left _ h, simp [heq] },
     { dsimp, rw ←hr₂, apply mem_disjoin_right heq h } },
   { intro h, cases heq : nat.bodd a,
     { simp [heq] at h, left, rw ←hr₁ at h, 
       use nat.div2 a, split, exact h,
       simpa [heq] using nat.bodd_add_div2 a },
     { simp [heq] at h, right, rw ←hr₂ at h, 
       use nat.div2 a, split, exact h,
       simpa [heq] using nat.bodd_add_div2 a } } }
end

theorem many_one_reducible_of_disjoin {p q r s: ℕ → Prop} (h₁ : p ≤₀ r) (h₂ : q ≤₀ s) : p ⊕ q ≤₀ r ⊕ s := 
disjoin_many_one_reducible 
(transitive_many_one_reducible h₁ (many_one_reducible_of_disjoin_left (reflexive_many_one_reducible _))) 
(transitive_many_one_reducible h₂ (many_one_reducible_of_disjoin_right (reflexive_many_one_reducible _)))

def many_one_degree_reduce {α} [primcodable α] : @many_one_degree α _ → @many_one_degree α _ → Prop := 
quotient.lift₂ (λ a b : set α, a ≤₀ b) 
(λ a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩, propext 
   ⟨λ h, transitive_many_one_reducible hr₁ (transitive_many_one_reducible h hl₂), 
    λ h, transitive_many_one_reducible hl₁ (transitive_many_one_reducible h hr₂)⟩) 

instance many_one_degree_le {α} [primcodable α] : has_le (@many_one_degree α _) := ⟨many_one_degree_reduce⟩

theorem refl_reduce {α} [primcodable α] (d : @many_one_degree α _) : 
many_one_degree_reduce d d :=
quotient.induction_on d (λ a b c, reflexive_many_one_reducible _) (set α) (set α)

theorem antisymm_reduce {α} [primcodable α] {d₁ d₂ : @many_one_degree α _} : 
d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ :=
quotient.induction_on₂ d₁ d₂ 
(λ a b c d h₁ h₂, begin apply quotient.sound, exact ⟨h₁, h₂⟩ end) (set α) (set α)

theorem transitive_reduce {α} [primcodable α] {d₁ d₂ d₃ : @many_one_degree α _} : 
d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ :=
quotient.induction_on₃ d₁ d₂ d₃ (λ a b c h₁ h₂, transitive_many_one_reducible h₁ h₂)

def many_one_degree_disjoin : @many_one_degree ℕ _ → @many_one_degree ℕ _ → @many_one_degree ℕ _ := 
quotient.lift₂ (λ a b : set ℕ, ⟦a ⊕ b⟧) 
(λ _ _ _ _ ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩, 
 quotient.sound ⟨many_one_reducible_of_disjoin hl₁ hl₂, many_one_reducible_of_disjoin hr₁ hr₂⟩)

instance degree_add : has_add (@many_one_degree ℕ _) := ⟨many_one_degree_disjoin⟩

theorem degree_le_sup_left {p q : @many_one_degree ℕ _} :  p ≤ p + q :=
quotient.induction_on₂ p q (λ a b, many_one_reducible_of_disjoin_left (reflexive_many_one_reducible _))

theorem degree_le_sup_right {p q : @many_one_degree ℕ _} :  q ≤ p + q :=
quotient.induction_on₂ p q (λ a b, many_one_reducible_of_disjoin_right (reflexive_many_one_reducible _))

theorem degree_sup_le {p q r : @many_one_degree ℕ _} : p ≤ r → q ≤ r → p + q ≤ r :=
quotient.induction_on₃ p q r (λ a b c h₁ h₂, disjoin_many_one_reducible h₁ h₂)

instance join_semilattice_many_one_degree : lattice.semilattice_sup (@many_one_degree ℕ _) := 
{ le := has_le.le,
  sup := has_add.add,
  le_refl := refl_reduce,
  le_antisymm := λ a b, antisymm_reduce,
  le_trans := λ a b c, transitive_reduce,
  le_sup_left := λ a b, degree_le_sup_left,
  le_sup_right := λ a b, degree_le_sup_right,
  sup_le := λ a b c, degree_sup_le }
