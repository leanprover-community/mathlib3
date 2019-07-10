/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Minchao Wu

Strong reducibility and degrees.
-/

import computability.halting 
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
      intro, dsimp, cases heq : g (f n), repeat { simp [hf, heq] },
      { intro, cases heq : g (f a), 
        { left, simp [hf, heq] },
        { right, simp [hf, heq] } } }
  end

theorem computable_of_one_one_reducible
  {p q : α → Prop} 
  (h₁ : p ≤₁ q) (h₂ : computable_pred q) : computable_pred p := 
  begin
    rcases h₁ with ⟨f, c, hinj, hf⟩,
    apply computable_of_many_one_reducible _ h₂,
    use f, exact ⟨c, hf⟩
  end

end computable_pred

def many_one_equiv {α} [primcodable α] (p q : α → Prop) := p ≤₀ q ∧ q ≤₀ p

def one_one_equiv {α} [primcodable α] (p q : α → Prop) := p ≤₁ q ∧ q ≤₁ p

theorem equivalence_of_m_equiv {α} [primcodable α] : equivalence (@many_one_equiv α _) :=
⟨λ x,⟨reflexive_many_one_reducible _, reflexive_many_one_reducible _⟩,  
 λ x y h, ⟨h.2, h.1⟩, 
 λ x y z h₁ h₂, ⟨transitive_many_one_reducible h₁.1 h₂.1, transitive_many_one_reducible h₂.2 h₁.2⟩⟩

theorem equivalence_of_one_equiv {α} [primcodable α] : equivalence (@one_one_equiv α _) :=
⟨λ x,⟨reflexive_one_one_reducible _, reflexive_one_one_reducible _⟩,  
 λ x y h, ⟨h.2, h.1⟩, 
 λ x y z h₁ h₂, ⟨transitive_one_one_reducible h₁.1 h₂.1, transitive_one_one_reducible h₂.2 h₁.2⟩⟩

instance many_one_equiv_setoid {α} [primcodable α] : setoid (α → Prop) := 
⟨many_one_equiv, @equivalence_of_m_equiv α _⟩

def many_one_degree {α} [primcodable α] := quotient (@many_one_equiv_setoid α _)

def disjoin (p q : set ℕ) : set ℕ  := (λ x, 2 * x) '' p ∪ (λ x, 2 * x + 1) '' q

local infix ` ⊕ `:1001 := disjoin

theorem mem_disjoin_left {p q : set ℕ} {n : ℕ} (h₁ : ¬nat.bodd n) (h₂ : (p ⊕ q) n) : p (nat.div2 n) :=
begin
  cases h₂,
  { rcases h₂ with ⟨w, hl, hr⟩, rw ←hr,  dsimp, rw ←nat.bit0_val, rw nat.div2_bit0, exact hl},
  { rcases h₂ with ⟨w, hl, hr⟩, rw ←hr at h₁, simp at h₁, contradiction }
end

theorem mem_disjoin_right {p q : set ℕ} {n : ℕ} (h₁ : nat.bodd n) (h₂ : (p ⊕ q) n) : q (nat.div2 n) :=
begin
  cases h₂,
  { rcases h₂ with ⟨w, hl, hr⟩, rw ←hr at h₁, simp at h₁, contradiction },
  { rcases h₂ with ⟨w, hl, hr⟩, rw ←hr, dsimp, rw ←nat.bit1_val, rw nat.div2_bit1, exact hl }
end

namespace nat.primrec

lemma add1 : primrec (nat.unpaired (λ x y, nat.succ y)) :=
by { rw primrec₂.unpaired, exact primrec.comp₂ primrec.succ primrec₂.right }

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

theorem many_one_reducible_of_disjoin_left {p q : ℕ → Prop} : p ≤₀ p ⊕ q := 
⟨λ a, (2 * a), by { apply primrec.to_comp, exact double }, 
 λ a, ⟨λ h, by { dsimp [disjoin], left, use a, simpa [h] },
       λ h, begin 
              dsimp [disjoin] at h, cases h, 
              { rcases h with ⟨b, hbl, hbr⟩, 
                rw [← nat.eq_of_mul_eq_mul_left _ hbr], 
                exact hbl, exact dec_trivial }, 
              { rcases h with ⟨b, hbl, hbr⟩, exfalso, apply nat.two_mul_ne_two_mul_add_one hbr.symm } 
            end⟩⟩

theorem many_one_reducible_of_disjoin_right {p q : ℕ → Prop} : q ≤₀ p ⊕ q := 
⟨λ a, (2 * a + 1), by {apply primrec.to_comp, exact double_succ },
 λ a, ⟨λ h, by { dsimp [disjoin], right, use a, simpa [h] },
       λ h, begin 
              dsimp [disjoin] at h, cases h, 
              { rcases h with ⟨b, hbl, hbr⟩, exfalso, apply nat.two_mul_ne_two_mul_add_one hbr }, 
              { rcases h with ⟨b, hbl, hbr⟩,
                simp only [add_left_inj, add_comm] at hbr,
                rw [←nat.eq_of_mul_eq_mul_left _ hbr], 
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
       have := nat.bodd_add_div2 a, simp [heq] at this, simp [this] },
     { simp [heq] at h, right, rw ←hr₂ at h, 
       use nat.div2 a, split, exact h,
       have := nat.bodd_add_div2 a, simp [heq] at this, simp [this] } } }
end
