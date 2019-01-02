/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

A formalization of Bayes theorem.
-/

import analysis.measure_theory.measure_space
import tactic.tidy 

-- set_option trace.simplify.rewrite true

open set measurable_space measure_theory ennreal

universe u

variables {α : Type u}

def samp_space := Type u 

@[reducible] def events (s:samp_space) := set s
variable s:samp_space

section setthry
variables a b : events s

lemma union_comm (a b : events s) : a ∪ b = b ∪ a := 
is_commutative.comm _ a b 

lemma inter_comm (a b : events s) : a ∩ b = b ∩ a := 
is_commutative.comm _ a b 

lemma inter_assoc (a b c : events s) : (a ∩ b) ∩ c = a ∩ (b ∩ c) := 
is_associative.assoc _ a b c 

lemma inter_distrib_left (a b c : events s) : (a ∩ (b ∪ c)) = (a ∩ b) ∪ (a ∩ c) := 
inter_distrib_left a b c 

lemma union_distrib_left (a b c : events s) : (a ∪ (b ∩ c)) = (a ∪ b) ∩ (a ∪ c) := 
union_distrib_left a b c 

lemma demorgan_union ( a b : events s) : -(a ∪ b) = -a ∩ -b :=
compl_union a b 

lemma demorgan_inter ( a b : events s) : -(a ∩ b) = -a ∪ -b :=
compl_inter a b 

def are_disjoint (a b : events s) := a ∩ b = ∅

def are_disj_ctble {s : samp_space} (a : set(events s)) :=
(countable a) ∧ (∀ x y ∈ a, (x ≠ y) → (x ∩ y = ∅)) 

def are_disj_ctble' (f : ℕ → events s) := ∀ i j : ℕ, (i ≠ j) → (f i) ∩ (f j) = ∅ 

def is_partition {s : samp_space} (a : set(events _)) := 
(are_disj_ctble a) ∧ ( ⋃₀ a = @univ s)

def is_partition' {s : samp_space} (f : ℕ  → events s) := 
(are_disj_ctble' _ f) ∧ ((⋃i, f i) = univ) 

end setthry

section axfndns

structure prob  (α : Type*) [measurable_space α] extends measure_theory.measure α :=
(is_one : measure_of univ = 1)

instance prob.has_coe_to_fun {α} [measurable_space α] : has_coe_to_fun (prob α) :=
⟨λ _, set α → ennreal, λ m, m.to_measure⟩

@[simp] lemma prob_eq_coerc {s : samp_space} [measurable_space s] (p : prob s) (a : set s): 
p a =  p.to_measure a := by refl 

-- def prob_fintype {s : samp_space} [fintype s] [measurable_space s] 
-- (p : s → ennreal) (h : finset.univ.sum p = 1) : prob s :=  
-- begin
--  fsplit, 
--  fapply measure.of_measurable,
--  {
--      intros a h1, 
--      haveI : decidable_pred a := λx, classical.prop_decidable _, --make a decidable
--      exact finset.sum (finset.univ.filter (∈ a)) p,
--  } ,
-- {
-- simp, simp,
-- -- repeat { simp }
-- },
-- {
-- intros f h_f g,
-- -- state a lemma of finsets on disj unions
-- -- prove it with induction in finset.lean
-- -- intros, repeat{ simp },
-- },
-- {
-- sorry
-- }
-- end


lemma prob_empty {s : samp_space} [measurable_space s] (p : prob s) : p(∅) = 0 :=
p.empty 

lemma prob_univ {s : samp_space} [measurable_space s] (p : prob s) : p(univ) = 1 := 
p.is_one

lemma prob_le_1 {s : samp_space} [measurable_space s] (p : prob s) : 
Π (a : set(s)),p(a) ≤ (1:ennreal) :=
begin
intros, rewrite ← prob_univ p, apply outer_measure.mono, apply subset_univ, 
end


lemma prob_ne_top {s : samp_space} [measurable_space s] (p : prob s):
Π (a : set(s)), p(a) ≠ ⊤ :=
begin
intros a,
rw ← lattice.lt_top_iff_ne_top,
have h : (1 : ennreal) < ⊤, {
    rw lattice.lt_top_iff_ne_top,
apply ennreal.one_ne_top,
},
apply lt_of_le_of_lt (prob_le_1 p a) h,
end

lemma prob_mono {s : samp_space} [measurable_space s] (p : prob s) (a b : set s)
(h1 : is_measurable a) (h2 : is_measurable b):
(a ⊆ b) → (p(a) ≤ p(b)) :=  measure_theory.measure_mono 

lemma prob_comp {s : samp_space} [measurable_space s] (p : prob s) 
(a : set s)
(h: is_measurable a): p(-a) + p(a) = 1 :=
begin
intros, rewrite ← prob_univ p,
simp only [prob_eq_coerc],
rewrite ← compl_union_self a,
rw measure_union _ _ _,
apply disjoint_iff.2 (@compl_inter_self _ a),
apply is_measurable.compl, repeat{assumption},
end

lemma prob_union {s : samp_space} [measurable_space s] (s₁ s₂ : set s)
(hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) (p : prob s) :
  p (s₁ ∪ s₂) = p s₁ + p s₂ := measure_theory.measure_union hd h₁ h₂ 

lemma prob_diff_inter {s : samp_space} [measurable_space s](p : prob s) 
(a b : set s) (h₁ : is_measurable a) (h₂ : is_measurable b) :
p(b ∩ -a) + p(b ∩ a) = p(b) :=
begin
have h :p(b) = p(b ∩ univ),
by rewrite inter_univ b,
rewrite [h,← compl_union_self a,set.inter_distrib_left,prob_union],
have g : (b ∩ -a) ∩ (b ∩ a) = ∅, by rw [inter_left_comm,set.inter_assoc, compl_inter_self,inter_empty,inter_empty],
apply disjoint_iff.2 g,
{
    rewrite ← diff_eq,
    apply is_measurable.diff h₂ h₁,
},
apply is_measurable.inter h₂ h₁,
end

lemma prob_union_inter {s : samp_space} [measurable_space s] (p : prob s) 
(a b : set s) (h_1 : is_measurable a) (h_2 : is_measurable b) :
p(a ∪ b) + p(a ∩ b) = p(a) + p(b) :=
begin 
have h₁ : a ∪ b = a ∪ (b ∩ -a),by
rewrite [set.union_distrib_left, union_compl_self a,inter_univ],
have h₂ : is_measurable(b ∩ -a),
{
    rewrite ← diff_eq,
    apply is_measurable.diff h_2 h_1,
},
rewrite [h₁,prob_union a _ _ h_1 h₂],
have h₃: a ∩ b = b ∩ a, by exact inter_comm a b,
rewrite [h₃,← prob_diff_inter p a b h_1 h_2],
simp,
have h₄ : a ∩ (b ∩ -a) = ∅, by tidy,
apply disjoint_iff.2 h₄,
end

lemma bonferroni {s : samp_space} [measurable_space s] (p : prob s)
(a b : set s) (h_1 : is_measurable a) (h_2 : is_measurable b) :
p(a) + p(b) ≤ p(a ∩ b) + 1 :=
begin
rewrite [← prob_union_inter p a b h_1 h_2, ← add_comm],
apply add_le_add_left' _,
apply prob_le_1,
end

lemma prob_partn {s : samp_space} [measurable_space s] (p : prob s)
(f : ℕ → events s) 
(h₁: is_partition' f) 
(a : events s) 
(h₂ : is_measurable a) 
(h₃ : ∀ i : ℕ, is_measurable (f i))
(i : ℕ) :
p(a) = ∑i, p(a ∩ f i) :=
begin
have g₁ : p(a) = p(a ∩ univ), by rw inter_univ,  
have g₂ : p(a) = p(⋃ i , (a ∩ f i)),by rw [g₁,← h₁.right, inter_Union_left],
rw g₂,
apply p.m_Union, 
{
    intros j, 
    apply is_measurable.inter, 
    exact h₂, exact h₃ j,
},
intros m n h,
have g₃ : (λ (i : ℕ), a ∩ f i) m ∩ (λ (i : ℕ), a ∩ f i) n = ∅,
{
rw [set.inter_left_comm,set.inter_assoc,h₁.left m n],
simpa,
},
apply disjoint_iff.2 g₃,
end

end axfndns

section cond_prob

noncomputable def cond_prob {s : samp_space} [measurable_space s] (p : prob s)
(a b : events s) := p(a ∩ b)/p(b)

variables a b : ennreal

notation `ℙ^`:95 p `[[`:95 a ` | `:95 b `]]`:0 := cond_prob p a b


lemma cond_prob_rw {s : samp_space} [measurable_space s] (p : prob s)
(a b : events s) (h₁ : p(b) ≠ 0):
p(a ∩ b) = ℙ^p [[ a | b ]] * p(b) :=
begin
unfold cond_prob,
rw [div_def,mul_assoc],
have g₁ : (1 : ennreal) < ⊤, {
    rw lattice.lt_top_iff_ne_top,
apply ennreal.one_ne_top,
},
have g₂ : ∀ a, (p(a) ≠ 0) → (p(a))⁻¹ * p(a) = 1,
{
    intros a k,
    rw mul_comm,
    apply ennreal.mul_inv_cancel, exact k, rw ← lattice.lt_top_iff_ne_top,
    apply lt_of_le_of_lt (prob_le_1 p a) g₁ 
},
rw g₂ b h₁, simp,
end

@[simp] theorem bayes {s : samp_space} [measurable_space s] (p : prob s)
(a b : events s) (h₁ : p a ≠ 0) (h₂ : p b ≠ 0) :
ℙ^p [[ b | a ]] * p(a) =  ℙ^p [[ a | b ]] * p(b) :=
begin
unfold cond_prob,
rw [div_def,mul_assoc],
have g₁ : (1 : ennreal) < ⊤, {
    rw lattice.lt_top_iff_ne_top,
apply ennreal.one_ne_top,
},
have g₂ : ∀ a, (p(a) ≠ 0) → (p(a))⁻¹ * p(a) = 1,
{
    intros a k,
    rw mul_comm,
    apply ennreal.mul_inv_cancel, exact k, rw ← lattice.lt_top_iff_ne_top,
    apply lt_of_le_of_lt (prob_le_1 p a) g₁ 
},
rw [g₂ a,div_def,mul_assoc,g₂ b, mul_one],
symmetry, rw [mul_one,set.inter_comm],
assumption, assumption,
end

lemma total_prob {s : samp_space} [measurable_space s] (p : prob s)
(f : ℕ → events s) 
(h₁: is_partition' f) 
(a : events s) 
(h₂ : is_measurable a) 
(h₃ : ∀ i : ℕ, is_measurable (f i))
(h₄ : ∀ i : ℕ, p (f i) ≠ 0)
(i : ℕ) :
p(a) = ∑j, ℙ^p[[a | f j]] * p(f j)
:=
begin 
rw prob_partn _ f h₁ a h₂ h₃ i,
have α : (λ (i : ℕ), p (a ∩ f i)) = (λ (i : ℕ),  ℙ^p [[ a | f i ]] * p(f i)),{
    apply funext, intros x, apply cond_prob_rw, apply h₄ x,  
},
rw α, 
end


theorem Bayes {s : samp_space} [measurable_space s] (p : prob s)
(f : ℕ → events s) (b : events s)
(h₁: is_partition' f) 
(h₂ : p b ≠ 0)
(h₃ : ∀ j : ℕ, is_measurable (f j))
(h₄ : ∀ j : ℕ, p (f j) ≠ 0)
(h₅ : is_measurable b)
:  ∀ i : ℕ , 
ℙ^p[[(f i) | b]] = (ℙ^p[[b | f i]])*(p(f i))/(∑j, ℙ^p[[b | f j]] * p(f j)):= 
begin
intros i,
rw ← total_prob _ f h₁ b h₅ h₃ h₄ i,
rw bayes _ (f i) b (h₄ i) ,
rw [div_def,mul_assoc],
rw ennreal.mul_inv_cancel h₂ (prob_ne_top _ b),
simp,
exact h₂,
end
end cond_prob