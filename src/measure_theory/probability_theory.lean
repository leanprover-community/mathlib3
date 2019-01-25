/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

A formalization of Basic probability theory + Bayes theorem.
-/
import measure_theory.measure_space tactic.tidy

open set measurable_space measure_theory ennreal lattice

universe u

/- The sample space -/
variable {s : Type u}

section probability_measure

structure probability_measure  (α : Type*) [measurable_space α] extends measure_theory.measure α :=
(is_one : measure_of univ = 1)

class probability_space (α : Type*) extends measurable_space α :=
(μ {} : probability_measure α)

instance prob.has_coe_to_fun {α} [probability_space α] : has_coe_to_fun (probability_measure α) :=
⟨λ _, set α → ennreal, λ m, m.to_measure⟩

/- The coercion of a ennreal probability measure to a nnreal probability measure -/
def prob [probability_space s] (p : probability_measure s) (a : set s)
:= (p a).to_nnreal

variables [probability_space s] (p : probability_measure s) (a : set s)

lemma prob_eq_coerc: prob p a = ennreal.to_nnreal(p a) := rfl

lemma coe_def (a : set s): p a = p.to_measure a := rfl

lemma prob_univ : p(univ) = 1 := p.is_one

lemma prob_univ_nnreal : prob p univ = 1 :=
begin
  rw [prob,prob_univ],refl,
end

lemma prob_le_1 :
Π (a : set(s)), p(a) ≤ (1:ennreal) :=
begin
  intros,
  rewrite ← prob_univ p,
  apply outer_measure.mono,
  apply subset_univ,
end

lemma prob_ne_top :
Π (a : set(s)), p(a) ≠ ⊤ :=
begin
  intros a,
  rw ← lattice.lt_top_iff_ne_top,
  have h : (1 : ennreal) < ⊤,
    { rw lattice.lt_top_iff_ne_top,
    apply ennreal.one_ne_top, },
  apply lt_of_le_of_lt (prob_le_1 p a) h,
end

@[simp] lemma coe_prob (a : set s) : (prob p a : ennreal) = p a := coe_to_nnreal  (prob_ne_top _ _)

lemma prob_le_1_nnreal :
Π (a : set(s)), prob p a ≤ (1:nnreal) :=
begin
  intros, rw ← ennreal.coe_le_coe,
  rw coe_prob,
  exact prob_le_1 p a,
end

lemma prob_empty : p(∅) = 0 := measure_empty

lemma prob_empty_nnreal : prob p ∅ = 0 :=
begin
rw prob, rw prob_empty, refl,
end

lemma prob_mono (a b : set s) (h1 : is_measurable a)
  (h2 : is_measurable b) : (a ⊆ b) → (p(a) ≤ p(b)) :=
  measure_theory.measure_mono

lemma prob_mono_nnreal (a b : set s) (h1 : is_measurable a)
  (h2 : is_measurable b) : (a ⊆ b) → (prob p a ≤ prob p b) :=
begin
  intros h,
  rw ← ennreal.coe_le_coe,
  rw [coe_prob,coe_prob],
  apply prob_mono p a b h1 h2 h,
end

lemma prob_comp
(a : set s)
(h: is_measurable a): p(-a) + p(a) = 1 :=
begin
  intros, rewrite ← prob_univ p,
  have h : ∀ x : set s, p x = p.to_measure x, {intros x, refl},
  repeat {rw h},
  rw [← compl_union_self a, measure_union _ _ _],
  apply disjoint_iff.2 (@compl_inter_self _ a),
  apply is_measurable.compl, repeat{assumption},
end

lemma prob_comp_nnreal
(a : set s)
(h: is_measurable a): prob p (-a) + prob p (a) = 1 :=
begin
  rw ← ennreal.coe_eq_coe,
  simp, rw add_comm,
  apply prob_comp p a h,
end


lemma prob_union {s : Type u} [probability_space s] (s₁ s₂ : set s) (hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) (p : probability_measure s) :
  p (s₁ ∪ s₂) = p s₁ + p s₂ := measure_theory.measure_union hd h₁ h₂

lemma prob_union_nnreal {s : Type u} [probability_space s] (s₁ s₂ : set s)
(hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) (p : probability_measure s) :
  prob p (s₁ ∪ s₂) = prob p s₁ + prob p s₂ :=
begin
  rw ← ennreal.coe_eq_coe, simp, apply prob_union s₁ s₂ hd h₁ h₂,
end

lemma prob_diff_inter {s : Type u} [probability_space s](p : probability_measure s)
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

lemma prob_diff_inter_nnreal {s : Type u} [probability_space s](p : probability_measure s)
(a b : set s) (h₁ : is_measurable a) (h₂ : is_measurable b) :
prob p (b ∩ -a) + prob p (b ∩ a) = prob p (b) :=
begin
  rw ← ennreal.coe_eq_coe,
  simp, rw add_comm,
  apply prob_diff_inter p a b h₁ h₂,
end

lemma prob_union_inter
(a b : set s) (g₁ : is_measurable a) (g₂ : is_measurable b) :
p(a ∪ b) + p(a ∩ b) = p(a) + p(b) :=
begin
  have h₁ : a ∪ b = a ∪ (b ∩ -a),by
    rewrite [set.union_distrib_left, union_compl_self a,inter_univ],
  have h₂ : is_measurable(b ∩ -a),
  {
    rewrite ← diff_eq,
    apply is_measurable.diff g₂ g₁,
  },
  rewrite [h₁,prob_union a _ _ g₁ h₂],
  have h₃: a ∩ b = b ∩ a, by exact set.inter_comm a b,
  rewrite [h₃,← prob_diff_inter p a b g₁ g₂],
  simp,
  have h₄ : a ∩ (b ∩ -a) = ∅, by tidy,
  apply disjoint_iff.2 h₄,
end

lemma prob_union_inter_nnreal
(a b : set s) (g₁ : is_measurable a) (g₂ : is_measurable b) :
prob p (a ∪ b) + prob p (a ∩ b) = prob p (a) + prob p (b) :=
begin
  rw ← ennreal.coe_eq_coe,
  simp only [coe_prob, ennreal.coe_add],
  apply prob_union_inter p a b g₁ g₂,
end

/-- The Bonnferroni inequality. --/
lemma prob_add_le_inter_add_one
(a b : set s) (h_1 : is_measurable a) (h_2 : is_measurable b) :
p(a) + p(b) ≤ p(a ∩ b) + 1 :=
begin
  rewrite [← prob_union_inter p a b h_1 h_2, ← add_comm],
  apply add_le_add_left' _,
  apply prob_le_1,
end

/-- The Bonnferroni inequality for a nnreal probability measure. --/
lemma prob_add_le_inter_add_one_nnreal
(a b : set s) (h_1 : is_measurable a) (h_2 : is_measurable b) :
prob p a + prob p b ≤ prob p (a ∩ b) + 1:=
begin
  rw ← ennreal.coe_le_coe, simp only [coe_prob, ennreal.coe_add, ennreal.coe_one],
  apply prob_add_le_inter_add_one p a b h_1 h_2,
end

def are_disj_ctble' (f : ℕ → set s) := pairwise (disjoint on λ (i : ℕ), f i)

def is_partition' (f : ℕ  → set s) := (are_disj_ctble' f) ∧ ((⋃i, f i) = univ)


lemma prob_partn
{f : ℕ → set s}
{a : set s}
(h₁: is_partition' f)
(h₂ : is_measurable a)
(h₃ : ∀ i : ℕ, is_measurable (f i))
:
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
  refine disjoint_mono _ _ (h₁.left m n h),
  repeat{apply inter_subset_right},
end

lemma prob_partn_ne_top {f : ℕ → set s}
(h₁: is_partition' f)
(h₂ : is_measurable a)
(h₃ : ∀ i : ℕ, is_measurable (f i)):
((∑i, p (a ∩ f i)) ≠ ⊤) :=
begin
rw ← lt_top_iff_ne_top,
have h : ∀ i , p(a ∩ f i) ≤ p (f i), {
  intro j,
  apply prob_mono,
  by apply is_measurable.inter h₂ (h₃ j),
  by exact h₃ j, by finish,
},
have k₁ : has_sum (λ (i : ℕ), p (f i)), by apply ennreal.has_sum,
have k₂ : has_sum (λ (i : ℕ), p (a ∩ f i)),
  by apply ennreal.has_sum,
have k₃ : (∑i, p (a ∩ f i)) ≤ (∑i, p (f i)),
{
  apply tsum_le_tsum h k₂ k₁,
},
have l₀ : tsum (λ (i : ℕ), p (f i)) = 1,
{
  rw [ ← prob_univ p,← h₁.right],
  symmetry,
  apply p.m_Union h₃,
  exact h₁.left,
},
rw l₀ at k₃,

apply lt_of_le_of_lt k₃, rw lt_top_iff_ne_top,
apply one_ne_top,
end


lemma prob_partn_nnreal
{f : ℕ → set s}
(h₁: is_partition' f)
{a : set s}
(h₂ : is_measurable a)
(h₃ : ∀ i : ℕ, is_measurable (f i))
:
prob p a = ∑i, prob p (a ∩ f i) :=
begin
  rw [←ennreal.coe_eq_coe, ←ennreal.tsum_coe'], simp,
  apply prob_partn p h₁ h₂ h₃,
  simp, rw ← prob_partn p h₁ h₂ h₃,
  apply prob_ne_top,
end

end probability_measure

section cond_prob

noncomputable def cond_prob {s : Type u} [probability_space s] (p : probability_measure s)
(a b : set s) := p(a ∩ b)/p(b)

noncomputable def cond_prob_nnreal {s : Type u} [probability_space s] (p : probability_measure s)
(a b : set s) := prob p (a ∩ b) /(prob p b)

variables [probability_space s] (p : probability_measure s)

notation `ℙ^`:95 p `[[`:95 a ` | `:95 b `]]`:0 := cond_prob p a b
notation `ℙ^^`:95 p `[[`:95 a ` | `:95 b `]]`:0 := cond_prob_nnreal p a b


lemma cond_prob_rw
(a b : set s) (h₁ : p(b) ≠ 0):
p(a ∩ b) = ℙ^p [[ a | b ]] * p(b) :=
begin
  unfold cond_prob,
  rw [div_def,mul_assoc],
  have g₁ : (1 : ennreal) < ⊤,
  {
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


lemma cond_prob_rw_nnreal
(a b : set s) (h₁ : p(b) ≠ 0):
prob p (a ∩ b) = ℙ^^p [[ a | b ]] * prob p b :=
begin
  unfold cond_prob_nnreal,
  rw ← ennreal.coe_eq_coe, simp,
  rw coe_div, simp, apply cond_prob_rw _ a b h₁,
  {
    rw [ne.def, ← ennreal.coe_eq_coe, coe_prob],
    assumption,
  }
end

/- Bayes theorem for two sets -/
@[simp] theorem cond_prob_swap
{a b : set s} (h₁ : p a ≠ 0) (h₂ : p b ≠ 0) :
ℙ^p [[ b | a ]] * p(a) =  ℙ^p [[ a | b ]] * p(b) :=
begin
  unfold cond_prob,
  rw [div_def,mul_assoc],
  have g₁ : (1 : ennreal) < ⊤,
  {
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

theorem cond_prob_swap_nnreal
{a b : set s} (h₁ : p a ≠ 0) (h₂ : p b ≠ 0) :
ℙ^^p [[ b | a ]] * prob p a =  ℙ^^p [[ a | b ]] * prob p b :=
begin
  unfold cond_prob_nnreal,
  rw ← ennreal.coe_eq_coe, simp,
  repeat{rw coe_div}, simp,
  apply cond_prob_swap p h₁ h₂,
  repeat{
    rw [ne.def, ← ennreal.coe_eq_coe, coe_prob],
    assumption,
  },
end

/-- Law of Total Probability for an ennreal probability measure--/
@[simp] lemma total_prob
{f : ℕ → set s}
(h₁: is_partition' f)
{a : set s}
(h₂ : is_measurable a)
(h₃ : ∀ i : ℕ, is_measurable (f i))
(h₄ : ∀ i : ℕ, p (f i) ≠ 0) :
p(a) = ∑j, ℙ^p[[a | f j]] * p(f j)
:=
begin
  rw prob_partn p h₁ h₂ h₃,
  have g : (λ (i : ℕ), p (a ∩ f i)) = (λ (i : ℕ),  ℙ^p [[ a | f i ]] * p(f i)),
  {
    apply funext, intros x, apply cond_prob_rw, apply h₄ x,
  },
  rw g,
end

/-- Law of Total Probability for a nnreal probability measure--/
lemma total_prob_nnreal
{f : ℕ → set s}
(h₁: is_partition' f)
{a : set s}
(h₂ : is_measurable a)
(h₃ : ∀ i : ℕ, is_measurable (f i))
(h₄ : ∀ i : ℕ, p (f i) ≠ 0) :
prob p a = ∑j, ℙ^^p[[a | f j]] * prob p (f j)
:=
begin
  rw prob_partn_nnreal p h₁ h₂ h₃,
   have g : (λ (i : ℕ),prob p (a ∩ f i)) = (λ (i : ℕ),  ℙ^^p [[ a | f i ]] * prob p(f i)),
  {
    apply funext, intros x, apply cond_prob_rw_nnreal, apply h₄ x,
  },
  rw g,
end

/-- Bayes theorem for an arbitrary partition of the sample space --/
theorem cond_prob_partn_swap
(f : ℕ → set s) (b : set s)
(h₁: is_partition' f)
(h₂ : p b ≠ 0)
(h₃ : ∀ j : ℕ, is_measurable (f j))
(h₄ : ∀ j : ℕ, p (f j) ≠ 0)
(h₅ : is_measurable b)
:  ∀ i : ℕ ,
ℙ^p[[(f i) | b]] = (ℙ^p[[b | f i]])*(p(f i))/(∑j, ℙ^p[[b | f j]] * p(f j)):=
begin
  intros i,
  rw ← total_prob p h₁ h₅ h₃ h₄,
  rw cond_prob_swap p (h₄ i) h₂,
  rw [div_def,mul_assoc],
  rw ennreal.mul_inv_cancel h₂ (prob_ne_top p b),
  simp,
end

/-- Bayes theorem for an arbitrary partition of the sample space for an nnreal probability measure --/
theorem cond_prob_partn_swap_nnreal
(f : ℕ → set s) (b : set s)
(h₁: is_partition' f)
(h₂ : p b ≠ 0)
(h₃ : ∀ j : ℕ, is_measurable (f j))
(h₄ : ∀ j : ℕ, p (f j) ≠ 0)
(h₅ : is_measurable b)
:  ∀ i : ℕ ,
ℙ^^p[[(f i) | b]] = (ℙ^^p[[b | f i]])*(prob p(f i))/(∑j, ℙ^^p[[b | f j]] * prob p (f j)):=
begin
  intros i,
  rw ← total_prob_nnreal p h₁ h₅ h₃ h₄,
  rw cond_prob_swap_nnreal p (h₄ i) h₂,
  rw [nnreal.div_def,mul_assoc],
  rw nnreal.mul_inv_cancel,
  simp, rw [ne.def, ← ennreal.coe_eq_coe, coe_prob],
  assumption,
end

end cond_prob
