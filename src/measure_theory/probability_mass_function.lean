/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Probability mass function -- discrete probability measures
-/
import topology.instances.nnreal topology.instances.ennreal topology.algebra.infinite_sum
noncomputable theory
variables {α : Type*} {β : Type*} {γ : Type*}
local attribute [instance] classical.prop_decidable

/-- Probability mass functions, i.e. discrete probability measures -/
def {u} pmf (α : Type u) : Type u := { f : α → nnreal // is_sum f 1 }

namespace pmf

instance : has_coe_to_fun (pmf α) := ⟨λp, α → nnreal, λp a, p.1 a⟩

@[extensionality] protected lemma ext : ∀{p q : pmf α}, (∀a, p a = q a) → p = q
| ⟨f, hf⟩ ⟨g, hg⟩ eq :=  subtype.eq $ funext eq

lemma is_sum_coe_one (p : pmf α) : is_sum p 1 := p.2

lemma has_sum_coe (p : pmf α) : has_sum p := has_sum_spec p.is_sum_coe_one

@[simp] lemma tsum_coe (p : pmf α) : (∑a, p a) = 1 := tsum_eq_is_sum p.is_sum_coe_one

def support (p : pmf α) : set α := {a | p.1 a ≠ 0}

def pure (a : α) : pmf α := ⟨λa', if a' = a then 1 else 0, is_sum_ite_eq _ _⟩

@[simp] lemma pure_apply (a a' : α) : pure a a' = (if a' = a then 1 else 0) := rfl

instance [inhabited α] : inhabited (pmf α) := ⟨pure (default α)⟩

lemma coe_le_one (p : pmf α) (a : α) : p a ≤ 1 :=
is_sum_le (by intro b; split_ifs; simp [h]; exact le_refl _) (is_sum_ite_eq a (p a)) p.2

protected lemma bind.has_sum (p : pmf α) (f : α → pmf β) (b : β) : has_sum (λa:α, p a * f a b) :=
begin
  refine nnreal.has_sum_of_le (assume a, _) p.has_sum_coe,
  suffices : p a * f a b ≤ p a * 1, { simpa },
  exact mul_le_mul_of_nonneg_left ((f a).coe_le_one _) (p a).2
end

def bind (p : pmf α) (f : α → pmf β) : pmf β :=
⟨λb, (∑a, p a * f a b),
  begin
    simp [ennreal.is_sum_coe.symm, (ennreal.tsum_coe (bind.has_sum p f _)).symm],
    rw [is_sum_iff_of_has_sum ennreal.has_sum, ennreal.tsum_comm],
    simp [ennreal.mul_tsum, (ennreal.tsum_coe (f _).has_sum_coe),
      ennreal.tsum_coe p.has_sum_coe]
  end⟩

@[simp] lemma bind_apply (p : pmf α) (f : α → pmf β) (b : β) : p.bind f b = (∑a, p a * f a b) := rfl

lemma coe_bind_apply (p : pmf α) (f : α → pmf β) (b : β) :
  (p.bind f b : ennreal) = (∑a, p a * f a b) :=
eq.trans (ennreal.tsum_coe $ bind.has_sum p f b).symm $ by simp

@[simp] lemma pure_bind (a : α) (f : α → pmf β) : (pure a).bind f = f a :=
have ∀b a', ite (a' = a) 1 0 * f a' b = ite (a' = a) (f a b) 0, from
  assume b a', by split_ifs; simp; subst h; simp,
by ext b; simp [this]

@[simp] lemma bind_pure (p : pmf α) : p.bind pure = p :=
have ∀a a', (p a * ite (a' = a) 1 0) = ite (a = a') (p a') 0, from
  assume a a', begin split_ifs; try { subst a }; try { subst a' }; simp * at * end,
by ext b; simp [this]

@[simp] lemma bind_bind (p : pmf α) (f : α → pmf β) (g : β → pmf γ) :
  (p.bind f).bind g = p.bind (λa, (f a).bind g) :=
begin
  ext b,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.mul_tsum.symm, ennreal.tsum_mul.symm],
  rw [ennreal.tsum_comm],
  simp [mul_assoc, mul_left_comm, mul_comm]
end

lemma bind_comm (p : pmf α) (q : pmf β) (f : α → β → pmf γ) :
  p.bind (λa, q.bind (f a)) = q.bind (λb, p.bind (λa, f a b)) :=
begin
  ext b,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.mul_tsum.symm, ennreal.tsum_mul.symm],
  rw [ennreal.tsum_comm],
  simp [mul_assoc, mul_left_comm, mul_comm]
end

def map (f : α → β) (p : pmf α) : pmf β := bind p (pure ∘ f)

lemma bind_pure_comp (f : α → β) (p : pmf α) : bind p (pure ∘ f) = map f p := rfl

lemma map_id (p : pmf α) : map id p = p := by simp [map]

lemma map_comp (p : pmf α) (f : α → β) (g : β → γ) : (p.map f).map g = p.map (g ∘ f) :=
by simp [map]

lemma pure_map (a : α) (f : α → β) : (pure a).map f = pure (f a) :=
by simp [map]

def seq (f : pmf (α → β)) (p : pmf α) : pmf β := f.bind (λm, p.bind $ λa, pure (m a))

def of_multiset (s : multiset α) (hs : s ≠ 0) : pmf α :=
⟨λa, s.count a / s.card,
  have s.to_finset.sum (λa, (s.count a : ℝ) / s.card) = 1,
    by simp [div_eq_inv_mul, finset.mul_sum.symm, (finset.sum_nat_cast _ _).symm, hs],
  have s.to_finset.sum (λa, (s.count a : nnreal) / s.card) = 1,
    by rw [← nnreal.eq_iff, nnreal.coe_one, ← this, nnreal.sum_coe]; simp,
  begin
    rw ← this,
    apply is_sum_sum_of_ne_finset_zero,
    simp {contextual := tt},
  end⟩

def of_fintype [fintype α] (f : α → nnreal) (h : finset.univ.sum f = 1) : pmf α :=
⟨f, h ▸ is_sum_sum_of_ne_finset_zero (by simp)⟩

def bernoulli (p : nnreal) (h : p ≤ 1) : pmf bool :=
of_fintype (λb, cond b p (1 - p)) (nnreal.eq $ by simp [h])

end pmf
