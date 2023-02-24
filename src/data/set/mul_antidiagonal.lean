/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import order.well_founded_set

/-! # Multiplication antidiagonal 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

namespace set
variables {α : Type*}

section has_mul
variables [has_mul α] {s s₁ s₂ t t₁ t₂ : set α} {a : α} {x : α × α}

/-- `set.mul_antidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that multiply to `a`. -/
@[to_additive "`set.add_antidiagonal s t a` is the set of all pairs of an element in `s` and an
element in `t` that add to `a`."]
def mul_antidiagonal (s t : set α) (a : α) : set (α × α) := {x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a}

@[simp, to_additive]
lemma mem_mul_antidiagonal : x ∈ mul_antidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a :=
iff.rfl

@[to_additive] lemma mul_antidiagonal_mono_left (h : s₁ ⊆ s₂) :
  mul_antidiagonal s₁ t a ⊆ mul_antidiagonal s₂ t a :=
λ x hx, ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive] lemma mul_antidiagonal_mono_right (h : t₁ ⊆ t₂) :
  mul_antidiagonal s t₁ a ⊆ mul_antidiagonal s t₂ a :=
λ x hx, ⟨hx.1, h hx.2.1, hx.2.2⟩

end has_mul

@[simp, to_additive] lemma swap_mem_mul_antidiagonal [comm_semigroup α] {s t : set α} {a : α}
  {x : α × α} :
  x.swap ∈ set.mul_antidiagonal s t a ↔ x ∈ set.mul_antidiagonal t s a :=
by simp [mul_comm, and.left_comm]

namespace mul_antidiagonal

section cancel_comm_monoid
variables [cancel_comm_monoid α] {s t : set α} {a : α} {x y : mul_antidiagonal s t a}

@[to_additive]
lemma fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2 :=
⟨λ h, mul_left_cancel (y.prop.2.2.trans $ by { rw ←h, exact x.2.2.2.symm }).symm,
  λ h, mul_right_cancel (y.prop.2.2.trans $ by { rw ←h, exact x.2.2.2.symm }).symm⟩

@[to_additive] lemma eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
subtype.ext $ prod.ext h $ fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive] lemma eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
subtype.ext $ prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

end cancel_comm_monoid

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] (s t : set α) (a : α) {x y : mul_antidiagonal s t a}

@[to_additive]
lemma eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 ≤ (y : α × α).1)
  (h₂ : (x : α × α).2 ≤ (y : α × α).2) :
  x = y :=
eq_of_fst_eq_fst $ h₁.eq_of_not_lt $ λ hlt, (mul_lt_mul_of_lt_of_le hlt h₂).ne $
  (mem_mul_antidiagonal.1 x.2).2.2.trans (mem_mul_antidiagonal.1 y.2).2.2.symm

variables {s t}

@[to_additive]
lemma finite_of_is_pwo (hs : s.is_pwo) (ht : t.is_pwo) (a) : (mul_antidiagonal s t a).finite :=
begin
  refine not_infinite.1 (λ h, _),
  have h1 : (mul_antidiagonal s t a).partially_well_ordered_on (prod.fst ⁻¹'o (≤)),
    from λ f hf, hs (prod.fst ∘ f) (λ n, (mem_mul_antidiagonal.1 (hf n)).1),
  have h2 : (mul_antidiagonal s t a).partially_well_ordered_on (prod.snd ⁻¹'o (≤)),
    from λ f hf, ht (prod.snd ∘ f) (λ n, (mem_mul_antidiagonal.1 (hf n)).2.1),
  obtain ⟨g, hg⟩ := h1.exists_monotone_subseq (λ n, h.nat_embedding _ n)
    (λ n, (h.nat_embedding _ n).2),
  obtain ⟨m, n, mn, h2'⟩ := h2 (λ x, (h.nat_embedding _) (g x)) (λ n, (h.nat_embedding _ _).2),
  refine mn.ne (g.injective $ (h.nat_embedding _).injective _),
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2',
end

end ordered_cancel_comm_monoid

@[to_additive]
lemma finite_of_is_wf [linear_ordered_cancel_comm_monoid α] {s t : set α} (hs : s.is_wf)
  (ht : t.is_wf) (a) :
  (mul_antidiagonal s t a).finite :=
finite_of_is_pwo hs.is_pwo ht.is_pwo a

end mul_antidiagonal

end set
