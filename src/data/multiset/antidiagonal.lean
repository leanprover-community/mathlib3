/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.powerset

/-!
# The antidiagonal on a multiset.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/

namespace multiset
open list

variables {α β : Type*}

/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
def antidiagonal (s : multiset α) : multiset (multiset α × multiset α) :=
quot.lift_on s
  (λ l, (revzip (powerset_aux l) : multiset (multiset α × multiset α)))
  (λ l₁ l₂ h, quot.sound (revzip_powerset_aux_perm h))

theorem antidiagonal_coe (l : list α) :
  @antidiagonal α l = revzip (powerset_aux l) := rfl

@[simp] theorem antidiagonal_coe' (l : list α) :
  @antidiagonal α l = revzip (powerset_aux' l) :=
quot.sound revzip_powerset_aux_perm_aux'

/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp] theorem mem_antidiagonal {s : multiset α} {x : multiset α × multiset α} :
  x ∈ antidiagonal s ↔ x.1 + x.2 = s :=
quotient.induction_on s $ λ l, begin
  simp [antidiagonal_coe], refine ⟨λ h, revzip_powerset_aux h, λ h, _⟩,
  haveI := classical.dec_eq α,
  simp [revzip_powerset_aux_lemma l revzip_powerset_aux, h.symm],
  cases x with x₁ x₂,
  exact ⟨_, le_add_right _ _, by rw add_sub_cancel_left _ _⟩
end

@[simp] theorem antidiagonal_map_fst (s : multiset α) :
  (antidiagonal s).map prod.fst = powerset s :=
quotient.induction_on s $ λ l,
by simp [powerset_aux']

@[simp] theorem antidiagonal_map_snd (s : multiset α) :
  (antidiagonal s).map prod.snd = powerset s :=
quotient.induction_on s $ λ l,
by simp [powerset_aux']

@[simp] theorem antidiagonal_zero : @antidiagonal α 0 = {(0, 0)} := rfl

@[simp] theorem antidiagonal_cons (a : α) (s) : antidiagonal (a ::ₘ s) =
  map (prod.map id (cons a)) (antidiagonal s) +
  map (prod.map (cons a) id) (antidiagonal s) :=
quotient.induction_on s $ λ l, begin
  simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powerset_aux'_cons, cons_coe,
    coe_map, antidiagonal_coe', coe_add],
  rw [← zip_map, ← zip_map, zip_append, (_ : _++_=_)],
  {congr; simp}, {simp}
end

@[simp] theorem card_antidiagonal (s : multiset α) :
  card (antidiagonal s) = 2 ^ card s :=
by have := card_powerset s;
   rwa [← antidiagonal_map_fst, card_map] at this

lemma prod_map_add [comm_semiring β] {s : multiset α} {f g : α → β} :
  prod (s.map (λa, f a + g a)) =
  sum ((antidiagonal s).map (λp, (p.1.map f).prod * (p.2.map g).prod)) :=
begin
  refine s.induction_on _ _,
  { simp },
  { assume a s ih,
    have := @sum_map_mul_left α β _,
    simp [ih, add_mul, mul_comm, mul_left_comm (f a), mul_left_comm (g a), mul_assoc,
      sum_map_mul_left.symm],
    cc },
end

end multiset
