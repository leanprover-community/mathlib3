/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import ring_theory.algebraic

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.
-/

variables {R : Type*} [comm_ring R]

namespace ideal

open polynomial
open submodule

section comm_ring
variables {S : Type*} [comm_ring S] {f : R →+* S} {I : ideal S}

lemma coeff_zero_mem_comap_of_root_mem {r : S} (hr : r ∈ I) {p : polynomial R}
  (hp : p.eval₂ f r = 0) : p.coeff 0 ∈ I.comap f :=
begin
  rw [←p.div_X_mul_X_add, eval₂_add, eval₂_C, eval₂_mul, eval₂_X] at hp,
  refine mem_comap.mpr ((I.add_mem_iff_right _).mp (by simpa only [←hp] using I.zero_mem)),
  exact I.mul_mem_left hr
end
end comm_ring

section integral_domain
variables {S : Type*} [integral_domain S] {f : R →+* S} {I : ideal S}

lemma exists_coeff_ne_zero_mem_comap_of_root_mem {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I)
  {p : polynomial R} : ∀ (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0),
  ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f :=
begin
  refine p.rec_on_horner _ _ _,
  { intro h, contradiction },
  { intros p a coeff_eq_zero a_ne_zero ih p_ne_zero hp,
    refine ⟨0, _, coeff_zero_mem_comap_of_root_mem hr hp⟩,
    simp [coeff_eq_zero, a_ne_zero] },
  { intros p p_nonzero ih mul_nonzero hp,
    rw [eval₂_mul, eval₂_X, mul_eq_zero] at hp,
    obtain ⟨i, hi, mem⟩ := ih p_nonzero (or.resolve_right hp r_ne_zero),
    refine ⟨i + 1, _, _⟩; simp [hi, mem] }
end

lemma comap_ne_bot_of_root_mem {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I)
  {p : polynomial R} (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0) :
  I.comap f ≠ ⊥ :=
λ h, let ⟨i, hi, mem⟩ := exists_coeff_ne_zero_mem_comap_of_root_mem r_ne_zero hr p_ne_zero hp in
absurd ((mem_bot _).mp (eq_bot_iff.mp h mem)) hi

variables [algebra R S]

lemma comap_ne_bot_of_algebraic_mem {I : ideal S} {x : S}
  (x_ne_zero : x ≠ 0) (x_mem : x ∈ I) (hx : is_algebraic R x) : I.comap (algebra_map R S) ≠ ⊥ :=
let ⟨p, p_ne_zero, hp⟩ := hx
in comap_ne_bot_of_root_mem x_ne_zero x_mem p_ne_zero hp

lemma comap_ne_bot_of_integral_mem [nontrivial R] {I : ideal S} {x : S}
  (x_ne_zero : x ≠ 0) (x_mem : x ∈ I) (hx : is_integral R x) : I.comap (algebra_map R S) ≠ ⊥ :=
comap_ne_bot_of_algebraic_mem x_ne_zero x_mem (hx.is_algebraic R)

lemma integral_closure.comap_ne_bot [nontrivial R] {I : ideal (integral_closure R S)}
  (I_ne_bot : I ≠ ⊥) : I.comap (algebra_map R (integral_closure R S)) ≠ ⊥ :=
let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot in
comap_ne_bot_of_integral_mem x_ne_zero x_mem (integral_closure.is_integral x)

lemma integral_closure.eq_bot_of_comap_eq_bot [nontrivial R] {I : ideal (integral_closure R S)} :
  I.comap (algebra_map R (integral_closure R S)) = ⊥ → I = ⊥ :=
imp_of_not_imp_not _ _ integral_closure.comap_ne_bot

end integral_domain

end ideal
