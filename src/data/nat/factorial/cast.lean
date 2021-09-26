/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.nat.choose.basic
import ring_theory.polynomial.pochhammer

/-!
# Cast of factorials

This file allows calculating factorials (including ascending and descending ones) as elements of a semiring.
-/

open nat
open_locale nat

variables  (S : Type*) [semiring S] (a b : ℕ)

lemma cast_asc_factorial :
  (a.asc_factorial b : S) = (pochhammer S b).eval (a + 1) :=
by rw [←pochhammer_nat_eq_asc_factorial, pochhammer_eval_cast, nat.cast_add, nat.cast_one]

lemma cast_desc_factorial :
  (a.desc_factorial b : S) = (pochhammer S b).eval (a - (b - 1) : ℕ) :=
begin
  rw [←pochhammer_eval_cast, pochhammer_nat_eq_desc_factorial],
  cases b,
  { simp_rw desc_factorial_zero },
  simp_rw succ_sub_one,
  obtain h | h := le_total a b,
  { rw [desc_factorial_of_lt (lt_succ_of_le h), desc_factorial_of_lt (lt_succ_of_le _)],
    rw [sub_eq_zero_of_le h, zero_add] },
  { rw nat.sub_add_cancel h }
end

lemma cast_factorial :
  (a! : S) = (pochhammer S b).eval 1 :=
by rw [←zero_asc_factorial, cast_asc_factorial, zero_add]

lemma cast_desc_factorial_two :
  (a.desc_factorial 2 : S) = a * (a - 1) :=
sorry
