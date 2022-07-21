/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import set_theory.ordinal.arithmetic

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

noncomputable theory

universe u

open order

namespace ordinal

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_eliminator] noncomputable def CNF_rec {b : ordinal} (hb : b ≠ 0)
  {C : ordinal → Sort*} (H0 : C 0) (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : ∀ o, C o
| o :=
  if ho : o = 0 then by rwa ho else
  have _, from mod_opow_log_lt_self hb ho,
  H o ho (CNF_rec (o % b ^ log b o))
using_well_founded {dec_tac := `[assumption]}

@[simp] theorem CNF_rec_zero {b} (hb) {C H0 H} : @CNF_rec b hb C H0 H 0 = H0 :=
by rw [CNF_rec, dif_pos rfl]; refl

@[simp] theorem CNF_rec_ne_zero {b} (hb) {C H0 H o} (ho) :
  @CNF_rec b hb C H0 H o = H o ho (@CNF_rec b hb C H0 H _) :=
by rw [CNF_rec, dif_neg ho]

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = []`, `CNF b 0 = []`, and `CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot] def CNF (b o : ordinal) : list (ordinal × ordinal) :=
if hb : b = 0 then [] else
CNF_rec hb [] (λ o o0 IH, (log b o, o / b ^ log b o) :: IH) o

@[simp] theorem zero_CNF (o) : CNF 0 o = [] :=
dif_pos rfl

@[simp] theorem CNF_zero (b) : CNF b 0 = [] :=
if hb : b = 0 then dif_pos hb else (dif_neg hb).trans $ CNF_rec_zero _

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : ordinal} (hb : b ≠ 0) (ho : o ≠ 0) :
  CNF b o = (log b o, o / b ^ log b o) :: CNF b (o % b ^ log b o) :=
by unfold CNF; rw [dif_neg hb, dif_neg hb, CNF_rec_ne_zero hb ho]

@[simp] theorem one_CNF {o : ordinal} (ho : o ≠ 0) : CNF 1 o = [(0, o)] :=
by rw [CNF_ne_zero ordinal.one_ne_zero ho, log_of_not_one_lt_left (irrefl _), opow_zero, mod_one,
       CNF_zero, div_one]

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr {b : ordinal} (hb : b ≠ 0) (o) :
  (CNF b o).foldr (λ p r, b ^ p.1 * p.2 + r) 0 = o :=
CNF_rec hb (by rw CNF_zero; refl)
  (λ o ho IH, by rw [CNF_ne_zero hb ho, list.foldr_cons, IH, div_add_mod]) o

/-- This theorem exists to factor out commonalities between the proofs of `ordinal.CNF_pairwise` and
`ordinal.CNF_fst_le_log`. -/
private theorem CNF_pairwise_aux (b o : ordinal.{u}) :
  (∀ p : ordinal × ordinal, p ∈ CNF b o → p.1 ≤ log b o) ∧ (CNF b o).pairwise (λ p q, q.1 < p.1) :=
begin
  by_cases hb : b = 0,
  { simp only [hb, zero_CNF, list.pairwise.nil, and_true], exact λ _, false.elim },
  cases lt_or_eq_of_le (one_le_iff_ne_zero.2 hb) with hb' hb',
  { refine CNF_rec hb _ _ o,
    { simp only [CNF_zero, list.pairwise.nil, and_true], exact λ _, false.elim },
    intros o ho IH, cases IH with IH₁ IH₂,
    simp only [CNF_ne_zero hb ho, list.forall_mem_cons, list.pairwise_cons, IH₂, and_true],
    refine ⟨⟨le_rfl, λ p m, _⟩, λ p m, _⟩,
    { exact (IH₁ p m).trans (log_mono_right _ $ le_of_lt $ mod_opow_log_lt_self hb ho) },
    { refine (IH₁ p m).trans_lt ((lt_opow_iff_log_lt hb' _).1 _),
      { rw ordinal.pos_iff_ne_zero, intro e,
        rw e at m, simpa only [CNF_zero] using m },
      { exact mod_lt _ (opow_ne_zero _ hb) } } },
  { by_cases ho : o = 0,
    { simp only [ho, CNF_zero, list.pairwise.nil, and_true], exact λ _, false.elim },
    rw [← hb', one_CNF ho],
    simp only [list.mem_singleton, log_one_left, forall_eq, le_refl, true_and,
      list.pairwise_singleton] }
end

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_pairwise (b o : ordinal.{u}) :
  (CNF b o).pairwise (λ p q : ordinal × ordinal, q.1 < p.1) :=
(CNF_pairwise_aux _ _).2

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem CNF_fst_le_log {b o : ordinal.{u}} :
  ∀ {p : ordinal × ordinal}, p ∈ CNF b o → p.1 ≤ log b o :=
(CNF_pairwise_aux _ _).1

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
theorem CNF_fst_le {b o : ordinal.{u}} {p : ordinal × ordinal} (hp : p ∈ CNF b o) : p.1 ≤ o :=
(CNF_fst_le_log hp).trans (log_le_self _ _)

/-- This theorem exists to factor out commonalities between the proofs of `ordinal.CNF_snd_lt` and
`ordinal.CNF_lt_snd`. -/
private theorem CNF_snd_lt_aux {b o : ordinal.{u}} (hb' : 1 < b) :
  ∀ {p : ordinal × ordinal}, p ∈ CNF b o → p.2 < b ∧ 0 < p.2 :=
begin
  have hb := (zero_lt_one.trans hb').ne',
  refine CNF_rec hb (λ _, by { rw CNF_zero, exact false.elim }) (λ o ho IH, _) o,
  simp only [CNF_ne_zero hb ho, list.mem_cons_iff, forall_eq_or_imp, iff_true_intro @IH, and_true],
  nth_rewrite 1 ←@succ_le_iff,
  rw [div_lt (opow_ne_zero _ hb), ←opow_succ, le_div (opow_ne_zero _ hb), succ_zero, mul_one],
  refine ⟨lt_opow_succ_log_self hb' _, opow_log_le_self _ _⟩,
  rwa ordinal.pos_iff_ne_zero
end

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem CNF_snd_lt {b o : ordinal.{u}} (hb : 1 < b) {p : ordinal × ordinal} (hp : p ∈ CNF b o) :
  p.2 < b :=
(CNF_snd_lt_aux hb hp).1

/-- Every coefficient in a Cantor normal form is positive. -/
theorem CNF_lt_snd {b o : ordinal.{u}} (hb : 1 < b) {p : ordinal × ordinal} (hp : p ∈ CNF b o) :
  0 < p.2 :=
(CNF_snd_lt_aux hb hp).2

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_sorted (b o : ordinal) : ((CNF b o).map prod.fst).sorted (>) :=
by { rw [list.sorted, list.pairwise_map], exact CNF_pairwise b o }

end ordinal
