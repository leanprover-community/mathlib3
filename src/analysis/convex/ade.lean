/-
Copyright (c) 2023 Anne Baanen, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Heather Macbeth
-/
import tactic.linarith
import tactic.positivity
import tactic.field_simp
import tactic.interval_cases

attribute [field_simps] div_le_div_iff div_lt_div_iff div_lt_iff

meta def tactic.interactive.inv_ineq_tac_aux (loc) : tactic unit :=
(tactic.interactive.simp none none tt [] [`field_simps] loc { discharger := `[positivity] }) ;
(tactic.interactive.ring_nf none tactic.ring.normalize_mode.horner loc) ;
(tactic.interactive.norm_cast loc)

local postfix (name := parser.optional) `?`:9001 := optional

/-- A tactic for normalizing inqualities among inverses of natural numbers. -/
meta def tactic.interactive.inv_ineq_tac (loc)
  (tgt : interactive.parse (lean.parser.tk "using" *> interactive.types.texpr)?) : tactic unit :=
match tgt with
| none := tactic.interactive.inv_ineq_tac_aux loc
| (some e) :=
  let loc := interactive.loc.ns [none, `this] in
  (tactic.interactive.have `this none e) ;
  (tactic.interactive.inv_ineq_tac_aux loc) ;
  `[exact this]
end

example {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (H : (p:ℚ)⁻¹ + q⁻¹ + r⁻¹ = 1) :
  (p = 2 ∧ q = 3 ∧ r = 6) ∨ (p = 2 ∧ q = 4 ∧ r = 4) ∨ (p = 3 ∧ q = 3 ∧ r = 3) :=
begin
  have hq₀ : 0 < q := by linarith,
  have hr₀ : 0 < r := by linarith,
  have Hr₀ : 0 < (r:ℚ)⁻¹ := by positivity,
  have Hp : (p:ℚ)⁻¹ ≤ 2⁻¹ := by inv_ineq_tac using hp,
  have Hpq : (q:ℚ)⁻¹ ≤ p⁻¹ := by inv_ineq_tac using hpq,
  have Hqr : (r:ℚ)⁻¹ ≤ q⁻¹ := by inv_ineq_tac using hqr,
  have : (1:ℚ)/3 ≤ p⁻¹ := by linarith only [H, Hpq, Hqr],
  have : ((1:ℚ) - 2⁻¹) / 2 ≤ q⁻¹ := by linarith only [H, Hp, Hqr],
  have : (q:ℚ)⁻¹ < 1/2 := by linarith only [H, Hr₀, Hpq],
  have Hq : (q:ℚ)⁻¹ ≤ 3⁻¹ := by inv_ineq_tac using this,
  have : (1:ℚ) - 2⁻¹ - 3⁻¹ ≤ r⁻¹ := by linarith only [H, Hp, Hq],
  inv_ineq_tac at *,
  interval_cases p; interval_cases q; interval_cases r; norm_num at H; tauto,
end

example {p q r : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (H : (p:ℚ)⁻¹ + q⁻¹ + r⁻¹ = 1) :
  (p = 2 ∧ q = 3 ∧ r = 6) ∨ (p = 2 ∧ q = 4 ∧ r = 4) ∨ (p = 3 ∧ q = 3 ∧ r = 3) :=
begin
  have hq₀ : 0 < q := by linarith,
  have hr₀ : 0 < r := by linarith,
  have Hq₀ : 0 < (q:ℚ)⁻¹ := by positivity,
  have Hr₀ : 0 < (r:ℚ)⁻¹ := by positivity,
  have Hpq : (q:ℚ)⁻¹ ≤ p⁻¹ := by inv_ineq_tac using hpq,
  have Hqr : (r:ℚ)⁻¹ ≤ q⁻¹ := by inv_ineq_tac using hqr,
  -- step 1a
  have : (1:ℚ)/3 ≤ p⁻¹ := by linarith only [H, Hpq, Hqr],
  -- step 1b
  have : (p:ℚ)⁻¹ < 1 := by linarith only [H, Hr₀, Hq₀],
  have Hp : (p:ℚ)⁻¹ ≤ 2⁻¹ := by inv_ineq_tac using this,
  -- step 2a
  have : ((1:ℚ) - 2⁻¹) / 2 ≤ q⁻¹ := by linarith only [H, Hp, Hqr],
  -- step 2b
  have : (q:ℚ)⁻¹ < 1/2 := by linarith only [H, Hr₀, Hpq],
  have Hq : (q:ℚ)⁻¹ ≤ 3⁻¹ := by inv_ineq_tac using this,
  -- step 3a
  have : (1:ℚ) - 2⁻¹ - 3⁻¹ ≤ r⁻¹ := by linarith only [H, Hp, Hq],
  inv_ineq_tac at *,
  interval_cases p; interval_cases q; interval_cases r; norm_num at H; tauto,
end

example {p q r : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (H : (p:ℚ)⁻¹ + q⁻¹ + r⁻¹ > 1) :
  p = 1 ∨ -- A
  (p = 2 ∧ q = 2) ∨ -- D
  (p = 2 ∧ q = 3 ∧ r = 3) ∨ -- E₆
  (p = 2 ∧ q = 3 ∧ r = 4) ∨ -- E₇
  (p = 2 ∧ q = 3 ∧ r = 5) := -- E₈
begin
  have hq₀ : 0 < q := by linarith,
  have hr₀ : 0 < r := by linarith,
  have Hpq : (q:ℚ)⁻¹ ≤ p⁻¹ := by inv_ineq_tac using hpq,
  have Hqr : (r:ℚ)⁻¹ ≤ q⁻¹ := by inv_ineq_tac using hqr,
  obtain rfl | (hp' : 2 ≤ p) := eq_or_lt_of_le hp,
  { tauto },
  have Hp : (p:ℚ)⁻¹ ≤ 2⁻¹ := by inv_ineq_tac using hp',
  obtain rfl | (hq : 3 ≤ q) := eq_or_lt_of_le (by linarith : 2 ≤ q),
  { interval_cases p ; tauto, },
  have Hq : (q:ℚ)⁻¹ ≤ 3⁻¹ := by inv_ineq_tac using hq,
  have : (1:ℚ)/3 ≤ p⁻¹ := by linarith only [H, Hpq, Hqr],
  have : ((1:ℚ) - 2⁻¹) / 2 ≤ q⁻¹ := by linarith only [H, Hp, Hqr],
  have : (1:ℚ) - 2⁻¹ - 3⁻¹ ≤ r⁻¹ := by linarith only [H, Hp, Hq],
  inv_ineq_tac at *,
  interval_cases p; interval_cases q; interval_cases r; norm_num at H; tauto,
end
