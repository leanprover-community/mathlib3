/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Mario Carneiro
-/
import data.rat.cast
import data.rat.meta_defs

/-!
# `norm_num`

Evaluating arithmetic expressions including *, +, -, ^, ≤
-/

universes u v w

namespace tactic

meta def refl_conv (e : expr) : tactic (expr × expr) :=
do p ← mk_eq_refl e, return (e, p)

meta def trans_conv (t₁ t₂ : expr → tactic (expr × expr)) (e : expr) :
  tactic (expr × expr) :=
(do (e₁, p₁) ← t₁ e,
  (do (e₂, p₂) ← t₂ e₁,
    p ← mk_eq_trans p₁ p₂, return (e₂, p)) <|>
  return (e₁, p₁)) <|> t₂ e

end tactic

open tactic

namespace norm_num
variable {α : Type u}

meta inductive match_numeral_result
| zero | one | bit0 (e : expr) | bit1 (e : expr)

meta def match_numeral : expr → option match_numeral_result
| `(bit0 %%e) := match_numeral_result.bit0 e
| `(bit1 %%e) := match_numeral_result.bit1 e
| `(@has_zero.zero _ _) := match_numeral_result.zero
| `(@has_one.one _ _) := match_numeral_result.one
| _ := none

theorem zero_succ {α} [semiring α] : (0 + 1 : α) = 1 := zero_add _
theorem one_succ {α} [semiring α] : (1 + 1 : α) = 2 := rfl
theorem bit0_succ {α} [semiring α] (a : α) : bit0 a + 1 = bit1 a := rfl
theorem bit1_succ {α} [semiring α] (a b : α) (h : a + 1 = b) : bit1 a + 1 = bit0 b :=
h ▸ by simp [bit1, bit0, add_left_comm]

section
open match_numeral_result
meta def prove_succ : instance_cache → expr → expr → tactic (instance_cache × expr)
| c e r := do m ← match_numeral e, match m with
  | zero := c.mk_app ``zero_succ []
  | one := c.mk_app ``one_succ []
  | bit0 e := c.mk_app ``bit0_succ [e]
  | bit1 e := do
    let r := r.app_arg,
    (c, p) ← prove_succ c e r,
    c.mk_app ``bit1_succ [e, r, p]
  end
end

theorem zero_adc {α} [semiring α] (a b : α) (h : a + 1 = b) : 0 + a + 1 = b := by rwa zero_add
theorem adc_zero {α} [semiring α] (a b : α) (h : a + 1 = b) : a + 0 + 1 = b := by rwa add_zero
theorem one_add {α} [semiring α] (a b : α) (h : a + 1 = b) : 1 + a = b := by rwa add_comm
theorem add_bit0_bit0 {α} [semiring α] (a b c : α) (h : a + b = c) : bit0 a + bit0 b = bit0 c :=
h ▸ by simp [bit0, add_left_comm]
theorem add_bit0_bit1 {α} [semiring α] (a b c : α) (h : a + b = c) : bit0 a + bit1 b = bit1 c :=
h ▸ by simp [bit0, bit1, add_left_comm]
theorem add_bit1_bit0 {α} [semiring α] (a b c : α) (h : a + b = c) : bit1 a + bit0 b = bit1 c :=
h ▸ by simp [bit0, bit1, add_left_comm, add_comm]
theorem add_bit1_bit1 {α} [semiring α] (a b c : α) (h : a + b + 1 = c) : bit1 a + bit1 b = bit0 c :=
h ▸ by simp [bit0, bit1, add_left_comm, add_comm]
theorem adc_one_one {α} [semiring α] : (1 + 1 + 1 : α) = 3 := rfl
theorem adc_bit0_one {α} [semiring α] (a b : α) (h : a + 1 = b) : bit0 a + 1 + 1 = bit0 b :=
h ▸ by simp [bit0, add_left_comm]
theorem adc_one_bit0 {α} [semiring α] (a b : α) (h : a + 1 = b) : 1 + bit0 a + 1 = bit0 b :=
h ▸ by simp [bit0, add_left_comm]
theorem adc_bit1_one {α} [semiring α] (a b : α) (h : a + 1 = b) : bit1 a + 1 + 1 = bit1 b :=
h ▸ by simp [bit1, bit0, add_left_comm]
theorem adc_one_bit1 {α} [semiring α] (a b : α) (h : a + 1 = b) : 1 + bit1 a + 1 = bit1 b :=
h ▸ by simp [bit1, bit0, add_left_comm]
theorem adc_bit0_bit0 {α} [semiring α] (a b c : α) (h : a + b = c) : bit0 a + bit0 b + 1 = bit1 c :=
h ▸ by simp [bit1, bit0, add_left_comm]
theorem adc_bit1_bit0 {α} [semiring α] (a b c : α) (h : a + b + 1 = c) : bit1 a + bit0 b + 1 = bit0 c :=
h ▸ by simp [bit1, bit0, add_left_comm]
theorem adc_bit0_bit1 {α} [semiring α] (a b c : α) (h : a + b + 1 = c) : bit0 a + bit1 b + 1 = bit0 c :=
h ▸ by simp [bit1, bit0, add_left_comm]
theorem adc_bit1_bit1 {α} [semiring α] (a b c : α) (h : a + b + 1 = c) : bit1 a + bit1 b + 1 = bit1 c :=
h ▸ by simp [bit1, bit0, add_left_comm]

section
open match_numeral_result

meta mutual def prove_add_nat, prove_adc_nat
with prove_add_nat : instance_cache → expr → expr → expr → tactic (instance_cache × expr)
| c a b r := do
  match match_numeral a, match_numeral b with
  | some zero, _ := c.mk_app ``zero_add [b]
  | _, some zero := c.mk_app ``add_zero [a]
  | _, some one := prove_succ c a r
  | some one, _ := do (c, p) ← prove_succ c b r, c.mk_app ``one_add [b, r, p]
  | some (bit0 a), some (bit0 b) := do let r := r.app_arg, (c, p) ← prove_add_nat c a b r, c.mk_app ``add_bit0_bit0 [a, b, r, p]
  | some (bit0 a), some (bit1 b) := do let r := r.app_arg, (c, p) ← prove_add_nat c a b r, c.mk_app ``add_bit0_bit1 [a, b, r, p]
  | some (bit1 a), some (bit0 b) := do let r := r.app_arg, (c, p) ← prove_add_nat c a b r, c.mk_app ``add_bit1_bit0 [a, b, r, p]
  | some (bit1 a), some (bit1 b) := do let r := r.app_arg, (c, p) ← prove_adc_nat c a b r, c.mk_app ``add_bit1_bit1 [a, b, r, p]
  | _, _ := failed
  end
with prove_adc_nat : instance_cache → expr → expr → expr → tactic (instance_cache × expr)
| c a b r := do
  match match_numeral a, match_numeral b with
  | some zero, _ := do (c, p) ← prove_succ c b r, c.mk_app ``zero_adc [b, r, p]
  | _, some zero := do (c, p) ← prove_succ c b r, c.mk_app ``adc_zero [b, r, p]
  | some one, some one := c.mk_app ``adc_one_one []
  | some (bit0 a), some one := do let r := r.app_arg, (c, p) ← prove_succ c a r, c.mk_app ``adc_bit0_one [a, r, p]
  | some one, some (bit0 b) := do let r := r.app_arg, (c, p) ← prove_succ c b r, c.mk_app ``adc_one_bit0 [b, r, p]
  | some (bit1 a), some one := do let r := r.app_arg, (c, p) ← prove_succ c a r, c.mk_app ``adc_bit1_one [a, r, p]
  | some one, some (bit1 b) := do let r := r.app_arg, (c, p) ← prove_succ c b r, c.mk_app ``adc_one_bit1 [b, r, p]
  | some (bit0 a), some (bit0 b) := do let r := r.app_arg, (c, p) ← prove_add_nat c a b r, c.mk_app ``adc_bit0_bit0 [a, b, r, p]
  | some (bit0 a), some (bit1 b) := do let r := r.app_arg, (c, p) ← prove_adc_nat c a b r, c.mk_app ``adc_bit0_bit1 [a, b, r, p]
  | some (bit1 a), some (bit0 b) := do let r := r.app_arg, (c, p) ← prove_adc_nat c a b r, c.mk_app ``adc_bit1_bit0 [a, b, r, p]
  | some (bit1 a), some (bit1 b) := do let r := r.app_arg, (c, p) ← prove_adc_nat c a b r, c.mk_app ``adc_bit1_bit1 [a, b, r, p]
  | _, _ := failed
  end

meta def prove_add_nat' (c : instance_cache) (a b : expr) : tactic (instance_cache × expr × expr) := do
  na ← a.to_nat,
  nb ← b.to_nat,
  r ← expr.of_nat c.α (na + nb),
  (c, p) ← prove_add_nat c a b r,
  return (c, r, p)

end

theorem mul_bit0' {α} [semiring α] (a b c : α) (h : a * b = c) :
  a * bit0 b = bit0 c := h ▸ by simp [bit0, mul_add]
theorem mul_bit1' {α} [semiring α] (a b c d : α) (h : a * b = c) (h₂ : bit0 c + a = d) :
  a * bit1 b = d := h₂ ▸ h ▸ by simp [bit1, bit0, mul_add]

section
open match_numeral_result

meta def prove_mul_nat : instance_cache → expr → expr → tactic (instance_cache × expr × expr)
| ic a b :=
  match match_numeral a, match_numeral b with
  | some zero, _ := do
    (ic, z) ← ic.mk_app ``has_zero.zero [],
    (ic, p) ← ic.mk_app ``zero_mul [b],
    return (ic, z, p)
  | _, some zero := do
    (ic, z) ← ic.mk_app ``has_zero.zero [],
    (ic, p) ← ic.mk_app ``mul_zero [b],
    return (ic, z, p)
  | some one, _ := do (ic, p) ← ic.mk_app ``one_mul [b], return (ic, b, p)
  | _, some one := do (ic, p) ← ic.mk_app ``mul_one [a], return (ic, a, p)
  | _, some (bit0 b) := do
    (ic, c, p) ← prove_mul_nat ic a b,
    (ic, p) ← ic.mk_app ``mul_bit0' [a, b, c, p],
    (ic, c') ← ic.mk_app ``_root_.bit0 [c],
    return (ic, c', p)
  | _, some (bit1 b) := do
    (ic, c, p) ← prove_mul_nat ic a b,
    (ic, c') ← ic.mk_app ``_root_.bit0 [c],
    (ic, d, p₂) ← prove_add_nat' ic c' a,
    (ic, p) ← ic.mk_app ``mul_bit1' [a, b, c, d, p, p₂],
    return (ic, d, p)
  | _, _ := failed
  end

end

meta def prove_pos : instance_cache → expr → tactic (instance_cache × expr)
| c `(has_one.one) := c.mk_app ``zero_lt_one []
| c `(bit0 %%e)      := do (c, p) ← prove_pos c e, c.mk_app ``bit0_pos [e, p]
| c `(bit1 %%e)      := do (c, p) ← prove_pos c e, c.mk_app ``bit1_pos' [e, p]
| c `(%%e₁ / %%e₂)   := do
  (c, p₁) ← prove_pos c e₁, (c, p₂) ← prove_pos c e₂,
  c.mk_app ``div_pos_of_pos_of_pos [e₁, e₂, p₁, p₂]
| c e := failed

meta def match_neg : expr → option expr
| `(- %%e) := some e
| _ := none

theorem ne_zero_of_pos {α} [ordered_add_comm_group α] (a : α) : 0 < a → a ≠ 0 := ne_of_gt
theorem ne_zero_neg {α} [add_group α] (a : α) : a ≠ 0 → -a ≠ 0 := mt neg_eq_zero.1

meta def prove_ne_zero : instance_cache → expr → tactic (instance_cache × expr)
| c a :=
  match match_neg a with
  | some a := do (c, p) ← prove_ne_zero c a, c.mk_app ``ne_zero_neg [a, p]
  | none := do (c, p) ← prove_pos c a, c.mk_app ``ne_zero_of_pos [a, p]
  end

theorem clear_denom_div {α} [division_ring α] (a b b' c d : α)
  (h₀ : b ≠ 0) (h₁ : b * b' = d) (h₂ : a * b' = c) : (a / b) * d = c :=
by rwa [← h₁, ← mul_assoc, div_mul_cancel _ h₀]

meta def prove_clear_denom (c : instance_cache) (a d : expr) (na : ℚ) (nd : ℕ) : tactic (instance_cache × expr × expr) :=
if na.denom = 1 then
  prove_mul_nat c a d
else do
  [α, _, a, b] ← return a.get_app_args,
  b' ← expr.of_nat α (nd / na.denom),
  (c, p₀) ← prove_ne_zero c b,
  (c, _, p₁) ← prove_mul_nat c b b',
  (c, r, p₂) ← prove_mul_nat c a b',
  (c, p) ← c.mk_app ``clear_denom_div [a, b, b', r, d, p₀, p₁, p₂],
  return (c, r, p)

theorem clear_denom_add {α} [division_ring α] (a a' b b' c c' d : α)
  (h₀ : d ≠ 0) (ha : a * d = a') (hb : b * d = b') (hc : c * d = c')
  (h : a' + b' = c') : a + b = c :=
mul_right_cancel' h₀ $ by rwa [add_mul, ha, hb, hc]

meta def prove_add_nonneg_rat (ic : instance_cache) (a b c : expr) (na nb nc : ℚ) : tactic (instance_cache × expr) :=
if na.denom = 1 ∧ nb.denom = 1 then
  prove_add_nat ic a b c
else do
  let nd := na.denom.lcm nb.denom,
  d ← expr.of_nat ic.α nd,
  (ic, p₀) ← prove_ne_zero ic d,
  (ic, a', pa) ← prove_clear_denom ic a d na nd,
  (ic, b', pb) ← prove_clear_denom ic b d nb nd,
  (ic, c', pc) ← prove_clear_denom ic c d nc nd,
  (ic, p) ← prove_add_nat ic a' b' c',
  ic.mk_app ``clear_denom_add [a, a', b, b', c, c', d, p₀, pa, pb, pc, p]

theorem add_pos_neg_pos {α} [add_group α] (a b c : α) (h : c + b = a) : a + -b = c :=
h ▸ by simp
theorem add_pos_neg_neg {α} [add_group α] (a b c : α) (h : c + a = b) : a + -b = -c :=
h ▸ by simp
theorem add_neg_pos_pos {α} [add_group α] (a b c : α) (h : a + c = b) : -a + b = c :=
h ▸ by simp
theorem add_neg_pos_neg {α} [add_group α] (a b c : α) (h : b + c = a) : -a + b = -c :=
h ▸ by simp
theorem add_neg_neg {α} [add_group α] (a b c : α) (h : b + a = c) : -a + -b = -c :=
h ▸ by simp

meta def prove_add_rat (ic : instance_cache) (ea eb ec : expr) (a b c : ℚ) : tactic (instance_cache × expr) :=
match match_neg ea, match_neg eb, match_neg ec with
| some ea, some eb, some ec := do
  (ic, p) ← prove_add_nonneg_rat ic eb ea ec b a c,
  ic.mk_app ``add_neg_neg [ea, eb, ec, p]
| some ea, none, some ec := do
  (ic, p) ← prove_add_nonneg_rat ic eb ec ea b c a,
  ic.mk_app ``add_neg_pos_neg [ea, eb, ec, p]
| some ea, none, none := do
  (ic, p) ← prove_add_nonneg_rat ic ea ec eb a c b,
  ic.mk_app ``add_neg_pos_pos [ea, eb, ec, p]
| none, some eb, some ec := do
  (ic, p) ← prove_add_nonneg_rat ic ec ea eb c a b,
  ic.mk_app ``add_pos_neg_neg [ea, eb, ec, p]
| none, some eb, none := do
  (ic, p) ← prove_add_nonneg_rat ic ec eb ea c b a,
  ic.mk_app ``add_pos_neg_pos [ea, eb, ec, p]
| _, _, _ := prove_add_nonneg_rat ic ea eb ec a b c
end

meta def prove_add_rat' (ic : instance_cache) (a b : expr) : tactic (instance_cache × expr × expr) := do
  na ← a.to_rat,
  nb ← b.to_rat,
  let nc := na + nb,
  c ← expr.of_rat ic.α nc,
  (ic, p) ← prove_add_rat ic a b c na nb nc,
  return (ic, c, p)

theorem clear_denom_simple_nat {α} [division_ring α] (a : α) :
  (1:α) ≠ 0 ∧ a * 1 = a := ⟨one_ne_zero, mul_one _⟩
theorem clear_denom_simple_div {α} [division_ring α] (a b : α) (h : b ≠ 0) :
  b ≠ 0 ∧ a / b * b = a := ⟨h, div_mul_cancel _ h⟩

meta def prove_clear_denom_simple (c : instance_cache) (a : expr) (na : ℚ) : tactic (instance_cache × expr × expr × expr) :=
if na.denom = 1 then do
  (c, d) ← c.mk_app ``has_one.one [],
  (c, p) ← c.mk_app ``clear_denom_simple_nat [a],
  return (c, d, a, p)
else do
  [α, _, a, b] ← return a.get_app_args,
  (c, p₀) ← prove_ne_zero c b,
  (c, p) ← c.mk_app ``clear_denom_simple_div [a, b, p₀],
  return (c, b, a, p)

theorem clear_denom_mul {α} [field α] (a a' b b' c c' d₁ d₂ d : α)
  (ha : d₁ ≠ 0 ∧ a * d₁ = a') (hb : d₂ ≠ 0 ∧ b * d₂ = b')
  (hc : c * d = c') (hd : d₁ * d₂ = d)
  (h : a' * b' = c') : a * b = c :=
mul_right_cancel' ha.1 $ mul_right_cancel' hb.1 $
by rw [mul_assoc c, hd, hc, ← h, ← ha.2, ← hb.2, ← mul_assoc, mul_right_comm a]

meta def prove_mul_nonneg_rat (ic : instance_cache) (a b : expr) (na nb : ℚ) : tactic (instance_cache × expr × expr) :=
if na.denom = 1 ∧ nb.denom = 1 then
  prove_mul_nat ic a b
else do
  let nc := na * nb, c ← expr.of_rat ic.α nc,
  (ic, d₁, a', pa) ← prove_clear_denom_simple ic a na,
  (ic, d₂, b', pb) ← prove_clear_denom_simple ic b nb,
  (ic, d, pd) ← prove_mul_nat ic d₁ d₂, nd ← d.to_nat,
  (ic, c', pc) ← prove_clear_denom ic c d nc nd,
  (ic, _, p) ← prove_mul_nat ic a' b',
  (ic, p) ← ic.mk_app ``clear_denom_mul [a, a', b, b', c, c', d₁, d₂, d, pa, pb, pc, pd, p],
  return (ic, c, p)

theorem mul_neg_pos {α} [ring α] (a b c : α) (h : a * b = c) : -a * b = -c := h ▸ by simp
theorem mul_pos_neg {α} [ring α] (a b c : α) (h : a * b = c) : a * -b = -c := h ▸ by simp
theorem mul_neg_neg {α} [ring α] (a b c : α) (h : a * b = c) : -a * -b = c := h ▸ by simp

meta def prove_mul_rat (ic : instance_cache) (a b : expr) (na nb : ℚ) : tactic (instance_cache × expr × expr) :=
match match_neg a, match_neg b with
| some a, some b := do
  (ic, c, p) ← prove_mul_nonneg_rat ic a b na nb,
  (ic, p) ← ic.mk_app ``mul_neg_neg [a, b, c, p],
  return (ic, c, p)
| some a, none := do
  (ic, c, p) ← prove_mul_nonneg_rat ic a b na nb,
  (ic, p) ← ic.mk_app ``mul_neg_pos [a, b, c, p],
  (ic, c') ← ic.mk_app ``has_neg.neg [c],
  return (ic, c', p)
| none, some b := do
  (ic, c, p) ← prove_mul_nonneg_rat ic a b na nb,
  (ic, p) ← ic.mk_app ``mul_pos_neg [a, b, c, p],
  (ic, c') ← ic.mk_app ``has_neg.neg [c],
  return (ic, c', p)
| none, none := prove_mul_nonneg_rat ic a b na nb
end

theorem inv_neg {α} [division_ring α] (a b : α) (h : a⁻¹ = b) : (-a)⁻¹ = -b :=
h ▸ by simp only [inv_eq_one_div, one_div_neg_eq_neg_one_div]

theorem inv_one {α} [division_ring α] : (1 : α)⁻¹ = 1 := one_inv_eq
theorem inv_one_div {α} [division_ring α] (a : α) : (1 / a)⁻¹ = a :=
by rw [one_div_eq_inv, inv_inv']
theorem inv_div_one {α} [division_ring α] (a : α) : a⁻¹ = 1 / a :=
inv_eq_one_div _
theorem inv_div {α} [division_ring α] (a b : α) : (a / b)⁻¹ = b / a :=
by simp only [inv_eq_one_div, one_div_div]

meta def prove_inv : instance_cache → expr → ℚ → tactic (instance_cache × expr × expr)
| ic e n :=
  if n = 0 then do
    (ic, p) ← ic.mk_app ``inv_zero [],
    return (ic, e, p)
  else match match_neg e with
  | some e := do
    (ic, e', p) ← prove_inv ic e (-n),
    (ic, r) ← ic.mk_app ``has_neg.neg [e'],
    (ic, p) ← ic.mk_app ``inv_neg [e, e'],
    return (ic, r, p)
  | none :=
    if n.num = 1 then
      if n.denom = 1 then do
        (ic, p) ← ic.mk_app ``one_inv_eq [],
        return (ic, e, p)
      else do
        (ic, p) ← ic.mk_app ``inv_one_div [e],
        return (ic, e.app_arg, p)
    else if n.denom = 1 then do
      (ic, p) ← ic.mk_app ``inv_div_one [e],
      e ← infer_type p,
      return (ic, e.app_arg, p)
    else do
      [_, _, a, b] ← return e.get_app_args,
      (ic, e') ← ic.mk_app ``has_div.div [b, a],
      (ic, p) ← ic.mk_app ``inv_div [a, b],
      return (ic, e', p)
  end

theorem div_eq {α} [division_ring α] (a b b' c : α)
  (hb : b⁻¹ = b') (h : a * b' = c) : a / b = c := by rwa ← hb at h

meta def prove_div (ic : instance_cache) (a b : expr) (na nb : ℚ) : tactic (instance_cache × expr × expr) :=
do (ic, b', pb) ← prove_inv ic b nb,
  (ic, c, p) ← prove_mul_rat ic a b' na nb⁻¹,
  (ic, p) ← ic.mk_app ``div_eq [a, b, b', c, pb, p],
  return (ic, c, p)

meta def prove_neg (ic : instance_cache) (a : expr) : tactic (instance_cache × expr × expr) :=
match match_neg a with
| some a := do
  (ic, p) ← ic.mk_app ``neg_neg [a],
  return (ic, a, p)
| none := do
  (ic, a') ← ic.mk_app ``has_neg.neg [a],
  p ← mk_eq_refl a',
  return (ic, a', p)
end

theorem sub_pos {α} [add_group α] (a b b' c : α) (hb : -b = b') (h : a + b' = c) : a - b = c :=
by rwa ← hb at h
theorem sub_neg {α} [add_group α] (a b c : α) (h : a + b = c) : a - -b = c :=
by rwa sub_neg_eq_add

meta def prove_sub (ic : instance_cache) (a b : expr) : tactic (instance_cache × expr × expr) :=
match match_neg b with
| some b := do
  (ic, c, p) ← prove_add_rat' ic a b,
  (ic, p) ← ic.mk_app ``sub_neg [a, b, c, p],
  return (ic, c, p)
| none := do
  (ic, b', pb) ← prove_neg ic b,
  (ic, c, p) ← prove_add_rat' ic a b',
  (ic, p) ← ic.mk_app ``sub_pos [a, b, b', c, pb, p],
  return (ic, c, p)
end

theorem sub_nat_pos (a b c : ℕ) (h : b + c = a) : a - b = c :=
h ▸ nat.add_sub_cancel_left _ _
theorem sub_nat_neg (a b c : ℕ) (h : a + c = b) : a - b = 0 :=
nat.sub_eq_zero_of_le $ h ▸ nat.le_add_right _ _

meta def prove_sub_nat (ic : instance_cache) (a b : expr) : tactic (expr × expr) :=
do na ← a.to_nat, nb ← b.to_nat,
  if nb ≤ na then do
    c ← expr.of_nat `(ℕ) (na - nb),
    (ic, p) ← prove_add_nat ic b c a,
    return (c, `(sub_nat_pos).mk_app [a, b, c, p])
  else do
    c ← expr.of_nat `(ℕ) (nb - na),
    (ic, p) ← prove_add_nat ic a c b,
    return (`(0 : ℕ), `(sub_nat_neg).mk_app [a, b, c, p])

meta def eval_field : expr → tactic (expr × expr)
| `(%%e₁ + %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  α ← infer_type e₁,
  c ← mk_instance_cache α,
  let n₃ := n₁ + n₂,
  e₃ ← expr.of_rat α n₃,
  (_, p) ← prove_add_rat c e₁ e₂ e₃ n₁ n₂ n₃,
  return (e₃, p)
| `(%%e₁ * %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  prod.snd <$> prove_mul_rat c e₁ e₂ n₁ n₂
| `(- %%e) := do
  c ← infer_type e >>= mk_instance_cache,
  prod.snd <$> prove_neg c e
| `(%%a - %%b) := do
  α ← infer_type a,
  c ← mk_instance_cache α,
  if α = `(nat) then prove_sub_nat c a b
  else prod.snd <$> prove_sub c a b
| `(has_inv.inv %%e) := do
  n ← e.to_rat,
  c ← infer_type e >>= mk_instance_cache,
  prod.snd <$> prove_inv c e n
| `(%%e₁ / %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  prod.snd <$> prove_div c e₁ e₂ n₁ n₂
| _ := failed

lemma pow_bit0 [monoid α] (a c' c : α) (b : ℕ)
  (h : a ^ b = c') (h₂ : c' * c' = c) : a ^ bit0 b = c :=
h₂ ▸ by simp [pow_bit0, h]

lemma pow_bit1 [monoid α] (a c₁ c₂ c : α) (b : ℕ)
  (h : a ^ b = c₁) (h₂ : c₁ * c₁ = c₂) (h₃ : c₂ * a = c) : a ^ bit1 b = c :=
by rw [← h₃, ← h₂]; simp [pow_bit1, h]

section
open match_numeral_result

meta def prove_pow (a : expr) (na : ℚ) : instance_cache → expr → tactic (instance_cache × expr × expr)
| ic b :=
  match match_numeral b with
  | some zero := do
    (ic, p) ← ic.mk_app ``pow_zero [a],
    (ic, o) ← ic.mk_app ``has_one.one [],
    return (ic, o, p)
  | some one := do
    (ic, p) ← ic.mk_app ``pow_one [a],
    return (ic, a, p)
  | some (bit0 b) := do
    (ic, c', p) ← prove_pow ic b,
    nc' ← expr.to_rat c',
    (ic, c, p₂) ← prove_mul_rat ic c' c' nc' nc',
    (ic, p) ← ic.mk_app ``pow_bit0 [a, c', c, b, p, p₂],
    return (ic, c, p)
  | some (bit1 b) := do
    (ic, c₁, p) ← prove_pow ic b,
    nc₁ ← expr.to_rat c₁,
    (ic, c₂, p₂) ← prove_mul_rat ic c₁ c₁ nc₁ nc₁,
    (ic, c, p₃) ← prove_mul_rat ic c₂ a (nc₁ * nc₁) na,
    (ic, p) ← ic.mk_app ``pow_bit1 [a, c₁, c₂, c, b, p, p₂, p₃],
    return (ic, c, p)
  | none := failed
  end

end

lemma lt_add_of_pos [ordered_cancel_add_comm_monoid α]
  (a b c : α) (h : a + b = c) (h₂ : 0 < b) : a < c :=
h ▸ (lt_add_iff_pos_right _).2 h₂

lemma nat_div (a b q r : ℕ) (h : r + q * b = a) (h₂ : r < b) : a / b = q :=
by rw [← h, nat.add_mul_div_right _ _ (lt_of_le_of_lt (nat.zero_le _) h₂),
       nat.div_eq_of_lt h₂, zero_add]

lemma int_div (a b q r : ℤ) (h : r + q * b = a) (h₁ : 0 ≤ r) (h₂ : r < b) : a / b = q :=
by rw [← h, int.add_mul_div_right _ _ (ne_of_gt (lt_of_le_of_lt h₁ h₂)),
       int.div_eq_zero_of_lt h₁ h₂, zero_add]

lemma nat_mod (a b q r : ℕ) (h : r + q * b = a) (h₂ : r < b) : a % b = r :=
by rw [← h, nat.add_mul_mod_self_right, nat.mod_eq_of_lt h₂]

lemma int_mod (a b q r : ℤ) (h : r + q * b = a) (h₁ : 0 ≤ r) (h₂ : r < b) : a % b = r :=
by rw [← h, int.add_mul_mod_self, int.mod_eq_of_lt h₁ h₂]

lemma from_nat_pow (a b c : ℕ) (h : @has_pow.pow _ _ monoid.has_pow a b = c) : a ^ b = c :=
(nat.pow_eq_pow _ _).symm.trans h

meta def eval_pow : expr → tactic (expr × expr)
| `(@has_pow.pow %%α _ %%m %%e₁ %%e₂) := do
  n₁ ← e₁.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  match m with
  | `(@monoid.has_pow %%_ %%_) := prod.snd <$> prove_pow e₁ n₁ c e₂
  | `(nat.has_pow) := do
    (_, c, p) ← prove_pow e₁ n₁ c e₂,
    return (c, `(from_nat_pow).mk_app [e₁, e₂, c, p])
  | _ := failed
  end
| `(monoid.pow %%e₁ %%e₂) := do
  n₁ ← e₁.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  prod.snd <$> prove_pow e₁ n₁ c e₂
| `(nat.pow %%e₁ %%e₂) := do
  n₁ ← e₁.to_rat,
  c ← mk_instance_cache `(ℕ),
  (_, c, p) ← prove_pow e₁ n₁ c e₂,
  return (c, `(from_nat_pow).mk_app [e₁, e₂, c, p])
| _ := failed

meta def prove_lt (simp : expr → tactic (expr × expr)) : instance_cache → expr → expr → tactic (instance_cache × expr)
| c `(- %%e₁) `(- %%e₂) := do
  (c, p) ← prove_lt c e₁ e₂,
  (c, p) ← c.mk_app ``neg_lt_neg [e₁, e₂, p],
  return (c, p)
| c `(- %%e₁) `(has_zero.zero) := do
  (c, p) ← prove_pos c e₁,
  (c, p) ← c.mk_app ``neg_neg_of_pos [e₁, p],
  return (c, p)
| c `(- %%e₁) e₂ := do
  (c, p₁) ← prove_pos c e₁,
  (c, me₁) ← c.mk_app ``has_neg.neg [e₁],
  (c, p₁) ← c.mk_app ``neg_neg_of_pos [e₁, p₁],
  (c, p₂) ← prove_pos c e₂,
  (c, z) ← c.mk_app ``has_zero.zero [],
  (c, p) ← c.mk_app ``lt_trans [me₁, z, e₂, p₁, p₂],
  return (c, p)
| c `(has_zero.zero) e₂ := prove_pos c e₂
| c e₁ e₂ := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  let nd := n₂ - n₁,
  d ← expr.of_rat c.α nd,
  (e₂', p) ← prove_add_rat c e₁ d e₂ n₁ nd n₂,
  (c, p') ← prove_pos c d,
  (c, p) ← c.mk_app ``lt_add_of_pos [e₁, d, e₂, p, p'],
  return (c, p)

private meta def true_intro (p : expr) : tactic (expr × expr) :=
prod.mk <$> mk_const `true <*> mk_app ``eq_true_intro [p]

private meta def false_intro (p : expr) : tactic (expr × expr) :=
prod.mk <$> mk_const `false <*> mk_app ``eq_false_intro [p]

meta def eval_ineq (simp : expr → tactic (expr × expr)) : expr → tactic (expr × expr)
| `(%%e₁ < %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  if n₁ < n₂ then
    do (_, p) ← prove_lt simp c e₁ e₂, true_intro p
  else do
    (c, p) ← if n₁ = n₂ then c.mk_app ``lt_irrefl [e₁] else
      (do (c, p') ← prove_lt simp c e₂ e₁,
          c.mk_app ``not_lt_of_gt [e₁, e₂, p']),
    false_intro p
| `(%%e₁ ≤ %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  if n₁ ≤ n₂ then do
    (c, p) ← if n₁ = n₂ then c.mk_app ``le_refl [e₁] else
      (do (c, p') ← prove_lt simp c e₁ e₂,
          c.mk_app ``le_of_lt [e₁, e₂, p']),
    true_intro p
  else do
    (c, p) ← prove_lt simp c e₂ e₁,
    (c, p) ← c.mk_app ``not_le_of_gt [e₁, e₂, p],
    false_intro p
| `(%%e₁ = %%e₂) := do
  n₁ ← e₁.to_rat, n₂ ← e₂.to_rat,
  c ← infer_type e₁ >>= mk_instance_cache,
  if n₁ < n₂ then do
    (c, p) ← prove_lt simp c e₁ e₂,
    (c, p) ← c.mk_app ``ne_of_lt [e₁, e₂, p],
    false_intro p
  else if n₂ < n₁ then do
    (c, p) ← prove_lt simp c e₂ e₁,
    (c, p) ← c.mk_app ``ne_of_gt [e₁, e₂, p],
    false_intro p
  else mk_eq_refl e₁ >>= true_intro
| `(%%e₁ > %%e₂) := mk_app ``has_lt.lt [e₂, e₁] >>= simp
| `(%%e₁ ≥ %%e₂) := mk_app ``has_le.le [e₂, e₁] >>= simp
| `(%%e₁ ≠ %%e₂) := do e ← mk_app ``eq [e₁, e₂], mk_app ``not [e] >>= simp
| _ := failed

meta def eval_div_ext (simp : expr → tactic (expr × expr)) : expr → tactic (expr × expr)
| `(has_inv.inv %%e) := do
  c ← infer_type e >>= mk_instance_cache,
  (c, p₁) ← c.mk_app ``inv_eq_one_div [e],
  (c, o) ← c.mk_app ``has_one.one [],
  (c, e') ← c.mk_app ``has_div.div [o, e],
  (do (e'', p₂) ← simp e',
    p ← mk_eq_trans p₁ p₂,
    return (e'', p)) <|> return (e', p₁)
| `(%%e₁ / %%e₂) := do
  α ← infer_type e₁,
  c ← mk_instance_cache α,
  match α with
  | `(nat) := do
    n₁ ← e₁.to_nat, n₂ ← e₂.to_nat,
    q ← expr.of_nat α (n₁ / n₂),
    r ← expr.of_nat α (n₁ % n₂),
    (c, e₃) ← c.mk_app ``has_mul.mul [q, e₂],
    (c, e₃) ← c.mk_app ``has_add.add [r, e₃],
    (e₁', p) ← simp e₃,
    guard (e₁' =ₐ e₁),
    (c, p') ← prove_lt simp c r e₂,
    p ← mk_app ``nat_div [e₁, e₂, q, r, p, p'],
    return (q, p)
  | `(int) := match match_neg e₂ with
    | some e₂' := do
      (c, p₁) ← c.mk_app ``int.div_neg [e₁, e₂'],
      (c, e) ← c.mk_app ``has_div.div [e₁, e₂'],
      (c, e) ← c.mk_app ``has_neg.neg [e],
      (e', p₂) ← simp e,
      p ← mk_eq_trans p₁ p₂,
      return (e', p)
    | none := do
      n₁ ← e₁.to_int,
      n₂ ← e₂.to_int,
      q ← expr.of_rat α $ rat.of_int (n₁ / n₂),
      r ← expr.of_rat α $ rat.of_int (n₁ % n₂),
      (c, e₃) ← c.mk_app ``has_mul.mul [q, e₂],
      (c, e₃) ← c.mk_app ``has_add.add [r, e₃],
      (e₁', p) ← simp e₃,
      guard (e₁' =ₐ e₁),
      (c, r0) ← c.mk_app ``has_zero.zero [],
      (c, r0) ← c.mk_app ``has_le.le [r0, r],
      (_, p₁) ← simp r0,
      p₁ ← mk_app ``of_eq_true [p₁],
      (c, p₂) ← prove_lt simp c r e₂,
      p ← mk_app ``int_div [e₁, e₂, q, r, p, p₁, p₂],
      return (q, p)
    end
  | _ := failed
  end
| `(%%e₁ % %%e₂) := do
  α ← infer_type e₁,
  c ← mk_instance_cache α,
  if α = `(nat) then do
    n₁ ← e₁.to_nat, n₂ ← e₂.to_nat,
    q ← expr.of_nat α (n₁ / n₂),
    r ← expr.of_nat α (n₁ % n₂),
    (c, e₃) ← c.mk_app ``has_mul.mul [q, e₂],
    (c, e₃) ← c.mk_app ``has_add.add [r, e₃],
    (e₁', p) ← simp e₃,
    guard (e₁' =ₐ e₁),
    (c, p') ← prove_lt simp c r e₂,
    p ← mk_app ``nat_mod [e₁, e₂, q, r, p, p'],
    return (r, p)
  else if α = `(int) then
    match match_neg e₂ with
    | some e₂' := do
      let p₁ := (expr.const ``int.mod_neg []).mk_app [e₁, e₂'],
      (c, e) ← c.mk_app ``has_mod.mod [e₁, e₂'],
      (e', p₂) ← simp e,
      p ← mk_eq_trans p₁ p₂,
      return (e', p)
    | none := do
      n₁ ← e₁.to_int,
      n₂ ← e₂.to_int,
      q ← expr.of_rat α $ rat.of_int (n₁ / n₂),
      r ← expr.of_rat α $ rat.of_int (n₁ % n₂),
      (c, e₃) ← c.mk_app ``has_mul.mul [q, e₂],
      (c, e₃) ← c.mk_app ``has_add.add [r, e₃],
      (e₁', p) ← simp e₃,
      guard (e₁' =ₐ e₁),
      (c, r0) ← c.mk_app ``has_zero.zero [],
      (c, r0) ← c.mk_app ``has_le.le [r0, r],
      (_, p₁) ← simp r0,
      p₁ ← mk_app ``of_eq_true [p₁],
      (c, p₂) ← prove_lt simp c r e₂,
      p ← mk_app ``int_mod [e₁, e₂, q, r, p, p₁, p₂],
      return (r, p)
    end
  else failed
| `(%%e₁ ∣ %%e₂) := do
  α ← infer_type e₁,
  c ← mk_instance_cache α,
  n ← if α = `(nat) then return ``nat.dvd_iff_mod_eq_zero else
      if α = `(int) then return ``int.dvd_iff_mod_eq_zero else
      failed,
  p₁ ← mk_app ``propext [@expr.const tt n [] e₁ e₂],
  (c, el) ← c.mk_app ``has_mod.mod [e₂, e₁],
  (c, z) ← c.mk_app ``has_zero.zero [],
  e ← mk_app ``eq [el, z],
  (e', p₂) ← simp e,
  p' ← mk_eq_trans p₁ p₂,
  return (e', p')
| _ := failed

lemma not_prime_helper (a b n : ℕ)
  (h : a * b = n) (h₁ : 1 < a) (h₂ : 1 < b) : ¬ nat.prime n :=
by rw ← h; exact nat.not_prime_mul h₁ h₂

lemma is_prime_helper (n : ℕ)
  (h₁ : 1 < n) (h₂ : nat.min_fac n = n) : nat.prime n :=
nat.prime_def_min_fac.2 ⟨h₁, h₂⟩

lemma min_fac_bit0 (n : ℕ) : nat.min_fac (bit0 n) = 2 :=
by simp [nat.min_fac_eq, show 2 ∣ bit0 n, by simp [bit0_eq_two_mul n]]

def min_fac_helper (n k : ℕ) : Prop :=
0 < k ∧ bit1 k ≤ nat.min_fac (bit1 n)

theorem min_fac_helper.n_pos {n k : ℕ} (h : min_fac_helper n k) : 0 < n :=
nat.pos_iff_ne_zero.2 $ λ e,
by rw e at h; exact not_le_of_lt (nat.bit1_lt h.1) h.2

lemma min_fac_ne_bit0 {n k : ℕ} : nat.min_fac (bit1 n) ≠ bit0 k :=
by rw bit0_eq_two_mul; exact λ e, absurd
  ((nat.dvd_add_iff_right (by simp [bit0_eq_two_mul n])).2
    (dvd_trans ⟨_, e⟩ (nat.min_fac_dvd _)))
  dec_trivial

lemma min_fac_helper_0 (n : ℕ) (h : 0 < n) : min_fac_helper n 1 :=
begin
  refine ⟨zero_lt_one, lt_of_le_of_ne _ min_fac_ne_bit0.symm⟩,
  refine @lt_of_le_of_ne ℕ _ _ _ (nat.min_fac_pos _) _,
  intro e,
  have := nat.min_fac_prime _,
  { rw ← e at this, exact nat.not_prime_one this },
  { exact ne_of_gt (nat.bit1_lt h) }
end

lemma min_fac_helper_1 {n k k' : ℕ} (e : k + 1 = k')
  (np : nat.min_fac (bit1 n) ≠ bit1 k)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  rw ← e,
  refine ⟨nat.succ_pos _,
    (lt_of_le_of_ne (lt_of_le_of_ne _ _ : k+1+k < _)
      min_fac_ne_bit0.symm : bit0 (k+1) < _)⟩,
  { rw add_right_comm, exact h.2 },
  { rw add_right_comm, exact np.symm }
end

lemma min_fac_helper_2 (n k k' : ℕ) (e : k + 1 = k')
  (np : ¬ nat.prime (bit1 k)) (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  refine min_fac_helper_1 e _ h,
  intro e₁, rw ← e₁ at np,
  exact np (nat.min_fac_prime $ ne_of_gt $ nat.bit1_lt h.n_pos)
end

lemma min_fac_helper_3 (n k k' : ℕ) (e : k + 1 = k')
  (nd : bit1 k ∣ bit1 n = false)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
begin
  refine min_fac_helper_1 e _ h,
  intro e₁, rw [eq_false, ← e₁] at nd,
  exact nd (nat.min_fac_dvd _)
end

lemma min_fac_helper_4 (n k : ℕ) (hd : bit1 k ∣ bit1 n = true)
  (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 k :=
by rw eq_true at hd; exact
le_antisymm (nat.min_fac_le_of_dvd (nat.bit1_lt h.1) hd) h.2

lemma min_fac_helper_5 (n k k' : ℕ) (e : bit1 k * bit1 k = k')
  (hd : bit1 n < k') (h : min_fac_helper n k) : nat.min_fac (bit1 n) = bit1 n :=
begin
  refine (nat.prime_def_min_fac.1 (nat.prime_def_le_sqrt.2
    ⟨nat.bit1_lt h.n_pos, _⟩)).2,
  rw ← e at hd,
  intros m m2 hm md,
  have := le_trans h.2 (le_trans (nat.min_fac_le_of_dvd m2 md) hm),
  rw nat.le_sqrt at this,
  exact not_le_of_lt hd this
end

meta def prove_non_prime (simp : expr → tactic (expr × expr)) (e : expr) (n d₁ : ℕ) : tactic expr :=
do let e₁ := reflect d₁,
  c ← mk_instance_cache `(nat),
  (c, p₁) ← prove_lt simp c `(1) e₁,
  let d₂ := n / d₁, let e₂ := reflect d₂,
  (e', p) ← mk_app ``has_mul.mul [e₁, e₂] >>= simp,
  guard (e' =ₐ e),
  (c, p₂) ← prove_lt simp c `(1) e₂,
  return $ (expr.const ``not_prime_helper []).mk_app [e₁, e₂, e, p, p₁, p₂]

meta def prove_min_fac (simp : expr → tactic (expr × expr))
  (e₁ : expr) (n1 : ℕ) : expr → expr → tactic (expr × expr)
| e₂ p := do
  k ← e₂.to_nat,
  let k1 := bit1 k,
  e₁1 ← mk_app ``bit1 [e₁],
  e₂1 ← mk_app ``bit1 [e₂],
  if n1 < k1*k1 then do
    c ← mk_instance_cache `(nat),
    (c, e') ← c.mk_app ``has_mul.mul [e₂1, e₂1],
    (e', p₁) ← simp e',
    (c, p₂) ← prove_lt simp c e₁1 e',
    p' ← mk_app ``min_fac_helper_5 [e₁, e₂, e', p₁, p₂, p],
    return (e₁1, p')
  else let d := k1.min_fac in
  if to_bool (d < k1) then do
    (e', p₁) ← simp `(%%e₂ + 1),
    p₂ ← prove_non_prime simp e₂1 k1 d,
    mk_app ``min_fac_helper_2 [e₁, e₂, e', p₁, p₂, p] >>= prove_min_fac e'
  else do
    (_, p₂) ← simp `((%%e₂1 : ℕ) ∣ %%e₁1),
    if k1 ∣ n1 then do
      p' ← mk_app ``min_fac_helper_4 [e₁, e₂, p₂, p],
      return (e₂1, p')
    else do
      (e', p₁) ← simp `(%%e₂ + 1),
      mk_app ``min_fac_helper_3 [e₁, e₂, e', p₁, p₂, p] >>= prove_min_fac e'

meta def eval_prime (simp : expr → tactic (expr × expr)) : expr → tactic (expr × expr)
| `(nat.prime %%e) := do
  n ← e.to_nat,
  match n with
  | 0 := false_intro `(nat.not_prime_zero)
  | 1 := false_intro `(nat.not_prime_one)
  | _ := let d₁ := n.min_fac in
    if d₁ < n then prove_non_prime simp e n d₁ >>= false_intro
    else do
      let e₁ := reflect d₁,
      c ← mk_instance_cache `(nat),
      (c, p₁) ← prove_lt simp c `(1) e₁,
      (e₁, p) ← simp `(nat.min_fac %%e),
      true_intro $ (expr.const ``is_prime_helper []).mk_app [e, p₁, p]
  end
| `(nat.min_fac 0) := refl_conv (reflect (0:ℕ))
| `(nat.min_fac 1) := refl_conv (reflect (1:ℕ))
| `(nat.min_fac (bit0 %%e)) := prod.mk `(2) <$> mk_app ``min_fac_bit0 [e]
| `(nat.min_fac (bit1 %%e)) := do
  n ← e.to_nat,
  c ← mk_instance_cache `(nat),
  (c, p) ← prove_pos c e,
  mk_app ``min_fac_helper_0 [e, p] >>= prove_min_fac simp e (bit1 n) `(1)
| _ := failed

meta def derive1 (simp : expr → tactic (expr × expr)) (e : expr) :
  tactic (expr × expr) :=
eval_field e <|> eval_div_ext simp e <|>
eval_pow e <|> eval_ineq simp e <|> eval_prime simp e

meta def derive : expr → tactic (expr × expr) | e :=
do e ← instantiate_mvars e,
   (_, e', pr) ←
    ext_simplify_core () {} simp_lemmas.mk (λ _, failed) (λ _ _ _ _ _, failed)
      (λ _ _ _ _ e,
        do (new_e, pr) ← derive1 derive e,
           guard (¬ new_e =ₐ e),
           return ((), new_e, some pr, tt))
      `eq e,
    return (e', pr)

/-- This version of `derive` does not fail when the input is already a numeral -/
meta def derive' : expr → tactic (expr × expr) := derive1 derive

end norm_num

namespace tactic.interactive
open norm_num interactive interactive.types

/-- Basic version of `norm_num` that does not call `simp`. -/
meta def norm_num1 (loc : parse location) : tactic unit :=
do ns ← loc.get_locals,
   tt ← tactic.replace_at derive ns loc.include_goal
      | fail "norm_num failed to simplify",
   when loc.include_goal $ try tactic.triv,
   when (¬ ns.empty) $ try tactic.contradiction

/-- Normalize numerical expressions. Supports the operations
`+` `-` `*` `/` `^` and `%` over numerical types such as
`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`,
where `A` and `B` are numerical expressions.
It also has a relatively simple primality prover. -/
meta def norm_num (hs : parse simp_arg_list) (l : parse location) : tactic unit :=
repeat1 $ orelse' (norm_num1 l) $
simp_core {} (norm_num1 (loc.ns [none])) ff hs [] l

add_hint_tactic "norm_num"

/-- Normalizes a numerical expression and tries to close the goal with the result. -/
meta def apply_normed (x : parse texpr) : tactic unit :=
do x₁ ← to_expr x,
  (x₂,_) ← derive x₁,
  tactic.exact x₂

/--
Normalises numerical expressions. It supports the operations `+` `-` `*` `/` `^` and `%` over
numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`, and can prove goals of the form `A = B`, `A ≠ B`,
`A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions. It also has a relatively simple primality prover.
```lean
import data.real.basic

example : (2 : ℝ) + 2 = 4 := by norm_num
example : (12345.2 : ℝ) ≠ 12345.3 := by norm_num
example : (73 : ℝ) < 789/2 := by norm_num
example : 123456789 + 987654321 = 1111111110 := by norm_num
example (R : Type*) [ring R] : (2 : R) + 2 = 4 := by norm_num
example (F : Type*) [linear_ordered_field F] : (2 : F) + 2 < 5 := by norm_num
example : nat.prime (2^13 - 1) := by norm_num
example : ¬ nat.prime (2^11 - 1) := by norm_num
example (x : ℝ) (h : x = 123 + 456) : x = 579 := by norm_num at h; assumption
```

The variant `norm_num1` does not call `simp`.

Both `norm_num` and `norm_num1` can be called inside the `conv` tactic.

The tactic `apply_normed` normalises a numerical expression and tries to close the goal with
the result. Compare:
```lean
def a : ℕ := 2^100
#print a -- 2 ^ 100

def normed_a : ℕ := by apply_normed 2^100
#print normed_a -- 1267650600228229401496703205376
```
-/
add_tactic_doc
{ name        := "norm_num",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.norm_num1, `tactic.interactive.norm_num,
                  `tactic.interactive.apply_normed],
  tags        := ["arithmetic", "decision procedure"] }

end tactic.interactive

namespace conv.interactive
open conv interactive tactic.interactive
open norm_num (derive)

meta def norm_num1 : conv unit := replace_lhs derive

meta def norm_num (hs : parse simp_arg_list) : conv unit :=
repeat1 $ orelse' norm_num1 $
simp_core {} norm_num1 ff hs [] (loc.ns [none])

end conv.interactive
