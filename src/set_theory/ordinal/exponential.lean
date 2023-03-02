/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import set_theory.ordinal.arithmetic

/-! # Ordinal exponential

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the power function and the logarithm function on ordinals. The two are
related by the lemma `ordinal.opow_le_iff_le_log : (b^c) ≤ x ↔ c ≤ log b x` for nontrivial inputs 
`b`, `c`.
-/

noncomputable theory

open function cardinal set equiv order
open_locale classical cardinal ordinal

universes u v w

namespace ordinal

/-- The ordinal exponential, defined by transfinite recursion. -/
instance : has_pow ordinal ordinal :=
⟨λ a b, if a = 0 then 1 - b else limit_rec_on b 1 (λ _ IH, IH * a) (λ b _, bsup.{u u} b)⟩

local infixr (name := ordinal.pow) ^ := @pow ordinal ordinal ordinal.has_pow

theorem opow_def (a b : ordinal) :
  a ^ b = if a = 0 then 1 - b else limit_rec_on b 1 (λ _ IH, IH * a) (λ b _, bsup.{u u} b) :=
rfl

theorem zero_opow' (a : ordinal) : 0 ^ a = 1 - a :=
by simp only [opow_def, if_pos rfl]

@[simp] theorem zero_opow {a : ordinal} (a0 : a ≠ 0) : 0 ^ a = 0 :=
by rwa [zero_opow', ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp] theorem opow_zero (a : ordinal) : a ^ 0 = 1 :=
by by_cases a = 0; [simp only [opow_def, if_pos h, sub_zero],
simp only [opow_def, if_neg h, limit_rec_on_zero]]

@[simp] theorem opow_succ (a b : ordinal) : a ^ succ b = a ^ b * a :=
if h : a = 0 then by subst a; simp only [zero_opow (succ_ne_zero _), mul_zero]
else by simp only [opow_def, limit_rec_on_succ, if_neg h]

theorem opow_limit {a b : ordinal} (a0 : a ≠ 0) (h : is_limit b) :
  a ^ b = bsup.{u u} b (λ c _, a ^ c) :=
by simp only [opow_def, if_neg a0]; rw limit_rec_on_limit _ _ _ _ h; refl

theorem opow_le_of_limit {a b c : ordinal} (a0 : a ≠ 0) (h : is_limit b) :
  a ^ b ≤ c ↔ ∀ b' < b, a ^ b' ≤ c :=
by rw [opow_limit a0 h, bsup_le_iff]

theorem lt_opow_of_limit {a b c : ordinal} (b0 : b ≠ 0) (h : is_limit c) :
  a < b ^ c ↔ ∃ c' < c, a < b ^ c' :=
by rw [← not_iff_not, not_exists]; simp only [not_lt, opow_le_of_limit b0 h, exists_prop, not_and]

@[simp] theorem opow_one (a : ordinal) : a ^ 1 = a :=
by rw [← succ_zero, opow_succ]; simp only [opow_zero, one_mul]

@[simp] theorem one_opow (a : ordinal) : 1 ^ a = 1 :=
begin
  apply limit_rec_on a,
  { simp only [opow_zero] },
  { intros _ ih, simp only [opow_succ, ih, mul_one] },
  refine λ b l IH, eq_of_forall_ge_iff (λ c, _),
  rw [opow_le_of_limit ordinal.one_ne_zero l],
  exact ⟨λ H, by simpa only [opow_zero] using H 0 l.pos,
         λ H b' h, by rwa IH _ h⟩,
end

theorem opow_pos {a : ordinal} (b)
  (a0 : 0 < a) : 0 < a ^ b :=
begin
  have h0 : 0 < a ^ 0, {simp only [opow_zero, zero_lt_one]},
  apply limit_rec_on b,
  { exact h0 },
  { intros b IH, rw [opow_succ],
    exact mul_pos IH a0 },
  { exact λ b l _, (lt_opow_of_limit (ordinal.pos_iff_ne_zero.1 a0) l).2
      ⟨0, l.pos, h0⟩ },
end

theorem opow_ne_zero {a : ordinal} (b)
  (a0 : a ≠ 0) : a ^ b ≠ 0 :=
ordinal.pos_iff_ne_zero.1 $ opow_pos b $ ordinal.pos_iff_ne_zero.2 a0

theorem opow_is_normal {a : ordinal} (h : 1 < a) : is_normal ((^) a) :=
have a0 : 0 < a, from zero_lt_one.trans h,
⟨λ b, by simpa only [mul_one, opow_succ] using
  (mul_lt_mul_iff_left (opow_pos b a0)).2 h,
 λ b l c, opow_le_of_limit (ne_of_gt a0) l⟩

theorem opow_lt_opow_iff_right {a b c : ordinal}
  (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
(opow_is_normal a1).lt_iff

theorem opow_le_opow_iff_right {a b c : ordinal}
  (a1 : 1 < a) : a ^ b ≤ a ^ c ↔ b ≤ c :=
(opow_is_normal a1).le_iff

theorem opow_right_inj {a b c : ordinal}
  (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
(opow_is_normal a1).inj

theorem opow_is_limit {a b : ordinal}
  (a1 : 1 < a) : is_limit b → is_limit (a ^ b) :=
(opow_is_normal a1).is_limit

theorem opow_is_limit_left {a b : ordinal}
  (l : is_limit a) (hb : b ≠ 0) : is_limit (a ^ b) :=
begin
  rcases zero_or_succ_or_limit b with e|⟨b,rfl⟩|l',
  { exact absurd e hb },
  { rw opow_succ,
    exact mul_is_limit (opow_pos _ l.pos) l },
  { exact opow_is_limit l.one_lt l' }
end

theorem opow_le_opow_right {a b c : ordinal}
  (h₁ : 0 < a) (h₂ : b ≤ c) : a ^ b ≤ a ^ c :=
begin
  cases lt_or_eq_of_le (one_le_iff_pos.2 h₁) with h₁ h₁,
  { exact (opow_le_opow_iff_right h₁).2 h₂ },
  { subst a, simp only [one_opow] }
end

theorem opow_le_opow_left {a b : ordinal} (c)
  (ab : a ≤ b) : a ^ c ≤ b ^ c :=
begin
  by_cases a0 : a = 0,
  { subst a, by_cases c0 : c = 0,
    { subst c, simp only [opow_zero] },
    { simp only [zero_opow c0, ordinal.zero_le] } },
  { apply limit_rec_on c,
    { simp only [opow_zero] },
    { intros c IH, simpa only [opow_succ] using mul_le_mul' IH ab },
    { exact λ c l IH, (opow_le_of_limit a0 l).2
        (λ b' h, (IH _ h).trans (opow_le_opow_right
          ((ordinal.pos_iff_ne_zero.2 a0).trans_le ab) h.le)) } }
end

theorem left_le_opow (a : ordinal) {b : ordinal} (b1 : 0 < b) : a ≤ a ^ b :=
begin
  nth_rewrite 0 ←opow_one a,
  cases le_or_gt a 1 with a1 a1,
  { cases lt_or_eq_of_le a1 with a0 a1,
    { rw lt_one_iff_zero at a0,
      rw [a0, zero_opow ordinal.one_ne_zero],
      exact ordinal.zero_le _ },
    rw [a1, one_opow, one_opow] },
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]
end

theorem right_le_opow {a : ordinal} (b) (a1 : 1 < a) : b ≤ a ^ b :=
(opow_is_normal a1).self_le _

theorem opow_lt_opow_left_of_succ {a b c : ordinal}
  (ab : a < b) : a ^ succ c < b ^ succ c :=
by { rw [opow_succ, opow_succ], exact
  (mul_le_mul_right' (opow_le_opow_left c ab.le) a).trans_lt
  (mul_lt_mul_of_pos_left ab (opow_pos c ((ordinal.zero_le a).trans_lt ab))) }

theorem opow_add (a b c : ordinal) : a ^ (b + c) = a ^ b * a ^ c :=
begin
  rcases eq_or_ne a 0 with rfl | a0,
  { rcases eq_or_ne c 0 with rfl | c0, { simp },
    have : b + c ≠ 0 := ((ordinal.pos_iff_ne_zero.2 c0).trans_le (le_add_left _ _)).ne',
    simp only [zero_opow c0, zero_opow this, mul_zero] },
  rcases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with rfl | a1,
  { simp only [one_opow, mul_one] },
  apply limit_rec_on c,
  { simp },
  { intros c IH,
    rw [add_succ, opow_succ, IH, opow_succ, mul_assoc] },
  { intros c l IH,
    refine eq_of_forall_ge_iff (λ d, (((opow_is_normal a1).trans
      (add_is_normal b)).limit_le l).trans _),
    dsimp only [function.comp],
    simp only [IH] {contextual := tt},
    exact (((mul_is_normal $ opow_pos b (ordinal.pos_iff_ne_zero.2 a0)).trans
      (opow_is_normal a1)).limit_le l).symm }
end

theorem opow_one_add (a b : ordinal) : a ^ (1 + b) = a * a ^ b :=
by rw [opow_add, opow_one]

theorem opow_dvd_opow (a) {b c : ordinal}
  (h : b ≤ c) : a ^ b ∣ a ^ c :=
by { rw [← ordinal.add_sub_cancel_of_le h, opow_add], apply dvd_mul_right }

theorem opow_dvd_opow_iff {a b c : ordinal}
  (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b ≤ c :=
⟨λ h, le_of_not_lt $ λ hn,
  not_le_of_lt ((opow_lt_opow_iff_right a1).2 hn) $
    le_of_dvd (opow_ne_zero _ $ one_le_iff_ne_zero.1 $ a1.le) h,
opow_dvd_opow _⟩

theorem opow_mul (a b c : ordinal) : a ^ (b * c) = (a ^ b) ^ c :=
begin
  by_cases b0 : b = 0, {simp only [b0, zero_mul, opow_zero, one_opow]},
  by_cases a0 : a = 0,
  { subst a,
    by_cases c0 : c = 0, {simp only [c0, mul_zero, opow_zero]},
    simp only [zero_opow b0, zero_opow c0, zero_opow (mul_ne_zero b0 c0)] },
  cases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1,
  { subst a1, simp only [one_opow] },
  apply limit_rec_on c,
  { simp only [mul_zero, opow_zero] },
  { intros c IH,
    rw [mul_succ, opow_add, IH, opow_succ] },
  { intros c l IH,
    refine eq_of_forall_ge_iff (λ d, (((opow_is_normal a1).trans
      (mul_is_normal (ordinal.pos_iff_ne_zero.2 b0))).limit_le l).trans _),
    dsimp only [function.comp],
    simp only [IH] {contextual := tt},
    exact (opow_le_of_limit (opow_ne_zero _ a0) l).symm }
end

/-! ### Ordinal logarithm -/

/-- The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` where `v < b` and
    `w < b ^ u`. -/
@[pp_nodot] def log (b : ordinal) (x : ordinal) : ordinal :=
if h : 1 < b then pred (Inf {o | x < b ^ o}) else 0

/-- The set in the definition of `log` is nonempty. -/
theorem log_nonempty {b x : ordinal} (h : 1 < b) : {o | x < b ^ o}.nonempty :=
⟨_, succ_le_iff.1 (right_le_opow _ h)⟩

theorem log_def {b : ordinal} (h : 1 < b) (x : ordinal) : log b x = pred (Inf {o | x < b ^ o}) :=
by simp only [log, dif_pos h]

theorem log_of_not_one_lt_left {b : ordinal} (h : ¬ 1 < b) (x : ordinal) : log b x = 0 :=
by simp only [log, dif_neg h]

theorem log_of_left_le_one {b : ordinal} (h : b ≤ 1) : ∀ x, log b x = 0 :=
log_of_not_one_lt_left h.not_lt

@[simp] lemma log_zero_left : ∀ b, log 0 b = 0 :=
log_of_left_le_one zero_le_one

@[simp] theorem log_zero_right (b : ordinal) : log b 0 = 0 :=
if b1 : 1 < b then begin
  rw [log_def b1, ← ordinal.le_zero, pred_le],
  apply cInf_le',
  dsimp,
  rw [succ_zero, opow_one],
  exact zero_lt_one.trans b1
end
else by simp only [log_of_not_one_lt_left b1]

@[simp] theorem log_one_left : ∀ b, log 1 b = 0 :=
log_of_left_le_one le_rfl

theorem succ_log_def {b x : ordinal} (hb : 1 < b) (hx : x ≠ 0) :
  succ (log b x) = Inf {o | x < b ^ o} :=
begin
  let t := Inf {o | x < b ^ o},
  have : x < b ^ t := Inf_mem (log_nonempty hb),
  rcases zero_or_succ_or_limit t with h|h|h,
  { refine ((one_le_iff_ne_zero.2 hx).not_lt _).elim,
    simpa only [h, opow_zero] },
  { rw [show log b x = pred t, from log_def hb x,
        succ_pred_iff_is_succ.2 h] },
  { rcases (lt_opow_of_limit (zero_lt_one.trans hb).ne' h).1 this with ⟨a, h₁, h₂⟩,
    exact h₁.not_le.elim ((le_cInf_iff'' (log_nonempty hb)).1 le_rfl a h₂) }
end

theorem lt_opow_succ_log_self {b : ordinal} (hb : 1 < b) (x : ordinal) : x < b ^ succ (log b x) :=
begin
  rcases eq_or_ne x 0 with rfl | hx,
  { apply opow_pos _ (zero_lt_one.trans hb) },
  { rw succ_log_def hb hx,
    exact Inf_mem (log_nonempty hb) }
end

theorem opow_log_le_self (b) {x : ordinal} (hx : x ≠ 0) : b ^ log b x ≤ x :=
begin
  rcases eq_or_ne b 0 with rfl | b0,
  { rw zero_opow',
    refine (sub_le_self _ _).trans (one_le_iff_ne_zero.2 hx) },
  rcases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with hb | rfl,
  { refine le_of_not_lt (λ h, (lt_succ (log b x)).not_le _),
    have := @cInf_le' _ _ {o | x < b ^ o} _ h,
    rwa ←succ_log_def hb hx at this },
  { rwa [one_opow, one_le_iff_ne_zero] }
end

/-- `opow b` and `log b` (almost) form a Galois connection. -/
theorem opow_le_iff_le_log {b x c : ordinal} (hb : 1 < b) (hx : x ≠ 0) : b ^ c ≤ x ↔ c ≤ log b x :=
⟨λ h, le_of_not_lt $ λ hn,
   (lt_opow_succ_log_self hb x).not_le $
   ((opow_le_opow_iff_right hb).2 (succ_le_of_lt hn)).trans h,
λ h, ((opow_le_opow_iff_right hb).2 h).trans (opow_log_le_self b hx)⟩

theorem lt_opow_iff_log_lt {b x c : ordinal} (hb : 1 < b) (hx : x ≠ 0) : x < b ^ c ↔ log b x < c :=
lt_iff_lt_of_le_iff_le (opow_le_iff_le_log hb hx)

theorem log_pos {b o : ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) : 0 < log b o :=
by rwa [←succ_le_iff, succ_zero, ←opow_le_iff_le_log hb ho, opow_one]

theorem log_eq_zero {b o : ordinal} (hbo : o < b) : log b o = 0 :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { exact log_zero_right b },
  cases le_or_lt b 1 with hb hb,
  { rcases le_one_iff.1 hb with rfl | rfl,
    { exact log_zero_left o },
    { exact log_one_left o } },
  { rwa [←ordinal.le_zero, ←lt_succ_iff, succ_zero, ←lt_opow_iff_log_lt hb ho, opow_one] }
end

@[mono] theorem log_mono_right (b) {x y : ordinal} (xy : x ≤ y) : log b x ≤ log b y :=
if hx : x = 0 then by simp only [hx, log_zero_right, ordinal.zero_le] else
if hb : 1 < b then
  (opow_le_iff_le_log hb (lt_of_lt_of_le (ordinal.pos_iff_ne_zero.2 hx) xy).ne').1 $
    (opow_log_le_self _ hx).trans xy
else by simp only [log_of_not_one_lt_left hb, ordinal.zero_le]

theorem log_le_self (b x : ordinal) : log b x ≤ x :=
if hx : x = 0 then by simp only [hx, log_zero_right, ordinal.zero_le] else
if hb : 1 < b then (right_le_opow _ hb).trans (opow_log_le_self b hx)
else by simp only [log_of_not_one_lt_left hb, ordinal.zero_le]

@[simp] theorem log_one_right (b : ordinal) : log b 1 = 0 :=
if hb : 1 < b then log_eq_zero hb else log_of_not_one_lt_left hb 1

theorem mod_opow_log_lt_self (b : ordinal) {o : ordinal} (ho : o ≠ 0) : o % b ^ log b o < o :=
begin
  rcases eq_or_ne b 0 with rfl | hb,
  { simpa using ordinal.pos_iff_ne_zero.2 ho },
  { exact (mod_lt _ $ opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho) }
end

theorem log_mod_opow_log_lt_log_self {b o : ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) :
  log b (o % b ^ log b o) < log b o :=
begin
  cases eq_or_ne (o % b ^ log b o) 0,
  { rw [h, log_zero_right],
    apply log_pos hb ho hbo },
  { rw [←succ_le_iff, succ_log_def hb h],
    apply cInf_le',
    apply mod_lt,
    rw ←ordinal.pos_iff_ne_zero,
    exact opow_pos _ (zero_lt_one.trans hb) }
end

lemma opow_mul_add_pos {b v : ordinal} (hb : b ≠ 0) (u) (hv : v ≠ 0) (w) : 0 < b ^ u * v + w :=
(opow_pos u $ ordinal.pos_iff_ne_zero.2 hb).trans_le $
  (le_mul_left _ $ ordinal.pos_iff_ne_zero.2 hv).trans $ le_add_right _ _

lemma opow_mul_add_lt_opow_mul_succ {b u w : ordinal} (v : ordinal) (hw : w < b ^ u) :
  b ^ u * v + w < b ^ u * (succ v) :=
by rwa [mul_succ, add_lt_add_iff_left]

lemma opow_mul_add_lt_opow_succ {b u v w : ordinal} (hvb : v < b) (hw : w < b ^ u) :
  b ^ u * v + w < b ^ (succ u) :=
begin
  convert (opow_mul_add_lt_opow_mul_succ v hw).trans_le (mul_le_mul_left' (succ_le_of_lt hvb) _),
  exact opow_succ b u
end

theorem log_opow_mul_add {b u v w : ordinal} (hb : 1 < b) (hv : v ≠ 0) (hvb : v < b)
  (hw : w < b ^ u) : log b (b ^ u * v + w) = u :=
begin
  have hne' := (opow_mul_add_pos (zero_lt_one.trans hb).ne' u hv w).ne',
  by_contra' hne,
  cases lt_or_gt_of_ne hne with h h,
  { rw ←lt_opow_iff_log_lt hb hne' at h,
    exact h.not_le ((le_mul_left _ (ordinal.pos_iff_ne_zero.2 hv)).trans (le_add_right _ _)) },
  { change _ < _ at h,
    rw [←succ_le_iff, ←opow_le_iff_le_log hb hne'] at h,
    exact (not_lt_of_le h) (opow_mul_add_lt_opow_succ hvb hw) }
end

theorem log_opow {b : ordinal} (hb : 1 < b) (x : ordinal) : log b (b ^ x) = x :=
begin
  convert log_opow_mul_add hb zero_ne_one.symm hb (opow_pos x (zero_lt_one.trans hb)),
  rw [add_zero, mul_one]
end

theorem div_opow_log_lt {b : ordinal} (o : ordinal) (hb : 1 < b) : o / b ^ log b o < b :=
begin
  rw [div_lt (opow_pos _ (zero_lt_one.trans hb)).ne', ←opow_succ],
  exact lt_opow_succ_log_self hb o
end

theorem add_log_le_log_mul {x y : ordinal} (b : ordinal) (hx : x ≠ 0) (hy : y ≠ 0) :
  log b x + log b y ≤ log b (x * y) :=
begin
  by_cases hb : 1 < b,
  { rw [←opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add],
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy) },
  simp only [log_of_not_one_lt_left hb, zero_add]
end

/-! ### Interaction with `nat.cast` -/

@[simp, norm_cast] theorem nat_cast_opow (m : ℕ) : ∀ n : ℕ, ((pow m n : ℕ) : ordinal) = m ^ n
| 0     := by simp
| (n+1) := by rw [pow_succ', nat_cast_mul, nat_cast_opow, nat.cast_succ, add_one_eq_succ, opow_succ]

local infixr (name := ordinal.pow) ^ := @pow ordinal ordinal ordinal.has_pow
theorem sup_opow_nat {o : ordinal} (ho : 0 < o) : sup (λ n : ℕ, o ^ n) = o ^ ω :=
begin
  rcases lt_or_eq_of_le (one_le_iff_pos.2 ho) with ho₁ | rfl,
  { exact (opow_is_normal ho₁).apply_omega },
  { rw one_opow,
    refine le_antisymm (sup_le (λ n, by rw one_opow)) _,
    convert le_sup _ 0,
    rw [nat.cast_zero, opow_zero] }
end

end ordinal

namespace tactic
open ordinal positivity

/-- Extension for the `positivity` tactic: `ordinal.opow` takes positive values on positive inputs.
-/
@[positivity]
meta def positivity_opow : expr → tactic strictness
| `(@has_pow.pow _ _ %%inst %%a %%b) := do
  strictness_a ← core a,
  match strictness_a with
  | positive p := positive <$> mk_app ``opow_pos [b, p]
  | _ := failed -- We already know that `0 ≤ x` for all `x : ordinal`
  end
| _ := failed

end tactic
