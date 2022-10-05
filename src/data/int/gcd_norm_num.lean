/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.gcd
import tactic.norm_num

/-! ### Computation of the greatest common divisor and least common multiple

This file implements a `norm_num` plugin to evaluate terms like `nat.gcd 6 8 = 2`,
`nat.coprime 127 128`, and so on for {nat, int}.{gcd, lcm, coprime}.

 -/
open norm_num

namespace tactic
namespace norm_num

lemma int_gcd_helper' {d : ℕ} {x y a b : ℤ} (h₁ : (d:ℤ) ∣ x) (h₂ : (d:ℤ) ∣ y)
  (h₃ : x * a + y * b = d) : int.gcd x y = d :=
begin
  refine nat.dvd_antisymm _ (int.coe_nat_dvd.1 (int.dvd_gcd h₁ h₂)),
  rw [← int.coe_nat_dvd, ← h₃],
  apply dvd_add,
  { exact (int.gcd_dvd_left _ _).mul_right _ },
  { exact (int.gcd_dvd_right _ _).mul_right _ }
end

lemma nat_gcd_helper_dvd_left (x y a : ℕ) (h : x * a = y) : nat.gcd x y = x :=
nat.gcd_eq_left ⟨a, h.symm⟩

lemma nat_gcd_helper_dvd_right (x y a : ℕ) (h : y * a = x) : nat.gcd x y = y :=
nat.gcd_eq_right ⟨a, h.symm⟩

lemma nat_gcd_helper_2 (d x y a b u v tx ty : ℕ) (hu : d * u = x) (hv : d * v = y)
  (hx : x * a = tx) (hy : y * b = ty) (h : ty + d = tx) : nat.gcd x y = d :=
begin
  rw ← int.coe_nat_gcd, apply @int_gcd_helper' _ _ _ a (-b)
    (int.coe_nat_dvd.2 ⟨_, hu.symm⟩) (int.coe_nat_dvd.2 ⟨_, hv.symm⟩),
  rw [mul_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add'],
  norm_cast, rw [hx, hy, h]
end

lemma nat_gcd_helper_1 (d x y a b u v tx ty : ℕ) (hu : d * u = x) (hv : d * v = y)
  (hx : x * a = tx) (hy : y * b = ty) (h : tx + d = ty) : nat.gcd x y = d :=
(nat.gcd_comm _ _).trans $ nat_gcd_helper_2 _ _ _ _ _ _ _ _ _ hv hu hy hx h

lemma nat_lcm_helper (x y d m n : ℕ) (hd : nat.gcd x y = d) (d0 : 0 < d)
  (xy : x * y = n) (dm : d * m = n) : nat.lcm x y = m :=
(nat.mul_right_inj d0).1 $ by rw [dm, ← xy, ← hd, nat.gcd_mul_lcm]

lemma nat_coprime_helper_zero_left (x : ℕ) (h : 1 < x) : ¬ nat.coprime 0 x :=
mt (nat.coprime_zero_left _).1 $ ne_of_gt h

lemma nat_coprime_helper_zero_right (x : ℕ) (h : 1 < x) : ¬ nat.coprime x 0 :=
mt (nat.coprime_zero_right _).1 $ ne_of_gt h

lemma nat_coprime_helper_1 (x y a b tx ty : ℕ)
  (hx : x * a = tx) (hy : y * b = ty) (h : tx + 1 = ty) : nat.coprime x y :=
nat_gcd_helper_1 _ _ _ _ _ _ _ _ _ (one_mul _) (one_mul _) hx hy h

lemma nat_coprime_helper_2 (x y a b tx ty : ℕ)
  (hx : x * a = tx) (hy : y * b = ty) (h : ty + 1 = tx) : nat.coprime x y :=
nat_gcd_helper_2 _ _ _ _ _ _ _ _ _ (one_mul _) (one_mul _) hx hy h

lemma nat_not_coprime_helper (d x y u v : ℕ) (hu : d * u = x) (hv : d * v = y)
  (h : 1 < d) : ¬ nat.coprime x y :=
nat.not_coprime_of_dvd_of_dvd h ⟨_, hu.symm⟩ ⟨_, hv.symm⟩

lemma int_gcd_helper (x y : ℤ) (nx ny d : ℕ) (hx : (nx:ℤ) = x) (hy : (ny:ℤ) = y)
  (h : nat.gcd nx ny = d) : int.gcd x y = d :=
by rwa [← hx, ← hy, int.coe_nat_gcd]

lemma int_gcd_helper_neg_left (x y : ℤ) (d : ℕ) (h : int.gcd x y = d) : int.gcd (-x) y = d :=
by rw int.gcd at h ⊢; rwa int.nat_abs_neg

lemma int_gcd_helper_neg_right (x y : ℤ) (d : ℕ) (h : int.gcd x y = d) : int.gcd x (-y) = d :=
by rw int.gcd at h ⊢; rwa int.nat_abs_neg

lemma int_lcm_helper (x y : ℤ) (nx ny d : ℕ) (hx : (nx:ℤ) = x) (hy : (ny:ℤ) = y)
  (h : nat.lcm nx ny = d) : int.lcm x y = d :=
by rwa [← hx, ← hy, int.coe_nat_lcm]

lemma int_lcm_helper_neg_left (x y : ℤ) (d : ℕ) (h : int.lcm x y = d) : int.lcm (-x) y = d :=
by rw int.lcm at h ⊢; rwa int.nat_abs_neg

lemma int_lcm_helper_neg_right (x y : ℤ) (d : ℕ) (h : int.lcm x y = d) : int.lcm x (-y) = d :=
by rw int.lcm at h ⊢; rwa int.nat_abs_neg

/-- Evaluates the `nat.gcd` function. -/
meta def prove_gcd_nat (c : instance_cache) (ex ey : expr) :
  tactic (instance_cache × expr × expr) := do
  x ← ex.to_nat,
  y ← ey.to_nat,
  match x, y with
  | 0, _ := pure (c, ey, `(nat.gcd_zero_left).mk_app [ey])
  | _, 0 := pure (c, ex, `(nat.gcd_zero_right).mk_app [ex])
  | 1, _ := pure (c, `(1:ℕ), `(nat.gcd_one_left).mk_app [ey])
  | _, 1 := pure (c, `(1:ℕ), `(nat.gcd_one_right).mk_app [ex])
  | _, _ := do
    let (d, a, b) := nat.xgcd_aux x 1 0 y 0 1,
    if d = x then do
      (c, ea) ← c.of_nat (y / x),
      (c, _, p) ← prove_mul_nat c ex ea,
      pure (c, ex, `(nat_gcd_helper_dvd_left).mk_app [ex, ey, ea, p])
    else if d = y then do
      (c, ea) ← c.of_nat (x / y),
      (c, _, p) ← prove_mul_nat c ey ea,
      pure (c, ey, `(nat_gcd_helper_dvd_right).mk_app [ex, ey, ea, p])
    else do
      (c, ed) ← c.of_nat d,
      (c, ea) ← c.of_nat a.nat_abs,
      (c, eb) ← c.of_nat b.nat_abs,
      (c, eu) ← c.of_nat (x / d),
      (c, ev) ← c.of_nat (y / d),
      (c, _, pu) ← prove_mul_nat c ed eu,
      (c, _, pv) ← prove_mul_nat c ed ev,
      (c, etx, px) ← prove_mul_nat c ex ea,
      (c, ety, py) ← prove_mul_nat c ey eb,
      (c, p) ← if a ≥ 0 then prove_add_nat c ety ed etx else prove_add_nat c etx ed ety,
      let pf : expr := if a ≥ 0 then `(nat_gcd_helper_2) else `(nat_gcd_helper_1),
      pure (c, ed, pf.mk_app [ed, ex, ey, ea, eb, eu, ev, etx, ety, pu, pv, px, py, p])
  end

/-- Evaluates the `nat.lcm` function. -/
meta def prove_lcm_nat (c : instance_cache) (ex ey : expr) :
  tactic (instance_cache × expr × expr) := do
  x ← ex.to_nat,
  y ← ey.to_nat,
  match x, y with
  | 0, _ := pure (c, `(0:ℕ), `(nat.lcm_zero_left).mk_app [ey])
  | _, 0 := pure (c, `(0:ℕ), `(nat.lcm_zero_right).mk_app [ex])
  | 1, _ := pure (c, ey, `(nat.lcm_one_left).mk_app [ey])
  | _, 1 := pure (c, ex, `(nat.lcm_one_right).mk_app [ex])
  | _, _ := do
    (c, ed, pd) ← prove_gcd_nat c ex ey,
    (c, p0) ← prove_pos c ed,
    (c, en, xy) ← prove_mul_nat c ex ey,
    d ← ed.to_nat,
    (c, em) ← c.of_nat ((x * y) / d),
    (c, _, dm) ← prove_mul_nat c ed em,
    pure (c, em, `(nat_lcm_helper).mk_app [ex, ey, ed, em, en, pd, p0, xy, dm])
  end

/-- Evaluates the `int.gcd` function. -/
meta def prove_gcd_int (zc nc : instance_cache) : expr → expr →
  tactic (instance_cache × instance_cache × expr × expr)
| x y := match match_neg x with
  | some x := do
    (zc, nc, d, p) ← prove_gcd_int x y,
    pure (zc, nc, d, `(int_gcd_helper_neg_left).mk_app [x, y, d, p])
  | none := match match_neg y with
    | some y := do
      (zc, nc, d, p) ← prove_gcd_int x y,
      pure (zc, nc, d, `(int_gcd_helper_neg_right).mk_app [x, y, d, p])
    | none := do
      (zc, nc, nx, px) ← prove_nat_uncast zc nc x,
      (zc, nc, ny, py) ← prove_nat_uncast zc nc y,
      (nc, d, p) ← prove_gcd_nat nc nx ny,
      pure (zc, nc, d, `(int_gcd_helper).mk_app [x, y, nx, ny, d, px, py, p])
    end
  end

/-- Evaluates the `int.lcm` function. -/
meta def prove_lcm_int (zc nc : instance_cache) : expr → expr →
  tactic (instance_cache × instance_cache × expr × expr)
| x y := match match_neg x with
  | some x := do
    (zc, nc, d, p) ← prove_lcm_int x y,
    pure (zc, nc, d, `(int_lcm_helper_neg_left).mk_app [x, y, d, p])
  | none := match match_neg y with
    | some y := do
      (zc, nc, d, p) ← prove_lcm_int x y,
      pure (zc, nc, d, `(int_lcm_helper_neg_right).mk_app [x, y, d, p])
    | none := do
      (zc, nc, nx, px) ← prove_nat_uncast zc nc x,
      (zc, nc, ny, py) ← prove_nat_uncast zc nc y,
      (nc, d, p) ← prove_lcm_nat nc nx ny,
      pure (zc, nc, d, `(int_lcm_helper).mk_app [x, y, nx, ny, d, px, py, p])
    end
  end

/-- Evaluates the `nat.coprime` function. -/
meta def prove_coprime_nat (c : instance_cache) (ex ey : expr) :
  tactic (instance_cache × (expr ⊕ expr)) := do
  x ← ex.to_nat,
  y ← ey.to_nat,
  match x, y with
  | 1, _ := pure (c, sum.inl $ `(nat.coprime_one_left).mk_app [ey])
  | _, 1 := pure (c, sum.inl $ `(nat.coprime_one_right).mk_app [ex])
  | 0, 0 := pure (c, sum.inr `(nat.not_coprime_zero_zero))
  | 0, _ := do
    c ← mk_instance_cache `(ℕ),
    (c, p) ← prove_lt_nat c `(1) ey,
    pure (c, sum.inr $ `(nat_coprime_helper_zero_left).mk_app [ey, p])
  | _, 0 := do
    c ← mk_instance_cache `(ℕ),
    (c, p) ← prove_lt_nat c `(1) ex,
    pure (c, sum.inr $ `(nat_coprime_helper_zero_right).mk_app [ex, p])
  | _, _ := do
    c ← mk_instance_cache `(ℕ),
    let (d, a, b) := nat.xgcd_aux x 1 0 y 0 1,
    if d = 1 then do
      (c, ea) ← c.of_nat a.nat_abs,
      (c, eb) ← c.of_nat b.nat_abs,
      (c, etx, px) ← prove_mul_nat c ex ea,
      (c, ety, py) ← prove_mul_nat c ey eb,
      (c, p) ← if a ≥ 0 then prove_add_nat c ety `(1) etx else prove_add_nat c etx `(1) ety,
      let pf : expr := if a ≥ 0 then `(nat_coprime_helper_2) else `(nat_coprime_helper_1),
      pure (c, sum.inl $ pf.mk_app [ex, ey, ea, eb, etx, ety, px, py, p])
    else do
      (c, ed) ← c.of_nat d,
      (c, eu) ← c.of_nat (x / d),
      (c, ev) ← c.of_nat (y / d),
      (c, _, pu) ← prove_mul_nat c ed eu,
      (c, _, pv) ← prove_mul_nat c ed ev,
      (c, p) ← prove_lt_nat c `(1) ed,
      pure (c, sum.inr $ `(nat_not_coprime_helper).mk_app [ed, ex, ey, eu, ev, pu, pv, p])
  end

/-- Evaluates the `gcd`, `lcm`, and `coprime` functions. -/
@[norm_num] meta def eval_gcd : expr → tactic (expr × expr)
| `(nat.gcd %%ex %%ey) := do
    c ← mk_instance_cache `(ℕ),
    prod.snd <$> prove_gcd_nat c ex ey
| `(nat.lcm %%ex %%ey) := do
    c ← mk_instance_cache `(ℕ),
    prod.snd <$> prove_lcm_nat c ex ey
| `(nat.coprime %%ex %%ey) := do
    c ← mk_instance_cache `(ℕ),
    prove_coprime_nat c ex ey >>= sum.elim true_intro false_intro ∘ prod.snd
| `(int.gcd %%ex %%ey) := do
    zc ← mk_instance_cache `(ℤ),
    nc ← mk_instance_cache `(ℕ),
    (prod.snd ∘ prod.snd) <$> prove_gcd_int zc nc ex ey
| `(int.lcm %%ex %%ey) := do
    zc ← mk_instance_cache `(ℤ),
    nc ← mk_instance_cache `(ℕ),
    (prod.snd ∘ prod.snd) <$> prove_lcm_int zc nc ex ey
| _ := failed

end norm_num
end tactic
