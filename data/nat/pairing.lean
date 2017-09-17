/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

Elegant pairing function.
-/
import data.nat.sqrt
open prod decidable

namespace nat

def mkpair (a b : nat) : nat :=
if a < b then b*b + a else a*a + a + b

def unpair (n : nat) : nat × nat :=
let s := sqrt n in
if n - s*s < s then (n - s*s, s) else (s, n - s*s - s)

theorem mkpair_unpair (n : nat) : mkpair (unpair n).1 (unpair n).2 = n :=
let s := sqrt n in begin
  simp [unpair], change sqrt n with s,
  by_cases n - s * s < s with h; simp [h, mkpair],
  { exact nat.add_sub_cancel' (sqrt_le _) },
  simp at h,
  suffices : n - s*s - s ≤ s,
  { simp [not_lt_of_ge this],
    rw [add_left_comm, nat.add_sub_cancel' h, nat.add_sub_cancel' (sqrt_le _)] },
  apply nat.sub_le_left_of_le_add, apply nat.sub_le_left_of_le_add,
  rw ← add_assoc, apply sqrt_le_add
end

theorem unpair_mkpair (a b : nat) : unpair (mkpair a b) = (a, b) :=
begin
  by_cases a < b; simp [h, mkpair],
  { have be : sqrt (a + b * b) = b,
    { rw [add_comm, sqrt_add_eq],
      exact le_trans (le_of_lt h) (le_add_left _ _) },
    simp [unpair, be, nat.add_sub_cancel, h] },
  { simp at h,
    have ae : sqrt (a + (b + a * a)) = a,
    { rw [← add_assoc, add_comm, sqrt_add_eq],
      exact add_le_add_left h _ },
    have : a ≤ a + (b + a * a) - a * a,
    { rw nat.add_sub_assoc (nat.le_add_left _ _), apply nat.le_add_right },
    simp [unpair, ae, not_lt_of_ge this],
    rw [nat.add_sub_assoc, nat.add_sub_cancel, nat.add_sub_cancel_left],
    apply nat.le_add_left }
end

theorem unpair_lt_aux {n : nat} (n1 : n ≥ 1) : (unpair n).1 < n :=
let s := sqrt n in begin
  simp [unpair], change sqrt n with s,
  by_cases n - s * s < s with h; simp [h],
  { exact lt_of_lt_of_le h (sqrt_le_self _) },
  { simp at h,
    have s0 : s > 0 := sqrt_pos.2 n1,
    exact lt_of_le_of_lt h (nat.sub_lt_self n1 (mul_pos s0 s0)) }
end

theorem unpair_lt (n : nat) : (unpair n).1 ≤ n :=
by cases n; [exact dec_trivial, apply le_of_lt (unpair_lt_aux (nat.succ_pos _))]

end nat
