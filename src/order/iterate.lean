/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import order.basic
import logic.function.iterate
import data.nat.basic

/-!
# Inequalities on iterates

In this file we prove some inequalities comparing `f^[n] x` and `g^[n] x` where `f` and `g` are
two self-maps that commute with each other.

Current selection of inequalities is motivated by formalization of the rotation number of
a circle homeomorphism.
-/
variables {α : Type*}

namespace function

namespace commute

section preorder

variables [preorder α] {f g : α → α}

lemma iterate_le_of_map_le (h : commute f g) (hf : monotone f)  (hg : monotone g)
  {x} (hx : f x ≤ g x) (n : ℕ) :
  f^[n] x ≤ (g^[n]) x :=
nat.rec_on n (le_refl _) $ λ n ihn,
calc f^[n+1] x = (f^[n]) (f x) : iterate_succ_apply f n x
           ... ≤ (f^[n]) (g x) : hf.iterate n hx
           ... = g (f^[n] x)   : h.iterate_left n x
           ... ≤ g (g^[n] x)   : hg ihn
           ... = (g^[n+1]) x   : (iterate_succ_apply' g n x).symm

lemma iterate_pos_lt_of_map_lt (h : commute f g) (hf : monotone f) (hg : strict_mono g)
  {x} (hx : f x < g x) {n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x :=
flip (nat.le_rec_on hn) hx $ λ n ihn,
calc f^[n+1] x = (f^[n]) (f x) : iterate_succ_apply f n x
           ... ≤ (f^[n]) (g x) : hf.iterate n (le_of_lt hx)
           ... = g (f^[n] x)   : h.iterate_left n x
           ... < g (g^[n] x)   : hg ihn
           ... = (g^[n+1]) x   : (iterate_succ_apply' g n x).symm

lemma iterate_pos_lt_of_map_lt' (h : commute f g) (hf : strict_mono f) (hg : monotone g)
  {x} (hx : f x < g x) {n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x :=
@iterate_pos_lt_of_map_lt (order_dual α) _ g f h.symm hg.order_dual hf.order_dual x hx n hn

end preorder

variables [linear_order α] {f g : α → α}

lemma iterate_pos_lt_iff_map_lt (h : commute f g) (hf : monotone f)
  (hg : strict_mono g) {x n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x ↔ f x < g x :=
begin
  rcases lt_trichotomy (f x) (g x) with H|H|H,
  { simp only [*, iterate_pos_lt_of_map_lt] },
  { simp only [*, h.iterate_eq_of_map_eq, lt_irrefl] },
  { simp only [lt_asymm H, lt_asymm (h.symm.iterate_pos_lt_of_map_lt' hg hf H hn)] }
end

lemma iterate_pos_lt_iff_map_lt' (h : commute f g) (hf : strict_mono f)
  (hg : monotone g) {x n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x ↔ f x < g x :=
@iterate_pos_lt_iff_map_lt (order_dual α) _ _ _ h.symm hg.order_dual hf.order_dual x n hn

lemma iterate_pos_le_iff_map_le (h : commute f g) (hf : monotone f)
  (hg : strict_mono g) {x n} (hn : 0 < n) :
  f^[n] x ≤ (g^[n]) x ↔ f x ≤ g x :=
by simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt' hg hf hn)

lemma iterate_pos_le_iff_map_le' (h : commute f g) (hf : strict_mono f)
  (hg : monotone g) {x n} (hn : 0 < n) :
  f^[n] x ≤ (g^[n]) x ↔ f x ≤ g x :=
by simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt hg hf hn)

lemma iterate_pos_eq_iff_map_eq (h : commute f g) (hf : monotone f)
  (hg : strict_mono g) {x n} (hn : 0 < n) :
  f^[n] x = (g^[n]) x ↔ f x = g x :=
by simp only [le_antisymm_iff, h.iterate_pos_le_iff_map_le hf hg hn,
  h.symm.iterate_pos_le_iff_map_le' hg hf hn]

end commute

end function

namespace monotone

variables [preorder α] {f g : α → α}

open function

/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
lemma iterate_le_of_le (hf : monotone f) (h : f ≤ g) (n : ℕ) :
  f^[n] ≤ (g^[n]) :=
nat.rec_on n (le_refl id) $ λ n ihn x,
calc f^[n] (f x) ≤ (f^[n]) (g x) : hf.iterate n (h x)
             ... ≤ (g^[n+1] x)   : ihn (g x)

/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
lemma iterate_ge_of_ge (hg : monotone g) (h : f ≤ g) (n : ℕ) :
  f^[n] ≤ (g^[n]) :=
hg.order_dual.iterate_le_of_le h n

end monotone
