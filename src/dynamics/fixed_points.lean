/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.nat.basic
import logic.function.iterate

/-!
# Fixed and periodic points of a self-map

In this file we define the following predicates in `function` namespace:

* `is_fixed_pt f x := f x = x`
-/

universe u

variables {α : Type u} {f g : α → α} {x : α} {m n k : ℕ}

namespace function

/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
def is_fixed_pt (f : α → α) (x : α) := f x = x

-- TODO: why this is not `rfl`?
lemma is_fixed_pt_id (x : α) : is_fixed_pt id x := by rw [is_fixed_pt, id]

namespace is_fixed_pt

instance [h : decidable_eq α] {f : α → α} {x : α} : decidable (is_fixed_pt f x) :=
h (f x) x

protected lemma eq (hf : is_fixed_pt f x) : f x = x := hf

lemma comp (hf : is_fixed_pt f x) (hg : is_fixed_pt g x) : is_fixed_pt (f ∘ g) x :=
calc f (g x) = f x : congr_arg f hg
         ... = x   : hf

lemma iterate (hf : is_fixed_pt f x) (n : ℕ) : is_fixed_pt (f^[n]) x :=
nat.rec_on n rfl $ λ n ihn, ihn.comp hf

lemma left_of_comp (hfg : is_fixed_pt (f ∘ g) x) (hg : is_fixed_pt g x) : is_fixed_pt f x :=
calc f x = f (g x) : congr_arg f hg.symm
     ... = x       : hfg

lemma to_left_inverse (hf : is_fixed_pt f x) (h : left_inverse g f) : is_fixed_pt g x :=
calc g x = g (f x) : congr_arg g hf.symm
     ... = x       : h x

end is_fixed_pt

/-- A point `x` is a periodic point of `f : α → α` of period `n` if `f^n x = x`.
Note that we do not require `0 < n` in this definition. Most theorems about periodic points
need this assumption. -/
def is_periodic_pt (f : α → α) (n : ℕ) (x : α) := is_fixed_pt (f^[n]) x

lemma is_fixed_pt.is_periodic_pt (hf : is_fixed_pt f x) (n : ℕ) : is_periodic_pt f n x :=
hf.iterate n

lemma is_preiodic_id (n : ℕ) (x : α) : is_periodic_pt id n x := (is_fixed_pt_id x).is_periodic_pt n

lemma is_periodic_pt_zero (f : α → α) (x : α) : is_periodic_pt f 0 x := is_fixed_pt_id x

namespace is_periodic_pt

instance [decidable_eq α] {f : α → α} {n : ℕ} {x : α} : decidable (is_periodic_pt f n x) :=
is_fixed_pt.decidable

protected lemma is_fixed_pt (hf : is_periodic_pt f n x) : is_fixed_pt (f^[n]) x := hf

protected lemma add (hn : is_periodic_pt f n x) (hm : is_periodic_pt f m x) :
  is_periodic_pt f (n + m) x :=
by { rw [is_periodic_pt, nat.iterate_add], exact hn.comp hm }

lemma left_of_add (hn : is_periodic_pt f (n + m) x) (hm : is_periodic_pt f m x) :
  is_periodic_pt f n x :=
by { rw [is_periodic_pt, nat.iterate_add] at hn, exact hn.left_of_comp hm }

lemma right_of_add (hn : is_periodic_pt f (n + m) x) (hm : is_periodic_pt f n x) :
  is_periodic_pt f m x :=
by { rw add_comm at hn, exact hn.left_of_add hm }

protected lemma sub (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) :
  is_periodic_pt f (m - n) x :=
begin
  cases le_total n m with h h,
  { refine left_of_add _ hn,
    rwa [nat.sub_add_cancel h] },
  { rw [nat.sub_eq_zero_of_le h],
    apply is_periodic_pt_zero }
end

protected lemma mul_const (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (m * n) x :=
by simp only [is_periodic_pt, nat.iterate_mul, hm.is_fixed_pt.iterate n]

protected lemma const_mul (hm : is_periodic_pt f m x) (n : ℕ) : is_periodic_pt f (n * m) x :=
by simp only [mul_comm n, hm.mul_const n]

lemma trans_dvd (hm : is_periodic_pt f m x) {n : ℕ} (hn : m ∣ n) : is_periodic_pt f n x :=
let ⟨k, hk⟩ := hn in hk.symm ▸ hm.mul_const k

protected lemma iterate (hf : is_periodic_pt f n x) (m : ℕ) : is_periodic_pt (f^[m]) n x :=
begin
  rw [is_periodic_pt, ← nat.iterate_mul, mul_comm, nat.iterate_mul],
  exact hf.is_fixed_pt.iterate m
end

protected lemma mod (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) :
  is_periodic_pt f (m % n) x :=
begin
  rw [← nat.mod_add_div m n] at hm,
  exact hm.left_of_add (hn.mul_const _)
end

protected lemma gcd (hm : is_periodic_pt f m x) (hn : is_periodic_pt f n x) :
  is_periodic_pt f (m.gcd n) x :=
begin
  revert hm hn,
  refine nat.gcd.induction m n (λ n h0 hn, _) (λ m n hm ih hm hn, _),
  { rwa [nat.gcd_zero_left], },
  { rw [nat.gcd_rec],
    exact ih (hn.mod hm) hm }
end

end is_periodic_pt

/-- The set of fixed points of a map `f : α → α`. -/
def fixed_points (f : α → α) : set α := {x : α | is_fixed_pt f x}

@[simp] lemma mem_fixed_points : x ∈ fixed_points f ↔ is_fixed_pt f x := iff.rfl

/-- The set of periodic points of a map `f : α → α`. -/
def periodic_pts (f : α → α) : set α := {x : α | ∃ n, 0 < n ∧ is_periodic_pt f n x}

lemma mk_mem_periodic_pts (hn : 0 < n) (hx : is_periodic_pt f n x) :
  x ∈ periodic_pts f :=
⟨n, hn, hx⟩

open_locale classical

noncomputable theory

/-- Minimal period of a point `x` under an endomorphism `f`. -/
def minimal_period (f : α → α) (x : α) :=
if h : x ∈ periodic_pts f then nat.find h else 0

lemma is_periodic_pt_minimal_period (f : α → α) (x : α) :
  is_periodic_pt f (minimal_period f x) x :=
begin
  delta minimal_period,
  split_ifs with hx,
  { exact (nat.find_spec hx).2 },
  { exact is_periodic_pt_zero f x }
end

lemma minimal_period_pos_of_mem_periodic_pts (hx : x ∈ periodic_pts f) :
  0 < minimal_period f x :=
by simp only [minimal_period, dif_pos hx, (nat.find_spec hx).1]

lemma is_periodic_pt.minimal_period_pos (hn : 0 < n) (hx : is_periodic_pt f n x) :
  0 < minimal_period f x :=
minimal_period_pos_of_mem_periodic_pts $ mk_mem_periodic_pts hn hx

lemma minimal_period_pos_iff_mem_periodic_pts :
  0 < minimal_period f x ↔ x ∈ periodic_pts f :=
⟨classical.not_imp_not.1 $ λ h,
  by simp only [minimal_period, dif_neg h, lt_irrefl 0, not_false_iff],
  minimal_period_pos_of_mem_periodic_pts⟩

lemma is_periodic_pt.minimal_period_le (hn : 0 < n) (hx : is_periodic_pt f n x) :
  minimal_period f x ≤ n :=
begin
  rw [minimal_period, dif_pos (mk_mem_periodic_pts hn hx)],
  exact nat.find_min' (mk_mem_periodic_pts hn hx) ⟨hn, hx⟩
end

lemma is_periodic_pt.eq_zero_of_lt_minimal_period (hx : is_periodic_pt f n x)
  (hn : n < minimal_period f x) :
  n = 0 :=
eq.symm $ (eq_or_lt_of_le $ zero_le n).resolve_right $ λ hn0,
not_lt.2 (hx.minimal_period_le hn0) hn

lemma is_periodic_pt.minimal_period_dvd (hx : is_periodic_pt f n x) :
  minimal_period f x ∣ n :=
(eq_or_lt_of_le $ zero_le n).elim (λ hn0, hn0 ▸ dvd_zero _) $ λ hn0,
(nat.dvd_iff_mod_eq_zero _ _).2 $
(hx.mod $ is_periodic_pt_minimal_period f x).eq_zero_of_lt_minimal_period $
nat.mod_lt _ $ hx.minimal_period_pos hn0

lemma is_periodic_pt_iff_minimal_period_dvd :
  is_periodic_pt f n x ↔ minimal_period f x ∣ n :=
⟨is_periodic_pt.minimal_period_dvd,
  λ h, (is_periodic_pt_minimal_period f x).trans_dvd h⟩

end function
