/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import logic.function.iterate
import data.nat.basic

/-!
# Inequalities on iterates

In this file we prove some inequalities comparing `f^[n] x` and `g^[n] x` where `f` and `g` are
two self-maps that commute with each other.

Current selection of inequalities is motivated by formalization of the rotation number of
a circle homeomorphism.
-/
variables {α β : Type*}
open function

namespace monotone

variables [preorder α] {f : α → α} {x y : ℕ → α}

/-!
### Comparison of two sequences

If $f$ is a monotone function, then $∀ k, x_{k+1} ≤ f(x_k)$ implies that $x_k$ grows slower than
$f^k(x_0)$, and similarly for the reversed inequalities. If $x_k$ and $y_k$ are two sequences such
that $x_{k+1} ≤ f(x_k)$ and $y_{k+1} ≥ f(y_k)$ for all $k < n$, then $x_0 ≤ y_0$ implies
$x_n ≤ y_n$, see `monotone.seq_le_seq`.

If some of the inequalities in this lemma are strict, then we have $x_n < y_n$. The rest of the
lemmas in this section formalize this fact for different inequalities made strict.
-/

lemma seq_le_seq (hf : monotone f) (n : ℕ) (h₀ : x 0 ≤ y 0)
  (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) :
  x n ≤ y n :=
begin
  induction n with n ihn,
  { exact h₀ },
  { refine (hx _ n.lt_succ_self).trans ((hf $ ihn _ _).trans (hy _ n.lt_succ_self)),
    exact λ k hk, hx _ (hk.trans n.lt_succ_self),
    exact λ k hk, hy _ (hk.trans n.lt_succ_self) }
end

lemma seq_pos_lt_seq_of_lt_of_le (hf : monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
  (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) :
  x n < y n :=
begin
  induction n with n ihn, { exact hn.false.elim },
  suffices : x n ≤ y n,
    from (hx n n.lt_succ_self).trans_le ((hf this).trans $ hy n n.lt_succ_self),
  cases n, { exact h₀ },
  refine (ihn n.zero_lt_succ (λ k hk, hx _ _) (λ k hk, hy _ _)).le;
    exact hk.trans n.succ.lt_succ_self
end

lemma seq_pos_lt_seq_of_le_of_lt (hf : monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
  (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) :
  x n < y n :=
hf.dual.seq_pos_lt_seq_of_lt_of_le hn h₀ hy hx

lemma seq_lt_seq_of_lt_of_le (hf : monotone f) (n : ℕ) (h₀ : x 0 < y 0)
  (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) :
  x n < y n :=
by { cases n, exacts [h₀, hf.seq_pos_lt_seq_of_lt_of_le n.zero_lt_succ h₀.le hx hy] }

lemma seq_lt_seq_of_le_of_lt (hf : monotone f) (n : ℕ) (h₀ : x 0 < y 0)
  (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) :
  x n < y n :=
hf.dual.seq_lt_seq_of_lt_of_le n h₀ hy hx

/-!
### Iterates of two functions

In this section we compare the iterates of a monotone function `f : α → α` to iterates of any
function `g : β → β`. If `h : β → α` satisfies `h ∘ g ≤ f ∘ h`, then `h (g^[n] x)` grows slower
than `f^[n] (h x)`, and similarly for the reversed inequality.

Then we specialize these two lemmas to the case `β = α`, `h = id`.
-/

variables {g : β → β} {h : β → α}
open function

lemma le_iterate_comp_of_le (hf : monotone f) (H : h ∘ g ≤ f ∘ h) (n : ℕ) :
  h ∘ (g^[n]) ≤ (f^[n]) ∘ h :=
λ x, by refine hf.seq_le_seq n _ (λ k hk, _) (λ k hk, _); simp [iterate_succ', H _]

lemma iterate_comp_le_of_le (hf : monotone f) (H : f ∘ h ≤ h ∘ g) (n : ℕ) :
  f^[n] ∘ h ≤ h ∘ (g^[n]) :=
hf.dual.le_iterate_comp_of_le H n

/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
lemma iterate_le_of_le {g : α → α} (hf : monotone f) (h : f ≤ g) (n : ℕ) :
  f^[n] ≤ (g^[n]) :=
hf.iterate_comp_le_of_le h n

/-- If `f ≤ g` and `g` is monotone, then `f^[n] ≤ g^[n]`. -/
lemma le_iterate_of_le {g : α → α} (hg : monotone g) (h : f ≤ g) (n : ℕ) :
  f^[n] ≤ (g^[n]) :=
hg.dual.iterate_le_of_le h n

end monotone

/-!
### Comparison of iterations and the identity function

If $f(x) ≤ x$ for all $x$ (we express this as `f ≤ id` in the code), then the same is true for
any iterate of $f$, and similarly for the reversed inequality.
-/

namespace function

section preorder
variables [preorder α] {f : α → α}

/-- If $x ≤ f x$ for all $x$ (we write this as `id ≤ f`), then the same is true for any iterate
`f^[n]` of `f`. -/
lemma id_le_iterate_of_id_le (h : id ≤ f) (n : ℕ) : id ≤ (f^[n]) :=
by simpa only [iterate_id] using monotone_id.iterate_le_of_le h n

lemma iterate_le_id_of_le_id (h : f ≤ id) (n : ℕ) : (f^[n]) ≤ id :=
@id_le_iterate_of_id_le (order_dual α) _ f h n

lemma monotone_iterate_of_id_le (h : id ≤ f) : monotone (λ m, f^[m]) :=
monotone_nat_of_le_succ $ λ n x, by { rw iterate_succ_apply', exact h _ }

lemma antitone_iterate_of_le_id (h : f ≤ id) : antitone (λ m, f^[m]) :=
λ m n hmn, @monotone_iterate_of_id_le (order_dual α) _ f h m n hmn

end preorder

/-!
### Iterates of commuting functions

If `f` and `g` are monotone and commute, then `f x ≤ g x` implies `f^[n] x ≤ g^[n] x`, see
`function.commute.iterate_le_of_map_le`. We also prove two strict inequality versions of this lemma,
as well as `iff` versions.
-/

namespace commute

section preorder
variables [preorder α] {f g : α → α}

lemma iterate_le_of_map_le (h : commute f g) (hf : monotone f)  (hg : monotone g)
  {x} (hx : f x ≤ g x) (n : ℕ) :
  f^[n] x ≤ (g^[n]) x :=
by refine hf.seq_le_seq n _ (λ k hk, _) (λ k hk, _);
  simp [iterate_succ' f, h.iterate_right _ _, hg.iterate _ hx]

lemma iterate_pos_lt_of_map_lt (h : commute f g) (hf : monotone f) (hg : strict_mono g)
  {x} (hx : f x < g x) {n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x :=
by refine hf.seq_pos_lt_seq_of_le_of_lt hn _ (λ k hk, _) (λ k hk, _);
  simp [iterate_succ' f, h.iterate_right _ _, hg.iterate _ hx]

lemma iterate_pos_lt_of_map_lt' (h : commute f g) (hf : strict_mono f) (hg : monotone g)
  {x} (hx : f x < g x) {n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x :=
@iterate_pos_lt_of_map_lt (order_dual α) _ g f h.symm hg.dual hf.dual x hx n hn

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
@iterate_pos_lt_iff_map_lt (order_dual α) _ _ _ h.symm hg.dual hf.dual x n hn

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

variables [preorder α] {f : α → α} {x : α}

/-- If `f` is a monotone map and `x ≤ f x` at some point `x`, then the iterates `f^[n] x` form
a monotone sequence. -/
lemma monotone_iterate_of_le_map (hf : monotone f) (hx : x ≤ f x) : monotone (λ n, f^[n] x) :=
monotone_nat_of_le_succ $ λ n, by { rw iterate_succ_apply, exact hf.iterate n hx  }

/-- If `f` is a monotone map and `f x ≤ x` at some point `x`, then the iterates `f^[n] x` form
a antitone sequence. -/
lemma antitone_iterate_of_map_le (hf : monotone f) (hx : f x ≤ x) : antitone (λ n, f^[n] x) :=
hf.dual.monotone_iterate_of_le_map hx

end monotone

namespace strict_mono

variables [preorder α] {f : α → α} {x : α}

/-- If `f` is a strictly monotone map and `x < f x` at some point `x`, then the iterates `f^[n] x`
form a strictly monotone sequence. -/
lemma strict_mono_iterate_of_lt_map (hf : strict_mono f) (hx : x < f x) :
  strict_mono (λ n, f^[n] x) :=
strict_mono_nat_of_lt_succ $ λ n, by { rw iterate_succ_apply, exact hf.iterate n hx  }

/-- If `f` is a strictly antitone map and `f x < x` at some point `x`, then the iterates `f^[n] x`
form a strictly antitone sequence. -/
lemma strict_anti_iterate_of_map_lt (hf : strict_mono f) (hx : f x < x) :
  strict_anti (λ n, f^[n] x) :=
hf.dual.strict_mono_iterate_of_lt_map hx

end strict_mono
