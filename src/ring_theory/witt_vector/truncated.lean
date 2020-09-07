/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.basic

/-!

# Truncated Witt vectors

-/

noncomputable theory

section defs

variables (p : ℕ) [fact p.prime] (n : ℕ) (R : Type*) [comm_ring R]

local notation `𝕎` := witt_vector p -- type as `\bbW`

@[derive comm_ring]
def truncated_witt_vector :=
(witt_vector.ideal p R n).quotient

variables {p} {R}

def witt_vector.truncate : 𝕎 R →+* truncated_witt_vector p n R :=
ideal.quotient.mk _

-- huh? It seems that `p` is nevertheless an explicit argument of `truncate`...

end defs

namespace truncated_witt_vector

variables (p : ℕ) [fact p.prime] {n : ℕ} {R : Type*} [comm_ring R]

local notation `𝕎` := witt_vector p -- type as `\bbW`

def mk (x : fin n → R) : truncated_witt_vector p n R :=
witt_vector.truncate p n $ witt_vector.mk p $
λ i, if h : i < n then x ⟨i, h⟩ else 0

variable {p}

def coeff (i : fin n) : truncated_witt_vector p n R → R :=
quot.lift (λ x : witt_vector p R, x.coeff i)
begin
  intros x y h,
  change x - y ∈ (witt_vector.ideal p R n) at h,
  set z := x - y with hz,
  have hx : x = z + y, { simp only [sub_add_cancel] },
  dsimp,
  rw [hx, witt_vector.add_coeff],
  -- hmmm, `witt_add_vars` is not good enough for this one :sad:
  -- the first `n` coeffs of `z` are `0`, by assumption
  -- this is enough, but we need a better lemma for this
  sorry
end

variables (p R)
def truncate {m : ℕ} (hm : n ≤ m) : truncated_witt_vector p m R →+* truncated_witt_vector p n R :=
ideal.quotient.lift _ (witt_vector.truncate p n)
begin
  intros w hw,
  rw [witt_vector.truncate, ideal.quotient.eq_zero_iff_mem],
  simp only [witt_vector.mem_ideal_iff] at *,
  intros i hi,
  apply hw,
  linarith
end

@[simp]
lemma truncate_comp {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) :
  (truncate p R h1).comp (truncate p R h2) = truncate p R (h1.trans h2) :=
by ext ⟨⟩; refl

@[simp]
lemma truncate_comp' {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) (x) :
  truncate p R h1 (truncate p R h2 x) = truncate p R (h1.trans h2) x :=
by rw ← truncate_comp p R h1 h2; refl

@[simp]
lemma truncate_comp_witt_vector_truncate {m : ℕ} (hm : n ≤ m) :
  (truncate p R hm).comp (witt_vector.truncate p _) = witt_vector.truncate p _ :=
rfl

@[simp]
lemma truncate_comp_witt_vector_truncate' {m : ℕ} (hm : n ≤ m) (x) :
  truncate p R hm (witt_vector.truncate p _ x) = witt_vector.truncate p _ x :=
by rw ← truncate_comp_witt_vector_truncate p R hm; refl


section mk_and_coeff

variables (p)

lemma mk_coeff (x : truncated_witt_vector p n R) :
  mk p (λ (i : fin n), coeff i x) = x :=
begin
  apply quot.induction_on x,
  intros x',
  show mk p (λ i : fin n, witt_vector.coeff i x') = _,
  apply quot.sound,
  show _ ∈ (witt_vector.ideal p R n),
  sorry
  -- intros i hi,
end

lemma coeff_mk (i : fin n) (x : fin n → R) :
  coeff i (mk p x) = x i :=
begin
  dsimp [coeff, mk],
  convert quot.lift_beta _ (coeff._proof_1 _) _,
  { dsimp, rw [dif_pos i.is_lt, fin.eta], },
  { apply_instance, }
end

section
local attribute [semireducible] witt_vector
lemma witt_vector.mk_zero : witt_vector.mk p (λ _, (0 : R)) = 0 :=
by ext; simp [witt_vector.mk]; refl
end

variables (p n R)
@[simp] lemma mk_zero : mk p (0 : fin n → R) = 0 :=
begin
  -- not sure if we need this
  have : ∀ i n, dite (i < n) (λ (h : i < n), (0 : fin n → R) ⟨i, h⟩) (λ (h : ¬i < n), 0) = 0,
  { intros, split_ifs; simp only [eq_self_iff_true, pi.zero_apply] },
  simp only [mk, this, witt_vector.mk_zero, ring_hom.map_zero],
end

def equiv : truncated_witt_vector p n R ≃ (fin n → R) :=
{ to_fun := λ x i, x.coeff i,
  inv_fun := mk p,
  left_inv := by { intros x, apply mk_coeff },
  right_inv := by { intros x, ext i, apply coeff_mk } }


end mk_and_coeff

section fintype

instance [fintype R] : fintype (truncated_witt_vector p n R) :=
by { equiv_rw (equiv p n R), apply_instance }

lemma card [fintype R] :
  fintype.card (truncated_witt_vector p n R) = fintype.card R ^ n :=
by simp [fintype.card_congr (equiv p n R)]

end fintype

end truncated_witt_vector
