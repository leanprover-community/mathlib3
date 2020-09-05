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

local notation `𝕎` := witt_vectors p -- type as `\bbW`

@[derive comm_ring]
def truncated_witt_vectors :=
(witt_vectors.ideal p R n).quotient

variables {p} {R}

def witt_vectors.truncate : 𝕎 R →+* truncated_witt_vectors p n R :=
ideal.quotient.mk _

-- huh? It seems that `p` is nevertheless an explicit argument of `truncate`...

end defs

namespace truncated_witt_vectors

variables (p : ℕ) [fact p.prime] {n : ℕ} {R : Type*} [comm_ring R]

local notation `𝕎` := witt_vectors p -- type as `\bbW`

def mk (x : fin n → R) : truncated_witt_vectors p n R :=
witt_vectors.truncate p n $ witt_vectors.mk p $
λ i, if h : i < n then x ⟨i, h⟩ else 0

variable {p}
def coeff (i : fin n) : truncated_witt_vectors p n R → R :=
quot.lift (λ x : witt_vectors p R, x.coeff i)
begin
  intros x y h,
  change x - y ∈ (witt_vectors.ideal p R n) at h,
  set z := x - y with hz,
  have hx : x = z + y, { simp only [sub_add_cancel] },
  dsimp,
  rw [hx, witt_vectors.add_coeff],
  -- hmmm, `witt_add_vars` is not good enough for this one :sad:
  -- the first `n` coeffs of `z` are `0`, by assumption
  -- this is enough, but we need a better lemma for this
  sorry
end

section mk_and_coeff

variables (p)

lemma mk_coeff (x : truncated_witt_vectors p n R) :
  mk p (λ (i : fin n), coeff i x) = x :=
begin
  sorry
end

lemma coeff_mk (i : fin n) (x : fin n → R) :
  coeff i (mk p x) = x i :=
begin
  sorry
end

variables (p n R)
@[simp] lemma mk_zero : mk p (0 : fin n → R) = 0 :=
begin
  -- not sure if we need this
  sorry
end

def equiv : truncated_witt_vectors p n R ≃ (fin n → R) :=
{ to_fun := λ x i, x.coeff i,
  inv_fun := mk p,
  left_inv := by { intros x, apply mk_coeff },
  right_inv := by { intros x, ext i, apply coeff_mk } }


end mk_and_coeff

section fintype

instance [fintype R] : fintype (truncated_witt_vectors p n R) :=
by { equiv_rw (equiv p n R), apply_instance }

lemma card [fintype R] :
  fintype.card (truncated_witt_vectors p n R) = fintype.card R ^ n :=
by { rw fintype.card_congr (equiv p n R), sorry }

end fintype

end truncated_witt_vectors
