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

section mk_and_coeff

variables (p)

@[simp]
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

@[simp]
lemma coeff_mk (i : fin n) (x : fin n → R) :
  coeff i (mk p x) = x i :=
begin
  dsimp [coeff, mk],
  convert quot.lift_beta _ (coeff._proof_1 _) _,
  { dsimp, rw [dif_pos i.is_lt, fin.eta], },
  { apply_instance, }
end

@[simp] lemma coeff_zero (i : fin n) : coeff i (0 : truncated_witt_vector p n R) = 0 :=
begin
  convert coeff_mk p i 0,
  symmetry,
  apply ideal.quotient.eq_zero_iff_mem.mpr,
  rw witt_vector.mem_ideal_iff,
  intros i hi,
  simp [hi]
end

section
-- move this
local attribute [semireducible] witt_vector
@[simp] lemma witt_vector.mk_zero : witt_vector.mk p (λ _, (0 : R)) = 0 :=
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

variables {p n R}

@[ext] lemma ext (x y : truncated_witt_vector p n R) (h : ∀ i : fin n, x.coeff i = y.coeff i) :
  x = y :=
begin
  apply (equiv p n R).injective,
  ext i,
  exact h i
end

@[ext] lemma ext_iff (x y : truncated_witt_vector p n R) :
  x = y ↔ (∀ i : fin n, x.coeff i = y.coeff i) :=
⟨λ h i, congr_arg _ h, ext x y⟩

end mk_and_coeff

end truncated_witt_vector

namespace witt_vector
local attribute [semireducible] witt_vector

variables {p n : ℕ} {R : Type*} [fact (nat.prime p)] [comm_ring R]

@[simp]
lemma coeff_truncate (x : witt_vector p R) (i : fin n) :
  (truncate p n x).coeff i = x.coeff i := rfl

@[simp]
lemma truncate_mk (f : ℕ → R) :
  truncate p n (mk p f) = truncated_witt_vector.mk _ (λ k, f k) :=
begin
  ext i,
  rw [coeff_truncate, coeff_mk, truncated_witt_vector.coeff_mk],
end

end witt_vector

namespace truncated_witt_vector

variables (p : ℕ) (R : Type*) [fact (nat.prime p)] [comm_ring R] {n : ℕ}
local notation `𝕎` := witt_vector p -- type as `\bbW`

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
lemma truncate_truncate {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) (x) :
  truncate p R h1 (truncate p R h2 x) = truncate p R (h1.trans h2) x :=
by rw ← truncate_comp p R h1 h2; refl

@[simp]
lemma truncate_comp_witt_vector_truncate {m : ℕ} (hm : n ≤ m) :
  (truncate p R hm).comp (witt_vector.truncate p _) = witt_vector.truncate p _ :=
rfl

@[simp]
lemma truncate_witt_vector_truncate {m : ℕ} (hm : n ≤ m) (x) :
  truncate p R hm (witt_vector.truncate p _ x) = witt_vector.truncate p _ x :=
by rw ← truncate_comp_witt_vector_truncate p R hm; refl

-- this proof confuses me
@[simp] lemma coeff_truncate {m : ℕ} (hm : n ≤ m) (i : fin n) (x : truncated_witt_vector p m R) :
  (truncate p R hm x).coeff i = x.coeff (fin.cast_le hm i) :=
begin
  induction x,
  { simp only [truncate, submodule.quotient.quot_mk_eq_mk, witt_vector.coeff_truncate, ideal.quotient.lift_mk,
      ideal.quotient.mk_eq_mk],
    show _ = coeff _ (submodule.quotient.mk _),
    rw [← submodule.quotient.quot_mk_eq_mk, coeff],
    refl },
  { refl }
end


section fintype

instance [fintype R] : fintype (truncated_witt_vector p n R) :=
by { equiv_rw (equiv p n R), apply_instance }

lemma card [fintype R] :
  fintype.card (truncated_witt_vector p n R) = fintype.card R ^ n :=
by simp [fintype.card_congr (equiv p n R)]

end fintype

section ideals

lemma ideal_inter : (⨅ i : ℕ, witt_vector.ideal p R i) = ⊥ :=
begin
  rw [submodule.eq_bot_iff],
  intros x hx,
  ext,
  simp only [witt_vector.mem_ideal_iff, ideal.mem_infi, witt_vector.zero_coeff] at hx ⊢,
  exact hx _ _ (nat.lt_succ_self _)
end

-- move this
lemma ideal.mem_bot {x : R} : x ∈ (⊥ : ideal R) ↔ x = 0 :=
submodule.mem_bot _

end ideals

section lift

variables {S : Type*} [comm_ring S]
variable (f : Π k : ℕ, S →+* truncated_witt_vector p k R)
variable f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), (truncate p R hk).comp (f k₂) = f k₁
variables {p R}

def lift_fun (s : S) : 𝕎 R :=
witt_vector.mk p $ λ k, coeff (fin.last k) (f (k+1) s)

include f_compat

variables {f}
@[simp]
private lemma truncate_lift_fun (s : S) :
  witt_vector.truncate p n (lift_fun p f s) = f n s :=
begin
  ext i,
  simp only [lift_fun, coeff_mk, witt_vector.truncate_mk],
  rw [← f_compat (i+1) n i.is_lt, ring_hom.comp_apply, coeff_truncate],
  -- this is a bit unfortunate
  congr' with _,
  simp only [fin.coe_last, fin.coe_cast_le],
end

lemma lift_fun_zero : lift_fun p f 0 = 0 :=
by simp [lift_fun]

lemma lift_fun_one : lift_fun p f 1 = 1 :=
begin
  rw [← sub_eq_zero, ← ideal.mem_bot, ← ideal_inter, ideal.mem_infi],
  intro i,
  rw [← ideal.quotient.eq, ring_hom.map_one],
  show witt_vector.truncate _ _ _ = _,
  simp [truncate_lift_fun, f_compat],
end

lemma lift_fun_add (x y) : lift_fun p f (x + y) = lift_fun p f x + lift_fun p f y :=
begin
  rw [← sub_eq_zero, ← ideal.mem_bot, ← ideal_inter, ideal.mem_infi],
  intro i,
  rw [← ideal.quotient.eq, ring_hom.map_add],
  show witt_vector.truncate _ _ _ = witt_vector.truncate _ _ _ + witt_vector.truncate _ _ _,
  simp [truncate_lift_fun, f_compat], -- squeeze_simp output fails??
end

lemma lift_fun_mul (x y) : lift_fun p f (x * y) = lift_fun p f x * lift_fun p f y :=
begin
  rw [← sub_eq_zero, ← ideal.mem_bot, ← ideal_inter, ideal.mem_infi],
  intro i,
  rw [← ideal.quotient.eq, ring_hom.map_mul],
  show witt_vector.truncate _ _ _ = witt_vector.truncate _ _ _ * witt_vector.truncate _ _ _,
  simp [truncate_lift_fun, f_compat], -- squeeze_simp output fails??
end

def lift : S →+* 𝕎 R :=
{ to_fun := lift_fun p f,
  map_one' := lift_fun_one f_compat,
  map_mul' := lift_fun_mul f_compat,
  map_zero' := lift_fun_zero f_compat,
  map_add' := lift_fun_add f_compat }

@[simp] lemma truncate_lift (s : S) :
  witt_vector.truncate p n (lift f_compat s) = f n s :=
truncate_lift_fun f_compat s

@[simp] lemma truncate_comp_lift :
  (witt_vector.truncate p n).comp (lift f_compat) = f n :=
by { ext1, rw [ring_hom.comp_apply, truncate_lift] }

end lift

end truncated_witt_vector
