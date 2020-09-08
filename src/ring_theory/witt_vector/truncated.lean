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

namespace witt_vector

def truncate : 𝕎 R →+* truncated_witt_vector p n R :=
ideal.quotient.mk _

-- huh? It seems that `p` is nevertheless an explicit argument of `truncate`...

lemma truncate_ker :
  (witt_vector.truncate p n : 𝕎 R →+* truncated_witt_vector p n R).ker =
  witt_vector.ideal p R n :=
begin
  ext1 x,
  rw [ring_hom.mem_ker, witt_vector.truncate, ideal.quotient.eq_zero_iff_mem],
end

lemma truncate_eq_iff (x y : 𝕎 R) (n : ℕ) :
  witt_vector.truncate p n x = witt_vector.truncate p n y ↔
  ∀ ⦃i : ℕ⦄, i < n → x.coeff i = y.coeff i :=
begin
  sorry
end

lemma coeff_eq_of_truncate_eq (x y : 𝕎 R) (n : ℕ)
  (h : witt_vector.truncate p n x = witt_vector.truncate p n y) :
  ∀ ⦃i : ℕ⦄, i < n → x.coeff i = y.coeff i :=
(truncate_eq_iff p _ _ n).mp h

end witt_vector

variables {n}

def truncated_witt_vector.coeff (i : fin n) (x : truncated_witt_vector p n R) : R :=
witt_vector.coeff i (quot.out x)

@[simp]
lemma witt_vector.coeff_truncate (x : witt_vector p R) (i : fin n) :
  (witt_vector.truncate p n x).coeff i = x.coeff i :=
begin
  apply witt_vector.coeff_eq_of_truncate_eq p _ _ n _ i.is_lt,
  exact quot.out_eq _,
end

-- variable (R)
lemma witt_vector.truncate_surjective :
  function.surjective (witt_vector.truncate p n : 𝕎 R → truncated_witt_vector p n R) :=
ideal.quotient.mk_surjective

end defs

namespace truncated_witt_vector

variables (p : ℕ) [fact p.prime] {n : ℕ} {R : Type*} [comm_ring R]

local notation `𝕎` := witt_vector p -- type as `\bbW`

def mk (x : fin n → R) : truncated_witt_vector p n R :=
witt_vector.truncate p n $ witt_vector.mk p $
λ i, if h : i < n then x ⟨i, h⟩ else 0

variable {p}

section mk_and_coeff

variables (p)

@[simp]
lemma coeff_mk (i : fin n) (x : fin n → R) :
  coeff i (mk p x) = x i :=
begin
  have : x i = witt_vector.coeff i (witt_vector.mk p $ λ k, if h : k < n then x ⟨k, h⟩ else 0),
  { rw [witt_vector.coeff_mk, dif_pos i.is_lt, fin.eta], },
  rw this,
  apply witt_vector.coeff_eq_of_truncate_eq p _ _ n _ i.is_lt,
  apply quot.out_eq,
end

@[simp]
lemma mk_coeff (x : truncated_witt_vector p n R) :
  mk p (λ (i : fin n), coeff i x) = x :=
begin
  obtain ⟨x, rfl⟩ := witt_vector.truncate_surjective p x,
  show witt_vector.truncate p n _ = _,
  rw witt_vector.truncate_eq_iff,
  intros i hi,
  simp only [witt_vector.coeff_mk, dif_pos hi, witt_vector.coeff_truncate, fin.coe_mk],
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

@[simp]
lemma equiv_apply (x : truncated_witt_vector p n R) (i : fin n) :
  equiv p n R x i = x.coeff i :=
begin
  dsimp [equiv], refl
end

variables {p n R}

@[ext] lemma ext (x y : truncated_witt_vector p n R) (h : ∀ i : fin n, x.coeff i = y.coeff i) :
  x = y :=
begin
  apply (equiv p n R).injective,
  ext i,
  simp only [equiv_apply, h],
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

lemma truncate_surjective {m : ℕ} (hm : n ≤ m) : function.surjective (truncate p R hm) :=
begin
  rintro ⟨x⟩,
  use ideal.quotient.mk _ x,
  simp [truncate], refl
end

@[simp] lemma coeff_truncate {m : ℕ} (hm : n ≤ m) (i : fin n) (x : truncated_witt_vector p m R) :
  (truncate p R hm x).coeff i = x.coeff (fin.cast_le hm i) :=
begin
  rcases witt_vector.truncate_surjective p x with ⟨y, rfl⟩,
  simp only [truncate_witt_vector_truncate, witt_vector.coeff_truncate, fin.coe_cast_le],
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

-- move this to a better place
lemma eq_of_le_of_cast_pow_eq_zero (i : ℕ) (hin : i ≤ n)
  (hpi : (p ^ i : truncated_witt_vector p n R) = 0) :
  i = n :=
begin
  sorry
end

section iso

lemma card_zmod : fintype.card (truncated_witt_vector p n (zmod p)) = p ^ n :=
by rw [card, zmod.card]

lemma char_p_zmod : char_p (truncated_witt_vector p n (zmod p)) (p ^ n) :=
char_p_of_prime_pow_ne_zero _ _ _ (card_zmod _)
    (eq_of_le_of_cast_pow_eq_zero p (zmod p))

local attribute [instance] char_p_zmod
variable (n)
def zmod_equiv_trunc : zmod (p^n) ≃+* truncated_witt_vector p n (zmod p) :=
iso_to_zmod (truncated_witt_vector p n (zmod p)) (p ^ n) (card_zmod _)

lemma zmod_equiv_trunc_apply {x : zmod (p^n)} :
  zmod_equiv_trunc p n x =
  zmod.cast_hom (show p ^ n ∣ p ^ n, by refl) (truncated_witt_vector p n (zmod p)) x :=
rfl

lemma commutes {m : ℕ} (hm : n ≤ m) :
  (truncate p (zmod p) hm).comp (zmod_equiv_trunc p m).to_ring_hom =
    (zmod_equiv_trunc p n).to_ring_hom.comp (zmod.cast_hom (show p ^ n ∣ p ^ m, by simpa using pow_dvd_pow p hm) _) :=
ring_hom.ext_zmod _ _

lemma commutes' {m : ℕ} (hm : n ≤ m) (x : zmod (p^m)) :
  truncate p (zmod p) hm (zmod_equiv_trunc p m x) =
    zmod_equiv_trunc p n (zmod.cast_hom (show p ^ n ∣ p ^ m, by simpa using pow_dvd_pow p hm) _ x) :=
show (truncate p (zmod p) hm).comp (zmod_equiv_trunc p m).to_ring_hom x = _,
by rw commutes _ _ hm; refl

lemma commutes_symm' {m : ℕ} (hm : n ≤ m) (x : truncated_witt_vector p m (zmod p)) :
  (zmod_equiv_trunc p n).symm (truncate p (zmod p) hm x) =
    zmod.cast_hom (show p ^ n ∣ p ^ m, by simpa using pow_dvd_pow p hm) _ ((zmod_equiv_trunc p m).symm x) :=
begin
  apply (zmod_equiv_trunc p n).injective,
  rw ← commutes',
  simp
end

lemma commutes_symm {m : ℕ} (hm : n ≤ m)  :
  (zmod_equiv_trunc p n).symm.to_ring_hom.comp (truncate p (zmod p) hm) =
    (zmod.cast_hom (show p ^ n ∣ p ^ m, by simpa using pow_dvd_pow p hm) _).comp (zmod_equiv_trunc p m).symm :=
by ext; apply commutes_symm'

end iso


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

-- everything about `lift` and `lift_fun` should probably move to `witt_vector` namespace
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

lemma lift_unique (g : S →+* 𝕎 R) (g_compat : ∀ k, (witt_vector.truncate p k).comp g = f k) :
  g = lift f_compat :=
begin
  sorry
end

-- other name? something with `ext`?
omit f_compat

lemma witt_vector.hom_ext (g₁ g₂ : S →+* 𝕎 R)
  (h : ∀ k, (witt_vector.truncate p k).comp g₁ = (witt_vector.truncate p k).comp g₂) :
  g₁ = g₂ :=
begin
  rw [lift_unique _ g₁, lift_unique _ g₂],
  { intro k, apply (h k).symm },
  { intros, rw [← ring_hom.comp_assoc], simp [truncate_comp_witt_vector_truncate] },
  { intro, refl }
end

end lift

end truncated_witt_vector
