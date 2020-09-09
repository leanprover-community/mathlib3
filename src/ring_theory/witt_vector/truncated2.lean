/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

-- import ring_theory.witt_vector.ideal
import ring_theory.witt_vector.init_tail
import tactic.equiv_rw

/-!

# Truncated Witt vectors

-/

open function (injective surjective)

noncomputable theory

variables {p : ℕ} [hp : fact p.prime] (n : ℕ) (R : Type*) [comm_ring R]

local notation `𝕎` := witt_vector p -- type as `\bbW`

def truncated_witt_vector (p : ℕ) (n : ℕ) (R : Type*) := fin n → R

variables {n R}

namespace truncated_witt_vector

variables (p)

def mk (x : fin n → R) : truncated_witt_vector p n R := x

variables {p}

def coeff (i : fin n) (x : truncated_witt_vector p n R) : R := x i

@[ext]
lemma ext {x y : truncated_witt_vector p n R} (h : ∀ i, x.coeff i = y.coeff i) : x = y :=
funext $ λ n, h n

lemma ext_iff {x y : truncated_witt_vector p n R} : x = y ↔ ∀ i, x.coeff i = y.coeff i :=
⟨λ h i, by rw h, ext⟩

@[simp] lemma coeff_mk (x : fin n → R) (i : fin n) :
  (mk p x).coeff i = x i := rfl

@[simp] lemma mk_coeff (x : truncated_witt_vector p n R) :
  mk p (λ i, x.coeff i) = x :=
by { ext i, rw [coeff_mk] }

def out (x : truncated_witt_vector p n R) : 𝕎 R :=
witt_vector.mk p $ λ i, if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]
lemma coeff_out (x : truncated_witt_vector p n R) (i : fin n) :
  x.out.coeff i = x.coeff i :=
by rw [out, witt_vector.coeff_mk, dif_pos i.is_lt, fin.eta]

lemma out_injective : injective (@out p n R _) :=
begin
  intros x y h,
  ext i,
  rw [witt_vector.ext_iff] at h,
  simpa only [coeff_out] using h ↑i
end

end truncated_witt_vector

namespace witt_vector

variables {p} (n)

section

local attribute [semireducible] witt_vector

def truncate_fun (x : 𝕎 R) : truncated_witt_vector p n R :=
truncated_witt_vector.mk p $ λ i, x.coeff i

end

variables {n}

@[simp] lemma coeff_truncate_fun (x : 𝕎 R) (i : fin n) :
  (truncate_fun n x).coeff i = x.coeff i :=
by rw [truncate_fun, truncated_witt_vector.coeff_mk]

@[simp] lemma out_truncate_fun (x : 𝕎 R) :
  (truncate_fun n x).out = init x n :=
begin
  ext i,
  dsimp [truncated_witt_vector.out, init],
  split_ifs with hi, swap, refl,
  rw [coeff_truncate_fun, fin.coe_mk],
end

end witt_vector

namespace truncated_witt_vector

@[simp] lemma truncate_fun_out (x : truncated_witt_vector p n R) :
  x.out.truncate_fun n = x :=
by simp only [witt_vector.truncate_fun, coeff_out, mk_coeff]

end truncated_witt_vector

namespace truncated_witt_vector
open witt_vector
variables (p n R)
include hp

instance : has_zero (truncated_witt_vector p n R) :=
⟨truncate_fun n 0⟩

instance : has_one (truncated_witt_vector p n R) :=
⟨truncate_fun n 1⟩

instance : has_add (truncated_witt_vector p n R) :=
⟨λ x y, truncate_fun n (x.out + y.out)⟩

instance : has_mul (truncated_witt_vector p n R) :=
⟨λ x y, truncate_fun n (x.out * y.out)⟩

instance : has_neg (truncated_witt_vector p n R) :=
⟨λ x, truncate_fun n (- x.out)⟩

@[simp] lemma coeff_zero (i : fin n) :
  (0 : truncated_witt_vector p n R).coeff i = 0 :=
begin
  show coeff i (truncate_fun _ 0 : truncated_witt_vector p n R) = 0,
  rw [coeff_truncate_fun, witt_vector.zero_coeff],
end

end truncated_witt_vector

meta def tactic.interactive.truncate_fun_tac : tactic unit :=
`[
  show _ = truncate_fun n _,
  apply truncated_witt_vector.out_injective,
  iterate { rw [out_truncate_fun] },
  rw init_add <|> rw init_mul <|> rw init_neg
]

namespace witt_vector

variables (p n R)

lemma truncate_fun_surjective :
  surjective (@truncate_fun p n R _) :=
λ x, ⟨x.out, truncated_witt_vector.truncate_fun_out x⟩

include hp

@[simp]
lemma truncate_fun_zero : truncate_fun n (0 : 𝕎 R) = 0 := rfl

@[simp]
lemma truncate_fun_one : truncate_fun n (1 : 𝕎 R) = 1 := rfl

variables {p R}

@[simp]
lemma truncate_fun_add (x y : 𝕎 R) :
  truncate_fun n (x + y) = truncate_fun n x + truncate_fun n y :=
by truncate_fun_tac

@[simp]
lemma truncate_fun_mul (x y : 𝕎 R) :
  truncate_fun n (x * y) = truncate_fun n x * truncate_fun n y :=
by truncate_fun_tac

lemma truncate_fun_neg (x : 𝕎 R) :
  truncate_fun n (-x) = -truncate_fun n x :=
by truncate_fun_tac

end witt_vector

namespace truncated_witt_vector
open witt_vector
variables (p n R)
include hp

instance : comm_ring (truncated_witt_vector p n R) :=
(truncate_fun_surjective p n R).comm_ring _
  (truncate_fun_zero p n R)
  (truncate_fun_one p n R)
  (truncate_fun_add n)
  (truncate_fun_mul n)
  (truncate_fun_neg n)

end truncated_witt_vector

namespace witt_vector
open truncated_witt_vector

variables (n)
include hp

def truncate : 𝕎 R →+* truncated_witt_vector p n R :=
{ to_fun := truncate_fun n,
  map_zero' := truncate_fun_zero p n R,
  map_add' := truncate_fun_add n,
  map_one' := truncate_fun_one p n R,
  map_mul' := truncate_fun_mul n }

variables (p n R)
lemma truncate_surjective : surjective (truncate n : 𝕎 R → truncated_witt_vector p n R) :=
truncate_fun_surjective p n R

@[simp] lemma coeff_truncate (x : 𝕎 R) (i : fin n) :
  (truncate n x).coeff i = x.coeff i :=
coeff_truncate_fun _ _

lemma mem_ker_truncate (x : 𝕎 R) :
  x ∈ (@truncate p _ n R _).ker ↔ ∀ i < n, x.coeff i = 0 :=
begin
  simp only [ring_hom.mem_ker, truncate, truncate_fun, ring_hom.coe_mk,
    truncated_witt_vector.ext_iff, truncated_witt_vector.coeff_mk, coeff_zero],
  erw [subtype.forall],
  refl,
end

end witt_vector

namespace witt_vector
local attribute [semireducible] witt_vector

include hp

@[simp]
lemma truncate_mk (f : ℕ → R) :
  truncate n (mk p f) = truncated_witt_vector.mk _ (λ k, f k) :=
begin
  ext i,
  rw [coeff_truncate, coeff_mk, truncated_witt_vector.coeff_mk],
end

end witt_vector

namespace truncated_witt_vector
include hp

def truncate {m : ℕ} (hm : n ≤ m) : truncated_witt_vector p m R →+* truncated_witt_vector p n R :=
ring_hom.lift_of_surjective
  (witt_vector.truncate m)
  (witt_vector.truncate_surjective p m R)
  (witt_vector.truncate n)
  begin
    intro x,
    simp only [witt_vector.mem_ker_truncate],
    intros h i hi,
    exact h i (lt_of_lt_of_le hi hm)
  end

@[simp]
lemma truncate_comp_witt_vector_truncate {m : ℕ} (hm : n ≤ m) :
  (@truncate p _ n R _ m hm).comp (witt_vector.truncate m) = witt_vector.truncate n :=
ring_hom.lift_of_surjective_comp _ _ _ _

@[simp]
lemma truncate_witt_vector_truncate {m : ℕ} (hm : n ≤ m) (x : 𝕎 R) :
  truncate hm (witt_vector.truncate m x) = witt_vector.truncate n x :=
ring_hom.lift_of_surjective_comp_apply _ _ _ _ _

@[simp]
lemma truncate_truncate {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃)
  (x : truncated_witt_vector p n₃ R) :
  (truncate h1) (truncate h2 x) = truncate (h1.trans h2) x :=
begin
  obtain ⟨x, rfl⟩ := witt_vector.truncate_surjective p n₃ R x,
  simp only [truncate_witt_vector_truncate],
end

@[simp]
lemma truncate_comp {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) :
  (@truncate p _ _ R _ _ h1).comp (truncate h2) = truncate (h1.trans h2) :=
begin
  ext1 x, simp only [truncate_truncate, function.comp_app, ring_hom.coe_comp]
end

lemma truncate_surjective {m : ℕ} (hm : n ≤ m) : surjective (@truncate p _ _ R _ _ hm) :=
begin
  intro x,
  obtain ⟨x, rfl⟩ := witt_vector.truncate_surjective p _ R x,
  exact ⟨witt_vector.truncate _ x, truncate_witt_vector_truncate _ _⟩
end

@[simp] lemma coeff_truncate {m : ℕ} (hm : n ≤ m) (i : fin n) (x : truncated_witt_vector p m R) :
  (truncate hm x).coeff i = x.coeff (fin.cast_le hm i) :=
begin
  rcases witt_vector.truncate_surjective p _ _ x with ⟨y, rfl⟩,
  simp only [truncate_witt_vector_truncate, witt_vector.coeff_truncate, fin.coe_cast_le],
end

section fintype

instance [fintype R] : fintype (truncated_witt_vector p n R) :=
pi.fintype

lemma card [fintype R] :
  fintype.card (truncated_witt_vector p n R) = fintype.card R ^ n :=
by simp only [truncated_witt_vector, fintype.card_fin, fintype.card_fun]

end fintype

section ideals

lemma ideal_inter : (⨅ i : ℕ, (@witt_vector.truncate p _ i R _).ker) = ⊥ :=
begin
  rw [submodule.eq_bot_iff],
  intros x hx,
  ext,
  simp only [witt_vector.mem_ker_truncate, ideal.mem_infi, witt_vector.zero_coeff] at hx ⊢,
  exact hx _ _ (nat.lt_succ_self _)
end

omit hp

-- move this
lemma ideal.mem_bot {x : R} : x ∈ (⊥ : ideal R) ↔ x = 0 :=
submodule.mem_bot _

end ideals

-- move this to a better place

variables (p n R)

lemma eq_of_le_of_cast_pow_eq_zero (i : ℕ) (hin : i ≤ n)
  (hpi : (p ^ i : truncated_witt_vector p n R) = 0) :
  i = n :=
begin
  sorry
end

section iso

variables (p n) {R}

lemma card_zmod : fintype.card (truncated_witt_vector p n (zmod p)) = p ^ n :=
by rw [card, zmod.card]

lemma char_p_zmod : char_p (truncated_witt_vector p n (zmod p)) (p ^ n) :=
char_p_of_prime_pow_ne_zero _ _ _ (card_zmod _ _)
    (eq_of_le_of_cast_pow_eq_zero p n (zmod p))

local attribute [instance] char_p_zmod
variable (n)
def zmod_equiv_trunc : zmod (p^n) ≃+* truncated_witt_vector p n (zmod p) :=
iso_to_zmod (truncated_witt_vector p n (zmod p)) (p ^ n) (card_zmod _ _)

lemma zmod_equiv_trunc_apply {x : zmod (p^n)} :
  zmod_equiv_trunc p n x =
  zmod.cast_hom (show p ^ n ∣ p ^ n, by refl) (truncated_witt_vector p n (zmod p)) x :=
rfl

lemma commutes {m : ℕ} (hm : n ≤ m) :
  (truncate hm).comp (zmod_equiv_trunc p m).to_ring_hom =
    (zmod_equiv_trunc p n).to_ring_hom.comp (zmod.cast_hom (show p ^ n ∣ p ^ m, by simpa using pow_dvd_pow p hm) _) :=
ring_hom.ext_zmod _ _

lemma commutes' {m : ℕ} (hm : n ≤ m) (x : zmod (p^m)) :
  truncate hm (zmod_equiv_trunc p m x) =
    zmod_equiv_trunc p n (zmod.cast_hom (show p ^ n ∣ p ^ m, by simpa using pow_dvd_pow p hm) _ x) :=
show (truncate hm).comp (zmod_equiv_trunc p m).to_ring_hom x = _,
by rw commutes _ _ hm; refl

lemma commutes_symm' {m : ℕ} (hm : n ≤ m) (x : truncated_witt_vector p m (zmod p)) :
  (zmod_equiv_trunc p n).symm (truncate hm x) =
    zmod.cast_hom (show p ^ n ∣ p ^ m, by simpa using pow_dvd_pow p hm) _ ((zmod_equiv_trunc p m).symm x) :=
begin
  apply (zmod_equiv_trunc p n).injective,
  rw ← commutes',
  simp
end

lemma commutes_symm {m : ℕ} (hm : n ≤ m)  :
  (zmod_equiv_trunc p n).symm.to_ring_hom.comp (truncate hm) =
    (zmod.cast_hom (show p ^ n ∣ p ^ m, by simpa using pow_dvd_pow p hm) _).comp (zmod_equiv_trunc p m).symm.to_ring_hom :=
by ext; apply commutes_symm'

end iso


section lift

variables {S : Type*} [comm_ring S]
variable (f : Π k : ℕ, S →+* truncated_witt_vector p k R)
variable f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), (truncate hk).comp (f k₂) = f k₁
variables {p R}

def lift_fun (s : S) : 𝕎 R :=
witt_vector.mk p $ λ k, coeff (fin.last k) (f (k+1) s)

include f_compat

variables {f}
@[simp]
private lemma truncate_lift_fun (s : S) :
  witt_vector.truncate n (lift_fun f s) = f n s :=
begin
  ext i,
  simp only [lift_fun, coeff_mk, witt_vector.truncate_mk],
  rw [← f_compat (i+1) n i.is_lt, ring_hom.comp_apply, coeff_truncate],
  -- this is a bit unfortunate
  congr' with _,
  simp only [fin.coe_last, fin.coe_cast_le],
end

lemma lift_fun_zero : lift_fun f 0 = 0 :=
by simp [lift_fun, witt_vector.ext_iff]

lemma lift_fun_one : lift_fun f 1 = 1 :=
begin
  rw [← sub_eq_zero, ← ideal.mem_bot, ← ideal_inter, ideal.mem_infi],
  intro i,
  simp [ring_hom.mem_ker, f_compat],
end

lemma lift_fun_add (x y) : lift_fun f (x + y) = lift_fun f x + lift_fun f y :=
begin
  rw [← sub_eq_zero, ← ideal.mem_bot, ← ideal_inter, ideal.mem_infi],
  intro i,
  simp [ring_hom.mem_ker, f_compat],
end

lemma lift_fun_mul (x y) : lift_fun f (x * y) = lift_fun f x * lift_fun f y :=
begin
  rw [← sub_eq_zero, ← ideal.mem_bot, ← ideal_inter, ideal.mem_infi],
  intro i,
  simp [ring_hom.mem_ker, f_compat],
end

variable (f)
-- everything about `lift` and `lift_fun` should probably move to `witt_vector` namespace
def lift : S →+* 𝕎 R :=
{ to_fun := lift_fun f,
  map_one' := lift_fun_one f_compat,
  map_mul' := lift_fun_mul f_compat,
  map_zero' := lift_fun_zero f_compat,
  map_add' := lift_fun_add f_compat }

variable {f}
@[simp] lemma truncate_lift (s : S) :
  witt_vector.truncate n (lift _ f_compat s) = f n s :=
truncate_lift_fun _ f_compat s

@[simp] lemma truncate_comp_lift :
  (witt_vector.truncate n).comp (lift _ f_compat) = f n :=
by { ext1, rw [ring_hom.comp_apply, truncate_lift] }

-- this is stated in reverse from `padic_int.lift_unique`, we should change one or the other
lemma lift_unique (g : S →+* 𝕎 R) (g_compat : ∀ k, (witt_vector.truncate k).comp g = f k) :
  g = lift _ f_compat :=
begin
  ext1 x,
  rw [← sub_eq_zero, ← ideal.mem_bot, ← ideal_inter, ideal.mem_infi],
  intro i,
  simp only [ring_hom.mem_ker, g_compat, ←ring_hom.comp_apply,
    truncate_comp_lift, ring_hom.map_sub, sub_self],
end

omit f_compat

lemma witt_vector.hom_ext (g₁ g₂ : S →+* 𝕎 R)
  (h : ∀ k, (witt_vector.truncate k).comp g₁ = (witt_vector.truncate k).comp g₂) :
  g₁ = g₂ :=
begin
  rw [lift_unique _ g₁, lift_unique _ g₂],
  { intro k, apply (h k).symm },
  { intros, rw [← ring_hom.comp_assoc], simp [truncate_comp_witt_vector_truncate] },
  { intro, refl }
end

end lift

end truncated_witt_vector
