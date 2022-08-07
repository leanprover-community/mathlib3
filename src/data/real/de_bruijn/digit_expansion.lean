/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import algebra.monoid_algebra.basic
import data.zmod.basic
import data.int.succ_pred

/-!
# Defining reals without the use of rationals

* [Defining reals without the use of rationals][debruijn1976]

-/

section s01

-- non-empty
example : nonempty ℤ := by apply_instance
-- totally ordered
example : linear_order ℤ := by apply_instance
-- without maximal element
example : no_max_order ℤ := by apply_instance
-- without minimal element
example : no_min_order ℤ := by apply_instance
-- every non-empty subset is bounded above (below) has a maximum (minimum)
noncomputable example : conditionally_complete_lattice ℤ := by apply_instance
-- combination of totally ordered and subset constraint
noncomputable example : conditionally_complete_linear_order ℤ := by apply_instance
-- successor function
example : succ_order ℤ := by apply_instance
-- predecessor function
example : pred_order ℤ := by apply_instance

variables (Z : Type*) [nonempty Z]
  [conditionally_complete_linear_order Z]
  [no_max_order Z] [no_min_order Z]
  [succ_order Z] [pred_order Z]

open order

-- unique successor
example : function.injective (succ : Z → Z) := succ_injective
-- unique predecessor
example : function.injective (pred : Z → Z) := pred_injective

structure formal_series (b : ℕ) := -- b will the base - 1
(to_fun : Z → fin (b + 1))
(bounded' : ¬ ∃ i₀, ∀ i > i₀, to_fun i = b)

namespace formal_series

-- we can treat it like a function
instance fun_like (b : ℕ) : fun_like (formal_series Z b) Z (λ _, fin (b + 1)) :=
{ coe := formal_series.to_fun,
  coe_injective' := by { rintro ⟨⟩ ⟨⟩, simp } }

variables {Z}

variables {Z} {b : ℕ} (f g : formal_series Z b) (i : Z)

-- extensional equality
@[ext] lemma ext (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

@[simp] lemma to_fun_apply : f.to_fun i = f i := rfl

end formal_series

end s01

-- section 2 defines notation

open order

-- Z is the set of all integers
variables {Z : Type*} [nonempty Z]
  [conditionally_complete_linear_order Z]
  [no_max_order Z] [no_min_order Z]
  [succ_order Z] [pred_order Z]
  -- b is a fixed integer > 1
  {b : ℕ} [hb : fact (b > 0)] -- because we use the base - 1

-- If P and Q are sets then Q^P is the set of all mappings of P into Q
@[reducible] def mapping (P Q : Sort*) := Q → P
local notation P ` ^ ` Q := mapping P Q

local notation `Σ` := formal_series Z b

variables (f g : Σ)

-- TODO
@[simp] lemma nat.mod_succ (n : ℕ) : n % n.succ = n := nat.mod_eq_of_lt (nat.lt_succ_self _)

lemma formal_series.exists_bounded (z : Z) : ∃ x > z, f x < b :=
begin
  have := f.bounded',
  push_neg at this,
  simp_rw exists_prop,
  refine (this z).imp (λ x, and.imp_right _),
  cases (fin.le_last (f x)).eq_or_lt with h h,
  { simp [h, fin.ext_iff] },
  { intro,
    simpa [fin.lt_iff_coe_lt_coe] using h }
end

include hb

instance base_nontrivial : nontrivial (fin (b + 1)) :=
⟨⟨0, 1,
  begin
    have : 1 < b + 1 := nat.succ_lt_succ_iff.mpr hb.out,
    simp [fin.ext_iff, fin.coe_one', nat.mod_eq_of_lt this]
  end⟩⟩

instance : has_zero Σ :=
⟨{ to_fun := (0 : Z → fin (b + 1)),
   bounded' := begin
     push_neg,
     intro x,
     refine ⟨succ x, lt_succ _, _⟩,
     simp [fin.ext_iff, has_lt.lt.ne hb.out]
   end }⟩

@[simp] lemma zero_apply (z : Z) : (0 : Σ) z = 0 := rfl

open_locale classical
noncomputable theory

section s03

def difcar : (fin (b + 1)) ^ Z :=
λ z, if (∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y) then 1 else 0

variables {f g}

lemma difcar_eq_one_iff {z : Z} :
  difcar f g z = 1 ↔ ∃ x > z, f x < g x ∧ ∀ y < x, z < y → f y ≤ g y :=
begin
  dsimp [difcar],
  split_ifs,
  { exact ⟨λ _, h, λ _, rfl⟩ },
  { exact ⟨λ H, absurd H zero_ne_one, λ H, absurd H h⟩ }
end

lemma difcar_eq_zero_iff {z : Z} :
  difcar f g z = 0 ↔ ∀ x > z, f x < g x → ∃ (y : Z), y < x ∧ z < y ∧ g y < f y :=
begin
  dsimp [difcar],
  split_ifs,
  { refine ⟨λ H, absurd H.symm zero_ne_one, λ _, absurd h _⟩,
    push_neg,
    assumption },
  { push_neg at h,
    exact ⟨λ _, h, λ _, rfl⟩ }
end

variables (f g)

lemma difcar_eq_zero_or_one (x : Z) : difcar f g x = 0 ∨ difcar f g x = 1 :=
begin
  rw [difcar_eq_zero_iff, difcar_eq_one_iff],
  refine (em' _).imp_left _,
  push_neg,
  exact id
end

variables {f g}

lemma difcar_pred_eq_one {z : Z} (h : f z < g z) :
  difcar f g (pred z) = 1 :=
begin
  rw difcar_eq_one_iff,
  refine ⟨z, pred_lt _, h, λ y hyz hy, _⟩,
  rw pred_lt_iff_eq_or_lt_of_not_is_min at hy,
  { rcases hy with rfl|hy,
    { exact absurd hyz (lt_irrefl _) },
    { exact absurd hyz hy.not_lt } },
  { exact not_is_min z }
end

lemma difcar_pred_eq_zero {z : Z} (h : g z < f z) :
  difcar f g (pred z) = 0 :=
begin
  rw difcar_eq_zero_iff,
  intros x hx hfgx,
  rcases (le_of_pred_lt hx).eq_or_lt with rfl|hz,
  { exact absurd hfgx h.not_lt },
  exact ⟨z, hz, pred_lt _, h⟩
end

lemma difcar_pred_eq_difcar {z : Z} (h : f z = g z) :
  difcar f g (pred z) = difcar f g z :=
begin
  cases difcar_eq_zero_or_one f g z with hz hz,
  { rw hz,
    rw difcar_eq_zero_iff at hz ⊢,
    intros x hx hfgx,
    rcases (le_of_pred_lt hx).eq_or_lt with rfl|hzx,
    { exact absurd h hfgx.ne },
    obtain ⟨y, hy, hyz, hfgy⟩ := hz x hzx hfgx,
    exact ⟨y, hy, (pred_lt _).trans hyz, hfgy⟩ },
  { rw hz,
    rw difcar_eq_one_iff at hz ⊢,
    obtain ⟨x, hzx, hfgx, hz⟩ := hz,
    refine ⟨x, (pred_lt _).trans hzx, hfgx, λ y hy hyz, _⟩,
    rcases (le_of_pred_lt hyz).eq_or_lt with rfl|hyz',
    { exact h.le },
    exact hz y hy hyz' }
end

@[simp] lemma difcar_zero_right (f : Σ) (z : Z) : difcar f 0 z = 0 :=
by simp [difcar_eq_zero_iff]

@[simp] lemma difcar_self (f : Σ) (z : Z) : difcar f f z = 0 :=
by simp [difcar_eq_zero_iff]

def sub_aux (x : Z) : fin (b + 1) := f x - g x - difcar f g x

omit hb

@[simp] lemma fin.add_one_lt_iff {n : ℕ} {k : fin (n + 2)} :
  k + 1 < k ↔ k = fin.last _ :=
begin
  simp only [fin.lt_iff_coe_lt_coe, fin.coe_add, fin.coe_last, fin.ext_iff],
  cases k with k hk,
  rcases (nat.le_of_lt_succ hk).eq_or_lt with rfl|hk',
  { simp },
  { simp [hk'.ne, nat.mod_eq_of_lt (nat.succ_lt_succ hk'), nat.le_succ _] }
end

@[simp] lemma fin.add_one_le_iff {n : ℕ} {k : fin (n + 1)} :
  k + 1 ≤ k ↔ k = fin.last _ :=
begin
  cases n,
  { simp [subsingleton.elim (k + 1) k, subsingleton.elim (fin.last _) k] },
  rw ←not_iff_not,
  simp [←fin.add_one_lt_iff, lt_iff_le_and_ne]
end

@[simp] lemma fin.last_le_iff {n : ℕ} {k : fin (n + 1)} :
  fin.last n ≤ k ↔ k = fin.last n :=
begin
  rcases (fin.le_last k).eq_or_lt with rfl|hk,
  { simp },
  { simp [hk.not_le, hk.ne] }
end

@[simp] lemma fin.lt_add_one_iff {n : ℕ} {k : fin (n + 1)} :
  k < k + 1 ↔ k < fin.last n :=
begin
  rw ←not_iff_not,
  simp
end

@[simp] lemma fin.lt_sub_one_iff {n : ℕ} {k : fin (n + 2)} :
  k < k - 1 ↔ k = 0 :=
begin
  rcases k with ⟨(_|k), hk⟩,
  simp [fin.lt_iff_coe_lt_coe],
  have : (k + 1 + (n + 1)) % (n + 2) = k % (n + 2),
  { rw [add_right_comm, add_assoc, nat.add_mod_right] },
  simp [fin.lt_iff_coe_lt_coe, fin.ext_iff, fin.coe_sub, nat.succ_eq_add_one, this,
        nat.mod_eq_of_lt ((nat.lt_succ_self _).trans hk)]
end

@[simp] lemma fin.le_sub_one_iff {n : ℕ} {k : fin (n + 1)} :
  k ≤ k - 1 ↔ k = 0 :=
begin
  cases n,
  { simp [subsingleton.elim (k - 1) k, subsingleton.elim 0 k] },
  rw [←fin.lt_sub_one_iff, le_iff_lt_or_eq, fin.lt_sub_one_iff, or_iff_left_iff_imp, eq_comm,
      sub_eq_iff_eq_add],
  simp
end

@[simp] lemma fin.le_zero_iff {n : ℕ} {k : fin (n + 1)} :
  k ≤ 0 ↔ k = 0 :=
begin
  cases k,
  simp [fin.le_iff_coe_le_coe, fin.ext_iff]
end

lemma fin.sub_one_lt_iff {n : ℕ} {k : fin (n + 1)} :
  k - 1 < k ↔ 0 < k :=
begin
  rw ←not_iff_not,
  simp
end

include hb

variables [is_succ_archimedean Z]

instance : has_sub Σ :=
⟨λ f g,
  { to_fun := λ x, f x - g x - difcar f g x,
    bounded' := begin
      sorry
      -- rintro ⟨x, hx⟩,
      -- obtain ⟨w, hw, hfgw⟩ : ∃ w ≥ x, difcar f g w = 0,
      -- { cases difcar_eq_zero_or_one f g x with px px,
      --   { exact ⟨x, le_rfl, px⟩ },
      --   { rw difcar_eq_one_iff at px,
      --     obtain ⟨y, hxy, hfgy, px⟩ := px,
      --     have := hx y hxy,
      --     rw sub_eq_iff_eq_add at this,
      --     refine ⟨y, le_of_lt hxy, _⟩,
      --     refine or.resolve_right (difcar_eq_zero_or_one _ _ _) (λ H, _),
      --     rw [H, ←nat.cast_add_one, zmod.nat_cast_self, sub_eq_zero] at this,
      --     exact absurd this hfgy.ne } },
      -- suffices : ∀ z > w, difcar f g z = 0 ∧ f z = b,
      -- {  obtain ⟨z, hwz, hz⟩ := f.exists_bounded w,
      --   exact not_le_of_lt hz (this _ hwz).right.ge },
      -- suffices : ∀ z > x, difcar f g (pred z) = 0 → f z = b ∧ g z = 0 ∧ difcar f g z = 0,
      -- { intros z hwz,
      --   refine succ.rec _ _ (succ_le_of_lt hwz),
      --   { refine (this _ (lt_of_le_of_lt hw (lt_succ _)) _).symm.imp and.elim_right id,
      --     rwa pred_succ },
      --   { rintros k hk ⟨hd, hf⟩,
      --     refine (this _ _ _).symm.imp and.elim_right id,
      --     { exact lt_of_lt_of_le (lt_of_le_of_lt hw (succ_le_iff.mp hk)) (le_succ _) },
      --     { rwa pred_succ } } },
      -- intros z hxz hfgz,
      -- specialize hx z hxz,
      -- rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at hx,
      -- rcases lt_trichotomy (f z) (g z) with H|H|H,
      -- { simpa [difcar_pred_eq_one H, ne_of_gt hb.out] using hfgz },
      -- { simpa [←difcar_pred_eq_difcar H, H, hfgz, fin.ext_iff ↑b, ne_of_gt hb.out] using hx },
      -- cases difcar_eq_zero_or_one f g z with hd hd,
      -- { rw [hd, add_zero] at hx,
      --   cases (fin.zero_le (g z)).eq_or_lt with hg hg,
      --   { simp [hx, ←hg, hd] },
      --   { have : g z - 1 = b + g z,
      --     { simp [sub_eq_iff_eq_add, add_right_comm] },
      --     casesI b, -- TODO
      --     { simp [hd] },
      --     rw [hx, ←this, fin.lt_sub_one_iff] at H,
      --     simp [hx, H, hd] } },
      -- { simpa [hd, H.ne'] using hx }
    end }⟩

variables (f g)

protected lemma formal_series.sub_def (x : Z) : (f - g) x = f x - g x - difcar f g x := rfl

protected lemma formal_series.sub_zero (f : Σ) : f - 0 = f :=
by { ext, simp [formal_series.sub_def] }

protected lemma formal_series.sub_self (f : Σ) : f - f = 0 :=
by { ext, simp [formal_series.sub_def] }

end s03
