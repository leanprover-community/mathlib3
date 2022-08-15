/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import algebra.monoid_algebra.basic
import data.zmod.basic
import data.int.succ_pred
import tactic.positivity

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
local notation P ` ^ ` Q := Q → P

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

lemma difcar_le_one (x : Z) : difcar f g x ≤ 1 :=
by { cases difcar_eq_zero_or_one f g x with h h; simp [h] }

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

namespace fin

lemma add_one_le_of_lt {n : ℕ} {a b : fin (n + 1)} (h : a < b) :
  a + 1 ≤ b :=
begin
  cases n,
  { simp [subsingleton.elim a b] },
  cases a with a ha,
  cases b with b hb,
  simp only [le_iff_coe_le_coe, coe_add, lt_iff_coe_lt_coe, coe_mk, coe_one] at h ⊢,
  rwa [nat.mod_eq_of_lt, nat.succ_le_iff],
  rw [nat.succ_lt_succ_iff],
  exact h.trans_le (nat.le_of_lt_succ hb)
end

end fin

@[simp] lemma int.zero_le_coe (n : ℕ) : (0 : ℤ) ≤ n := int.zero_le_of_nat n

lemma fin.exists_eq_add_of_le {n : ℕ} {a b : fin n} (h : a ≤ b) : ∃ k ≤ b, b = a + k :=
begin
  obtain ⟨k, hk⟩ : ∃ (k : ℕ), (b : ℕ) = a + k := nat.exists_eq_add_of_le h,
  have hkb : k ≤ b := le_add_self.trans hk.ge,
  refine ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, _⟩,
  simp [fin.ext_iff, fin.coe_add, ←hk, nat.mod_eq_of_lt b.is_lt]
end

lemma fin.exists_eq_add_of_lt {n : ℕ} {a b : fin (n + 1)} (h : a < b) :
  ∃ k < b, k + 1 ≤ b ∧ b = a + k + 1 :=
begin
  cases n,
  { rw [subsingleton.elim a b] at h,
    exact absurd h (lt_irrefl _) },
  obtain ⟨k, hk⟩ : ∃ (k : ℕ), (b : ℕ) = a + k + 1 := nat.exists_eq_add_of_lt h,
  have hkb : k < b,
  { rw [hk, add_comm _ k, nat.lt_succ_iff],
    exact le_self_add },
  refine ⟨⟨k, hkb.trans b.is_lt⟩, hkb, _, _⟩,
  { rw [fin.le_iff_coe_le_coe, fin.coe_add_one],
    split_ifs;
    simp [nat.succ_le_iff, hkb] },
  simp [fin.ext_iff, fin.coe_add, ←hk, nat.mod_eq_of_lt b.is_lt]
end

namespace fin

lemma coe_sub_iff_le {n : ℕ} {a b : fin n} :
  (↑(a - b) : ℕ) = a - b ↔ b ≤ a :=
begin
  cases n, {exact fin_zero_elim a},
  rw [le_iff_coe_le_coe, fin.coe_sub, ←add_tsub_assoc_of_le b.is_lt.le],
  cases le_or_lt (b : ℕ) a with h h,
  { simp [←tsub_add_eq_add_tsub h, h, nat.mod_eq_of_lt ((nat.sub_le _ _).trans_lt a.is_lt)] },
  { rw [nat.mod_eq_of_lt, tsub_eq_zero_of_le h.le, tsub_eq_zero_iff_le, ←not_iff_not],
    { simpa [b.is_lt.trans_le (le_add_self)] using h },
    { rwa [tsub_lt_iff_left (b.is_lt.le.trans (le_add_self)), add_lt_add_iff_right] } }
end

lemma coe_sub_iff_lt {n : ℕ} {a b : fin n} :
  (↑(a - b) : ℕ) = n + a - b ↔ a < b :=
begin
  cases n, {exact fin_zero_elim a},
  rw [lt_iff_coe_lt_coe, fin.coe_sub, add_comm],
  cases le_or_lt (b : ℕ) a with h h,
  { simpa [add_tsub_assoc_of_le h, ←not_le, h]
    using ((nat.mod_lt _ (nat.succ_pos _)).trans_le le_self_add).ne },
  { simp [←tsub_tsub_assoc b.is_lt.le h.le, ←tsub_add_eq_add_tsub b.is_lt.le,
          nat.mod_eq_of_lt (tsub_lt_self (nat.succ_pos _) (tsub_pos_of_lt h)), h] }
end

end fin

include hb

variables [is_succ_archimedean Z]

instance : has_sub Σ :=
⟨λ f g,
  { to_fun := λ x, f x - g x - difcar f g x,
    bounded' := begin
      rintro ⟨x, hx⟩,
      obtain ⟨w, hw, hfgw⟩ : ∃ w ≥ x, difcar f g w = 0,
      { cases difcar_eq_zero_or_one f g x with px px,
        { exact ⟨x, le_rfl, px⟩ },
        { rw difcar_eq_one_iff at px,
          obtain ⟨y, hxy, hfgy, px⟩ := px,
          have := hx y hxy,
          rw sub_eq_iff_eq_add at this,
          refine ⟨y, le_of_lt hxy, _⟩,
          refine or.resolve_right (difcar_eq_zero_or_one _ _ _) (λ H, _),
          rw [H, ←nat.cast_add_one, zmod.nat_cast_self, sub_eq_zero] at this,
          exact absurd this hfgy.ne } },
      suffices : ∀ z > w, difcar f g z = 0 ∧ f z = b,
      {  obtain ⟨z, hwz, hz⟩ := f.exists_bounded w,
        exact not_le_of_lt hz (this _ hwz).right.ge },
      suffices : ∀ z > x, difcar f g (pred z) = 0 → f z = b ∧ g z = 0 ∧ difcar f g z = 0,
      { intros z hwz,
        refine succ.rec _ _ (succ_le_of_lt hwz),
        { refine (this _ (lt_of_le_of_lt hw (lt_succ _)) _).symm.imp and.elim_right id,
          rwa pred_succ },
        { rintros k hk ⟨hd, hf⟩,
          refine (this _ _ _).symm.imp and.elim_right id,
          { exact lt_of_lt_of_le (lt_of_le_of_lt hw (succ_le_iff.mp hk)) (le_succ _) },
          { rwa pred_succ } } },
      intros z hxz hfgz,
      specialize hx z hxz,
      rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at hx,
      rcases lt_trichotomy (f z) (g z) with H|H|H,
      { simpa [difcar_pred_eq_one H, ne_of_gt hb.out] using hfgz },
      { simpa [←difcar_pred_eq_difcar H, H, hfgz, fin.ext_iff ↑b, ne_of_gt hb.out] using hx },
      cases difcar_eq_zero_or_one f g z with hd hd,
      { rw [hd, add_zero] at hx,
        cases (fin.zero_le (g z)).eq_or_lt with hg hg,
        { simp [hx, ←hg, hd] },
        { have : g z - 1 = b + g z,
          { simp [sub_eq_iff_eq_add, add_right_comm] },
          casesI b, -- TODO
          { simp [hd] },
          rw [hx, ←this, fin.lt_sub_one_iff] at H,
          simp [hx, H, hd] } },
      { simpa [hd, H.ne'] using hx }
    end }⟩

variables (f g)

omit hb

/-- A recursor that splits `n` into a multiple of `b` and a remainder `r` -/
def int.mul_add_cases {C : ℤ → Sort*} (n b : ℤ) (hb : b ≠ 0)
  (hm : ∀ (k : ℤ) (r < |b|), C (b * k + r)) : C n :=
cast (congr_arg _ (int.div_add_mod n b)) (hm (n / b) (n % b) (int.mod_lt _ hb))

/-- Recursion principle based on the div and modulus decomposition against some base `b : ℤ`:
given maps `C k → C (k + b)` and `C k → C (k - b)` for each `k`,
and the construction of `C r` for all `r < |b|`, one can construct `C n` for any `n : ℤ`.  -/
@[elab_as_eliminator]
def add_sub_base_rec {C : ℤ → Sort*} (n b : ℤ) (hb : b ≠ 0) (hr : ∀ r < |b|, C r)
  (hp : ∀ k, C k → C (k + b)) (hn : ∀ k, C k → C (k - b)): C n :=
int.mul_add_cases _ _ hb $ λ z, int.induction_on' z 0
  (λ r hrb, cast (congr_arg _ (by ring)) (hr r hrb))
  (λ k kpos IH r hrb, cast (congr_arg _ (by ring)) (hp _ (IH r hrb)))
  (λ k kneg IH r hrb, cast (congr_arg _ (by ring)) (hn _ (IH r hrb)))

lemma int.neg_mod {a b : ℤ} : -a % b = (b - a) % b :=
by rw [←int.add_mod_self_left, sub_eq_add_neg]

include hb

protected lemma formal_series.sub_def (x : Z) : (f - g) x = f x - g x - difcar f g x := rfl

lemma coe_sub (z : Z) :
  ((f - g) z : ℤ) = f z - g z - difcar f g z + (b + 1) * (difcar f g (pred z)) :=
begin
  simp_rw [coe_coe, f.sub_def, fin.coe_sub],
  simp only [nat.cast_sub, (g z).is_lt.le, (difcar f g z).is_lt.le, nat.mod_add_mod,
             int.coe_nat_mod, nat.cast_add, nat.cast_one],
  rw [add_sub, add_sub, add_comm, ←add_sub, int.add_mod_self_left, add_comm,
      ←add_sub, ←add_sub, int.add_mod_self_left],
  casesI b,
  { exact absurd hb.out (lt_irrefl _) },
  rw ←nat.cast_succ,
  rcases lt_trichotomy (f z) (g z) with h|h|h,
  any_goals { have h' := h, rw fin.lt_iff_coe_lt_coe at h', },
  { simp only [difcar_pred_eq_one h, fin.coe_one, nat.cast_one, mul_one],
    rw [←int.add_mod_self, int.mod_eq_of_lt],
    { rw [sub_add, sub_sub, le_sub, sub_zero, add_sub, tsub_le_iff_right, ←nat.cast_add,
          ←nat.cast_add, int.coe_nat_le_coe_nat_iff],
      exact le_add_self.trans' ((add_le_add (g z).is_le
        (fin.le_iff_coe_le_coe.mp (difcar_le_one _ _ _)))) },
    { simp only [sub_lt, add_lt_iff_neg_right, tsub_zero],
      refine (int.sub_le_self _ _).trans_lt _;
      simp [h] } },
  { simp only [h, difcar_pred_eq_difcar h, int.neg_mod, sub_self, zero_sub],
    cases difcar_eq_zero_or_one f g z with hd hd,
    { simp [hd] },
    { rw [hd, fin.coe_one, ←nat.cast_sub, ←int.coe_nat_mod];
      simp [nat.succ_le_succ_iff] } },
  { simp only [difcar_pred_eq_zero h, fin.coe_zero, nat.cast_zero, mul_zero, add_zero],
    rw [←nat.cast_sub h'.le, int.mod_eq_of_lt],
    { rw [sub_nonneg, nat.cast_le, le_tsub_iff_right h'.le, add_comm],
      cases difcar_eq_zero_or_one f g z with hd hd;
      simp [hd, nat.succ_le_iff, h', h'.le] },
    { rw [←nat.cast_sub, int.coe_nat_lt],
      { exact tsub_lt_of_lt (tsub_lt_of_lt (f z).is_lt), },
      { refine (fin.le_iff_coe_le_coe.mp (difcar_le_one _ _ _)).trans _,
        rw [fin.coe_one, nat.succ_le_iff, tsub_pos_iff_lt],
        exact h' } } }
end

protected lemma formal_series.sub_zero (f : Σ) : f - 0 = f :=
by { ext, simp [formal_series.sub_def] }

protected lemma formal_series.sub_self (f : Σ) : f - f = 0 :=
by { ext, simp [formal_series.sub_def] }

end s03

section s04

variables [is_succ_archimedean Z]

-- set_option pp.coercions false

-- The paper mistakenly says `f - (g - h) = h - (f - g)`.
protected lemma formal_series.sub_sub_comm (f g h : Σ) : f - (g - h) = h - (g - f) :=
begin
  set p := difcar g h with hp,
  set s := g - h with hs,
  set t := f - s with ht,
  set q := difcar f s with hq,
  set p' := difcar g f with hp',
  set s' := g - f with hs',
  set t' := h - s' with ht',
  set q' := difcar h s' with hq',
  have hsz : ∀ z, (s z : ℤ) = g z - h z - p z + (b + 1) * p (pred z),
  { intro z, rw [hs, hp, coe_sub g h z] },
  have htz : ∀ z, (t z : ℤ) = f z + h z - g z + (p z - q z) - (b + 1) * (p (pred z) - (q (pred z))),
  { intro z, rw [ht, hq, coe_sub f s z, hsz], ring },
  have hsz' : ∀ z, (s' z : ℤ) = g z - f z - p' z + (b + 1) * p' (pred z),
  { intro z, rw [hs', hp', coe_sub g f z] },
  have htz' : ∀ z, (t' z : ℤ) = h z + f z - g z + (p' z - q' z) -
    (b + 1) * (p' (pred z) - (q' (pred z))),
  { intro z, rw [ht', hq', coe_sub h s' z, hsz'], ring },
  have H : ∀ z, (t z : ℤ) - t' z = (p z - q z) - (p' z - q' z) -
    (b + 1) * ((p (pred z) - q (pred z)) - (p' (pred z) - q' (pred z))),
  { intro z, rw [htz, htz'], ring },
  clear hsz hsz' htz htz',
  have htd : ∀ z, | (t z : ℤ) - t' z | < b + 1,
  { intro z,
    rw [abs_lt, coe_coe, coe_coe, ←nat.cast_succ],
    refine ⟨int.neg_lt_sub_left_of_lt_add ((int.le_add_of_nonneg_right _).trans_lt' _),
      int.sub_right_lt_of_lt_add ((int.le_add_of_nonneg_right _).trans_lt' _)⟩,
    { simp },
    { exact int.coe_nat_lt_coe_nat_of_lt ((t' z).is_lt) },
    { simp },
    { exact int.coe_nat_lt_coe_nat_of_lt ((t z).is_lt) } },
  have hpq1 : ∀ z , | (p z : ℤ) - q z | ≤ 1,
  { intro z,
    rw [hp, hq],
    casesI b,
    { exact absurd hb.out (lt_irrefl _) },
    cases difcar_eq_zero_or_one g h z with hp0 hp0;
    cases difcar_eq_zero_or_one f s z with hq0 hq0;
    norm_num [hp0, hq0] },
  have hpq1' : ∀ z , | (p' z : ℤ) - q' z | ≤ 1,
  { intro z,
    rw [hp', hq'],
    casesI b,
    { exact absurd hb.out (lt_irrefl _) },
    cases difcar_eq_zero_or_one g f z with hp0 hp0;
    cases difcar_eq_zero_or_one h s' z with hq0 hq0;
    norm_num [hp0, hq0] },
  have hr2 : ∀ z, | ((p z : ℤ) - q z) - (p' z - q' z) | ≤ 2,
  { intro z,
    refine (abs_sub _ _).trans ((add_le_add (hpq1 _) (hpq1' _)).trans _),
    norm_num },
  replace hr2 : ∀ z, | (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) | ≤ 1,
  { intro z,
    specialize htd z,
    rw H at htd,
    have hr2' := hr2 (pred z),
    rw abs_le at hr2' ⊢,
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq, int.lt_iff_add_one_le, int.lt_iff_add_one_le] at hr2',
    rcases hr2' with ⟨hl|hl, hr|hr⟩,
    { rw ←le_sub_iff_add_le at hr,
      norm_num1 at hl hr,
      exact ⟨hl, hr⟩ },
    any_goals { rw [hr, abs_lt, mul_two, ←sub_sub, sub_lt_iff_lt_add, lt_sub, sub_neg_eq_add,
          sub_add_cancel] at htd,
      suffices : (b : ℤ) + 1 < 2,
      { norm_num [←lt_sub_iff_add_lt, ne_of_gt hb.out] at this },
      exact htd.left.trans_le (le_of_abs_le (hr2 _)) },
    { rw [←hl, abs_lt, mul_neg, sub_neg_eq_add, mul_two, ←add_assoc, add_lt_iff_neg_right] at htd,
      suffices : (b : ℤ) + 1 < 2,
      { norm_num [←lt_sub_iff_add_lt, ne_of_gt hb.out] at this },
      rw [←sub_neg_eq_add _ ((b : ℤ) + 1), ←sub_neg_eq_add _ ((b : ℤ) + 1), sub_lt_iff_lt_add,
          zero_add, lt_neg] at htd,
      exact htd.right.trans_le ((neg_le_abs_self _).trans (hr2 _)) } },
  replace hpq1 : ∀ z, (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = 1 →
    (p z : ℤ) - q z - (p' z - q' z) = 1,
  { intros z hz,
    specialize H z,
    rw [hz, mul_one] at H,
    have hr2' := hr2 (succ z),
    rw [pred_succ, int.abs_le_one_iff] at hr2',
    rcases hr2' with hr2'|hr2'|hr2',
    { rw [hr2', zero_sub] at H,
      exact absurd H (neg_lt_of_abs_lt (htd _)).ne' },
    { exact hr2' },
    { rw [hr2'] at H,
      refine absurd H (ne_of_gt ((neg_lt_of_abs_lt (htd _)).trans' _)),
      rw [←zero_sub ((b : ℤ) + 1), sub_lt_sub_iff_right, neg_lt_zero],
      exact zero_lt_one } },
  replace hpq1' : ∀ z, (p' (pred z) : ℤ) - q' (pred z) - (p (pred z) - q (pred z)) = 1 →
    (p' z : ℤ) - q' z - (p z - q z) = 1,
  { intros z hz,
    specialize H z,
    rw [←neg_inj, neg_sub] at hz,
    rw [hz, mul_neg, mul_one, sub_neg_eq_add] at H,
    have hr2' := hr2 (succ z),
    rw [pred_succ, int.abs_le_one_iff] at hr2',
    rcases hr2' with hr2'|hr2'|hr2',
    { rw [hr2', zero_add] at H,
      exact absurd H (lt_of_abs_lt (htd _)).ne },
    { rw [hr2'] at H,
      refine absurd H (ne_of_lt ((lt_of_abs_lt (htd _)).trans _)),
      simp },
    { rw [←neg_inj, neg_sub, hr2'] } },
  clear htd,
  replace hpq1 : ∀ z, (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = 1 →
    ∀ y ≥ z, (p y : ℤ) - q y - (p' y - q' y) = 1,
  { intros z hz y hy,
    refine succ.rec (hpq1 _ hz) (λ x hx hpx, hpq1 _ _) hy,
    rw pred_succ,
    exact hpx },
  replace hpq1' : ∀ z, (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = -1 →
    ∀ y ≥ z, (p y : ℤ) - q y - (p' y - q' y) = -1,
  { intros z hz y hy,
    rw [eq_comm, neg_eq_iff_neg_eq, neg_sub] at hz ⊢,
    refine succ.rec (hpq1' _ hz) (λ x hx hpx, hpq1' _ _) hy,
    rw pred_succ,
    exact hpx },
  replace hpq1 : ¬ ∃ z, (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = 1,
  { rintro ⟨z, hz⟩,
    suffices : ∀ y > z, (t' y : ℤ) = b,
    { obtain ⟨x, hx, hb⟩ := t'.exists_bounded z,
      specialize this x hx,
      simp only [coe_coe, nat.cast_inj] at this,
      rw [fin.lt_iff_coe_lt_coe, fin.coe_of_nat_eq_mod,
          nat.mod_eq_of_lt (nat.lt_succ_self _)] at hb,
      exact hb.ne this },
    intros y hy,
    specialize H y,
    rw [hpq1 z hz _ (le_pred_of_lt hy), hpq1 z hz _ (le_of_lt hy), mul_one] at H,
    cases (fin.le_last (t' y)).eq_or_lt with hbz hbz,
    { simp [hbz], },
    { have htz0 : (0 : ℤ) = t y,
      { refine le_antisymm _ _,
        { rw [coe_coe, ←nat.cast_zero, nat.cast_le],
          exact (t y).zero_le },
        rw [sub_eq_iff_eq_add] at H,
        rw [H, sub_add, sub_le, sub_zero, add_comm, ←add_sub, le_add_iff_nonneg_right,
            sub_nonneg, coe_coe, nat.cast_le],
        exact (t' y).is_le },
      rw [←htz0, zero_sub, neg_eq_iff_neg_eq] at H,
      simp [←H] } },
  replace hpq1' : ¬ ∃ z, (p (pred z) : ℤ) - q (pred z) - (p' (pred z) - q' (pred z)) = -1,
  { rintro ⟨z, hz⟩,
    suffices : ∀ y > z, (t y : ℤ) = b,
    { obtain ⟨x, hx, hb⟩ := t.exists_bounded z,
      specialize this x hx,
      simp only [coe_coe, nat.cast_inj] at this,
      rw [fin.lt_iff_coe_lt_coe, fin.coe_of_nat_eq_mod,
          nat.mod_eq_of_lt (nat.lt_succ_self _)] at hb,
      exact hb.ne this },
    intros y hy,
    specialize H y,
    rw [hpq1' z hz _ (le_pred_of_lt hy), hpq1' z hz _ (le_of_lt hy), mul_neg, mul_one] at H,
    cases (fin.le_last (t y)).eq_or_lt with hbz hbz,
    { simp [hbz], },
    { have htz0 : (0 : ℤ) = t' y,
      { refine le_antisymm _ _,
        { rw [coe_coe, ←nat.cast_zero, nat.cast_le],
          exact (t' y).zero_le },
        rw [←neg_add', eq_comm, neg_eq_iff_neg_eq, neg_sub, sub_eq_iff_eq_add,
            ←sub_eq_add_neg, ←sub_sub, sub_sub_cancel_left] at H,
        rw [H, add_comm, ←sub_eq_add_neg, sub_le, sub_zero, coe_coe, nat.cast_le],
        exact (t y).is_le },
      rw [←htz0, sub_zero] at H,
      simp [H] } },
  replace hr2 : ∀ z, (p z : ℤ) - q z - (p' z - q' z) = 0,
  { push_neg at hpq1 hpq1',
    intros z,
    specialize hr2 (succ z),
    rw [int.abs_le_one_iff] at hr2,
    rcases hr2 with hr2'|hr2'|hr2',
    { rw ←pred_succ z,
      exact hr2' },
    { exact absurd hr2' (hpq1 _) },
    { exact absurd hr2' (hpq1' _) } },
  ext z,
  rw [←@nat.cast_inj ℤ, ←sub_eq_zero, ←coe_coe, ←coe_coe, H, hr2, hr2, mul_zero, sub_zero]
end

end s04

section s05

variables [is_succ_archimedean Z]

instance : has_add Σ := ⟨λ f g, f - (0 - g)⟩

-- 5.1
protected lemma formal_series.add_def : f + g = f - (0 - g) := rfl
-- (i)
protected lemma formal_series.add_zero : f + 0 = f :=
calc f + 0 = f - (0 - 0) : rfl
...        = f - 0       : by rw [formal_series.sub_zero]
...        = f           : formal_series.sub_zero _
-- (ii)
protected lemma formal_series.add_comm : f + g = g + f :=
calc f + g = f - (0 - g) : rfl
...        = g - (0 - f) : formal_series.sub_sub_comm _ _ _
...        = g + f       : rfl
-- (iii)
protected lemma formal_series.add_assoc (f g h : Σ) : f + (g + h) = f + g + h :=
calc f + (g + h) = f + (h + g) : by rw [g.add_comm]
...  = f - (0 - (h - (0 - g))) : by simp_rw [formal_series.add_def]
...  = f - ((0 - g) - (h - 0)) : by rw [formal_series.sub_sub_comm 0, formal_series.sub_zero]
...  = f - ((0 - g) - h)       : by rw [formal_series.sub_zero]
...  = h - ((0 - g) - f)       : formal_series.sub_sub_comm _ _ _
...  = h - ((0 - g) - (f - 0)) : by rw [formal_series.sub_zero]
...  = h - (0 - (f - (0 - g))) : by rw [formal_series.sub_sub_comm 0, formal_series.sub_zero]
...  = h + (f + g)             : by simp_rw [formal_series.add_def]
...  = f + g + h               : formal_series.add_comm _ _
-- (iv)
protected lemma formal_series.add_sub_cancel : g + (f - g) = f :=
calc g + (f - g) = g - (0 - (f - g)) : formal_series.add_def _ _
...  = g - (g - (f - 0))             : by rw formal_series.sub_sub_comm g f 0
...  = g - (g - f)                   : by rw formal_series.sub_zero
...  = f - (g - g)                   : formal_series.sub_sub_comm _ _ _
...  = f - 0                         : by rw formal_series.sub_self
...  = f                             : formal_series.sub_zero _

instance : has_neg Σ := ⟨λ f, 0 - f⟩
protected lemma formal_series.neg_def : -f = 0 - f := rfl

instance : add_comm_group Σ :=
{ add := (+),
  add_assoc := λ _ _ _, (formal_series.add_assoc _ _ _).symm,
  zero := 0,
  zero_add := λ _, by simp [formal_series.add_def, formal_series.sub_sub_comm,
    formal_series.sub_zero],
  add_zero := λ _, by simp [formal_series.add_def, formal_series.sub_sub_comm,
    formal_series.sub_zero],
  neg := λ f, -f,
  sub := λ f g, f - g,
  sub_eq_add_neg := λ f g, by simp [g.neg_def, f.add_def, formal_series.sub_sub_comm 0,
    formal_series.sub_zero],
  add_left_neg := λ f, by simp [f.neg_def, formal_series.add_def, formal_series.sub_sub_comm,
    formal_series.sub_sub_comm 0 0 f, formal_series.sub_zero, formal_series.sub_self],
  add_comm := λ _ _, formal_series.add_comm _ _ }

end s05
