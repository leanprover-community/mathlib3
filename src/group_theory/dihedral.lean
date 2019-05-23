/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

We define finite dihedral groups, with elements denoted by
`r i` and `s i` for `i : zmod n`.  We show that a pair of elements
`r0, s0 ∈ G` satisfying appropriate relations gives rise to a
homomorphism `Dₙ → G`, sending `r i` to `r0 ^ i` and `s i` to
`(r0 ^ i) * s0`.  (We have chosen to formulate this in
a way that works when `G` is merely a monoid, as that makes
it easier to deal with `Dₙ`-actions as homomorphisms from
`Dₙ` to endomorphism monoids.  Thus, our relations are
`r0 ^ n = s0 * s0 = 1` and `r0 * s0 * r0 = s0`.)

We also do the case n = ∞ separately.
-/

import data.fintype algebra.power_mod group_theory.cyclic

namespace group_theory

variable n : ℕ+

@[derive decidable_eq]
inductive dihedral
| r : (zmod n) → dihedral
| s : (zmod n) → dihedral

namespace dihedral

variable {n}

def log : dihedral n → (zmod n)
| (r i) := i
| (s i) := i

def is_s : dihedral n → bool
| (r _) := ff
| (s _) := tt

def to_bz : dihedral n → bool × (zmod n)
| (r i) := ⟨ff,i⟩
| (s i) := ⟨tt,i⟩

def of_bz : bool × (zmod n) → dihedral n
| ⟨ff,i⟩ := r i
| ⟨tt,i⟩ := s i

variable (n)
def bz_equiv : dihedral n ≃ (bool × (zmod n)) :=
{ to_fun := to_bz,
  inv_fun := of_bz,
  left_inv := λ g, by {cases g; refl},
  right_inv := λ bi, by {rcases bi with ⟨_|_,i⟩ ; refl} }

def inc : cyclic n → dihedral n
| (cyclic.r i) := r i

variable {n}

instance : fintype (dihedral n) :=
fintype.of_equiv (bool × (zmod n)) (bz_equiv n).symm

lemma card : fintype.card (dihedral n) = 2 * n :=
by simp [fintype.card_congr (bz_equiv n), zmod.card_zmod]

def one : dihedral n := r 0

def inv : ∀ (g : dihedral n), dihedral n
| (r i) := r (-i)
| (s i) := s i

def mul : ∀ (g h : dihedral n), dihedral n
| (r i) (r j) := r (i + j)
| (r i) (s j) := s (i + j)
| (s i) (r j) := s (i - j)
| (s i) (s j) := r (i - j)

instance : has_one (dihedral n) := ⟨r 0⟩
lemma one_eq : (1 : dihedral n) = r 0 := rfl

instance : has_inv (dihedral n) := ⟨dihedral.inv⟩
lemma r_inv (i : zmod n) : (r i)⁻¹ = r (- i) := rfl
lemma s_inv (i : zmod n) : (s i)⁻¹ = s i := rfl

instance : has_mul (dihedral n) := ⟨dihedral.mul⟩
lemma rr_mul (i j : zmod n) : (r i) * (r j) = r (i + j) := rfl
lemma rs_mul (i j : zmod n) : (r i) * (s j) = s (i + j) := rfl
lemma sr_mul (i j : zmod n) : (s i) * (r j) = s (i - j) := rfl
lemma ss_mul (i j : zmod n) : (s i) * (s j) = r (i - j) := rfl

instance : group (dihedral n) :=
begin
  refine_struct { .. dihedral.has_one, .. dihedral.has_mul, .. dihedral.has_inv};
  repeat {intro g, cases g};
  simp only
   [one_eq, r_inv, s_inv, rr_mul, rs_mul, sr_mul, ss_mul,
    zero_add, add_zero, sub_zero, add_neg, sub_self, neg_add_self,
    add_assoc, add_sub_assoc, sub_add, sub_sub]
end

instance inc_hom : is_monoid_hom (inc n) :=
{ map_one := rfl,
  map_mul := λ a b, by { cases a, cases b,
    rw [cyclic.rr_mul, inc, inc, inc, rr_mul]} }

section hom_from_gens
variables {M : Type*} [monoid M] {r0 s0: M}
variables (hr : r0 ^ (n : ℕ) = 1)
          (hs : s0 * s0 = 1)
          (hrs : r0 * s0 * r0 = s0)

variable (n)

include r0 s0 hr hs hrs

def hom_from_gens :
 (dihedral n) → M
| (r i) := r0 ^ i
| (s i) := (r0 ^ i) * s0
variable {n}

lemma hom_from_gens_r (i : zmod n) :
 hom_from_gens n hr hs hrs (r i) = r0 ^ i := rfl

lemma hom_from_gens_s (i : zmod n) :
 hom_from_gens n hr hs hrs (s i) = (r0 ^ i) * s0 := rfl

lemma sr_rs : ∀ (i : ℕ), r0 ^ i * s0 * (r0 ^ i) = s0
| 0 := by {rw [pow_zero, one_mul, mul_one]}
| (i + 1) := calc
    r0 ^ (i + 1) * s0 * r0 ^ (i + 1) =
     r0 ^ (i + 1) * s0 * r0 ^ (1 + i) : by {rw [add_comm i 1]}
    ... = (r0 ^ i * r0) * s0 * (r0 * r0 ^ i) : by {rw [pow_add, pow_add, pow_one]}
    ... = (r0 ^ i) * ((r0 * s0) * (r0 * (r0 ^ i))) :
      by rw [mul_assoc (r0 ^ i) r0 s0, mul_assoc (r0 ^ i)]
    ... = (r0 ^ i) * (((r0 * s0) * r0) * r0 ^ i) :
      by rw [mul_assoc (r0 * s0) r0 (r0 ^ i)]
    ... = s0 : by rw [hrs, ← mul_assoc, sr_rs i]

lemma sr_rs' : ∀ (i : zmod n),
 s0 * r0 ^ i = r0 ^ (- i) * s0 :=
λ i, calc
  s0 * r0 ^ i =
    1 * (s0 * r0 ^ i) : (one_mul _).symm
  ... = r0 ^ ((- i) + i)  * (s0 * r0 ^ i) :
    by rw [← pow_mod_zero, neg_add_self]
  ... = (r0 ^ (- i)) * (r0 ^ i * s0 * (r0 ^ i)) :
    by {rw [pow_mod_add hr, mul_assoc (r0 ^ (- i)), mul_assoc]}
  ... = (r0 ^ (- i)) * (r0 ^ i.val * s0 * r0 ^ i.val) : rfl
  ... = (r0 ^ (- i)) * s0 : by rw [sr_rs hr hs hrs i.val]

instance is_hom_from_gens : is_monoid_hom (hom_from_gens n hr hs hrs) :=
let h := sr_rs' hr hs hrs in
{ map_one := by {rw [one_eq, hom_from_gens_r], refl},
  map_mul := by
  { intros a b,
    cases a with i i; cases b with j j;
    simp [rr_mul, rs_mul, sr_mul, ss_mul, hom_from_gens_r, hom_from_gens_s],
    {rw [pow_mod_add hr]},
    {rw [← mul_assoc, pow_mod_add hr]},
    {rw [mul_assoc,h j, ← mul_assoc, pow_mod_add hr]},
    {rw [mul_assoc, ← mul_assoc s0 _ s0, h j, mul_assoc, hs,
         mul_one, pow_mod_add hr]}}}

end hom_from_gens
end dihedral

@[derive decidable_eq]
inductive infinite_dihedral
| r : ℤ → infinite_dihedral
| s : ℤ → infinite_dihedral

namespace infinite_dihedral

variable {n}

def log : infinite_dihedral → ℤ
| (r i) := i
| (s i) := i

def is_s : infinite_dihedral → bool
| (r _) := ff
| (s _) := tt

def to_bz : infinite_dihedral → bool × ℤ
| (r i) := ⟨ff,i⟩
| (s i) := ⟨tt,i⟩

def of_bz : bool × ℤ → infinite_dihedral
| ⟨ff,i⟩ := r i
| ⟨tt,i⟩ := s i

variable (n)
def bz_equiv : infinite_dihedral ≃ (bool × ℤ) :=
{ to_fun := to_bz,
  inv_fun := of_bz,
  left_inv := λ g, by {cases g; refl},
  right_inv := λ bi, by {rcases bi with ⟨_|_,i⟩ ; refl} }

def inc : infinite_cyclic → infinite_dihedral
| (infinite_cyclic.r i) := r i

variable {n}

def one : infinite_dihedral := r 0

def inv : ∀ (g : infinite_dihedral), infinite_dihedral
| (r i) := r (-i)
| (s i) := s i

def mul : ∀ (g h : infinite_dihedral), infinite_dihedral
| (r i) (r j) := r (i + j)
| (r i) (s j) := s (i + j)
| (s i) (r j) := s (i - j)
| (s i) (s j) := r (i - j)

instance : has_one (infinite_dihedral) := ⟨r 0⟩
lemma one_eq : (1 : infinite_dihedral) = r 0 := rfl

instance : has_inv (infinite_dihedral) := ⟨infinite_dihedral.inv⟩
lemma r_inv (i : ℤ) : (r i)⁻¹ = r (- i) := rfl
lemma s_inv (i : ℤ) : (s i)⁻¹ = s i := rfl

instance : has_mul (infinite_dihedral) := ⟨infinite_dihedral.mul⟩
lemma rr_mul (i j : ℤ) : (r i) * (r j) = r (i + j) := rfl
lemma rs_mul (i j : ℤ) : (r i) * (s j) = s (i + j) := rfl
lemma sr_mul (i j : ℤ) : (s i) * (r j) = s (i - j) := rfl
lemma ss_mul (i j : ℤ) : (s i) * (s j) = r (i - j) := rfl

instance : group (infinite_dihedral) :=
begin
  refine_struct
  { .. infinite_dihedral.has_one,
    .. infinite_dihedral.has_mul,
    .. infinite_dihedral.has_inv };
  repeat {intro g, cases g};
  simp only
   [one_eq, r_inv, s_inv, rr_mul, rs_mul, sr_mul, ss_mul,
    zero_add, add_zero, sub_zero, add_neg, sub_self, neg_add_self,
    add_assoc, add_sub_assoc, sub_add, sub_sub]
end

instance inc_hom : is_monoid_hom inc :=
{ map_one := rfl,
  map_mul := λ a b, by { cases a, cases b,
    rw [infinite_cyclic.rr_mul, inc, inc, inc, rr_mul]}}

section hom_from_gens

variables {G : Type*} [group G] (r0 : G) {s0: G}
variables (hs : s0 * s0 = 1)
          (hrs : r0 * s0 * r0 = s0)

include r0 s0 hs hrs

def hom_from_gens :
 (infinite_dihedral) → G
| (r i) := r0 ^ i
| (s i) := r0 ^ i * s0

lemma hom_from_gens_r (i : ℤ) :
hom_from_gens r0 hs hrs (r i) = r0 ^ i := rfl

lemma hom_from_gens_s (i : ℤ) :
hom_from_gens r0 hs hrs (s i) = r0 ^ i * s0 := rfl

lemma sr_rs : ∀ (i : ℤ), r0 ^ i * s0 * (r0 ^ i) = s0 :=
begin
  have h_nat : ∀ (i : ℕ), r0 ^ i * s0 * (r0 ^ i) = s0,
  begin
    intro i,
    induction i with i ih,
    {rw [pow_zero, one_mul, mul_one]},
    exact calc
      r0 ^ (i + 1) * s0 * r0 ^ (i + 1) =
        r0 ^ (i + 1) * s0 * r0 ^ (1 + i) : by {rw [add_comm i 1]}
      ... = (r0 ^ i * r0) * s0 * (r0 * r0 ^ i) : by {rw [pow_add, pow_add, pow_one]}
      ... = (r0 ^ i) * ((r0 * s0) * (r0 * (r0 ^ i))) :
        by rw [mul_assoc (r0 ^ i) r0 s0, mul_assoc (r0 ^ i)]
      ... = (r0 ^ i) * (((r0 * s0) * r0) * r0 ^ i) :
        by rw [mul_assoc (r0 * s0) r0 (r0 ^ i)]
      ... = s0 : by rw [hrs, ← mul_assoc, ih]
  end,
  rintro (i | i),
  { exact h_nat i},
  { dsimp [gpow],
    rw [mul_inv_eq_iff_eq_mul, inv_mul_eq_iff_eq_mul,← mul_assoc],
    exact (h_nat (i + 1)).symm }
end

lemma sr_rs' (i : ℤ) : s0 * (r0 ^ i) = (r0 ^ (- i)) * s0 :=
calc
  s0 * r0 ^ i = 1 * (s0 * r0 ^ i) : (one_mul _).symm
  ... = (r0 ^ ((- i) + i))  * (s0 * r0 ^ i) :
     by {rw [← pow_zero r0, neg_add_self], refl}
  ... = (r0 ^ (- i)) * ((r0 ^ i) * s0 * (r0 ^ i)) :
     by {rw [gpow_add, mul_assoc (r0 ^ (- i)), mul_assoc]}
  ... = r0 ^ (- i) * s0 : by {rw [sr_rs r0 hs hrs i]}

instance is_hom_from_gens : is_monoid_hom (hom_from_gens r0 hs hrs) :=
let h := sr_rs' r0 hs hrs in
{ map_one := by {rw [one_eq, hom_from_gens_r],refl,},
  map_mul := by
   { intros a b,
     cases a with i i; cases b with j j;
     simp [rr_mul, rs_mul, sr_mul, ss_mul, hom_from_gens_r, hom_from_gens_s],
     {rw [gpow_add]},
     {rw [← mul_assoc, gpow_add]},
     {rw [mul_assoc,h j, ← mul_assoc, gpow_add]},
     {rw [mul_assoc, ← mul_assoc s0 _ s0, h j, mul_assoc, hs, mul_one, gpow_add]}}}

end hom_from_gens

section monoid_hom_from_gens

variables {M : Type*} [monoid M] (r0 : M) {s0: M}
variables (hs : s0 * s0 = 1)
          (hrs : r0 * s0 * r0 = s0)

include r0 s0 hs hrs

def r0_unit : units M :=
{ val := r0, inv := s0 * r0 * s0,
  val_inv := by {rw [← mul_assoc,← mul_assoc, hrs, hs]},
  inv_val := by {rw [mul_assoc, mul_assoc,← mul_assoc r0, hrs, hs]} }

def s0_unit : units M :=
{ val := s0, inv := s0, val_inv := hs, inv_val := hs }

theorem hs_unit : (s0_unit r0 hs hrs) * (s0_unit r0 hs hrs) = 1 :=
 units.ext hs

theorem hrs_unit :
 (r0_unit r0 hs hrs) * (s0_unit r0 hs hrs) * (r0_unit r0 hs hrs) =
   (s0_unit r0 hs hrs) :=
 units.ext hrs

def monoid_hom_from_gens : (infinite_dihedral) → M :=
λ g, (((hom_from_gens (r0_unit r0 hs hrs)
        (hs_unit r0 hs hrs) (hrs_unit r0 hs hrs)) g : units M) : M)

lemma monoid_hom_from_gens_r_nonneg (i : ℕ) :
  monoid_hom_from_gens r0 hs hrs (r i) = r0 ^ i :=
begin
  dsimp [monoid_hom_from_gens],
  rw [hom_from_gens_r,gpow_coe_nat,units.coe_pow],
  refl
end

lemma monoid_hom_from_gens_s_nonneg (i : ℕ) :
  monoid_hom_from_gens r0 hs hrs (s i) = r0 ^ i * s0 :=
begin
  dsimp [monoid_hom_from_gens],
  rw [hom_from_gens_s,gpow_coe_nat,units.coe_mul,units.coe_pow],
  refl
end

lemma monoid_hom_from_gens_r_nonpos (i : ℕ) :
  monoid_hom_from_gens r0 hs hrs (r (- i)) = (s0 * r0 * s0) ^ i :=
begin
  dsimp [monoid_hom_from_gens],
  rw [hom_from_gens_r,gpow_neg,← inv_gpow,gpow_coe_nat,units.coe_pow],
  refl
end

lemma monoid_hom_from_gens_s_nonpos (i : ℕ) :
  monoid_hom_from_gens r0 hs hrs (s (- i)) = (s0 * r0 * s0) ^ i * s0 :=
begin
  dsimp [monoid_hom_from_gens],
  rw [hom_from_gens_s,units.coe_mul,gpow_neg,← inv_gpow,
      gpow_coe_nat,units.coe_pow],
  refl
end

instance is_monoid_hom_from_gens :
 is_monoid_hom (monoid_hom_from_gens r0 hs hrs) :=
{ map_one := by
   {rw [one_eq, ← int.coe_nat_zero, monoid_hom_from_gens_r_nonneg], refl},
 map_mul := by
   {haveI h := infinite_dihedral.is_hom_from_gens
      (r0_unit r0 hs hrs) (hs_unit r0 hs hrs) (hrs_unit r0 hs hrs),
    intros a b,
    dsimp [monoid_hom_from_gens],
    rw [@is_monoid_hom.map_mul _ _ _ _ _ h,units.coe_mul] }}

end monoid_hom_from_gens
end infinite_dihedral

end group_theory
