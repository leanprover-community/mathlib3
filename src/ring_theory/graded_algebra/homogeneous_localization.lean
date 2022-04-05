/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import ring_theory.localization.at_prime
import ring_theory.graded_algebra.basic

/-!
# Homogeneous Localization

## Notation
- `ι` is a commutative monoid;
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ι → submodule R A` is the grading of `A`;
- `x : ideal A` is a prime ideal.

## Main definitions and results

This file constructs the subring of `Aₓ` where the numerator and denominator have the same grading,
i.e. `{a/b ∈ Aₓ | ∃ (i : ι), a ∈ 𝒜ᵢ ∧ b ∈ 𝒜ᵢ}`.

* `homogeneous_localization.num_denom_same_deg`: a structure with a numerator and denominator field
  where they are required to have the same grading.

However `num_denom_same_deg 𝒜 x` cannot have a ring structure for many reasons, for example if `c`
is a `num_denom_same_deg`, then generally, `c + (-c)` is not necessarily `0` for degree reasons ---
`0` is considered to have grade zero (see `deg_zero`) but `c + (-c)` has the same degree as `c`. To
circumvent this, we quotient `num_denom_same_deg 𝒜 x` by the kernel of `c ↦ c.num / c.denom`.

* `homogeneous_localization.num_denom_same_deg.embedding` : for `x : prime ideal of A` and any
  `c : num_denom_same_deg 𝒜 x`, or equivalent a numerator and a denominator of the same degree,
  we get an element `c.num / c.denom` of `Aₓ`.
* `homogeneous_localization`: `num_denom_same_deg 𝒜 x` quotiented by kernel of `embedding 𝒜 x`.
* `homogeneous_localization.val`: if `f : homogeneous_localization 𝒜 x`, then `f.val` is an element
  of `Aₓ`. In another word, one can view `homogeneous_localization 𝒜 x` as a subring of `Aₓ`
  through `homogeneous_localization.val`.
* `homogeneous_localization.num`: if `f : homogeneous_localization 𝒜 x`, then `f.num : A` is the
  numerator of `f`.
* `homogeneous_localization.num`: if `f : homogeneous_localization 𝒜 x`, then `f.denom : A` is the
  denominator of `f`.
* `homogeneous_localization.deg`: if `f : homogeneous_localization 𝒜 x`, then `f.deg : ι` is the
  degree of `f` such that `f.num ∈ 𝒜 f.deg` and `f.denom ∈ 𝒜 f.deg`
  (see `homogeneous_localization.num_mem` and `homogeneous_localization.denom_mem`).
* `homogeneous_localization.num_mem`: if `f : homogeneous_localization 𝒜 x`, then `f.num_mem` is a
  proof that `f.num ∈ f.deg`.
* `homogeneous_localization.denom_mem`: if `f : homogeneous_localization 𝒜 x`, then `f.denom_mem`
  is a proof that `f.denom ∈ f.deg`.
* `homogeneous_localization.eq_num_div_denom`: if `f : homogeneous_localization 𝒜 x`, then
  `f.val : Aₓ` is equal to `f.num / f.denom`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

noncomputable theory

open_locale direct_sum big_operators pointwise
open direct_sum set_like

variables {ι R A: Type*}
variables [add_comm_monoid ι] [decidable_eq ι]
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variables (x : ideal A) [ideal.is_prime x]

local notation `at ` x := localization.at_prime x

namespace homogeneous_localization

section
/--
Let `x` be a prime ideal, then `num_denom_same_deg 𝒜 x` is a structure with a numerator and a
denominator with same grading such that the denominator is not contained in `x`.
-/
@[nolint has_inhabited_instance]
structure num_denom_same_deg :=
(deg : ι)
(num denom : 𝒜 deg)
(denom_not_mem : (denom : A) ∉ x)

end

namespace num_denom_same_deg

open set_like.graded_monoid submodule

variable {𝒜}
@[ext] lemma ext {c1 c2 : num_denom_same_deg 𝒜 x} (hdeg : c1.deg = c2.deg)
  (hnum : (c1.num : A) = c2.num) (hdenom : (c1.denom : A) = c2.denom) :
  c1 = c2 :=
begin
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩,
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩,
  dsimp only [subtype.coe_mk] at *,
  simp only,
  exact ⟨hdeg, by subst hdeg; subst hnum, by subst hdeg; subst hdenom⟩,
end

instance : has_one (num_denom_same_deg 𝒜 x) :=
{ one :=
  { deg := 0,
    num := ⟨1, one_mem⟩,
    denom := ⟨1, one_mem⟩,
    denom_not_mem := λ r, (infer_instance : x.is_prime).ne_top $ x.eq_top_iff_one.mpr r } }

@[simp] lemma deg_one : (1 : num_denom_same_deg 𝒜 x).deg = 0 := rfl
@[simp] lemma num_one : ((1 : num_denom_same_deg 𝒜 x).num : A) = 1 := rfl
@[simp] lemma denom_one : ((1 : num_denom_same_deg 𝒜 x).denom : A) = 1 := rfl

instance : has_zero (num_denom_same_deg 𝒜 x) :=
{ zero := ⟨0, 0, ⟨1, one_mem⟩, λ r, (infer_instance : x.is_prime).ne_top $ x.eq_top_iff_one.mpr r⟩ }

@[simp] lemma deg_zero : (0 : num_denom_same_deg 𝒜 x).deg = 0 := rfl
@[simp] lemma num_zero : (0 : num_denom_same_deg 𝒜 x).num = 0 := rfl
@[simp] lemma denom_zero : ((0 : num_denom_same_deg 𝒜 x).denom : A) = 1 := rfl

instance : has_mul (num_denom_same_deg 𝒜 x) :=
{ mul := λ p q,
  { deg := p.deg + q.deg,
    num := ⟨p.num * q.num, mul_mem p.num.prop q.num.prop⟩,
    denom := ⟨p.denom * q.denom, mul_mem p.denom.prop q.denom.prop⟩,
    denom_not_mem := λ r, or.elim
      ((infer_instance : x.is_prime).mem_or_mem r) p.denom_not_mem q.denom_not_mem } }

@[simp] lemma deg_mul (c1 c2 : num_denom_same_deg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg := rfl
@[simp] lemma num_mul (c1 c2 : num_denom_same_deg 𝒜 x) :
  ((c1 * c2).num : A) = c1.num * c2.num := rfl
@[simp] lemma denom_mul (c1 c2 : num_denom_same_deg 𝒜 x) :
  ((c1 * c2).denom : A) = c1.denom * c2.denom := rfl

instance : has_add (num_denom_same_deg 𝒜 x) :=
{ add := λ c1 c2,
  { deg := c1.deg + c2.deg,
    num := ⟨c1.denom * c2.num + c2.denom * c1.num,
      add_mem _ (mul_mem c1.denom.2 c2.num.2)
        (add_comm c2.deg c1.deg ▸ mul_mem c2.denom.2 c1.num.2)⟩,
    denom := ⟨c1.denom * c2.denom, mul_mem c1.denom.2 c2.denom.2⟩,
    denom_not_mem := λ r, or.elim
      ((infer_instance : x.is_prime).mem_or_mem r) c1.denom_not_mem c2.denom_not_mem } }

@[simp] lemma deg_add (c1 c2 : num_denom_same_deg 𝒜 x) : (c1 + c2).deg = c1.deg + c2.deg := rfl
@[simp] lemma num_add (c1 c2 : num_denom_same_deg 𝒜 x) :
  ((c1 + c2).num : A) = c1.denom * c2.num + c2.denom * c1.num := rfl
@[simp] lemma denom_add (c1 c2 : num_denom_same_deg 𝒜 x) :
  ((c1 + c2).denom : A) = c1.denom * c2.denom := rfl

instance : has_neg (num_denom_same_deg 𝒜 x) :=
{ neg := λ c, ⟨c.deg, ⟨-c.num, neg_mem _ c.num.2⟩, c.denom, c.denom_not_mem⟩ }

@[simp] lemma deg_neg (c : num_denom_same_deg 𝒜 x) : (-c).deg = c.deg := rfl
@[simp] lemma num_neg (c : num_denom_same_deg 𝒜 x) : ((-c).num : A) = -c.num := rfl
@[simp] lemma denom_neg (c : num_denom_same_deg 𝒜 x) : ((-c).denom : A) = c.denom := rfl

instance : comm_monoid (num_denom_same_deg 𝒜 x) :=
{ one := 1,
  mul := (*),
  mul_assoc := λ c1 c2 c3, ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _),
  one_mul := λ c, ext _ (zero_add _) (one_mul _) (one_mul _),
  mul_one := λ c, ext _ (add_zero _) (mul_one _) (mul_one _),
  mul_comm := λ c1 c2, ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _) }

instance : has_pow (num_denom_same_deg 𝒜 x) ℕ :=
{ pow := λ c n, ⟨n • c.deg, ⟨c.num ^ n, pow_mem n c.num.2⟩, ⟨c.denom ^ n, pow_mem n c.denom.2⟩,
    begin
      cases n,
      { simp only [pow_zero],
        exact λ r, (infer_instance : x.is_prime).ne_top $ (ideal.eq_top_iff_one _).mpr r, },
      { exact λ r, c.denom_not_mem $
          ((infer_instance : x.is_prime).pow_mem_iff_mem n.succ (nat.zero_lt_succ _)).mp r }
    end⟩ }

@[simp] lemma deg_pow (c : num_denom_same_deg 𝒜 x) (n : ℕ) : (c ^ n).deg = n • c.deg := rfl
@[simp] lemma num_pow (c : num_denom_same_deg 𝒜 x) (n : ℕ) : ((c ^ n).num : A) = c.num ^ n := rfl
@[simp] lemma denom_pow (c : num_denom_same_deg 𝒜 x) (n : ℕ) :
  ((c ^ n).denom : A) = c.denom ^ n := rfl

section has_scalar
variables {α : Type*} [has_scalar α R] [has_scalar α A] [is_scalar_tower α R A]

instance : has_scalar α (num_denom_same_deg 𝒜 x) :=
{ smul := λ m c, ⟨c.deg, m • c.num, c.denom, c.denom_not_mem⟩ }

@[simp] lemma deg_smul (c : num_denom_same_deg 𝒜 x) (m : α) : (m • c).deg = c.deg := rfl
@[simp] lemma num_smul (c : num_denom_same_deg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num := rfl
@[simp] lemma denom_smul (c : num_denom_same_deg 𝒜 x) (m : α) :
  ((m • c).denom : A) = c.denom := rfl

end has_scalar

variable (𝒜)

/--
For `x : prime ideal of A` and any `p : num_denom_same_deg 𝒜 x`, or equivalent a numerator and a
denominator of the same degree, we get an element `p.num / p.denom` of `Aₓ`.
-/
def embedding (p : num_denom_same_deg 𝒜 x) : at x :=
localization.mk p.num ⟨p.denom, p.denom_not_mem⟩

end num_denom_same_deg

end homogeneous_localization

/--
For `x : prime ideal of A`, `homogeneous_localization 𝒜 x` is `num_denom_same_deg 𝒜 x` modulo the
kernel of `embedding 𝒜 x`. This is essentially the subring of `Aₓ` where the numerator and
denominator share the same grading.
-/
@[nolint has_inhabited_instance]
def homogeneous_localization : Type* :=
quotient (setoid.ker $ homogeneous_localization.num_denom_same_deg.embedding 𝒜 x)

namespace homogeneous_localization

open homogeneous_localization homogeneous_localization.num_denom_same_deg

variables {𝒜} {x}
/--
View an element of `homogeneous_localization 𝒜 x` as an element of `Aₓ` by forgetting that the
numerator and denominator are of the same grading.
-/
def val (y : homogeneous_localization 𝒜 x) : at x :=
quotient.lift_on' y (num_denom_same_deg.embedding 𝒜 x) $ λ _ _, id

variable (x)
lemma val_injective :
  function.injective (@homogeneous_localization.val _ _ _ _ _ _ _ _ 𝒜 _ x _) :=
λ a b, quotient.rec_on_subsingleton₂' a b $ λ a b h, quotient.sound' h

instance has_pow : has_pow (homogeneous_localization 𝒜 x) ℕ :=
{ pow := λ z n, (quotient.map' (^ n)
    (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _), begin
      change localization.mk _ _ = localization.mk _ _,
      simp only [num_pow, denom_pow],
      convert congr_arg (λ z, z ^ n) h;
      erw localization.mk_pow;
      refl,
    end) : homogeneous_localization 𝒜 x → homogeneous_localization 𝒜 x) z }

section has_scalar
variables {α : Type*} [has_scalar α R] [has_scalar α A] [is_scalar_tower α R A]
variables [is_scalar_tower α A A]

instance : has_scalar α (homogeneous_localization 𝒜 x) :=
{ smul := λ m, quotient.map' ((•) m)
    (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _), begin
      change localization.mk _ _ = localization.mk _ _,
      simp only [num_smul, denom_smul],
      convert congr_arg (λ z : at x, m • z) h;
      rw localization.smul_mk;
      refl,
    end) }

@[simp] lemma smul_val (y : homogeneous_localization 𝒜 x) (n : α) :
  (n • y).val = n • y.val :=
begin
  induction y using quotient.induction_on,
  unfold homogeneous_localization.val has_scalar.smul,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = n • localization.mk _ _,
  dsimp only,
  rw localization.smul_mk,
  congr' 1,
end

end has_scalar

instance : has_neg (homogeneous_localization 𝒜 x) :=
{ neg := quotient.map' has_neg.neg
    (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _), begin
      change localization.mk _ _ = localization.mk _ _,
      simp only [num_neg, denom_neg, ←localization.neg_mk],
      exact congr_arg (λ c, -c) h
    end) }

instance : has_add (homogeneous_localization 𝒜 x) :=
{ add := quotient.map₂' (+) (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _)
    c3 c4 (h' : localization.mk _ _ = localization.mk _ _), begin
    change localization.mk _ _ = localization.mk _ _,
    simp only [num_add, denom_add, ←localization.add_mk],
    convert congr_arg2 (+) h h';
    erw [localization.add_mk];
    refl
  end) }

instance : has_sub (homogeneous_localization 𝒜 x) :=
{ sub := λ z1 z2, z1 + (-z2) }

instance : has_mul (homogeneous_localization 𝒜 x) :=
{ mul := quotient.map₂' (*) (λ c1 c2 (h : localization.mk _ _ = localization.mk _ _)
    c3 c4 (h' : localization.mk _ _ = localization.mk _ _), begin
    change localization.mk _ _ = localization.mk _ _,
    simp only [num_mul, denom_mul],
    convert congr_arg2 (*) h h';
    erw [localization.mk_mul];
    refl,
  end) }

instance : has_one (homogeneous_localization 𝒜 x) :=
{ one := quotient.mk' 1 }

instance : has_zero (homogeneous_localization 𝒜 x) :=
{ zero := quotient.mk' 0 }

lemma zero_eq :
  (0 : homogeneous_localization 𝒜 x) = quotient.mk' 0 := rfl

lemma one_eq :
  (1 : homogeneous_localization 𝒜 x) = quotient.mk' 1 := rfl

variable {x}
lemma zero_val : (0 : homogeneous_localization 𝒜 x).val = 0 :=
localization.mk_zero _

lemma one_val : (1 : homogeneous_localization 𝒜 x).val = 1 :=
localization.mk_one

@[simp] lemma add_val (y1 y2 : homogeneous_localization 𝒜 x) :
  (y1 + y2).val = y1.val + y2.val :=
begin
  induction y1 using quotient.induction_on,
  induction y2 using quotient.induction_on,
  unfold homogeneous_localization.val has_add.add,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = localization.mk _ _ + localization.mk _ _,
  dsimp only,
  rw [localization.add_mk],
  refl
end

@[simp] lemma mul_val (y1 y2 : homogeneous_localization 𝒜 x) :
  (y1 * y2).val = y1.val * y2.val :=
begin
  induction y1 using quotient.induction_on,
  induction y2 using quotient.induction_on,
  unfold homogeneous_localization.val has_mul.mul,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = localization.mk _ _ * localization.mk _ _,
  dsimp only,
  rw [localization.mk_mul],
  refl,
end

@[simp] lemma neg_val (y : homogeneous_localization 𝒜 x) :
  (-y).val = -y.val :=
begin
  induction y using quotient.induction_on,
  unfold homogeneous_localization.val has_neg.neg,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = - localization.mk _ _,
  dsimp only,
  rw [localization.neg_mk],
  refl,
end

@[simp] lemma sub_val (y1 y2 : homogeneous_localization 𝒜 x) :
  (y1 - y2).val = y1.val - y2.val :=
by rw [show y1 - y2 = y1 + (-y2), from rfl, add_val, neg_val]; refl

@[simp] lemma pow_val (y : homogeneous_localization 𝒜 x) (n : ℕ) :
  (y ^ n).val = y.val ^ n :=
begin
  induction y using quotient.induction_on,
  unfold homogeneous_localization.val has_pow.pow,
  simp only [quotient.lift_on₂'_mk, quotient.lift_on'_mk],
  change localization.mk _ _ = (localization.mk _ _) ^ n,
  rw localization.mk_pow,
  dsimp only,
  congr' 1,
end

instance : comm_ring (homogeneous_localization 𝒜 x) :=
(homogeneous_localization.val_injective x).comm_ring _ zero_val one_val add_val mul_val neg_val
  sub_val (λ z n, smul_val x z n) (λ z n, smul_val x z n) pow_val

end homogeneous_localization

namespace homogeneous_localization

open homogeneous_localization homogeneous_localization.num_denom_same_deg

variables {𝒜} {x}

/-- numerator of an element in `homogeneous_localization x`-/
def num (f : homogeneous_localization 𝒜 x) : A :=
(quotient.out' f).num

/-- denominator of an element in `homogeneous_localization x`-/
def denom (f : homogeneous_localization 𝒜 x) : A :=
(quotient.out' f).denom

/-- For an element in `homogeneous_localization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : homogeneous_localization 𝒜 x) : ι :=
(quotient.out' f).deg

lemma denom_not_mem (f : homogeneous_localization 𝒜 x) :
  f.denom ∉ x :=
(quotient.out' f).denom_not_mem

lemma num_mem (f : homogeneous_localization 𝒜 x) : f.num ∈ 𝒜 f.deg :=
(quotient.out' f).num.2

lemma denom_mem (f : homogeneous_localization 𝒜 x) : f.denom ∈ 𝒜 f.deg :=
(quotient.out' f).denom.2

lemma eq_num_div_denom (f : homogeneous_localization 𝒜 x) :
  f.val = localization.mk f.num ⟨f.denom, f.denom_not_mem⟩ :=
begin
  have := (quotient.out_eq' f),
  apply_fun homogeneous_localization.val at this,
  rw ← this,
  unfold homogeneous_localization.val,
  simp only [quotient.lift_on'_mk'],
  refl,
end

lemma ext_iff_val (f g : homogeneous_localization 𝒜 x) : f = g ↔ f.val = g.val :=
{ mp := λ h, h ▸ rfl,
  mpr := λ h, begin
    induction f using quotient.induction_on,
    induction g using quotient.induction_on,
    rw quotient.eq,
    unfold homogeneous_localization.val at h,
    simpa only [quotient.lift_on'_mk] using h,
  end }

end homogeneous_localization
