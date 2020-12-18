/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.char_p
import algebra.ring.pi
import analysis.special_functions.pow
import field_theory.perfect_closure
import ring_theory.localization
import ring_theory.subring
import ring_theory.valuation.integers

/-!
# Ring Perfection and Tilt

In this file we define the perfection of a ring of characteristic p, and the tilt of a field
given a valuation to `ℝ≥0`.

## TODO

Define the valuation on the tilt, and define a characteristic predicate for the tilt.

-/

universes u₁ u₂ u₃

open_locale nnreal

/-- The perfection of a monoid `M`, defined to be the projective limit of `M`
using the `p`-th power maps `M → M` indexed by the natural numbers, implemented as
`{ f : ℕ → M | ∀ n, f (n + 1) ^ p = f n }`. -/
def monoid.perfection (M : Type u₁) [comm_monoid M] (p : ℕ) : submonoid (ℕ → M) :=
{ carrier := { f | ∀ n, f (n + 1) ^ p = f n },
  one_mem' := λ n, one_pow _,
  mul_mem' := λ f g hf hg n, (mul_pow _ _ _).trans $ congr_arg2 _ (hf n) (hg n) }

/-- The perfection of a semiring `R` with characteristic `p`,
defined to be the projective limit of `R` using the Frobenius maps `R → R`
indexed by the natural numbers, implemented as `{ f : ℕ → R | ∀ n, f (n + 1) ^ p = f n }`. -/
def semiring.perfection (R : Type u₁) [comm_semiring R]
  (p : ℕ) [hp : fact p.prime] [char_p R p] :
  subsemiring (ℕ → R) :=
{ zero_mem' := λ n, zero_pow $ hp.pos,
  add_mem' := λ f g hf hg n, (frobenius_add R p _ _).trans $ congr_arg2 _ (hf n) (hg n),
  .. monoid.perfection R p }

/-- The perfection of a ring `R` with characteristic `p`,
defined to be the projective limit of `R` using the Frobenius maps `R → R`
indexed by the natural numbers, implemented as `{ f : ℕ → R | ∀ n, f (n + 1) ^ p = f n }`. -/
def ring.perfection (R : Type u₁) [comm_ring R] (p : ℕ) [hp : fact p.prime] [char_p R p] :
  subring (ℕ → R) :=
{ neg_mem' := λ f hf n, (frobenius_neg R p _).trans $ congr_arg _ (hf n),
  .. semiring.perfection R p }

namespace ring.perfection

variables (R : Type u₁) [comm_ring R] (p : ℕ) [hp : fact p.prime] [char_p R p]
include hp

/-- The `n`-th coefficient of an element of the perfection. -/
def coeff (n : ℕ) : ring.perfection R p →+* R :=
{ to_fun := λ f, f.1 n,
  map_one' := rfl,
  map_mul' := λ f g, rfl,
  map_zero' := rfl,
  map_add' := λ f g, rfl }

variables {R p}

@[ext] lemma ext {f g : ring.perfection R p} (h : ∀ n, coeff R p n f = coeff R p n g) : f = g :=
subtype.eq $ funext h

variables (R p)

/-- The `p`-th root of an element of the perfection. -/
def pth_root : ring.perfection R p →+* ring.perfection R p :=
{ to_fun := λ f, ⟨λ n, coeff R p (n + 1) f, λ n, f.2 _⟩,
  map_one' := rfl,
  map_mul' := λ f g, rfl,
  map_zero' := rfl,
  map_add' := λ f g, rfl }

variables {R p}

lemma coeff_pth_root (f : ring.perfection R p) (n : ℕ) :
  coeff R p n (pth_root R p f) = coeff R p (n + 1) f :=
rfl

lemma coeff_pow_p (f : ring.perfection R p) (n : ℕ) :
  coeff R p (n + 1) (f ^ p) = coeff R p n f :=
by { rw ring_hom.map_pow, exact f.2 n }

lemma coeff_frobenius (f : ring.perfection R p) (n : ℕ) :
  coeff R p (n + 1) (frobenius _ p f) = coeff R p n f :=
by convert coeff_pow_p f n

lemma pth_root_frobenius : (pth_root R p).comp (frobenius _ p) = ring_hom.id _ :=
ring_hom.ext $ λ x, ext $ λ n,
by rw [ring_hom.comp_apply, ring_hom.id_apply, coeff_pth_root, coeff_frobenius]

lemma frobenius_pth_root : (frobenius _ p).comp (pth_root R p) = ring_hom.id _ :=
ring_hom.ext $ λ x, ext $ λ n,
by rw [ring_hom.comp_apply, ring_hom.id_apply, ring_hom.map_frobenius, coeff_pth_root,
    ← ring_hom.map_frobenius, coeff_frobenius]

lemma coeff_add_ne_zero {f : ring.perfection R p} {n : ℕ} (hfn : coeff R p n f ≠ 0) (k : ℕ) :
  coeff R p (n + k) f ≠ 0 :=
nat.rec_on k hfn $ λ k ih h, ih $ by erw [← coeff_pow_p, ring_hom.map_pow, h, zero_pow hp.pos]

lemma coeff_ne_zero_of_le {f : ring.perfection R p} {m n : ℕ} (hfm : coeff R p m f ≠ 0)
  (hmn : m ≤ n) : coeff R p n f ≠ 0 :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_le hmn in hk.symm ▸ coeff_add_ne_zero hfm k

end ring.perfection

section perfectoid

variables (K : Type u₁) [field K] (v : valuation K ℝ≥0)
variables (O : Type u₂) [comm_ring O] [algebra O K] (hv : v.integers O)
variables (p : ℕ)
include hv

/-- `O/(p)` for `O`, ring of integers of `K`. -/
@[nolint unused_arguments has_inhabited_instance] def mod_p :=
(ideal.span {p} : ideal O).quotient

variables [hp : fact p.prime] [hvp : fact (v p ≠ 1)]

namespace mod_p

instance : comm_ring (mod_p K v O hv p) :=
ideal.quotient.comm_ring _

include hp hvp
instance : char_p (mod_p K v O hv p) p :=
char_p.quotient O p $ mt hv.one_of_is_unit $ ((algebra_map O K).map_nat_cast p).symm ▸ hvp

instance : nontrivial (mod_p K v O hv p) :=
char_p.nontrivial_of_char_ne_one hp.ne_one

section classical
local attribute [instance] classical.dec

omit hp hvp
/-- For a field `K` with valuation `v : K → ℝ≥0` and ring of integers `O`,
a function `O/(p) → ℝ≥0` that sends `0` to `0` and `x + (p)` to `v(x)` as long as `x ∉ (p)`. -/
noncomputable def pre_val (x : mod_p K v O hv p) : ℝ≥0 :=
if x = 0 then 0 else v (algebra_map O K x.out')

variables {K v O hv p}
lemma pre_val_mk {x : O} (hx : (ideal.quotient.mk _ x : mod_p K v O hv p) ≠ 0) :
  pre_val K v O hv p (ideal.quotient.mk _ x) = v (algebra_map O K x) :=
begin
  obtain ⟨r, hr⟩ := ideal.mem_span_singleton'.1 (ideal.quotient.eq.1 $ quotient.sound' $
    @quotient.mk_out' O (ideal.span {p} : ideal O).quotient_rel x),
  refine (if_neg hx).trans (v.map_eq_of_sub_lt $ lt_of_not_ge' _),
  erw [← ring_hom.map_sub, ← hr, hv.le_iff_dvd],
  exact λ hprx, hx (ideal.quotient.eq_zero_iff_mem.2 $ ideal.mem_span_singleton.2 $
    dvd_of_mul_left_dvd hprx),
end

lemma pre_val_zero : pre_val K v O hv p 0 = 0 :=
if_pos rfl

lemma pre_val_mul {x y : mod_p K v O hv p} (hxy0 : x * y ≠ 0) :
  pre_val K v O hv p (x * y) = pre_val K v O hv p x * pre_val K v O hv p y :=
begin
  have hx0 : x ≠ 0 := mt (by { rintro rfl, rw zero_mul }) hxy0,
  have hy0 : y ≠ 0 := mt (by { rintro rfl, rw mul_zero }) hxy0,
  obtain ⟨r, rfl⟩ := ideal.quotient.mk_surjective x,
  obtain ⟨s, rfl⟩ := ideal.quotient.mk_surjective y,
  rw ← ring_hom.map_mul at hxy0 ⊢,
  rw [pre_val_mk hx0, pre_val_mk hy0, pre_val_mk hxy0, ring_hom.map_mul, v.map_mul]
end

lemma pre_val_add (x y : mod_p K v O hv p) :
  pre_val K v O hv p (x + y) ≤ max (pre_val K v O hv p x) (pre_val K v O hv p y) :=
begin
  by_cases hx0 : x = 0, { rw [hx0, zero_add], exact le_max_right _ _ },
  by_cases hy0 : y = 0, { rw [hy0, add_zero], exact le_max_left _ _ },
  by_cases hxy0 : x + y = 0, { rw [hxy0, pre_val_zero], exact zero_le _ },
  obtain ⟨r, rfl⟩ := ideal.quotient.mk_surjective x,
  obtain ⟨s, rfl⟩ := ideal.quotient.mk_surjective y,
  rw ← ring_hom.map_add at hxy0 ⊢,
  rw [pre_val_mk hx0, pre_val_mk hy0, pre_val_mk hxy0, ring_hom.map_add], exact v.map_add _ _
end

lemma v_p_lt_pre_val {x : mod_p K v O hv p} : v p < pre_val K v O hv p x ↔ x ≠ 0 :=
begin
  refine ⟨λ h hx, by { rw [hx, pre_val_zero] at h, exact not_lt_zero' h },
    λ h, lt_of_not_ge' $ λ hp, h _⟩,
  obtain ⟨r, rfl⟩ := ideal.quotient.mk_surjective x,
  rw [pre_val_mk h, ← (algebra_map O K).map_nat_cast p, hv.le_iff_dvd] at hp,
  rw [ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton], exact hp
end

lemma pre_val_eq_zero {x : mod_p K v O hv p} : pre_val K v O hv p x = 0 ↔ x = 0 :=
⟨λ hvx, classical.by_contradiction $ λ hx0 : x ≠ 0,
  by { rw [← v_p_lt_pre_val, hvx] at hx0, exact not_lt_zero' hx0 },
λ hx, hx.symm ▸ pre_val_zero⟩

variables (hv hvp)
lemma v_p_lt_val {x : O} :
  v p < v (algebra_map O K x) ↔ (ideal.quotient.mk _ x : mod_p K v O hv p) ≠ 0 :=
by rw [lt_iff_not_ge', not_iff_not, ← (algebra_map O K).map_nat_cast p, hv.le_iff_dvd,
      ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton]

open nnreal

variables {hv} [hvp]
include hp
lemma mul_ne_zero_of_pow_p_ne_zero {x y : mod_p K v O hv p} (hx : x ^ p ≠ 0) (hy : y ^ p ≠ 0) :
  x * y ≠ 0 :=
begin
  obtain ⟨r, rfl⟩ := ideal.quotient.mk_surjective x,
  obtain ⟨s, rfl⟩ := ideal.quotient.mk_surjective y,
  have h1p : (0 : ℝ) < 1 / p := one_div_pos.2 (nat.cast_pos.2 hp.pos),
  rw ← ring_hom.map_mul, rw ← ring_hom.map_pow at hx hy,
  rw ← v_p_lt_val hv at hx hy ⊢,
  rw [ring_hom.map_pow, v.map_pow, ← rpow_lt_rpow_iff h1p, ← rpow_nat_cast, ← rpow_mul,
      mul_one_div_cancel (nat.cast_ne_zero.2 hp.ne_zero : (p : ℝ) ≠ 0), rpow_one] at hx hy,
  rw [ring_hom.map_mul, v.map_mul], refine lt_of_le_of_lt _ (mul_lt_mul'''' hx hy),
  by_cases hvp : v p = 0, { rw hvp, exact zero_le _ }, replace hvp := zero_lt_iff.2 hvp,
  conv_lhs { rw ← rpow_one (v p) }, rw ← rpow_add (ne_of_gt hvp),
  refine rpow_le_rpow_of_exponent_ge hvp ((algebra_map O K).map_nat_cast p ▸ hv.2 _) _,
  rw [← add_div, div_le_one (nat.cast_pos.2 hp.pos : 0 < (p : ℝ))], exact_mod_cast hp.two_le
end

end classical

end mod_p

include hp hvp
/-- Perfection of `O/(p)` where `O` is the ring of integers of `K`. -/
@[nolint has_inhabited_instance] def pre_tilt :=
ring.perfection (mod_p K v O hv p) p

namespace pre_tilt

section classical
local attribute [instance] classical.dec

open ring.perfection

/-- The valuation `Perfection(O/(p)) → ℝ≥0` as a function.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `pre_val(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`. -/
noncomputable def val_aux (f : pre_tilt K v O hv p) : ℝ≥0 :=
if h : ∃ n, coeff _ _ n f ≠ 0
then mod_p.pre_val K v O hv p (coeff _ _ (nat.find h) f) ^ (p ^ nat.find h)
else 0

variables {K v O hv p}
lemma coeff_nat_find_add_ne_zero {f : pre_tilt K v O hv p} {h : ∃ n, coeff _ _ n f ≠ 0} (k : ℕ) :
  coeff _ _ (nat.find h + k) f ≠ 0 :=
coeff_add_ne_zero (nat.find_spec h) k

lemma val_aux_eq {f : pre_tilt K v O hv p} {n : ℕ} (hfn : coeff _ _ n f ≠ 0) :
  val_aux K v O hv p f = mod_p.pre_val K v O hv p (coeff _ _ n f) ^ (p ^ n) :=
begin
  have h : ∃ n, coeff _ _ n f ≠ 0 := ⟨n, hfn⟩,
  rw [val_aux, dif_pos h],
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le (nat.find_min' h hfn),
  induction k with k ih, { refl },
  obtain ⟨x, hx⟩ := ideal.quotient.mk_surjective (coeff _ _ (nat.find h + k + 1) f),
  have h1 : (ideal.quotient.mk _ x : mod_p K v O hv p) ≠ 0 := hx.symm ▸ hfn,
  have h2 : (ideal.quotient.mk _ (x ^ p) : mod_p K v O hv p) ≠ 0,
    by { erw [ring_hom.map_pow, hx, ← ring_hom.map_pow, coeff_pow_p],
      exact coeff_nat_find_add_ne_zero k },
  erw [ih (coeff_nat_find_add_ne_zero k), ← hx, ← coeff_pow_p, ring_hom.map_pow, ← hx,
      ← ring_hom.map_pow, mod_p.pre_val_mk h1, mod_p.pre_val_mk h2,
      ring_hom.map_pow, v.map_pow, ← pow_mul, pow_succ], refl
end

lemma val_aux_zero : val_aux K v O hv p 0 = 0 :=
dif_neg $ λ ⟨n, hn⟩, hn rfl

lemma val_aux_one : val_aux K v O hv p 1 = 1 :=
(val_aux_eq $ by exact one_ne_zero).trans $
by { rw [pow_zero, pow_one, ring_hom.map_one, ← (ideal.quotient.mk _).map_one, mod_p.pre_val_mk,
    ring_hom.map_one, v.map_one], exact @one_ne_zero (mod_p K v O hv p) _ _ }

lemma val_aux_mul (f g : pre_tilt K v O hv p) :
  val_aux K v O hv p (f * g) = val_aux K v O hv p f * val_aux K v O hv p g :=
begin
  by_cases hf : f = 0, { rw [hf, zero_mul, val_aux_zero, zero_mul] },
  by_cases hg : g = 0, { rw [hg, mul_zero, val_aux_zero, mul_zero] },
  replace hf : ∃ n, coeff _ _ n f ≠ 0 := not_forall.1 (λ h, hf $ ring.perfection.ext h),
  replace hg : ∃ n, coeff _ _ n g ≠ 0 := not_forall.1 (λ h, hg $ ring.perfection.ext h),
  obtain ⟨m, hm⟩ := hf, obtain ⟨n, hn⟩ := hg,
  replace hm := coeff_ne_zero_of_le hm (le_max_left m n),
  replace hn := coeff_ne_zero_of_le hn (le_max_right m n),
  have hfg : coeff _ _ (max m n + 1) (f * g) ≠ 0,
  { rw ring_hom.map_mul, refine mod_p.mul_ne_zero_of_pow_p_ne_zero _ _;
    rw [← ring_hom.map_pow, coeff_pow_p]; assumption },
  rw [val_aux_eq (coeff_add_ne_zero hm 1), val_aux_eq (coeff_add_ne_zero hn 1), val_aux_eq hfg],
  rw ring_hom.map_mul at hfg ⊢, rw [mod_p.pre_val_mul hfg, mul_pow]
end

lemma val_aux_add (f g : pre_tilt K v O hv p) :
  val_aux K v O hv p (f + g) ≤ max (val_aux K v O hv p f) (val_aux K v O hv p g) :=
begin
  by_cases hf : f = 0, { rw [hf, zero_add, val_aux_zero, max_eq_right], exact zero_le _ },
  by_cases hg : g = 0, { rw [hg, add_zero, val_aux_zero, max_eq_left], exact zero_le _ },
  by_cases hfg : f + g = 0, { rw [hfg, val_aux_zero], exact zero_le _ },
  replace hf : ∃ n, coeff _ _ n f ≠ 0 := not_forall.1 (λ h, hf $ ring.perfection.ext h),
  replace hg : ∃ n, coeff _ _ n g ≠ 0 := not_forall.1 (λ h, hg $ ring.perfection.ext h),
  replace hfg : ∃ n, coeff _ _ n (f + g) ≠ 0 := not_forall.1 (λ h, hfg $ ring.perfection.ext h),
  obtain ⟨m, hm⟩ := hf, obtain ⟨n, hn⟩ := hg, obtain ⟨k, hk⟩ := hfg,
  replace hm := coeff_ne_zero_of_le hm (le_trans (le_max_left m n) (le_max_left _ k)),
  replace hn := coeff_ne_zero_of_le hn (le_trans (le_max_right m n) (le_max_left _ k)),
  replace hk := coeff_ne_zero_of_le hk (le_max_right (max m n) k),
  rw [val_aux_eq hm, val_aux_eq hn, val_aux_eq hk, ring_hom.map_add],
  cases le_max_iff.1
    (mod_p.pre_val_add (coeff _ _ (max (max m n) k) f) (coeff _ _ (max (max m n) k) g)) with h h,
  { exact le_max_left_of_le (canonically_ordered_semiring.pow_le_pow_of_le_left h _) },
  { exact le_max_right_of_le (canonically_ordered_semiring.pow_le_pow_of_le_left h _) }
end

variables (K v O hv p)
/-- The valuation `Perfection(O/(p)) → ℝ≥0`.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `pre_val(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`. -/
noncomputable def val : valuation (pre_tilt K v O hv p) ℝ≥0 :=
{ to_fun := val_aux K v O hv p,
  map_one' := val_aux_one,
  map_mul' := val_aux_mul,
  map_zero' := val_aux_zero,
  map_add' := val_aux_add }

variables {K v O hv p}
lemma map_eq_zero {f : pre_tilt K v O hv p} : val K v O hv p f = 0 ↔ f = 0 :=
begin
  by_cases hf0 : f = 0, { rw hf0, exact iff_of_true (valuation.map_zero _) rfl },
  obtain ⟨n, hn⟩ : ∃ n, coeff _ _ n f ≠ 0 := not_forall.1 (λ h, hf0 $ ring.perfection.ext h),
  show val_aux K v O hv p f = 0 ↔ f = 0, refine iff_of_false (λ hvf, hn _) hf0,
  rw val_aux_eq hn at hvf, replace hvf := nnreal.pow_eq_zero hvf, rwa mod_p.pre_val_eq_zero at hvf
end

end classical

instance : integral_domain (pre_tilt K v O hv p) :=
{ exists_pair_ne := (char_p.nontrivial_of_char_ne_one hp.ne_one).1,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ f g hfg,
    by { simp_rw ← map_eq_zero at hfg ⊢, contrapose! hfg, rw valuation.map_mul,
      exact mul_ne_zero hfg.1 hfg.2 },
  .. (infer_instance : comm_ring (pre_tilt K v O hv p)) }

end pre_tilt

/-- The tilt of a field, as defined in Perfectoid Spaces by Peter Scholze, as in
[scholze2011perfectoid]. Given a field `K` with valuation `K → ℝ≥0` and ring of integers `O`,
this is implemented as the fraction field of the perfection of `O/(p)`. -/
@[nolint has_inhabited_instance] def tilt :=
fraction_ring (pre_tilt K v O hv p)

namespace tilt

noncomputable instance : field (tilt K v O hv p) :=
fraction_ring.field

end tilt

end perfectoid
