/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.structure_sheaf
import algebraic_geometry.Spec

noncomputable theory

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `spo g`     : basic open set at `g` in `Spec`
* `A⁰ₓ`       : the degree zero part of localized ring `Aₓ`

## Implementation

In `src/algebraic_geometry/projective_spectrum/structure_sheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any `f : A`, `Proj.T | (pbo f)` is homeomorphic to `Spec.T A⁰_f`:
  - forward direction :
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `x ∩ span {g / 1 | g ∈ A}` (see `Top_component.forward.carrier`). This ideal is prime, the proof
    is in `Top_component.forward.to_fun`. The fact that this function is continuous is found in
    `Top_component.forward`
  - backward direction : TBC

## Main Definitions and Statements

* `degree_zero_part`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `Top_component.forward`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `Top_component.forward.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero, then the preimage
  of `sbo a/f^m` under `forward f` is `pbo f ∩ pbo a`.


* [Robin Hartshorne, *Algebraic Geometry*][Har77]
-/

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise big_operators
open direct_sum set_like.graded_monoid localization finset (hiding mk_zero)

variables {R A : Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]

variables (𝒜 : ℕ → submodule R A)
variables [graded_algebra 𝒜]

open Top topological_space
open category_theory opposite
open projective_spectrum.structure_sheaf

local notation `Proj` := Proj.to_LocallyRingedSpace 𝒜
-- `Proj` as a locally ringed space
local notation `Proj.T` := Proj .1.1.1
-- the underlying topological space of `Proj`
local notation `Proj| ` U := Proj .restrict (opens.open_embedding (U : opens Proj.T))
-- `Proj` restrict to some open set
local notation `Proj.T| ` U :=
  (Proj .restrict (opens.open_embedding (U : opens Proj.T))).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Proj` restricted to some open set
local notation `pbo` x := projective_spectrum.basic_open 𝒜 x
-- basic open sets in `Proj`
local notation `sbo` f := prime_spectrum.basic_open f
-- basic open sets in `Spec`
local notation `Spec` ring := Spec.LocallyRingedSpace_obj (CommRing.of ring)
-- `Spec` as a locally ringed space
local notation `Spec.T` ring :=
  (Spec.LocallyRingedSpace_obj (CommRing.of ring)).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Spec`

section
variable {𝒜}
/--
The degree zero part of the localized ring `Aₓ` is the subring of elements of the form `a/x^n` such
that `a` and `x^n` have the same degree.
-/
def degree_zero_part {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) : subring (away f) :=
{ carrier := { y | ∃ (n : ℕ) (a : 𝒜 (m * n)), y = mk a.1 ⟨f^n, ⟨n, rfl⟩⟩ },
  mul_mem' := λ _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩, h.symm ▸ h'.symm ▸
    ⟨n+n', ⟨⟨a.1 * b.1, (mul_add m n n').symm ▸ mul_mem a.2 b.2⟩,
    by {rw mk_mul, congr' 1, simp only [pow_add], refl }⟩⟩,
  one_mem' := ⟨0, ⟨1, (mul_zero m).symm ▸ one_mem⟩,
    by { symmetry, convert ← mk_self 1, simp only [pow_zero], refl, }⟩,
  add_mem' := λ _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩, h.symm ▸ h'.symm ▸
    ⟨n+n', ⟨⟨f ^ n * b.1 + f ^ n' * a.1, (mul_add m n n').symm ▸
      add_mem (mul_mem (by { rw mul_comm, exact set_like.graded_monoid.pow_mem n f_deg }) b.2)
        begin
          rw add_comm,
          refine mul_mem _ a.2,
          rw mul_comm,
          exact set_like.graded_monoid.pow_mem _ f_deg
        end⟩, begin
          rw add_mk,
          congr' 1,
          simp only [pow_add],
          refl,
        end⟩⟩,
  zero_mem' := ⟨0, ⟨0, (mk_zero _).symm⟩⟩,
  neg_mem' := λ x ⟨n, ⟨a, h⟩⟩, h.symm ▸ ⟨n, ⟨-a, neg_mk _ _⟩⟩ }

instance (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) : comm_ring (degree_zero_part m f_deg) :=
(degree_zero_part m f_deg).to_comm_ring

/--
Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks this natural number `n`
-/
def degree_zero_part.deg {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) (x : degree_zero_part m f_deg) : ℕ :=
x.2.some

/--
Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks the numerator `a`
-/
def degree_zero_part.num {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) (x : degree_zero_part m f_deg) : A :=
x.2.some_spec.some.1

lemma degree_zero_part.num_mem {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) (x : degree_zero_part m f_deg) :
  degree_zero_part.num m f_deg x ∈ 𝒜 (m * degree_zero_part.deg m f_deg x) :=
x.2.some_spec.some.2

lemma degree_zero_part.eq {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) (x : degree_zero_part m f_deg) :
  x.1 = mk (degree_zero_part.num m f_deg x) ⟨f^(degree_zero_part.deg m f_deg x), ⟨_, rfl⟩⟩ :=
x.2.some_spec.some_spec

lemma degree_zero_part.mul_val {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) (x y : degree_zero_part m f_deg) :
  (x * y).1 = x.1 * y.1 := rfl

end

section clear_denominator

-- this is a wrapper around `is_localization.exist_integer_multiples_of_finset`, the main purpose
-- of this lemma is to make the degree of denominator explicit.
lemma clear_denominator {f : A} (s : finset (away f)) :
  ∃ (n : ℕ), ∀ (x : away f), x ∈ s →
    x * (mk (f^n) 1 : away f) ∈
    (λ y, (mk y 1 : localization.away f)) '' set.univ :=
begin
  rcases is_localization.exist_integer_multiples_of_finset (submonoid.powers f) s with
    ⟨⟨_, ⟨n, rfl⟩⟩, h⟩,
  refine ⟨n, λ x hx, _⟩,
  rcases h x hx with ⟨a, eq1⟩,
  induction x using localization.induction_on with data,
  rcases data with ⟨x, y⟩,
  dsimp at *,
  change mk a 1 = f^n • _ at eq1,
  unfold has_scalar.smul localization.smul at eq1,
  rw [localization.lift_on_mk, smul_eq_mul] at eq1,
  rw [mk_mul, mul_one, mul_comm, ← eq1],
  refine ⟨a, trivial, rfl⟩,
end

end clear_denominator

namespace Top_component

/-
This section is to construct the homeomorphism between `Proj` restricted at basic open set at
a homogeneous element `x` and `Spec A⁰ₓ` where `A⁰ₓ` is the degree zero part of the localized
ring `Aₓ`.
-/

namespace forward

-- This section is to construct the forward direction :
-- So for any `x` in `Proj| (pbo f)`, we need some point in `Spec A⁰_f`, i.e. a prime ideal,
-- and we need this correspondence to be continuous in their Zariski topology.

variables {𝒜} {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) (x : Proj| (pbo f))

/--For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
is prime is proven in `Top_component.forward.to_fun`-/
def carrier : ideal (degree_zero_part m f_deg) :=
ideal.comap (algebra_map (degree_zero_part m f_deg) (away f))
  (ideal.span { y | ∃ (g : A), g ∈ x.1.as_homogeneous_ideal.1 ∧ y = (mk g 1 : away f) })

lemma mem_carrier_iff (z : degree_zero_part m f_deg) :
  z ∈ carrier m f_deg x ↔
  z.1 ∈ ideal.span { y | ∃ (g : A), g ∈ x.1.as_homogeneous_ideal.1 ∧ y = (mk g 1 : away f) } :=
iff.rfl

lemma carrier_ne_top :
  ((x.1.as_homogeneous_ideal.1 : set A) ∩ (submonoid.powers f : set A)) = ∅ →
  carrier m f_deg x ≠ ⊤ := λ eq_top,
begin
  haveI : decidable_eq (localization.away f) := classical.dec_eq _,
  contrapose! eq_top,
  rw [ideal.eq_top_iff_one, mem_carrier_iff] at eq_top,
  change (1 : away f) ∈ _ at eq_top,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at eq_top,
  obtain ⟨c, eq1⟩ := eq_top,
  rw [finsupp.total_apply, finsupp.sum] at eq1,
  dsimp only at eq1,
  -- y = localization.mk (g y) 1
  set g :=
  λ (a : {y : away f | ∃ (g : A),
      g ∈ (projective_spectrum.as_homogeneous_ideal x.val).to_ideal ∧ y = localization.mk g 1}),
    classical.some a.2 with g_eq,
  obtain ⟨N, hN⟩ := clear_denominator (finset.image c c.support), -- N is the common denom
  choose after_clear_denominator hacd using hN,
  -- if x ∈ c.support, then `after_clear_denominator x = x * f ^ N ∈ A`
  have prop1 : ∀ i, i ∈ c.support → c i ∈ finset.image c c.support,
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  set G := ∑ i in c.support.attach, (after_clear_denominator (c i.1) (prop1 i.1 i.2)) * (g i.1) with
    G_eq,
  have G_mem1 : G ∈ x.1.as_homogeneous_ideal.1,
  { apply ideal.sum_mem, intros i hi,
    apply ideal.mul_mem_left,
    refine (classical.some_spec i.1.2).1, },
  have G_mem2 : ∃ (m : ℕ), G * f^m ∈ submonoid.powers f,
  { have eq2 := calc
          (localization.mk G 1 : localization.away f)
        = localization.mk (∑ i in c.support.attach,
          after_clear_denominator (c i.1) (prop1 i.1 i.2) * (g i.1)) 1
        : begin
          congr' 1,
        end
    ... = ∑ i in c.support.attach, localization.mk
            (after_clear_denominator (c i.1) (prop1 i.1 i.2) * (g i.1)) 1
        : begin
          induction c.support.attach using finset.induction_on with a s ha ih,
          { rw [sum_empty, sum_empty, mk_zero] },
          { rw [sum_insert ha, sum_insert ha, ←ih, add_mk, mul_one, submonoid.coe_one, one_mul,
              one_mul, add_comm] },
        end
    ... = ∑ i in c.support.attach, localization.mk
            (after_clear_denominator (c i.1) (prop1 i.1 i.2)) 1 * localization.mk (g i.1) 1
        : begin
          rw [finset.sum_congr rfl (λ i hi, _)],
          rw [localization.mk_mul, one_mul],
        end
    ... = ∑ i in c.support.attach, (c i.1) * localization.mk (f^N) 1 * localization.mk (g i.1) 1
        : begin
          rw [finset.sum_congr rfl (λ i hi, _)],
          erw ←(hacd _ _).2,
        end
    ... = ∑ i in c.support.attach, (c i.1) * localization.mk (f^N) 1 * i.1.1
        : begin
          rw [finset.sum_congr rfl (λ i hi, _)],
          rw (classical.some_spec i.1.2).2,
        end
    ... = localization.mk (f^N) 1 * ∑ i in c.support.attach, (c i.1) • i.1.1
        : begin
          rw [finset.mul_sum, finset.sum_congr rfl (λ i hi, _)], rw smul_eq_mul, ring,
        end
    ... = localization.mk (f^N) 1 * ∑ i in c.support, (c i) • i.1
        : begin
          congr' 1,
          apply finset.sum_bij',
          work_on_goal 5 { rintros a ha, exact a.2, },
          work_on_goal 4 { rintros a ha, exact ⟨a, ha⟩, },
          { rintros, dsimp only, refl, },
          { rintros, dsimp only, rw subtype.ext_iff, refl, },
          { rintros, dsimp only, rw subtype.ext_iff, },
          { rintros, dsimp only, apply finset.mem_attach, },
        end
    ... = localization.mk (f^N) 1 * 1 : by erw eq1
    ... = localization.mk (f^N) 1 : by rw mul_one,
    simp only [localization.mk_eq_mk', is_localization.eq] at eq2,
    obtain ⟨⟨c, ⟨m, rfl⟩⟩, hc2⟩ := eq2,
    erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, show (1 : submonoid.powers f).val = 1, from rfl,
      mul_one, mul_one] at hc2,
    dsimp only at hc2, rw ←pow_add at hc2,
    refine ⟨m, ⟨N+m, hc2.symm⟩⟩, },

  obtain ⟨m, hm⟩ := G_mem2,
  rw [set.ne_empty_iff_nonempty],
  refine ⟨_, _, hm⟩,
  apply ideal.mul_mem_right,
  exact G_mem1,
end

lemma no_intersection :
  ((x.1.as_homogeneous_ideal.to_ideal : set A) ∩ (submonoid.powers f : set A)) = ∅ :=
begin
  by_contra rid,
  rw [←ne.def, set.ne_empty_iff_nonempty] at rid,
  choose g hg using rid,
  obtain ⟨hg1, ⟨k, rfl⟩⟩ := hg,
  by_cases k_ineq : 0 < k,
  { erw x.1.is_prime.pow_mem_iff_mem _ k_ineq at hg1,
    exact x.2 hg1 },
  { erw [show k = 0, by linarith, pow_zero, ←ideal.eq_top_iff_one] at hg1,
    apply x.1.is_prime.1,
    exact hg1 },
end

/--The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. The fact that this function is continuous is proven in `Top_component.forward`.
-/
def to_fun : (Proj.T| (pbo f)) → (Spec.T (degree_zero_part m f_deg)) := λ x,
⟨carrier m f_deg x,
  ⟨begin
    classical,
    apply carrier_ne_top,
    apply no_intersection
  end, λ x1 x2 hx12, begin
    haveI : decidable_eq (away f) := classical.dec_eq _,
    rw mem_carrier_iff at hx12,
    rcases x1 with ⟨x1, hx1⟩,
    induction x1 using localization.induction_on with data_x1,
    rcases data_x1 with ⟨a1, _, ⟨n1, rfl⟩⟩,
    rcases x2 with ⟨x2, hx2⟩,
    induction x2 using localization.induction_on with data_x2,
    rcases data_x2 with ⟨a2, _, ⟨n2, rfl⟩⟩,
    dsimp only at hx1 hx2 hx12,
    simp only [degree_zero_part.mul_val, localization.mk_mul] at hx12,
    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hx12,
    obtain ⟨c, eq1⟩ := hx12,
    erw [finsupp.total_apply, finsupp.sum] at eq1,
    -- (a1 a2) / (f^(n + m)) = ∑ i in c.support, (c i) * i,

    have prop1 : ∀ i, i ∈ c.support → c i ∈ finset.image c c.support,
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
    set g :=
    λ (a : {y : localization (submonoid.powers f) | ∃ (g : A),
      g ∈ (projective_spectrum.as_homogeneous_ideal x.val).to_ideal ∧ y = localization.mk g 1}),
        classical.some a.2 with g_eq,
    obtain ⟨N, hN⟩ := clear_denominator (finset.image c c.support), -- N is the common denom
    choose after_clear_denominator hacd using hN,
    -- if x ∈ c.support, then `after_clear_denominator x = x * f ^ N`
    have eq2 := calc
            localization.mk (f^(n1+n2)) 1 * localization.mk (f^N) 1 *
            ∑ i in c.support, c i • i.1
          = localization.mk (f^(n1+n2)) 1 * localization.mk (f^N) 1 *
            ∑ i in c.support.attach, c (i.1) • i.1.1
          : begin
            congr' 1,
            apply finset.sum_bij',
            work_on_goal 4 { rintros a ha, exact ⟨a, ha⟩ },
            work_on_goal 5 { rintros a ha, refine ⟨a.1.1, a.1.2⟩ },
            { rintros, dsimp only, refl },
            { rintros, dsimp only, simp only [subtype.ext_iff_val] },
            { rintros, dsimp only, simp only [subtype.ext_iff_val] },
            { rintros, dsimp only, apply mem_attach },
            { rintros, dsimp only, convert a.2, simp only [subtype.ext_iff_val] }
          end
      ... = localization.mk (f^(n1+n2)) 1 * localization.mk (f^N) 1 *
            ∑ i in c.support.attach, c (i.1) * i.1.1
          : by congr' 1
      ... = localization.mk (f^(n1+n2)) 1 *
            ∑ i in c.support.attach, c (i.1) * localization.mk (f^N) 1 * i.1.1
          : begin
            erw [mul_assoc, finset.mul_sum, finset.sum_congr rfl (λ i hi, _)], ring,
          end
      ... = localization.mk (f^(n1+n2)) 1 * ∑ i in c.support.attach,
              localization.mk (after_clear_denominator (c i.1) (prop1 i.1 i.2)) 1 * i.1.1
          : begin
            erw [finset.sum_congr rfl (λ i hi, _)],
            erw ←(hacd _ _).2,
          end
      ... = localization.mk (f^(n1+n2)) 1 * ∑ i in c.support.attach,
              localization.mk (after_clear_denominator (c i.1) (prop1 i.1 i.2)) 1 *
              localization.mk (g i.1) 1
          : begin
            erw [finset.sum_congr rfl (λ i hi, _)],
            rw (classical.some_spec i.1.2).2,
          end
      ... = localization.mk (f^(n1+n2)) 1 * ∑ i in c.support.attach,
              localization.mk ((after_clear_denominator (c i.1) (prop1 i.1 i.2)) * (g i.1)) 1
          : begin
            erw [finset.sum_congr rfl (λ i hi, _)],
            rw [localization.mk_mul, mul_one],
          end
      ... = localization.mk (f^(n1+n2)) 1 *
            localization.mk (∑ i in c.support.attach, (after_clear_denominator (c i.1)
              (prop1 i.1 i.2)) * (g i.1)) 1
          : begin
            congr' 1,
            induction c.support.attach using finset.induction_on with a s ha ih,
            { rw [finset.sum_empty, finset.sum_empty, localization.mk_zero], },
            { rw [finset.sum_insert, finset.sum_insert, ih, localization.add_mk, mul_one],
              congr' 1, erw [one_mul, one_mul, add_comm], exact ha, exact ha, }
          end,
    erw [eq1, localization.mk_mul, one_mul, localization.mk_mul, one_mul] at eq2,
    have eq3 : (localization.mk (f ^ (n1 + n2) * f ^ N * (a1 * a2)) (⟨f ^ n1, _⟩ * ⟨f ^ n2, _⟩)
      : localization.away f) = localization.mk (f^N * (a1 * a2)) 1,
    { simp only [localization.mk_eq_mk'],
      rw [is_localization.eq], use 1,
      erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one, mul_one, mul_one,
        show (∀ (a b : submonoid.powers f), (a * b).val = a.val * b.val), from λ _ _, rfl,
        pow_add], ring, },
    erw [eq3, localization.mk_mul, mul_one] at eq2,
    simp only [localization.mk_eq_mk'] at eq2,
    erw [is_localization.eq] at eq2,
    obtain ⟨⟨_, ⟨k, rfl⟩⟩, eq2⟩ := eq2,
    erw [mul_one, mul_one, ←subtype.val_eq_coe] at eq2,
    dsimp only at eq2,
    have mem1 : f ^ N * (a1 * a2) * f ^ k ∈ x.1.as_homogeneous_ideal.1,
    { rw eq2, apply ideal.mul_mem_right, apply ideal.mul_mem_left,
      apply ideal.sum_mem, intros i hi,
      apply ideal.mul_mem_left,
      exact (classical.some_spec i.1.2).1, },
    rcases x.1.is_prime.mem_or_mem mem1 with h1|h3,
    rcases x.1.is_prime.mem_or_mem h1 with h1|h2,
    { exfalso, apply x.2,
      apply x.1.is_prime.mem_of_pow_mem N h1, },
    { rcases x.1.is_prime.mem_or_mem h2,
      { left, dsimp only,
        rw mem_carrier_iff,
        have eq3 : (localization.mk a1 ⟨f ^ n1, _⟩ : localization.away f) =
          localization.mk a1 1 * localization.mk 1 ⟨f^n1, ⟨n1, rfl⟩⟩,
        { erw [localization.mk_mul, mul_one, one_mul], },
        dsimp only,
        rw eq3,
        refine ideal.mul_mem_right _ _ _,
        apply ideal.subset_span,
        refine ⟨a1, h, rfl⟩, },
      { right, dsimp only,
        rw mem_carrier_iff,
        have eq3 : (localization.mk a2 ⟨f ^ n2, _⟩ : localization.away f) =
          localization.mk a2 1 * localization.mk 1 ⟨f^n2, ⟨n2, rfl⟩⟩,
        { erw [localization.mk_mul, mul_one, one_mul], },
        dsimp only,
        erw eq3,
        refine ideal.mul_mem_right _ _ _,
        apply ideal.subset_span,
        refine ⟨a2, h, rfl⟩, } },
    { exfalso, apply x.2,
      apply x.1.is_prime.mem_of_pow_mem k h3, },
  end⟩⟩

lemma preimage_eq (a : A) (n : ℕ)
  (a_mem_degree_zero : (mk a ⟨f ^ n, ⟨n, rfl⟩⟩ : away f) ∈ degree_zero_part m f_deg) :
  to_fun 𝒜 m f_deg ⁻¹'
      (sbo (⟨mk a ⟨f ^ n, ⟨_, rfl⟩⟩, a_mem_degree_zero⟩ : degree_zero_part m f_deg)).1
  = {x | x.1 ∈ (pbo f) ⊓ (pbo a)} :=
begin
  haveI : decidable_eq (away f) := classical.dec_eq _,
  symmetry,
  ext1 y, split; intros hy,
  { change y.1 ∈ _ at hy,
    rcases hy with ⟨hy1, hy2⟩,
    erw projective_spectrum.mem_basic_open at hy1 hy2,
    rw [set.mem_preimage, to_fun],
    dsimp only,
    erw prime_spectrum.mem_basic_open,
    intro rid,
    change (localization.mk a ⟨f^n, ⟨n, rfl⟩⟩ : localization.away f) ∈ _ at rid,
    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at rid,
    obtain ⟨c, eq1⟩ := rid,
    erw [finsupp.total_apply, finsupp.sum] at eq1,

    obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i.1) c.support),
    -- N is the common denom
    choose after_clear_denominator hacd using hN,
    have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },

    have eq2 := calc (localization.mk (f^N * a) 1 : localization.away f)
            = (localization.mk (f^N) 1 : localization.away f) * localization.mk a 1
            : begin
              erw [localization.mk_mul, one_mul],
            end
        ... = localization.mk (f^N) 1 * localization.mk (f^n) 1 * localization.mk a ⟨f^n, ⟨_, rfl⟩⟩
            : begin
              erw [localization.mk_mul, localization.mk_mul, localization.mk_mul, one_mul, one_mul],
              simp only [localization.mk_eq_mk', is_localization.eq],
              use 1,
              erw [mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
              dsimp only,
              ring,
            end
        ... = localization.mk (f^N) 1* localization.mk (f^n) 1 * ∑ i in c.support, c i * i.1 : by erw eq1
        ... = localization.mk (f^N) 1* localization.mk (f^n) 1 * ∑ i in c.support.attach, c i.1 * i.1.1
            : begin
              congr' 1,
              apply finset.sum_bij',
              work_on_goal 4 { rintros a ha, exact ⟨a, ha⟩ },
              work_on_goal 5 { rintros a ha, refine ⟨a.1.1, a.1.2⟩ },
              { rintros, dsimp only, refl },
              { rintros, dsimp only, simp only [subtype.ext_iff_val] },
              { rintros, dsimp only, simp only [subtype.ext_iff_val] },
              { rintros, dsimp only, apply mem_attach },
              { rintros b hb, dsimp only, convert b.2, simp only [subtype.ext_iff_val] }
            end
        ... = mk (f^n) 1 * (mk (f^N) 1 * ∑ i in c.support.attach, c i.1 * i.1.1) : by ring
        ... = mk (f^n) 1 * ∑ i in c.support.attach, mk (f^N) 1 * (c i.1 * i.1.1)
            : begin
              congr' 1,
              erw finset.mul_sum,
            end
        ... = localization.mk (f^n) 1 *
              ∑ i in c.support.attach, localization.mk
                (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
            : begin
              congr' 1,
              erw finset.sum_congr rfl (λ j hj, _),
              have := (hacd (c j * j) (prop1 j _)).2,
              dsimp only at this,
              erw [this, mul_comm],
              refl,
            end
        ... = localization.mk (f^n) 1 *
              localization.mk
                (∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
            : begin
              congr' 1,
              induction c.support.attach using finset.induction_on with a s ha ih,
              erw [finset.sum_empty, finset.sum_empty, localization.mk_zero],
              erw [finset.sum_insert ha, finset.sum_insert ha, ih, localization.add_mk,
                one_mul, one_mul, one_mul, add_comm],
            end
        ... = localization.mk (f^n * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
            : begin
              erw [localization.mk_mul, one_mul],
            end
        ... = localization.mk (∑ i in c.support.attach, f^n * after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                : by erw finset.mul_sum,

    simp only [localization.mk_eq_mk', is_localization.eq] at eq2,
    obtain ⟨⟨_, ⟨k1, rfl⟩⟩, eq2⟩ := eq2,
    erw [mul_one, mul_one, ←subtype.val_eq_coe] at eq2,
    dsimp only at eq2,

    have mem1 : (∑ i in c.support.attach, f^n * after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) * f^k1 ∈ y.1.as_homogeneous_ideal,
    { apply ideal.mul_mem_right,
      apply ideal.sum_mem,
      intros j hj,
      apply ideal.mul_mem_left,
      set g := classical.some j.1.2 with g_eq,
      have mem3 : g ∈ y.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
      have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2,
      have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
      dsimp only at eq4,

      have eq5 : ∃ (a : A) (z : ℕ), c j.1 = localization.mk a ⟨f^z, ⟨z, rfl⟩⟩,
      { induction (c j.1) using localization.induction_on with data,
        rcases data with ⟨a, ⟨_, ⟨z, rfl⟩⟩⟩,
        refine ⟨a, z, rfl⟩, },
      obtain ⟨α, z, hz⟩ := eq5,

      have eq6 := calc localization.mk (after_clear_denominator (c j.1 * j.1.1) (prop1 j.1 j.2)) 1
          = c j.1 * j.1.1 * localization.mk (f^N) 1 : eq4
      ... = (localization.mk α ⟨f^z, ⟨z, rfl⟩⟩ : localization.away f) * j.1.1 * localization.mk (f^N) 1
          : by erw hz
      ... = (localization.mk α ⟨f^z, ⟨z, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1
          : by erw eq3
      ... = localization.mk (α * g * f^N) ⟨f^z, ⟨z, rfl⟩⟩
          : begin
            erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
          end,
      simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
      obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
      erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq6,
      dsimp only at eq6,

      have mem3 : α * g * f ^ N * f ^ v ∈ y.1.as_homogeneous_ideal,
      { apply ideal.mul_mem_right,
        apply ideal.mul_mem_right,
        apply ideal.mul_mem_left,
        exact mem3, },
      erw ←eq6 at mem3,
      rcases y.1.is_prime.mem_or_mem mem3 with H1 | H3,
      rcases y.1.is_prime.mem_or_mem H1 with H1 | H2,
      { exact H1 },
      { exfalso, apply hy1,
        exact y.1.is_prime.mem_of_pow_mem _ H2, },
      { exfalso, apply hy1,
        exact y.1.is_prime.mem_of_pow_mem _ H3, }, },

    erw ←eq2 at mem1,
    rcases y.1.is_prime.mem_or_mem mem1 with H1 | H3,
    rcases y.1.is_prime.mem_or_mem H1 with H1 | H2,
    { apply hy1,
      exact y.1.is_prime.mem_of_pow_mem _ H1, },
    { apply hy2,
      exact H2, },
    { apply hy1,
      exact y.1.is_prime.mem_of_pow_mem _ H3, }, },

  { change y.1 ∈ _ ⊓ _,
    refine ⟨y.2, _⟩,
    -- a ∉ y,
    erw [set.mem_preimage, prime_spectrum.mem_basic_open] at hy,
    erw projective_spectrum.mem_basic_open,
    intro a_mem_y,
    apply hy,
    unfold to_fun,
    rw mem_carrier_iff,
    dsimp only,
    have eq1 : (localization.mk a ⟨f^n, ⟨_, rfl⟩⟩ : localization.away f) =
      localization.mk 1 ⟨f^n, ⟨_, rfl⟩⟩ * localization.mk a 1,
    { erw [localization.mk_mul, one_mul, mul_one], },
    erw eq1,
    change _ ∈ (_ : ideal _),
    convert ideal.mul_mem_left _ _ _,
    exact ideal.subset_span ⟨a, a_mem_y, rfl⟩, }
end

end forward

section

variable {𝒜}

/--The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic
open set in `Spec A⁰_f`.
-/
def forward {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj.T| (pbo f)) ⟶ (Spec.T (degree_zero_part m f_deg)) :=
{ to_fun := forward.to_fun 𝒜 m f_deg,
  continuous_to_fun := begin
    apply is_topological_basis.continuous (prime_spectrum.is_topological_basis_basic_opens),
    rintros _ ⟨⟨g, hg⟩, rfl⟩,
    induction g using localization.induction_on with data,
    obtain ⟨a, ⟨_, ⟨n, rfl⟩⟩⟩ := data,
    dsimp only,

    -- we want to use `projective_spectrum.basic_open 𝒜 (f*a) = preimage`
    set set1 : set ((Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1) :=
    { x | x.1 ∈ projective_spectrum.basic_open 𝒜 f ⊓ projective_spectrum.basic_open 𝒜 a } with set1_eq,
    have o1 : is_open set1,
    { rw is_open_induced_iff,
      refine ⟨(projective_spectrum.basic_open 𝒜 f).1 ⊓ (projective_spectrum.basic_open 𝒜 a).1,
        is_open.inter (projective_spectrum.basic_open 𝒜 f).2 (projective_spectrum.basic_open 𝒜 a).2, _⟩,
      ext z, split; intros hz,
      { erw set.mem_preimage at hz,
        erw set1_eq,
        exact hz, },
      { erw set1_eq at hz,
        change _ ∧ _ at hz,
        erw set.mem_preimage,
        exact hz, }, },
    suffices : set1 = forward.to_fun 𝒜 m f_deg ⁻¹'
      (prime_spectrum.basic_open (⟨mk a ⟨f ^ n, _⟩, hg⟩ : degree_zero_part m f_deg)).1,
    { erw ←this, exact o1, },
    { symmetry, apply forward.preimage_eq },
  end }

end

end Top_component

end algebraic_geometry
