/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.structure_sheaf
import algebraic_geometry.Spec
import ring_theory.graded_algebra.radical
import ring_theory.localization.cardinality

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
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`      : the degree zero part of localized ring `Aₓ`

## Implementation

In `src/algebraic_geometry/projective_spectrum/structure_sheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any homogeneous element `f : A` of positive degree `m`, `Proj.T | (pbo f)` is
    homeomorphic to `Spec.T A⁰_f`:
  - forward direction `to_Spec`:
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `A⁰_f ∩ span {g / 1 | g ∈ x}` (see `Proj_iso_Spec_Top_component.to_Spec.carrier`). This ideal is
    prime, the proof is in `Proj_iso_Spec_Top_component.to_Spec.to_fun`. The fact that this function
    is continuous is found in `Proj_iso_Spec_Top_component.to_Spec`
  - backward direction `from_Spec`:
    for any `q : Spec A⁰_f`, we send it to `{a | ∀ i, aᵢᵐ/fⁱ ∈ q}`; we need this to be a
    homogeneous prime ideal that is relevant.
    * This is in fact an ideal, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal`;
    * This ideal is also homogeneous, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.homogeneous`;
    * This ideal is relevant, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.relevant`;
    * This ideal is prime, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.prime`.
    Hence we have a well defined function `Spec.T A⁰_f → Proj.T | (pbo f)`, this function is called
    `Proj_iso_Spec_Top_component.from_Spec.to_fun`. But to prove the continuity of this function,
    we need to prove `from_Spec ∘ to_Spec` and `to_Spec ∘ from_Spec` are both identities (TBC).

## Main Definitions and Statements

* `degree_zero_part`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `Proj_iso_Spec_Top_component.to_Spec`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `Proj_iso_Spec_Top_component.to_Spec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `to_Spec f` is `pbo f ∩ pbo a`.

* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/

noncomputable theory

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
open _root_.homogeneous_localization localization is_localization (hiding away)

local notation `Proj` := Proj.to_LocallyRingedSpace 𝒜
-- `Proj` as a locally ringed space
local notation `Proj.T` := Proj .1.1.1
-- the underlying topological space of `Proj`
local notation `Proj| ` U := Proj .restrict (opens.open_embedding (U : opens Proj.T))
-- `Proj` restrict to some open set
local notation `Proj.T| ` U :=
  (Proj .restrict (opens.open_embedding (U : opens Proj.T))).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Proj` restricted to some open set
local notation `pbo ` x := projective_spectrum.basic_open 𝒜 x
-- basic open sets in `Proj`
local notation `sbo ` f := prime_spectrum.basic_open f
-- basic open sets in `Spec`
local notation `Spec ` ring := Spec.LocallyRingedSpace_obj (CommRing.of ring)
-- `Spec` as a locally ringed space
local notation `Spec.T ` ring :=
  (Spec.LocallyRingedSpace_obj (CommRing.of ring)).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Spec`
local notation `A⁰_ ` f := homogeneous_localization.away 𝒜 f

namespace Proj_iso_Spec_Top_component

/-
This section is to construct the homeomorphism between `Proj` restricted at basic open set at
a homogeneous element `x` and `Spec A⁰ₓ` where `A⁰ₓ` is the degree zero part of the localized
ring `Aₓ`.
-/

namespace to_Spec

open ideal

-- This section is to construct the forward direction :
-- So for any `x` in `Proj| (pbo f)`, we need some point in `Spec A⁰_f`, i.e. a prime ideal,
-- and we need this correspondence to be continuous in their Zariski topology.

variables {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : Proj| (pbo f))

/--For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
is prime is proven in `Top_component.forward.to_fun`-/
def carrier : ideal (A⁰_ f) :=
ideal.comap (algebra_map (A⁰_ f) (away f))
  (ideal.span $ algebra_map A (away f) '' x.val.as_homogeneous_ideal)

lemma mem_carrier_iff (z : A⁰_ f) :
  z ∈ carrier 𝒜 x ↔
  z.val ∈ ideal.span (algebra_map A (away f) '' x.1.as_homogeneous_ideal) :=
iff.rfl

lemma mem_carrier.clear_denominator' [decidable_eq (away f)]
  {z : localization.away f}
  (hz : z ∈ span ((algebra_map A (away f)) '' x.val.as_homogeneous_ideal)) :
  ∃ (c : algebra_map A (away f) '' x.1.as_homogeneous_ideal →₀ away f)
    (N : ℕ) (acd : Π y ∈ c.support.image c, A),
    f ^ N • z = algebra_map A (away f)
      (∑ i in c.support.attach, acd (c i) (finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * i.1.2.some) :=
begin
  rw [←submodule_span_eq, finsupp.span_eq_range_total, linear_map.mem_range] at hz,
  rcases hz with ⟨c, eq1⟩,
  rw [finsupp.total_apply, finsupp.sum] at eq1,
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := is_localization.exist_integer_multiples_of_finset (submonoid.powers f)
    (c.support.image c),
  choose acd hacd using hN,

  refine ⟨c, N, acd, _⟩,
  rw [← eq1, smul_sum, map_sum, ← sum_attach],
  congr' 1,
  ext i,
  rw [_root_.map_mul, hacd, (classical.some_spec i.1.2).2, smul_eq_mul, smul_mul_assoc],
  refl
end

lemma mem_carrier.clear_denominator [decidable_eq (away f)]
  {z : A⁰_ f} (hz : z ∈ carrier 𝒜 x) :
  ∃ (c : algebra_map A (away f) '' x.1.as_homogeneous_ideal →₀ away f)
    (N : ℕ) (acd : Π y ∈ c.support.image c, A),
    f ^ N • z.val = algebra_map A (away f)
      (∑ i in c.support.attach, acd (c i) (finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * i.1.2.some) :=
mem_carrier.clear_denominator' x $ (mem_carrier_iff 𝒜 x z).mpr hz


section carrier'
/--
The underlying set of `to_Spec.carrier` is equal to the underlying set of ideal generated by
elements in `A_f` whose numerator is in `x` and has the same degree as the denominator.
-/
def carrier' : ideal (A⁰_ f) :=
ideal.span { z | ∃ ⦃s F : A⦄ (hs : s ∈ x.1.as_homogeneous_ideal) (n : ℕ)
  (s_mem : s ∈ 𝒜 n) (F_mem1 : F ∈ 𝒜 n) (F_mem2 : F ∈ submonoid.powers f),
  z = quotient.mk' ⟨_, ⟨s, s_mem⟩, ⟨F, F_mem1⟩, F_mem2⟩ }

lemma carrier_eq_carrier' :
  carrier 𝒜 x = carrier' 𝒜 x :=
begin
  classical, ext z, split; intros hz,
  { rw mem_carrier_iff at hz,
    change z ∈ ideal.span _,
    let k : ℕ := z.denom_mem.some, have hk : f^k = z.denom := z.denom_mem.some_spec,
    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz, erw [finsupp.total_apply, finsupp.sum] at eq1,

    suffices mem1 : z.num ∈ x.1.as_homogeneous_ideal,
    { apply ideal.subset_span _,
      refine ⟨_, _, mem1, _, z.num_mem_deg, z.denom_mem_deg, z.denom_mem, _⟩,
      rw [ext_iff_val, val_mk', eq_num_div_denom], refl },

    obtain ⟨⟨_, N, rfl⟩, hN⟩ := exist_integer_multiples_of_finset (submonoid.powers f)
      (finset.image (λ i, c i * i.1) c.support),
    choose acd hacd using hN,
    change ∀ _ _, localization.mk (acd _ _) _ = _ at hacd,
    have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
    have eq3 : (mk (num z * f ^ N) 1 : localization.away f) =
    mk (∑ i in c.support.attach,
       f ^ k * acd (c i.val * i.val.val) (prop1 i.1 i.2)) 1,
    { rw [mk_sum], rw [z.eq_num_div_denom] at eq1, simp_rw [←hk] at eq1,
      convert_to _ = ∑ i in c.support.attach, (localization.mk _ 1 : localization.away f) * mk _ 1,
      { refine finset.sum_congr rfl (λ i hi, _), work_on_goal 3
        { rw [mk_mul, show (1 * 1 : submonoid.powers f) = 1, from one_mul _], }, },
      simp_rw [←finset.mul_sum, hacd, subtype.coe_mk, ←finset.smul_sum],
      rw [algebra.smul_def, ←mul_assoc],
      have eq1' := congr_arg ((*) (mk (f^k * f^N) 1) :
        localization.away f → localization.away f) eq1,
      rw [mk_mul, one_mul] at eq1', convert eq1'.symm using 1,
      { rw [mk_eq_mk', is_localization.eq], refine ⟨1, _⟩,
        simp only [submonoid.coe_one, one_mul, mul_one, subtype.coe_mk], ring1, },
      { congr' 1, swap, { nth_rewrite 1 [←finset.sum_attach], refl, },
        change localization.mk _ _ * mk (f^N) 1 = _,
        rw [mk_mul, mk_eq_mk', is_localization.eq], refine ⟨1, _⟩,
        simp only [submonoid.coe_one, one_mul, mul_one, subtype.coe_mk], }, },
    simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
    obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
    erw [mul_one, subtype.coe_mk, mul_one] at eq3,
    suffices : (∑ i in c.support.attach, (f^k * (acd (c i.1 * i.1.1) (prop1 i.1 i.2)))) * f^l ∈
      x.1.as_homogeneous_ideal,
    { erw ←eq3 at this,
      rcases x.1.is_prime.mem_or_mem this with H1 | H3,
      rcases x.1.is_prime.mem_or_mem H1 with H1 | H2,
      exacts [H1, false.elim ((projective_spectrum.mem_basic_open 𝒜 _ _).mp x.2
        (x.1.is_prime.mem_of_pow_mem _ H2)), false.elim
        ((projective_spectrum.mem_basic_open 𝒜 _ _).mp x.2 (x.1.is_prime.mem_of_pow_mem _ H3))], },

    refine ideal.mul_mem_right _ _ (ideal.sum_mem _ (λ j hj, ideal.mul_mem_left _ _ _)),
    set g := classical.some j.1.2 with g_eq,
    have mem3 : g ∈ x.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
    have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2.symm,
    have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)),
    simp_rw [algebra.smul_def] at eq4,
    have eq5 : ∃ (a : A) (z : ℕ), c j.1 = mk a ⟨f^z, ⟨z, rfl⟩⟩,
    { induction (c j.1) using localization.induction_on with data,
      rcases data with ⟨a, ⟨_, ⟨z, rfl⟩⟩⟩,
      refine ⟨a, z, rfl⟩, },
    obtain ⟨α, z, hz⟩ := eq5,
    have eq6 : (mk (acd (c j.1 * j.1.1) (prop1 j.1 j.2)) 1 : localization.away f) =
      mk (α * g * f^N) ⟨f^z, ⟨z, rfl⟩⟩,
    { erw [eq4, subtype.coe_mk, hz, eq3, mk_mul, mk_mul, one_mul, mul_one], congr' 1,
      change (f^N) * _ = _, ring1, },
    simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
    obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
    simp only [subtype.coe_mk, submonoid.coe_one, mul_one] at eq6,

    have mem4 : α * g * f ^ N * f ^ v ∈ x.1.as_homogeneous_ideal,
    { refine ideal.mul_mem_right _ _ (ideal.mul_mem_right _ _ (ideal.mul_mem_left _ _ mem3)) },
    erw ←eq6 at mem4,

    rcases x.1.is_prime.mem_or_mem mem4 with H1 | H3,
    rcases x.1.is_prime.mem_or_mem H1 with H1 | H2,
    exacts [H1, false.elim ((projective_spectrum.mem_basic_open 𝒜 _ _).mp x.2
      (x.1.is_prime.mem_of_pow_mem _ H2)), false.elim
      ((projective_spectrum.mem_basic_open 𝒜 _ _).mp x.2 (x.1.is_prime.mem_of_pow_mem _ H3))], },

  { change z ∈ ideal.span _ at hz, rw mem_carrier_iff,
    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz, erw [finsupp.total_apply, finsupp.sum] at eq1,
    erw [←eq1, homogeneous_localization.sum_val],
    convert submodule.sum_mem _ (λ j hj, _),
    rw [smul_eq_mul, mul_val],
    obtain ⟨s, _, hs, n, s_mem, F_mem1, ⟨l, rfl⟩, hj2⟩ := j.2,
    convert ideal.mul_mem_left _ _ _,
    rw [←subtype.val_eq_coe, hj2, val_mk'],
    erw show (mk s ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) = mk 1 ⟨f^l, ⟨_, rfl⟩⟩ * mk s 1,
    { rw [mk_mul, one_mul, mul_one], },
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span, exact ⟨s, hs, rfl⟩, },
end

end carrier'

lemma disjoint :
  (disjoint (x.1.as_homogeneous_ideal.to_ideal : set A) (submonoid.powers f : set A)) :=
begin
  by_contra rid,
  rw [set.not_disjoint_iff] at rid,
  choose g hg using rid,
  obtain ⟨hg1, ⟨k, rfl⟩⟩ := hg,
  by_cases k_ineq : 0 < k,
  { erw x.1.is_prime.pow_mem_iff_mem _ k_ineq at hg1,
    exact x.2 hg1 },
  { erw [show k = 0, by linarith, pow_zero, ←ideal.eq_top_iff_one] at hg1,
    apply x.1.is_prime.1,
    exact hg1 },
end

lemma carrier_ne_top :
  carrier 𝒜 x ≠ ⊤ :=
begin
  have eq_top := disjoint x,
  classical,
  contrapose! eq_top,
  obtain ⟨c, N, acd, eq1⟩ := mem_carrier.clear_denominator _ x ((ideal.eq_top_iff_one _).mp eq_top),
  rw [algebra.smul_def, homogeneous_localization.one_val, mul_one] at eq1,
  change localization.mk (f ^ N) 1 = mk (∑ _, _) 1 at eq1,
  simp only [mk_eq_mk', is_localization.eq] at eq1,
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
  erw [mul_one, mul_one] at eq1,
  change f^_ * f^_ = _ * f^_ at eq1,
  rw set.not_disjoint_iff_nonempty_inter,
  refine ⟨f^N * f^M, eq1.symm ▸ mul_mem_right _ _
    (sum_mem _ (λ i hi, mul_mem_left _ _ _)), ⟨N+M, by rw pow_add⟩⟩,
  generalize_proofs h₁ h₂,
  exact (classical.some_spec h₂).1,
end

variable (f)
/--The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `Top_component.forward`.
-/
def to_fun (x : Proj.T| (pbo f)) : (Spec.T (A⁰_ f)) :=
⟨carrier 𝒜 x, carrier_ne_top x, λ x1 x2 hx12, begin
  classical, simp only [mem_carrier_iff] at hx12 ⊢,
  let J := span (⇑(algebra_map A (away f)) '' x.val.as_homogeneous_ideal),
  suffices h : ∀ (x y : localization.away f), x * y ∈ J → x ∈ J ∨ y ∈ J,
  { rw [homogeneous_localization.mul_val] at hx12, exact h x1.val x2.val hx12, },
  clear' x1 x2 hx12, intros x1 x2 hx12,
  induction x1 using localization.induction_on with data_x1,
  induction x2 using localization.induction_on with data_x2,
  rcases ⟨data_x1, data_x2⟩ with ⟨⟨a1, _, ⟨n1, rfl⟩⟩, ⟨a2, _, ⟨n2, rfl⟩⟩⟩,
  rcases mem_carrier.clear_denominator' x hx12 with ⟨c, N, acd, eq1⟩,
  simp only [algebra.smul_def] at eq1,
  change localization.mk (f ^ N) 1 * (mk _ _ * mk _ _) = mk (∑ _, _) _ at eq1,
  simp only [localization.mk_mul, one_mul] at eq1,
  simp only [mk_eq_mk', is_localization.eq] at eq1,
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
  rw [submonoid.coe_one, mul_one] at eq1,
  change _ * _ * f^_ = _ * (f^_ * f^_) * f^_ at eq1,

  rcases x.1.is_prime.mem_or_mem (show a1 * a2 * f ^ N * f ^ M ∈ _, from _) with h1|rid2,
  rcases x.1.is_prime.mem_or_mem h1 with h1|rid1,
  rcases x.1.is_prime.mem_or_mem h1 with h1|h2,
  { left, simp only [show (mk a1 ⟨f ^ n1, _⟩ : away f) = mk a1 1 * mk 1 ⟨f^n1, ⟨_, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h1, rfl⟩), },
  { right, simp only [show (mk a2 ⟨f ^ n2, _⟩ : away f) = mk a2 1 * mk 1 ⟨f^n2, ⟨_, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h2, rfl⟩), },
  { exact false.elim (x.2 (x.1.is_prime.mem_of_pow_mem N rid1)), },
  { exact false.elim (x.2 (x.1.is_prime.mem_of_pow_mem M rid2)), },
  { rw [mul_comm _ (f^N), eq1],
    refine mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ (λ i hi, mul_mem_left _ _ _))),
    generalize_proofs h₁ h₂, exact (classical.some_spec h₂).1 },
end⟩

/-
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map from `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in  `Proj A`. This lemma is used to prove that the
forward map is continuous.
-/
lemma preimage_eq (a b : A) (k : ℕ) (a_mem : a ∈ 𝒜 k) (b_mem1 : b ∈ 𝒜 k)
  (b_mem2 : b ∈ submonoid.powers f) : to_fun 𝒜 f ⁻¹'
    ((@prime_spectrum.basic_open (A⁰_ f) _
      (quotient.mk' ⟨k, ⟨a, a_mem⟩, ⟨b, b_mem1⟩, b_mem2⟩)) :
        set (prime_spectrum (homogeneous_localization.away 𝒜 f)))
  = {x | x.1 ∈ (pbo f) ⊓ (pbo a)} :=
begin
  classical,
  ext1 y, split; intros hy,
  { refine ⟨y.2, _⟩,
    rw [set.mem_preimage, opens.mem_coe, prime_spectrum.mem_basic_open] at hy,
    rw projective_spectrum.mem_coe_basic_open,
    intro a_mem_y,
    apply hy,
    rw [to_fun, mem_carrier_iff, homogeneous_localization.val_mk', subtype.coe_mk],
    dsimp, rcases b_mem2 with ⟨k, hk⟩,
    simp only [show (mk a ⟨b, ⟨k, hk⟩⟩ : localization.away f) = mk 1 ⟨f^k, ⟨_, rfl⟩⟩ * mk a 1,
      by { rw [mk_mul, one_mul, mul_one], congr, rw hk }],
    exact ideal.mul_mem_left _ _ (ideal.subset_span ⟨_, a_mem_y, rfl⟩), },
  { change y.1 ∈ _ at hy,
    rcases hy with ⟨hy1, hy2⟩,
    rw projective_spectrum.mem_coe_basic_open at hy1 hy2,
    rw [set.mem_preimage, to_fun, opens.mem_coe, prime_spectrum.mem_basic_open],
    intro rid, dsimp at rid,
    rcases mem_carrier.clear_denominator 𝒜 _ rid with ⟨c, N, acd, eq1⟩,
    rw [algebra.smul_def] at eq1,
    change localization.mk (f^N) 1 * mk _ _ = mk (∑ _, _) _ at eq1,
    rw [mk_mul, one_mul, mk_eq_mk', is_localization.eq] at eq1,
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
    rw [submonoid.coe_one, mul_one] at eq1,
    simp only [subtype.coe_mk] at eq1,

    rcases y.1.is_prime.mem_or_mem (show a * f ^ N * f ^ M ∈ _, from _) with H1 | H3,
    rcases y.1.is_prime.mem_or_mem H1 with H1 | H2,
    { exact hy2 H1, },
    { exact y.2 (y.1.is_prime.mem_of_pow_mem N H2), },
    { exact y.2 (y.1.is_prime.mem_of_pow_mem M H3), },
    { rw [mul_comm _ (f^N), eq1],
      refine mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ (λ i hi, mul_mem_left _ _ _))),
      generalize_proofs h₁ h₂, exact (classical.some_spec h₂).1, }, },
end

end to_Spec

section

variable {𝒜}

/--The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic
open set in `Spec A⁰_f`.
-/
def to_Spec {f : A} : (Proj.T| (pbo f)) ⟶ (Spec.T (A⁰_ f)) :=
{ to_fun := to_Spec.to_fun 𝒜 f,
  continuous_to_fun := begin
    apply is_topological_basis.continuous (prime_spectrum.is_topological_basis_basic_opens),
    rintros _ ⟨⟨k, ⟨a, ha⟩, ⟨b, hb1⟩, ⟨k', hb2⟩⟩, rfl⟩, dsimp,
    erw to_Spec.preimage_eq f a b k ha hb1 ⟨k', hb2⟩,
    refine is_open_induced_iff.mpr ⟨(pbo f).1 ⊓ (pbo a).1, is_open.inter (pbo f).2 (pbo a).2, _⟩,
    ext z, split; intros hz; simpa [set.mem_preimage],
  end }

end

namespace from_Spec

open graded_algebra set_like finset (hiding mk_zero)
open _root_.homogeneous_localization (hiding away)

variables {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)

private meta def mem_tac : tactic unit :=
let b : tactic unit :=
  `[exact pow_mem_graded _ (submodule.coe_mem _) <|> exact nat_cast_mem_graded _ _ <|>
    exact pow_mem_graded _ f_deg] in
b <|> `[by repeat { all_goals { apply graded_monoid.mul_mem } }; b]

include f_deg
/--The function from `Spec A⁰_f` to `Proj|D(f)` is defined by `q ↦ {a | aᵢᵐ/fⁱ ∈ q}`, i.e. sending
`q` a prime ideal in `A⁰_f` to the homogeneous prime relevant ideal containing only and all the
elements `a : A` such that for every `i`, the degree 0 element formed by dividing the `m`-th power
of the `i`-th projection of `a` by the `i`-th power of the degree-`m` homogeneous element `f`,
lies in `q`.

The set `{a | aᵢᵐ/fⁱ ∈ q}`
* is an ideal, as proved in `carrier.as_ideal`;
* is homogeneous, as proved in `carrier.as_homogeneous_ideal`;
* is prime, as proved in `carrier.as_ideal.prime`;
* is relevant, as proved in `carrier.relevant`.
-/
def carrier (q : Spec.T (A⁰_ f)) : set A :=
{a | ∀ i, (quotient.mk' ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
  ⟨f^i, by rw mul_comm; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.1}

lemma mem_carrier_iff (q : Spec.T (A⁰_ f)) (a : A) :
  a ∈ carrier f_deg q ↔
  ∀ i, (quotient.mk' ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩, ⟨f^i, by rw mul_comm; mem_tac⟩, ⟨_, rfl⟩⟩
    : A⁰_ f) ∈ q.1 :=
iff.rfl

lemma mem_carrier_iff' (q : Spec.T (A⁰_ f)) (a : A) :
  a ∈ carrier f_deg q ↔
  ∀ i, (localization.mk (proj 𝒜 i a ^ m) ⟨f^i, ⟨i, rfl⟩⟩ : localization.away f) ∈
    (algebra_map (homogeneous_localization.away 𝒜 f) (localization.away f)) '' q.1.1 :=
(mem_carrier_iff f_deg q a).trans begin
  split; intros h i; specialize h i,
  { rw set.mem_image, refine ⟨_, h, rfl⟩, },
  { rw set.mem_image at h, rcases h with ⟨x, h, hx⟩,
    convert h, rw [ext_iff_val, val_mk'], dsimp only [subtype.coe_mk], rw ←hx, refl, },
end

lemma carrier.add_mem (q : Spec.T (A⁰_ f)) {a b : A} (ha : a ∈ carrier f_deg q)
  (hb : b ∈ carrier f_deg q) :
  a + b ∈ carrier f_deg q :=
begin
  refine λ i, (q.2.mem_or_mem _).elim id id,
  change (quotient.mk' ⟨_, _, _, _⟩ : A⁰_ f) ∈ q.1, dsimp only [subtype.coe_mk],
  simp_rw [←pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul],
  let g : ℕ → A⁰_ f := λ j, (m + m).choose j • if h2 : m + m < j then 0 else if h1 : j ≤ m
    then quotient.mk' ⟨m * i, ⟨proj 𝒜 i a^j * proj 𝒜 i b ^ (m - j), _⟩,
      ⟨_, by rw mul_comm; mem_tac⟩, ⟨i, rfl⟩⟩ *
      quotient.mk' ⟨m * i, ⟨proj 𝒜 i b ^ m, by mem_tac⟩, ⟨_, by rw mul_comm; mem_tac⟩, ⟨i, rfl⟩⟩
    else quotient.mk' ⟨m * i, ⟨proj 𝒜 i a ^ m, by mem_tac⟩,
      ⟨_, by rw mul_comm; mem_tac⟩, ⟨i, rfl⟩⟩ * quotient.mk' ⟨m * i, ⟨proj 𝒜 i a ^ (j - m) *
        proj 𝒜 i b ^ (m + m - j), _⟩, ⟨_, by rw mul_comm; mem_tac⟩, ⟨i, rfl⟩⟩,
  rotate,
  { rw (_ : m*i = _), mem_tac, rw [← add_smul, nat.add_sub_of_le h1], refl },
  { rw (_ : m*i = _), mem_tac, rw ←add_smul, congr, zify [le_of_not_lt h2, le_of_not_le h1], abel },
  convert_to ∑ i in range (m + m + 1), g i ∈ q.1, swap,
  { refine q.1.sum_mem (λ j hj, nsmul_mem _ _), split_ifs,
    exacts [q.1.zero_mem, q.1.mul_mem_left _ (hb i), q.1.mul_mem_right _ (ha i)] },
  rw [ext_iff_val, val_mk'],
  change _ = (algebra_map (homogeneous_localization.away 𝒜 f) (localization.away f)) _,
  dsimp only [subtype.coe_mk], rw [map_sum, mk_sum],
  apply finset.sum_congr rfl (λ j hj, _),
  change _ = homogeneous_localization.val _,
  rw [homogeneous_localization.smul_val],
  split_ifs with h2 h1,
  { exact ((finset.mem_range.1 hj).not_le h2).elim },
  all_goals { simp only [mul_val, zero_val, val_mk', subtype.coe_mk, mk_mul, ←smul_mk], congr' 2 },
  { rw [mul_assoc, ←pow_add, add_comm (m-j), nat.add_sub_assoc h1] }, { simp_rw [pow_add], refl },
  { rw [← mul_assoc, ←pow_add, nat.add_sub_of_le (le_of_not_le h1)] }, { simp_rw [pow_add], refl },
end

variables (hm : 0 < m) (q : Spec.T (A⁰_ f))
include hm

lemma carrier.zero_mem : (0 : A) ∈ carrier f_deg q := λ i, begin
  convert submodule.zero_mem q.1 using 1,
  rw [ext_iff_val, val_mk', zero_val], simp_rw [map_zero, zero_pow hm],
  convert localization.mk_zero _ using 1,
end

lemma carrier.smul_mem (c x : A) (hx : x ∈ carrier f_deg q) : c • x ∈ carrier f_deg q :=
begin
  revert c,
  refine direct_sum.decomposition.induction_on 𝒜 _ _ _,
  { rw zero_smul, exact carrier.zero_mem f_deg hm _ },
  { rintros n ⟨a, ha⟩ i,
    simp_rw [subtype.coe_mk, proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha],
    split_ifs,
    { convert_to (quotient.mk' ⟨_, ⟨a^m, pow_mem_graded m ha⟩, ⟨_, _⟩, ⟨n, rfl⟩⟩ * quotient.mk'
         ⟨_, ⟨proj 𝒜 (i - n) x ^ m, by mem_tac⟩, ⟨_, _⟩, ⟨i - n, rfl⟩⟩ : A⁰_ f) ∈ q.1,
      { erw [ext_iff_val, val_mk', mul_val, val_mk', val_mk', subtype.coe_mk],
        simp_rw [mul_pow, subtype.coe_mk], rw [localization.mk_mul],
        congr, erw [← pow_add, nat.add_sub_of_le h] },
      { exact ideal.mul_mem_left _ _ (hx _), rw [smul_eq_mul, mul_comm], mem_tac, } },
    { simp_rw [zero_pow hm], convert carrier.zero_mem f_deg hm q i, rw [map_zero, zero_pow hm] } },
  { simp_rw add_smul, exact λ _ _, carrier.add_mem f_deg q },
end

/--
For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as an ideal.
-/
def carrier.as_ideal : ideal A :=
{ carrier := carrier f_deg q,
  zero_mem' := carrier.zero_mem f_deg hm q,
  add_mem' := λ a b, carrier.add_mem f_deg q,
  smul_mem' := carrier.smul_mem f_deg hm q }

lemma carrier.as_ideal.homogeneous : (carrier.as_ideal f_deg hm q).is_homogeneous 𝒜 :=
λ i a ha j, (em (i = j)).elim
  (λ h, h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _)
  (λ h, begin
    simp only [proj_apply, decompose_of_mem_ne 𝒜 (submodule.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm], convert carrier.zero_mem f_deg hm q j, rw [map_zero, zero_pow hm],
  end)

/--
For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as a homogeneous ideal.
-/
def carrier.as_homogeneous_ideal : homogeneous_ideal 𝒜 :=
⟨carrier.as_ideal f_deg hm q, carrier.as_ideal.homogeneous f_deg hm q⟩

lemma carrier.denom_not_mem : f ∉ carrier.as_ideal f_deg hm q :=
λ rid, q.is_prime.ne_top $ (ideal.eq_top_iff_one _).mpr
begin
  convert rid m,
  simpa only [ext_iff_val, one_val, proj_apply, decompose_of_mem_same _ f_deg, val_mk'] using
    (mk_self (⟨_, m, rfl⟩ : submonoid.powers f)).symm,
end

lemma carrier.relevant :
  ¬homogeneous_ideal.irrelevant 𝒜 ≤ carrier.as_homogeneous_ideal f_deg hm q :=
λ rid, carrier.denom_not_mem f_deg hm q $ rid $ direct_sum.decompose_of_mem_ne 𝒜 f_deg hm.ne'

lemma carrier.as_ideal.ne_top : (carrier.as_ideal f_deg hm q) ≠ ⊤ :=
λ rid, carrier.denom_not_mem f_deg hm q (rid.symm ▸ submodule.mem_top)

lemma carrier.as_ideal.prime : (carrier.as_ideal f_deg hm q).is_prime :=
(carrier.as_ideal.homogeneous f_deg hm q).is_prime_of_homogeneous_mem_or_mem
  (carrier.as_ideal.ne_top f_deg hm q) $ λ x y ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy,
show (∀ i, _ ∈ _) ∨ ∀ i, _ ∈ _, begin
  rw [← and_forall_ne nx, and_iff_left, ← and_forall_ne ny, and_iff_left],
  { apply q.2.mem_or_mem, convert hxy (nx + ny) using 1,
    simp_rw [proj_apply, decompose_of_mem_same 𝒜 hnx, decompose_of_mem_same 𝒜 hny,
      decompose_of_mem_same 𝒜 (mul_mem hnx hny), mul_pow, pow_add],
    simpa only [ext_iff_val, val_mk', mul_val, mk_mul], },
  all_goals { intros n hn, convert q.1.zero_mem using 1,
    rw [ext_iff_val, val_mk', zero_val], simp_rw [proj_apply, subtype.coe_mk],
    convert mk_zero _, rw [decompose_of_mem_ne 𝒜 _ hn.symm, zero_pow hm],
    { exact hnx <|> exact hny } },
end

variable (f_deg)
/--
The function `Spec A⁰_f → Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
-/
def to_fun : (Spec.T (A⁰_ f)) → (Proj.T| (pbo f)) :=
λ q, ⟨⟨carrier.as_homogeneous_ideal f_deg hm q, carrier.as_ideal.prime f_deg hm q,
  carrier.relevant f_deg hm q⟩,
  (projective_spectrum.mem_basic_open _ f _).mp $ carrier.denom_not_mem f_deg hm q⟩

end from_Spec

section to_Spec_from_Spec

lemma to_Spec_from_Spec {f : A} {m : ℕ}
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (x : Spec.T (A⁰_ f)) :
  to_Spec.to_fun 𝒜 f (from_Spec.to_fun f_deg hm x) = x :=
begin
ext z, split,
{ intros hz,
  change z ∈ (to_Spec.to_fun _ f (⟨⟨⟨from_Spec.carrier.as_ideal f_deg hm x, _⟩, _, _⟩, _⟩)).1 at hz,
  unfold to_Spec.to_fun at hz,
  dsimp only at hz,
  erw to_Spec.carrier_eq_carrier' at hz,
  unfold to_Spec.carrier' at hz,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
  obtain ⟨c, eq1⟩ := hz,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  erw ←eq1,
  apply ideal.sum_mem,
  rintros ⟨j, j_mem⟩ hj,
  change ∃ _, _ at j_mem,

  obtain ⟨s, F, hs, n, s_mem, F_mem1, ⟨k, rfl⟩, rfl⟩ := j_mem,
  apply ideal.mul_mem_left,
  erw [←subtype.val_eq_coe],
  dsimp only,
  dsimp only at hs,
  change ∀ _, _ at hs,
  specialize hs n,
  simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 s_mem] at hs,
  have eq4 : ((quotient.mk' ⟨_, ⟨s, s_mem⟩, ⟨_, F_mem1⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ^ m : A⁰_ f) =
    (quotient.mk' ⟨_, ⟨s^m, set_like.pow_mem_graded _ s_mem⟩, ⟨f^n,
    begin
      rw [smul_eq_mul, mul_comm],
      refine set_like.pow_mem_graded _ f_deg,
    end⟩, ⟨_, rfl⟩⟩ : A⁰_ f),
  { change (quotient.mk' ⟨m * n, ⟨s ^ m, _⟩, _, _⟩ : A⁰_ f) = _, dsimp,
    rw homogeneous_localization.ext_iff_val,
    erw homogeneous_localization.val_mk',
    rw homogeneous_localization.val_mk',
    dsimp,
    -- if `f^k ≠ 0`, then `n = m * k` hence the equality holds
    -- if `f^k = 0`, then `A⁰_ f` is the zero ring, then they are equal as well.
    by_cases h : f^k = 0,
    { haveI : subsingleton (localization.away f),
      { refine is_localization.subsingleton_of_zero_mem (submonoid.powers f) _ ⟨k, h⟩, },
      exact subsingleton.elim _ _, },
    { have mem1 : (f ^ k) ∈ 𝒜 (k * m) := set_like.pow_mem_graded _ f_deg,
      simp_rw ←pow_mul,
      simp_rw decomposition.degree_uniq_of_nonzero 𝒜 (f^k) mem1 F_mem1 h,
      refl, } },
  erw ←eq4 at hs,
  exact ideal.is_prime.mem_of_pow_mem (x.is_prime) _ hs,
   },
  { intros hz,
    unfold to_Spec.to_fun,
    erw to_Spec.mem_carrier_iff,
    let k : ℕ := z.denom_mem.some,
    have eq1 : val z = localization.mk z.num ⟨f^k, ⟨k, rfl⟩⟩,
    { rw z.eq_num_div_denom, simp_rw z.denom_mem.some_spec, },
    rw eq1,
    have mem1 : z.num ∈ from_Spec.carrier f_deg x,
    { intros j,
      by_cases ineq1 : j = z.deg,
      { simp only [ineq1, graded_algebra.proj_apply],
        dsimp only,
        simp only [direct_sum.decompose_of_mem_same 𝒜 z.num_mem_deg],
        have mem2 := (ideal.is_prime.pow_mem_iff_mem x.is_prime m hm).mpr hz,
        convert mem2 using 1,
        rw [homogeneous_localization.ext_iff_val, homogeneous_localization.pow_val, eq1,
          homogeneous_localization.val_mk'],
        dsimp only [subtype.coe_mk],
        rw mk_pow,
        change localization.mk _ _ = mk _ ⟨(f^k)^m, _⟩,
        by_cases h : f^k = 0,
        { haveI : subsingleton (localization.away f),
          { refine is_localization.subsingleton_of_zero_mem (submonoid.powers f) _ ⟨k, h⟩, },
          exact subsingleton.elim _ _, },
        { have eq2 : f^k = z.denom := z.denom_mem.some_spec,
          have mem1 : z.denom ∈ _ := z.denom_mem_deg,
          rw ←eq2 at mem1,
          have mem2 : f^k ∈ _ := set_like.pow_mem_graded _ f_deg,
          simp_rw decomposition.degree_uniq_of_nonzero _ _ mem1 mem2 h,
          simp_rw [←pow_mul],
          refl, }, },
    {
      simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne 𝒜 z.num_mem_deg (ne.symm ineq1), zero_pow hm],
      convert submodule.zero_mem x.as_ideal using 1,
      rw homogeneous_localization.ext_iff_val,
      rw homogeneous_localization.val_mk',
      dsimp only [subtype.coe_mk],
      rw localization.mk_zero,
      rw homogeneous_localization.zero_val, }, },
    have eq3 : (mk z.num ⟨f^k, ⟨_, rfl⟩⟩ : away f) =
      mk 1 ⟨f^k, ⟨_, rfl⟩⟩ * mk z.num 1,
    { rw [mk_mul, one_mul, mul_one], },
    erw eq3,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨z.num, mem1, rfl⟩, },
end

end to_Spec_from_Spec

section from_Spec_to_Spec

lemma from_Spec_to_Spec {f : A} {m : ℕ}
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (x) :
  from_Spec.to_fun f_deg hm
    (to_Spec.to_fun 𝒜 f_deg x) = x :=
begin
  classical,
  ext z, split; intros hz,
  { change ∀ i, _ at hz,
    erw ←direct_sum.sum_support_decompose 𝒜 z,
    apply ideal.sum_mem,
    intros i hi,
    specialize hz i,
    erw to_Spec.mem_carrier_iff at hz,
    dsimp only at hz,
    rw ←graded_algebra.proj_apply,
    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz,
    erw [finsupp.total_apply, finsupp.sum] at eq1,
    dsimp only [subtype.coe_mk] at eq1,
    obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i.1) c.support),
    -- N is the common denom
    choose after_clear_denominator hacd using hN,
    have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
    have eq2 := calc (localization.mk (f^(i + N)) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
                  = (localization.mk (f^(i + N)) 1) * ∑ i in c.support, c i • i.1 : by erw eq1
              ... = (localization.mk (f^(i + N)) 1) * ∑ i in c.support.attach, c i.1 • i.1.1
                  : begin
                    congr' 1,
                    symmetry,
                    convert finset.sum_attach,
                    refl,
                  end
              ... = localization.mk (f^i) 1 * ((localization.mk (f^N) 1) * ∑ i in c.support.attach, c i.1 • i.1.1)
                  : begin
                    rw [←mul_assoc, localization.mk_mul, mul_one, pow_add],
                  end
              ... = localization.mk (f^i) 1 * (localization.mk (f^N) 1 * ∑ i in c.support.attach, c i.1 * i.1.1) : rfl
              ... = localization.mk (f^i) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
                  : by rw finset.mul_sum
              ... = localization.mk (f^i) 1 * ∑ i in c.support.attach, localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    congr' 1,
                    rw finset.sum_congr rfl (λ j hj, _),
                    have := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
                    dsimp only at this,
                      erw [this, mul_comm],
                    end
              ... = localization.mk (f^i) 1 * localization.mk (∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    congr' 1,
                    induction c.support.attach using finset.induction_on with a s ha ih,
                    { rw [finset.sum_empty, finset.sum_empty, localization.mk_zero], },
                    { erw [finset.sum_insert ha, finset.sum_insert ha, ih, localization.add_mk, mul_one, one_mul, one_mul, add_comm], },
                  end
              ... = localization.mk (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    rw [localization.mk_mul, one_mul],
                  end,
    have eq3 := calc
                (localization.mk (f^(i + N)) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
              = (localization.mk (f^N) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) 1)
              : begin
                rw [localization.mk_mul, localization.mk_mul, one_mul, one_mul, localization.mk_eq_mk', is_localization.eq],
                refine ⟨1, _⟩,
                erw [mul_one, mul_one, mul_one, pow_add, ←subtype.val_eq_coe],
                dsimp only,
                ring,
              end
          ... = (localization.mk (f^N * (graded_algebra.proj 𝒜 i z)^m) 1)
              : begin
                rw [localization.mk_mul, one_mul],
              end,
    have eq4 : ∃ (C : submonoid.powers f),
      (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) * C.1 =
      (f^N * (graded_algebra.proj 𝒜 i z)^m) * C.1,
    { rw [eq2] at eq3,
      simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
      obtain ⟨C, hC⟩ := eq3,
      erw [mul_one, mul_one] at hC,
      refine ⟨C, hC⟩, },
    obtain ⟨C, hC⟩ := eq4,
    have mem1 :
      (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) * C.1 ∈ x.1.as_homogeneous_ideal,
    { apply ideal.mul_mem_right,
      apply ideal.mul_mem_left,
      apply ideal.sum_mem,
      rintros ⟨j, hj⟩ _,
      have eq5 := (hacd (c j * j.1) (prop1 j hj)).2,
      dsimp only at eq5 ⊢,
      have mem2 := j.2,
      change ∃ g, _ at mem2,
      obtain ⟨g, hg1, hg2⟩ := mem2,
      have eq6 : ∃ (k : ℕ) (z : A), c j = localization.mk z ⟨f^k, ⟨_, rfl⟩⟩,
      { induction (c j) using localization.induction_on with data,
        obtain ⟨z, ⟨_, k, rfl⟩⟩ := data,
        refine ⟨_, _, rfl⟩,},
      obtain ⟨k, z, eq6⟩ := eq6,
      change localization.mk g 1 = _ at hg2,
      have eq7 := calc localization.mk (after_clear_denominator (c j * j.1) (prop1 j hj)) 1
                = c j * j.1 * localization.mk (f^N) 1 : eq5
            ... = (localization.mk z ⟨f^k, ⟨_, rfl⟩⟩ : localization.away f) * j.1 * localization.mk (f^N) 1 : by rw eq6
            ... = (localization.mk z ⟨f^k, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1 : by rw hg2
            ... = localization.mk (z*g*f^N) ⟨f^k, ⟨_, rfl⟩⟩
                : begin
                  rw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
                end,
      simp only [localization.mk_eq_mk', is_localization.eq] at eq7,
      obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq7⟩ := eq7,
      erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq7,
      dsimp only at eq7,
      have mem3 : z * g * f ^ N * f ^ l ∈ x.1.as_homogeneous_ideal,
      { apply ideal.mul_mem_right,
        apply ideal.mul_mem_right,
        apply ideal.mul_mem_left,
        exact hg1, },
      erw [←eq7, mul_assoc, ←pow_add] at mem3,
      rcases ideal.is_prime.mem_or_mem (x.1.is_prime) mem3 with H | RID,
      { exact H, },
      { exfalso,
        have mem4 := x.2,
        erw projective_spectrum.mem_basic_open at mem4,
        apply mem4,
        replace RID := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID,
        exact RID,
        } },

    erw hC at mem1,
    rcases ideal.is_prime.mem_or_mem (x.1.is_prime) mem1 with S | RID2,
    rcases ideal.is_prime.mem_or_mem (x.1.is_prime) S with RID1 | H,
    { exfalso,
      replace RID1 := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID1,
      have mem2 := x.2,
      erw projective_spectrum.mem_basic_open at mem2,
      apply mem2,
      apply RID1, },
    { replace H := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ H,
      exact H, },
    { exfalso,
      rcases C with ⟨_, ⟨k, rfl⟩⟩,
      replace RID2 := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID2,
      have mem2 := x.2,
      erw projective_spectrum.mem_basic_open at mem2,
      apply mem2,
      exact RID2, }, },
  { erw from_Spec.mem_carrier_iff,
    intros i,
    dsimp only,
    have mem2 := x.1.as_homogeneous_ideal.2 i hz,
    rw ←graded_algebra.proj_apply at mem2,
    have eq1 : (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
          = localization.mk 1 ⟨f^i, ⟨_, rfl⟩⟩ * localization.mk ((graded_algebra.proj 𝒜 i z)^m) 1,
    { erw [localization.mk_mul, one_mul, mul_one] },
    erw [to_Spec.mem_carrier_iff],
    simp only [eq1],
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨(graded_algebra.proj 𝒜 i z)^m, _, rfl⟩,
    erw ideal.is_prime.pow_mem_iff_mem (x.1.is_prime),
    exact mem2,
    exact hm, },
end

lemma to_Spec.to_fun_inj {f : A} {m : ℕ}
  (hm : 0 < m) (f_deg : f ∈ 𝒜 m) : function.injective (to_Spec.to_fun 𝒜 f_deg) := λ x1 x2 hx12,
begin
  convert congr_arg (from_Spec.to_fun f_deg hm) hx12; symmetry;
  apply from_Spec_to_Spec,
end

lemma to_Spec.to_fun_surj {f : A} {m : ℕ}
  (hm : 0 < m) (f_deg : f ∈ 𝒜 m) : function.surjective (to_Spec.to_fun 𝒜 f_deg) :=
begin
  erw function.surjective_iff_has_right_inverse,
  refine ⟨from_Spec.to_fun f_deg hm, λ x, _⟩,
  rw to_Spec_from_Spec,
end

end from_Spec_to_Spec

section

variables {𝒜}

def from_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (Spec.T (A⁰_ f_deg)) ⟶ (Proj.T| (pbo f)) :=
{ to_fun := from_Spec.to_fun f_deg hm,
  continuous_to_fun := begin
    apply is_topological_basis.continuous,
    exact @is_topological_basis.inducing (Proj.T| (pbo f)) _ Proj _ (λ x, x.1) _ ⟨rfl⟩ (projective_spectrum.is_topological_basis_basic_opens 𝒜),

    intros s hs,
    erw set.mem_preimage at hs,
    obtain ⟨t, ht1, ht2⟩ := hs,
    rw set.mem_range at ht1,
    obtain ⟨a, rfl⟩ := ht1,
    dsimp only at ht2,
    have set_eq1 : s =
      {x | x.1 ∈ (pbo f) ⊓ (pbo a) },
    { ext x, split; intros hx,
      erw [←ht2, set.mem_preimage] at hx,
      refine ⟨x.2, hx⟩,

      rcases hx with ⟨hx1, hx2⟩,
      erw [←ht2, set.mem_preimage],
      exact hx2, },

    -- we want to use preimage = forward s,
    set set1 := to_Spec.to_fun 𝒜 f_deg '' s with set1_eq,
    have o1 : is_open set1,
    {
      suffices : is_open (to_Spec.to_fun 𝒜 f_deg '' {x | x.1 ∈ (pbo f).1 ⊓ (pbo a).1}),
      erw [set1_eq, set_eq1], exact this,

      have set_eq2 := calc to_Spec.to_fun 𝒜 f_deg ''
            {x | x.1 ∈ (pbo f) ⊓ (pbo a)}
          = to_Spec.to_fun 𝒜 f_deg ''
            {x | x.1 ∈ (pbo f) ⊓ (⨆ (i : ℕ), (pbo (graded_algebra.proj 𝒜 i a)))}
          : begin
            congr',
            ext x,
            erw projective_spectrum.basic_open_eq_union_of_projection 𝒜 a,
          end
      ... = to_Spec.to_fun 𝒜 f_deg ''
            {x | x.1 ∈
              (⨆ (i : ℕ), (pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)) : opens Proj.T)}
          : begin
            congr',
            ext x,
            split; intros hx,
            { rcases hx with ⟨hx1, hx2⟩,
              erw opens.mem_Sup at hx2 ⊢,
              obtain ⟨_, ⟨j, rfl⟩, hx2⟩ := hx2,
              refine ⟨(pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 j a)), ⟨j, rfl⟩, ⟨hx1, hx2⟩⟩, },
            { erw opens.mem_Sup at hx,
              obtain ⟨_, ⟨j, rfl⟩, ⟨hx1, hx2⟩⟩ := hx,
              refine ⟨hx1, _⟩,
              erw opens.mem_Sup,
              refine ⟨pbo (graded_algebra.proj 𝒜 j a), ⟨j, rfl⟩, hx2⟩, },
          end
      ... = to_Spec.to_fun 𝒜 f_deg '' ⋃ (i : ℕ), {x | x.1 ∈ ((pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)))}
          : begin
            congr',
            ext x,
            split; intros hx; dsimp only at hx ⊢,
            { change ∃ _, _ at hx,
              obtain ⟨s, hs1, hs2⟩ := hx,
              erw set.mem_image at hs1,
              obtain ⟨s, hs1, rfl⟩ := hs1,
              erw set.mem_range at hs1,
              obtain ⟨i, rfl⟩ := hs1,
              change ∃ _, _,
              refine ⟨_, ⟨i, rfl⟩, _⟩,
              exact hs2, },
            { change ∃ _, _ at hx,
              obtain ⟨_, ⟨j, rfl⟩, hx⟩ := hx,
              change x.val ∈ _ at hx,
              simp only [opens.mem_supr],
              refine ⟨j, hx⟩, },
          end
      ... = ⋃ (i : ℕ), to_Spec.to_fun 𝒜 f_deg ''
              {x | x.1 ∈ ((pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)))}
          : begin
            erw set.image_Union,
          end,


    erw set_eq2,
    apply is_open_Union,
    intros i,
    suffices : to_Spec.to_fun 𝒜 f_deg '' {x | x.1 ∈ ((pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)))}
        = (sbo (⟨mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
            ⟨i, ⟨(graded_algebra.proj 𝒜 i a)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg)).1,
    { erw this,
      exact (prime_spectrum.basic_open _).2 },

    suffices : to_Spec.to_fun 𝒜 f_deg ⁻¹' (sbo (⟨mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
            ⟨i, ⟨(graded_algebra.proj 𝒜 i a)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg)).1 =
      {x | x.1 ∈ (pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a))},
    { erw ←this,
      apply function.surjective.image_preimage,
      exact to_Spec.to_fun_surj 𝒜 hm f_deg, },

    { erw to_Spec.preimage_eq f_deg ((graded_algebra.proj 𝒜 i a)^m) i,
      erw projective_spectrum.basic_open_pow,
      exact hm } },

    suffices : set1 = from_Spec.to_fun f_deg hm ⁻¹' _,
    erw ←this,
    exact o1,

    { erw set1_eq,
      ext z, split; intros hz,
      { erw set.mem_preimage,
        erw set.mem_image at hz,
        obtain ⟨α, α_mem, rfl⟩ := hz,
        erw from_Spec_to_Spec,
        exact α_mem, },
      { erw set.mem_preimage at hz,
        erw set.mem_image,
        refine ⟨from_Spec.to_fun f_deg hm z, hz, _⟩,
        erw to_Spec_from_Spec, }, },
  end }

end

end Proj_iso_Spec_Top_component

section

variables {𝒜}
def Proj_iso_Spec_Top_component {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (Proj.T| (pbo f)) ≅ (Spec.T (A⁰_ f_deg)) :=
{ hom := Proj_iso_Spec_Top_component.to_Spec m f_deg,
  inv := Proj_iso_Spec_Top_component.from_Spec hm f_deg,
  hom_inv_id' := begin
    ext1 x,
    simp only [id_app, comp_app],
    apply Proj_iso_Spec_Top_component.from_Spec_to_Spec,
  end,
  inv_hom_id' := begin
    ext1 x,
    simp only [id_app, comp_app],
    apply Proj_iso_Spec_Top_component.to_Spec_from_Spec,
  end }

end

end Proj_iso_Spec_Top_component

end algebraic_geometry
