/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.structure_sheaf
import algebraic_geometry.Spec
import ring_theory.graded_algebra.radical

/-!
# Proj as a scheme

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  erw [one_mul, one_mul] at eq1,
  change f^_ * f^_ = f^_ * _ at eq1,
  rw set.not_disjoint_iff_nonempty_inter,
  refine ⟨f^M * f^N, eq1.symm ▸ mul_mem_left _ _
    (sum_mem _ (λ i hi, mul_mem_left _ _ _)), ⟨M + N, by rw pow_add⟩⟩,
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
  rw [submonoid.coe_one, one_mul] at eq1,
  change f^_ * (_ * _) = f^_ * (f^_ * f^_ * _) at eq1,
  rcases x.1.is_prime.mem_or_mem (show a1 * a2 * f ^ N * f ^ M ∈ _, from _) with h1|rid2,
  rcases x.1.is_prime.mem_or_mem h1 with h1|rid1,
  rcases x.1.is_prime.mem_or_mem h1 with h1|h2,
  { left, simp only [show (mk a1 ⟨f ^ n1, _⟩ : away f) = mk a1 1 * mk 1 ⟨f^n1, ⟨n1, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h1, rfl⟩), },
  { right, simp only [show (mk a2 ⟨f ^ n2, _⟩ : away f) = mk a2 1 * mk 1 ⟨f^n2, ⟨n2, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h2, rfl⟩), },
  { exact false.elim (x.2 (x.1.is_prime.mem_of_pow_mem N rid1)), },
  { exact false.elim (x.2 (x.1.is_prime.mem_of_pow_mem M rid2)), },
  { rw [←mul_comm (f^M), ←mul_comm (f^N), eq1],
    refine mul_mem_left _ _ (mul_mem_left _ _ (sum_mem _ (λ i hi, mul_mem_left _ _ _))),
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
    rw [set.mem_preimage, set_like.mem_coe, prime_spectrum.mem_basic_open] at hy,
    rw projective_spectrum.mem_coe_basic_open,
    intro a_mem_y,
    apply hy,
    rw [to_fun, mem_carrier_iff, homogeneous_localization.val_mk', subtype.coe_mk],
    dsimp, rcases b_mem2 with ⟨k, hk⟩,
    simp only [show (mk a ⟨b, ⟨k, hk⟩⟩ : away f) = mk 1 ⟨f^k, ⟨_, rfl⟩⟩ * mk a 1,
      by { rw [mk_mul, one_mul, mul_one], congr, rw hk }],
    exact ideal.mul_mem_left _ _ (ideal.subset_span ⟨_, a_mem_y, rfl⟩), },
  { change y.1 ∈ _ at hy,
    rcases hy with ⟨hy1, hy2⟩,
    rw projective_spectrum.mem_coe_basic_open at hy1 hy2,
    rw [set.mem_preimage, to_fun, set_like.mem_coe, prime_spectrum.mem_basic_open],
    intro rid, dsimp at rid,
    rcases mem_carrier.clear_denominator 𝒜 _ rid with ⟨c, N, acd, eq1⟩,
    rw [algebra.smul_def] at eq1,
    change localization.mk (f^N) 1 * mk _ _ = mk (∑ _, _) _ at eq1,
    rw [mk_mul, one_mul, mk_eq_mk', is_localization.eq] at eq1,
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
    rw [submonoid.coe_one, one_mul] at eq1,
    simp only [subtype.coe_mk] at eq1,

    rcases y.1.is_prime.mem_or_mem (show a * f ^ N * f ^ M ∈ _, from _) with H1 | H3,
    rcases y.1.is_prime.mem_or_mem H1 with H1 | H2,
    { exact hy2 H1, },
    { exact y.2 (y.1.is_prime.mem_of_pow_mem N H2), },
    { exact y.2 (y.1.is_prime.mem_of_pow_mem M H3), },
    { rw [mul_comm _ (f^N), mul_comm _ (f^M), eq1],
      refine mul_mem_left _ _ (mul_mem_left _ _ (sum_mem _ (λ i hi, mul_mem_left _ _ _))),
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
open _root_.homogeneous_localization

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

end Proj_iso_Spec_Top_component

end algebraic_geometry
