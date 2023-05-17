/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.structure_sheaf
import algebraic_geometry.Scheme
import ring_theory.graded_algebra.radical
import ring_theory.localization.cardinality
import algebra.category.Ring.limits

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
    `Proj_iso_Spec_Top_component.from_Spec.to_fun`. By using that `from_Spec ∘ to_Spec` and
    `to_Spec ∘ from_Spec` are both identities, one can check continuity of `from_Spec` on basic open
    sets, this can found in `Proj_iso_Spec_Top_component.from_Spec`.
3. from 1 and 2, we have constructed a homoemorphism `Proj_iso_Spec_Top_component` between
  `Proj | D(f)` and `Spec A⁰_f`. Let's denote `Spec A⁰_f ⟶ Proj | D(f)` by `φ` and the other
  direction `Proj | D(f) ⟶ Spec A⁰_f` by `ψ`.

Then, we need to construct an isomorphism between sheaves `ψ _* (Proj | D(f)) ≅ Spec A⁰_f`.
4. For the backward direction: let `V` be an open set of `Spec A⁰_f`, we defines a ring homomorphism
  `Ψ : (Spec A⁰_f)(V) ⟶ (φ_* (Proj | D(f)))(V)` by:
  `h ↦ y ↦ (n_a * f^i_b) / (n_b * f^i_a)` where `a/b = hh(φ(y))`, `n_a` is the numerator of `a`,
  `n_b` is the numerator of `b`, `i_a` is the degree of `a` and `i_b` is the degree of `b`. Note
  that both `n_a * f^i_b` and `n_b * f^i_a` are both in `𝒜 (i_a + i_b)`, so
  `(n_a * f^i_b) / (n_b * f^i_a)` is in `A⁰_ f`. Furthermore, this `V ↦ ring_hom` is natural,
  hence defining a morphism between sheaves.
5. For the forward direction: Let `U ⊆ Spec A⁰_f` be an open set, We a ring homomorphism
  `Φ : (ψ _* Proj | D(f))(U) ⟶ (Spec A⁰_f)(U)` defined by:
  ```
             (a * b ^ (m - 1)) / f^d
  h ↦ y ↦ -------------------------
                  b^m / f^d
  ```
  where `hh(φ(y)) = a / b`, `f ∈ 𝒜 m` and `a, b ∈ 𝒜 d`. This assignment `U ↦ ring_hom` is natural
  in `U`, thus defining a morphism between sheaves.
6. We can check that `Ψ ∘ Φ` and `Φ ∘ Ψ` are both identity, hence we have constructed an isomorphism
  between `ψ_* Proj|D(f) ≅ Spec A⁰_f`.
7. Finanlly, we note that for any `x ∈ Proj` i.e. a homogeneous prime ideal that is relevant, we can
  always find some `f ∈ 𝒜 m` with `0 < m` such that `f ∉ x` (or equivalently `x ∈ D(f)`). Such
  `D(f)`s and the isomorphism of sheaves above will provide an affine open cover for `Proj`, hence
  proving that `Proj` is a scheme.

## Main Definitions and Statements

For a homogeneous element `f` of degree `n`
* `Proj_iso_Spec_Top_component.to_Spec`: the continuous map from `Proj.T| D(f)` to `Spec.T A⁰_f`.
* `Proj_iso_Spec_Top_component.to_Spec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `to_Spec f` is `pbo f ∩ pbo a`.
* `Proj_iso_Spec_Top_component.from_Spec`: the continuous map from `Spec.T A⁰_f` to `Proj.T| D(f)`.
* `Proj_iso_Spec_Top_component.from_Spec_to_Spec`: `from_Spec ∘ to_Spec` is the identity function.
* `Proj_iso_Spec_Top_component.to_Spec_from_Spec`: `to_Spec ∘ from_Spec` is the identity function.

* `Proj_iso_Spec_Sheaf_component.to_Spec`: the morphism of sheaves from the pushforward sheaf
  `ψ_* Proj | D(f)` to  the structure sheaf of `Spec A⁰_f`.
* `Proj_iso_Spec_Sheaf_component.from_Spec`: the morphism of sheaves from the structure sheaf of
  `Spec A⁰_f` to the pushforward sheaf `ψ_* Proj | D(f)`.
* `Proj_iso_Spec_Sheaf_component.from_Spec_to_Spec`: `from_Spec ∘ to_Spec` is the identity.
* `Proj_iso_Spec_Sheaf_component.to_Spec_from_Spec`: `to_Spec ∘ from_Spec` is the identity.
* `Proj_iso_Spec_Sheaf_component.iso`: `Proj| D(f)` and `Spec A⁰_f` are isomorphic as locally ringed
  space.
* `Proj.to_Scheme`: `Proj` of a graded algebra as a scheme.

* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise big_operators
open direct_sum set_like set_like.graded_monoid graded_algebra
open homogeneous_localization localization finset (hiding mk_zero)

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
  { left, simp only [show (mk a1 ⟨f ^ n1, _⟩ : away f) = mk a1 1 * mk 1 ⟨f^n1, ⟨_, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h1, rfl⟩), },
  { right, simp only [show (mk a2 ⟨f ^ n2, _⟩ : away f) = mk a2 1 * mk 1 ⟨f^n2, ⟨_, rfl⟩⟩,
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
    simp only [show (mk a ⟨b, ⟨k, hk⟩⟩ : localization.away f) = mk 1 ⟨f^k, ⟨_, rfl⟩⟩ * mk a 1,
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
def to_Spec (f : A) : (Proj.T| (pbo f)) ⟶ (Spec.T (A⁰_ f)) :=
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
    change z ∈ (to_Spec.to_fun _ f ⟨⟨⟨from_Spec.carrier.as_ideal f_deg hm x, _⟩, _, _⟩, _⟩).1 at hz,
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

    obtain ⟨s, F, hs, n, s_mem, F_mem1, ⟨k, rfl⟩, rfl⟩ := j_mem,
    apply ideal.mul_mem_left,
    erw [←subtype.val_eq_coe],
    dsimp only,
    dsimp only at hs,
    specialize hs n,
    simp only [proj_apply, direct_sum.decompose_of_mem_same 𝒜 s_mem] at hs,
    have eq4 : ((quotient.mk' ⟨_, ⟨s, s_mem⟩, ⟨_, F_mem1⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ^ m : A⁰_ f) =
      (quotient.mk' ⟨_, ⟨s^m, pow_mem_graded _ s_mem⟩, ⟨f^n,
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
    exact ideal.is_prime.mem_of_pow_mem (x.is_prime) _ hs, },
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
        have mem2 := (x.is_prime.pow_mem_iff_mem m hm).mpr hz,
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
          simp_rw [decomposition.degree_uniq_of_nonzero _ _ mem1 mem2 h, ←pow_mul],
          refl, }, },
      { simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne 𝒜 z.num_mem_deg
          (ne.symm ineq1), zero_pow hm],
        convert submodule.zero_mem x.as_ideal using 1,
        rw homogeneous_localization.ext_iff_val,
        rw homogeneous_localization.val_mk',
        dsimp only [subtype.coe_mk],
        rw localization.mk_zero,
        rw homogeneous_localization.zero_val, }, },
    erw show (mk z.num ⟨f^k, ⟨_, rfl⟩⟩ : away f) =
      mk 1 ⟨f^k, ⟨_, rfl⟩⟩ * mk z.num 1,
    { rw [mk_mul, one_mul, mul_one], },
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨z.num, mem1, rfl⟩, },
end

end to_Spec_from_Spec

section from_Spec_to_Spec

lemma from_Spec_to_Spec.aux1 {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (x) :
  (from_Spec.to_fun f_deg hm (to_Spec.to_fun 𝒜 f x)).1.as_homogeneous_ideal ≤
  x.1.as_homogeneous_ideal :=
begin
  classical,
  intros z hz,
  change ∀ i, _ at hz,
  erw ←direct_sum.sum_support_decompose 𝒜 z,
  apply ideal.sum_mem,
  intros i hi,
  specialize hz i,
  erw to_Spec.mem_carrier_iff at hz,
  dsimp only at hz,
  rw ←graded_algebra.proj_apply,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
  obtain ⟨c, eq1⟩ := hz,
  erw [finsupp.total_apply, finsupp.sum, homogeneous_localization.val_mk'] at eq1,
  dsimp only [subtype.coe_mk] at eq1,
  obtain ⟨N, hN⟩ := localization.away.clear_denominator (finset.image (λ i, c i * i.1) c.support),
  -- N is the common denom
  choose acd hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  have eq2 := calc
          mk (f^(i + N)) 1 * (mk (proj 𝒜 i z ^ m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
        = mk (f^(i + N)) 1 * ∑ i in c.support, c i • i.1 : by { erw eq1, refl, }
    ... = mk (f^(i + N)) 1 * ∑ i in c.support.attach, c i.1 • i.1.1
        : by { congr' 1, convert finset.sum_attach.symm using 2 }
    ... = mk (f^i) 1 * (mk (f^N) 1 * ∑ i in c.support.attach, c i.1 • i.1.1)
        : by rw [←mul_assoc, localization.mk_mul, mul_one, pow_add]
    ... = mk (f^i) 1 * (mk (f^N) 1 * ∑ i in c.support.attach, c i.1 * i.1.1) : rfl
    ... = mk (f^i) 1 * ∑ i in c.support.attach, mk (f^N) 1 * (c i.1 * i.1.1)
        : by rw finset.mul_sum
    ... = mk (f^i) 1 *
          ∑ i in c.support.attach, mk (acd (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
        : begin
          refine congr_arg2 (*) rfl (finset.sum_congr rfl (λ j hj, _)),
          erw [show localization.mk _ _ = _, from (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
            mul_comm],
        end
    ... = mk (f^i) 1 * mk (∑ i in c.support.attach, acd (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
        : begin
          congr' 1,
          induction c.support.attach using finset.induction_on with a s ha ih,
          { rw [finset.sum_empty, finset.sum_empty, localization.mk_zero], },
          { erw [finset.sum_insert ha, finset.sum_insert ha, ih, localization.add_mk, mul_one,
              one_mul, one_mul, add_comm], },
        end
    ... = mk (f^i * ∑ i in c.support.attach, acd (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
        : by rw [localization.mk_mul, one_mul],

  have eq3 := calc
          mk (f^(i + N)) 1 * (mk (proj 𝒜 i z ^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
        = mk (f^N) 1 * mk (proj 𝒜 i z ^m) 1
        : begin
          rw [mk_mul, mk_mul, one_mul, one_mul, mk_eq_mk', is_localization.eq],
          refine ⟨1, _⟩,
          erw [mul_one, mul_one, mul_one, pow_add, subtype.coe_mk],
          ring,
        end
    ... = mk (f^N * proj 𝒜 i z ^ m) 1 : by rw [mk_mul, one_mul],
  obtain ⟨C, hC⟩ := show ∃ (C : submonoid.powers f),
    (f^i * ∑ i in c.support.attach, acd (c i.1 * i.1.1) (prop1 i.1 i.2)) * C.1 =
    (f^N * proj 𝒜 i z ^ m) * C.1,
  { rw [eq2] at eq3,
    simp only [mk_eq_mk', is_localization.eq] at eq3,
    obtain ⟨C, hC⟩ := eq3,
    erw [mul_one, mul_one] at hC,
    refine ⟨C, hC⟩, },

  have mem1 : (f^i * ∑ i in c.support.attach, acd (c i.1 * i.1.1) (prop1 i.1 i.2)) * C.1 ∈
    x.1.as_homogeneous_ideal,
  { refine ideal.mul_mem_right _ _ (ideal.mul_mem_left _ _ (ideal.sum_mem _ _)),
    rintros ⟨j, hj⟩ _,
    obtain ⟨g, hg1, (hg2 : localization.mk g 1 = _)⟩ := j.2,
    obtain ⟨k, z, eq6⟩ := show ∃ (k : ℕ) (z : A), c j = mk z ⟨f^k, ⟨_, rfl⟩⟩,
    { induction (c j) using localization.induction_on with data,
      obtain ⟨z, ⟨_, k, rfl⟩⟩ := data,
      refine ⟨_, _, rfl⟩ },
    have eq7 := calc (mk (acd (c j * j.1) (prop1 j hj)) 1 : localization.away f)
          = c j * j.1 * (localization.mk (f^N) 1 : localization.away f)
          : (hacd (c j * j.1) (prop1 j hj)).2
      ... = mk z ⟨f^k, ⟨_, rfl⟩⟩ * j.1 * mk (f^N) 1 : by rw eq6
      ... = mk z ⟨f^k, ⟨_, rfl⟩⟩ * mk g 1 * mk (f^N) 1 : by rw hg2
      ... = mk (z*g*f^N) ⟨f^k, ⟨_, rfl⟩⟩ : by rw [mk_mul, mk_mul, mul_one, mul_one],
    simp only [localization.mk_eq_mk', is_localization.eq] at eq7,
    obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq7⟩ := eq7,
    simp only [subtype.coe_mk, mul_one, submonoid.coe_one] at eq7,
    have mem3 : z * g * f ^ N * f ^ l ∈ x.1.as_homogeneous_ideal :=
      ideal.mul_mem_right _ _ (ideal.mul_mem_right _ _ (ideal.mul_mem_left _ _ hg1)),
    rw [←eq7, mul_assoc, ←pow_add] at mem3,
    exact (x.1.is_prime.mem_or_mem mem3).elim id
      (λ H, false.elim ((projective_spectrum.mem_basic_open 𝒜 _ _).mp x.2
        (x.1.is_prime.mem_of_pow_mem _ H))) },

  rw hC at mem1,
  rcases ideal.is_prime.mem_or_mem (x.1.is_prime) mem1 with S | RID2,
  rcases ideal.is_prime.mem_or_mem (x.1.is_prime) S with RID1 | H,
  { exact false.elim ((projective_spectrum.mem_basic_open 𝒜 _ _).mp x.2
      (x.1.is_prime.mem_of_pow_mem _ RID1)), },
  { exact ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ H, },
  { rcases C with ⟨_, ⟨k, rfl⟩⟩,
    exact false.elim ((projective_spectrum.mem_basic_open 𝒜 _ _).mp x.2
      (x.1.is_prime.mem_of_pow_mem _ RID2)), },
end

lemma from_Spec_to_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (x) :
  from_Spec.to_fun f_deg hm (to_Spec.to_fun 𝒜 f x) = x :=
begin
  classical,
  ext z, split; intros hz,
  { exact from_Spec_to_Spec.aux1 𝒜 hm f_deg x hz, },
  { erw from_Spec.mem_carrier_iff,
    intros i,
    dsimp only,
    have mem2 := x.1.as_homogeneous_ideal.2 i hz,
    rw ←proj_apply at mem2,
    have eq1 : (mk (proj 𝒜 i z ^ m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
          = mk 1 ⟨f^i, ⟨_, rfl⟩⟩ * mk (proj 𝒜 i z ^ m) 1,
    { rw [localization.mk_mul, one_mul, mul_one] },
    erw [to_Spec.mem_carrier_iff],
    simp only [eq1],
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    exact ⟨proj 𝒜 i z ^ m, (x.1.is_prime.pow_mem_iff_mem m hm).mpr mem2, rfl⟩, },
end

lemma to_Spec.to_fun_inj {f : A} {m : ℕ}
  (hm : 0 < m) (f_deg : f ∈ 𝒜 m) : function.injective (to_Spec.to_fun 𝒜 f) := λ x1 x2 hx12,
begin
  convert congr_arg (from_Spec.to_fun f_deg hm) hx12,
  all_goals { rw from_Spec_to_Spec },
end

lemma to_Spec.to_fun_surj {f : A} {m : ℕ}
  (hm : 0 < m) (f_deg : f ∈ 𝒜 m) : function.surjective (to_Spec.to_fun 𝒜 f) :=
begin
  erw function.surjective_iff_has_right_inverse,
  refine ⟨from_Spec.to_fun f_deg hm, λ x, _⟩,
  rw to_Spec_from_Spec,
end

end from_Spec_to_Spec

section

variables {𝒜}

/--
The continuous function from the prime spectrum of `A⁰_ f` to the projective
spectrum of `A` restricted to the basic open set at `f` by sending `q ⊆ A⁰_f` to
`{a | ∀ i, aᵢᵐ/fⁱ ∈ q}`
-/
def from_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (Spec.T (A⁰_ f)) ⟶ (Proj.T| (pbo f)) :=
{ to_fun := from_Spec.to_fun f_deg hm,
  continuous_to_fun := begin
    apply is_topological_basis.continuous,
    exact @is_topological_basis.inducing (Proj.T| (pbo f)) _ Proj _ (λ x, x.1) _
      ⟨rfl⟩ (projective_spectrum.is_topological_basis_basic_opens 𝒜),

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
    set set1 := to_Spec.to_fun 𝒜 f '' s with set1_eq,
    have o1 : is_open set1,
    { suffices : is_open (to_Spec.to_fun 𝒜 f '' {x | x.1 ∈ (pbo f).1 ⊓ (pbo a).1}),
      erw [set1_eq, set_eq1], exact this,

      have set_eq2 := calc
            to_Spec.to_fun 𝒜 f '' {x | x.1 ∈ (pbo f) ⊓ (pbo a)}
          = to_Spec.to_fun 𝒜 f ''
            {x | x.1 ∈ (pbo f) ⊓ (⨆ (i : ℕ), (pbo (graded_algebra.proj 𝒜 i a)))}
          : by erw projective_spectrum.basic_open_eq_union_of_projection 𝒜 a
      ... = to_Spec.to_fun 𝒜 f ''
            {x | x.1 ∈ (⨆ (i : ℕ), (pbo f) ⊓ (pbo (proj 𝒜 i a)) : opens Proj.T)}
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
      ... = to_Spec.to_fun 𝒜 f '' ⋃ (i : ℕ), {x | x.1 ∈ ((pbo f) ⊓ pbo (proj 𝒜 i a))}
          : begin
            congr',
            ext x,
            split; intros hx; dsimp only at hx ⊢,
            { obtain ⟨s, hs1, hs2⟩ := hx,
              erw set.mem_range at hs1,
              obtain ⟨s, rfl⟩ := hs1,
              rw set.mem_Union at hs2,
              obtain ⟨⟨i, rfl⟩, hs2⟩ := hs2,
              refine ⟨_, ⟨i, rfl⟩, hs2⟩, },
            { obtain ⟨_, ⟨j, rfl⟩, (hx : x.1 ∈ _)⟩ := hx,
              simp only [opens.mem_supr],
              refine ⟨j, hx⟩, },
          end
      ... = ⋃ (i : ℕ), to_Spec.to_fun 𝒜 f ''
              {x | x.1 ∈ ((pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)))}
          : by erw set.image_Union,

      erw set_eq2,
      refine is_open_Union (λ i, _),

      suffices : to_Spec.to_fun 𝒜 f '' {x | x.1 ∈ ((pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)))}
          = (sbo (quotient.mk' ⟨m * i, ⟨proj 𝒜 i a ^ m, pow_mem_graded _ (submodule.coe_mem _)⟩,
              ⟨f^i, by simpa only [nat.mul_comm m i] using pow_mem_graded _ f_deg⟩,
              ⟨i, rfl⟩⟩ : A⁰_ f)).1,
      { rw [this], exact (prime_spectrum.basic_open _).2, },

      suffices : to_Spec.to_fun 𝒜 f ⁻¹' (sbo _).1 =
        {x | x.1 ∈ (pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a))},
      { rw ←this, exact (to_Spec.to_fun_surj 𝒜 hm f_deg).image_preimage _, },
      { rwa [subtype.val_eq_coe, to_Spec.preimage_eq, projective_spectrum.basic_open_pow], } },

    suffices : set1 = from_Spec.to_fun f_deg hm ⁻¹' _,
    { rwa ←this },

    rw set1_eq,
    ext z, split; intros hz,
    { obtain ⟨α, α_mem, rfl⟩ := hz,
      rwa [set.mem_preimage, from_Spec_to_Spec], },
    { exact ⟨from_Spec.to_fun f_deg hm z, hz, to_Spec_from_Spec 𝒜 _ _ _⟩, },
  end }

end

end Proj_iso_Spec_Top_component

section

variables {𝒜}
/--
The topological space of projective spectrum of `A` restricted to basic open set
at `f` is homeomorphic to the topological space of prime spectrum of `A⁰_ f`.
-/
def Proj_iso_Spec_Top_component {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (Proj.T| (pbo f)) ≅ (Spec.T (A⁰_ f)) :=
{ hom := Proj_iso_Spec_Top_component.to_Spec 𝒜 f,
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

namespace Proj_iso_Spec_Sheaf_component

namespace from_Spec

open algebraic_geometry

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens (Spec (A⁰_ f)))ᵒᵖ)
variables (hh : (Spec (A⁰_ f)).presheaf.obj V)
variables (y : ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
  ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop)

lemma data_prop1 : y.1 ∈ (pbo f) :=
begin
  obtain ⟨⟨a, ha1⟩, -, ha2⟩ := y.2,
  rw ← ha2,
  exact ha1,
end

lemma data_prop2 :
  (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 hm f_deg V y⟩ ∈ unop V :=
begin
  obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := y.2,
  convert ha2,
  rw ← ha3,
  refl,
end

variable {V}

/--
Let `V` be an open set of `Spec A⁰_f` and `y ∈ (Proj A |_ D(f))(φ⁻¹(V))` and
`hh` be a section of `Spec A⁰_ f` at `V` where `φ` is the homeomorphism between
`Proj A |_ D(f)` and `Spec A⁰_ f`, this definition is `hh(φ(y))`.
-/
def data : structure_sheaf.localizations (A⁰_ f)
  ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩) :=
hh.1 ⟨_, data_prop2 _ _ _ _⟩

lemma data.one :
  data 𝒜 hm f_deg (1 : (Spec (A⁰_ f)).presheaf.obj V) = 1 := rfl

lemma data.zero :
  data 𝒜 hm f_deg (0 : (Spec (A⁰_ f)).presheaf.obj V) = 0 := rfl

lemma data.add_apply (x y : (Spec (A⁰_ f)).presheaf.obj V) (z):
  data 𝒜 hm f_deg (x + y) z = data 𝒜 hm f_deg x z + data 𝒜 hm f_deg y z := rfl

lemma data.mul_apply (x y : (Spec (A⁰_ f)).presheaf.obj V) (z):
  data 𝒜 hm f_deg (x * y) z = data 𝒜 hm f_deg x z * data 𝒜 hm f_deg y z := rfl

private lemma data.exist_rep
  (data : structure_sheaf.localizations (A⁰_ f)
    ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩)) :
  ∃ (a : A⁰_ f)
    (b : ((Proj_iso_Spec_Top_component hm f_deg).hom
      ⟨y.1, data_prop1 _ _ _ _⟩).as_ideal.prime_compl), data = mk a b :=
begin
  induction data using localization.induction_on with d,
  rcases d with ⟨a, b⟩,
  refine ⟨a, b, rfl⟩,
end

/--
the numerator of `hh(φ(y))`, see also the doc string for
`Proj_iso_Spec_Sheaf_component.from_Spec.data`
-/
def data.num : A⁰_ f :=
classical.some $ data.exist_rep _ hm f_deg y (data _ hm f_deg hh y)

/--
the denominator of `hh(φ(y))`, see also the doc string for
`Proj_iso_Spec_Sheaf_component.from_Spec.data`
-/
def data.denom : A⁰_ f :=
(classical.some $ classical.some_spec $ data.exist_rep _ hm f_deg y
  (data _ hm f_deg hh y)).1

lemma data.denom_not_mem :
  (data.denom _ hm f_deg hh y) ∉
  ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩).as_ideal :=
(classical.some $ classical.some_spec $ data.exist_rep _ hm f_deg y
  (data _ hm f_deg hh y)).2

lemma data.eq_num_div_denom :
  data _ hm f_deg hh y =
  mk (data.num _ hm f_deg hh y) ⟨data.denom _ hm f_deg hh y, data.denom_not_mem hm f_deg hh y⟩ :=
begin
  rw (data.exist_rep _ hm f_deg y (data _ hm f_deg hh y)).some_spec.some_spec,
  congr,
  rw subtype.ext_iff,
  refl,
end

/--
`n_a * f^i_b` where `a/b = hh(φ(y))`, `n_a` is the numerator of `a` and `i_b` is
the degree of `b`.

See also the doc string for
`Proj_iso_Spec_Sheaf_component.from_Spec.data`.
-/
def num : A :=
  (data.num _ hm f_deg hh y).num * (data.denom _ hm f_deg hh y).denom

lemma num.mem :
    (num hm f_deg hh y)
  ∈ 𝒜 ((data.num _ hm f_deg hh y).deg + (data.denom _ hm f_deg hh y).deg) :=
mul_mem (num_mem_deg _) (denom_mem_deg _)

/--
`n_b * f^i_a` where `a/b = hh(φ(y))`, `n_b` is the numerator of `b` and `i_a` is
the degree of `a`.

See also the doc string for
`Proj_iso_Spec_Sheaf_component.from_Spec.data`.
-/
def denom : A :=
  (data.denom _ hm f_deg hh y).num * (data.num _ hm f_deg hh y).denom

lemma denom.mem :
  (denom hm f_deg hh y) ∈
  𝒜 ((data.num _ hm f_deg hh y).deg + (data.denom _ hm f_deg hh y).deg) :=
by { rw add_comm, exact mul_mem (num_mem_deg _) (denom_mem_deg _) }

lemma denom_not_mem :
  denom hm f_deg hh y ∉ y.1.as_homogeneous_ideal := λ rid,
begin
  rcases y.1.is_prime.mem_or_mem rid with H1 | H2,
  { have mem1 := data.denom_not_mem hm f_deg hh y,
    have eq1 := (data.denom _ hm f_deg hh y).eq_num_div_denom,
    dsimp only at mem1,
    change _ ∉ _ at mem1,
    apply mem1,
    erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
    rw eq1,
    convert ideal.mul_mem_left _ _ _,
    work_on_goal 2
    { exact mk 1 ⟨(data.denom _ hm f_deg hh y).denom, homogeneous_localization.denom_mem _⟩ },
    work_on_goal 2
    { exact mk (data.denom _ hm f_deg hh y).num 1 },
    { rw [mk_mul, one_mul, mul_one], },
    { apply ideal.subset_span,
      exact ⟨_, H1, rfl⟩ }, },
  { let k : ℕ := (data.num _ hm f_deg hh y).denom_mem.some,
    have k_eq : f^k = _ := (data.num _ hm f_deg hh y).denom_mem.some_spec,
    rw ←k_eq at H2,
    replace H2 := y.1.is_prime.mem_of_pow_mem _ H2,
    obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := y.2,
    erw projective_spectrum.mem_basic_open at ha1,
    apply ha1,
    convert H2, }
end

variable (V)
/--
`(n_a * f^i_b) / (n_b * f^i_a)` where `a/b = hh(φ(y))`, `n_a` is the numerator
of `a`, `n_b` is the numerator of `b`, `i_a` is the degree of `a` and `i_b` is
the degree of `b`.
Note that both `n_a * f^i_b` and `n_b * f^i_a` are both in `𝒜 (i_a + i_b)`, so
`(n_a * f^i_b) / (n_b * f^i_a)` is in `A⁰_ y`.

See also the doc string for
`Proj_iso_Spec_Sheaf_component.from_Spec.data`.
-/
def bmk : homogeneous_localization.at_prime 𝒜 y.1.as_homogeneous_ideal.to_ideal :=
quotient.mk'
{ deg := (data.num _ hm f_deg hh y).deg + (data.denom _ hm f_deg hh y).deg,
  num := ⟨num hm f_deg hh y, num.mem hm f_deg hh y⟩,
  denom := ⟨denom hm f_deg hh y, denom.mem hm f_deg hh y⟩,
  denom_mem := denom_not_mem hm f_deg hh y }

lemma bmk_one :
  bmk hm f_deg V 1 = 1 :=
begin
  ext1 y,
  have y_mem : y.val ∈ (pbo f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := y.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = y.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.one_apply,
  unfold bmk,
  rw [ext_iff_val, val_mk', one_val],
  simp only [← subtype.val_eq_coe],
  unfold num denom,

  have eq1 := data.eq_num_div_denom hm f_deg 1 y,
  rw [data.one, pi.one_apply] at eq1,
  replace eq1 := eq1.symm,
  rw [show (1 : structure_sheaf.localizations (A⁰_ f)
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨y.val, y_mem⟩)) = localization.mk 1 1,
    by erw localization.mk_self 1, localization.mk_eq_mk'] at eq1,
  replace eq1 := (@@is_localization.eq _ _ _ _).mp eq1,
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1,
  simp only [mul_one, one_mul, submonoid.coe_one, subtype.coe_mk] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq],
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  rw [homogeneous_localization.eq_num_div_denom] at hC,
  dsimp only at hC,

  have eq_num := (data.num _ hm f_deg 1 y).eq_num_div_denom,
  have eq_denom := (data.denom _ hm f_deg 1 y).eq_num_div_denom,

  rw homogeneous_localization.ext_iff_val at eq1,
  simp only [homogeneous_localization.mul_val, C.eq_num_div_denom] at eq1,
  erw [eq_num, eq_denom, mk_mul, mk_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq, subtype.coe_mk, submonoid.coe_mul] at eq1,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, eq1⟩ := eq1,
  simp only [submonoid.coe_mul, subtype.coe_mk] at eq1,

  have C_not_mem : C.num ∉ y.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (mk C.num ⟨C.denom, C.denom_mem⟩ : localization.away f) =
      mk 1 ⟨C.denom, C.denom_mem⟩ * mk C.num 1,
    { rw [mk_mul, one_mul, mul_one], },
    erw eq1 at hC,
    exact hC (ideal.mul_mem_left _ _ (ideal.subset_span ⟨_, rid, rfl⟩)), },

  rw [show (1 : localization.at_prime y.1.as_homogeneous_ideal.to_ideal) = mk (1 : _) 1,
    by erw mk_self 1, mk_eq_mk', is_localization.eq],
  use C.num * (C.denom * f^n1),
  { intros rid,
    refine (y.1.is_prime.mem_or_mem rid).elim C_not_mem (λ H3, _),
    let l : ℕ := C.denom_mem.some,
    let l_eq : f^l = C.denom := C.denom_mem.some_spec,
    rw [←l_eq, ←pow_add] at H3,
    exact y_mem (y.1.is_prime.mem_of_pow_mem _ H3), },

  simp only [submonoid.coe_one, one_mul, mul_one],
  simp only [subtype.coe_mk],
  rw calc (data.num _ hm f_deg 1 y).num
        * (data.denom _ hm f_deg 1 y).denom
        * (C.num * (C.denom * f ^ n1))
      = (data.num _ hm f_deg 1 y).num * C.num
        * ((data.denom _ hm f_deg 1 y).denom * C.denom)
        * f^n1 : by ring_exp,
  rw [eq1],
  ring,
end

lemma bmk_zero :
  bmk hm f_deg V 0 = 0 :=
begin
  ext1 y,
  have y_mem : y.val ∈ (pbo f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := y.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = y.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.zero_apply,
  unfold bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', zero_val],
  simp only [← subtype.val_eq_coe],
  rw [show (0 : localization.at_prime y.1.as_homogeneous_ideal.to_ideal) = mk 0 1, by erw mk_zero],
  dsimp only,
  unfold num denom,

  have eq1 := data.eq_num_div_denom hm f_deg 0 y,
  rw [data.zero, pi.zero_apply] at eq1,
  replace eq1 := eq1.symm,
  erw [show (0 : structure_sheaf.localizations (A⁰_ f)
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨y.val, y_mem⟩)) = localization.mk 0 1,
    by erw localization.mk_zero, localization.mk_eq_mk', is_localization.eq] at eq1,

  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1,
  simp only [submonoid.coe_one, mul_one, one_mul, subtype.coe_mk] at eq1,
  simp only [zero_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq],
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  rw [homogeneous_localization.eq_num_div_denom] at hC,
  dsimp only at hC,

  have eq_num := (data.num _ hm f_deg 0 y).eq_num_div_denom,
  have eq_denom := (data.denom _ hm f_deg 0 y).eq_num_div_denom,

  rw homogeneous_localization.ext_iff_val at eq1,
  simp only [homogeneous_localization.mul_val, homogeneous_localization.zero_val] at eq1,
  rw [eq_num, show (0 : localization.away f) = mk 0 1, by rw mk_zero, C.eq_num_div_denom,
    mk_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, eq1⟩ := eq1,
  simp only [submonoid.coe_mul, ←pow_add, submonoid.coe_one, mul_one, zero_mul,
    subtype.coe_mk] at eq1,

  have C_not_mem : C.num ∉ y.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (mk C.num ⟨C.denom, C.denom_mem⟩ : localization.away f) =
      mk 1 ⟨C.denom, C.denom_mem⟩ * mk C.num 1,
    { rw [localization.mk_mul, one_mul, mul_one] },
    erw eq1 at hC,
    refine hC (ideal.mul_mem_left _ _ (ideal.subset_span ⟨C.num, rid, rfl⟩)), },

  refine ⟨⟨C.num * f^n1, λ rid, (y.1.is_prime.mem_or_mem rid).elim C_not_mem
    (λ H2, y_mem (y.1.is_prime.mem_of_pow_mem _ H2))⟩, _⟩,

  simp only [submonoid.coe_one, zero_mul, mul_one, subtype.coe_mk],

  rw calc (data.num _ hm f_deg 0 y).num
        * (data.denom _ hm f_deg 0 y).denom
        * (C.num * f ^ n1)
      = (data.num _ hm f_deg 0 y).num
        * C.num * f ^ n1
        * (data.denom _ hm f_deg 0 y).denom
      : by ring,
  rw [eq1, zero_mul],
end

lemma bmk_add (x y : (Spec (A⁰_ f)).presheaf.obj V) :
  bmk hm f_deg V (x + y) = bmk hm f_deg V x + bmk hm f_deg V y :=
begin
  ext1 z,
  have z_mem : z.val ∈ (projective_spectrum.basic_open 𝒜 f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := z.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = z.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.add_apply,
  unfold bmk,
  simp only [ext_iff_val, val_mk', add_val, subtype.coe_mk],
  unfold num denom,
  dsimp only,

  have add_eq := data.eq_num_div_denom hm f_deg (x + y) z,
  rw [data.add_apply, data.eq_num_div_denom, data.eq_num_div_denom, add_mk] at add_eq,
  simp only [mk_eq_mk'] at add_eq,
  erw is_localization.eq at add_eq,
  obtain ⟨⟨C, hC⟩, add_eq⟩ := add_eq,

  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  rw [C.eq_num_div_denom] at hC,
  simp only [submonoid.coe_mul, subtype.coe_mk] at add_eq,
  rw homogeneous_localization.ext_iff_val at add_eq,
  simp only [homogeneous_localization.add_val, homogeneous_localization.mul_val] at add_eq,

  have C_not_mem : C.num ∉ z.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (mk C.num ⟨C.denom, C.denom_mem⟩ : localization.away f) =
      mk 1 ⟨C.denom, C.denom_mem⟩ * mk C.num 1,
    { rw [localization.mk_mul, one_mul, mul_one] },
    erw eq1 at hC,
    exact hC (ideal.mul_mem_left _ _ (ideal.subset_span ⟨C.num, rid, rfl⟩)), },

  simp only [eq_num_div_denom, mk_mul, add_mk, submonoid.coe_mul] at add_eq,
  rw [mk_eq_mk', is_localization.eq] at add_eq,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, add_eq⟩ := add_eq,
  simp only [←subtype.val_eq_coe, submonoid.coe_mul] at add_eq,

  set a_xy : A := (data.num _ hm f_deg (x + y) z).num with a_xy_eq,
  set i_xy : ℕ := (data.num _ hm f_deg (x + y) z).denom_mem.some with i_xy_eq,
  have i_xy_eq' : _ = f^i_xy := (data.num _ hm f_deg (x + y) z).denom_mem.some_spec.symm,

  set b_xy : A := (data.denom _ hm f_deg (x + y) z).num with b_xy_eq,
  set j_xy : ℕ := (data.denom _ hm f_deg (x + y) z).denom_mem.some with j_xy_eq,
  have j_xy_eq' : _ = f^j_xy := (data.denom _ hm f_deg (x + y) z).denom_mem.some_spec.symm,

  set a_x : A := (data.num _ hm f_deg x z).num with a_x_eq,
  set i_x : ℕ := (data.num _ hm f_deg x z).denom_mem.some with i_x_eq,
  have i_x_eq' : _ = f^i_x := (data.num _ hm f_deg x z).denom_mem.some_spec.symm,

  set b_x : A := (data.denom _ hm f_deg x z).num with b_x_eq,
  set j_x : ℕ := (data.denom _ hm f_deg x z).denom_mem.some with j_x_eq,
  have j_x_eq' : _ = f^j_x := (data.denom _ hm f_deg x z).denom_mem.some_spec.symm,

  set a_y : A := (data.num _ hm f_deg y z).num with a_y_eq,
  set i_y : ℕ := (data.num _ hm f_deg y z).denom_mem.some with i_y_eq,
  have i_y_eq' : _ = f^i_y := (data.num _ hm f_deg y z).denom_mem.some_spec.symm,
  set b_y : A := (data.denom _ hm f_deg y z).num with b_y_eq,
  set j_y : ℕ := (data.denom _ hm f_deg y z).denom_mem.some with j_y_eq,
  set j_y_eq' : _ = f^j_y := (data.denom _ hm f_deg y z).denom_mem.some_spec.symm,

  set l := C.denom_mem.some with l_eq,
  set l_eq' : _ = f^l := C.denom_mem.some_spec.symm,

  rw [j_x_eq', i_y_eq', ←b_y_eq, ←a_x_eq, j_y_eq', i_x_eq', ←b_x_eq, ←a_y_eq, ←b_xy_eq,
      i_xy_eq', l_eq', ←a_xy_eq, j_xy_eq'] at add_eq,

  suffices : (mk (a_xy * f ^ j_xy) ⟨b_xy * f ^ i_xy, _⟩ : localization.at_prime _) =
    mk (a_x * f ^ j_x) ⟨b_x * f ^ i_x, _⟩ + mk (a_y * f ^ j_y) ⟨b_y * f ^ i_y, _⟩,
  { convert this using 1,
    { rw [←a_xy_eq, j_xy_eq'], simp_rw [←b_xy_eq],
      congr' 1, rw subtype.ext_iff_val, dsimp only, congr' 1, },
    { rw [←a_x_eq, j_x_eq', ←a_y_eq, j_y_eq'],
      simp_rw [←b_x_eq, ←b_y_eq],
      congr' 1,
      { congr' 1, rw subtype.ext_iff_val, dsimp only, congr' 1, },
      { congr' 1, rw subtype.ext_iff_val, dsimp only, congr' 1, }, }, },
  swap, { rw [←i_xy_eq', b_xy_eq], exact denom_not_mem hm f_deg (x + y) z, },
  swap, { rw [←i_x_eq', b_x_eq], exact denom_not_mem hm f_deg x z, },
  swap, { rw [←i_y_eq', b_y_eq], exact denom_not_mem hm f_deg y z },

  rw localization.add_mk,
  simp only [subtype.coe_mk,
    show ∀ (α β : z.1.as_homogeneous_ideal.to_ideal.prime_compl), α * β = ⟨α.1 * β.1, λ rid,
      (z.1.is_prime.mem_or_mem rid).elim α.2 β.2⟩,
    by { intros α β, simpa only [subtype.ext_iff] },
    show b_x * f ^ i_x * (a_y * f ^ j_y) = a_y * b_x * f ^ (i_x + j_y),
    by { rw pow_add, ring, },
    show b_y * f ^ i_y * (a_x * f ^ j_x) = a_x * b_y * f ^ (i_y + j_x),
    by { rw pow_add, ring },
    show b_x * f ^ i_x * (b_y * f ^ i_y) = b_x * b_y * f ^ (i_x + i_y),
    by { rw pow_add, ring }],
  rw [calc (f ^ j_x * f ^ i_y * (b_y * a_x) + f ^ j_y * f ^ i_x * (b_x * a_y)) * b_xy * C.num
          * (f ^ i_xy * (f ^ j_x * f ^ j_y) * f ^ l) * f ^ n1
        = ((f ^ j_x * f ^ i_y) * (b_y * a_x) + (f ^ j_y * f ^ i_x) * (b_x * a_y)) * b_xy * C.num
          * ((f ^ i_xy * (f ^ j_x * f ^ j_y) * f ^ l) * f ^ n1) : by ring
    ... = ((f ^ (j_x + i_y)) * (b_y * a_x) + (f ^ (j_y + i_x)) * (b_x * a_y)) * b_xy * C.num
          * f ^ ((((i_xy + (j_x + j_y))) + l) + n1) : by ring_exp,
      calc a_xy * (b_x * b_y) * C.num *
          (f ^ j_x * f ^ i_y * (f ^ j_y * f ^ i_x) * f ^ j_xy * f ^ l) * f ^ n1
        = a_xy * (b_x * b_y) * C.num *
          ((f ^ j_x * f ^ i_y * (f ^ j_y * f ^ i_x) * f ^ j_xy * f ^ l) * f ^ n1) : by ring
    ... = a_xy * (b_x * b_y) * C.num *
          f ^ (((((j_x + i_y) + (j_y + i_x)) + j_xy) + l) + n1) : by simp only [pow_add]] at add_eq,

  simp only [mk_eq_mk', is_localization.eq],
  refine ⟨⟨C.num * f ^ ((j_x + j_y) + l + n1), λ rid, (z.1.is_prime.mem_or_mem rid).elim C_not_mem
    (λ H2, z_mem (z.1.is_prime.mem_of_pow_mem _ H2))⟩, _⟩,
  simp only [←subtype.val_eq_coe],

  rw [calc (a_y * b_x * f ^ (i_x + j_y) + a_x * b_y * f ^ (i_y + j_x)) * (b_xy * f ^ i_xy)
          * (C.num * f ^ ((j_x + j_y) + l + n1))
        = (f ^ (i_y + j_x) * (b_y * a_x) +  f ^ (i_x + j_y) * (b_x * a_y)) * b_xy * C.num
          * (f ^ i_xy * f ^ ((j_x + j_y) + l + n1)) : by ring
    ... = (f ^ (i_y + j_x) * (b_y * a_x) +  f ^ (i_x + j_y) * (b_x * a_y)) * b_xy * C.num
          * (f ^ (i_xy + ((j_x + j_y) + l + n1))) : by simp only [pow_add]
    ... = (f ^ (j_x + i_y) * (b_y * a_x) +  f ^ (j_y + i_x) * (b_x * a_y)) * b_xy * C.num
          * (f ^ (i_xy + (j_x + j_y) + l + n1))
        : by ring_exp, add_eq],
  simp only [pow_add],
  ring,
end

lemma bmk_mul (x y : (Spec (A⁰_ f)).presheaf.obj V) :
  bmk hm f_deg V (x * y) = bmk hm f_deg V x * bmk hm f_deg V y :=
begin
  ext1 z,
  have z_mem : z.val ∈ (projective_spectrum.basic_open 𝒜 f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    obtain ⟨⟨a, ha1⟩, ha, (ha2 : a = z.1)⟩ := z.2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    exact ha1 rid, },

  rw pi.mul_apply,
  unfold bmk,
  simp only [ext_iff_val, val_mk', homogeneous_localization.mul_val, subtype.coe_mk],
  unfold num denom,

  have mul_eq := data.eq_num_div_denom hm f_deg (x * y) z,
  rw [data.mul_apply, data.eq_num_div_denom, data.eq_num_div_denom, mk_mul] at mul_eq,
  simp only [localization.mk_eq_mk'] at mul_eq,
  erw is_localization.eq at mul_eq,
  obtain ⟨⟨C, hC⟩, mul_eq⟩ := mul_eq,
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  simp only [subtype.coe_mk, C.eq_num_div_denom] at hC,
  rw homogeneous_localization.ext_iff_val at mul_eq,
  simp only [mul_val, submonoid.coe_mul, subtype.coe_mk, C.eq_num_div_denom] at mul_eq,


  have C_not_mem : C.num ∉ z.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (mk C.num ⟨C.denom, C.denom_mem⟩ : localization.away f) =
      mk 1 ⟨C.denom, C.denom_mem⟩ * mk C.num 1,
    { rw [localization.mk_mul, one_mul, mul_one] },
    erw eq1 at hC,
    exact hC (ideal.mul_mem_left _ _ (ideal.subset_span ⟨C.num, rid, rfl⟩)), },

  simp only [subtype.coe_mk, subring.coe_mul, coe_add, subtype.coe_mk, eq_num_div_denom,
    show ∀ (α β : (prime_spectrum.as_ideal (((Proj_iso_Spec_Top_component hm f_deg).hom)
      ⟨z.val, z_mem⟩)).prime_compl),
      (α * β).1 = α.1 * β.1, from λ _ _, rfl] at mul_eq,
  simp only [localization.mk_mul, localization.add_mk] at mul_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at mul_eq,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, mul_eq⟩ := mul_eq,
  simp only [←subtype.val_eq_coe, submonoid.coe_mul] at mul_eq,

  set a_xy : A := (data.num _ hm f_deg (x * y) z).num with a_xy_eq,
  set i_xy : ℕ := (data.num _ hm f_deg (x * y) z).denom_mem.some with i_xy_eq,
  have i_xy_eq' : _ = f^i_xy := (data.num _ hm f_deg (x * y) z).denom_mem.some_spec.symm,
  set b_xy : A := (data.denom _ hm f_deg (x * y) z).num with b_xy_eq,
  set j_xy : ℕ := (data.denom _ hm f_deg (x * y) z).denom_mem.some with j_xy_eq,
  have j_xy_eq' : _ = f^j_xy := (data.denom _ hm f_deg (x * y) z).denom_mem.some_spec.symm,

  set a_x : A := (data.num _ hm f_deg x z).num with a_x_eq,
  set i_x : ℕ := (data.num _ hm f_deg x z).denom_mem.some with i_x_eq,
  have i_x_eq' : _ = f ^ i_x := (data.num _ hm f_deg x z).denom_mem.some_spec.symm,
  set b_x : A := (data.denom _ hm f_deg x z).num with b_x_eq,
  set j_x : ℕ := (data.denom _ hm f_deg x z).denom_mem.some with j_x_eq,
  have j_x_eq' : _ = f ^ j_x := (data.denom _ hm f_deg x z).denom_mem.some_spec.symm,

  set a_y : A := (data.num _ hm f_deg y z).num with a_y_eq,
  set i_y : ℕ := (data.num _ hm f_deg y z).denom_mem.some with i_y_eq,
  have i_y_eq' : _ = f ^ i_y := (data.num _ hm f_deg y z).denom_mem.some_spec.symm,
  set b_y : A := (data.denom _ hm f_deg y z).num with b_y_eq,
  set j_y : ℕ := (data.denom _ hm f_deg y z).denom_mem.some with j_y_eq,
  set j_y_eq' : _ = f ^ j_y := (data.denom _ hm f_deg y z).denom_mem.some_spec.symm,

  set l : ℕ := C.denom_mem.some with l_eq,
  have l_eq' : _ = f^l := C.denom_mem.some_spec.symm,

  simp only [←a_xy_eq, ←b_xy_eq, ←a_x_eq, ←b_x_eq, ←a_y_eq, ←b_y_eq] at mul_eq ⊢,
  rw [i_xy_eq', j_x_eq', j_y_eq', l_eq', i_x_eq', i_y_eq', j_xy_eq'] at mul_eq,

  suffices : (mk (a_xy * f ^ j_xy) ⟨b_xy * f ^ i_xy, _⟩ : localization.at_prime _) =
    mk (a_x * f ^ j_x) ⟨b_x * f ^ i_x, _⟩ * mk (a_y * f ^ j_y) ⟨b_y * f ^ i_y, _⟩,
  { convert this using 1,
    { congr' 1, rw j_xy_eq', rw subtype.ext_iff_val, dsimp only, congr' 1, },
    { congr' 1,
      { rw j_x_eq', congr' 1, rw subtype.ext_iff_val, dsimp only, congr' 1 },
      { rw j_y_eq', congr' 1, rw subtype.ext_iff_val, dsimp only, congr' 1 }, }, },
  swap, { rw [←i_xy_eq', b_xy_eq], exact denom_not_mem hm f_deg (x * y) z, },
  swap, { rw [←i_x_eq', b_x_eq], exact denom_not_mem hm f_deg x z, },
  swap, { rw [←i_y_eq', b_y_eq], exact denom_not_mem hm f_deg y z, },
  rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
  refine ⟨⟨C.num * f^(l + n1), λ rid, (z.1.is_prime.mem_or_mem rid).elim C_not_mem (λ H2, z_mem
    (z.1.is_prime.mem_of_pow_mem _ H2))⟩, _⟩,
  simp only [subtype.coe_mk, submonoid.coe_mul],
  simp only [pow_add],
  ring_nf at mul_eq ⊢,
  rw mul_eq,
end

namespace is_locally_quotient

variable {V}
lemma mem_pbo : y.1 ∈ pbo f := (projective_spectrum.mem_basic_open _ _ _).mpr $ λ rid,
begin
  obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := y.2,
  erw ←ha2 at rid,
  exact ha1 rid,
end

lemma hom_apply_mem :
  (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, mem_pbo hm f_deg y⟩ ∈ unop V :=
begin
  obtain ⟨a, ha1, ha2⟩ := y.2,
  erw set.mem_preimage at ha1,
  change ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, _⟩) ∈ (unop V).1,
  convert ha1,
  rw subtype.ext_iff,
  exact ha2.symm,
end

/--
Let `V` be an open set of `Spec A⁰_f`, then `{x | x ∈ φ⁻¹(V)} ⊆ Proj A` is also
open. For type theoretical reason, one cannot simply use `set.preimage`.

`φ` is the homeomorphism `Proj A | D(f) ≅ Spec A⁰_f`
-/
def Uo (VV : opens (Spec.T (A⁰_ f))) :
  opens (projective_spectrum.Top 𝒜) :=
⟨{x | ∃ x' : homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg) ⁻¹' VV.1, x = x'.1.1},
  begin
    have O1 := (homeomorph.is_open_preimage (homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg))).2
      VV.2,
    rw is_open_induced_iff at O1,
    obtain ⟨s, Os, set_eq1⟩ := O1,
    have O2 : is_open (s ∩ (projective_spectrum.basic_open 𝒜 f).1),
    apply is_open.inter Os (projective_spectrum.basic_open 𝒜 f).2,
    convert O2,
    ext γ, split; intros hγ,
    { obtain ⟨x', rfl⟩ := hγ,
      have mem1 := x'.2,
      simp only [←set_eq1] at mem1,
      erw set.mem_preimage at mem1,
      refine ⟨mem1, _⟩,
      have mem2 := x'.2,
      rw set.mem_preimage at mem2,
      intro rid,
      have mem3 : (quotient.mk' ⟨m, ⟨f, f_deg⟩, ⟨f^1, by rwa [pow_one]⟩, ⟨1, rfl⟩⟩ : A⁰_ f) ∈
        ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).as_ideal,
      { erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
        change (mk f ⟨f^1, ⟨_, rfl⟩⟩ : localization.away f) ∈ ideal.span _,
        convert ideal.mul_mem_left _ _ _,
        work_on_goal 2 { exact mk 1 ⟨f^1, ⟨_, rfl⟩⟩ },
        work_on_goal 2 { exact mk f 1 },
        { rw [mk_mul, one_mul, mul_one], },
        { exact ideal.subset_span ⟨f, rid, rfl⟩, } },
      have mem4 : (1 : A⁰_ f) ∈ ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).as_ideal,
      { convert mem3,
        rw [ext_iff_val, homogeneous_localization.one_val, homogeneous_localization.val_mk'],
        dsimp only [subtype.coe_mk],
        simp_rw [pow_one],
        convert (localization.mk_self _).symm,
        refl, },
      exact ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).is_prime.1
        ((ideal.eq_top_iff_one _).mpr mem4), },

    { rcases hγ with ⟨hγ1, hγ2⟩,
      use ⟨γ, hγ2⟩,
      rw [←set_eq1, set.mem_preimage],
      convert hγ1, }
  end⟩

/--
If `V' ⊆ V ⊆ Spec A⁰_f`, then `{x | x ∈ φ⁻¹(V')} ⊆ φ⁻¹(V)`. For type theoretical
reason.

`φ` is the homeomorphism `Proj A | D(f) ≅ Spec A⁰_f`
-/
def subset2 (VV : opens (Spec.T (A⁰_ f)))
  (subset1 : VV ⟶ unop V) :
  Uo 𝒜 hm f_deg VV ⟶
  (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop) :=
hom_of_le $ λ γ γ_mem, begin
  replace subset3 := le_of_hom subset1,
  obtain ⟨⟨γ, γ_mem⟩, rfl⟩ := γ_mem,
  erw set.mem_preimage at γ_mem,
  refine ⟨γ, _, rfl⟩,
  erw set.mem_preimage,
  apply subset3,
  exact γ_mem
end

end is_locally_quotient

lemma is_locally_quotient :
  ∃ (U : opens _) (mem : y.val ∈ U)
    (subset1 : U ⟶
      (((@opens.open_embedding (projective_spectrum.Top 𝒜)
          (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop))
    (a b : A) (degree : ℕ) (a_hom : a ∈ 𝒜 degree) (b_hom : b ∈ 𝒜 degree),
    ∀ (x : U),
      ∃ (s_nin : b ∉ projective_spectrum.as_homogeneous_ideal x.val),
        (bmk hm f_deg V hh ⟨x.1, (subset1 x).2⟩).val = mk a ⟨b, s_nin⟩ :=
begin
  have y_mem : y.val ∈ projective_spectrum.basic_open 𝒜 f := is_locally_quotient.mem_pbo hm f_deg y,

  have hom_y_mem : (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, y_mem⟩ ∈ unop V,
  { convert is_locally_quotient.hom_apply_mem hm f_deg y, },
  have is_local := hh.2,
  rw structure_sheaf.is_locally_fraction_pred' at is_local,
  specialize is_local ⟨(Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, y_mem⟩, hom_y_mem⟩,
  obtain ⟨VV, hom_y_mem_VV, subset1, α, β, is_local⟩ := is_local,

  set U := is_locally_quotient.Uo 𝒜 hm f_deg VV with U_eq,

  have y_mem_U : y.1 ∈ U,
  { use ⟨y.1, y_mem⟩,
    rw set.mem_preimage,
    exact hom_y_mem_VV, },

  set α' : A := α.num with α'_eq,
  set l1 : ℕ := α.denom_mem.some with l1_eq,
  have l1_eq' : _ = f^l1 := α.denom_mem.some_spec.symm,
  have α_eq : α.val = mk α' ⟨f^l1, ⟨_, rfl⟩⟩,
  { rw [α.eq_num_div_denom], congr' 1, rw subtype.ext_iff_val, congr' 1, },

  set β' : A := β.num with β'_eq,
  set l2 : ℕ := β.denom_mem.some with l2_eq,
  have l2_eq' : _ = f^l2 := β.denom_mem.some_spec.symm,
  have β_eq : β.val = mk β' ⟨f^l2, ⟨_, rfl⟩⟩,
  { rw [β.eq_num_div_denom], congr' 1, rw subtype.ext_iff_val, congr' 1, },

  set subset2 : U ⟶ _ := is_locally_quotient.subset2 𝒜 hm f_deg VV subset1,
  refine ⟨U, y_mem_U, subset2, α' * f^l2, β' * f^l1, α.deg + β.deg,
    mul_mem α.num_mem_deg (by { rw [←l2_eq'], exact β.denom_mem_deg }),
    by {rw add_comm, exact mul_mem β.num_mem_deg (by {rw [←l1_eq'], exact α.denom_mem_deg})}, _⟩,

  rintros ⟨z, z_mem_U⟩,
  have z_mem_bo : z ∈ pbo f,
  { obtain ⟨⟨z, hz⟩, rfl⟩ := z_mem_U, exact z.2, },

  have hom_z_mem_VV : ((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z, z_mem_bo⟩ ∈ VV,
  { obtain ⟨γ, h1, h2⟩ := z_mem_U, exact γ.2, },

  specialize is_local ⟨((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z, z_mem_bo⟩), hom_z_mem_VV⟩,
  obtain ⟨not_mem1, eq1⟩ := is_local,

  have not_mem2 : β' * f ^ l1 ∉ z.as_homogeneous_ideal,
  { intro rid,
    rcases z.is_prime.mem_or_mem rid with H1 | H2,
    { apply not_mem1,
      have eq2 : (localization.mk β' ⟨f^l2, ⟨_, rfl⟩⟩ : localization.away f) =
        localization.mk 1 ⟨f^l2, ⟨_, rfl⟩⟩ * localization.mk β' 1,
      { rw [localization.mk_mul, one_mul, mul_one], },
      erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
      rw [β.eq_num_div_denom, ←β'_eq],
      suffices : (mk β' ⟨f^l2, ⟨l2, rfl⟩⟩ : localization.away f) ∈ _,
      { convert this, },
      rw [eq2],
      convert ideal.mul_mem_left _ _ _,
      apply ideal.subset_span,
      refine ⟨β', H1, rfl⟩, },
    { replace H2 := z.is_prime.mem_of_pow_mem _ H2,
      exact z_mem_bo H2, } },
  refine ⟨not_mem2, _⟩,
  have data_eq : data 𝒜 hm f_deg hh (subset2 ⟨z, z_mem_U⟩) =
    hh.val (subset1 ⟨((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z, z_mem_bo⟩, hom_z_mem_VV⟩),
  { congr', },
  rw ←data_eq at eq1,

  have z_mem2 : z ∈ (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop),
  { use z, refine ⟨_, rfl⟩, exact (le_of_hom subset1) hom_z_mem_VV,  },

  have data_eq2 : data 𝒜 hm f_deg hh (subset2 ⟨z, z_mem_U⟩) = data 𝒜 hm f_deg hh ⟨z, z_mem2⟩,
  { congr', },
  rw [data_eq2, data.eq_num_div_denom, localization.mk_eq_mk'] at eq1,
  erw is_localization.eq at eq1,

  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1,
  set L : ℕ := C.denom_mem.some with L_eq,
  set L_eq' : _ = f^L := C.denom_mem.some_spec.symm with L_eq',
  have C_eq : C.val = mk C.num ⟨f^L, ⟨_, rfl⟩⟩,
  { rw [C.eq_num_div_denom], congr' 1, rw subtype.ext_iff_val, congr' 1 },
  rw [homogeneous_localization.ext_iff_val] at eq1,
  simp only [mul_val, localization.mk_mul, subtype.coe_mk, β_eq, α_eq, C_eq] at eq1,
  simp only [homogeneous_localization.eq_num_div_denom] at eq1,
  simp only [localization.mk_mul, submonoid.coe_mul, subtype.coe_mk] at eq1,
  erw [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩ := eq1,
  simp only [subtype.coe_mk, submonoid.coe_mul, ←pow_add] at eq1,

  unfold bmk,
  rw [homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],
  unfold num denom,

  set p := (data.num _ hm f_deg hh ⟨z, z_mem2⟩).num with p_eq,
  set q := (data.denom _ hm f_deg hh ⟨z, z_mem2⟩).num with q_eq,
  set ii := (data.num _ hm f_deg hh ⟨z, z_mem2⟩).denom_mem.some with ii_eq,
  have ii_eq' : _ = f^ii := (data.num _ hm f_deg hh ⟨z, z_mem2⟩).denom_mem.some_spec.symm,
  set jj := (data.denom _ hm f_deg hh ⟨z, z_mem2⟩).denom_mem.some with jj_eq,
  have jj_eq' : _ = f^jj := (data.denom _ hm f_deg hh ⟨z, z_mem2⟩).denom_mem.some_spec.symm,
  simp only [←p_eq, ←q_eq] at eq1,
  rw [ii_eq', jj_eq', ←pow_add, ←pow_add, ←pow_add, ←pow_add] at eq1,

  simp only [localization.mk_eq_mk', is_localization.eq],

  have C_not_mem : C.num ∉ z.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (mk C.num ⟨f ^ L, ⟨_, rfl⟩⟩ : localization.away f) =
      mk 1 ⟨f^L, ⟨_, rfl⟩⟩ * mk C.num 1,
    { rw [localization.mk_mul, one_mul, mul_one] },
    apply hC,
    erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
    rw [C_eq, eq1],
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨C.num, rid, rfl⟩ },

  refine ⟨⟨C.num * f^(L+M), λ rid, (z.is_prime.mem_or_mem rid).elim C_not_mem $ λ H2, z_mem_bo $
    z.is_prime.mem_of_pow_mem _ H2⟩, _⟩,

  simp only [subtype.coe_mk, submonoid.coe_mul],

  suffices EQ : p * f^jj * (β' * f^l1) * (C.num * f^(L+M)) =
    α' * f^l2 * (q * f^ii) * (C.num * f^(L + M)),
  { convert EQ },
  rw calc p * f^jj * (β' * f^l1) * (C.num * f^(L+M))
        = p * f^jj * (β' * f^l1) * (C.num * (f^L * f^M)) : by simp only [pow_add]
    ... = p * β' * C.num * (f^l1 * f^jj * f^L) * f^M : by ring
    ... = p * β' * C.num * f^(l1 + jj + L) * f^M : by simp only [pow_add]
    ... = α' * q * C.num * f ^ (ii + l2 + L) * f ^ M : by rw eq1,
  ring_exp,
end

/--
Composing `bmk` and the fact that the resulting function is locally quotient.
-/
def to_fun.aux (hh : (Spec (A⁰_ f)).presheaf.obj V) :
  ((Proj_iso_Spec_Top_component hm f_deg).hom _*
    (Proj| (pbo f)).presheaf).obj V :=
⟨bmk hm f_deg V hh, λ y, begin
  rcases is_locally_quotient hm f_deg V hh y with ⟨VV, mem1, subset1, a, b,
    degree, a_mem, b_mem, l⟩,
  refine ⟨VV, mem1, subset1, degree, ⟨a, a_mem⟩, ⟨b, b_mem⟩, λ x, _⟩,
  rcases l x with ⟨s_nin, l⟩,
  refine ⟨s_nin, _⟩,
  dsimp only,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],
  erw ← l,
  rw ← homogeneous_localization.ext_iff_val,
  congr' 1
end⟩

/--
Let `V` be an open set of `Spec A⁰_f`, `to_fun` defines a ring homomorphism
`(Spec A⁰_f)(V) ⟶ (φ_* (Proj | D(f)))(V)` by:
`h ↦ y ↦ (n_a * f^i_b) / (n_b * f^i_a)` where `a/b = hh(φ(y))`, `n_a` is the
numerator of `a`, `n_b` is the numerator of `b`, `i_a` is the degree of `a` and
`i_b` is the degree of `b`.
Note that both `n_a * f^i_b` and `n_b * f^i_a` are both in `𝒜 (i_a + i_b)`, so
`(n_a * f^i_b) / (n_b * f^i_a)` is in `A⁰_ y`.

See also the doc string for
`Proj_iso_Spec_Sheaf_component.from_Spec.data`.
-/
def to_fun :
  (Spec (A⁰_ f)).presheaf.obj V ⟶
  ((Proj_iso_Spec_Top_component hm f_deg).hom _*
    (Proj| (pbo f)).presheaf).obj V :=
{ to_fun := λ hh, to_fun.aux 𝒜 hm f_deg V hh,
  map_one' := begin
    rw subtype.ext_iff,
    convert bmk_one hm f_deg V,
  end,
  map_mul' := λ x y, begin
    rw subtype.ext_iff,
    convert bmk_mul 𝒜 hm f_deg V x y,
  end,
  map_zero' := begin
    rw subtype.ext_iff,
    convert bmk_zero hm f_deg V,
  end,
  map_add' := λ x y, begin
    rw subtype.ext_iff,
    convert bmk_add 𝒜 hm f_deg V x y,
  end }

end from_Spec

/--
Let `V` be an open set of `Spec A⁰_f`, `to_fun` defines a ring homomorphism
`(Spec A⁰_f)(V) ⟶ (φ_* (Proj | D(f)))(V)` by:
`h ↦ y ↦ (n_a * f^i_b) / (n_b * f^i_a)` where `a/b = hh(φ(y))`, `n_a` is the
numerator of `a`, `n_b` is the numerator of `b`, `i_a` is the degree of `a` and
`i_b` is the degree of `b`.
Note that both `n_a * f^i_b` and `n_b * f^i_a` are both in `𝒜 (i_a + i_b)`, so
`(n_a * f^i_b) / (n_b * f^i_a)` is in `A⁰_ y`.

This is natural, thus defining a morphism between sheaves.

See also the doc string for
`Proj_iso_Spec_Sheaf_component.from_Spec.data`.

-/
def from_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (Spec (A⁰_ f)).presheaf ⟶
  (Proj_iso_Spec_Top_component hm f_deg).hom _*
    (Proj| (pbo f)).presheaf :=
{ app := λ V, from_Spec.to_fun 𝒜 hm f_deg V,
  naturality' := λ U V subset1,
  begin
    ext1 z,
    simpa only [comp_apply, ring_hom.coe_mk, functor.op_map, presheaf.pushforward_obj_map],
  end }

namespace to_Spec

variables {𝒜} {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
variable (U : (opens (Spec.T (A⁰_ f)))ᵒᵖ)

-- pushforward a sheaf
local notation `pf_sheaf` x :=
  (Proj_iso_Spec_Top_component hm f_deg).hom _* x.presheaf

-- `hh` is a section, i.e `hh ∈ (ψ _* (Proj | D(f)))(U)` where
-- `ψ : Proj | D(f) ≅ Spec A⁰_f `
variable (hh : (pf_sheaf (Proj| (pbo f))).obj U)

lemma pf_sheaf.one_val :
  (1 : (pf_sheaf (Proj| (pbo f))).obj U).1 = 1 := rfl

lemma pf_sheaf.zero_val :
  (0 : (pf_sheaf (Proj| (pbo f))).obj U).1 = 0 := rfl

lemma pf_sheaf.add_val (x y : (pf_sheaf (Proj| (pbo f))).obj U) :
  (x + y).1 = x.1 + y.1 := rfl

lemma pf_sheaf.mul_val (x y : (pf_sheaf (Proj| (pbo f))).obj U) :
  (x * y).1 = x.1 * y.1 := rfl

variables {f_deg hm U}
lemma inv_mem (y : unop U) :
  ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1 ∈
    ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
      ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop :=
begin
  refine ⟨⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1,
    ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).2⟩, _, rfl⟩,
  change _ ∈ _ ⁻¹' _,
  erw set.mem_preimage,
  change (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f
    (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm y.1)) ∈ _,
  erw Proj_iso_Spec_Top_component.to_Spec_from_Spec 𝒜 hm f_deg y.1,
  exact y.2,
end

variables (f_deg hm)
/--
short for homogeneous localization.

Let `U` be an open set of `Spec A⁰_f` and `y ∈ U`, `hl` means
`hh(φ(y)) = a / b`
-/
def hl (y : unop U) : homogeneous_localization 𝒜 _ :=
hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1, inv_mem y⟩

lemma hl.one (y : unop U) :
  hl hm f_deg 1 y = 1 :=
by rw [hl, pf_sheaf.one_val, pi.one_apply]

lemma hl.zero (y : unop U) :
  hl hm f_deg 0 y = 0 :=
by rw [hl, pf_sheaf.zero_val, pi.zero_apply]

lemma hl.add (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  hl hm f_deg (x + y) z = hl hm f_deg x z + hl hm f_deg y z :=
by rw [hl, pf_sheaf.add_val, pi.add_apply, hl, hl]

lemma hl.mul (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  hl hm f_deg (x * y) z = hl hm f_deg x z * hl hm f_deg y z :=
by rw [hl, hl, hl, pf_sheaf.mul_val, pi.mul_apply]

/--
`num = (a * b ^ (m - 1)) / f^d`, where `hh(φ(y)) = a / b`, `f ∈ 𝒜 m` and
`a, b ∈ 𝒜 d`.
Note that `a * b ^ (m - 1)` has degree `d + (m - 1) * d = m * d`
and `f^d ∈ 𝒜 (m * d)` also has degree `m * d`, so this is well defined.

See also doc string for `Proj_iso_Spec_Sheaf_component.to_Spec.hl`.
-/
def num (y : unop U) : A⁰_ f :=
quotient.mk'
{ deg := m * (hl hm f_deg hh y).deg,
  num := ⟨(hl hm f_deg hh y).num * (hl hm f_deg hh y).denom ^ m.pred,
  begin
    rw calc m * (hl hm f_deg hh y).deg = (m.pred + 1) * (hl hm f_deg hh y).deg : _
    ... = m.pred * (hl hm f_deg hh y).deg + (hl hm f_deg hh y).deg : by rw [add_mul, one_mul]
    ... = (hl hm f_deg hh y).deg + m.pred * (hl hm f_deg hh y).deg : by rw add_comm,
    exact mul_mem (hl hm f_deg hh y).num_mem_deg (pow_mem_graded _ (denom_mem_deg _)),
    congr, rw ←nat.succ_pred_eq_of_pos hm, refl,
  end⟩,
  denom := ⟨f^(hl hm f_deg hh y).deg, by rw [mul_comm]; exact pow_mem_graded _ f_deg⟩,
  denom_mem := ⟨_, rfl⟩ }

/--
`denom = b^m / f^d`, where `hh(φ(y)) = a / b`, `f ∈ 𝒜 m` and `b ∈ 𝒜 d`.
Note that `b^m` and `f^d ∈ 𝒜 (m * d)` both has degree `m * d`, so this is well
defined.

See also doc string for `Proj_iso_Spec_Sheaf_component.to_Spec.hl`.
-/
def denom (y : unop U) : A⁰_ f :=
quotient.mk'
{ deg := m * (hl hm f_deg hh y).deg,
  num := ⟨(hl hm f_deg hh y).denom ^ m, pow_mem_graded _ (hl hm f_deg hh y).denom_mem_deg⟩,
  denom := ⟨f ^ (hl hm f_deg hh y).deg, by rw [mul_comm]; exact pow_mem_graded _ f_deg⟩,
  denom_mem := ⟨_, rfl⟩ }

lemma denom.not_mem (y : unop U) : denom hm f_deg hh y ∉ y.1.as_ideal := λ r,
begin
  have prop1 : ¬ (_ ∈ (Proj_iso_Spec_Top_component.from_Spec.to_fun
    f_deg hm y.1).1.as_homogeneous_ideal) := (hl hm f_deg hh y).denom_mem,
  erw not_forall at prop1,
  obtain ⟨n, hn⟩ := prop1,

  have eq1 : (hl hm f_deg hh y).deg = n,
  { -- n ≠ i, contradiction,
    by_contra ineq,
    simp only [proj_apply, direct_sum.decompose_of_mem_ne 𝒜 ((hl hm f_deg hh y).denom_mem_deg) ineq,
      zero_pow hm, mk_zero] at hn,
    apply hn,
    rw homogeneous_localization.mk'_zero,
    convert submodule.zero_mem _ using 1, },
  apply hn,
  rw ←eq1,
  convert r,
  rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same],
  exact (hl hm f_deg hh y).denom_mem_deg,
end

/--
```
       (a * b ^ (m - 1)) / f^d
fmk = -------------------------
             b^m / f^d
```
where `hh(φ(y)) = a / b`, `f ∈ 𝒜 m` and `a, b ∈ 𝒜 d`.


See also doc string for `Proj_iso_Spec_Sheaf_component.to_Spec.hl`.
-/
def fmk (y : unop U) : localization.at_prime y.1.as_ideal :=
mk (num hm f_deg hh y) ⟨denom hm f_deg hh y, denom.not_mem hm f_deg hh y⟩

lemma fmk.one (y : unop U) : fmk hm f_deg 1 y = 1 :=
begin
  unfold fmk,
  dsimp only,
  rw [show (1: structure_sheaf.localizations (A⁰_ f) y.val) = mk 1 1, by erw localization.mk_self 1,
    mk_eq_mk', is_localization.eq],

  have eq1 := (hl hm f_deg 1 y).eq_num_div_denom,
  rw [hl.one, homogeneous_localization.one_val] at eq1,
  erw [show (1 : localization.at_prime
    ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1.as_homogeneous_ideal.to_ideal) = mk 1 1,
      by { convert (localization.mk_self _).symm, refl }, mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨c, hc1⟩, eq1⟩ := eq1,

  change ¬(∀ i : ℕ, _ ∈ _) at hc1,
  rw not_forall at hc1,
  obtain ⟨j, hc1⟩ := hc1,
  rw [one_mul, submonoid.coe_one, mul_one] at eq1,
  simp only [←subtype.val_eq_coe] at eq1,
  rw [← hl.one] at eq1,
  have eq2 : proj 𝒜 ((hl hm f_deg 1 y).deg + j) ((hl hm f_deg 1 y).denom * c)
    = proj 𝒜 ((hl hm f_deg 1 y).deg + j) ((hl hm f_deg 1 y).num * c) := congr_arg _ eq1,

  have eq3 :
    proj 𝒜 ((hl hm f_deg 1 y).deg + j) ((hl hm f_deg 1 y).denom * c) =
    (hl hm f_deg 1 y).denom * proj 𝒜 j c := proj_hom_mul _ _ _ _ _ (hl hm f_deg 1 y).denom_mem_deg,

  have eq4 : proj 𝒜 ((hl hm f_deg 1 y).deg + j) ((hl hm f_deg 1 y).num * c)
    = (hl hm f_deg 1 y).num * proj 𝒜 j c := proj_hom_mul _ _ _ _ _ (num_mem_deg _),

  erw [eq3, eq4] at eq2,

  refine ⟨⟨quotient.mk' ⟨m * j,
     ⟨proj 𝒜 j c ^ m, pow_mem_graded _ (submodule.coe_mem _)⟩,
     ⟨f^j, by rw [mul_comm]; exact pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩, hc1⟩, _⟩,
  rw [submonoid.coe_one, one_mul, mul_one],

  unfold num denom,
  rw [homogeneous_localization.ext_iff_val],
  simp only [mul_val, homogeneous_localization.val_mk', subtype.coe_mk],
  rw [mk_mul, mk_mul],
  congr' 1,
  exact calc (hl hm f_deg 1 y).num * (hl hm f_deg 1 y).denom ^ m.pred * proj 𝒜 j c ^ m
          = (hl hm f_deg 1 y).num * (hl hm f_deg 1 y).denom ^ m.pred * proj 𝒜 j c ^ (m.pred + 1)
          : by { congr', exact (nat.succ_pred_eq_of_pos hm).symm }
      ... = (hl hm f_deg 1 y).num * (hl hm f_deg 1 y).denom ^ m.pred *
            (proj 𝒜 j c ^ m.pred * proj 𝒜 j c) : by ring_exp
      ... = ((hl hm f_deg 1 y).num * proj 𝒜 j c) *
            ((hl hm f_deg 1 y).denom ^ m.pred * proj 𝒜 j c ^ m.pred) : by ring
      ... = ((hl hm f_deg 1 y).denom * proj 𝒜 j c) *
            ((hl hm f_deg 1 y).denom ^ m.pred * proj 𝒜 j c ^ m.pred) : by rw eq2
      ... = ((hl hm f_deg 1 y).denom * proj 𝒜 j c) ^ (1 + m.pred) : by ring_exp
      ... = ((hl hm f_deg 1 y).denom * proj 𝒜 j c) ^ m
          : by { congr' 1, rw [add_comm], convert nat.succ_pred_eq_of_pos hm }
      ... = _ : by rw mul_pow,
end

lemma fmk.zero (y : unop U) : fmk hm f_deg 0 y = 0 :=
begin
  unfold fmk,
  rw [show (0 : structure_sheaf.localizations (A⁰_ f) y.val) = mk 0 1, by rw localization.mk_zero,
    mk_eq_mk', is_localization.eq],
  dsimp only,

  have eq1 := (hl hm f_deg 0 y).eq_num_div_denom,
  rw [hl.zero, homogeneous_localization.zero_val] at eq1,
  erw [show (0 : localization.at_prime
    ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1.as_homogeneous_ideal.to_ideal) = mk 0 1,
      by rw localization.mk_zero, mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨c, hc1⟩, eq1⟩ := eq1,
  rw [zero_mul, zero_mul, submonoid.coe_one, mul_one] at eq1,
  simp only [subtype.coe_mk] at eq1,
  dsimp only at eq1,

  change c ∉ Proj_iso_Spec_Top_component.from_Spec.carrier _ _ at hc1,
  change ¬(∀ i : ℕ, _ ∈ _) at hc1,
  rw not_forall at hc1,
  obtain ⟨j, hc1⟩ := hc1,
  replace eq1 := eq1.symm,
  have eq2 : proj 𝒜 ((hl hm f_deg 0 y).deg + j) ((hl hm f_deg 0 y).num * c) = 0,
  { erw [eq1, linear_map.map_zero], },
  have eq3 : proj 𝒜 ((hl hm f_deg 0 y).deg + j) ((hl hm f_deg 0 y).num * c)
    = (hl hm f_deg 0 y).num * proj 𝒜 j c := proj_hom_mul _ _ _ _ _ (num_mem_deg _),
  erw eq3 at eq2,

  refine ⟨⟨quotient.mk' ⟨m * j, ⟨proj 𝒜 j c ^ m, pow_mem_graded _ (submodule.coe_mem _)⟩,
    ⟨f^j, by rw [mul_comm]; exact pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩, hc1⟩, _⟩,
  unfold num,
  simp only [ext_iff_val, mul_val, submonoid.coe_one, zero_val, one_val, mul_one, one_mul, mul_zero,
    zero_mul, val_mk', subtype.coe_mk],
  rw [mk_mul],
  convert mk_zero _,
  exact calc (hl hm f_deg 0 y).num * (hl hm f_deg 0 y).denom ^ m.pred * (proj 𝒜 j) c ^ m
          = (hl hm f_deg 0 y).num * (hl hm f_deg 0 y).denom ^ m.pred * (proj 𝒜 j) c ^ (m.pred + 1)
          : by { congr', exact (nat.succ_pred_eq_of_pos hm).symm }
      ... = (hl hm f_deg 0 y).num * (hl hm f_deg 0 y).denom ^ m.pred *
            (proj 𝒜 j c ^ m.pred * proj 𝒜 j c) : by rw [pow_add, pow_one]
      ... = ((hl hm f_deg 0 y).num * proj 𝒜 j c)
            * ((hl hm f_deg 0 y).denom ^ m.pred * proj 𝒜 j c ^ m.pred) : by ring
      ... = 0 * ((hl hm f_deg 0 y).denom ^ m.pred * proj 𝒜 j c ^ m.pred) : by rw eq2
      ... = 0 : by rw zero_mul,
end

lemma fmk.add (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  fmk hm f_deg (x + y) z = fmk hm f_deg x z + fmk hm f_deg y z :=
begin
  unfold fmk,
  rw [localization.add_mk],

  have eq_xz := (hl hm f_deg x z).eq_num_div_denom,
  have eq_yz := (hl hm f_deg y z).eq_num_div_denom,
  have eq_addz := (hl hm f_deg (x + y) z).eq_num_div_denom,
  rw [hl.add, add_val, eq_xz, eq_yz, add_mk, mk_eq_mk', is_localization.eq] at eq_addz,
  obtain ⟨⟨c, hc⟩, eq_addz⟩ := eq_addz,
  simp only [submonoid.coe_mul, subtype.coe_mk] at eq_addz ⊢,

  set d_x := (hl hm f_deg x z).denom with dx_eq,
  set n_x := (hl hm f_deg x z).num with nx_eq,
  set d_y := (hl hm f_deg y z).denom with dy_eq,
  set n_y := (hl hm f_deg y z).num with ny_eq,
  set d_xy := (hl hm f_deg (x + y) z).denom with dxy_eq,
  set n_xy := (hl hm f_deg (x + y) z).num with nxy_eq,
  set i_x := (hl hm f_deg x z).deg with ix_eq,
  set i_y := (hl hm f_deg y z).deg with iy_eq,
  set i_xy := (hl hm f_deg (x + y) z).deg with ixy_eq,

  unfold num denom,
  simp only [←dx_eq, ←nx_eq, ←dy_eq, ←ny_eq, ←dxy_eq, ←nxy_eq, ←i_x, ←i_y, ←i_xy] at eq_addz ⊢,
  rw [localization.mk_eq_mk', is_localization.eq],

  change ¬(∀ i : ℕ, _ ∈ _) at hc,
  rw not_forall at hc,
  obtain ⟨j, hc⟩ := hc,

  refine ⟨⟨_, hc⟩, _⟩,
  rw [submonoid.coe_mul],
  simp only [subtype.coe_mk, ext_iff_val, mul_val, add_val, val_mk', mk_mul, add_mk,
    submonoid.coe_mul],
  rw [localization.mk_eq_mk', is_localization.eq],
  use 1,
  simp only [submonoid.coe_one, submonoid.mk_mul_mk, set_like.coe_mk, mul_one, ← pow_add],

  rw calc (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred))
          + f ^ (i_y + i_x) * (d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * proj 𝒜 j c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        = (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred))
            + f ^ (i_x + i_y) * (d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * proj 𝒜 j c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        : begin
          congr' 4,
          rw add_comm,
        end
    ... = (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * proj 𝒜 j c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        : begin
          congr' 3,
          rw mul_add,
        end
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * proj 𝒜 j c ^ m
          * (f ^ (i_x + i_y) * f ^ (i_xy + (i_x + i_y) + j)) : by ring
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * proj 𝒜 j c ^ m
          * (f ^ (i_x + i_y + (i_xy + (i_x + i_y) + j)))
        : begin
          congr' 1,
          rw [←pow_add],
        end
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * proj 𝒜 j c ^ m
          * (f ^ (i_x + i_y + (i_y + i_x) + i_xy + j))
        : begin
          congr' 2,
          ring,
        end,
  congr' 1,
  suffices EQ : (d_x * n_y + d_y * n_x) * d_xy * proj 𝒜 j c = n_xy * (d_x * d_y) * proj 𝒜 j c,
  { rw calc n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m) * proj 𝒜 j c ^ m
          = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m) * proj 𝒜 j c ^ (m.pred + 1)
          : by { congr', exact (nat.succ_pred_eq_of_pos hm).symm, }
      ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ m) * proj 𝒜 j c ^ (m.pred + 1)
          : by { congr', exact (nat.succ_pred_eq_of_pos hm).symm, }
      ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ (m.pred + 1)) *
            proj 𝒜 j c ^ (m.pred + 1) : by { congr', exact (nat.succ_pred_eq_of_pos hm).symm, }
      ... = n_xy * d_xy ^ m.pred * (d_x ^ m.pred * d_x * (d_y ^ m.pred * d_y))
            * (proj 𝒜 j c ^ m.pred * proj 𝒜 j c) : by simp only [pow_add, pow_one]
      ... = (n_xy * (d_x * d_y) * proj 𝒜 j c)
            * (d_xy ^ m.pred * d_x ^ m.pred * d_y ^ m.pred * proj 𝒜 j c ^ m.pred) : by ring
      ... = ((d_x * n_y + d_y * n_x) * d_xy * (graded_algebra.proj 𝒜 j) c)
            * (d_xy ^ m.pred * d_x ^ m.pred * d_y ^ m.pred * proj 𝒜 j c ^ m.pred) : by rw EQ
      ... = (d_x * n_y + d_y * n_x)
            * ((d_xy ^ m.pred * d_xy) * d_x ^ m.pred * d_y ^ m.pred
              * (proj 𝒜 j c ^ m.pred * proj 𝒜 j c)): by ring
      ... = (d_x * n_y + d_y * n_x)
            * (d_xy ^ m * d_x ^ m.pred * d_y ^ m.pred * proj 𝒜 j c ^ m)
          : begin
            congr';
            conv_rhs { rw [show m = m.pred + 1, from (nat.succ_pred_eq_of_pos hm).symm] };
            rw [pow_add, pow_one],
          end
      ... = (d_x * n_y + d_y * n_x) * d_x ^ m.pred * d_y ^ m.pred * d_xy ^ m * proj 𝒜 j c ^ m
          : by ring,
    congr',

    exact calc (d_x * n_y + d_y * n_x) * d_x ^ m.pred * d_y ^ m.pred
          = (d_y ^ m.pred * d_y) * (n_x * d_x ^ m.pred) +
            (d_x ^ m.pred * d_x) * (n_y * d_y ^ m.pred) : by ring
      ... = (d_y ^ m.pred * d_y^1) * (n_x * d_x ^ m.pred) +
            (d_x ^ m.pred * d_x ^ 1) * (n_y * d_y ^ m.pred) : by simp only [pow_one]
      ... = (d_y ^ (m.pred + 1)) * (n_x * d_x ^ m.pred) +
            (d_x ^ (m.pred + 1)) * (n_y * d_y ^ m.pred) : by simp only [pow_add]
      ... = d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred)
          : by { congr'; apply nat.succ_pred_eq_of_pos hm, } },

  replace eq_addz := congr_arg (graded_algebra.proj 𝒜 ((i_x + i_y) + i_xy + j)) eq_addz,
  have eq1 : (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) ((d_x * n_y + d_y * n_x) * d_xy * c)
    = (d_x * n_y + d_y * n_x) * d_xy * graded_algebra.proj 𝒜 j c,
  { refine proj_hom_mul _ _ _ _ _ (mul_mem (submodule.add_mem _
      (set_like.graded_monoid.mul_mem (denom_mem_deg _) (num_mem_deg _)) _) (denom_mem_deg _)),
    { rw add_comm, exact mul_mem (denom_mem_deg _) (num_mem_deg _), }, },
  erw eq1 at eq_addz,
  clear eq1,

  have eq2 : proj 𝒜 (i_x + i_y + i_xy + j) (n_xy * (d_x * d_y) * c)
    = n_xy * (d_x * d_y) * proj 𝒜 j c,
  { refine proj_hom_mul _ _ _ _ _ _,
    { rw show i_x + i_y + i_xy = i_xy + (i_x + i_y), by ring,
      exact mul_mem (num_mem_deg _) (set_like.graded_monoid.mul_mem
        (denom_mem_deg _) (denom_mem_deg _)), }, },
  erw eq2 at eq_addz,
  exact eq_addz,
end

lemma fmk.mul (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  fmk hm f_deg (x * y) z = fmk hm f_deg x z * fmk hm f_deg y z :=
begin
  unfold fmk,
  rw [mk_mul],

  have eq_xz := (hl hm f_deg x z).eq_num_div_denom,
  have eq_yz := (hl hm f_deg y z).eq_num_div_denom,
  have eq_mulz := (hl hm f_deg (x * y) z).eq_num_div_denom,
  rw [hl.mul, mul_val, eq_xz, eq_yz, mk_mul, mk_eq_mk', is_localization.eq] at eq_mulz,
  obtain ⟨⟨c, hc⟩, eq_mulz⟩ := eq_mulz,
  simp only [submonoid.coe_mul] at eq_mulz,
  simp only [← subtype.val_eq_coe] at eq_mulz,

  set d_x := (hl hm f_deg x z).denom with dx_eq,
  set n_x := (hl hm f_deg x z).num with nx_eq,
  set d_y := (hl hm f_deg y z).denom with dy_eq,
  set n_y := (hl hm f_deg y z).num with ny_eq,
  set d_xy := (hl hm f_deg (x * y) z).denom with dxy_eq,
  set n_xy := (hl hm f_deg (x * y) z).num with nxy_eq,
  set i_x := (hl hm f_deg x z).deg with ix_eq,
  set i_y := (hl hm f_deg y z).deg with iy_eq,
  set i_xy := (hl hm f_deg (x * y) z).deg with ixy_eq,

  unfold num denom,
  simp only [←dx_eq, ←nx_eq, ←dy_eq, ←ny_eq, ←dxy_eq, ←nxy_eq, ←i_x, ←i_y, ←i_xy] at eq_mulz ⊢,
  rw [localization.mk_eq_mk', is_localization.eq],

  change ¬(∀ i : ℕ, _ ∈ _) at hc,
  erw not_forall at hc,
  obtain ⟨j, hc⟩ := hc,

  refine ⟨⟨_, hc⟩, _⟩,
  simp only [submonoid.coe_mul, subtype.coe_mk, ext_iff_val, submonoid.coe_mul, mul_val, val_mk',
    mk_mul],
  simp only [mk_eq_mk', is_localization.eq],

  use 1,
  simp only [submonoid.coe_one, submonoid.coe_mul, mul_one],
  simp only [subtype.coe_mk, ← pow_add],

  suffices EQ : n_x * n_y * d_xy * proj 𝒜 j c = n_xy * (d_x * d_y) * proj 𝒜 j c,

  rw calc n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * proj 𝒜 j c ^ m
          * f ^ (i_x + i_y + i_xy + j)
        = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * proj 𝒜 j c ^ (m.pred + 1)
          * f ^ (i_x + i_y + i_xy + j) : by { congr', exact (nat.succ_pred_eq_of_pos hm).symm, }
    ... = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * (proj 𝒜 j c ^ m.pred * proj 𝒜 j c)
          * f ^ (i_x + i_y + i_xy + j) : by ring_exp
    ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ (m.pred + 1))
          * (proj 𝒜 j c ^ m.pred * proj 𝒜 j c)
          * f ^ (i_x + i_y + i_xy + j)
        : by { congr', all_goals { symmetry, apply nat.succ_pred_eq_of_pos hm, } }
    ... = (n_xy * (d_x * d_y) * proj 𝒜 j c)
          * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * proj 𝒜 j c^m.pred)
          * f ^ (i_x + i_y + i_xy + j) : by ring_exp
    ... = (n_x * n_y * d_xy * proj 𝒜 j c)
          * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * proj 𝒜 j c^m.pred)
          * f ^ (i_x + i_y + i_xy + j) : by rw EQ
    ... = (n_x * n_y * d_xy)
          * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (proj 𝒜 j c ^ m.pred * proj 𝒜 j c))
          * f ^ (i_x + i_y + i_xy + j) : by ring
    ... = (n_x * n_y * d_xy)
          * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (proj 𝒜 j c^m.pred * proj 𝒜 j c^1))
          * f ^ (i_x + i_y + i_xy + j) : by rw pow_one
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (proj 𝒜 j c^(m.pred + 1)))
          * f ^ (i_x + i_y + i_xy + j) : by ring_exp
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (proj 𝒜 j c^m))
          * f ^ (i_x + i_y + i_xy + j) : by { congr', exact nat.succ_pred_eq_of_pos hm, }
    ... = (n_x * n_y) * ((d_xy^m.pred * d_xy) * d_x^m.pred * d_y^m.pred * (proj 𝒜 j c^m))
          * f ^ (i_x + i_y + i_xy + j) : by ring
    ... = (n_x * n_y) * ((d_xy^m.pred * d_xy^1) * d_x^m.pred * d_y^m.pred * (proj 𝒜 j c^m))
          * f ^ (i_x + i_y + i_xy + j) : by rw pow_one
    ... = (n_x * n_y) * ((d_xy^(m.pred + 1)) * d_x^m.pred * d_y^m.pred * (proj 𝒜 j c^m))
          * f ^ (i_x + i_y + i_xy + j) : by ring_exp
    ... = (n_x * n_y) * (d_xy^m * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j) : by { congr', exact nat.succ_pred_eq_of_pos hm },
  ring_nf,

  have INEQ : graded_algebra.proj 𝒜 j c ≠ 0,
  { intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    rw homogeneous_localization.mk'_zero,
    exact submodule.zero_mem _, },
  replace eq_mulz := congr_arg (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) eq_mulz,
  rwa [proj_hom_mul, proj_hom_mul] at eq_mulz,

  { have : (hl hm f_deg x z * hl hm f_deg y z).num * (d_x * d_y) ∈ 𝒜 (i_xy + (i_x + i_y)),
    { refine set_like.graded_monoid.mul_mem _ (mul_mem (denom_mem_deg _) (denom_mem_deg _)),
      rw [← hl.mul],
      exact (hl hm f_deg (x * y) z).num_mem_deg, },
    convert this using 2,
    ring, },

  refine set_like.graded_monoid.mul_mem (mul_mem (num_mem_deg _) (num_mem_deg _)) _,
  rw [← hl.mul],
  exact (hl hm f_deg (x * y) z).denom_mem_deg,
end

namespace is_locally_quotient

variable (f_deg)
/--
Let `V` be an open set of `Proj`, then `ψ(V)` is an open in `Spec A⁰_f`
-/
def open_set (V : opens Proj.T) : opens (Spec.T (A⁰_ f)) :=
⟨homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg) ''
  {z | @coe (subtype _) ↥((Proj.to_LocallyRingedSpace (λ {m : ℕ}, 𝒜 m)).to_Top) _ z ∈ V.1}, begin
  rw [homeomorph.is_open_image, is_open_induced_iff],
  exact ⟨V.1, V.2, rfl⟩,
end⟩

/--
If `V ⊆ φ⁻¹ U` then `ψ V ⊆ U`.
-/
def open_set_is_subset
  (V : opens Proj.T)
  (subset1 : V ⟶ ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
            ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop) :
  (open_set 𝒜 hm f_deg V) ⟶ unop U := hom_of_le
begin
  have subset2 := le_of_hom subset1,
  rintros z z_mem,
  obtain ⟨z, z_mem, rfl⟩ := z_mem,
  dsimp only [set.mem_set_of] at z_mem,
  specialize subset2 z_mem,
  obtain ⟨a, a_mem, eq2⟩ := subset2,
  erw set.mem_preimage at a_mem,
  rw homeo_of_iso_apply,
  change _ ∈ (unop U).val,
  convert a_mem,
  rw subtype.ext_iff,
  rw ←eq2,
  refl,
end

lemma mem_open_subset_of_inv_mem (V : opens Proj.T) (y : unop U)
  (mem1 : (((Proj_iso_Spec_Top_component hm f_deg).inv) y.val).val ∈ V) :
  y.1 ∈ open_set 𝒜 hm f_deg V  :=
begin
  refine ⟨(Proj_iso_Spec_Top_component hm f_deg).inv y.1, mem1, _⟩,
  rw [homeo_of_iso_apply],
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
end

/--
For b ∈ 𝒜 i
z ∈ V and b ∉ z, then b^m / f^i ∉ forward f
-/
lemma not_mem
  (b : A) (degree : ℕ) (b_mem : b ∈ 𝒜 degree)
  (z : Proj.T| (pbo f))
  (b_not_mem : b ∉ z.1.as_homogeneous_ideal) :
  (quotient.mk' ⟨m * degree, ⟨b ^ m, set_like.pow_mem_graded _ b_mem⟩,
    ⟨f^degree, by rw [mul_comm]; exact set_like.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩ : A⁰_ f)
  ∉ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).as_ideal := λ rid,
begin
  classical,

  rw homeo_of_iso_apply at rid,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at rid,
  dsimp only at rid,

  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at rid,
  obtain ⟨c, eq1⟩ := rid,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  dsimp only [subtype.coe_mk] at eq1,
  obtain ⟨N, hN⟩ := localization.away.clear_denominator (finset.image (λ i, c i * i.1) c.support),
  -- N is the common denom
  choose acd hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  have eq3 := calc (mk (b^m) 1 : localization.away f) * mk (f^N) 1
        = mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩ * mk (f^degree) 1 * mk (f^N) 1
        : begin
          congr,
          rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
          use 1,
          erw [mul_one, mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
        end
    ... = mk (f^degree) 1 * mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩ * mk (f^N) 1 : by ring
    ... = mk (f^degree) 1 * mk (f^N) 1 * ∑ i in c.support, c i * i.1
        : begin
          erw eq1,
          rw homogeneous_localization.val_mk',
          simp only [subtype.coe_mk, mk_mul, one_mul, mul_one],
          congr' 1,
          ring,
        end
    ... = mk (f^degree) 1 * (mk (f^N) 1 * ∑ i in c.support, c i * i.1) : by ring
    ... = mk (f^degree) 1 * ∑ i in c.support, (mk (f^N) 1) * (c i * i.1)
        : by { congr' 1, rw finset.mul_sum }
    ... = mk (f^degree) 1 * ∑ i in c.support.attach, (mk (f^N) 1) * (c i.1 * i.1.1)
        : by { congr' 1, convert finset.sum_attach.symm, }
    ... = mk (f^degree) 1 * ∑ i in c.support.attach, (mk (acd (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
        : begin
          congr' 1,
          rw finset.sum_congr rfl (λ j hj, _),
          have eq2 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
          dsimp only at eq2,
          erw eq2,
          rw mul_comm,
        end
    ... = ∑ i in c.support.attach, (mk (f^degree) 1) * (mk (acd (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
        : by rw finset.mul_sum
    ... = ∑ i in c.support.attach, mk (f^degree * (acd (c i.1 * i.1.1) (prop1 i.1 i.2))) 1
        : by { rw finset.sum_congr rfl (λ j hj, _), erw [mk_mul, one_mul] }
    ... = mk (∑ i in c.support.attach, (f^degree * (acd (c i.1 * i.1.1) (prop1 i.1 i.2)))) 1
        : begin
          induction c.support.attach using finset.induction_on with y s hy ih,
          rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],
          rw [finset.sum_insert hy, finset.sum_insert hy, ih, add_mk, mul_one, submonoid.coe_one,
            one_mul, one_mul, add_comm],
        end,
  erw [localization.mk_mul, one_mul] at eq3,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
  erw [mul_one, ←subtype.val_eq_coe, mul_one] at eq3,
  dsimp only at eq3,
  suffices : (∑ i in c.support.attach, (f^degree * acd (c i.1 * i.1.1) (prop1 i.1 i.2))) * f^l ∈
    z.1.as_homogeneous_ideal,
  erw ←eq3 at this,
  rcases z.1.is_prime.mem_or_mem this with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { exact b_not_mem ((z.1.is_prime.pow_mem_iff_mem _ hm).mp H1), },
  { exact (projective_spectrum.mem_basic_open 𝒜 _ _).mpr z.2 (z.1.is_prime.mem_of_pow_mem _ H2), },
  { exact (projective_spectrum.mem_basic_open 𝒜 _ _).mpr z.2 (z.1.is_prime.mem_of_pow_mem _ H3), },
  refine ideal.mul_mem_right _ _ (ideal.sum_mem _ $ λ j hj, ideal.mul_mem_left _ _ _),
  set g := classical.some j.1.2 with g_eq,
  have mem3 : g ∈ z.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
  have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2.symm,
  have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
  dsimp only at eq4,
  have eq5 : ∃ (a : A) (zz : ℕ), c j.1 = mk a ⟨f^zz, ⟨zz, rfl⟩⟩,
  { induction (c j.1) using localization.induction_on with data,
    rcases data with ⟨a, ⟨_, ⟨zz, rfl⟩⟩⟩,
    refine ⟨a, zz, rfl⟩, },
  obtain ⟨α, zz, hzz⟩ := eq5,
  have eq6 := calc (mk (acd (c j.1 * j.1.1) (prop1 j.1 j.2)) 1 : localization.away f)
          = c j.1 * j.1.1 * mk (f^N) 1 : eq4
      ... = mk α ⟨f^zz, ⟨zz, rfl⟩⟩ * j.1.1 * mk (f^N) 1 : by erw hzz
      ... = mk α ⟨f^zz, ⟨zz, rfl⟩⟩ * mk g 1 * mk (f^N) 1 : by erw eq3
      ... = mk (α * g * f^N) ⟨f^zz, ⟨zz, rfl⟩⟩
          : by erw [mk_mul, mk_mul, mul_one, mul_one],
  simp only [mk_eq_mk', is_localization.eq] at eq6,
  obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
  rw [subtype.coe_mk, subtype.coe_mk, submonoid.coe_one, mul_one] at eq6,
  have mem4 : α * g * f ^ N * f ^ v ∈ z.1.as_homogeneous_ideal :=
    ideal.mul_mem_right _ _ (ideal.mul_mem_right _ _ (ideal.mul_mem_left _ _ mem3)),
  erw ←eq6 at mem4,
  rcases z.1.is_prime.mem_or_mem mem4 with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { exact H1 },
  { exact false.elim (((projective_spectrum.mem_basic_open _ _ _).mpr z.2)
      (z.1.is_prime.mem_of_pow_mem _ H2)), },
  { exact false.elim (((projective_spectrum.mem_basic_open _ _ _).mpr z.2)
      (z.1.is_prime.mem_of_pow_mem _ H3)), },
end

include hm
lemma mk_proj_pow_not_mem
  (z : Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f)))
  (C : A) (j : ℕ) (hj : graded_algebra.proj 𝒜 j C ∉ z.1.as_homogeneous_ideal) :
  (localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f ^ j, ⟨j, rfl⟩⟩ : localization.away f) ∉
    ideal.span ((algebra_map A (away f)) '' ↑(projective_spectrum.as_homogeneous_ideal z.val)) :=
begin
  classical,

  intro rid,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at rid,
  obtain ⟨c, eq1⟩ := rid,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  obtain ⟨N, hN⟩ := localization.away.clear_denominator (finset.image (λ i, c i * i.1) c.support),
  -- N is the common denom
  choose acd hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  have eq3 := calc (mk (proj 𝒜 j C ^ m) 1 : localization.away f) * mk (f^N) 1
        = mk (proj 𝒜 j C ^ m) ⟨f^j, ⟨_, rfl⟩⟩ * mk (f^j) 1 * mk (f^N) 1
        : begin
          congr,
          rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
          use 1,
          erw [mul_one, mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
        end
    ... = mk (f^j) 1 * mk (proj 𝒜 j C ^ m) ⟨f^j, ⟨_, rfl⟩⟩ * mk (f^N) 1 : by ring
    ... = mk (f^j) 1 * mk (f^N) 1 * ∑ i in c.support, c i * i.1 : by { erw eq1, ring }
    ... = mk (f^j) 1 * (mk (f^N) 1 * ∑ i in c.support, c i * i.1) : by ring
    ... = mk (f^j) 1 * ∑ i in c.support, (mk (f^N) 1) * (c i * i.1)
        : by { congr' 1, rw finset.mul_sum }
    ... = mk (f^j) 1 * ∑ i in c.support.attach, (mk (f^N) 1) * (c i.1 * i.1.1)
        : by { congr' 1, convert finset.sum_attach.symm }
    ... = mk (f^j) 1 * ∑ i in c.support.attach, (mk (acd (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
        : begin
          congr' 1,
          rw finset.sum_congr rfl (λ j hj, _),
          have eq2' := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
          dsimp only at eq2',
          erw eq2',
          rw mul_comm,
        end
    ... = ∑ i in c.support.attach, (mk (f^j) 1) * (mk (acd (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
        : begin
          rw finset.mul_sum,
        end
    ... = ∑ i in c.support.attach, mk (f^j * (acd (c i.1 * i.1.1) (prop1 i.1 i.2))) 1
        : begin
          rw finset.sum_congr rfl (λ j hj, _),
          erw [localization.mk_mul, one_mul],
        end
    ... = mk (∑ i in c.support.attach, (f^j * (acd (c i.1 * i.1.1) (prop1 i.1 i.2)))) 1
        : begin
          induction c.support.attach using finset.induction_on with y s hy ih,
          rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],
          erw [finset.sum_insert hy, finset.sum_insert hy, ih, add_mk, mul_one, one_mul,
            one_mul, add_comm],
        end,
  erw [localization.mk_mul, one_mul] at eq3,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
  erw [mul_one, ←subtype.val_eq_coe, mul_one] at eq3,
  dsimp only at eq3,
  suffices : (∑ i in c.support.attach, (f^j * (acd (c i.1 * i.1.1) (prop1 i.1 i.2)))) * f^l ∈
    z.1.as_homogeneous_ideal,
  erw ←eq3 at this,
  rcases z.1.is_prime.mem_or_mem this with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { refine hj ((z.1.is_prime.pow_mem_iff_mem _ hm).mp H1), },
  { exact false.elim (((projective_spectrum.mem_basic_open _ _ _).mpr z.2)
      (z.1.is_prime.mem_of_pow_mem _ H2)), },
  { exact false.elim (((projective_spectrum.mem_basic_open _ _ _).mpr z.2)
      (z.1.is_prime.mem_of_pow_mem _ H3)), },
  refine ideal.mul_mem_right _ _ (ideal.sum_mem _ $ λ j hj, ideal.mul_mem_left _ _ _),
  set g := classical.some j.1.2 with g_eq,
  have mem3 : g ∈ z.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
  have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2.symm,
  have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
  dsimp only at eq4,

  have eq5 : ∃ (a : A) (zz : ℕ), c j.1 = mk a ⟨f^zz, ⟨zz, rfl⟩⟩,
  { induction (c j.1) using localization.induction_on with data,
    rcases data with ⟨a, ⟨_, ⟨zz, rfl⟩⟩⟩,
    refine ⟨a, zz, rfl⟩, },
  obtain ⟨α, zz, hzz⟩ := eq5,

  have eq6 := calc (mk (acd (c j.1 * j.1.1) (prop1 j.1 j.2)) 1 : localization.away f)
        = c j.1 * j.1.1 * mk (f^N) 1 : eq4
    ... = mk α ⟨f^zz, ⟨zz, rfl⟩⟩ * j.1.1 * mk (f^N) 1 : by erw hzz
    ... = mk α ⟨f^zz, ⟨zz, rfl⟩⟩ * mk g 1 * mk (f^N) 1 : by erw eq3
    ... = mk (α * g * f^N) ⟨f^zz, ⟨zz, rfl⟩⟩
        : by erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
  simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
  obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
  rw [subtype.coe_mk, subtype.coe_mk, submonoid.coe_one, mul_one] at eq6,
  dsimp only at eq6,

  have mem4 : α * g * f ^ N * f ^ v ∈ z.1.as_homogeneous_ideal,
  { exact ideal.mul_mem_right _ _ (ideal.mul_mem_right _ _ (ideal.mul_mem_left _ _ mem3)), },
  erw ←eq6 at mem4,

  rcases z.1.is_prime.mem_or_mem mem4 with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { exact H1 },
  { exact false.elim (((projective_spectrum.mem_basic_open _ _ _).mpr z.2)
      (z.1.is_prime.mem_of_pow_mem _ H2)), },
  { exact false.elim (((projective_spectrum.mem_basic_open _ _ _).mpr z.2)
      (z.1.is_prime.mem_of_pow_mem _ H3)), }
end

omit hm
lemma final_eq
  (d_hh n_hh a b C : A) (degree i_hh j : ℕ)
  (d_hh_mem : d_hh ∈ 𝒜 i_hh) (n_hh_mem : n_hh ∈ 𝒜 i_hh)
  (a_hom : a ∈ 𝒜 degree) (b_hom : b ∈ 𝒜 degree)
  (eq1 : n_hh * b * C = a * d_hh * C) :
  n_hh * b * proj 𝒜 j C = a * d_hh * proj 𝒜 j C :=
begin
  have eq2 := congr_arg (graded_algebra.proj 𝒜 (i_hh + degree + j)) eq1,
  rw [proj_hom_mul, proj_hom_mul] at eq2,
  exact eq2,
  { rw add_comm,
    exact set_like.graded_monoid.mul_mem a_hom d_hh_mem, },
  { exact set_like.graded_monoid.mul_mem n_hh_mem b_hom, },
end

lemma inv_hom_mem_bo (V : opens Proj.T) (z : Proj.T| (pbo f))
  (subset2 : open_set 𝒜 hm f_deg V ⟶ unop U) (z_mem : z.1 ∈ V) :
  (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, ⟨z, z_mem, rfl⟩⟩).val).val ∈
  projective_spectrum.basic_open 𝒜 f :=
begin
  erw projective_spectrum.mem_basic_open,
  intro rid,
  change ∀ _, _ at rid,
  specialize rid m,
  simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 f_deg] at rid,
  change _ ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1 at rid,
  have rid2 : (1 : A⁰_ f) ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1,
  { convert rid,
    simp only [ext_iff_val, subtype.coe_mk, one_val, homogeneous_localization.val_mk'],
    convert (localization.mk_self _).symm,
    refl, },
  rw homeo_of_iso_apply at rid2,
  apply (((Proj_iso_Spec_Top_component hm f_deg).hom) z).is_prime.1,
  rw ideal.eq_top_iff_one,
  exact rid2,
end

lemma inv_hom_mem2
  (V : opens Proj.T)
  (z : Proj.T| (pbo f))
  (subset2 : open_set 𝒜 hm f_deg V ⟶ unop U)
  (z_mem : z.1 ∈ V) :
  (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, ⟨z, z_mem, rfl⟩⟩).val).val ∈
  ((@opens.open_embedding (projective_spectrum.Top 𝒜)
      (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop :=
begin
  simp only [unop_op, functor.op_obj],
  set z' := (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, ⟨z, z_mem, rfl⟩⟩).val).val
    with z'_eq,
  refine ⟨⟨z', _⟩, _, rfl⟩,
  have mem_z' : z' ∈ projective_spectrum.basic_open 𝒜 f,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    erw z'_eq at rid,
    change ∀ _, _ at rid,
    specialize rid m,
    simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 f_deg] at rid,
    change _ ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1 at rid,
    have rid2 : (1 : A⁰_ f) ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1,
    { convert rid,
      simp only [homogeneous_localization.ext_iff_val, homogeneous_localization.one_val,
        homogeneous_localization.val_mk', subtype.coe_mk],
      convert (localization.mk_self _).symm,
      refl, },
    rw homeo_of_iso_apply at rid2,
    apply (((Proj_iso_Spec_Top_component hm f_deg).hom) z).is_prime.1,
    rw ideal.eq_top_iff_one,
    exact rid2 },
  { exact mem_z' },
  erw [set.mem_preimage],
  have subset3 := le_of_hom subset2,
  suffices : ((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z', _⟩ ∈ open_set 𝒜 hm f_deg V,
  { exact subset3 this, },

  refine ⟨z, z_mem, _⟩,
  simp only [homeo_of_iso_apply],
  congr',
  rw subtype.ext_iff,
  dsimp only [subtype.coe_mk],
  rw z'_eq,
  change z.1 = (Proj_iso_Spec_Top_component.from_Spec hm f_deg
    (Proj_iso_Spec_Top_component.to_Spec _ _ _)).1,
  congr',
  exact (Proj_iso_Spec_Top_component.from_Spec_to_Spec 𝒜 hm f_deg z).symm,
end

end is_locally_quotient

variables (hm f_deg)
lemma fmk_is_locally_quotient (y : unop U) :
  ∃ (V : opens (Spec.T (A⁰_ f))) (mem : y.val ∈ V) (i : V ⟶ unop U) (r s : (A⁰_ f)),
    ∀ (z : V),
      ∃ (s_not_mem : s ∉ prime_spectrum.as_ideal z.val),
        fmk hm f_deg hh ⟨(i z).1, (i z).2⟩ = mk r ⟨s, s_not_mem⟩ :=
begin
  classical,

  obtain ⟨V, mem1, subset1, degree, ⟨a, a_mem⟩, ⟨b, b_mem⟩, eq1⟩ :=
    hh.2 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1, inv_mem y⟩,
  set VVo : opens (Spec.T (A⁰_ f)) := is_locally_quotient.open_set 𝒜 hm f_deg V with VVo_eq,
  have subset2 : VVo ⟶ unop U := is_locally_quotient.open_set_is_subset 𝒜 hm f_deg V subset1,
  have y_mem1 : y.1 ∈ VVo,
  { convert is_locally_quotient.mem_open_subset_of_inv_mem 𝒜 hm f_deg V y mem1 },
  refine ⟨VVo, y_mem1, subset2,
    quotient.mk' ⟨m * degree, ⟨a * b^m.pred,
      begin
        have mem1 : b^m.pred ∈ 𝒜 (m.pred * degree) := set_like.pow_mem_graded _ b_mem,
        have mem2 := set_like.graded_monoid.mul_mem a_mem mem1,
        convert mem2,
        exact calc m * degree
                = (m.pred + 1) * degree
                : begin
                  congr' 1,
                  symmetry,
                  apply nat.succ_pred_eq_of_pos hm,
                end
            ... = m.pred * degree + 1 * degree : by rw add_mul
            ... = m.pred * degree + degree : by rw one_mul
            ... = degree + m.pred * degree : by rw add_comm,
      end⟩, ⟨f^degree, by rw [mul_comm]; exact set_like.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
    quotient.mk' ⟨m * degree, ⟨b^m, set_like.pow_mem_graded _ b_mem⟩,
      ⟨f^degree, by rw [mul_comm]; exact set_like.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩, _⟩,

  rintros ⟨z, z_mem⟩,
  obtain ⟨z, z_mem, rfl⟩ := z_mem,
  specialize eq1 ⟨z.1, z_mem⟩,
  obtain ⟨b_not_mem, eq1⟩ := eq1,

  refine ⟨is_locally_quotient.not_mem hm f_deg b degree b_mem z b_not_mem, _⟩,

  have eq2 := (hh.val (subset1 ⟨z.val, z_mem⟩)).eq_num_div_denom,
  dsimp only at eq1,
  rw [homogeneous_localization.ext_iff_val] at eq1,
  rw [eq2, homogeneous_localization.val_mk'] at eq1,
  rw [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1,
  unfold fmk,
  rw [localization.mk_eq_mk', is_localization.eq],
  simp only [subtype.coe_mk] at eq1,
  set degree_hh := (hh.val (subset1 ⟨z.val, z_mem⟩)).deg with degree_hh_eq,
  have mem_C : ∃ (j : ℕ), proj 𝒜 j C ∉ z.1.as_homogeneous_ideal,
  { by_contra rid,
    rw not_exists at rid,
    apply hC,
    rw ←direct_sum.sum_support_decompose 𝒜 C,
    apply ideal.sum_mem,
    intros j hj,
    specialize rid j,
    rw not_not at rid,
    apply rid, },
  obtain ⟨j, hj⟩ := mem_C,
  refine ⟨⟨quotient.mk' ⟨m * j, ⟨(graded_algebra.proj 𝒜 j C)^m,
    set_like.pow_mem_graded _ (submodule.coe_mem _)⟩, ⟨f^j,
    by rw [mul_comm]; exact set_like.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩, _⟩, _⟩,

  { change _ ∉ _,
    simp only [← subtype.val_eq_coe],
    erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
    apply is_locally_quotient.mk_proj_pow_not_mem 𝒜 hm z C j hj, },

  set z' := (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, ⟨z, z_mem, rfl⟩⟩).val).val
    with z'_eq,

  have z'_mem : z' ∈ (((@opens.open_embedding Proj.T) (pbo f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop,
  { convert is_locally_quotient.inv_hom_mem2 𝒜 hm f_deg V z subset2 z_mem },

  have eq_pt : (subset1 ⟨z.1, z_mem⟩) = ⟨z', z'_mem⟩,
  { rw subtype.ext_iff,
    change z.1 = (Proj_iso_Spec_Top_component.from_Spec hm f_deg
      (Proj_iso_Spec_Top_component.to_Spec 𝒜 f _)).1,
    congr',
    exact (Proj_iso_Spec_Top_component.from_Spec_to_Spec 𝒜 hm f_deg z).symm, },
  erw [eq_pt] at eq1,

  unfold num denom,
  simp only [subtype.coe_mk, ext_iff_val, mul_val, val_mk', mk_mul, submonoid.coe_mul],
  rw [localization.mk_eq_mk', is_localization.eq],
  use 1,
  simp only [submonoid.coe_mul, submonoid.coe_one],
  simp only [←subtype.val_eq_coe, one_mul, mul_one, ←pow_add],

  set d_hh := (hh.val ⟨z', z'_mem⟩).denom with d_hh_eq,
  set n_hh := (hh.val ⟨z', z'_mem⟩).num with n_hh_eq,
  set i_hh := (hh.val ⟨z', z'_mem⟩).deg with i_hh_eq,
  simp only [←d_hh_eq, ←n_hh_eq, ←i_hh_eq] at eq1,

  suffices : n_hh * d_hh ^ m.pred * b ^ m * proj 𝒜 j C ^ m * f ^ (degree + i_hh + j)
    = a * b ^ m.pred * d_hh ^ m * proj 𝒜 j C ^ m * f ^ (i_hh + degree + j),
  convert this,

  suffices EQ : n_hh * b * proj 𝒜 j C = a * d_hh * proj 𝒜 j C,
  erw calc n_hh * d_hh ^ m.pred * b ^ m * proj 𝒜 j C ^ m * f ^ (degree + i_hh + j)
        = n_hh * d_hh ^ m.pred * b ^ (m.pred + 1) * proj 𝒜 j C^(m.pred + 1) * f^(degree + i_hh + j)
        : by congr'; exact (nat.succ_pred_eq_of_pos hm).symm
    ... = n_hh * d_hh ^ m.pred * (b ^ m.pred * b) * (proj 𝒜 j C ^ m.pred * proj 𝒜 j C)
          * f^(degree + i_hh + j) : by { congr', all_goals { rw [pow_add, pow_one], } }
    ... = (n_hh * b * proj 𝒜 j C) * (d_hh ^ m.pred * b ^ m.pred * proj 𝒜 j C^m.pred)
          * f^(degree + i_hh + j)  : by ring
    ... = (a * d_hh * proj 𝒜 j C) * (d_hh ^ m.pred * b ^ m.pred * proj 𝒜 j C^m.pred)
          * f^(degree + i_hh + j)  : by rw EQ
    ... = a * b ^ m.pred * (d_hh ^ m.pred * d_hh) * (proj 𝒜 j C^m.pred * proj 𝒜 j C)
          * f^(degree + i_hh + j)  : by ring
    ... = a * b ^ m.pred * (d_hh ^ m.pred * d_hh^1) * (proj 𝒜 j C^m.pred * proj 𝒜 j C ^ 1)
          * f^(degree + i_hh + j) : by rw [pow_one, pow_one]
    ... =  a * b ^ m.pred * (d_hh ^ (m.pred + 1)) * (proj 𝒜 j C^(m.pred + 1))
          * f^(degree + i_hh + j) : by simp only [pow_add]
    ... = a * b ^ m.pred * d_hh ^ m * proj 𝒜 j C^m * f^(degree + i_hh + j)
        : by { congr', all_goals { apply nat.succ_pred_eq_of_pos hm, } }
    ... = a * b ^ m.pred * d_hh ^ m * proj 𝒜 j C^m * f^(i_hh + degree + j)
        : by { congr' 1, rw add_comm i_hh degree },
  have INEQ : proj 𝒜 j C ≠ 0,
  { intro rid,
    apply hj,
    rw rid,
    exact submodule.zero_mem _, },

  have eq2 := congr_arg (graded_algebra.proj 𝒜 (i_hh + degree + j)) eq1,
  rw [graded_algebra.proj_hom_mul, graded_algebra.proj_hom_mul] at eq2,
  exact eq2,

  { rw add_comm,
    refine set_like.graded_monoid.mul_mem a_mem (denom_mem_deg _), },
  { exact set_like.graded_monoid.mul_mem (num_mem_deg _) b_mem, },
end

variable (U)
/--
Let `U ⊆ Spec A⁰_f`, this is a ring homomorphism
`(ψ _* Proj | D(f))(U) ⟶ (Spec A⁰_f)(U)` defined by:
```
           (a * b ^ (m - 1)) / f^d
h ↦ y ↦ -------------------------
                b^m / f^d
```
where `hh(φ(y)) = a / b`, `f ∈ 𝒜 m` and `a, b ∈ 𝒜 d`.


See also doc string for `Proj_iso_Spec_Sheaf_component.to_Spec.hl`.
-/
def to_fun : (pf_sheaf (Proj| (pbo f))).obj U ⟶ (Spec (A⁰_ f)).presheaf.obj U :=
{ to_fun := λ hh, ⟨λ y, fmk hm f_deg hh y, begin
    rw algebraic_geometry.structure_sheaf.is_locally_fraction_pred',
    exact fmk_is_locally_quotient hm f_deg hh,
  end⟩,
  map_one' := begin
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    ext y,
    rw [fmk.one hm],
    convert pi.one_apply _,
  end,
  map_mul' := λ x y, begin
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    ext z,
    rw [fmk.mul hm],
    change _ * _ = _ * _,
    dsimp only,
    refl,
  end,
  map_zero' := begin
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    ext y,
    rw [fmk.zero hm],
    convert pi.zero_apply _,
  end,
  map_add' := λ x y, begin
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    ext z,
    rw [fmk.add hm],
    change _ + _ = fmk hm f_deg x z + fmk hm f_deg y z,
    dsimp only,
    refl
  end }

end to_Spec

section

/--
Let `U ⊆ Spec A⁰_f`, this is a ring homomorphism
`(ψ _* Proj | D(f))(U) ⟶ (Spec A⁰_f)(U)` defined by:
```
           (a * b ^ (m - 1)) / f^d
h ↦ y ↦ -------------------------
                b^m / f^d
```
where `hh(φ(y)) = a / b`, `f ∈ 𝒜 m` and `a, b ∈ 𝒜 d`.

This is natural in `U`, thus defining a morphism between sheaves.

See also doc string for `Proj_iso_Spec_Sheaf_component.to_Spec.hl`.
-
-/
def to_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m):
  ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf) ⟶
  (Spec (A⁰_ f)).presheaf :=
{ app := λ U, to_Spec.to_fun hm f_deg U,
  naturality' := λ U V subset1, begin
    ext1 z,
    simp only [comp_apply, ring_hom.coe_mk, functor.op_map, presheaf.pushforward_obj_map],
    refl,
  end }

end

namespace from_Spec_to_Spec

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens (Spec.T (A⁰_ f)))ᵒᵖ)
variables (hh : ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf).obj V)
variables (z : (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
  ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop))

lemma section_congr
  (hh : ((Spec (A⁰_ f)).presheaf).obj V) (x y : unop V) (h1 : x = y)
  (a : _) (b : x.1.as_ideal.prime_compl)
  (h2 : (hh.1 x) = mk a b) : (hh.1 y) = mk a ⟨b.1, λ _, b.2 (by simpa only [h1])⟩ :=
begin
  induction h1,
  convert h2,
  rw subtype.ext_iff_val,
end

lemma inv_hom_apply_eq :
  ((Proj_iso_Spec_Top_component hm f_deg).inv
    ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg _ _⟩)).1 =
  z.1 :=
begin
  change (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm
    (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f _)).1 = z.1,
  rw Proj_iso_Spec_Top_component.from_Spec_to_Spec,
end

lemma pt_eq :
  z = ⟨((Proj_iso_Spec_Top_component hm f_deg).inv
    ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg _ _⟩)).1,
      by simpa only [inv_hom_apply_eq hm f_deg V z] using z.2⟩ :=
by rw [subtype.ext_iff_val, inv_hom_apply_eq]

include hm
lemma final_eq (a α β b C : A) (ι ii jj L1 L2 : ℕ)
  (data_eq2 : α * β ^ m.pred * b * C * f ^ (ii + ι + L1) * f ^ L2 =
    a * β ^ m * C * f ^ (ι + jj + L1) * f ^ L2) :
  a * f ^ jj * β * (C * β ^ m.pred * f ^ (ι + L1 + L2)) =
  α * (b * f ^ ii) * (C * β ^ m.pred * f ^ (ι + L1 + L2)) :=
begin
  symmetry,
  rw calc α * (b * f ^ ii) * (C * β ^ m.pred * f ^ (ι + L1 + L2))
        = α * β ^ m.pred * b * C * (f^ii * f^(ι + L1 + L2)) : by ring
    ... = α * β ^ m.pred * b * C * (f^ii * (f^ι * f^L1 * f^L2)) : by simp only [pow_add]
    ... = α * β ^ m.pred * b * C * (f ^ ii * f^ι * f^L1) * f ^ L2 : by ring
    ... = α * β ^ m.pred * b * C * (f ^ (ii + ι + L1)) * f ^ L2 : by simp only [pow_add]
    ... = a * β ^ m * C * f ^ (ι + jj + L1) * f ^ L2 : by rw data_eq2
    ... = a * β ^ (m.pred + 1) * C * f ^ (ι + jj + L1) * f ^ L2
        : by { congr', exact (nat.succ_pred_eq_of_pos hm).symm },
  simp only [pow_add, pow_one],
  ring,
end

section

omit hm
lemma
  _root_.algebraic_geometry.Proj_iso_Spec_Sheaf_component.from_Spec_to_Spec:
  from_Spec.bmk hm f_deg V (((to_Spec 𝒜 hm f_deg).app V) hh) z = hh.1 z :=
begin
  unfold from_Spec.bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],

  set hom_z := (Proj_iso_Spec_Top_component hm f_deg).hom
    ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩ with hom_z_eq,
  have hom_z_mem_V : hom_z ∈ unop V,
  { apply from_Spec.data_prop2 hm f_deg V _, },

  set data := from_Spec.data 𝒜 hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z with data_eq,
  have data_eq1 := data_eq,
  replace data_eq1 : data = to_Spec.fmk hm f_deg hh ⟨hom_z, hom_z_mem_V⟩,
  { convert data_eq1, },
  unfold to_Spec.fmk to_Spec.num to_Spec.denom at data_eq1,

  have data_eq2 := from_Spec.data.eq_num_div_denom hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z,
  rw [←data_eq, data_eq1] at data_eq2,
  set α := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1,
    to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).num with α_eq,
  set β := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1,
    to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).denom with β_eq,
  set ι := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1,
    to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).deg with ι_eq,
  have β_not_in : β ∉ (((Proj_iso_Spec_Top_component hm f_deg).inv)
    ((Proj_iso_Spec_Top_component hm f_deg).hom
      ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩)).1.as_homogeneous_ideal,
  { exact (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1,
      to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).denom_mem, },
  have hartshorne_eq : (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1,
    to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).val = mk α ⟨β, β_not_in⟩,
  { exact (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1,
      to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).eq_num_div_denom, },

  rw show (hh.1 z).val = mk α ⟨β, by { rw inv_hom_apply_eq at β_not_in, convert β_not_in }⟩,
  { have := (pt_eq hm f_deg V z),
    convert hartshorne_eq;
    rw pt_eq hm f_deg V z;
    refl <|> { ext, refl }, },

  simp only [←α_eq, ←β_eq, ←ι_eq] at data_eq2,
  erw [localization.mk_eq_mk', is_localization.eq] at data_eq2,
  obtain ⟨⟨C, hC⟩, data_eq2⟩ := data_eq2,
  set L1 : ℕ := C.denom_mem.some with L1_eq,
  have L1_eq' : _ = f^L1 := C.denom_mem.some_spec.symm,
  have C_eq : C.val = mk C.num ⟨f^L1, ⟨_, rfl⟩⟩,
  { simp_rw [←L1_eq', C.eq_num_div_denom], },

  simp only [ext_iff_val, C_eq, mul_val, subtype.coe_mk, val_mk'] at data_eq2,
  simp only [eq_num_div_denom, homogeneous_localization.val_mk'] at data_eq2,

  set a := (from_Spec.data.num 𝒜 hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z).num with a_eq,
  set b := (from_Spec.data.denom 𝒜 hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z).num with b_eq,
  set ii := (from_Spec.data.num 𝒜 hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z).denom_mem.some
    with ii_eq,
  have ii_eq' : _ = f^ii := (from_Spec.data.num 𝒜 hm f_deg
    (((to_Spec 𝒜 hm f_deg).app V) hh) z).denom_mem.some_spec.symm,
  set jj := (from_Spec.data.denom 𝒜 hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z).denom_mem.some
    with jj_eq,
  have jj_eq' : _ = f^jj := (from_Spec.data.denom 𝒜 hm f_deg
    (((to_Spec 𝒜 hm f_deg).app V) hh) z).denom_mem.some_spec.symm,
  simp only [localization.mk_mul, subtype.coe_mk] at data_eq2,
  rw [localization.mk_eq_mk', is_localization.eq] at data_eq2,
  obtain ⟨⟨_, ⟨L2, rfl⟩⟩, data_eq2⟩ := data_eq2,
  simp only [submonoid.coe_mul, subtype.coe_mk] at data_eq2,
  rw [ii_eq', jj_eq'] at data_eq2,
  simp only [←pow_add] at data_eq2,
  unfold from_Spec.num from_Spec.denom,
  dsimp only,
  rw [localization.mk_eq_mk', is_localization.eq],

  refine ⟨⟨C.num * β^m.pred * f^(ι+L1+L2), _⟩, _⟩,
  { intro rid,
    rcases z.1.is_prime.mem_or_mem rid with H1 | H3,
    rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
    { have eq1 : (mk C.num ⟨f ^ L1, ⟨_, rfl⟩⟩ : localization.away f) =
        mk 1 ⟨f^L1, ⟨_, rfl⟩⟩ * mk C.num 1,
      { rw [localization.mk_mul, one_mul, mul_one] },
      apply hC,
      erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
      simp only [C_eq, homogeneous_localization.val_mk', subtype.coe_mk],
      erw [eq1],
      convert ideal.mul_mem_left _ _ _,
      apply ideal.subset_span,
      refine ⟨C.num, H1, rfl⟩, },
    { replace H2 := z.1.is_prime.mem_of_pow_mem _ H2,
      apply β_not_in,
      erw show (((Proj_iso_Spec_Top_component hm f_deg).inv)
        ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩)).1 =
        z.1,
      { change (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm
          (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 _ _)).1 = z.1,
        rw Proj_iso_Spec_Top_component.from_Spec_to_Spec, },
      exact H2, },
    { replace H3 := z.1.is_prime.mem_of_pow_mem _ H3,
      obtain ⟨⟨a, ha⟩, ha2, (ha3 : a = z.1)⟩ := z.2,
      apply ha,
      rwa ha3, } },
  { simp only [subtype.coe_mk], convert final_eq hm _ _ _ _ C.num ι ii jj L1 L2 data_eq2 },
end

end

end from_Spec_to_Spec

namespace to_Spec_from_Spec

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens ((Spec.T (A⁰_ f))))ᵒᵖ)
variables (hh : ((Spec (A⁰_ f)).presheaf.obj V)) (z : V.unop)

lemma inv_mem :
((Proj_iso_Spec_Top_component hm f_deg).inv z).1 ∈
  ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop :=
begin
  have mem1 := ((Proj_iso_Spec_Top_component hm f_deg).inv z).2,
  refine ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z), _, rfl⟩,
  erw set.mem_preimage,
  convert z.2,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
end

lemma inv_mem_pbo :
    ((Proj_iso_Spec_Top_component hm f_deg).inv z).1 ∈ pbo f :=
begin
  intro rid,
  obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := inv_mem hm f_deg V z,
  change a = ((Proj_iso_Spec_Top_component hm f_deg).inv z).1 at ha3,
  erw ←ha3 at rid,
  apply ha1,
  exact rid,
end

lemma dd_not_mem_z
  (dd : (((Proj_iso_Spec_Top_component hm f_deg).hom)
    ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1,
      inv_mem_pbo hm f_deg V z⟩).as_ideal.prime_compl) : dd.1 ∉ z.1.as_ideal :=
begin
  have mem1 : dd.1 ∉ (((Proj_iso_Spec_Top_component hm f_deg).hom)
    ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).val, _⟩).as_ideal := dd.2,
  convert mem1,
  change z.1 = Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f
    (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm _),
  rw Proj_iso_Spec_Top_component.to_Spec_from_Spec,
  refl,
end

lemma eq0
  (dd : (((Proj_iso_Spec_Top_component hm f_deg).hom)
      ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1,
        inv_mem_pbo hm f_deg V z⟩).as_ideal.prime_compl)
  (nn : A⁰_ f)
  (data_eq1 : localization.mk nn dd =
    hh.val ⟨((Proj_iso_Spec_Top_component hm f_deg).hom)
    ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).val, _⟩, begin
      convert z.2,
      change (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f
        (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm _)) = z.1,
      rw Proj_iso_Spec_Top_component.to_Spec_from_Spec,
      refl,
    end⟩) :
  (hh.1 z) = mk nn ⟨dd.1, dd_not_mem_z hm f_deg V z dd⟩ :=
begin
  convert from_Spec_to_Spec.section_congr 𝒜 V hh _ _ _ nn ⟨dd.1, _⟩ _,
  refine ⟨((Proj_iso_Spec_Top_component hm f_deg).hom)
    ⟨(((Proj_iso_Spec_Top_component hm f_deg).inv) ↑z).val, _⟩, _⟩,
  apply inv_mem_pbo,
  { convert z.2,
    convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _ },
  { rw subtype.ext_iff_val,
    convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _ },
  { exact dd.2 },
  rw ← data_eq1,
  congr' 1,
  rw subtype.ext_iff_val,
end

lemma not_mem1
  (C : A) (j : ℕ)
  (hj : proj 𝒜 j C ∉ (((Proj_iso_Spec_Top_component hm f_deg).inv z)).1.as_homogeneous_ideal) :
  (quotient.mk' ⟨m * j, ⟨proj 𝒜 j C ^ m, pow_mem_graded _ (submodule.coe_mem _)⟩,
    ⟨f^j, by rw [mul_comm]; exact pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈
  z.1.as_ideal.prime_compl :=
begin
  intro rid,
  change graded_algebra.proj 𝒜 j C ∉ Proj_iso_Spec_Top_component.from_Spec.carrier _ _ at hj,
  apply hj,
  intro k,
  by_cases ineq : j = k,
  { rw ←ineq,
    convert rid using 1,
    rw [ext_iff_val, val_mk', homogeneous_localization.val_mk'],
    dsimp only [subtype.coe_mk],
    congr' 1,
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same],
    exact submodule.coe_mem _, },
  { convert submodule.zero_mem _ using 1,
    rw [ext_iff_val, val_mk', homogeneous_localization.zero_val],
    dsimp only [subtype.coe_mk],
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne],
    { rw [zero_pow hm, localization.mk_zero] },
    { exact submodule.coe_mem _ },
    { exact ineq }, }
end

lemma eq1
  (hart : homogeneous_localization.at_prime 𝒜
    ((Proj_iso_Spec_Top_component hm f_deg).inv z).1.as_homogeneous_ideal.to_ideal)
  (C : A) (j : ℕ)
  (dd : (((Proj_iso_Spec_Top_component hm f_deg).hom)
    ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1,
      inv_mem_pbo hm f_deg V z⟩).as_ideal.prime_compl)
  (nn : A⁰_ f)
  (EQ : hart.num * (dd.val.num * nn.denom) * graded_algebra.proj 𝒜 j C =
        nn.num * dd.val.denom * hart.denom * graded_algebra.proj 𝒜 j C) :
  hart.num * hart.denom ^ m.pred * dd.val.num * (graded_algebra.proj 𝒜 j) C ^ m *
    (nn.denom * f ^ hart.deg * f ^ j) =
  nn.num * hart.denom ^ m * (graded_algebra.proj 𝒜 j) C ^ m *
    (f ^ hart.deg * dd.val.denom * f ^ j) :=
begin
  rw calc hart.num * hart.denom ^ m.pred * dd.val.num
          * proj 𝒜 j C ^ m * (nn.denom * f ^ hart.deg * f^j)
        = hart.num * hart.denom ^ m.pred * dd.val.num
          * proj 𝒜 j C ^ (m.pred + 1) * (nn.denom * f ^ hart.deg * f^j)
        : by { congr', exact (nat.succ_pred_eq_of_pos hm).symm }
    ... = hart.num * hart.denom ^ m.pred * dd.val.num
          * (proj 𝒜 j C ^ m.pred * proj 𝒜 j C)
          * (nn.denom * f ^ hart.deg * f^j) : by simp only [pow_add, pow_one]
    ... = (hart.num * (dd.val.num * nn.denom) * proj 𝒜 j C)
          * (hart.denom ^ m.pred * proj 𝒜 j C ^ m.pred * f ^ hart.deg * f ^ j) : by ring
    ... = (nn.num * dd.val.denom * hart.denom * proj 𝒜 j C)
          * (hart.denom ^ m.pred * proj 𝒜 j C ^ m.pred * f ^ hart.deg * f ^ j) : by rw EQ
    ... = (nn.num * dd.val.denom)
          * (proj 𝒜 j C ^ m.pred * proj 𝒜 j C)
          * (hart.denom ^ m.pred * hart.denom) * (f ^ hart.deg * f ^ j) : by ring
    ... = (nn.num * dd.val.denom)
          * (proj 𝒜 j C ^ m.pred * proj 𝒜 j C ^ 1) * (hart.denom ^ m.pred * hart.denom ^ 1)
          * (f ^ hart.deg * f ^ j) : by simp only [pow_one]
    ... = (nn.num * dd.val.denom)
          * (proj 𝒜 j C ^ (m.pred + 1))
          * (hart.denom ^ (m.pred + 1)) * (f ^ hart.deg * f ^ j) : by simp only [pow_add]
    ... = (nn.num * dd.val.denom)
          * (proj 𝒜 j C ^ m)
          * (hart.denom ^ m) * (f ^ hart.deg * f ^ j)
        : by congr'; apply nat.succ_pred_eq_of_pos hm,
  simp only [pow_add],
  ring,
end

lemma eq2
  (hart : homogeneous_localization.at_prime 𝒜
    ((Proj_iso_Spec_Top_component hm f_deg).inv z).1.as_homogeneous_ideal.to_ideal)
  (C : A) (j : ℕ)
  (dd : (((Proj_iso_Spec_Top_component hm f_deg).hom)
    ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1,
      inv_mem_pbo hm f_deg V z⟩).as_ideal.prime_compl)
  (nn : A⁰_ f)
  (eq1 : hart.num * (dd.val.num * nn.denom) * C =
    nn.num * dd.val.denom * hart.denom * C) :
  hart.num * (dd.val.num * nn.denom) * graded_algebra.proj 𝒜 j C =
  nn.num * dd.val.denom * hart.denom * graded_algebra.proj 𝒜 j C :=
begin
  have mem1 := dd.1.num_mem_deg,
  have mem2 := nn.num_mem_deg,
  have eq2 := congr_arg
    (graded_algebra.proj 𝒜 (hart.deg + dd.1.deg + nn.deg + j)) eq1,
  rw graded_algebra.proj_hom_mul at eq2,
  rw graded_algebra.proj_hom_mul at eq2,
  exact eq2,

  rw show nn.num * dd.val.denom * hart.denom =
    hart.denom * dd.1.denom * nn.num, by ring,

  { exact set_like.graded_monoid.mul_mem (mul_mem (denom_mem_deg _) dd.1.denom_mem_deg) mem2 },

  { rw ←mul_assoc,
    exact set_like.graded_monoid.mul_mem (mul_mem (num_mem_deg _) mem1) (denom_mem_deg _), },
end

lemma _root_.algebraic_geometry.Proj_iso_Spec_Sheaf_component.to_Spec_from_Spec
  {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (V hh z) :
  to_Spec.fmk hm f_deg (((from_Spec 𝒜 hm f_deg).app V) hh) z =
  hh.val z :=
begin
  classical,

  set b_hh := ((from_Spec 𝒜 hm f_deg).app V hh) with b_hh_eq,
  unfold to_Spec.fmk to_Spec.num to_Spec.denom,
  set inv_z := ((Proj_iso_Spec_Top_component hm f_deg).inv z) with inv_z_eq,
  have inv_z_mem : inv_z.1 ∈
    ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop,
  { apply to_Spec_from_Spec.inv_mem, },

  have inv_z_mem_bo : inv_z.1 ∈ projective_spectrum.basic_open 𝒜 f,
  { apply to_Spec_from_Spec.inv_mem_pbo, },

  set hart := b_hh.1 ⟨inv_z.1, inv_z_mem⟩ with hart_eq,
  rw homogeneous_localization.ext_iff_val at hart_eq,
  have hart_eq1 := hart.eq_num_div_denom,
  rw hart_eq at hart_eq1,

  rw b_hh_eq at hart_eq,
  replace hart_eq : hart.val = (from_Spec.bmk hm f_deg V hh ⟨inv_z.val, inv_z_mem⟩).val,
  { convert hart_eq },
  unfold from_Spec.bmk at hart_eq,
  rw [homogeneous_localization.val_mk'] at hart_eq,
  simp only [← subtype.val_eq_coe] at hart_eq,
  unfold from_Spec.num from_Spec.denom at hart_eq,

  set data := from_Spec.data 𝒜 hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with data_eq,
  have data_eq1 := data_eq,
  unfold from_Spec.data at data_eq1,
  erw from_Spec.data.eq_num_div_denom at data_eq,
  erw data_eq at data_eq1,
  set nn := from_Spec.data.num 𝒜 hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with nn_eq,
  set dd := from_Spec.data.denom 𝒜 hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with dd_eq,
  dsimp only at hart_eq,

  rw hart.eq_num_div_denom at hart_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at hart_eq,
  obtain ⟨⟨C, hC⟩, eq1⟩ := hart_eq,
  simp only [←subtype.val_eq_coe] at eq1,
  have hC2 : ∃ j : ℕ, graded_algebra.proj 𝒜 j C ∉ inv_z.1.as_homogeneous_ideal,
  { by_contra rid,
    rw not_exists at rid,
    apply hC,
    rw ←direct_sum.sum_support_decompose 𝒜 C,
    apply ideal.sum_mem inv_z.1.as_homogeneous_ideal.1,
    intros j hj,
    specialize rid j,
    rw not_not at rid,
    exact rid, },
  obtain ⟨j, hj⟩ := hC2,

  have proj_C_ne_zero : graded_algebra.proj 𝒜 j C ≠ 0,
  { intro rid,
    rw rid at hj,
    apply hj,
    exact submodule.zero_mem _, },

  have dd_not_mem_z : dd ∉ z.val.as_ideal,
  { apply to_Spec_from_Spec.dd_not_mem_z, },

  have eq0 : (hh.1 z) = localization.mk nn ⟨dd, dd_not_mem_z⟩,
  { convert to_Spec_from_Spec.eq0 hm f_deg _ hh z ⟨dd, _⟩ nn data_eq1, },
  rw [eq0, localization.mk_eq_mk', is_localization.eq],
  simp only [ext_iff_val, mul_val, val_mk', subtype.coe_mk],
  rw [dd.eq_num_div_denom, nn.eq_num_div_denom, localization.mk_mul, localization.mk_mul],

  refine ⟨⟨quotient.mk' ⟨m * j, ⟨(graded_algebra.proj 𝒜 j C)^m,
    pow_mem_graded _ (submodule.coe_mem _)⟩, ⟨f^j,
    by rw [mul_comm]; exact pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
    to_Spec_from_Spec.not_mem1 hm f_deg V z C j hj⟩, _⟩,
  simp only [subtype.coe_mk],
  { rw [homogeneous_localization.val_mk'],
    simp only [subtype.coe_mk],
    rw [localization.mk_mul, localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
    use 1,
    simp only [subtype.coe_mk, submonoid.coe_mul, submonoid.coe_one, mul_one, one_mul],
    apply to_Spec_from_Spec.eq1,
    apply to_Spec_from_Spec.eq2;
    assumption }
end

end to_Spec_from_Spec

end Proj_iso_Spec_Sheaf_component
/--
The function defined in `Proj_iso_Spec_Sheaf_component.to_Spec` and
`Proj_iso_Spec_Sheaf_component.from_Spec` forms an isomorphism of sheaves
`ψ_* (Proj | D(f)) ≅ Spec A⁰_f`

See also docstrings for `Proj_iso_Spec_Sheaf_component.to_Spec` and
`Proj_iso_Spec_Sheaf_component.from_Spec`.
-/
def Sheaf_component {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
  (Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf ≅
  (Spec (A⁰_ f)).presheaf :=
{ hom := Proj_iso_Spec_Sheaf_component.to_Spec 𝒜 hm f_deg,
  inv := Proj_iso_Spec_Sheaf_component.from_Spec 𝒜 hm f_deg,
  hom_inv_id' := begin
    ext V hh : 3,
    erw [nat_trans.comp_app, nat_trans.id_app, comp_apply, id_apply, subtype.ext_iff_val],
    ext1 z,
    apply Proj_iso_Spec_Sheaf_component.from_Spec_to_Spec,
  end,
  inv_hom_id' := begin
    ext V hh : 3,
    erw [nat_trans.comp_app, nat_trans.id_app, comp_apply, id_apply],
    rw subtype.ext_iff_val,
    ext1 z,
    apply Proj_iso_Spec_Sheaf_component.to_Spec_from_Spec,
  end }

/--
`Proj | D(f)` and `Spec A⁰_f` are isomorphic as locally ringed space.
-/
def Proj_iso_Spec_Sheaf_component.iso {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
  (Proj| (pbo f)) ≅ Spec (A⁰_ f) :=
let H : (Proj| (pbo f)).to_PresheafedSpace ≅ (Spec (A⁰_ f)).to_PresheafedSpace :=
  PresheafedSpace.iso_of_components
    (Proj_iso_Spec_Top_component hm f_deg) (Sheaf_component 𝒜 f_deg hm) in
LocallyRingedSpace.iso_of_SheafedSpace_iso
{ hom := H.1,
  inv := H.2,
  hom_inv_id' := H.3,
  inv_hom_id' := H.4 }

/--
For any `x ∈ Proj` (a homogeneous prime ideal that is relevant), there is always
some `0 < n ∈ ℕ` and `f ∈ A` such that `f ∈ 𝒜 n` but `f ∉ x` (i.e. `x ∈ D(f)`).
-/
def choose_element (x : Proj) :
  Σ' (n : ℕ) (hn : 0 < n) (f : A), f ∈ 𝒜 n ∧ f ∉ x.as_homogeneous_ideal :=
begin
  classical,
  have := x.3,
  erw set.not_subset at this,
  choose f h1 h2 using this,
  erw ←direct_sum.sum_support_decompose 𝒜 f at h2,
  have : ∃ (n : ℕ) (hn : 0 < n), (direct_sum.decompose 𝒜 f n : A) ∉ x.as_homogeneous_ideal.1,
  { by_contra rid,
    simp only [not_exists, exists_prop, not_and, not_not, subtype.val_eq_coe] at rid,
    refine h2 (ideal.sum_mem _ (λ c hc, (em (0 < c)).elim (λ ineq1, rid _ ineq1) (λ ineq1, _))),
    rw not_lt at ineq1,
    replace ineq1 := nat.eq_zero_of_le_zero ineq1,
    rw ineq1,
    dsimp only at h1,
    change f ∈ (homogeneous_ideal.irrelevant 𝒜) at h1,
    rw ←graded_algebra.proj_apply,
    rw homogeneous_ideal.mem_irrelevant_iff at h1,
    erw h1,
    exact submodule.zero_mem _, },
  choose n hn1 hn2 using this,
  refine ⟨n, hn1, (direct_sum.decompose _ f n : A), submodule.coe_mem _, hn2⟩,
end

/--
For any `x ∈ Proj`, there exists `x ∈ D(f)` for some `f ∈ 𝒜 m` with `0 < m`,
then these `D(f)` forms an open affine cover.

In another word, `Proj` is a scheme.

See also docstring for `algebraic_geoemtry.choose_element`
-/
def Proj.to_Scheme : Scheme :=
{ local_affine := λ x,
  begin
    rcases choose_element 𝒜 x with ⟨n, hn, f, f_deg, mem⟩,
    refine ⟨⟨pbo f, mem⟩, ⟨A⁰_ f⟩, ⟨Proj_iso_Spec_Sheaf_component.iso 𝒜 f_deg hn⟩⟩,
  end,
  ..Proj }

end algebraic_geometry
