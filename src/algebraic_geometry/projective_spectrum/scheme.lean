/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.structure_sheaf
import algebraic_geometry.Spec

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
* `A⁰_x`       : the degree zero part of localized ring `Aₓ`

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
def degree_zero_part {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) : subring (away f) :=
{ carrier := { y | ∃ (n : ℕ) (a : 𝒜 (m * n)), y = mk a ⟨f^n, ⟨n, rfl⟩⟩ },
  mul_mem' := λ _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩, h.symm ▸ h'.symm ▸
    ⟨n+n', ⟨⟨a.1 * b.1, (mul_add m n n').symm ▸ mul_mem a.2 b.2⟩,
    by {rw mk_mul, congr' 1, simp only [pow_add], refl }⟩⟩,
  one_mem' := ⟨0, ⟨1, (mul_zero m).symm ▸ one_mem⟩,
    by { symmetry, rw subtype.coe_mk, convert ← mk_self 1, simp only [pow_zero], refl, }⟩,
  add_mem' := λ _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩, h.symm ▸ h'.symm ▸
    ⟨n+n', ⟨⟨f ^ n * b.1 + f ^ n' * a.1, (mul_add m n n').symm ▸
      add_mem (mul_mem (by { rw mul_comm, exact set_like.pow_mem_graded n f_deg }) b.2)
        begin
          rw add_comm,
          refine mul_mem _ a.2,
          rw mul_comm,
          exact set_like.pow_mem_graded _ f_deg
        end⟩, begin
          rw add_mk,
          congr' 1,
          simp only [pow_add],
          refl,
        end⟩⟩,
  zero_mem' := ⟨0, ⟨0, (mk_zero _).symm⟩⟩,
  neg_mem' := λ x ⟨n, ⟨a, h⟩⟩, h.symm ▸ ⟨n, ⟨-a, neg_mk _ _⟩⟩ }

end

local notation `A⁰_` f_deg := degree_zero_part f_deg

section

variable {𝒜}

instance (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) : comm_ring (A⁰_ f_deg) :=
(degree_zero_part f_deg).to_comm_ring

/--
Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks this natural number `n`
-/
def degree_zero_part.deg {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_ f_deg) : ℕ :=
x.2.some

/--
Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks the numerator `a`
-/
def degree_zero_part.num {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_ f_deg) : A :=
x.2.some_spec.some.1

lemma degree_zero_part.num_mem {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_ f_deg) :
  degree_zero_part.num x ∈ 𝒜 (m * degree_zero_part.deg x) :=
x.2.some_spec.some.2

lemma degree_zero_part.eq {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_ f_deg) :
  (x : away f) = mk (degree_zero_part.num x) ⟨f^(degree_zero_part.deg x), ⟨_, rfl⟩⟩ :=
x.2.some_spec.some_spec

lemma degree_zero_part.coe_mul {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x y : A⁰_ f_deg) :
  (↑(x * y) : away f) = x * y := rfl

end

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
def carrier : ideal (A⁰_ f_deg) :=
ideal.comap (algebra_map (A⁰_ f_deg) (away f))
  (ideal.span $ algebra_map A (away f) '' x.1.as_homogeneous_ideal)

lemma mem_carrier_iff (z : A⁰_ f_deg) :
  z ∈ carrier f_deg x ↔
  ↑z ∈ ideal.span (algebra_map A (away f) '' x.1.as_homogeneous_ideal) :=
iff.rfl

lemma mem_carrier.clear_denominator [decidable_eq (away f)]
  {z : A⁰_ f_deg} (hz : z ∈ carrier f_deg x) :
  ∃ (c : algebra_map A (away f) '' x.1.as_homogeneous_ideal →₀ away f)
    (N : ℕ)
    (acd : Π y ∈ c.support.image c, A),
    f ^ N • ↑z =
    algebra_map A (away f) (∑ i in c.support.attach,
      acd (c i) (finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * classical.some i.1.2) :=
begin
  rw [mem_carrier_iff, ←submodule_span_eq, finsupp.span_eq_range_total, linear_map.mem_range] at hz,
  rcases hz with ⟨c, eq1⟩,
  rw [finsupp.total_apply, finsupp.sum] at eq1,
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := is_localization.exist_integer_multiples_of_finset (submonoid.powers f)
    (c.support.image c),
  choose acd hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i ∈ finset.image c c.support,
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },

  refine ⟨c, N, acd, _⟩,
  rw [← eq1, smul_sum, map_sum, ← sum_attach],
  congr' 1,
  ext i,
  rw [_root_.map_mul, hacd, (classical.some_spec i.1.2).2, smul_eq_mul, smul_mul_assoc],
  refl
end

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
  carrier f_deg x ≠ ⊤ :=
begin
  have eq_top := disjoint x,
  classical,
  contrapose! eq_top,
  obtain ⟨c, N, acd, eq1⟩ := mem_carrier.clear_denominator _ x ((ideal.eq_top_iff_one _).mp eq_top),
  rw [algebra.smul_def, subring.coe_one, mul_one] at eq1,
  change localization.mk (f ^ N) 1 = mk (∑ _, _) 1 at eq1,
  simp only [mk_eq_mk', is_localization.eq] at eq1,
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
  erw [mul_one, mul_one] at eq1,
  change f^_ * f^_ = _ * f^_ at eq1,
  rw set.not_disjoint_iff_nonempty_inter,
  refine ⟨f^N * f^M, eq1.symm ▸ mul_mem_right _ _
    (sum_mem _ (λ i hi, mul_mem_left _ _ _)), ⟨N+M, by rw pow_add⟩⟩,
  generalize_proofs h,
  exact (classical.some_spec h).1,
end

/--The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `Top_component.forward`.
-/
def to_fun (x : Proj.T| (pbo f)) : (Spec.T (A⁰_ f_deg)) :=
⟨carrier f_deg x, carrier_ne_top f_deg x, λ x1 x2 hx12, begin
  classical,
  rcases ⟨x1, x2⟩ with ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩,
  induction x1 using localization.induction_on with data_x1,
  induction x2 using localization.induction_on with data_x2,
  rcases ⟨data_x1, data_x2⟩ with ⟨⟨a1, _, ⟨n1, rfl⟩⟩, ⟨a2, _, ⟨n2, rfl⟩⟩⟩,
  rcases mem_carrier.clear_denominator f_deg x hx12 with ⟨c, N, acd, eq1⟩,
  simp only [degree_zero_part.coe_mul, algebra.smul_def] at eq1,
  change localization.mk (f ^ N) 1 * (mk _ _ * mk _ _) = mk (∑ _, _) _ at eq1,
  simp only [localization.mk_mul, one_mul] at eq1,
  simp only [mk_eq_mk', is_localization.eq] at eq1,
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
  rw [submonoid.coe_one, mul_one] at eq1,
  change _ * _ * f^_ = _ * (f^_ * f^_) * f^_ at eq1,

  rcases x.1.is_prime.mem_or_mem (show a1 * a2 * f ^ N * f ^ M ∈ _, from _) with h1|rid2,
  rcases x.1.is_prime.mem_or_mem h1 with h1|rid1,
  rcases x.1.is_prime.mem_or_mem h1 with h1|h2,
  { left,
    rw mem_carrier_iff,
    simp only [show (mk a1 ⟨f ^ n1, _⟩ : away f) = mk a1 1 * mk 1 ⟨f^n1, ⟨n1, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h1, rfl⟩), },
  { right,
    rw mem_carrier_iff,
    simp only [show (mk a2 ⟨f ^ n2, _⟩ : away f) = mk a2 1 * mk 1 ⟨f^n2, ⟨n2, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h2, rfl⟩), },
  { exact false.elim (x.2 (x.1.is_prime.mem_of_pow_mem N rid1)), },
  { exact false.elim (x.2 (x.1.is_prime.mem_of_pow_mem M rid2)), },
  { rw [mul_comm _ (f^N), eq1],
    refine mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ (λ i hi, mul_mem_left _ _ _))),
    generalize_proofs h,
    exact (classical.some_spec h).1 },
end⟩

/-
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map from `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in  `Proj A`. This lemma is used to prove that the
forward map is continuous.
-/
lemma preimage_eq (a : A) (n : ℕ)
  (a_mem_degree_zero : (mk a ⟨f ^ n, ⟨n, rfl⟩⟩ : away f) ∈ A⁰_ f_deg) :
  to_fun 𝒜 f_deg ⁻¹'
      ((sbo (⟨mk a ⟨f ^ n, ⟨_, rfl⟩⟩, a_mem_degree_zero⟩ : A⁰_ f_deg)) :
        set (prime_spectrum {x // x ∈ A⁰_ f_deg}))
  = {x | x.1 ∈ (pbo f) ⊓ (pbo a)} :=
begin
  classical,
  ext1 y, split; intros hy,
  { refine ⟨y.2, _⟩,
    rw [set.mem_preimage, opens.mem_coe, prime_spectrum.mem_basic_open] at hy,
    rw projective_spectrum.mem_coe_basic_open,
    intro a_mem_y,
    apply hy,
    rw [to_fun, mem_carrier_iff],
    simp only [show (mk a ⟨f^n, ⟨_, rfl⟩⟩ : away f) = mk 1 ⟨f^n, ⟨_, rfl⟩⟩ * mk a 1,
      by rw [mk_mul, one_mul, mul_one]],
    exact ideal.mul_mem_left _ _ (ideal.subset_span ⟨_, a_mem_y, rfl⟩), },
  { change y.1 ∈ _ at hy,
    rcases hy with ⟨hy1, hy2⟩,
    rw projective_spectrum.mem_coe_basic_open at hy1 hy2,
    rw [set.mem_preimage, to_fun, opens.mem_coe, prime_spectrum.mem_basic_open],
    intro rid,
    rcases mem_carrier.clear_denominator f_deg _ rid with ⟨c, N, acd, eq1⟩,
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
      generalize_proofs h,
      exact (classical.some_spec h).1, }, },
end

end to_Spec

section

variable {𝒜}

/--The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic
open set in `Spec A⁰_f`.
-/
def to_Spec {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj.T| (pbo f)) ⟶ (Spec.T (A⁰_ f_deg)) :=
{ to_fun := to_Spec.to_fun 𝒜 f_deg,
  continuous_to_fun := begin
    apply is_topological_basis.continuous (prime_spectrum.is_topological_basis_basic_opens),
    rintros _ ⟨⟨g, hg⟩, rfl⟩,
    induction g using localization.induction_on with data,
    obtain ⟨a, ⟨_, ⟨n, rfl⟩⟩⟩ := data,

    erw to_Spec.preimage_eq,
    refine is_open_induced_iff.mpr ⟨(pbo f).1 ⊓ (pbo a).1, is_open.inter (pbo f).2 (pbo a).2, _⟩,
    ext z, split; intros hz; simpa [set.mem_preimage],
  end }

end

end Proj_iso_Spec_Top_component

end algebraic_geometry
