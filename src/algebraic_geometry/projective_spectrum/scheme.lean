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
  - forward direction `to_Spec`:
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `x ∩ span {g / 1 | g ∈ A}` (see `Proj_iso_Spec_Top_component.to_Spec.carrier`). This ideal is
    prime, the proof is in `Proj_iso_Spec_Top_component.to_Spec.to_fun`. The fact that this function
    is continuous is found in `Proj_iso_Spec_Top_component.to_Spec`
  - backward direction `from_Spec`:
    for any `q : Spec A⁰_f`, we sent it to `{a | forall i, aᵢ^m/f^i ∈ q}`; we need this to be a
    homogeneous prime ideal that is relevant.
    * This is in fact an ideal, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal`;
    * This ideal is also homogeneous, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.as_ideal.homogeneous`;
    * This ideal is relavent, the proof can be found in
      `Proj_iso_Spec_Top_component.from_Spec.carrier.relavent`;
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

lemma degree_zero_part.coe_one {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) :
  (↑(1 : A⁰_ f_deg) : away f) = 1 := rfl

lemma degree_zero_part.coe_sum {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) {ι : Type*}
  (s : finset ι) (g : ι → A⁰_ f_deg) :
  (↑(∑ i in s, g i) : away f) = ∑ i in s, (g i : away f) :=
begin
  classical,
  induction s using finset.induction_on with i s hi ih;
  simp,
end

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

namespace from_Spec

open graded_algebra set_like finset (hiding mk_zero)

variables {𝒜} {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m}

private meta def mem_tac : tactic unit :=
let b : tactic unit :=
  `[exact pow_mem_graded _ (submodule.coe_mem _) <|> exact nat_cast_mem_graded _ _] in
b <|> `[by repeat { all_goals { apply graded_monoid.mul_mem } }; b]

/--The function from `Spec A⁰_f` to `Proj|D(f)` is defined by `q ↦ {a | aᵢᵐ ∈ q}`, i.e. send `q` a
prime ideal in `A⁰_f` to the homogeneous prime relevant ideal containing only and all the element
`a : A` such that the `m`-th power of `i`-th projection of `a` is in `q`.

Th set `{a | aᵢᵐ ∈ q}`
* is an ideal is proved in  `carrier.as_ideal`;
* is homogeneous is proved in `carrier.as_homogeneous_ideal`;
* is prime is proved in `carrier.as_ideal.prime`;
* is relevant is proved in `carrier.as_ideal.relevant`
-/
def carrier (q : Spec.T (A⁰_ f_deg)) : set A :=
{a | ∀ i, (⟨mk ((proj 𝒜 i a)^m) ⟨_, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ q.1 }

lemma mem_carrier_iff (q : Spec.T (A⁰_ f_deg)) (a : A) :
  a ∈ carrier q ↔
  ∀ i, (⟨mk ((proj 𝒜 i a)^m) ⟨_, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ q.1 :=
iff.rfl

lemma carrier.zero_mem (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) :
  (0 : A) ∈ carrier q := λ i,
by simpa only [linear_map.map_zero, zero_pow hm, mk_zero] using submodule.zero_mem _

lemma carrier.add_mem (q : Spec.T (A⁰_ f_deg)) {a b : A}
  (ha : a ∈ carrier q) (hb : b ∈ carrier q) :
  a + b ∈ carrier q :=
begin
  rw carrier at ha hb ⊢,
  intro i,
  set α := (⟨mk ((proj 𝒜 i (a + b))^m) ⟨f^i, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg),
  suffices : α * α ∈ q.1,
  { cases q.2.mem_or_mem this; assumption },
  rw show α * α =
  ⟨mk ((proj 𝒜 i (a + b))^(2*m)) ⟨f^(2*i), ⟨_, rfl⟩⟩,
    ⟨2 * i, ⟨_, by { rw show m * (2 * i) = (2 * m) * i, by ring, mem_tac }⟩, rfl⟩⟩,
  { rw [subtype.ext_iff, degree_zero_part.coe_mul],
    change localization.mk _ _ * mk _ _ = mk _ _,
    rw [mk_mul],
    congr' 1,
    { rw [two_mul, pow_add] },
    { simpa only [subtype.ext_iff, submonoid.coe_mul, two_mul, pow_add], } },
    clear α,

    set s := ∑ j in range (2*m+1), ((proj 𝒜 i) a)^j * ((proj 𝒜 i) b)^(2*m - j) * (2 * m).choose j,
    set s' := ∑ j in (range (2*m+1)).attach, (proj 𝒜 i a)^j.1 *
                (proj 𝒜 i b)^(2*m - j.1) * (2*m).choose j.1,
    have ss' : s = s',
    { symmetry, convert sum_attach, refl },
    have mem1 : (proj 𝒜 i) (a + b) ^ (2 * m) ∈ 𝒜 (m * (2 * i)),
    { rw show m * (2 * i) = (2 * m) * i, by ring, mem_tac },
    have eq1 : (proj 𝒜 i (a + b))^(2*m) = s,
    { rw [linear_map.map_add, add_pow] },
    rw calc (⟨mk ((proj 𝒜 i (a + b))^(2*m)) ⟨f^(2*i), ⟨_, rfl⟩⟩,
                ⟨2 * i, ⟨_, mem1⟩, rfl⟩⟩ : A⁰_ f_deg)
          = ⟨mk s ⟨f ^ (2 * i), ⟨_, rfl⟩⟩, ⟨2*i, ⟨s, eq1 ▸ mem1⟩, rfl⟩⟩ : by simp only [eq1]
      ... = ⟨mk s' ⟨f ^ (2 * i), ⟨_, rfl⟩⟩, ⟨2*i, ⟨s', ss' ▸ eq1 ▸ mem1⟩, rfl⟩⟩ : by congr' 2
      ... = ∑ j in (range (2 * m + 1)).attach,
              ⟨mk ((proj 𝒜 i a)^j.1 * (proj 𝒜 i b)^(2 * m - j.1) * (2 * m).choose j.1)
                ⟨f^(2 * i), ⟨2*i, rfl⟩⟩,
                ⟨_, ⟨_, begin
                  rw show m * (2 * i) = ((j.1*i) + (2*m-j.1)*i + 0),
                  { zify,
                    rw [show (↑(2 * m - j.1) : ℤ) = 2 * m - j.1, from _, sub_mul, add_zero],
                    { ring },
                    { rw [eq_sub_iff_add_eq, ←int.coe_nat_add, nat.sub_add_cancel
                        (nat.lt_succ_iff.mp (mem_range.mp j.2))],
                      refl, }, },
                  mem_tac,
                end⟩, rfl⟩⟩
          : begin
              rw [subtype.ext_iff, degree_zero_part.coe_sum],
              change localization.mk _ _ = ∑ _, mk _ _,
              rw [localization.mk_sum, univ_eq_attach],
            end,
    clear' s s' ss' eq1,
    apply ideal.sum_mem,
    intros k hk,
    by_cases ineq : m ≤ k.1,
    { -- use (proj 𝒜 i) a ^ k
      set α := (⟨mk ((proj 𝒜 i) a ^ m) ⟨f^i, ⟨i, rfl⟩⟩, ⟨i, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg),
      set β := (⟨mk ((proj 𝒜 i) a ^ (k.val - m) *
          (proj 𝒜 i) b ^ (2 * m - k.val) * (2*m).choose k.1) ⟨f^i, ⟨i, rfl⟩⟩, begin
            refine ⟨i, ⟨_, _⟩, rfl⟩,
            rw show m * i = ((k.val - m) * i) + ((2*m-k.1) * i) + 0,
            { rw [add_zero, ←add_mul],
              congr' 1,
              symmetry,
              exact calc k.val - m + (2*m - k.val)
                        = (k.val + (2 * m - k.1)) - m : by { rw nat.sub_add_comm ineq, }
                    ... = (k.1 + 2 * m) - k.1 - m
                        : begin
                          rw ←nat.add_sub_assoc,
                          have hk := k.2,
                          rw [finset.mem_range, nat.lt_succ_iff] at hk,
                          exact hk,
                        end
                    ... = 2 * m - m : by { rw nat.add_sub_cancel_left k.1 (2*m), }
                    ... = m + m - m : by { rw two_mul, }
                    ... = m : by rw nat.add_sub_cancel, },
            mem_tac,
          end⟩ : A⁰_ f_deg),
      suffices : α * β ∈ q.1,
      { convert this,
        rw [mk_mul],
        congr' 1,
        { simp only [← mul_assoc],
          congr' 2,
          rw [← pow_add],
          congr' 1,
          symmetry,
          exact calc m + (k.1 - m)
                    = m + k.1 - m : by erw ←nat.add_sub_assoc ineq
                ... = k.1 + m - m : by rw nat.add_comm
                ... = k.1 + (m-m) : by erw nat.add_sub_assoc (le_refl _)
                ... = k.1 + 0 : by rw nat.sub_self
                ... = k.1 : by rw add_zero },
        { simp only [two_mul, pow_add], refl, } },
      exact ideal.mul_mem_right _ _ (ha _), },

    { set α := (⟨mk ((proj 𝒜 i) b ^ m) ⟨f^i, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg),
      set β := (⟨mk ((proj 𝒜 i) a ^ k.val * (proj 𝒜 i) b ^ (m - k.val) * ((2 * m).choose k.val))
        ⟨f^i, ⟨_, rfl⟩⟩, begin
          refine ⟨_, ⟨_, _⟩, rfl⟩,
          rw ← show k.1 * i + (m - k.1) * i + 0 = m * i,
          { exact calc k.1 * i + (m - k.1) * i + 0
                    = k.1 * i + (m - k.1) * i : by { rw add_zero }
                ... = (k.1 + (m - k.1)) * i : by { rw add_mul, }
                ... = (k.1 + m - k.1) * i
                      : begin
                        rw nat.add_sub_assoc,
                        rw not_le at ineq,
                        apply le_of_lt,
                        exact ineq,
                      end
                ... = m * i : by rw nat.add_sub_cancel_left, },
          mem_tac,
        end⟩ : A⁰_ f_deg),
      suffices : α * β ∈ q.1,
      { convert this,
        rw [localization.mk_mul],
        congr' 1,
        { rw show ∀ (a b c d : A), a * (b * c * d) = b * (a * c) * d, by {intros, ring},
          congr,
          rw [←pow_add, ← nat.add_sub_assoc (by linarith : k.1 ≤ m), ←two_mul], },
        { simpa only [two_mul, pow_add], } },
      exact ideal.mul_mem_right _ _ (hb _), },
end

lemma carrier.smul_mem (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) (c x : A) (hx : x ∈ carrier q) :
  c • x ∈ carrier q :=
begin
  classical,
  let 𝒜' : ℕ → add_submonoid A := λ i, (𝒜 i).to_add_submonoid,
  letI : graded_ring 𝒜' :=
    { decompose' := (direct_sum.decompose 𝒜 : A → ⨁ i, 𝒜 i),
      left_inv := direct_sum.decomposition.left_inv,
      right_inv := direct_sum.decomposition.right_inv,
      ..(by apply_instance : graded_monoid 𝒜), },
  have mem_supr : ∀ x, x ∈ supr 𝒜',
  { intro x,
    rw direct_sum.is_internal.add_submonoid_supr_eq_top 𝒜'
      (direct_sum.decomposition.is_internal 𝒜'),
    exact add_submonoid.mem_top x },

  refine add_submonoid.supr_induction 𝒜' (mem_supr c) (λ n a ha, _) _ _,
  { intros i,
    by_cases ineq1 : n ≤ i,
    { have eq1 : (graded_algebra.proj 𝒜 i) (a * x) =
          ite (i - n ∈ (direct_sum.decompose_alg_equiv 𝒜 x).support)
            (a * (graded_algebra.proj 𝒜 (i - n)) x) 0,
      { have := @direct_sum.coe_decompose_mul_add_of_left_mem _ _ _ _ _ _ _ _ 𝒜 _ a x _ (i - n) ha,
        rw [show n + (i - n) = i, by linarith] at this,
        rw [proj_apply, this],
        split_ifs,
        { refl, },
        { rw dfinsupp.mem_support_iff at h,
          push_neg at h,
          erw [h, mul_zero], } },

      split_ifs at eq1,
      { generalize_proofs h1 h2,
        erw calc
                (⟨mk ((proj 𝒜 i) (a * x) ^ m) ⟨f ^ i, h1⟩, h2⟩ : A⁰_ f_deg)
              = (⟨mk ((a * (proj 𝒜 (i - n) x))^m) ⟨f ^ i, h1⟩, eq1 ▸ h2⟩ : A⁰_ f_deg)
              : by { simp only [subtype.ext_iff_val, eq1], }
          ... = (⟨localization.mk ((a^m * (graded_algebra.proj 𝒜 (i - n) x)^m))
                  ⟨f^i, h1⟩, by { rw [←mul_pow, ←eq1], exact h2 }⟩ : A⁰_ f_deg)
              : begin
                rw subtype.ext_iff_val,
                dsimp only,
                rw mul_pow,
              end
          ... = (⟨mk (a^m) ⟨f^n, ⟨_, rfl⟩⟩,
                  ⟨n, ⟨a^m, pow_mem_graded m ha⟩, rfl⟩⟩ : A⁰_ f_deg) *
                ⟨mk ((proj 𝒜 (i-n) x)^m) ⟨f^(i-n), ⟨_, rfl⟩⟩,
                  ⟨_, ⟨(proj 𝒜 (i-n) x)^m, pow_mem_graded _ (submodule.coe_mem _)⟩, rfl⟩⟩
              : begin
                rw [subtype.ext_iff, degree_zero_part.coe_mul],
                change localization.mk _ _ = mk _ _ * mk _ _,
                rw [localization.mk_mul],
                congr',
                dsimp only,
                rw ←pow_add,
                congr',
                rw [←nat.add_sub_assoc, add_comm, nat.add_sub_assoc, nat.sub_self, add_zero],
                refl,
                exact ineq1,
              end,
        exact ideal.mul_mem_left _ _ (hx _), },
      { simp only [smul_eq_mul, eq1, zero_pow hm, localization.mk_zero], exact zero_mem _ } },
    { -- in this case, the left hand side is zero
      rw not_le at ineq1,
      convert submodule.zero_mem _,
      suffices : graded_algebra.proj 𝒜 i (a • x) = 0,
      { erw [this, zero_pow hm, localization.mk_zero] },

      rw [← sum_support_decompose 𝒜 x, smul_eq_mul, finset.mul_sum, linear_map.map_sum],
      convert finset.sum_eq_zero (λ j hj, _),
      exact decompose_of_mem_ne 𝒜 (mul_mem ha (submodule.coe_mem _)) (by linarith) } },
  { rw zero_smul, exact carrier.zero_mem hm _, },
  { intros a b ha hb,
    rw add_smul,
    apply carrier.add_mem q ha hb, },
end

/--
For a prime ideal `q` in `A⁰_f`, the set `{a | aᵐᵢ ∈ q }` as an ideal.
-/
def carrier.as_ideal (hm : 0 < m) (q : Spec.T (A⁰_ f_deg) ) :
  ideal A :=
{ carrier := carrier q,
  zero_mem' := carrier.zero_mem hm q,
  add_mem' := λ a b, carrier.add_mem q,
  smul_mem' := carrier.smul_mem hm q }

lemma carrier.as_ideal.homogeneous  (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) :
  (carrier.as_ideal hm q).is_homogeneous 𝒜  :=
begin
  intros i a ha,
  rw ←graded_algebra.proj_apply,
  change (proj _ i a) ∈ carrier q,
  change a ∈ carrier q at ha,
  intros j,
  erw calc (⟨mk ((proj 𝒜 j (proj 𝒜 i a))^m) ⟨_, ⟨_, rfl⟩⟩, ⟨j, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg)
        = ⟨mk ((ite (j = i) (proj 𝒜 j a) 0)^m) ⟨f^j, ⟨_, rfl⟩⟩,
            ⟨j, ⟨((ite (j = i) (proj 𝒜 j a) 0)^m), by exact pow_mem_graded m
                (show ite (j = i) ((proj 𝒜 j) a) 0 ∈ 𝒜 j, by split_ifs; tidy)⟩, rfl⟩⟩
          : begin
            rw [subtype.ext_iff],
            congr',
            split_ifs with eq1,
            { rw [graded_algebra.proj_apply, graded_algebra.proj_apply, eq1],
              exact direct_sum.decompose_of_mem_same _ (submodule.coe_mem _), },
            exact direct_sum.decompose_of_mem_ne 𝒜 (submodule.coe_mem _) (ne.symm eq1),
          end
    ... = ⟨localization.mk ((ite (j = i) ((graded_algebra.proj 𝒜 j a)^m) 0))
          ⟨f^j, ⟨_, rfl⟩⟩, ⟨j, ⟨(ite (j = i) ((graded_algebra.proj 𝒜 j a)^m) 0),
            by { split_ifs, mem_tac, exact submodule.zero_mem _ }⟩, rfl⟩⟩
          : by { split_ifs, refl, rw zero_pow hm }
    ... = ite (j = i) ⟨mk ((proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by mem_tac⟩, rfl⟩⟩ 0
          : begin
            split_ifs with H,
            { erw H },
            { simpa only [localization.mk_zero], },
          end,
    split_ifs with H,
    { apply ha, },
    { exact submodule.zero_mem _, },
end

/--
For a prime ideal `q` in `A⁰_f`, the set `{a | aᵐᵢ ∈ q }` as a homogeneous ideal.
-/
def carrier.as_homogeneous_ideal (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) : homogeneous_ideal 𝒜 :=
⟨carrier.as_ideal hm q, carrier.as_ideal.homogeneous hm q⟩

lemma carrier.denom_not_mem (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) : f ∉ carrier.as_ideal hm q :=
λ rid, q.is_prime.ne_top $ (ideal.eq_top_iff_one _).mpr
begin
  convert rid m,
  rw [subtype.ext_iff, degree_zero_part.coe_one],
  change (1 : away f) = mk _ _,
  rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same _ f_deg],
  exact (localization.mk_self (⟨_, ⟨m, rfl⟩⟩ : submonoid.powers f)).symm,
end

lemma carrier.relevant (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) :
  ¬ homogeneous_ideal.irrelevant 𝒜 ≤ carrier.as_homogeneous_ideal hm q :=
λ rid, carrier.denom_not_mem hm q $ rid $ direct_sum.decompose_of_mem_ne 𝒜 f_deg $ by linarith

lemma carrier.as_ideal.prime (hm : 0 < m)
  (q : Spec.T (A⁰_ f_deg)) : (carrier.as_ideal hm q).is_prime :=
begin
  apply (carrier.as_ideal.homogeneous hm q).is_prime_of_homogeneous_mem_or_mem,
  { intro rid,
    rw ideal.eq_top_iff_one at rid,
    apply q.is_prime.1,
    rw ideal.eq_top_iff_one,
    specialize rid 0,
    have eq1 : proj 𝒜 0 1 = 1,
    { rw [proj_apply, decompose_of_mem_same], exact one_mem, },
    simp only [eq1, one_pow] at rid,
    convert rid,
    rw [subtype.ext_iff, degree_zero_part.coe_one],
    change (1 : away f) = mk 1 _,
    simp only [pow_zero],
    convert ←localization.mk_one.symm, },
  { -- homogeneously prime
    rintros x y ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy,
    contrapose hxy,
    rw not_or_distrib at hxy,
    rcases hxy with ⟨hx, hy⟩,
    erw not_forall at hx hy,
    obtain ⟨ix, hix⟩ := hx,
    obtain ⟨iy, hiy⟩ := hy,
    intro rid,
    specialize rid (nx + ny),
    have eqx : nx = ix,
    { by_contra rid,
      apply hix,
      convert submodule.zero_mem _,
      rw [proj_apply, decompose_of_mem_ne 𝒜 hnx rid, zero_pow hm, localization.mk_zero], },
    have eqy : ny = iy,
    { by_contra rid,
      apply hiy,
      convert submodule.zero_mem _,
      rw [proj_apply, decompose_of_mem_ne 𝒜 hny rid, zero_pow hm, localization.mk_zero], },
    rw ←eqx at hix,
    rw ←eqy at hiy,

    have eqx2 : (⟨mk ((proj 𝒜 nx) x ^ m) ⟨_, ⟨_, rfl⟩⟩, ⟨nx, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg) =
    ⟨mk (x^m) ⟨f^nx, ⟨_, rfl⟩⟩, ⟨nx, ⟨_, by exact pow_mem_graded m hnx⟩, rfl⟩⟩,
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rwa [proj_apply, decompose_of_mem_same], },
    rw eqx2 at hix,

    have eqy2 : (⟨mk ((proj 𝒜 ny) y ^ m) ⟨_, ⟨_, rfl⟩⟩, ⟨ny, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg) =
      ⟨mk (y^m) ⟨f^ny, ⟨_, rfl⟩⟩, ⟨ny, ⟨_, by exact pow_mem_graded _ hny⟩, rfl⟩⟩,
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rwa [proj_apply, decompose_of_mem_same], },
    erw eqy2 at hiy,

    rw show (⟨mk ((proj 𝒜 (nx+ny)) (x*y)^m) ⟨_, ⟨_, rfl⟩⟩, ⟨_, ⟨_, by mem_tac⟩, rfl⟩⟩ : A⁰_ f_deg) =
      ⟨mk ((x*y)^m) ⟨f^(nx+ny), ⟨_, rfl⟩⟩, ⟨_, ⟨_, pow_mem_graded _ (mul_mem hnx hny)⟩, rfl⟩⟩,
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same],
      apply graded_monoid.mul_mem hnx hny, } at rid,

    rw show (⟨mk ((x*y)^m) ⟨_, ⟨_, rfl⟩⟩, ⟨_, ⟨_, pow_mem_graded _ (mul_mem hnx hny)⟩, rfl⟩⟩: A⁰_ _)
      = (⟨mk (x^m) ⟨f^nx, ⟨_, rfl⟩⟩, ⟨nx, ⟨_, pow_mem_graded _ hnx⟩, rfl⟩⟩ : A⁰_ f_deg) *
        (⟨mk (y^m) ⟨f^ny, ⟨_, rfl⟩⟩, ⟨ny, ⟨_, pow_mem_graded _ hny⟩, rfl⟩⟩ : A⁰_ f_deg),
    { rw [subtype.ext_iff, degree_zero_part.coe_mul],
      change localization.mk _ _ = mk _ _ * mk _ _,
      rw [localization.mk_mul],
      congr';
      ring_exp, } at rid,

    cases ideal.is_prime.mem_or_mem (q.is_prime) rid;
    tauto, },
end

variable (f_deg)
/--
The function `Spec A⁰_f → Proj|D(f)` by sending `q` to `{a | aᵐᵢ ∈ q}`.
-/
def to_fun (hm : 0 < m) : (Spec.T (A⁰_ f_deg)) → (Proj.T| (pbo f)) :=
λ q, ⟨⟨carrier.as_homogeneous_ideal hm q, carrier.as_ideal.prime hm q, carrier.relevant hm q⟩,
  (projective_spectrum.mem_basic_open _ f _).mp $ carrier.denom_not_mem hm q⟩

end from_Spec

end Proj_iso_Spec_Top_component

end algebraic_geometry
