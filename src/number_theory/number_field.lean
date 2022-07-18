/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/

import ring_theory.dedekind_domain.integral_closure
import algebra.char_p.algebra
import data.complex.basic

/-!
# Number fields
This file defines a number field, the ring of integers corresponding to it and includes some
basic facts about the embeddings into an algebraic closed field.

## Main definitions
 - `number_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

## Main Result
 - `eq_roots`: let `x ∈ K` with `K` number field and let `A` be an algebraic closed field of
    char. 0, then the images of `x` by the embeddings of `K` in `A` are exactly the roots in
    `A` of the minimal polynomial of `x` over `ℚ`.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
number field, ring of integers
-/

/-- A number field is a field which has characteristic zero and is finite
dimensional over ℚ. -/
class number_field (K : Type*) [field K] : Prop :=
[to_char_zero : char_zero K]
[to_finite_dimensional : finite_dimensional ℚ K]

open function
open_locale classical big_operators

/-- `ℤ` with its usual ring structure is not a field. -/
lemma int.not_is_field : ¬ is_field ℤ :=
λ h, int.not_even_one $ (h.mul_inv_cancel two_ne_zero).imp $ λ a, (by rw ← two_mul; exact eq.symm)

namespace number_field

variables (K L : Type*) [field K] [field L] [nf : number_field K]

include nf

-- See note [lower instance priority]
attribute [priority 100, instance] number_field.to_char_zero number_field.to_finite_dimensional

protected lemma is_algebraic : algebra.is_algebraic ℚ K := algebra.is_algebraic_of_finite _ _

omit nf

/-- The ring of integers (or number ring) corresponding to a number field
is the integral closure of ℤ in the number field. -/
def ring_of_integers := integral_closure ℤ K

localized "notation `𝓞` := number_field.ring_of_integers" in number_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 K ↔ is_integral ℤ x := iff.rfl

/-- Given an algebra between two fields, create an algebra between their two rings of integers.

For now, this is not an instance by default as it creates an equal-but-not-defeq diamond with
`algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on subtypes. This
will likely change in Lean 4. -/
def ring_of_integers_algebra [algebra K L] : algebra (𝓞 K) (𝓞 L) := ring_hom.to_algebra
{ to_fun := λ k, ⟨algebra_map K L k, is_integral.algebra_map k.2⟩,
  map_zero' := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_zero, map_zero],
  map_one'  := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_one, map_one],
  map_add' := λ x y, subtype.ext $ by simp only [map_add, subalgebra.coe_add, subtype.coe_mk],
  map_mul' := λ x y, subtype.ext $ by simp only [subalgebra.coe_mul, map_mul, subtype.coe_mk] }

namespace ring_of_integers

variables {K}

instance [number_field K] : is_fraction_ring (𝓞 K) K :=
integral_closure.is_fraction_ring_of_finite_extension ℚ _

instance : is_integral_closure (𝓞 K) ℤ K :=
integral_closure.is_integral_closure _ _

instance [number_field K] : is_integrally_closed (𝓞 K) :=
integral_closure.is_integrally_closed_of_finite_extension ℚ

lemma is_integral_coe (x : 𝓞 K) : is_integral ℤ (x : K) :=
x.2

/-- The ring of integers of `K` are equivalent to any integral closure of `ℤ` in `K` -/
protected noncomputable def equiv (R : Type*) [comm_ring R] [algebra R K]
  [is_integral_closure R ℤ K] : 𝓞 K ≃+* R :=
(is_integral_closure.equiv ℤ R K _).symm.to_ring_equiv

variables (K)

instance [number_field K] : char_zero (𝓞 K) := char_zero.of_module _ K

/-- The ring of integers of a number field is not a field. -/
lemma not_is_field [number_field K] : ¬ is_field (𝓞 K) :=
begin
  have h_inj : function.injective ⇑(algebra_map ℤ (𝓞 K)),
  { exact ring_hom.injective_int (algebra_map ℤ (𝓞 K)) },
  intro hf,
  exact int.not_is_field
    (((is_integral_closure.is_integral_algebra ℤ K).is_field_iff_is_field h_inj).mpr hf)
end

instance [number_field K] : is_dedekind_domain (𝓞 K) :=
is_integral_closure.is_dedekind_domain ℤ ℚ K _

end ring_of_integers

end number_field

namespace rat

open number_field

local attribute [instance] subsingleton_rat_module

instance number_field : number_field ℚ :=
{ to_char_zero := infer_instance,
  to_finite_dimensional :=
    -- The vector space structure of `ℚ` over itself can arise in multiple ways:
    -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
    -- all char 0 fields have a canonical embedding of `ℚ` (used in `number_field`).
    -- Show that these coincide:
    by convert (infer_instance : finite_dimensional ℚ ℚ), }

/-- The ring of integers of `ℚ` as a number field is just `ℤ`. -/
noncomputable def ring_of_integers_equiv : ring_of_integers ℚ ≃+* ℤ :=
ring_of_integers.equiv ℤ

end rat

namespace adjoin_root

section

open_locale polynomial

local attribute [-instance] algebra_rat
local attribute [instance] algebra_rat_subsingleton

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
instance {f : ℚ[X]} [hf : fact (irreducible f)] : number_field (adjoin_root f) :=
{ to_char_zero := char_zero_of_injective_algebra_map (algebra_map ℚ _).injective,
  to_finite_dimensional := by convert (adjoin_root.power_basis hf.out.ne_zero).finite_dimensional }
end

end adjoin_root

namespace number_field.embeddings

section fintype

open finite_dimensional

-- TODO : check explicit and implicit variables and open usage
variables (K : Type*) [field K] [number_field K]
variables (A : Type*) [field A] [char_zero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : fintype (K →+* A) := fintype.of_equiv (K →ₐ[ℚ] A)
ring_hom.equiv_rat_alg_hom.symm

variables [is_alg_closed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
lemma card : fintype.card (K →+* A) = finrank ℚ K :=
by rw [fintype.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, alg_hom.card]

end fintype

section roots

open set finite_dimensional polynomial

-- TODO. fix docstring, name of lemma, opens, arguments
/-- For `x ∈ K`, with `K` a number field, and `F` a sub-extension of `K`, the images of `x`
by the embeddings of `K` fixing `F` are exactly the roots of the minimal polynomial of `x`
over `F` -/
lemma range_eq_roots (F K A : Type*) [field F] [number_field F] [field K] [number_field K]
[field A] [is_alg_closed A] [algebra F K] [algebra F A] (x : K) :
range (λ ψ : K →ₐ[F] A, ψ x) = (minpoly F x).root_set A :=
begin
  haveI : finite_dimensional F K := finite_dimensional.right ℚ  _ _ ,
  have hx : is_integral F x := is_separable.is_integral F x,
  ext a, split,
  { rintro ⟨ψ, hψ⟩,
    rw [mem_root_set_iff, ←hψ],
    { rw aeval_alg_hom_apply ψ x (minpoly F x),
      simp only [minpoly.aeval, map_zero], },
    exact minpoly.ne_zero hx, },
  { intro ha,
    let Fx := adjoin_root (minpoly F x),
    haveI : fact (irreducible $ minpoly F x) := ⟨minpoly.irreducible hx⟩,
    have hK : (aeval x) (minpoly F x) = 0 := minpoly.aeval _ _,
    have hA : (aeval a) (minpoly F x) = 0,
    { rwa [aeval_def, ←eval_map, ←mem_root_set_iff'],
      exact polynomial.monic.ne_zero (polynomial.monic.map (algebra_map F A) (minpoly.monic hx)), },
    letI : algebra Fx A := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map F A) a hA),
    letI : algebra Fx K := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map F K) x hK),
    haveI : finite_dimensional Fx K := finite_dimensional.right ℚ  _ _ ,
    let ψ₀ : K →ₐ[Fx] A := is_alg_closed.lift (algebra.is_algebraic_of_finite _ _),
    haveI : is_scalar_tower F Fx K := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ _ hK),
    haveI : is_scalar_tower F Fx A := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ _ hA),
    let ψ : K →ₐ[F] A := alg_hom.restrict_scalars F ψ₀,
    refine ⟨ψ, _⟩,
    rw (_ : x = (algebra_map Fx K) (adjoin_root.root (minpoly F x))),
    rw (_ : a = (algebra_map Fx A) (adjoin_root.root (minpoly F x))),
    exact alg_hom.commutes _ _,
    exact (adjoin_root.lift_root hA).symm,
    exact (adjoin_root.lift_root hK).symm, },
end

variables (K A : Type*) [field K] [number_field K] [field A] [char_zero A] [is_alg_closed A] (x : K)

lemma rat_range_eq_roots :
range (λ φ : K →+* A, φ x) = (minpoly ℚ x).root_set A :=
begin
  convert range_eq_roots ℚ K A x using 1,
  ext a,
  exact ⟨λ ⟨φ, hφ⟩, ⟨φ.to_rat_alg_hom, hφ⟩, λ ⟨φ, hφ⟩, ⟨φ.to_ring_hom, hφ⟩⟩,
end

#lint

variables (a : A) (ha : a ∈ (minpoly ℚ x).root_set A)
include a ha

--noncomputable instance algK : algebra (adjoin_root(minpoly ℚ x)) K :=
--begin
--  have hK : (aeval x) (minpoly ℚ x) = 0 := minpoly.aeval _ _,
--  exact ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map ℚ K) x hK),
--end

noncomputable instance algA : algebra (adjoin_root(minpoly ℚ x)) A :=
begin
  have hx : is_integral ℚ x := is_separable.is_integral ℚ x,
  haveI : fact (irreducible $ minpoly ℚ x) := ⟨minpoly.irreducible hx⟩,
  have hA : (aeval a) (minpoly ℚ x) = 0,
  { rwa [aeval_def, ←eval_map, ←mem_root_set_iff'],
    exact polynomial.monic.ne_zero (polynomial.monic.map (algebra_map ℚ A) (minpoly.monic hx)), },
  exact ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map ℚ A) a hA),
end

def fix : {ψ : K →+* A | ψ x = a} ≃
  {φ : K →* A | φ ∘ algebra_map (adjoin_root(minpoly ℚ x)) K = algebra_map (adjoin_root(minpoly ℚ x)) A} :=
sorry

#exit

-- For fixed root a ∈ A, construct a map : { φ : K →+* A, φ x = a } → (K →ₐ[Qx] A)
-- Prove that it is a injective and surjective
lemma card_eq_rank : ∀ a ∈ (minpoly ℚ x).root_set A,
  fintype.card {φ : K →+* A | φ x = a} = finrank (algebra.adjoin ℚ ({x} : set K)) K :=
begin

  intros a ha,
  have hx : is_integral ℚ x := is_separable.is_integral ℚ x,
  let Qx := adjoin_root (minpoly ℚ x),
  haveI : fact (irreducible $ minpoly ℚ x) := ⟨minpoly.irreducible hx⟩,

  have hK : (aeval x) (minpoly ℚ x) = 0 := minpoly.aeval _ _,
  have hA : (aeval a) (minpoly ℚ x) = 0,
  { rwa [aeval_def, ←eval_map, ←mem_root_set_iff'],
    exact polynomial.monic.ne_zero (polynomial.monic.map (algebra_map ℚ A) (minpoly.monic hx)), },
  letI : algebra Qx A := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map ℚ A) a hA),
  letI : algebra Qx K := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map ℚ K) x hK),

  haveI : finite_dimensional Qx K := finite_dimensional.right ℚ  _ _,

  rw (_ : finrank (algebra.adjoin ℚ ({x} : set K)) K = fintype.card (K →ₐ[Qx] A)),
  { let S : (K →ₐ[Qx] A) → {φ : K →+* A | φ x = a} := λ ψ, ⟨ψ.to_ring_hom, _⟩,
    swap,
    { rw [alg_hom.to_ring_hom_eq_coe, mem_set_of_eq, alg_hom.coe_to_ring_hom],
      rw (_ : a = (algebra_map Qx A) (adjoin_root.root (minpoly ℚ x))),
      convert alg_hom.commutes _ _,
      exact (adjoin_root.lift_root hK).symm,
      exact (adjoin_root.lift_root hA).symm, },
    have S_inj : function.injective S,
    { intros φ₀ φ₁ h,
      ext t,
      simp only [alg_hom.to_ring_hom_eq_coe, subtype.mk_eq_mk] at *,
      exact ring_hom.ext_iff.mp h t, },
    have S_surj : function.surjective S,
    { rintros  ⟨φ, hφ⟩,
      letI : algebra K A := ring_hom.to_algebra φ,
      let pi := adjoin_root.power_basis (monic.ne_zero (minpoly.monic hx)),
      let ψ₀ : Qx →ₐ[ℚ] A := (ring_hom.comp (algebra_map K A) (algebra_map Qx K)).to_rat_alg_hom,
      let ψ₁ : Qx →ₐ[ℚ] A := (algebra_map Qx A).to_rat_alg_hom,
      have : ∀ r : Qx, ((algebra_map K A) ∘ (algebra_map Qx K)) r = (algebra_map Qx A) r,
      {
        suffices hpi : ((algebra_map K A) ∘ (algebra_map Qx K)) pi.gen = (algebra_map Qx A) pi.gen,
        {
          let ψ₀ : Qx →ₐ[ℚ] A := (ring_hom.comp (algebra_map K A) (algebra_map Qx K)).to_rat_alg_hom,
          let ψ₁ : Qx →ₐ[ℚ] A := (algebra_map Qx A).to_rat_alg_hom,
          rw (_ : ((algebra_map K A) ∘ (algebra_map Qx K)) pi.gen = ψ₀ pi.gen) at hpi,
          rw (_ : (algebra_map Qx A) pi.gen = ψ₁ pi.gen) at hpi,
          have : _, from power_basis.alg_hom_ext pi hpi,
          intro r,
          have : _, from alg_hom.ext_iff.mp this r,
          exact this,
          refl,
          refl,  },
        rw adjoin_root.power_basis_gen (monic.ne_zero (minpoly.monic hx)),
        rw ( _ : (algebra_map Qx A) (adjoin_root.root (minpoly ℚ x)) = a),
        rw function.comp,
        dsimp,
        rw ( _ : (algebra_map Qx K) (adjoin_root.root (minpoly ℚ x)) = x),
        exact hφ,
        exact (adjoin_root.lift_root hK),
        exact (adjoin_root.lift_root hA), },
        let ψ : K →ₐ[Qx] A := {
          to_fun := φ,
          map_one' := ring_hom.map_one _,
          map_mul' := ring_hom.map_mul _,
          map_zero' := ring_hom.map_zero _,
          map_add' := ring_hom.map_add _,
          commutes' := this,
        },
        refine ⟨ψ, _⟩,
        simp only [alg_hom.to_ring_hom_eq_coe, subtype.mk_eq_mk],
        ext,
        refl, },
    have : (K →ₐ[Qx] A) ≃ {φ : K →+* A | φ x = a} := equiv.of_bijective S ⟨S_inj, S_surj⟩,
    exact fintype.card_congr this.symm, },
  { have hh : _, from linear_equiv.finrank_eq
      (alg_equiv.to_linear_equiv (adjoin_root.minpoly.equiv_adjoin hx)),


    -- use the equiv directly
    rw alg_hom.card Qx K A,
    have hh : _, from linear_equiv.finrank_eq
      (alg_equiv.to_linear_equiv (adjoin_root.minpoly.equiv_adjoin hx)),
    have : finrank ℚ Qx ≠ 0, { sorry, },
    apply (mul_right_inj' this).mp,
    nth_rewrite 0 hh,
    haveI : finite_dimensional ℚ Qx := sorry,
    rw finite_dimensional.finrank_mul_finrank ℚ Qx K,
    haveI : field (algebra.adjoin ℚ ({x} : set K)) := sorry,
    letI : algebra ℚ (algebra.adjoin ℚ ({x} : set K)) := sorry,



    -- probably direct with the latest results
    sorry, },
end

end roots

#exit

section card

open set finite_dimensional polynomial

variables (K : Type*) [field K] [number_field K] (x : K)
variables (A : Type*) [field A] [char_zero A] [is_alg_closed A]

def aux : (K →+* A) → (K →+* A) → Prop := λ φ ψ, φ x = ψ x

lemma aux_equivalence : equivalence (aux K x A) :=
  ⟨λ φ, rfl, λ _ _ h, eq.symm h, λ _ _ _ h1 h2, eq.trans h1 h2⟩

def auxquot : setoid (K →+* A) := eqv_gen.setoid (aux K x A)

-- TODO. Fix statement
lemma card_eq_rank0 : ∀ a ∈ (minpoly ℚ x).root_set A,
  finrank (algebra.adjoin ℚ ({x} : set K)) K = fintype.card {φ : K →+* A | φ x = a}  :=
begin
  intros a ha,
  have hx : is_integral ℚ x := is_separable.is_integral ℚ x,
  haveI : fact (irreducible (minpoly ℚ x)) := ⟨minpoly.irreducible hx⟩,
  let Qx := adjoin_root (minpoly ℚ x),
  have hK : (aeval x) (minpoly ℚ x) = 0 := minpoly.aeval _ _,
  have hA : (aeval a) (minpoly ℚ x) = 0,
  { rwa [aeval_def, ←eval_map, ←mem_root_set_iff'],
    exact polynomial.monic.ne_zero (polynomial.monic.map (algebra_map ℚ A) (minpoly.monic hx)), },
  let φ₀ : Qx →+* A := by convert adjoin_root.lift (algebra_map ℚ A) a hA,
  letI : algebra Qx A := ring_hom.to_algebra φ₀,
  letI : algebra Qx K := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map ℚ K) x hK),



  suffices : ∀ a ∈ (minpoly ℚ x).root_set A,
    finrank (algebra.adjoin ℚ ({x} : set K)) K ≤ fintype.card {φ : K →+* A | φ x = a},
  { refine (finset.sum_eq_sum_iff_of_le _).mp _,
    exact this,
    rw finset.sum_const,
    rw algebra.id.smul_eq_mul,
    rw ( _ : (map (algebra_map ℚ A) (minpoly ℚ x)).roots.to_finset.card
      = finrank ℚ (algebra.adjoin ℚ ({x} : set K))),
    have : _, from rat_range_eq_roots K A x,
    sorry,
    sorry, },
  intros a ha,



  haveI : finite_dimensional Qx K,{ sorry, },
  have : fintype.card (K →ₐ[Qx] A) = finrank (algebra.adjoin ℚ ({x} : set K)) K,
  { convert alg_hom.card Qx K A,
    sorry, },
  rw ←this,
  let S : (K →ₐ[Qx] A) → {φ : K →+* A | φ x = a} := λ ψ, ⟨ψ.to_ring_hom, _⟩,
  refine fintype.card_le_of_injective S _,
  { intros ψ₀ ψ₁ h,
    ext k,
    simp only [subtype.mk_eq_mk, alg_hom.to_ring_hom_eq_coe] at h,
    exact congr_arg (λ (f : K →+* A), f k) h, },
  { show ψ x = a,
    convert alg_hom.commutes ψ (adjoin_root.root (minpoly ℚ x)),
    { exact (adjoin_root.lift_root hK).symm, },
    { exact (adjoin_root.lift_root hA).symm, }},
end

end card

section complex_case

variables {K : Type*} [comm_ring K]

open_locale complex_conjugate

variables (φ : K →* ℂ)

/-- An embedding is real if its fixed by complex conjugation-/
def is_real (φ : K →+* ℂ) : Prop := conj ∘ φ =  φ

/-- An embedding is real if its not fixed by complex conjugation-/
def is_complex (φ : K →+* ℂ) : Prop := conj ∘ φ ≠ φ

-- TODO. get complex embeddings modulo conj, prove the number of complex emb. is even
--       define the additive lattice embedding
--       define the complex lattice embedding

local notation `r1` := fintype.card { φ  : K →+* ℂ // is_real φ }
local notation `r2` := fintype.card { φ  : K →+* ℂ // is_complex φ } / 2

end complex_case

end number_field.embeddings
