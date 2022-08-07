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

open set polynomial

/-- Let `A` an algebraically closed field and let `x ∈ K`, with `K` a number field. For `F`,
subfield of `K`, the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
the roots in `A` of the minimal polynomial of `x` over `F` -/
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
      exact monic.ne_zero (monic.map (algebra_map F A) (minpoly.monic hx)), },
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

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ` -/
lemma rat_range_eq_roots :
range (λ φ : K →+* A, φ x) = (minpoly ℚ x).root_set A :=
begin
  convert range_eq_roots ℚ K A x using 1,
  ext a,
  exact ⟨λ ⟨φ, hφ⟩, ⟨φ.to_rat_alg_hom, hφ⟩, λ ⟨φ, hφ⟩, ⟨φ.to_ring_hom, hφ⟩⟩,
end

end roots

end number_field.embeddings
