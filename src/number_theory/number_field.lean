/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Anne Baanen
-/

import ring_theory.dedekind_domain.integral_closure
import algebra.char_p.algebra
import analysis.complex.polynomial

/-!
# Number fields
This file defines a number field, the ring of integers corresponding to it and includes some
basic facts about the embeddings into `ℂ` of a number field.

## Main definitions
 - `number_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.

## Main Results
 - `lift`: for `L/K` an extension of number fields, any embedding of a number field `K`
    can be lifted to an embedding of `L`.
 - `eq_roots`: let `x ∈ K` with `K` number field, then the images of `x` by the embeddings
    of `K` are exactly the roots in `ℂ` of the minimal polynomial of `x` over `ℚ`.

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

instance rat.number_field : number_field ℚ :=
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

/-- The quotient of `ℚ[X]` by the ideal generated by an irreducible polynomial of `ℚ[X]`
is a number field. -/
instance {f : ℚ[X]} [hf : irreducible f] : number_field (adjoin_root f) :=
{ to_char_zero := char_zero_of_injective_algebra_map (algebra_map ℚ _).injective,
  to_finite_dimensional := begin
   let := (adjoin_root.power_basis (irreducible.ne_zero hf : f ≠ 0)),
   convert power_basis.finite_dimensional this,
   haveI : subsingleton (algebra ℚ (adjoin_root f)) := algebra_rat_subsingleton,
   exact subsingleton.elim _ _,
  end }

end

end adjoin_root

namespace number_field.embeddings

open set finite_dimensional complex
open_locale complex_conjugate

variables {K L : Type*} [field K] [field L]
section number_field
variables [number_field K] [number_field L]  (x : K)

/-- The equivalence between algebra maps from a number field to `ℂ` and plain
ring morphisms between them. -/
noncomputable def equiv_alg : (K →ₐ[ℚ] ℂ) ≃ (K →+* ℂ) :=
{ to_fun := coe,
  inv_fun := λ f : K →+* ℂ, alg_hom.mk' f (λ (c : ℚ) x, map_rat_smul f _ _),
  left_inv  := λ x, alg_hom.ext  $ by simp only [forall_const, alg_hom.coe_to_ring_hom,
                                                 eq_self_iff_true, alg_hom.coe_mk'],
  right_inv := λ x, ring_hom.ext $ by simp only [forall_const, alg_hom.coe_to_ring_hom,
                                                 eq_self_iff_true, alg_hom.coe_mk'] }

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : fintype (K →+* ℂ) := fintype.of_equiv (K →ₐ[ℚ] ℂ) equiv_alg

/-- The number of embeddings of a number field is its finrank. -/
lemma card_embeddings : fintype.card (K →+* ℂ) = finrank ℚ K :=
by rw [fintype.of_equiv_card equiv_alg, alg_hom.card]

open polynomial

/-- Any embeddings of a number field `K` can be extended to an embedding of an extension `L`. -/
lemma lift {L : Type*} [field L] [number_field L] [algebra K L] (φ : K →+* ℂ) :
  ∃ ψ : L →+* ℂ, φ = ψ.comp (algebra_map K L) :=
begin
  letI : algebra K ℂ, from ring_hom.to_algebra φ,
  letI : is_alg_closed ℂ, from complex.is_alg_closed,
  have hS : algebra.is_algebraic K L,
  { show ∀ (a : L), is_algebraic K a,
    intro a,
    obtain ⟨p, hp⟩ := (number_field.is_algebraic L) a,
    haveI : algebra ℚ K, { exact algebra_rat },
    use (map (algebra_map ℚ K) p),
    split,
    simp only [ne.def, map_eq_zero, not_false_iff, hp.left],
    simp only [aeval_map, map_zero, hp.right], },
  let ψ₀ : L →ₐ[K] ℂ := is_alg_closed.lift hS,
  let ψ := ψ₀.to_ring_hom,
  use ψ,
  refine fun_like.ext φ (ψ.comp (algebra_map K L)) _,
  intro x,
  show φ x = ψ₀ ((algebra_map K L) x),
  rw alg_hom.commutes ψ₀ x,
  exact rfl,
end

/-- For `x ∈ K`, with `K` a number field, the images of `x` by the embeddings of `K` are exactly
the roots of the minimal polynomial of `x` over `ℚ` -/
lemma eq_roots : range (λ φ : K →+* ℂ, φ x) = (minpoly ℚ x).root_set ℂ :=
begin
  have hx : is_integral ℚ x, { exact is_separable.is_integral ℚ x },
  ext a,
  split,
  { rintro ⟨φ, hφ⟩,
    rw [mem_root_set_iff, ←hφ],
    let ψ := ring_hom.to_rat_alg_hom φ,
    show (aeval (ψ x)) (minpoly ℚ x) = 0,
    { rw aeval_alg_hom_apply ψ x (minpoly ℚ x),
      simp only [minpoly.aeval, map_zero] },
    exact minpoly.ne_zero hx, },
  { intro ha,
    let Qx := adjoin_root (minpoly ℚ x),
    haveI : irreducible (minpoly ℚ x), { exact minpoly.irreducible hx },
    haveI : number_field Qx := by apply_instance,
    have hK : (aeval x) (minpoly ℚ x) = 0, { exact minpoly.aeval _ _, },
    have hC : (aeval a) (minpoly ℚ x) = 0,
    { rw [aeval_def, ←eval_map, ←mem_root_set_iff'],
      exact ha,
      suffices : (minpoly ℚ x) ≠ 0,
      { contrapose! this,
        simp only [polynomial.ext_iff, coeff_map, coeff_zero] at this ⊢,
        suffices inj : function.injective (algebra_map ℚ ℂ),
        { exact λ n : ℕ, inj (by rw [(this n), (algebra_map ℚ ℂ).map_zero]),},
        exact (algebra_map ℚ ℂ).injective, },
      exact minpoly.ne_zero hx, },
    let ψ : Qx →+* ℂ := adjoin_root.lift (algebra_map ℚ ℂ) a hC,
    letI : algebra Qx K,
    { exact ring_hom.to_algebra (adjoin_root.lift (algebra_map ℚ K) x hK), },
    obtain ⟨φ, hφ⟩ := lift ψ,
    use φ,
    rw (_ : x = (algebra_map Qx K) (adjoin_root.root (minpoly ℚ x))),
    rw (_ : a = ψ (adjoin_root.root (minpoly ℚ x))),
    simp only [congr_fun, hφ, ring_hom.coe_comp],
    exact (adjoin_root.lift_root hC).symm,
    exact (adjoin_root.lift_root hK).symm,
    apply_instance, },
end

end number_field

variables (φ : K →* ℂ)

/-- An embedding is real if its fixed by complex conjugation. -/
def is_real (φ : K →+* ℂ) : Prop := conj ∘ φ = φ

/-- An embedding is real if its not fixed by complex conjugation. -/
def is_complex (φ : K →+* ℂ) : Prop := conj ∘ φ ≠ φ

/-- Two embeddings are conjuate if `conj` takes one to the other. -/
def are_conj (φ θ : K →+* ℂ) : Prop := conj ∘ φ = θ

/-- An element of a number field is real if its image under any embedding is fixed by conj. -/
def element_is_real (x : K) : Prop := ∀ φ : K →+* ℂ, conj (φ x) = φ x

local notation `r1` := fintype.card { φ  : K →+* ℂ // is_real φ }

local notation `c2` := fintype.card { φ  : K →+* ℂ // is_complex φ }

lemma not_real_eq_complex (φ : K →+* ℂ) : is_real φ ↔ ¬ is_complex φ :=
begin
  rw [is_real, is_complex],
  simp only [not_not],
end

lemma real_eq_rank_sub_complex [number_field K] :
  r1 = finrank ℚ K  - c2 :=
begin
  rw ← card_embeddings,
  simp_rw not_real_eq_complex,
  exact fintype.card_subtype_compl _,
end

lemma elem_is_real_is_real (x : K) (h : element_is_real x) :
   ∀  φ : K →+* ℂ, ∃ (r : ℝ), φ x = (r : ℂ) :=
begin
  intro φ,
  simp_rw [element_is_real] at h,
  have h1 := h φ,
  rw eq_conj_iff_real at h1,
  exact h1,
end

end number_field.embeddings

namespace number_field

open number_field.embeddings

/-- A number field all of whose embeddings are real. -/
def is_totally_real {K : Type*} [field K] : Prop := ∀ φ : K →+* ℂ, is_real φ

/-- A number field all of whose embeddings are complex. -/
def is_totally_complex {K : Type*} [field K] : Prop := ∀ φ : K →+* ℂ, is_complex φ

end number_field
