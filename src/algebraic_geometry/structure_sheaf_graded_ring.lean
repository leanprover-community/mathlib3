/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_geometry.prime_spectrum_graded_ring
import algebra.category.CommRing.colimits
import algebra.category.CommRing.limits
import topology.sheaves.local_predicate
import ring_theory.localization
import ring_theory.subring

/-!
# The structure sheaf on `prime_spectrum R`.

We define the structure sheaf on `Top.of (prime_spectrum R)`, for a commutative ring `R` and prove
basic properties about it. We define this as a subsheaf of the sheaf of dependent functions into the
localizations, cut out by the condition that the function must be locally equal to a ratio of
elements of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `topology.sheaves.sheaf_of_functions`,
where we show that dependent functions into any type family form a sheaf,
and also `topology.sheaves.local_predicate`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

We also set up the ring structure, obtaining
`structure_sheaf R : sheaf CommRing (Top.of (prime_spectrum R))`.

We then construct two basic isomorphisms, relating the structure sheaf to the underlying ring `R`.
First, `structure_sheaf.stalk_iso` gives an isomorphism between the stalk of the structure sheaf
at a point `p` and the localization of `R` at the prime ideal `p`. Second,
`structure_sheaf.basic_open_iso` gives an isomorphism between the structure sheaf on `basic_open f`
and the localization of `R` at the submonoid of powers of `f`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


noncomputable theory

open_locale classical direct_sum big_operators pointwise
open direct_sum

variables {ι : Type*} [linear_ordered_cancel_add_comm_monoid ι]
variables (A : ι → Type*) [Π i, add_comm_group (A i)] [gcomm_semiring A]

open Top
open topological_space
open category_theory
open opposite

namespace algebraic_geometry

/--
The prime spectrum, just as a topological space.
-/
def prime_spectrum_of_graded_ring.Top : Top := Top.of (prime_spectrum_of_graded_ring A)

namespace structure_sheaf

/--
The type family over `prime_spectrum R` consisting of the localization over each point.
-/
@[derive [comm_ring, local_ring]]
def localizations (P : prime_spectrum_of_graded_ring.Top A) := localization.at_prime P.as_ideal

instance (P : prime_spectrum_of_graded_ring.Top A) : inhabited (localizations A P) :=
⟨1⟩

instance (U : opens (prime_spectrum_of_graded_ring.Top A)) (x : U) :
  algebra (⨁ i, A i) (localizations A x) :=
localization.algebra

instance (U : opens (prime_spectrum_of_graded_ring.Top A)) (x : U) :
  is_localization.at_prime (localizations A x) (x : prime_spectrum_of_graded_ring.Top A).as_ideal :=
localization.is_localization

variables {A}

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (prime_spectrum_of_graded_ring.Top A)}
  (f : Π x : U, localizations A x) : Prop :=
∃ (r s : (⨁ i, A i)), ∀ x : U,
  ¬ (s ∈ x.1.as_ideal) ∧ f x * algebra_map _ _ s = algebra_map _ _ r

lemma is_fraction.eq_mk' {U : opens (prime_spectrum_of_graded_ring.Top A)}
  {f : Π x : U, localizations A x}
  (hf : is_fraction f) :
  ∃ (r s : (⨁ i, A i)) , ∀ x : U, ∃ (hs : s ∉ x.1.as_ideal), f x =
    is_localization.mk' (localization.at_prime _) r
      (⟨s, hs⟩ : (x : prime_spectrum_of_graded_ring.Top A).as_ideal.prime_compl) :=
begin
  rcases hf with ⟨r, s, h⟩,
  refine ⟨r, s, λ x, ⟨(h x).1, (is_localization.mk'_eq_iff_eq_mul.mpr _).symm⟩⟩,
  exact (h x).2.symm,
end

variables (A)

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (localizations A) :=
{ pred := λ U f, is_fraction f,
  res := by { rintro V U i f ⟨r, s, w⟩, exact ⟨r, s, λ x, w (i x)⟩ } }

/--
We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $U ⊆ Spec A$, we define $𝒪(U)$ to be the set of functions
$s : U → ⨆_{𝔭 ∈ U} A_𝔭$, such that $s(𝔭) ∈ A_𝔭$ for each $𝔭$,
and such that $s$ is locally a quotient of elements of $A$:
to be precise, we require that for each $𝔭 ∈ U$, there is a neighborhood $V$ of $𝔭$,
contained in $U$, and elements $a, f ∈ A$, such that for each $𝔮 ∈ V, f ∉ 𝔮$,
and $s(𝔮) = a/f$ in $A_𝔮$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, localizations x`.
-/
def is_locally_fraction : local_predicate (localizations A) :=
(is_fraction_prelocal A).sheafify

@[simp]
lemma is_locally_fraction_pred
  {U : opens (prime_spectrum_of_graded_ring.Top A)} (f : Π x : U, localizations A x) :
  (is_locally_fraction A).pred f =
  ∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : (⨁ i, A i)), ∀ y : V,
  ¬ (s ∈ y.1.as_ideal) ∧
    f (i y : U) * algebra_map _ _ s = algebra_map _ _ r :=
rfl

/--
The functions satisfying `is_locally_fraction` form a subring.
-/
def sections_subring (U : (opens (prime_spectrum_of_graded_ring.Top A))ᵒᵖ) :
  subring (Π x : unop U, localizations A x) :=
{ carrier := { f | (is_locally_fraction A).pred f },
  zero_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 0, 1, λ y, ⟨_, _⟩⟩,
    { rw ←ideal.ne_top_iff_one, exact y.1.is_prime.1, },
    { simp, },
  end,
  one_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 1, 1, λ y, ⟨_, _⟩⟩,
    { rw ←ideal.ne_top_iff_one, exact y.1.is_prime.1, },
    { simp, },
  end,
  add_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * sb + rb * sa, sa * sb, _⟩,
    intro y,
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩,
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩,
    fsplit,
    { intro H, cases y.1.is_prime.mem_or_mem H; contradiction, },
    { simp only [add_mul, ring_hom.map_add, pi.add_apply, ring_hom.map_mul],
      erw [←wa, ←wb],
      simp only [mul_assoc],
      congr' 2,
      rw [mul_comm], refl, }
  end,
  neg_mem' :=
  begin
    intros a ha x,
    rcases ha x with ⟨V, m, i, r, s, w⟩,
    refine ⟨V, m, i, -r, s, _⟩,
    intro y,
    rcases w y with ⟨nm, w⟩,
    fsplit,
    { exact nm, },
    { simp only [ring_hom.map_neg, pi.neg_apply],
      erw [←w],
      simp only [neg_mul_eq_neg_mul_symm], }
  end,
  mul_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * rb, sa * sb, _⟩,
    intro y,
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩,
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩,
    fsplit,
    { intro H, cases y.1.is_prime.mem_or_mem H; contradiction, },
    { simp only [pi.mul_apply, ring_hom.map_mul],
      erw [←wa, ←wb],
      simp only [mul_left_comm, mul_assoc, mul_comm],
      refl, }
  end, }

end structure_sheaf

open structure_sheaf

/--
The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.
-/
def structure_sheaf_in_Type : sheaf Type* (prime_spectrum_of_graded_ring.Top A):=
subsheaf_to_Types (is_locally_fraction A)

instance comm_ring_structure_sheaf_in_Type_obj (U : (opens (prime_spectrum_of_graded_ring.Top A))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type A).1.obj U) :=
(sections_subring A U).to_comm_ring

open _root_.prime_spectrum

/--
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (prime_spectrum_of_graded_ring.Top A) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type A).1.obj U),
  map := λ U V i,
  { to_fun := ((structure_sheaf_in_Type A).1.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl, }, }

/--
Some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def structure_presheaf_comp_forget :
  structure_presheaf_in_CommRing A ⋙ (forget CommRing) ≅ (structure_sheaf_in_Type A).1 :=
nat_iso.of_components
  (λ U, iso.refl _)
  (by tidy)

open Top.presheaf

/--
The structure sheaf on $Spec R$, valued in `CommRing`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def structure_sheaf : sheaf CommRing (prime_spectrum_of_graded_ring.Top A) :=
⟨structure_presheaf_in_CommRing A,
  -- We check the sheaf condition under `forget CommRing`.
  (is_sheaf_iff_is_sheaf_comp _ _).mpr
    (is_sheaf_of_iso (structure_presheaf_comp_forget A).symm
      (structure_sheaf_in_Type A).property)⟩

end algebraic_geometry
