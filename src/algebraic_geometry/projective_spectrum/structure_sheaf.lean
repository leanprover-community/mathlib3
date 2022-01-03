/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_geometry.projective_spectrum.topology
import algebra.category.CommRing.colimits
import algebra.category.CommRing.limits
import topology.sheaves.local_predicate
import ring_theory.localization

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
open direct_sum set_like

variables {ι R A: Type*} [linear_ordered_cancel_add_comm_monoid ι]
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

open Top
open topological_space
open category_theory
open opposite

namespace algebraic_geometry

/--
The prime spectrum, just as a topological space.
-/
def projective_spectrum.Top : Top := Top.of (projective_spectrum 𝒜)

namespace projective_spectrum.structure_sheaf

/--
The type family over `prime_spectrum R` consisting of the localization over each point.
-/
@[derive [comm_ring]]
def localizations (P : projective_spectrum.Top 𝒜) :=
localization.at_prime P.as_homogeneous_ideal.1

instance (P : projective_spectrum.Top 𝒜) : inhabited (localizations 𝒜 P) :=
⟨1⟩

instance (U : opens (projective_spectrum.Top 𝒜)) (x : U) :
  algebra A (localizations 𝒜 x) :=
localization.algebra

instance (U : opens (projective_spectrum.Top 𝒜)) (x : U) :
  is_localization.at_prime (localizations 𝒜 x)
  (x : projective_spectrum.Top 𝒜).as_homogeneous_ideal.1 :=
localization.is_localization

variables {𝒜}

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (projective_spectrum.Top 𝒜)}
  (f : Π x : U, localizations 𝒜 x) : Prop :=
∃ (r s : A) (r_s_deg_same : ∃ (i : ι), r ∈ 𝒜 i ∧ s ∈ 𝒜 i),
  ∀ x : U, ¬ (s ∈ x.1.as_homogeneous_ideal) ∧ f x * algebra_map _ _ s = algebra_map _ _ r

lemma is_fraction.eq_mk' {U : opens (projective_spectrum.Top 𝒜)}
  {f : Π x : U, localizations 𝒜 x}
  (hf : is_fraction f) :
  ∃ (r s : A) (r_s_deg_same : ∃ (i : ι), r ∈ 𝒜 i ∧ s ∈ 𝒜 i),
    ∀ x : U, ∃ (hs : s ∉ x.1.as_homogeneous_ideal), f x =
    is_localization.mk' (localization.at_prime _) r
      (⟨s, hs⟩ : (x : projective_spectrum.Top 𝒜).as_homogeneous_ideal.1.prime_compl) :=
begin
  rcases hf with ⟨r, s, r_s_deg_same, h⟩,
  refine ⟨r, s, r_s_deg_same,
    λ x, ⟨(h x).1, (is_localization.mk'_eq_iff_eq_mul.mpr _).symm⟩⟩,
  exact (h x).2.symm,
end

variables (𝒜)

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (localizations 𝒜) :=
{ pred := λ U f, is_fraction f,
  res := by { rintro V U i f ⟨r, s, r_s_deg_same, w⟩,
    exact ⟨r, s, r_s_deg_same, λ x, ⟨(w (i x)).1, (w (i x)).2⟩⟩ } }

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
def is_locally_fraction : local_predicate (localizations 𝒜) :=
(is_fraction_prelocal 𝒜).sheafify

@[simp]
lemma is_locally_fraction_pred
  {U : opens (projective_spectrum.Top 𝒜)} (f : Π x : U, localizations 𝒜 x) :
  (is_locally_fraction 𝒜).pred f =
  ∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : A)  (r_s_deg_same : ∃ (i : ι), r ∈ 𝒜 i ∧ s ∈ 𝒜 i), ∀ y : V,
  ¬ (s ∈ y.1.as_homogeneous_ideal) ∧
    f (i y : U) * algebra_map _ _ s = algebra_map _ _ r :=
rfl

/--
The functions satisfying `is_locally_fraction` form a subring.
-/
def sections_subring (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  subring (Π x : unop U, localizations 𝒜 x) :=
{ carrier := { f | (is_locally_fraction 𝒜).pred f },
  zero_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 0, 1,
      ⟨0, submodule.zero_mem _, set_like.has_graded_one.one_mem⟩, λ y, ⟨_, _⟩⟩,
    { erw ←ideal.ne_top_iff_one ((y : projective_spectrum.Top 𝒜).as_homogeneous_ideal.1),
      exact y.1.is_prime.1, },
    { simp, },
  end,
  one_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 1, 1,
      ⟨0, set_like.has_graded_one.one_mem, set_like.has_graded_one.one_mem⟩, λ y, ⟨_, _⟩⟩,
    { erw ←ideal.ne_top_iff_one ((y : projective_spectrum.Top 𝒜).as_homogeneous_ideal.1),
      exact y.1.is_prime.1, },
    { simp, },
  end,
  add_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, ⟨ja, ra_sa_same_deg⟩, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, ⟨jb, rb_sb_same_deg⟩, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * sb + rb * sa, sa * sb,
      ⟨ja + jb, submodule.add_mem _ _ _,
        set_like.graded_monoid.mul_mem ra_sa_same_deg.2 rb_sb_same_deg.2⟩, λ y, ⟨λ h, _, _⟩⟩,
    { apply set_like.graded_monoid.mul_mem, exact ra_sa_same_deg.1,
      exact rb_sb_same_deg.2, },
    { rw add_comm, apply set_like.graded_monoid.mul_mem,
      exact rb_sb_same_deg.1, exact ra_sa_same_deg.2, },
    { have := (y : projective_spectrum.Top 𝒜).is_prime.mem_or_mem h, cases this,
      apply (wa ⟨y, _⟩).1, exact this,
      suffices : y.1 ∈ Va, exact this,
      exact (opens.inf_le_left Va Vb y).2,
      apply (wb ⟨y, _⟩).1, exact this,
      suffices : y.1 ∈ Vb, exact this,
      exact (opens.inf_le_right Va Vb y).2, },
    { simp only [add_mul, ring_hom.map_add, pi.add_apply, ring_hom.map_mul],
      erw ←(wa (opens.inf_le_left Va Vb y)).2,
      erw ←(wb (opens.inf_le_right Va Vb y)).2,
      simp only [mul_assoc],
      congr' 2,
      rw [mul_comm], refl, }
  end,
  neg_mem' :=
  begin
    intros a ha x,
    rcases ha x with ⟨V, m, i, r, s, ⟨j, r_hom_j, s_hom_j⟩, w⟩,
    refine ⟨V, m, i, -r, s, ⟨j, submodule.neg_mem _ r_hom_j, s_hom_j⟩, λ y, ⟨(w _).1, _⟩⟩,
    simp only [ring_hom.map_neg, pi.neg_apply],
      erw [←(w _).2],
      simp only [neg_mul_eq_neg_mul_symm],
  end,
  mul_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, ⟨ja, ra_hom_ja, sa_hom_ja⟩, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, ⟨jb, rb_hom_jb, sb_hom_jb⟩, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * rb, sa * sb,
      ⟨ja + jb, set_like.graded_monoid.mul_mem ra_hom_ja rb_hom_jb,
        set_like.graded_monoid.mul_mem sa_hom_ja sb_hom_jb⟩, λ y, ⟨λ h, _, _⟩⟩,
    { have := (y : projective_spectrum.Top 𝒜).is_prime.mem_or_mem h, cases this,
      apply (wa ⟨y, _⟩).1, exact this,
      suffices : y.1 ∈ Va, exact this,
      exact (opens.inf_le_left Va Vb y).2,
      apply (wb ⟨y, _⟩).1, exact this,
      suffices : y.1 ∈ Vb, exact this,
      exact (opens.inf_le_right Va Vb y).2, },
    { simp only [pi.mul_apply, ring_hom.map_mul],
      erw ←(wa (opens.inf_le_left Va Vb y)).2,
      erw ←(wb (opens.inf_le_right Va Vb y)).2,
      simp only [mul_left_comm, mul_assoc, mul_comm],
      refl, }
  end, }

/--
The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.
-/
def structure_sheaf_in_Type : sheaf Type* (projective_spectrum.Top 𝒜):=
subsheaf_to_Types (is_locally_fraction 𝒜)

instance comm_ring_structure_sheaf_in_Type_obj
  (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type 𝒜).1.obj U) :=
(sections_subring 𝒜 U).to_comm_ring

/--
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (projective_spectrum.Top 𝒜) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type 𝒜).1.obj U),
  map := λ U V i,
  { to_fun := ((structure_sheaf_in_Type 𝒜).1.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl, }, }

/--
Some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def structure_presheaf_comp_forget :
  structure_presheaf_in_CommRing 𝒜 ⋙ (forget CommRing) ≅ (structure_sheaf_in_Type 𝒜).1 :=
nat_iso.of_components
  (λ U, iso.refl _)
  (by tidy)

open Top.presheaf

/--
The structure sheaf on $Spec R$, valued in `CommRing`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def structure_sheaf : sheaf CommRing (projective_spectrum.Top 𝒜) :=
⟨structure_presheaf_in_CommRing 𝒜,
  -- We check the sheaf condition under `forget CommRing`.
  (is_sheaf_iff_is_sheaf_comp _ _).mpr
    (is_sheaf_of_iso (structure_presheaf_comp_forget 𝒜).symm
      (structure_sheaf_in_Type 𝒜).property)⟩

end projective_spectrum.structure_sheaf

end algebraic_geometry
