/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_geometry.prime_spectrum
import algebra.category.CommRing.limits
import topology.sheaves.local_predicate
import topology.sheaves.forget
import ring_theory.localization
import ring_theory.subring

/-!
# The structure sheaf on `prime_spectrum R`.

We define the structure sheaf on `Top.of (prime_spectrum R)`, for a commutative ring `R`.
We define this as a subsheaf of the sheaf of dependent functions into the localizations,
cut out by the condition that the function must be locally equal to a ratio of elements of `R`.

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
-/

universe u

noncomputable theory

variables (R : Type u) [comm_ring R]

open Top
open topological_space
open category_theory
open opposite

namespace algebraic_geometry

/--
$Spec R$, just as a topological space.
-/
def Spec.Top : Top := Top.of (prime_spectrum R)

namespace structure_sheaf

/--
The type family over `prime_spectrum R` consisting of the localization over each point.
-/
@[derive [comm_ring, local_ring]]
def localizations (P : Spec.Top R) : Type u := localization.at_prime P.as_ideal

instance (P : Spec.Top R) : inhabited (localizations R P) :=
⟨(localization.of _).to_map 1⟩

variables {R}

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (Spec.Top R)} (f : Π x : U, localizations R x) : Prop :=
∃ (r s : R), ∀ x : U,
  ¬ (s ∈ x.1.as_ideal) ∧ f x * (localization.of _).to_map s = (localization.of _).to_map r

variables (R)

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (localizations R) :=
{ pred := λ U f, is_fraction f,
  res := by { rintro V U i f ⟨r, s, w⟩, exact ⟨r, s, λ x, w (i x)⟩ } }

/--
We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $$U ⊆ Spec A$$, we define $$𝒪(U)$$ to be the set of functions
$$s : U → ⨆_{𝔭 ∈ U} A_𝔭$$, such that $s(𝔭) ∈ A_𝔭$$ for each $$𝔭$$,
and such that $$s$$ is locally a quotient of elements of $$A$$:
to be precise, we require that for each $$𝔭 ∈ U$$, there is a neighborhood $$V$$ of $$𝔭$$,
contained in $$U$$, and elements $$a, f ∈ A$$, such that for each $$𝔮 ∈ V, f ∉ 𝔮$$,
and $$s(𝔮) = a/f$$ in $$A_𝔮$$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, localizations x`.
-/
def is_locally_fraction : local_predicate (localizations R) :=
(is_fraction_prelocal R).sheafify

@[simp]
lemma is_locally_fraction_pred
  {U : opens (Spec.Top R)} (f : Π x : U, localizations R x) :
  (is_locally_fraction R).pred f =
  ∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : R), ∀ y : V,
  ¬ (s ∈ y.1.as_ideal) ∧
    f (i y : U) * (localization.of _).to_map s = (localization.of _).to_map r :=
rfl

/--
The functions satisfying `is_locally_fraction` form a submonoid.
-/
def sections_subring (U : (opens (Spec.Top R))ᵒᵖ) :
  subring (Π x : unop U, localizations R x) :=
{ carrier := { f | (is_locally_fraction R).pred f },
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
def structure_sheaf_in_Type : sheaf (Type u) (Spec.Top R):=
subsheaf_to_Types (is_locally_fraction R)

instance comm_ring_structure_sheaf_in_Type_obj (U : (opens (Spec.Top R))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type R).presheaf.obj U) :=
(sections_subring R U).to_comm_ring

open prime_spectrum

/--
The `stalk_to_fiber` map for the structure sheaf is surjective.
(In fact, an isomorphism, as constructed below in `stalk_iso_Type`.)
-/
lemma structure_sheaf_stalk_to_fiber_surjective (x : Top.of (prime_spectrum R)) :
  function.surjective (stalk_to_fiber (is_locally_fraction R) x) :=
begin
  apply stalk_to_fiber_surjective,
  intro t,
  obtain ⟨r, ⟨s, hs⟩, rfl⟩ := (localization.of _).mk'_surjective t,
  exact ⟨⟨⟨basic_open s, basic_open_open⟩, hs⟩, λ y, (localization.of _).mk' r ⟨s, y.2⟩,
    ⟨prelocal_predicate.sheafify_of ⟨r, s, λ y, ⟨y.2, localization_map.mk'_spec _ _ _⟩⟩, rfl⟩⟩,
end

/--
The `stalk_to_fiber` map for the structure sheaf is injective.
(In fact, an isomorphism, as constructed below in `stalk_iso_Type`.)

The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
-/
lemma structure_sheaf_stalk_to_fiber_injective (x : Top.of (prime_spectrum R)) :
  function.injective (stalk_to_fiber (is_locally_fraction R) x) :=
begin
  apply stalk_to_fiber_injective,
  intros U V fU hU fV hV e,
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, ⟨a, b, wU⟩⟩,
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, ⟨c, d, wV⟩⟩,

  have wUx := (wU ⟨x, mU⟩).2,
  dsimp at wUx,
  have wVx := (wV ⟨x, mV⟩).2,
  dsimp at wVx,
  have e' := congr_arg (λ z, z * ((localization.of _).to_map (b * d))) e,
  dsimp at e',
  simp only [←mul_assoc, ring_hom.map_mul] at e',
  rw [mul_right_comm (fV _)] at e',
  erw [wUx, wVx] at e',
  simp only [←ring_hom.map_mul] at e',
  have := @localization_map.mk'_eq_iff_eq _ _ _ _ _
    (localization.of (as_ideal x).prime_compl) a c ⟨b, (wU ⟨x, mU⟩).1⟩ ⟨d, (wV ⟨x, mV⟩).1⟩,
  dsimp at this,
  rw ←this at e',
  rw localization_map.eq at e',
  rcases e' with ⟨⟨h, hh⟩, e''⟩,
  dsimp at e'',

  let Wb : opens _ := ⟨basic_open b, basic_open_open⟩,
  let Wd : opens _ := ⟨basic_open d, basic_open_open⟩,
  let Wh : opens _ := ⟨basic_open h, basic_open_open⟩,
  use ((Wb ⊓ Wd) ⊓ Wh) ⊓ (U' ⊓ V'),
  refine ⟨⟨⟨(wU ⟨x, mU⟩).1, (wV ⟨x, mV⟩).1⟩, hh⟩, ⟨mU, mV⟩⟩,

  refine ⟨_, _, _⟩,
  change _ ⟶ U.val,
  exact (opens.inf_le_right _ _) ≫ (opens.inf_le_left _ _) ≫ iU,
  change _ ⟶ V.val,
  exact (opens.inf_le_right _ _) ≫ (opens.inf_le_right _ _) ≫ iV,

  intro w,

  dsimp,
  have wU' := (wU ⟨w.1, w.2.2.1⟩).2,
  dsimp at wU',
  have wV' := (wV ⟨w.1, w.2.2.2⟩).2,
  dsimp at wV',
  -- We need to prove `fU w = fV w`.
  -- First we show that is suffices to prove `fU w * b * d * h = fV w * b * d * h`.
  -- Then we calculate (at w) as follows:
  --   fU w * b * d * h
  --       = a * d * h        : wU'
  --   ... = c * b * h        : e''
  --   ... = fV w * d * b * h : wV'
  have u : is_unit ((localization.of (as_ideal w.1).prime_compl).to_map (b * d * h)),
  { simp only [ring_hom.map_mul],
    apply is_unit.mul, apply is_unit.mul,
    exact (localization.of (as_ideal w.1).prime_compl).map_units ⟨b, (wU ⟨w, w.2.2.1⟩).1⟩,
    exact (localization.of (as_ideal w.1).prime_compl).map_units ⟨d, (wV ⟨w, w.2.2.2⟩).1⟩,
    exact (localization.of (as_ideal w.1).prime_compl).map_units ⟨h, w.2.1.2⟩, },
  apply (is_unit.mul_left_inj u).1,
  conv_rhs { rw [mul_comm b d] },
  simp only [ring_hom.map_mul, ←mul_assoc],
  erw [wU', wV'],
  dsimp,
  simp only [←ring_hom.map_mul, ←mul_assoc],
  rw e'',
end


/--
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (Spec.Top R) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type R).presheaf.obj U),
  map := λ U V i,
  { to_fun := ((structure_sheaf_in_Type R).presheaf.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl, }, }

/--
Some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def structure_presheaf_comp_forget :
  structure_presheaf_in_CommRing R ⋙ (forget CommRing) ≅ (structure_sheaf_in_Type R).presheaf :=
nat_iso.of_components
  (λ U, iso.refl _)
  (by tidy)

/--
The structure sheaf on $Spec R$, valued in `CommRing`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def structure_sheaf : sheaf CommRing (Spec.Top R) :=
{ presheaf := structure_presheaf_in_CommRing R,
  sheaf_condition :=
    -- We check the sheaf condition under `forget CommRing`.
    (sheaf_condition_equiv_sheaf_condition_comp _ _).symm
      (sheaf_condition_equiv_of_iso (structure_presheaf_comp_forget R).symm
        (structure_sheaf_in_Type R).sheaf_condition), }

/--
The stalk at `x` is equivalent (just as a type) to the localization at `x`.
-/
def stalk_iso_Type (x : prime_spectrum R) :
  (structure_sheaf_in_Type R).presheaf.stalk x ≅ localization.at_prime x.as_ideal :=
(equiv.of_bijective _
  ⟨structure_sheaf_stalk_to_fiber_injective R x,
   structure_sheaf_stalk_to_fiber_surjective R x⟩).to_iso

-- PROJECT: Improve this to an isomorphism of rings.
/-
/--
TODO: this should follow easily from `forget CommRing` preserving filtered colimits.
-/
def compare_stalks (x : prime_spectrum R) :
  (forget CommRing).obj ((structure_sheaf R).presheaf.stalk x) ≅ (structure_sheaf_in_Type R).presheaf.stalk x :=
sorry

/--
TODO:
-/
def stalk_to_fiber_ring_hom (x : prime_spectrum R) :
  (structure_sheaf R).presheaf.stalk x ⟶ CommRing.of (localization.at_prime x.as_ideal) :=
{ to_fun := (compare_stalks R x).hom ≫ stalk_to_fiber (is_locally_fraction_local R) x,
  map_zero' := sorry,
  map_add' := sorry,
  map_one' := sorry,
  map_mul' := sorry }

/--
The stalk at `x` is equivalent, as a commutative ring, to the localization at `x`.
-/
def stalk_iso (x : prime_spectrum R) :
  (structure_sheaf R).presheaf.stalk x ≅ CommRing.of (localization.at_prime x.as_ideal) :=
({ ..stalk_to_fiber_ring_hom R x,
   ..(compare_stalks R x ≪≫ stalk_iso_Type R x).to_equiv } : _ ≃+* _).to_CommRing_iso
-/

end algebraic_geometry
