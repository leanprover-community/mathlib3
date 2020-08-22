/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_geometry.prime_spectrum
import ring_theory.localization
import algebra.category.CommRing
import topology.sheaves.local_predicate
import topology.sheaves.forget
import ring_theory.bundled_subring

/-!
# The structure sheaf on `prime_spectrum R`.

-/

universe u

noncomputable theory

variables (R : Type u) [comm_ring R]

open Top
open topological_space
open category_theory
open opposite

/--
The type family over `prime_spectrum R` consisting of the localization over each point.
-/
@[reducible]
def localizations := λ (P : Top.of (prime_spectrum R)), localization.at_prime P.as_ideal

variables {R}

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
`Π x : U, stalks x`.
-/
def locally_fraction {U : opens (Top.of (prime_spectrum R))} (f : Π x : U, localizations R x) : Prop :=
∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : R), ∀ y : V,
  ¬ (s ∈ y.1.as_ideal) ∧
    f (i y : U) * (localization.of _).to_map s = (localization.of _).to_map r

variables (R)

/--
We verify that `locally_fraction` is a `local_predicate`.
This is purely formal, just shuffling around quantifiers.
-/
def locally_fraction_local : local_predicate (localizations R) :=
{ pred := λ U f, locally_fraction f,
  res := λ V U i f h x,
  begin
    rcases h (i x : U) with ⟨W, m, i, r, s, w⟩,
    exact ⟨V ⊓ W, ⟨x.2, m⟩, opens.inf_le_left V W, r, s, (λ y, w ⟨y.1, y.2.2⟩)⟩,
  end,
  locality := λ U f w x,
  begin
    rcases w x with ⟨V, m, i, h⟩, clear w,
    rcases h ⟨x.1, m⟩ with ⟨V', m', i', r, s, h'⟩, clear h,
    exact ⟨V', m', i' ≫ i, r, s, h'⟩,
  end, }

/--
The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `locally_fraction`.
-/
def structure_sheaf_in_Type : sheaf (Type u) (Top.of (prime_spectrum R)) :=
subsheaf_to_Types (locally_fraction_local R)

/--
The functions satisfying `locally_fraction` form a subring.
-/
def sections_subring (U : (opens (Top.of (prime_spectrum R)))ᵒᵖ) :
  subring (Π x : unop U, localizations R x) :=
{ carrier := { f | locally_fraction f },
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

instance comm_ring_structure_sheaf_in_Type_obj (U : (opens (Top.of (prime_spectrum R)))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type R).presheaf.obj U) :=
(sections_subring R U).to_comm_ring

/--
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (Top.of (prime_spectrum R)) :=
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
The structure sheaf on $$Spec R$$, valued in `CommRing`.
-/
def structure_sheaf : sheaf CommRing (Top.of (prime_spectrum R)) :=
{ presheaf := structure_presheaf_in_CommRing R,
  sheaf_condition :=
    -- We check the sheaf condition under `forget CommRing`.
    (sheaf_condition_equiv_sheaf_condition_comp _ _).symm
      (sheaf_condition_equiv_of_iso (structure_presheaf_comp_forget R).symm
        (structure_sheaf_in_Type R).sheaf_condition), }

-- TODO: we need to prove that the stalk at `P` is `localization.at_prime P.as_ideal`
