/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_geometry.prime_spectrum
import algebra.category.CommRing.colimits
import algebra.category.CommRing.limits
import topology.sheaves.local_predicate
import topology.sheaves.forget
import ring_theory.localization
import ring_theory.subring

/-!
# The structure sheaf on `prime_spectrum R`.

We define the structure sheaf on `Top.of (prime_spectrum R)`, for a commutative ring `R` and prove
basic properties of it. We define this as a subsheaf of the sheaf of dependent functions into the
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

## Main statements

* `stalk_iso`: The stalk of the structure sheaf at a point `p : prime_spectrum R` is isomorphic
  (as a commutative ring) to the localization of `R` at the prime ideal `p`.
* `basic_open_iso`: The structure sheaf on `basic_open f` is isomorphic (as a commutative ring) to
  the localization of `R` at the submonoid of powers of `f`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


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
The functions satisfying `is_locally_fraction` form a subring.
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

open Top.presheaf

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

@[simp] lemma res_apply (U V : opens (Spec.Top R)) (i : V ⟶ U)
  (s : (structure_sheaf R).presheaf.obj (op U)) (x : V) :
  ((structure_sheaf R).presheaf.map i.op s).1 x = (s.1 (i x) : _) :=
rfl

/-

Notation in this comment

X = Spec R
OX = structure sheaf

In the following we construct an isomorphism between OX_p and R_p given any point p corresponding
to a prime ideal in R.

We do this via 8 steps:

1. def const (f g : R) (V) (hv : V ≤ D_g) : OX(V) [for api]
2. def to_open (U) : R ⟶ OX(U)
3. [2] def to_stalk (p : Spec R) : R ⟶ OX_p
4. [2] def to_basic_open (f : R) : R_f ⟶ OX(D_f)
5. [3] def localization_to_stalk (p : Spec R) : R_p ⟶ OX_p
6. def open_to_localization (U) (p) (hp : p ∈ U) : OX(U) ⟶ R_p
7. [6] def stalk_to_fiber_ring_hom (p : Spec R) : OX_p ⟶ R_p
8. [5,7] def stalk_iso (p : Spec R) : OX_p ≅ R_p

In the square brackets we list the dependencies of a construction on the previous steps.

-/

/-- The section of `structure_sheaf R` on an open `U` sending each `x ∈ U` to the element
`f/g` in the localization of `R` at `x`. -/
def const (f g : R) (U : opens (Spec.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : Spec.Top R).as_ideal.prime_compl) :
  (structure_sheaf R).presheaf.obj (op U) :=
⟨λ x, (localization.of _).mk' f ⟨g, hu x x.2⟩,
 λ x, ⟨U, x.2, 𝟙 _, f, g, λ y, ⟨hu y y.2, localization_map.mk'_spec _ _ _⟩⟩⟩

@[simp] lemma const_apply (f g : R) (U : opens (Spec.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : Spec.Top R).as_ideal.prime_compl) (x : U) :
  (const R f g U hu).1 x = (localization.of _).mk' f ⟨g, hu x x.2⟩ :=
rfl

lemma const_apply' (f g : R) (U : opens (Spec.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : Spec.Top R).as_ideal.prime_compl) (x : U)
  (hx : g ∈ (as_ideal x.1).prime_compl) :
  (const R f g U hu).1 x = (localization.of _).mk' f ⟨g, hx⟩ :=
rfl

lemma exists_const (U) (s : (structure_sheaf R).presheaf.obj (op U)) (x : Spec.Top R) (hx : x ∈ U) :
  ∃ (V : opens (Spec.Top R)) (hxV : x ∈ V) (i : V ⟶ U) (f g : R) hg,
  const R f g V hg = (structure_sheaf R).presheaf.map i.op s :=
let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩ in
⟨V, hxV, iVU, f, g, λ y hyV, (hfg ⟨y, hyV⟩).1, subtype.eq $ funext $ λ y,
(localization.of _).mk'_eq_iff_eq_mul.2 $ eq.symm $ (hfg y).2⟩

@[simp] lemma res_const (f g : R) (U hu V hv i) :
  (structure_sheaf R).presheaf.map i (const R f g U hu) = const R f g V hv :=
rfl

lemma res_const' (f g : R) (V hv) :
  (structure_sheaf R).presheaf.map (hom_of_le hv).op (const R f g (basic_open g) (λ _, id)) =
    const R f g V hv :=
rfl

lemma const_zero (f : R) (U hu) : const R 0 f U hu = 0 :=
subtype.eq $ funext $ λ x, (localization.of _).mk'_eq_iff_eq_mul.2 $
by erw [ring_hom.map_zero, subtype.val_eq_coe, subring.coe_zero, pi.zero_apply, zero_mul]

lemma const_self (f : R) (U hu) : const R f f U hu = 1 :=
subtype.eq $ funext $ λ x, localization_map.mk'_self _ _

lemma const_one (U) : const R 1 1 U (λ p _, submonoid.one_mem _) = 1 :=
const_self R 1 U _

lemma const_add (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
  const R f₁ g₁ U hu₁ + const R f₂ g₂ U hu₂ =
  const R (f₁ * g₂ + f₂ * g₁) (g₁ * g₂) U (λ x hx, submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx)) :=
subtype.eq $ funext $ λ x, eq.symm $
by convert (localization.of _).mk'_add f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

lemma const_mul (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
  const R f₁ g₁ U hu₁ * const R f₂ g₂ U hu₂ =
  const R (f₁ * f₂) (g₁ * g₂) U (λ x hx, submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx)) :=
subtype.eq $ funext $ λ x, eq.symm $
by convert (localization.of _).mk'_mul f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

lemma const_ext {f₁ f₂ g₁ g₂ : R} {U hu₁ hu₂} (h : f₁ * g₂ = f₂ * g₁) :
  const R f₁ g₁ U hu₁ = const R f₂ g₂ U hu₂ :=
subtype.eq $ funext $ λ x, (localization.of _).mk'_eq_of_eq h.symm

lemma const_congr {f₁ f₂ g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
  const R f₁ g₁ U hu = const R f₂ g₂ U (hg ▸ hu) :=
by substs hf hg

lemma const_mul_rev (f g : R) (U hu₁ hu₂) :
  const R f g U hu₁ * const R g f U hu₂ = 1 :=
by rw [const_mul, const_congr R rfl (mul_comm g f), const_self]

lemma const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) :
  const R f g₁ U hu₁ * const R g₁ g₂ U hu₂ = const R f g₂ U hu₂ :=
by { rw [const_mul, const_ext], rw mul_assoc }

lemma const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) :
  const R g₁ g₂ U hu₂ * const R f g₁ U hu₁ = const R f g₂ U hu₂ :=
by rw [mul_comm, const_mul_cancel]

/-- The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf. -/
def to_open (U : opens (Spec.Top R)) : CommRing.of R ⟶ (structure_sheaf R).presheaf.obj (op U) :=
{ to_fun := λ f, ⟨λ x, (localization.of _).to_map f,
    λ x, ⟨U, x.2, 𝟙 _, f, 1, λ y, ⟨(ideal.ne_top_iff_one _).1 y.1.2.1,
      by { rw [ring_hom.map_one, mul_one], refl } ⟩⟩⟩,
  map_one' := subtype.eq $ funext $ λ x, ring_hom.map_one _,
  map_mul' := λ f g, subtype.eq $ funext $ λ x, ring_hom.map_mul _ _ _,
  map_zero' := subtype.eq $ funext $ λ x, ring_hom.map_zero _,
  map_add' := λ f g, subtype.eq $ funext $ λ x, ring_hom.map_add _ _ _ }

@[simp] lemma to_open_res (U V : opens (Spec.Top R)) (i : V ⟶ U) :
  to_open R U ≫ (structure_sheaf R).presheaf.map i.op = to_open R V :=
rfl

@[simp] lemma to_open_apply (U : opens (Spec.Top R)) (f : R) (x : U) :
  (to_open R U f).1 x = (localization.of _).to_map f :=
rfl

lemma to_open_eq_const (U : opens (Spec.Top R)) (f : R) : to_open R U f =
  const R f 1 U (λ x _, (ideal.ne_top_iff_one _).1 x.2.1) :=
subtype.eq $ funext $ λ x, eq.symm $ (localization.of _).mk'_one f

/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structure_sheaf R` at `x`. -/
def to_stalk (x : Spec.Top R) : CommRing.of R ⟶ (structure_sheaf R).presheaf.stalk x :=
(to_open R ⊤ ≫ (structure_sheaf R).presheaf.germ ⟨x, ⟨⟩⟩ : _)

@[simp] lemma to_open_germ (U : opens (Spec.Top R)) (x : U) :
  to_open R U ≫ (structure_sheaf R).presheaf.germ x =
  to_stalk R x :=
by { rw [← to_open_res R ⊤ U (hom_of_le le_top : U ⟶ ⊤), category.assoc, presheaf.germ_res], refl }

@[simp] lemma germ_to_open (U : opens (Spec.Top R)) (x : U) (f : R) :
  (structure_sheaf R).presheaf.germ x (to_open R U f) = to_stalk R x f :=
by { rw ← to_open_germ, refl }

lemma germ_to_top (x : Spec.Top R) (f : R) :
  (structure_sheaf R).presheaf.germ (⟨x, trivial⟩ : (⊤ : opens (Spec.Top R))) (to_open R ⊤ f) =
    to_stalk R x f :=
rfl

lemma is_unit_to_basic_open_self (f : R) : is_unit (to_open R (basic_open f) f) :=
is_unit_of_mul_eq_one _ (const R 1 f (basic_open f) (λ _, id)) $
by rw [to_open_eq_const, const_mul_rev]

lemma is_unit_to_stalk (x : Spec.Top R) (f : x.as_ideal.prime_compl) :
  is_unit (to_stalk R x (f : R)) :=
by { erw ← germ_to_open R (basic_open (f : R)) ⟨x, f.2⟩ (f : R),
    exact ring_hom.is_unit_map _ (is_unit_to_basic_open_self R f) }

/-- The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`. -/
def localization_to_stalk (x : Spec.Top R) :
  CommRing.of (localization.at_prime x.as_ideal) ⟶ (structure_sheaf R).presheaf.stalk x :=
(localization.of _).lift (is_unit_to_stalk R x)

@[simp] lemma localization_to_stalk_of (x : Spec.Top R) (f : R) :
  localization_to_stalk R x ((localization.of _).to_map f) = to_stalk R x f :=
(localization.of _).lift_eq _ f

@[simp] lemma localization_to_stalk_mk' (x : Spec.Top R) (f : R) (s : (as_ideal x).prime_compl) :
  localization_to_stalk R x ((localization.of _).mk' f s) =
  (structure_sheaf R).presheaf.germ (⟨x, s.2⟩ : basic_open (s : R))
    (const R f s (basic_open s) (λ _, id)) :=
((localization.of _).lift_mk'_spec _ _ _ _).2 $
by erw [← germ_to_open R (basic_open s) ⟨x, s.2⟩, ← germ_to_open R (basic_open s) ⟨x, s.2⟩,
    ← ring_hom.map_mul, to_open_eq_const, to_open_eq_const, const_mul_cancel']

/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def open_to_localization (U : opens (Spec.Top R)) (x : Spec.Top R) (hx : x ∈ U) :
  (structure_sheaf R).presheaf.obj (op U) ⟶ CommRing.of (localization.at_prime x.as_ideal) :=
{ to_fun := λ s, (s.1 ⟨x, hx⟩ : _),
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

@[simp] lemma coe_open_to_localization (U : opens (Spec.Top R)) (x : Spec.Top R) (hx : x ∈ U) :
  (open_to_localization R U x hx :
    (structure_sheaf R).presheaf.obj (op U) → localization.at_prime x.as_ideal) =
  (λ s, (s.1 ⟨x, hx⟩ : _)) :=
rfl

lemma open_to_localization_apply (U : opens (Spec.Top R)) (x : Spec.Top R) (hx : x ∈ U)
  (s : (structure_sheaf R).presheaf.obj (op U)) :
  open_to_localization R U x hx s = (s.1 ⟨x, hx⟩ : _) :=
rfl

/-- The ring homomorphism from the stalk of the structure sheaf of `R` at a point corresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `open_to_localization` maps. -/
def stalk_to_fiber_ring_hom (x : Spec.Top R) :
  (structure_sheaf R).presheaf.stalk x ⟶ CommRing.of (localization.at_prime x.as_ideal) :=
limits.colimit.desc (((open_nhds.inclusion x).op) ⋙ (structure_sheaf R).presheaf)
  { X := _,
    ι :=
    { app := λ U, open_to_localization R ((open_nhds.inclusion _).obj (unop U)) x (unop U).2, } }

@[simp] lemma germ_comp_stalk_to_fiber_ring_hom (U : opens (Spec.Top R)) (x : U) :
  (structure_sheaf R).presheaf.germ x ≫ stalk_to_fiber_ring_hom R x =
  open_to_localization R U x x.2 :=
limits.colimit.ι_desc _ _

@[simp] lemma stalk_to_fiber_ring_hom_germ' (U : opens (Spec.Top R)) (x : Spec.Top R) (hx : x ∈ U)
  (s : (structure_sheaf R).presheaf.obj (op U)) :
  stalk_to_fiber_ring_hom R x ((structure_sheaf R).presheaf.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
ring_hom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom R U ⟨x, hx⟩ : _) s

@[simp] lemma stalk_to_fiber_ring_hom_germ (U : opens (Spec.Top R)) (x : U)
  (s : (structure_sheaf R).presheaf.obj (op U)) :
  stalk_to_fiber_ring_hom R x ((structure_sheaf R).presheaf.germ x s) = s.1 x :=
by { cases x, exact stalk_to_fiber_ring_hom_germ' R U _ _ _ }

@[simp] lemma to_stalk_comp_stalk_to_fiber_ring_hom (x : Spec.Top R) :
  to_stalk R x ≫ stalk_to_fiber_ring_hom R x = (localization.of _).to_map :=
by { erw [to_stalk, category.assoc, germ_comp_stalk_to_fiber_ring_hom], refl }

@[simp] lemma stalk_to_fiber_ring_hom_to_stalk (x : Spec.Top R) (f : R) :
  stalk_to_fiber_ring_hom R x (to_stalk R x f) = (localization.of _).to_map f :=
ring_hom.ext_iff.1 (to_stalk_comp_stalk_to_fiber_ring_hom R x) _

/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
def stalk_iso (x : Spec.Top R) :
  (structure_sheaf R).presheaf.stalk x ≅ CommRing.of (localization.at_prime x.as_ideal) :=
{ hom := stalk_to_fiber_ring_hom R x,
  inv := localization_to_stalk R x,
  hom_inv_id' := (structure_sheaf R).presheaf.stalk_hom_ext $ λ U hxU,
  begin
    ext s, simp only [coe_comp], rw [coe_id, stalk_to_fiber_ring_hom_germ'],
    obtain ⟨V, hxV, iVU, f, g, hg, hs⟩ := exists_const _ _ s x hxU,
    erw [← res_apply R U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localization_to_stalk_mk'],
    refine (structure_sheaf R).presheaf.germ_ext V hxV (hom_of_le hg) iVU _,
    erw [← hs, res_const']
  end,
  inv_hom_id' := (localization.of x.as_ideal.prime_compl).epic_of_localization_map $ λ f,
    by simp only [ring_hom.comp_apply, coe_comp, coe_id, localization_to_stalk_of,
        stalk_to_fiber_ring_hom_to_stalk] }


/-- The canonical ring homomorphism interpreting `s ∈ R_f` as a section of the structure sheaf
on the basic open defined by `f ∈ R`. -/
def to_basic_open (f : R) : CommRing.of (localization (submonoid.powers f)) ⟶
  (structure_sheaf R).presheaf.obj (op $ basic_open f) :=
localization_map.away_map.lift f (localization.away.of f) (is_unit_to_basic_open_self R f)

@[simp] lemma to_basic_open_mk' (s f : R) (g : submonoid.powers s) :
  to_basic_open R s ((localization.of _).mk' f g) =
  const R f g (basic_open s) (λ x hx, submonoid.powers_subset hx g.2) :=
((localization.of _).lift_mk'_spec _ _ _ _).2 $
by rw [to_open_eq_const, to_open_eq_const, const_mul_cancel']

@[simp] lemma localization_to_basic_open (f : R) :
  @category_theory.category_struct.comp _ _ (CommRing.of R)
      (CommRing.of (localization (submonoid.powers f))) _
    (localization.of $ submonoid.powers f).to_map
    (to_basic_open R f) =
  to_open R (basic_open f) :=
ring_hom.ext $ λ g, (localization.of _).lift_eq _ _

@[simp] lemma to_basic_open_to_map (s f : R) : to_basic_open R s ((localization.of _).to_map f) =
  const R f 1 (basic_open s) (λ _ _, submonoid.one_mem _) :=
((localization.of _).lift_eq _ _).trans $ to_open_eq_const _ _ _

-- The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
lemma to_basic_open_injective (f : R) : function.injective (to_basic_open R f) :=
begin
  intros s t h_eq,
  obtain ⟨a, ⟨b, hb⟩, rfl⟩ := (localization.of _).mk'_surjective s,
  obtain ⟨c, ⟨d, hd⟩, rfl⟩ := (localization.of _).mk'_surjective t,
  simp only [to_basic_open_mk'] at h_eq,
  rw localization_map.eq,
  -- We know that the fractions `a/b` and `c/d` are equal as sections of the structure sheaf on
  -- `basic_open f`. We need to show that they agree as elements in the localization of `R` at `f`.
  -- This amounts showing that `a * d * r = c * b * r`, for some power `r = f ^ n` of `f`.
  -- We define `I` as the ideal of *all* elements `r` satisfying the above equation.
  let I : ideal R :=
  { carrier := {r : R | a * d * r = c * b * r},
    zero_mem' := by simp only [set.mem_set_of_eq, mul_zero],
    add_mem' := λ r₁ r₂ hr₁ hr₂, by { dsimp at hr₁ hr₂ ⊢, simp only [mul_add, hr₁, hr₂] },
    smul_mem' := λ r₁ r₂ hr₂, by { dsimp at hr₂ ⊢, simp only [mul_comm r₁ r₂, ← mul_assoc, hr₂] }},
  -- Our claim now reduces to showing that `f` is contained in the radical of `I`
  suffices : f ∈ I.radical,
  { obtain ⟨n, hn⟩ := this,
    use [f ^ n, n, hn] },
  rw [← vanishing_ideal_zero_locus_eq_radical, mem_vanishing_ideal],
  intros p hfp,
  contrapose hfp,
  rw [mem_zero_locus, set.not_subset],
  have := congr_fun (congr_arg subtype.val h_eq) ⟨p,hfp⟩,
  rw [const_apply, const_apply, localization_map.eq] at this,
  obtain ⟨r, hr⟩ := this,
  exact ⟨r.1, hr, r.2⟩
end

/-
Auxiliary lemma for surjectivity of `to_basic_open`.
Every section can locally be represented on basic opens `basic_opens g` as a fraction `f/g`
-/
lemma locally_const_basic_open (U : opens (Spec.Top R))
  (s : (structure_sheaf R).presheaf.obj (op U)) (x : U) :
  ∃ (f g : R) (i : basic_open g ⟶ U), x.1 ∈ basic_open g ∧
    const R f g (basic_open g) (λ y hy, hy) = (structure_sheaf R).presheaf.map i.op s :=
begin
  -- First, we can represent `s` as a fraction `f/g` on *some* basic open `basic_open h`, since
  -- these form a basis
  obtain ⟨V, (hxV : x.1 ∈ V.1), iVU, f, g, (hVDg : V ⊆ basic_open g), s_eq⟩ :=
    exists_const R U s x.1 x.2,
  obtain ⟨_, ⟨h, rfl⟩, hxDh, (hDhV : basic_open h ⊆ V)⟩ :=
    is_topological_basis_basic_opens.exists_subset_of_mem_open hxV V.2,
  -- The problem is of course, that `g` and `h` don't need to coincide.
  -- But, as we will now prove, some power of `h` is a multiple of `g`, i.e. `h` lies in the
  -- radical of the ideal generated by `g`
  obtain ⟨n, hn⟩ : h ∈ (ideal.span {g}).radical := by
  { have hDhDg := set.subset.trans hDhV hVDg,
    simp only [basic_open_eq_zero_locus_compl, set.compl_subset_compl] at hDhDg,
    replace hDhDg := vanishing_ideal_anti_mono hDhDg,
    rw [← vanishing_ideal_zero_locus_eq_radical, zero_locus_span],
    exact hDhDg (subset_vanishing_ideal_zero_locus {h} (set.mem_singleton h)) },
  -- Actually, we will need a *nonzero* power of `h`.
  -- This is because we will need the equality `basic_open (h ^ n) = basic_open h`, which only
  -- holds for a nonzero power `n`
  replace hn := ideal.mul_mem_left (ideal.span {g}) h hn,
  rw [← pow_succ, ideal.mem_span_singleton'] at hn,
  rcases hn with ⟨c, hc⟩,
  have basic_opens_eq := basic_open_pow h (n+1) (by linarith),
  have res_basic_open := eq_to_hom basic_opens_eq ≫ hom_of_le hDhV,
  -- Now we have all the ingredients we need
  use [f * c, h ^ (n+1), res_basic_open ≫ iVU, (basic_opens_eq.symm.le : _) hxDh],
  rw [op_comp, functor.map_comp, coe_comp, ← s_eq, res_const],
  -- Note that the last rewrite here generated an additional goal, which was a parameter
  -- of `res_const`. We prove this goal first
  swap,
  { intros y hy,
    rw basic_opens_eq at hy,
    exact (set.subset.trans hDhV hVDg : _) hy },
  -- All that is left is a simple calculation
  apply const_ext,
  rw [mul_assoc f c g, hc],
end

/-
Auxiliary lemma for surjectivity of `to_basic_open`.
A local representation of a section `s` as fractions `a i / h i` on finitely many basic opens
`basic_open (h i)` can be "normalized" in such a way that `a i * h j = h i * a j` for all `i, j`
-/
lemma normalize_finite_fraction_representation (U : opens (Spec.Top R))
  (s : (structure_sheaf R).presheaf.obj (op U)) {ι : Type*} (a h : ι → R)
  (iDh : Π i : ι, basic_open (h i) ⟶ U) (t : finset ι)
  (h_cover : U.1 ⊆ ⋃ i ∈ t, (basic_open (h i)).1)
  (hs : ∀ i : ι, const R (a i) (h i) (basic_open (h i)) (λ y hy, hy) =
    (structure_sheaf R).presheaf.map (iDh i).op s) :
  ∃ (a' h' : ι → R) (iDh' : Π i : ι, (basic_open (h' i)) ⟶ U),
    (U.1 ⊆ ⋃ i ∈ t, (basic_open (h' i)).1) ∧
    (∀ i j ∈ t, h' i * a' j = a' i * h' j) ∧
    (∀ i ∈ t, (structure_sheaf R).presheaf.map (iDh' i).op s =
      const R (a' i) (h' i) (basic_open (h' i)) (λ y hy, hy)) :=
begin
  -- First we show that the fractions `(a i * h j) / (h i * h j)` and `(h i * a j) / (h i * h j)`
  -- coincide in the localization of `R`
  have fractions_eq : ∀ (i j : ι),
    (localization.of _).mk' (a i * h j) ⟨h i * h j, submonoid.mem_powers _⟩ =
    (localization.of _).mk' (h i * a j) ⟨h i * h j, submonoid.mem_powers _⟩,
  { intros i j,
    let D := basic_open (h i * h j),
    let iDi : D ⟶ basic_open (h i) := hom_of_le (basic_open_mul_le_left _ _),
    let iDj : D ⟶ basic_open (h j) := hom_of_le (basic_open_mul_le_right _ _),
    -- Crucially, we need injectivity of `to_basic_open`
    apply to_basic_open_injective R (h i * h j),
    simp only [set_like.coe_mk, to_basic_open_mk'],
    -- Here, both sides of the equation are equal to a restriction of `s`
    transitivity,
    convert congr_arg ((structure_sheaf R).presheaf.map iDi.op) (hs i) using 1, swap,
    convert congr_arg ((structure_sheaf R).presheaf.map iDj.op) (hs j).symm using 1,
    all_goals { rw res_const, apply const_ext, ring },
    -- The remaining two goals were generated during the rewrite of `res_const`
    -- These can be solved immediately
    exacts [basic_open_mul_le_right _ _, basic_open_mul_le_left _ _] },

  -- From the equality in the localization, we obtain for each `i j` some power `(h i * h j) ^ n`
  -- which equalizes `a i * h j` and `h i * a j`
  have exists_power : ∀ (i j : ι), ∃ n : ℕ,
    a i * h j * (h i * h j) ^ n = h i * a j * (h i * h j) ^ n,
  { intros i j,
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := (localization_map.eq _).mp (fractions_eq i j),
    use (n+1),
    rw pow_succ,
    dsimp at hc,
    convert hc using 1 ; ring },
  let n := λ (p : ι × ι), (exists_power p.1 p.2).some,
  have n_spec := λ (p : ι × ι), (exists_power p.fst p.snd).some_spec,
  -- We need one power `(h i * h j) ^ N` that works for *all* pairs `(i,j)`
  -- Since there are only finitely many indices involved, we can pick the supremum.
  let N := (t.product t).sup n,
  have basic_opens_eq : ∀ i : ι, basic_open ((h i) ^ (N+1)) = basic_open (h i) :=
    λ i, basic_open_pow _ _ (by linarith),
  -- Expanding the fraction `a i / h i` by the power `(h i) ^ N` gives the desired normalization
  refine ⟨(λ i, a i * (h i) ^ N), (λ i, (h i) ^ (N + 1)),
    (λ i, eq_to_hom (basic_opens_eq i) ≫ iDh i), _, _, _⟩,
  { simpa only [basic_opens_eq] using h_cover },
  { intros i j hi hj,
    -- Here we need to show that our new fractions `a i / h i` satisfy the normalization condition
    -- Of course, the power `N` we used to expand the fractions might be bigger than the power
    -- `n (i, j)` which was originally chosen. We denote their difference by `k`
    have n_le_N : n (i, j) ≤ N := finset.le_sup (finset.mem_product.mpr ⟨hi, hj⟩),
    rcases nat.le.dest n_le_N with ⟨k, hk⟩,
    simp only [← hk, pow_add, pow_one],
    -- To accommodate for the difference `k`, we multiply both sides of the equation `n_spec (i, j)`
    -- by `(h i * h j) ^ k`
    convert congr_arg (λ z, z * (h i * h j) ^ k) (n_spec (i, j)).symm using 1 ;
    { simp only [n, mul_pow], ring } },

  -- Lastly, we need to show that the new fractions still represent our original `s`
  intros i hi,
  rw [op_comp, functor.map_comp, coe_comp, ← hs, res_const],
  -- additional goal spit out by `res_const`
  swap, exact (basic_opens_eq i).le,
  apply const_ext,
  rw pow_succ,
  ring
end

open_locale classical
open_locale big_operators

-- The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
lemma to_basic_open_surjective (f : R) : function.surjective (to_basic_open R f) :=
begin
  intro s,
  -- In this proof, `basic_open f` will play two distinct roles: Firstly, it is an open set in the
  -- prime spectrum. Secondly, it is used as an indexing type for various families of objects
  -- (open sets, ring elements, ...). In order to make the distinction clear, we introduce a type
  -- alias `ι` that is used whenever we want think of it as an indexing type.
  let ι : Type u := basic_open f,

  -- First, we pick some cover of basic opens, on which we can represent `s` as a fraction
  choose a' h' iDh' hxDh' s_eq' using locally_const_basic_open R (basic_open f) s,
  -- Since basic opens are compact, we can pass to a finite subcover
  obtain ⟨t, ht_cover'⟩ := (is_compact_basic_open f).elim_finite_subcover
   (λ (i : ι), (basic_open (h' i)).1) (λ i, is_open_basic_open) (λ x hx, _),
  swap,
  { -- Here, we need to show that our basic opens actually form a cover of `basic_open f`
    rw set.mem_Union,
    exact ⟨⟨x,hx⟩, hxDh' ⟨x, hx⟩⟩ },
  -- Next, we use the normalization lemma from above
  obtain ⟨a, h, iDh, ht_cover, ha_ah, s_eq⟩ := normalize_finite_fraction_representation R
    (basic_open f) s a' h' iDh' t ht_cover' s_eq',
  clear s_eq' iDh' hxDh' ht_cover' a' h',
  -- Next we show that some power of `f` is a linear combination of the `h i`
  obtain ⟨n, hn⟩ : f ∈ (ideal.span (finset.image h t : set R)).radical,
  { rw [← vanishing_ideal_zero_locus_eq_radical, zero_locus_span, finset.coe_image],
    simp_rw [subtype.val_eq_coe, basic_open_eq_zero_locus_compl] at ht_cover,
    rw set.compl_subset_comm at ht_cover, -- Why doesn't `simp_rw` do this?
    simp_rw [set.compl_Union, compl_compl, ← zero_locus_Union, ← finset.set_bUnion_coe,
             ← set.image_eq_Union ] at ht_cover,
    apply vanishing_ideal_anti_mono ht_cover,
    exact subset_vanishing_ideal_zero_locus {f} (set.mem_singleton f) },

  -- Actually, we will need a *nonzero* power of `h`.
  -- This is because we will need the equality `basic_open (h ^ n) = basic_open h`, which only
  -- holds for a nonzero power `n`
  replace hn := ideal.mul_mem_left _ f hn,
  erw [← pow_succ, mem_span_finset] at hn,
  cases hn with b hb,

  rw finset.sum_image at hb,
  swap,
  { sorry },
  use (localization.of (submonoid.powers f)).mk'
    (∑ (i : ι) in t, b (h i) * a i) ⟨f ^ (n+1), n+1, rfl⟩,
  rw to_basic_open_mk',
  let tt := ((t : set (basic_open f)) : Type u),

  -- The rest of this proof would be a little nicer if we could write
  -- `(structure_sheaf R).eq_of_locally_eq'`. For that, the API on unique gluing should be
  -- extended to more general (algebraic?) categories, rather than only work with sheaves of types
  apply (structure_sheaf_in_Type R).eq_of_locally_eq'
    (λ i : tt, basic_open (h i)) (basic_open f) (λ i : tt, iDh i),
  { intros x hx,
    simp only [set.mem_Union, set_coe.exists, topological_space.opens.supr_s, subtype.val_eq_coe],
    have := ht_cover hx,
    dsimp at this,
    rw [← finset.set_bUnion_coe, set.mem_bUnion_iff] at this,
    obtain ⟨i, i_mem, x_mem⟩ := this,
    use [i, i_mem] },

  rintro ⟨i, i_mem⟩,
  dsimp,
  change (structure_sheaf R).presheaf.map (iDh i).op _ =
         (structure_sheaf R).presheaf.map (iDh i).op _,
  rw [s_eq i i_mem, res_const],
  swap,
  { intros y hy,
    change y ∈ basic_open (f ^ (n+1)),
    rw basic_open_pow f (n+1) (by linarith),
    exact (le_of_hom (iDh i) : _) hy },
  apply const_ext,
  rw [← hb, finset.sum_mul, finset.mul_sum],
  apply finset.sum_congr rfl,
  intros j hj, dsimp,
  rw [mul_assoc, ← ha_ah j i hj i_mem],
  ring,
end

instance is_iso_to_basic_open (f : R) : is_iso (to_basic_open R f) :=
begin
  haveI : is_iso ((forget CommRing).map (to_basic_open R f)) := (is_iso_iff_bijective _).mpr
    ⟨to_basic_open_injective R f, to_basic_open_surjective R f⟩,
  exact is_iso_of_reflects_iso _ (forget CommRing),
end

def basic_open_iso (f : R) (hf : basic_open f ≠ ∅) :
  (structure_sheaf R).presheaf.obj (op (basic_open f)) ≅
  CommRing.of (localization (submonoid.powers f)) :=
(as_iso (to_basic_open R f)).symm

end algebraic_geometry
