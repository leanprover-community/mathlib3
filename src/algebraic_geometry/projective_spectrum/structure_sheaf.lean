/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.topology
import topology.sheaves.local_predicate
import ring_theory.graded_algebra.homogeneous_localization
import algebraic_geometry.locally_ringed_space

/-!
# The structure sheaf on `projective_spectrum 𝒜`.

In `src/algebraic_geometry/topology.lean`, we have given a topology on `projective_spectrum 𝒜`; in
this file we will construct a sheaf on `projective_spectrum 𝒜`.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → submodule R A` is the grading of `A`;
- `U` is opposite object of some open subset of `projective_spectrum.Top`.

## Main definitions and results
We define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, homogeneous_localization 𝒜 x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `algebraic_geometry.projective_spectrum.structure_sheaf.is_locally_fraction`: the predicate that
  a dependent function is locally expressible as a ratio of two elements of the same grading.
* `algebraic_geometry.projective_spectrum.structure_sheaf.sections_subring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, homogeneous_localization 𝒜 x`.
* `algebraic_geometry.Proj.structure_sheaf`: the sheaf with `U ↦ sections_subring U` and natural
  restriction map.

Then we establish that `Proj 𝒜` is a `LocallyRingedSpace`:
* `algebraic_geometry.Proj.stalk_iso'`: for any `x : projective_spectrum 𝒜`, the stalk of
  `Proj.structure_sheaf` at `x` is isomorphic to `homogeneous_localization 𝒜 x`.
* `algebraic_geometry.Proj.to_LocallyRingedSpace`: `Proj` as a locally ringed space.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise
open direct_sum set_like localization Top topological_space category_theory opposite

variables {R A: Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]

local notation `at ` x := homogeneous_localization 𝒜 x.as_homogeneous_ideal.to_ideal

namespace projective_spectrum.structure_sheaf

variables {𝒜}

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` of *same grading* in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (projective_spectrum.Top 𝒜)} (f : Π x : U, at x.1) : Prop :=
∃ (i : ℕ) (r s : 𝒜 i),
  ∀ x : U, ∃ (s_nin : s.1 ∉ x.1.as_homogeneous_ideal),
  (f x) = quotient.mk' ⟨i, r, s, s_nin⟩

variables (𝒜)

/--
The predicate `is_fraction` is "prelocal", in the sense that if it holds on `U` it holds on any open
subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (λ (x : projective_spectrum.Top 𝒜), at x) :=
{ pred := λ U f, is_fraction f,
  res := by rintros V U i f ⟨j, r, s, w⟩; exact ⟨j, r, s, λ y, w (i y)⟩ }

/--
We will define the structure sheaf as the subsheaf of all dependent functions in
`Π x : U, homogeneous_localization 𝒜 x` consisting of those functions which can locally be expressed
as a ratio of `A` of same grading.-/
def is_locally_fraction : local_predicate (λ (x : projective_spectrum.Top 𝒜), at x) :=
(is_fraction_prelocal 𝒜).sheafify

namespace section_subring
variable {𝒜}

open submodule set_like.graded_monoid homogeneous_localization

lemma zero_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  (is_locally_fraction 𝒜).pred (0 : Π x : unop U, at x.1) :=
λ x, ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem⟩, λ y, ⟨_, rfl⟩⟩⟩

lemma one_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  (is_locally_fraction 𝒜).pred (1 : Π x : unop U, at x.1) :=
λ x, ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨1, one_mem⟩, ⟨1, one_mem⟩, λ y, ⟨_, rfl⟩⟩⟩

lemma add_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ)
  (a b : Π x : unop U, at x.1)
  (ha : (is_locally_fraction 𝒜).pred a) (hb : (is_locally_fraction 𝒜).pred b) :
  (is_locally_fraction 𝒜).pred (a + b) := λ x,
begin
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, wa⟩,
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, wb⟩,
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ja + jb,
    ⟨sb * ra + sa * rb, add_mem (add_comm jb ja ▸ mul_mem sb_mem ra_mem : sb * ra ∈ 𝒜 (ja + jb))
      (mul_mem sa_mem rb_mem)⟩,
    ⟨sa * sb, mul_mem sa_mem sb_mem⟩, λ y, ⟨λ h, _, _⟩⟩,
  { cases (y : projective_spectrum.Top 𝒜).is_prime.mem_or_mem h with h h,
    { obtain ⟨nin, -⟩ := (wa ⟨y, (opens.inf_le_left Va Vb y).2⟩), exact nin h },
    { obtain ⟨nin, -⟩ := (wb ⟨y, (opens.inf_le_right Va Vb y).2⟩), exact nin h } },
  { simp only [add_mul, map_add, pi.add_apply, ring_hom.map_mul, ext_iff_val, add_val],
    obtain ⟨nin1, hy1⟩ := (wa (opens.inf_le_left Va Vb y)),
    obtain ⟨nin2, hy2⟩ := (wb (opens.inf_le_right Va Vb y)),
    dsimp only at hy1 hy2,
    erw [hy1, hy2],
    simpa only [val_mk', add_mk, ← subtype.val_eq_coe, add_comm], }
end

lemma neg_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ)
  (a : Π x : unop U, at x.1)
  (ha : (is_locally_fraction 𝒜).pred a) :
  (is_locally_fraction 𝒜).pred (-a) := λ x,
begin
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, w⟩,
  choose nin hy using w,
  refine ⟨V, m, i, j, ⟨-r, submodule.neg_mem _ r_mem⟩, ⟨s, s_mem⟩, λ y, ⟨nin y, _⟩⟩,
  simp only [ext_iff_val, val_mk', ←subtype.val_eq_coe] at hy,
  simp only [pi.neg_apply, ext_iff_val, neg_val, hy, val_mk', ←subtype.val_eq_coe, neg_mk],
end

lemma mul_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ)
  (a b : Π x : unop U, at x.1)
  (ha : (is_locally_fraction 𝒜).pred a) (hb : (is_locally_fraction 𝒜).pred b) :
  (is_locally_fraction 𝒜).pred (a * b) := λ x,
begin
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, wa⟩,
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, wb⟩,
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ja + jb,
    ⟨ra * rb, set_like.graded_monoid.mul_mem ra_mem rb_mem⟩,
    ⟨sa * sb, set_like.graded_monoid.mul_mem sa_mem sb_mem⟩, λ y, ⟨λ h, _, _⟩⟩,
  { cases (y : projective_spectrum.Top 𝒜).is_prime.mem_or_mem h with h h,
    { choose nin hy using wa ⟨y, (opens.inf_le_left Va Vb y).2⟩, exact nin h },
    { choose nin hy using wb ⟨y, (opens.inf_le_right Va Vb y).2⟩, exact nin h }, },
  { simp only [pi.mul_apply, ring_hom.map_mul],
    choose nin1 hy1 using wa (opens.inf_le_left Va Vb y),
    choose nin2 hy2 using wb (opens.inf_le_right Va Vb y),
    rw ext_iff_val at hy1 hy2 ⊢,
    erw [mul_val, hy1, hy2],
    simpa only [val_mk', mk_mul, ← subtype.val_eq_coe] }
end

end section_subring

section

open section_subring

variable {𝒜}
/--The functions satisfying `is_locally_fraction` form a subring of all dependent functions
`Π x : U, homogeneous_localization 𝒜 x`.-/
def sections_subring (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) : subring (Π x : unop U, at x.1) :=
{ carrier := { f | (is_locally_fraction 𝒜).pred f },
  zero_mem' := zero_mem' U,
  one_mem' := one_mem' U,
  add_mem' := add_mem' U,
  neg_mem' := neg_mem' U,
  mul_mem' := mul_mem' U }

end

/--The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.-/
def structure_sheaf_in_Type : sheaf Type* (projective_spectrum.Top 𝒜):=
subsheaf_to_Types (is_locally_fraction 𝒜)

instance comm_ring_structure_sheaf_in_Type_obj (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type 𝒜).1.obj U) := (sections_subring U).to_comm_ring

/--The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.-/
@[simps] def structure_presheaf_in_CommRing : presheaf CommRing (projective_spectrum.Top 𝒜) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type 𝒜).1.obj U),
  map := λ U V i,
  { to_fun := ((structure_sheaf_in_Type 𝒜).1.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl, }, }

/--Some glue, verifying that that structure presheaf valued in `CommRing` agrees with the `Type`
valued structure presheaf.-/
def structure_presheaf_comp_forget :
  structure_presheaf_in_CommRing 𝒜 ⋙ (forget CommRing) ≅ (structure_sheaf_in_Type 𝒜).1 :=
nat_iso.of_components (λ U, iso.refl _) (by tidy)

end projective_spectrum.structure_sheaf

namespace projective_spectrum

open Top.presheaf projective_spectrum.structure_sheaf opens

/--The structure sheaf on `Proj` 𝒜, valued in `CommRing`.-/
def Proj.structure_sheaf : sheaf CommRing (projective_spectrum.Top 𝒜) :=
⟨structure_presheaf_in_CommRing 𝒜,
  -- We check the sheaf condition under `forget CommRing`.
  (is_sheaf_iff_is_sheaf_comp _ _).mpr
    (is_sheaf_of_iso (structure_presheaf_comp_forget 𝒜).symm
      (structure_sheaf_in_Type 𝒜).property)⟩

end projective_spectrum

end algebraic_geometry
