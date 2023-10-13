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

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

local notation `at ` x := homogeneous_localization.at_prime 𝒜 x.as_homogeneous_ideal.to_ideal

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
    simpa only [val_mk', add_mk, ← subtype.val_eq_coe, add_comm, mul_comm sa sb], }
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
    ⟨ra * rb, set_like.mul_mem_graded ra_mem rb_mem⟩,
    ⟨sa * sb, set_like.mul_mem_graded sa_mem sb_mem⟩, λ y, ⟨λ h, _, _⟩⟩,
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
      (structure_sheaf_in_Type 𝒜).cond)⟩

end projective_spectrum

section

open projective_spectrum projective_spectrum.structure_sheaf opens

@[simp] lemma res_apply (U V : opens (projective_spectrum.Top 𝒜)) (i : V ⟶ U)
  (s : (Proj.structure_sheaf 𝒜).1.obj (op U)) (x : V) :
  ((Proj.structure_sheaf 𝒜).1.map i.op s).1 x = (s.1 (i x) : _) :=
rfl

/--`Proj` of a graded ring as a `SheafedSpace`-/
def Proj.to_SheafedSpace : SheafedSpace CommRing :=
{ carrier := Top.of (projective_spectrum 𝒜),
  presheaf := (Proj.structure_sheaf 𝒜).1,
  is_sheaf := (Proj.structure_sheaf 𝒜).2 }

/-- The ring homomorphism that takes a section of the structure sheaf of `Proj` on the open set `U`,
implemented as a subtype of dependent functions to localizations at homogeneous prime ideals, and
evaluates the section on the point corresponding to a given homogeneous prime ideal. -/
def open_to_localization (U : opens (projective_spectrum.Top 𝒜)) (x : projective_spectrum.Top 𝒜)
  (hx : x ∈ U) :
  (Proj.structure_sheaf 𝒜).1.obj (op U) ⟶ CommRing.of (at x) :=
{ to_fun := λ s, (s.1 ⟨x, hx⟩ : _),
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

/-- The ring homomorphism from the stalk of the structure sheaf of `Proj` at a point corresponding
to a homogeneous prime ideal `x` to the *homogeneous localization* at `x`,
formed by gluing the `open_to_localization` maps. -/
def stalk_to_fiber_ring_hom (x : projective_spectrum.Top 𝒜) :
  (Proj.structure_sheaf 𝒜).presheaf.stalk x ⟶ CommRing.of (at x) :=
limits.colimit.desc (((open_nhds.inclusion x).op) ⋙ (Proj.structure_sheaf 𝒜).1)
  { X := _,
    ι :=
    { app := λ U, open_to_localization 𝒜 ((open_nhds.inclusion _).obj (unop U)) x (unop U).2, } }

@[simp] lemma germ_comp_stalk_to_fiber_ring_hom (U : opens (projective_spectrum.Top 𝒜)) (x : U) :
  (Proj.structure_sheaf 𝒜).presheaf.germ x ≫ stalk_to_fiber_ring_hom 𝒜 x =
  open_to_localization 𝒜 U x x.2 :=
limits.colimit.ι_desc _ _

@[simp] lemma stalk_to_fiber_ring_hom_germ' (U : opens (projective_spectrum.Top 𝒜))
  (x : projective_spectrum.Top 𝒜) (hx : x ∈ U) (s : (Proj.structure_sheaf 𝒜).1.obj (op U)) :
  stalk_to_fiber_ring_hom 𝒜 x
    ((Proj.structure_sheaf 𝒜).presheaf.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
ring_hom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom 𝒜 U ⟨x, hx⟩ : _) s

@[simp] lemma stalk_to_fiber_ring_hom_germ (U : opens (projective_spectrum.Top 𝒜)) (x : U)
  (s : (Proj.structure_sheaf 𝒜).1.obj (op U)) :
  stalk_to_fiber_ring_hom 𝒜 x ((Proj.structure_sheaf 𝒜).presheaf.germ x s) = s.1 x :=
by { cases x, exact stalk_to_fiber_ring_hom_germ' 𝒜 U _ _ _ }

lemma homogeneous_localization.mem_basic_open (x : projective_spectrum.Top 𝒜) (f : at x) :
  x ∈ projective_spectrum.basic_open 𝒜 f.denom :=
by { rw projective_spectrum.mem_basic_open, exact f.denom_mem }

variable (𝒜)

/--Given a point `x` corresponding to a homogeneous prime ideal, there is a (dependent) function
such that, for any `f` in the homogeneous localization at `x`, it returns the obvious section in the
basic open set `D(f.denom)`-/
def section_in_basic_open (x : projective_spectrum.Top 𝒜) :
  Π (f : at x),
    (Proj.structure_sheaf 𝒜).1.obj (op (projective_spectrum.basic_open 𝒜 f.denom)) :=
λ f, ⟨λ y, quotient.mk' ⟨f.deg, ⟨f.num, f.num_mem_deg⟩, ⟨f.denom, f.denom_mem_deg⟩, y.2⟩,
  λ y, ⟨projective_spectrum.basic_open 𝒜 f.denom, y.2,
    ⟨𝟙 _, ⟨f.deg, ⟨⟨f.num, f.num_mem_deg⟩, ⟨f.denom, f.denom_mem_deg⟩,
      λ z, ⟨z.2, rfl⟩⟩⟩⟩⟩⟩

/--Given any point `x` and `f` in the homogeneous localization at `x`, there is an element in the
stalk at `x` obtained by `section_in_basic_open`. This is the inverse of `stalk_to_fiber_ring_hom`.
-/
def homogeneous_localization_to_stalk (x : projective_spectrum.Top 𝒜) :
  (at x) → (Proj.structure_sheaf 𝒜).presheaf.stalk x :=
λ f, (Proj.structure_sheaf 𝒜).presheaf.germ
  (⟨x, homogeneous_localization.mem_basic_open _ x f⟩ : projective_spectrum.basic_open _ f.denom)
  (section_in_basic_open _ x f)

/--Using `homogeneous_localization_to_stalk`, we construct a ring isomorphism between stalk at `x`
and homogeneous localization at `x` for any point `x` in `Proj`.-/
def Proj.stalk_iso' (x : projective_spectrum.Top 𝒜) :
  (Proj.structure_sheaf 𝒜).presheaf.stalk x ≃+* CommRing.of (at x)  :=
ring_equiv.of_bijective (stalk_to_fiber_ring_hom _ x)
⟨λ z1 z2 eq1, begin
  obtain ⟨u1, memu1, s1, rfl⟩ := (Proj.structure_sheaf 𝒜).presheaf.germ_exist x z1,
  obtain ⟨u2, memu2, s2, rfl⟩ := (Proj.structure_sheaf 𝒜).presheaf.germ_exist x z2,
  obtain ⟨v1, memv1, i1, ⟨j1, ⟨a1, a1_mem⟩, ⟨b1, b1_mem⟩, hs1⟩⟩ := s1.2 ⟨x, memu1⟩,
  obtain ⟨v2, memv2, i2, ⟨j2, ⟨a2, a2_mem⟩, ⟨b2, b2_mem⟩, hs2⟩⟩ := s2.2 ⟨x, memu2⟩,
  obtain ⟨b1_nin_x, eq2⟩ := hs1 ⟨x, memv1⟩,
  obtain ⟨b2_nin_x, eq3⟩ := hs2 ⟨x, memv2⟩,
  dsimp only at eq1 eq2 eq3,
  erw [stalk_to_fiber_ring_hom_germ 𝒜 u1 ⟨x, memu1⟩ s1,
    stalk_to_fiber_ring_hom_germ 𝒜 u2 ⟨x, memu2⟩ s2] at eq1,
  erw eq1 at eq2,
  erw [eq2, quotient.eq] at eq3,
  change localization.mk _ _ = localization.mk _ _ at eq3,
  rw [localization.mk_eq_mk', is_localization.eq] at eq3,
  obtain ⟨⟨c, hc⟩, eq3⟩ := eq3,
  simp only [← subtype.val_eq_coe] at eq3,
  have eq3' : ∀ (y : projective_spectrum.Top 𝒜)
    (hy : y ∈ projective_spectrum.basic_open 𝒜 b1 ⊓
      projective_spectrum.basic_open 𝒜 b2 ⊓
      projective_spectrum.basic_open 𝒜 c),
    (localization.mk a1
      ⟨b1, show b1 ∉ y.as_homogeneous_ideal,
        by rw ←projective_spectrum.mem_basic_open;
          exact le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_left _ _) hy⟩ :
            localization.at_prime y.1.to_ideal) =
    localization.mk a2
      ⟨b2, show b2 ∉ y.as_homogeneous_ideal,
        by rw ←projective_spectrum.mem_basic_open;
        exact le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_right _ _) hy⟩,
  { intros y hy,
    rw [localization.mk_eq_mk', is_localization.eq],
    exact ⟨⟨c, show c ∉ y.as_homogeneous_ideal, by rw ←projective_spectrum.mem_basic_open;
      exact le_of_hom (opens.inf_le_right _ _) hy⟩, eq3⟩ },
  refine presheaf.germ_ext (Proj.structure_sheaf 𝒜).1
    (projective_spectrum.basic_open _ b1 ⊓
      projective_spectrum.basic_open _ b2 ⊓
      projective_spectrum.basic_open _ c ⊓ v1 ⊓ v2)
    ⟨⟨⟨⟨b1_nin_x, b2_nin_x⟩, hc⟩, memv1⟩, memv2⟩
    (opens.inf_le_left _ _ ≫ opens.inf_le_right _ _ ≫ i1) (opens.inf_le_right _ _ ≫ i2) _,
  rw subtype.ext_iff_val,
  ext1 y,
  simp only [res_apply],
  obtain ⟨b1_nin_y, eq6⟩ := hs1 ⟨_, le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_right _ _) y.2⟩,
  obtain ⟨b2_nin_y, eq7⟩ := hs2 ⟨_, le_of_hom (opens.inf_le_right _ _) y.2⟩,
  simp only at eq6 eq7,
  erw [eq6, eq7, quotient.eq],
  change localization.mk _ _ = localization.mk _ _,
  exact eq3' _ ⟨⟨le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_left _ _ ≫
      opens.inf_le_left _ _ ≫ opens.inf_le_left _ _) y.2,
    le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_left _ _ ≫
      opens.inf_le_left _ _ ≫ opens.inf_le_right _ _) y.2⟩,
    le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_left _ _ ≫
      opens.inf_le_right _ _) y.2⟩,
end, function.surjective_iff_has_right_inverse.mpr ⟨homogeneous_localization_to_stalk 𝒜 x,
  λ f, begin
    rw homogeneous_localization_to_stalk,
    erw stalk_to_fiber_ring_hom_germ 𝒜
      (projective_spectrum.basic_open 𝒜 f.denom) ⟨x, _⟩ (section_in_basic_open _ x f),
    simp only [section_in_basic_open, subtype.ext_iff_val, homogeneous_localization.ext_iff_val,
      homogeneous_localization.val_mk', f.eq_num_div_denom],
    refl,
  end⟩⟩

/--`Proj` of a graded ring as a `LocallyRingedSpace`-/
def Proj.to_LocallyRingedSpace : LocallyRingedSpace :=
{ local_ring := λ x, @@ring_equiv.local_ring _
    (show local_ring (at x), from infer_instance) _
    (Proj.stalk_iso' 𝒜 x).symm,
  ..(Proj.to_SheafedSpace 𝒜) }

end

end algebraic_geometry
