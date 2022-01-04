/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_geometry.projective_spectrum.topology
import algebraic_geometry.Spec
import algebra.category.CommRing.colimits
import algebra.category.CommRing.limits
import topology.sheaves.local_predicate
import ring_theory.localization
import algebraic_geometry.sheafed_space
import algebraic_geometry.locally_ringed_space
import ring_theory.graded_algebra.homogeneous_ideal

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

namespace algebraic_geometry

universe u

open_locale classical direct_sum big_operators pointwise
open direct_sum set_like

variables {ι R A: Type.{u}} [linear_ordered_cancel_add_comm_monoid ι]
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

open Top
open topological_space
open category_theory
open opposite
/--
The prime spectrum, just as a topological space.
-/
def projective_spectrum.Top : Top := Top.of (projective_spectrum 𝒜)

namespace projective_spectrum.structure_sheaf

/--
The type family over `prime_spectrum R` consisting of the localization over each point.
-/
-- @[derive [comm_ring]]
-- def localizations (P : projective_spectrum.Top 𝒜) :=
-- localization.at_prime P.as_homogeneous_ideal.1

@[derive [comm_ring]]
def hartshorne_localisation (x : projective_spectrum.Top 𝒜) : Type* :=
(subring.mk
  {y : (localization.at_prime x.as_homogeneous_ideal.1) |
    ∃ (a b : A) (i : ι) (a_hom : a ∈ 𝒜 i) (b_hom : b ∈ 𝒜 i) (b_nin : b ∉ x.as_homogeneous_ideal),
    y = (localization.mk a ⟨b, b_nin⟩ : (localization.at_prime x.as_homogeneous_ideal.1))}
  begin
    refine ⟨1, 1, 0, set_like.has_graded_one.one_mem, set_like.has_graded_one.one_mem, _, _⟩,
    erw ←ideal.ne_top_iff_one, exact x.is_prime.ne_top,
    simp only [is_localization.mk'_self, localization.mk_eq_mk'],
  end begin
    rintros y1 y2 ⟨a1, b1, i1, a1_hom, b1_hom, b1_nin, hy1⟩
      ⟨a2, b2, i2, a2_hom, b2_hom, b2_nin, hy2⟩,
    rw [hy1, hy2, localization.mk_mul],
    refine ⟨a1 * a2, b1 * b2, i1 + i2, set_like.graded_monoid.mul_mem a1_hom a2_hom,
      set_like.graded_monoid.mul_mem b1_hom b2_hom, _, rfl⟩,
  end begin
    refine ⟨0, 1, 0, submodule.zero_mem _, set_like.has_graded_one.one_mem, _, _⟩,
    erw ←ideal.ne_top_iff_one, exact x.is_prime.ne_top,
    rw localization.mk_zero,
  end begin
    rintros y1 y2 ⟨a1, b1, i1, a1_hom, b1_hom, b1_nin, hy1⟩
      ⟨a2, b2, i2, a2_hom, b2_hom, b2_nin, hy2⟩,
    refine ⟨a1 * b2 + a2 * b1, b1 * b2, i1 + i2,
      submodule.add_mem _ (set_like.graded_monoid.mul_mem a1_hom b2_hom) _,
      set_like.graded_monoid.mul_mem b1_hom b2_hom, λ h, _, _⟩,
    { rw add_comm, refine set_like.graded_monoid.mul_mem a2_hom b1_hom, },
    { cases ideal.is_prime.mem_or_mem x.is_prime h with h' h',
      apply b1_nin, exact h', apply b2_nin, exact h', },
    { rw [hy1, hy2, localization.add_mk],
      simp only [subtype.coe_mk, localization.mk_eq_mk'],
      congr' 1, ring, },
  end begin
    rintro y ⟨a, b, i, a_hom, b_hom, b_nin, hy⟩,
    refine ⟨-a, b, i, submodule.neg_mem _ a_hom, b_hom, b_nin, _⟩,
    rw [hy, localization.neg_mk],
  end)

-- instance (P : projective_spectrum.Top 𝒜) : inhabited (localizations 𝒜 P) :=
-- ⟨1⟩

-- instance (U : opens (projective_spectrum.Top 𝒜)) (x : U) :
--   algebra A (localizations 𝒜 x) :=
-- localization.algebra

-- instance (U : opens (projective_spectrum.Top 𝒜)) (x : U) :
--   is_localization.at_prime (localizations 𝒜 x)
--   (x : projective_spectrum.Top 𝒜).as_homogeneous_ideal.1 :=
-- localization.is_localization

lemma hartshorne_localisation.val_add (x : projective_spectrum.Top 𝒜)
  (f g : hartshorne_localisation 𝒜 x) : (f + g).val = f.val + g.val := rfl

lemma hartshorne_localisation.val_neg (x : projective_spectrum.Top 𝒜)
  (f : hartshorne_localisation 𝒜 x) : (-f).val = -f.val := rfl

lemma hartshorne_localisation.val_mul (x : projective_spectrum.Top 𝒜)
  (f g : hartshorne_localisation 𝒜 x) : (f * g).val = f.val * g.val := rfl

lemma hartshorne_localisation.val_sub (x : projective_spectrum.Top 𝒜)
  (f g : hartshorne_localisation 𝒜 x) : (f - g).val = f.val - g.val := rfl

lemma hartshorne_localisation.val_zero (x : projective_spectrum.Top 𝒜) :
  (0 : hartshorne_localisation 𝒜 x).val = localization.mk 0 1 :=
begin
  rw localization.mk_zero, refl
end

lemma hartshorne_localisation.val_one (x : projective_spectrum.Top 𝒜) :
  (1 : hartshorne_localisation 𝒜 x).val = localization.mk 1 1 :=
begin
  rw localization.mk_one, refl
end

lemma hartshorne_localisation.ext (x y : projective_spectrum.Top 𝒜)
   (hxy : y.as_homogeneous_ideal ≤ x.as_homogeneous_ideal)
  (a a' b b' : A) (i i' : ι) (a_hom : a ∈ 𝒜 i) (b_hom : b ∈ 𝒜 i)
  (a_hom' : a' ∈ 𝒜 i') (b_hom' : b' ∈ 𝒜 i')
  (b_ninx : b ∉ x.as_homogeneous_ideal) (b_ninx' : b' ∉ x.as_homogeneous_ideal)
  (b_niny : b ∉ y.as_homogeneous_ideal) (b_niny' : b' ∉ y.as_homogeneous_ideal)
  (eq1 :
    (⟨localization.mk a ⟨b, b_ninx⟩, ⟨a, b, i, a_hom, b_hom, b_ninx, rfl⟩⟩ :
      hartshorne_localisation 𝒜 x) =
    (⟨localization.mk a' ⟨b', b_ninx'⟩, ⟨a', b', i', a_hom', b_hom', b_ninx', rfl⟩⟩ :
      hartshorne_localisation 𝒜 x)) :
  (⟨localization.mk a ⟨b, b_niny⟩, ⟨a, b, i, a_hom, b_hom, b_niny, rfl⟩⟩ :
      hartshorne_localisation 𝒜 y) =
    (⟨localization.mk a' ⟨b', b_niny'⟩, ⟨a', b', i', a_hom', b_hom', b_niny', rfl⟩⟩ :
      hartshorne_localisation 𝒜 y) :=
begin
  rw [subtype.ext_iff_val] at eq1 ⊢, dsimp only at eq1 ⊢,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq1 ⊢,
  obtain ⟨⟨c, hc⟩, eq1⟩ := eq1, use c, intro h, apply hc, apply hxy, exact h,
  erw eq1, refl,
end

variables {𝒜}

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (projective_spectrum.Top 𝒜)}
  (f : Π x : U, hartshorne_localisation 𝒜 x) : Prop :=
∃ (r s : A) (i : ι) (r_hom : r ∈ 𝒜 i) (s_hom : s ∈ 𝒜 i),
  ∀ x : U, ∃ (s_nin : ¬ (s ∈ x.1.as_homogeneous_ideal)),
  f x = ⟨localization.mk r ⟨s, s_nin⟩, ⟨r, s, i, r_hom, s_hom, s_nin, rfl⟩⟩

lemma is_fraction.eq_mk' {U : opens (projective_spectrum.Top 𝒜)}
  {f : Π x : U, hartshorne_localisation 𝒜 x}
  (hf : is_fraction f) :
  ∃ (r s : A) (i : ι) (r_hom : r ∈ 𝒜 i) (s_hom : s ∈ 𝒜 i),
    ∀ x : U, ∃ (s_nin : s ∉ x.1.as_homogeneous_ideal),
    f x =
    ⟨localization.mk r ⟨s, s_nin⟩, ⟨r, s, i, r_hom, s_hom, s_nin, rfl⟩⟩ :=
begin
  rcases hf with ⟨r, s, i, r_hom, s_hom, h⟩,
  refine ⟨r, s, i, r_hom, s_hom, h⟩,
end

variables (𝒜)

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (hartshorne_localisation 𝒜) :=
{ pred := λ U f, is_fraction f,
  res := by { rintros V U i f ⟨r, s, j, r_hom, s_hom, w⟩,
    refine ⟨r, s, j, r_hom, s_hom, λ y, w (i y)⟩ } }

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

def is_locally_fraction : local_predicate (hartshorne_localisation 𝒜) :=
(is_fraction_prelocal 𝒜).sheafify

/--
The functions satisfying `is_locally_fraction` form a subring.
-/
def sections_subring (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  subring (Π x : unop U, hartshorne_localisation 𝒜 x) :=
{ carrier := { f | (is_locally_fraction 𝒜).pred f },
  zero_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 0, 1, 0, submodule.zero_mem _,
      set_like.has_graded_one.one_mem, λ y, ⟨_, _⟩⟩,
    { erw ←ideal.ne_top_iff_one ((y : projective_spectrum.Top 𝒜).as_homogeneous_ideal.1),
      exact y.1.is_prime.1, },
    { simp only [pi.zero_apply],
      rw subtype.ext_iff_val, dsimp only,
      rw localization.mk_zero, refl,},
  end,
  one_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 1, 1, 0,
      set_like.has_graded_one.one_mem, set_like.has_graded_one.one_mem, λ y, ⟨_, _⟩⟩,
    { erw ←ideal.ne_top_iff_one ((y : projective_spectrum.Top 𝒜).as_homogeneous_ideal.1),
      exact y.1.is_prime.1, },
    { simp only [pi.one_apply],
      rw subtype.ext_iff_val, dsimp only,
      erw localization.mk_one, refl, },
  end,
  add_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, ja, ra_hom, sa_hom, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, jb, rb_hom, sb_hom, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * sb + rb * sa, sa * sb, ja + jb,
      submodule.add_mem _ (set_like.graded_monoid.mul_mem ra_hom sb_hom) _,
      set_like.graded_monoid.mul_mem sa_hom sb_hom,
      λ y, ⟨λ h, _, _⟩⟩,
    { rw add_comm, apply set_like.graded_monoid.mul_mem,
      exact rb_hom, exact sa_hom, },
    { have := (y : projective_spectrum.Top 𝒜).is_prime.mem_or_mem h, cases this,
      obtain ⟨nin, hy⟩ := (wa ⟨y, _⟩), apply nin, exact this,
      suffices : y.1 ∈ Va, exact this,
      exact (opens.inf_le_left Va Vb y).2,
      obtain ⟨nin, hy⟩ := (wb ⟨y, _⟩), apply nin, exact this,
      suffices : y.1 ∈ Vb, exact this,
      exact (opens.inf_le_right Va Vb y).2, },
    { simp only [add_mul, ring_hom.map_add, pi.add_apply, ring_hom.map_mul],
      choose nin hy using (wa (opens.inf_le_left Va Vb y)),
      erw hy,
      choose nin hy using (wb (opens.inf_le_right Va Vb y)),
      erw hy, rw subtype.ext_iff_val, dsimp only,
      rw [hartshorne_localisation.val_add], dsimp only,
      rw [localization.add_mk],
      congr' 1, rw [add_comm], congr' 1,
      rw [mul_comm], refl,
      rw [mul_comm], refl, }
  end,
  neg_mem' :=
  begin
    intros a ha x,
    rcases ha x with ⟨V, m, i, r, s, j, r_hom_j, s_hom_j, w⟩,
    refine ⟨V, m, i, -r, s, j, submodule.neg_mem _ r_hom_j, s_hom_j, λ y, ⟨_, _⟩⟩,
    choose nin hy using w y, exact nin,
    choose nin hy using w y,
    simp only [ring_hom.map_neg, pi.neg_apply],
    erw hy, rw [subtype.ext_iff_val, hartshorne_localisation.val_neg], dsimp only,
    rw localization.neg_mk,
  end,
  mul_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, ja, ra_hom_ja, sa_hom_ja, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, jb, rb_hom_jb, sb_hom_jb, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * rb, sa * sb,
      ja + jb, set_like.graded_monoid.mul_mem ra_hom_ja rb_hom_jb,
        set_like.graded_monoid.mul_mem sa_hom_ja sb_hom_jb, λ y, ⟨λ h, _, _⟩⟩,
    { have := (y : projective_spectrum.Top 𝒜).is_prime.mem_or_mem h, cases this,
      choose nin hy using wa ⟨y, (opens.inf_le_left Va Vb y).2⟩,
      apply nin, exact this,
      choose nin hy using wb ⟨y, (opens.inf_le_right Va Vb y).2⟩,
      apply nin, exact this, },
    { simp only [pi.mul_apply, ring_hom.map_mul],
      choose nin hy1 using wa (opens.inf_le_left Va Vb y),
      choose nin hy2 using wb (opens.inf_le_right Va Vb y),
      erw [hy1, hy2], rw [subtype.ext_iff_val, hartshorne_localisation.val_mul],
      dsimp only, rw [localization.mk_mul], refl, }
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

@[simp] lemma res_apply (U V : opens (projective_spectrum.Top 𝒜)) (i : V ⟶ U)
  (s : (structure_sheaf 𝒜).1.obj (op U)) (x : V) :
  ((structure_sheaf 𝒜).1.map i.op s).1 x = (s.1 (i x) : _) :=
rfl

def Proj.to_SheafedSpace : SheafedSpace CommRing :=
{ carrier := Top.of (projective_spectrum 𝒜),
  presheaf := (structure_sheaf 𝒜).1,
  is_sheaf := (structure_sheaf 𝒜).2 }

-- CommRing.of (localization
--   { carrier := {r : A | r ∈ 𝒜 0 ∧ r ∉ x.as_homogeneous_ideal },
--     one_mem' := ⟨set_like.has_graded_one.one_mem, begin
--       erw ←ideal.ne_top_iff_one x.as_homogeneous_ideal.1,
--       exact x.is_prime.ne_top,
--     end⟩,
--     mul_mem' := λ a b ha hb, ⟨begin
--       suffices : a * b ∈ 𝒜 (0 + 0),
--       convert this, rw zero_add,
--       apply set_like.graded_monoid.mul_mem, exact ha.1, exact hb.1,
--     end, λ h, begin
--       have := ideal.is_prime.mem_or_mem (x.is_prime) h, cases this,
--       apply ha.2, exact this, apply hb.2, exact this,
--     end⟩ })

def open_to_localization (U : opens (projective_spectrum.Top 𝒜)) (x : projective_spectrum.Top 𝒜)
  (hx : x ∈ U) :
  (structure_sheaf 𝒜).1.obj (op U) ⟶ CommRing.of (hartshorne_localisation 𝒜 x) :=
{ to_fun := λ s, (s.1 ⟨x, hx⟩ : _),
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

def stalk_to_fiber_ring_hom (x : projective_spectrum.Top 𝒜) :
  (structure_sheaf 𝒜).1.stalk x ⟶ CommRing.of (hartshorne_localisation 𝒜 x) :=
limits.colimit.desc (((open_nhds.inclusion x).op) ⋙ (structure_sheaf 𝒜).1)
  { X := _,
    ι :=
    { app := λ U, open_to_localization 𝒜 ((open_nhds.inclusion _).obj (unop U)) x (unop U).2, } }

@[simp] lemma germ_comp_stalk_to_fiber_ring_hom (U : opens (projective_spectrum.Top 𝒜)) (x : U) :
  (structure_sheaf 𝒜).1.germ x ≫ stalk_to_fiber_ring_hom 𝒜 x =
  open_to_localization 𝒜 U x x.2 :=
limits.colimit.ι_desc _ _

@[simp] lemma stalk_to_fiber_ring_hom_germ' (U : opens (projective_spectrum.Top 𝒜))
  (x : projective_spectrum.Top 𝒜) (hx : x ∈ U) (s : (structure_sheaf 𝒜).1.obj (op U)) :
  stalk_to_fiber_ring_hom 𝒜 x ((structure_sheaf 𝒜).1.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
ring_hom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom 𝒜 U ⟨x, hx⟩ : _) s

@[simp] lemma stalk_to_fiber_ring_hom_germ (U : opens (projective_spectrum.Top 𝒜)) (x : U)
  (s : (structure_sheaf 𝒜).1.obj (op U)) :
  stalk_to_fiber_ring_hom 𝒜 x ((structure_sheaf 𝒜).1.germ x s) = s.1 x :=
by { cases x, exact stalk_to_fiber_ring_hom_germ' 𝒜 U _ _ _ }

def stalk_iso (x : projective_spectrum.Top 𝒜) :
  (structure_sheaf 𝒜).1.stalk x ≃+* CommRing.of (hartshorne_localisation 𝒜 x)  :=
sorry

def hartshorne_localisation.is_local (x : projective_spectrum.Top 𝒜) :
  local_ring (hartshorne_localisation 𝒜 x) :=
{ exists_pair_ne := ⟨0, 1, λ rid, begin
    rw subtype.ext_iff_val at rid,
    rw hartshorne_localisation.val_zero at rid,
    rw hartshorne_localisation.val_one at rid,
    simpa only [localization.mk_eq_mk', is_localization.mk'_eq_iff_eq, mul_one, map_one,
      submonoid.coe_one, zero_ne_one, map_zero] using rid,
  end⟩,
  is_local := λ ⟨a, ha⟩, begin
  induction a with r s,
  rcases ha with ⟨r', s', i, r'_hom, s'_hom, s'_nin, eq1⟩,
  by_cases mem1 : r' ∈ x.as_homogeneous_ideal.1,
  { right,
    have : s' - r' ∉ x.as_homogeneous_ideal.1,
    { intro h, apply s'_nin,
      convert submodule.add_mem' _ h mem1, rw sub_add_cancel, },
    apply is_unit_of_mul_eq_one, swap,
    refine ⟨(localization.mk s' ⟨s' - r', this⟩), s', s' - r', i, s'_hom,
      submodule.sub_mem _ s'_hom r'_hom, this, rfl⟩,
    rw [sub_mul, subtype.ext_iff_val, hartshorne_localisation.val_sub,
      hartshorne_localisation.val_mul, hartshorne_localisation.val_mul],
    dsimp only, erw [eq1, localization.mk_mul, one_mul, sub_eq_add_neg, localization.neg_mk,
      localization.add_mk, ←subtype.val_eq_coe, ←subtype.val_eq_coe],
    dsimp only,
    suffices : localization.mk ((s' - r') * -(r' * s') + s' * (s' - r') * s')
      ⟨(s' - r') * (s' * (s' - r')), _⟩ = 1,
    convert this,
    convert localization.mk_self _,
    ring_nf, },
  { left, apply is_unit_of_mul_eq_one, swap,
    refine ⟨localization.mk s' ⟨r', mem1⟩, s', r', i, s'_hom, r'_hom, mem1, rfl⟩,
    rw [subtype.ext_iff_val, hartshorne_localisation.val_mul], dsimp only,
    rw [eq1, localization.mk_mul],
    convert localization.mk_self _, rw mul_comm, refl, },
  refl,
end}

def Proj.to_LocallyRingedSpace : LocallyRingedSpace :=
{ local_ring := λ x, @@ring_equiv.local_ring _
    (show local_ring (hartshorne_localisation 𝒜 x), from hartshorne_localisation.is_local 𝒜 x) _
    (stalk_iso 𝒜 x).symm,
  ..(Proj.to_SheafedSpace 𝒜) }


end projective_spectrum.structure_sheaf


end algebraic_geometry
