/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import topology.sheaves.forget
import category_theory.limits.shapes.types
import topology.sheaves.sheaf
import category_theory.types

/-!
# The sheaf condition in terms of unique gluings

We provide an alternative formulation of the sheaf condition in terms of unique gluings.

We work with sheaves valued in a concrete category `C` admitting all limits, whose forgetful
functor `C ⥤ Type` preserves limits and reflects isomorphisms. The usual categories of algebraic
structures, such as `Mon`, `AddCommGroup`, `Ring`, `CommRing` etc. are all examples of this kind of
category.

A presheaf `F : presheaf C X` satisfies the sheaf condition if and only if, for every
compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique gluing
`s : F.obj (op (supr U))`.

Here, the family `sf` is called compatible, if for all `i j : ι`, the restrictions of `sf i`
and `sf j` to `U i ⊓ U j` agree. A section `s : F.obj (op (supr U))` is a gluing for the
family `sf`, if `s` restricts to `sf i` on `U i` for all `i : ι`

We show that the sheaf condition in terms of unique gluings is equivalent to the definition
in terms of equalizers. Our approach is as follows: First, we show them to be equivalent for
`Type`-valued presheaves. Then we use that composing a presheaf with a limit-preserving and
isomorphism-reflecting functor leaves the sheaf condition invariant, as shown in
`topology/sheaves/forget.lean`.

-/

noncomputable theory

open Top
open Top.presheaf
open Top.presheaf.sheaf_condition_equalizer_products
open category_theory
open category_theory.limits
open topological_space
open topological_space.opens
open opposite

universes u v

variables {C : Type u} [category.{v} C] [concrete_category.{v} C]

namespace Top

namespace presheaf

section

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

/--
A family of sections `sf` is compatible, if the restrictions of `sf i` and `sf j` to `U i ⊓ U j`
agree, for all `i` and `j`
-/
def is_compatible (sf : Π i : ι, F.obj (op (U i))) : Prop :=
  ∀ i j : ι, F.map (inf_le_left (U i) (U j)).op (sf i) = F.map (inf_le_right (U i) (U j)).op (sf j)

/--
A section `s` is a gluing for a family of sections `sf` if it restricts to `sf i` on `U i`,
for all `i`
-/
def is_gluing (sf : Π i : ι, F.obj (op (U i))) (s : F.obj (op (supr U))) : Prop :=
∀ i : ι, F.map (opens.le_supr U i).op s = sf i

/--
The sheaf condition in terms of unique gluings. A presheaf `F : presheaf C X` satisfies this sheaf
condition if and only if, for every compatible family of sections `sf : Π i : ι, F.obj (op (U i))`,
there exists a unique gluing `s : F.obj (op (supr U))`.

We prove this to be equivalent to the usual one below in
`is_sheaf_iff_is_sheaf_unique_gluing`
-/
def is_sheaf_unique_gluing : Prop :=
∀ ⦃ι : Type v⦄ (U : ι → opens X) (sf : Π i : ι, F.obj (op (U i))),
  is_compatible F U sf → ∃! s : F.obj (op (supr U)), is_gluing F U sf s

end

section type_valued

variables {X : Top.{v}} (F : presheaf (Type v) X) {ι : Type v} (U : ι → opens X)

/--
For presheaves of types, terms of `pi_opens F U` are just families of sections.
-/
def pi_opens_iso_sections_family : pi_opens F U ≅ Π i : ι, F.obj (op (U i)) :=
limits.is_limit.cone_point_unique_up_to_iso
  (limit.is_limit (discrete.functor (λ i : ι, F.obj (op (U i)))))
  ((types.product_limit_cone (λ i : ι, F.obj (op (U i)))).is_limit)

/--
Under the isomorphism `pi_opens_iso_sections_family`, compatibility of sections is the same
as being equalized by the arrows `left_res` and `right_res` of the equalizer diagram.
-/
lemma compatible_iff_left_res_eq_right_res (sf : pi_opens F U) :
  is_compatible F U ((pi_opens_iso_sections_family F U).hom sf)
    ↔ left_res F U sf = right_res F U sf :=
begin
  split ; intros h,
  { ext ⟨i, j⟩,
    rw [left_res, types.limit.lift_π_apply', fan.mk_π_app,
        right_res, types.limit.lift_π_apply', fan.mk_π_app],
    exact h i j, },
  { intros i j,
    convert congr_arg (limits.pi.π (λ p : ι × ι, F.obj (op (U p.1 ⊓ U p.2))) (i,j)) h,
    { rw [left_res, types.pi_lift_π_apply], refl },
    { rw [right_res, types.pi_lift_π_apply], refl } }
end

/--
Under the isomorphism `pi_opens_iso_sections_family`, being a gluing of a family of
sections `sf` is the same as lying in the preimage of `res` (the leftmost arrow of the
equalizer diagram).
-/
@[simp]
lemma is_gluing_iff_eq_res (sf : pi_opens F U) (s : F.obj (op (supr U))):
  is_gluing F U ((pi_opens_iso_sections_family F U).hom sf) s ↔ res F U s = sf :=
begin
  split ; intros h,
  { ext i,
    rw [res, types.limit.lift_π_apply', fan.mk_π_app],
    exact h i, },
  { intro i,
    convert congr_arg (limits.pi.π (λ i : ι, F.obj (op (U i))) i) h,
    rw [res, types.pi_lift_π_apply],
    refl },
end

/--
The "equalizer" sheaf condition can be obtained from the sheaf condition
in terms of unique gluings.
-/
lemma is_sheaf_of_is_sheaf_unique_gluing_types (Fsh : F.is_sheaf_unique_gluing) :
  F.is_sheaf :=
begin
  intros ι U,
  refine ⟨fork.is_limit.mk' _ _⟩,
  intro s,
  have h_compatible : ∀ x : s.X,
    F.is_compatible U ((F.pi_opens_iso_sections_family U).hom (s.ι x)),
  { intro x,
    rw compatible_iff_left_res_eq_right_res,
    convert congr_fun s.condition x, },
  choose m m_spec m_uniq using
    λ x : s.X, Fsh U ((pi_opens_iso_sections_family F U).hom (s.ι x)) (h_compatible x),
  refine ⟨m, _, _⟩,
  { ext i x,
    simp [res],
    exact m_spec x i, },
  { intros l hl,
    ext x,
    apply m_uniq,
    rw is_gluing_iff_eq_res,
    exact congr_fun hl x },
end

/--
The sheaf condition in terms of unique gluings can be obtained from the usual
"equalizer" sheaf condition.
-/
lemma is_sheaf_unique_gluing_of_is_sheaf_types (Fsh : F.is_sheaf) :
  F.is_sheaf_unique_gluing :=
begin
  intros ι U sf hsf,
  let sf' := (pi_opens_iso_sections_family F U).inv sf,
  have hsf' : left_res F U sf' = right_res F U sf',
  { rwa [← compatible_iff_left_res_eq_right_res F U sf', inv_hom_id_apply] },
  choose s s_spec s_uniq using types.unique_of_type_equalizer _ _ (Fsh U).some sf' hsf',
  use s,
  dsimp,
  split,
  { convert (is_gluing_iff_eq_res F U sf' _).mpr s_spec,
    rw inv_hom_id_apply },
  { intros y hy,
    apply s_uniq,
    rw ← is_gluing_iff_eq_res F U,
    convert hy,
    rw inv_hom_id_apply, },
end

/--
For type-valued presheaves, the sheaf condition in terms of unique gluings is equivalent to the
usual sheaf condition in terms of equalizer diagrams.
-/
lemma is_sheaf_iff_is_sheaf_unique_gluing_types :
  F.is_sheaf ↔ F.is_sheaf_unique_gluing :=
iff.intro (is_sheaf_unique_gluing_of_is_sheaf_types F)
  (is_sheaf_of_is_sheaf_unique_gluing_types F)

end type_valued

section

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variables [has_limits C] [reflects_isomorphisms (forget C)] [preserves_limits (forget C)]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

/--
For presheaves valued in a concrete category, whose forgetful functor reflects isomorphisms and
preserves limits, the sheaf condition in terms of unique gluings is equivalent to the usual one
in terms of equalizer diagrams.
-/
lemma is_sheaf_iff_is_sheaf_unique_gluing :
  F.is_sheaf ↔ F.is_sheaf_unique_gluing :=
iff.trans (is_sheaf_iff_is_sheaf_comp (forget C) F)
  (is_sheaf_iff_is_sheaf_unique_gluing_types (F ⋙ forget C))

end

end presheaf

namespace sheaf

open presheaf
open category_theory

section

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variables [has_limits C] [reflects_isomorphisms (concrete_category.forget C)]
variables [preserves_limits (concrete_category.forget C)]

variables {X : Top.{v}} (F : sheaf C X) {ι : Type v} (U : ι → opens X)

/--
A more convenient way of obtaining a unique gluing of sections for a sheaf.
-/
lemma exists_unique_gluing (sf : Π i : ι, F.1.obj (op (U i)))
  (h : is_compatible F.1 U sf ) :
  ∃! s : F.1.obj (op (supr U)), is_gluing F.1 U sf s :=
(is_sheaf_iff_is_sheaf_unique_gluing F.1).mp F.property U sf h

/--
In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
lemma exists_unique_gluing' (V : opens X) (iUV : Π i : ι, U i ⟶ V) (hcover : V ≤ supr U)
  (sf : Π i : ι, F.1.obj (op (U i))) (h : is_compatible F.1 U sf) :
  ∃! s : F.1.obj (op V), ∀ i : ι, F.1.map (iUV i).op s = sf i :=
begin
  have V_eq_supr_U : V = supr U := le_antisymm hcover (supr_le (λ i, (iUV i).le)),
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.exists_unique_gluing U sf h,
  refine ⟨F.1.map (eq_to_hom V_eq_supr_U).op gl, _, _⟩,
  { intro i,
    rw [← comp_apply, ← F.1.map_comp],
    exact gl_spec i },
  { intros gl' gl'_spec,
    convert congr_arg _ (gl_uniq (F.1.map (eq_to_hom V_eq_supr_U.symm).op gl') (λ i,_)) ;
      rw [← comp_apply, ← F.1.map_comp],
    { rw [eq_to_hom_op, eq_to_hom_op, eq_to_hom_trans, eq_to_hom_refl,
      F.1.map_id, id_apply] },
    { convert gl'_spec i } }
end

@[ext]
lemma eq_of_locally_eq (s t : F.1.obj (op (supr U)))
  (h : ∀ i, F.1.map (opens.le_supr U i).op s = F.1.map (opens.le_supr U i).op t) :
  s = t :=
begin
  let sf : Π i : ι, F.1.obj (op (U i)) := λ i, F.1.map (opens.le_supr U i).op s,
  have sf_compatible : is_compatible _ U sf,
  { intros i j, simp_rw [← comp_apply, ← F.1.map_comp], refl },
  obtain ⟨gl, -, gl_uniq⟩ := F.exists_unique_gluing U sf sf_compatible,
  transitivity gl,
  { apply gl_uniq, intro i, refl },
  { symmetry, apply gl_uniq, intro i, rw ← h },
end

/--
In this version of the lemma, the inclusion homs `iUV` can be specified directly by the user,
which can be more convenient in practice.
-/
lemma eq_of_locally_eq' (V : opens X) (iUV : Π i : ι, U i ⟶ V) (hcover : V ≤ supr U)
  (s t : F.1.obj (op V))
  (h : ∀ i, F.1.map (iUV i).op s = F.1.map (iUV i).op t) : s = t :=
begin
  have V_eq_supr_U : V = supr U := le_antisymm hcover (supr_le (λ i, (iUV i).le)),
  suffices : F.1.map (eq_to_hom V_eq_supr_U.symm).op s =
             F.1.map (eq_to_hom V_eq_supr_U.symm).op t,
  { convert congr_arg (F.1.map (eq_to_hom V_eq_supr_U).op) this ;
    rw [← comp_apply, ← F.1.map_comp, eq_to_hom_op, eq_to_hom_op, eq_to_hom_trans,
      eq_to_hom_refl, F.1.map_id, id_apply] },
  apply eq_of_locally_eq,
  intro i,
  rw [← comp_apply, ← comp_apply, ← F.1.map_comp],
  convert h i,
end

end

end sheaf

end Top
