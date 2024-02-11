/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import topology.sheaves.sheaf_condition.opens_le_cover
import category_theory.limits.final
import category_theory.limits.preserves.basic
import category_theory.category.pairwise
import category_theory.limits.constructions.binary_products
import algebra.category.Ring.constructions

/-!
# Equivalent formulations of the sheaf condition

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → opens X` provides a functor `diagram U : overlap ι ⥤ (opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `supr U`,
and in fact this is a limit cone.

A presheaf `F : presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `is_limit (F.map_cone (cone U))`, or
* `preserves_limit (diagram U) F`

We show that this sheaf condition is equivalent to the `opens_le_cover` sheaf condition, and
thereby also equivalent to the default sheaf condition.
-/

noncomputable theory

universes w v u

open topological_space Top opposite category_theory category_theory.limits

variables {C : Type u} [category.{v} C] {X : Top.{w}}

namespace Top.presheaf

section

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_pairwise_intersections`).

A presheaf is a sheaf if `F` sends the cone `(pairwise.cocone U).op` to a limit cone.
(Recall `pairwise.cocone U` has cone point `supr U`, mapping down to the `U i` and the `U i ⊓ U j`.)
-/
def is_sheaf_pairwise_intersections (F : presheaf C X) : Prop :=
∀ ⦃ι : Type w⦄ (U : ι → opens X), nonempty (is_limit (F.map_cone (pairwise.cocone U).op))

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections`).

A presheaf is a sheaf if `F` preserves the limit of `pairwise.diagram U`.
(Recall `pairwise.diagram U` is the diagram consisting of the pairwise intersections
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `supr U`.)
-/
def is_sheaf_preserves_limit_pairwise_intersections (F : presheaf C X) : Prop :=
∀ ⦃ι : Type w⦄ (U : ι → opens X), nonempty (preserves_limit (pairwise.diagram U).op F)

end

namespace sheaf_condition

variables {ι : Type w} (U : ι → opens X)

open category_theory.pairwise

/--
Implementation detail:
the object level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
@[simp]
def pairwise_to_opens_le_cover_obj : pairwise ι → opens_le_cover U
| (single i) := ⟨U i, ⟨i, le_rfl⟩⟩
| (pair i j) := ⟨U i ⊓ U j, ⟨i, inf_le_left⟩⟩

open category_theory.pairwise.hom

/--
Implementation detail:
the morphism level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
def pairwise_to_opens_le_cover_map :
  Π {V W : pairwise ι},
    (V ⟶ W) → (pairwise_to_opens_le_cover_obj U V ⟶ pairwise_to_opens_le_cover_obj U W)
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _
| _ _ (left i j) := hom_of_le inf_le_left
| _ _ (right i j) := hom_of_le inf_le_right

/--
The category of single and double intersections of the `U i` maps into the category
of open sets below some `U i`.
-/
@[simps]
def pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U :=
{ obj := pairwise_to_opens_le_cover_obj U,
  map := λ V W i, pairwise_to_opens_le_cover_map U i, }

instance (V : opens_le_cover U) :
  nonempty (structured_arrow V (pairwise_to_opens_le_cover U)) :=
⟨@structured_arrow.mk _ _ _ _ _ (single (V.index)) _ (by exact V.hom_to_index)⟩

/--
The diagram consisting of the `U i` and `U i ⊓ U j` is cofinal in the diagram
of all opens contained in some `U i`.
-/
-- This is a case bash: for each pair of types of objects in `pairwise ι`,
-- we have to explicitly construct a zigzag.
instance : functor.final (pairwise_to_opens_le_cover U) :=
⟨λ V, is_connected_of_zigzag $ λ A B, begin
  rcases A with ⟨⟨⟨⟩⟩, ⟨i⟩|⟨i,j⟩, a⟩;
  rcases B with ⟨⟨⟨⟩⟩, ⟨i'⟩|⟨i',j'⟩, b⟩;
  dsimp at *,
  { refine ⟨[
    { left := ⟨⟨⟩⟩, right := pair i i',
      hom := (le_inf a.le b.le).hom, }, _], _, rfl⟩,
    exact
      list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
        (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩) list.chain.nil) },
  { refine ⟨[
    { left := ⟨⟨⟩⟩, right := pair i' i,
      hom := (le_inf (b.le.trans inf_le_left) a.le).hom, },
    { left := ⟨⟨⟩⟩, right := single i',
      hom := (b.le.trans inf_le_left).hom, }, _], _, rfl⟩,
    exact
      list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := right i' i, }⟩)
        (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i' i, }⟩)
          (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i' j', }⟩) list.chain.nil)) },
  { refine ⟨[
    { left := ⟨⟨⟩⟩, right := single i,
      hom := (a.le.trans inf_le_left).hom, },
    { left := ⟨⟨⟩⟩, right := pair i i', hom :=
      (le_inf (a.le.trans inf_le_left) b.le).hom, }, _], _, rfl⟩,
    exact
      list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i j, }⟩)
        (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
          (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩) list.chain.nil)) },
  { refine ⟨[
    { left := ⟨⟨⟩⟩, right := single i,
      hom := (a.le.trans inf_le_left).hom, },
    { left := ⟨⟨⟩⟩, right := pair i i',
      hom := (le_inf (a.le.trans inf_le_left) (b.le.trans inf_le_left)).hom, },
    { left := ⟨⟨⟩⟩, right := single i',
      hom := (b.le.trans inf_le_left).hom, }, _], _, rfl⟩,
    exact
      list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := left i j, }⟩)
      (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i i', }⟩)
      (list.chain.cons (or.inl ⟨{ left := 𝟙 _, right := right i i', }⟩)
      (list.chain.cons (or.inr ⟨{ left := 𝟙 _, right := left i' j', }⟩) list.chain.nil))), },
end⟩

/--
The diagram in `opens X` indexed by pairwise intersections from `U` is isomorphic
(in fact, equal) to the diagram factored through `opens_le_cover U`.
-/
def pairwise_diagram_iso :
  pairwise.diagram U ≅
  pairwise_to_opens_le_cover U ⋙ full_subcategory_inclusion _ :=
{ hom := { app := begin rintro (i|⟨i,j⟩); exact 𝟙 _, end, },
  inv := { app := begin rintro (i|⟨i,j⟩); exact 𝟙 _, end, }, }

/--
The cocone `pairwise.cocone U` with cocone point `supr U` over `pairwise.diagram U` is isomorphic
to the cocone `opens_le_cover_cocone U` (with the same cocone point)
after appropriate whiskering and postcomposition.
-/
def pairwise_cocone_iso :
  (pairwise.cocone U).op ≅
  (cones.postcompose_equivalence (nat_iso.op (pairwise_diagram_iso U : _) : _)).functor.obj
    ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op) :=
cones.ext (iso.refl _) (by tidy)

end sheaf_condition

open sheaf_condition

variable (F : presheaf C X)

/--
The sheaf condition
in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`
is equivalent to the reformulation
in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
lemma is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections :
  F.is_sheaf_opens_le_cover ↔ F.is_sheaf_pairwise_intersections :=
forall₂_congr $ λ ι U, equiv.nonempty_congr $
  calc is_limit (F.map_cone (opens_le_cover_cocone U).op)
    ≃ is_limit ((F.map_cone (opens_le_cover_cocone U).op).whisker (pairwise_to_opens_le_cover U).op)
        : (functor.initial.is_limit_whisker_equiv (pairwise_to_opens_le_cover U).op _).symm
... ≃ is_limit (F.map_cone ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op))
        : is_limit.equiv_iso_limit F.map_cone_whisker.symm
... ≃ is_limit ((cones.postcompose_equivalence _).functor.obj
          (F.map_cone ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op)))
        : (is_limit.postcompose_hom_equiv _ _).symm
... ≃ is_limit (F.map_cone ((cones.postcompose_equivalence _).functor.obj
          ((opens_le_cover_cocone U).op.whisker (pairwise_to_opens_le_cover U).op)))
        : is_limit.equiv_iso_limit (functor.map_cone_postcompose_equivalence_functor _).symm
... ≃ is_limit (F.map_cone (pairwise.cocone U).op)
        : is_limit.equiv_iso_limit
            ((cones.functoriality _ _).map_iso (pairwise_cocone_iso U : _).symm)

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
lemma is_sheaf_iff_is_sheaf_pairwise_intersections :
  F.is_sheaf ↔ F.is_sheaf_pairwise_intersections :=
by rw [is_sheaf_iff_is_sheaf_opens_le_cover,
  is_sheaf_opens_le_cover_iff_is_sheaf_pairwise_intersections]

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
lemma is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections :
  F.is_sheaf ↔ F.is_sheaf_preserves_limit_pairwise_intersections :=
begin
  rw is_sheaf_iff_is_sheaf_pairwise_intersections,
  split,
  { intros h ι U,
    exact ⟨preserves_limit_of_preserves_limit_cone (pairwise.cocone_is_colimit U).op (h U).some⟩ },
  { intros h ι U,
    haveI := (h U).some,
    exact ⟨preserves_limit.preserves (pairwise.cocone_is_colimit U).op⟩ }
end

end Top.presheaf

namespace Top.sheaf

variables (F : X.sheaf C) (U V : opens X)
open category_theory.limits

/-- For a sheaf `F`, `F(U ⊔ V)` is the pullback of `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)`.
This is the pullback cone. -/
def inter_union_pullback_cone : pullback_cone
  (F.1.map (hom_of_le inf_le_left : U ⊓ V ⟶ _).op) (F.1.map (hom_of_le inf_le_right).op) :=
pullback_cone.mk (F.1.map (hom_of_le le_sup_left).op) (F.1.map (hom_of_le le_sup_right).op)
  (by { rw [← F.1.map_comp, ← F.1.map_comp], congr })

@[simp] lemma inter_union_pullback_cone_X :
  (inter_union_pullback_cone F U V).X = F.1.obj (op $ U ⊔ V) := rfl
@[simp] lemma inter_union_pullback_cone_fst :
  (inter_union_pullback_cone F U V).fst = F.1.map (hom_of_le le_sup_left).op := rfl
@[simp] lemma inter_union_pullback_cone_snd :
  (inter_union_pullback_cone F U V).snd = F.1.map (hom_of_le le_sup_right).op := rfl

variable (s : pullback_cone
  (F.1.map (hom_of_le inf_le_left : U ⊓ V ⟶ _).op) (F.1.map (hom_of_le inf_le_right).op))

/-- (Implementation).
Every cone over `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)` factors through `F(U ⊔ V)`.
-/
def inter_union_pullback_cone_lift : s.X ⟶ F.1.obj (op (U ⊔ V)) :=
begin
  let ι : ulift.{w} walking_pair → opens X := λ j, walking_pair.cases_on j.down U V,
  have hι : U ⊔ V = supr ι,
  { ext,
    rw [opens.coe_supr, set.mem_Union],
    split,
    { rintros (h|h),
      exacts [⟨⟨walking_pair.left⟩, h⟩, ⟨⟨walking_pair.right⟩, h⟩] },
    { rintro ⟨⟨_ | _⟩, h⟩,
      exacts [or.inl h, or.inr h] } },
  refine (F.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 ι).some.lift
    ⟨s.X, { app := _, naturality' := _ }⟩ ≫ F.1.map (eq_to_hom hι).op,
  { apply opposite.rec,
    rintro ((_|_)|(_|_)),
    exacts [s.fst, s.snd, s.fst ≫ F.1.map (hom_of_le inf_le_left).op,
      s.snd ≫ F.1.map (hom_of_le inf_le_left).op] },
  rintros i j f,
  induction i using opposite.rec,
  induction j using opposite.rec,
  let g : j ⟶ i := f.unop, have : f = g.op := rfl, clear_value g, subst this,
  rcases i with (⟨⟨(_|_)⟩⟩|⟨⟨(_|_)⟩,⟨_⟩⟩); rcases j with (⟨⟨(_|_)⟩⟩|⟨⟨(_|_)⟩,⟨_⟩⟩); rcases g; dsimp;
    simp only [category.id_comp, s.condition, category_theory.functor.map_id, category.comp_id],
  { rw [← cancel_mono (F.1.map (eq_to_hom $ inf_comm : U ⊓ V ⟶ _).op), category.assoc,
      category.assoc],
    erw [← F.1.map_comp, ← F.1.map_comp],
    convert s.condition.symm },
end

lemma inter_union_pullback_cone_lift_left :
  inter_union_pullback_cone_lift F U V s ≫ F.1.map (hom_of_le le_sup_left).op = s.fst :=
begin
  erw [category.assoc, ←F.1.map_comp],
  exact (F.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 _).some.fac _
    (op $ pairwise.single (ulift.up walking_pair.left))
end

lemma inter_union_pullback_cone_lift_right :
  inter_union_pullback_cone_lift F U V s ≫ F.1.map (hom_of_le le_sup_right).op = s.snd :=
begin
  erw [category.assoc, ←F.1.map_comp],
  exact (F.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 _).some.fac _
    (op $ pairwise.single (ulift.up walking_pair.right))
end

/-- For a sheaf `F`, `F(U ⊔ V)` is the pullback of `F(U) ⟶ F(U ⊓ V)` and `F(V) ⟶ F(U ⊓ V)`. -/
def is_limit_pullback_cone : is_limit (inter_union_pullback_cone F U V) :=
begin
  let ι : ulift.{w} walking_pair → opens X := λ ⟨j⟩, walking_pair.cases_on j U V,
  have hι : U ⊔ V = supr ι,
  { ext,
    rw [opens.coe_supr, set.mem_Union],
    split,
    { rintros (h|h),
      exacts [⟨⟨walking_pair.left⟩, h⟩, ⟨⟨walking_pair.right⟩, h⟩] },
    { rintro ⟨⟨_ | _⟩, h⟩,
      exacts [or.inl h, or.inr h] } },
  apply pullback_cone.is_limit_aux',
  intro s,
  use inter_union_pullback_cone_lift F U V s,
  refine ⟨_,_,_⟩,
  { apply inter_union_pullback_cone_lift_left },
  { apply inter_union_pullback_cone_lift_right },
  { intros m h₁ h₂,
    rw ← cancel_mono (F.1.map (eq_to_hom hι.symm).op),
    apply (F.presheaf.is_sheaf_iff_is_sheaf_pairwise_intersections.mp F.2 ι).some.hom_ext,
    apply opposite.rec,
    rintro ((_|_)|(_|_)); rw [category.assoc, category.assoc],
    { erw ← F.1.map_comp,
      convert h₁,
      apply inter_union_pullback_cone_lift_left },
    { erw ← F.1.map_comp,
      convert h₂,
      apply inter_union_pullback_cone_lift_right },
    all_goals
    { dsimp only [functor.op, pairwise.cocone_ι_app, functor.map_cone_π_app,
        cocone.op, pairwise.cocone_ι_app_2, unop_op, op_comp, nat_trans.op],
      simp_rw [F.1.map_comp, ← category.assoc],
      congr' 1,
      simp_rw [category.assoc, ← F.1.map_comp] },
    { convert h₁,
      apply inter_union_pullback_cone_lift_left },
    { convert h₂,
      apply inter_union_pullback_cone_lift_right } }
end

/-- If `U, V` are disjoint, then `F(U ⊔ V) = F(U) × F(V)`. -/
def is_product_of_disjoint (h : U ⊓ V = ⊥) : is_limit
    (binary_fan.mk (F.1.map (hom_of_le le_sup_left : _ ⟶ U ⊔ V).op)
      (F.1.map (hom_of_le le_sup_right : _ ⟶ U ⊔ V).op)) :=
is_product_of_is_terminal_is_pullback _ _ _ _
  (F.is_terminal_of_eq_empty h) (is_limit_pullback_cone F U V)

/-- `F(U ⊔ V)` is isomorphic to the `eq_locus` of the two maps `F(U) × F(V) ⟶ F(U ⊓ V)`. -/
def obj_sup_iso_prod_eq_locus {X : Top} (F : X.sheaf CommRing)
  (U V : opens X) :
  F.1.obj (op $ U ⊔ V) ≅ CommRing.of (ring_hom.eq_locus _ _) :=
(F.is_limit_pullback_cone U V).cone_point_unique_up_to_iso (CommRing.pullback_cone_is_limit _ _)

lemma obj_sup_iso_prod_eq_locus_hom_fst {X : Top} (F : X.sheaf CommRing)
  (U V : opens X) (x) :
  ((F.obj_sup_iso_prod_eq_locus U V).hom x).1.fst = F.1.map (hom_of_le le_sup_left).op x :=
concrete_category.congr_hom ((F.is_limit_pullback_cone U V).cone_point_unique_up_to_iso_hom_comp
  (CommRing.pullback_cone_is_limit _ _) walking_cospan.left) x

lemma obj_sup_iso_prod_eq_locus_hom_snd {X : Top} (F : X.sheaf CommRing)
  (U V : opens X) (x) :
  ((F.obj_sup_iso_prod_eq_locus U V).hom x).1.snd = F.1.map (hom_of_le le_sup_right).op x :=
concrete_category.congr_hom ((F.is_limit_pullback_cone U V).cone_point_unique_up_to_iso_hom_comp
  (CommRing.pullback_cone_is_limit _ _) walking_cospan.right) x

lemma obj_sup_iso_prod_eq_locus_inv_fst {X : Top} (F : X.sheaf CommRing)
  (U V : opens X) (x) :
  F.1.map (hom_of_le le_sup_left).op ((F.obj_sup_iso_prod_eq_locus U V).inv x) = x.1.1 :=
concrete_category.congr_hom ((F.is_limit_pullback_cone U V).cone_point_unique_up_to_iso_inv_comp
  (CommRing.pullback_cone_is_limit _ _) walking_cospan.left) x

lemma obj_sup_iso_prod_eq_locus_inv_snd {X : Top} (F : X.sheaf CommRing)
  (U V : opens X) (x) :
  F.1.map (hom_of_le le_sup_right).op ((F.obj_sup_iso_prod_eq_locus U V).inv x) = x.1.2 :=
concrete_category.congr_hom ((F.is_limit_pullback_cone U V).cone_point_unique_up_to_iso_inv_comp
  (CommRing.pullback_cone_is_limit _ _) walking_cospan.right) x

end Top.sheaf
