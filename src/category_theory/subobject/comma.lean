/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.subobject.well_powered
import category_theory.limits.preserves.finite
import category_theory.limits.shapes.finite_limits

/-!
# Subobjects in the category of structured arrows

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We compute the subobjects of an object `A` in the category `structured_arrow S T` for `T : C ⥤ D`
and `S : D` as a subtype of the subobjects of `A.right`. We deduce that `structured_arrow S T` is
well-powered if `C` is.

## Main declarations
* `structured_arrow.equiv_subtype`: the order-equivalence between `subobject A` and a subtype of
  `subobject A.right`.

## Implementation notes
Our computation requires that `C` has all limits and `T` preserves all limits. Furthermore, we
require that the morphisms of `C` and `D` are in the same universe. It is possible that both of
these requirements can be relaxed by refining the results about limits in comma categories.

We also provide the dual results. As usual, we use `subobject (op A)` for the quotient objects of
`A`.

-/

noncomputable theory

open category_theory.limits opposite

universes v u₁ u₂

namespace category_theory
variables {C : Type u₁} [category.{v} C] {D : Type u₂} [category.{v} D]

namespace structured_arrow
variables {S : D} {T : C ⥤ D}

/-- Every subobject of a structured arrow can be projected to a subobject of the underlying
    object. -/
def project_subobject [has_limits C] [preserves_limits T] {A : structured_arrow S T} :
  subobject A → subobject A.right :=
begin
  refine subobject.lift (λ P f hf, by exactI subobject.mk f.right) _,
  introsI P Q f g hf hg i hi,
  refine subobject.mk_eq_mk_of_comm _ _ ((proj S T).map_iso i) _,
  exact congr_arg comma_morphism.right hi
end

@[simp]
lemma project_subobject_mk [has_limits C] [preserves_limits T] {A P : structured_arrow S T}
  (f : P ⟶ A) [mono f] : project_subobject (subobject.mk f) = subobject.mk f.right :=
rfl

lemma project_subobject_factors [has_limits C] [preserves_limits T] {A : structured_arrow S T} :
  ∀ P : subobject A, ∃ q, q ≫ T.map (project_subobject P).arrow = A.hom :=
subobject.ind _ $ λ P f hf,
  ⟨P.hom ≫ T.map (subobject.underlying_iso _).inv, by { dsimp, simp [← T.map_comp] }⟩

/-- A subobject of the underlying object of a structured arrow can be lifted to a subobject of
    the structured arrow, provided that there is a morphism making the subobject into a structured
    arrow. -/
@[simp]
def lift_subobject {A : structured_arrow S T} (P : subobject A.right) {q}
  (hq : q ≫ T.map P.arrow = A.hom) : subobject A :=
subobject.mk (hom_mk P.arrow hq : mk q ⟶ A)

/-- Projecting and then lifting a subobject recovers the original subobject, because there is at
    most one morphism making the projected subobject into a structured arrow. -/
lemma lift_project_subobject [has_limits C] [preserves_limits T] {A : structured_arrow S T} :
  ∀ (P : subobject A) {q} (hq : q ≫ T.map (project_subobject P).arrow = A.hom),
    lift_subobject (project_subobject P) hq = P := subobject.ind _
begin
  introsI P f hf q hq,
  fapply subobject.mk_eq_mk_of_comm,
  { fapply iso_mk,
    { exact subobject.underlying_iso _ },
    { exact (cancel_mono (T.map f.right)).1 (by { dsimp, simpa [← T.map_comp] using hq }) } },
  { exact ext _ _ (by { dsimp, simp })}
end

/-- If `A : S → T.obj B` is a structured arrow for `S : D` and `T : C ⥤ D`, then we can explicitly
    describe the subobjects of `A` as the subobjects `P` of `B` in `C` for which `A.hom` factors
    through the image of `P` under `T`. -/
@[simps]
def subobject_equiv [has_limits C] [preserves_limits T] (A : structured_arrow S T) :
  subobject A ≃o { P : subobject A.right // ∃ q, q ≫ T.map P.arrow = A.hom } :=
{ to_fun := λ P, ⟨project_subobject P, project_subobject_factors P⟩,
  inv_fun := λ P, lift_subobject P.val P.prop.some_spec,
  left_inv := λ P, lift_project_subobject _ _,
  right_inv := λ P, subtype.ext (by simp),
  map_rel_iff' := subobject.ind₂ _
  begin
    introsI P Q f g hf hg,
    refine ⟨λ h, subobject.mk_le_mk_of_comm _ (ext _ _ _), λ h, _⟩,
    { refine hom_mk (subobject.of_mk_le_mk _ _ h) ((cancel_mono (T.map g.right)).1 _),
      simp [← T.map_comp] },
    { simp only [mono_over.mk'_arrow, subobject.of_mk_le_mk_comp, comma.comp_right, hom_mk_right] },
    { refine subobject.mk_le_mk_of_comm (subobject.of_mk_le_mk _ _ h).right _,
      exact congr_arg comma_morphism.right (subobject.of_mk_le_mk_comp h) }
  end }

/-- If `C` is well-powered and complete and `T` preserves limits, then `structured_arrow S T` is
    well-powered. -/
instance well_powered_structured_arrow [well_powered C] [has_limits C] [preserves_limits T] :
  well_powered (structured_arrow S T) :=
{ subobject_small := λ X, small_map (subobject_equiv X).to_equiv }

end structured_arrow

namespace costructured_arrow
variables {S : C ⥤ D} {T : D}

/-- Every quotient of a costructured arrow can be projected to a quotient of the underlying
    object. -/
def project_quotient [has_colimits C] [preserves_colimits S] {A : costructured_arrow S T} :
  subobject (op A) → subobject (op A.left) :=
begin
  refine subobject.lift (λ P f hf, by exactI subobject.mk f.unop.left.op) _,
  introsI P Q f g hf hg i hi,
  refine subobject.mk_eq_mk_of_comm _ _ ((proj S T).map_iso i.unop).op (quiver.hom.unop_inj _),
  have := congr_arg quiver.hom.unop hi,
  simpa using congr_arg comma_morphism.left this,
end

@[simp]
lemma project_quotient_mk [has_colimits C] [preserves_colimits S] {A : costructured_arrow S T}
  {P : (costructured_arrow S T)ᵒᵖ} (f : P ⟶ op A) [mono f] :
  (project_quotient (subobject.mk f)) = subobject.mk f.unop.left.op :=
rfl

lemma project_quotient_factors [has_colimits C] [preserves_colimits S]
  {A : costructured_arrow S T} :
  ∀ P : subobject (op A), ∃ q, S.map (project_quotient P).arrow.unop ≫ q = A.hom :=
subobject.ind _ $ λ P f hf, ⟨S.map (subobject.underlying_iso _).unop.inv ≫ P.unop.hom,
  by { dsimp, rw [← category.assoc, ← S.map_comp, ← unop_comp], simp }⟩

/-- A quotient of the underlying object of a costructured arrow can be lifted to a quotient of
    the costructured arrow, provided that there is a morphism making the quotient into a
    costructured arrow. -/
@[simp]
def lift_quotient {A : costructured_arrow S T} (P : subobject (op A.left)) {q}
  (hq : S.map P.arrow.unop ≫ q = A.hom) : subobject (op A) :=
subobject.mk (hom_mk P.arrow.unop hq : A ⟶ mk q).op

/-- Technical lemma for `lift_project_quotient`. -/
@[simp]
lemma unop_left_comp_underlying_iso_hom_unop {A : costructured_arrow S T}
  {P : (costructured_arrow S T)ᵒᵖ} (f : P ⟶ op A) [mono f.unop.left.op] :
  f.unop.left ≫ (subobject.underlying_iso f.unop.left.op).hom.unop =
    (subobject.mk f.unop.left.op).arrow.unop :=
begin
  conv_lhs { congr, rw [← quiver.hom.unop_op f.unop.left] },
  rw [← unop_comp, subobject.underlying_iso_hom_comp_eq_mk]
end

/-- Projecting and then lifting a quotient recovers the original quotient, because there is at most
    one morphism making the projected quotient into a costructured arrow. -/
lemma lift_project_quotient [has_colimits C] [preserves_colimits S] {A : costructured_arrow S T} :
  ∀ (P : subobject (op A)) {q} (hq : S.map (project_quotient P).arrow.unop ≫ q = A.hom),
    lift_quotient (project_quotient P) hq = P := subobject.ind _
begin
  introsI P f hf q hq,
  fapply subobject.mk_eq_mk_of_comm,
  { refine (iso.op (iso_mk _ _) : _ ≅ op (unop P)),
    { exact (subobject.underlying_iso f.unop.left.op).unop },
    { refine (cancel_epi (S.map f.unop.left)).1 _,
      simpa [← category.assoc, ← S.map_comp] using hq } },
  { exact quiver.hom.unop_inj (ext _ _ (by { dsimp, simp })) }
end

/-- Technical lemma for `quotient_equiv`. -/
lemma unop_left_comp_of_mk_le_mk_unop {A : costructured_arrow S T}
  {P Q : (costructured_arrow S T)ᵒᵖ} {f : P ⟶ op A} {g : Q ⟶ op A} [mono f.unop.left.op]
  [mono g.unop.left.op] (h : subobject.mk f.unop.left.op ≤ subobject.mk g.unop.left.op) :
  g.unop.left ≫ (subobject.of_mk_le_mk f.unop.left.op g.unop.left.op h).unop = f.unop.left :=
begin
  conv_lhs { congr, rw [← quiver.hom.unop_op g.unop.left] },
  rw [← unop_comp],
  simp only [subobject.of_mk_le_mk_comp, quiver.hom.unop_op]
end

/-- If `A : S.obj B ⟶ T` is a costructured arrow for `S : C ⥤ D` and `T : D`, then we can
    explicitly describe the quotients of `A` as the quotients `P` of `B` in `C` for which `A.hom`
    factors through the image of `P` under `S`. -/
def quotient_equiv [has_colimits C] [preserves_colimits S] (A : costructured_arrow S T) :
  subobject (op A) ≃o { P : subobject (op A.left) // ∃ q, S.map P.arrow.unop ≫ q = A.hom } :=
{ to_fun := λ P, ⟨project_quotient P, project_quotient_factors P⟩,
  inv_fun := λ P, lift_quotient P.val P.prop.some_spec,
  left_inv := λ P, lift_project_quotient _ _,
  right_inv := λ P, subtype.ext (by simp),
  map_rel_iff' := subobject.ind₂ _
  begin
    introsI P Q f g hf hg,
    refine ⟨λ h, subobject.mk_le_mk_of_comm _ (quiver.hom.unop_inj (ext _ _ _)), λ h, _⟩,
    { refine (hom_mk (subobject.of_mk_le_mk _ _ h).unop ((cancel_epi (S.map g.unop.left)).1 _)).op,
      dsimp only [mono_over.mk'_arrow],
      rw [← category.assoc, ← S.map_comp, unop_left_comp_of_mk_le_mk_unop],
      dsimp,
      simp },
    { exact unop_left_comp_of_mk_le_mk_unop _ },
    { refine subobject.mk_le_mk_of_comm (subobject.of_mk_le_mk _ _ h).unop.left.op _,
      refine quiver.hom.unop_inj _,
      have := congr_arg quiver.hom.unop (subobject.of_mk_le_mk_comp h),
      simpa [-subobject.of_mk_le_mk_comp] using congr_arg comma_morphism.left this }
  end }

/-- If `C` is well-copowered and cocomplete and `S` preserves colimits, then
    `costructured_arrow S T` is well-copowered. -/
instance well_copowered_costructured_arrow [well_powered Cᵒᵖ] [has_colimits C]
  [preserves_colimits S] : well_powered (costructured_arrow S T)ᵒᵖ :=
{ subobject_small := λ X, small_map (quotient_equiv (unop X)).to_equiv }

end costructured_arrow

end category_theory
