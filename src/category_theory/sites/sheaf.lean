/-
Copyright (c) 2020 Kevin Buzzard, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bhavik Mehta
-/

import category_theory.limits.preserves.shapes.equalizers
import category_theory.limits.preserves.shapes.products
import category_theory.limits.yoneda
import category_theory.preadditive.functor_category
import category_theory.sites.sheaf_of_types

/-!
# Sheaves taking values in a category

If C is a category with a Grothendieck topology, we define the notion of a sheaf taking values in
an arbitrary category `A`. We follow the definition in https://stacks.math.columbia.edu/tag/00VR,
noting that the presheaf of sets "defined above" can be seen in the comments between tags 00VQ and
00VR on the page <https://stacks.math.columbia.edu/tag/00VL>. The advantage of this definition is
that we need no assumptions whatsoever on `A` other than the assumption that the morphisms in `C`
and `A` live in the same universe.

* An `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is defined to be a sheaf (for the topology `J`) iff for
  every `E : A`, the type-valued presheaves of sets given by sending `U : Cᵒᵖ` to `Hom_{A}(E, P U)`
  are all sheaves of sets, see `category_theory.presheaf.is_sheaf`.
* When `A = Type`, this recovers the basic definition of sheaves of sets, see
  `category_theory.is_sheaf_iff_is_sheaf_of_type`.
* An alternate definition when `C` is small, has pullbacks and `A` has products is given by an
  equalizer condition `category_theory.presheaf.is_sheaf'`. This is equivalent to the earlier
  definition, shown in `category_theory.presheaf.is_sheaf_iff_is_sheaf'`.
* When `A = Type`, this is *definitionally* equal to the equalizer condition for presieves in
  `category_theory.sites.sheaf_of_types`.
* When `A` has limits and there is a functor `s : A ⥤ Type` which is faithful, reflects isomorphisms
  and preserves limits, then `P : Cᵒᵖ ⥤ A` is a sheaf iff the underlying presheaf of types
  `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf (`category_theory.presheaf.is_sheaf_iff_is_sheaf_forget`).
  Cf https://stacks.math.columbia.edu/tag/0073, which is a weaker version of this statement (it's
  only over spaces, not sites) and https://stacks.math.columbia.edu/tag/00YR (a), which
  additionally assumes filtered colimits.
-/

universes w v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

open opposite category_theory category limits sieve

namespace presheaf

variables {C : Type u₁} [category.{v₁} C]
variables {A : Type u₂} [category.{v₂} A]
variables (J : grothendieck_topology C)

-- We follow https://stacks.math.columbia.edu/tag/00VL definition 00VR

/--
A sheaf of A is a presheaf P : Cᵒᵖ => A such that for every E : A, the
presheaf of types given by sending U : C to Hom_{A}(E, P U) is a sheaf of types.

https://stacks.math.columbia.edu/tag/00VR
-/
def is_sheaf (P : Cᵒᵖ ⥤ A) : Prop :=
∀ E : A, presieve.is_sheaf J (P ⋙ coyoneda.obj (op E))

section limit_sheaf_condition
open presieve presieve.family_of_elements limits
variables (P : Cᵒᵖ ⥤ A) {X : C} (S : sieve X) (R : presieve X) (E : Aᵒᵖ)

/-- Given a sieve `S` on `X : C`, a presheaf `P : Cᵒᵖ ⥤ A`, and an object `E` of `A`,
    the cones over the natural diagram `S.arrows.diagram.op ⋙ P` associated to `S` and `P`
    with cone point `E` are in 1-1 correspondence with sieve_compatible family of elements
    for the sieve `S` and the presheaf of types `Hom (E, P -)`. -/
@[simps] def cones_equiv_sieve_compatible_family :
  (S.arrows.diagram.op ⋙ P).cones.obj E ≃
  {x : family_of_elements (P ⋙ coyoneda.obj E) S // x.sieve_compatible} :=
{ to_fun := λ π, ⟨λ Y f h, π.app (op ⟨over.mk f, h⟩), λ _, by
    { intros, apply (id_comp _).symm.trans, dsimp,
      convert π.naturality (quiver.hom.op (over.hom_mk _ _)); dsimp; refl }⟩,
  inv_fun := λ x, { app := λ f, x.1 f.unop.1.hom f.unop.2,
    naturality' := λ f f' g, by
    { refine eq.trans _ (x.2 f.unop.1.hom g.unop.left f.unop.2),
      erw id_comp, congr, rw over.w g.unop } },
  left_inv := λ π, by { ext, dsimp, congr,
    rw op_eq_iff_eq_unop, ext, symmetry, apply costructured_arrow.eq_mk },
  right_inv := λ x, by { ext, refl } }

variables {P S E} {x : family_of_elements (P ⋙ coyoneda.obj E) S} (hx : x.sieve_compatible)

/-- The cone corresponding to a sieve_compatible family of elements, dot notation enabled. -/
@[simp] def _root_.category_theory.presieve.family_of_elements.sieve_compatible.cone :
  cone (S.arrows.diagram.op ⋙ P) :=
{ X := E.unop, π := (cones_equiv_sieve_compatible_family P S E).inv_fun ⟨x,hx⟩ }

/-- Cone morphisms from the cone corresponding to a sieve_compatible family to the natural
    cone associated to a sieve `S` and a presheaf `P` are in 1-1 correspondence with amalgamations
    of the family. -/
def hom_equiv_amalgamation :
  (hx.cone ⟶ P.map_cone S.arrows.cocone.op) ≃ {t // x.is_amalgamation t} :=
{ to_fun := λ l, ⟨l.hom, λ Y f hf, l.w (op ⟨over.mk f, hf⟩)⟩,
  inv_fun := λ t, ⟨t.1, λ f, t.2 f.unop.1.hom f.unop.2⟩,
  left_inv := λ l, by { ext, refl },
  right_inv := λ t, by { ext, refl } }

variables (P S)

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone is a limit cone
    iff `Hom (E, P -)` is a sheaf of types for the sieve `S` and all `E : A`. -/
lemma is_limit_iff_is_sheaf_for :
  nonempty (is_limit (P.map_cone S.arrows.cocone.op)) ↔
  ∀ E : Aᵒᵖ, is_sheaf_for (P ⋙ coyoneda.obj E) S :=
begin
  dsimp [is_sheaf_for], simp_rw compatible_iff_sieve_compatible,
  rw ((cone.is_limit_equiv_is_terminal _).trans (is_terminal_equiv_unique _ _)).nonempty_congr,
  rw classical.nonempty_pi, split,
  { intros hu E x hx, specialize hu hx.cone,
    erw (hom_equiv_amalgamation hx).unique_congr.nonempty_congr at hu,
    exact (unique_subtype_iff_exists_unique _).1 hu },
  { rintros h ⟨E,π⟩, let eqv := cones_equiv_sieve_compatible_family P S (op E),
    rw ← eqv.left_inv π, erw (hom_equiv_amalgamation (eqv π).2).unique_congr.nonempty_congr,
    rw unique_subtype_iff_exists_unique, exact h _ _ (eqv π).2 },
end

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone admits at most one
    morphism from every cone in the same category (i.e. over the same diagram),
    iff `Hom (E, P -)`is separated for the sieve `S` and all `E : A`. -/
lemma subsingleton_iff_is_separated_for :
  (∀ c, subsingleton (c ⟶ P.map_cone S.arrows.cocone.op)) ↔
  ∀ E : Aᵒᵖ, is_separated_for (P ⋙ coyoneda.obj E) S :=
begin
  split,
  { intros hs E x t₁ t₂ h₁ h₂, have hx := is_compatible_of_exists_amalgamation x ⟨t₁,h₁⟩,
    rw compatible_iff_sieve_compatible at hx, specialize hs hx.cone, cases hs,
    have := (hom_equiv_amalgamation hx).symm.injective,
    exact subtype.ext_iff.1 (@this ⟨t₁,h₁⟩ ⟨t₂,h₂⟩ (hs _ _)) },
  { rintros h ⟨E,π⟩, let eqv := cones_equiv_sieve_compatible_family P S (op E), split,
    rw ← eqv.left_inv π, intros f₁ f₂, let eqv' := hom_equiv_amalgamation (eqv π).2,
    apply eqv'.injective, ext, apply h _ (eqv π).1; exact (eqv' _).2 },
end

/-- A presheaf `P` is a sheaf for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` is a limit cone. -/
lemma is_sheaf_iff_is_limit : is_sheaf J P ↔
  ∀ ⦃X : C⦄ (S : sieve X), S ∈ J X → nonempty (is_limit (P.map_cone S.arrows.cocone.op)) :=
⟨λ h X S hS, (is_limit_iff_is_sheaf_for P S).2 (λ E, h E.unop S hS),
 λ h E X S hS, (is_limit_iff_is_sheaf_for P S).1 (h S hS) (op E)⟩

/-- A presheaf `P` is separated for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` admits at most one morphism from every
    cone in the same category. -/
lemma is_separated_iff_subsingleton :
  (∀ E : A, is_separated J (P ⋙ coyoneda.obj (op E))) ↔
  ∀ ⦃X : C⦄ (S : sieve X), S ∈ J X → ∀ c, subsingleton (c ⟶ P.map_cone S.arrows.cocone.op) :=
⟨λ h X S hS, (subsingleton_iff_is_separated_for P S).2 (λ E, h E.unop S hS),
 λ h E X S hS, (subsingleton_iff_is_separated_for P S).1 (h S hS) (op E)⟩

/-- Given presieve `R` and presheaf `P : Cᵒᵖ ⥤ A`, the natural cone associated to `P` and
    the sieve `sieve.generate R` generated by `R` is a limit cone iff `Hom (E, P -)` is a
    sheaf of types for the presieve `R` and all `E : A`. -/
lemma is_limit_iff_is_sheaf_for_presieve :
  nonempty (is_limit (P.map_cone (generate R).arrows.cocone.op)) ↔
  ∀ E : Aᵒᵖ, is_sheaf_for (P ⋙ coyoneda.obj E) R :=
(is_limit_iff_is_sheaf_for P _).trans (forall_congr (λ _, (is_sheaf_for_iff_generate _).symm))

/-- A presheaf `P` is a sheaf for the Grothendieck topology generated by a pretopology `K`
    iff for every covering presieve `R` of `K`, the natural cone associated to `P` and
    `sieve.generate R` is a limit cone. -/
lemma is_sheaf_iff_is_limit_pretopology [has_pullbacks C] (K : pretopology C) :
  is_sheaf (K.to_grothendieck C) P ↔ ∀ ⦃X : C⦄ (R : presieve X), R ∈ K X →
    nonempty (is_limit (P.map_cone (generate R).arrows.cocone.op)) :=
by { dsimp [is_sheaf], simp_rw is_sheaf_pretopology, exact
  ⟨λ h X R hR, (is_limit_iff_is_sheaf_for_presieve P R).2 (λ E, h E.unop R hR),
   λ h E X R hR, (is_limit_iff_is_sheaf_for_presieve P R).1 (h R hR) (op E)⟩ }

end limit_sheaf_condition

variable {J}

/-- This is a wrapper around `presieve.is_sheaf_for.amalgamate` to be used below.
  If `P`s a sheaf, `S` is a cover of `X`, and `x` is a collection of morphisms from `E`
  to `P` evaluated at terms in the cover which are compatible, then we can amalgamate
  the `x`s to obtain a single morphism `E ⟶ P.obj (op X)`. -/
def is_sheaf.amalgamate {A : Type u₂} [category.{max v₁ u₁} A]
  {E : A} {X : C} {P : Cᵒᵖ ⥤ A} (hP : presheaf.is_sheaf J P) (S : J.cover X)
  (x : Π (I : S.arrow), E ⟶ P.obj (op I.Y))
  (hx : ∀ (I : S.relation), x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) :
  E ⟶ P.obj (op X) :=
(hP _ _ S.condition).amalgamate (λ Y f hf, x ⟨Y,f,hf⟩) $
  λ Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w, hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩

@[simp, reassoc]
lemma is_sheaf.amalgamate_map {A : Type u₂} [category.{max v₁ u₁} A]
  {E : A} {X : C} {P : Cᵒᵖ ⥤ A} (hP : presheaf.is_sheaf J P) (S : J.cover X)
  (x : Π (I : S.arrow), E ⟶ P.obj (op I.Y))
  (hx : ∀ (I : S.relation), x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op)
  (I : S.arrow) : hP.amalgamate S x hx ≫ P.map I.f.op = x _ :=
begin
  rcases I with ⟨Y,f,hf⟩,
  apply @presieve.is_sheaf_for.valid_glue _ _ _ _ _ _ (hP _ _ S.condition)
    (λ Y f hf, x ⟨Y,f,hf⟩)
    (λ Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w, hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩) f hf,
end

lemma is_sheaf.hom_ext {A : Type u₂} [category.{max v₁ u₁} A]
  {E : A} {X : C} {P : Cᵒᵖ ⥤ A} (hP : presheaf.is_sheaf J P) (S : J.cover X)
  (e₁ e₂ : E ⟶ P.obj (op X)) (h : ∀ (I : S.arrow), e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) :
  e₁ = e₂ :=
(hP _ _ S.condition).is_separated_for.ext (λ Y f hf, h ⟨Y,f,hf⟩)

lemma is_sheaf_of_iso_iff {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P') : is_sheaf J P ↔ is_sheaf J P' :=
forall_congr $ λ a, ⟨presieve.is_sheaf_iso J (iso_whisker_right e _),
  presieve.is_sheaf_iso J (iso_whisker_right e.symm _)⟩

variable (J)

lemma is_sheaf_of_is_terminal {X : A} (hX : is_terminal X) :
 presheaf.is_sheaf J ((category_theory.functor.const _).obj X) :=
λ _ _ _ _ _ _, ⟨hX.from _, λ _ _ _, hX.hom_ext _ _, λ _ _, hX.hom_ext _ _⟩

end presheaf

variables {C : Type u₁} [category.{v₁} C]
variables (J : grothendieck_topology C)
variables (A : Type u₂) [category.{v₂} A]

/-- The category of sheaves taking values in `A` on a grothendieck topology. -/
structure Sheaf :=
(val : Cᵒᵖ ⥤ A)
(cond : presheaf.is_sheaf J val)

namespace Sheaf

variables {J A}

/-- Morphisms between sheaves are just morphisms of presheaves. -/
@[ext]
structure hom (X Y : Sheaf J A) :=
(val : X.val ⟶ Y.val)

@[simps]
instance : category (Sheaf J A) :=
{ hom := hom,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.val ≫ g.val⟩,
  id_comp' := λ X Y f, hom.ext _ _ $ id_comp _,
  comp_id' := λ X Y f, hom.ext _ _ $ comp_id _,
  assoc' := λ X Y Z W f g h, hom.ext _ _ $ assoc _ _ _ }

-- Let's make the inhabited linter happy...
instance (X : Sheaf J A) : inhabited (hom X X) := ⟨𝟙 X⟩

end Sheaf

/-- The inclusion functor from sheaves to presheaves. -/
@[simps]
def Sheaf_to_presheaf : Sheaf J A ⥤ (Cᵒᵖ ⥤ A) :=
{ obj := Sheaf.val,
  map := λ _ _ f, f.val,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl }

instance : full (Sheaf_to_presheaf J A) := { preimage := λ X Y f, ⟨f⟩ }
instance : faithful (Sheaf_to_presheaf J A) := {}

/--This is stated as a lemma to prevent class search from forming a loop since a sheaf morphism is
monic if and only if it is monic as a presheaf morphism (under suitable assumption).-/
lemma Sheaf.hom.mono_of_presheaf_mono {F G : Sheaf J A} (f : F ⟶ G) [h : mono f.1] : mono f :=
(Sheaf_to_presheaf J A).mono_of_mono_map h

instance Sheaf.hom.epi_of_presheaf_epi {F G : Sheaf J A} (f : F ⟶ G) [h : epi f.1] : epi f :=
(Sheaf_to_presheaf J A).epi_of_epi_map h

/-- The sheaf of sections guaranteed by the sheaf condition. -/
@[simps] def sheaf_over {A : Type u₂} [category.{v₂} A] {J : grothendieck_topology C}
  (ℱ : Sheaf J A) (E : A) : SheafOfTypes J := ⟨ℱ.val ⋙ coyoneda.obj (op E), ℱ.cond E⟩

lemma is_sheaf_iff_is_sheaf_of_type (P : Cᵒᵖ ⥤ Type w) :
  presheaf.is_sheaf J P ↔ presieve.is_sheaf J P :=
begin
  split,
  { intros hP,
    refine presieve.is_sheaf_iso J _ (hP punit),
    exact iso_whisker_left _ coyoneda.punit_iso ≪≫ P.right_unitor },
  { intros hP X Y S hS z hz,
    refine ⟨λ x, (hP S hS).amalgamate (λ Z f hf, z f hf x) _, _, _⟩,
    { intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h,
      exact congr_fun (hz g₁ g₂ hf₁ hf₂ h) x },
    { intros Z f hf,
      ext x,
      apply presieve.is_sheaf_for.valid_glue },
    { intros y hy,
      ext x,
      apply (hP S hS).is_separated_for.ext,
      intros Y' f hf,
      rw [presieve.is_sheaf_for.valid_glue _ _ _ hf, ← hy _ hf],
      refl } }
end

/--
The category of sheaves taking values in Type is the same as the category of set-valued sheaves.
-/
@[simps]
def Sheaf_equiv_SheafOfTypes : Sheaf J (Type w) ≌ SheafOfTypes J :=
{ functor :=
  { obj := λ S, ⟨S.val, (is_sheaf_iff_is_sheaf_of_type _ _).1 S.2⟩,
    map := λ S T f, ⟨f.val⟩ },
  inverse :=
  { obj := λ S, ⟨S.val, (is_sheaf_iff_is_sheaf_of_type _ _ ).2 S.2⟩,
    map := λ S T f, ⟨f.val⟩ },
  unit_iso := nat_iso.of_components (λ X, ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by tidy, by tidy⟩) (by tidy),
  counit_iso := nat_iso.of_components (λ X, ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by tidy, by tidy⟩) (by tidy) }

instance : inhabited (Sheaf (⊥ : grothendieck_topology C) (Type w)) :=
⟨(Sheaf_equiv_SheafOfTypes _).inverse.obj default⟩

variables {J} {A}

/-- If the empty sieve is a cover of `X`, then `F(X)` is terminal. -/
def Sheaf.is_terminal_of_bot_cover (F : Sheaf J A) (X : C) (H : ⊥ ∈ J X) :
  is_terminal (F.1.obj (op X)) :=
begin
  apply_with is_terminal.of_unique { instances := ff },
  intro Y,
  choose t h using F.2 Y _ H (by tidy) (by tidy),
  exact ⟨⟨t⟩, λ a, h.2 a (by tidy)⟩
end

section preadditive

open preadditive

variables [preadditive A] {P Q : Sheaf J A}

instance Sheaf_hom_has_zsmul  : has_smul ℤ (P ⟶ Q) :=
{ smul := λ n f, Sheaf.hom.mk
  { app := λ U, n • f.1.app U,
    naturality' := λ U V i, begin
      induction n using int.induction_on with n ih n ih,
      { simp only [zero_smul, comp_zero, zero_comp], },
      { simpa only [add_zsmul, one_zsmul, comp_add, nat_trans.naturality, add_comp, add_left_inj] },
      { simpa only [sub_smul, one_zsmul, comp_sub, nat_trans.naturality, sub_comp, sub_left_inj]
          using ih, }
    end } }

instance : has_sub (P ⟶ Q) :=
{ sub := λ f g, Sheaf.hom.mk $ f.1 - g.1 }

instance : has_neg (P ⟶ Q) :=
{ neg := λ f, Sheaf.hom.mk $ -f.1 }

instance Sheaf_hom_has_nsmul : has_smul ℕ (P ⟶ Q) :=
{ smul := λ n f, Sheaf.hom.mk
  { app := λ U, n • f.1.app U,
    naturality' := λ U V i, begin
      induction n with n ih,
      { simp only [zero_smul, comp_zero, zero_comp], },
      { simp only [nat.succ_eq_add_one, add_smul, ih, one_nsmul, comp_add, nat_trans.naturality,
          add_comp], },
    end } }

instance : has_zero (P ⟶ Q) :=
{ zero := Sheaf.hom.mk 0 }

instance : has_add (P ⟶ Q) :=
{ add := λ f g, Sheaf.hom.mk $ f.1 + g.1 }

@[simp] lemma Sheaf.hom.add_app (f g : P ⟶ Q) (U) :
  (f + g).1.app U = f.1.app U + g.1.app U := rfl

instance : add_comm_group (P ⟶ Q) :=
function.injective.add_comm_group (λ (f : Sheaf.hom P Q), f.1)
  (λ _ _ h, Sheaf.hom.ext _ _ h) rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
  (λ _ _, by { dsimp at *, ext, simpa [*] }) (λ _ _, by { dsimp at *, ext, simpa [*] })

instance : preadditive (Sheaf J A) :=
{ hom_group := λ P Q, infer_instance,
  add_comp' := λ P Q R f f' g, by { ext, simp, },
  comp_add' := λ P Q R f g g', by { ext, simp, } }

end preadditive

end category_theory

namespace category_theory

open opposite category_theory category limits sieve

namespace presheaf

-- Under here is the equalizer story, which is equivalent if A has products (and doesn't
-- make sense otherwise). It's described in https://stacks.math.columbia.edu/tag/00VL,
-- between 00VQ and 00VR.

variables {C : Type u₁} [category.{v₁} C]
variables {A : Type u₂} [category.{max v₁ u₁} A]
variables (J : grothendieck_topology C)
variables {U : C} (R : presieve U)
variables (P : Cᵒᵖ ⥤ A)

section multiequalizer_conditions

/-- When `P` is a sheaf and `S` is a cover, the associated multifork is a limit. -/
def is_limit_of_is_sheaf {X : C} (S : J.cover X) (hP : is_sheaf J P) :
  is_limit (S.multifork P) :=
{ lift := λ (E : multifork _), hP.amalgamate S (λ I, E.ι _) (λ I, E.condition _),
  fac' := begin
    rintros (E : multifork _) (a|b),
    { apply hP.amalgamate_map },
    { rw [← E.w (walking_multicospan.hom.fst b),
        ← (S.multifork P).w (walking_multicospan.hom.fst b), ← assoc],
      congr' 1,
      apply hP.amalgamate_map }
  end,
  uniq' := begin
    rintros (E : multifork _) m hm,
    apply hP.hom_ext S,
    intros I,
    erw hm (walking_multicospan.left I),
    symmetry,
    apply hP.amalgamate_map
  end }

lemma is_sheaf_iff_multifork : is_sheaf J P ↔
  (∀ (X : C) (S : J.cover X), nonempty (is_limit (S.multifork P))) :=
begin
  refine ⟨λ hP X S, ⟨is_limit_of_is_sheaf _ _ _ hP⟩, _⟩,
  intros h E X S hS x hx,
  let T : J.cover X := ⟨S,hS⟩,
  obtain ⟨hh⟩ := h _ T,
  let K : multifork (T.index P) :=
    multifork.of_ι _ E (λ I, x I.f I.hf) (λ I, hx _ _ _ _ I.w),
  use hh.lift K,
  dsimp, split,
  { intros Y f hf,
    apply hh.fac K (walking_multicospan.left ⟨Y,f,hf⟩) },
  { intros e he,
    apply hh.uniq K,
    rintros (a|b),
    { apply he },
    { rw [← K.w (walking_multicospan.hom.fst b),
        ← (T.multifork P).w (walking_multicospan.hom.fst b), ← assoc],
      congr' 1,
      apply he } }
end

lemma is_sheaf_iff_multiequalizer
  [∀ (X : C) (S : J.cover X), has_multiequalizer (S.index P)] : is_sheaf J P ↔
  (∀ (X : C) (S : J.cover X), is_iso (S.to_multiequalizer P)) :=
begin
  rw is_sheaf_iff_multifork,
  refine forall₂_congr (λ X S, ⟨_, _⟩),
  { rintros ⟨h⟩,
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.cone_point_unique_up_to_iso (limit.is_limit _),
    exact (infer_instance : is_iso e.hom) },
  { introsI h,
    refine ⟨is_limit.of_iso_limit (limit.is_limit _) (cones.ext _ _)⟩,
    { apply (@as_iso _ _ _ _ _ h).symm },
    { intros a,
      symmetry,
      erw is_iso.inv_comp_eq,
      change _ = limit.lift _ _ ≫ _,
      simp } }
end

end multiequalizer_conditions

section

variables [has_products.{(max u₁ v₁)} A]

/--
The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of <https://stacks.math.columbia.edu/tag/00VM>.
-/
def first_obj : A :=
∏ (λ (f : Σ V, {f : V ⟶ U // R f}), P.obj (op f.1))

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of <https://stacks.math.columbia.edu/tag/00VM>.
-/
def fork_map : P.obj (op U) ⟶ first_obj R P :=
pi.lift (λ f, P.map f.2.1.op)

variables [has_pullbacks C]

/--
The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
def second_obj : A :=
∏ (λ (fg : (Σ V, {f : V ⟶ U // R f}) × (Σ W, {g : W ⟶ U // R g})),
  P.obj (op (pullback fg.1.2.1 fg.2.2.1)))

/-- The map `pr₀*` of <https://stacks.math.columbia.edu/tag/00VM>. -/
def first_map : first_obj R P ⟶ second_obj R P :=
pi.lift (λ fg, pi.π _ _ ≫ P.map pullback.fst.op)

/-- The map `pr₁*` of <https://stacks.math.columbia.edu/tag/00VM>. -/
def second_map : first_obj R P ⟶ second_obj R P :=
pi.lift (λ fg, pi.π _ _ ≫ P.map pullback.snd.op)

lemma w : fork_map R P ≫ first_map R P = fork_map R P ≫ second_map R P :=
begin
  apply limit.hom_ext,
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩,
  simp only [first_map, second_map, fork_map, limit.lift_π, limit.lift_π_assoc, assoc,
    fan.mk_π_app, subtype.coe_mk, subtype.val_eq_coe],
  rw [← P.map_comp, ← op_comp, pullback.condition],
  simp,
end

/--
An alternative definition of the sheaf condition in terms of equalizers. This is shown to be
equivalent in `category_theory.presheaf.is_sheaf_iff_is_sheaf'`.
-/
def is_sheaf' (P : Cᵒᵖ ⥤ A) : Prop := ∀ (U : C) (R : presieve U) (hR : generate R ∈ J U),
nonempty (is_limit (fork.of_ι _ (w R P)))

/-- (Implementation). An auxiliary lemma to convert between sheaf conditions. -/
def is_sheaf_for_is_sheaf_for' (P : Cᵒᵖ ⥤ A) (s : A ⥤ Type (max v₁ u₁))
  [Π J, preserves_limits_of_shape (discrete.{max v₁ u₁} J) s] (U : C) (R : presieve U) :
  is_limit (s.map_cone (fork.of_ι _ (w R P))) ≃
    is_limit (fork.of_ι _ (equalizer.presieve.w (P ⋙ s) R)) :=
begin
  apply equiv.trans (is_limit_map_cone_fork_equiv _ _) _,
  apply (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _),
  { apply nat_iso.of_components _ _,
    { rintro (_ | _),
      { apply preserves_product.iso s },
      { apply preserves_product.iso s } },
    { rintro _ _ (_ | _),
      { ext : 1,
        dsimp [equalizer.presieve.first_map, first_map],
        simp only [limit.lift_π, map_lift_pi_comparison, assoc, fan.mk_π_app, functor.map_comp],
        erw pi_comparison_comp_π_assoc },
      { ext : 1,
        dsimp [equalizer.presieve.second_map, second_map],
        simp only [limit.lift_π, map_lift_pi_comparison, assoc, fan.mk_π_app, functor.map_comp],
        erw pi_comparison_comp_π_assoc },
      { dsimp,
        simp } } },
  { refine fork.ext (iso.refl _) _,
    dsimp [equalizer.fork_map, fork_map],
    simp [fork.ι] }
end

/-- The equalizer definition of a sheaf given by `is_sheaf'` is equivalent to `is_sheaf`. -/
theorem is_sheaf_iff_is_sheaf' :
  is_sheaf J P ↔ is_sheaf' J P :=
begin
  split,
  { intros h U R hR,
    refine ⟨_⟩,
    apply coyoneda_jointly_reflects_limits,
    intro X,
    have q : presieve.is_sheaf_for (P ⋙ coyoneda.obj X) _ := h X.unop _ hR,
    rw ←presieve.is_sheaf_for_iff_generate at q,
    rw equalizer.presieve.sheaf_condition at q,
    replace q := classical.choice q,
    apply (is_sheaf_for_is_sheaf_for' _ _ _ _).symm q },
  { intros h U X S hS,
    rw equalizer.presieve.sheaf_condition,
    refine ⟨_⟩,
    refine is_sheaf_for_is_sheaf_for' _ _ _ _ _,
    letI := preserves_smallest_limits_of_preserves_limits (coyoneda.obj (op U)),
    apply is_limit_of_preserves,
    apply classical.choice (h _ S _),
    simpa }
end

end

section concrete

variables [has_pullbacks C]

/--
For a concrete category `(A, s)` where the forgetful functor `s : A ⥤ Type v` preserves limits and
reflects isomorphisms, and `A` has limits, an `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is a sheaf iff its
underlying `Type`-valued presheaf `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf.

Note this lemma applies for "algebraic" categories, eg groups, abelian groups and rings, but not
for the category of topological spaces, topological rings, etc since reflecting isomorphisms doesn't
hold.
-/
lemma is_sheaf_iff_is_sheaf_forget (s : A ⥤ Type (max v₁ u₁))
  [has_limits A] [preserves_limits s] [reflects_isomorphisms s] :
  is_sheaf J P ↔ is_sheaf J (P ⋙ s) :=
begin
  rw [is_sheaf_iff_is_sheaf', is_sheaf_iff_is_sheaf'],
  apply forall_congr (λ U, _),
  apply ball_congr (λ R hR, _),
  letI : reflects_limits s := reflects_limits_of_reflects_isomorphisms,
  have : is_limit (s.map_cone (fork.of_ι _ (w R P))) ≃ is_limit (fork.of_ι _ (w R (P ⋙ s))) :=
    is_sheaf_for_is_sheaf_for' P s U R,
  rw ←equiv.nonempty_congr this,
  split,
  { haveI := preserves_smallest_limits_of_preserves_limits s,
    exact nonempty.map (λ t, is_limit_of_preserves s t) },
  { haveI := reflects_smallest_limits_of_reflects_limits s,
    exact nonempty.map (λ t, is_limit_of_reflects s t) }
end

end concrete

end presheaf

end category_theory
