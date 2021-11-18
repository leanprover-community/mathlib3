/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction.basic
import category_theory.conj
import category_theory.yoneda
import category_theory.category.Cat

/-!
# Mate of natural transformations

This file establishes the bijection between the 2-cells

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, and shows that in the special case where `G,H` are identity then the
bijection preserves and reflects isomorphisms (i.e. we have bijections `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`, and
if either side is an iso then the other side is as well).

On its own, this bijection is not particularly useful but it includes a number of interesting cases
as specializations.

For instance, this generalises the fact that adjunctions are unique (since if `L₁ ≅ L₂` then we
deduce `R₁ ≅ R₂`).
Another example arises from considering the square representing that a functor `H` preserves
products, in particular the morphism `HA ⨯ H- ⟶ H(A ⨯ -)`. Then provided `(A ⨯ -)` and `HA ⨯ -` have
left adjoints (for instance if the relevant categories are cartesian closed), the transferred
natural transformation is the exponential comparison morphism: `H(A ^ -) ⟶ HA ^ H-`.
Furthermore if `H` has a left adjoint `L`, this morphism is an isomorphism iff its mate
`L(HA ⨯ -) ⟶ A ⨯ L-` is an isomorphism, see
https://ncatlab.org/nlab/show/Frobenius+reciprocity#InCategoryTheory.
This also relates to Grothendieck's yoga of six operations, though this is not spelled out in
mathlib: https://ncatlab.org/nlab/show/six+operations.
-/
universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace category_theory
open category

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]

section square

variables {E : Type u₃} {F : Type u₄} [category.{v₃} E] [category.{v₄} F]

variables {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variables (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

include adj₁ adj₂

/--
Suppose we have a square of functors (where the top and bottom are adjunctions `L₁ ⊣ R₁` and
`L₂ ⊣ R₂` respectively).

      C ↔ D
    G ↓   ↓ H
      E ↔ F

Then we have a bijection between natural transformations `G ⋙ L₂ ⟶ L₁ ⋙ H` and
`R₁ ⋙ G ⟶ H ⋙ R₂`.
This can be seen as a bijection of the 2-cells:

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

Note that if one of the transformations is an iso, it does not imply the other is an iso.
-/
def transfer_nat_trans : (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) :=
{ to_fun := λ h,
  { app := λ X, adj₂.unit.app _ ≫ R₂.map (h.app _ ≫ H.map (adj₁.counit.app _)),
    naturality' := λ X Y f,
    begin
      dsimp,
      rw [assoc, ← R₂.map_comp, assoc, ← H.map_comp, ← adj₁.counit_naturality, H.map_comp,
          ←functor.comp_map L₁, ←h.naturality_assoc],
      simp,
    end },
  inv_fun := λ h,
  { app := λ X, L₂.map (G.map (adj₁.unit.app _) ≫ h.app _) ≫ adj₂.counit.app _,
  naturality' := λ X Y f,
  begin
    dsimp,
    rw [← L₂.map_comp_assoc, ← G.map_comp_assoc, ← adj₁.unit_naturality, G.map_comp_assoc,
        ← functor.comp_map, h.naturality],
    simp,
  end },
  left_inv := λ h,
  begin
    ext X,
    dsimp,
    simp only [L₂.map_comp, assoc, adj₂.counit_naturality, adj₂.left_triangle_components_assoc,
      ←functor.comp_map G L₂, h.naturality_assoc, functor.comp_map L₁, ←H.map_comp,
      adj₁.left_triangle_components],
    dsimp,
    simp, -- See library note [dsimp, simp].
  end,
  right_inv := λ h,
  begin
    ext X,
    dsimp,
    simp [-functor.comp_map, ←functor.comp_map H, functor.comp_map R₁, -nat_trans.naturality,
      ←h.naturality, -functor.map_comp, ←functor.map_comp_assoc G, R₂.map_comp],
  end }

lemma transfer_nat_trans_counit (f : G ⋙ L₂ ⟶ L₁ ⋙ H) (Y : D) :
  L₂.map ((transfer_nat_trans adj₁ adj₂ f).app _) ≫ adj₂.counit.app _ =
    f.app _ ≫ H.map (adj₁.counit.app Y) :=
by { erw functor.map_comp, simp }

lemma unit_transfer_nat_trans (f : G ⋙ L₂ ⟶ L₁ ⋙ H) (X : C) :
  G.map (adj₁.unit.app X) ≫ (transfer_nat_trans adj₁ adj₂ f).app _ =
    adj₂.unit.app _ ≫ R₂.map (f.app _) :=
begin
  dsimp [transfer_nat_trans],
  rw [←adj₂.unit_naturality_assoc, ←R₂.map_comp, ← functor.comp_map G L₂, f.naturality_assoc,
    functor.comp_map, ← H.map_comp],
  dsimp, simp, -- See library note [dsimp, simp]
end

end square

section self

variables {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}
variables (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/--
Given two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` both between categories `C`, `D`, there is a
bijection between natural transformations `L₂ ⟶ L₁` and natural transformations `R₁ ⟶ R₂`.
This is defined as a special case of `transfer_nat_trans`, where the two "vertical" functors are
identity.
TODO: Generalise to when the two vertical functors are equivalences rather than being exactly `𝟭`.

Furthermore, this bijection preserves (and reflects) isomorphisms, i.e. a transformation is an iso
iff its image under the bijection is an iso, see eg `category_theory.transfer_nat_trans_self_iso`.
This is in contrast to the general case `transfer_nat_trans` which does not in general have this
property.
-/
def transfer_nat_trans_self : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) :=
calc (L₂ ⟶ L₁) ≃ _         : (iso.hom_congr L₂.left_unitor L₁.right_unitor).symm
           ... ≃ _         : transfer_nat_trans adj₁ adj₂
           ... ≃ (R₁ ⟶ R₂) : R₁.right_unitor.hom_congr R₂.left_unitor

lemma transfer_nat_trans_self_app (f : L₂ ⟶ L₁) (X : D) :
  (transfer_nat_trans_self adj₁ adj₂ f).app X =
    adj₂.unit.app (R₁.obj X) ≫ R₂.map (f.app (R₁.obj X) ≫ adj₁.counit.app X) :=
by { dsimp [transfer_nat_trans_self, transfer_nat_trans], simp }

lemma transfer_nat_trans_self_symm_app (f : R₁ ⟶ R₂) (X : C) :
  ((transfer_nat_trans_self adj₁ adj₂).symm f).app X =
    L₂.map (adj₁.unit.app X ≫ f.app (L₁.obj X)) ≫ adj₂.counit.app (L₁.obj X) :=
by { dsimp [transfer_nat_trans_self, transfer_nat_trans], simp }

lemma transfer_nat_trans_self_counit (f : L₂ ⟶ L₁) (X) :
  L₂.map ((transfer_nat_trans_self adj₁ adj₂ f).app _) ≫ adj₂.counit.app X =
    f.app _ ≫ adj₁.counit.app X :=
begin
  dsimp [transfer_nat_trans_self],
  rw [id_comp, comp_id],
  have := transfer_nat_trans_counit adj₁ adj₂ (L₂.left_unitor.hom ≫ f ≫ L₁.right_unitor.inv) X,
  dsimp at this,
  rw this,
  simp,
end

lemma unit_transfer_nat_trans_self (f : L₂ ⟶ L₁) (X) :
  adj₁.unit.app _ ≫ (transfer_nat_trans_self adj₁ adj₂ f).app _ =
    adj₂.unit.app X ≫ functor.map _ (f.app _) :=
begin
  dsimp [transfer_nat_trans_self],
  rw [id_comp, comp_id],
  have := unit_transfer_nat_trans adj₁ adj₂ (L₂.left_unitor.hom ≫ f ≫ L₁.right_unitor.inv) X,
  dsimp at this,
  rw this,
  simp
end

@[simp]
lemma transfer_nat_trans_self_id : transfer_nat_trans_self adj₁ adj₁ (𝟙 _) = 𝟙 _ :=
by { ext, dsimp [transfer_nat_trans_self, transfer_nat_trans], simp }
  -- See library note [dsimp, simp]

@[simp]
lemma transfer_nat_trans_self_symm_id :
  (transfer_nat_trans_self adj₁ adj₁).symm (𝟙 _) = 𝟙 _ :=
by { rw equiv.symm_apply_eq, simp }

lemma transfer_nat_trans_self_comp (f g) :
  transfer_nat_trans_self adj₁ adj₂ f ≫ transfer_nat_trans_self adj₂ adj₃ g =
    transfer_nat_trans_self adj₁ adj₃ (g ≫ f) :=
begin
  ext,
  dsimp [transfer_nat_trans_self, transfer_nat_trans],
  simp only [id_comp, comp_id],
  rw [←adj₃.unit_naturality_assoc, ←R₃.map_comp, g.naturality_assoc, L₂.map_comp, assoc,
    adj₂.counit_naturality, adj₂.left_triangle_components_assoc, assoc],
end

lemma transfer_nat_trans_self_symm_comp (f g) :
  (transfer_nat_trans_self adj₂ adj₁).symm f ≫ (transfer_nat_trans_self adj₃ adj₂).symm g =
    (transfer_nat_trans_self adj₃ adj₁).symm (g ≫ f) :=
by { rw [equiv.eq_symm_apply, ← transfer_nat_trans_self_comp _ adj₂], simp }

lemma transfer_nat_trans_self_comm {f g} (gf : g ≫ f = 𝟙 _) :
  transfer_nat_trans_self adj₁ adj₂ f ≫ transfer_nat_trans_self adj₂ adj₁ g = 𝟙 _ :=
by rw [transfer_nat_trans_self_comp, gf, transfer_nat_trans_self_id]

lemma transfer_nat_trans_self_symm_comm {f g} (gf : g ≫ f = 𝟙 _) :
  (transfer_nat_trans_self adj₁ adj₂).symm f ≫ (transfer_nat_trans_self adj₂ adj₁).symm g = 𝟙 _ :=
by rw [transfer_nat_trans_self_symm_comp, gf, transfer_nat_trans_self_symm_id]

/--
If `f` is an isomorphism, then the transferred natural transformation is an isomorphism.
The converse is given in `transfer_nat_trans_self_of_iso`.
-/
def transfer_nat_trans_self_iso (f : L₂ ≅ L₁) : R₁ ≅ R₂ :=
{ hom := transfer_nat_trans_self adj₁ adj₂ f.hom,
  inv := transfer_nat_trans_self adj₂ adj₁ f.inv,
  hom_inv_id' := transfer_nat_trans_self_comm _ _ (by simp),
  inv_hom_id' := transfer_nat_trans_self_comm _ _ (by simp) }

instance transfer_nat_trans_self_is_iso (f : L₂ ⟶ L₁) [is_iso f] :
  is_iso (transfer_nat_trans_self adj₁ adj₂ f) :=
is_iso.of_iso $ transfer_nat_trans_self_iso adj₁ adj₂ (as_iso f)

/--
If `f` is an isomorphism, then the un-transferred natural transformation is an isomorphism.
The converse is given in `transfer_nat_trans_self_symm_of_iso`.
-/
def transfer_nat_trans_self_symm_iso (f : R₁ ≅ R₂) : L₂ ≅ L₁ :=
{ hom := (transfer_nat_trans_self adj₁ adj₂).symm f.hom,
  inv := (transfer_nat_trans_self adj₂ adj₁).symm f.inv,
  hom_inv_id' := transfer_nat_trans_self_symm_comm _ _ (by simp),
  inv_hom_id' := transfer_nat_trans_self_symm_comm _ _ (by simp) }

instance transfer_nat_trans_self_symm_is_iso (f : R₁ ⟶ R₂) [is_iso f] :
  is_iso ((transfer_nat_trans_self adj₁ adj₂).symm f) :=
is_iso.of_iso $ transfer_nat_trans_self_symm_iso adj₁ adj₂ (as_iso f)

/--
If `f` is a natural transformation whose transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transfer_nat_trans_self_iso`.
-/
lemma transfer_nat_trans_self_of_iso (f : L₂ ⟶ L₁) [is_iso (transfer_nat_trans_self adj₁ adj₂ f)] :
  is_iso f :=
begin
  suffices :
    is_iso ((transfer_nat_trans_self adj₁ adj₂).symm (transfer_nat_trans_self adj₁ adj₂ f)),
  { simpa using this },
  apply_instance,
end

/--
If `f` is a natural transformation whose un-transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transfer_nat_trans_self_symm_iso`.
-/
lemma transfer_nat_trans_self_symm_of_iso (f : R₁ ⟶ R₂)
  [is_iso ((transfer_nat_trans_self adj₁ adj₂).symm f)] :
  is_iso f :=
begin
  suffices :
    is_iso ((transfer_nat_trans_self adj₁ adj₂) ((transfer_nat_trans_self adj₁ adj₂).symm f)),
  { simpa using this },
  apply_instance,
end

variables {ι : Type*} {L : ι → (C ⥤ D)} {R : ι → (D ⥤ C)}
{adj : ∀ i, L i ⊣ R i} {i j : ι} (h : i = j)
include h

lemma transfer_nat_trans_self_eq₁ {f : L₂ ⟶ L i} :
  transfer_nat_trans_self (adj i) adj₂ f =
  eq_to_hom (by rw h) ≫ transfer_nat_trans_self (adj j) adj₂ (f ≫ eq_to_hom (by rw h)) :=
by { cases h, erw [id_comp, comp_id] }

lemma transfer_nat_trans_self_eq₂ {f : L i ⟶ L₁} :
  transfer_nat_trans_self adj₁ (adj i) f =
  transfer_nat_trans_self adj₁ (adj j) (eq_to_hom (by rw h) ≫ f) ≫ eq_to_hom (by rw h) :=
by { cases h, erw [id_comp, comp_id] }

end self

variable (C)
/-- Definition follows https://stacks.math.columbia.edu/tag/003N, but replaces
    natural isomophisms with transformations `map_id` and `map_comp`. Notice that
    this is slightly different from the lax functor defined in
    https://ncatlab.org/nlab/show/pseudofunctor, because the direction of `map_comp`
    is different, so it seems ours definition is a mixture between lax and colax functors.
    However when `map_id` and `map_comp` are isomorphisms, obviously all definitions agree.

    It's harder to state for the general situation than for pushforward and pullback only,
    because there the associativity and composition with id are defeq. -/
structure lax_functor_to_Cat extends prefunctor C Cat :=
(map_id : ∀ (X : C), 𝟭 (obj X) ⟶ map (𝟙 X))
(map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) ⟶ map f ⋙ map g)
(id_comp : ∀ {X Y : C} (f : X ⟶ Y), map_comp (𝟙 X) f =
  eq_to_hom (by {rw id_comp, cases map f, refl}) ≫ whisker_right (map_id X) (map f) . obviously)
(comp_id : ∀ {X Y : C} (f : X ⟶ Y), map_comp f (𝟙 Y) =
  eq_to_hom (by {rw comp_id, cases map f, refl}) ≫ whisker_left (map f) (map_id Y) . obviously)
(assoc : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
  map_comp (f ≫ g) h ≫ whisker_right (map_comp f g) (map h) = eq_to_hom (by rw assoc) ≫
  map_comp f (g ≫ h) ≫ whisker_left (map f) (map_comp g h) . obviously)

instance : inhabited (lax_functor_to_Cat Cat) :=
⟨{ obj := 𝟙 Cat,
   map := λ _ _, id,
   map_id := λ _, 𝟙 _,
   map_comp := λ _ _ _ _ _, 𝟙 _ }⟩


def transfer_lax_functor (L : lax_functor_to_Cat C)
  (Rmap : ∀ {X Y : C} (f : X ⟶ Y), L.obj Y ⟶ L.obj X)
  (adj : ∀ {X Y : C} (f : X ⟶ Y), L.map f ⊣ Rmap f) :
  lax_functor_to_Cat Cᵒᵖ :=
{ obj := λ X, Cat.op.obj (L.obj X.unop),
  map := λ X Y f, functor.op (Rmap f.unop),
  map_id := λ X, nat_trans.op $
    transfer_nat_trans_self (adj (𝟙 X.unop)) adjunction.id (L.map_id X.unop),
  map_comp := λ X Y Z f g, nat_trans.op $ transfer_nat_trans_self
    (adjunction.comp _ _ (adj g.unop) (adj f.unop)) (adj (f ≫ g).unop) (L.map_comp g.unop f.unop),
  id_comp := λ X Y f, by {
    rw transfer_nat_trans_self_eq₂ _ (congr_arg quiver.hom.unop (id_comp f)),
    ext, induction x using opposite.rec,
    induction X using opposite.rec, induction Y using opposite.rec,
    apply quiver.hom.unop_inj, dsimp, set f' := f.unop,
    erw [transfer_nat_trans_self_app, L.comp_id],
    rw [adjunction.comp, eq_to_hom_trans_assoc, nat_trans.comp_app, eq_to_hom_app], erw id_comp,
    dsimp, rw id_comp,
    let : (L.to_prefunctor.map f').obj ((Rmap f').obj ((Rmap (𝟙 X)).obj x)) =
      (Rmap f' ⋙ L.map f').obj ((Rmap (𝟙 X)).obj x) := rfl, erw this,
    --rw functor.map_comp, dsimp, erw ← nat_trans.naturality_assoc (adj f').unit,
    --rw ← congr_arg (L.map_id X).app ((Rmap f').comp_obj (L.to_prefunctor.map f') ((Rmap (𝟙 X)).obj x)),
    change _ ≫ (Rmap f').map ((L.map_id X).app ((Rmap f' ⋙ L.map f').obj ((Rmap (𝟙 X)).obj x)) ≫ _) ≫ _ = _,

    have : (L.map_id X).app ((L.to_prefunctor.map f').obj ((Rmap f').obj ((Rmap (𝟙 X)).obj x)))
      = (L.map_id X).app ((Rmap f' ⋙ L.map f').obj ((Rmap (𝟙 X)).obj x)) := rfl,
      erw (Rmap f').comp_obj, rw this,
    --erw ← (Rmap f').comp_obj (L.to_prefunctor.map f') ((Rmap (𝟙 X)).obj x),
    --dsimp [-functor.comp_obj],-- rw id_comp,
    --have := (Rmap f').comp_obj (L.to_prefunctor.map f') ((Rmap (𝟙 X)).obj x),
    --rw ← this,
    --have := (L.map_id X).naturality_assoc ((adj f').counit.app ((Rmap (𝟙 X)).obj x)) ((adj (𝟙 X)).counit.app x),
    --rw ← this,
    rw ← nat_trans.naturality_assoc,

    --iterate 2 {erw transfer_nat_trans_self_app},
    --erw L.comp_id, rw [adjunction.comp, adjunction.id],
    --simp [transfer_nat_trans_self_app],
    --, adjunction.comp, adjunction.id
    --rw unop_id,
    simp,
     dsimp,

    rw ← functor.map_comp,

  rw comp_id, },
  comp_id := ,
  assoc := }


namespace lax_functor

end lax_functor

end category_theory
