/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import category_theory.comm_sq
import category_theory.limits.opposites
import category_theory.limits.shapes.biproducts
import category_theory.limits.shapes.zero_morphisms
import category_theory.limits.constructions.binary_products
import category_theory.limits.constructions.zero_objects

/-!
# Pullback and pushout squares, and bicartesian squares

We provide another API for pullbacks and pushouts.

`is_pullback fst snd f g` is the proposition that
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square.

(And similarly for `is_pushout`.)

We provide the glue to go back and forth to the usual `is_limit` API for pullbacks, and prove
`is_pullback (pullback.fst : pullback f g ⟶ X) (pullback.snd : pullback f g ⟶ Y) f g`
for the usual `pullback f g` provided by the `has_limit` API.

We don't attempt to restate everything we know about pullbacks in this language,
but do restate the pasting lemmas.

We define bicartesian squares, and
show that the pullback and pushout squares for a biproduct are bicartesian.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v₁ v₂ u₁ u₂

namespace category_theory

variables {C : Type u₁} [category.{v₁} C]

attribute [simp] comm_sq.mk

namespace comm_sq

variables {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/--
The (not necessarily limiting) `pullback_cone h i` implicit in the statement
that we have `comm_sq f g h i`.
-/
def cone (s : comm_sq f g h i) : pullback_cone h i := pullback_cone.mk _ _ s.w

/--
The (not necessarily limiting) `pushout_cocone f g` implicit in the statement
that we have `comm_sq f g h i`.
-/
def cocone (s : comm_sq f g h i) : pushout_cocone f g := pushout_cocone.mk _ _ s.w

@[simp] lemma cone_fst (s : comm_sq f g h i) : s.cone.fst = f := rfl
@[simp] lemma cone_snd (s : comm_sq f g h i) : s.cone.snd = g := rfl
@[simp] lemma cocone_inl (s : comm_sq f g h i) : s.cocone.inl = h := rfl
@[simp] lemma cocone_inr (s : comm_sq f g h i) : s.cocone.inr = i := rfl

/-- The pushout cocone in the opposite category associated to the cone of
a commutative square identifies to the cocone of the flipped commutative square in
the opposite category -/
def cone_op (p : comm_sq f g h i) : p.cone.op ≅ p.flip.op.cocone :=
pushout_cocone.ext (iso.refl _) (by tidy) (by tidy)

/-- The pullback cone in the opposite category associated to the cocone of
a commutative square identifies to the cone of the flipped commutative square in
the opposite category -/
def cocone_op (p : comm_sq f g h i) : p.cocone.op ≅ p.flip.op.cone :=
pullback_cone.ext (iso.refl _) (by tidy) (by tidy)

/-- The pushout cocone obtained from the pullback cone associated to a
commutative square in the opposite category identifies to the cocone associated
to the flipped square. -/
def cone_unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
  (p : comm_sq f g h i) : p.cone.unop ≅ p.flip.unop.cocone :=
pushout_cocone.ext (iso.refl _) (by tidy) (by tidy)

/-- The pullback cone obtained from the pushout cone associated to a
commutative square in the opposite category identifies to the cone associated
to the flipped square. -/
def cocone_unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
  (p : comm_sq f g h i) : p.cocone.unop ≅ p.flip.unop.cone :=
pullback_cone.ext (iso.refl _) (by tidy) (by tidy)

end comm_sq

/-- The proposition that a square
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square. (Also known as a fibered product or cartesian square.)
-/
structure is_pullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  extends comm_sq fst snd f g : Prop :=
(is_limit' : nonempty (is_limit (pullback_cone.mk _ _ w)))

/-- The proposition that a square
```
  Z ---f---> X
  |          |
  g         inl
  |          |
  v          v
  Y --inr--> P

```
is a pushout square. (Also known as a fiber coproduct or cocartesian square.)
-/
structure is_pushout {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)
  extends comm_sq f g inl inr : Prop :=
(is_colimit' : nonempty (is_colimit (pushout_cocone.mk _ _ w)))


section
set_option old_structure_cmd true

/-- A *bicartesian* square is a commutative square
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
that is both a pullback square and a pushout square.
-/
structure bicartesian_sq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z)
  extends is_pullback f g h i, is_pushout f g h i : Prop

-- Lean should make these parent projections as `lemma`, not `def`.
attribute [nolint def_lemma doc_blame] bicartesian_sq.to_is_pullback bicartesian_sq.to_is_pushout

end

/-!
We begin by providing some glue between `is_pullback` and the `is_limit` and `has_limit` APIs.
(And similarly for `is_pushout`.)
-/

namespace is_pullback

variables {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/--
The (limiting) `pullback_cone f g` implicit in the statement
that we have a `is_pullback fst snd f g`.
-/
def cone (h : is_pullback fst snd f g) : pullback_cone f g := h.to_comm_sq.cone

@[simp] lemma cone_fst (h : is_pullback fst snd f g) : h.cone.fst = fst := rfl
@[simp] lemma cone_snd (h : is_pullback fst snd f g) : h.cone.snd = snd := rfl

/--
The cone obtained from `is_pullback fst snd f g` is a limit cone.
-/
noncomputable def is_limit (h : is_pullback fst snd f g) : is_limit h.cone :=
h.is_limit'.some

/-- If `c` is a limiting pullback cone, then we have a `is_pullback c.fst c.snd f g`. -/
lemma of_is_limit {c : pullback_cone f g} (h : limits.is_limit c) :
  is_pullback c.fst c.snd f g :=
{ w := c.condition,
  is_limit' := ⟨is_limit.of_iso_limit h
    (limits.pullback_cone.ext (iso.refl _) (by tidy) (by tidy))⟩, }

/-- A variant of `of_is_limit` that is more useful with `apply`. -/
lemma of_is_limit' (w : comm_sq fst snd f g) (h : limits.is_limit w.cone) :
  is_pullback fst snd f g :=
of_is_limit h

/-- The pullback provided by `has_pullback f g` fits into a `is_pullback`. -/
lemma of_has_pullback (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] :
  is_pullback (pullback.fst : pullback f g ⟶ X) (pullback.snd : pullback f g ⟶ Y) f g :=
of_is_limit (limit.is_limit (cospan f g))

/-- If `c` is a limiting binary product cone, and we have a terminal object,
then we have `is_pullback c.fst c.snd 0 0`
(where each `0` is the unique morphism to the terminal object). -/
lemma of_is_product {c : binary_fan X Y} (h : limits.is_limit c) (t : is_terminal Z) :
  is_pullback c.fst c.snd (t.from _) (t.from _) :=
of_is_limit (is_pullback_of_is_terminal_is_product _ _ _ _ t
  (is_limit.of_iso_limit h (limits.cones.ext (iso.refl c.X) (by rintro ⟨⟨⟩⟩; { dsimp, simp, }))))

/-- A variant of `of_is_product` that is more useful with `apply`. -/
lemma of_is_product' (h : limits.is_limit (binary_fan.mk fst snd)) (t : is_terminal Z) :
  is_pullback fst snd (t.from _) (t.from _) :=
of_is_product h t

variables (X Y)

lemma of_has_binary_product' [has_binary_product X Y] [has_terminal C] :
  is_pullback limits.prod.fst limits.prod.snd (terminal.from X) (terminal.from Y) :=
of_is_product (limit.is_limit _) terminal_is_terminal

open_locale zero_object

lemma of_has_binary_product [has_binary_product X Y] [has_zero_object C] [has_zero_morphisms C] :
  is_pullback limits.prod.fst limits.prod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
by convert of_is_product (limit.is_limit _) has_zero_object.zero_is_terminal

variables {X Y}

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `has_limit` API. -/
noncomputable
def iso_pullback (h : is_pullback fst snd f g) [has_pullback f g] : P ≅ pullback f g :=
(limit.iso_limit_cone ⟨_, h.is_limit⟩).symm

@[simp] lemma iso_pullback_hom_fst (h : is_pullback fst snd f g) [has_pullback f g] :
  h.iso_pullback.hom ≫ pullback.fst = fst :=
by { dsimp [iso_pullback, cone, comm_sq.cone], simp, }
@[simp] lemma iso_pullback_hom_snd (h : is_pullback fst snd f g) [has_pullback f g] :
  h.iso_pullback.hom ≫ pullback.snd = snd :=
by { dsimp [iso_pullback, cone, comm_sq.cone], simp, }
@[simp] lemma iso_pullback_inv_fst (h : is_pullback fst snd f g) [has_pullback f g] :
  h.iso_pullback.inv ≫ fst = pullback.fst :=
by simp [iso.inv_comp_eq]
@[simp] lemma iso_pullback_inv_snd (h : is_pullback fst snd f g) [has_pullback f g] :
  h.iso_pullback.inv ≫ snd = pullback.snd :=
by simp [iso.inv_comp_eq]

lemma of_iso_pullback (h : comm_sq fst snd f g) [has_pullback f g] (i : P ≅ pullback f g)
  (w₁ : i.hom ≫ pullback.fst = fst) (w₂ : i.hom ≫ pullback.snd = snd) : is_pullback fst snd f g :=
of_is_limit' h (limits.is_limit.of_iso_limit (limit.is_limit _)
  (@pullback_cone.ext _ _ _ _ _ _ _ (pullback_cone.mk _ _ _) _ i w₁.symm w₂.symm).symm)

lemma of_horiz_is_iso [is_iso fst] [is_iso g] (sq : comm_sq fst snd f g) :
  is_pullback fst snd f g := of_is_limit' sq
begin
  refine pullback_cone.is_limit.mk _ (λ s, s.fst ≫ inv fst) (by tidy) (λ s, _) (by tidy),
  simp only [← cancel_mono g, category.assoc, ← sq.w, is_iso.inv_hom_id_assoc, s.condition],
end

end is_pullback

namespace is_pushout

variables {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/--
The (colimiting) `pushout_cocone f g` implicit in the statement
that we have a `is_pushout f g inl inr`.
-/
def cocone (h : is_pushout f g inl inr) : pushout_cocone f g := h.to_comm_sq.cocone

@[simp] lemma cocone_inl (h : is_pushout f g inl inr) : h.cocone.inl = inl := rfl
@[simp] lemma cocone_inr (h : is_pushout f g inl inr) : h.cocone.inr = inr := rfl

/--
The cocone obtained from `is_pushout f g inl inr` is a colimit cocone.
-/
noncomputable def is_colimit (h : is_pushout f g inl inr) : is_colimit h.cocone :=
h.is_colimit'.some

/-- If `c` is a colimiting pushout cocone, then we have a `is_pushout f g c.inl c.inr`. -/
lemma of_is_colimit {c : pushout_cocone f g} (h : limits.is_colimit c) :
  is_pushout f g c.inl c.inr :=
{ w := c.condition,
  is_colimit' := ⟨is_colimit.of_iso_colimit h
    (limits.pushout_cocone.ext (iso.refl _) (by tidy) (by tidy))⟩, }

/-- A variant of `of_is_colimit` that is more useful with `apply`. -/
lemma of_is_colimit' (w : comm_sq f g inl inr) (h : limits.is_colimit w.cocone) :
  is_pushout f g inl inr :=
of_is_colimit h

/-- The pushout provided by `has_pushout f g` fits into a `is_pushout`. -/
lemma of_has_pushout (f : Z ⟶ X) (g : Z ⟶ Y) [has_pushout f g] :
  is_pushout f g (pushout.inl : X ⟶ pushout f g) (pushout.inr : Y ⟶ pushout f g) :=
of_is_colimit (colimit.is_colimit (span f g))

/-- If `c` is a colimiting binary coproduct cocone, and we have an initial object,
then we have `is_pushout 0 0 c.inl c.inr`
(where each `0` is the unique morphism from the initial object). -/
lemma of_is_coproduct {c : binary_cofan X Y} (h : limits.is_colimit c) (t : is_initial Z) :
  is_pushout (t.to _) (t.to _) c.inl c.inr :=
of_is_colimit (is_pushout_of_is_initial_is_coproduct _ _ _ _ t
  (is_colimit.of_iso_colimit h
    (limits.cocones.ext (iso.refl c.X) (by rintro ⟨⟨⟩⟩; { dsimp, simp, }))))

/-- A variant of `of_is_coproduct` that is more useful with `apply`. -/
lemma of_is_coproduct' (h : limits.is_colimit (binary_cofan.mk inl inr)) (t : is_initial Z) :
  is_pushout (t.to _) (t.to _) inl inr :=
of_is_coproduct h t

variables (X Y)

lemma of_has_binary_coproduct' [has_binary_coproduct X Y] [has_initial C] :
  is_pushout (initial.to _) (initial.to _) (coprod.inl : X ⟶ _) (coprod.inr : Y ⟶ _)  :=
of_is_coproduct (colimit.is_colimit _) initial_is_initial

open_locale zero_object

lemma of_has_binary_coproduct
  [has_binary_coproduct X Y] [has_zero_object C] [has_zero_morphisms C] :
  is_pushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) coprod.inl coprod.inr :=
by convert of_is_coproduct (colimit.is_colimit _) has_zero_object.zero_is_initial

variables {X Y}

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `has_limit` API. -/
noncomputable
def iso_pushout (h : is_pushout f g inl inr) [has_pushout f g] : P ≅ pushout f g :=
(colimit.iso_colimit_cocone ⟨_, h.is_colimit⟩).symm

@[simp] lemma inl_iso_pushout_inv (h : is_pushout f g inl inr) [has_pushout f g] :
  pushout.inl ≫ h.iso_pushout.inv = inl :=
by { dsimp [iso_pushout, cocone, comm_sq.cocone], simp, }
@[simp] lemma inr_iso_pushout_inv (h : is_pushout f g inl inr) [has_pushout f g] :
  pushout.inr ≫ h.iso_pushout.inv = inr :=
by { dsimp [iso_pushout, cocone, comm_sq.cocone], simp, }
@[simp] lemma inl_iso_pushout_hom (h : is_pushout f g inl inr) [has_pushout f g] :
  inl ≫ h.iso_pushout.hom = pushout.inl :=
by simp [←iso.eq_comp_inv]
@[simp] lemma inr_iso_pushout_hom (h : is_pushout f g inl inr) [has_pushout f g] :
  inr ≫ h.iso_pushout.hom = pushout.inr :=
by simp [←iso.eq_comp_inv]

lemma of_iso_pushout (h : comm_sq f g inl inr) [has_pushout f g] (i : P ≅ pushout f g)
  (w₁ : inl ≫ i.hom = pushout.inl) (w₂ : inr ≫ i.hom = pushout.inr) : is_pushout f g inl inr :=
of_is_colimit' h (limits.is_colimit.of_iso_colimit (colimit.is_colimit _)
  (@pushout_cocone.ext _ _ _ _ _ _ _ (pushout_cocone.mk _ _ _) _ i w₁ w₂).symm)

end is_pushout

namespace is_pullback

variables {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma flip (h : is_pullback fst snd f g) : is_pullback snd fst g f :=
of_is_limit (@pullback_cone.flip_is_limit _ _ _ _ _ _ _ _ _ _ h.w.symm h.is_limit)

lemma flip_iff : is_pullback fst snd f g ↔ is_pullback snd fst g f :=
⟨flip, flip⟩

section

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

/-- The square with `0 : 0 ⟶ 0` on the left and `𝟙 X` on the right is a pullback square. -/
@[simp] lemma zero_left (X : C) : is_pullback (0 : 0 ⟶ X) (0 : 0 ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
{ w := by simp,
  is_limit' :=
  ⟨{ lift := λ s, 0,
     fac' := λ s, by simpa using @pullback_cone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
       (by simpa using (pullback_cone.condition s).symm), }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pullback square. -/
@[simp] lemma zero_top (X : C) : is_pullback (0 : 0 ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
(zero_left X).flip

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pullback square. -/
@[simp] lemma zero_right (X : C) : is_pullback (0 : X ⟶ 0) (𝟙 X) (0 : 0 ⟶ 0) (0 : X ⟶ 0) :=
of_iso_pullback (by simp) ((zero_prod_iso X).symm ≪≫ (pullback_zero_zero_iso _ _).symm)
  (by simp) (by simp)

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pullback square. -/
@[simp] lemma zero_bot (X : C) : is_pullback (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : 0 ⟶ 0) :=
(zero_right X).flip

end

/-- Paste two pullback squares "vertically" to obtain another pullback square. -/
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
lemma paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : is_pullback h₁₁ v₁₁ v₁₂ h₂₁) (t : is_pullback h₂₁ v₂₁ v₂₂ h₃₁) :
  is_pullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
(of_is_limit
  (big_square_is_pullback _ _ _ _ _ _ _ s.w t.w t.is_limit s.is_limit))

/-- Paste two pullback squares "horizontally" to obtain another pullback square. -/
lemma paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : is_pullback h₁₁ v₁₁ v₁₂ h₂₁) (t : is_pullback h₁₂ v₁₂ v₁₃ h₂₂) :
  is_pullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
(paste_vert s.flip t.flip).flip

/-- Given a pullback square assembled from a commuting square on the top and
a pullback square on the bottom, the top square is a pullback square. -/
lemma of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : is_pullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
  (t : is_pullback h₂₁ v₂₁ v₂₂ h₃₁) :
  is_pullback h₁₁ v₁₁ v₁₂ h₂₁ :=
of_is_limit (left_square_is_pullback _ _ _ _ _ _ _ p _ t.is_limit s.is_limit)

/-- Given a pullback square assembled from a commuting square on the left and
a pullback square on the right, the left square is a pullback square. -/
lemma of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : is_pullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
  (t : is_pullback h₁₂ v₁₂ v₁₃ h₂₂) :
  is_pullback h₁₁ v₁₁ v₁₂ h₂₁ :=
(of_bot s.flip p.symm t.flip).flip

lemma paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : is_pullback h₂₁ v₂₁ v₂₂ h₃₁) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
  is_pullback h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ is_pullback h₁₁ v₁₁ v₁₂ h₂₁ :=
⟨λ h, h.of_bot e s, λ h, h.paste_vert s⟩

lemma paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : is_pullback h₁₂ v₁₂ v₁₃ h₂₂) (e : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
  is_pullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ is_pullback h₁₁ v₁₁ v₁₂ h₂₁ :=
⟨λ h, h.of_right e s, λ h, h.paste_horiz s⟩

section

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

lemma of_is_bilimit {b : binary_bicone X Y} (h : b.is_bilimit) :
  is_pullback b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
by convert is_pullback.of_is_product' h.is_limit has_zero_object.zero_is_terminal

@[simp] lemma of_has_biproduct (X Y : C) [has_binary_biproduct X Y] :
  is_pullback biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
of_is_bilimit (binary_biproduct.is_bilimit X Y)

lemma inl_snd' {b : binary_bicone X Y} (h : b.is_bilimit) :
  is_pullback b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) :=
by { refine of_right _ (by simp) (of_is_bilimit h), simp, }

/--
The square
```
  X --inl--> X ⊞ Y
  |            |
  0           snd
  |            |
  v            v
  0 ---0-----> Y
```
is a pullback square.
-/
@[simp] lemma inl_snd (X Y : C) [has_binary_biproduct X Y] :
  is_pullback biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
inl_snd' (binary_biproduct.is_bilimit X Y)

lemma inr_fst' {b : binary_bicone X Y} (h : b.is_bilimit) :
  is_pullback b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) :=
by { apply flip, refine of_bot _ (by simp) (of_is_bilimit h), simp, }

/--
The square
```
  Y --inr--> X ⊞ Y
  |            |
  0           fst
  |            |
  v            v
  0 ---0-----> X
```
is a pullback square.
-/
@[simp] lemma inr_fst (X Y : C) [has_binary_biproduct X Y] :
  is_pullback biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
inr_fst' (binary_biproduct.is_bilimit X Y)

lemma of_is_bilimit' {b : binary_bicone X Y} (h : b.is_bilimit) :
  is_pullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr :=
by { refine is_pullback.of_right _ (by simp) (is_pullback.inl_snd' h).flip, simp, }

lemma of_has_binary_biproduct (X Y : C) [has_binary_biproduct X Y] :
  is_pullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
of_is_bilimit' (binary_biproduct.is_bilimit X Y)

instance has_pullback_biprod_fst_biprod_snd [has_binary_biproduct X Y] :
  has_pullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) :=
has_limit.mk ⟨_, (of_has_binary_biproduct X Y).is_limit⟩

/-- The pullback of `biprod.inl` and `biprod.inr` is the zero object. -/
def pullback_biprod_inl_biprod_inr [has_binary_biproduct X Y] :
  pullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) ≅ 0 :=
limit.iso_limit_cone ⟨_, (of_has_binary_biproduct X Y).is_limit⟩

end

lemma op (h : is_pullback fst snd f g) : is_pushout g.op f.op snd.op fst.op :=
is_pushout.of_is_colimit (is_colimit.of_iso_colimit
  (limits.pullback_cone.is_limit_equiv_is_colimit_op h.flip.cone h.flip.is_limit)
  h.to_comm_sq.flip.cone_op)

lemma unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (h : is_pullback fst snd f g) : is_pushout g.unop f.unop snd.unop fst.unop :=
is_pushout.of_is_colimit (is_colimit.of_iso_colimit
  (limits.pullback_cone.is_limit_equiv_is_colimit_unop h.flip.cone h.flip.is_limit)
  h.to_comm_sq.flip.cone_unop)

lemma of_vert_is_iso [is_iso snd] [is_iso f] (sq : comm_sq fst snd f g) :
  is_pullback fst snd f g := is_pullback.flip (of_horiz_is_iso sq.flip)

end is_pullback

namespace is_pushout

variables {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

lemma flip (h : is_pushout f g inl inr) : is_pushout g f inr inl :=
of_is_colimit (@pushout_cocone.flip_is_colimit _ _ _ _ _ _ _ _ _ _ h.w.symm h.is_colimit)

lemma flip_iff : is_pushout f g inl inr ↔ is_pushout g f inr inl :=
⟨flip, flip⟩

section

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pushout square. -/
@[simp] lemma zero_right (X : C) : is_pushout (0 : X ⟶ 0) (𝟙 X) (0 : 0 ⟶ 0) (0 : X ⟶ 0) :=
{ w := by simp,
  is_colimit' :=
  ⟨{ desc := λ s, 0,
     fac' := λ s, begin
       have c := @pushout_cocone.coequalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _) (by simp)
         (by simpa using (pushout_cocone.condition s)),
      dsimp at c,
      simpa using c,
     end }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pushout square. -/
@[simp] lemma zero_bot (X : C) : is_pushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : 0 ⟶ 0) :=
(zero_right X).flip

/-- The square with `0 : 0 ⟶ 0` on the right left `𝟙 X` on the right is a pushout square. -/
@[simp] lemma zero_left (X : C) : is_pushout (0 : 0 ⟶ X) (0 : 0 ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
of_iso_pushout (by simp) ((coprod_zero_iso X).symm ≪≫ (pushout_zero_zero_iso _ _).symm)
  (by simp) (by simp)

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pushout square. -/
@[simp] lemma zero_top (X : C) : is_pushout (0 : 0 ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
(zero_left X).flip

end

/-- Paste two pushout squares "vertically" to obtain another pushout square. -/
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
lemma paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : is_pushout h₁₁ v₁₁ v₁₂ h₂₁) (t : is_pushout h₂₁ v₂₁ v₂₂ h₃₁) :
  is_pushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
(of_is_colimit
  (big_square_is_pushout _ _ _ _ _ _ _ s.w t.w t.is_colimit s.is_colimit))

/-- Paste two pushout squares "horizontally" to obtain another pushout square. -/
lemma paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : is_pushout h₁₁ v₁₁ v₁₂ h₂₁) (t : is_pushout h₁₂ v₁₂ v₁₃ h₂₂) :
  is_pushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
(paste_vert s.flip t.flip).flip

/-- Given a pushout square assembled from a pushout square on the top and
a commuting square on the bottom, the bottom square is a pushout square. -/
lemma of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : is_pushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁)
  (t : is_pushout h₁₁ v₁₁ v₁₂ h₂₁) :
  is_pushout h₂₁ v₂₁ v₂₂ h₃₁ :=
of_is_colimit (right_square_is_pushout _ _ _ _ _ _ _ _ p t.is_colimit s.is_colimit)

/-- Given a pushout square assembled from a pushout square on the left and
a commuting square on the right, the right square is a pushout square. -/
lemma of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : is_pushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂)
  (t : is_pushout h₁₁ v₁₁ v₁₂ h₂₁) :
  is_pushout h₁₂ v₁₂ v₁₃ h₂₂ :=
(of_bot s.flip p.symm t.flip).flip

lemma paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : is_pushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁) :
  is_pushout h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ ↔ is_pushout h₂₁ v₂₁ v₂₂ h₃₁ :=
⟨λ h, h.of_bot e s, s.paste_vert⟩

lemma paste_horiz_iff {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : is_pushout h₁₁ v₁₁ v₁₂ h₂₁) (e : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂) :
  is_pushout (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) ↔ is_pushout h₁₂ v₁₂ v₁₃ h₂₂ :=
⟨λ h, h.of_right e s, s.paste_horiz⟩

section

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

lemma of_is_bilimit {b : binary_bicone X Y} (h : b.is_bilimit) :
  is_pushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr :=
by convert is_pushout.of_is_coproduct' h.is_colimit has_zero_object.zero_is_initial

@[simp] lemma of_has_biproduct (X Y : C) [has_binary_biproduct X Y] :
  is_pushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
of_is_bilimit (binary_biproduct.is_bilimit X Y)

lemma inl_snd' {b : binary_bicone X Y} (h : b.is_bilimit) :
  is_pushout b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) :=
by { apply flip, refine of_right _ (by simp) (of_is_bilimit h), simp, }

/--
The square
```
  X --inl--> X ⊞ Y
  |            |
  0           snd
  |            |
  v            v
  0 ---0-----> Y
```
is a pushout square.
-/
lemma inl_snd (X Y : C) [has_binary_biproduct X Y] :
  is_pushout biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
inl_snd' (binary_biproduct.is_bilimit X Y)

lemma inr_fst' {b : binary_bicone X Y} (h : b.is_bilimit) :
  is_pushout b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) :=
by { refine of_bot _ (by simp) (of_is_bilimit h), simp, }

/--
The square
```
  Y --inr--> X ⊞ Y
  |            |
  0           fst
  |            |
  v            v
  0 ---0-----> X
```
is a pushout square.
-/
lemma inr_fst (X Y : C) [has_binary_biproduct X Y] :
  is_pushout biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
inr_fst' (binary_biproduct.is_bilimit X Y)

lemma of_is_bilimit' {b : binary_bicone X Y} (h : b.is_bilimit) :
  is_pushout b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
by { refine is_pushout.of_right _ (by simp) (is_pushout.inl_snd' h), simp, }

lemma of_has_binary_biproduct (X Y : C) [has_binary_biproduct X Y] :
  is_pushout biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
of_is_bilimit' (binary_biproduct.is_bilimit X Y)

instance has_pushout_biprod_fst_biprod_snd [has_binary_biproduct X Y] :
  has_pushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) :=
has_colimit.mk ⟨_, (of_has_binary_biproduct X Y).is_colimit⟩

/-- The pushout of `biprod.fst` and `biprod.snd` is the zero object. -/
def pushout_biprod_fst_biprod_snd [has_binary_biproduct X Y] :
  pushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) ≅ 0 :=
colimit.iso_colimit_cocone ⟨_, (of_has_binary_biproduct X Y).is_colimit⟩

end

lemma op (h : is_pushout f g inl inr) : is_pullback inr.op inl.op g.op f.op :=
is_pullback.of_is_limit (is_limit.of_iso_limit
  (limits.pushout_cocone.is_colimit_equiv_is_limit_op h.flip.cocone h.flip.is_colimit)
  h.to_comm_sq.flip.cocone_op)

lemma unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  (h : is_pushout f g inl inr) : is_pullback inr.unop inl.unop g.unop f.unop :=
is_pullback.of_is_limit (is_limit.of_iso_limit
  (limits.pushout_cocone.is_colimit_equiv_is_limit_unop h.flip.cocone h.flip.is_colimit)
  h.to_comm_sq.flip.cocone_unop)

lemma of_horiz_is_iso [is_iso f] [is_iso inr] (sq : comm_sq f g inl inr) :
  is_pushout f g inl inr := of_is_colimit' sq
begin
  refine pushout_cocone.is_colimit.mk _ (λ s, inv inr ≫ s.inr) (λ s, _) (by tidy) (by tidy),
  simp only [← cancel_epi f, s.condition, sq.w_assoc, is_iso.hom_inv_id_assoc],
end

lemma of_vert_is_iso [is_iso g] [is_iso inl] (sq : comm_sq f g inl inr) :
  is_pushout f g inl inr := (of_horiz_is_iso sq.flip).flip

end is_pushout

section equalizer

variables {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}

/-- If `f : X ⟶ Y`, `g g' : Y ⟶ Z` forms a pullback square, then `f` is the equalizer of
`g` and `g'`. -/
noncomputable
def is_pullback.is_limit_fork (H : is_pullback f f g g') :
  is_limit (fork.of_ι f H.w) :=
begin
  fapply fork.is_limit.mk,
  { exact λ s, H.is_limit.lift (pullback_cone.mk s.ι s.ι s.condition) },
  { exact λ s, H.is_limit.fac _ walking_cospan.left },
  { intros s m e, apply pullback_cone.is_limit.hom_ext H.is_limit; refine e.trans _;
      symmetry; exact H.is_limit.fac _ _ }
end

/-- If `f f' : X ⟶ Y`, `g : Y ⟶ Z` forms a pushout square, then `g` is the coequalizer of
`f` and `f'`. -/
noncomputable
def is_pushout.is_limit_fork (H : is_pushout f f' g g) :
  is_colimit (cofork.of_π g H.w) :=
begin
  fapply cofork.is_colimit.mk,
  { exact λ s, H.is_colimit.desc (pushout_cocone.mk s.π s.π s.condition) },
  { exact λ s, H.is_colimit.fac _ walking_span.left },
  { intros s m e, apply pushout_cocone.is_colimit.hom_ext H.is_colimit; refine e.trans _;
      symmetry; exact H.is_colimit.fac _ _ }
end

end equalizer

namespace bicartesian_sq

variables {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

lemma of_is_pullback_is_pushout (p₁ : is_pullback f g h i) (p₂ : is_pushout f g h i) :
  bicartesian_sq f g h i :=
bicartesian_sq.mk p₁.to_comm_sq ⟨p₁.is_limit⟩ ⟨p₂.is_colimit⟩

lemma flip (p : bicartesian_sq f g h i) : bicartesian_sq g f i h :=
of_is_pullback_is_pushout p.to_is_pullback.flip p.to_is_pushout.flip

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

/--
```
 X ⊞ Y --fst--> X
   |            |
  snd           0
   |            |
   v            v
   Y -----0---> 0
```
is a bicartesian square.
-/
lemma of_is_biproduct₁ {b : binary_bicone X Y} (h : b.is_bilimit) :
  bicartesian_sq b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
of_is_pullback_is_pushout (is_pullback.of_is_bilimit h) (is_pushout.of_is_bilimit' h)

/--
```
   0 -----0---> X
   |            |
   0           inl
   |            |
   v            v
   Y --inr--> X ⊞ Y
```
is a bicartesian square.
-/
lemma of_is_biproduct₂ {b : binary_bicone X Y} (h : b.is_bilimit) :
  bicartesian_sq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr :=
of_is_pullback_is_pushout (is_pullback.of_is_bilimit' h) (is_pushout.of_is_bilimit h)

/--
```
 X ⊞ Y --fst--> X
   |            |
  snd           0
   |            |
   v            v
   Y -----0---> 0
```
is a bicartesian square.
-/
@[simp] lemma of_has_biproduct₁ [has_binary_biproduct X Y] :
  bicartesian_sq biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
by convert of_is_biproduct₁ (binary_biproduct.is_bilimit X Y)

/--
```
   0 -----0---> X
   |            |
   0           inl
   |            |
   v            v
   Y --inr--> X ⊞ Y
```
is a bicartesian square.
-/
@[simp] lemma of_has_biproduct₂ [has_binary_biproduct X Y] :
  bicartesian_sq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
by convert of_is_biproduct₂ (binary_biproduct.is_bilimit X Y)

end bicartesian_sq

section functor

variables {D : Type u₂} [category.{v₂} D]
variables (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

lemma functor.map_is_pullback [preserves_limit (cospan h i) F] (s : is_pullback f g h i) :
  is_pullback (F.map f) (F.map g) (F.map h) (F.map i) :=
-- This is made slightly awkward because `C` and `D` have different universes,
-- and so the relevant `walking_cospan` diagrams live in different universes too!
begin
  refine is_pullback.of_is_limit' (F.map_comm_sq s.to_comm_sq)
    (is_limit.equiv_of_nat_iso_of_iso (cospan_comp_iso F h i) _ _ (walking_cospan.ext _ _ _)
      (is_limit_of_preserves F s.is_limit)),
  { refl, },
  { dsimp, simp, },
  { dsimp, simp, },
end

lemma functor.map_is_pushout [preserves_colimit (span f g) F] (s : is_pushout f g h i) :
  is_pushout (F.map f) (F.map g) (F.map h) (F.map i) :=
begin
  refine is_pushout.of_is_colimit' (F.map_comm_sq s.to_comm_sq)
    (is_colimit.equiv_of_nat_iso_of_iso (span_comp_iso F f g) _ _ (walking_span.ext _ _ _)
      (is_colimit_of_preserves F s.is_colimit)),
  { refl, },
  { dsimp, simp, },
  { dsimp, simp, },
end

alias functor.map_is_pullback ← is_pullback.map
alias functor.map_is_pushout ← is_pushout.map

lemma is_pullback.of_map [reflects_limit (cospan h i) F] (e : f ≫ h = g ≫ i)
  (H : is_pullback (F.map f) (F.map g) (F.map h) (F.map i)) : is_pullback f g h i :=
begin
  refine ⟨⟨e⟩, ⟨is_limit_of_reflects F $ _⟩⟩,
  refine (is_limit.equiv_of_nat_iso_of_iso (cospan_comp_iso F h i) _ _
    (walking_cospan.ext _ _ _)).symm H.is_limit,
  exacts [iso.refl _, (category.comp_id _).trans (category.id_comp _).symm,
    (category.comp_id _).trans (category.id_comp _).symm]
end

lemma is_pullback.of_map_of_faithful [reflects_limit (cospan h i) F] [faithful F]
  (H : is_pullback (F.map f) (F.map g) (F.map h) (F.map i)) : is_pullback f g h i :=
H.of_map F (F.map_injective $ by simpa only [F.map_comp] using H.w)

lemma is_pullback.map_iff {D : Type*} [category D] (F : C ⥤ D)
  [preserves_limit (cospan h i) F] [reflects_limit (cospan h i) F] (e : f ≫ h = g ≫ i) :
  is_pullback (F.map f) (F.map g) (F.map h) (F.map i) ↔ is_pullback f g h i  :=
⟨λ h, h.of_map F e, λ h, h.map F⟩

lemma is_pushout.of_map [reflects_colimit (span f g) F] (e : f ≫ h = g ≫ i)
  (H : is_pushout (F.map f) (F.map g) (F.map h) (F.map i)) : is_pushout f g h i :=
begin
  refine ⟨⟨e⟩, ⟨is_colimit_of_reflects F $ _⟩⟩,
  refine (is_colimit.equiv_of_nat_iso_of_iso (span_comp_iso F f g) _ _
    (walking_span.ext _ _ _)).symm H.is_colimit,
  exacts [iso.refl _, (category.comp_id _).trans (category.id_comp _),
    (category.comp_id _).trans (category.id_comp _)]
end

lemma is_pushout.of_map_of_faithful [reflects_colimit (span f g) F] [faithful F]
  (H : is_pushout (F.map f) (F.map g) (F.map h) (F.map i)) : is_pushout f g h i :=
H.of_map F (F.map_injective $ by simpa only [F.map_comp] using H.w)

lemma is_pushout.map_iff {D : Type*} [category D] (F : C ⥤ D)
  [preserves_colimit (span f g) F] [reflects_colimit (span f g) F] (e : f ≫ h = g ≫ i) :
  is_pushout (F.map f) (F.map g) (F.map h) (F.map i) ↔ is_pushout f g h i  :=
⟨λ h, h.of_map F e, λ h, h.map F⟩

end functor

end category_theory
