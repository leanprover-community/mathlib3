/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import category_theory.comm_sq
import category_theory.limits.preserves.shapes.pullbacks
import category_theory.limits.shapes.zero_morphisms
import category_theory.limits.constructions.binary_products
import category_theory.limits.opposites

/-!
# Pullback and pushout squares

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

## Future work
Bicartesian squares, and
show that the pullback and pushout squares for a biproduct are bicartesian.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v₁ v₂ u₁ u₂

namespace category_theory

variables {C : Type u₁} [category.{v₁} C]

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
is a pullback square.
-/
structure is_pullback
  {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
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
is a pushout square.
-/
structure is_pushout
  {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)
  extends comm_sq f g inl inr : Prop :=
(is_colimit' : nonempty (is_colimit (pushout_cocone.mk _ _ w)))

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

end is_pullback

namespace is_pushout

variables {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/--
The (colimiting) `pushout_cocone f g` implicit in the statement
that we have a `is_pushout f g inl inr`.
-/
def cocone (h : is_pushout f g inl inr) : pushout_cocone f g := h.to_comm_sq.cocone

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

section

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

/-- The square with `0 : 0 ⟶ 0` on the left and `𝟙 X` on the right is a pullback square. -/
lemma zero_left (X : C) : is_pullback (0 : 0 ⟶ X) (0 : 0 ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
{ w := by simp,
  is_limit' :=
  ⟨{ lift := λ s, 0,
     fac' := λ s, by simpa using @pullback_cone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
       (by simpa using (pullback_cone.condition s).symm), }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pullback square. -/
lemma zero_top (X : C) : is_pullback (0 : 0 ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
(zero_left X).flip

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

lemma op (h : is_pullback fst snd f g) : is_pushout g.op f.op snd.op fst.op :=
is_pushout.of_is_colimit (is_colimit.of_iso_colimit
  (limits.pullback_cone.is_limit_equiv_is_colimit_op h.flip.cone h.flip.is_limit)
  h.to_comm_sq.flip.cone_op)

lemma unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  (h : is_pullback fst snd f g) : is_pushout g.unop f.unop snd.unop fst.unop :=
is_pushout.of_is_colimit (is_colimit.of_iso_colimit
  (limits.pullback_cone.is_limit_equiv_is_colimit_unop h.flip.cone h.flip.is_limit)
  h.to_comm_sq.flip.cone_unop)

end is_pullback

namespace is_pushout

variables {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

lemma flip (h : is_pushout f g inl inr) : is_pushout g f inr inl :=
of_is_colimit (@pushout_cocone.flip_is_colimit _ _ _ _ _ _ _ _ _ _ h.w.symm h.is_colimit)

section

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pushout square. -/
lemma zero_right (X : C) : is_pushout (0 : X ⟶ 0) (𝟙 X) (0 : 0 ⟶ 0) (0 : X ⟶ 0) :=
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
lemma zero_bot (X : C) : is_pushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : 0 ⟶ 0) :=
(zero_right X).flip

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

lemma op (h : is_pushout f g inl inr) : is_pullback inr.op inl.op g.op f.op :=
is_pullback.of_is_limit (is_limit.of_iso_limit
  (limits.pushout_cocone.is_colimit_equiv_is_limit_op h.flip.cocone h.flip.is_colimit)
  h.to_comm_sq.flip.cocone_op)

lemma unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  (h : is_pushout f g inl inr) : is_pullback inr.unop inl.unop g.unop f.unop :=
is_pullback.of_is_limit (is_limit.of_iso_limit
  (limits.pushout_cocone.is_colimit_equiv_is_limit_unop h.flip.cocone h.flip.is_colimit)
  h.to_comm_sq.flip.cocone_unop)

end is_pushout

namespace functor

variables {D : Type u₂} [category.{v₂} D]
variables (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

lemma map_is_pullback [preserves_limit (cospan h i) F] (s : is_pullback f g h i) :
  is_pullback (F.map f) (F.map g) (F.map h) (F.map i) :=
-- This is made slightly awkward because `C` and `D` have different universes,
-- and so the relevant `walking_cospan` diagrams live in different universes too!
begin
  refine is_pullback.of_is_limit' (F.map_comm_sq s.to_comm_sq)
    (is_limit.equiv_of_nat_iso_of_iso (cospan_comp_iso F h i) _ _ (walking_cospan.ext _ _ _)
      (is_limit_of_preserves F s.is_limit)),
  { refl, },
  { dsimp, simp, refl, },
  { dsimp, simp, refl, },
end

lemma map_is_pushout [preserves_colimit (span f g) F] (s : is_pushout f g h i) :
  is_pushout (F.map f) (F.map g) (F.map h) (F.map i) :=
begin
  refine is_pushout.of_is_colimit' (F.map_comm_sq s.to_comm_sq)
    (is_colimit.equiv_of_nat_iso_of_iso (span_comp_iso F f g) _ _ (walking_span.ext _ _ _)
      (is_colimit_of_preserves F s.is_colimit)),
  { refl, },
  { dsimp, simp, refl, },
  { dsimp, simp, refl, },
end

end functor

alias functor.map_is_pullback ← is_pullback.map
alias functor.map_is_pushout ← is_pushout.map

namespace comm_sq

variables {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}

@[ext, nolint has_inhabited_instance]
structure lift_struct (sq : comm_sq f i p g) :=
(l : B ⟶ X) (fac_left' : i ≫ l = f . obviously) (fac_right' : l ≫ p = g . obviously)

namespace lift_struct

restate_axiom fac_left'
restate_axiom fac_right'

@[simps]
def op {sq : comm_sq f i p g} (l : lift_struct sq) : lift_struct sq.op :=
{ l := l.l.op,
  fac_left' := by rw [← op_comp, l.fac_right],
  fac_right' := by rw [← op_comp, l.fac_left], }

@[simps]
def unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : comm_sq f i p g}
  (l : lift_struct sq) : lift_struct sq.unop :=
{ l := l.l.unop,
  fac_left' := by rw [← unop_comp, l.fac_right],
  fac_right' := by rw [← unop_comp, l.fac_left], }

@[simps]
def op_equiv (sq : comm_sq f i p g) : lift_struct sq ≃ lift_struct sq.op :=
{ to_fun := op,
  inv_fun := unop,
  left_inv := by tidy,
  right_inv := by tidy, }

def unop_equiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  (sq : comm_sq f i p g) : lift_struct sq ≃ lift_struct sq.unop :=
{ to_fun := unop,
  inv_fun := op,
  left_inv := by tidy,
  right_inv := by tidy, }

end lift_struct

variable (sq : comm_sq f i p g)

class has_lift : Prop := (exists_lift : nonempty sq.lift_struct)

namespace has_lift

lemma iff : has_lift sq ↔ nonempty sq.lift_struct :=
by { split, exacts [λ h, h.exists_lift, λ h, mk h], }

lemma iff_op : has_lift sq ↔ has_lift sq.op :=
begin
  rw [iff, iff],
  exact nonempty.congr (lift_struct.op_equiv sq).to_fun (lift_struct.op_equiv sq).inv_fun,
end

lemma iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} (sq : comm_sq f i p g) :
  has_lift sq ↔ has_lift sq.unop :=
begin
  rw [iff, iff],
  exact nonempty.congr (lift_struct.unop_equiv sq).to_fun (lift_struct.unop_equiv sq).inv_fun,
end

end has_lift

noncomputable
def lift [hsq : has_lift sq] : B ⟶ X :=
hsq.exists_lift.some.l

@[simp, reassoc]
lemma fac_left [hsq : has_lift sq] : i ≫ sq.lift = f :=
hsq.exists_lift.some.fac_left

@[simp, reassoc]
lemma fac_right [hsq : has_lift sq] : sq.lift ≫ p = g :=
hsq.exists_lift.some.fac_right

end comm_sq

end category_theory
