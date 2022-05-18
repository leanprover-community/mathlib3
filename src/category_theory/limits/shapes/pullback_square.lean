/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.zero_morphisms

/-!
# Pullback and pushout squares

We provide another API for pullbacks and pushouts.

`pullback_square fst snd f g` is the proposition that
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square.

(And similarly for `pushout_square`.)

We provide the glue to go back and forth to the usual `is_limit` API for pullbacks, and prove
`pullback_square (pullback.fst : pullback f g ⟶ X) (pullback.snd : pullback f g ⟶ Y) f g`
for the usual `pullback f g` provided by the `has_limit` API.

We don't attempt to restate everything we know about pullbacks in this language,
but do restate the pasting lemmas.

## Future work
Bicartesian squares, and
show that the pullback and pushout squares for a biproduct are bicartesian.
-/

open category_theory

namespace category_theory.limits

variables {C : Type*} [category C]

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
structure pullback_square
  {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : Prop :=
mk' ::
(w : fst ≫ f = snd ≫ g)
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
structure pushout_square
  {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) : Prop :=
mk' ::
(w : f ≫ inl = g ≫ inr)
(is_colimit' : nonempty (is_colimit (pushout_cocone.mk _ _ w)))

/-!
We begin by providing some glue between `pullback_square` and the `is_limit` and `has_limit` APIs.
(And similarly for `pushout_square`.)
-/

namespace pullback_square

variables {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/--
The `pullback_cone f g` implicit in the statement that we have a `pullback_square fst snd f g`.
-/
def cone (h : pullback_square fst snd f g) : pullback_cone f g := pullback_cone.mk _ _ h.w

/--
The cone obtained from `pullback_square fst snd f g` is a limit cone.
-/
noncomputable def is_limit (h : pullback_square fst snd f g) : is_limit h.cone :=
h.is_limit'.some

/-- If `c` is a limiting pullback cone, then we have a `pullback_square c.fst c.snd f g`. -/
lemma of_is_limit {c : pullback_cone f g} (h : limits.is_limit c) :
  pullback_square c.fst c.snd f g :=
{ w := c.condition,
  is_limit' := ⟨is_limit.of_iso_limit h
    (limits.pullback_cone.ext (iso.refl _) (by tidy) (by tidy))⟩, }

/-- The pullback provided by `has_pullback f g` fits into a `pullback_square`. -/
lemma of_has_pullback (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] :
  pullback_square (pullback.fst : pullback f g ⟶ X) (pullback.snd : pullback f g ⟶ Y) f g :=
of_is_limit (limit.is_limit (cospan f g))

end pullback_square

namespace pushout_square

variables {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/--
The `pushout_cocone f g` implicit in the statement that we have a `pushout_square f g inl inr`.
-/
def cocone (h : pushout_square f g inl inr) : pushout_cocone f g := pushout_cocone.mk _ _ h.w

/--
The cocone obtained from `pushout_square f g inl inr` is a colimit cocone.
-/
noncomputable def is_colimit (h : pushout_square f g inl inr) : is_colimit h.cocone :=
h.is_colimit'.some

/-- If `c` is a colimiting pushout cocone, then we have a `pushout_square f g c.inl c.inr`. -/
lemma of_is_colimit {c : pushout_cocone f g} (h : limits.is_colimit c) :
  pushout_square f g c.inl c.inr :=
{ w := c.condition,
  is_colimit' := ⟨is_colimit.of_iso_colimit h
    (limits.pushout_cocone.ext (iso.refl _) (by tidy) (by tidy))⟩, }

/-- The pushout provided by `has_pushout f g` fits into a `pushout_square`. -/
lemma of_has_pushout (f : Z ⟶ X) (g : Z ⟶ Y) [has_pushout f g] :
  pushout_square f g (pushout.inl : X ⟶ pushout f g) (pushout.inr : Y ⟶ pushout f g) :=
of_is_colimit (colimit.is_colimit (span f g))

end pushout_square

namespace pullback_square

variables {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma flip (h : pullback_square fst snd f g) : pullback_square snd fst g f :=
of_is_limit (@pullback_cone.flip_is_limit _ _ _ _ _ _ _ _ _ _ h.w.symm h.is_limit)

section

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

/-- The square with `0 : 0 ⟶ 0` on the left and `𝟙 X` on the right is a pullback square. -/
lemma zero_left (X : C) : pullback_square (0 : 0 ⟶ X) (0 : 0 ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
{ w := by simp,
  is_limit' :=
  ⟨{ lift := λ s, 0,
     fac' := λ s, by simpa using @pullback_cone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
       (by simpa using (pullback_cone.condition s).symm), }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pullback square. -/
lemma zero_top (X : C) : pullback_square (0 : 0 ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
(zero_left X).flip

end

/-- Paste two pullback squares "vertically" to obtain another pullback square. -/
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
lemma paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : pullback_square h₁₁ v₁₁ v₁₂ h₂₁) (t : pullback_square h₂₁ v₂₁ v₂₂ h₃₁) :
  pullback_square h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
(of_is_limit
  (big_square_is_pullback _ _ _ _ _ _ _ s.w t.w t.is_limit s.is_limit))

/-- Paste two pullback squares "horizontally" to obtain another pullback square. -/
lemma paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : pullback_square h₁₁ v₁₁ v₁₂ h₂₁) (t : pullback_square h₁₂ v₁₂ v₁₃ h₂₂) :
  pullback_square (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
(paste_vert s.flip t.flip).flip

/-- Given a pullback square assembled from a commuting square on the top and
a pullback square on the bottom, the top square is a pullback square. -/
lemma of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : pullback_square h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
  (t : pullback_square h₂₁ v₂₁ v₂₂ h₃₁) :
  pullback_square h₁₁ v₁₁ v₁₂ h₂₁ :=
of_is_limit (left_square_is_pullback _ _ _ _ _ _ _ p _ t.is_limit s.is_limit)

/-- Given a pullback square assembled from a commuting square on the left and
a pullback square on the right, the left square is a pullback square. -/
lemma of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : pullback_square (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁)
  (t : pullback_square h₁₂ v₁₂ v₁₃ h₂₂) :
  pullback_square h₁₁ v₁₁ v₁₂ h₂₁ :=
(of_bot s.flip p.symm t.flip).flip

end pullback_square

namespace pushout_square

variables {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

lemma flip (h : pushout_square f g inl inr) : pushout_square g f inr inl :=
of_is_colimit (@pushout_cocone.flip_is_colimit _ _ _ _ _ _ _ _ _ _ h.w.symm h.is_colimit)

section

variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pushout square. -/
lemma zero_right (X : C) : pushout_square (0 : X ⟶ 0) (𝟙 X) (0 : 0 ⟶ 0) (0 : X ⟶ 0) :=
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
lemma zero_bot (X : C) : pushout_square (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : 0 ⟶ 0) :=
(zero_right X).flip

end

/-- Paste two pushout squares "vertically" to obtain another pushout square. -/
-- Objects here are arranged in a 3x2 grid, and indexed by their xy coordinates.
-- Morphisms are named `hᵢⱼ` for a horizontal morphism starting at `(i,j)`,
-- and `vᵢⱼ` for a vertical morphism starting at `(i,j)`.
lemma paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : pushout_square h₁₁ v₁₁ v₁₂ h₂₁) (t : pushout_square h₂₁ v₂₁ v₂₂ h₃₁) :
  pushout_square h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
(of_is_colimit
  (big_square_is_pushout _ _ _ _ _ _ _ s.w t.w t.is_colimit s.is_colimit))

/-- Paste two pushout squares "horizontally" to obtain another pushout square. -/
lemma paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : pushout_square h₁₁ v₁₁ v₁₂ h₂₁) (t : pushout_square h₁₂ v₁₂ v₁₃ h₂₂) :
  pushout_square (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) :=
(paste_vert s.flip t.flip).flip

/-- Given a pushout square assembled from a pushout square on the top and
a commuting square on the bottom, the bottom square is a pushout square. -/
lemma of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂}
  (s : pushout_square h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁) (p : h₂₁ ≫ v₂₂ = v₂₁ ≫ h₃₁)
  (t : pushout_square h₁₁ v₁₁ v₁₂ h₂₁) :
  pushout_square h₂₁ v₂₁ v₂₂ h₃₁ :=
of_is_colimit (right_square_is_pushout _ _ _ _ _ _ _ _ p t.is_colimit s.is_colimit)

/-- Given a pushout square assembled from a pushout square on the left and
a commuting square on the right, the right square is a pushout square. -/
lemma of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
  {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
  {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
  (s : pushout_square (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂)) (p : h₁₂ ≫ v₁₃ = v₁₂ ≫ h₂₂)
  (t : pushout_square h₁₁ v₁₁ v₁₂ h₂₁) :
  pushout_square h₁₂ v₁₂ v₁₃ h₂₂ :=
(of_bot s.flip p.symm t.flip).flip

end pushout_square


end category_theory.limits
