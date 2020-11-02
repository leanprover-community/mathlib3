/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.types
import category_theory.limits.shapes.products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal

/-!
# Special shapes for limits in `Type`.

The general shape (co)limits defined in `category_theory.limits.types`
are intended for use through the limits API,
and the actual implementation should mostly be considered "sealed".

In this file, we provide definitions of the "standard" special shapes of limits in `Type`,
giving the expected definitional implementation:
* the terminal object is `punit`
* the binary product of `X` and `Y` is `X × Y`
* the product of a family `f : J → Type` is `Π j, f j`.

Because these are not intended for use with the `has_limit` API,
we instead construct terms of `limit_data`.

As an example, when setting up the monoidal category structure on `Type`
we use the `types_has_terminal` and `types_has_binary_products` instances.
-/

universes u

open category_theory
open category_theory.limits

namespace category_theory.limits.types

/-- A restatement of `types.lift_π_apply` that uses `pi.π` and `pi.lift`. -/
@[simp]
lemma pi_lift_π_apply {β : Type u} (f : β → Type u) {P : Type u} (s : Π b, P ⟶ f b) (b : β) (x : P) :
  (pi.π f b : (∏ f) → f b) (@pi.lift β _ _ f _ P s x) = s b x :=
congr_fun (limit.lift_π (fan.mk P s) b) x

/-- A restatement of `types.map_π_apply` that uses `pi.π` and `pi.map`. -/
@[simp]
lemma pi_map_π_apply {β : Type u} {f g : β → Type u} (α : Π j, f j ⟶ g j) (b : β) (x) :
  (pi.π g b : (∏ g) → g b) (pi.map α x) = α b ((pi.π f b : (∏ f) → f b) x) :=
limit.map_π_apply _ _ _

/-- The category of types has `punit` as a terminal object. -/
def terminal_limit_cone : limits.limit_cone (functor.empty (Type u)) :=
{ cone :=
  { X := punit,
    π := by tidy, },
  is_limit := by tidy, }

/-- The category of types has `pempty` as an initial object. -/
def initial_limit_cone : limits.colimit_cocone (functor.empty (Type u)) :=
{ cocone :=
  { X := pempty,
    ι := by tidy, },
  is_colimit := by tidy, }

open category_theory.limits.walking_pair

local attribute [tidy] tactic.case_bash

/--
The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
def binary_product_limit_cone (X Y : Type u) : limits.limit_cone (pair X Y) :=
{ cone :=
  { X := X × Y,
    π :=
    { app := by { rintro ⟨_|_⟩, exact prod.fst, exact prod.snd, } }, },
  is_limit :=
  { lift := λ s x, (s.π.app left x, s.π.app right x),
    uniq' := λ s m w,
    begin
      ext,
      exact congr_fun (w left) x,
      exact congr_fun (w right) x,
    end }, }

/--
The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binary_coproduct_limit_cone (X Y : Type u) : limits.colimit_cocone (pair X Y) :=
{ cocone :=
  { X := X ⊕ Y,
    ι :=
    { app := by { rintro ⟨_|_⟩, exact sum.inl, exact sum.inr, } }, },
  is_colimit :=
  { desc := λ s x, sum.elim (s.ι.app left) (s.ι.app right) x,
    uniq' := λ s m w,
    begin
      ext (x|x),
      exact (congr_fun (w left) x : _),
      exact (congr_fun (w right) x : _),
    end }, }

/--
The category of types has `Π j, f j` as the product of a type family `f : J → Type`.
-/
def product_limit_cone {J : Type u} (F : J → Type u) : limits.limit_cone (discrete.functor F) :=
{ cone :=
  { X := Π j, F j,
    π :=
    { app := λ j f, f j }, },
  is_limit :=
  { lift := λ s x j, s.π.app j x,
    uniq' := λ s m w,
    begin
      ext x j,
      have := congr_fun (w j) x,
      exact this,
    end }, }

/--
The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/
def coproduct_limit_cone {J : Type u} (F : J → Type u) : limits.colimit_cocone (discrete.functor F) :=
{ cocone :=
  { X := Σ j, F j,
    ι :=
    { app := λ j x, ⟨j, x⟩ }, },
  is_colimit :=
  { desc := λ s x, s.ι.app x.1 x.2,
    uniq' := λ s m w,
    begin
      ext ⟨j, x⟩,
      have := congr_fun (w j) x,
      exact this,
    end }, }

section fork
variables {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/--
Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
noncomputable def type_equalizer_of_unique (t : ∀ (y : Y), g y = h y → ∃! (x : X), f x = y) :
  is_limit (fork.of_ι _ w) :=
fork.is_limit.mk' _ $ λ s,
begin
  refine ⟨λ i, _, _, _⟩,
  { apply classical.some (t (s.ι i) _),
    apply congr_fun s.condition i },
  { ext i,
    apply (classical.some_spec (t (s.ι i) _)).1 },
  { intros m hm,
    ext i,
    apply (classical.some_spec (t (s.ι i) _)).2,
    apply congr_fun hm i },
end

/-- The converse of `type_equalizer_of_unique`. -/
lemma unique_of_type_equalizer (t : is_limit (fork.of_ι _ w)) :
  (∀ (y : Y), g y = h y → ∃! (x : X), f x = y) :=
begin
  intros y hy,
  let y' : punit ⟶ Y := λ _, y,
  have hy' : y' ≫ g = y' ≫ h := funext (λ _, hy),
  refine ⟨(fork.is_limit.lift' t _ hy').1 ⟨⟩, congr_fun (fork.is_limit.lift' t y' _).2 ⟨⟩, _⟩,
  intros x' hx',
  suffices : (λ (_ : punit), x') = (fork.is_limit.lift' t y' hy').1,
    rw ← this,
  apply fork.is_limit.hom_ext t,
  ext ⟨⟩,
  apply hx'.trans (congr_fun (fork.is_limit.lift' t _ hy').2 ⟨⟩).symm,
end

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
def equalizer_limit : limits.limit_cone (parallel_pair g h) :=
{ cone := fork.of_ι (subtype.val : {x : Y // g x = h x} → Y) (funext subtype.prop),
  is_limit := fork.is_limit.mk' _ $ λ s,
    ⟨λ i, ⟨s.ι i, by apply congr_fun s.condition i⟩,
     rfl,
     λ m hm, funext $ λ x, subtype.ext (congr_fun hm x)⟩ }

end fork

end category_theory.limits.types
