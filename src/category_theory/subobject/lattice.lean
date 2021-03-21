/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import category_theory.subobject.factor_thru

/-!
# The lattice of subobjects

We provide the `semilattice_inf_top (subobject X)` instance when `[has_pullback C]`,
and the `semilattice_sup (subobject X)` instance when `[has_images C] [has_binary_coproducts C]`.
-/

universes v₁ v₂ u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v₁} C] {X Y Z : C}
variables {D : Type u₂} [category.{v₂} D]

namespace category_theory

namespace mono_over

section has_top

instance {X : C} : has_top (mono_over X) :=
{ top := mk' (𝟙 _) }

instance {X : C} : inhabited (mono_over X) := ⟨⊤⟩

/-- The morphism to the top object in `mono_over X`. -/
def le_top (f : mono_over X) : f ⟶ ⊤ :=
hom_mk f.arrow (comp_id _)

@[simp] lemma top_left (X : C) : ((⊤ : mono_over X) : C) = X := rfl
@[simp] lemma top_arrow (X : C) : (⊤ : mono_over X).arrow = 𝟙 X := rfl

/-- `map f` sends `⊤ : mono_over X` to `⟨X, f⟩ : mono_over Y`. -/
def map_top (f : X ⟶ Y) [mono f] : (map f).obj ⊤ ≅ mk' f :=
iso_of_both_ways (hom_mk (𝟙 _) rfl) (hom_mk (𝟙 _) (by simp [id_comp f]))

section
variable [has_pullbacks C]

/-- The pullback of the top object in `mono_over Y`
is (isomorphic to) the top object in `mono_over X`. -/
def pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤ :=
iso_of_both_ways (le_top _) (hom_mk (pullback.lift f (𝟙 _) (by tidy)) (pullback.lift_snd _ _ _))

/-- There is a morphism from `⊤ : mono_over A` to the pullback of a monomorphism along itself;
as the category is thin this is an isomorphism. -/
def top_le_pullback_self {A B : C} (f : A ⟶ B) [mono f] :
  (⊤ : mono_over A) ⟶ (pullback f).obj (mk' f) :=
hom_mk _ (pullback.lift_snd _ _ rfl)

/-- The pullback of a monomorphism along itself is isomorphic to the top object. -/
def pullback_self {A B : C} (f : A ⟶ B) [mono f] :
  (pullback f).obj (mk' f) ≅ ⊤ :=
iso_of_both_ways (le_top _) (top_le_pullback_self _)

end

end has_top

section has_bot
variables [has_zero_morphisms C] [has_zero_object C]
local attribute [instance] has_zero_object.has_zero

instance {X : C} : has_bot (mono_over X) :=
{ bot := mk' (0 : 0 ⟶ X) }

@[simp] lemma bot_left (X : C) : ((⊥ : mono_over X) : C) = 0 := rfl
@[simp] lemma bot_arrow {X : C} : (⊥ : mono_over X).arrow = 0 :=
by ext

/-- The (unique) morphism from `⊥ : mono_over X` to any other `f : mono_over X`. -/
def bot_le {X : C} (f : mono_over X) : ⊥ ⟶ f :=
hom_mk 0 (by simp)

/-- `map f` sends `⊥ : mono_over X` to `⊥ : mono_over Y`. -/
def map_bot (f : X ⟶ Y) [mono f] : (map f).obj ⊥ ≅ ⊥ :=
iso_of_both_ways (hom_mk 0 (by simp)) (hom_mk (𝟙 _) (by simp [id_comp f]))

end has_bot

section inf
variables [has_pullbacks C]

/--
When `[has_pullbacks C]`, `mono_over A` has "intersections", functorial in both arguments.

As `mono_over A` is only a preorder, this doesn't satisfy the axioms of `semilattice_inf`,
but we reuse all the names from `semilattice_inf` because they will be used to construct
`semilattice_inf (subobject A)` shortly.
-/
@[simps]
def inf {A : C} : mono_over A ⥤ mono_over A ⥤ mono_over A :=
{ obj := λ f, pullback f.arrow ⋙ map f.arrow,
  map := λ f₁ f₂ k,
  { app := λ g,
    begin
      apply hom_mk _ _,
      apply pullback.lift pullback.fst (pullback.snd ≫ k.left) _,
      rw [pullback.condition, assoc, w k],
      dsimp,
      rw [pullback.lift_snd_assoc, assoc, w k],
    end } }.

/-- A morphism from the "infimum" of two objects in `mono_over A` to the first object. -/
def inf_le_left {A : C} (f g : mono_over A) :
  (inf.obj f).obj g ⟶ f :=
hom_mk _ rfl

/-- A morphism from the "infimum" of two objects in `mono_over A` to the second object. -/
def inf_le_right {A : C} (f g : mono_over A) :
  (inf.obj f).obj g ⟶ g :=
hom_mk _ pullback.condition

/-- A morphism version of the `le_inf` axiom. -/
def le_inf {A : C} (f g h : mono_over A) :
  (h ⟶ f) → (h ⟶ g) → (h ⟶ (inf.obj f).obj g) :=
begin
  intros k₁ k₂,
  refine hom_mk (pullback.lift k₂.left k₁.left _) _,
  rw [w k₁, w k₂],
  erw [pullback.lift_snd_assoc, w k₁],
end

end inf

section sup
variables [has_images C] [has_binary_coproducts C]

/-- When `[has_images C] [has_binary_coproducts C]`, `mono_over A` has a `sup` construction,
which is functorial in both arguments,
and which on `subobject A` will induce a `semilattice_sup`. -/
def sup  {A : C} : mono_over A ⥤ mono_over A ⥤ mono_over A :=
curry_obj ((forget A).prod (forget A) ⋙ uncurry.obj over.coprod ⋙ image)

/-- A morphism version of `le_sup_left`. -/
def le_sup_left {A : C} (f g : mono_over A) :
  f ⟶ (sup.obj f).obj g :=
begin
  refine hom_mk (coprod.inl ≫ factor_thru_image _) _,
  erw [category.assoc, image.fac, coprod.inl_desc],
  refl,
end

/-- A morphism version of `le_sup_right`. -/
def le_sup_right {A : C} (f g : mono_over A) :
  g ⟶ (sup.obj f).obj g :=
begin
  refine hom_mk (coprod.inr ≫ factor_thru_image _) _,
  erw [category.assoc, image.fac, coprod.inr_desc],
  refl,
end

/-- A morphism version of `sup_le`. -/
def sup_le {A : C} (f g h : mono_over A) :
  (f ⟶ h) → (g ⟶ h) → ((sup.obj f).obj g ⟶ h) :=
begin
  intros k₁ k₂,
  refine hom_mk _ _,
  apply image.lift ⟨_, h.arrow, coprod.desc k₁.left k₂.left, _⟩,
  { dsimp,
    ext1,
    { simp [w k₁] },
    { simp [w k₂] } },
  { apply image.lift_fac }
end

end sup

end mono_over

namespace subobject

section order_top

instance order_top {X : C} : order_top (subobject X) :=
{ top := quotient.mk' ⊤,
  le_top :=
  begin
    refine quotient.ind' (λ f, _),
    exact ⟨mono_over.le_top f⟩,
  end,
  ..subobject.partial_order X}

instance {X : C} : inhabited (subobject X) := ⟨⊤⟩

lemma top_eq_id {B : C} : (⊤ : subobject B) = subobject.mk (𝟙 B) := rfl

/-- The object underlying `⊤ : subobject B` is (up to isomorphism) `B`. -/
def top_coe_iso_self {B : C} : ((⊤ : subobject B) : C) ≅ B := underlying_iso _

@[simp]
lemma underlying_iso_id_eq_top_coe_iso_self {B : C} : underlying_iso (𝟙 B) = top_coe_iso_self :=
rfl

@[simp, reassoc]
lemma underlying_iso_inv_top_arrow {B : C} :
  top_coe_iso_self.inv ≫ (⊤ : subobject B).arrow = 𝟙 B :=
underlying_iso_arrow _

lemma map_top (f : X ⟶ Y) [mono f] : (map f).obj ⊤ = quotient.mk' (mono_over.mk' f) :=
quotient.sound' ⟨mono_over.map_top f⟩

lemma top_factors {A B : C} (f : A ⟶ B) : (⊤ : subobject B).factors f :=
⟨f, comp_id _⟩

section
variables [has_pullbacks C]

lemma pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤ :=
quotient.sound' ⟨mono_over.pullback_top f⟩

lemma pullback_self {A B : C} (f : A ⟶ B) [mono f] :
  (pullback f).obj (mk f) = ⊤ :=
quotient.sound' ⟨mono_over.pullback_self f⟩

end

end order_top

section order_bot
variables [has_zero_morphisms C] [has_zero_object C]
local attribute [instance] has_zero_object.has_zero

instance order_bot {X : C} : order_bot (subobject X) :=
{ bot := quotient.mk' ⊥,
  bot_le :=
  begin
    refine quotient.ind' (λ f, _),
    exact ⟨mono_over.bot_le f⟩,
  end,
  ..subobject.partial_order X}

lemma bot_eq_zero {B : C} : (⊥ : subobject B) = subobject.mk (0 : 0 ⟶ B) := rfl

/-- The object underlying `⊥ : subobject B` is (up to isomorphism) the zero object. -/
def bot_coe_iso_zero {B : C} : ((⊥ : subobject B) : C) ≅ 0 := underlying_iso _

@[simp] lemma bot_arrow {B : C} : (⊥ : subobject B).arrow = 0 :=
zero_of_source_iso_zero _ bot_coe_iso_zero

lemma map_bot (f : X ⟶ Y) [mono f] : (map f).obj ⊥ = ⊥ :=
quotient.sound' ⟨mono_over.map_bot f⟩

lemma bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : subobject B).factors f ↔ f = 0 :=
⟨by { rintro ⟨h, w⟩, simp at w, exact w.symm, }, by { rintro rfl, exact ⟨0, by simp⟩, }⟩

end order_bot

section functor
variable (C)

/-- Sending `X : C` to `subobject X` is a contravariant functor `Cᵒᵖ ⥤ Type`. -/
@[simps]
def functor [has_pullbacks C] : Cᵒᵖ ⥤ Type (max u₁ v₁) :=
{ obj := λ X, subobject X.unop,
  map := λ X Y f, (pullback f.unop).obj,
  map_id' := λ X, funext pullback_id,
  map_comp' := λ X Y Z f g, funext (pullback_comp _ _) }

end functor

section semilattice_inf_top
variables [has_pullbacks C]

/-- The functorial infimum on `mono_over A` descends to an infimum on `subobject A`. -/
def inf {A : C} : subobject A ⥤ subobject A ⥤ subobject A :=
thin_skeleton.map₂ mono_over.inf

lemma inf_le_left  {A : C} (f g : subobject A) :
  (inf.obj f).obj g ≤ f :=
quotient.induction_on₂' f g (λ a b, ⟨mono_over.inf_le_left _ _⟩)

lemma inf_le_right {A : C} (f g : subobject A) :
  (inf.obj f).obj g ≤ g :=
quotient.induction_on₂' f g (λ a b, ⟨mono_over.inf_le_right _ _⟩)

lemma le_inf {A : C} (h f g : subobject A) :
  h ≤ f → h ≤ g → h ≤ (inf.obj f).obj g :=
quotient.induction_on₃' h f g
begin
  rintros f g h ⟨k⟩ ⟨l⟩,
  exact ⟨mono_over.le_inf _ _ _ k l⟩,
end

instance {B : C} : semilattice_inf_top (subobject B) :=
{ inf := λ m n, (inf.obj m).obj n,
  inf_le_left := inf_le_left,
  inf_le_right := inf_le_right,
  le_inf := le_inf,
  ..subobject.order_top }

lemma factors_left_of_inf_factors {A B : C} {X Y : subobject B} {f : A ⟶ B}
  (h : (X ⊓ Y).factors f) : X.factors f :=
factors_of_le _ (inf_le_left _ _) h

lemma factors_right_of_inf_factors {A B : C} {X Y : subobject B} {f : A ⟶ B}
  (h : (X ⊓ Y).factors f) : Y.factors f :=
factors_of_le _ (inf_le_right _ _) h

@[simp]
lemma inf_factors {A B : C} {X Y : subobject B} (f : A ⟶ B) :
  (X ⊓ Y).factors f ↔ X.factors f ∧ Y.factors f :=
⟨λ h, ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩,
  begin
    revert X Y,
    refine quotient.ind₂' _,
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩,
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩,
  end⟩

lemma inf_arrow_factors_left {B : C} (X Y : subobject B) : X.factors (X ⊓ Y).arrow :=
(factors_iff _ _).mpr ⟨underlying.map (hom_of_le (inf_le_left X Y)), by simp⟩

lemma inf_arrow_factors_right {B : C} (X Y : subobject B) : Y.factors (X ⊓ Y).arrow :=
(factors_iff _ _).mpr ⟨underlying.map (hom_of_le (inf_le_right X Y)), by simp⟩

@[simp]
lemma finset_inf_factors {I : Type*} {A B : C} {s : finset I} {P : I → subobject B}
  (f : A ⟶ B) :
  (s.inf P).factors f ↔ ∀ i ∈ s, (P i).factors f :=
begin
  classical,
  apply finset.induction_on s,
  { simp [top_factors] },
  { intros i s nm ih, simp [ih] },
end

-- `i` is explicit here because often we'd like to defer a proof of `m`
lemma finset_inf_arrow_factors {I : Type*} {B : C} (s : finset I) (P : I → subobject B)
  (i : I) (m : i ∈ s) : (P i).factors (s.inf P).arrow :=
begin
  revert i m,
  classical,
  apply finset.induction_on s,
  { rintro _ ⟨⟩, },
  { intros i s nm ih j m,
    rw [finset.inf_insert],
    simp only [finset.mem_insert] at m, rcases m with (rfl|m),
    { rw ←factor_thru_arrow _ _ (inf_arrow_factors_left _ _),
      exact factors_comp_arrow _, },
    { rw ←factor_thru_arrow _ _ (inf_arrow_factors_right _ _),
      apply factors_of_factors_right,
      exact ih _ m, } },
end

lemma inf_eq_map_pullback' {A : C} (f₁ : mono_over A) (f₂ : subobject A) :
  (subobject.inf.obj (quotient.mk' f₁)).obj f₂ =
    (subobject.map f₁.arrow).obj ((subobject.pullback f₁.arrow).obj f₂) :=
begin
  apply quotient.induction_on' f₂,
  intro f₂,
  refl,
end

lemma inf_eq_map_pullback {A : C} (f₁ : mono_over A) (f₂ : subobject A) :
  (quotient.mk' f₁ ⊓ f₂ : subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) :=
inf_eq_map_pullback' f₁ f₂

lemma prod_eq_inf {A : C} {f₁ f₂ : subobject A} [has_binary_product f₁ f₂] :
  (f₁ ⨯ f₂) = f₁ ⊓ f₂ :=
le_antisymm
  (_root_.le_inf
    (le_of_hom limits.prod.fst)
    (le_of_hom limits.prod.snd))
  (le_of_hom
    (prod.lift
      (hom_of_le _root_.inf_le_left)
      (hom_of_le _root_.inf_le_right)))

lemma inf_def {B : C} (m m' : subobject B) :
  m ⊓ m' = (inf.obj m).obj m' := rfl

/-- `⊓` commutes with pullback. -/
lemma inf_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) :
  (pullback g).obj (f₁ ⊓ f₂) = (pullback g).obj f₁ ⊓ (pullback g).obj f₂ :=
begin
  revert f₁,
  apply quotient.ind',
  intro f₁,
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp,
       ← map_pullback pullback.condition (pullback_is_pullback f₁.arrow g),
       ← pullback_comp, pullback.condition],
  refl,
end

/-- `⊓` commutes with map. -/
lemma inf_map {X Y : C} (g : Y ⟶ X) [mono g] (f₁ f₂) :
  (map g).obj (f₁ ⊓ f₂) = (map g).obj f₁ ⊓ (map g).obj f₂ :=
begin
  revert f₁,
  apply quotient.ind',
  intro f₁,
  erw [inf_def, inf_def, inf_eq_map_pullback',
       inf_eq_map_pullback', ← map_comp],
  dsimp,
  rw [pullback_comp, pullback_map_self],
end

end semilattice_inf_top

section semilattice_sup
variables [has_images C] [has_binary_coproducts C]

/-- The functorial supremum on `mono_over A` descends to an supremum on `subobject A`. -/
def sup {A : C} : subobject A ⥤ subobject A ⥤ subobject A :=
thin_skeleton.map₂ mono_over.sup

instance {B : C} : semilattice_sup (subobject B) :=
{ sup := λ m n, (sup.obj m).obj n,
  le_sup_left := λ m n, quotient.induction_on₂' m n (λ a b, ⟨mono_over.le_sup_left _ _⟩),
  le_sup_right := λ m n, quotient.induction_on₂' m n (λ a b, ⟨mono_over.le_sup_right _ _⟩),
  sup_le := λ m n k, quotient.induction_on₃' m n k (λ a b c ⟨i⟩ ⟨j⟩, ⟨mono_over.sup_le _ _ _ i j⟩),
  ..subobject.partial_order B }

lemma sup_factors_of_factors_left {A B : C} {X Y : subobject B} {f : A ⟶ B} (P : X.factors f) :
  (X ⊔ Y).factors f :=
factors_of_le f le_sup_left P

lemma sup_factors_of_factors_right {A B : C} {X Y : subobject B} {f : A ⟶ B} (P : Y.factors f) :
  (X ⊔ Y).factors f :=
factors_of_le f le_sup_right P

/-!
Unfortunately, there are two different ways we may obtain a `semilattice_sup_bot (subobject B)`,
either as here, by assuming `[has_zero_morphisms C] [has_zero_object C]`,
or if `C` is cartesian closed.

These will be definitionally different, and at the very least we will need two different versions
of `finset_sup_factors`. So far I don't see how to handle this through generalization.
-/
section
variables [has_zero_morphisms C] [has_zero_object C]

instance {B : C} : semilattice_sup_bot (subobject B) :=
{ ..subobject.order_bot,
  ..subobject.semilattice_sup }

lemma finset_sup_factors {I : Type*} {A B : C} {s : finset I} {P : I → subobject B}
  {f : A ⟶ B} (h : ∃ i ∈ s, (P i).factors f) :
  (s.sup P).factors f :=
begin
  classical,
  revert h,
  apply finset.induction_on s,
  { rintro ⟨_, ⟨⟨⟩, _⟩⟩, },
  { rintros i s nm ih ⟨j, ⟨m, h⟩⟩,
    simp only [finset.sup_insert],
    simp at m, rcases m with (rfl|m),
    { exact sup_factors_of_factors_left h, },
    { exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩), }, },
end

end

end semilattice_sup

section lattice
variables [has_pullbacks C] [has_images C] [has_binary_coproducts C]

instance {B : C} : lattice (subobject B) :=
{ ..subobject.semilattice_inf_top,
  ..subobject.semilattice_sup }

variables [has_zero_morphisms C] [has_zero_object C]

instance {B : C} : bounded_lattice (subobject B) :=
{ ..subobject.semilattice_inf_top,
  ..subobject.semilattice_sup_bot }

end lattice

end subobject

end category_theory
