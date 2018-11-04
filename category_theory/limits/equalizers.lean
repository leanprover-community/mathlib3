import category_theory.limits.limits
import category_theory.limits.pullbacks

open category_theory

namespace category_theory.limits

local attribute [tidy] tactic.case_bash

universes u v w

inductive walking_pair : Type v
| zero | one

open walking_pair

inductive walking_pair_hom : walking_pair → walking_pair → Type v
| inl : walking_pair_hom zero one
| inr : walking_pair_hom zero one
| id : Π X : walking_pair.{v}, walking_pair_hom X X

open walking_pair_hom

instance walking_pair_category : small_category walking_pair :=
{ hom := walking_pair_hom,
  id := walking_pair_hom.id,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | _, _ ,_, (id _), h := h
  | _, _, _, inl, (id one) := inl
  | _, _, _, inr, (id one) := inr
  end }

lemma walking_pair_hom_id (X : walking_pair.{v}) : walking_pair_hom.id X = 𝟙 X := rfl

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables {X Y : C}

def pair (f g : X ⟶ Y) : walking_pair.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | one := Y
  end,
  map' := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, inl := f
  | _, _, inr := g
  end }.

@[simp] lemma pair_map_inl (f g : X ⟶ Y) : (pair f g).map inl = f := rfl
@[simp] lemma pair_map_inr (f g : X ⟶ Y) : (pair f g).map inr = g := rfl

@[simp] lemma pair_functor_obj {F : walking_pair.{v} ⥤ C} (j : walking_pair.{v}) :
  (pair (F.map inl) (F.map inr)) j = F j :=
begin
  cases j; refl
end

def fork (f g : X ⟶ Y) := cone (pair f g)

variables {f g : X ⟶ Y}

attribute [simp] walking_pair_hom_id

def fork.of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : fork f g :=
{ X := P,
  π :=
  { app := λ X, begin cases X, exact ι, exact ι ≫ f, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      exact w
    end }}

def fork.ι (t : fork f g) := t.π zero

def is_equalizer (t : fork f g) := is_limit t

lemma is_equalizer.mono {t : fork f g} (h : is_equalizer t) : mono t.ι :=
⟨λ W (e₁ e₂ : W ⟶ t.X) H, begin
   unfold fork.ι at H,
   apply h.hom_eq,
   rintro (_|_),
   { exact H },
   { have : t.π one = t.π zero ≫ f, from (t.w inl).symm,
     rw [this, ←category.assoc, ←category.assoc, H] }
 end⟩

variables {t : fork f g}

instance is_equalizer_subsingleton : subsingleton (is_equalizer t) := by dsimp [is_equalizer]; apply_instance

class has_equalizer {X Y : C} (f g : X ⟶ Y) :=
(fork : fork.{u v} f g)
(is_equalizer : is_equalizer fork . obviously)

variable (C)

class has_equalizers :=
(fork : Π {X Y : C} (f g : X ⟶ Y), fork.{u v} f g)
(is_equalizer : Π {X Y : C} (f g : X ⟶ Y), is_equalizer (fork f g) . obviously)

variable {C}

instance has_equalizer_of_has_equalizers [has_equalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) :
  has_equalizer.{u v} f g :=
{ fork := has_equalizers.fork f g,
  is_equalizer := has_equalizers.is_equalizer C f g }

-- Special cases of this may be marked with [instance] as desired.
def has_equalizers_of_has_limits [limits.has_limits.{u v} C] : has_equalizers.{u v} C :=
{ fork := λ X Y f g, limit.cone (pair f g),
  is_equalizer := λ X Y f g, limit.universal_property (pair f g) }

@[simp] def cone.of_fork {F : walking_pair.{v} ⥤ C} (t : fork (F.map inl) (F.map inr)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w inl, refl,
      erw ← t.w inr, refl,
    end } }.

@[simp] def fork.of_cone {F : walking_pair.{v} ⥤ C} (t : cone F) : fork (F.map inl) (F.map inr) :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy) } }

instance has_limits_of_shape_of_has_equalizers [has_equalizers.{u v} C] :
  limits.has_limits_of_shape.{u v} walking_pair.{v} C :=
begin
  exact
  { cone := λ F, cone.of_fork (has_equalizers.fork (F.map inl) (F.map inr)),
    is_limit := λ F, let is_equalizer := has_equalizer.is_equalizer (F.map inl) (F.map inr) in
    { lift := λ s, is_equalizer.lift (fork.of_cone s),
      fac' := λ s j,
      begin
        convert is_equalizer.fac (fork.of_cone s) j; cases j,
        tidy,
      end,
      uniq' := λ s m w, is_equalizer.uniq (fork.of_cone s) m
        (λ j, begin convert w j; cases j, tidy end) } }
end

variable {C}

section
variables (f g)

def equalizer.fork [has_equalizer f g]: fork f g := has_equalizer.fork.{u v} f g
def equalizer [has_equalizer f g] := (equalizer.fork f g).X
def equalizer.ι [has_equalizer f g] : equalizer f g ⟶ X := (equalizer.fork f g).π.app zero
@[simp] lemma equalizer.w [has_equalizer f g] : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
begin
  erw ((equalizer.fork f g).w inl),
  erw ((equalizer.fork f g).w inr)
end
def equalizer.universal_property [has_equalizer f g] : is_equalizer (equalizer.fork f g) :=
has_equalizer.is_equalizer f g

def equalizer.lift [has_equalizer f g] {P : C} (h : P ⟶ X) (w : h ≫ f = h ≫ g) : P ⟶ equalizer f g :=
(equalizer.universal_property f g).lift (fork.of_ι h w)

@[simp] lemma equalizer.lift_ι [has_equalizer f g] {P : C} (h : P ⟶ X) (w : h ≫ f = h ≫ g) : equalizer.lift f g h w ≫ equalizer.ι f g = h :=
is_limit.fac _ _ _

instance [has_equalizer f g] : mono (equalizer.ι f g) := (has_equalizer.is_equalizer f g).mono

@[extensionality] lemma equalizer.hom_ext [has_equalizer f g] {P : C}
  {h k : P ⟶ equalizer f g}
  (w : h ≫ equalizer.ι f g = k ≫ equalizer.ι f g) : h = k := mono.right_cancellation h k w

end

end category_theory.limits
