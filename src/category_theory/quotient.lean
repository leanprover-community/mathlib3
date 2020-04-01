import category_theory.functor
import category_theory.eq_to_hom

/-
  This file defines quotient categories. Given a category and an arbitrary family of relations
  on its homsets, thought of as identifying some homs, we construct a new category on an
  identical type of objects, where related homs are identified.

    Note that we do *not* assume that our relation behaves well under composition, or that it is
  an equivalence relation.
-/

universes v v₁ u u₁

namespace category_theory

variables
  {C : Type u} [category.{v} C]
  (r : Π (a b : C), (a ⟶ b) → (a ⟶ b) → Prop)
include r

/-- The type of objects in the quotient category --/
structure quotient := (to_C : C)
def of_C (a : C) : quotient r := ⟨r, a⟩

namespace quotient

/- Generates the closure of a family of relations wrt composition from left and right
  If m₁ and m₂ are identified, then fm₁g and fm₂g should also be identified. -/
inductive ccl {s t : C} : (s ⟶ t) → (s ⟶ t) → Prop
| intro {a b} (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r _ _ m₁ m₂) :
  ccl (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)

lemma comp_left {a b c : C} (f : a ⟶ b) : Π (g₁ g₂ : b ⟶ c) (h : ccl r g₁ g₂),
  ccl r (f ≫ g₁) (f ≫ g₂)
| _ _ ⟨x, m₁, m₂, y, h⟩ := by simpa using ccl.intro (f ≫ x) m₁ m₂ y h

lemma comp_right {a b c : C} (g : b ⟶ c) : Π (f₁ f₂ : a ⟶ b) (h : ccl r f₁ f₂),
  ccl r (f₁ ≫ g) (f₂ ≫ g)
| _ _ ⟨x, m₁, m₂, y, h⟩ := by simpa using ccl.intro x m₁ m₂ (y ≫ g) h

def hom (s t : quotient r) := quot $ @ccl C _ r s.to_C t.to_C

-- We get well-defined composition on the quotient because of comp_left and comp_right
def comp {a b c : quotient r} : hom r a b → hom r b c → hom r a c :=
λ hf hg, quot.lift_on hf ( λ f, quot.lift_on hg (λ g, quot.mk _ (f ≫ g))
  (λ g₁ g₂ h, quot.sound $ comp_left r f g₁ g₂ h) )
  (λ f₁ f₂ h, quot.induction_on hg $ λ g, quot.sound $ comp_right r g f₁ f₂ h)

@[simp]
lemma hcomp_mk {a b c : quotient r} (f : a.to_C ⟶ b.to_C) (g : b.to_C ⟶ c.to_C) :
  comp r (quot.mk _ f) (quot.mk _ g) = quot.mk _ (f ≫ g) := rfl

instance category : category (quotient r) :=
{ hom := hom r,
  id := λ a, quot.mk _ (𝟙 a.to_C),
  comp := @comp _ _ r }

-- The functor from a category to its quotient
@[simps]
def functor : C ⥤ quotient r :=
{ obj := of_C r,
  map := λ _ _ f, quot.mk _ f }

-- We haven't made our category any bigger
protected lemma induction {P : Π {a b : quotient r}, (a ⟶ b) → Prop}
  (h : ∀ {x y : C} (f : x ⟶ y), P ((functor r).map f)) :
  ∀ {a b : quotient r} (f : a ⟶ b), P f :=
begin rintros ⟨x⟩ ⟨y⟩ ⟨f⟩, exact h f, end

-- Related homs are identical in the quotient category
protected lemma sound {a b : C} (f₁ f₂ : a ⟶ b) (h : r a b f₁ f₂) :
  quot.mk (ccl r) f₁ = quot.mk _ f₂ :=
by simpa using quot.sound (@ccl.intro C _ r a b a b (𝟙 a) f₁ f₂ (𝟙 b) h)

variables {r} {D : Type*} [category D]
  (F : C ⥤ D)
  (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r _ _ f₁ f₂ → F.map f₁ = F.map f₂)
include H

-- The lift to the quotient category of a functor that maps related homs to identical homs
@[simps]
def lift : quotient r ⥤ D :=
{ obj := λ a, F.obj a.to_C,
  map := λ a b hf, quot.lift_on hf (λ f, F.map f)
    begin
      rintros _ _ ⟨x, y, f, m₁, m₂, g, h⟩,
      unfold,
      repeat { rw functor.map_comp },
      rw H x y m₁ m₂ h,
    end,
  map_id' := λ a, F.map_id' a.to_C,
  map_comp' := begin rintros a b c ⟨f⟩ ⟨g⟩, exact F.map_comp' f g end }

@[simp]
lemma lift.is_lift : (functor r) ⋙ lift F H = F :=
category_theory.functor.ext (λ a, rfl) (by simp)

end quotient

end category_theory
