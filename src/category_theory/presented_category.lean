import combinatorics.quiver.path
import category_theory.path_category

universes v u

open quiver
namespace category_theory

class presented_category (C : Type u) extends quiver.{v+1} C :=
(rel : Π {X Y : C}, path X Y → path X Y → Prop)

namespace presented_category

inductive equiv_rel (C : Type u) [presented_category.{v} C] : Π {X Y : C}, path X Y → path X Y → Prop
| of {X Y : C} {p q : path X Y} (r : rel p q) : equiv_rel p q
| refl {X Y : C} (p : path X Y) : equiv_rel p p
| trans {X Y : C} {p q r : path X Y} (f : equiv_rel p q) (g : equiv_rel q r) : equiv_rel p r
| symm {X Y : C} {p q : path X Y} (f : equiv_rel p q) : equiv_rel q p
| comp_left {X Y Z : C} (p : path X Y) {q r : path Y Z} (f : equiv_rel q r) :
  equiv_rel (p.comp q) (p.comp r)
| comp_right {X Y Z : C} {p q : path X Y} (r : path Y Z) (f : equiv_rel p q) :
  equiv_rel (p.comp r) (q.comp r)

instance setoid {C : Type u} [presented_category.{v} C] (X Y : C) : setoid (path X Y) :=
{ r := equiv_rel C,
  iseqv := sorry, }

def of (C : Type*) [presented_category C] : Type* := C

def unwrap {C : Type*} [presented_category C] (X : of C) : C := X

instance (C : Type u) [presented_category.{v} C] : category.{max v u} (of C) :=
{ hom := λ X Y, quotient (presented_category.setoid (unwrap X) (unwrap Y)),
  id := λ X, quotient.mk path.nil,
  comp := λ X Y Z f g, quotient.lift₂ (λ p q, quotient.mk (path.comp p q))
    (begin
      intros p q p' q' hp hq,
      exact quotient.sound (setoid.trans (equiv_rel.comp_left _ hq) (equiv_rel.comp_right _ hp)),
     end) f g,
  id_comp' := by { intros, induction f, { apply quotient.sound, simp, }, { refl, }, },
  comp_id' := by { intros, induction f, { apply quotient.sound, simp, }, { refl, }, },
  assoc' := begin
    intros,
    induction f, induction g, induction h,
    { apply quotient.sound,
      simp,  },
    all_goals { refl, },
  end, }

def trivial_presentation (C : Type u) [category.{v} C] : Type u := C

instance (C : Type u) [category.{v} C] :
  presented_category (trivial_presentation C) :=
{ rel := λ X Y p q, @compose_path C _ _ _ p = @compose_path C _ _ _ q, }

lemma trivial_presentation_equiv_rel (C : Type u) [category.{v} C] {X Y : C} (p q : path X Y) :
  equiv_rel (trivial_presentation C) p q ↔ @compose_path C _ _ _ p = @compose_path C _ _ _ q :=
sorry

def of_trivial_presentation_equivalence (C : Type u) [category.{v} C] :
  of (trivial_presentation C) ≌ C :=
{ functor :=
  { obj := λ X, X,
    map := begin
      intros X Y f,
      apply quotient.lift_on f (λ p, @compose_path C _ _ _ p),
      intros g h w,
      rw ←trivial_presentation_equiv_rel,
      exact w,
    end,
    map_id' := sorry,
    map_comp' := sorry, },
  inverse :=
  { obj := λ X, X,
    map := λ X Y f, quotient.mk (hom.to_path f),
    map_id' := sorry,
    map_comp' := sorry, },
  unit_iso := nat_iso.of_components (λ X, iso.refl _) sorry,
  counit_iso := nat_iso.of_components (λ X, iso.refl _) sorry, }

end presented_category

end category_theory
