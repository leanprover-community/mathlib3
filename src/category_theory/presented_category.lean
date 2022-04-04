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
  iseqv := ⟨λ p, equiv_rel.refl p, λ _ _ f, equiv_rel.symm f, λ _ _ _ f g, equiv_rel.trans f g⟩, }

def of (C : Type*) [presented_category C] : Type* := C

def unwrap {C : Type*} [presented_category C] (X : of C) : C := X

@[simps]
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
begin
  split,
  { intro w, induction w,
    { exact w_r, },
    { refl, },
    { cc, },
    { cc, },
    { simp [w_ih], },
    { simp [w_ih], }, },
  { intro w, exact equiv_rel.of w, }
end

/-- The category constructed from the trivial presentation of a category
is equivalent to the original category. -/
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
    map_id' := by { intros, simp, refl, },
    map_comp' := by { intros, induction f, { induction g; simp, }, { refl, }, }, },
  inverse :=
  { obj := λ X, X,
    map := λ X Y f, quotient.mk (hom.to_path f),
    map_id' := by { intros, apply quotient.sound, apply (trivial_presentation_equiv_rel _ _ _).2, simp, refl, },
    map_comp' := by { intros, apply quotient.sound, apply (trivial_presentation_equiv_rel _ _ _).2, simp, }, },
  unit_iso := nat_iso.of_components (λ X, iso.refl _) begin
    intros,
    induction f,
    { apply quotient.sound, apply (trivial_presentation_equiv_rel _ _ _).2,
      simp, },
    { refl, },
  end,
  counit_iso := nat_iso.of_components (λ X, iso.refl _) (by tidy), }

end presented_category

end category_theory
