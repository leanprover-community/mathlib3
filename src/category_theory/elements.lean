import category_theory.types
import category_theory.comma
import category_theory.equivalence
import category_theory.punit
import category_theory.eq_to_hom

namespace category_theory

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

def functor.elements (F : C ⥤ Type u) := (Σ c : C, F.obj c)

instance category_of_elements (F : C ⥤ Type u) : category F.elements :=
{ hom := λ p q, { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 },
  id := λ p, ⟨ 𝟙 p.1, by obviously ⟩,
  comp := λ p q r f g, ⟨ f.val ≫ g.val, by obviously ⟩ }

namespace category_of_elements
variable (F : C ⥤ Type u)

def π : F.elements ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.val }

@[simp] lemma π_obj (X : F.elements) : (π F).obj X = X.1 := rfl
@[simp] lemma π_map {X Y : F.elements} (f : X ⟶ Y) : (π F).map f = f.val := rfl

def to_comma : F.elements ⥤ comma (functor.of.obj punit) F :=
{ obj := λ X, { left := punit.star, right := X.1, hom := λ _, X.2 },
  map := λ X Y f, { right := f.val } }

@[simp] lemma to_comma_obj (X) :
  (to_comma F).obj X = { left := punit.star, right := X.1, hom := λ _, X.2 } := rfl
@[simp] lemma to_comma_map {X Y} (f : X ⟶ Y) :
  (to_comma F).map f = { right := f.val } := rfl

def from_comma : comma (functor.of.obj punit) F ⥤ F.elements :=
{ obj := λ X, ⟨X.right, X.hom (punit.star)⟩,
  map := λ X Y f, ⟨f.right, congr_fun f.w'.symm punit.star⟩ }

@[simp] lemma from_comma_obj (X) :
  (from_comma F).obj X = ⟨X.right, X.hom (punit.star)⟩ := rfl
@[simp] lemma from_comma_map {X Y} (f : X ⟶ Y) :
  (from_comma F).map f = ⟨f.right, congr_fun f.w'.symm punit.star⟩ := rfl

section
def comma_equivalence : F.elements ≌ comma (functor.of.obj punit) F :=
{ functor := to_comma F,
  inverse := from_comma F,
  fun_inv_id' := nat_iso.of_components (λ X, eq_to_iso (by tidy)) (by tidy),
  inv_fun_id' := nat_iso.of_components
    (λ X, { hom := { right := 𝟙 _ }, inv := { right := 𝟙 _ } })
    (by tidy) }
end

end category_of_elements
end category_theory
