import category_theory.types
import category_theory.comma
import category_theory.equivalence
import category_theory.punit
import category_theory.eq_to_hom

namespace category_theory

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

def category_of_elements (F : C ⥤ Type u) : category (Σ c : C, F.obj c) :=
{ hom := λ p q, { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 },
  id := λ p, ⟨ 𝟙 p.1, by obviously ⟩,
  comp := λ p q r f g, ⟨ f.val ≫ g.val, by obviously ⟩ }

namespace category_of_elements
local attribute [instance] category_of_elements
variable (F : C ⥤ Type u)

def π : (Σ c : C, F.obj c) ⥤ C :=
{ obj := λ X, X.1,
  map := λ X Y f, f.val }

def to_comma : (Σ c : C, F.obj c) ⥤ comma (functor.of.obj punit) F :=
{ obj := λ X, { left := punit.star, right := X.1, hom := λ _, X.2 },
  map := λ X Y f, { right := f.val, } }

def from_comma : comma (functor.of.obj punit) F ⥤ (Σ c : C, F.obj c) :=
{ obj := λ X, ⟨X.right, X.hom (punit.star)⟩,
  map := λ X Y f, ⟨f.right, congr_fun f.w'.symm punit.star⟩ }

section
local attribute [simp] to_comma from_comma

def comma_equivalence : (Σ c : C, F.obj c) ≌ comma (functor.of.obj punit) F :=
{ functor := to_comma F,
  inverse := from_comma F,
  fun_inv_id' := nat_iso.of_components (λ X, eq_to_iso (by tidy)) (by tidy),
  inv_fun_id' := nat_iso.of_components
    (λ X, { hom := begin tidy, exact 𝟙 _, simp, end, inv := begin tidy, exact 𝟙 _, simp, end })
    (by tidy) }
end

end category_of_elements
end category_theory
