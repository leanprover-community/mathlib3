import category_theory.limits.cones
import category_theory.structured_arrow
import category_theory.fin_category

universes v₁ u₁

open category_theory.limits

namespace category_theory
section bicones
variables (J : Type u₁) [category.{v₁} J] [decidable_eq J] [∀ (j k : J), decidable_eq (j ⟶ k)]

@[derive decidable_eq]
inductive bicones (J : Type u₁)
| left : bicones
| right : bicones
| diagram (val : J) : bicones

@[derive decidable_eq]
inductive bicones_hom : bicones J → bicones J → Type (max u₁ v₁)
| left_id  : bicones_hom bicones.left bicones.left
| right_id : bicones_hom bicones.right bicones.right
| left (j : J) : bicones_hom bicones.left (bicones.diagram j)
| right (j : J) : bicones_hom bicones.right (bicones.diagram j)
| diagram {j k : J} (f : j ⟶ k) : bicones_hom (bicones.diagram j) (bicones.diagram k)

@[simps]
def bicones_category_struct : category_struct (bicones J) :=
{ hom := bicones_hom J,
  id := λ j, bicones.cases_on j
    bicones_hom.left_id bicones_hom.right_id (λ k, bicones_hom.diagram (𝟙 k)),
  comp := λ X Y Z f g, by
  { cases f, exact g, exact g,
    cases g, exact bicones_hom.left g_k,
    cases g, exact bicones_hom.right g_k,
    cases g, exact bicones_hom.diagram (f_f ≫ g_f) } }


instance bicones_category : category (bicones J) :=
{ id_comp' := λ X Y f, by { cases f; simp },
  comp_id' := λ X Y f, by { cases f; simp },
  assoc' := λ W X Y Z f g h, by { cases f; cases g; cases h; simp },
  ..(bicones_category_struct J) }

end bicones
section small_category
variables (J : Type v₁) [small_category J] [decidable_eq J] [∀ (j k : J), decidable_eq (j ⟶ k)]

def bicones_mk {C : Type u₁} [category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : cone F) : bicones J ⥤ C :=
{ obj := λ X, bicones.cases_on X c₁.X c₂.X (λ j, F.obj j),
  map := λ X Y f, by
  { cases f, exact (𝟙 _), exact (𝟙 _),
    exact c₁.π.app f_1,
    exact c₂.π.app f_1,
    exact F.map f_f, },
  map_id' := λ X, by { cases X; simp },
  map_comp' := λ X Y Z f g, by
  { cases f,
    exact (category.id_comp _).symm,
    exact (category.id_comp _).symm,
    cases g, exact (category.id_comp _).symm.trans (c₁.π.naturality g_f : _),
    cases g, exact (category.id_comp _).symm.trans (c₂.π.naturality g_f : _),
    cases g, exact F.map_comp _ _ } }

instance fin_bicones [fintype J] : fintype (bicones J) :=
{ elems := [bicones.left, bicones.right].to_finset ∪ finset.image bicones.diagram (fintype.elems J),
  complete := λ j, by { cases j; simp, exact fintype.complete j, }, }

instance fin_bicones_hom [fin_category J] (j k : bicones J) : fintype (j ⟶ k) :=
begin
cases j; cases k,
exact { elems := {bicones_hom.left_id}, complete := λ f, by { cases f, simp } },
exact { elems := ∅, complete := λ f, by { cases f } },
exact { elems := {bicones_hom.left k}, complete := λ f, by { cases f, simp } },
exact { elems := ∅, complete := λ f, by { cases f } },
exact { elems := {bicones_hom.right_id}, complete := λ f, by { cases f, simp } },
exact { elems := {bicones_hom.right k}, complete := λ f, by { cases f, simp } },
exact { elems := ∅, complete := λ f, by { cases f } },
exact { elems := ∅, complete := λ f, by { cases f } },
exact { elems := finset.image (bicones_hom.diagram) (fintype.elems (j ⟶ k)),
        complete := λ f, by
          { cases f, simp only [finset.mem_image], use f_f, simpa using fintype.complete _, } },
end

instance bicones_small_category : small_category (bicones J) := category_theory.bicones_category J

instance bicones_fin_category [fin_category J] : fin_category (bicones J) := {}
end small_category
end category_theory
