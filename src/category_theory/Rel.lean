import data.rel category_theory.types

universe u

namespace category_theory

def Rel := Type u

instance Rel.category : large_category Rel.{u} :=
{ hom := rel,
  comp := @rel.comp,
  id := @eq,
  comp_id' := @rel.comp_right_id,
  id_comp' := @rel.comp_left_id,
  assoc' := @rel.comp_assoc }

def find_better_name : Type u ⥤ Rel.{u} :=
{ obj := id,
  map := @function.graph',
  map_id' := @function.graph'_id,
  map_comp' := @function.graph'_comp }

instance find_better_name_faithful : faithful find_better_name :=
⟨@function.graph'_inj⟩

end category_theory

