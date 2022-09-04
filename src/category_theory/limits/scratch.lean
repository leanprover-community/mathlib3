import category_theory.limits.yoneda
import category_theory.limits.types

universes w' w v u

noncomputable theory

open category_theory

namespace category_theory.limits
variables {J : Type v} [category.{v} J] {C : Type u} [category.{v} C]
variables (F : J ⥤ C) (c l : cocone F)

def blubb (j : Jᵒᵖ) : (l.X ⟶ c.X) ⟶ (F.op ⋙ yoneda.obj c.X).obj j :=
λ f, l.ι.app j.unop ≫ f

def blubb' : (l.X ⟶ c.X) ⟶ (limit (F.op ⋙ yoneda.obj c.X) : Type v) :=
limit.lift _
{ X := _,
  π :=
  { app := λ j, blubb F c l j,
    naturality' :=
    begin
      dsimp [blubb],
      intros X Y f,
      ext g,
      simp only [types_comp_apply, types_id_apply, yoneda_obj_map, quiver.hom.unop_op,
        cocone.w_assoc]
    end } }

lemma something [is_iso (blubb' F c l)] (x : limit (F.op ⋙ yoneda.obj c.X)) (j : J) :
l.ι.app j ≫ inv (blubb' F c l) x = limits.limit.π (F.op ⋙ yoneda.obj c.X) (opposite.op j) x
 :=
begin
  have : blubb' F c l ((inv (blubb' F c l)) x) = x,
  { rw ←types_comp_apply (inv (blubb' F c l)) (blubb' F c l),
    simp [-types_comp_apply] },
  change (limit.lift _ ⟨_, _⟩ : (l.X ⟶ c.X) ⟶ (limit (F.op ⋙ yoneda.obj c.X) : Type v)) _ = _ at this,
  have h := congr_arg (limit.π (F.op ⋙ yoneda.obj c.X) (opposite.op j)) this,
  rw [←types_comp_apply (limits.limit.lift _ _) (limits.limit.π _ _), limit.lift_π] at h,
  dsimp [blubb] at h,
  exact h
end

def is_colimit_of_is_iso_blubb' [∀ c, is_iso (blubb' F c l)] : is_colimit l :=
{ desc := λ s,
  begin
    refine (inv (blubb' F s l)) _,
    refine (types.limit_equiv_sections.{v v} (F.op ⋙ yoneda.obj s.X)).symm _,
    refine ⟨λ j, s.ι.app j.unop, λ j j' f, _⟩,
    simp only [functor.comp_map, functor.op_map, yoneda_obj_map, quiver.hom.unop_op, cocone.w]
  end,
  fac' := λ s j,
  begin
    rw something,
    simp,
    dsimp,
    simp,
  end,
  uniq' := λ s m h,
  begin
    have : (inv (blubb' F s l)) (blubb' F s l m) = m,
    { rw ←types_comp_apply (blubb' F s l) (inv (blubb' F s l)),
      simp [-types_comp_apply] },
    rw ←this,
    congr' 1,
    apply (limits.types.limit_equiv_sections.{v v} (F.op ⋙ yoneda.obj s.X)).injective,
    simp [blubb'],
    ext j,
    simp [blubb, h j.unop],
  end }

end category_theory.limits
