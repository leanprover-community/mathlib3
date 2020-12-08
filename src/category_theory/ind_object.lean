import category_theory.limits.functor_category
import category_theory.full_subcategory
import category_theory.limits.types
import category_theory.Fintype
import category_theory.punit

namespace category_theory
namespace limits

universes v u
variables {C : Type u} [category.{v} C]

structure as_inductive (P : Cᵒᵖ ⥤ Type v) :=
(D : Type*)
[𝒟 : small_category D]
[hD : is_filtered D]
(α : D ⥤ C)
(c : cocone (α ⋙ yoneda))
(hc : is_colimit c)
(i : P ≅ c.X)

structure is_inductive (P : Cᵒᵖ ⥤ Type v) : Prop :=
(mk' : nonempty (as_inductive P))

variable (C)

@[derive category]
def ind := {P : Cᵒᵖ ⥤ Type v // is_inductive P}

@[derive [full, faithful]]
def to_Presheaf : ind C ⥤ Cᵒᵖ ⥤ Type v := full_subcategory_inclusion _

instance : is_filtered (discrete punit) :=
{ cocone_objs := λ X Y, ⟨punit.star, eq_to_hom (by simp), eq_to_hom (by simp), ⟨⟩⟩,
  cocone_maps := λ X Y f g, ⟨punit.star, eq_to_hom (by simp), by simp⟩ }

def embed : C ⥤ ind C :=
{ obj := λ X,
  begin
    let i : (functor.from_punit X ⋙ yoneda) ≅ functor.from_punit (yoneda.obj X) :=
      discrete.nat_iso (λ i, iso.refl _),
    refine ⟨yoneda.obj X, ⟨⟨⟨_, functor.from_punit X, _, _, _⟩⟩⟩⟩,
    -- TODO: make an API for (co)limits over diagrams of the form `functor.from_punit T`
    { apply (cocones.precompose i.hom).obj ⟨yoneda.obj X, (discrete.nat_trans (λ i, 𝟙 _))⟩ },
    { apply (is_colimit.precompose_hom_equiv _ _).symm _,
      refine ⟨λ s, s.ι.app punit.star, _, _⟩,
      { rintro s ⟨⟩,
        apply category.id_comp },
      { intros s m w,
        rw ← w,
        apply (category.id_comp _).symm } },
    apply iso.refl _
  end,
  map := λ X Y f,
  begin
    apply (to_Presheaf C).preimage,
    apply yoneda.map f,
  end }

def thing : ind Fintype.{u} ≌ Type u :=
sorry

end limits
end category_theory
