import category_theory.examples.topological_spaces
import category_theory.adjunction
import analysis.topology.stone_cech

universes u v

namespace category_theory.examples.Top
open category_theory category_theory.examples category_theory.functor_to_types
  category_theory.adjunction
open set

def discrete : Type u ⥤ Top.{u} :=
{ obj := λ α, ⟨α, ⊤⟩,
  map := λ α β f, ⟨f, continuous_top⟩ }

def indiscrete : Type u ⥤ Top.{u} :=
{ obj := λ α, ⟨α, ⊥⟩,
  map := λ α β f, ⟨f, continuous_bot⟩ }

def discrete_adj : adjunction discrete (forget topological_space) :=
adjunction_of_equiv
  (λ α β, ⟨λ f, f.1, λ f, ⟨f, continuous_top⟩, by tidy, by tidy⟩)
  (by tidy)
  (by tidy)

def indiscrete_adj : adjunction (forget topological_space) indiscrete :=
adjunction_of_equiv
  (λ α β, ⟨λ f, ⟨f, continuous_bot⟩, λ f, f.1, by tidy, by tidy⟩)
  (by tidy)
  (by tidy)


def CptHaus := {X : Top // compact_space X ∧ t2_space X}

instance : category CptHaus := by apply category_theory.full_subcategory

def CptHaus.mk_ob (X : Type u) [topological_space X] [h₁ : compact_space X] [h₂ : t2_space X] :
  CptHaus.{u} := ⟨mk_ob X, h₁, h₂⟩

instance (X : CptHaus) : compact_space X.val.α := X.property.1
instance (X : CptHaus) : t2_space X.val.α := X.property.2

def stone_cech_obj : Top → CptHaus := λ X, CptHaus.mk_ob (stone_cech X)

def stone_cech_unit_hom {X} : X ⟶ (stone_cech_obj X).val :=
by exact ⟨stone_cech_unit, continuous_stone_cech_unit⟩ -- UGH?

noncomputable def stone_cech_e (X Y) :
  (stone_cech_obj X ⟶ Y) ≃ (X ⟶ Y.val) :=
⟨λ f, stone_cech_unit_hom ≫ f,
 λ f, ⟨stone_cech_extend f.2, continuous_stone_cech_extend f.2⟩,
 λ ⟨f, hf⟩, begin                     -- Extension is unique; make this a lemma or two
   apply subtype.eq,
   dsimp,
   apply funext,
   refine is_closed_property stone_cech_unit_dense _ _,
   { refine is_closed_eq (continuous_stone_cech_extend _) hf },
   { intro x, change (stone_cech_extend _ ∘ stone_cech_unit) x = _,
     rw stone_cech_extend_extends, refl }
 end,
 λ ⟨f, hf⟩, subtype.eq (stone_cech_extend_extends hf)⟩

noncomputable def stone_cech : Top ⥤ CptHaus :=
left_adjoint_of_equiv
  -- This is pretty bad; make F, G arguments of left_adjoint_of_equiv explicit
  (show Π (X Y), (stone_cech_obj X ⟶ Y) ≃ (X ⟶ (full_subcategory_inclusion _).obj Y),
   from stone_cech_e)
  (by intros; refl)

end category_theory.examples.Top

