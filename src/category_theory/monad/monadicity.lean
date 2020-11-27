import category_theory.limits.shapes.reflexive
import category_theory.monad.adjunction

universes v₁ v₂ u₁ u₂

namespace category_theory
namespace monad
open limits

/-!
Show that any algebra is a coequalizer of free algebras.
-/
namespace cofork_free
variables {B : Type u₂}
variables [category.{v₂} B]

variables (T : B ⥤ B) [monad T] (X : monad.algebra T)

/-- The top map in the coequalizer diagram we will construct. -/
@[simps {rhs_md := semireducible}]
def top_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
(monad.free T).map X.a
/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def bottom_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
{ f := (μ_ T).app X.A,
  h' := monad.assoc X.A }
/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
def coequalizer_map : (monad.free T).obj X.A ⟶ X :=
{ f := X.a,
  h' := X.assoc.symm }

lemma comm : top_map T X ≫ coequalizer_map T X = bottom_map T X ≫ coequalizer_map T X :=
monad.algebra.hom.ext _ _ X.assoc.symm

/--
The cofork constructed is a colimit. This shows that any algebra is a coequalizer of free algebras.
-/
def is_colimit : is_colimit (cofork.of_π _ (comm T X)) :=
cofork.is_colimit.mk' _ $ λ s,
begin
  have h₁ : T.map X.a ≫ s.π.f = (μ_ T).app X.A ≫ s.π.f := congr_arg monad.algebra.hom.f s.condition,
  have h₂ : T.map s.π.f ≫ s.X.a = (μ_ T).app X.A ≫ s.π.f := s.π.h,
  refine ⟨⟨(η_ T).app _ ≫ s.π.f, _⟩, _, _⟩,
  { dsimp,
    rw [T.map_comp, category.assoc, h₂, monad.right_unit_assoc,
        (show X.a ≫ _ ≫ _ = _, from (η_ T).naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { ext1,
    dsimp,
    rw [(show X.a ≫ _ ≫ _ = _, from (η_ T).naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { intros m hm,
    ext1,
    dsimp,
    rw ← hm,
    dsimp,
    rw X.unit_assoc }
end
@[simp] lemma is_colimit_X : (cofork.of_π _ (comm T X)).X = X := rfl

end cofork_free

noncomputable theory
namespace monadicity

section

parameters {C : Type u₁} {D : Type u₂}
parameters [category.{v₁} C] [category.{v₁} D]
parameters {G : D ⥤ C} [is_right_adjoint G]

abbreviation F : C ⥤ D := left_adjoint G
abbreviation adj : F ⊣ G := adjunction.of_right_adjoint G
abbreviation K : D ⥤ algebra (F ⋙ G) := monad.comparison _

def comparison_left_adjoint_obj
  (A : algebra (F ⋙ G)) [has_coequalizer (F.map A.a) (adj.counit.app _)] : D :=
coequalizer (F.map A.a) (adj.counit.app _)

abbreviation L_obj := comparison_left_adjoint_obj

def comparison_left_adjoint_hom_equiv (A : algebra (F ⋙ G)) (B : D)
  [has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
  (L_obj A ⟶ B) ≃ (A ⟶ K.obj B) :=
calc (L_obj A ⟶ B) ≃ {f : F.obj A.A ⟶ B // _} : cofork.is_colimit.hom_iso (colimit.is_colimit _) B
     ... ≃ {g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g} :
      begin
        refine (adj.hom_equiv _ _).subtype_congr _,
        intro f,
        rw [← (adj.hom_equiv _ _).injective.eq_iff, adjunction.hom_equiv_naturality_left,
            adj.hom_equiv_unit, adj.hom_equiv_unit, G.map_comp],
        dsimp,
        rw [adj.right_triangle_components_assoc, ← G.map_comp, F.map_comp, category.assoc,
            adj.counit_naturality, adj.left_triangle_components_assoc],
        apply eq_comm,
      end
     ... ≃ (A ⟶ K.obj B) :
     { to_fun := λ g, { f := _, h' := g.prop },
       inv_fun := λ f, ⟨f.f, f.h⟩,
       left_inv := λ g, begin ext, refl end,
       right_inv := λ f, begin ext, refl end }

def left_adjoint_comparison
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
  algebra (F ⋙ G) ⥤ D :=
begin
  refine @adjunction.left_adjoint_of_equiv _ _ _ _ K (λ A, L_obj A) (λ A B, _) _,
  { apply comparison_left_adjoint_hom_equiv },
  { intros A B B' g h,
    ext1,
    dsimp [comparison_left_adjoint_hom_equiv],
    rw [← adjunction.hom_equiv_naturality_right, category.assoc] },
end

def comparison_adjunction
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
  left_adjoint_comparison ⊣ comparison G :=
adjunction.adjunction_of_equiv_left _ _

lemma comparison_adjunction_unit
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
  (A : algebra (F ⋙ G)) :
  (comparison_adjunction.unit.app A).f =
    adj.hom_equiv A.A (L_obj A) (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
begin
  dsimp [comparison_adjunction, adjunction.adjunction_of_equiv_left, adjunction.mk_of_hom_equiv,
         comparison_left_adjoint_hom_equiv, adjunction.left_adjoint_of_equiv],
         -- lots of these should be dsimp/simp lemmas instead of being unfolded here
  erw category.comp_id,
end

lemma comparison_adjunction_unit'
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
  (A : algebra (F ⋙ G)) :
  comparison_adjunction.unit.app A = (cofork.is_colimit.desc' (cofork_free.is_colimit (F ⋙ G) _) (begin refine (comparison G).map _, change _ ⟶ coequalizer _ _, dsimp, apply coequalizer.π end) _).1 :=
begin
end

section reflexive_monadicity

variables [has_reflexive_coequalizers D] [reflects_isomorphisms G]
variables [∀ ⦃A B⦄ (f g : A ⟶ B) [is_reflexive_pair f g], preserves_colimit (parallel_pair f g) G]

def reflexive_monadicity : monadic_right_adjoint G :=
begin
  have : ∀ (A : algebra (F ⋙ G)), is_reflexive_pair (F.map A.a) (adj.counit.app (F.obj A.A)),
  { intro A,
    apply is_reflexive_pair.mk' (F.map (adj.unit.app _)) _ _,
    { rw ← F.map_comp,
      erw A.unit,
      erw F.map_id },
    { rw adj.left_triangle_components,
      refl } },
  resetI,
  let L : algebra (F ⋙ G) ⥤ D := left_adjoint_comparison,
  letI i : is_right_adjoint (comparison G) := ⟨_, comparison_adjunction⟩,
  constructor,
  let : Π (X : algebra (left_adjoint G ⋙ G)),
    is_iso ((adjunction.of_right_adjoint (comparison G)).unit.app X),
  { intro X,
    apply is_iso_of_reflects_iso _ (monad.forget (F ⋙ G)),
    { dsimp,
      erw comparison_adjunction_unit,


    },
    { apply_instance } },
  let : Π (Y : D),
    is_iso ((adjunction.of_right_adjoint (comparison G)).counit.app Y),
  { sorry },
  exactI adjunction.is_right_adjoint_to_is_equivalence,
end

end reflexive_monadicity

end

end monadicity

end monad
end category_theory
