import category_theory.limits.shapes.reflexive
import category_theory.limits.preserves.shapes.equalizers
import category_theory.limits.preserves.limits
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

@[simps {rhs_md := semireducible}]
def beck_algebra_cofork : cofork (top_map T X) (bottom_map T X) :=
cofork.of_π _ (comm T X)

/--
The cofork constructed is a colimit. This shows that any algebra is a coequalizer of free algebras.
-/
def beck_algebra_coequalizer : is_colimit (beck_algebra_cofork T X) :=
cofork.is_colimit.mk' _ $ λ s,
begin
  have h₁ : T.map X.a ≫ s.π.f = (μ_ T).app X.A ≫ s.π.f := congr_arg monad.algebra.hom.f s.condition,
  have h₂ : T.map s.π.f ≫ s.X.a = (μ_ T).app X.A ≫ s.π.f := s.π.h,
  refine ⟨⟨(η_ T).app _ ≫ s.π.f, _⟩, _, _⟩,
  { dsimp,
    rw [T.map_comp, category.assoc, h₂, monad.right_unit_assoc,
        (show X.a ≫ _ ≫ _ = _, from (η_ T).naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { ext1,
    dsimp [beck_algebra_cofork],
    rw [(show X.a ≫ _ ≫ _ = _, from (η_ T).naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { intros m hm,
    ext1,
    dsimp,
    rw ← hm,
    dsimp [beck_algebra_cofork],
    rw X.unit_assoc }
end
@[simp] lemma is_colimit_X : (cofork.of_π _ (comm T X)).X = X := rfl

def beck_split_coequalizer : is_split_coequalizer (T.map X.a) ((μ_ T).app _) X.a :=
⟨X.assoc.symm, (η_ T).app _, (η_ T).app _, X.unit, monad.left_unit _, ((η_ T).naturality _).symm⟩

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
def beck_cofork : cofork (T.map X.a) ((μ_ T).app _)  :=
(beck_split_coequalizer T X).as_cofork

noncomputable def beck_coequalizer : limits.is_colimit (beck_cofork T X) :=
(beck_split_coequalizer T X).is_coequalizer

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

instance main_pair_reflexive (A : algebra (F ⋙ G)) :
  is_reflexive_pair (F.map A.a) (adj.counit.app (F.obj A.A)) :=
begin
  apply is_reflexive_pair.mk' (F.map (adj.unit.app _)) _ _,
  { rw ← F.map_comp,
    erw A.unit,
    erw F.map_id },
  { rw adj.left_triangle_components,
    refl },
end

instance main_pair_G_split (A : algebra (F ⋙ G)) :
  G.is_split_pair (F.map A.a) (adj.counit.app (F.obj A.A)) :=
{ splittable := ⟨_, _, cofork_free.beck_split_coequalizer (F ⋙ G) A⟩ }

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

/--
This is a cofork which key in understanding the unit of the adjunction.
-/
def unit_cofork (A : algebra (F ⋙ G)) [has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
  cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj A.A))) :=
cofork.of_π (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))))
begin
  change _ = G.map _ ≫ _,
  rw [← G.map_comp, coequalizer.condition, G.map_comp],
end

def counit_cofork (B : D) :
  cofork (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B))) :=
cofork.of_π (adj.counit.app B) (adj.counit_naturality _)

def unit_colimit_of_preserves_coequalizer
  (A : algebra (F ⋙ G)) [has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
  [preserves_colimit (parallel_pair (F.map A.a) (adj.counit.app (F.obj A.A))) G] :
  is_colimit (unit_cofork A) :=
preserves_coequalizer.is_limit_of_has_equalizer_of_preserves_limit G _ _

def counit_coequalizer_of_reflects_coequalizer (B : D)
  [reflects_colimit (parallel_pair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B)))) G] :
  is_colimit (counit_cofork B) :=
preserves_coequalizer.is_limit_of_reflects_of_map_is_limit G _
  (cofork_free.beck_coequalizer (F ⋙ G) ((comparison G).obj B))

lemma comparison_adjunction_unit''
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
  (A : algebra (F ⋙ G)) :
  (comparison_adjunction.unit.app A).f = (cofork_free.beck_coequalizer (F ⋙ G) A).desc (unit_cofork A) :=
begin
  apply limits.cofork.is_colimit.hom_ext (cofork_free.beck_coequalizer (F ⋙ G) A),
  rw is_colimit.fac,
  dsimp [cofork_free.beck_cofork], -- TODO: need dsimp lemmas about this, and probably dsimp lemmas about cofork.of_π
  rw [comparison_adjunction_unit, ← adj.hom_equiv_naturality_left A.a, adj.hom_equiv_apply_eq,
      coequalizer.condition, ← adj.counit_naturality, adj.hom_equiv_counit],
  refl,
end

lemma comparison_adjunction_counit
  [∀ (A : algebra (F ⋙ G)), has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] (B : D) :
  comparison_adjunction.counit.app B = colimit.desc _ (counit_cofork B) :=
begin
  apply coequalizer.hom_ext,
  conv_rhs {erw colimit.ι_desc},
  conv_lhs {erw colimit.ι_desc},
  dsimp [counit_cofork],
  rw adjunction.hom_equiv_counit,
  rw F.map_id,
  rw category.id_comp,
end

section beck_monadicity

variables [∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], creates_colimit (parallel_pair f g) G]

/--
Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
-/
def beck_monadicity : monadic_right_adjoint G :=
begin
  letI : ∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], has_coequalizer f g,
  { introsI A B f g i,
    have : has_colimit (parallel_pair f g ⋙ G),
    { apply has_colimit_of_iso (diagram_iso_parallel_pair _),
      change has_coequalizer (G.map f) (G.map g),
      apply_instance },
    exactI has_colimit_of_created _ G },
  letI : ∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], preserves_colimit (parallel_pair f g) G,
  { introsI A B f g i,
    have : has_colimit (parallel_pair f g ⋙ G),
    { apply has_colimit_of_iso (diagram_iso_parallel_pair _),
      change has_coequalizer (G.map f) (G.map g),
      apply_instance },
    resetI,
    apply_instance },
  let L : algebra (F ⋙ G) ⥤ D := left_adjoint_comparison,
  letI i : is_right_adjoint (comparison G) := ⟨_, comparison_adjunction⟩,
  constructor,
  let : Π (X : algebra (left_adjoint G ⋙ G)),
    is_iso ((adjunction.of_right_adjoint (comparison G)).unit.app X),
  { intro X,
    apply is_iso_of_reflects_iso (monad.forget (F ⋙ G)) _,
    { apply_instance },
    dsimp,
    erw comparison_adjunction_unit'',
    change
      is_iso
        (is_colimit.cocone_point_unique_up_to_iso
          (cofork_free.beck_coequalizer (F ⋙ G) X)
          (unit_colimit_of_preserves_coequalizer X)).hom,
    apply is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _) },
  let : Π (Y : D),
    is_iso ((adjunction.of_right_adjoint (comparison G)).counit.app Y),
  { intro Y,
    erw comparison_adjunction_counit,
    change is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).hom,
    apply_instance,
    apply counit_coequalizer_of_reflects_coequalizer _,
    letI : G.is_split_pair (F.map (G.map (adj.counit.app Y))) (adj.counit.app (F.obj (G.obj Y))),
      apply monadicity.main_pair_G_split ((comparison G).obj Y),
    apply_instance },
  exactI adjunction.is_right_adjoint_to_is_equivalence,
end

end beck_monadicity

section reflexive_monadicity

variables [has_reflexive_coequalizers D] [reflects_isomorphisms G]
variables [∀ ⦃A B⦄ (f g : A ⟶ B) [is_reflexive_pair f g], preserves_colimit (parallel_pair f g) G]

/--
Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def reflexive_monadicity : monadic_right_adjoint G :=
begin
  let L : algebra (F ⋙ G) ⥤ D := left_adjoint_comparison,
  letI i : is_right_adjoint (comparison G) := ⟨_, comparison_adjunction⟩,
  constructor,
  let : Π (X : algebra (left_adjoint G ⋙ G)),
    is_iso ((adjunction.of_right_adjoint (comparison G)).unit.app X),
  { intro X,
    apply is_iso_of_reflects_iso (monad.forget (F ⋙ G)) _,
    { apply_instance },
    dsimp,
    erw comparison_adjunction_unit'',
    change
      is_iso
        (is_colimit.cocone_point_unique_up_to_iso
          (cofork_free.beck_coequalizer (F ⋙ G) X)
          (unit_colimit_of_preserves_coequalizer X)).hom,
    apply is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _) },
  let : Π (Y : D),
    is_iso ((adjunction.of_right_adjoint (comparison G)).counit.app Y),
  { intro Y,
    erw comparison_adjunction_counit,
    change is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).hom,
    apply_instance,
    apply counit_coequalizer_of_reflects_coequalizer _,
    apply reflects_colimit_of_reflects_isomorphisms },
  exactI adjunction.is_right_adjoint_to_is_equivalence,
end

end reflexive_monadicity

end

end monadicity

end monad

#check @monad.monadicity.reflexive_monadicity

end category_theory
