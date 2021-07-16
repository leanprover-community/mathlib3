/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monad.algebra
import category_theory.adjunction.reflective

namespace category_theory
open category

universes v₁ v₂ v₃ u₁ u₂ u₃
  -- morphism levels before object levels. See note [category_theory universes].

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables {L : C ⥤ D} {R : D ⥤ C}

namespace adjunction

/--
For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a monad on
the category `C`.
-/
@[simps]
def to_monad (h : L ⊣ R) : monad C :=
{ to_functor := L ⋙ R,
  η' := h.unit,
  μ' := whisker_right (whisker_left L h.counit) R,
  assoc' := λ X, by { dsimp, rw [←R.map_comp], simp },
  right_unit' := λ X, by { dsimp, rw [←R.map_comp], simp } }

/--
For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a comonad on
the category `D`.
-/
@[simps]
def to_comonad (h : L ⊣ R) : comonad D :=
{ to_functor := R ⋙ L,
  ε' := h.counit,
  δ' := whisker_right (whisker_left R h.unit) L,
  coassoc' := λ X, by { dsimp, rw ← L.map_comp, simp },
  right_counit' := λ X, by { dsimp, rw ← L.map_comp, simp } }

/-- The monad induced by the Eilenberg-Moore adjunction is the original monad.  -/
@[simps]
def adj_to_monad_iso (T : monad C) : T.adj.to_monad ≅ T :=
monad_iso.mk (nat_iso.of_components (λ X, iso.refl _) (by tidy))
  (λ X, by { dsimp, simp })
  (λ X, by { dsimp, simp })

/-- The comonad induced by the Eilenberg-Moore adjunction is the original comonad. -/
@[simps]
def adj_to_comonad_iso (G : comonad C) : G.adj.to_comonad ≅ G :=
comonad_iso.mk (nat_iso.of_components (λ X, iso.refl _) (by tidy))
  (λ X, by { dsimp, simp })
  (λ X, by { dsimp, simp })

end adjunction

/--
Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.monad.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
@[simps]
def monad.comparison (h : L ⊣ R) : D ⥤ h.to_monad.algebra :=
{ obj := λ X,
  { A := R.obj X,
    a := R.map (h.counit.app X),
    assoc' := by { dsimp, rw [← R.map_comp, ← adjunction.counit_naturality, R.map_comp], refl } },
  map := λ X Y f,
  { f := R.map f,
    h' := by { dsimp, rw [← R.map_comp, adjunction.counit_naturality, R.map_comp] } } }.

/--
The underlying object of `(monad.comparison R).obj X` is just `R.obj X`.
-/
@[simps]
def monad.comparison_forget (h : L ⊣ R) :
  monad.comparison h ⋙ h.to_monad.forget ≅ R :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, } }.

-- def monad.free_comparison {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
--   L ⋙ monad.comparison h ≅ h.to_monad.free :=
-- { hom := { app := λ X, { f := 𝟙 _ } },
--   inv := { app := λ X, { f := 𝟙 _ } } }

-- lemma monad.free_comparison_forget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
--   iso_whisker_right (monad.free_comparison h) h.to_monad.forget = _ :=
-- begin
-- end

lemma monad.comparison_unique_aux {L : C ⥤ D} {R : D ⥤ C} {h : L ⊣ R}
  {K : D ⥤ h.to_monad.algebra}
  {hK₁ : K ⋙ h.to_monad.forget ≅ R}
  (hK₂ : Π X, (L ⋙ K).obj X ⟶ h.to_monad.free.obj X)
  (hK : ∀ X, (hK₂ X).f = hK₁.hom.app (L.obj X)) : -- compatibility between hK₁ and hK₂
  ∀ Y, R.map (L.map (hK₁.hom.app Y)) ≫ R.map (h.counit.app Y) = (K.obj Y).a ≫ hK₁.hom.app Y :=
begin
  let β' : Π (Y : D), R.obj (L.obj (R.obj Y)) ⟶ R.obj Y :=
    λ Y, inv (R.map (L.map (hK₁.hom.app Y))) ≫ (K.obj Y).a ≫ hK₁.hom.app _,
  have hβ' : ∀ {Y Y'} (f : Y ⟶ Y'), β' Y ≫ R.map f = R.map (L.map (R.map f)) ≫ β' Y',
  { intros Y Y' f,
    rw [assoc, is_iso.inv_comp_eq, assoc, ←R.map_comp_assoc, ←L.map_comp, ←hK₁.hom.naturality,
      functor.comp_map, monad.forget_map, ←(K.map f).h_assoc, L.map_comp, R.map_comp_assoc,
      is_iso.hom_inv_id_assoc],
    refl },
  intro Y,
  suffices : R.map (h.counit.app Y) = β' Y,
  { rw [this, is_iso.hom_inv_id_assoc] },
  have : ∀ (X : C), R.map (h.counit.app (L.obj X)) = β' (L.obj X),
  { intro X,
    have := (hK₂ X).h,
    dsimp at this,
    simp [hK] at this,
    simpa [hK] using (hK₂ X).h },
  haveI : split_epi (R.map (h.counit.app Y)) := ⟨h.unit.app _, h.right_triangle_components⟩,
  rw [←cancel_epi (R.map (L.map (R.map (h.counit.app Y)))), ←R.map_comp],
  dsimp only [functor.comp_obj, functor.id_obj],
  rw [←hβ', h.counit_naturality, R.map_comp, this],
end

def monad.comparison_unique {L : C ⥤ D} {R : D ⥤ C} {h : L ⊣ R} {K : D ⥤ h.to_monad.algebra}
  (hK : K ⋙ h.to_monad.forget ≅ R) (hK' : L ⋙ K ≅ h.to_monad.free)
  (h' : ∀ (X : C), (hK'.hom.app X).f = hK.hom.app (L.obj X)) :
  K ≅ monad.comparison h :=
nat_iso.of_components
  (λ X, monad.algebra.iso_mk (hK.app X) (monad.comparison_unique_aux hK'.hom.app h' _))
  (λ X Y f, by { ext, apply hK.hom.naturality f })

-- lemma monad.left_comparison (h : L ⊣ R) : L ⋙ monad.comparison h = h.to_monad.free := rfl

instance [faithful R] (h : L ⊣ R) :
  faithful (monad.comparison h) :=
{ map_injective' := λ X Y f g w, R.map_injective (congr_arg monad.algebra.hom.f w : _) }

instance (T : monad C) : full (monad.comparison T.adj) :=
{ preimage := λ X Y f, ⟨f.f, by simpa using f.h⟩ }

instance (T : monad C) : ess_surj (monad.comparison T.adj) :=
{ mem_ess_image := λ X,
  ⟨{ A := X.A, a := X.a, unit' := by simpa using X.unit, assoc' := by simpa using X.assoc },
    ⟨monad.algebra.iso_mk (iso.refl _) (by simp)⟩⟩ }

/--
Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.comonad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlying object
`L.obj X`.
-/
@[simps]
def comonad.comparison (h : L ⊣ R) : C ⥤ h.to_comonad.coalgebra :=
{ obj := λ X,
  { A := L.obj X,
    a := L.map (h.unit.app X),
    coassoc' := by { dsimp, rw [← L.map_comp, ← adjunction.unit_naturality, L.map_comp], refl } },
  map := λ X Y f,
  { f := L.map f,
    h' := by { dsimp, rw ← L.map_comp, simp } } }

/--
The underlying object of `(comonad.comparison L).obj X` is just `L.obj X`.
-/
@[simps]
def comonad.comparison_forget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
  comonad.comparison h ⋙ h.to_comonad.forget ≅ L :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, } }

lemma comonad.left_comparison (h : L ⊣ R) : R ⋙ comonad.comparison h = h.to_comonad.cofree := rfl

instance comonad.comparison_faithful_of_faithful [faithful L] (h : L ⊣ R) :
  faithful (comonad.comparison h) :=
{ map_injective' := λ X Y f g w, L.map_injective (congr_arg comonad.coalgebra.hom.f w : _) }

instance (G : comonad C) : full (comonad.comparison G.adj) :=
{ preimage := λ X Y f, ⟨f.f, by simpa using f.h⟩ }

instance (G : comonad C) : ess_surj (comonad.comparison G.adj) :=
{ mem_ess_image := λ X,
  ⟨{ A := X.A, a := X.a, counit' := by simpa using X.counit, coassoc' := by simpa using X.coassoc },
    ⟨comonad.coalgebra.iso_mk (iso.refl _) (by simp)⟩⟩ }

/--
A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison functor `monad.comparison R`
from `D` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class monadic_right_adjoint (R : D ⥤ C) extends is_right_adjoint R :=
(eqv : is_equivalence (monad.comparison (adjunction.of_right_adjoint R)))

/--
A left adjoint functor `L : C ⥤ D` is *comonadic* if the comparison functor `comonad.comparison L`
from `C` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class comonadic_left_adjoint (L : C ⥤ D) extends is_left_adjoint L :=
(eqv : is_equivalence (comonad.comparison (adjunction.of_left_adjoint L)))

attribute [instance] monadic_right_adjoint.eqv comonadic_left_adjoint.eqv

/-- Given an adjunction `L ⊣ R₁` and an isomorphism `R₁ ≅ R₂` the monads induced on `C` by `R₁` and
`R₂` are isomorphic. -/
@[simps]
def to_monad_iso_of_nat_iso_right {L : C ⥤ D} {R₁ R₂ : D ⥤ C} (h₁ : L ⊣ R₁) (i : R₁ ≅ R₂) :
  h₁.to_monad ≅ (h₁.of_nat_iso_right i).to_monad :=
monad_iso.mk (iso_whisker_left L i)
  (λ X, by simp)
  (λ X,
  begin
    dsimp only [adjunction.to_monad_coe, adjunction.to_monad_μ, whisker_left_app, functor.comp_obj,
      whisker_right_app, functor.comp_map, iso_whisker_left_hom, functor.id_obj],
    simp only [i.hom.naturality, h₁.of_nat_iso_right_counit_app, assoc, ←R₂.map_comp,
      ←L.map_comp_assoc, i.hom_inv_id_app, L.map_id, id_comp],
  end)

def is_equivalence_of_iso (R₁ R₂ : D ⥤ C) (i : R₁ ≅ R₂) [is_equivalence R₁] :
  is_equivalence R₂ :=
is_equivalence.mk
  R₁.inv
  (is_equivalence.unit_iso ≪≫ iso_whisker_right i _)
  (iso_whisker_left _ i.symm ≪≫ is_equivalence.counit_iso)

def monadic_of_iso (R₁ R₂ : D ⥤ C) [monadic_right_adjoint R₁] (i : R₁ ≅ R₂) :
  monadic_right_adjoint R₂ :=
{ to_is_right_adjoint := ⟨_, (adjunction.of_right_adjoint R₁).of_nat_iso_right i⟩,
  eqv :=
  begin
    let h₁ := adjunction.of_right_adjoint R₁,
    change is_equivalence (monad.comparison (h₁.of_nat_iso_right i)),
    let z' : h₁.to_monad.algebra ≌ (h₁.of_nat_iso_right i).to_monad.algebra :=
      monad.algebra_equiv_of_iso_monads (to_monad_iso_of_nat_iso_right h₁ i),
    let : monad.comparison h₁ ⋙ z'.functor ≅ monad.comparison (h₁.of_nat_iso_right i),
    { refine nat_iso.of_components _ _,
      { intro X,
        refine monad.algebra.iso_mk (i.app X) _,
        dsimp,
        rw [adjunction.of_nat_iso_right_counit_app, assoc, i.hom.naturality,
          i.inv_hom_id_app_assoc, ←R₂.map_comp, ←functor.map_comp_assoc, i.hom_inv_id_app,
          functor.map_id, id_comp] },
      { intros X Y f,
        ext,
        apply i.hom.naturality } },
    apply is_equivalence_of_iso _ _ this,
  end }

variables {D' : Type u₃} [category.{v₃} D']

@[simps]
def to_monad_iso_of_equivalence {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) (e : D ≌ D') :
  h.to_monad ≅ (h.comp _ _ e.to_adjunction).to_monad :=
monad_iso.mk
  (iso_whisker_left L (e.fun_inv_id_assoc R).symm ≪≫ (L.associator _ _).symm)
  (λ X, by simp)
  (λ X,
  begin
    dsimp,
    simp only [e.counit_inv_functor_comp, id_comp, e.fun_inv_id_assoc_inv_app, assoc, ←R.map_comp],
    simp,
  end)

def monadic_of_equivalent (R : D ⥤ C) (e : D' ≌ D) [monadic_right_adjoint R] :
  monadic_right_adjoint (e.functor ⋙ R) :=
{ eqv :=
  begin
    let h := adjunction.of_right_adjoint R,
    let h' := h.comp _ _ e.symm.to_adjunction,
    let z' : h.to_monad.algebra ≌ h'.to_monad.algebra :=
      monad.algebra_equiv_of_iso_monads (to_monad_iso_of_equivalence _ e.symm),
    let : e.functor ⋙ monad.comparison (adjunction.of_right_adjoint R) ⋙ z'.functor ≅
            monad.comparison (h.comp _ _ e.symm.to_adjunction),
    { apply nat_iso.of_components _ _,
      { intro X,
        exact monad.algebra.iso_mk (iso.refl _) (by { dsimp, simp }) },
      { intros X Y f,
        ext,
        dsimp,
        simp } },
    apply is_equivalence_of_iso _ _ this,
  end }

noncomputable instance (T : monad C) : monadic_right_adjoint T.forget :=
⟨(equivalence.of_fully_faithfully_ess_surj _ : is_equivalence (monad.comparison T.adj))⟩

noncomputable instance (G : comonad C) : comonadic_left_adjoint G.forget :=
⟨(equivalence.of_fully_faithfully_ess_surj _ : is_equivalence (comonad.comparison G.adj))⟩

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
instance μ_iso_of_reflective [reflective R] : is_iso (adjunction.of_right_adjoint R).to_monad.μ :=
by { dsimp, apply_instance }

attribute [instance] monadic_right_adjoint.eqv
attribute [instance] comonadic_left_adjoint.eqv

namespace reflective

instance [reflective R] (X : (adjunction.of_right_adjoint R).to_monad.algebra) :
  is_iso ((adjunction.of_right_adjoint R).unit.app X.A) :=
⟨⟨X.a, ⟨X.unit, begin
    dsimp only [functor.id_obj],
    rw ← (adjunction.of_right_adjoint R).unit_naturality,
    dsimp only [functor.comp_obj, adjunction.to_monad_coe],
    rw [unit_obj_eq_map_unit, ←functor.map_comp, ←functor.map_comp],
    erw X.unit,
    simp,
  end⟩⟩⟩

instance comparison_ess_surj [reflective R] :
  ess_surj (monad.comparison (adjunction.of_right_adjoint R)) :=
begin
  refine ⟨λ X, ⟨(left_adjoint R).obj X.A, ⟨_⟩⟩⟩,
  symmetry,
  refine monad.algebra.iso_mk _ _,
  { exact as_iso ((adjunction.of_right_adjoint R).unit.app X.A) },
  dsimp only [functor.comp_map, monad.comparison_obj_a, as_iso_hom, functor.comp_obj,
    monad.comparison_obj_A, monad_to_functor_eq_coe, adjunction.to_monad_coe],
  rw [←cancel_epi ((adjunction.of_right_adjoint R).unit.app X.A), adjunction.unit_naturality_assoc,
      adjunction.right_triangle_components, comp_id],
  apply (X.unit_assoc _).symm,
end

instance comparison_full [full R] [is_right_adjoint R] :
  full (monad.comparison (adjunction.of_right_adjoint R)) :=
{ preimage := λ X Y f, R.preimage f.f }

end reflective

-- It is possible to do this computably since the construction gives the data of the inverse, not
-- just the existence of an inverse on each object.
/-- Any reflective inclusion has a monadic right adjoint.
    cf Prop 5.3.3 of [Riehl][riehl2017] -/
@[priority 100] -- see Note [lower instance priority]
noncomputable instance monadic_of_reflective [reflective R] : monadic_right_adjoint R :=
{ eqv := equivalence.of_fully_faithfully_ess_surj _ }

end category_theory
