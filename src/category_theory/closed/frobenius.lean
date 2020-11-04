import category_theory.adjunction.limits
import category_theory.closed.cartesian
import category_theory.conj

universes v u₁ u₂

namespace category_theory
open category limits
variables {C : Type u₁} [category.{v} C] [has_finite_products C] [cartesian_closed C]
variables {D : Type u₂} [category.{v} D] [has_finite_products D] [cartesian_closed D]
variables (F : C ⥤ D)

class cartesian_closed_functor :=
[preserves_bin_prods : preserves_limits_of_shape (discrete walking_pair) F]
(comparison_iso : ∀ A B, is_iso (exp_comparison F A B))

attribute [instance] cartesian_closed_functor.comparison_iso

variables {F} {L : D ⥤ C}

noncomputable def frobenius_map (A : C) (B : D) (adj : L ⊣ F) : L.obj (F.obj A ⨯ B) ⟶ A ⨯ L.obj B :=
prod_comparison _ _ _ ≫ limits.prod.map (adj.counit.app A) (𝟙 _)

@[reassoc]
lemma frob_naturality {A A' : C} {B B' : D} (adj : L ⊣ F) (f : A ⟶ A') (g : B ⟶ B') :
  frobenius_map A B adj ≫ limits.prod.map f (L.map g) = L.map (limits.prod.map (F.map f) g) ≫ frobenius_map A' B' adj :=
begin
  rw [frobenius_map, frobenius_map, assoc, prod_comparison_natural_assoc],
  apply prod.hom_ext,
  simp only [assoc, limits.prod.map_fst, limits.prod.map_fst_assoc, adjunction.counit_naturality],
  simp only [assoc, limits.prod.map_snd, limits.prod.map_snd_assoc, comp_id, id_comp],
end

@[reassoc]
lemma frob_inv_naturality {A A' : C} {B B' : D} (adj : L ⊣ F) (f : A ⟶ A') (g : B ⟶ B')
  [is_iso (frobenius_map A B adj)]
  [is_iso (frobenius_map A' B' adj)] :
  inv (frobenius_map A B adj) ≫ L.map (limits.prod.map (F.map f) g) =
  limits.prod.map f (L.map g) ≫ inv (frobenius_map A' B' adj) :=
by rw [is_iso.comp_is_iso_eq, assoc, is_iso.inv_comp_eq, frob_naturality]

variables (adj : L ⊣ F) [∀ A B, is_iso (frobenius_map A B adj)]

noncomputable def biject (adj : L ⊣ F) [∀ A B, is_iso (frobenius_map A B adj)]
  {A B : C} {c : D} : (c ⟶ F.obj (B ^^ A)) ≃ (c ⟶ F.obj B ^^ F.obj A) :=
calc (c ⟶ F.obj (B ^^ A)) ≃ (L.obj c ⟶ B ^^ A) : (adj.hom_equiv _ _).symm
     ... ≃ (A ⨯ L.obj c ⟶ B) : ((exp.adjunction A).hom_equiv _ _).symm
     ... ≃ (L.obj (F.obj A ⨯ c) ⟶ B) : iso.hom_congr (as_iso (frobenius_map _ _ adj)).symm (iso.refl _)
     ... ≃ (F.obj A ⨯ c ⟶ F.obj B) : adj.hom_equiv _ _
     ... ≃ (c ⟶ F.obj B ^^ F.obj A) : ((exp.adjunction _).hom_equiv _ _)

-- tidy this up
lemma biject_id {A B : C} [preserves_limits_of_shape (discrete walking_pair) F] :
  biject adj (𝟙 _) = exp_comparison F A B :=
begin
  dsimp [biject, iso.hom_congr, frobenius_map, exp_comparison],
  rw [comp_id],
  change cartesian_closed.curry _ = _,
  congr' 1,
  erw (as_iso (prod_comparison F A ((exp A).obj B))).eq_inv_comp,
  rw adj.hom_equiv_unit,
  erw adj.unit.naturality_assoc,
  dsimp [prod_comparison],
  erw ← F.map_comp,
  rw adjunction.hom_equiv_counit,
  rw adjunction.hom_equiv_counit,
  rw L.map_id,
  rw id_comp,
  dsimp,
  rw prod.lift_map,
  rw prod.lift_map_assoc,
  rw comp_id,
  rw comp_id,
  simp only [functor.map_comp],
  rw ← F.map_comp,
  rw ← F.map_comp,
  rw ← adj.hom_equiv_unit,
  rw adj.hom_equiv_apply_eq,
  rw adj.hom_equiv_counit,
  erw adj.counit.naturality,
  rw ← assoc,
  congr' 1,
  apply prod.hom_ext; simp [← functor.map_comp_assoc],
end

lemma biject_id' {A B : C} [preserves_limits_of_shape (discrete walking_pair) F] :
  𝟙 (F.obj ((exp A).obj B)) = (biject adj).symm (exp_comparison F A B) :=
begin
  rw equiv.eq_symm_apply,
  rw biject_id,
end

lemma biject_natural
  {A B B' : C} {c c' : D} (f : c' ⟶ c) (g : B ⟶ B') (q : c ⟶ F.obj (B ^^ A)) :
f ≫ biject adj q ≫ (exp _).map (F.map g) = biject adj (f ≫ q ≫ F.map ((exp _).map g)) :=
begin
  dsimp [biject, iso.hom_congr],
  rw [comp_id, comp_id],
  rw ← adjunction.hom_equiv_naturality_right,
  rw ← adjunction.hom_equiv_naturality_left,
  erw ← adjunction.hom_equiv_naturality_right,
  rw ← adjunction.hom_equiv_naturality_left,
  rw assoc,
  rw adj.hom_equiv_naturality_left_symm,
  rw adjunction.hom_equiv_naturality_left_symm,
  erw frob_naturality_assoc,
  rw adj.hom_equiv_naturality_right_symm,
  rw adjunction.hom_equiv_naturality_right_symm,
  congr' 4,
  dsimp, simp,
end

lemma biject_natural_left
  {A B : C} {c c' : D} (f : c' ⟶ c) (q : c ⟶ F.obj (B ^^ A)) :
f ≫ biject adj q = biject adj (f ≫ q) :=
by simpa using biject_natural adj f (𝟙 _) q

lemma biject_natural_right
  {A B B' : C} {c : D} (g : B ⟶ B') (q : c ⟶ F.obj (B ^^ A)) :
biject adj q ≫ (exp _).map (F.map g) = biject adj (q ≫ F.map ((exp _).map g)) :=
by simpa using biject_natural adj (𝟙 _) g q

noncomputable def cartesian_closed_of_frobenius_iso : cartesian_closed_functor F :=
{ preserves_bin_prods :=
  begin
    letI := adj.right_adjoint_preserves_limits,
    apply_instance,
  end,
  comparison_iso := λ A B,
  { inv := (biject adj).symm (𝟙 _),
    hom_inv_id' :=
    begin
      rw ← (biject adj).apply_eq_iff_eq,
      rw biject_id _,
      rw ← biject_natural_left,
      rw equiv.apply_symm_apply,
      rw comp_id,
    end,
    inv_hom_id' :=
    begin
      letI := adj.right_adjoint_preserves_limits,
      rw ← biject_id adj,
      rw biject_natural_left,
      rw comp_id,
      rw equiv.apply_symm_apply,
    end } }

-- TODO: If F has a left adjoint L, then F is cartesian closed if and only if
-- L (B ⨯ F A) ⟶ L B ⨯ L F A ⟶ L B ⨯ A
-- is an iso for all A ∈ D, B ∈ C.
-- Corollary: If F has a left adjoint L which preserves finite products, F is cartesian closed iff
-- F is full and faithful.
end category_theory
