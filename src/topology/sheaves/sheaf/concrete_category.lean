import topology.sheaves.sheaf
import category_theory.limits.preserves
import category_theory.limits.types

open category_theory
open category_theory.limits
open topological_space
open opposite
open Top

section

universes v u

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variables {F G : J ⥤ C} (α : F ≅ G)
variables (c : cone F)

def postcompose_hom_equiv (c : cone F) : is_limit ((cones.postcompose α.hom).obj c) ≃ is_limit c :=
begin
  change is_limit ((cones.postcompose_equivalence α).functor.obj c) ≃ _,
  apply is_limit.of_cone_equiv',
end

def postcompose_inv_equiv (c : cone G) : is_limit ((cones.postcompose α.inv).obj c) ≃ is_limit c :=
begin
  change is_limit ((cones.postcompose_equivalence α.symm).functor.obj c) ≃ _,
  apply is_limit.of_cone_equiv',
end

end

section
open sheaf_condition

universes v u

variables {C : Type u} [category.{v} C] [has_products C]
variables {D : Type u} [category.{v} D] [has_products D]
variables (G : C ⥤ D) [preserves_limits G]

section
variables {J : Type v} [small_category J]

def preserves_limits_iso (F : J ⥤ C) [has_limit F] [has_limit (F ⋙ G)] :
  G.obj (limit F) ≅ limit (F ⋙ G) :=
begin
  have := is_limit.unique_up_to_iso (preserves_limit.preserves (limit.is_limit F)) (limit.is_limit (F ⋙ G)),
  exact (cones.forget _).map_iso this,
end

-- TODO @[simp] lemmas

def preserves_product_iso {J : Type v} (f : J → C) [has_product f] [has_product (λ j, G.obj (f j))] :
  G.obj (pi_obj f) ≅ pi_obj (λ j, G.obj (f j)) :=
preserves_limits_iso G (discrete.functor f) ≪≫ has_limit.iso_of_nat_iso (discrete.nat_iso (λ j, iso.refl _))

@[simp, reassoc]
lemma preserves_product_iso_hom {J : Type v} (f : J → C) [has_product f] [has_product (λ j, G.obj (f j))] (j) :
  (preserves_product_iso G f).hom ≫ limit.π _ j = G.map (pi.π f j) :=
begin
  dsimp [preserves_product_iso, preserves_limits_iso, has_limit.iso_of_nat_iso, cones.postcompose, is_limit.unique_up_to_iso, is_limit.lift_cone_morphism],
  simp, dsimp, simp,
end

@[simp, reassoc]
lemma lift_comp_preserves_product_iso_hom {J : Type v} (f : J → C) [has_product f] [has_product (λ j, G.obj (f j))] (P) (g : Π j, P ⟶ f j) :
  G.map (pi.lift g) ≫ (preserves_product_iso G f).hom = pi.lift (λ j, G.map (g j)) :=
begin
  ext,
  simp,
  simp only [←G.map_comp],
  simp,
end


end


variables {X : Top.{v}} (F : presheaf C X)
variables {ι : Type v} (U : ι → opens X)

def bar :
  parallel_pair (left_restriction F U) (right_restriction F U) ⋙ G
    ≅ parallel_pair (left_restriction (F ⋙ G) U) (right_restriction (F ⋙ G) U)
 :=
begin
  fapply nat_iso.of_components,
  intro j,
  cases j,
  exact (preserves_product_iso _ _),
  exact (preserves_product_iso _ _),
  intros j j' f,
  cases j; cases j'; cases f,
  { simp, dsimp, simp, },
  { ext, simp [left_restriction], dsimp, simp, },
  { ext, simp [right_restriction], dsimp, simp, },
  { simp, dsimp, simp, },
end

def foo : G.map_cone (sheaf_condition.fork F U) ≅
  (cones.postcompose (bar G F U).inv).obj (sheaf_condition.fork (F ⋙ G) U) :=
cones.ext (iso.refl _) (λ j,
begin
  dsimp, simp [bar], cases j; dsimp [restriction],
  { rw iso.eq_comp_inv,
    ext,
    simp, },
  { rw iso.eq_comp_inv,
    ext,
    simp [left_restriction],
    dsimp,
    simp,
    simp only [←G.map_comp],
    simp,
  },
end)

end

universes v u

open sheaf_condition

variables {C : Type (u+1)} [large_category C] [concrete_category C]
variables [reflects_isomorphisms (forget C)]
variables [has_limits C] [preserves_limits (forget C)]

variables {X : Top.{u}} (F : presheaf C X)

-- FIXME remove this attribute?
local attribute [-simp] forget_map_eq_coe

def sheaf_condition_in_Type : sheaf_condition F ≃ sheaf_condition (F ⋙ (forget C)) :=
begin
  fsplit,
  { intros S ι U,
    have t1 := S U,
    have t2 := @preserves_limit.preserves _ _ _ _ _ _ _ (forget C) _ _ t1,
    have t3 := is_limit.of_iso_limit t2 (foo _ _ _),
    have t4 := postcompose_inv_equiv _ _ t3,
    exact t4, },
  { intros S ι U,
    let f := equalizer.lift _ (fork_condition F U),
    haveI : is_iso ((forget C).map f) :=
    begin
      let c := sheaf_condition.fork (F ⋙ forget C) U,
      have hc : is_limit c := S U,
      let d := (forget C).map_cone (equalizer.fork (left_restriction F U) (right_restriction F U)),
      have hd : is_limit d := preserves_limit.preserves (limit.is_limit _),
      -- `c` is a limit cone by `S`
      -- `d` is a limit cone because `forget C` preserves limits
      -- `(forget C).map f` is a morphism from `c` to `d`
      -- so it's an isomorphism...
      -- EXCEPT: `c` and `d` don't quite have the same shape yet.
      let d' := (cones.postcompose (bar _ F U).hom).obj d,
      have hd' : is_limit d' := (postcompose_hom_equiv.{u} (bar (forget C) F U) _).symm hd,
      let g : c ⟶ d' :=
      fork.mk_hom ((forget C).map f)
      begin
        dsimp only [c, d, d', f, bar, restriction],
        dunfold fork.ι,
        ext1 j,
        dsimp,
        simp only [category.assoc],
        simp only [←functor.map_comp_assoc],
        simp,
        dsimp, simp [restriction], dsimp, simp,
      end,
      haveI : is_iso g := is_limit.hom_is_iso hc hd' g,
      exact { ..((cones.forget _).map_iso (as_iso g)) },
    end,
    haveI : is_iso f := is_iso_of_reflects_iso f (forget C),
    apply is_limit.of_iso_limit (limit.is_limit _),
    apply iso.symm,
    fapply cones.ext,
    exact (as_iso f),
    rintro ⟨_|_⟩; { dsimp [f], simp, },
  },
  { intros S, apply subsingleton.elim, },
  { intros S, apply subsingleton.elim, },
end
