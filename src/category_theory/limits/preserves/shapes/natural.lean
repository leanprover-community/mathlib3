/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes
import category_theory.is_connected
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.preserves.shapes.terminal

/-!
# Preserving limits from naturality

The definition of `G : C ⥤ D` preserving limits of shape `J` can equivalently be stated as:
for any `F : J ⥤ C`, the canonical morphism `G.obj (limit F) ⟶ limit (G ⋙ F)` is an isomorphism.
Note that this morphism is natural in `F`.
However in certain cases, to show `G` preserves limits of shape `J`, it suffices to show there are
natural isomorphisms `G.obj (limit F) ⟶ limit (G ⋙ F)`: in particular these might not be the
canonical isomorphisms.
For instance, there are cases where the natural isomorphisms are not unique, but their mere
existence is enough to establish that the canonical morphism is isomorphic.

At the moment, this file shows only a special case (Theorem 3.3 of [Winskel]):
If `G` preserves the terminal object and there are natural isomorphisms `G (X ⨯ Y) ≅ G X ⨯ G Y`,
then `G` preserves binary products.

## References

* [Winskel] https://www.cl.cam.ac.uk/~gw104/preservation.pdf
-/

noncomputable theory

universes v u₁ u₂

namespace category_theory
open category limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

namespace preserves_connected

variables {J : Type v} [small_category J] [is_connected J]

@[simps {rhs_md := semireducible}]
def same_cones {c : C} : yoneda.obj c ≅ ((functor.const J).obj c).cones :=
nat_iso.of_components
  (λ d, (equiv_of_fully_faithful (functor.const J : C ⥤ _)).to_iso)
  (λ d d' f, rfl)

instance constant_has_limit {c : C} : has_limit ((functor.const J).obj c) :=
has_limit.mk ⟨_, is_limit.of_nat_iso same_cones⟩

def limit_constant_iso (c : C) : limit ((functor.const J).obj c) ≅ c :=
limit.iso_limit_cone ⟨_, is_limit.of_nat_iso same_cones⟩

-- Note the LHS does not depend on `j`, so this shouldn't be a simp lemma
lemma limit_constant_iso_hom {c : C} (j : J) :
  (limit_constant_iso c).hom = limit.π ((functor.const J).obj c) j :=
nat_trans_from_is_connected _ (classical.arbitrary J) j

@[reassoc, simp]
lemma limit_constant_iso_inv (c : C) (j : J) :
  (limit_constant_iso c).inv ≫ limit.π ((functor.const J).obj c) j = 𝟙 c :=
limit.lift_π _ _

variables [has_limits_of_shape J C] [has_limits_of_shape J D]

def preserves_of_shape_of_natural_iso (θ : Π (K : J ⥤ C), G.obj (limit K) ≅ limit (K ⋙ G))
  (hθ : ∀ {K K'} α, (θ K).hom ≫ lim_map (whisker_right α G) = G.map (lim_map α) ≫ (θ K').hom) :
  preserves_limits_of_shape J G :=
{ preserves_limit := λ K,
  { preserves := λ c t,
    begin
      apply (limit.is_limit (K ⋙ G)).of_point_iso,
      let i₂ : limit ((functor.const J).obj c.X) ≅ limit K :=
        limit_constant_iso c.X ≪≫ t.cone_point_unique_up_to_iso (limit.is_limit _),
      have q : i₂.hom = lim_map c.π,
      { ext j,
        simp [limit_constant_iso_hom j] },
      let i₁ : (functor.const J).obj (G.obj c.X) ≅ (functor.const J).obj c.X ⋙ G :=
        nat_iso.of_components (λ _, iso.refl _) (by tidy),
      let i := (limit_constant_iso (G.obj c.X)).symm ≪≫ has_limit.iso_of_nat_iso i₁,
      have z : limit.lift (K ⋙ G) (G.map_cone c) = i.hom ≫ lim_map (whisker_right c.π G : _),
      { ext1,
        simp [limit_constant_iso_inv_assoc (G.obj c.X)] },
      specialize hθ c.π,
      rw ← iso.eq_inv_comp at hθ,
      dsimp,
      rw [z, hθ, ← q],
      apply_instance,
    end } }

end preserves_connected

namespace preserves_pair

variables [has_finite_products C] [has_finite_products D]
variables [preserves_limit (functor.empty _) G]

@[simps]
def left_unit (X : C) {T : C} (hT : is_terminal T) : T ⨯ X ≅ X :=
{ hom := limits.prod.snd,
  inv := prod.lift (hT.from X) (𝟙 X),
  hom_inv_id' := prod.hom_ext (hT.hom_ext _ _) (by simp) }

@[simps]
def right_unit (X : C) {T : C} (hT : is_terminal T) : X ⨯ T ≅ X :=
{ hom := limits.prod.fst,
  inv := prod.lift (𝟙 X) (hT.from X),
  hom_inv_id' := prod.hom_ext (by simp) (hT.hom_ext _ _) }

/--
If we have natural isomorphisms `G (X ⨯ Y) ≅ G X ⨯ G Y` and `G` preserves the terminal objects,
then `G` preserves binary products. In particular, the isomorphisms do not need to be the canonical
isomorphisms, but using the terminal object we can show binary products are preserved.

Proof is taken from Theorem 3.3 of [Winskel].
-/
def preserves_pair_of_natural_isomorphism {X Y : C} (s : Π X Y, G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y)
  (w : ∀ {X X' Y Y'} (f) (g), (s X Y).hom ≫ limits.prod.map (G.map f) (G.map g) = G.map (limits.prod.map f g) ≫ (s X' Y').hom) :
  preserves_limit (pair X Y) G :=
begin
  refine preserves_limit_of_preserves_limit_cone (prod_is_prod _ _) _,
  apply (binary_fan_map_cone_limit _ _ _).symm _,
  -- This isomorphism is the main idea of the proof: we use an isomorphism which is (in general)
  -- not the identity isomorphism, but it gives nice naturality
  let s₁ : G.obj X ≅ G.obj X,
  { apply _ ≪≫ s X (⊤_ C) ≪≫ _,
    { apply G.map_iso (right_unit _ terminal_is_terminal).symm },
    { apply right_unit _ (preserves_terminal.is_limit_of_has_terminal_of_preserves_limit G) } },
  let s₂ : G.obj Y ≅ G.obj Y,
  { apply _ ≪≫ s (⊤_ C) Y ≪≫ _,
    { apply G.map_iso (left_unit _ terminal_is_terminal).symm },
    { apply left_unit _ (preserves_terminal.is_limit_of_has_terminal_of_preserves_limit G) } },
  have hs₁ : (s X Y).hom ≫ limits.prod.fst = G.map limits.prod.fst ≫ s₁.hom,
  { have := w (𝟙 X) (terminal.from Y) =≫ limits.prod.fst,
    simp only [functor.map_id, assoc, comp_id, limits.prod.map_fst] at this,
    change _ = _ ≫ G.map (right_unit X terminal_is_terminal).inv ≫ _ ≫ _,
    rw [this, ← G.map_comp_assoc],
    congr' 2,
    rw iso.eq_comp_inv,
    simp },
  have hs₂ : (s X Y).hom ≫ limits.prod.snd = G.map limits.prod.snd ≫ s₂.hom,
  { have := w (terminal.from X) (𝟙 Y) =≫ limits.prod.snd,
    simp only [functor.map_id, assoc, limits.prod.map_snd, comp_id] at this,
    change _ = _ ≫ G.map (left_unit _ terminal_is_terminal).inv ≫ _ ≫ _,
    rw [this, ← G.map_comp_assoc],
    congr' 2,
    rw iso.eq_comp_inv,
    simp },
  refine is_limit.of_iso_limit
            ((is_limit.postcompose_inv_equiv _ _).symm
              (prod_is_prod (G.obj X) (G.obj Y))) _,
  { apply discrete.nat_iso _,
    intro j,
    cases j,
    { apply s₁ },
    { apply s₂ } },
  { symmetry,
    refine cones.ext (s _ _) _,
    rintro (_ | _),
    { change G.map _ = (s X Y).hom ≫ limits.prod.fst ≫ s₁.inv,
      rw [reassoc_of hs₁, iso.hom_inv_id, comp_id] },
    { change G.map _ = _ ≫ limits.prod.snd ≫ s₂.inv,
      rw [reassoc_of hs₂, iso.hom_inv_id, comp_id] } }
end

end preserves_pair
end category_theory
