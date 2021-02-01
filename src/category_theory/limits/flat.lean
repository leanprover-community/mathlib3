import category_theory.limits.filtered_colimit_commutes_finite_limit2
import category_theory.elements
import category_theory.limits.preserves.limits

namespace category_theory
open limits opposite

universes w₁ w₂ v₁ v₂ u₁ u₂

variables (J : Type v₁) [small_category J]
variables {C : Type u₁} [category.{v₂} C]
variables (F : C ⥤ Type v₂) (hF : is_filtered F.elementsᵒᵖ)

-- set_option pp.universes true

@[simps {rhs_md := semireducible}]
def my_functor (F : C ⥤ Type v₂) : F.elementsᵒᵖ ⥤ C ⥤ Type v₂ :=
functor.op (category_of_elements.π F) ⋙ coyoneda

@[simps]
def alt_cocone (F : C ⥤ Type v₂) :
  cocone (my_functor F) :=
{ X := F,
  ι :=
  { app := λ p,
    { app := λ Y f, F.map f p.unop.2,
      naturality' := λ Y₁ Y₂ g,
      begin
        ext f,
        apply functor_to_types.map_comp_apply F f g,
      end },
    naturality' := λ p₁ p₂ α,
    begin
      ext X x,
      change F.map (α.unop.1 ≫ x) _ = F.map _ _,
      rw [functor_to_types.map_comp_apply F, α.unop.2],
    end } }

def alt_colimit (F : C ⥤ Type v₂) :
  is_colimit (alt_cocone F) :=
{ desc := λ s,
  { app := λ X t, (s.ι.app (op ⟨X, t⟩)).app _ (𝟙 _),
    naturality' :=
    begin
      intros X Y f,
      ext t,
      let X' : F.elementsᵒᵖ := op ⟨X, t⟩,
      let Y' : F.elementsᵒᵖ := op ⟨Y, F.map f t⟩,
      let f' : Y' ⟶ X' := has_hom.hom.op ⟨_, rfl⟩,
      change (s.ι.app Y').app _ (𝟙 Y) = s.X.map f ((s.ι.app X').app _ _),
      rw ← s.w f',
      change (s.ι.app X').app Y (f ≫ 𝟙 Y) = ((s.ι.app X').app X ≫ s.X.map f) (𝟙 X),
      rw category.comp_id,
      rw ← (show _ = (s.ι.app X').app X ≫ s.X.map f, from (s.ι.app X').naturality f),
      change _ = (s.ι.app X').app Y (𝟙 X ≫ f),
      rw category.id_comp f,
    end },
  fac' := λ s j,
  begin
    op_induction j,
    cases j with X x,
    ext Y f,
    let X' : F.elementsᵒᵖ := op ⟨X, x⟩,
    let Y' : F.elementsᵒᵖ := op ⟨Y, F.map f x⟩,
    let f' : Y' ⟶ X' := has_hom.hom.op ⟨_, rfl⟩,
    change (s.ι.app Y').app Y (𝟙 Y) = (s.ι.app X').app Y f,
    rw ← s.w f',
    dsimp,
    simp,
  end,
  uniq' :=  λ s m w,
  begin
    ext X x,
    change m.app X x = (s.ι.app (op ⟨X, x⟩)).app X (𝟙 X),
    rw ← w (op ⟨X, x⟩),
    dsimp,
    simp,
  end }

def my_thm (hF : is_filtered F.elementsᵒᵖ) :
  preserves_limits_of_shape J F :=
begin
  split,
  intro K,
  split,
  intros c t,
  let Γ : F.elementsᵒᵖ ⥤ J ⥤ Type v₂ := my_functor F ⋙ (whiskering_left J C _).obj K,
  let cj : Π (j : (F.elements)ᵒᵖ), cone (Γ.obj j) :=
    λ j, ((my_functor F).obj j).map_cone c,
  let ck : Π (k : J), cocone (Γ.flip.obj k) :=
    λ j, ((evaluation C (Type v₂)).obj (K.obj j)).map_cocone (alt_cocone F),
  let tj : Π j, is_limit (cj j),
  { intro j,
    apply is_limit_of_preserves _ t,
    dsimp [my_functor],
  },
  -- have := filtered_colimit_finite_limit_iso Γ,
  -- have := limits.colimit_limit_to_limit_colimit_is_iso θ,
end

end category_theory
