import category_theory.limits.filtered_colimit_commutes_finite_limit2
import category_theory.elements
import category_theory.limits.preserves.limits
import category_theory.limits.yoneda

namespace category_theory
open limits opposite

universes w₁ w₂ v₁ v₂ u₁ u₂

variables (J : Type v₂) [small_category J]
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

noncomputable def my_thm
  (J : Type v₂) [small_category J] [fin_category J]
  {C : Type u₁} [category.{v₂} C]
  (F : C ⥤ Type v₂) (hF : is_filtered F.elementsᵒᵖ) :
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
  have tj : Π j, is_limit (cj j),
  { intro j,
    apply is_limit_of_preserves (coyoneda.obj (op (unop j).fst)) t },
  have tk : Π k, is_colimit (ck k),
  { intro k,
    refine ⟨λ s q, s.ι.app (op ⟨_, q⟩) (𝟙 _), _, _⟩,
    { intros s j,
      op_induction j,
      cases j with X x,
      ext q,
      let X' : F.elementsᵒᵖ := op ⟨X, x⟩,
      let Y' : F.elementsᵒᵖ := (op ⟨K.obj k, F.map q x⟩),
      let α : Y' ⟶ X' := has_hom.hom.op ⟨q, rfl⟩,
      have := s.w α,
      dsimp at this,
      change s.ι.app Y' _ = _,
      rw ← this,
      dsimp,
      simp },
    { intros s m w,
      ext X,
      dsimp,
      rw ← w,
      dsimp,
      simp } },
  let c₁ : cocone (cones_to_functor tj),
  { refine ⟨F.obj c.X, λ j q, F.map q j.unop.2, _⟩,
    { intros j₁ j₂ α,
      ext,
      dsimp at x,
      dsimp,
      rw ← α.unop.2,
      rw ← functor_to_types.map_comp_apply,
      congr' 1,
      let m : (cj j₁).X ⟶ (cj j₂).X := λ z, α.unop.1 ≫ z,
      have : is_limit.map (cj j₁) (tj j₂) (whisker_left K ((my_functor F).map α)) = m,
      { refine (tj j₂).hom_ext _,
        intro j,
        rw is_limit.map_π,
        ext,
        change _ ≫ _ ≫ _ = (_ ≫ _) ≫ _,
        rw category.assoc,
        refl },
      rw this } },
  let c₂ : cone (cocones_to_functor tk),
  { apply limit.cone (cocones_to_functor tk) },
  let t₁ : is_colimit c₁,
  { refine ⟨λ s q, _, _, _⟩,
    { apply s.ι.app (op ⟨_, q⟩) (𝟙 _) },
    { intros s j,
      op_induction j,
      cases j with X x,
      ext q,
      dsimp,
      let X' : F.elementsᵒᵖ := op ⟨X, x⟩,
      let Y' : F.elementsᵒᵖ := (op ⟨_, F.map q x⟩),
      let α : Y' ⟶ X' := has_hom.hom.op ⟨q, rfl⟩,
      rw ← s.w α,
      dsimp,
      congr' 1,
      have : is_limit.map (cj Y') (tj X') (whisker_left K ((my_functor F).map α)) = (λ z, q ≫ z),
      { apply (tj X').hom_ext,
        intro j,
        rw is_limit.map_π,
        ext z,
        dsimp [my_functor],
        simp },
      rw this,
      simp },
    { intros s m w,
      ext q,
      rw ← w,
      dsimp,
      simp, } },
  let t₂ : is_limit c₂ := limit.is_limit _,
  let q : cocones_to_functor tk ≅ K ⋙ F,
  { refine nat_iso.of_components (λ X, iso.refl _) _,
    intros X Y f,
    dsimp,
    rw [category.id_comp, category.comp_id],
    apply (tk X).hom_ext,
    intro j,
    rw is_colimit.ι_map,
    ext q,
    dsimp [alt_cocone, my_functor],
    simp, },
  let i₂ := has_limit.iso_of_nat_iso q,
  let i₃ : F.obj c.X ≅ limit (K ⋙ F) := filtered_colimit_finite_limit_iso Γ tj tk t₁ t₂ ≪≫ i₂,
  apply is_limit.of_point_iso (limit.is_limit (K ⋙ F)),
  dsimp,
  have : limit.lift (K ⋙ F) (F.map_cone c) = i₃.hom,
  { apply limit.hom_ext,
    intro j,
    rw limit.lift_π,
    dsimp,
    change _ = (_ ≫ _) ≫ _,
    rw category.assoc,
    simp only [iso.refl_hom, category.comp_id, nat_iso.of_components.hom_app,
      has_limit.iso_of_nat_iso_hom_π],
    apply t₁.hom_ext,
    intro k,
    change _ = _ ≫ _ ≫ c₂.π.app j,
    rw ι_colimit_to_limit_π,
    ext q,
    dsimp,
    simp, },
  rw this,
  apply is_iso.of_iso,
end

end category_theory
