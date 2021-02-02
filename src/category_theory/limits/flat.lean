import category_theory.limits.filtered_colimit_commutes_finite_limit2
import category_theory.elements
import category_theory.functor_category
import category_theory.limits.preserves.limits
import category_theory.limits.yoneda
import category_theory.limits.creates

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

def is_set_flat (F : C ⥤ Type v₂) := is_filtered F.elementsᵒᵖ

variable (C)

@[derive category]
def flat := {F : C ⥤ Type v₂ // is_set_flat F}

def flat_to_functors : flat C ⥤ (C ⥤ Type v₂) := full_subcategory_inclusion _

-- example {C : Type v₂} [small_category C] : has_limits (C ⥤ Type v₂) := infer_instance

def six_three_six {C : Type v₂} [small_category C] {D : Type v₂} [small_category D] [is_filtered D]
  (H : D ⥤ C ⥤ Type v₂)
  {c : cocone H} (t : is_colimit c)
  (hD : ∀ d, is_set_flat (H.obj d)) : is_set_flat c.X :=
{ nonempty :=
  begin
    haveI : nonempty D := is_filtered.nonempty,
    inhabit D,
    obtain ⟨t⟩ := (hD (default D)).nonempty,
    refine ⟨op ⟨(unop t).1, (c.ι.app (default D)).app _ (unop t).2⟩⟩,
  end,
  cocone_objs :=
  begin
    intros Aa Bb,
    op_induction Aa,
    op_induction Bb,
    cases Aa with A a,
    cases Bb with B b,
    let t' : is_colimit (((evaluation C _).obj A).map_cocone c) := is_colimit_of_preserves _ t,
    rcases types.jointly_surjective _ t' a with ⟨d, a' : (H.obj _).obj _, ha' : (c.ι.app d).app A a' = a⟩,
    let t'' : is_colimit (((evaluation C _).obj B).map_cocone c) := is_colimit_of_preserves _ t,
    rcases types.jointly_surjective _ t'' b with ⟨d', (b' : (H.obj _).obj _), hb' : (c.ι.app d').app B b' = b⟩,
    rcases is_filtered_or_empty.cocone_objs d d' with ⟨d'', f, g, ⟨⟩⟩,
    let a'' := (H.map f).app A a',
    have ha'' : (c.ι.app d'').app A a'' = a,
    { rw ←c.w f at ha',
      apply ha' },
    let b'' := (H.map g).app B b',
    have hb'' : (c.ι.app d'').app B b'' = b,
    { rw ←c.w g at hb',
      apply hb' },
    clear_value a'' b'',
    clear ha' hb' a' b' f g d d' t' t'',
    subst ha'',
    subst hb'',
    rename d'' d,
    rename a'' a',
    rename b'' b',
    have cof := (hD d).cocone_objs,
    rcases cof (op ⟨_, a'⟩) (op ⟨_, b'⟩) with ⟨Cc, u, v, ⟨⟩⟩,

    -- Manually do the op_induction/cases on Cc
    let C' := Cc.unop.1,
    let c' : (H.obj _).obj C' := Cc.unop.2,
    have : Cc = op ⟨C', c'⟩,
    { simp },
    clear_value C' c',
    subst this,

    have ha' : (H.obj _).map u.unop.1 c' = a' := u.unop.2,
    have hb' : (H.obj _).map v.unop.1 c' = b' := v.unop.2,
    have : c.X.obj C' := (c.ι.app d).app C' c',
    refine ⟨op ⟨_, (c.ι.app d).app C' c'⟩,
            has_hom.hom.op ⟨u.unop.1, _⟩,
            has_hom.hom.op ⟨v.unop.1, _⟩, ⟨⟩⟩,
    { change ((c.ι.app d).app C' ≫ c.X.map u.unop.1) c' = (c.ι.app d).app A a',
      have : _ = (c.ι.app d).app C' ≫ c.X.map u.unop.val := (c.ι.app d).naturality u.unop.1,
      rw ← this,
      change (c.ι.app d).app A ((H.obj d).map u.unop.1 c') = (c.ι.app d).app A a',
      apply congr_arg _ ha' },
    { change ((c.ι.app d).app C' ≫ c.X.map v.unop.1) c' = (c.ι.app d).app B b',
      have : _ = (c.ι.app d).app C' ≫ c.X.map v.unop.val := (c.ι.app d).naturality v.unop.1,
      rw ← this,
      change (c.ι.app d).app B ((H.obj d).map v.unop.1 c') = (c.ι.app d).app B b',
      apply congr_arg _ hb' },
  end,
  cocone_maps :=
  begin
    intros Bb Aa u' v',
    let A := Aa.unop.1,
    let a : c.X.obj A := Aa.unop.2,
    let B := Bb.unop.1,
    let b : c.X.obj B := Bb.unop.2,
    let u : A ⟶ B := u'.unop.1,
    let v : A ⟶ B := v'.unop.1,
    have hu : c.X.map u a = b := u'.unop.2,
    have hv : c.X.map v a = b := v'.unop.2,

    let t' : is_colimit (((evaluation C _).obj A).map_cocone c) := is_colimit_of_preserves _ t,
    rcases types.jointly_surjective _ t' a with ⟨d, a' : (H.obj _).obj _, ha' : (c.ι.app d).app A a' = a⟩,
    let t'' : is_colimit (((evaluation C _).obj B).map_cocone c) := is_colimit_of_preserves _ t,
    rcases types.jointly_surjective _ t'' b with ⟨d', (b' : (H.obj _).obj _), hb' : (c.ι.app d').app B b' = b⟩,
    rcases is_filtered_or_empty.cocone_objs d d' with ⟨d'', f, g, ⟨⟩⟩,
    let a'' := (H.map f).app A a',
    have ha'' : (c.ι.app d'').app A a'' = a,
    { rw ←c.w f at ha',
      apply ha' },
    let b'' := (H.map g).app B b',
    have hb'' : (c.ι.app d'').app B b'' = b,
    { rw ←c.w g at hb',
      apply hb' },
    clear_value a'' b'',
    clear' a' b' ha' hb' t' f g d d',
    rename [d'' d, a'' a', b'' b', ha'' ha', hb'' hb'],
    have q : ((H.obj d).map u ≫ (c.ι.app d).app B) a' = ((H.obj d).map v ≫ (c.ι.app d).app B) a',
    { rw [(c.ι.app d).naturality, (c.ι.app d).naturality, types_comp_apply, types_comp_apply, ha'],
      change c.X.map u a = c.X.map v a,
      rw [hu, hv] },
    rw [types_comp_apply, types_comp_apply] at q,
    -- have : (c.ι.app d).app _ = _,
    have : (c.ι.app d).app B ((H.obj d).map u a') = (c.ι.app d).app B ((H.obj d).map v a') ↔ _ :=
      types.filtered_colimit.is_colimit_eq_iff' _ t'',
    dsimp at this,
    rw this at q,
    rcases q with ⟨d', dh, q⟩,
    let b'' := (H.map dh).app B ((H.obj d).map u a'),
    have : (H.obj d').map u ((H.map dh).app _ a') = b'',
    { rw ←functor_to_types.naturality },
    have : (H.obj d').map v ((H.map dh).app _ a') = b'',
    { rw ←functor_to_types.naturality, rw ←q },
    let A' : (H.obj d').elementsᵒᵖ := op ⟨A, _⟩,
    let B' : (H.obj d').elementsᵒᵖ := op ⟨B, _⟩,

  end

}

end category_theory
