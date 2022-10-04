
def diagonal_is (P : morphism_property) : morphism_property :=
λ X Y f, P (pullback.diagonal f)

lemma diagonal_is_respects_iso  (P : morphism_property)
  (hP : respects_iso P) : respects_iso (diagonal_is P) :=
begin
  split,
  { introv H,
    delta diagonal_is at *,
    rwa [pullback.diagonal_comp, hP.cancel_left_is_iso, hP.cancel_left_is_iso,
      ← hP.cancel_right_is_iso _ _, ← pullback.condition, hP.cancel_left_is_iso],
    apply_instance },
  { introv H,
    delta diagonal_is at *,
    rwa [pullback.diagonal_comp, hP.cancel_right_is_iso] }
end

lemma diagonal_is_stable_under_composition  (P : morphism_property)
  (hP : stable_under_base_change P) (hP' : respects_iso P) (hP'' : stable_under_composition P) :
  stable_under_composition (diagonal_is P) :=
begin
  introv X h₁ h₂,
  delta diagonal_is at *,
  rw pullback.diagonal_comp,
  apply hP'', { assumption },
  rw hP'.cancel_left_is_iso,
  apply hP.symmetry hP',
  assumption
end

lemma diagonal_is_stable_under_base_change  (P : morphism_property)
  (hP : stable_under_base_change P) (hP' : respects_iso P) :
  stable_under_base_change (diagonal_is P) :=
begin
  introv X h,
  delta diagonal_is at *,
  rw [diagonal_pullback_fst, hP'.cancel_left_is_iso, hP'.cancel_right_is_iso],
  convert hP.base_change_map hP' f _ _; simp; assumption
end

lemma diagonal_is_target_affine_locally_of_open_cover (P : affine_target_morphism_property)
  (hP : P.is_local)
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y)
  [∀ i, is_affine (𝒰.obj i)] (𝒰' : Π i, Scheme.open_cover.{u} (pullback f (𝒰.map i)))
  [∀ i j, is_affine ((𝒰' i).obj j)]
  (h𝒰' : ∀ i j k, P (pullback.map_desc ((𝒰' i).map j) ((𝒰' i).map k) pullback.snd)) :
    diagonal_is (target_affine_locally P) f :=
begin
  refine (hP.affine_open_cover_iff _ _).mpr _,
  { exact ((Scheme.pullback.open_cover_of_base 𝒰 f f).bind (λ i,
      Scheme.pullback.open_cover_of_left_right.{u u} (𝒰' i) (𝒰' i) pullback.snd pullback.snd)) },
  { intro i,
    dsimp at *,
    apply_instance },
  { rintro ⟨i, j, k⟩,
    dsimp,
    convert (hP.1.cancel_left_is_iso
    (pullback_diagonal_map_iso _ _ ((𝒰' i).map j) ((𝒰' i).map k)).inv pullback.snd).mp _,
    swap 3,
    { convert h𝒰' i j k, apply pullback.hom_ext; simp, },
    all_goals
    { apply pullback.hom_ext; simp only [category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc] } }
end

def diagonal_is.affine_property (P : affine_target_morphism_property) :
  affine_target_morphism_property :=
λ X Y f hf, ∀ {U₁ U₂ : Scheme} (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [is_affine U₁] [is_affine U₂]
  [is_open_immersion f₁] [is_open_immersion f₂],
  by exactI P (pullback.map_desc f₁ f₂ f)

lemma diagonal_is.affine_property_respects_iso (P : affine_target_morphism_property)
  (hP : P.respects_iso) :
  (diagonal_is.affine_property P).respects_iso :=
begin
  delta diagonal_is.affine_property,
  split,
  { introv H _ _,
    resetI,
    rw [pullback.map_desc_comp, hP.cancel_left_is_iso, hP.cancel_right_is_iso],
    apply H },
  { introv H _ _,
    resetI,
    rw [pullback.map_desc_comp, hP.cancel_right_is_iso],
    apply H }
end

lemma diagonal_is_affine_property_of_diagonal_is (P : affine_target_morphism_property)
  (hP : P.is_local) {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [is_affine U] [is_open_immersion g] (H : diagonal_is (target_affine_locally P) f) :
    diagonal_is.affine_property P (pullback.snd : pullback f g ⟶ _) :=
begin
  rintros U V f₁ f₂ _ _ _ _,
  resetI,
  replace H := ((hP.affine_open_cover_tfae (pullback.diagonal f)).out 0 3).mp H,
  let g₁ := pullback.map (f₁ ≫ pullback.snd)
    (f₂ ≫ pullback.snd) f f
    (f₁ ≫ pullback.fst)
    (f₂ ≫ pullback.fst) g
    (by rw [category.assoc, category.assoc, pullback.condition])
    (by rw [category.assoc, category.assoc, pullback.condition]),
  let g₂ : pullback f₁ f₂ ⟶ pullback f g := pullback.fst ≫ f₁,
  specialize H g₁,
  rw ← hP.1.cancel_left_is_iso (pullback_diagonal_map_iso f _ f₁ f₂).hom,
  convert H,
  { apply pullback.hom_ext; simp only [category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_fst_assoc, pullback.lift_snd_assoc, category.comp_id,
    pullback_diagonal_map_iso_hom_fst, pullback_diagonal_map_iso_hom_snd], }
end

lemma diagonal_is_affine_property.affine_open_cover_tfae (P : affine_target_morphism_property)
  (hP : P.is_local) {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [diagonal_is (target_affine_locally P) f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)], by exactI
      ∀ (i : 𝒰.J), diagonal_is.affine_property P (pullback.snd : pullback f (𝒰.map i) ⟶ _),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J), by exactI
      diagonal_is.affine_property P (pullback.snd : pullback f (𝒰.map i) ⟶ _),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g], by exactI
      diagonal_is.affine_property P (pullback.snd : pullback f g ⟶ _),
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)]
      (𝒰' : Π i, Scheme.open_cover.{u} (pullback f (𝒰.map i))) [∀ i j, is_affine ((𝒰' i).obj j)],
    by exactI ∀ i j k, P (pullback.map_desc ((𝒰' i).map j) ((𝒰' i).map k) pullback.snd)] :=
begin
  tfae_have : 1 → 4,
  { introv H hU hg, resetI, apply diagonal_is_affine_property_of_diagonal_is; assumption },
  tfae_have : 4 → 3,
  { introv H h𝒰, resetI, apply H },
  tfae_have : 3 → 2,
  { exact λ H, ⟨Y.affine_cover, infer_instance, H Y.affine_cover⟩ },
  tfae_have : 2 → 5,
  { rintro ⟨𝒰, h𝒰, H⟩,
    resetI,
    refine ⟨𝒰, infer_instance, λ _, Scheme.affine_cover _, infer_instance, _⟩,
    intros i j k,
    apply H },
  tfae_have : 5 → 1,
  { rintro ⟨𝒰, _, 𝒰', _, H⟩,
    exactI diagonal_is_target_affine_locally_of_open_cover P hP f 𝒰 𝒰' H, },
  tfae_finish
end

lemma diagonal_is_affine_property.is_local (P : affine_target_morphism_property)
  (hP : P.is_local) : (diagonal_is.affine_property P).is_local :=
affine_target_morphism_property.is_local_of_open_cover_imply
  (diagonal_is.affine_property P)
  (diagonal_is.affine_property_respects_iso P hP.1)
  (λ _ _ f, ((diagonal_is_affine_property.affine_open_cover_tfae P hP f).out 1 3).mp)

lemma diagonal_is_eq_diagonal_is_affine_property (P : affine_target_morphism_property)
  (hP : P.is_local) :
    diagonal_is (target_affine_locally P) = target_affine_locally (diagonal_is.affine_property P) :=
begin
  ext _ _ f,
  exact ((diagonal_is_affine_property.affine_open_cover_tfae P hP f).out 0 1).trans
    ( ((diagonal_is_affine_property.is_local P hP).affine_open_cover_tfae f).out 1 0),
end
