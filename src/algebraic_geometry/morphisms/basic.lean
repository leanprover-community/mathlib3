/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.AffineScheme
import algebraic_geometry.pullbacks
import category_theory.adjunction.over

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-properties are defined

* `respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and `P f → P (f ≫ e)`, where
  `e` is an isomorphism.
* `stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `stable_under_base_change`: `P` is stable under base change if `P (Y ⟶ S) → P (X ×[S] Y ⟶ X)`.

Special support is also provided for morphism properties defined for `X ⟶ Y` with `Y` affine
(`affine_target_morphism_property`). A morphism `f : X ⟶ Y` is locally `P`
(`target_affine_locally P`) if `P (f ∣_ U)` for each affine open set `U ⊆ Y`. Such a property `P` is
called local (`P.is_local`) if
1. `P` respects iso.
2. If `P` holds for some `f : X ⟶ Y`, `P` holds for `f ∣_ D (r)` for all `r : Γ(Y)`.
3. If `P` holds for `f ∣_ D (r)` for each `r` in a spanning set `s` of `Γ(Y)`, then `P` holds for
  `f`.

If `P` is local, then given a `f : X ⟶ Y`, then TFAE:
1. `f` is locally `P`.
2. `P` holds for all `f ∣_ Uᵢ` for all affine covers `{ Uᵢ }` of `Y`.
3. `P` holds for all `f ∣_ Uᵢ` for some affine cover `{ Uᵢ }` of `Y`.
4. locally `P` holds for all `f ∣_ Uᵢ` for all open covers `{ Uᵢ }` of `Y`.
5. locally `P` holds for all `f ∣_ Uᵢ` for some open cover `{ Uᵢ }` of `Y`.

Also, to check that "locally `P`" is stable under base change, it suffices to check that
  `P (Y ⟶ S) → P (X ×[S] Y ⟶ X)` for affine `S` and `X`.

-/

universe u

open topological_space category_theory category_theory.limits opposite

noncomputable theory

namespace algebraic_geometry

def morphism_property := ∀ ⦃X Y : Scheme⦄ (f : X ⟶ Y), Prop

def affine_target_morphism_property := ∀ ⦃X Y : Scheme⦄ (f : X ⟶ Y) [is_affine Y], Prop

def affine_target_morphism_property.to_property (P : affine_target_morphism_property) :
  morphism_property :=
λ X Y f, ∃ h, @@P f h

lemma affine_target_morphism_property.to_property_apply (P : affine_target_morphism_property)
  {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] :
  P.to_property f ↔ P f := by { delta affine_target_morphism_property.to_property, simp [*] }

def respects_iso (P : morphism_property) :=
  (∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.hom ≫ f)) ∧
  (∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y), P f → P (f ≫ e.hom))

def stable_under_composition (P : morphism_property) :=
  ∀ ⦃X Y Z⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → (P (f ≫ g))

def stable_under_base_change
  (P : morphism_property) : Prop :=
∀ ⦃X Y S : Scheme⦄ (f : X ⟶ S) (g : Y ⟶ S), P g → P (pullback.fst : pullback f g ⟶ X)

lemma stable_under_composition.respects_iso {P : morphism_property}
  (hP : stable_under_composition P) (hP' : ∀ {X Y} (e : X ≅ Y), P e.hom) : respects_iso P :=
⟨λ X Y Z e f hf, hP _ _ (hP' e) hf, λ X Y Z e f hf, hP _ _ hf (hP' e)⟩

lemma respects_iso.cancel_left_is_iso {P : morphism_property}
  (hP : respects_iso P) {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] :
    P (f ≫ g) ↔ P g :=
⟨λ h, by simpa using hP.1 (as_iso f).symm (f ≫ g) h, hP.1 (as_iso f) g⟩

lemma respects_iso.cancel_right_is_iso {P : morphism_property}
  (hP : respects_iso P) {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] :
    P (f ≫ g) ↔ P f :=
⟨λ h, by simpa using hP.2 (as_iso g).symm (f ≫ g) h, hP.2 (as_iso g) f⟩

lemma stable_under_base_change.symmetry {P : morphism_property}
  (hP : stable_under_base_change P) (hP' : respects_iso P) {X Y S : Scheme} (f : X ⟶ S)
  (g : Y ⟶ S) (H : P f) : P (pullback.snd : pullback f g ⟶ Y) :=
begin
  rw [← pullback_symmetry_hom_comp_fst, hP'.cancel_left_is_iso],
  apply hP,
  exact H
end

lemma stable_under_base_change.base_change_obj {P : morphism_property}
  (hP : stable_under_base_change P) (hP' : respects_iso P) {S S' : Scheme} (f : S' ⟶ S)
  (X : over S) (H : P X.hom) : P ((base_change f).obj X).hom :=
hP.symmetry hP' X.hom f H

def pullback.congr {C : Type*} [category C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
  (e₁ : f₁ = f₂) (e₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
    pullback f₁ g₁ ≅ pullback f₂ g₂ :=
as_iso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using e₁) (by simpa using e₂))

@[simp, reassoc]
lemma pullback.congr_hom_fst {C : Type*} [category C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
  (e₁ : f₁ = f₂) (e₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
    (pullback.congr e₁ e₂).hom ≫ pullback.fst = pullback.fst :=
by { delta pullback.congr, simp }

@[simp, reassoc]
lemma pullback.congr_hom_snd {C : Type*} [category C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
  (e₁ : f₁ = f₂) (e₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
    (pullback.congr e₁ e₂).hom ≫ pullback.snd = pullback.snd :=
by { delta pullback.congr, simp }

@[simp, reassoc]
lemma pullback.congr_inv_fst {C : Type*} [category C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
  (e₁ : f₁ = f₂) (e₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
    (pullback.congr e₁ e₂).inv ≫ pullback.fst = pullback.fst :=
by rw [iso.inv_comp_eq, pullback.congr_hom_fst]

@[simp, reassoc]
lemma pullback.congr_inv_snd {C : Type*} [category C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
  (e₁ : f₁ = f₂) (e₂ : g₁ = g₂) [has_pullback f₁ g₁] [has_pullback f₂ g₂] :
    (pullback.congr e₁ e₂).inv ≫ pullback.snd = pullback.snd :=
by rw [iso.inv_comp_eq, pullback.congr_hom_snd]

lemma stable_under_base_change.base_change_map {P : morphism_property}
  (hP : stable_under_base_change P) (hP' : respects_iso P) {S S' : Scheme} (f : S' ⟶ S)
  {X Y : over S} (g : X ⟶ Y) (H : P g.left) : P ((base_change f).map g).left :=
begin
  let e := pullback_right_pullback_fst_iso Y.hom f g.left ≪≫
    pullback.congr (g.w.trans (category.comp_id _)) rfl,
  have : e.inv ≫ pullback.snd = ((base_change f).map g).left,
  { apply pullback.hom_ext; dsimp; simp },
  rw [← this, hP'.cancel_left_is_iso],
  apply hP.symmetry hP',
  exact H
end

lemma stable_under_base_change.pullback_map {P : morphism_property}
  (hP : stable_under_base_change P) (hP' : respects_iso P)
  (hP'' : stable_under_composition P) {S X X' Y Y' : Scheme}
  {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'}
  (h₁ : P i₁) (h₂ : P i₂) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _)
      ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂)) :=
begin
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _)
    ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂) =
      ((pullback_symmetry _ _).hom ≫
      ((base_change _).map (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g')).left) ≫
      (pullback_symmetry _ _).hom ≫
      ((base_change g').map (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f')).left,
  { apply pullback.hom_ext; dsimp; simp },
  rw this,
  apply hP''; rw hP'.cancel_left_is_iso,
  exacts [hP.base_change_map hP' _ (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g') h₂,
    hP.base_change_map hP' _ (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f') h₁],
end

lemma congr_property_morphism_restrict_iff (P : morphism_property) (hP : respects_iso P)
  {X Y : Scheme} (f : X ⟶ Y) {U V : opens Y.carrier} (e : U = V) :
  P (f ∣_ U) ↔ P (f ∣_ V) :=
by subst e

lemma property_iff_of_is_open_immersion (P : morphism_property) (hP : respects_iso P)
  {X Y U : Scheme} (f : X ⟶ Y) (g : U ⟶ Y) [hg : is_open_immersion g] :
  P (pullback.snd : pullback f g ⟶ _) ↔ P (f ∣_ ⟨set.range g.1.base, hg.base_open.open_range⟩) :=
begin
  let V : opens Y.carrier := ⟨set.range g.1.base, hg.base_open.open_range⟩,
  let e := is_open_immersion.iso_of_range_eq g (Y.of_restrict V.open_embedding)
    (by exact subtype.range_coe.symm),
  let t : pullback f g ⟶ pullback f (Y.of_restrict V.open_embedding) :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [category.comp_id, category.id_comp])
      (by rw [category.comp_id, is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac]),
  have : t ≫ (pullback_restrict_iso_restrict f V).hom ≫ f ∣_ V ≫ e.inv = pullback.snd,
  { rw [← cancel_mono g, is_open_immersion.iso_of_range_eq_inv, category.assoc, category.assoc,
      category.assoc, is_open_immersion.lift_fac, ← pullback.condition, morphism_restrict_ι,
      pullback_restrict_iso_restrict_hom_restrict_assoc,
      pullback.lift_fst_assoc, category.comp_id] },
  rw [← this, hP.cancel_left_is_iso, hP.cancel_left_is_iso, hP.cancel_right_is_iso],
end

lemma property_restrict_restrict_iff (P : morphism_property) (hP : respects_iso P)
  {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) (V : opens U) :
  P (f ∣_ U ∣_ V) ↔ P (f ∣_ (U.open_embedding.is_open_map.functor.obj V)) :=
begin
  let : (f ∣_ U ∣_ V) = ((pullback_restrict_iso_restrict (f ∣_ U) V).inv ≫
    (pullback_symmetry _ _).hom ≫ pullback.map _ _ _ _ (𝟙 _)
      ((pullback_restrict_iso_restrict f U).inv ≫ (pullback_symmetry _ _).hom) (𝟙 _)
    ((category.comp_id _).trans (category.id_comp _).symm) (by simpa) ≫
    (pullback_right_pullback_fst_iso _ _ _).hom ≫ (pullback_symmetry _ _).hom) ≫ pullback.snd,
  { simpa },
  rw [this, hP.cancel_left_is_iso, property_iff_of_is_open_immersion _ hP],
  apply congr_property_morphism_restrict_iff P hP,
  ext1,
  dsimp,
  rw [coe_comp, set.range_comp],
  congr,
  exact subtype.range_coe,
end

lemma property_restrict_restrict_basic_open_iff (P : morphism_property) (hP : respects_iso P)
  {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) (r : Y.presheaf.obj (op U)) :
  P (f ∣_ U ∣_ (Y.restrict _).basic_open
    (Y.presheaf.map (eq_to_hom U.open_embedding_obj_top).op r)) ↔ P (f ∣_ Y.basic_open r) :=
begin
  rw property_restrict_restrict_iff _ hP,
  apply congr_property_morphism_restrict_iff _ hP,
  have e := Scheme.preimage_basic_open (Y.of_restrict U.open_embedding) r,
  erw [Scheme.of_restrict_coe_c_app, opens.adjunction_counit_app_self, eq_to_hom_op] at e,
  rw [← (Y.restrict U.open_embedding).basic_open_res_eq _
    (eq_to_hom U.inclusion_map_eq_top).op, ← comp_apply],
  erw ← Y.presheaf.map_comp,
  rw [eq_to_hom_op, eq_to_hom_op, eq_to_hom_map, eq_to_hom_trans],
  erw ← e,
  ext1, dsimp [opens.map, opens.inclusion],
  rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset, subtype.range_coe],
  exact Y.basic_open_subset r
end

def target_affine_locally (P : affine_target_morphism_property) : morphism_property :=
  λ {X Y : Scheme} (f : X ⟶ Y), ∀ (U : Y.affine_opens), @@P (f ∣_ U) U.prop

lemma target_affine_locally_respects_iso {P : affine_target_morphism_property}
  (hP : respects_iso P.to_property) : respects_iso (target_affine_locally P) :=
begin
  split,
  { introv H U,
    rw [morphism_restrict_comp, ← P.to_property_apply, hP.cancel_left_is_iso],
    convert H U,
    rw ← P.to_property_apply },
  { introv H U,
    rw [morphism_restrict_comp, ← P.to_property_apply, hP.cancel_right_is_iso],
    convert H ⟨(opens.map e.hom.val.base).obj U.1, U.2.map_is_iso e.hom⟩,
    rwa ← P.to_property_apply,
    refl }
end

structure affine_target_morphism_property.is_local (P : affine_target_morphism_property) : Prop :=
(respects_iso : respects_iso P.to_property)
(to_basic_open : ∀ {X Y : Scheme} [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj $ op ⊤),
  by exactI P f →
    @@P (f ∣_ (Y.basic_open r)) ((top_is_affine_open Y).basic_open_is_affine _))
(of_basic_open_cover : ∀ {X Y : Scheme} [is_affine Y] (f : X ⟶ Y)
  (s : finset (Y.presheaf.obj $ op ⊤)) (hs : ideal.span (s : set (Y.presheaf.obj $ op ⊤)) = ⊤),
  by exactI (∀ (r : s), @@P (f ∣_ (Y.basic_open r.1))
    ((top_is_affine_open Y).basic_open_is_affine _)) → P f)

lemma target_affine_locally_of_open_cover {P : affine_target_morphism_property}
  (hP : P.is_local)
  {X Y : Scheme} (f : X ⟶ Y) (𝒰 : Y.open_cover) [∀ i, is_affine (𝒰.obj i)]
  (h𝒰 : ∀ i, P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i)) :
    target_affine_locally P f :=
begin
  classical,
  let S := λ i, (⟨⟨set.range (𝒰.map i).1.base, (𝒰.is_open i).base_open.open_range⟩,
    range_is_affine_open_of_open_immersion (𝒰.map i)⟩ : Y.affine_opens),
  apply of_affine_open_cover (λ U, @@P (f ∣_ U.1) U.2) _ _ (set.range S); dsimp only,
  { rw set.eq_univ_iff_forall,
    simp only [set.mem_Union],
    intro x,
    exact ⟨⟨_, ⟨𝒰.f x, rfl⟩⟩, 𝒰.covers x⟩ },
  { rintro ⟨_, i, rfl⟩,
    simp_rw ← P.to_property_apply at ⊢ h𝒰,
    exact (property_iff_of_is_open_immersion _ hP.1 _ _).mp (h𝒰 i) },
  { intros U r h,
    haveI : is_affine _ := U.2,
    have := hP.2 (f ∣_ U.1),
    replace this := this (Y.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op r) h,
    rw ← P.to_property_apply at this ⊢,
    exact (property_restrict_restrict_basic_open_iff _ hP.1 _ _ r).mp this },
  { intros U s hs H,
    haveI : is_affine _ := U.2,
    apply hP.3 (f ∣_ U.1) (s.image (Y.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op)),
    { apply_fun ideal.comap (Y.presheaf.map (eq_to_hom U.1.open_embedding_obj_top.symm).op) at hs,
      rw ideal.comap_top at hs,
      rw ← hs,
      simp only [eq_to_hom_op, eq_to_hom_map, finset.coe_image],
      have : ∀ {R S : CommRing} (e : S = R) (s : set S),
        (by exactI ideal.span (eq_to_hom e '' s) = ideal.comap (eq_to_hom e.symm) (ideal.span s)),
      { intros, subst e, simpa },
      apply this },
    { rintro ⟨r, hr⟩,
      obtain ⟨r, hr', rfl⟩ := finset.mem_image.mp hr,
      simp_rw ← P.to_property_apply at ⊢ H,
      exact (property_restrict_restrict_basic_open_iff _ hP.1 f _ r).mpr (H ⟨r, hr'⟩) } }
end

lemma affine_target_morphism_property.is_local.affine_open_cover_tfae
  {P : affine_target_morphism_property}
  (hP : P.is_local) {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [target_affine_locally P f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)], ∀ (i : 𝒰.J),
      by exactI P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      by exactI P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_affine U] [is_open_immersion g],
      by exactI P (pullback.snd : pullback f g ⟶ U)] :=
begin
  tfae_have : 1 → 4,
  { intros H U g h₁ h₂,
    resetI,
    replace H := H ⟨⟨_, h₂.base_open.open_range⟩,
      range_is_affine_open_of_open_immersion g⟩,
    rw ← P.to_property_apply at H ⊢,
    rwa property_iff_of_is_open_immersion _ hP.1 },
  tfae_have : 4 → 3,
  { intros H 𝒰 h𝒰 i,
    resetI,
    apply H },
  tfae_have : 3 → 2,
  { exact λ H, ⟨Y.affine_cover, infer_instance, H Y.affine_cover⟩ },
  tfae_have : 2 → 1,
  { rintro ⟨𝒰, h𝒰, H⟩, exactI target_affine_locally_of_open_cover hP f 𝒰 H },
  tfae_finish
end

lemma affine_target_morphism_property.is_local.open_cover_tfae
  {P : affine_target_morphism_property}
  (hP : P.is_local) {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [target_affine_locally P f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      target_affine_locally P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      target_affine_locally P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), target_affine_locally P (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      target_affine_locally P (pullback.snd : pullback f g ⟶ U)] :=
begin
  tfae_have : 2 → 1,
  { rintros ⟨𝒰, h𝒰⟩,
    rw (hP.affine_open_cover_tfae f).out 0 1,
    refine ⟨𝒰.bind (λ _, Scheme.affine_cover _), _, _⟩,
    { intro i, dsimp [Scheme.open_cover.bind], apply_instance },
    { intro i,
      specialize h𝒰 i.1,
      rw (hP.affine_open_cover_tfae (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)).out 0 2
        at h𝒰,
      specialize h𝒰 (Scheme.affine_cover _) i.2,
      let e : pullback f ((𝒰.obj i.fst).affine_cover.map i.snd ≫ 𝒰.map i.fst) ⟶
        pullback (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)
          ((𝒰.obj i.fst).affine_cover.map i.snd),
      { refine (pullback_symmetry _ _).hom ≫ _,
        refine (pullback_right_pullback_fst_iso _ _ _).inv ≫ _,
        refine (pullback_symmetry _ _).hom ≫ _,
        refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _; simp },
      rw ← P.to_property_apply at ⊢ h𝒰,
      rw ← hP.1.cancel_left_is_iso e at h𝒰,
      convert h𝒰,
      simp } },
  tfae_have : 1 → 4,
  { intros H U V,
    rw [← P.to_property_apply, property_restrict_restrict_iff _ hP.1],
    convert H ⟨_, V.2.image_is_open_immersion (Y.of_restrict _)⟩,
    rw ← P.to_property_apply,
    refl },
  tfae_have : 4 → 3,
  { intros H 𝒰 i,
    have := H ⟨_, (𝒰.is_open i).base_open.open_range⟩,
    rw property_iff_of_is_open_immersion _ (target_affine_locally_respects_iso hP.1),
    exact H ⟨_, (𝒰.is_open i).base_open.open_range⟩ },
  tfae_have : 3 → 2,
  { exact λ H, ⟨Y.affine_cover, H Y.affine_cover⟩ },
  tfae_have : 4 → 5,
  { intros H U g hg,
    resetI,
    rw property_iff_of_is_open_immersion _ (target_affine_locally_respects_iso hP.1),
    apply H },
  tfae_have : 5 → 4,
  { intros H U,
    erw (target_affine_locally_respects_iso hP.1).cancel_left_is_iso,
    apply H },
  tfae_finish
end

lemma affine_target_morphism_property.is_local.affine_open_cover_iff
  {P : affine_target_morphism_property} (hP : P.is_local)
  {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.open_cover.{u} Y) [h𝒰 : ∀ i, is_affine (𝒰.obj i)] :
  target_affine_locally P f ↔ ∀ i, @@P (pullback.snd : pullback f (𝒰.map i) ⟶ _) (h𝒰 i) :=
⟨λ H, let h := ((hP.affine_open_cover_tfae f).out 0 2).mp H in h 𝒰,
  λ H, let h := ((hP.affine_open_cover_tfae f).out 1 0).mp in h ⟨𝒰, infer_instance, H⟩⟩

lemma affine_target_morphism_property.is_local.open_cover_iff
  {P : affine_target_morphism_property} (hP : P.is_local)
  {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.open_cover.{u} Y) :
  target_affine_locally P f ↔
    ∀ i, target_affine_locally P (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
⟨λ H, let h := ((hP.open_cover_tfae f).out 0 2).mp H in h 𝒰,
  λ H, let h := ((hP.open_cover_tfae f).out 1 0).mp in h ⟨𝒰, H⟩⟩

universe v

/-- An isomorphism `X ⟶ Y` is an open cover of `Y`. -/
 @[simps J obj map]
 def open_cover_of_is_iso {X Y : Scheme.{u}} (f : X ⟶ Y) [is_iso f] :
   Y.open_cover :=
 { J := punit.{v+1},
   obj := λ _, X,
   map := λ _, f,
   f := λ _, punit.star,
   covers := λ x, by { rw set.range_iff_surjective.mpr, { trivial }, rw ← Top.epi_iff_surjective,
     apply_instance } }

lemma affine_target_morphism_property.is_local.affine_target_iff
  {P : affine_target_morphism_property} (hP : P.is_local)
  {X Y : Scheme.{u}} (f : X ⟶ Y) [is_affine Y] :
  target_affine_locally P f ↔ P f :=
begin
  rw hP.affine_open_cover_iff f _,
  swap, { exact open_cover_of_is_iso (𝟙 Y) },
  swap, { intro _, dsimp, apply_instance },
  transitivity (P (pullback.snd : pullback f (𝟙 _) ⟶ _)),
  { exact ⟨λ H, H punit.star, λ H _, H⟩ },
  rw [← P.to_property_apply, ← P.to_property_apply, ← category.comp_id pullback.snd,
    ← pullback.condition, hP.1.cancel_left_is_iso],
end



-- @[simps]
-- def Scheme.open_cover.add {X : Scheme} (𝒰 : X.open_cover) {Y : Scheme} (f : Y ⟶ X)
--   [is_open_immersion f] : X.open_cover :=
-- { J := option 𝒰.J,
--   obj := λ i, option.rec Y 𝒰.obj i,
--   map := λ i, option.rec f 𝒰.map i,
--   f := λ x, some (𝒰.f x),
--   covers := 𝒰.covers,
--   is_open := by rintro (_|_); dsimp; apply_instance }

def affine_target_morphism_property.stable_under_base_change
  (P : affine_target_morphism_property) : Prop :=
∀ ⦃X Y S : Scheme⦄ [is_affine S] [is_affine X] (f : X ⟶ S) (g : Y ⟶ S),
  by exactI P g → P (pullback.fst : pullback f g ⟶ X)

lemma affine_target_morphism_property.is_local.affine_pullback_snd_of_left
  {P : affine_target_morphism_property} (hP : P.is_local) (hP' : P.stable_under_base_change)
  {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [is_affine S] (H : P g) :
  target_affine_locally P (pullback.fst : pullback f g ⟶ X) :=
begin
  rw (hP.affine_open_cover_tfae (pullback.fst : pullback f g ⟶ X)).out 0 1,
  use [X.affine_cover, infer_instance],
  intro i,
  let e := pullback_symmetry _ _ ≪≫ pullback_right_pullback_fst_iso f g (X.affine_cover.map i),
  have : e.hom ≫ pullback.fst = pullback.snd := by simp,
  rw [← this, ← P.to_property_apply, hP.1.cancel_left_is_iso, P.to_property_apply],
  apply hP'; assumption,
end

lemma affine_target_morphism_property.is_local.stable_under_base_change
  {P : affine_target_morphism_property} (hP : P.is_local) (hP' : P.stable_under_base_change) :
  stable_under_base_change (target_affine_locally P) :=
begin
  introv X H,
  rw (hP.open_cover_tfae (pullback.fst : pullback f g ⟶ X)).out 0 1,
  use S.affine_cover.pullback_cover f,
  intro i,
  rw (hP.affine_open_cover_tfae g).out 0 3 at H,
  let e : pullback (pullback.fst : pullback f g ⟶ _) ((S.affine_cover.pullback_cover f).map i) ≅
    _,
  { refine pullback_symmetry _ _ ≪≫ pullback_right_pullback_fst_iso f g _ ≪≫
      _ ≪≫
      (pullback_right_pullback_fst_iso (S.affine_cover.map i) g
        (pullback.snd : pullback f (S.affine_cover.map i) ⟶ _)).symm,
    exact as_iso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _)
      (by simpa using pullback.condition) (by simp)) },
  have : e.hom ≫ pullback.fst = pullback.snd := by simp,
  rw [← this, (target_affine_locally_respects_iso hP.1).cancel_left_is_iso],
  apply hP.affine_pullback_snd_of_left hP',
  rw [← pullback_symmetry_hom_comp_snd, ← P.to_property_apply,
    hP.1.cancel_left_is_iso, P.to_property_apply],
  apply H
end


end algebraic_geometry
