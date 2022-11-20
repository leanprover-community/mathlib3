/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.shapes.comm_sq
import category_theory.limits.shapes.strict_initial
import category_theory.limits.shapes.types
import topology.category.Top.limits
import category_theory.limits.functor_category
import category_theory.limits.preserves.finite
import category_theory.limits.preserves.shapes.pullbacks
/-!

# Extensive categories

## Main definitions
- `category_theory.is_van_kampen_colimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.
- `category_theory.finitary_extensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `category_theory.has_strict_initial_objects_of_finitary_extensive`: The initial object
  in extensive categories is strict.
- `category_theory.finitary_extensive.mono_inr_of_is_colimit`: Coproduct injections are monic in
  extensive categories.
- `category_theory.binary_cofan.is_pullback_initial_to_of_is_van_kampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `category_theory.types.finitary_extensive`: The category of types is extensive.

## TODO

Show that the following are finitary extensive:
- the categories of sheaves over a site
- `Scheme`
- `AffineScheme` (`CommRingᵒᵖ`)

## References
- https://ncatlab.org/nlab/show/extensive+category
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]

-/

open category_theory.limits

namespace category_theory

universes v' u' v u v'' u''

variables {J : Type v'} [category.{u'} J] {C : Type u} [category.{v} C]
variables {D : Type u''} [category.{v''} D]


/-- A natural transformation is equifibered if every commutative square of the following form is
a pullback.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
def nat_trans.equifibered {F G : J ⥤ C} (α : F ⟶ G) : Prop :=
∀ ⦃i j : J⦄ (f : i ⟶ j), is_pullback (F.map f) (α.app i) (α.app j) (G.map f)

lemma nat_trans.equifibered_of_is_iso {F G : J ⥤ C} (α : F ⟶ G) [is_iso α] : α.equifibered :=
λ _ _ f, is_pullback.of_vert_is_iso ⟨nat_trans.naturality _ f⟩

lemma nat_trans.equifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H}
  (hα : α.equifibered) (hβ : β.equifibered) : (α ≫ β).equifibered :=
λ i j f, (hα f).paste_vert (hβ f)

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is universal if it is stable under pullbacks. -/
def is_universal_colimit {F : J ⥤ C} (c : cocone F) : Prop :=
∀ ⦃F' : J ⥤ C⦄ (c' : cocone F') (α : F' ⟶ F) (f : c'.X ⟶ c.X)
  (h : α ≫ c.ι = c'.ι ≫ (functor.const J).map f) (hα : α.equifibered),
  (∀ j : J, is_pullback (c'.ι.app j) (α.app j) f (c.ι.app j)) → nonempty (is_colimit c')

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is van Kampen if for every cocone `c'` over the
pullback of the diagram `F' : J ⥤ C'`, `c'` is colimiting iff `c'` is the pullback of `c`.

TODO: Show that this is iff the functor `C ⥤ Catᵒᵖ` sending `x` to `C/x` preserves it.
TODO: Show that this is iff the inclusion functor `C ⥤ Span(C)` preserves it.
-/
def is_van_kampen_colimit {F : J ⥤ C} (c : cocone F) : Prop :=
∀ ⦃F' : J ⥤ C⦄ (c' : cocone F') (α : F' ⟶ F) (f : c'.X ⟶ c.X)
  (h : α ≫ c.ι = c'.ι ≫ (functor.const J).map f) (hα : α.equifibered),
  nonempty (is_colimit c') ↔ ∀ j : J, is_pullback (c'.ι.app j) (α.app j) f (c.ι.app j)

lemma is_van_kampen_colimit.is_universal {F : J ⥤ C} {c : cocone F} (H : is_van_kampen_colimit c) :
  is_universal_colimit c :=
λ _ c' α f h hα, (H c' α f h hα).mpr

/-- A van Kampen colimit is a colimit. -/
noncomputable
def is_van_kampen_colimit.is_colimit {F : J ⥤ C} {c : cocone F} (h : is_van_kampen_colimit c) :
  is_colimit c :=
begin
  refine ((h c (𝟙 F) (𝟙 c.X : _) (by rw [functor.map_id, category.comp_id, category.id_comp])
    (nat_trans.equifibered_of_is_iso _)).mpr $ λ j, _).some,
  haveI : is_iso (𝟙 c.X) := infer_instance,
  exact is_pullback.of_vert_is_iso ⟨by erw [nat_trans.id_app, category.comp_id, category.id_comp]⟩,
end

lemma is_initial.is_van_kampen_colimit [has_strict_initial_objects C] {X : C} (h : is_initial X) :
  is_van_kampen_colimit (as_empty_cocone X) :=
begin
  intros F' c' α f hf hα,
  have : F' = functor.empty C := by apply functor.hext; rintro ⟨⟨⟩⟩,
  subst this,
  haveI := h.is_iso_to f,
  refine ⟨by rintro _ ⟨⟨⟩⟩, λ _,
    ⟨is_colimit.of_iso_colimit h (cocones.ext (as_iso f).symm $ by rintro ⟨⟨⟩⟩)⟩⟩
end

lemma nat_trans.equifibered.whisker_right {F G : J ⥤ C} {α : F ⟶ G} (hα : α.equifibered)
  (H : C ⥤ D) [preserves_limits_of_shape walking_cospan H] : (whisker_right α H).equifibered :=
λ i j f, (hα f).map H

lemma is_van_kampen_colimit.of_iso {F : J ⥤ C} {c c' : cocone F} (H : is_van_kampen_colimit c)
  (e : c ≅ c') : is_van_kampen_colimit c' :=
begin
  intros F' c'' α f h hα,
  have : c'.ι ≫ (functor.const J).map e.inv.hom = c.ι,
  { ext j, exact e.inv.2 j },
  rw H c'' α (f ≫ e.inv.1) (by rw [functor.map_comp, ← reassoc_of h, this]) hα,
  apply forall_congr,
  intro j,
  conv_lhs { rw [← category.comp_id (α.app j)] },
  haveI : is_iso e.inv.hom := functor.map_is_iso (cocones.forget _) e.inv,
  exact (is_pullback.of_vert_is_iso ⟨by simp⟩).paste_vert_iff (nat_trans.congr_app h j).symm
end

lemma is_van_kampen_colimit.precompose_iso {F G : C ⥤ D} {c : cocone G}
  (h : is_van_kampen_colimit c)
  (η : F ⟶ G) [is_iso η] : is_van_kampen_colimit ((cocones.precompose η).obj c) :=
begin
  intros F' c' α f e hα,
  rw h c' (α ≫ η) f ((category.assoc _ _ _).trans e) (hα.comp $ nat_trans.equifibered_of_is_iso η),
  apply forall_congr (λ j, _),
  conv_lhs { rw ← category.comp_id f },
  refine is_pullback.paste_vert_iff _ _,
  { exact is_pullback.of_vert_is_iso ⟨category.comp_id _⟩ },
  { exact nat_trans.congr_app e.symm j }
end

lemma is_van_kampen_colimit.of_precompose_iso {F G : C ⥤ D} (c : cocone G)
  (η : F ⟶ G) [is_iso η]  (h : is_van_kampen_colimit ((cocones.precompose η).obj c))
  : is_van_kampen_colimit c :=
begin
  apply is_van_kampen_colimit.of_iso (h.precompose_iso $ inv η),
  exact cocones.ext (iso.refl c.X) (λ j, by { dsimp, simp })
end

section extensive

variables {X Y : C}

/--
A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen.

TODO: Show that this is iff all finite coproducts are van Kampen. -/
class finitary_extensive (C : Type u) [category.{v} C] : Prop :=
[has_finite_coproducts : has_finite_coproducts C]
(van_kampen' : ∀ {X Y : C} (c : binary_cofan X Y), is_colimit c → is_van_kampen_colimit c)

attribute [priority 100, instance] finitary_extensive.has_finite_coproducts

lemma finitary_extensive.van_kampen [finitary_extensive C] {F : discrete walking_pair ⥤ C}
  (c : cocone F) (hc : is_colimit c) : is_van_kampen_colimit c :=
begin
  let X := F.obj ⟨walking_pair.left⟩, let Y := F.obj ⟨walking_pair.right⟩,
  have : F = pair X Y,
  { apply functor.hext, { rintros ⟨⟨⟩⟩; refl }, { rintros ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩; simpa } },
  clear_value X Y, subst this,
  exact finitary_extensive.van_kampen' c hc
end

lemma map_pair_equifibered {F F' : discrete walking_pair ⥤ C} (α : F ⟶ F') : α.equifibered :=
begin
  rintros ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩,
  all_goals { dsimp, simp only [discrete.functor_map_id],
    exact is_pullback.of_horiz_is_iso ⟨by simp only [category.comp_id, category.id_comp]⟩ }
end

lemma binary_cofan.is_van_kampen_iff (c : binary_cofan X Y) :
  is_van_kampen_colimit c ↔
  ∀ {X' Y' : C} (c' : binary_cofan X' Y') (αX : X' ⟶ X) (αY : Y' ⟶ Y)
    (f : c'.X ⟶ c.X) (hαX : αX ≫ c.inl = c'.inl ≫ f) (hαY : αY ≫ c.inr = c'.inr ≫ f),
    nonempty (is_colimit c') ↔ is_pullback c'.inl αX f c.inl ∧ is_pullback c'.inr αY f c.inr :=
begin
  split,
  { introv H hαX hαY,
    rw H c' (map_pair αX αY) f (by ext ⟨⟨⟩⟩; dsimp; assumption) (map_pair_equifibered _),
    split, { intro H, exact ⟨H _, H _⟩ }, { rintros H ⟨⟨⟩⟩, exacts [H.1, H.2] } },
  { introv H F' hα h,
    let X' := F'.obj ⟨walking_pair.left⟩, let Y' := F'.obj ⟨walking_pair.right⟩,
    have : F' = pair X' Y',
    { apply functor.hext, { rintros ⟨⟨⟩⟩; refl }, { rintros ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩; simpa } },
    clear_value X' Y', subst this, change binary_cofan X' Y' at c',
    rw H c' _ _ _ (nat_trans.congr_app hα ⟨walking_pair.left⟩)
      (nat_trans.congr_app hα ⟨walking_pair.right⟩),
    split, { rintros H ⟨⟨⟩⟩, exacts [H.1, H.2] }, { intro H, exact ⟨H _, H _⟩ } }
end

lemma binary_cofan.is_van_kampen_mk {X Y : C} (c : binary_cofan X Y)
  (cofans : ∀ (X Y : C), binary_cofan X Y) (colimits : ∀ X Y, is_colimit (cofans X Y))
  (cones : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), pullback_cone f g)
  (limits : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),  is_limit (cones f g))
  (h₁ : ∀ {X' Y' : C} (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : (cofans X' Y').X ⟶ c.X)
    (hαX : αX ≫ c.inl = (cofans X' Y').inl ≫ f) (hαY : αY ≫ c.inr = (cofans X' Y').inr ≫ f),
    is_pullback (cofans X' Y').inl αX f c.inl ∧ is_pullback (cofans X' Y').inr αY f c.inr)
  (h₂ : ∀ {Z : C} (f : Z ⟶ c.X),
    is_colimit (binary_cofan.mk (cones f c.inl).fst (cones f c.inr).fst)) :
  is_van_kampen_colimit c :=
begin
  rw binary_cofan.is_van_kampen_iff,
  introv hX hY,
  split,
  { rintros ⟨h⟩,
    let e := h.cocone_point_unique_up_to_iso (colimits _ _),
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [hX]) (by simp [hY]),
    split,
    { rw [← category.id_comp αX, ← iso.hom_inv_id_assoc e f],
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl := by { dsimp, simp },
      haveI : is_iso (𝟙 X') := infer_instance,
      exact (is_pullback.of_vert_is_iso ⟨this⟩).paste_vert hl },
    { rw [← category.id_comp αY, ← iso.hom_inv_id_assoc e f],
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr := by { dsimp, simp },
      haveI : is_iso (𝟙 Y') := infer_instance,
      exact (is_pullback.of_vert_is_iso ⟨this⟩).paste_vert hr } },
  { rintro ⟨H₁, H₂⟩,
    refine ⟨is_colimit.of_iso_colimit _ $ (iso_binary_cofan_mk _).symm⟩,
    let e₁ : X' ≅ _ := H₁.is_limit.cone_point_unique_up_to_iso (limits _ _),
    let e₂ : Y' ≅ _ := H₂.is_limit.cone_point_unique_up_to_iso (limits _ _),
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp,
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp,
    rw [he₁, he₂],
    apply binary_cofan.is_colimit_comp_right_iso (binary_cofan.mk _ _),
    apply binary_cofan.is_colimit_comp_left_iso (binary_cofan.mk _ _),
    exact h₂ f }
end
.
lemma binary_cofan.mono_inr_of_is_van_kampen [has_initial C] {X Y : C} {c : binary_cofan X Y}
  (h : is_van_kampen_colimit c) : mono c.inr :=
begin
  refine pullback_cone.mono_of_is_limit_mk_id_id _ (is_pullback.is_limit _),
  refine (h (binary_cofan.mk (initial.to Y) (𝟙 Y))
    (map_pair (initial.to X) (𝟙 Y)) c.inr _ (map_pair_equifibered _)).mp ⟨_⟩ ⟨walking_pair.right⟩,
  { ext ⟨⟨⟩⟩; dsimp; simp },
  { exact ((binary_cofan.is_colimit_iff_is_iso_inr initial_is_initial _).mpr
      (by { dsimp, apply_instance })).some }
end

lemma finitary_extensive.mono_inr_of_is_colimit [finitary_extensive C]
  {c : binary_cofan X Y} (hc : is_colimit c) : mono c.inr :=
binary_cofan.mono_inr_of_is_van_kampen (finitary_extensive.van_kampen c hc)

lemma finitary_extensive.mono_inl_of_is_colimit [finitary_extensive C]
  {c : binary_cofan X Y} (hc : is_colimit c) : mono c.inl :=
finitary_extensive.mono_inr_of_is_colimit (binary_cofan.is_colimit_flip hc)

instance [finitary_extensive C] (X Y : C) : mono (coprod.inl : X ⟶ X ⨿ Y) :=
(finitary_extensive.mono_inl_of_is_colimit (coprod_is_coprod X Y) : _)

instance [finitary_extensive C] (X Y : C) : mono (coprod.inr : Y ⟶ X ⨿ Y) :=
(finitary_extensive.mono_inr_of_is_colimit (coprod_is_coprod X Y) : _)

lemma binary_cofan.is_pullback_initial_to_of_is_van_kampen [has_initial C]
  {c : binary_cofan X Y}
  (h : is_van_kampen_colimit c) : is_pullback (initial.to _) (initial.to _) c.inl c.inr :=
begin
  refine ((h (binary_cofan.mk (initial.to Y) (𝟙 Y)) (map_pair (initial.to X) (𝟙 Y)) c.inr _
    (map_pair_equifibered _)).mp ⟨_⟩ ⟨walking_pair.left⟩).flip,
  { ext ⟨⟨⟩⟩; dsimp; simp },
  { exact ((binary_cofan.is_colimit_iff_is_iso_inr initial_is_initial _).mpr
      (by { dsimp, apply_instance })).some }
end

lemma finitary_extensive.is_pullback_initial_to_binary_cofan [finitary_extensive C]
  {c : binary_cofan X Y} (hc : is_colimit c) :
  is_pullback (initial.to _) (initial.to _) c.inl c.inr :=
binary_cofan.is_pullback_initial_to_of_is_van_kampen (finitary_extensive.van_kampen c hc)

lemma has_strict_initial_of_is_universal [has_initial C]
  (H : is_universal_colimit (binary_cofan.mk (𝟙 (⊥_ C)) (𝟙 (⊥_ C)))) :
  has_strict_initial_objects C :=
has_strict_initial_objects_of_initial_is_strict
begin
  intros A f,
  suffices : is_colimit (binary_cofan.mk (𝟙 A) (𝟙 A)),
  { obtain ⟨l, h₁, h₂⟩ := limits.binary_cofan.is_colimit.desc' this (f ≫ initial.to A) (𝟙 A),
    rcases (category.id_comp _).symm.trans h₂ with rfl,
    exact ⟨⟨_, ((category.id_comp _).symm.trans h₁).symm, initial_is_initial.hom_ext _ _⟩⟩ },
  refine (H (binary_cofan.mk (𝟙 _) (𝟙 _)) (map_pair f f) f (by ext ⟨⟨⟩⟩; dsimp; simp)
    (map_pair_equifibered _) _).some,
  rintro ⟨⟨⟩⟩; dsimp;
    exact is_pullback.of_horiz_is_iso ⟨(category.id_comp _).trans (category.comp_id _).symm⟩
end

@[priority 100]
instance has_strict_initial_objects_of_finitary_extensive [finitary_extensive C] :
  has_strict_initial_objects C :=
has_strict_initial_of_is_universal (finitary_extensive.van_kampen _
  ((binary_cofan.is_colimit_iff_is_iso_inr initial_is_initial _).mpr
    (by { dsimp, apply_instance })).some).is_universal

lemma finitary_extensive_iff_of_is_terminal (C : Type u) [category.{v} C] [has_finite_coproducts C]
  (T : C) (HT : is_terminal T) (c₀ : binary_cofan T T) (hc₀ : is_colimit c₀) :
  finitary_extensive C ↔ is_van_kampen_colimit c₀ :=
begin
  refine ⟨λ H, H.2 c₀ hc₀, λ H, _⟩,
  constructor,
  simp_rw binary_cofan.is_van_kampen_iff at H ⊢,
  intros X Y c hc X' Y' c' αX αY f hX hY,
  obtain ⟨d, hd, hd'⟩ := limits.binary_cofan.is_colimit.desc' hc
    (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr),
  rw H c' (αX ≫ HT.from _) (αY ≫ HT.from _) (f ≫ d)
    (by rw [← reassoc_of hX, hd, category.assoc])
    (by rw [← reassoc_of hY, hd', category.assoc]),
  obtain ⟨hl, hr⟩ := (H c (HT.from _) (HT.from _) d hd.symm hd'.symm).mp ⟨hc⟩,
  rw [hl.paste_vert_iff hX.symm, hr.paste_vert_iff hY.symm]
end

instance types.finitary_extensive : finitary_extensive (Type u) :=
begin
  rw [finitary_extensive_iff_of_is_terminal (Type u) punit types.is_terminal_punit _
    (types.binary_coproduct_colimit _ _)],
  apply binary_cofan.is_van_kampen_mk _ _ (λ X Y, types.binary_coproduct_colimit X Y) _
    (λ X Y Z f g, (limits.types.pullback_limit_cone f g).2),
  { intros,
    split,
    { refine ⟨⟨hαX.symm⟩, ⟨pullback_cone.is_limit_aux' _ _⟩⟩,
      intro s,
      have : ∀ x, ∃! y, s.fst x = sum.inl y,
      { intro x,
        cases h : s.fst x,
        { simp_rw sum.inl_injective.eq_iff, exact exists_unique_eq' },
        { apply_fun f at h,
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαY val : _).symm } },
      delta exists_unique at this,
      choose l hl hl',
      exact ⟨l, (funext hl).symm, types.is_terminal_punit.hom_ext _ _,
        λ l' h₁ h₂, funext $ λ x, hl' x (l' x) (congr_fun h₁ x).symm⟩ },
    { refine ⟨⟨hαY.symm⟩, ⟨pullback_cone.is_limit_aux' _ _⟩⟩,
      intro s, dsimp,
      have : ∀ x, ∃! y, s.fst x = sum.inr y,
      { intro x,
        cases h : s.fst x,
        { apply_fun f at h,
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαX val : _).symm },
        { simp_rw sum.inr_injective.eq_iff, exact exists_unique_eq' } },
      delta exists_unique at this,
      choose l hl hl',
      exact ⟨l, (funext hl).symm, types.is_terminal_punit.hom_ext _ _,
        λ l' h₁ h₂, funext $ λ x, hl' x (l' x) (congr_fun h₁ x).symm⟩ } },
  { intros Z f,
    dsimp [limits.types.binary_coproduct_cocone],
    delta types.pullback_obj,
    have : ∀ x, f x = sum.inl punit.star ∨ f x = sum.inr punit.star,
    { intro x, rcases f x with (⟨⟨⟩⟩|⟨⟨⟩⟩), exacts [or.inl rfl, or.inr rfl] },
    let eX : {p : Z × punit // f p.fst = sum.inl p.snd} ≃ {x : Z // f x = sum.inl punit.star } :=
      ⟨λ p, ⟨p.1.1, by convert p.2⟩, λ x, ⟨⟨_, _⟩, x.2⟩, λ _, by ext; refl, λ _, by ext; refl⟩,
    let eY : {p : Z × punit // f p.fst = sum.inr p.snd} ≃ {x : Z // f x = sum.inr punit.star } :=
      ⟨λ p, ⟨p.1.1, p.2.trans (congr_arg sum.inr $ subsingleton.elim _ _)⟩,
        λ x, ⟨⟨_, _⟩, x.2⟩, λ _, by ext; refl, λ _, by ext; refl⟩,
    fapply binary_cofan.is_colimit_mk,
    { exact λ s x, dite _ (λ h, s.inl $ eX.symm ⟨x, h⟩)
        (λ h, s.inr $ eY.symm ⟨x, (this x).resolve_left h⟩) },
    { intro s, ext ⟨⟨x, ⟨⟩⟩, _⟩, dsimp, split_ifs; refl },
    { intro s, ext ⟨⟨x, ⟨⟩⟩, hx⟩, dsimp, split_ifs, { cases h.symm.trans hx }, { refl } },
    { intros s m e₁ e₂, ext x, split_ifs, { rw ← e₁, refl }, { rw ← e₂, refl } } }
end

section Top

/-- (Implementation) An auxiliary lemma for the proof that `Top` is finitary extensive. -/
def finitary_extensive_Top_aux (Z : Top.{u}) (f : Z ⟶ Top.of (punit.{u+1} ⊕ punit.{u+1})) :
  is_colimit (binary_cofan.mk
    (Top.pullback_fst f (Top.binary_cofan (Top.of punit) (Top.of punit)).inl)
    (Top.pullback_fst f (Top.binary_cofan (Top.of punit) (Top.of punit)).inr)) :=
begin
  have : ∀ x, f x = sum.inl punit.star ∨ f x = sum.inr punit.star,
  { intro x, rcases f x with (⟨⟨⟩⟩|⟨⟨⟩⟩), exacts [or.inl rfl, or.inr rfl] },
  let eX : {p : Z × punit // f p.fst = sum.inl p.snd} ≃ { x : Z // f x = sum.inl punit.star } :=
    ⟨λ p, ⟨p.1.1, p.2.trans (congr_arg sum.inl $ subsingleton.elim _ _)⟩,
      λ x, ⟨⟨_, _⟩, x.2⟩, λ _, by ext; refl, λ _, by ext; refl⟩,
  let eY : {p : Z × punit // f p.fst = sum.inr p.snd} ≃ { x : Z // f x = sum.inr punit.star } :=
    ⟨λ p, ⟨p.1.1, p.2.trans (congr_arg sum.inr $ subsingleton.elim _ _)⟩,
      λ x, ⟨⟨_, _⟩, x.2⟩, λ _, by ext; refl, λ _, by ext; refl⟩,
  fapply binary_cofan.is_colimit_mk,
  { refine λ s, ⟨λ x, dite _ (λ h, s.inl $ eX.symm ⟨x, h⟩)
      (λ h, s.inr $ eY.symm ⟨x, (this x).resolve_left h⟩), _⟩,
    rw continuous_iff_continuous_at,
    intro x,
    by_cases f x = sum.inl punit.star,
    { revert h x,
      apply (is_open.continuous_on_iff _).mp,
      { rw continuous_on_iff_continuous_restrict,
        convert_to continuous (λ x : {x|f x = sum.inl punit.star}, s.inl ⟨(x, punit.star), x.2⟩),
        { ext ⟨x, hx⟩, exact dif_pos hx },
        continuity },
      { convert f.2.1 _ (open_embedding_inl).open_range, ext x, exact ⟨λ h, ⟨_, h.symm⟩,
          λ ⟨e, h⟩, h.symm.trans (congr_arg sum.inl $ subsingleton.elim _ _)⟩ } },
    { revert h x,
      apply (is_open.continuous_on_iff _).mp,
      { rw continuous_on_iff_continuous_restrict,
        convert_to continuous (λ x : {x|f x ≠ sum.inl punit.star},
          s.inr ⟨(x, punit.star), (this _).resolve_left x.2⟩),
        { ext ⟨x, hx⟩, exact dif_neg hx },
        continuity },
      { convert f.2.1 _ (open_embedding_inr).open_range, ext x,
        change f x ≠ sum.inl punit.star ↔ f x ∈ set.range sum.inr,
        transitivity f x = sum.inr punit.star,
        { rcases f x with (⟨⟨⟩⟩|⟨⟨⟩⟩);
            simp only [iff_self, eq_self_iff_true, not_true, ne.def, not_false_iff] },
        { exact ⟨λ h, ⟨_, h.symm⟩, λ ⟨e, h⟩,
            h.symm.trans (congr_arg sum.inr $ subsingleton.elim _ _)⟩ } } } },
  { intro s, ext ⟨⟨x, ⟨⟩⟩, _⟩, change dite _ _ _ = _, split_ifs; refl },
  { intro s, ext ⟨⟨x, ⟨⟩⟩, hx⟩, change dite _ _ _ = _,
    split_ifs, { cases h.symm.trans hx }, { refl } },
  { intros s m e₁ e₂, ext x, change m x = dite _ _ _,
    split_ifs, { rw ← e₁, refl }, { rw ← e₂, refl } }
end

instance : finitary_extensive Top.{u} :=
begin
  rw [finitary_extensive_iff_of_is_terminal Top.{u} _ Top.is_terminal_punit _
    (Top.binary_cofan_is_colimit _ _)],
  apply binary_cofan.is_van_kampen_mk _ _ (λ X Y, Top.binary_cofan_is_colimit X Y) _
    (λ X Y Z f g, Top.pullback_cone_is_limit f g),
  { intros,
    split,
    { refine ⟨⟨hαX.symm⟩, ⟨pullback_cone.is_limit_aux' _ _⟩⟩,
      intro s,
      have : ∀ x, ∃! y, s.fst x = sum.inl y,
      { intro x,
        cases h : s.fst x,
        { simp_rw sum.inl_injective.eq_iff, exact exists_unique_eq' },
        { apply_fun f at h,
          cases ((concrete_category.congr_hom s.condition x).symm.trans h).trans
            (concrete_category.congr_hom hαY val : _).symm } },
      delta exists_unique at this,
      choose l hl hl',
      refine ⟨⟨l, _⟩, continuous_map.ext (λ a, (hl a).symm), Top.is_terminal_punit.hom_ext _ _,
        λ l' h₁ h₂, continuous_map.ext $ λ x,
          hl' x (l' x) (concrete_category.congr_hom h₁ x).symm⟩,
      apply embedding_inl.to_inducing.continuous_iff.mpr,
      convert s.fst.2 using 1, exact (funext hl).symm },
    { refine ⟨⟨hαY.symm⟩, ⟨pullback_cone.is_limit_aux' _ _⟩⟩,
      intro s, dsimp,
      have : ∀ x, ∃! y, s.fst x = sum.inr y,
      { intro x,
        cases h : s.fst x,
        { apply_fun f at h,
          cases ((concrete_category.congr_hom s.condition x).symm.trans h).trans
            (concrete_category.congr_hom hαX val : _).symm },
        { simp_rw sum.inr_injective.eq_iff, exact exists_unique_eq' } },
      delta exists_unique at this,
      choose l hl hl',
      refine ⟨⟨l, _⟩, continuous_map.ext (λ a, (hl a).symm), Top.is_terminal_punit.hom_ext _ _,
        λ l' h₁ h₂, continuous_map.ext $
          λ x, hl' x (l' x) (concrete_category.congr_hom h₁ x).symm⟩,
      apply embedding_inr.to_inducing.continuous_iff.mpr,
      convert s.fst.2 using 1, exact (funext hl).symm } },
  { intros Z f, exact finitary_extensive_Top_aux Z f }
end

end Top

section functor

lemma is_universal_colimit.map_reflective [has_colimits_of_shape J C]
  [has_pullbacks C] [has_pullbacks D]
  {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [full Gr] [faithful Gr]
  [preserves_limits_of_shape walking_cospan Gl] {F : J ⥤ D} {c : cocone (F ⋙ Gr)}
  (H : is_universal_colimit c) :
  is_universal_colimit (Gl.map_cocone c) :=
begin
  haveI := adj.right_adjoint_preserves_limits,
  haveI : preserves_colimits_of_size.{u' v'} Gl := adj.left_adjoint_preserves_colimits,
  haveI : reflects_limits_of_shape walking_cospan Gr :=
    reflects_limits_of_shape_of_reflects_isomorphisms,
  intros F' c' α f h hα hc',
  let α' := α ≫ (functor.associator _ _ _).hom ≫ whisker_left F adj.counit ≫ F.right_unitor.hom,
  have hα' : α'.equifibered := hα.comp (nat_trans.equifibered_of_is_iso _),
  have hadj : ∀ X, Gl.map (adj.unit.app X) = inv (adj.counit.app _),
  { intro X, apply is_iso.eq_inv_of_inv_hom_id, exact adj.left_triangle_components },
  haveI : ∀ X, is_iso (Gl.map (adj.unit.app X)) := by { simp_rw hadj, apply_instance },
  have hα'' : ∀ j, Gl.map (Gr.map $ α'.app j) = adj.counit.app _ ≫ α.app j,
  { intro j, rw ← cancel_mono (adj.counit.app $ F.obj j), dsimp,
    simp only [category.comp_id, adjunction.counit_naturality_assoc, category.id_comp,
      adjunction.counit_naturality, category.assoc, functor.map_comp] },
  have hc'' : ∀ j, α.app j ≫ Gl.map (c.ι.app j) = c'.ι.app j ≫ f := nat_trans.congr_app h,
  let β := iso_whisker_left F' (as_iso adj.counit) ≪≫ F'.right_unitor,
  let c'' : cocone (F' ⋙ Gr),
  { refine { X := pullback (Gr.map f) (adj.unit.app _), ι := { app := λ j,
      pullback.lift (Gr.map $ c'.ι.app j) (Gr.map (α'.app j) ≫ c.ι.app j) _,
      naturality' := _ } },
    { rw [← Gr.map_comp, ← hc''], erw ← adj.unit_naturality, rw [Gl.map_comp, hα''], dsimp,
      simp only [category.assoc, functor.map_comp, adj.right_triangle_components_assoc], },
    { intros i j g, ext; dsimp; simp only [category.comp_id, category.id_comp, category.assoc,
        ← functor.map_comp, pullback.lift_fst, pullback.lift_snd, ← functor.map_comp_assoc],
      { congr' 1, exact c'.w _ },
      { rw [α.naturality_assoc], dsimp, rw [adj.counit_naturality, ← category.assoc,
          Gr.map_comp_assoc], congr' 1, exact c.w _ } } },
  let cf : (cocones.precompose β.hom).obj c' ⟶ Gl.map_cocone c'',
  { refine { hom := pullback.lift _ f _ ≫ (preserves_pullback.iso _ _ _).inv, w' := _ },
    exact (inv $ adj.counit.app c'.X),
    { rw [is_iso.inv_comp_eq, ← adj.counit_naturality_assoc, ← cancel_mono (adj.counit.app $
        Gl.obj c.X), category.assoc, category.assoc, adj.left_triangle_components],
      erw category.comp_id, refl },
    { intro j, rw [← category.assoc, iso.comp_inv_eq], ext; simp only
        [preserves_pullback.iso_hom_fst, preserves_pullback.iso_hom_snd, pullback.lift_fst,
          pullback.lift_snd, category.assoc, functor.map_cocone_ι_app, ← Gl.map_comp],
      { rw [is_iso.comp_inv_eq, adj.counit_naturality], dsimp, rw category.comp_id },
      { rw [Gl.map_comp, hα'', category.assoc, hc''], dsimp,
        rw [category.comp_id, category.assoc] } } },
  have : cf.hom ≫ (preserves_pullback.iso _ _ _).hom ≫ pullback.fst ≫ adj.counit.app _ = 𝟙 _,
  { simp only [is_iso.inv_hom_id, iso.inv_hom_id_assoc, category.assoc, pullback.lift_fst_assoc] },
  haveI : is_iso cf,
  { apply_with cocones.cocone_iso_of_hom_iso { instances := ff },
    rw ← is_iso.eq_comp_inv at this,
    rw this,
    apply_instance },
  obtain ⟨Hc''⟩ := H c'' (whisker_right α' Gr) pullback.snd _ (hα'.whisker_right Gr) _,
  rotate,
  { ext j, dsimp, simp only [category.comp_id, category.id_comp, category.assoc, functor.map_comp,
      pullback.lift_snd] },
  { intro j,
    apply is_pullback.of_right _ _ (is_pullback.of_has_pullback _ _),
    { dsimp, simp only [category.comp_id, category.id_comp, category.assoc, functor.map_comp,
        pullback.lift_fst],
      rw ← category.comp_id (Gr.map f),
      refine ((hc' j).map Gr).paste_vert (is_pullback.of_vert_is_iso ⟨_⟩),
      rw [← adj.unit_naturality, category.comp_id, ← category.assoc,
        ← category.id_comp (Gr.map ((Gl.map_cocone c).ι.app j))],
      congr' 1,
      rw ← cancel_mono (Gr.map (adj.counit.app (F.obj j))),
      dsimp,
      simp only [category.comp_id, adjunction.right_triangle_components, category.id_comp,
        category.assoc] },
    { dsimp, simp only [category.comp_id, category.id_comp, category.assoc, functor.map_comp,
        pullback.lift_snd] } },
  exact ⟨is_colimit.precompose_hom_equiv β c' $
    (is_colimit_of_preserves Gl Hc'').of_iso_colimit (as_iso cf).symm⟩
end

lemma is_van_kampen_colimit.map_reflective [has_colimits_of_shape J C]
  [has_pullbacks C] [has_pullbacks D]
  {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [full Gr] [faithful Gr]
  [preserves_limits_of_shape walking_cospan Gl]
  [is_iso adj.counit] {F : J ⥤ D} {c : cocone (F ⋙ Gr)} (H : is_van_kampen_colimit c) :
   is_van_kampen_colimit (Gl.map_cocone c) :=
begin
  haveI := adj.right_adjoint_preserves_limits,
  haveI : preserves_colimits_of_size.{u' v'} Gl := adj.left_adjoint_preserves_colimits,
  haveI : reflects_limits_of_shape walking_cospan Gr :=
    reflects_limits_of_shape_of_reflects_isomorphisms,
  intros F' c' α f h hα,
  refine ⟨_, H.is_universal.map_reflective adj c' α f h hα⟩,
  rintro ⟨hc'⟩ j,
  let α' := α ≫ (functor.associator _ _ _).hom ≫ whisker_left F adj.counit ≫ F.right_unitor.hom,
  have hα' : α'.equifibered := hα.comp (nat_trans.equifibered_of_is_iso _),
  have hα'' : ∀ j, Gl.map (Gr.map $ α'.app j) = adj.counit.app _ ≫ α.app j,
  { intro j, rw ← cancel_mono (adj.counit.app $ F.obj j), dsimp,
    simp only [category.comp_id, adjunction.counit_naturality_assoc, category.id_comp,
      adjunction.counit_naturality, category.assoc, functor.map_comp] },
  have hc'' : ∀ j, α.app j ≫ Gl.map (c.ι.app j) = c'.ι.app j ≫ f := nat_trans.congr_app h,
  let β := iso_whisker_left F' (as_iso adj.counit) ≪≫ F'.right_unitor,
  let hl := (is_colimit.precompose_hom_equiv β c').symm hc',
  let hr := is_colimit_of_preserves Gl (colimit.is_colimit $ F' ⋙ Gr),
  have : α.app j = β.inv.app _ ≫ Gl.map (Gr.map $ α'.app j),
  { rw hα'', simp },
  rw this,
  have : f = (hl.cocone_point_unique_up_to_iso hr).hom ≫
    Gl.map (colimit.desc _ ⟨_, whisker_right α' Gr ≫ c.2⟩),
  { symmetry,
    convert @is_colimit.cocone_point_unique_up_to_iso_hom_desc _ _ _ _ ((F' ⋙ Gr) ⋙ Gl)
      (Gl.map_cocone ⟨_, (whisker_right α' Gr ≫ c.2 : _)⟩) _ _ hl hr using 3,
    { apply hr.hom_ext, intro j, rw [hr.fac, functor.map_cocone_ι_app, ← Gl.map_comp,
        colimit.cocone_ι, colimit.ι_desc], refl },
    { clear_value α', apply hl.hom_ext, intro j, rw hl.fac, dsimp,
      simp only [category.comp_id, hα'', category_theory.category.assoc, Gl.map_comp],
      congr' 1, exact (nat_trans.congr_app h j).symm } },
  rw this,
  have := ((H (colimit.cocone $ F' ⋙ Gr) (whisker_right α' Gr)
    (colimit.desc _ ⟨_, whisker_right α' Gr ≫ c.2⟩) _ (hα'.whisker_right Gr)).mp
    ⟨(get_colimit_cocone $ F' ⋙ Gr).2⟩ j).map Gl,
  convert is_pullback.paste_vert _ this,
  { refine is_pullback.of_vert_is_iso ⟨_⟩,
    rw [← is_iso.inv_comp_eq, ← category.assoc, nat_iso.inv_inv_app],
    exact is_colimit.comp_cocone_point_unique_up_to_iso_hom hl hr _ },
  { clear_value α', ext j, simp }
end

lemma is_van_kampen_colimit.of_map {D : Type*} [category D] (G : C ⥤ D) {F : J ⥤ C} {c : cocone F}
  [preserves_limits_of_shape walking_cospan G] [reflects_limits_of_shape walking_cospan G]
    [preserves_colimits_of_shape J G] [reflects_colimits_of_shape J G]
   (H : is_van_kampen_colimit (G.map_cocone c)) : is_van_kampen_colimit c :=
begin
  intros F' c' α f h hα,
  refine (iff.trans _ (H (G.map_cocone c') (whisker_right α G) (G.map f)
    (by { ext j, simpa using G.congr_map (nat_trans.congr_app h j) })
    (hα.whisker_right G))).trans (forall_congr $ λ j, _),
  { exact ⟨λ h, ⟨is_colimit_of_preserves G h.some⟩, λ h, ⟨is_colimit_of_reflects G h.some⟩⟩ },
  { exact is_pullback.map_iff G (nat_trans.congr_app h.symm j) }
end

lemma is_van_kampen_colimit_of_evaluation [has_pullbacks D] [has_colimits_of_shape J D]
  (F : J ⥤ C ⥤ D) (c : cocone F)
  (hc : ∀ x : C, is_van_kampen_colimit (((evaluation C D).obj x).map_cocone c)) :
  is_van_kampen_colimit c :=
begin
  intros F' c' α f e hα,
  have := λ x, hc x (((evaluation C D).obj x).map_cocone c') (whisker_right α _)
    (((evaluation C D).obj x).map f)
    (by { ext y, dsimp, exact nat_trans.congr_app (nat_trans.congr_app e y) x })
    (hα.whisker_right _),
  split,
  { rintros ⟨hc'⟩ j,
    refine ⟨⟨(nat_trans.congr_app e j).symm⟩, ⟨evaluation_jointly_reflects_limits _ _⟩⟩,
    refine λ x, (is_limit_map_cone_pullback_cone_equiv _ _).symm _,
    exact ((this x).mp ⟨preserves_colimit.preserves hc'⟩ _).is_limit },
  { exact λ H, ⟨evaluation_jointly_reflects_colimits _
      (λ x, ((this x).mpr (λ j, (H j).map ((evaluation C D).obj x))).some)⟩ }
end

instance [has_pullbacks C] [finitary_extensive C] : finitary_extensive (D ⥤ C) :=
begin
  haveI : has_finite_coproducts (D ⥤ C) :=
    ⟨λ J hJ, by exactI limits.functor_category_has_colimits_of_shape⟩,
  exact ⟨λ X Y c hc, is_van_kampen_colimit_of_evaluation _ c
    (λ x, finitary_extensive.van_kampen _ $ preserves_colimit.preserves hc)⟩
end

lemma finitary_extensive_of_preserves_and_reflects (F : C ⥤ D)
  [finitary_extensive D] [has_finite_coproducts C]
    [preserves_limits_of_shape walking_cospan F]
    [reflects_limits_of_shape walking_cospan F]
    [preserves_colimits_of_shape (discrete walking_pair) F]
    [reflects_colimits_of_shape (discrete walking_pair) F] :
  finitary_extensive C :=
⟨λ X Y c hc, (finitary_extensive.van_kampen _ (is_colimit_of_preserves F hc)).of_map F⟩

lemma finitary_extensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D)
  [finitary_extensive D] [has_finite_coproducts C] [has_pullbacks C]
    [preserves_limits_of_shape walking_cospan F]
    [preserves_colimits_of_shape (discrete walking_pair) F]
    [reflects_isomorphisms F] :
  finitary_extensive C :=
begin
  haveI : reflects_limits_of_shape walking_cospan F :=
    reflects_limits_of_shape_of_reflects_isomorphisms,
  haveI : reflects_colimits_of_shape (discrete walking_pair) F :=
    reflects_colimits_of_shape_of_reflects_isomorphisms,
  exact finitary_extensive_of_preserves_and_reflects F,
end

lemma finitary_extensive_of_reflective [has_finite_coproducts D] [has_pullbacks D]
  [finitary_extensive C] [has_pullbacks C]
  {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [full Gr] [faithful Gr]
  [preserves_limits_of_shape walking_cospan Gl] :
  finitary_extensive D :=
begin
  haveI : preserves_colimits_of_size Gl := adj.left_adjoint_preserves_colimits,
  constructor,
  intros X Y c hc,
  apply is_van_kampen_colimit.of_precompose_iso _
    (iso_whisker_left _ (as_iso adj.counit) ≪≫ functor.right_unitor _).hom,
  refine ((finitary_extensive.van_kampen _ (colimit.is_colimit $ pair X Y ⋙ _)).map_reflective
    adj).of_iso (is_colimit.unique_up_to_iso _ _),
  { exact is_colimit_of_preserves Gl (colimit.is_colimit _) },
  { exact (is_colimit.precompose_hom_equiv _ _).symm hc },
  { apply_instance }
end

end functor

end extensive

end category_theory
