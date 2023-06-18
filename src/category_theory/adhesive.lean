/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.extensive
import category_theory.limits.shapes.kernel_pair

/-!

# Adhesive categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions
- `category_theory.is_pushout.is_van_kampen`: A convenience formulation for a pushout being
  a van Kampen colimit.
- `category_theory.adhesive`: A category is adhesive if it has pushouts and pullbacks along
  monomorphisms, and such pushouts are van Kampen.

## Main Results
- `category_theory.type.adhesive`: The category of `Type` is adhesive.
- `category_theory.adhesive.is_pullback_of_is_pushout_of_mono_left`: In adhesive categories,
  pushouts along monomorphisms are pullbacks.
- `category_theory.adhesive.mono_of_is_pushout_of_mono_left`: In adhesive categories,
  monomorphisms are stable under pushouts.
- `category_theory.adhesive.to_regular_mono_category`: Monomorphisms in adhesive categories are
  regular (this implies that adhesive categories are balanced).

## TODO

Show that the following are adhesive:
- functor categories into adhesive categories
- the categories of sheaves over a site

## References
- https://ncatlab.org/nlab/show/adhesive+category
- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

-/
namespace category_theory

open limits

universes v' u' v u

variables {J : Type v'} [category.{u'} J] {C : Type u} [category.{v} C]

variables {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/-- A convenience formulation for a pushout being a van Kampen colimit.
See `is_pushout.is_van_kampen_iff` below. -/
@[nolint unused_arguments] -- This only makes sense when the original diagram is a pushout.
def is_pushout.is_van_kampen (H : is_pushout f g h i) : Prop :=
∀ ⦃W' X' Y' Z' : C⦄ (f' : W' ⟶ X') (g' : W' ⟶ Y') (h' : X' ⟶ Z') (i' : Y' ⟶ Z')
  (αW : W' ⟶ W) (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z)
  (hf : is_pullback f' αW αX f) (hg : is_pullback g' αW αY g)
  (hh : comm_sq h' αX αZ h) (hi : comm_sq i' αY αZ i)
  (w : comm_sq f' g' h' i'),
  is_pushout f' g' h' i' ↔ is_pullback h' αX αZ h ∧ is_pullback i' αY αZ i

lemma is_pushout.is_van_kampen.flip {H : is_pushout f g h i} (H' : H.is_van_kampen) :
  H.flip.is_van_kampen :=
begin
  introv W' hf hg hh hi w,
  simpa only [is_pushout.flip_iff, is_pullback.flip_iff, and_comm] using
    H' g' f' i' h' αW αY αX αZ hg hf hi hh w.flip,
end

lemma is_pushout.is_van_kampen_iff (H : is_pushout f g h i) :
  H.is_van_kampen ↔ is_van_kampen_colimit (pushout_cocone.mk h i H.w) :=
begin
  split,
  { intros H F' c' α fα eα hα,
    refine iff.trans _ ((H (F'.map walking_span.hom.fst) (F'.map walking_span.hom.snd)
      (c'.ι.app _) (c'.ι.app _) (α.app _) (α.app _) (α.app _) fα
      (by convert hα walking_span.hom.fst) (by convert hα walking_span.hom.snd)
      _ _ _).trans _),
    { have : F'.map walking_span.hom.fst ≫ c'.ι.app walking_span.left =
        F'.map walking_span.hom.snd ≫ c'.ι.app walking_span.right := by simp only [cocone.w],
      rw (is_colimit.equiv_of_nat_iso_of_iso (diagram_iso_span F') c'
        (pushout_cocone.mk _ _ this) _).nonempty_congr,
      { exact ⟨λ h, ⟨⟨this⟩, h⟩, λ h, h.2⟩ },
      { refine cocones.ext (iso.refl c'.X) _, rintro (_|_|_); dsimp;
          simp only [c'.w, category.assoc, category.id_comp, category.comp_id] } },
    { exact ⟨nat_trans.congr_app eα.symm _⟩ },
    { exact ⟨nat_trans.congr_app eα.symm _⟩ },
    { exact ⟨by simp⟩ },
    split,
    { rintros ⟨h₁, h₂⟩ (_|_|_),
      { rw ← c'.w walking_span.hom.fst, exact (hα walking_span.hom.fst).paste_horiz h₁ },
      exacts [h₁, h₂] },
    { intro h, exact ⟨h _, h _⟩ } },
  { introv H W' hf hg hh hi w,
    refine (iff.trans _
      ((H w.cocone ⟨by { rintros (_|_|_), exacts [αW, αX, αY] }, _⟩ αZ _ _).trans _)),
    rotate,
    { rintros i _ (_|_|_),
      { dsimp, simp only [functor.map_id, category.comp_id, category.id_comp] },
      exacts [hf.w, hg.w] },
    { ext (_|_|_),
      { dsimp, rw pushout_cocone.condition_zero, erw [category.assoc, hh.w, hf.w_assoc] },
      exacts [hh.w.symm, hi.w.symm] },
    { rintros i _ (_|_|_),
      { dsimp, simp_rw functor.map_id,
        exact is_pullback.of_horiz_is_iso ⟨by rw [category.comp_id, category.id_comp]⟩ },
      exacts [hf, hg] },
    { split,
      { intro h, exact ⟨h walking_cospan.left, h walking_cospan.right⟩ },
      { rintro ⟨h₁, h₂⟩ (_|_|_),
        { dsimp, rw pushout_cocone.condition_zero, exact hf.paste_horiz h₁ },
        exacts [h₁, h₂] } },
    { exact ⟨λ h, h.2, λ h, ⟨_, h⟩⟩ } }
end
.

lemma is_coprod_iff_is_pushout {X E Y YE : C} (c : binary_cofan X E)
  (hc : is_colimit c) {f : X ⟶ Y} {iY : Y ⟶ YE} {fE : c.X ⟶ YE}
  (H : comm_sq f c.inl iY fE) :
  nonempty (is_colimit (binary_cofan.mk (c.inr ≫ fE) iY)) ↔ is_pushout f c.inl iY fE :=
begin
  split,
  { rintro ⟨h⟩,
    refine ⟨H, ⟨limits.pushout_cocone.is_colimit_aux' _ _⟩⟩,
    intro s,
    dsimp,
    refine ⟨h.desc (binary_cofan.mk (c.inr ≫ s.inr) s.inl), h.fac _ ⟨walking_pair.right⟩, _, _⟩,
    { apply binary_cofan.is_colimit.hom_ext hc,
      { rw ← H.w_assoc, erw h.fac _ ⟨walking_pair.right⟩, exact s.condition },
      { rw ← category.assoc, exact h.fac _ ⟨walking_pair.left⟩ } },
    { intros m e₁ e₂,
      apply binary_cofan.is_colimit.hom_ext h,
      { dsimp, rw [category.assoc, e₂, eq_comm], exact h.fac _ ⟨walking_pair.left⟩ },
      { refine e₁.trans (eq.symm _), exact h.fac _ _ } } },
  { refine λ H, ⟨_⟩,
    fapply limits.binary_cofan.is_colimit_mk,
    { exact λ s, H.is_colimit.desc (pushout_cocone.mk s.inr _ $
        (hc.fac (binary_cofan.mk (f ≫ s.inr) s.inl) ⟨walking_pair.left⟩).symm) },
    { intro s,
      erw [category.assoc, H.is_colimit.fac _ walking_span.right, hc.fac], refl },
    { intro s, exact H.is_colimit.fac _ walking_span.left },
    { intros s m e₁ e₂,
      apply pushout_cocone.is_colimit.hom_ext H.is_colimit,
      { symmetry, exact (H.is_colimit.fac _ walking_span.left).trans e₂.symm },
      { erw H.is_colimit.fac _ walking_span.right,
        apply binary_cofan.is_colimit.hom_ext hc,
        { dsimp, erw [hc.fac, ← H.w_assoc, e₂], refl },
        { refine ((category.assoc _ _ _).symm.trans e₁).trans _, symmetry, exact hc.fac _ _ } } } }
end

lemma is_pushout.is_van_kampen_inl {W E X Z : C} (c : binary_cofan W E)
  [finitary_extensive C]
  [has_pullbacks C]
  (hc : is_colimit c) (f : W ⟶ X) (h : X ⟶ Z) (i : c.X ⟶ Z)
  (H : is_pushout f c.inl h i) : H.is_van_kampen :=
begin
  obtain ⟨hc₁⟩ := (is_coprod_iff_is_pushout c hc H.1).mpr H,
  introv W' hf hg hh hi w,
  obtain ⟨hc₂⟩ := ((binary_cofan.is_van_kampen_iff _).mp (finitary_extensive.van_kampen c hc)
    (binary_cofan.mk _ pullback.fst) _ _ _ hg.w.symm pullback.condition.symm).mpr
    ⟨hg, is_pullback.of_has_pullback αY c.inr⟩,
  refine (is_coprod_iff_is_pushout _ hc₂ w).symm.trans _,
  refine ((binary_cofan.is_van_kampen_iff _).mp (finitary_extensive.van_kampen _ hc₁)
    (binary_cofan.mk _ _) pullback.snd _ _ _ hh.w.symm).trans _,
  { dsimp, rw [← pullback.condition_assoc, category.assoc, hi.w] },
  split,
  { rintro ⟨hc₃, hc₄⟩,
    refine ⟨hc₄, _⟩,
    let Y'' := pullback αZ i,
    let cmp : Y' ⟶ Y'' := pullback.lift i' αY hi.w,
    have e₁ : (g' ≫ cmp) ≫ pullback.snd = αW ≫ c.inl :=
      by rw [category.assoc, pullback.lift_snd, hg.w],
    have e₂ : (pullback.fst ≫ cmp : pullback αY c.inr ⟶ _) ≫ pullback.snd =
      pullback.snd ≫ c.inr :=
      by rw [category.assoc, pullback.lift_snd, pullback.condition],
    obtain ⟨hc₄⟩ := ((binary_cofan.is_van_kampen_iff _).mp (finitary_extensive.van_kampen c hc)
      (binary_cofan.mk _ _) αW _ _ e₁.symm e₂.symm).mpr ⟨_, _⟩,
    { rw [← category.id_comp αZ, ← show cmp ≫ pullback.snd = αY, from pullback.lift_snd _ _ _],
      apply is_pullback.paste_vert _ (is_pullback.of_has_pullback αZ i),
      have : cmp = (hc₂.cocone_point_unique_up_to_iso hc₄).hom,
      { apply binary_cofan.is_colimit.hom_ext hc₂,
        exacts [(hc₂.comp_cocone_point_unique_up_to_iso_hom hc₄ ⟨walking_pair.left⟩).symm,
          (hc₂.comp_cocone_point_unique_up_to_iso_hom hc₄ ⟨walking_pair.right⟩).symm] },
      rw this,
      exact is_pullback.of_vert_is_iso ⟨by rw [← this, category.comp_id, pullback.lift_fst]⟩ },
    { apply is_pullback.of_right _ e₁ (is_pullback.of_has_pullback _ _),
      rw [category.assoc, pullback.lift_fst, ← H.w, ← w.w], exact hf.paste_horiz hc₄ },
    { apply is_pullback.of_right _ e₂ (is_pullback.of_has_pullback _ _),
      rw [category.assoc, pullback.lift_fst], exact hc₃ } },
  { rintros ⟨hc₃, hc₄⟩,
    exact ⟨(is_pullback.of_has_pullback αY c.inr).paste_horiz hc₄, hc₃⟩ }
end

lemma is_pushout.is_van_kampen.is_pullback_of_mono_left [mono f]
  {H : is_pushout f g h i} (H' : H.is_van_kampen) :
  is_pullback f g h i :=
((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i
  (is_kernel_pair.id_of_mono f) (is_pullback.of_vert_is_iso ⟨by simp⟩) H.1.flip ⟨rfl⟩
  ⟨by simp⟩).mp (is_pushout.of_horiz_is_iso ⟨by simp⟩)).1.flip

lemma is_pushout.is_van_kampen.is_pullback_of_mono_right [mono g]
  {H : is_pushout f g h i} (H' : H.is_van_kampen) :
  is_pullback f g h i :=
((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h  (is_pullback.of_vert_is_iso ⟨by simp⟩)
  (is_kernel_pair.id_of_mono g) ⟨rfl⟩ H.1
  ⟨by simp⟩).mp (is_pushout.of_vert_is_iso ⟨by simp⟩)).2

lemma is_pushout.is_van_kampen.mono_of_mono_left [mono f]
  {H : is_pushout f g h i} (H' : H.is_van_kampen) :
  mono i :=
is_kernel_pair.mono_of_is_iso_fst
  (((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i
  (is_kernel_pair.id_of_mono f) (is_pullback.of_vert_is_iso ⟨by simp⟩) H.1.flip ⟨rfl⟩
  ⟨by simp⟩).mp (is_pushout.of_horiz_is_iso ⟨by simp⟩)).2)

lemma is_pushout.is_van_kampen.mono_of_mono_right [mono g]
  {H : is_pushout f g h i} (H' : H.is_van_kampen) :
  mono h :=
is_kernel_pair.mono_of_is_iso_fst
  ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h  (is_pullback.of_vert_is_iso ⟨by simp⟩)
  (is_kernel_pair.id_of_mono g) ⟨rfl⟩ H.1
  ⟨by simp⟩).mp (is_pushout.of_vert_is_iso ⟨by simp⟩)).1

/-- A category is adhesive if it has pushouts and pullbacks along monomorphisms,
and such pushouts are van Kampen. -/
class adhesive (C : Type u) [category.{v} C] : Prop :=
[has_pullback_of_mono_left : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [mono f], has_pullback f g]
[has_pushout_of_mono_left : ∀ {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [mono f], has_pushout f g]
(van_kampen : ∀ {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} [mono f]
  (H : is_pushout f g h i), H.is_van_kampen)

attribute [priority 100, instance]
  adhesive.has_pullback_of_mono_left adhesive.has_pushout_of_mono_left

lemma adhesive.van_kampen' [adhesive C] [mono g] (H : is_pushout f g h i) : H.is_van_kampen :=
(adhesive.van_kampen H.flip).flip

lemma adhesive.is_pullback_of_is_pushout_of_mono_left [adhesive C]
  (H : is_pushout f g h i) [mono f] : is_pullback f g h i :=
(adhesive.van_kampen H).is_pullback_of_mono_left

lemma adhesive.is_pullback_of_is_pushout_of_mono_right [adhesive C]
  (H : is_pushout f g h i) [mono g] : is_pullback f g h i :=
(adhesive.van_kampen' H).is_pullback_of_mono_right

lemma adhesive.mono_of_is_pushout_of_mono_left [adhesive C]
  (H : is_pushout f g h i) [mono f] : mono i :=
(adhesive.van_kampen H).mono_of_mono_left

lemma adhesive.mono_of_is_pushout_of_mono_right [adhesive C]
  (H : is_pushout f g h i) [mono g] : mono h :=
(adhesive.van_kampen' H).mono_of_mono_right

instance type.adhesive : adhesive (Type u) :=
begin
  constructor,
  intros,
  exactI (is_pushout.is_van_kampen_inl _ (types.is_coprod_of_mono f) _ _ _ H.flip).flip
end

@[priority 100] noncomputable
instance adhesive.to_regular_mono_category [adhesive C] : regular_mono_category C :=
⟨λ X Y f hf, by exactI
  { Z := pushout f f,
    left := pushout.inl,
    right := pushout.inr,
    w := pushout.condition,
    is_limit := (adhesive.is_pullback_of_is_pushout_of_mono_left
      (is_pushout.of_has_pushout f f)).is_limit_fork }⟩

-- This then implies that adhesive categories are balanced
example [adhesive C] : balanced C := infer_instance

end category_theory
