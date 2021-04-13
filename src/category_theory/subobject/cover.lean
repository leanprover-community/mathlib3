import category_theory.limits.shapes.strong_epi
import category_theory.limits.shapes.equalizers
import category_theory.subobject.lattice
import category_theory.subobject.specific_subobjects

universes v u

open category_theory.limits

namespace category_theory
variables {C : Type u} [category.{v} C]

/-- We say that a morphism `f` is a cover if it does not factor through any proper subobject of
    its codomain. -/
class cover {X Y : C} (f : X ⟶ Y) : Prop :=
(eq_top_of_factors : ∀ P : subobject Y, P.factors f → P = ⊤)

lemma eq_top_of_factors {X Y : C} (f : X ⟶ Y) [cover f] (P : subobject Y) (hP : P.factors f) :
  P = ⊤ :=
cover.eq_top_of_factors P hP

lemma equalizer_ext {X Y : C} (f g : X ⟶ Y) [has_equalizers C] [is_iso (equalizer.ι f g)] : f = g :=
calc f = inv (equalizer.ι f g) ≫ equalizer.ι f g ≫ f : eq.symm $ is_iso.inv_hom_id_assoc _ _
   ... = inv (equalizer.ι f g) ≫ equalizer.ι f g ≫ g : equalizer.condition f g ▸ rfl
   ... = g                                            : is_iso.inv_hom_id_assoc _ _

lemma is_iso_of_is_iso_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] (h : is_iso g) :
  is_iso (f ≫ g) :=
⟨⟨inv g ≫ inv f, by simp⟩⟩

lemma is_iso_of_is_iso_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] (h : is_iso f) :
  is_iso (f ≫ g) :=
⟨⟨inv g ≫ inv f, by simp⟩⟩

lemma is_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] [is_iso g] : is_iso (f ≫ g) :=
⟨⟨inv g ≫ inv f, by simp⟩⟩

instance {X : C} : is_iso (⊤ : subobject X).arrow :=
begin
  rw [subobject.top_eq_id, ←subobject.underlying_iso_hom_comp_eq_mk],
  apply_instance,
end

lemma is_iso_iff_mk_eq_top {X Y : C} (f : X ⟶ Y) [mono f] : is_iso f ↔ subobject.mk f = ⊤ :=
⟨λ _, by exactI subobject.mk_eq_mk_of_comm _ _ (as_iso f) (category.comp_id _),
 λ h, subobject.underlying_iso_arrow f ▸ is_iso_of_is_iso_left _ _ (h.symm ▸ infer_instance)⟩

lemma equalizer_subobject_ext {X Y : C} (f g : X ⟶ Y) [has_equalizers C]
  (h : equalizer_subobject f g = ⊤) : f = g :=
have _, from (is_iso_iff_mk_eq_top _).2 h, by exactI equalizer_ext f g

lemma eq_top_of_is_iso_arrow {X : C} (P : subobject X) [is_iso P.arrow] : P = ⊤ :=
begin
  rw [←subobject.mk_arrow P, ←is_iso_iff_mk_eq_top],
  apply_instance
end

lemma eq_top_of_is_iso_arrow' {X : C} (P : subobject X) (h : is_iso P.arrow) : P = ⊤ :=
eq_top_of_is_iso_arrow _

lemma is_iso_of_factors_mk {X Y Z : C} (f : X ⟶ Y) [cover f] (g : Z ⟶ Y) [mono g]
  (h : (subobject.mk g).factors f) : is_iso g :=
by rw [is_iso_iff_mk_eq_top, eq_top_of_factors f _ h]

lemma is_iso_arrow_of_factors_mk {X Y : C} (f : X ⟶ Y) [cover f] (P : subobject Y)
  (h : P.factors f) : is_iso P.arrow :=
is_iso_of_factors_mk f P.arrow $ (subobject.mk_arrow P).symm ▸ h

lemma cover_of_is_image {X Y : C} (f : X ⟶ Y) (F : mono_factorisation f) (h : is_image F) :
  cover F.e :=
⟨λ P hP, eq_top_of_is_iso_arrow' _
 begin
  refine ⟨⟨h.lift ⟨P, P.arrow ≫ F.m, P.factor_thru F.e hP⟩, ⟨_, _⟩⟩⟩;
  simp [←cancel_mono P.arrow, ←cancel_mono F.m]
 end⟩

instance cover_factor_thru_image {X Y : C} (f : X ⟶ Y) [has_image f] :
  cover (factor_thru_image f) :=
cover_of_is_image _ _ (image.is_image f)

@[simps]
def triv {X Y : C} (f : X ⟶ Y) : mono_factorisation f :=
{ I := _,
  m := 𝟙 Y,
  e := f,
  fac' := category.comp_id _ }

lemma is_iso_of_factors {X Y : C} (f : X ⟶ Y) [cover f] {Z : C} (g : Z ⟶ Y) [mono g] (h : X ⟶ Z)
  (hf : h ≫ g = f) : is_iso g :=
(is_iso_iff_mk_eq_top _).2 (eq_top_of_factors f _ ⟨h, hf⟩)

/-- Any cover is an image and any cover has an image. -/
@[simps] noncomputable def is_image_triv {X Y : C} (f : X ⟶ Y) [cover f] : is_image (triv f) :=
⟨λ F, have is_iso F.m, from is_iso_of_factors f F.m F.e F.fac', by exactI inv F.m, by tidy⟩

instance has_image_of_cover {X Y : C} (f : X ⟶ Y) [cover f] : has_image f :=
⟨⟨⟨_, is_image_triv f⟩⟩⟩

instance is_iso_image_ι_of_cover {X Y : C} (f : X ⟶ Y) [cover f] : is_iso (image.ι f) :=
begin
  convert is_iso_comp (is_image.iso_ext (image.is_image f) (is_image_triv f)).hom (𝟙 _),
  exact (is_image.iso_ext_hom_m _ _).symm
end

@[simp] lemma mk_eq_top_of_is_iso {X Y : C} (f : X ⟶ Y) [is_iso f] : subobject.mk f = ⊤ :=
(is_iso_iff_mk_eq_top f).1 infer_instance

instance epi_of_cover {X Y : C} (f : X ⟶ Y) [cover f] [has_equalizers C] : epi f :=
⟨λ Z g h hf,
  equalizer_subobject_ext _ _ $ eq_top_of_factors f _ $ equalizer_subobject_factors _ _ _ hf⟩

instance strong_epi_of_cover {X Y : C} (f : X ⟶ Y) [cover f] [has_equalizers C] [has_pullbacks C] :
  strong_epi f :=
{ epi := by apply_instance,
  has_lift := λ A B h k g g_mono comm,
  ⟨⟨have is_iso (pullback.snd : pullback g k ⟶ Y),
      by exactI is_iso_of_factors f _ (pullback.lift _ _ comm) (pullback.lift_snd _ _ _),
    by exactI { lift := inv (pullback.snd : pullback g k ⟶ Y) ≫ pullback.fst,
      fac_left' := by simp [←cancel_mono g, pullback.condition, comm],
      fac_right' := by simp [pullback.condition] }⟩⟩ }

lemma cover_of_strong_epi {X Y : C} (f : X ⟶ Y) [strong_epi f] : cover f :=
⟨λ P hP, suffices is_iso P.arrow, by exactI eq_top_of_is_iso_arrow _,
  suffices split_epi P.arrow, by exactI is_iso_of_mono_of_split_epi _,
  { section_ := arrow.lift $ arrow.hom_mk' $ show P.factor_thru f hP ≫ P.arrow = f ≫ 𝟙 _, by simp }⟩

end category_theory
