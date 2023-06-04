import category_theory.preadditive.basic
import category_theory.abelian.exact
import algebra.homology.exact
import category_theory.limits.preserves.shapes.terminal
import category_theory.limits.shapes.zero_morphisms

namespace category_theory
namespace limits

open category_theory.limits

variables {C : Type*} [category C] [has_zero_morphisms C]

open_locale zero_object


lemma is_zero_iff_id_eq_zero {X : C} : is_zero X ↔ 𝟙 X = 0 :=
begin
  split,
  { exact λ h, h.eq_of_src _ _, },
  { intro e, split; intro Y; use 0; intro f,
    { rw [← cancel_epi (𝟙 _), e, comp_zero, zero_comp], apply_instance },
    { rw [← cancel_mono (𝟙 _), e, comp_zero, zero_comp], apply_instance }, }
end

lemma is_zero_of_mono {X Y : C} (f : X ⟶ Y) [mono f] (h : is_zero Y) : is_zero X :=
by rw [is_zero_iff_id_eq_zero, ← cancel_mono f, zero_comp, h.eq_of_tgt (𝟙 _ ≫ f)]

lemma is_zero_of_epi {X Y : C} (f : X ⟶ Y) [epi f] (h : is_zero X) : is_zero Y :=
by rw [is_zero_iff_id_eq_zero, ← cancel_epi f, comp_zero, h.eq_of_src (f ≫ 𝟙 Y)]

lemma is_zero_of_top_le_bot [has_zero_object C] (X : C)
  (h : (⊤ : subobject X) ≤ ⊥) : is_zero X :=
{ unique_to := λ Y,
  begin
    use 0, intro f,
    rw [← cancel_epi ((⊤ : subobject X).arrow), ← subobject.of_le_arrow h],
    simp only [subobject.bot_arrow, comp_zero, zero_comp],
  end,
  unique_from := λ Y,
  begin
    use 0, intro f,
    rw ← subobject.bot_factors_iff_zero,
    exact subobject.factors_of_le f h (subobject.top_factors f),
  end }

-- inline this
lemma is_zero_of_iso_of_zero {C : Type*} [category C] [has_zero_morphisms C]
  {X : C} (hX : is_zero X) {Y : C} (h : X ≅ Y) : is_zero Y :=
hX.of_iso h.symm

lemma is_zero_of_exact_zero_zero {C : Type*} [category C] [abelian C]
  {X Y Z : C} (h : exact (0 : X ⟶ Y) (0 : Y ⟶ Z)) : is_zero Y :=
is_zero_of_top_le_bot _
begin
  rw abelian.exact_iff_image_eq_kernel at h,
  rw [← @kernel_subobject_zero _ _ _ Y Z, ← @image_subobject_zero _ _ _ _ X Y, h],
end

lemma exact_of_is_zero {C : Type*} [category C] [abelian C]
  {X Y Z : C} (hY : is_zero Y) (f : X ⟶ Y) (g : Y ⟶ Z) : exact f g :=
by simp only [abelian.exact_iff, is_zero.eq_zero_of_tgt hY f,
  is_zero.eq_zero_of_tgt hY (kernel.ι g), zero_comp, eq_self_iff_true, and_self]

lemma is_zero_iff_exact_zero_zero {C : Type*} [category C] [abelian C]
  {X Y Z : C} : is_zero Y ↔ exact (0 : X ⟶ Y) (0 : Y ⟶ Z) :=
⟨λ h, exact_of_is_zero h 0 0, is_zero_of_exact_zero_zero⟩

lemma is_zero_of_exact_zero_zero' {C : Type*} [category C] [abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : exact f g) (hf : f = 0) (hg : g = 0) : is_zero Y :=
by { rw [hf, hg] at h, exact is_zero_of_exact_zero_zero h }

lemma is_zero_of_exact_is_zero_is_zero {C : Type*} [category C] [abelian C] {X Y Z : C}
  (f : X ⟶ Y) (g : Y ⟶ Z) (h : exact f g) (hX : is_zero X) (hZ : is_zero Z) : is_zero Y :=
is_zero_of_exact_zero_zero' f g h (hX.eq_of_src f _) (hZ.eq_of_tgt g _)

lemma is_zero_cokernel_of_epi {C : Type*} [category C] [abelian C] {X Y : C}
  (f : X ⟶ Y) [epi f] : is_zero (cokernel f) :=
begin
  have h1 : cokernel.π f = 0, by rwa ← abelian.epi_iff_cokernel_π_eq_zero,
  have h2 : exact (cokernel.π f) 0 := category_theory.exact_epi_zero (cokernel.π f),
  exact is_zero_of_exact_zero_zero' (cokernel.π f) 0 h2 h1 rfl,
end

lemma epi_iff_is_zero_cokernel {C : Type*} [category C] [abelian C] {X Y : C}
  (f : X ⟶ Y) : epi f ↔ is_zero (cokernel f) :=
begin
  split,
  { introsI, apply is_zero_cokernel_of_epi },
  { intros h,
    rw abelian.epi_iff_cokernel_π_eq_zero,
    apply h.eq_of_tgt }
end

lemma is_zero_kernel_of_mono {C : Type*} [category C] [abelian C] {X Y : C}
  (f : X ⟶ Y) [mono f] : is_zero (kernel f) :=
begin
  have h1 : kernel.ι f = 0, by rwa ← abelian.mono_iff_kernel_ι_eq_zero,
  have h2 : exact 0 (kernel.ι f) := category_theory.exact_zero_mono (kernel.ι f),
  exact is_zero_of_exact_zero_zero' 0 (kernel.ι f) h2 rfl h1
end

lemma mono_iff_is_zero_kernel {C : Type*} [category C] [abelian C] {X Y : C}
  (f : X ⟶ Y) : mono f ↔ is_zero (kernel f) :=
begin
  split,
  { introsI, apply is_zero_kernel_of_mono },
  { intros h,
    rw abelian.mono_iff_kernel_ι_eq_zero,
    apply h.eq_of_src }
end

noncomputable def image_iso_of_eq [category C] [abelian C] {A B : C} {f f' : A ⟶ B} (h : f = f') : image f ≅ image f' :=
eq_to_iso (by rw h)

noncomputable def image.is_iso_comp {𝓐 : Type*} [category 𝓐] [abelian 𝓐] {A B C : 𝓐} {f : A ⟶ B} [is_iso f] (g : B ⟶ C) : image (f ≫ g) ≅ image g :=
{ hom := image.lift (({ I := _,
  m := image.ι _,
  m_mono := infer_instance,
  e := f ≫ factor_thru_image g,
  fac' := by simp only [category.assoc, image.fac]} : mono_factorisation _)),
  inv := image.lift (({ I := _,
  m := image.ι _,
  m_mono := infer_instance,
  e := (inv f) ≫ factor_thru_image (f ≫ g),
  fac' := by simp only [category.assoc, image.fac, is_iso.inv_hom_id_assoc]} : mono_factorisation _)) }

lemma is_iso_of_is_zero_of_is_zero {𝓐 : Type*} [category 𝓐] [abelian 𝓐] {a b : 𝓐} (ha : is_zero a) (hb : is_zero b)
  (f : a ⟶ b) : is_iso f :=
begin
  rw is_zero.eq_zero_of_src ha f,
  apply (is_iso_zero_equiv a b).symm.to_fun,
  exact ⟨is_zero.eq_of_src ha (𝟙 a) 0, is_zero.eq_of_src hb (𝟙 b) 0⟩,
end

lemma obj_is_zero_of_iso {𝓐 : Type*} [category 𝓐] [abelian 𝓐] {𝓑 : Type*} [category 𝓑] [abelian 𝓑] {F G : 𝓐 ⥤ 𝓑}
  (h : F ≅ G) {a : 𝓐} (ha : is_zero (F.obj a)) : is_zero (G.obj a) :=
is_zero_of_iso_of_zero ha (h.app a)

lemma map_is_iso_of_iso_of_map_is_iso {𝓐 : Type*} [category 𝓐] [abelian 𝓐] {𝓑 : Type*} [category 𝓑] [abelian 𝓑] {F G : 𝓐 ⥤ 𝓑}
  (h : F ≅ G) {a₁ a₂ : 𝓐} (f : a₁ ⟶ a₂) (ha : is_iso (F.map f)) : is_iso (G.map f) :=
begin
  rw ← nat_iso.naturality_1 h,
  exact is_iso.comp_is_iso,
end

@[simp] lemma epi_comp_iso_iff_epi {V : Type*} [category V] {A B C : V} (e : A ≅ B) (f : B ⟶ C) :
  epi (e.hom ≫ f) ↔ epi f :=
begin
  split,
  { rintro ⟨h⟩,
    constructor,
    intros Z s t h2,
    apply h,
    simp [h2], },
  { rintro ⟨h⟩,
    constructor,
    intros Z s t h2,
    apply h,
    simpa using h2,
  },
end

@[simp] lemma epi_iso_comp_iff_epi {V : Type*} [category V] {A B C : V} (f : A ⟶ B) (e : B ≅ C) :
  epi (f ≫ e.hom) ↔ epi f :=
begin
  split,
  { introI h,
    constructor,
    intros Z s t h2,
    suffices : e.inv ≫ s = e.inv ≫ t,
      simpa,
    rw ← cancel_epi (f ≫ e.hom),
    simpa using h2, },
  { introI h,
    constructor,
    intros Z s t h2,
    simp only [category.assoc] at h2,
    rw cancel_epi at h2,
    rwa cancel_epi at h2, },
end

lemma is_iso_iff_is_iso_comp_left {V : Type*} [category V] {A B C : V} (f : A ⟶ B) {e : B ⟶ C}
  [is_iso f] : is_iso (f ≫ e) ↔ is_iso e :=
begin
  split,
  { introI h, exact is_iso.of_is_iso_comp_left f e },
  { introI h, exact is_iso.comp_is_iso },
end

lemma is_iso_iff_is_iso_comp_right {V : Type*} [category V] {A B C : V} {f : A ⟶ B} (g : B ⟶ C)
  [is_iso g] : is_iso (f ≫ g) ↔ is_iso f :=
begin
  split,
  { introI, exact is_iso.of_is_iso_comp_right f g},
  { introI h, exact is_iso_of_op (f ≫ g), },
end

@[simp] lemma epi_comp_is_iso_iff_epi {V : Type*} [category V] {A B C : V} (e : A ⟶ B) (f : B ⟶ C)
  [is_iso e] : epi (e ≫ f) ↔ epi f :=
epi_comp_iso_iff_epi (as_iso e) f

@[simp] lemma epi_is_iso_comp_iff_epi {V : Type*} [category V] {A B C : V} (f : A ⟶ B) (e : B ⟶ C)
  [is_iso e] : epi (f ≫ e) ↔ epi f :=
epi_iso_comp_iff_epi f (as_iso e)

lemma zero_of_epi_comp_zero {V : Type*} [category V] [abelian V]
  {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) [epi f] : g = 0 :=
(preadditive.epi_iff_cancel_zero f).mp infer_instance C g w

@[simp] lemma comp_mono_zero_iff {V : Type*} [category V] [abelian V]
  {A B C : V} {f : A ⟶ B} {g : B ⟶ C} [mono g] : f ≫ g = 0 ↔ f = 0 :=
⟨(preadditive.mono_iff_cancel_zero g).1 infer_instance A f, λ f, f.symm ▸ zero_comp⟩

lemma epi_of_epi_of_comp_epi_of_mono {V : Type*} [category V] [abelian V]
  {A B C : V} (f : A ⟶ B) (g : B ⟶ C) [epi (f ≫ g)] [mono g] : epi f :=
begin
  haveI foo : is_iso g,
  { rw is_iso_iff_mono_and_epi,
    refine ⟨infer_instance, _⟩,
    apply epi_of_epi f,
  },
  simp * at *,
end

lemma is_zero_initial {C : Type*} [category C] [abelian C] : is_zero (⊥_ C) :=
is_zero_of_iso_of_zero (is_zero_zero _) $
{ hom := 0,
  inv := 0 }

lemma is_zero_terminal {C : Type*} [category C] [abelian C] : is_zero (⊤_ C) :=
is_zero_of_iso_of_zero (is_zero_zero _) $
{ hom := 0,
  inv := 0 }

universes v u₁ u₂

class preserves_zero_objects {C D : Type*} [category C] [has_zero_morphisms C]
  [category D] [has_zero_morphisms D] (F : C ⥤ D) : Prop :=
(preserves : ∀ (X : C), is_zero X → is_zero (F.obj X))

instance preserves_zero_of_preserves_initial {C : Type u₁} {D : Type u₂}
  [category.{v} C] [abelian C] [category.{v} D] [abelian D] (F : C ⥤ D)
  [preserves_colimit (functor.empty C) F] :
  preserves_zero_objects F := preserves_zero_objects.mk $ λ X hX,
begin
  have e : X ≅ ⊥_ _ := hX.iso is_zero_initial,
  replace e : F.obj X ≅ F.obj ⊥_ _ := F.map_iso e,
  apply is_zero_of_iso_of_zero _ e.symm,
  have : F.obj ⊥_ _ ≅ ⊥_ _,
  { apply_with limits.preserves_initial.iso { instances := ff }, assumption },
  apply is_zero_of_iso_of_zero _ this.symm,
  exact is_zero_initial,
end

-- sanity check
example {C : Type u₁} {D : Type u₂}
  [category.{v} C] [abelian C] [category.{v} D] [abelian D] (F : C ⥤ D)
  [preserves_colimits F] : preserves_zero_objects F := infer_instance

instance preserves_zero_of_preserves_terminal {C : Type u₁} {D : Type u₂}
  [category.{v} C] [abelian C] [category.{v} D] [abelian D] (F : C ⥤ D)
  [preserves_limit (functor.empty C) F] :
  preserves_zero_objects F := preserves_zero_objects.mk $ λ X hX,
begin
  have e : X ≅ ⊤_ _ := hX.iso is_zero_terminal,
  replace e : F.obj X ≅ F.obj ⊤_ _ := F.map_iso e,
  apply is_zero_of_iso_of_zero _ e.symm,
  have : F.obj ⊤_ _ ≅ ⊤_ _,
  { apply_with limits.preserves_terminal.iso { instances := ff }, assumption },
  apply is_zero_of_iso_of_zero _ this.symm,
  exact is_zero_terminal,
end

-- sanity check
example {C : Type u₁} {D : Type u₂}
  [category.{v} C] [abelian C] [category.{v} D] [abelian D] (F : C ⥤ D)
  [preserves_limits F] : preserves_zero_objects F := infer_instance

lemma is_zero_of_preserves {C D : Type*} [category C] [has_zero_morphisms C]
  [category D] [has_zero_morphisms D] {X : C} (F : C ⥤ D)
  [preserves_zero_objects F] (e : is_zero X) : is_zero (F.obj X) :=
preserves_zero_objects.preserves _ e

lemma is_zero_biprod {C : Type u₁} [category.{v} C] [abelian C] (X Y : C)
  (hX : is_zero X) (hY : is_zero Y) : is_zero (biprod X Y) :=
begin
  constructor,
  { intro W, use 0, intro f, ext, simp, apply hX.eq_of_src, simp, apply hY.eq_of_src },
  { intro W, use 0, intro f, ext, simp, apply hX.eq_of_tgt, simp, apply hY.eq_of_tgt }
end

end limits

end category_theory
