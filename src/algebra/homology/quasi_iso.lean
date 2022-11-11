/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import algebra.homology.homology
import algebra.homology.homotopy
import category_theory.abelian.homology
import algebra.homology.homotopy_category
import category_theory.limits.preserves.shapes.images

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

## Future work

Define the derived category as the localization at quasi-isomorphisms?
-/

open category_theory
open category_theory.limits

universes v u

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_morphisms V] [has_zero_object V]
variables [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]
variables {c : complex_shape ι} {C D E : homological_complex V c}

/--
A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class quasi_iso (f : C ⟶ D) : Prop :=
(is_iso : ∀ i, is_iso ((homology_functor V c i).map f))

attribute [instance] quasi_iso.is_iso

@[priority 100]
instance quasi_iso_of_iso (f : C ⟶ D) [is_iso f] : quasi_iso f :=
{ is_iso := λ i, begin
    change is_iso (((homology_functor V c i).map_iso (as_iso f)).hom),
    apply_instance,
  end }

instance quasi_iso_comp (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso g] : quasi_iso (f ≫ g) :=
{ is_iso := λ i, begin
    rw functor.map_comp,
    apply_instance,
  end }

lemma quasi_iso_of_comp_left (f : C ⟶ D) [quasi_iso f] (g : D ⟶ E) [quasi_iso (f ≫ g)] :
  quasi_iso g :=
{ is_iso := λ i, is_iso.of_is_iso_fac_left ((homology_functor V c i).map_comp f g).symm }

lemma quasi_iso_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [quasi_iso g] [quasi_iso (f ≫ g)] :
  quasi_iso f :=
{ is_iso := λ i, is_iso.of_is_iso_fac_right ((homology_functor V c i).map_comp f g).symm }

namespace homotopy_equiv

section
variables {W : Type*} [category W] [preadditive W] [has_cokernels W] [has_images W]
  [has_equalizers W] [has_zero_object W] [has_image_maps W]

/-- An homotopy equivalence is a quasi-isomorphism. -/
lemma to_quasi_iso {C D : homological_complex W c} (e : homotopy_equiv C D) :
  quasi_iso e.hom :=
⟨λ i, begin
  refine ⟨⟨(homology_functor W c i).map e.inv, _⟩⟩,
  simp only [← functor.map_comp, ← (homology_functor W c i).map_id],
  split; apply homology_map_eq_of_homotopy,
  exacts [e.homotopy_hom_inv_id, e.homotopy_inv_hom_id],
end⟩

lemma to_quasi_iso_inv {C D : homological_complex W c} (e : homotopy_equiv C D) (i : ι) :
  (@as_iso _ _ _ _ _ (e.to_quasi_iso.1 i)).inv = (homology_functor W c i).map e.inv :=
begin
  symmetry,
  simp only [←iso.hom_comp_eq_id, as_iso_hom, ←functor.map_comp, ←(homology_functor W c i).map_id,
    homology_map_eq_of_homotopy e.homotopy_hom_inv_id _],
end

end

section to_single₀
variables {W : Type*} [category W] [abelian W]

section
variables {X : chain_complex W ℕ} {Y : W} (H : homotopy_equiv X ((chain_complex.single₀ _).obj Y))

/-- If a chain complex `X` is homotopy equivalent to a complex concentrated at 0 (for some
object `Y`), the cokernel of the differential `d : X₁ → X₀` is isomorphic to `Y.` -/
noncomputable def to_single₀_cokernel_at_zero : cokernel (X.d 1 0) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (H.to_quasi_iso.1 0)).trans
  ((chain_complex.homology_functor_0_single₀ W).app Y)))

lemma to_single₀_cokernel_at_zero_hom_eq :
  H.to_single₀_cokernel_at_zero.hom = cokernel.desc (X.d 1 0) (H.1.f 0)
    (by rw ←H.1.2 1 0 rfl; exact comp_zero) :=
begin
  ext,
  dunfold to_single₀_cokernel_at_zero chain_complex.homology_zero_iso homology_of_zero_right
    homology.map_iso chain_complex.homology_functor_0_single₀ cokernel.map,
  dsimp,
  simp only [cokernel.π_desc, category.assoc, homology.map_desc],
  simp only [←category.assoc, cokernel.π_desc],
  simp only [category.assoc, homology.desc, cokernel.π_desc],
  suffices : (iso.refl (X.X 0)).inv ≫ H.1.f 0 = H.1.f 0,
  begin
    by simpa,
  end,
  rw [iso.refl_inv, category.id_comp],
end

lemma to_single₀_f_0_epi :
  epi (H.hom.f 0) :=
begin
  constructor,
  intros Z g h Hgh,
  have : H.inv.f 0 ≫ H.hom.f 0 = 𝟙 _ := by rw [←homological_complex.comp_f, H.4.3 0]; simp,
  rw [←category.id_comp g, ←category.id_comp h, ←this,
    category.assoc, category.assoc, Hgh]
end

lemma to_single₀_exact_d_f_0 :
  exact (X.d 1 0) (H.hom.f 0) :=
begin
  rw preadditive.exact_iff_homology_zero,
  have h : X.d 1 0 ≫ H.hom.f 0 = 0,
  { simp only [← H.1.2 1 0 rfl, chain_complex.single₀_obj_X_d, comp_zero], },
  refine ⟨h, nonempty.intro (homology_iso_kernel_desc _ _ _ ≪≫ _)⟩,
  { suffices : is_iso (cokernel.desc _ _ h),
    { haveI := this, apply kernel.of_mono, },
      rw ←to_single₀_cokernel_at_zero_hom_eq,
      apply_instance }
end

lemma to_chain_complex_single₀_exact_succ (n : ℕ) :
  exact (X.d (n + 2) (n + 1)) (X.d (n + 1) n) :=
(preadditive.exact_iff_homology_zero _ _).2 ⟨X.d_comp_d _ _ _,
⟨(chain_complex.homology_succ_iso _ _).symm.trans
  ((homology_obj_iso_of_homotopy_equiv H _).trans homology_zero_zero)⟩⟩

end
section
variables {X : cochain_complex W ℕ} {Y : W}
  (H : homotopy_equiv X ((cochain_complex.single₀ _).obj Y))

/-- If a cochain complex `X` is homotopy equivalent to a complex concentrated at 0 (for some
object `Y`), the kernel of the differential `d : X₀ → X₁` is isomorphic to `Y.` -/
noncomputable def to_single₀_kernel_at_zero : kernel (X.d 0 1) ≅ Y :=
(X.homology_zero_iso.symm.trans ((@as_iso _ _ _ _ _ (H.to_quasi_iso.1 0)).trans
  ((cochain_complex.homology_functor_0_single₀ W).app Y)))

lemma to_single₀_kernel_at_zero_inv_eq :
  H.to_single₀_kernel_at_zero.inv = kernel.lift (X.d 0 1) (H.2.f 0)
    (by rw H.2.2 0 1 rfl; exact zero_comp) :=
begin
  ext,
  dunfold to_single₀_kernel_at_zero,
  simp only [iso.trans_inv, iso.app_inv, iso.symm_inv, category.assoc,
    equalizer_as_kernel, kernel.lift_ι, to_quasi_iso_inv],
  dunfold to_single₀_kernel_at_zero cochain_complex.homology_zero_iso homology_of_zero_left
    homology.map_iso cochain_complex.homology_functor_0_single₀ kernel.map,
  dsimp,
  simp only [category.assoc, homology.π_map, cokernel_zero_iso_target_hom,
    cokernel_iso_of_eq_hom_comp_desc, kernel_subobject_arrow, homology.π_map_assoc,
    is_iso.inv_comp_eq],
  rw [←category.assoc, ←category.assoc, ←kernel_subobject_map_comp, ←kernel_subobject_map_comp,
    ←category.assoc (homology.π _ _ _), homology.π],
  suffices : (kernel_subobject 0).arrow ≫ H.inv.f 0 ≫ (iso.refl (X.X 0)).hom
    = (kernel_subobject 0).arrow ≫ H.inv.f 0,
  begin
    simpa,
  end,
  rw [iso.refl_hom, category.comp_id],
end

lemma to_single₀_inv_f_0_mono :
  mono (H.inv.f 0) :=
begin
  constructor,
  intros Z g h Hgh,
  have : H.inv.f 0 ≫ H.hom.f 0 = 𝟙 _ := by rw [←homological_complex.comp_f, H.4.3 0]; simp,
    rw [←category.comp_id g, ←category.comp_id h, ←this,
    ←category.assoc, ←category.assoc, Hgh]
end

lemma to_single₀_exact_inv_f_d_0 :
  exact (H.inv.f 0) (X.d 0 1) :=
begin
  rw preadditive.exact_iff_homology_zero,
  have h : H.inv.f 0 ≫ X.d 0 1 = 0,
  { simp only [homological_complex.hom.comm, cochain_complex.single₀_obj_X_d, zero_comp] },
  refine ⟨h, nonempty.intro (homology_iso_cokernel_lift _ _ _ ≪≫ _)⟩,
  { suffices : is_iso (kernel.lift (X.d 0 1) (H.inv.f 0) h),
    { haveI := this, apply cokernel.of_epi },
    rw ←H.to_single₀_kernel_at_zero_inv_eq,
    apply_instance },
end

lemma to_cochain_complex_single₀_exact_succ (n : ℕ) :
  exact (X.d n (n + 1)) (X.d (n + 1) (n + 2)) :=
(preadditive.exact_iff_homology_zero _ _).2
  ⟨X.d_comp_d _ _ _, ⟨(cochain_complex.homology_succ_iso _ _).symm.trans
  ((homology_obj_iso_of_homotopy_equiv H _).trans homology_zero_zero)⟩⟩

end
end to_single₀
end homotopy_equiv
#where
variables {W : Type u} [category.{v} W] [abelian W]
  {U : Type u} [category.{v} U] [abelian U]
  (F : W ⥤ U)-- [faithful F]
  [functor.additive F]
  [preserves_finite_limits F] [preserves_finite_colimits F]
  (A B : homological_complex W c) (f : A ⟶ B)
#check reflects_isomorphisms
#check functor.preserves_finite_colimits_of_preserves_epis_and_kernels
#check homology_functor
#check cokernel_cofork
#check F.map_cocone
#check preserves_colimit.preserves
#check colimit.cocone (parallel_pair _ _)
#check is_limit.unique_up_to_iso
#check creates_colimit
#check parallel_pair
#check walking_parallel_pair
#check image
#check preserves_image.iso
#check image_subobject

variables (X : homological_complex W c)

noncomputable def map_X_next_iso {i j : ι} (h : c.rel i j) :
  ((F.map_homological_complex _).obj X).X_next i ≅ F.obj (X.X_next i) :=
(homological_complex.X_next_iso _ h).trans (F.map_iso (X.X_next_iso h).symm)

noncomputable def map_X_next_iso_self {i : ι} (h : ¬c.rel i (c.next i)) :
  ((F.map_homological_complex _).obj X).X_next i ≅ F.obj (X.X_next i) :=
(homological_complex.X_next_iso_self _ h).trans (F.map_iso (X.X_next_iso_self h).symm)

noncomputable def map_X_prev_iso {i j : ι} (h : c.rel i j) :
  ((F.map_homological_complex _).obj X).X_prev j ≅ F.obj (X.X_prev j) :=
(homological_complex.X_prev_iso _ h).trans (F.map_iso (X.X_prev_iso h).symm)

noncomputable def map_X_prev_iso_self {i : ι} (h : ¬c.rel (c.prev i) i) :
  ((F.map_homological_complex _).obj X).X_prev i ≅ F.obj (X.X_prev i) :=
(homological_complex.X_prev_iso_self _ h).trans (F.map_iso (X.X_prev_iso_self h).symm)

lemma map_d_to_eq {i j : ι} (h : c.rel i j) :
  ((F.map_homological_complex _).obj X).d_to j
  = (map_X_prev_iso F X h).hom ≫ F.map (X.d_to j) :=
by simpa only [map_X_prev_iso, ←F.map_comp, functor.map_iso_symm, iso.trans_hom, iso.symm_hom, functor.map_iso_inv, category.assoc,
  homological_complex.X_prev_iso_comp_d_to, ←iso.inv_comp_eq]

lemma map_d_from_eq {i j : ι} (h : c.rel i j) :
  ((F.map_homological_complex _).obj X).d_from i =
  F.map (X.d_from i) ≫ (map_X_next_iso F X h).inv :=
begin
  sorry,
  /-simp only [map_X_next_iso, functor.map_iso_symm, iso.trans_hom, iso.symm_hom,
  homological_complex.d_from_comp_X_next_iso_assoc, functor.map_homological_complex_obj_d,
  iso.comp_inv_eq, functor.map_iso_hom, ←F.map_comp, homological_complex.d_from_comp_X_next_iso],-/
end
#check kernel_iso_of_eq
#check preserves_kernel.iso
#check kernel_subobject
variables (i j k : ι) (hij : c.rel i j) (hjk : c.rel j k)
noncomputable def um1 : ↑(image_subobject (((F.map_homological_complex c).obj X).d_to j))
  ≅ F.obj ↑(image_subobject (X.d_to j)) :=
((image_subobject_iso _).trans ((((image.eq_to_iso (map_d_to_eq F X hij)).trans
    (as_iso (image.pre_comp _ _))).trans (preserves_image.iso _ _)).trans (F.map_iso (image_subobject_iso _).symm)))

noncomputable def um2 : ↑(kernel_subobject (((F.map_homological_complex c).obj X).d_from j))
  ≅ F.obj ↑(kernel_subobject (X.d_from j)) :=
((kernel_subobject_iso _).trans ((((kernel_iso_of_eq (map_d_from_eq F X hjk)).trans (kernel_comp_mono _ _)).trans
     (preserves_kernel.iso F _).symm).trans (F.map_iso (kernel_subobject_iso _).symm)))

lemma hmmm : image_to_kernel (((F.map_homological_complex c).obj X).d_to j)
  (((F.map_homological_complex c).obj X).d_from j) sorry ≫ (um2 F X j k hjk).hom = 0 :=
begin
  unfold um2,
  simp only [iso.trans_assoc, functor.map_iso_symm, iso.trans_hom, kernel_comp_mono_hom, iso.symm_hom, functor.map_iso_inv],

end

noncomputable def fucksake (i j k : ι) (hij : c.rel i j) (hjk : c.rel j k) :
  (parallel_pair (image_to_kernel (((F.map_homological_complex c).obj X).d_to j)
    (((F.map_homological_complex c).obj X).d_from j)
    (homological_complex.d_comp_d _ _ _ _)) 0)
  ≅ (parallel_pair (image_to_kernel (X.d_to j) (X.d_from j) (X.d_comp_d _ _ _)) 0 ⋙ F) :=
parallel_pair.ext (um1 F X i _ hij) (um2 _ _ _ k hjk)
_ _

def hmmmm (i : ι) (X : homological_complex W c) :
  colimit_cocone (parallel_pair (image_to_kernel (((F.map_homological_complex c).obj X).d_to i) (((F.map_homological_complex c).obj X).d_from i)
    (homological_complex.d_comp_d _ _ _ _)) 0) :=
{ cocone :=
  { X := colimit (parallel_pair (image_to_kernel (X.d_to i) (X.d_from i) (X.d_comp_d _ _ _)) 0 ⋙ F),
    ι :=
    { app := λ j,
      begin
        dsimp,
        cases j,
        dsimp,
      end,
      naturality' := _ } },
  is_colimit := _ }
/-
def umm (i : ι) :
  F.map_homological_complex c ⋙ homology_functor U c i ≅ homology_functor W c i ⋙ F :=
nat_iso.of_components
  (λ X,
  begin
    let H := colimit.cocone (parallel_pair (image_to_kernel
      (X.d_to i) (X.d_from i) (X.d_comp_d _ _ _)) 0),
    haveI Hl : is_colimit H := colimit.is_colimit _,
    let FH := F.map_cocone H,
    have FHl : is_colimit FH := preserves_colimit.preserves Hl,
    --dsimp,
    have := (is_colimit.cocone_point_unique_up_to_iso FHl (colimit.is_colimit _)).symm,
    dsimp,
    dunfold homological_complex.homology homology cokernel coequalizer,
    refine iso.trans _ this,
symm
    let l := is_colimit.get_colimit_cocone,
    let L := (X.homology i).get_colimit_cocone,
    have := F.map_cocone L,
    have : is_colimit (F.map_cocone (cokernel_cofork (image_to_kernel _ _ _)))),
    refine is_limit.cone_point_unique_up_to_iso _ _,

  end) _-/
#check preserves_limit
#check kernel_subobject
#check image.lift
#check homology.desc
#check kernel
#check image_to_kernel'
#check cokernel.map_iso
#check preserves_kernel.iso
#check kernel_subobject_iso
#check kernel_comparison
#check preserves_image.iso
#check mono.right_cancellation
/-{ hom := homology.desc _ _ _ (@is_limit.lift _ _ ≫ F.map ((kernel_subobject_iso _).inv ≫ homology.π _ _ _)) _,
  inv := _,
  hom_inv_id' := _,
  inv_hom_id' := _ }-/
#check arrow.hom_mk
lemma hmmkernel {X Y X' Y' : W} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (p : X ⟶ X') (q : Y ⟶ Y') (w : f ≫ q = p ≫ f') :
  kernel.map f f' p q w = (kernel_subobject_iso _).inv
    ≫ kernel_subobject_map (arrow.hom_mk w.symm) ≫ (kernel_subobject_iso _).hom :=
begin
  ext,
  simp only [kernel.lift_ι, category.assoc, kernel_subobject_arrow, kernel_subobject_map_arrow, arrow.hom_mk_left,
  kernel_subobject_arrow'_assoc],
end

def hmmmmm (i j k : ι) (hij : c.rel i j) (hjk : c.rel j k) :
  ((F.map_homological_complex _).obj X).homology j
    ≅ homology (F.map (X.d i j)) (F.map (X.d j k)) sorry :=
homology.map_iso _ _ (arrow.iso_mk (homological_complex.X_prev_iso _ hij) (iso.refl _)
$
begin
  simp only [arrow.mk_hom, iso.refl_hom],
  erw category.comp_id,
  symmetry,
  rw ←iso.inv_comp_eq,
  exact homological_complex.X_prev_iso_comp_d_to _ _,
end) (arrow.iso_mk (iso.refl _) (homological_complex.X_next_iso _ hjk) $
begin
  simp only [iso.refl_hom, arrow.mk_hom, category.id_comp, homological_complex.d_from_comp_X_next_iso,
  functor.map_homological_complex_obj_d],
end) $
begin
  simpa only [iso.refl_hom, arrow.iso_mk_hom_right, arrow.iso_mk_hom_left],
end

def hmm3 (i j : ι) (hij : c.rel i j) (hj : ¬c.rel j (c.next j)) :
  ((F.map_homological_complex _).obj X).homology j
  ≅ homology (F.map (X.d i j)) (0 : F.obj (X.X j) ⟶ F.obj (X.X j)) comp_zero :=
homology.map_iso _ _ (arrow.iso_mk (homological_complex.X_prev_iso _ hij) (iso.refl _)
(by {simp only [arrow.mk_hom, iso.refl_hom], erw category.comp_id, sorry }))
(arrow.iso_mk (iso.refl _) (homological_complex.X_next_iso_self _ hj) sorry) sorry

def hmm4 (j k : ι) (hj : ¬c.rel (c.prev j) j) (hjk : c.rel j k) :
  ((F.map_homological_complex _).obj X).homology j ≅
    homology (0 : F.obj (X.X j) ⟶ F.obj (X.X j)) (F.map (X.d j k)) sorry :=
homology.map_iso _ _ (arrow.iso_mk (homological_complex.X_prev_iso_self _ hj) (iso.refl _) sorry)
(arrow.iso_mk (iso.refl _) (homological_complex.X_next_iso _ hjk) sorry) sorry

noncomputable def hmmm6 (j : ι) :
  F.obj (X.homology j) ≅ ((F.map_homological_complex _).obj X).homology j :=
(preserves_cokernel.iso _ _).trans (cokernel.map_iso _ _
((F.map_iso (image_subobject_iso _)).trans $ ((preserves_image.iso _ _).symm.trans
  (image_subobject_iso _).symm))
  ((F.map_iso (kernel_subobject_iso _)).trans
    ((preserves_kernel.iso _ _).trans (kernel_subobject_iso _).symm)) $
begin
  refine @mono.right_cancellation _ _ _ _ (kernel_subobject (F.map _)).arrow _ _ _ _ _,
    dsimp,
    rw ←category.assoc,
    rw ←category.assoc,
    rw ←F.map_comp,
    have : image_to_kernel (X.d_to j) (X.d_from j) sorry ≫ (kernel_subobject_iso (X.d_from j)).hom =
      kernel.lift (X.d_from j) (image_subobject (X.d_to j)).arrow sorry,
    begin
      ext,
      simp only [category.assoc, kernel_subobject_arrow, image_to_kernel_arrow, kernel.lift_ι],
    end,
      rw this,
      rw map_lift_kernel_comparison,
      simp only [category.assoc, kernel_subobject_arrow', kernel.lift_ι],
      erw image_to_kernel_arrow,
      erw image_subobject_arrow',
      rw is_image.lift_ι,
      simp only [←F.map_comp, image_subobject_arrow],
end)

#check cokernel_comparison
#check homology.ι
#check kernel.map
#check kernel.lift
#check kernel_comparison
#check kernel.map
#check homology_iso_kernel_desc
#check kernel_subobject_map
def hmmm7 (j : ι) :
  F.map_homological_complex _ ⋙ homology_functor U c j ≅ homology_functor W c j ⋙ F :=
nat_iso.of_components (λ X, (hmmm6 _ _ _).symm) $
begin
  intros X Y f,
  unfold hmmm6,
  dsimp,
  simp only [homological_complex.d_to_comp_d_from, category.assoc],
  unfold homology.map,
  rw cokernel_comparison_map_desc,
  unfold cokernel_comparison,
  refine (cokernel.map_desc _ _ _ _ _ _ _ _ _ _ _).symm,
  rw category.assoc,
  dunfold cokernel.map,
  rw ←category.assoc (cokernel.π _),
  rw cokernel.π_desc,
  rw category.assoc,
  rw cokernel.π_desc,
  simp only [category.assoc],
  rw ←iso.inv_comp_eq,
  symmetry,
  rw iso.inv_comp_eq,
  simp only [functor.map_comp, preserves_kernel.iso_hom, coequalizer_as_cokernel],
  simp only [←category.assoc],
  rw category.assoc _ (kernel_subobject_iso _).inv,
  rw category.assoc (kernel_comparison _ _),
  have : (kernel_subobject_iso (F.map (X.d_from j))).inv ≫
    kernel_subobject_map (homological_complex.hom.sq_from
     ((F.map_homological_complex c).map f) j) ≫
    (kernel_subobject_iso (F.map (Y.d_from j))).hom =
    kernel.map (F.map (X.d_from j)) (F.map (Y.d_from j))
    (((F.map_homological_complex _).map f).f j)
    (((F.map_homological_complex _).map f).next j) sorry :=
  begin
    ext, simp only [category.assoc, kernel_subobject_arrow, functor.map_homological_complex_map_f, kernel.lift_ι],
    rw iso.inv_comp_eq,
    rw ←category.assoc,
    rw kernel_subobject_arrow,
    convert kernel_subobject_map_arrow _,
  end,


end







#exit
begin
  intros X Y f,
  unfold hmmm6,
  simp only [homological_complex.d_to_comp_d_from, iso.trans_hom, functor.map_iso_hom, preserves_kernel.iso_hom, iso.symm_hom,
  preserves_image.iso_inv, functor.comp_map, homology_functor_map, cokernel.map_iso_hom, category.assoc],
  unfold homology.map,
  rw ←iso.inv_comp_eq,
  rw preserves_cokernel.iso_inv,
  rw ←category.assoc,
  rw cokernel_comparison_map_desc,
  refine (cokernel.map_desc _ _ _ _ _ _ _ _ _ _ _).symm,
  simp only [category.assoc],
  unfold kernel_comparison,
  have : F.map (kernel_subobject_iso (X.d_from j)).hom ≫
    kernel.lift (F.map (X.d_from j)) (F.map (kernel.ι (X.d_from j))) sorry =
    kernel.lift (F.map (X.d_from j)) (F.map ((kernel_subobject_iso (X.d_from j)).hom ≫ (kernel.ι (X.d_from j)))) sorry :=
  begin
    ext,
    simp only [category.assoc, kernel.lift_ι, kernel_subobject_arrow],
    rw ←F.map_comp,
    rw kernel_subobject_arrow,
  end,
  simp only [←category.assoc],
  rw this,

  --rw kernel_subobject
end

def fucksake2 (i j k : ι) (hij : c.rel i j) (hjk : c.rel j k) :
  F.obj (homology (X.d i j) (X.d j k) sorry) ≅ homology (F.map (X.d i j)) (F.map (X.d j k)) sorry :=
(preserves_cokernel.iso _ _).trans (cokernel.map_iso _ _
((F.map_iso (image_subobject_iso _)).trans $ ((preserves_image.iso _ _).symm.trans
  (image_subobject_iso _).symm))
  ((F.map_iso (kernel_subobject_iso _)).trans
    ((preserves_kernel.iso _ _).trans (kernel_subobject_iso _).symm)) $
  begin

    refine @mono.right_cancellation _ _ _ _ (kernel_subobject (F.map (X.d j k))).arrow _ _ _ _ _,
    dsimp,
    rw ←category.assoc,
    rw ←category.assoc,
    rw ←F.map_comp,
    have : image_to_kernel (X.d i j) (X.d j k) sorry ≫ (kernel_subobject_iso (X.d j k)).hom =
      kernel.lift (X.d j k) (image_subobject (X.d i j)).arrow sorry,
    begin
      ext,
      simp only [category.assoc, kernel_subobject_arrow, image_to_kernel_arrow, kernel.lift_ι],
    end,
      rw this,
      rw map_lift_kernel_comparison,
    simp only [category.assoc, kernel_subobject_arrow', kernel.lift_ι, image_to_kernel_arrow, image_subobject_arrow',
  is_image.lift_ι],
     rw ←F.map_comp,
     simp only [image_subobject_arrow],
  end)

def hmm5 (X : chain_complex W ℕ) : Π i : ℕ,
  ((F.map_homological_complex _).obj X).homology i ≅ F.obj (X.homology i) :=

#exit
iso.trans (cokernel.map_iso _ _ ((image_subobject_iso _).trans ((preserves_image.iso _ _).trans
  (F.map_iso (image_subobject_iso _).symm))).symm
  ((kernel_subobject_iso _).trans ((preserves_kernel.iso _ _).symm.trans
  (F.map_iso (kernel_subobject_iso _).symm))).symm $
  begin
    dsimp,
    rw preserves_kernel.iso_hom,
    unfold kernel_comparison,
    unfold kernel_subobject_iso,
    have := kernel.lift
    show _ ≫ (_ ≫ _ ≫ _) = _,
    --unfold preserves_kernel.iso,
  sorry,
  end) (preserves_cokernel.iso F _).symm
instance djksfdhsk (hf : quasi_iso ((F.map_homological_complex _).map f)) :
  quasi_iso f :=
{ is_iso := λ i,
  begin
    have H := hf.is_iso i,

    apply_instance,
  end }
