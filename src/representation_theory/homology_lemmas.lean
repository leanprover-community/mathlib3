import algebraic_topology.extra_degeneracy
import category_theory.preadditive.projective_resolution
import algebra.category.Module.abelian
import category_theory.abelian.homology

universes v u
open category_theory category_theory.limits
open_locale zero_object
noncomputable theory
variables {k : Type u} [comm_ring k] (C : chain_complex (Module.{u} k) ℕ)
  (X : Module.{u} k) (H : homotopy_equiv C ((chain_complex.single₀ _).obj X))

def single₀_succ_homology (n : ℕ) :
  ((chain_complex.single₀ _).obj X).homology (n + 1) ≅ 0 := homology_zero_zero

def single₀_zero_homology :
  ((chain_complex.single₀ _).obj X).homology 0 ≅ X := homology_zero_zero

def homology_of_zero_right {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  {X Y Z : V} (f : X ⟶ Y) :
  homology f (0 : Y ⟶ Z) comp_zero ≅ cokernel f :=
{ hom := homology.desc _ _ _ ((kernel_subobject 0).arrow ≫ cokernel.π f) sorry,
  inv := cokernel.desc _ (((kernel_subobject_iso 0).trans
    kernel_zero_iso_source).inv ≫ cokernel.π _) sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

variables {X} {Y Z : Module.{u} k} (W : Module.{u} k) (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0)

def chain_complex.zeroth {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  (C : chain_complex V ℕ) :
  C.homology 0 ≅ homology (C.d 1 0) (0 : C.X 0 ⟶ C.X_next 0) comp_zero :=
homology.map_iso _ _ (arrow.iso_mk (C.X_prev_iso rfl) (iso.refl _) $
by rw C.d_to_eq rfl; exact (category.comp_id _).symm)
  (arrow.iso_mk (iso.refl _) (iso.refl _) $
by simp [C.d_from_eq_zero (λ (h : _ = _), one_ne_zero $ by rwa chain_complex.next_nat_zero at h)])
rfl

def chain_complex.zeroth' {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  (C : chain_complex V ℕ) :
  C.homology 0 ≅ cokernel (C.d 1 0) :=
C.zeroth.trans $ homology_of_zero_right _

def chain_complex.succth {V : Type u} [category.{v} V] [has_zero_object V]
  [has_zero_morphisms V] [has_kernels V] [has_images V] [has_cokernels V]
  (C : chain_complex V ℕ) (n : ℕ) :
  C.homology (n + 1) ≅ homology (C.d (n + 2) (n + 1)) (C.d (n + 1) n) (C.d_comp_d _ _ _) :=
homology.map_iso _ _ (arrow.iso_mk (C.X_prev_iso rfl) (iso.refl _) $ by dsimp;
  rw [C.d_to_eq rfl, category.comp_id])
(arrow.iso_mk (iso.refl _) (C.X_next_iso rfl) $ by dsimp; rw [C.d_from_comp_X_next_iso rfl,
   category.id_comp]) rfl

def cokernel_iso : cokernel (C.d 1 0) ≅ X :=
(homology_of_zero_right _).symm.trans $ (C.zeroth.symm.trans
  (homology_obj_iso_of_homotopy_equiv H 0)).trans homology_zero_zero

def cokernel.ext (f : X ⟶ Y) (g h : cokernel f ⟶ Z) (H : cokernel.π f ≫ g = cokernel.π f ≫ h) :
  g = h :=
coequalizer.hom_ext H

-- well that was incredibly painful.
lemma desc_factor : cokernel.desc (C.d 1 0) (H.1.f 0) sorry = (cokernel_iso C H).hom :=
begin
  show _ = cokernel.desc _ _ _ ≫ ((homology.map _ _ _ _ _ ≫ homology.map _ _ _ _ _) ≫ _),
  refine cokernel.ext _ _ _ _,
  rw [homology.map_comp, cokernel.π_desc, ←category.assoc, cokernel.π_desc, homology.map,
    category.assoc _ (cokernel.π _), ←category.assoc _ (cokernel.desc _ _ _), cokernel.π_desc],
  dsimp,
  rw [category.assoc _ (cokernel.π _), homology.desc],
  erw cokernel.π_desc,
  simp only [kernel_zero_iso_source_inv, kernel_subobject_map_comp, category.assoc],
  ext,
  dsimp,
  simp only [homological_complex.hom.sq_from_left, kernel_subobject_map_arrow_apply, arrow.iso_mk_inv_left, kernel_subobject_arrow'_apply, kernel.lift_ι_apply,
  Module.id_apply],
  refl,
end
lemma grrrr (n : ℕ) :
  C.homology (n + 1) ≅ 0 :=
(homology_obj_iso_of_homotopy_equiv H (n + 1)).trans homology_zero_zero

noncomputable def huh : ProjectiveResolution X :=
{ complex := C,
  π := H.1,
  projective := sorry,
  exact₀ := (preadditive.exact_iff_homology_zero _ _).2
  ⟨sorry, ⟨(homology_iso_kernel_desc _ _ _).trans $ @kernel.of_mono _ _ _ _ _ _ _ _ $
  begin
    rw desc_factor,
    exact is_iso.mono_of_iso _,
  end⟩⟩,
  exact := λ n, (preadditive.exact_iff_homology_zero _ _).2 ⟨C.d_comp_d _ _ _,
    ⟨(C.succth _).symm.trans $
      (homology_obj_iso_of_homotopy_equiv H (n + 1)).trans homology_zero_zero⟩⟩,
  epi := sorry }
