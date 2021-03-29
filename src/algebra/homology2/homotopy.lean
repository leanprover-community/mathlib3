import algebra.homology2.additive
import algebra.category.Module.abelian
import algebra.category.Module.subobject

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

section

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_object V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

@[ext]
structure ihom (k : ℤ) (C D : homological_complex V c) :=
(h : Π i j, C.X i ⟶ D.X j)
(zero' : ∀ i j, ¬ c.r' k i j → h i j = 0 . obviously)

def ihom.to_pred {k : ℤ} (f : ihom k C D) (i j : ι) : C.X i ⟶ D.X_pred j := sorry
def ihom.from_succ {k : ℤ} (f : ihom k C D) (i j : ι) : C.X_succ i ⟶ D.X j := sorry

structure homotopy (f g : C ⟶ D) extends ihom (-1) C D :=
(comm' : ∀ i, to_ihom.to_pred i i ≫ D.d_to i + C.d_from i ≫ to_ihom.from_succ i i + g.f i = f.f i)

variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

theorem homology_map_eq_of_homotopy (h : homotopy f g) (i : ι) :
  (homology_functor V c i).map f = (homology_functor V c i).map g :=
begin
  dsimp [homology_functor, cycles_map],
  ext,
  dsimp,
  simp [←h.comm' i],
  apply eq_of_sub_eq_zero,
  rw [←preadditive.sub_comp],

  suffices h : ((D.cycles i).factor_thru ((C.cycles i).arrow ≫ h.to_ihom.to_pred i i ≫ D.d_to i) _) ≫ cokernel.π (D.boundaries_to_cycles i) = 0,
  sorry, -- interaction of factor_thru and preadditive
  dsimp [cycles],
  erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)],
  dsimp [boundaries_to_cycles],
  simp,
  dsimp [boundaries],
  rw [←category.assoc],
  apply image_subobject_factors_comp_self,
end

end

variables {R : Type v} [comm_ring R]

-- Generalize to any concrete category.
@[ext]
lemma cokernel_funext {M N K : Module R} {f : M ⟶ N} {g h : cokernel f ⟶ K}
  (w : ∀ (n : N), g (cokernel.π f n) = h (cokernel.π f n)) : g = h :=
begin
  apply coequalizer.hom_ext,
  ext,
  exact w x,
end

@[ext]
lemma cokernel_π_ext {M N : Module R} (f : M ⟶ N) {x y : N} (w : ∃ m, f m + x = y) :
  cokernel.π f x = cokernel.π f y :=
begin
  obtain ⟨m, rfl⟩ := w,
  simp,
end

def to_kernel_subobject {M N : Module R} {f : M ⟶ N} (m : M) (w : f m = 0) : kernel_subobject f :=
(kernel_subobject_iso f ≪≫ Module.kernel_iso_ker f).symm.to_linear_equiv.to_equiv ⟨m, w⟩

@[ext]
lemma subquotient_ext {L M N K : Module R} {f : L ⟶ M} {g : M ⟶ N} (w : f ≫ g = 0)
  {h k : subquotient w ⟶ K}
  (w : ∀ (m : M) (p : g m = 0),
    h (cokernel.π (image_to_kernel w) (to_kernel_subobject m p)) =
      k (cokernel.π (image_to_kernel w) (to_kernel_subobject m p))) : h = k :=
begin
  ext n,
  -- Gosh it would be nice if `equiv_rw` could directly use isomorphisms, or enriched `≃`.
  equiv_rw (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).to_linear_equiv.to_equiv at n,
  convert w n.1 n.2; simp,
end

variables {ι : Type*} {c : complex_shape ι} {C D : homological_complex (Module.{v} R) c}

namespace homological_complex

def to_cycles (C : homological_complex (Module.{v} R) c)
  {i : ι} (x : C.X i) (p : C.d_from i x = 0) : C.cycles i :=
to_kernel_subobject x p

@[simp] lemma to_cycles_arrow {C : homological_complex (Module.{v} R) c} {i : ι}
  (x : C.X i) (p : C.d_from i x = 0) : (C.cycles i).arrow (C.to_cycles x p) = x :=
begin
  simp [to_cycles],
  dsimp [to_kernel_subobject, cycles, kernel_subobject_iso],
  have := subobject.underlying_iso_arrow (kernel.ι (C.d_from i)),
  have := concrete_category.congr_hom this _,
  convert this,
end

@[ext] lemma cycles_ext {C : homological_complex (Module.{v} R) c} {i : ι}
  {x y : C.cycles i} (w : (C.cycles i).arrow x = (C.cycles i).arrow y) : x = y :=
sorry

end homological_complex

@[simp] lemma cycles_map_to_cycles (f : C ⟶ D) {i : ι} {x : C.X i} (p : C.d_from i x = 0) :
  (cycles_map f i) (C.to_cycles x p) = D.to_cycles (f.f i x) sorry :=
begin
  ext,
  simp,
end

def homological_complex.to_homology (C : homological_complex (Module.{v} R) c) {i : ι} (x : C.X i) (p : C.d_from i x = 0) : C.homology i :=
cokernel.π (image_to_kernel (C.d_to_comp_d_from i)) (C.to_cycles x p)

@[ext]
lemma from_homology_ext {M : Module R} (i : ι) {h k : C.homology i ⟶ M}
  (w : ∀ (x : C.X i) (p : C.d_from i x = 0), h (C.to_homology x p) = k (C.to_homology x p)) : h = k :=
subquotient_ext _ w

variables (f g : C ⟶ D)


theorem homology_map_eq_of_homotopy' (h : homotopy f g) (i : ι) :
  (homology_functor (Module.{v} R) c i).map f = (homology_functor (Module.{v} R) c i).map g :=
begin
  ext,
  dsimp [homology_functor, homology, homological_complex.to_homology],
  erw colimit.ι_desc_apply, -- a cokernel specific version?
  erw colimit.ι_desc_apply,
  simp only [function.comp_app, Module.coe_comp, category_theory.limits.cofork.of_π_ι_app],
  simp only [cycles_map_to_cycles],
  ext,
  refine ⟨_, _⟩, swap,
  ext,
  -- rw [←h.comm' i],
  -- simp,
  -- simp,
end
