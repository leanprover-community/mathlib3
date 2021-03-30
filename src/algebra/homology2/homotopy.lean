import algebra.homology2.additive
import algebra.category.Module.abelian
import algebra.category.Module.subobject
import category_theory.limits.shapes.concrete_category

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
  dsimp [homology_functor],
  ext,
  simp,
  dunfold cycles_map,
  simp [←h.comm' i],
  apply eq_of_sub_eq_zero,
  rw [←preadditive.sub_comp],

  suffices h : ((D.cycles i).factor_thru ((C.cycles i).arrow ≫ h.to_ihom.to_pred i i ≫ D.d_to i) _) ≫ cokernel.π (D.boundaries_to_cycles i) = 0,
  { sorry, }, -- interaction of factor_thru and preadditive
  { dsimp [cycles],
    rw [←category.assoc], -- Need some sort of congruence lemma for factor_thru here.
    erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)],
    { simp,
      sorry, },
    { rw [←category.assoc],
      apply image_subobject_factors_comp_self, }, },
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
lemma cokernel_π_ext {M N : Module.{v} R} (f : M ⟶ N) {x y : N} (m : M) (w : f m + x = y) :
  cokernel.π f x = cokernel.π f y :=
begin
  subst w,
  simp,
end

@[ext]
lemma cokernel_π_image_subobject_ext {L M N : Module.{v} R}
  (f : L ⟶ M) (g : (image_subobject f : Module.{v} R) ⟶ N)
  {x y : N} (l : L) (w : g (factor_thru_image_subobject f l) + x = y) :
  cokernel.π g x = cokernel.π g y :=
begin
  subst w,
  simp,
end

def to_kernel {M N : Module R} {f : M ⟶ N} (m : M) (w : f m = 0) : (kernel f : Module R) :=
(Module.kernel_iso_ker f).symm.to_linear_equiv.to_equiv ⟨m, w⟩

@[simp] lemma to_kernel_kernel_ι {M N : Module R} {f : M ⟶ N} (m : M) (w : f m = 0) :
  (kernel.ι f) (to_kernel m w) = m :=
by simp [to_kernel]

def to_kernel_subobject {M N : Module R} {f : M ⟶ N} (m : M) (w : f m = 0) : kernel_subobject f :=
(kernel_subobject_iso f ≪≫ Module.kernel_iso_ker f).inv ⟨m, w⟩

@[simp] lemma to_kernel_subobject_arrow {M N : Module R} {f : M ⟶ N} (m : M) (w : f m = 0) :
  (kernel_subobject f).arrow (to_kernel_subobject m w) = m :=
sorry

/--
To prove that two maps out of a homology group are equal,
it suffices to check they are equal on the images of cycles.
-/
@[ext]
lemma homology_ext {L M N K : Module R} {f : L ⟶ M} {g : M ⟶ N} (w : f ≫ g = 0)
  {h k : homology f g w ⟶ K}
  (w : ∀ (m : M) (p : g m = 0),
    h (cokernel.π (image_to_kernel _ _ w) (to_kernel_subobject m p)) =
      k (cokernel.π (image_to_kernel _ _ w) (to_kernel_subobject m p))) : h = k :=
begin
  ext n,
  -- Gosh it would be nice if `equiv_rw` could directly use an isomorphism, or an enriched `≃`.
  equiv_rw (kernel_subobject_iso g ≪≫ Module.kernel_iso_ker g).to_linear_equiv.to_equiv at n,
  convert w n.1 n.2; simp [to_kernel_subobject],
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
  simp,
  -- erw is needed here because of the difference between `kernel_subobject` and `subobject.mk (kernel.ι ....)`
  -- erw subobject.underlying_iso_arrow_apply (kernel.ι (C.d_from i)),
  -- simp,
end

@[ext] lemma cycles_ext {C : homological_complex (Module.{v} R) c} {i : ι}
  {x y : C.cycles i} (w : (C.cycles i).arrow x = (C.cycles i).arrow y) : x = y :=
begin
  apply_fun (C.cycles i).arrow,
  exact w,
  sorry,
end

end homological_complex

@[simp] lemma cycles_map_to_cycles (f : C ⟶ D) {i : ι} {x : C.X i} (p : C.d_from i x = 0) :
  (cycles_map f i) (C.to_cycles x p) = D.to_cycles (f.f i x) sorry :=
begin
  ext,
  simp,
end

def homological_complex.to_homology (C : homological_complex (Module.{v} R) c) {i : ι} (x : C.X i) (p : C.d_from i x = 0) : C.homology i :=
cokernel.π (image_to_kernel _ _ (C.d_to_comp_d_from i)) (C.to_cycles x p)

@[ext]
lemma homological_complex.ext {M : Module R} (i : ι) {h k : C.homology i ⟶ M}
  (w : ∀ (x : C.X i) (p : C.d_from i x = 0), h (C.to_homology x p) = k (C.to_homology x p)) : h = k :=
homology_ext _ w

variables (f g : C ⟶ D)

attribute [elementwise] cokernel.π_desc

theorem homology_map_eq_of_homotopy' (h : homotopy f g) (i : ι) :
  (homology_functor (Module.{v} R) c i).map f = (homology_functor (Module.{v} R) c i).map g :=
begin
  -- To check two morphisms out of a homology group agree, it suffices to check on cycles:
  ext,
  dsimp [homology_functor, homological_complex.to_homology],
  simp,
  -- erw colimit.ι_desc_apply, -- a cokernel specific version?
  -- erw colimit.ι_desc_apply,
  -- simp only [function.comp_app, Module.coe_comp, category_theory.limits.cofork.of_π_ι_app],
  -- simp only [cycles_map_to_cycles],
  -- -- To check that two elements are equal mod coboundaries, it suffices to exhibit a coboundary:
  -- ext1,
  -- -- Moreover, to check that two cycles are equal, it suffices to check their underlying elements:
  -- ext1,
  -- simp only [homological_complex.to_cycles_arrow, linear_map.map_add],
  -- rw ←h.comm' i,
  -- simp only [function.comp_app, Module.coe_comp, linear_map.add_apply],
  -- -- Now we use `p : d x = 0` to get rid of a term:
  -- simp only [p, linear_map.map_zero, add_zero],
  -- -- Cancel the `g` terms:
  -- simp only [←add_assoc, add_left_eq_self],

  -- rw [←h.comm' i],
  -- simp,
  -- simp,
  sorry,
  sorry,
end
