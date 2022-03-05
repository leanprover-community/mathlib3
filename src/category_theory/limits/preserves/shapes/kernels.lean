/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.kernels
import category_theory.limits.preserves.shapes.equalizers
import category_theory.limits.preserves.shapes.zero

/-!
# Preserving (co)kernels

Constructions to relate the notions of preserving (co)kernels and reflecting (co)kernels
to concrete (co)forks.

In particular, we show that `kernel_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,0`, as well as the dual result.
-/

noncomputable theory

universes v u₁ u₂

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v} C] [has_zero_morphisms C]
variables {D : Type u₂} [category.{v} D] [has_zero_morphisms D]
variables (G : C ⥤ D) [functor.preserves_zero_morphisms G]

namespace category_theory.limits

section kernels
variables {X Y Z : C} {f : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = 0)

/--
The map of a kernel fork is a limit iff
the kernel fork consisting of the mapped morphisms is a limit.
This essentially lets us commute `kernel_fork.of_ι` with `functor.map_cone`.

This is a variant of `is_limit_map_cone_fork_equiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def is_limit_map_cone_fork_equiv' :
  is_limit (G.map_cone (kernel_fork.of_ι h w)) ≃
  is_limit (kernel_fork.of_ι (G.map h) (by simp only [←G.map_comp, w, functor.map_zero])
    : fork (G.map f) 0) :=
begin
  refine (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _),
  refine parallel_pair.ext (iso.refl _) (iso.refl _) _ _; simp,
  refine fork.ext (iso.refl _) _,
  simp,
end

/--
The property of preserving kernels expressed in terms of kernel forks.

This is a variant of `is_limit_fork_map_of_is_limit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def is_limit_fork_map_of_is_limit' [preserves_limit (parallel_pair f 0) G]
  (l : is_limit (kernel_fork.of_ι h w)) :
  is_limit (kernel_fork.of_ι (G.map h) (by simp only [←G.map_comp, w, functor.map_zero]) :
    fork (G.map f) 0) :=
is_limit_map_cone_fork_equiv' G w (preserves_limit.preserves l)

variables (f) [has_kernel f]

/--
If `G` preserves kernels and `C` has them, then the fork constructed of the mapped morphisms of
a kernel fork is a limit.
-/
def is_limit_of_has_kernel_of_preserves_limit [preserves_limit (parallel_pair f 0) G] :
  is_limit (fork.of_ι (G.map (kernel.ι f))
    (by simp only [←G.map_comp, equalizer.condition, comp_zero, functor.map_zero])
      : fork (G.map f) 0) :=
is_limit_fork_map_of_is_limit' G (kernel.condition f) (kernel_is_kernel f)

variables [has_kernel (G.map f)]

/--
If the kernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
kernel of `f`.
-/
def preserves_kernel.of_iso_comparison [i : is_iso (kernel_comparison f G)] :
  preserves_limit (parallel_pair f 0) G :=
begin
  apply preserves_limit_of_preserves_limit_cone (kernel_is_kernel f),
  apply (is_limit_map_cone_fork_equiv' G (kernel.condition f)).symm _,
  apply is_limit.of_point_iso (limit.is_limit (parallel_pair (G.map f) 0)),
  apply i,
end

variables [preserves_limit (parallel_pair f 0) G]
/--
If `G` preserves the kernel of `f`, then the kernel comparison map for `G` at `f` is
an isomorphism.
-/
def preserves_kernel.iso :
  G.obj (kernel f) ≅ kernel (G.map f) :=
is_limit.cone_point_unique_up_to_iso
  (is_limit_of_has_kernel_of_preserves_limit G f)
  (limit.is_limit _)

@[simp]
lemma preserves_kernel.iso_hom :
  (preserves_kernel.iso G f).hom = kernel_comparison f G :=
rfl

instance : is_iso (kernel_comparison f G) :=
begin
  rw ← preserves_kernel.iso_hom,
  apply_instance
end

end kernels

section cokernels

variables {X Y Z : C} {f : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = 0)

/--
The map of a cokernel cofork is a colimit iff
the cokernel cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cokernel_cofork.of_π` with `functor.map_cocone`.

This is a variant of `is_colimit_map_cocone_cofork_equiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def is_colimit_map_cocone_cofork_equiv' :
  is_colimit (G.map_cocone (cokernel_cofork.of_π h w)) ≃
  is_colimit (cokernel_cofork.of_π (G.map h) (by simp only [←G.map_comp, w, functor.map_zero])
    : cofork (G.map f) 0) :=
begin
  refine (is_colimit.precompose_hom_equiv _ _).symm.trans (is_colimit.equiv_iso_colimit _),
  refine parallel_pair.ext (iso.refl _) (iso.refl _) _ _; simp,
  refine cofork.ext (iso.refl _) _,
  simp, dsimp, simp,
end

/--
The property of preserving cokernels expressed in terms of cokernel coforks.

This is a variant of `is_colimit_cofork_map_of_is_colimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def is_colimit_cofork_map_of_is_colimit' [preserves_colimit (parallel_pair f 0) G]
  (l : is_colimit (cokernel_cofork.of_π h w)) :
  is_colimit (cokernel_cofork.of_π (G.map h) (by simp only [←G.map_comp, w, functor.map_zero]) :
    cofork (G.map f) 0) :=
is_colimit_map_cocone_cofork_equiv' G w (preserves_colimit.preserves l)

variables (f) [has_cokernel f]

/--
If `G` preserves cokernels and `C` has them, then the cofork constructed of the mapped morphisms of
a cokernel cofork is a colimit.
-/
def is_colimit_of_has_cokernel_of_preserves_colimit [preserves_colimit (parallel_pair f 0) G] :
  is_colimit (cofork.of_π (G.map (cokernel.π f))
    (by simp only [←G.map_comp, coequalizer.condition, zero_comp, functor.map_zero])
      : cofork (G.map f) 0) :=
is_colimit_cofork_map_of_is_colimit' G (cokernel.condition f) (cokernel_is_cokernel f)

variables [has_cokernel (G.map f)]

/--
If the cokernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
cokernel of `f`.
-/
def preserves_cokernel.of_iso_comparison [i : is_iso (cokernel_comparison f G)] :
  preserves_colimit (parallel_pair f 0) G :=
begin
  apply preserves_colimit_of_preserves_colimit_cocone (cokernel_is_cokernel f),
  apply (is_colimit_map_cocone_cofork_equiv' G (cokernel.condition f)).symm _,
  apply is_colimit.of_point_iso (colimit.is_colimit (parallel_pair (G.map f) 0)),
  apply i,
end

variables [preserves_colimit (parallel_pair f 0) G]
/--
If `G` preserves the cokernel of `f`, then the cokernel comparison map for `G` at `f` is
an isomorphism.
-/
def preserves_cokernel.iso :
  G.obj (cokernel f) ≅ cokernel (G.map f) :=
is_colimit.cocone_point_unique_up_to_iso
  (is_colimit_of_has_cokernel_of_preserves_colimit G f)
  (colimit.is_colimit _)

@[simp]
lemma preserves_cokernel.iso_hom :
  (preserves_cokernel.iso G f).inv = cokernel_comparison f G :=
rfl

instance : is_iso (cokernel_comparison f G) :=
begin
  rw ← preserves_cokernel.iso_hom,
  apply_instance
end

end cokernels

end category_theory.limits
