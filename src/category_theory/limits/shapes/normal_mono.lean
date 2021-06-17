/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.shapes.regular_mono
import category_theory.limits.shapes.kernels

/-!
# Definitions and basic properties of normal monomorphisms and epimorphisms.

A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the construction `normal_mono → regular_mono` (`category_theory.normal_mono.regular_mono`)
as well as the dual construction for normal epimorphisms. We show equivalences reflect normal
monomorphisms (`category_theory.equivalence_reflects_normal_mono`), and that the pullback of a
normal monomorphism is normal (`category_theory.normal_of_is_pullback_snd_of_normal`).
-/

noncomputable theory

namespace category_theory
open category_theory.limits

universes v₁ u₁ u₂

variables {C : Type u₁} [category.{v₁} C]

variables {X Y : C}

section
variables [has_zero_morphisms C]
/-- A normal monomorphism is a morphism which is the kernel of some morphism. -/
class normal_mono (f : X ⟶ Y) :=
(Z : C)
(g : Y ⟶ Z)
(w : f ≫ g = 0)
(is_limit : is_limit (kernel_fork.of_ι f w))

section
local attribute [instance] fully_faithful_reflects_limits
local attribute [instance] equivalence.ess_surj_of_equivalence

/-- If `F` is an equivalence and `F.map f` is a normal mono, then `f` is a normal mono. -/
def equivalence_reflects_normal_mono {D : Type u₂} [category.{v₁} D] [has_zero_morphisms D]
  (F : C ⥤ D) [is_equivalence F] {X Y : C} {f : X ⟶ Y} (hf : normal_mono (F.map f)) :
  normal_mono f :=
{ Z := F.obj_preimage hf.Z,
  g := full.preimage (hf.g ≫ (F.obj_obj_preimage_iso hf.Z).inv),
  w := faithful.map_injective F $ by simp [reassoc_of hf.w],
  is_limit := reflects_limit.reflects $
    is_limit.of_cone_equiv (cones.postcompose_equivalence (comp_nat_iso F)) $
      is_limit.of_iso_limit
        (by exact is_limit.of_iso_limit
          (is_kernel.of_comp_iso _ _ (F.obj_obj_preimage_iso hf.Z) (by simp) hf.is_limit)
          (of_ι_congr (category.comp_id _).symm)) (iso_of_ι _).symm }

end

/-- Every normal monomorphism is a regular monomorphism. -/
@[priority 100]
instance normal_mono.regular_mono (f : X ⟶ Y) [I : normal_mono f] : regular_mono f :=
{ left := I.g,
  right := 0,
  w := (by simpa using I.w),
  ..I }

/-- If `f` is a normal mono, then any map `k : W ⟶ Y` such that `k ≫ normal_mono.g = 0` induces
    a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def normal_mono.lift' {W : C} (f : X ⟶ Y) [normal_mono f] (k : W ⟶ Y) (h : k ≫ normal_mono.g = 0) :
  {l : W ⟶ X // l ≫ f = k} :=
kernel_fork.is_limit.lift' normal_mono.is_limit _ h

/--
The second leg of a pullback cone is a normal monomorphism if the right component is too.

See also `pullback.snd_of_mono` for the basic monomorphism version, and
`normal_of_is_pullback_fst_of_normal` for the flipped version.
-/
def normal_of_is_pullback_snd_of_normal
  {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [hn : normal_mono h] (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk _ _ comm)) :
normal_mono g :=
{ Z := hn.Z,
  g := k ≫ hn.g,
  w := by rw [← reassoc_of comm, hn.w, has_zero_morphisms.comp_zero],
  is_limit :=
  begin
    letI gr := regular_of_is_pullback_snd_of_regular comm t,
    have q := (has_zero_morphisms.comp_zero k hn.Z).symm,
    convert gr.is_limit,
    dunfold kernel_fork.of_ι fork.of_ι,
    congr, exact q, exact q, exact q, apply proof_irrel_heq,
  end }

/--
The first leg of a pullback cone is a normal monomorphism if the left component is too.

See also `pullback.fst_of_mono` for the basic monomorphism version, and
`normal_of_is_pullback_snd_of_normal` for the flipped version.
-/
def normal_of_is_pullback_fst_of_normal
  {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [hn : normal_mono k] (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk _ _ comm)) :
normal_mono f :=
normal_of_is_pullback_snd_of_normal comm.symm (pullback_cone.flip_is_limit t)

end

section
variables [has_zero_morphisms C]
/-- A normal epimorphism is a morphism which is the cokernel of some morphism. -/
class normal_epi (f : X ⟶ Y) :=
(W : C)
(g : W ⟶ X)
(w : g ≫ f = 0)
(is_colimit : is_colimit (cokernel_cofork.of_π f w))

section
local attribute [instance] fully_faithful_reflects_colimits
local attribute [instance] equivalence.ess_surj_of_equivalence

/-- If `F` is an equivalence and `F.map f` is a normal epi, then `f` is a normal epi. -/
def equivalence_reflects_normal_epi {D : Type u₂} [category.{v₁} D] [has_zero_morphisms D]
  (F : C ⥤ D) [is_equivalence F] {X Y : C} {f : X ⟶ Y} (hf : normal_epi (F.map f)) :
  normal_epi f :=
{ W := F.obj_preimage hf.W,
  g := full.preimage ((F.obj_obj_preimage_iso hf.W).hom ≫ hf.g),
  w := faithful.map_injective F $ by simp [hf.w],
  is_colimit := reflects_colimit.reflects $
    is_colimit.of_cocone_equiv (cocones.precompose_equivalence (comp_nat_iso F).symm) $
      is_colimit.of_iso_colimit
        (by exact is_colimit.of_iso_colimit
          (is_cokernel.of_iso_comp _ _ (F.obj_obj_preimage_iso hf.W).symm (by simp) hf.is_colimit)
            (of_π_congr (category.id_comp _).symm))
        (iso_of_π _).symm }

end

/-- Every normal epimorphism is a regular epimorphism. -/
@[priority 100]
instance normal_epi.regular_epi (f : X ⟶ Y) [I : normal_epi f] : regular_epi f :=
{ left := I.g,
  right := 0,
  w := (by simpa using I.w),
  ..I }

/-- If `f` is a normal epi, then every morphism `k : X ⟶ W` satisfying `normal_epi.g ≫ k = 0`
    induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def normal_epi.desc' {W : C} (f : X ⟶ Y) [normal_epi f] (k : X ⟶ W) (h : normal_epi.g ≫ k = 0) :
  {l : Y ⟶ W // f ≫ l = k} :=
cokernel_cofork.is_colimit.desc' (normal_epi.is_colimit) _ h

/--
The second leg of a pushout cocone is a normal epimorphism if the right component is too.

See also `pushout.snd_of_epi` for the basic epimorphism version, and
`normal_of_is_pushout_fst_of_normal` for the flipped version.
-/
def normal_of_is_pushout_snd_of_normal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [gn : normal_epi g] (comm : f ≫ h = g ≫ k) (t : is_colimit (pushout_cocone.mk _ _ comm)) :
normal_epi h :=
{ W := gn.W,
  g := gn.g ≫ f,
  w := by rw [category.assoc, comm, reassoc_of gn.w, zero_comp],
  is_colimit :=
  begin
    letI hn := regular_of_is_pushout_snd_of_regular comm t,
    have q := (@zero_comp _ _ _ gn.W _ _ f).symm,
    convert hn.is_colimit,
    dunfold cokernel_cofork.of_π cofork.of_π,
    congr, exact q, exact q, exact q, apply proof_irrel_heq,
  end }

/--
The first leg of a pushout cocone is a normal epimorphism if the left component is too.

See also `pushout.fst_of_epi` for the basic epimorphism version, and
`normal_of_is_pushout_snd_of_normal` for the flipped version.
-/
def normal_of_is_pushout_fst_of_normal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [hn : normal_epi f] (comm : f ≫ h = g ≫ k) (t : is_colimit (pushout_cocone.mk _ _ comm)) :
normal_epi k :=
normal_of_is_pushout_snd_of_normal comm.symm (pushout_cocone.flip_is_colimit t)

end

open opposite
variables [has_zero_morphisms C]

/-- A normal mono becomes a normal epi in the opposite category. -/
def normal_epi_of_normal_mono_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : normal_mono f.unop) :
  normal_epi f :=
{ W := op m.Z,
  g := m.g.op,
  w := congr_arg quiver.hom.op m.w,
  is_colimit := is_colimit.of_π _ _
    (λ Z' g' w',
      (kernel_fork.is_limit.lift' m.is_limit g'.unop (congr_arg quiver.hom.unop w')).1.op)
    (λ Z' g' w',
      congr_arg quiver.hom.op
        (kernel_fork.is_limit.lift' m.is_limit g'.unop (congr_arg quiver.hom.unop w')).2)
    begin
      rintros Z' g' w' m' rfl,
      apply quiver.hom.unop_inj,
      apply m.is_limit.uniq (kernel_fork.of_ι (m'.unop ≫ f.unop) _) m'.unop,
      rintro (⟨⟩|⟨⟩); simp,
    end, }

/-- A normal epi becomes a normal mono in the opposite category. -/
def normal_mono_of_normal_epi_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : normal_epi f.unop) :
  normal_mono f :=
{ Z := op m.W,
  g := m.g.op,
  w := congr_arg quiver.hom.op m.w,
  is_limit := is_limit.of_ι _ _
    (λ Z' g' w',
      (cokernel_cofork.is_colimit.desc' m.is_colimit g'.unop (congr_arg quiver.hom.unop w')).1.op)
    (λ Z' g' w',
      congr_arg quiver.hom.op
        (cokernel_cofork.is_colimit.desc' m.is_colimit g'.unop (congr_arg quiver.hom.unop w')).2)
    begin
      rintros Z' g' w' m' rfl,
      apply quiver.hom.unop_inj,
      apply m.is_colimit.uniq (cokernel_cofork.of_π (f.unop ≫ m'.unop) _) m'.unop,
      rintro (⟨⟩|⟨⟩); simp,
    end, }

end category_theory
