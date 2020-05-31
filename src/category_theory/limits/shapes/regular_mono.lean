/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.strong_epi
import category_theory.limits.shapes.pullbacks

/-!
# Definitions and basic properties of regular and normal monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.
A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the constructions
* `split_mono → regular_mono`
* `normal_mono → regular_mono`, and
* `regular_mono → mono`
as well as the dual constructions for regular and normal epimorphisms. Additionally, we give the
construction
* `regular_epi ⟶ strong_epi`.

-/

namespace category_theory
open category_theory.limits

universes v₁ u₁

variables {C : Type u₁} [category.{v₁} C]

variables {X Y : C}

/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
class regular_mono (f : X ⟶ Y) :=
(Z : C)
(left right : Y ⟶ Z)
(w : f ≫ left = f ≫ right)
(is_limit : is_limit (fork.of_ι f w))

attribute [reassoc] regular_mono.w

/-- Every regular monomorphism is a monomorphism. -/
@[priority 100]
instance regular_mono.mono (f : X ⟶ Y) [regular_mono f] : mono f :=
mono_of_is_limit_parallel_pair regular_mono.is_limit

/-- Every split monomorphism is a regular monomorphism. -/
@[priority 100]
instance regular_mono.of_split_mono (f : X ⟶ Y) [split_mono f] : regular_mono f :=
{ Z     := Y,
  left  := 𝟙 Y,
  right := retraction f ≫ f,
  w     := by tidy,
  is_limit := split_mono_equalizes f }

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `regular_mono.left` and
    `regular_mono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def regular_mono.lift' {W : C} (f : X ⟶ Y) [regular_mono f] (k : W ⟶ Y)
  (h : k ≫ (regular_mono.left : Y ⟶ @regular_mono.Z _ _ _ _ f _) = k ≫ regular_mono.right) :
  {l : W ⟶ X // l ≫ f = k} :=
fork.is_limit.lift' regular_mono.is_limit _ h

/-- If `h` is a regular mono and `g` is a pullback of `h`, then `g` is a regular mono. -/
def regular_of_is_pullback_snd_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [hr : regular_mono h] (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk _ _ comm)) :
regular_mono g :=
{ Z := hr.Z,
  left := k ≫ hr.left,
  right := k ≫ hr.right,
  w := by rw [← reassoc_of comm, ← reassoc_of comm, hr.w],
  is_limit :=
  begin
    apply fork.is_limit.mk' _ _,
    intro s,
    have l₁ : (fork.ι s ≫ k) ≫ regular_mono.left = (fork.ι s ≫ k) ≫ regular_mono.right,
      rw [category.assoc, s.condition, category.assoc],
    obtain ⟨l, hl⟩ := fork.is_limit.lift' hr.is_limit _ l₁,
    obtain ⟨p, hp₁, hp₂⟩ := pullback_cone.is_limit.lift' t _ _ hl,
    refine ⟨p, hp₂, _⟩,
    intros m w,
    have z : m ≫ g = p ≫ g := w.trans hp₂.symm,
    apply t.hom_ext,
    apply (pullback_cone.mk f g comm).equalizer_ext,
    { erw [← cancel_mono h, category.assoc, category.assoc, comm, reassoc_of z] },
    { exact z },
  end }

/-- If `k` is a regular mono and `f` is a pullback of `k`, then `f` is a regular mono. -/
def regular_of_is_pullback_fst_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [hr : regular_mono k] (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk _ _ comm)) :
regular_mono f :=
{ Z := hr.Z,
  left := h ≫ hr.left,
  right := h ≫ hr.right,
  w := by rw [reassoc_of comm, reassoc_of comm, hr.w],
  is_limit :=
  begin
    apply fork.is_limit.mk' _ _,
    intro s,
    have l₁ : (s.ι ≫ h) ≫ hr.left = (s.ι ≫ h) ≫ hr.right,
      rw [category.assoc, s.condition, category.assoc],
    obtain ⟨l, hl⟩ := fork.is_limit.lift' hr.is_limit (fork.ι s ≫ h) l₁,
    obtain ⟨p, hp₁, hp₂⟩ := pullback_cone.is_limit.lift' t _ _ hl.symm,
    refine ⟨p, hp₁, _⟩,
    intros m w,
    have z : m ≫ f = p ≫ f := w.trans hp₁.symm,
    apply t.hom_ext,
    apply (pullback_cone.mk f g comm).equalizer_ext,
    { exact z },
    { erw [← cancel_mono k, category.assoc, category.assoc, ← comm, reassoc_of z] },
  end }

section
variables [has_zero_morphisms.{v₁} C]
/-- A normal monomorphism is a morphism which is the kernel of some morphism. -/
class normal_mono (f : X ⟶ Y) :=
(Z : C)
(g : Y ⟶ Z)
(w : f ≫ g = 0)
(is_limit : is_limit (kernel_fork.of_ι f w))

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

/-- If `h` is a normal mono and `g` is a pullback of `g`, then `g` is a normal mono. -/
def normal_of_is_pullback_snd_of_normal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
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

/-- If `k` is a normal mono and `f` is a pullback of `k`, then `f` is a normal mono. -/
def normal_of_is_pullback_fst_of_normal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [hn : normal_mono k] (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk _ _ comm)) :
normal_mono f :=
{ Z := hn.Z,
  g := h ≫ hn.g,
  w := by rw [reassoc_of comm, hn.w, has_zero_morphisms.comp_zero],
  is_limit :=
  begin
    letI fr := regular_of_is_pullback_fst_of_regular comm t,
    have q := (has_zero_morphisms.comp_zero h hn.Z).symm,
    convert fr.is_limit,
    dunfold kernel_fork.of_ι fork.of_ι,
    congr, exact q, exact q, exact q, apply proof_irrel_heq,
  end }

end
/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
class regular_epi (f : X ⟶ Y) :=
(W : C)
(left right : W ⟶ X)
(w : left ≫ f = right ≫ f)
(is_colimit : is_colimit (cofork.of_π f w))

attribute [reassoc] regular_epi.w

/-- Every regular epimorphism is an epimorphism. -/
@[priority 100]
instance regular_epi.epi (f : X ⟶ Y) [regular_epi f] : epi f :=
epi_of_is_colimit_parallel_pair regular_epi.is_colimit

/-- Every split epimorphism is a regular epimorphism. -/
@[priority 100]
instance regular_epi.of_split_epi (f : X ⟶ Y) [split_epi f] : regular_epi f :=
{ W     := X,
  left  := 𝟙 X,
  right := f ≫ section_ f,
  w     := by tidy,
  is_colimit := split_epi_coequalizes f }

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `regular_epi.left` and
    `regular_epi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def regular_epi.desc' {W : C} (f : X ⟶ Y) [regular_epi f] (k : X ⟶ W)
  (h : (regular_epi.left : regular_epi.W f ⟶ X) ≫ k = regular_epi.right ≫ k) :
  {l : Y ⟶ W // f ≫ l = k} :=
cofork.is_colimit.desc' (regular_epi.is_colimit) _ h

/-- If `g` is a regular epi and `h` is a pushout of `g`, then `h` is a regular epi. -/
def regular_of_is_pushout_snd_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [gr : regular_epi g] (comm : f ≫ h = g ≫ k) (t : is_colimit (pushout_cocone.mk _ _ comm)) :
regular_epi h :=
{ W := gr.W,
  left := gr.left ≫ f,
  right := gr.right ≫ f,
  w := by rw [category.assoc, category.assoc, comm, reassoc_of gr.w],
  is_colimit :=
  begin
    apply cofork.is_colimit.mk' _ _,
    intro s,
    have l₁ : gr.left ≫ f ≫ s.π = gr.right ≫ f ≫ s.π,
      rw [← category.assoc, ← category.assoc, s.condition],
    obtain ⟨l, hl⟩ := cofork.is_colimit.desc' gr.is_colimit (f ≫ cofork.π s) l₁,
    obtain ⟨p, hp₁, hp₂⟩ := pushout_cocone.is_colimit.desc' t _ _ hl.symm,
    refine ⟨p, hp₁, _⟩,
    intros m w,
    have z := w.trans hp₁.symm,
    apply t.hom_ext,
    apply (pushout_cocone.mk _ _ comm).coequalizer_ext,
    { exact z },
    { erw [← cancel_epi g, ← reassoc_of comm, ← reassoc_of comm, z], refl },
  end }

/-- If `f` is a regular epi and `k` is a pushout of `f`, then `k` is a regular epi. -/
def regular_of_is_pushout_fst_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [fr : regular_epi f] (comm : f ≫ h = g ≫ k) (t : is_colimit (pushout_cocone.mk _ _ comm)) :
regular_epi k :=
{ W := fr.W,
  left := fr.left ≫ g,
  right := fr.right ≫ g,
  w := by rw [category.assoc, category.assoc, ← comm, reassoc_of fr.w],
  is_colimit :=
  begin
    apply cofork.is_colimit.mk' _ _,
    intro s,
    have l₁ : fr.left ≫ g ≫ s.π = fr.right ≫ g ≫ s.π,
      rw [← category.assoc, ← category.assoc, s.condition],
    obtain ⟨l, hl⟩ := cofork.is_colimit.desc' fr.is_colimit (g ≫ cofork.π s) l₁,
    obtain ⟨p, hp₁, hp₂⟩ := pushout_cocone.is_colimit.desc' t _ _ hl,
    refine ⟨p, hp₂, _⟩,
    intros m w,
    have z := w.trans hp₂.symm,
    apply t.hom_ext,
    apply (pushout_cocone.mk _ _ comm).coequalizer_ext,
    { erw [← cancel_epi f, reassoc_of comm, reassoc_of comm, z], refl },
    { exact z },
  end }

@[priority 100]
instance strong_epi_of_regular_epi (f : X ⟶ Y) [regular_epi f] : strong_epi f :=
{ epi := by apply_instance,
  has_lift :=
  begin
    introsI,
    have : (regular_epi.left : regular_epi.W f ⟶ X) ≫ u = regular_epi.right ≫ u,
    { apply (cancel_mono z).1,
      simp only [category.assoc, h, regular_epi.w_assoc] },
    obtain ⟨t, ht⟩ := regular_epi.desc' f u this,
    exact ⟨t, ht, (cancel_epi f).1
      (by simp only [←category.assoc, ht, ←h, arrow.mk_hom, arrow.hom_mk'_right])⟩,
  end }

section
variables [has_zero_morphisms.{v₁} C]
/-- A normal epimorphism is a morphism which is the cokernel of some morphism. -/
class normal_epi (f : X ⟶ Y) :=
(W : C)
(g : W ⟶ X)
(w : g ≫ f = 0)
(is_colimit : is_colimit (cokernel_cofork.of_π f w))

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

/-- If `h` is a normal mono and `g` is a pullback of `g`, then `g` is a normal mono. -/
def normal_of_is_pushout_snd_of_normal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [gn : normal_epi g] (comm : f ≫ h = g ≫ k) (t : is_colimit (pushout_cocone.mk _ _ comm)) :
normal_epi h :=
{ W := gn.W,
  g := gn.g ≫ f,
  w := by rw [category.assoc, comm, reassoc_of gn.w, has_zero_morphisms.zero_comp],
  is_colimit :=
  begin
    letI hn := regular_of_is_pushout_snd_of_regular comm t,
    have q := (has_zero_morphisms.zero_comp gn.W f).symm,
    convert hn.is_colimit,
    dunfold cokernel_cofork.of_π cofork.of_π,
    congr, exact q, exact q, exact q, apply proof_irrel_heq,
  end }

/-- If `k` is a normal mono and `f` is a pullback of `k`, then `f` is a normal mono. -/
def normal_of_is_pushout_fst_of_normal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [hn : normal_mono k] (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk _ _ comm)) :
normal_mono f :=
{ Z := hn.Z,
  g := h ≫ hn.g,
  w := by rw [reassoc_of comm, hn.w, has_zero_morphisms.comp_zero],
  is_limit :=
  begin
    letI fr := regular_of_is_pullback_fst_of_regular comm t,
    have q := (has_zero_morphisms.comp_zero h hn.Z).symm,
    convert fr.is_limit,
    dunfold kernel_fork.of_ι fork.of_ι,
    congr, exact q, exact q, exact q, apply proof_irrel_heq,
  end }

end

end category_theory
