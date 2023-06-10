/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.strong_epi
import category_theory.limits.shapes.equalizers

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

We give the constructions
* `is_split_mono → regular_mono` and
* `regular_mono → mono`
as well as the dual constructions for regular epimorphisms. Additionally, we give the construction
* `regular_epi ⟶ strong_epi`.

We also define classes `regular_mono_category` and `regular_epi_category` for categories in which
every monomorphism or epimorphism is regular, and deduce that these categories are
`strong_mono_category`s resp. `strong_epi_category`s.

-/

noncomputable theory

namespace category_theory
open category_theory.limits

universes v₁ u₁ u₂

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
mono_of_is_limit_fork regular_mono.is_limit

instance equalizer_regular (g h : X ⟶ Y) [has_limit (parallel_pair g h)] :
  regular_mono (equalizer.ι g h) :=
{ Z := Y,
  left := g,
  right := h,
  w := equalizer.condition g h,
  is_limit := fork.is_limit.mk _ (λ s, limit.lift _ s) (by simp) (λ s m w, by { ext1, simp [←w] }) }

/-- Every split monomorphism is a regular monomorphism. -/
@[priority 100]
instance regular_mono.of_is_split_mono (f : X ⟶ Y) [is_split_mono f] : regular_mono f :=
{ Z     := Y,
  left  := 𝟙 Y,
  right := retraction f ≫ f,
  w     := by tidy,
  is_limit := is_split_mono_equalizes f }

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `regular_mono.left` and
    `regular_mono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def regular_mono.lift' {W : C} (f : X ⟶ Y) [regular_mono f] (k : W ⟶ Y)
  (h : k ≫ (regular_mono.left : Y ⟶ @regular_mono.Z _ _ _ _ f _) = k ≫ regular_mono.right) :
  {l : W ⟶ X // l ≫ f = k} :=
fork.is_limit.lift' regular_mono.is_limit _ h

/--
The second leg of a pullback cone is a regular monomorphism if the right component is too.

See also `pullback.snd_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_fst_of_regular` for the flipped version.
-/
def regular_of_is_pullback_snd_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S}
  {k : R ⟶ S} [hr : regular_mono h] (comm : f ≫ h = g ≫ k)
  (t : is_limit (pullback_cone.mk _ _ comm)) :
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

/--
The first leg of a pullback cone is a regular monomorphism if the left component is too.

See also `pullback.fst_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_snd_of_regular` for the flipped version.
-/
def regular_of_is_pullback_fst_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S}
  {k : R ⟶ S} [hr : regular_mono k] (comm : f ≫ h = g ≫ k)
  (t : is_limit (pullback_cone.mk _ _ comm)) :
regular_mono f :=
regular_of_is_pullback_snd_of_regular comm.symm (pullback_cone.flip_is_limit t)

@[priority 100]
instance strong_mono_of_regular_mono (f : X ⟶ Y) [regular_mono f] : strong_mono f :=
strong_mono.mk' begin
  introsI A B z hz u v sq,
  have : v ≫ (regular_mono.left : Y ⟶ regular_mono.Z f) = v ≫ regular_mono.right,
  { apply (cancel_epi z).1,
    simp only [regular_mono.w, ← reassoc_of sq.w] },
  obtain ⟨t, ht⟩ := regular_mono.lift' _ _ this,
  refine comm_sq.has_lift.mk' ⟨t, (cancel_mono f).1 _, ht⟩,
  simp only [arrow.mk_hom, arrow.hom_mk'_left, category.assoc, ht, sq.w],
end

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
lemma is_iso_of_regular_mono_of_epi (f : X ⟶ Y) [regular_mono f] [e : epi f] : is_iso f :=
is_iso_of_epi_of_strong_mono _

section
variables (C)

/-- A regular mono category is a category in which every monomorphism is regular. -/
class regular_mono_category :=
(regular_mono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [mono f], regular_mono f)

end

/-- In a category in which every monomorphism is regular, we can express every monomorphism as
    an equalizer. This is not an instance because it would create an instance loop. -/
def regular_mono_of_mono [regular_mono_category C] (f : X ⟶ Y) [mono f] : regular_mono f :=
regular_mono_category.regular_mono_of_mono _

@[priority 100]
instance regular_mono_category_of_split_mono_category [split_mono_category C] :
  regular_mono_category C :=
{ regular_mono_of_mono := λ _ _ f _,
  by { haveI := by exactI is_split_mono_of_mono f, apply_instance } }

@[priority 100]
instance strong_mono_category_of_regular_mono_category [regular_mono_category C] :
  strong_mono_category C :=
{ strong_mono_of_mono := λ _ _ f _,
    by { haveI := by exactI regular_mono_of_mono f, apply_instance } }

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
epi_of_is_colimit_cofork regular_epi.is_colimit

instance coequalizer_regular (g h : X ⟶ Y) [has_colimit (parallel_pair g h)] :
  regular_epi (coequalizer.π g h) :=
{ W := X,
  left := g,
  right := h,
  w := coequalizer.condition g h,
  is_colimit := cofork.is_colimit.mk _ (λ s, colimit.desc _ s) (by simp)
    (λ s m w, by { ext1, simp [←w] }) }

/-- Every split epimorphism is a regular epimorphism. -/
@[priority 100]
instance regular_epi.of_split_epi (f : X ⟶ Y) [is_split_epi f] : regular_epi f :=
{ W     := X,
  left  := 𝟙 X,
  right := f ≫ section_ f,
  w     := by tidy,
  is_colimit := is_split_epi_coequalizes f }

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `regular_epi.left` and
    `regular_epi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def regular_epi.desc' {W : C} (f : X ⟶ Y) [regular_epi f] (k : X ⟶ W)
  (h : (regular_epi.left : regular_epi.W f ⟶ X) ≫ k = regular_epi.right ≫ k) :
  {l : Y ⟶ W // f ≫ l = k} :=
cofork.is_colimit.desc' (regular_epi.is_colimit) _ h

/--
The second leg of a pushout cocone is a regular epimorphism if the right component is too.

See also `pushout.snd_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_fst_of_regular` for the flipped version.
-/
def regular_of_is_pushout_snd_of_regular
  {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
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

/--
The first leg of a pushout cocone is a regular epimorphism if the left component is too.

See also `pushout.fst_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_snd_of_regular` for the flipped version.
-/
def regular_of_is_pushout_fst_of_regular
  {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  [fr : regular_epi f] (comm : f ≫ h = g ≫ k) (t : is_colimit (pushout_cocone.mk _ _ comm)) :
regular_epi k :=
regular_of_is_pushout_snd_of_regular comm.symm (pushout_cocone.flip_is_colimit t)

@[priority 100]
instance strong_epi_of_regular_epi (f : X ⟶ Y) [regular_epi f] : strong_epi f :=
strong_epi.mk' begin
  introsI A B z hz u v sq,
  have : (regular_epi.left : regular_epi.W f ⟶ X) ≫ u = regular_epi.right ≫ u,
  { apply (cancel_mono z).1,
    simp only [category.assoc, sq.w, regular_epi.w_assoc] },
  obtain ⟨t, ht⟩ := regular_epi.desc' f u this,
  exact comm_sq.has_lift.mk' ⟨t, ht, (cancel_epi f).1
    (by simp only [←category.assoc, ht, ←sq.w, arrow.mk_hom, arrow.hom_mk'_right])⟩,
end

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
lemma is_iso_of_regular_epi_of_mono (f : X ⟶ Y) [regular_epi f] [m : mono f] : is_iso f :=
is_iso_of_mono_of_strong_epi _

section
variables (C)

/-- A regular epi category is a category in which every epimorphism is regular. -/
class regular_epi_category :=
(regular_epi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [epi f], regular_epi f)

end

/-- In a category in which every epimorphism is regular, we can express every epimorphism as
    a coequalizer. This is not an instance because it would create an instance loop. -/
def regular_epi_of_epi [regular_epi_category C] (f : X ⟶ Y) [epi f] : regular_epi f :=
regular_epi_category.regular_epi_of_epi _

@[priority 100]
instance regular_epi_category_of_split_epi_category [split_epi_category C] :
  regular_epi_category C :=
{ regular_epi_of_epi := λ _ _ f _, by { haveI := by exactI is_split_epi_of_epi f, apply_instance } }

@[priority 100]
instance strong_epi_category_of_regular_epi_category [regular_epi_category C] :
  strong_epi_category C :=
{ strong_epi_of_epi := λ _ _ f _, by { haveI := by exactI regular_epi_of_epi f, apply_instance } }

end category_theory
