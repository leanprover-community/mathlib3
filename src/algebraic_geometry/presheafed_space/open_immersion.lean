/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.presheafed_space.has_colimits
import category_theory.limits.shapes.binary_products

/-!
# Open immersions of presheafed spaces

We say that a morphism of presheaved spaces `f : X ⟶ Y` is an open immersions if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`, and `f` factors through
`of_restrict : Y|ᵤ ⟶ Y` via some isomorphism `X ≅ Y|ᵤ`.

We also proves that the pullback of two presheaved spaces exists, and is also an open immersion.

## Main definitions

* `algebraic_geometry.PresheafedSpace.open_immersion`: A structure `(f : X ⟶ Y) → Type*` asserting
  that `f` is an open immersion.
* `algebraic_geometry.PresheafedSpace.open_immersion.comp`: The composition of two open immersions
  is an open immersion.
* `algebraic_geometry.PresheafedSpace.open_immersion.of_iso`: An isomorphism is an open immersion.
* `algebraic_geometry.PresheafedSpace.open_immersion.pullback_cone_of_open_immersion`:
  The constructed limit cone of the pullback.
* `algebraic_geometry.PresheafedSpace.open_immersion.pullback`: An abbreviation of `pullback`.
  Unlocks the `pullback` API.
* `algebraic_geometry.PresheafedSpace.open_immersion.pullback_imm_open_immersion`:
  The pullback is an open immersion.
-/


open topological_space category_theory opposite
open category_theory.limits algebraic_geometry
namespace algebraic_geometry.PresheafedSpace

universes v u

variables {C : Type u} [category.{v} C]

/--
An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, and an isomorphism between the structure sheaves `𝒪ₓ ≅ 𝒪|ᵤ`, such that `f` factors through
`of_restrict : 𝒪|ᵤ ⟶ 𝒪_Y`.
-/
@[nolint has_inhabited_instance]
structure open_immersion {X Y : PresheafedSpace C} (f : X ⟶ Y) :=
(base_open : open_embedding f.base)
(iso_restrict : X ≅ Y.restrict base_open)
(fac : iso_restrict.hom ≫ Y.of_restrict _ = f)

attribute [simp] open_immersion.fac

namespace open_immersion

variables {X Y : PresheafedSpace C} {f : X ⟶ Y} (H : open_immersion f)

@[simp] lemma inv_fac : H.iso_restrict.inv ≫ f = Y.of_restrict _ :=
by { rw iso.inv_comp_eq, simp }

@[elementwise, simp]
lemma iso_restrict_hom_base : H.iso_restrict.hom.base = 𝟙 _ :=
begin
  haveI := (Top.mono_iff_injective f.base).mpr H.base_open.inj,
  rw ←cancel_mono f.base,
  refine (congr_arg PresheafedSpace.hom.base H.fac).trans (category.id_comp _).symm,
end

@[elementwise, simp]
lemma iso_restrict_inv_base : H.iso_restrict.inv.base = 𝟙 _ :=
begin
  convert congr_arg PresheafedSpace.hom.base H.iso_restrict.hom_inv_id using 1,
  simp only [PresheafedSpace.comp_base, iso_restrict_hom_base, category.id_comp]
end

/-- The isomorphism of structure sheaves. -/
def c_iso : X.presheaf ≅ (Y.restrict H.base_open).presheaf :=
PresheafedSpace.sheaf_iso_of_iso H.iso_restrict.symm ≪≫
iso_whisker_right (eq_to_iso
  (by { rw [iso_restrict_inv_base], apply functor.hext; simp }) :
    (opens.map H.iso_restrict.inv.base).op ⋙
      (is_open_map.functor _).op ≅ (is_open_map.functor _).op) (Y.presheaf)

@[elementwise, reassoc, simp]
lemma c_app_comp_iso_restrict_hom_c_app (U : opens (X.carrier)) :
  H.iso_restrict.hom.c.app (op U) =
  f.c.app (op (H.base_open.is_open_map.functor.obj U)) ≫ X.presheaf.map
    (eq_to_hom (by { dsimp only [opens.map, functor.op], congr' 2,
      erw set.preimage_image_eq _ H.base_open.inj, simpa })) :=
begin
  have := PresheafedSpace.congr_app H.fac (op (H.base_open.is_open_map.functor.obj U)),
  generalize_proofs _ _ h at this,
  have := congr_arg (λ x, x ≫ X.presheaf.map (eq_to_hom h.symm)) this,
  simp only [eq_to_hom_refl, category.assoc, ← X.presheaf.map_comp,
    eq_to_hom_trans, X.presheaf.map_id] at this,
  erw category.comp_id at this,
  rw [←this, category.assoc, ←functor.map_comp, eq_to_hom_trans, ←is_iso.comp_inv_eq],
  simp only [PresheafedSpace.comp_c_app, PresheafedSpace.of_restrict_c_app, inv_eq_to_hom,
    ←functor.map_inv],
  have h' := H.iso_restrict.hom.c.naturality,
  dsimp [-forall_3_true_iff] at h',
  convert (h' _).symm using 2,
  swap 4,
  { dsimp only [functor.op],
    apply quiver.hom.op, apply hom_of_le,
    rintros _ ⟨_, hx, eq⟩,
    cases H.base_open.inj eq,
    exact hx },
  { congr },
  { congr },
  { congr, simp }
end

@[simp, elementwise, reassoc]
lemma c_app_comp_iso_restrict_inv_c_app (U : opens (Y.carrier)) :
f.c.app (op U) ≫ H.iso_restrict.inv.c.app (op ((opens.map f.base).obj (unop (op U)))) =
  Y.presheaf.map ((@hom_of_le (opens Y.1) _ ⟨_, _⟩ U
  (by { rintros _ ⟨x, hx₂, rfl⟩, simpa using hx₂ })).op) :=
begin
  have := PresheafedSpace.congr_app H.inv_fac (op U),
  simp only [PresheafedSpace.restrict, PresheafedSpace.comp_c_app,
    PresheafedSpace.of_restrict_c_app] at this,
  erw ←functor.map_comp at this,
  convert this
end

lemma eq_to_hom_heq_id {C : Type*} [category C] {X Y Z : C} (H : X = Y) (H' : Y = Z) :
  eq_to_hom H == 𝟙 Z := by { cases H, cases H', refl }

lemma heq_of_subsingleton (α β : Type*) [subsingleton α] (x : α) (y : β)
   (H : α = β) : x == y := by { cases H, simp, }

lemma c_app_comp_iso_restrict_inv_c_app' (U : opens X) :
  f.c.app (op (H.base_open.is_open_map.functor.obj U)) ≫
  X.presheaf.map
    (eq_to_hom (by { cases U, simp [opens.map, set.preimage_image_eq U_val H.base_open.inj] })) ≫
  H.iso_restrict.inv.c.app (op U) =
  Y.presheaf.map ((@eq_to_hom (opens Y.1) _ ⟨_, _⟩ (H.base_open.is_open_map.functor.obj U)
  (by simpa)).op) :=
begin
  have : op U = (opens.map f.base).op.obj (op (H.base_open.is_open_map.functor.obj U)),
  { cases U, simp [opens.map, set.preimage_image_eq U_val H.base_open.inj] },
  convert c_app_comp_iso_restrict_inv_c_app H (H.base_open.is_open_map.functor.obj U),
  rw H.iso_restrict.inv.c.naturality (eq_to_hom _),
  refine heq.trans _ (heq_iff_eq.mpr (category.comp_id _)),
  congr,
  exact this,
  { rw eq_to_hom_map, apply eq_to_hom_heq_id, simp[this] },
  { apply heq_of_subsingleton, simp[this] }
end

variable {f}

lemma app_is_iso (H : open_immersion f) (U : opens X) :
  is_iso (f.c.app (op (H.base_open.is_open_map.functor.obj U))) :=
begin
  have := c_app_comp_iso_restrict_inv_c_app' H U,
  rw [←is_iso.eq_comp_inv] at this,
  rw this,
  apply_instance
end

/-- (Implementation). The inverse of the open immersion `f` at some `U ⊆ X`. -/
noncomputable
abbreviation inv_c_app (H : open_immersion f) (U : opens X) :=
@@inv _ (f.c.app (op (H.base_open.is_open_map.functor.obj U))) (H.app_is_iso U)

lemma iso_restrict_inv_c_app_eq_inv_f_app
(H : open_immersion f) (U : opens X) :
  H.iso_restrict.inv.c.app (op U) =
  X.presheaf.map
    (eq_to_hom (by { cases U, simp [opens.map, set.preimage_image_eq U_val H.base_open.inj] })) ≫
  H.inv_c_app U ≫
  Y.presheaf.map ((@eq_to_hom (opens Y.1) _ ⟨_, _⟩ (H.base_open.is_open_map.functor.obj U)
  (by simpa)).op) :=
begin
  rw ← H.c_app_comp_iso_restrict_inv_c_app' U,
  simp,
end

@[simp, reassoc]
lemma iso_restrict_inv_c_app_comp_c_app
(H : open_immersion f) (U : opens X) :
  H.iso_restrict.inv.c.app (op U) ≫ f.c.app _ =
  X.presheaf.map
    (eq_to_hom (by { cases U, simpa [opens.map, set.preimage_image_eq _ H.base_open.inj] })) :=
begin
  rw iso_restrict_inv_c_app_eq_inv_f_app H U,
  simp only [category.assoc],
  rw f.c.naturality,
  simpa
end

lemma mono (H : open_immersion f) : mono f :=
by { rw ← H.fac, apply mono_comp }

/-- The composition of two open immersions is an open immersion. -/
@[simps iso_restrict]
def comp {Z : PresheafedSpace C} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g) :
  open_immersion (f ≫ g) :=
{ base_open := hg.base_open.comp hf.base_open,
  iso_restrict := hf.iso_restrict ≪≫
    restrict_map_iso _ hf.base_open hg.iso_restrict ≪≫ restrict_eq _ _ _ (by simp)
    ≪≫ (Z.restrict_comp _ hf.base_open _ hg.base_open _ rfl).symm,
  fac :=
  begin
    ext,
    dsimp only [iso_restrict_hom_base, iso.hom_inv_id, iso.inv_hom_id_assoc, iso.hom_inv_id_assoc,
      eq_self_iff_true, category.comp_id, iso.inv_hom_id, category.assoc, restrict, iso.trans],
    simp only [restrict_map_iso_hom_c_app, comp_c_app, whisker_right_app, restrict_eq_hom_c_app',
      nat_trans.comp_app, eq_to_hom_app, c_app_comp_iso_restrict_hom_c_app,
      of_restrict_c_app, category.assoc],
    erw [restrict_comp_inv_c_app, category.id_comp],
    simp only [functor.comp_map, category.assoc, ←functor.map_comp, ←functor.map_comp_assoc],
    erw [g.c.naturality_assoc, f.c.naturality_assoc, f.c.naturality_assoc],
    rw [←category.assoc, ←functor.map_comp_assoc],
    erw ←X.presheaf.map_comp,
    convert category.comp_id _,
    exact (congr_arg (λ f, X.presheaf.map f) (subsingleton.elim _ _)).trans (X.presheaf.map_id _),
    change g.base (f.base _) = g.base (f.base _),
    congr' 2,
    erw iso_restrict_hom_base_apply
  end
}

/-- An isomorphism is an open immersion. -/
@[simps]
def of_iso {X Y : PresheafedSpace C} (H : X ≅ Y) :
  open_immersion H.hom :=
{ base_open := (Top.homeo_of_iso (base_iso_of_iso H)).open_embedding,
  iso_restrict := H ≪≫ iso_restrict_iso _ (base_iso_of_iso H),
  fac := by simp }

/-- The identity is an open immersion. -/
abbreviation of_id (X : PresheafedSpace C) : open_immersion (𝟙 X) := of_iso (iso.refl X)

/-- This should be have better definitions than `H ▸ hf`. -/
@[simps]
def of_eq {X Y : PresheafedSpace C} (f g : X ⟶ Y) (H : f = g) (hf : open_immersion f) :
  open_immersion g :=
{ base_open := H ▸ hf.base_open,
  iso_restrict := hf.iso_restrict ≪≫ Y.restrict_eq _ _ (by { cases H, refl }),
  fac :=
  begin
    erw category.assoc,
    rw ←iso.eq_inv_comp,
    transitivity hf.iso_restrict.inv ≫ f,
    { simp },
    { congr, assumption }
  end }

end open_immersion

open open_immersion

section pullback
noncomputable theory

variables {X Y Z : PresheafedSpace C}
variables {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g)
include hf hg

/--
We construct the pullback of two open immersions via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullback_cone_of_open_immersion : pullback_cone f g :=
begin
 fapply pullback_cone.mk,
 exact Z.restrict (Top.open_embedding_of_pullback_open_embeddings hf.base_open hg.base_open),
 exact (restrict_comp Z _
  (Top.fst_open_embedding_of_right_open_embedding f.base hg.base_open) f.base hf.base_open
  (limit.π (cospan f.base g.base) walking_cospan.one) (limit.w _ walking_cospan.hom.inl).symm).hom
    ≫ PresheafedSpace.of_restrict _ _ ≫ (hf.iso_restrict).inv,
 exact (restrict_comp Z _
  (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base) g.base hg.base_open
  (limit.π (cospan f.base g.base) walking_cospan.one) (limit.w _ walking_cospan.hom.inr).symm).hom
    ≫ PresheafedSpace.of_restrict _ _ ≫ (hg.iso_restrict).inv,
  simp,
end

variables (s : pullback_cone f g)

/--
  (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullback_cone_of_open_immersion_lift : s.X ⟶ (pullback_cone_of_open_immersion hf hg).X :=
{ base := pullback.lift s.fst.base s.snd.base
  (congr_arg (λ x, PresheafedSpace.hom.base x) s.condition),
  c := whisker_left _ (s.π.app walking_cospan.one).c ≫
    (whisker_right (nat_trans.op
    { app := λ U, hom_of_le
      (λ x (hx : x ∈ (opens.map (pullback.lift s.fst.base s.snd.base _)).obj U),
        ⟨pullback.lift s.fst.base s.snd.base
            (congr_arg (λ x, PresheafedSpace.hom.base x) s.condition) x, hx,
          show limit.π (cospan f.base g.base) walking_cospan.one
            (pullback.lift s.fst.base s.snd.base _ x) = (s.π.app walking_cospan.one).base x,
          by  { have := s.π.naturality walking_cospan.hom.inl,
                erw category.id_comp at this,
                simp [this] } ⟩),
      naturality' := λ _ _ _, refl _ }) s.X.presheaf
      : (is_open_map.functor _ ⋙ opens.map _).op ⋙ s.X.presheaf ⟶ _ ⋙ s.X.presheaf)}

lemma pullback_cone_of_open_immersion_lift_comp_fst :
  pullback_cone_of_open_immersion_lift hf hg s ≫
    (pullback_cone_of_open_immersion hf hg).fst = s.fst :=
begin
  delta pullback_cone_of_open_immersion_lift pullback_cone_of_open_immersion,
  ext x,
  { induction x using opposite.rec,
    let fx : ((opens.map f.base).op.obj
      (op (hf.base_open.is_open_map.functor.obj ((opens.map hf.iso_restrict.inv.base).obj x)))) ⟶
        op x,
    { apply eq_to_hom, cases x, simpa[opens.map, set.preimage_image_eq _ hf.base_open.inj] },
    have := λ x, PresheafedSpace.congr_app
      ((category.id_comp _).symm.trans (s.π.naturality walking_cospan.hom.inl : _)) x,
    dsimp only [PresheafedSpace.comp_c_app, whisker_right_app,
      nat_trans.comp_app],
    erw this,
    dsimp only [pullback_cone.mk_fst, PresheafedSpace.comp_c_app],
    erw restrict_comp_hom_c_app',
    simp only [category.assoc],
    erw ←Z.presheaf.map_comp_assoc,
    erw f.c.naturality_assoc,
    erw s.fst.c.naturality_assoc,
    rw [Top.presheaf.pushforward_obj_map],
    iterate 3 { erw [←s.X.presheaf.map_comp] },
    erw ← s.fst.c.naturality fx,
    erw hf.iso_restrict_inv_c_app_comp_c_app_assoc,
    rw [←functor.map_comp_assoc, eq_to_hom_trans, eq_to_hom_refl,
      X.presheaf.map_id, category.id_comp] },
  { change pullback.lift _ _ _ ≫ 𝟙 _ ≫ pullback.fst ≫ hf.iso_restrict.inv.base = _,
    simp only [category.comp_id, hf.iso_restrict_inv_base, category.id_comp,
      pullback.lift_fst] }
end

lemma pullback_cone_of_open_immersion_lift_comp_snd :
  pullback_cone_of_open_immersion_lift hf hg s ≫
    (pullback_cone_of_open_immersion hf hg).snd = s.snd :=
begin
  delta pullback_cone_of_open_immersion_lift pullback_cone_of_open_immersion,
  ext x,
  { induction x using opposite.rec,
    let gx : ((opens.map g.base).op.obj
      (op (hg.base_open.is_open_map.functor.obj ((opens.map hg.iso_restrict.inv.base).obj x)))) ⟶
        op x,
    { apply eq_to_hom, cases x, simpa[opens.map, set.preimage_image_eq _ hg.base_open.inj] },
    have := λ x, PresheafedSpace.congr_app
      ((category.id_comp _).symm.trans (s.π.naturality walking_cospan.hom.inr : _)) x,
    dsimp only [PresheafedSpace.comp_c_app, whisker_right_app,
      nat_trans.comp_app],
    erw this,
    dsimp only [pullback_cone.mk_snd, PresheafedSpace.comp_c_app],
    erw restrict_comp_hom_c_app',
    simp only [category.assoc],
    erw ←Z.presheaf.map_comp_assoc,
    erw g.c.naturality_assoc,
    erw s.snd.c.naturality_assoc,
    rw [Top.presheaf.pushforward_obj_map],
    iterate 3 { erw [←s.X.presheaf.map_comp] },
    erw ← s.snd.c.naturality gx,
    erw hg.iso_restrict_inv_c_app_comp_c_app_assoc,
    rw [←functor.map_comp_assoc, eq_to_hom_trans, eq_to_hom_refl,
      Y.presheaf.map_id, category.id_comp] },
  { change pullback.lift _ _ _ ≫ 𝟙 _ ≫ pullback.snd ≫ hg.iso_restrict.inv.base = _,
    simp only [category.comp_id, hg.iso_restrict_inv_base, category.id_comp,
      pullback.lift_snd] }
end


lemma pullback_cone_π_app_one_base {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g) :
  ((pullback_cone_of_open_immersion hf hg).π.app walking_cospan.one).base =
    limit.π (cospan f.base g.base) walking_cospan.one :=
begin
  delta pullback_cone_of_open_immersion,
  simp only [open_immersion.inv_fac, restrict_comp_hom_base, cospan_map_inl,
    category.assoc, PresheafedSpace.comp_base, pullback_cone.mk_π_app_one,
    PresheafedSpace.of_restrict_base, ← limit.w (cospan f.base g.base) walking_cospan.hom.inl],
  erw category.id_comp
end

/-- The constructed pullback cone is an open immersion. -/
def pullback_cone_open_immersion :
  open_immersion ((pullback_cone_of_open_immersion hf hg).π.app walking_cospan.one) :=
{ base_open :=
  begin
    convert Top.open_embedding_of_pullback_open_embeddings hf.base_open hg.base_open,
    apply pullback_cone_π_app_one_base
  end,
  iso_restrict :=
  begin
    refine restrict_eq Z _ _ _,
    symmetry,
    apply pullback_cone_π_app_one_base,
  end,
  fac :=
  begin
    ext U,
    { dsimp only [nat_trans.comp_app, PresheafedSpace.comp_c_app, whisker_right_app],
      rw restrict_eq_hom_c_app',
      erw category_theory.functor.map_id,
      erw category.comp_id,
      dsimp only [pullback_cone_of_open_immersion, pullback_cone.mk_π_app_one,
        PresheafedSpace.comp_c_app],
      simp only [category.assoc],
      induction U using opposite.rec,
      rw c_app_comp_iso_restrict_inv_c_app_assoc,
      rw restrict_comp_hom_c_app',
      dsimp only [PresheafedSpace.of_restrict_c_app, cospan_one, PresheafedSpace.restrict_presheaf,
        functor.comp_map],
      simp only [←functor.map_comp],
      congr },
    { simp only [restrict_eq_hom_base, PresheafedSpace.comp_base,
        PresheafedSpace.of_restrict_base],
      erw category.id_comp },
  end }

/-- The constructed pullback cone is indeed the pullback. -/
def pullback_cone_of_open_immersion_is_limit :
  is_limit (pullback_cone_of_open_immersion hf hg) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  split,
  swap,
  exact pullback_cone_of_open_immersion_lift hf hg s,
  split,
  apply pullback_cone_of_open_immersion_lift_comp_fst,
  split,
  apply pullback_cone_of_open_immersion_lift_comp_snd,
  intros m h₁ h₂,
  haveI := (pullback_cone_open_immersion hf hg).mono,
  have := congr_arg (λ i, i ≫ f)
    (h₁.trans (pullback_cone_of_open_immersion_lift_comp_fst hf hg s).symm),
  simp only [category.assoc] at this,
  erw ← (pullback_cone_of_open_immersion hf hg).π.naturality walking_cospan.hom.inl at this,
  simp only [←category.assoc] at this,
  rw cancel_mono at this,
  erw cancel_mono (𝟙 _) at this,
  exact this,
  apply_instance
end

lemma has_pullback_of_open_immersion (hf : open_immersion f) (hg : open_immersion g) :
  has_pullback f g :=
⟨⟨⟨_, pullback_cone_of_open_immersion_is_limit hf hg⟩⟩⟩

/-- The pullback of two open immersions. -/
abbreviation open_immersion.pullback (hf : open_immersion f) (hg : open_immersion g) :
  PresheafedSpace C :=
@@pullback _ f g (has_pullback_of_open_immersion hf hg)

/-- The projection `X ×[Z] Y ⟶ Z`. -/
abbreviation open_immersion.pullback_imm :
  hf.pullback hg ⟶ Z :=
@@limit.π _ _ _ (has_pullback_of_open_immersion hf hg) walking_cospan.one

/-- The projection `X ×[Z] Y ⟶ Z` is an open immersion. -/
def open_immersion.pullback_imm_open_immersion :
  open_immersion (hf.pullback_imm hg) :=
begin
  haveI := has_pullback_of_open_immersion hf hg,
  apply of_eq _ _ (limit.iso_limit_cone_hom_π
    ⟨_, (pullback_cone_of_open_immersion_is_limit hf hg)⟩ walking_cospan.one),
  apply open_immersion.comp,
  apply of_iso,
  apply pullback_cone_open_immersion
end

end pullback

end algebraic_geometry.PresheafedSpace
