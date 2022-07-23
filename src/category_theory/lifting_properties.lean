/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach, Joël Riou
-/
import category_theory.limits.shapes.comm_sq

/-!
# Lifting properties

This file defines the lifting property of two arrows in a category and shows basic properties of
this notion.

## Main results
- `has_lifting_property`: the definition of the lifting property

## Tags
lifting property



@TODO : `comm_sq.lean` depends on a lot of things, including
`strong_epi.lean`. Then the most basic parts of
`comm_sq.lean` should be moved to a new file
`category_theory/comm_sq.lean`, and only the parts related
to pushout and pullback should be in `limits/shapes`.

-/

universe v

namespace category_theory

open limits category

variables {C : Type*} [category C] {A B B' X Y Y' : C}
  (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y) (p' : Y ⟶ Y')

class has_lifting_property : Prop :=
(sq_has_lift : ∀ {f : A ⟶ X} {g : B ⟶ Y} (sq : comm_sq f i p g), sq.has_lift)

@[priority 100]
instance sq_has_lift_of_has_lifting_property {f : A ⟶ X} {g : B ⟶ Y} (sq : comm_sq f i p g)
  [hip : has_lifting_property i p] : sq.has_lift := by apply hip.sq_has_lift

namespace has_lifting_property

variables {i p}

lemma op (h : has_lifting_property i p) : has_lifting_property p.op i.op :=
begin
  constructor,
  intros f g sq,
  simp only [comm_sq.has_lift.iff_unop, quiver.hom.unop_op],
  haveI := h,
  apply_instance,
end

lemma unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y}
  (h : has_lifting_property i p) : has_lifting_property p.unop i.unop :=
begin
  constructor,
  intros f g sq,
  rw comm_sq.has_lift.iff_op,
  simp only [quiver.hom.op_unop],
  haveI := h,
  apply_instance,
end

lemma iff_op : has_lifting_property i p ↔ has_lifting_property p.op i.op := ⟨op, unop⟩

lemma iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
  has_lifting_property i p ↔ has_lifting_property p.unop i.unop := ⟨unop, op⟩

variables (i p)

@[priority 100]
instance of_left_iso [is_iso i] : has_lifting_property i p :=
⟨λ f g sq, ⟨nonempty.intro
  { l := inv i ≫ f,
    fac_left' := by simp only [is_iso.hom_inv_id_assoc],
    fac_right' := by simp only [sq.w, assoc, is_iso.inv_hom_id_assoc], }⟩⟩

@[priority 100]
instance of_right_iso [is_iso p] : has_lifting_property i p :=
⟨λ f g sq, ⟨nonempty.intro
  { l := g ≫ inv p,
    fac_left' := by simp only [← sq.w_assoc, is_iso.hom_inv_id, comp_id],
    fac_right' := by simp only [assoc, is_iso.inv_hom_id, comp_id], }⟩⟩

instance of_comp_left [has_lifting_property i p] [has_lifting_property i' p] :
  has_lifting_property (i ≫ i') p :=
⟨λ f g sq, begin
  have fac := sq.w,
  rw assoc at fac,
  exact ⟨nonempty.intro
  { l := (comm_sq.mk (comm_sq.mk fac).fac_right).lift,
    fac_left' := by simp only [assoc, comm_sq.fac_left],
    fac_right' := by simp only [comm_sq.fac_right], }⟩,
end⟩

instance of_comp_right [has_lifting_property i p] [has_lifting_property i p'] :
  has_lifting_property i (p ≫ p') :=
⟨λ f g sq, begin
  have fac := sq.w,
  rw ← assoc at fac,
  let sq₂ := (comm_sq.mk ((comm_sq.mk fac).fac_left.symm)).lift,
  exact ⟨nonempty.intro
  { l := (comm_sq.mk ((comm_sq.mk fac).fac_left.symm)).lift,
    fac_left' := by simp only [comm_sq.fac_left],
    fac_right' := by simp only [comm_sq.fac_right_assoc, comm_sq.fac_right], }⟩,
end⟩

/-
lemma of_retract_left {A' B' : C} {i : A ⟶ B} {i' : A' ⟶ B'} {p : X ⟶ Y}
  (h : is_retract_hom i i') [has_lifting_property i' p] :
  has_lifting_property i p :=
begin
  constructor,
  intros f g sq,
  rcases h with ⟨s, r, hsr⟩,
  have fac : (r.left ≫ f) ≫ p = i' ≫ (r.right ≫ g) :=
    by simpa only [assoc, sq.w] using arrow.w_assoc r g,
  constructor,
  exact nonempty.intro
  { l := s.right ≫ (comm_sq.mk fac).lift,
    fac_left := begin
      have hs := arrow.w s,
      simp only [arrow.mk_hom] at hs,
      rw [← assoc, ← hs, assoc, comm_sq.fac_left, ← assoc, ← comma.comp_left, hsr, arrow.id_left],
      apply id_comp,
    end,
    fac_right := begin
      rw [assoc, comm_sq.fac_right, ← assoc, ← comma.comp_right, hsr, arrow.id_right],
      apply id_comp,
    end, },
end

lemma of_retract_right {X' Y' : C} {i : A ⟶ B} {p : X ⟶ Y} {p' : X' ⟶ Y'}
  (h : is_retract_hom p p') [hip' : has_lifting_property_new i p'] :
  has_lifting_property_new i p :=
begin
  rw iff_op at ⊢ hip',
  rw is_retract_hom.iff_op at h,
  haveI := hip',
  exact of_retract_left h,
end-/

variables {i}

/-lemma of_direct_image {A' B' : C} {f : A ⟶ A'} {g : B ⟶ B'} {i' : A' ⟶ B'}
  (h : is_pushout f i i' g) (p : X ⟶ Y) [hi : has_lifting_property i p] :
  has_lifting_property i' p :=
⟨λ f' g' sq, begin
  have fac : (f ≫ f') ≫ p = i ≫ (g ≫ g') := by rw [assoc, sq.w, ← assoc, h.w, assoc],
  exact ⟨nonempty.intro
  { l := h.desc f' (comm_sq.mk fac).lift (by simp only [comm_sq.fac_left]),
    fac_left' := by simp only [is_pushout.inl_desc],
    fac_right' := h.hom_ext _ _ (by simpa using sq.w)
      (by simp only [is_pushout.inr_desc_assoc, comm_sq.fac_right]), }⟩,
end⟩-/

instance ⦃I : Type v⦄ (A B : I → C) [hA : has_coproduct A] [hB : has_coproduct B]
  (φ : Π i, A i ⟶ B i) [hφ : ∀ i, has_lifting_property (φ i) p] :
    has_lifting_property (@limits.sigma.map _ _ _ A B hA hB φ) p :=
⟨λ f g sq, begin
  have fac : ∀ (i : I), (sigma.ι _ i ≫ f) ≫ p = φ i ≫ (sigma.ι _ i ≫ g) :=
    λ i, by simp only [sq.w, assoc, ι_colim_map_assoc, discrete.nat_trans_app],
  have sq := λ i, (comm_sq.mk (fac i)).lift,
  exact ⟨nonempty.intro
  { l := sigma.desc (λ i, (comm_sq.mk (fac i)).lift),
    fac_left' := begin
      ext i,
      cases i,
      simp only [ι_colim_map_assoc, colimit.ι_desc, cofan.mk_ι_app, comm_sq.fac_left],
    end,
    fac_right' := begin
      ext i,
      cases i,
      simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, comm_sq.fac_right],
    end, }⟩,
end⟩

variable (i)
/-
lemma equiv_of_fully_faithful (F : C ⥤ D) [full F] [faithful F] :
  has_lifting_property i p ↔ has_lifting_property (F.map i) (F.map p) :=
begin
  split,
  { introI,
    constructor,
    intros f g sq,
    let sq' := comm_sq.preimage F sq,
    have hsq' : sq'.has_lift := by { simp only [preimage_map], apply_instance, },
    rw comm_sq.has_lift.equiv_of_fully_faithful _ F at hsq',
    convert hsq',
    all_goals { simp only [functor.image_preimage, preimage_map], }, },
  { introI,
    constructor,
    intros f g sq,
    simpa only [← comm_sq.has_lift.equiv_of_fully_faithful _ F]
      using (infer_instance : (sq.apply F).has_lift),
    },
end-/

end has_lifting_property
/-
namespace arrow_class

@[protected]
def has_lifting_property (F G : arrow_class C) :=
∀ ⦃A B X Y : C⦄ (i : A ⟶ B) (hi : arrow.mk i ∈ F) (p : X ⟶ Y) (hp : arrow.mk p ∈ G),
has_lifting_property_new i p

namespace has_lifting_property

lemma has_lift {F G : arrow_class C} (h : has_lifting_property F G)
{A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
(sq : comm_sq f i p g) (hi : arrow.mk i ∈ F) (hp : arrow.mk p ∈ G) :
  sq.has_lift := by { haveI := h i hi p hp, apply_instance, }

lemma op {F G : arrow_class C} (h : has_lifting_property F G) :
  has_lifting_property G.op F.op :=
λ A B X Y i hi p hp, (h p.unop hp i.unop hi).op

lemma unop {F G : arrow_class Cᵒᵖ} (h : has_lifting_property F G) :
  has_lifting_property G.unop F.unop :=
λ A B X Y i hi p hp, (h p.op hp i.op hi).unop

lemma iff_op (F G : arrow_class C) :
  has_lifting_property F G ↔ has_lifting_property G.op F.op := ⟨op, unop⟩

lemma iff_unop (F' G' : arrow_class Cᵒᵖ) :
  has_lifting_property F' G' ↔ has_lifting_property G'.unop F'.unop := ⟨unop, op⟩

end has_lifting_property

@[simp]
def llp_with (G : arrow_class C) : arrow_class C :=
λ i, ∀ {X Y : C} (p : X ⟶ Y), arrow.mk p ∈ G → has_lifting_property_new i.hom p

@[simp]
def rlp_with (F : arrow_class C) : arrow_class C :=
λ p, ∀ {X Y : C} (i : X ⟶ Y), arrow.mk i ∈ F → has_lifting_property_new i p.hom

lemma llp_with_op (F : arrow_class C) :
  F.op.llp_with = F.rlp_with.op :=
begin
  ext i,
  split,
  { intros h X Y p hp,
    simpa only [has_lifting_property_new.iff_unop] using h p.op hp, },
  { intros h X Y p hp,
    have hp' := h p.unop hp,
    rw has_lifting_property_new.iff_op at hp',
    exact hp', },
end

lemma llp_with_unop (F : arrow_class Cᵒᵖ) :
  F.unop.rlp_with = F.llp_with.unop :=
begin
  have h := llp_with_op F.unop,
  rw F.op_unop at h,
  rw [h, arrow_class.unop_op],
end

lemma rlp_with_op (F : arrow_class C) :
  F.op.rlp_with = F.llp_with.op :=
begin
  ext p,
  split,
  { intros h X Y i hi,
    have paf := h i.op,
    simpa only [has_lifting_property_new.iff_unop] using h i.op hi, },
  { intros h X Y i hi,
    have hi' := h i.unop hi,
    rw has_lifting_property_new.iff_op at hi',
    exact hi', },
end

lemma rlp_with_unop (F : arrow_class Cᵒᵖ) :
   F.unop.llp_with = F.rlp_with.unop :=
begin
  have h := rlp_with_op F.unop,
  rw F.op_unop at h,
  rw [h, arrow_class.unop_op],
end

namespace is_stable_by_composition

lemma for_llp_with (F : arrow_class C) :
  F.llp_with.is_stable_by_composition :=
λ X Y Z f g hf hg A B p hp, begin
  rw arrow.mk_hom,
  haveI : has_lifting_property_new f p := hf p hp,
  haveI : has_lifting_property_new g p := hg p hp,
  apply_instance,
end

lemma for_rlp_with (F : arrow_class C) :
  F.rlp_with.is_stable_by_composition :=
λ A B C f g hf hg X Y i hi, begin
  rw arrow.mk_hom,
  haveI : has_lifting_property_new i f := hf i hi,
  haveI : has_lifting_property_new i g := hg i hi,
  apply_instance,
end

end is_stable_by_composition


lemma isomorphisms_subset_llp_with (F : arrow_class C) : isomorphisms ⊆ F.llp_with :=
λ f hf X Y p hp, by { haveI : is_iso f.hom := hf, apply_instance, }

lemma isomorphisms_subset_rlp_with (F : arrow_class C) : isomorphisms ⊆ F.rlp_with :=
λ f hf X Y i hi, by { haveI : is_iso f.hom := hf, apply_instance, }

namespace is_stable_by_direct_image

lemma for_llp_with (F : arrow_class C) :
  F.llp_with.is_stable_by_direct_image :=
λ A B A' B' f i i' g h hi X Y p hp,
begin
  haveI : has_lifting_property_new i p := hi p hp,
  exact has_lifting_property_new.of_direct_image h p,
end

end is_stable_by_direct_image

namespace is_stable_by_coproduct

lemma for_llp_with (F : arrow_class C) :
  F.llp_with.is_stable_by_coproduct :=
λ I X Y hX hY f hf X Y p hp,
begin
  simp only [arrow.mk_hom],
  haveI : ∀ i, has_lifting_property_new (f i) p := λ i, hf i p hp,
  apply_instance,
end

end is_stable_by_coproduct

namespace has_lifting_property_new

lemma llp_with_singleton_iff : arrow.mk i ∈ ({arrow.mk p} : arrow_class C).llp_with ↔ has_lifting_property_new i p :=
begin
  split,
  { exact λ hi, hi p (set.mem_singleton _), },
  { intro hi,
    intros X' Y' q hq,
    simp only [set.mem_singleton_iff] at hq,
    simp only [arrow.mk_hom],
    have h₁ := arrow.congr_left hq.symm,
    have h₂ := arrow.congr_right hq.symm,
    simp at h₁ h₂,
    substs h₁ h₂,
    rw arrow.mk_inj at hq,
    rw hq,
    exact hi, }
end

instance binary_coproduct {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [has_binary_coproduct X₁ X₂] [has_binary_coproduct Y₁ Y₂]
  [has_lifting_property_new f₁ p] [has_lifting_property_new f₂ p] :
  has_lifting_property_new (coprod.map f₁ f₂) p :=
begin
  refine (is_stable_by_coproduct.for_llp_with {arrow.mk p}).binary f₁ f₂ _ _ p (set.mem_singleton _),
  { simp only [llp_with_singleton_iff], apply_instance, },
  { simp only [llp_with_singleton_iff], apply_instance, },
end

end has_lifting_property_new

end arrow_class
-/

end category_theory
