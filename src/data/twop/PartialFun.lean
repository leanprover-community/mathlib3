/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.category.Bipointed
import data.pfun

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of two-pointed types.
-/

open category_theory option

universes u
variables {α β : Type*}

@[simp] lemma subtype.coe_inj {p : α → Prop} {a b : subtype p} : (a : α) = b ↔ a = b :=
subtype.coe_injective.eq_iff

/-- The category of types equipped with partial functions. -/
def PartialFun : Type* := Type*

namespace PartialFun

instance : has_coe_to_sort PartialFun Type* := ⟨id⟩

/-- Turns a type into a `PartialFun`. -/
def of (X : Type*) : PartialFun := X

instance : inhabited PartialFun := ⟨Type*⟩

instance large_category : large_category.{u} PartialFun :=
{ hom := pfun,
  id := pfun.id,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := @pfun.comp_id,
  comp_id' := @pfun.id_comp,
  assoc' := λ W X Y Z _ _ _, (pfun.comp_assoc _ _ _).symm }

end PartialFun

/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
def Type_to_PartialFun : Type ⥤ PartialFun :=
{ obj := id,
  map := @pfun.lift,
  map_comp' := λ _ _ _ _ _, pfun.coe_comp _ _ }

/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This the computable part of the equivalence `PartialFun_equiv_Pointed`. -/
def Pointed_to_PartialFun : Pointed ⥤ PartialFun :=
{ obj := λ X, {x : X // x ≠ X.point},
  map := λ X Y f, pfun.to_subtype _ f.to_fun ∘ subtype.val,
  map_id' := λ X, pfun.ext $ λ a b,
    pfun.mem_to_subtype_iff.trans (subtype.coe_inj.trans part.mem_some_iff.symm),
  map_comp' := λ X Y Z f g, pfun.ext $ λ a c, begin
    refine pfun.mem_to_subtype_iff.trans (iff.trans _ part.mem_bind_iff.symm),
    simp_rw [pfun.mem_to_subtype_iff, subtype.exists],
    refine ⟨λ h, ⟨f.to_fun a, λ ha, c.2 $ h.trans
      ((congr_arg g.to_fun ha : g.to_fun _ = _).trans g.map_point), rfl, h⟩, _⟩,
    rintro ⟨b, _, (rfl : b = _), h⟩,
    exact h,
  end }

protected lemma part.dom.bind {α : Type*} {o : part α} [decidable o.dom] (h : o.dom)
  (f : α → part β) :
  o.bind f = f (o.get h) :=
begin
  ext b,
  simp only [part.mem_bind_iff, exists_prop],
  refine ⟨_, λ hb, ⟨o.get h, part.get_mem _, hb⟩⟩,
  rintro ⟨a, ha, hb⟩,
  rwa part.get_eq_of_mem ha,
end

protected lemma part.dom.to_option {α : Type*} {a : part α} [decidable a.dom] (h : a.dom) :
  a.to_option = a.get h := dif_pos h

lemma part.dom.of_bind {α : Type*} {f : α → part β} {a : part α} (h : (a.bind f).dom) : a.dom :=
h.some

lemma part.to_option_eq_none_iff {α : Type*} {a : part α} [decidable a.dom] :
  a.to_option = none ↔ ¬ a.dom :=
ne.dite_eq_right_iff $ λ h, option.some_ne_none _

lemma part.bind_to_option {α : Type*} (f : α → part β) (a : part α) [decidable a.dom]
  [Π a, decidable (f a).dom] [decidable (a.bind f).dom] :
  (a.bind f).to_option = a.to_option.elim none (λ a, (f a).to_option) :=
begin
  by_cases a.dom,
  { simp_rw [h.to_option, h.bind],
    refl },
  { rw part.to_option_eq_none_iff.2 h,
    exact part.to_option_eq_none_iff.2 (λ ha, h ha.of_bind) }
end

/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This the computable part of the equivalence `PartialFun_equiv_Pointed`. -/
noncomputable def PartialFun_to_Pointed : PartialFun ⥤ Pointed :=
{ obj := λ X, ⟨option X, none⟩,
  map := λ X Y f,
    ⟨λ o, o.elim none (λ a, @part.to_option _ (f a) (classical.prop_decidable _)), rfl⟩,
  map_id' := λ X, Pointed.hom.ext _ _ $ funext $ λ o,
    option.rec_on o rfl (λ a, by convert part.some_to_option _),
  map_comp' := λ X Y Z f g, Pointed.hom.ext _ _ $ funext $ λ o,
    option.rec_on o rfl (λ a, by convert part.bind_to_option _ _) }

noncomputable def PartialFun_equiv_Pointed : PartialFun ≌ Pointed :=
by classical; exact
equivalence.mk PartialFun_to_Pointed Pointed_to_PartialFun
  (nat_iso.of_components (λ X,
    { hom := λ a, part.some ⟨some a, some_ne_none _⟩,
      inv := λ a, part.some (option.get $ ne_none_iff_is_some.1 a.2),
      hom_inv_id' := pfun.ext $ λ a b, begin
        change _ ↔ b ∈ part.some _,
        refine (iff.trans _ part.mem_some_iff.symm),
        change b ∈ part.some _ ↔ _,
        sorry
        -- refine part.mem_some_iff.trans _,
        -- refine part.mem_some_iff.trans (iff.trans _ part.mem_some_iff.symm),
      end,
      inv_hom_id' := pfun.ext $ λ a b, begin
        refine (iff.trans _ part.mem_some_iff.symm),
        sorry,
        -- simp,
        -- refine part.mem_some_iff.trans _,
      end }) _)
  (nat_iso.of_components (λ X,
    { hom := ⟨λ a, a.elim X.point subtype.val, rfl⟩,
      inv := ⟨λ a, if h : a = X.point then none else some ⟨_, h⟩, dif_pos rfl⟩,
      hom_inv_id' := Pointed.hom.ext _ _ $ funext $ λ a, option.rec_on a (dif_pos rfl) $ λ a,
        (dif_neg a.2).trans begin
        simp only [option.elim, subtype.val_eq_coe, subtype.coe_eta],
        refl,
      end,
      inv_hom_id' := Pointed.hom.ext _ _ $ funext $ λ a, begin
        change option.elim (dite _ _ _) _ _ = _,
        split_ifs,
        { rw h, refl },
        { refl }
      end }) _)

@[simp] lemma PartialFun_swap_comp_forget_to_Bipointed :
  PartialFun.swap ⋙ forget₂ PartialFun Bipointed = forget₂ PartialFun Bipointed ⋙ Bipointed.swap := rfl

/-- The functor from `Pointed` to `PartialFun` which adds a second point. -/
def Pointed_to_PartialFun_fst : Pointed.{u} ⥤ PartialFun :=
{ obj := λ X, ⟨option X, ⟨X.point, none⟩, some_ne_none _⟩,
  map := λ X Y f, ⟨option.map f.to_fun, congr_arg _ f.map_point, rfl⟩,
  map_id' := λ X, Bipointed.hom.ext _ _ option.map_id,
  map_comp' := λ X Y Z f g, Bipointed.hom.ext _ _ (option.map_comp_map  _ _).symm }

/-- The functor from `Pointed` to `PartialFun` which adds a first point. -/
def Pointed_to_PartialFun_snd : Pointed.{u} ⥤ PartialFun :=
{ obj := λ X, ⟨option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩,
  map := λ X Y f, ⟨option.map f.to_fun, rfl, congr_arg _ f.map_point⟩,
  map_id' := λ X, Bipointed.hom.ext _ _ option.map_id,
  map_comp' := λ X Y Z f g, Bipointed.hom.ext _ _ (option.map_comp_map  _ _).symm }

@[simp] lemma Pointed_to_PartialFun_fst_comp_swap :
  Pointed_to_PartialFun_fst ⋙ PartialFun.swap = Pointed_to_PartialFun_snd := rfl

@[simp] lemma Pointed_to_PartialFun_snd_comp_swap :
  Pointed_to_PartialFun_snd ⋙ PartialFun.swap = Pointed_to_PartialFun_fst := rfl

@[simp] lemma Pointed_to_PartialFun_fst_comp_forget_to_Bipointed :
  Pointed_to_PartialFun_fst ⋙ forget₂ PartialFun Bipointed = Pointed_to_Bipointed_fst := rfl

@[simp] lemma Pointed_to_PartialFun_snd_comp_forget_to_Bipointed :
  Pointed_to_PartialFun_snd ⋙ forget₂ PartialFun Bipointed = Pointed_to_Bipointed_snd := rfl

/-- `Pointed_to_PartialFun_fst` is one of the two free functors. -/
def Pointed_to_PartialFun_fst_forget_comp_Bipointed_to_Pointed_fst_adjunction :
  Pointed_to_PartialFun_fst ⊣ forget₂ PartialFun Bipointed ⋙ Bipointed_to_Pointed_fst :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, ⟨f.to_fun ∘ option.some, f.map_fst⟩,
    inv_fun := λ f, ⟨λ o, o.elim Y.to_two_pointing.to_prod.2 f.to_fun, f.map_point, rfl⟩,
    left_inv := λ f, by { ext, cases x, exact f.map_snd.symm, refl },
    right_inv := λ f, Pointed.hom.ext _ _ rfl },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by { ext, cases x; refl } }

/-- `Pointed_to_PartialFun_snd` is one of the two free functors. -/
def Pointed_to_PartialFun_snd_forget_comp_Bipointed_to_Pointed_snd_adjunction :
  Pointed_to_PartialFun_snd ⊣ forget₂ PartialFun Bipointed ⋙ Bipointed_to_Pointed_snd :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, ⟨f.to_fun ∘ option.some, f.map_snd⟩,
    inv_fun := λ f, ⟨λ o, o.elim Y.to_two_pointing.to_prod.1 f.to_fun, rfl, f.map_point⟩,
    left_inv := λ f, by { ext, cases x, exact f.map_fst.symm, refl },
    right_inv := λ f, Pointed.hom.ext _ _ rfl },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by { ext, cases x; refl } }
