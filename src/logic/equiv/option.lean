/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import control.equiv_functor
import data.option.basic
import data.subtype
import logic.equiv.defs

/-!
# Equivalences for `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


We define
* `equiv.option_congr`: the `option α ≃ option β` constructed from `e : α ≃ β` by sending `none` to
  `none`, and applying a `e` elsewhere.
* `equiv.remove_none`: the `α ≃ β` constructed from `option α ≃ option β` by removing `none` from
  both sides.
-/

namespace equiv

open option

variables {α β γ : Type*}

section option_congr

/-- A universe-polymorphic version of `equiv_functor.map_equiv option e`. -/
@[simps apply]
def option_congr (e : α ≃ β) : option α ≃ option β :=
{ to_fun := option.map e,
  inv_fun := option.map e.symm,
  left_inv := λ x, (option.map_map _ _ _).trans $
    e.symm_comp_self.symm ▸ congr_fun option.map_id x,
  right_inv := λ x, (option.map_map _ _ _).trans $
    e.self_comp_symm.symm ▸ congr_fun option.map_id x }

@[simp] lemma option_congr_refl : option_congr (equiv.refl α) = equiv.refl _ :=
ext $ congr_fun option.map_id

@[simp] lemma option_congr_symm (e : α ≃ β) : (option_congr e).symm = option_congr e.symm := rfl

@[simp] lemma option_congr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
  (option_congr e₁).trans (option_congr e₂) = option_congr (e₁.trans e₂) :=
ext $ option.map_map _ _

/-- When `α` and `β` are in the same universe, this is the same as the result of
`equiv_functor.map_equiv`. -/
lemma option_congr_eq_equiv_function_map_equiv {α β : Type*} (e : α ≃ β) :
  option_congr e = equiv_functor.map_equiv option e := rfl

end option_congr

section remove_none
variables (e : option α ≃ option β)

private def remove_none_aux (x : α) : β :=
if h : (e (some x)).is_some
  then option.get h
  else option.get $ show (e none).is_some, from
  begin
    rw ←option.ne_none_iff_is_some,
    intro hn,
    rw [option.not_is_some_iff_eq_none, ←hn] at h,
    simpa only using e.injective h,
  end

private lemma remove_none_aux_some {x : α} (h : ∃ x', e (some x) = some x') :
  some (remove_none_aux e x) = e (some x) :=
by simp [remove_none_aux, option.is_some_iff_exists.mpr h]

private lemma remove_none_aux_none {x : α} (h : e (some x) = none) :
  some (remove_none_aux e x) = e none :=
by simp [remove_none_aux, option.not_is_some_iff_eq_none.mpr h]

private lemma remove_none_aux_inv (x : α) : remove_none_aux e.symm (remove_none_aux e x) = x :=
option.some_injective _ begin
  cases h1 : e.symm (some (remove_none_aux e x)); cases h2 : (e (some x)),
  { rw remove_none_aux_none _ h1,
    exact (e.eq_symm_apply.mpr h2).symm },
  { rw remove_none_aux_some _ ⟨_, h2⟩ at h1,
    simpa using h1, },
  { rw remove_none_aux_none _ h2 at h1,
    simpa using h1, },
  { rw remove_none_aux_some _ ⟨_, h1⟩,
    rw remove_none_aux_some _ ⟨_, h2⟩,
    simp },
end

/-- Given an equivalence between two `option` types, eliminate `none` from that equivalence by
mapping `e.symm none` to `e none`. -/
def remove_none : α ≃ β :=
{ to_fun := remove_none_aux e,
  inv_fun := remove_none_aux e.symm,
  left_inv := remove_none_aux_inv e,
  right_inv := remove_none_aux_inv e.symm, }

@[simp]
lemma remove_none_symm : (remove_none e).symm = remove_none e.symm := rfl

lemma remove_none_some {x : α} (h : ∃ x', e (some x) = some x') :
  some (remove_none e x) = e (some x) := remove_none_aux_some e h

lemma remove_none_none {x : α} (h : e (some x) = none) :
  some (remove_none e x) = e none := remove_none_aux_none e h

@[simp] lemma option_symm_apply_none_iff : e.symm none = none ↔ e none = none :=
⟨λ h, by simpa using (congr_arg e h).symm, λ h, by simpa using (congr_arg e.symm h).symm⟩

lemma some_remove_none_iff {x : α} :
  some (remove_none e x) = e none ↔ e.symm none = some x :=
begin
  cases h : e (some x) with a,
  { rw remove_none_none _ h,
    simpa using (congr_arg e.symm h).symm },
  { rw remove_none_some _ ⟨a, h⟩,
    have := (congr_arg e.symm h),
    rw [symm_apply_apply] at this,
    simp only [false_iff, apply_eq_iff_eq],
    simp [this] }
end

@[simp]
lemma remove_none_option_congr (e : α ≃ β) : remove_none e.option_congr = e :=
equiv.ext $ λ x, option.some_injective _ $ remove_none_some _ ⟨e x, by simp [equiv_functor.map]⟩

end remove_none

lemma option_congr_injective : function.injective (option_congr : α ≃ β → option α ≃ option β) :=
function.left_inverse.injective remove_none_option_congr

/-- Equivalences between `option α` and `β` that send `none` to `x` are equivalent to
equivalences between `α` and `{y : β // y ≠ x}`. -/
def option_subtype [decidable_eq β] (x : β) :
  {e : option α ≃ β // e none = x} ≃ (α ≃ {y : β // y ≠ x}) :=
{ to_fun := λ e,
    { to_fun := λ a, ⟨e a, ((equiv_like.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      inv_fun := λ b, get (ne_none_iff_is_some.1 (((equiv_like.injective _).ne_iff'
        (((apply_eq_iff_eq_symm_apply _).1 e.property).symm)).2 b.property)),
      left_inv := λ a, begin
          rw [←some_inj, some_get, ←coe_def],
          exact symm_apply_apply (e : option α ≃ β) a
        end,
      right_inv := λ b, begin
          ext,
          simp,
          exact apply_symm_apply _ _
        end },
  inv_fun := λ e,
    ⟨{ to_fun := λ a, cases_on' a x (coe ∘ e),
       inv_fun := λ b, if h : b = x then none else e.symm ⟨b, h⟩,
       left_inv := λ a, begin
           cases a, { simp },
           simp only [cases_on'_some, function.comp_app, subtype.coe_eta, symm_apply_apply,
                      dite_eq_ite],
           exact if_neg (e a).property
         end,
       right_inv := λ b, begin
           by_cases h : b = x;
             simp [h]
         end},
     rfl⟩,
  left_inv := λ e, begin
      ext a,
      cases a,
      { simpa using e.property.symm },
      { simpa }
    end,
  right_inv := λ e, begin
      ext a,
      refl
    end }

@[simp] lemma option_subtype_apply_apply [decidable_eq β] (x : β)
  (e : {e : option α ≃ β // e none = x}) (a : α) (h) :
  option_subtype x e a = ⟨(e : option α ≃ β) a, h⟩ :=
rfl

@[simp] lemma coe_option_subtype_apply_apply [decidable_eq β] (x : β)
  (e : {e : option α ≃ β // e none = x}) (a : α) :
  ↑(option_subtype x e a) = (e : option α ≃ β) a :=
rfl

@[simp] lemma option_subtype_apply_symm_apply [decidable_eq β] (x : β)
  (e : {e : option α ≃ β // e none = x}) (b : {y : β // y ≠ x}) :
  ↑((option_subtype x e).symm b) = (e : option α ≃ β).symm b :=
begin
  dsimp only [option_subtype],
  simp
end

@[simp] lemma option_subtype_symm_apply_apply_coe [decidable_eq β] (x : β)
  (e : α ≃ {y : β // y ≠ x}) (a : α) : (option_subtype x).symm e a = e a :=
rfl

@[simp] lemma option_subtype_symm_apply_apply_some [decidable_eq β] (x : β)
  (e : α ≃ {y : β // y ≠ x}) (a : α) : (option_subtype x).symm e (some a) = e a :=
rfl

@[simp] lemma option_subtype_symm_apply_apply_none [decidable_eq β] (x : β)
  (e : α ≃ {y : β // y ≠ x}) : (option_subtype x).symm e none = x :=
rfl

@[simp] lemma option_subtype_symm_apply_symm_apply [decidable_eq β] (x : β)
  (e : α ≃ {y : β // y ≠ x}) (b : {y : β // y ≠ x}) :
  ((option_subtype x).symm e : option α ≃ β).symm b = e.symm b :=
begin
  simp only [option_subtype, coe_fn_symm_mk, subtype.coe_mk, subtype.coe_eta, dite_eq_ite,
             ite_eq_right_iff],
  exact λ h, false.elim (b.property h),
end

end equiv
