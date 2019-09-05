/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import data.equiv.local_equiv topology.constructions

/-!
# Local homeomorphisms

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`local_homeomorph α β` is an extension of `local_equiv α β`, i.e., it is a pair of functions
`e.to_fun` and `e.inv_fun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

Contrary to equivs, we do not register the coercion to functions and we use explicitly to_fun and
inv_fun: coercions create unification problems for manifolds.

## Main definitions

`homeomorph.to_local_homeomorph`: associating a local homeomorphism to a homeomorphism, with
                                  source = target = univ
`local_homeomorph.symm`  : the inverse of a local homeomorphism
`local_homeomorph.trans` : the composition of two local homeomorphisms
`local_homeomorph.refl`  : the identity local homeomorphism
`local_homeomorph.of_set`: the identity on a set `s`
`eq_on_source`           : equivalence relation describing the "right" notion of equality for local
                           homeomorphisms

## Implementation notes

Most statements are copied from their local_equiv versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `local_equiv.lean`.
-/

open function set

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
[topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

/-- local homeomorphisms, defined on open subsets of the space -/
structure local_homeomorph (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  extends local_equiv α β :=
(open_source        : is_open source)
(open_target        : is_open target)
(continuous_to_fun  : continuous_on to_fun source)
(continuous_inv_fun : continuous_on inv_fun target)

/-- A homeomorphism induces a local homeomorphism on the whole space -/
def homeomorph.to_local_homeomorph (e : homeomorph α β) :
  local_homeomorph α β :=
{ open_source        := is_open_univ,
  open_target        := is_open_univ,
  continuous_to_fun  := by { erw ← continuous_iff_continuous_on_univ, exact e.continuous_to_fun },
  continuous_inv_fun := by { erw ← continuous_iff_continuous_on_univ, exact e.continuous_inv_fun },
  ..e.to_equiv.to_local_equiv }

namespace local_homeomorph

variables (e : local_homeomorph α β) (e' : local_homeomorph β γ)

lemma eq_of_local_equiv_eq {e e' : local_homeomorph α β}
  (h : e.to_local_equiv = e'.to_local_equiv) : e = e' :=
begin
  cases e, cases e',
  dsimp at *,
  induction h,
  refl
end

@[extensionality]
protected lemma ext (e' : local_homeomorph α β) (h : ∀x, e.to_fun x = e'.to_fun x)
  (hsymm : ∀x, e.inv_fun x = e'.inv_fun x) (hs : e.source = e'.source) : e = e' :=
eq_of_local_equiv_eq (local_equiv.ext e.to_local_equiv e'.to_local_equiv h hsymm hs)

/-- The inverse of a local homeomorphism -/
protected def symm : local_homeomorph β α :=
{ open_source        := e.open_target,
  open_target        := e.open_source,
  continuous_to_fun  := e.continuous_inv_fun,
  continuous_inv_fun := e.continuous_to_fun,
  ..e.to_local_equiv.symm }

@[simp] lemma symm_to_local_equiv : e.symm.to_local_equiv = e.to_local_equiv.symm := rfl
@[simp] lemma symm_to_fun : e.symm.to_fun = e.inv_fun := rfl
@[simp] lemma symm_inv_fun : e.symm.inv_fun = e.to_fun := rfl
@[simp] lemma symm_source : e.symm.source = e.target := rfl
@[simp] lemma symm_target : e.symm.target = e.source := rfl
@[simp] lemma symm_symm : e.symm.symm = e := eq_of_local_equiv_eq $ by simp

/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
lemma preimage_interior (s : set β) :
  e.source ∩ e.to_fun ⁻¹' (interior s) = e.source ∩ interior (e.to_fun ⁻¹' s) :=
begin
  apply subset.antisymm,
  { exact e.continuous_to_fun.preimage_interior_subset_interior_preimage e.open_source },
  { calc e.source ∩ interior (e.to_fun ⁻¹' s)
    = (e.source ∩ e.to_fun ⁻¹' e.target) ∩ interior (e.to_fun ⁻¹' s) : begin
        congr,
        apply (inter_eq_self_of_subset_left _).symm,
        apply e.to_local_equiv.source_subset_preimage_target,
      end
    ... = (e.source ∩ interior (e.to_fun ⁻¹' s)) ∩ (e.to_fun ⁻¹' e.target) :
      by simp [inter_comm, inter_assoc]
    ... = (e.source ∩ e.to_fun ⁻¹' (e.inv_fun ⁻¹' (interior (e.to_fun ⁻¹' s)))) ∩ (e.to_fun ⁻¹' e.target) :
      by rw e.to_local_equiv.source_inter_preimage_inv_preimage
    ... = e.source ∩ e.to_fun ⁻¹' (e.target ∩ e.inv_fun ⁻¹' (interior (e.to_fun ⁻¹' s))) :
       by rw [inter_comm e.target, preimage_inter, inter_assoc]
    ... ⊆ e.source ∩ e.to_fun ⁻¹' (e.target ∩ interior (e.inv_fun ⁻¹' (e.to_fun ⁻¹' s))) : begin
        apply inter_subset_inter (subset.refl _) (preimage_mono _),
        exact e.continuous_inv_fun.preimage_interior_subset_interior_preimage e.open_target
      end
    ... = e.source ∩ e.to_fun ⁻¹' (interior (e.target ∩ e.inv_fun ⁻¹' (e.to_fun ⁻¹' s))) :
      by rw [interior_inter, interior_eq_of_open e.open_target]
    ... = e.source ∩ e.to_fun ⁻¹' (interior (e.target ∩ s)) :
      by rw e.to_local_equiv.target_inter_inv_preimage_preimage
    ... = e.source ∩ e.to_fun ⁻¹' e.target ∩ e.to_fun ⁻¹' (interior s) :
      by rw [interior_inter, preimage_inter, interior_eq_of_open e.open_target, inter_assoc]
    ... = e.source ∩ e.to_fun ⁻¹' (interior s) : begin
        congr,
        apply inter_eq_self_of_subset_left,
        apply e.to_local_equiv.source_subset_preimage_target
      end }
end

/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
protected def restr (s : set α) : local_homeomorph α β :=
{ open_source        := is_open_inter e.open_source is_open_interior,
  open_target        := (continuous_on_open_iff e.open_target).1 e.continuous_inv_fun (interior s)
                          is_open_interior,
  continuous_to_fun  := e.continuous_to_fun.mono (inter_subset_left _ _),
  continuous_inv_fun := e.continuous_inv_fun.mono (inter_subset_left _ _),
  ..e.to_local_equiv.restr (interior s) }

@[simp] lemma restr_to_fun (s : set α) : (e.restr s).to_fun = e.to_fun := rfl
@[simp] lemma restr_inv_fun (s : set α) : (e.restr s).inv_fun = e.inv_fun := rfl
@[simp] lemma restr_source (s : set α) : (e.restr s).source = e.source ∩ interior s := rfl
@[simp] lemma restr_target (s : set α) :
  (e.restr s).target = e.target ∩ e.inv_fun ⁻¹' (interior s) := rfl
@[simp] lemma restr_to_local_equiv (s : set α) :
  (e.restr s).to_local_equiv = (e.to_local_equiv).restr (interior s) := rfl

lemma restr_source' (s : set α) (hs : is_open s) : (e.restr s).source = e.source ∩ s :=
by rw [e.restr_source, interior_eq_of_open hs]

lemma restr_to_local_equiv' (s : set α) (hs : is_open s):
  (e.restr s).to_local_equiv = e.to_local_equiv.restr s :=
by rw [e.restr_to_local_equiv, interior_eq_of_open hs]

lemma restr_eq_of_source_subset {e : local_homeomorph α β} {s : set α} (h : e.source ⊆ s) :
  e.restr s = e :=
begin
  apply eq_of_local_equiv_eq,
  rw restr_to_local_equiv,
  apply local_equiv.restr_eq_of_source_subset,
  have := interior_mono h,
  rwa interior_eq_of_open (e.open_source) at this
end

@[simp] lemma restr_univ {e : local_homeomorph α β} : e.restr univ = e :=
restr_eq_of_source_subset (subset_univ _)

/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is less easy
to use than restr because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restr_open (s : set α) (hs : is_open s) :
  local_homeomorph α β :=
{ open_source := is_open_inter e.open_source hs,
  open_target := (continuous_on_open_iff e.open_target).1 e.continuous_inv_fun s hs,
  continuous_to_fun  := e.continuous_to_fun.mono (inter_subset_left _ _),
  continuous_inv_fun := e.continuous_inv_fun.mono (inter_subset_left _ _),
  ..e.to_local_equiv.restr s}

@[simp] lemma restr_open_source (s : set α) (hs : is_open s) :
  (e.restr_open s hs).source = e.source ∩ s := rfl

lemma restr_open_to_local_equiv (s : set α) (hs : is_open s) :
  (e.restr_open s hs).to_local_equiv = e.to_local_equiv.restr s := rfl

/-- The identity on the whole space as a local homeomorphism. -/
protected def refl (α : Type*) [topological_space α] : local_homeomorph α α :=
(homeomorph.refl α).to_local_homeomorph

@[simp] lemma refl_source  : (local_homeomorph.refl α).source = univ := rfl
@[simp] lemma refl_target  : (local_homeomorph.refl α).target = univ := rfl
@[simp] lemma refl_symm    : (local_homeomorph.refl α).symm = local_homeomorph.refl α := rfl
@[simp] lemma refl_to_fun  : (local_homeomorph.refl α).to_fun = id := rfl
@[simp] lemma refl_inv_fun : (local_homeomorph.refl α).inv_fun = id := rfl
@[simp] lemma refl_local_equiv : (local_homeomorph.refl α).to_local_equiv = local_equiv.refl α := rfl

section
variables {s : set α} (hs : is_open s)

/-- The identity local equiv on a set `s` -/
def of_set (s : set α) (hs : is_open s) : local_homeomorph α α :=
{ open_source        := hs,
  open_target        := hs,
  continuous_to_fun  := continuous_id.continuous_on,
  continuous_inv_fun := continuous_id.continuous_on,
  ..local_equiv.of_set s }

@[simp] lemma of_set_source  : (of_set s hs).source = s := rfl
@[simp] lemma of_set_target  : (of_set s hs).target = s := rfl
@[simp] lemma of_set_to_fun  : (of_set s hs).to_fun = id := rfl
@[simp] lemma of_set_inv_fun : (of_set s hs).inv_fun = id := rfl
@[simp] lemma of_set_symm    : (of_set s hs).symm = of_set s hs := rfl
@[simp] lemma of_set_to_local_equiv : (of_set s hs).to_local_equiv = local_equiv.of_set s := rfl

end

/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.target = e'.source) : local_homeomorph α γ :=
{ open_source       := e.open_source,
  open_target       := e'.open_target,
  continuous_to_fun := begin
    apply continuous_on.comp e'.continuous_to_fun e.continuous_to_fun,
    rw [e.to_local_equiv.image_source_eq_target, h]
  end,
  continuous_inv_fun := begin
    apply continuous_on.comp e.continuous_inv_fun e'.continuous_inv_fun,
    rw [e'.to_local_equiv.inv_image_target_eq_source, h],
  end,
  ..local_equiv.trans' e.to_local_equiv e'.to_local_equiv h }

/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : local_homeomorph α γ :=
  local_homeomorph.trans' (e.symm.restr_open e'.source e'.open_source).symm
    (e'.restr_open e.target e.open_target) (by simp [inter_comm])

@[simp] lemma trans_to_local_equiv :
  (e.trans e').to_local_equiv = e.to_local_equiv.trans e'.to_local_equiv := rfl

@[simp] lemma trans_to_fun : (e.trans e').to_fun = e'.to_fun ∘ e.to_fun := rfl
@[simp] lemma trans_inv_fun : (e.trans e').inv_fun = e.inv_fun ∘ e'.inv_fun := rfl

lemma trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm :=
by cases e; cases e'; refl

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
lemma trans_source : (e.trans e').source = e.source ∩ e.to_fun ⁻¹' e'.source :=
local_equiv.trans_source e.to_local_equiv e'.to_local_equiv

lemma trans_source' : (e.trans e').source = e.source ∩ e.to_fun ⁻¹' (e.target ∩ e'.source) :=
local_equiv.trans_source' e.to_local_equiv e'.to_local_equiv

lemma trans_source'' : (e.trans e').source = e.inv_fun '' (e.target ∩ e'.source) :=
local_equiv.trans_source'' e.to_local_equiv e'.to_local_equiv

lemma image_trans_source : e.to_fun '' (e.trans e').source = e.target ∩ e'.source :=
local_equiv.image_trans_source e.to_local_equiv e'.to_local_equiv

lemma trans_target : (e.trans e').target = e'.target ∩ e'.inv_fun ⁻¹' e.target := rfl

lemma trans_target' : (e.trans e').target = e'.target ∩ e'.inv_fun ⁻¹' (e'.source ∩ e.target) :=
trans_source' e'.symm e.symm

lemma trans_target'' : (e.trans e').target = e'.to_fun '' (e'.source ∩ e.target) :=
trans_source'' e'.symm e.symm

lemma inv_image_trans_target : e'.inv_fun '' (e.trans e').target = e'.source ∩ e.target :=
image_trans_source e'.symm e.symm

lemma trans_assoc (e'' : local_homeomorph γ δ) :
  (e.trans e').trans e'' = e.trans (e'.trans e'') :=
eq_of_local_equiv_eq $ local_equiv.trans_assoc e.to_local_equiv e'.to_local_equiv e''.to_local_equiv

@[simp] lemma trans_refl : e.trans (local_homeomorph.refl β) = e :=
eq_of_local_equiv_eq $ local_equiv.trans_refl e.to_local_equiv

@[simp] lemma refl_trans : (local_homeomorph.refl α).trans e = e :=
eq_of_local_equiv_eq $ local_equiv.refl_trans e.to_local_equiv

lemma trans_of_set {s : set β} (hs : is_open s) :
  e.trans (of_set s hs) = e.restr (e.to_fun ⁻¹' s) :=
local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) $
  by simp [local_equiv.trans_source, (e.preimage_interior _).symm, interior_eq_of_open hs]

lemma trans_of_set' {s : set β} (hs : is_open s) :
  e.trans (of_set s hs) = e.restr (e.source ∩ e.to_fun ⁻¹' s) :=
begin
  refine local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) _,
  simp only [refl_source, interior_inter, restr_source, univ_inter, trans_source, of_set_source],
  rw [interior_eq_of_open e.open_source, ← inter_assoc, inter_self,
      (e.preimage_interior _).symm, interior_eq_of_open hs]
end

lemma trans_of_set'' {s : set β} (hs : is_open s) :
  e.trans (of_set s hs) = e.restr (e.source ∩ e.to_fun ⁻¹' s) :=
begin
  refine local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) _,
  simp only [refl_source, interior_inter, restr_source, univ_inter, trans_source, of_set_source],
  rw [interior_eq_of_open e.open_source, ← inter_assoc, inter_self,
      (e.preimage_interior _).symm, interior_eq_of_open hs]
end

lemma restr_trans (s : set α) :
  (e.restr s).trans e' = (e.trans e').restr s :=
eq_of_local_equiv_eq $ local_equiv.restr_trans e.to_local_equiv e'.to_local_equiv (interior s)

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def eq_on_source (e e' : local_homeomorph α β) : Prop :=
e.source = e'.source ∧ (∀x ∈ e.source, e.to_fun x = e'.to_fun x)

lemma eq_on_source_iff (e e' : local_homeomorph α β) :
eq_on_source e e' ↔ local_equiv.eq_on_source e.to_local_equiv e'.to_local_equiv :=
by refl

/-- `eq_on_source` is an equivalence relation -/
instance : setoid (local_homeomorph α β) :=
{ r     := eq_on_source,
  iseqv := ⟨
    λe, (@local_equiv.eq_on_source_setoid α β).iseqv.1 e.to_local_equiv,
    λe e' h, (@local_equiv.eq_on_source_setoid α β).iseqv.2.1 ((eq_on_source_iff e e').1 h),
    λe e' e'' h h', (@local_equiv.eq_on_source_setoid α β).iseqv.2.2
      ((eq_on_source_iff e e').1 h) ((eq_on_source_iff e' e'').1 h')⟩ }

lemma eq_on_source_refl : e ≈ e := setoid.refl _

/-- If two local homeomorphisms are equivalent, so are their inverses -/
lemma eq_on_source_symm {e e' : local_homeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
local_equiv.eq_on_source_symm h

/-- Two equivalent local homeomorphisms have the same source -/
lemma source_eq_of_eq_on_source {e e' : local_homeomorph α β} (h : e ≈ e') : e.source = e'.source :=
h.1

/-- Two equivalent local homeomorphisms have the same target -/
lemma target_eq_of_eq_on_source {e e' : local_homeomorph α β} (h : e ≈ e') : e.target = e'.target :=
(eq_on_source_symm h).1

/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
lemma apply_eq_of_eq_on_source {e e' : local_homeomorph α β} (h : e ≈ e') {x : α} (hx : x ∈ e.source) :
  e.to_fun x = e'.to_fun x :=
h.2 x hx

/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
lemma inv_apply_eq_of_eq_on_source {e e' : local_homeomorph α β} (h : e ≈ e') {x : β} (hx : x ∈ e.target) :
  e.inv_fun x = e'.inv_fun x :=
(eq_on_source_symm h).2 x hx

/-- Composition of local homeomorphisms respects equivalence -/
lemma eq_on_source_trans {e e' : local_homeomorph α β} {f f' : local_homeomorph β γ}
  (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
begin
  change local_equiv.eq_on_source (e.trans f).to_local_equiv (e'.trans f').to_local_equiv,
  simp only [trans_to_local_equiv],
  apply local_equiv.eq_on_source_trans,
  exact he,
  exact hf
end

/-- Restriction of local homeomorphisms respects equivalence -/
lemma eq_on_source_restr {e e' : local_homeomorph α β} (he : e ≈ e') (s : set α) :
  e.restr s ≈ e'.restr s :=
local_equiv.eq_on_source_restr he _

/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
lemma trans_self_symm :
  e.trans e.symm ≈ local_homeomorph.of_set e.source e.open_source :=
local_equiv.trans_self_symm _

lemma trans_symm_self :
  e.symm.trans e ≈ local_homeomorph.of_set e.target e.open_target :=
e.symm.trans_self_symm

lemma eq_of_eq_on_source_univ {e e' : local_homeomorph α β} (h : e ≈ e')
  (s : e.source = univ) (t : e.target = univ) : e = e' :=
eq_of_local_equiv_eq $ local_equiv.eq_of_eq_on_source_univ _ _ h s t

section prod

/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
def prod (e : local_homeomorph α β) (e' : local_homeomorph γ δ) : local_homeomorph (α × γ) (β × δ) :=
{ open_source := is_open_prod e.open_source e'.open_source,
  open_target := is_open_prod e.open_target e'.open_target,
  continuous_to_fun := continuous_on.prod
    (continuous_on.comp e.continuous_to_fun continuous_fst.continuous_on (fst_image_prod_subset _ _))
    (continuous_on.comp e'.continuous_to_fun continuous_snd.continuous_on (snd_image_prod_subset _ _)),
  continuous_inv_fun := continuous_on.prod
    (continuous_on.comp e.continuous_inv_fun continuous_fst.continuous_on (fst_image_prod_subset _ _))
    (continuous_on.comp e'.continuous_inv_fun continuous_snd.continuous_on (snd_image_prod_subset _ _)),
  ..e.to_local_equiv.prod e'.to_local_equiv }

@[simp] lemma prod_to_local_equiv (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').to_local_equiv = e.to_local_equiv.prod e'.to_local_equiv := rfl

@[simp] lemma prod_source (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').source = set.prod e.source e'.source := rfl

@[simp] lemma prod_target (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').target = set.prod e.target e'.target := rfl

@[simp] lemma prod_to_fun (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').to_fun = (λp, (e.to_fun p.1, e'.to_fun p.2)) := rfl

@[simp] lemma prod_inv_fun (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').inv_fun = (λp, (e.inv_fun p.1, e'.inv_fun p.2)) := rfl

end prod

section continuous_on

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
lemma continuous_on_iff_continuous_on_comp_right {f : β → γ} {s : set β} (h : s ⊆ e.target) :
  continuous_on f s ↔ continuous_on (f ∘ e.to_fun) (e.source ∩ e.to_fun ⁻¹' s) :=
begin
  split,
  { assume f_cont,
    apply continuous_on.comp f_cont,
    apply e.continuous_to_fun.mono (inter_subset_left _ _),
    have : e.to_fun '' (e.to_fun ⁻¹' s) ⊆ s :=
      image_preimage_subset _ _,
    exact subset.trans (image_subset _ (inter_subset_right _ _)) this },
  { assume fe_cont,
    have A : e.inv_fun '' s ⊆ e.source ∩ e.to_fun ⁻¹' s,
    { rw [image_subset_iff, preimage_inter],
      assume x hx,
      simp [h hx, hx, e.map_target] },
    have : continuous_on e.inv_fun s := e.continuous_inv_fun.mono h,
    have : continuous_on ((f ∘ e.to_fun) ∘ e.inv_fun) s := continuous_on.comp fe_cont this A,
    refine continuous_on.congr_mono this (λx hx, _) (subset.refl _),
    simp [h hx, hx] }
end

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
lemma continuous_on_iff_continuous_on_comp_left {f : γ → α} {s : set γ} (h : f '' s ⊆ e.source) :
  continuous_on f s ↔ continuous_on (e.to_fun ∘ f) s :=
begin
  split,
  { assume f_cont,
    exact continuous_on.comp e.continuous_to_fun f_cont h },
  { assume fe_cont,
    have : e.to_fun ∘ f '' s ⊆ e.target, from calc
      e.to_fun ∘ f '' s = e.to_fun '' (f '' s) : by rw image_comp
      ... ⊆ e.to_fun '' (e.source) : image_subset _ h
      ... = e.target : e.to_local_equiv.image_source_eq_target,
    have : continuous_on (e.inv_fun ∘ e.to_fun ∘ f) s :=
      continuous_on.comp e.continuous_inv_fun fe_cont this,
    refine continuous_on.congr_mono this (λx hx, _) (subset.refl _),
    have : f x ∈ e.source := h (mem_image_of_mem _ hx),
    simp [this] }
end

end continuous_on

end local_homeomorph

namespace homeomorph
variables (e : homeomorph α β) (e' : homeomorph β γ)
/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/

@[simp] lemma to_local_homeomorph_source  : e.to_local_homeomorph.source = univ := rfl
@[simp] lemma to_local_homeomorph_target  : e.to_local_homeomorph.target = univ := rfl
@[simp] lemma to_local_homeomorph_to_fun  : e.to_local_homeomorph.to_fun = e.to_fun := rfl
@[simp] lemma to_local_homeomorph_inv_fun : e.to_local_homeomorph.inv_fun = e.inv_fun := rfl
@[simp] lemma refl_to_local_homeomorph :
  (homeomorph.refl α).to_local_homeomorph = local_homeomorph.refl α := rfl
@[simp] lemma symm_to_local_homeomorph : e.symm.to_local_homeomorph = e.to_local_homeomorph.symm := rfl
@[simp] lemma trans_to_local_homeomorph :
  (e.trans e').to_local_homeomorph = e.to_local_homeomorph.trans e'.to_local_homeomorph :=
local_homeomorph.eq_of_local_equiv_eq $ equiv.trans_to_local_equiv _ _

end homeomorph
