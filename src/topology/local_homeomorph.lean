/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.equiv.local_equiv
import topology.homeomorph
import topology.opens

/-!
# Local homeomorphisms

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`local_homeomorph α β` is an extension of `local_equiv α β`, i.e., it is a pair of functions
`e.to_fun` and `e.inv_fun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.to_fun x` and `e.inv_fun x`.

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
open_locale topological_space

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
[topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

/-- local homeomorphisms, defined on open subsets of the space -/
@[nolint has_inhabited_instance]
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

instance : has_coe_to_fun (local_homeomorph α β) := ⟨_, λ e, e.to_local_equiv.to_fun⟩

/-- The inverse of a local homeomorphism -/
protected def symm : local_homeomorph β α :=
{ open_source        := e.open_target,
  open_target        := e.open_source,
  continuous_to_fun  := e.continuous_inv_fun,
  continuous_inv_fun := e.continuous_to_fun,
  ..e.to_local_equiv.symm }

protected lemma continuous_on : continuous_on e e.source := e.continuous_to_fun

lemma continuous_on_symm : continuous_on e.symm e.target := e.continuous_inv_fun

@[simp, mfld_simps] lemma mk_coe (e : local_equiv α β) (a b c d) :
  (local_homeomorph.mk e a b c d : α → β) = e := rfl

@[simp, mfld_simps] lemma mk_coe_symm (e : local_equiv α β) (a b c d) :
  ((local_homeomorph.mk e a b c d).symm : β → α) = e.symm := rfl

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/

@[simp, mfld_simps] lemma to_fun_eq_coe (e : local_homeomorph α β) : e.to_fun = e := rfl

@[simp, mfld_simps] lemma inv_fun_eq_coe (e : local_homeomorph α β) : e.inv_fun = e.symm := rfl

@[simp, mfld_simps] lemma coe_coe : (e.to_local_equiv : α → β) = e := rfl

@[simp, mfld_simps] lemma coe_coe_symm : (e.to_local_equiv.symm : β → α) = e.symm := rfl

@[simp, mfld_simps] lemma map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
e.map_source' h

@[simp, mfld_simps] lemma map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
e.map_target' h

@[simp, mfld_simps] lemma left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
e.left_inv' h

@[simp, mfld_simps] lemma right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
e.right_inv' h

lemma source_preimage_target : e.source ⊆ e ⁻¹' e.target := λ _ h, map_source e h

lemma eq_of_local_equiv_eq {e e' : local_homeomorph α β}
  (h : e.to_local_equiv = e'.to_local_equiv) : e = e' :=
begin
  cases e, cases e',
  dsimp at *,
  induction h,
  refl
end

lemma eventually_left_inverse (e : local_homeomorph α β) {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
filter.eventually.mono (mem_nhds_sets e.open_source hx) e.left_inv'

lemma eventually_left_inverse' (e : local_homeomorph α β) {x} (hx : x ∈ e.target) :
  ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
e.eventually_left_inverse (e.map_target hx)

lemma eventually_right_inverse (e : local_homeomorph α β) {x} (hx : x ∈ e.target) :
  ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
filter.eventually.mono (mem_nhds_sets e.open_target hx) e.right_inv'

lemma eventually_right_inverse' (e : local_homeomorph α β) {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
e.eventually_right_inverse (e.map_source hx)

lemma image_eq_target_inter_inv_preimage {s : set α} (h : s ⊆ e.source) :
  e '' s = e.target ∩ e.symm ⁻¹' s :=
e.to_local_equiv.image_eq_target_inter_inv_preimage h

lemma image_inter_source_eq (s : set α) :
  e '' (s ∩ e.source) = e.target ∩ e.symm ⁻¹' (s ∩ e.source) :=
e.image_eq_target_inter_inv_preimage (inter_subset_right _ _)

lemma symm_image_eq_source_inter_preimage {s : set β} (h : s ⊆ e.target) :
  e.symm '' s = e.source ∩ e ⁻¹' s :=
e.symm.image_eq_target_inter_inv_preimage h

lemma symm_image_inter_target_eq (s : set β) :
  e.symm '' (s ∩ e.target) = e.source ∩ e ⁻¹' (s ∩ e.target) :=
e.symm.image_inter_source_eq _

/-- Two local homeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected lemma ext (e' : local_homeomorph α β) (h : ∀x, e x = e' x)
  (hinv : ∀x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
eq_of_local_equiv_eq (local_equiv.ext h hinv hs)

@[simp, mfld_simps] lemma symm_to_local_equiv : e.symm.to_local_equiv = e.to_local_equiv.symm := rfl
-- The following lemmas are already simp via local_equiv
lemma symm_source : e.symm.source = e.target := rfl
lemma symm_target : e.symm.target = e.source := rfl
@[simp, mfld_simps] lemma symm_symm : e.symm.symm = e := eq_of_local_equiv_eq $ by simp

/-- A local homeomorphism is continuous at any point of its source -/
protected lemma continuous_at {x : α} (h : x ∈ e.source) : continuous_at e x :=
(e.continuous_on x h).continuous_at (mem_nhds_sets e.open_source h)

/-- A local homeomorphism inverse is continuous at any point of its target -/
lemma continuous_at_symm {x : β} (h : x ∈ e.target) : continuous_at e.symm x :=
e.symm.continuous_at h

lemma tendsto_symm (e : local_homeomorph α β) {x} (hx : x ∈ e.source) :
  filter.tendsto e.symm (𝓝 (e x)) (𝓝 x) :=
by simpa only [continuous_at, e.left_inv hx] using e.continuous_at_symm (e.map_source hx)

/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
lemma preimage_interior (s : set β) :
  e.source ∩ e ⁻¹' (interior s) = e.source ∩ interior (e ⁻¹' s) :=
begin
  apply subset.antisymm,
  { exact e.continuous_on.preimage_interior_subset_interior_preimage e.open_source },
  { calc e.source ∩ interior (e ⁻¹' s)
        = (e.source ∩ interior (e ⁻¹' s)) ∩ (e ⁻¹' e.target) : by mfld_set_tac
    ... = (e.source ∩ e ⁻¹' (e.symm ⁻¹' (interior (e ⁻¹' s)))) ∩ (e ⁻¹' e.target) :
      begin
        have := e.to_local_equiv.source_inter_preimage_inv_preimage _,
        simp only [coe_coe_symm, coe_coe] at this,
        rw this
      end
    ... = e.source ∩ e ⁻¹' (e.target ∩ e.symm ⁻¹' (interior (e ⁻¹' s))) :
       by rw [inter_comm e.target, preimage_inter, inter_assoc]
    ... ⊆ e.source ∩ e ⁻¹' (e.target ∩ interior (e.symm ⁻¹' (e ⁻¹' s))) : begin
        apply inter_subset_inter (subset.refl _) (preimage_mono _),
        exact e.continuous_on_symm.preimage_interior_subset_interior_preimage e.open_target
      end
    ... = e.source ∩ e ⁻¹' (interior (e.target ∩ e.symm ⁻¹' (e ⁻¹' s))) :
      by rw [interior_inter, interior_eq_of_open e.open_target]
    ... = e.source ∩ e ⁻¹' (interior (e.target ∩ s)) :
      begin
        have := e.to_local_equiv.target_inter_inv_preimage_preimage,
        simp only [coe_coe_symm, coe_coe] at this,
        rw this
      end
    ... = e.source ∩ e ⁻¹' e.target ∩ e ⁻¹' (interior s) :
      by rw [interior_inter, preimage_inter, interior_eq_of_open e.open_target, inter_assoc]
    ... = e.source ∩ e ⁻¹' (interior s) : by mfld_set_tac }
end

lemma preimage_open_of_open {s : set β} (hs : is_open s) : is_open (e.source ∩ e ⁻¹' s) :=
e.continuous_on.preimage_open_of_open e.open_source hs

lemma preimage_open_of_open_symm {s : set α} (hs : is_open s) : is_open (e.target ∩ e.symm ⁻¹' s) :=
e.symm.continuous_on.preimage_open_of_open e.open_target hs

/-- The image of an open set in the source is open. -/
lemma image_open_of_open {s : set α} (hs : is_open s) (h : s ⊆ e.source) : is_open (e '' s) :=
begin
  have : e '' s = e.target ∩ e.symm ⁻¹' s :=
    e.to_local_equiv.image_eq_target_inter_inv_preimage h,
  rw this,
  exact e.continuous_on_symm.preimage_open_of_open e.open_target hs
end

/-- The image of the restriction of an open set to the source is open. -/
lemma image_open_of_open' {s : set α} (hs : is_open s) : is_open (e '' (s ∩ e.source)) :=
begin
  refine image_open_of_open _ (is_open_inter hs e.open_source) _,
  simp,
end

/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restr_open (s : set α) (hs : is_open s) :
  local_homeomorph α β :=
{ open_source := is_open_inter e.open_source hs,
  open_target := (continuous_on_open_iff e.open_target).1 e.continuous_inv_fun s hs,
  continuous_to_fun  := e.continuous_to_fun.mono (inter_subset_left _ _),
  continuous_inv_fun := e.continuous_inv_fun.mono (inter_subset_left _ _),
  ..e.to_local_equiv.restr s}

@[simp, mfld_simps] lemma restr_open_to_local_equiv (s : set α) (hs : is_open s) :
  (e.restr_open s hs).to_local_equiv = e.to_local_equiv.restr s := rfl

-- Already simp via local_equiv
lemma restr_open_source (s : set α) (hs : is_open s) :
  (e.restr_open s hs).source = e.source ∩ s := rfl

/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
protected def restr (s : set α) : local_homeomorph α β :=
e.restr_open (interior s) is_open_interior

@[simp, mfld_simps] lemma restr_to_local_equiv (s : set α) :
  (e.restr s).to_local_equiv = (e.to_local_equiv).restr (interior s) := rfl
@[simp, mfld_simps] lemma restr_coe (s : set α) : (e.restr s : α → β) = e := rfl
@[simp, mfld_simps] lemma restr_coe_symm (s : set α) : ((e.restr s).symm : β → α) = e.symm := rfl
lemma restr_source (s : set α)  : (e.restr s).source = e.source ∩ interior s := rfl
lemma restr_target (s : set α) :
  (e.restr s).target = e.target ∩ e.symm ⁻¹' (interior s) := rfl

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

@[simp, mfld_simps] lemma restr_univ {e : local_homeomorph α β} : e.restr univ = e :=
restr_eq_of_source_subset (subset_univ _)

lemma restr_source_inter (s : set α) : e.restr (e.source ∩ s) = e.restr s :=
begin
  refine local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) _,
  simp [interior_eq_of_open e.open_source],
  rw [← inter_assoc, inter_self]
end

/-- The identity on the whole space as a local homeomorphism. -/
protected def refl (α : Type*) [topological_space α] : local_homeomorph α α :=
(homeomorph.refl α).to_local_homeomorph

@[simp, mfld_simps] lemma refl_local_equiv :
  (local_homeomorph.refl α).to_local_equiv = local_equiv.refl α := rfl
lemma refl_source : (local_homeomorph.refl α).source = univ := rfl
lemma refl_target : (local_homeomorph.refl α).target = univ := rfl
@[simp, mfld_simps] lemma refl_symm : (local_homeomorph.refl α).symm = local_homeomorph.refl α :=
rfl
@[simp, mfld_simps] lemma refl_coe : (local_homeomorph.refl α : α → α) = id := rfl

section
variables {s : set α} (hs : is_open s)

/-- The identity local equiv on a set `s` -/
def of_set (s : set α) (hs : is_open s) : local_homeomorph α α :=
{ open_source        := hs,
  open_target        := hs,
  continuous_to_fun  := continuous_id.continuous_on,
  continuous_inv_fun := continuous_id.continuous_on,
  ..local_equiv.of_set s }

@[simp, mfld_simps] lemma of_set_to_local_equiv :
  (of_set s hs).to_local_equiv = local_equiv.of_set s := rfl
lemma of_set_source : (of_set s hs).source = s := rfl
lemma of_set_target : (of_set s hs).target = s := rfl
@[simp, mfld_simps] lemma of_set_coe : (of_set s hs : α → α) = id := rfl
@[simp, mfld_simps] lemma of_set_symm : (of_set s hs).symm = of_set s hs := rfl

@[simp, mfld_simps] lemma of_set_univ_eq_refl :
  of_set univ is_open_univ = local_homeomorph.refl α :=
by ext; simp

end

/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.target = e'.source) : local_homeomorph α γ :=
{ open_source       := e.open_source,
  open_target       := e'.open_target,
  continuous_to_fun := begin
    apply continuous_on.comp e'.continuous_to_fun e.continuous_to_fun,
    rw ← h,
    exact e.to_local_equiv.source_subset_preimage_target
  end,
  continuous_inv_fun := begin
    apply continuous_on.comp e.continuous_inv_fun e'.continuous_inv_fun,
    rw h,
    exact e'.to_local_equiv.target_subset_preimage_source
  end,
  ..local_equiv.trans' e.to_local_equiv e'.to_local_equiv h }

/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : local_homeomorph α γ :=
  local_homeomorph.trans' (e.symm.restr_open e'.source e'.open_source).symm
    (e'.restr_open e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps] lemma trans_to_local_equiv :
  (e.trans e').to_local_equiv = e.to_local_equiv.trans e'.to_local_equiv := rfl
@[simp, mfld_simps] lemma coe_trans : (e.trans e' : α → γ) = e' ∘ e := rfl
@[simp, mfld_simps] lemma coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm := rfl

lemma trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm :=
by cases e; cases e'; refl

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
lemma trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
local_equiv.trans_source e.to_local_equiv e'.to_local_equiv

lemma trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
local_equiv.trans_source' e.to_local_equiv e'.to_local_equiv

lemma trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
local_equiv.trans_source'' e.to_local_equiv e'.to_local_equiv

lemma image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
local_equiv.image_trans_source e.to_local_equiv e'.to_local_equiv

lemma trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target := rfl

lemma trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
trans_source' e'.symm e.symm

lemma trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
trans_source'' e'.symm e.symm

lemma inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
image_trans_source e'.symm e.symm

lemma trans_assoc (e'' : local_homeomorph γ δ) :
  (e.trans e').trans e'' = e.trans (e'.trans e'') :=
eq_of_local_equiv_eq $ local_equiv.trans_assoc e.to_local_equiv e'.to_local_equiv e''.to_local_equiv

@[simp, mfld_simps] lemma trans_refl : e.trans (local_homeomorph.refl β) = e :=
eq_of_local_equiv_eq $ local_equiv.trans_refl e.to_local_equiv

@[simp, mfld_simps] lemma refl_trans : (local_homeomorph.refl α).trans e = e :=
eq_of_local_equiv_eq $ local_equiv.refl_trans e.to_local_equiv

lemma trans_of_set {s : set β} (hs : is_open s) :
  e.trans (of_set s hs) = e.restr (e ⁻¹' s) :=
local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) $
  by simp [local_equiv.trans_source, (e.preimage_interior _).symm, interior_eq_of_open hs]

lemma trans_of_set' {s : set β} (hs : is_open s) :
  e.trans (of_set s hs) = e.restr (e.source ∩ e ⁻¹' s) :=
by rw [trans_of_set, restr_source_inter]

lemma of_set_trans {s : set α} (hs : is_open s) :
  (of_set s hs).trans e = e.restr s :=
local_homeomorph.ext _ _ (λx, rfl) (λx, rfl) $
  by simp [local_equiv.trans_source, interior_eq_of_open hs, inter_comm]

lemma of_set_trans' {s : set α} (hs : is_open s) :
  (of_set s hs).trans e = e.restr (e.source ∩ s) :=
by rw [of_set_trans, restr_source_inter]

@[simp, mfld_simps] lemma of_set_trans_of_set
  {s : set α} (hs : is_open s) {s' : set α} (hs' : is_open s') :
  (of_set s hs).trans (of_set s' hs') = of_set (s ∩ s') (is_open_inter hs hs')  :=
begin
  rw (of_set s hs).trans_of_set hs',
  ext; simp [interior_eq_of_open hs']
end

lemma restr_trans (s : set α) :
  (e.restr s).trans e' = (e.trans e').restr s :=
eq_of_local_equiv_eq $ local_equiv.restr_trans e.to_local_equiv e'.to_local_equiv (interior s)

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def eq_on_source (e e' : local_homeomorph α β) : Prop :=
e.source = e'.source ∧ (eq_on e e' e.source)

lemma eq_on_source_iff (e e' : local_homeomorph α β) :
eq_on_source e e' ↔ local_equiv.eq_on_source e.to_local_equiv e'.to_local_equiv :=
iff.rfl

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
lemma eq_on_source.symm' {e e' : local_homeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
local_equiv.eq_on_source.symm' h

/-- Two equivalent local homeomorphisms have the same source -/
lemma eq_on_source.source_eq {e e' : local_homeomorph α β} (h : e ≈ e') : e.source = e'.source :=
h.1

/-- Two equivalent local homeomorphisms have the same target -/
lemma eq_on_source.target_eq {e e' : local_homeomorph α β} (h : e ≈ e') : e.target = e'.target :=
h.symm'.1

/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
lemma eq_on_source.eq_on {e e' : local_homeomorph α β} (h : e ≈ e') :
  eq_on e e' e.source :=
h.2

/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
lemma eq_on_source.symm_eq_on_target {e e' : local_homeomorph α β} (h : e ≈ e') :
  eq_on e.symm e'.symm e.target :=
h.symm'.2

/-- Composition of local homeomorphisms respects equivalence -/
lemma eq_on_source.trans' {e e' : local_homeomorph α β} {f f' : local_homeomorph β γ}
  (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
local_equiv.eq_on_source.trans' he hf

/-- Restriction of local homeomorphisms respects equivalence -/
lemma eq_on_source.restr {e e' : local_homeomorph α β} (he : e ≈ e') (s : set α) :
  e.restr s ≈ e'.restr s :=
local_equiv.eq_on_source.restr he _

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
    (e.continuous_to_fun.comp continuous_fst.continuous_on (prod_subset_preimage_fst _ _))
    (e'.continuous_to_fun.comp continuous_snd.continuous_on (prod_subset_preimage_snd _ _)),
  continuous_inv_fun := continuous_on.prod
    (e.continuous_inv_fun.comp continuous_fst.continuous_on (prod_subset_preimage_fst _ _))
    (e'.continuous_inv_fun.comp continuous_snd.continuous_on (prod_subset_preimage_snd _ _)),
  ..e.to_local_equiv.prod e'.to_local_equiv }

@[simp, mfld_simps] lemma prod_to_local_equiv (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').to_local_equiv = e.to_local_equiv.prod e'.to_local_equiv := rfl

lemma prod_source (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').source = set.prod e.source e'.source := rfl

lemma prod_target (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').target = set.prod e.target e'.target := rfl

@[simp, mfld_simps] lemma prod_coe (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e' : α × γ → β × δ) = λp, (e p.1, e' p.2) := rfl

lemma prod_coe_symm (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  ((e.prod e').symm : β × δ → α × γ) = λp, (e.symm p.1, e'.symm p.2) := rfl

@[simp, mfld_simps] lemma prod_symm (e : local_homeomorph α β) (e' : local_homeomorph γ δ) :
  (e.prod e').symm = (e.symm.prod e'.symm) :=
by ext x; simp [prod_coe_symm]

@[simp, mfld_simps] lemma prod_trans
  {η : Type*} {ε : Type*} [topological_space η] [topological_space ε]
  (e : local_homeomorph α β) (f : local_homeomorph β γ)
  (e' : local_homeomorph δ η) (f' : local_homeomorph η ε) :
  (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
by ext x; simp [ext_iff]; tauto

end prod

section continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
lemma continuous_within_at_iff_continuous_within_at_comp_right
  {f : β → γ} {s : set β} {x : β} (h : x ∈ e.target) :
  continuous_within_at f s x ↔
  continuous_within_at (f ∘ e) (e ⁻¹' s) (e.symm x) :=
begin
  split,
  { assume f_cont,
    have : e (e.symm x) = x := e.right_inv h,
    rw ← this at f_cont,
    have : e.source ∈ 𝓝 (e.symm x) := mem_nhds_sets e.open_source (e.map_target h),
    rw [← continuous_within_at_inter this, inter_comm],
    exact continuous_within_at.comp f_cont
      ((e.continuous_at (e.map_target h)).continuous_within_at) (inter_subset_right _ _) },
  { assume fe_cont,
    have : continuous_within_at ((f ∘ e) ∘ e.symm) (s ∩ e.target) x,
    { apply continuous_within_at.comp fe_cont,
      apply (e.continuous_at_symm h).continuous_within_at,
      assume x hx,
      simp [hx.1, hx.2, e.map_target] },
    have : continuous_within_at f (s ∩ e.target) x :=
      continuous_within_at.congr this (λy hy, by simp [hy.2]) (by simp [h]),
    rwa continuous_within_at_inter at this,
    exact mem_nhds_sets e.open_target h }
end

/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
lemma continuous_at_iff_continuous_at_comp_right
  {f : β → γ} {x : β} (h : x ∈ e.target) :
  continuous_at f x ↔ continuous_at (f ∘ e) (e.symm x) :=
by rw [← continuous_within_at_univ, e.continuous_within_at_iff_continuous_within_at_comp_right h,
       preimage_univ, continuous_within_at_univ]

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
lemma continuous_on_iff_continuous_on_comp_right {f : β → γ} {s : set β} (h : s ⊆ e.target) :
  continuous_on f s ↔ continuous_on (f ∘ e) (e.source ∩ e ⁻¹' s) :=
begin
  split,
  { assume f_cont x hx,
    have := e.continuous_within_at_iff_continuous_within_at_comp_right (e.map_source hx.1),
    rw e.left_inv hx.1 at this,
    have A := f_cont _ hx.2,
    rw this at A,
    exact A.mono (inter_subset_right _ _), },
  { assume fe_cont x hx,
    have := e.continuous_within_at_iff_continuous_within_at_comp_right (h hx),
    rw this,
    have : e.source ∈ 𝓝 (e.symm x) := mem_nhds_sets e.open_source (e.map_target (h hx)),
    rw [← continuous_within_at_inter this, inter_comm],
    exact fe_cont _ (by simp [hx, h hx, e.map_target (h hx)]) }
end

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
lemma continuous_within_at_iff_continuous_within_at_comp_left
  {f : γ → α} {s : set γ} {x : γ} (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ nhds_within x s) :
  continuous_within_at f s x ↔ continuous_within_at (e ∘ f) s x :=
begin
  rw [← continuous_within_at_inter' h, ← continuous_within_at_inter' h],
  split,
  { assume f_cont,
    have : e.source ∈ 𝓝 (f x) := mem_nhds_sets e.open_source hx,
    apply continuous_within_at.comp (e.continuous_on (f x) hx) f_cont (inter_subset_right _ _) },
  { assume fe_cont,
    have : continuous_within_at (e.symm ∘ (e ∘ f)) (s ∩ f ⁻¹' e.source) x,
    { have : continuous_within_at e.symm univ (e (f x))
        := (e.continuous_at_symm (e.map_source hx)).continuous_within_at,
      exact continuous_within_at.comp this fe_cont (subset_univ _) },
    exact this.congr (λy hy, by simp [e.left_inv hy.2]) (by simp [e.left_inv hx]) }
end

/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
lemma continuous_at_iff_continuous_at_comp_left
  {f : γ → α} {x : γ} (h : f ⁻¹' e.source ∈ 𝓝 x) :
  continuous_at f x ↔ continuous_at (e ∘ f) x :=
begin
  have hx : f x ∈ e.source := (mem_of_nhds h : _),
  have h' : f ⁻¹' e.source ∈ nhds_within x univ, by rwa nhds_within_univ,
  rw [← continuous_within_at_univ, ← continuous_within_at_univ,
      e.continuous_within_at_iff_continuous_within_at_comp_left hx h']
end

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
lemma continuous_on_iff_continuous_on_comp_left {f : γ → α} {s : set γ} (h : s ⊆ f ⁻¹' e.source) :
  continuous_on f s ↔ continuous_on (e ∘ f) s :=
begin
  split,
  { assume f_cont,
    exact e.continuous_on.comp f_cont h },
  { assume fe_cont,
    have : continuous_on (e.symm ∘ e ∘ f) s,
    { apply continuous_on.comp e.continuous_on_symm fe_cont,
      assume x hx,
      have : f x ∈ e.source := h hx,
      simp [this] },
    refine continuous_on.congr_mono this (λx hx, _) (subset.refl _),
    have : f x ∈ e.source := h hx,
    simp [this] }
end

end continuity

/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
def to_homeomorph_of_source_eq_univ_target_eq_univ (h : e.source = (univ : set α))
  (h' : e.target = univ) : homeomorph α β :=
{ to_fun := e,
  inv_fun := e.symm,
  left_inv := λx, e.left_inv $ by { rw h, exact mem_univ _ },
  right_inv := λx, e.right_inv $ by { rw h', exact mem_univ _ },
  continuous_to_fun := begin
    rw [continuous_iff_continuous_on_univ],
    convert e.continuous_to_fun,
    rw h
  end,
  continuous_inv_fun := begin
    rw [continuous_iff_continuous_on_univ],
    convert e.continuous_inv_fun,
    rw h'
  end }

@[simp, mfld_simps] lemma to_homeomorph_coe (h : e.source = (univ : set α)) (h' : e.target = univ) :
  (e.to_homeomorph_of_source_eq_univ_target_eq_univ h h' : α → β) = e := rfl

@[simp, mfld_simps] lemma to_homeomorph_symm_coe
  (h : e.source = (univ : set α)) (h' : e.target = univ) :
  ((e.to_homeomorph_of_source_eq_univ_target_eq_univ h h').symm : β → α) = e.symm := rfl

/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `open_embedding.to_local_homeomorph`. -/
lemma to_open_embedding (h : e.source = set.univ) : open_embedding e.to_fun :=
begin
  apply open_embedding_of_continuous_injective_open,
  { apply continuous_iff_continuous_on_univ.mpr,
    rw ← h,
    exact e.continuous_to_fun },
  { apply set.injective_iff_inj_on_univ.mpr,
    rw ← h,
    exact e.to_local_equiv.bij_on_source.inj_on },
  { intros U hU,
    simpa only [h, subset_univ] with mfld_simps using e.image_open_of_open hU}
end

end local_homeomorph

namespace homeomorph
variables (e : homeomorph α β) (e' : homeomorph β γ)
/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/

@[simp, mfld_simps] lemma to_local_homeomorph_source   : e.to_local_homeomorph.source = univ := rfl
@[simp, mfld_simps] lemma to_local_homeomorph_target   : e.to_local_homeomorph.target = univ := rfl
@[simp, mfld_simps] lemma to_local_homeomorph_coe      : (e.to_local_homeomorph : α → β) = e := rfl
@[simp, mfld_simps] lemma to_local_homeomorph_coe_symm :
  (e.to_local_homeomorph.symm : β → α) = e.symm := rfl
@[simp, mfld_simps] lemma refl_to_local_homeomorph :
  (homeomorph.refl α).to_local_homeomorph = local_homeomorph.refl α := rfl
@[simp, mfld_simps] lemma symm_to_local_homeomorph :
  e.symm.to_local_homeomorph = e.to_local_homeomorph.symm := rfl
@[simp, mfld_simps] lemma trans_to_local_homeomorph :
  (e.trans e').to_local_homeomorph = e.to_local_homeomorph.trans e'.to_local_homeomorph :=
local_homeomorph.eq_of_local_equiv_eq $ equiv.trans_to_local_equiv _ _

end homeomorph

namespace open_embedding
variables [nonempty α]
variables {f : α → β} (h : open_embedding f)
include f h

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local equivalence whose source
is all of `α`.  This is mainly an auxiliary lemma for the stronger result `to_local_homeomorph`. -/
noncomputable def to_local_equiv : local_equiv α β :=
set.inj_on.to_local_equiv f set.univ (set.injective_iff_inj_on_univ.mp h.to_embedding.inj)

@[simp, mfld_simps] lemma to_local_equiv_coe : (h.to_local_equiv : α → β) = f := rfl
@[simp, mfld_simps] lemma to_local_equiv_source : h.to_local_equiv.source = set.univ := rfl

@[simp, mfld_simps] lemma to_local_equiv_target : h.to_local_equiv.target = set.range f :=
begin
  rw ←local_equiv.image_source_eq_target,
  ext,
  split,
  { exact λ ⟨a, _, h'⟩, ⟨a, h'⟩ },
  { exact λ ⟨a, h'⟩, ⟨a, by trivial, h'⟩ }
end

lemma open_target : is_open h.to_local_equiv.target :=
by simpa only with mfld_simps using h.open_range

lemma continuous_inv_fun : continuous_on h.to_local_equiv.inv_fun h.to_local_equiv.target :=
begin
  apply (continuous_on_open_iff h.open_target).mpr,
  intros t ht,
  simp only with mfld_simps,
  convert h.open_iff_image_open.mp ht,
  ext y,
  have hinv : ∀ x : α, (f x = y) → h.to_local_equiv.symm y = x :=
    λ x hxy, by { simpa only [hxy.symm] with mfld_simps using h.to_local_equiv.left_inv },
  simp only [mem_image, mem_range] with mfld_simps,
  split,
  { rintros ⟨⟨x, hxy⟩, hy⟩,
    refine ⟨x, _, hxy⟩,
    rwa (hinv x hxy) at hy },
  { rintros ⟨x, hx, hxy⟩,
    refine ⟨⟨x, hxy⟩, _⟩,
    rwa ← (hinv x hxy) at hx }
end

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `local_homeomorph.to_open_embedding`. -/
noncomputable def to_local_homeomorph : local_homeomorph α β :=
{ to_local_equiv := h.to_local_equiv,
  open_source := is_open_univ,
  open_target := h.open_target,
  continuous_to_fun := by simpa only with mfld_simps using h.continuous.continuous_on,
  continuous_inv_fun := h.continuous_inv_fun }

@[simp, mfld_simps] lemma to_local_homeomorph_coe : (h.to_local_homeomorph : α → β) = f := rfl
@[simp, mfld_simps] lemma source : h.to_local_homeomorph.source = set.univ := rfl
@[simp, mfld_simps] lemma target : h.to_local_homeomorph.target = set.range f :=
h.to_local_equiv_target

end open_embedding

namespace topological_space.opens

open topological_space
variables (s : opens α) [nonempty s]

/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
noncomputable def local_homeomorph_subtype_coe : local_homeomorph s α :=
open_embedding.to_local_homeomorph (s.2.open_embedding_subtype_coe)

@[simp, mfld_simps] lemma local_homeomorph_subtype_coe_coe :
  (s.local_homeomorph_subtype_coe : s → α) = coe := rfl

@[simp, mfld_simps] lemma local_homeomorph_subtype_coe_source :
  s.local_homeomorph_subtype_coe.source = set.univ := rfl

@[simp, mfld_simps] lemma local_homeomorph_subtype_coe_target :
  s.local_homeomorph_subtype_coe.target = s :=
by { simp only [local_homeomorph_subtype_coe, subtype.range_coe_subtype] with mfld_simps, refl }

end topological_space.opens

namespace local_homeomorph

open topological_space
variables (e : local_homeomorph α β)
variables (s : opens α) [nonempty s]

/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
noncomputable def subtype_restr : local_homeomorph s β := s.local_homeomorph_subtype_coe.trans e

lemma subtype_restr_def : e.subtype_restr s = s.local_homeomorph_subtype_coe.trans e := rfl

@[simp, mfld_simps] lemma subtype_restr_coe : ((e.subtype_restr s : local_homeomorph s β) : s → β)
  = set.restrict (e : α → β) s := rfl

@[simp, mfld_simps] lemma subtype_restr_source : (e.subtype_restr s).source = coe ⁻¹' e.source :=
by simp only [subtype_restr_def] with mfld_simps

/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
lemma subtype_restr_symm_trans_subtype_restr (f f' : local_homeomorph α β) :
  (f.subtype_restr s).symm.trans (f'.subtype_restr s)
  ≈ (f.symm.trans f').restr (f.target ∩ (f.symm) ⁻¹' s) :=
begin
  simp only [subtype_restr_def, trans_symm_eq_symm_trans_symm],
  have openness₁ : is_open (f.target ∩ f.symm ⁻¹' s) := f.preimage_open_of_open_symm s.2,
  rw [← of_set_trans _ openness₁, ← trans_assoc, ← trans_assoc],
  refine eq_on_source.trans' _ (eq_on_source_refl _),
  -- f' has been eliminated !!!
  have sets_identity : f.symm.source ∩ (f.target ∩ (f.symm) ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s,
  { mfld_set_tac },
  have openness₂ : is_open (s : set α) := s.2,
  rw [of_set_trans', sets_identity, ← trans_of_set' _ openness₂, trans_assoc],
  refine eq_on_source.trans' (eq_on_source_refl _) _,
  -- f has been eliminated !!!
  refine setoid.trans (trans_symm_self s.local_homeomorph_subtype_coe) _,
  simp only with mfld_simps,
end

end local_homeomorph
