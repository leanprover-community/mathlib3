/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import data.equiv.basic

/-!
# Local equivalences

This files defines equivalences between subsets of given types.
An element `e` of `local_equiv α β` is made of two maps `e.to_fun` and `e.inv_fun` respectively
from α to β and from  β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two local equivalences by restricting
the source and target to the maximal set where the composition makes sense.

Contrary to equivs, we do not register the coercion to functions and we use explicitly to_fun and
inv_fun: coercions create numerous unification problems for manifolds.

## Main definitions

`equiv.to_local_equiv`: associating a local equiv to an equiv, with source = target = univ
`local_equiv.symm`    : the inverse of a local equiv
`local_equiv.trans`   : the composition of two local equivs
`local_equiv.refl`    : the identity local equiv
`local_equiv.of_set`  : the identity on a set `s`
`eq_on_source`        : equivalence relation describing the "right" notion of equality for local
                        equivs (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of local equivalences:
* equivs on subtypes
* pairs of functions taking values in `option α` and `option β`, equal to none where the local
equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
restriction of domains. Checking that one always belongs to the right subtype makes things very
tedious, and leads quickl to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
the domain is restricted automatically). These are implemented in `pequiv.lean`. For manifolds,
where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
overhead as one would need to extend all classes of smoothness to option-valued maps.
* The local_equiv version as explained above is easier to use for manifolds. The drawback is that
there is extra useless data (the values of `to_fun` and `inv_fun` outside of `source` and `target`).
In particular, the equality notion between local equivs is not "the right one", i.e., coinciding
source and target and equality there. Moreover, there are no local equivs in this sense between
an empty type and a nonempty type. Since empty types are not that useful, and since one almost never
needs to talk about equal local equivs, this is not an issue in practice.
Still, we introduce an equivalence relation `eq_on_source` that captures this right notion of
equality, and show that many properties are invariant under this equivalence relation.
-/

open function set

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

structure local_equiv (α : Type*) (β : Type*) :=
(to_fun     : α → β)
(inv_fun    : β → α)
(source     : set α)
(target     : set β)
(map_source : ∀{x}, x ∈ source → to_fun x ∈ target)
(map_target : ∀{x}, x ∈ target → inv_fun x ∈ source)
(left_inv   : ∀{x}, x ∈ source → inv_fun (to_fun x) = x)
(right_inv  : ∀{x}, x ∈ target → to_fun (inv_fun x) = x)

attribute [simp] local_equiv.left_inv local_equiv.right_inv

def equiv.to_local_equiv (e : equiv α β) : local_equiv α β :=
{ to_fun     := e.to_fun,
  inv_fun    := e.inv_fun,
  source     := univ,
  target     := univ,
  map_source := λx hx, mem_univ _,
  map_target := λy hy, mem_univ _,
  left_inv   := λx hx, e.left_inv x,
  right_inv  := λx hx, e.right_inv x }

namespace local_equiv

variables (e : local_equiv α β) (e' : local_equiv β γ)

protected def to_equiv : equiv (e.source) (e.target) :=
{ to_fun    := λ⟨x, hx⟩, ⟨e.to_fun x, e.map_source hx⟩,
  inv_fun   := λ⟨y, hy⟩, ⟨e.inv_fun y, e.map_target hy⟩,
  left_inv  := λ⟨x, hx⟩, subtype.eq $ e.left_inv hx,
  right_inv := λ⟨y, hy⟩, subtype.eq $ e.right_inv hy }

protected def symm : local_equiv β α :=
{ to_fun     := e.inv_fun,
  inv_fun    := e.to_fun,
  source     := e.target,
  target     := e.source,
  map_source := e.map_target,
  map_target := e.map_source,
  left_inv   := e.right_inv,
  right_inv  := e.left_inv }

@[simp] lemma symm_to_fun : e.symm.to_fun = e.inv_fun := rfl
@[simp] lemma symm_inv_fun : e.symm.inv_fun = e.to_fun := rfl
@[simp] lemma symm_source : e.symm.source = e.target := rfl
@[simp] lemma symm_target : e.symm.target = e.source := rfl
@[simp] lemma symm_symm : e.symm.symm = e := by { cases e, refl }

lemma bij_on_source : bij_on e.to_fun e.source e.target :=
bij_on_of_inv_on e.map_source e.map_target ⟨e.left_inv, e.right_inv⟩

lemma image_eq_target_inter_inv_preimage {s : set α} (h : s ⊆ e.source) :
  e.to_fun '' s = e.target ∩ e.inv_fun ⁻¹' s :=
begin
  refine subset.antisymm (λx hx, _) (λx hx, _),
  { rcases (mem_image _ _ _).1 hx with ⟨y, ys, hy⟩,
    rw ← hy,
    split,
    { apply e.map_source,
      exact h ys },
    { rwa [mem_preimage, e.left_inv (h ys)] } },
  { rw ← e.right_inv hx.1,
    exact mem_image_of_mem _ hx.2 }
end

lemma inv_image_eq_source_inter_preimage {s : set β} (h : s ⊆ e.target) :
  e.inv_fun '' s = e.source ∩ e.to_fun ⁻¹' s :=
e.symm.image_eq_target_inter_inv_preimage h

lemma source_inter_preimage_inv_preimage (s : set α) :
  e.source ∩ e.to_fun ⁻¹' (e.inv_fun ⁻¹' s) = e.source ∩ s :=
begin
  ext, split,
  { rintros ⟨hx, xs⟩,
    simp only [mem_preimage, hx, e.left_inv, mem_preimage] at xs,
    exact ⟨hx, xs⟩ },
  { rintros ⟨hx, xs⟩,
    simp [hx, xs] }
end

lemma target_inter_inv_preimage_preimage (s : set β) :
  e.target ∩ e.inv_fun ⁻¹' (e.to_fun ⁻¹' s) = e.target ∩ s :=
e.symm.source_inter_preimage_inv_preimage _

lemma image_source_eq_target : e.to_fun '' e.source = e.target :=
image_eq_of_bij_on e.bij_on_source

lemma source_subset_preimage_target : e.source ⊆ e.to_fun ⁻¹' e.target :=
λx hx, e.map_source hx

lemma inv_image_target_eq_source : e.inv_fun '' e.target = e.source :=
image_eq_of_bij_on e.symm.bij_on_source

lemma target_subset_preimage_source : e.target ⊆ e.inv_fun ⁻¹' e.source :=
λx hx, e.map_target hx

protected lemma eq (e' : local_equiv α β) (h : ∀x, e.to_fun x = e'.to_fun x)
  (hsymm : ∀x, e.inv_fun x = e'.inv_fun x) (hs : e.source = e'.source) : e = e' :=
begin
  have A : e.to_fun = e'.to_fun, by { ext x, exact h x },
  have B : e.inv_fun = e'.inv_fun, by { ext x, exact hsymm x },
  have I : e.to_fun '' e.source = e.target := e.image_source_eq_target,
  have I' : e'.to_fun '' e'.source = e'.target := e'.image_source_eq_target,
  rw [A, hs, I'] at I,
  cases e; cases e',
  simp * at *
end

/-- Restricting a local equivalence to e.source ∩ s -/
protected def restr (s : set α) : local_equiv α β :=
{ to_fun  := e.to_fun,
  inv_fun := e.inv_fun,
  source  := e.source ∩ s,
  target  := e.target ∩ e.inv_fun⁻¹' s,
  map_source  := λx hx, begin
    apply mem_inter,
    { apply e.map_source,
      exact hx.1 },
    { rw [mem_preimage, e.left_inv],
      exact hx.2,
      exact hx.1 },
  end,
  map_target := λy hy, begin
    apply mem_inter,
    { apply e.map_target,
      exact hy.1 },
    { exact hy.2 },
  end,
  left_inv := λx hx, e.left_inv hx.1,
  right_inv := λy hy, e.right_inv hy.1 }

@[simp] lemma restr_to_fun (s : set α) : (e.restr s).to_fun = e.to_fun := rfl
@[simp] lemma restr_inv_fun (s : set α) : (e.restr s).inv_fun = e.inv_fun := rfl
@[simp] lemma restr_source (s : set α) : (e.restr s).source = e.source ∩ s := rfl
@[simp] lemma restr_target (s : set α) : (e.restr s).target = e.target ∩ e.inv_fun ⁻¹' s := rfl

lemma restr_eq_of_source_subset {e : local_equiv α β} {s : set α} (h : e.source ⊆ s) :
  e.restr s = e :=
local_equiv.eq _ _ (λ_, rfl) (λ_, rfl) (by simp [inter_eq_self_of_subset_left h])

@[simp] lemma restr_univ {e : local_equiv α β} : e.restr univ = e :=
restr_eq_of_source_subset (subset_univ _)

/-- The identity local equiv -/
protected def refl (α : Type*) : local_equiv α α := (equiv.refl α).to_local_equiv

@[simp] lemma refl_source : (local_equiv.refl α).source = univ := rfl
@[simp] lemma refl_target : (local_equiv.refl α).target = univ := rfl
@[simp] lemma refl_to_fun : (local_equiv.refl α).to_fun = id := rfl
@[simp] lemma refl_inv_fun : (local_equiv.refl α).inv_fun = id := rfl
@[simp] lemma refl_symm : (local_equiv.refl α).symm = local_equiv.refl α := rfl

@[simp] lemma refl_restr_source (s : set α) : ((local_equiv.refl α).restr s).source = s :=
by simp

@[simp] lemma refl_restr_target (s : set α) : ((local_equiv.refl α).restr s).target = s :=
by { change univ ∩ id⁻¹' s = s, simp }

/-- The identity local equiv on a set `s` -/
def of_set (s : set α) : local_equiv α α :=
{ to_fun     := id,
  inv_fun    := id,
  source     := s,
  target     := s,
  map_source := λx hx, hx,
  map_target := λx hx, hx,
  left_inv   := λx hx, rfl,
  right_inv  := λx hx, rfl }

@[simp] lemma of_set_source (s : set α) : (local_equiv.of_set s).source = s := rfl
@[simp] lemma of_set_target (s : set α) : (local_equiv.of_set s).target = s := rfl
@[simp] lemma of_set_to_fun (s : set α) : (local_equiv.of_set s).to_fun = id := rfl
@[simp] lemma of_set_inv_fun {s : set α} : (local_equiv.of_set s).inv_fun = id := rfl
@[simp] lemma of_set_symm (s : set α) : (local_equiv.of_set s).symm = local_equiv.of_set s := rfl

/-- Composing two local equivs if the target of the first coincides with the source of the
second. -/
protected def trans' (e' : local_equiv β γ) (h : e.target = e'.source) :
  local_equiv α γ :=
{ to_fun := e'.to_fun ∘ e.to_fun,
  inv_fun := e.inv_fun ∘ e'.inv_fun,
  source := e.source,
  target := e'.target,
  map_source := λx hx, begin
    apply e'.map_source,
    rw ← h,
    apply e.map_source hx
  end,
  map_target := λy hy, begin
    apply e.map_target,
    rw h,
    apply e'.map_target hy
  end,
  left_inv := λx hx, begin
    change e.inv_fun (e'.inv_fun (e'.to_fun (e.to_fun x))) = x,
    rw e'.left_inv,
    { exact e.left_inv hx },
    { rw ← h, exact e.map_source hx }
  end,
  right_inv := λy hy, begin
    change e'.to_fun (e.to_fun (e.inv_fun (e'.inv_fun y))) = y,
    rw e.right_inv,
    { exact e'.right_inv hy },
    { rw h, exact e'.map_target hy }
  end }

/-- Composing two local equivs, by restricting to the maximal domain where their composition
is well defined. -/
protected def trans : local_equiv α γ :=
  local_equiv.trans' (e.symm.restr (e'.source)).symm (e'.restr (e.target)) (inter_comm _ _)

@[simp] lemma trans_to_fun : (e.trans e').to_fun = e'.to_fun ∘ e.to_fun := rfl
@[simp] lemma trans_apply (x : α) : (e.trans e').to_fun x = e'.to_fun (e.to_fun x) := rfl
@[simp] lemma trans_inv_fun : (e.trans e').inv_fun = e.inv_fun ∘ e'.inv_fun := rfl
@[simp] lemma trans_inv_apply (x : γ) : (e.trans e').inv_fun x = e.inv_fun (e'.inv_fun x) := rfl

lemma trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm :=
by cases e; cases e'; refl

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
lemma trans_source : (e.trans e').source = e.source ∩ e.to_fun ⁻¹' e'.source := rfl

lemma trans_source' : (e.trans e').source = e.source ∩ e.to_fun ⁻¹' (e.target ∩ e'.source) :=
begin
  symmetry, calc
    e.source ∩ e.to_fun ⁻¹' (e.target ∩ e'.source) =
    (e.source ∩ e.to_fun ⁻¹' (e.target)) ∩ e.to_fun ⁻¹' (e'.source) :
      by rw [preimage_inter, inter_assoc]
    ... = e.source ∩ e.to_fun ⁻¹' (e'.source) :
      by { congr' 1, apply inter_eq_self_of_subset_left e.source_subset_preimage_target }
    ... = (e.trans e').source : rfl
end

lemma trans_source'' : (e.trans e').source = e.inv_fun '' (e.target ∩ e'.source) :=
begin
  rw [e.trans_source', e.inv_image_eq_source_inter_preimage, inter_comm],
  exact inter_subset_left _ _,
end

lemma image_trans_source : e.to_fun '' (e.trans e').source = e.target ∩ e'.source :=
image_source_eq_target (local_equiv.symm (local_equiv.restr (local_equiv.symm e) (e'.source)))

lemma trans_target : (e.trans e').target = e'.target ∩ e'.inv_fun ⁻¹' e.target := rfl

lemma trans_target' : (e.trans e').target = e'.target ∩ e'.inv_fun ⁻¹' (e'.source ∩ e.target) :=
trans_source' e'.symm e.symm

lemma trans_target'' : (e.trans e').target = e'.to_fun '' (e'.source ∩ e.target) :=
trans_source'' e'.symm e.symm

lemma inv_image_trans_target : e'.inv_fun '' (e.trans e').target = e'.source ∩ e.target :=
image_trans_source e'.symm e.symm

lemma trans_assoc (e'' : local_equiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
local_equiv.eq _ _ (λx, rfl) (λx, rfl) (by simp [trans_source, @preimage_comp α β γ, inter_assoc])

@[simp] lemma trans_refl : e.trans (local_equiv.refl β) = e :=
local_equiv.eq _ _ (λx, rfl) (λx, rfl) (by simp [trans_source])

@[simp] lemma refl_trans : (local_equiv.refl α).trans e = e :=
local_equiv.eq _ _ (λx, rfl) (λx, rfl) (by simp [trans_source, preimage_id])

lemma trans_refl_restr (s : set β) :
  e.trans ((local_equiv.refl β).restr s) = e.restr (e.to_fun ⁻¹' s) :=
local_equiv.eq _ _ (λx, rfl) (λx, rfl) (by simp [trans_source])

lemma trans_refl_restr' (s : set β) :
  e.trans ((local_equiv.refl β).restr s) = e.restr (e.source ∩ e.to_fun ⁻¹' s) :=
local_equiv.eq _ _ (λx, rfl) (λx, rfl) $ by { simp [trans_source], rw [← inter_assoc, inter_self] }

lemma restr_trans (s : set α) :
  (e.restr s).trans e' = (e.trans e').restr s :=
local_equiv.eq _ _ (λx, rfl) (λx, rfl) $ by { simp [trans_source, inter_comm], rwa inter_assoc }

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same local equiv. -/
def eq_on_source (e e' : local_equiv α β) : Prop :=
e.source = e'.source ∧ (∀x ∈ e.source, e.to_fun x = e'.to_fun x)

/-- `eq_on_source` is an equivalence relation -/
instance eq_on_source_setoid : setoid (local_equiv α β) :=
{ r     := eq_on_source,
  iseqv := ⟨
    λe, by simp [eq_on_source],
    λe e' h, by { simp [eq_on_source, h.1.symm], exact λx hx, (h.2 x hx).symm },
    λe e' e'' h h', ⟨by rwa [← h'.1, ← h.1], λx hx, by { rw [← h'.2 x, h.2 x hx], rwa ← h.1 }⟩⟩ }

lemma eq_on_source_refl : e ≈ e := setoid.refl _

/-- If two local equivs are equivalent, so are their inverses -/
lemma eq_on_source_symm {e e' : local_equiv α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
begin
  have T : e.target = e'.target,
  { have : set.bij_on e'.to_fun e.source e.target := bij_on_of_eq_on h.2 e.bij_on_source,
    have A : e'.to_fun '' e.source = e.target := image_eq_of_bij_on this,
    rw [h.1, image_eq_of_bij_on e'.bij_on_source] at A,
    exact A.symm },
  refine ⟨T, λx hx, _⟩,
  have xt : x ∈ e.target := hx,
  rw T at xt,
  have e's : e'.inv_fun x ∈ e.source, by { rw h.1, apply e'.map_target xt },
  have A : e.to_fun (e.inv_fun x) = x := e.right_inv hx,
  have B : e.to_fun (e'.inv_fun x) = x,
    by { rw h.2, exact e'.right_inv xt, exact e's },
  apply inj_on_of_bij_on e.bij_on_source (e.map_target hx) e's,
  rw [A, B]
end

/-- Two equivalent local equivs have the same source -/
lemma source_eq_of_eq_on_source {e e' : local_equiv α β} (h : e ≈ e') : e.source = e'.source :=
h.1

/-- Two equivalent local equivs have the same target -/
lemma target_eq_of_eq_on_source {e e' : local_equiv α β} (h : e ≈ e') : e.target = e'.target :=
(eq_on_source_symm h).1

/-- Two equivalent local equivs coincide on the source -/
lemma apply_eq_of_eq_on_source {e e' : local_equiv α β} (h : e ≈ e') {x : α} (hx : x ∈ e.source) :
  e.to_fun x = e'.to_fun x :=
h.2 x hx

/-- Two equivalent local equivs have coinciding inverses on the target -/
lemma inv_apply_eq_of_eq_on_source {e e' : local_equiv α β} (h : e ≈ e') {x : β} (hx : x ∈ e.target) :
  e.inv_fun x = e'.inv_fun x :=
(eq_on_source_symm h).2 x hx

/-- Composition of local equivs respects equivalence -/
lemma eq_on_source_trans {e e' : local_equiv α β} {f f' : local_equiv β γ}
  (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
begin
  split,
  { have : e.target = e'.target := (eq_on_source_symm he).1,
    rw [trans_source'', trans_source'', ← this, ← hf.1],
    exact image_eq_image_of_eq_on (λx hx, (eq_on_source_symm he).2 x hx.1) },
  { assume x hx,
    rw trans_source at hx,
    simp [(he.2 x hx.1).symm, hf.2 _ hx.2] }
end

/-- Restriction of local equivs respects equivalence -/
lemma eq_on_source_restr {e e' : local_equiv α β} (he : e ≈ e') (s : set α) :
  e.restr s ≈ e'.restr s :=
begin
  split,
  { simp [he.1] },
  { assume x hx,
    simp only [mem_inter_eq, restr_source] at hx,
    exact he.2 x hx.1 }
end

/-- Preimages are respected by equivalence -/
lemma eq_on_source_preimage {e e' : local_equiv α β} (he : e ≈ e') (s : set β) :
  e.source ∩ e.to_fun ⁻¹' s = e'.source ∩ e'.to_fun ⁻¹' s :=
begin
  ext x,
  simp only [mem_inter_eq, mem_preimage],
  split,
  { assume hx,
    rwa [apply_eq_of_eq_on_source (setoid.symm he), source_eq_of_eq_on_source (setoid.symm he)],
    rw source_eq_of_eq_on_source he at hx,
    exact hx.1 },
  { assume hx,
    rwa [apply_eq_of_eq_on_source he, source_eq_of_eq_on_source he],
    rw source_eq_of_eq_on_source (setoid.symm he) at hx,
    exact hx.1 },
end

/-- Composition of a local equiv and its inverse is equivalent to the restriction of the identity
to the source -/
lemma trans_self_symm :
  e.trans e.symm ≈ local_equiv.of_set e.source :=
begin
  have A : (e.trans e.symm).source = e.source,
    by simp [trans_source, inter_eq_self_of_subset_left (source_subset_preimage_target _)],
  refine ⟨by simp [A], λx hx, _⟩,
  rw A at hx,
  simp [hx]
end

lemma trans_symm_self :
  e.symm.trans e ≈ local_equiv.of_set e.target :=
trans_self_symm (e.symm)

/-- Two equivalent local equivs are equal when the source and target are univ -/
lemma eq_of_eq_on_source_univ (e e' : local_equiv α β) (h : e ≈ e')
  (s : e.source = univ) (t : e.target = univ) : e = e' :=
begin
  apply local_equiv.eq _ _ (λx, _) (λx, _) h.1,
  { apply h.2 x,
    rw s,
    exact mem_univ _ },
  { apply (eq_on_source_symm h).2 x,
    rw [symm_source, t],
    exact mem_univ _ }
end

section prod

/-- The product of two local equivs, as a local equiv on the product. -/
def prod (e : local_equiv α β) (e' : local_equiv γ δ) : local_equiv (α × γ) (β × δ) :=
{ source := set.prod e.source e'.source,
  target := set.prod e.target e'.target,
  to_fun := λp, (e.to_fun p.1, e'.to_fun p.2),
  inv_fun := λp, (e.inv_fun p.1, e'.inv_fun p.2),
  map_source := λp hp, by { simp at hp, simp [map_source, hp] },
  map_target := λp hp, by { simp at hp, simp [map_target, hp] },
  left_inv := λp hp, by { simp at hp, simp [hp] },
  right_inv := λp hp, by { simp at hp, simp [hp] } }

@[simp] lemma prod_source (e : local_equiv α β) (e' : local_equiv γ δ) :
  (e.prod e').source = set.prod e.source e'.source := rfl

@[simp] lemma prod_target (e : local_equiv α β) (e' : local_equiv γ δ) :
  (e.prod e').target = set.prod e.target e'.target := rfl

@[simp] lemma prod_to_fun (e : local_equiv α β) (e' : local_equiv γ δ) :
  (e.prod e').to_fun = (λp, (e.to_fun p.1, e'.to_fun p.2)) := rfl

@[simp] lemma prod_inv_fun (e : local_equiv α β) (e' : local_equiv γ δ) :
  (e.prod e').inv_fun = (λp, (e.inv_fun p.1, e'.inv_fun p.2)) := rfl

end prod

end local_equiv

namespace equiv
/- equivs give rise to local_equiv. We set up simp lemmas to reduce most properties of the local
equiv to that of the equiv. -/
variables (e : equiv α β) (e' : equiv β γ)

@[simp] lemma to_local_equiv_to_fun (x : α) : e.to_local_equiv.to_fun = e.to_fun := rfl
@[simp] lemma to_local_equiv_inv_fun (x : α) : e.to_local_equiv.inv_fun = e.inv_fun := rfl
@[simp] lemma to_local_equiv_source : e.to_local_equiv.source = univ := rfl
@[simp] lemma to_local_equiv_target : e.to_local_equiv.target = univ := rfl
@[simp] lemma refl_to_local_equiv : (equiv.refl α).to_local_equiv = local_equiv.refl α := rfl
@[simp] lemma symm_to_local_equiv : e.symm.to_local_equiv = e.to_local_equiv.symm := rfl
@[simp] lemma trans_to_local_equiv :
  (e.trans e').to_local_equiv = e.to_local_equiv.trans e'.to_local_equiv :=
local_equiv.eq _ _ (λx, rfl) (λx, rfl) (by simp [local_equiv.trans_source, equiv.to_local_equiv])

end equiv
