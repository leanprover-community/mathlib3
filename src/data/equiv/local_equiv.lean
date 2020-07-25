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

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.to_fun x` and `e.inv_fun y`.

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
tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
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

mk_simp_attribute mfld_simps "The simpset `mfld_simps` records several simp lemmas that are
especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
readability.

The typical use case is the following, in a file on manifolds:
If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar] with mfld_simps` and paste
its output. The list of lemmas should be reasonable (contrary to the output of
`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
enough.
"

-- register in the simpset `mfld_simps` several lemmas that are often useful when dealing
-- with manifolds
attribute [mfld_simps] id.def function.comp.left_id set.mem_set_of_eq set.image_eq_empty
set.univ_inter set.preimage_univ set.prod_mk_mem_set_prod_eq and_true set.mem_univ
set.mem_image_of_mem true_and set.mem_inter_eq set.mem_preimage function.comp_app
set.inter_subset_left set.mem_prod set.range_id and_self set.mem_range_self
eq_self_iff_true forall_const forall_true_iff set.inter_univ set.preimage_id function.comp.right_id
not_false_iff and_imp set.prod_inter_prod set.univ_prod_univ true_or or_true

namespace tactic.interactive

/-- A very basic tactic to show that sets showing up in manifolds coincide or are included in
one another. -/
meta def mfld_set_tac : tactic unit := do
  goal ← tactic.target,
  match goal with
  | `(%%e₁ = %%e₂) :=
      `[ext my_y,
        split;
        { assume h_my_y,
          try { simp only [*, -h_my_y] with mfld_simps at h_my_y },
          simp only [*] with mfld_simps }]
  | `(%%e₁ ⊆ %%e₂) :=
      `[assume my_y h_my_y,
        try { simp only [*, -h_my_y] with mfld_simps at h_my_y },
        simp only [*] with mfld_simps]
  | _ := tactic.fail "goal should be an equality or an inclusion"
  end

end tactic.interactive

open function set

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- Local equivalence between subsets `source` and `target` of α and β respectively. The (global)
maps `to_fun : α → β` and `inv_fun : β → α` map `source` to `target` and conversely, and are inverse
to each other there. The values of `to_fun` outside of `source` and of `inv_fun` outside of `target`
are irrelevant. -/
@[nolint has_inhabited_instance]
structure local_equiv (α : Type*) (β : Type*) :=
(to_fun      : α → β)
(inv_fun     : β → α)
(source      : set α)
(target      : set β)
(map_source' : ∀{x}, x ∈ source → to_fun x ∈ target)
(map_target' : ∀{x}, x ∈ target → inv_fun x ∈ source)
(left_inv'   : ∀{x}, x ∈ source → inv_fun (to_fun x) = x)
(right_inv'  : ∀{x}, x ∈ target → to_fun (inv_fun x) = x)

/-- Associating a local_equiv to an equiv-/
def equiv.to_local_equiv (e : equiv α β) : local_equiv α β :=
{ to_fun      := e.to_fun,
  inv_fun     := e.inv_fun,
  source      := univ,
  target      := univ,
  map_source' := λx hx, mem_univ _,
  map_target' := λy hy, mem_univ _,
  left_inv'   := λx hx, e.left_inv x,
  right_inv'  := λx hx, e.right_inv x }

namespace local_equiv

variables (e : local_equiv α β) (e' : local_equiv β γ)

/-- The inverse of a local equiv -/
protected def symm : local_equiv β α :=
{ to_fun     := e.inv_fun,
  inv_fun    := e.to_fun,
  source     := e.target,
  target     := e.source,
  map_source' := e.map_target',
  map_target' := e.map_source',
  left_inv'   := e.right_inv',
  right_inv'  := e.left_inv' }

instance : has_coe_to_fun (local_equiv α β) := ⟨_, local_equiv.to_fun⟩

@[simp, mfld_simps] theorem coe_mk (f : α → β) (g s t ml mr il ir) :
  (local_equiv.mk f g s t ml mr il ir : α → β) = f := rfl

@[simp, mfld_simps] theorem coe_symm_mk (f : α → β) (g s t ml mr il ir) :
  ((local_equiv.mk f g s t ml mr il ir).symm : β → α) = g := rfl

@[simp, mfld_simps] lemma to_fun_as_coe : e.to_fun = e := rfl

@[simp, mfld_simps] lemma inv_fun_as_coe : e.inv_fun = e.symm := rfl

@[simp, mfld_simps] lemma map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
e.map_source' h

protected lemma maps_to : maps_to e e.source e.target := λ _, e.map_source

@[simp, mfld_simps] lemma map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
e.map_target' h

lemma symm_maps_to : maps_to e.symm e.target e.source := e.symm.maps_to

@[simp, mfld_simps] lemma left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
e.left_inv' h

protected lemma left_inv_on : left_inv_on e.symm e e.source := λ _, e.left_inv

@[simp, mfld_simps] lemma right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
e.right_inv' h

protected lemma right_inv_on : right_inv_on e.symm e e.target := λ _, e.right_inv

/-- Associating to a local_equiv an equiv between the source and the target -/
protected def to_equiv : equiv (e.source) (e.target) :=
{ to_fun    := λ x, ⟨e x, e.map_source x.mem⟩,
  inv_fun   := λ y, ⟨e.symm y, e.map_target y.mem⟩,
  left_inv  := λ⟨x, hx⟩, subtype.eq $ e.left_inv hx,
  right_inv := λ⟨y, hy⟩, subtype.eq $ e.right_inv hy }

@[simp, mfld_simps] lemma symm_source : e.symm.source = e.target := rfl
@[simp, mfld_simps] lemma symm_target : e.symm.target = e.source := rfl
@[simp, mfld_simps] lemma symm_symm : e.symm.symm = e := by { cases e, refl }

/-- A local equiv induces a bijection between its source and target -/
lemma bij_on_source : bij_on e e.source e.target :=
inv_on.bij_on ⟨e.left_inv_on, e.right_inv_on⟩ e.maps_to e.symm_maps_to

lemma image_eq_target_inter_inv_preimage {s : set α} (h : s ⊆ e.source) :
  e '' s = e.target ∩ e.symm ⁻¹' s :=
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

lemma image_inter_source_eq (s : set α) :
  e '' (s ∩ e.source) = e.target ∩ e.symm ⁻¹' (s ∩ e.source) :=
e.image_eq_target_inter_inv_preimage (inter_subset_right _ _)

lemma image_inter_source_eq' (s : set α) :
  e '' (s ∩ e.source) = e.target ∩ e.symm ⁻¹' s :=
begin
  rw e.image_eq_target_inter_inv_preimage (inter_subset_right _ _),
  ext x, split; { assume hx, simp at hx, simp [hx] }
end

lemma symm_image_eq_source_inter_preimage {s : set β} (h : s ⊆ e.target) :
  e.symm '' s = e.source ∩ e ⁻¹' s :=
e.symm.image_eq_target_inter_inv_preimage h

lemma symm_image_inter_target_eq (s : set β) :
  e.symm '' (s ∩ e.target) = e.source ∩ e ⁻¹' (s ∩ e.target) :=
e.symm.image_inter_source_eq _

lemma symm_image_inter_target_eq' (s : set β) :
  e.symm '' (s ∩ e.target) = e.source ∩ e ⁻¹' s :=
e.symm.image_inter_source_eq' _

lemma source_inter_preimage_inv_preimage (s : set α) :
  e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
begin
  ext x, split,
  { rintros ⟨hx, xs⟩,
    simp only [mem_preimage, hx, e.left_inv, mem_preimage] at xs,
    exact ⟨hx, xs⟩ },
  { rintros ⟨hx, xs⟩,
    simp [hx, xs] }
end

lemma target_inter_inv_preimage_preimage (s : set β) :
  e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
e.symm.source_inter_preimage_inv_preimage _

lemma image_source_eq_target : e '' e.source = e.target :=
e.bij_on_source.image_eq

lemma source_subset_preimage_target : e.source ⊆ e ⁻¹' e.target :=
λx hx, e.map_source hx

lemma inv_image_target_eq_source : e.symm '' e.target = e.source :=
e.symm.bij_on_source.image_eq

lemma target_subset_preimage_source : e.target ⊆ e.symm ⁻¹' e.source :=
λx hx, e.map_target hx

/-- Two local equivs that have the same `source`, same `to_fun` and same `inv_fun`, coincide. -/
@[ext]
protected lemma ext {e e' : local_equiv α β} (h : ∀x, e x = e' x)
  (hsymm : ∀x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
begin
  have A : (e : α → β) = e', by { ext x, exact h x },
  have B : (e.symm : β → α) = e'.symm, by { ext x, exact hsymm x },
  have I : e '' e.source = e.target := e.image_source_eq_target,
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target,
  rw [A, hs, I'] at I,
  cases e; cases e',
  simp * at *
end

/-- Restricting a local equivalence to e.source ∩ s -/
protected def restr (s : set α) : local_equiv α β :=
{ to_fun  := e,
  inv_fun := e.symm,
  source  := e.source ∩ s,
  target  := e.target ∩ e.symm⁻¹' s,
  map_source'  := λx hx, begin
    simp only with mfld_simps at hx,
    simp only [hx] with mfld_simps,
  end,
  map_target' := λy hy, begin
    simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps,
  end,
  left_inv'  := λx hx, e.left_inv hx.1,
  right_inv' := λy hy, e.right_inv hy.1 }

@[simp, mfld_simps] lemma restr_coe (s : set α) : (e.restr s : α → β) = e := rfl
@[simp, mfld_simps] lemma restr_coe_symm (s : set α) : ((e.restr s).symm : β → α) = e.symm := rfl
@[simp, mfld_simps] lemma restr_source (s : set α) : (e.restr s).source = e.source ∩ s := rfl
@[simp, mfld_simps] lemma restr_target (s : set α) : (e.restr s).target = e.target ∩ e.symm ⁻¹' s := rfl

lemma restr_eq_of_source_subset {e : local_equiv α β} {s : set α} (h : e.source ⊆ s) :
  e.restr s = e :=
local_equiv.ext (λ_, rfl) (λ_, rfl) (by simp [inter_eq_self_of_subset_left h])

@[simp, mfld_simps] lemma restr_univ {e : local_equiv α β} : e.restr univ = e :=
restr_eq_of_source_subset (subset_univ _)

/-- The identity local equiv -/
protected def refl (α : Type*) : local_equiv α α := (equiv.refl α).to_local_equiv

@[simp, mfld_simps] lemma refl_source : (local_equiv.refl α).source = univ := rfl
@[simp, mfld_simps] lemma refl_target : (local_equiv.refl α).target = univ := rfl
@[simp, mfld_simps] lemma refl_coe : (local_equiv.refl α : α → α) = id := rfl
@[simp, mfld_simps] lemma refl_symm : (local_equiv.refl α).symm = local_equiv.refl α := rfl

@[simp, mfld_simps] lemma refl_restr_source (s : set α) : ((local_equiv.refl α).restr s).source = s :=
by simp

@[simp, mfld_simps] lemma refl_restr_target (s : set α) : ((local_equiv.refl α).restr s).target = s :=
by { change univ ∩ id⁻¹' s = s, simp }

/-- The identity local equiv on a set `s` -/
def of_set (s : set α) : local_equiv α α :=
{ to_fun      := id,
  inv_fun     := id,
  source      := s,
  target      := s,
  map_source' := λx hx, hx,
  map_target' := λx hx, hx,
  left_inv'   := λx hx, rfl,
  right_inv'  := λx hx, rfl }

@[simp, mfld_simps] lemma of_set_source (s : set α) : (local_equiv.of_set s).source = s := rfl
@[simp, mfld_simps] lemma of_set_target (s : set α) : (local_equiv.of_set s).target = s := rfl
@[simp, mfld_simps] lemma of_set_coe (s : set α) : (local_equiv.of_set s : α → α) = id := rfl
@[simp, mfld_simps] lemma of_set_symm (s : set α) : (local_equiv.of_set s).symm = local_equiv.of_set s := rfl

/-- Composing two local equivs if the target of the first coincides with the source of the
second. -/
protected def trans' (e' : local_equiv β γ) (h : e.target = e'.source) :
  local_equiv α γ :=
{ to_fun := e' ∘ e,
  inv_fun := e.symm ∘ e'.symm,
  source := e.source,
  target := e'.target,
  map_source' := λx hx, by simp [h.symm, hx],
  map_target' := λy hy, by simp [h, hy],
  left_inv' := λx hx, by simp [hx, h.symm],
  right_inv' := λy hy, by simp [hy, h] }

/-- Composing two local equivs, by restricting to the maximal domain where their composition
is well defined. -/
protected def trans : local_equiv α γ :=
  local_equiv.trans' (e.symm.restr (e'.source)).symm (e'.restr (e.target)) (inter_comm _ _)

@[simp, mfld_simps] lemma coe_trans : (e.trans e' : α → γ) = e' ∘ e := rfl
@[simp, mfld_simps] lemma coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm := rfl

lemma trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm :=
by cases e; cases e'; refl

@[simp, mfld_simps] lemma trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source := rfl

lemma trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
by mfld_set_tac

lemma trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
by rw [e.trans_source', inter_comm e.target, e.symm_image_inter_target_eq]

lemma image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
image_source_eq_target (local_equiv.symm (local_equiv.restr (local_equiv.symm e) (e'.source)))

@[simp, mfld_simps] lemma trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target := rfl

lemma trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
trans_source' e'.symm e.symm

lemma trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
trans_source'' e'.symm e.symm

lemma inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
image_trans_source e'.symm e.symm

lemma trans_assoc (e'' : local_equiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
local_equiv.ext (λx, rfl) (λx, rfl) (by simp [trans_source, @preimage_comp α β γ, inter_assoc])

@[simp, mfld_simps] lemma trans_refl : e.trans (local_equiv.refl β) = e :=
local_equiv.ext (λx, rfl) (λx, rfl) (by simp [trans_source])

@[simp, mfld_simps] lemma refl_trans : (local_equiv.refl α).trans e = e :=
local_equiv.ext (λx, rfl) (λx, rfl) (by simp [trans_source, preimage_id])

lemma trans_refl_restr (s : set β) :
  e.trans ((local_equiv.refl β).restr s) = e.restr (e ⁻¹' s) :=
local_equiv.ext (λx, rfl) (λx, rfl) (by simp [trans_source])

lemma trans_refl_restr' (s : set β) :
  e.trans ((local_equiv.refl β).restr s) = e.restr (e.source ∩ e ⁻¹' s) :=
local_equiv.ext (λx, rfl) (λx, rfl) $ by { simp [trans_source], rw [← inter_assoc, inter_self] }

lemma restr_trans (s : set α) :
  (e.restr s).trans e' = (e.trans e').restr s :=
local_equiv.ext (λx, rfl) (λx, rfl) $ by { simp [trans_source, inter_comm], rwa inter_assoc }

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same local equiv. -/
def eq_on_source (e e' : local_equiv α β) : Prop :=
e.source = e'.source ∧ (e.source.eq_on e e')

/-- `eq_on_source` is an equivalence relation -/
instance eq_on_source_setoid : setoid (local_equiv α β) :=
{ r     := eq_on_source,
  iseqv := ⟨
    λe, by simp [eq_on_source],
    λe e' h, by { simp [eq_on_source, h.1.symm], exact λx hx, (h.2 hx).symm },
    λe e' e'' h h', ⟨by rwa [← h'.1, ← h.1], λx hx, by { rw [← h'.2, h.2 hx], rwa ← h.1 }⟩⟩ }

lemma eq_on_source_refl : e ≈ e := setoid.refl _

/-- Two equivalent local equivs have the same source -/
lemma eq_on_source.source_eq {e e' : local_equiv α β} (h : e ≈ e') : e.source = e'.source :=
h.1

/-- Two equivalent local equivs coincide on the source -/
lemma eq_on_source.eq_on {e e' : local_equiv α β} (h : e ≈ e') : e.source.eq_on e e' :=
h.2

/-- Two equivalent local equivs have the same target -/
lemma eq_on_source.target_eq {e e' : local_equiv α β} (h : e ≈ e') : e.target = e'.target :=
by simp only [← image_source_eq_target, ← h.source_eq, h.2.image_eq]

/-- If two local equivs are equivalent, so are their inverses. -/
lemma eq_on_source.symm' {e e' : local_equiv α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
begin
  refine ⟨h.target_eq, eq_on_of_left_inv_on_of_right_inv_on e.left_inv_on _ _⟩;
    simp only [symm_source, h.target_eq, h.source_eq, e'.symm_maps_to],
  exact e'.right_inv_on.congr_right e'.symm_maps_to (h.source_eq ▸ h.eq_on.symm),
end

/-- Two equivalent local equivs have coinciding inverses on the target -/
lemma eq_on_source.symm_eq_on {e e' : local_equiv α β} (h : e ≈ e') :
  eq_on e.symm e'.symm e.target :=
h.symm'.eq_on

/-- Composition of local equivs respects equivalence -/
lemma eq_on_source.trans' {e e' : local_equiv α β} {f f' : local_equiv β γ}
  (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
begin
  split,
  { rw [trans_source'', trans_source'', ← he.target_eq, ← hf.1],
    exact (he.symm'.eq_on.mono $ inter_subset_left _ _).image_eq },
  { assume x hx,
    rw trans_source at hx,
    simp [(he.2 hx.1).symm, hf.2 hx.2] }
end

/-- Restriction of local equivs respects equivalence -/
lemma eq_on_source.restr {e e' : local_equiv α β} (he : e ≈ e') (s : set α) :
  e.restr s ≈ e'.restr s :=
begin
  split,
  { simp [he.1] },
  { assume x hx,
    simp only [mem_inter_eq, restr_source] at hx,
    exact he.2 hx.1 }
end

/-- Preimages are respected by equivalence -/
lemma eq_on_source.source_inter_preimage_eq {e e' : local_equiv α β} (he : e ≈ e') (s : set β) :
  e.source ∩ e ⁻¹' s = e'.source ∩ e' ⁻¹' s :=
begin
  ext x,
  simp only [mem_inter_eq, mem_preimage],
  split,
  { assume hx,
    rwa [← he.2 hx.1, ← he.source_eq] },
  { assume hx,
    rwa [← (setoid.symm he).2 hx.1, he.source_eq] }
end

/-- Composition of a local equiv and its inverse is equivalent to the restriction of the identity
to the source -/
lemma trans_self_symm :
  e.trans e.symm ≈ local_equiv.of_set e.source :=
begin
  have A : (e.trans e.symm).source = e.source, by mfld_set_tac,
  refine ⟨by simp [A], λx hx, _⟩,
  rw A at hx,
  simp only [hx] with mfld_simps
end

/-- Composition of the inverse of a local equiv and this local equiv is equivalent to the
restriction of the identity to the target -/
lemma trans_symm_self :
  e.symm.trans e ≈ local_equiv.of_set e.target :=
trans_self_symm (e.symm)

/-- Two equivalent local equivs are equal when the source and target are univ -/
lemma eq_of_eq_on_source_univ (e e' : local_equiv α β) (h : e ≈ e')
  (s : e.source = univ) (t : e.target = univ) : e = e' :=
begin
  apply local_equiv.ext (λx, _) (λx, _) h.1,
  { apply h.2,
    rw s,
    exact mem_univ _ },
  { apply h.symm'.2,
    rw [symm_source, t],
    exact mem_univ _ }
end

section prod

/-- The product of two local equivs, as a local equiv on the product. -/
def prod (e : local_equiv α β) (e' : local_equiv γ δ) : local_equiv (α × γ) (β × δ) :=
{ source := set.prod e.source e'.source,
  target := set.prod e.target e'.target,
  to_fun := λp, (e p.1, e' p.2),
  inv_fun := λp, (e.symm p.1, e'.symm p.2),
  map_source' := λp hp, by { simp at hp, simp [hp] },
  map_target' := λp hp, by { simp at hp, simp [map_target, hp] },
  left_inv'   := λp hp, by { simp at hp, simp [hp] },
  right_inv'  := λp hp, by { simp at hp, simp [hp] } }

@[simp, mfld_simps] lemma prod_source (e : local_equiv α β) (e' : local_equiv γ δ) :
  (e.prod e').source = set.prod e.source e'.source := rfl

@[simp, mfld_simps] lemma prod_target (e : local_equiv α β) (e' : local_equiv γ δ) :
  (e.prod e').target = set.prod e.target e'.target := rfl

@[simp, mfld_simps] lemma prod_coe (e : local_equiv α β) (e' : local_equiv γ δ) :
  ((e.prod e') : α × γ → β × δ) = (λp, (e p.1, e' p.2)) := rfl

lemma prod_coe_symm (e : local_equiv α β) (e' : local_equiv γ δ) :
  ((e.prod e').symm : β × δ → α × γ) = (λp, (e.symm p.1, e'.symm p.2)) := rfl

@[simp, mfld_simps] lemma prod_symm (e : local_equiv α β) (e' : local_equiv γ δ) :
  (e.prod e').symm = (e.symm.prod e'.symm) :=
by ext x; simp [prod_coe_symm]

@[simp, mfld_simps] lemma prod_trans {η : Type*} {ε : Type*}
  (e : local_equiv α β) (f : local_equiv β γ) (e' : local_equiv δ η) (f' : local_equiv η ε) :
  (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
by ext x; simp [ext_iff]; tauto

end prod

end local_equiv

namespace set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : set α` and `t : set β` provides a local equivalence
between `α` and `β`. -/
@[simps] noncomputable def bij_on.to_local_equiv [nonempty α] (f : α → β) (s : set α) (t : set β)
  (hf : bij_on f s t) :
  local_equiv α β :=
{ to_fun := f,
  inv_fun := inv_fun_on f s,
  source := s,
  target := t,
  map_source' := hf.maps_to,
  map_target' := hf.surj_on.maps_to_inv_fun_on,
  left_inv'   := hf.inv_on_inv_fun_on.1,
  right_inv'  := hf.inv_on_inv_fun_on.2 }

/-- A map injective on a subset of its domain provides a local equivalence. -/
@[simp, mfld_simps] noncomputable def inj_on.to_local_equiv [nonempty α] (f : α → β) (s : set α)
  (hf : inj_on f s) :
  local_equiv α β :=
hf.bij_on_image.to_local_equiv f s (f '' s)

end set

namespace equiv
/- equivs give rise to local_equiv. We set up simp lemmas to reduce most properties of the local
equiv to that of the equiv. -/
variables (e : equiv α β) (e' : equiv β γ)

@[simp, mfld_simps] lemma to_local_equiv_coe : (e.to_local_equiv : α → β) = e := rfl
@[simp, mfld_simps] lemma to_local_equiv_symm_coe : (e.to_local_equiv.symm : β → α) = e.symm := rfl
@[simp, mfld_simps] lemma to_local_equiv_source : e.to_local_equiv.source = univ := rfl
@[simp, mfld_simps] lemma to_local_equiv_target : e.to_local_equiv.target = univ := rfl
@[simp, mfld_simps] lemma refl_to_local_equiv : (equiv.refl α).to_local_equiv = local_equiv.refl α := rfl
@[simp, mfld_simps] lemma symm_to_local_equiv : e.symm.to_local_equiv = e.to_local_equiv.symm := rfl
@[simp, mfld_simps] lemma trans_to_local_equiv :
  (e.trans e').to_local_equiv = e.to_local_equiv.trans e'.to_local_equiv :=
local_equiv.ext (λx, rfl) (λx, rfl) (by simp [local_equiv.trans_source, equiv.to_local_equiv])

end equiv
