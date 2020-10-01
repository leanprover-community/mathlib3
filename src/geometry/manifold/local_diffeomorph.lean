/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.diffeomorph

/-!
# Local diffeomorphisms

This file defines diffeomorphisms between open subsets of manifolds. An element `e` of
`local_times_diffeomorph α β` is an extension of `local_equiv α β`, i.e., it is a pair of functions
`e.to_fun` and `e.inv_fun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are smooth on them.
Equivalently, they are diffeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.to_fun x` and `e.inv_fun x`.

## Main definitions

`times_diffeomorph.to_local_times_diffeomorph`: associating a local diffeomorphism to a diffeomorphism,
                                                with source = target = univ
`local_times_diffeomorph.symm`  : the inverse of a local diffeomorphism
`local_times_diffeomorph.trans` : the composition of two local diffeomorphisms
`local_times_diffeomorph.refl`  : the identity local diffeomorphism
-/

open function set
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']

/-- Local diffeomorphisms, defined on open subsets of the manifold -/
@[nolint has_inhabited_instance]
structure local_times_diffeomorph
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
(n : with_top ℕ)
extends local_equiv M M' :=
(open_source                  : is_open source)
(open_target                  : is_open target)
(times_cont_mdiff_to_fun      : times_cont_mdiff_on I I' n to_fun source)
(times_cont_mdiff_inv_fun     : times_cont_mdiff_on I' I n inv_fun target)

@[reducible] def local_diffeomorph (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] :=
local_times_diffeomorph I I' M M' ⊤

/-- A diffomorphism induces a local diffeomorphism on the whole manifold -/
def times_diffeomorph.to_local_times_diffeomorph
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{n : with_top ℕ}
(e : times_diffeomorph I I' M M' n) :
  local_times_diffeomorph I I' M M' n :=
{ open_source        := is_open_univ,
  open_target        := is_open_univ,
  times_cont_mdiff_to_fun  := by { erw times_cont_mdiff_on_univ, exact e.times_cont_mdiff_to_fun },
  times_cont_mdiff_inv_fun := by { erw times_cont_mdiff_on_univ, exact e.times_cont_mdiff_inv_fun },
  ..e.to_equiv.to_local_equiv }

namespace local_times_diffeomorph

variables {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F' G'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{N' : Type*} [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']
{n : with_top ℕ}
(e : local_times_diffeomorph I I' M M' n) (e' : local_times_diffeomorph I' J M' N n)
(f : local_times_diffeomorph I I' M M' ⊤)

def to_local_homeomorph (h : local_times_diffeomorph I I' M M' n) : local_homeomorph M M' :=
{ continuous_to_fun := h.times_cont_mdiff_to_fun.continuous_on,
  continuous_inv_fun :=  h.times_cont_mdiff_inv_fun.continuous_on,
  ..h }

instance : has_coe (local_times_diffeomorph I I' M M' n) (local_homeomorph M M') := ⟨to_local_homeomorph⟩
instance : has_coe_to_fun (local_times_diffeomorph I I' M M' n) := ⟨_, λ e, e.to_local_equiv.to_fun⟩

variables (I M n)

/-- The identity on the whole space as a local diffeomorphism. -/
protected def refl : local_times_diffeomorph I I M M n :=
(times_diffeomorph.refl I M n).to_local_times_diffeomorph

variables {I M n}

/-- The inverse of a local diffeomorphism -/
protected def symm : local_times_diffeomorph I' I M' M n :=
{ open_source        := e.open_target,
  open_target        := e.open_source,
  times_cont_mdiff_to_fun   := e.times_cont_mdiff_inv_fun,
  times_cont_mdiff_inv_fun  := e.times_cont_mdiff_to_fun,
  ..e.to_local_equiv.symm }

protected lemma continuous_on : continuous_on e e.source := e.times_cont_mdiff_to_fun.continuous_on
protected lemma times_cont_mdiff_on : times_cont_mdiff_on I I' n e e.source := e.times_cont_mdiff_to_fun
protected lemma smooth_on : smooth_on I I' f f.source := f.times_cont_mdiff_to_fun

lemma continuous_on_symm : continuous_on e.symm e.target := e.times_cont_mdiff_inv_fun.continuous_on
lemma times_cont_mdiff_on_symm : times_cont_mdiff_on I' I n e.symm e.target :=
  e.times_cont_mdiff_inv_fun
lemma smooth_on_symm : smooth_on I' I f.symm f.target := f.times_cont_mdiff_inv_fun

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
diffeomorphism in its normal form, i.e., in terms of its coercion to a function. -/

@[simp, mfld_simps] lemma to_fun_eq_coe (e : local_times_diffeomorph I I' M M' n) : e.to_fun = e :=
rfl

@[simp, mfld_simps] lemma inv_fun_eq_coe (e : local_times_diffeomorph I I' M M' n) :
  e.inv_fun = e.symm := rfl

@[simp, mfld_simps] lemma coe_coe : (e.to_local_equiv : M → M') = e := rfl

@[simp, mfld_simps] lemma coe_coe_symm : (e.to_local_equiv.symm : M' → M) = e.symm := rfl

@[simp, mfld_simps] lemma map_source {x : M} (h : x ∈ e.source) : e x ∈ e.target :=
e.map_source' h

@[simp, mfld_simps] lemma map_target {x : M'} (h : x ∈ e.target) : e.symm x ∈ e.source :=
e.map_target' h

@[simp, mfld_simps] lemma left_inv {x : M} (h : x ∈ e.source) : e.symm (e x) = x :=
e.left_inv' h

@[simp, mfld_simps] lemma right_inv {x : M'} (h : x ∈ e.target) : e (e.symm x) = x :=
e.right_inv' h

lemma source_preimage_target : e.source ⊆ e ⁻¹' e.target := λ _ h, map_source e h

lemma eq_of_local_equiv_eq {e e' : local_times_diffeomorph I I' M M' n}
  (h : e.to_local_equiv = e'.to_local_equiv) : e = e' :=
by { cases e, cases e', dsimp only [] at h, induction h, refl }

lemma eventually_left_inverse (e : local_times_diffeomorph I I' M M' n) {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
filter.eventually.mono (mem_nhds_sets e.open_source hx) e.left_inv'

/-- Two local diffeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected lemma ext (e' : local_times_diffeomorph I I' M M' n) (h : ∀x, e x = e' x)
  (hinv : ∀x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
eq_of_local_equiv_eq (local_equiv.ext h hinv hs)

@[simp, mfld_simps] lemma refl_local_equiv :
  (local_times_diffeomorph.refl I M n).to_local_equiv = local_equiv.refl M := rfl
lemma refl_source : (local_times_diffeomorph.refl I M n).source = univ := rfl
lemma refl_target : (local_times_diffeomorph.refl I M n).target = univ := rfl
@[simp, mfld_simps] lemma refl_symm :
  (local_times_diffeomorph.refl I M n).symm = local_times_diffeomorph.refl I M n := rfl
@[simp, mfld_simps] lemma refl_coe : (local_times_diffeomorph.refl I M n : M → M) = id := rfl

@[simp, mfld_simps] lemma symm_to_local_equiv : e.symm.to_local_equiv = e.to_local_equiv.symm := rfl
-- The following lemmas are already simp via local_equiv
lemma symm_source : e.symm.source = e.target := rfl
lemma symm_target : e.symm.target = e.source := rfl
@[simp, mfld_simps] lemma symm_symm : e.symm.symm = e := eq_of_local_equiv_eq $ by simp

/-- Restricting a local diffeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restr_open (s : set M) (hs : is_open s) :
  local_times_diffeomorph I I' M M' n :=
{ times_cont_mdiff_to_fun  := e.times_cont_mdiff_to_fun.mono (inter_subset_left _ _),
  times_cont_mdiff_inv_fun := e.times_cont_mdiff_inv_fun.mono (inter_subset_left _ _),
  ..e.to_local_homeomorph.restr_open s hs }

@[simp, mfld_simps] lemma restr_open_to_local_equiv (s : set M) (hs : is_open s) :
  (e.restr_open s hs).to_local_equiv = e.to_local_equiv.restr s := rfl

-- Already simp via local_equiv
lemma restr_open_source (s : set M) (hs : is_open s) :
  (e.restr_open s hs).source = e.source ∩ s := rfl

/-- Composition of two local diffeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.target = e'.source) : local_times_diffeomorph I J M N n :=
{ open_source       := e.open_source,
  open_target       := e'.open_target,
  times_cont_mdiff_to_fun := begin
    apply e'.times_cont_mdiff_to_fun.comp e.times_cont_mdiff_to_fun,
    rw ← h,
    exact e.to_local_equiv.source_subset_preimage_target
  end,
  times_cont_mdiff_inv_fun := begin
    apply e.times_cont_mdiff_inv_fun.comp e'.times_cont_mdiff_inv_fun,
    rw h,
    exact e'.to_local_equiv.target_subset_preimage_source
  end,
  ..local_equiv.trans' e.to_local_equiv e'.to_local_equiv h }

/-- Composing two local diffeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : local_times_diffeomorph I J M N n :=
local_times_diffeomorph.trans' (e.symm.restr_open e'.source e'.open_source).symm
  (e'.restr_open e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps] lemma trans_to_local_equiv :
  (e.trans e').to_local_equiv = e.to_local_equiv.trans e'.to_local_equiv := rfl
@[simp, mfld_simps] lemma coe_trans : (e.trans e' : M → N) = e' ∘ e := rfl
@[simp, mfld_simps] lemma coe_trans_symm : ((e.trans e').symm : N → M) = e.symm ∘ e'.symm := rfl

lemma trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm :=
by cases e; cases e'; refl

end local_times_diffeomorph
