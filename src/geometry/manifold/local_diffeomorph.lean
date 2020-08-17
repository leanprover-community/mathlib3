import .diffeomorph

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

/-- local diffeomorphisms, defined on open subsets of the space -/
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

/-- A diffomorphism induces a local diffeomorphism on the whole space -/
def times_diffeomorph.to_local_times_diffeomorph
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
(n : with_top ℕ)
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
(e : local_times_diffeomorph I I' M M' n) (e' : local_times_diffeomorph J J' N N' n)

instance : has_coe (local_times_diffeomorph I I' M M' n) (local_homeomorph M M') := sorry
instance : has_coe_to_fun (local_times_diffeomorph I I' M M' n) := ⟨_, λ e, e.to_local_equiv.to_fun⟩

/-- The inverse of a local homeomorphism -/
protected def symm : local_times_diffeomorph I' I M' M n :=
{ open_source        := e.open_target,
  open_target        := e.open_source,
  times_cont_mdiff_to_fun   := e.times_cont_mdiff_inv_fun,
  times_cont_mdiff_inv_fun  := e.times_cont_mdiff_to_fun,
  ..e.to_local_equiv.symm }

protected lemma times_cont_mdiff_on : times_cont_mdiff_on I I' n e e.source := e.times_cont_mdiff_to_fun

lemma times_cont_mdiff_on_symm : times_cont_mdiff_on I' I n e.symm e.target := e.times_cont_mdiff_inv_fun

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
diffeomorphism in its normal form, i.e., in terms of its coercion to a function. -/

@[simp, mfld_simps] lemma to_fun_eq_coe (e : local_times_diffeomorph I I' M M' n) : e.to_fun = e := rfl

@[simp, mfld_simps] lemma inv_fun_eq_coe (e : local_times_diffeomorph I I' M M' n) : e.inv_fun = e.symm := rfl

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

lemma eq_of_local_equiv_eq {e e' : local_times_diffeomorph I I' M M' n}
  (h : e.to_local_equiv = e'.to_local_equiv) : e = e' :=
by { cases e, cases e', dsimp only [] at h, induction h, refl }

lemma eventually_left_inverse (e : local_times_diffeomorph I I' M M' n) {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
filter.eventually.mono (mem_nhds_sets e.open_source hx) e.left_inv'

end local_times_diffeomorph
