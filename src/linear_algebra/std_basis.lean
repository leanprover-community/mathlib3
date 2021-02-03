/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import linear_algebra.basic

/-!
# The standard basis

This file defines the standard basis `std_basis R φ i b j`, which is `b` where `i = j` and `0`
elsewhere.

To give a concrete example, `std_basis R (λ (i : fin 3), R) i 1` gives the `i`th unit basis vector
in `R³`, and `pi.is_basis_fun` proves this is a basis over `fin 3 → R`.
-/

namespace linear_map
open function submodule
open_locale big_operators

variables (R : Type*) {ι : Type*} [semiring R] (φ : ι → Type*)
  [Π i, add_comm_monoid (φ i)] [Π i, semimodule R (φ i)] [decidable_eq ι]

/-- The standard basis of the product of `φ`. -/
def std_basis (i : ι) : φ i →ₗ[R] (Πi, φ i) := pi (diag i)

lemma std_basis_apply (i : ι) (b : φ i) : std_basis R φ i b = update 0 i b :=
by ext j; rw [std_basis, pi_apply, diag, update_apply]; refl

@[simp] lemma std_basis_same (i : ι) (b : φ i) : std_basis R φ i b i = b :=
by rw [std_basis_apply, update_same]

lemma std_basis_ne (i j : ι) (h : j ≠ i) (b : φ i) : std_basis R φ i b j = 0 :=
by rw [std_basis_apply, update_noteq h]; refl

lemma ker_std_basis (i : ι) : ker (std_basis R φ i) = ⊥ :=
ker_eq_bot_of_injective $ assume f g hfg,
  have std_basis R φ i f i = std_basis R φ i g i := hfg ▸ rfl,
  by simpa only [std_basis_same]

lemma proj_comp_std_basis (i j : ι) : (proj i).comp (std_basis R φ j) = diag j i :=
by rw [std_basis, proj_pi]

lemma proj_std_basis_same (i : ι) : (proj i).comp (std_basis R φ i) = id :=
by ext b; simp

lemma proj_std_basis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (std_basis R φ j) = 0 :=
by ext b; simp [std_basis_ne R φ _ _ h]

lemma supr_range_std_basis_le_infi_ker_proj (I J : set ι) (h : disjoint I J) :
  (⨆i∈I, range (std_basis R φ i)) ≤ (⨅i∈J, ker (proj i)) :=
begin
  refine (supr_le $ assume i, supr_le $ assume hi, range_le_iff_comap.2 _),
  simp only [(ker_comp _ _).symm, eq_top_iff, le_def', mem_ker, comap_infi, mem_infi],
  assume b hb j hj,
  have : i ≠ j := assume eq, h ⟨hi, eq.symm ▸ hj⟩,
  rw [proj_std_basis_ne R φ j i this.symm, zero_apply]
end

lemma infi_ker_proj_le_supr_range_std_basis {I : finset ι} {J : set ι} (hu : set.univ ⊆ ↑I ∪ J) :
  (⨅ i∈J, ker (proj i)) ≤ (⨆i∈I, range (std_basis R φ i)) :=
submodule.le_def'.2
begin
  assume b hb,
  simp only [mem_infi, mem_ker, proj_apply] at hb,
  rw ← show ∑ i in I, std_basis R φ i (b i) = b,
  { ext i,
    rw [finset.sum_apply, ← std_basis_same R φ i (b i)],
    refine finset.sum_eq_single i (assume j hjI ne, std_basis_ne _ _ _ _ ne.symm _) _,
    assume hiI,
    rw [std_basis_same],
    exact hb _ ((hu trivial).resolve_left hiI) },
  exact sum_mem _ (assume i hiI, mem_supr_of_mem i $ mem_supr_of_mem hiI $
    (std_basis R φ i).mem_range_self (b i))
end

lemma supr_range_std_basis_eq_infi_ker_proj {I J : set ι}
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) (hI : set.finite I) :
  (⨆i∈I, range (std_basis R φ i)) = (⨅i∈J, ker (proj i)) :=
begin
  refine le_antisymm (supr_range_std_basis_le_infi_ker_proj _ _ _ _ hd) _,
  have : set.univ ⊆ ↑hI.to_finset ∪ J, { rwa [hI.coe_to_finset] },
  refine le_trans (infi_ker_proj_le_supr_range_std_basis R φ this) (supr_le_supr $ assume i, _),
  rw [set.finite.mem_to_finset],
  exact le_refl _
end

lemma supr_range_std_basis [fintype ι] : (⨆i:ι, range (std_basis R φ i)) = ⊤ :=
have (set.univ : set ι) ⊆ ↑(finset.univ : finset ι) ∪ ∅ := by rw [finset.coe_univ, set.union_empty],
begin
  apply top_unique,
  convert (infi_ker_proj_le_supr_range_std_basis R φ this),
  exact infi_emptyset.symm,
  exact (funext $ λi, (@supr_pos _ _ _ (λh, range (std_basis R φ i)) $ finset.mem_univ i).symm)
end

lemma disjoint_std_basis_std_basis (I J : set ι) (h : disjoint I J) :
  disjoint (⨆i∈I, range (std_basis R φ i)) (⨆i∈J, range (std_basis R φ i)) :=
begin
  refine disjoint.mono
    (supr_range_std_basis_le_infi_ker_proj _ _ _ _ $ disjoint_compl_right)
    (supr_range_std_basis_le_infi_ker_proj _ _ _ _ $ disjoint_compl_right) _,
  simp only [disjoint, submodule.le_def', mem_infi, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff],
  rintros b ⟨hI, hJ⟩ i,
  classical,
  by_cases hiI : i ∈ I,
  { by_cases hiJ : i ∈ J,
    { exact (h ⟨hiI, hiJ⟩).elim },
    { exact hJ i hiJ } },
  { exact hI i hiI }
end

lemma std_basis_eq_single {a : R} :
  (λ (i : ι), (std_basis R (λ _ : ι, R) i) a) = λ (i : ι), (finsupp.single i a) :=
begin
  ext i j,
  rw [std_basis_apply, finsupp.single_apply],
  split_ifs,
  { rw [h, function.update_same] },
  { rw [function.update_noteq (ne.symm h)], refl },
end

end linear_map
