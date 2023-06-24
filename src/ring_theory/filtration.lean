/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.ideal.local_ring
import ring_theory.noetherian
import ring_theory.rees_algebra
import ring_theory.finiteness
import data.polynomial.module
import order.hom.lattice

/-!

# `I`-filtrations of modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definitions and basic results around (stable) `I`-filtrations of modules.

## Main results

- `ideal.filtration`: An `I`-filtration on the module `M` is a sequence of decreasing submodules
  `N i` such that `I • N ≤ I (i + 1)`. Note that we do not require the filtration to start from `⊤`.
- `ideal.filtration.stable`: An `I`-filtration is stable if `I • (N i) = N (i + 1)` for large
  enough `i`.
- `ideal.filtration.submodule`: The associated module `⨁ Nᵢ` of a filtration, implemented as a
  submodule of `M[X]`.
- `ideal.filtration.submodule_fg_iff_stable`: If `F.N i` are all finitely generated, then
  `F.stable` iff `F.submodule.fg`.
- `ideal.filtration.stable.of_le`: In a finite module over a noetherian ring,
  if `F' ≤ F`, then `F.stable → F'.stable`.
- `ideal.exists_pow_inf_eq_pow_smul`: **Artin-Rees lemma**.
  given `N ≤ M`, there exists a `k` such that `IⁿM ⊓ N = Iⁿ⁻ᵏ(IᵏM ⊓ N)` for all `n ≥ k`.
- `ideal.infi_pow_eq_bot_of_local_ring`:
  **Krull's intersection theorem** (`⨅ i, I ^ i = ⊥`) for noetherian local rings.
- `ideal.infi_pow_eq_bot_of_is_domain`:
  **Krull's intersection theorem** (`⨅ i, I ^ i = ⊥`) for noetherian domains.

-/


universes u v

variables {R M : Type u} [comm_ring R] [add_comm_group M] [module R M] (I : ideal R)

open polynomial
open_locale polynomial big_operators

/-- An `I`-filtration on the module `M` is a sequence of decreasing submodules `N i` such that
`I • (N i) ≤ N (i + 1)`. Note that we do not require the filtration to start from `⊤`. -/
@[ext]
structure ideal.filtration (M : Type u) [add_comm_group M] [module R M] :=
(N : ℕ → submodule R M)
(mono : ∀ i, N (i + 1) ≤ N i)
(smul_le : ∀ i, I • N i ≤ N (i + 1))

variables (F F' : I.filtration M) {I}

namespace ideal.filtration

lemma pow_smul_le (i j : ℕ) : I ^ i • F.N j ≤ F.N (i + j) :=
begin
  induction i,
  { simp },
  { rw [pow_succ, mul_smul, nat.succ_eq_add_one, add_assoc, add_comm 1, ← add_assoc],
    exact (submodule.smul_mono_right i_ih).trans (F.smul_le _) }
end

lemma pow_smul_le_pow_smul (i j k : ℕ) : I ^ (i + k) • F.N j ≤ I ^ k • F.N (i + j) :=
by { rw [add_comm, pow_add, mul_smul], exact submodule.smul_mono_right (F.pow_smul_le i j) }

protected
lemma antitone : antitone F.N :=
antitone_nat_of_succ_le F.mono

/-- The trivial `I`-filtration of `N`. -/
@[simps]
def _root_.ideal.trivial_filtration (I : ideal R) (N : submodule R M) : I.filtration M :=
{ N := λ i, N,
  mono := λ i, le_of_eq rfl,
  smul_le := λ i, submodule.smul_le_right }

/-- The `sup` of two `I.filtration`s is an `I.filtration`. -/
instance : has_sup (I.filtration M) :=
⟨λ F F', ⟨F.N ⊔ F'.N, λ i, sup_le_sup (F.mono i) (F'.mono i),
    λ i, (le_of_eq (submodule.smul_sup _ _ _)).trans $ sup_le_sup (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `Sup` of a family of `I.filtration`s is an `I.filtration`. -/
instance : has_Sup (I.filtration M) := ⟨λ S,
{ N := Sup (ideal.filtration.N '' S),
  mono := λ i, begin
    apply Sup_le_Sup_of_forall_exists_le _,
    rintros _ ⟨⟨_, F, hF, rfl⟩, rfl⟩,
    exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩,
  end,
  smul_le := λ i, begin
    rw [Sup_eq_supr', supr_apply, submodule.smul_supr, supr_apply],
    apply supr_mono _,
    rintro ⟨_, F, hF, rfl⟩,
    exact F.smul_le i,
  end }⟩

/-- The `inf` of two `I.filtration`s is an `I.filtration`. -/
instance : has_inf (I.filtration M) :=
⟨λ F F', ⟨F.N ⊓ F'.N, λ i, inf_le_inf (F.mono i) (F'.mono i),
    λ i, (submodule.smul_inf_le _ _ _).trans $ inf_le_inf (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `Inf` of a family of `I.filtration`s is an `I.filtration`. -/
instance : has_Inf (I.filtration M) := ⟨λ S,
{ N := Inf (ideal.filtration.N '' S),
  mono := λ i, begin
    apply Inf_le_Inf_of_forall_exists_le _,
    rintros _ ⟨⟨_, F, hF, rfl⟩, rfl⟩,
    exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩,
  end,
  smul_le := λ i, begin
    rw [Inf_eq_infi', infi_apply, infi_apply],
    refine submodule.smul_infi_le.trans _,
    apply infi_mono _,
    rintro ⟨_, F, hF, rfl⟩,
    exact F.smul_le i,
  end }⟩

instance : has_top (I.filtration M) := ⟨I.trivial_filtration ⊤⟩
instance : has_bot (I.filtration M) := ⟨I.trivial_filtration ⊥⟩

@[simp] lemma sup_N : (F ⊔ F').N = F.N ⊔ F'.N := rfl
@[simp] lemma Sup_N (S : set (I.filtration M)) : (Sup S).N = Sup (ideal.filtration.N '' S) := rfl
@[simp] lemma inf_N : (F ⊓ F').N = F.N ⊓ F'.N := rfl
@[simp] lemma Inf_N (S : set (I.filtration M)) : (Inf S).N = Inf (ideal.filtration.N '' S) := rfl
@[simp] lemma top_N : (⊤ : I.filtration M).N = ⊤ := rfl
@[simp] lemma bot_N : (⊥ : I.filtration M).N = ⊥ := rfl

@[simp] lemma supr_N {ι : Sort*} (f : ι → I.filtration M) : (supr f).N = ⨆ i, (f i).N :=
congr_arg Sup (set.range_comp _ _).symm

@[simp] lemma infi_N {ι : Sort*} (f : ι → I.filtration M) : (infi f).N = ⨅ i, (f i).N :=
congr_arg Inf (set.range_comp _ _).symm

instance : complete_lattice (I.filtration M) :=
function.injective.complete_lattice ideal.filtration.N ideal.filtration.ext
  sup_N inf_N (λ _, Sup_image) (λ _, Inf_image) top_N bot_N

instance : inhabited (I.filtration M) := ⟨⊥⟩

/-- An `I` filtration is stable if `I • F.N n = F.N (n+1)` for large enough `n`. -/
def stable : Prop :=
∃ n₀, ∀ n ≥ n₀, I • F.N n = F.N (n + 1)

/-- The trivial stable `I`-filtration of `N`. -/
@[simps]
def _root_.ideal.stable_filtration (I : ideal R) (N : submodule R M) :
  I.filtration M :=
{ N := λ i, I ^ i • N,
  mono := λ i, by { rw [add_comm, pow_add, mul_smul], exact submodule.smul_le_right },
  smul_le := λ i, by { rw [add_comm, pow_add, mul_smul, pow_one], exact le_refl _ } }

lemma _root_.ideal.stable_filtration_stable (I : ideal R) (N : submodule R M) :
  (I.stable_filtration N).stable :=
by { use 0, intros n _, dsimp, rw [add_comm, pow_add, mul_smul, pow_one] }

variables {F F'} (h : F.stable)

include h

lemma stable.exists_pow_smul_eq :
  ∃ n₀, ∀ k, F.N (n₀ + k) = I ^ k • F.N n₀ :=
begin
  obtain ⟨n₀, hn⟩ := h,
  use n₀,
  intro k,
  induction k,
  { simp },
  { rw [nat.succ_eq_add_one, ← add_assoc, ← hn, k_ih, add_comm, pow_add, mul_smul, pow_one],
    linarith }
end

lemma stable.exists_pow_smul_eq_of_ge :
  ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ :=
begin
  obtain ⟨n₀, hn₀⟩ := h.exists_pow_smul_eq,
  use n₀,
  intros n hn,
  convert hn₀ (n - n₀),
  rw [add_comm, tsub_add_cancel_of_le hn],
end

omit h

lemma stable_iff_exists_pow_smul_eq_of_ge :
  F.stable ↔ ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ :=
begin
  refine ⟨stable.exists_pow_smul_eq_of_ge, λ h, ⟨h.some, λ n hn, _⟩⟩,
  rw [h.some_spec n hn, h.some_spec (n+1) (by linarith), smul_smul, ← pow_succ,
    tsub_add_eq_add_tsub hn],
end

lemma stable.exists_forall_le (h : F.stable) (e : F.N 0 ≤ F'.N 0) :
  ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n :=
begin
  obtain ⟨n₀, hF⟩ := h,
  use n₀,
  intro n,
  induction n with n hn,
  { refine (F.antitone _).trans e, simp },
  { rw [nat.succ_eq_one_add, add_assoc, add_comm, add_comm 1 n, ← hF],
    exact (submodule.smul_mono_right hn).trans (F'.smul_le _),
    simp },
end

lemma stable.bounded_difference (h : F.stable) (h' : F'.stable) (e : F.N 0 = F'.N 0) :
  ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n ∧ F'.N (n + n₀) ≤ F.N n :=
begin
  obtain ⟨n₁, h₁⟩ := h.exists_forall_le (le_of_eq e),
  obtain ⟨n₂, h₂⟩ := h'.exists_forall_le (le_of_eq e.symm),
  use max n₁ n₂,
  intro n,
  refine ⟨(F.antitone _).trans (h₁ n), (F'.antitone _).trans (h₂ n)⟩; simp
end

open polynomial_module

variables (F F')

/-- The `R[IX]`-submodule of `M[X]` associated with an `I`-filtration. -/
protected
def submodule : submodule (rees_algebra I) (polynomial_module R M) :=
{ carrier := { f | ∀ i, f i ∈ F.N i },
  add_mem' := λ f g hf hg i, submodule.add_mem _ (hf i) (hg i),
  zero_mem' := λ i, submodule.zero_mem _,
  smul_mem' := λ r f hf i, begin
    rw [subalgebra.smul_def, polynomial_module.smul_apply],
    apply submodule.sum_mem,
    rintro ⟨j, k⟩ e,
    rw finset.nat.mem_antidiagonal at e,
    subst e,
    exact F.pow_smul_le j k (submodule.smul_mem_smul (r.2 j) (hf k))
  end }

@[simp]
lemma mem_submodule (f : polynomial_module R M) : f ∈ F.submodule ↔ ∀ i, f i ∈ F.N i := iff.rfl

lemma inf_submodule : (F ⊓ F').submodule = F.submodule ⊓ F'.submodule :=
by { ext, exact forall_and_distrib }

variables (I M)

/-- `ideal.filtration.submodule` as an `inf_hom` -/
def submodule_inf_hom :
  inf_hom (I.filtration M) (submodule (rees_algebra I) (polynomial_module R M)) :=
{ to_fun := ideal.filtration.submodule, map_inf' := inf_submodule }

variables {I M}

lemma submodule_closure_single :
  add_submonoid.closure (⋃ i, single R i '' (F.N i : set M)) = F.submodule.to_add_submonoid :=
begin
  apply le_antisymm,
  { rw [add_submonoid.closure_le, set.Union_subset_iff],
    rintro i _ ⟨m, hm, rfl⟩ j,
    rw single_apply,
    split_ifs,
    { rwa ← h },
    { exact (F.N j).zero_mem } },
  { intros f hf,
    rw [← f.sum_single],
    apply add_submonoid.sum_mem _ _,
    rintros c -,
    exact add_submonoid.subset_closure (set.subset_Union _ c $ set.mem_image_of_mem _ (hf c)) }
end

lemma submodule_span_single :
  submodule.span (rees_algebra I) (⋃ i, single R i '' (F.N i : set M)) = F.submodule :=
begin
  rw [← submodule.span_closure, submodule_closure_single],
  simp,
end

lemma submodule_eq_span_le_iff_stable_ge (n₀ : ℕ) :
  F.submodule = submodule.span _ (⋃ i ≤ n₀, single R i '' (F.N i : set M)) ↔
    ∀ n ≥ n₀, I • F.N n = F.N (n + 1) :=
begin
  rw [← submodule_span_single, ← has_le.le.le_iff_eq, submodule.span_le,
    set.Union_subset_iff],
  swap, { exact submodule.span_mono (set.Union₂_subset_Union _ _) },
  split,
  { intros H n hn,
    refine (F.smul_le n).antisymm _,
    intros x hx,
    obtain ⟨l, hl⟩ := (finsupp.mem_span_iff_total _ _ _).mp (H _ ⟨x, hx, rfl⟩),
    replace hl := congr_arg (λ f : ℕ →₀ M, f (n + 1)) hl,
    dsimp only at hl,
    erw finsupp.single_eq_same at hl,
    rw [← hl, finsupp.total_apply, finsupp.sum_apply],
    apply submodule.sum_mem _ _,
    rintros ⟨_, _, ⟨n', rfl⟩, _, ⟨hn', rfl⟩, m, hm, rfl⟩ -,
    dsimp only [subtype.coe_mk],
    rw [subalgebra.smul_def, smul_single_apply, if_pos (show n' ≤ n + 1, by linarith)],
    have e : n' ≤ n := by linarith,
    have := F.pow_smul_le_pow_smul (n - n') n' 1,
    rw [tsub_add_cancel_of_le e, pow_one, add_comm _ 1, ← add_tsub_assoc_of_le e, add_comm] at this,
    exact this (submodule.smul_mem_smul ((l _).2 $ n + 1 - n') hm) },
  { let F' := submodule.span (rees_algebra I) (⋃ i ≤ n₀, single R i '' (F.N i : set M)),
    intros hF i,
    have : ∀ i ≤ n₀, single R i '' (F.N i : set M) ⊆ F' :=
      λ i hi, set.subset.trans (set.subset_Union₂ i hi) submodule.subset_span,
    induction i with j hj,
    { exact this _ (zero_le _) },
    by_cases hj' : j.succ ≤ n₀,
    { exact this _ hj' },
    simp only [not_le, nat.lt_succ_iff] at hj',
    rw [nat.succ_eq_add_one, ← hF _ hj'],
    rintro _ ⟨m, hm, rfl⟩,
    apply submodule.smul_induction_on hm,
    { intros r hr m' hm',
      rw [add_comm, ← monomial_smul_single],
      exact F'.smul_mem ⟨_, rees_algebra.monomial_mem.mpr (by rwa pow_one)⟩
        (hj $ set.mem_image_of_mem _ hm') },
    { intros x y hx hy, rw map_add, exact F'.add_mem hx hy } }
end

/-- If the components of a filtration are finitely generated, then the filtration is stable iff
its associated submodule of is finitely generated.  -/
lemma submodule_fg_iff_stable (hF' : ∀ i, (F.N i).fg) :
  F.submodule.fg ↔ F.stable :=
begin
  classical,
  delta ideal.filtration.stable,
  simp_rw ← F.submodule_eq_span_le_iff_stable_ge,
  split,
  { rintro H,
    apply H.stablizes_of_supr_eq
      ⟨λ n₀, submodule.span _ (⋃ (i : ℕ) (H : i ≤ n₀), single R i '' ↑(F.N i)), _⟩,
    { dsimp,
      rw [← submodule.span_Union, ← submodule_span_single],
      congr' 1,
      ext,
      simp only [set.mem_Union, set.mem_image, set_like.mem_coe, exists_prop],
      split,
      { rintro ⟨-, i, -, e⟩, exact ⟨i, e⟩ },
      { rintro ⟨i, e⟩, exact ⟨i, i, le_refl i, e⟩ } },
    { intros n m e,
      rw [submodule.span_le, set.Union₂_subset_iff],
      intros i hi,
      refine (set.subset.trans _ (set.subset_Union₂ i (hi.trans e : _))).trans
        submodule.subset_span,
      refl } },
  { rintros ⟨n, hn⟩,
    rw hn,
    simp_rw [submodule.span_Union₂, ← finset.mem_range_succ_iff, supr_subtype'],
    apply submodule.fg_supr,
    rintro ⟨i, hi⟩,
    obtain ⟨s, hs⟩ := hF' i,
    have : submodule.span (rees_algebra I) (s.image (lsingle R i) : set (polynomial_module R M))
      = submodule.span _ (single R i '' (F.N i : set M)),
    { rw [finset.coe_image, ← submodule.span_span_of_tower R, ← submodule.map_span, hs], refl },
    rw [subtype.coe_mk, ← this],
    exact ⟨_, rfl⟩ }
end
.
variables {F}

lemma stable.of_le [is_noetherian_ring R] [h : module.finite R M] (hF : F.stable)
  {F' : I.filtration M} (hf : F' ≤ F) : F'.stable :=
begin
  haveI := is_noetherian_of_fg_of_noetherian' h.1,
  rw ← submodule_fg_iff_stable at hF ⊢,
  any_goals { intro i, exact is_noetherian.noetherian _ },
  have := is_noetherian_of_fg_of_noetherian _ hF,
  rw is_noetherian_submodule at this,
  exact this _ (order_hom_class.mono (submodule_inf_hom M I) hf),
end

lemma stable.inter_right [is_noetherian_ring R] [h : module.finite R M] (hF : F.stable) :
  (F ⊓ F').stable :=
hF.of_le inf_le_left

lemma stable.inter_left [is_noetherian_ring R] [h : module.finite R M] (hF : F.stable) :
  (F' ⊓ F).stable :=
hF.of_le inf_le_right

end ideal.filtration

variable (I)

/-- **Artin-Rees lemma** -/
lemma ideal.exists_pow_inf_eq_pow_smul [is_noetherian_ring R] [h : module.finite R M]
  (N : submodule R M) : ∃ k : ℕ, ∀ n ≥ k, I ^ n • ⊤ ⊓ N = I ^ (n - k) • (I ^ k • ⊤ ⊓ N) :=
((I.stable_filtration_stable ⊤).inter_right (I.trivial_filtration N)).exists_pow_smul_eq_of_ge

lemma ideal.mem_infi_smul_pow_eq_bot_iff [is_noetherian_ring R] [hM : module.finite R M] (x : M) :
  x ∈ (⨅ i : ℕ, I ^ i • ⊤ : submodule R M) ↔ ∃ r : I, (r : R) • x = x :=
begin
  let N := (⨅ i : ℕ, I ^ i • ⊤ : submodule R M),
  have hN : ∀ k, (I.stable_filtration ⊤ ⊓ I.trivial_filtration N).N k = N,
  { intro k, exact inf_eq_right.mpr ((infi_le _ k).trans $ le_of_eq $ by simp) },
  split,
  { haveI := is_noetherian_of_fg_of_noetherian' hM.out,
    obtain ⟨r, hr₁, hr₂⟩ := submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N
      (is_noetherian.noetherian N) _,
    { intro H, exact ⟨⟨r, hr₁⟩, hr₂ _ H⟩ },
    obtain ⟨k, hk⟩ := (I.stable_filtration_stable ⊤).inter_right (I.trivial_filtration N),
    have := hk k (le_refl _),
    rw [hN, hN] at this,
    exact le_of_eq this.symm },
  { rintro ⟨r, eq⟩,
    rw submodule.mem_infi,
    intro i,
    induction i with i hi,
    { simp },
    { rw [nat.succ_eq_one_add, pow_add, ← smul_smul, pow_one, ← eq],
      exact submodule.smul_mem_smul r.prop hi } }
end

lemma ideal.infi_pow_smul_eq_bot_of_local_ring [is_noetherian_ring R] [local_ring R]
  [module.finite R M] (h : I ≠ ⊤) :
  (⨅ i : ℕ, I ^ i • ⊤ : submodule R M) = ⊥ :=
begin
  rw eq_bot_iff,
  intros x hx,
  obtain ⟨r, hr⟩ := (I.mem_infi_smul_pow_eq_bot_iff x).mp hx,
  have := local_ring.is_unit_one_sub_self_of_mem_nonunits _ (local_ring.le_maximal_ideal h r.prop),
  apply this.smul_left_cancel.mp,
  swap, { apply_instance },
  simp [sub_smul, hr],
end

/-- **Krull's intersection theorem** for noetherian local rings. -/
lemma ideal.infi_pow_eq_bot_of_local_ring [is_noetherian_ring R] [local_ring R] (h : I ≠ ⊤) :
  (⨅ i : ℕ, I ^ i) = ⊥ :=
begin
  convert I.infi_pow_smul_eq_bot_of_local_ring h,
  ext i,
  rw [smul_eq_mul, ← ideal.one_eq_top, mul_one],
  apply_instance,
end

/-- **Krull's intersection theorem** for noetherian domains. -/
lemma ideal.infi_pow_eq_bot_of_is_domain [is_noetherian_ring R] [is_domain R] (h : I ≠ ⊤) :
  (⨅ i : ℕ, I ^ i) = ⊥ :=
begin
  rw eq_bot_iff,
  intros x hx,
  by_contra hx',
  have := ideal.mem_infi_smul_pow_eq_bot_iff I x,
  simp_rw [smul_eq_mul, ← ideal.one_eq_top, mul_one] at this,
  obtain ⟨r, hr⟩ := this.mp hx,
  have := mul_right_cancel₀ hx' (hr.trans (one_mul x).symm),
  exact I.eq_top_iff_one.not.mp h (this ▸ r.prop),
end
