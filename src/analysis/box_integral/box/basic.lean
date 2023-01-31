/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.intervals.monotone
import topology.algebra.order.monotone_convergence
import topology.metric_space.basic

/-!
# Rectangular boxes in `ℝⁿ`

In this file we define rectangular boxes in `ℝⁿ`. As usual, we represent `ℝⁿ` as the type of
functions `ι → ℝ` (usually `ι = fin n` for some `n`). When we need to interpret a box `[l, u]` as a
set, we use the product `{x | ∀ i, l i < x i ∧ x i ≤ u i}` of half-open intervals `(l i, u i]`. We
exclude `l i` because this way boxes of a partition are disjoint as sets in `ℝⁿ`.

Currently, the only use cases for these constructions are the definitions of Riemann-style integrals
(Riemann, Henstock-Kurzweil, McShane).

## Main definitions

We use the same structure `box_integral.box` both for ambient boxes and for elements of a partition.
Each box is stored as two points `lower upper : ι → ℝ` and a proof of `∀ i, lower i < upper i`. We
define instances `has_mem (ι → ℝ) (box ι)` and `has_coe_t (box ι) (set $ ι → ℝ)` so that each box is
interpreted as the set `{x | ∀ i, x i ∈ set.Ioc (I.lower i) (I.upper i)}`. This way boxes of a
partition are pairwise disjoint and their union is exactly the original box.

We require boxes to be nonempty, because this way coercion to sets is injective. The empty box can
be represented as `⊥ : with_bot (box_integral.box ι)`.

We define the following operations on boxes:

* coercion to `set (ι → ℝ)` and `has_mem (ι → ℝ) (box_integral.box ι)` as described above;
* `partial_order` and `semilattice_sup` instances such that `I ≤ J` is equivalent to
  `(I : set (ι → ℝ)) ⊆ J`;
* `lattice` instances on `with_bot (box_integral.box ι)`;
* `box_integral.box.Icc`: the closed box `set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `box ι` to `set (ι → ℝ)`;
* `box_integral.box.face I i : box (fin n)`: a hyperface of `I : box_integral.box (fin (n + 1))`;
* `box_integral.box.distortion`: the maximal ratio of two lengths of edges of a box; defined as the
  supremum of `nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`.

We also provide a convenience constructor `box_integral.box.mk' (l u : ι → ℝ) : with_bot (box ι)`
that returns the box `⟨l, u, _⟩` if it is nonempty and `⊥` otherwise.

## Tags

rectangular box
-/

open set function metric filter

noncomputable theory
open_locale nnreal classical topology

namespace box_integral

variables {ι : Type*}

/-!
### Rectangular box: definition and partial order
-/

/-- A nontrivial rectangular box in `ι → ℝ` with corners `lower` and `upper`. Repesents the product
of half-open intervals `(lower i, upper i]`. -/
structure box (ι : Type*) :=
(lower upper : ι → ℝ)
(lower_lt_upper : ∀ i, lower i < upper i)

attribute [simp] box.lower_lt_upper

namespace box

variables (I J : box ι) {x y : ι → ℝ}

instance : inhabited (box ι) := ⟨⟨0, 1, λ i, zero_lt_one⟩⟩

lemma lower_le_upper : I.lower ≤ I.upper := λ i, (I.lower_lt_upper i).le
lemma lower_ne_upper (i) : I.lower i ≠ I.upper i := (I.lower_lt_upper i).ne

instance : has_mem (ι → ℝ) (box ι) := ⟨λ x I, ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)⟩
instance : has_coe_t (box ι) (set $ ι → ℝ) := ⟨λ I, {x | x ∈ I}⟩

@[simp] lemma mem_mk {l u x : ι → ℝ} {H} : x ∈ mk l u H ↔ ∀ i, x i ∈ Ioc (l i) (u i) := iff.rfl
@[simp, norm_cast] lemma mem_coe : x ∈ (I : set (ι → ℝ)) ↔ x ∈ I := iff.rfl

lemma mem_def : x ∈ I ↔ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i) := iff.rfl

lemma mem_univ_Ioc {I : box ι}  : x ∈ pi univ (λ i, Ioc (I.lower i) (I.upper i)) ↔ x ∈ I :=
mem_univ_pi

lemma coe_eq_pi : (I : set (ι → ℝ)) = pi univ (λ i, Ioc (I.lower i) (I.upper i)) :=
set.ext $ λ x, mem_univ_Ioc.symm

@[simp] lemma upper_mem : I.upper ∈ I := λ i, right_mem_Ioc.2 $ I.lower_lt_upper i

lemma exists_mem : ∃ x, x ∈ I := ⟨_, I.upper_mem⟩
lemma nonempty_coe : set.nonempty (I : set (ι → ℝ)) := I.exists_mem
@[simp] lemma coe_ne_empty : (I : set (ι → ℝ)) ≠ ∅ := I.nonempty_coe.ne_empty
@[simp] lemma empty_ne_coe : ∅ ≠ (I : set (ι → ℝ)) := I.coe_ne_empty.symm

instance : has_le (box ι) := ⟨λ I J, ∀ ⦃x⦄, x ∈ I → x ∈ J⟩

lemma le_def : I ≤ J ↔ ∀ x ∈ I, x ∈ J := iff.rfl

lemma le_tfae :
  tfae [I ≤ J,
    (I : set (ι → ℝ)) ⊆ J,
    Icc I.lower I.upper ⊆ Icc J.lower J.upper,
    J.lower ≤ I.lower ∧ I.upper ≤ J.upper] :=
begin
  tfae_have : 1 ↔ 2, from iff.rfl,
  tfae_have : 2 → 3,
  { intro h,
    simpa [coe_eq_pi, closure_pi_set, lower_ne_upper] using closure_mono h },
  tfae_have : 3 ↔ 4, from Icc_subset_Icc_iff I.lower_le_upper,
  tfae_have : 4 → 2, from λ h x hx i, Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i),
  tfae_finish
end

variables {I J}

@[simp, norm_cast] lemma coe_subset_coe : (I : set (ι → ℝ)) ⊆ J ↔ I ≤ J := iff.rfl
lemma le_iff_bounds : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper := (le_tfae I J).out 0 3

lemma injective_coe : injective (coe : box ι → set (ι → ℝ)) :=
begin
  rintros ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h,
  simp only [subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h,
  congr,
  exacts [le_antisymm h.2.1 h.1.1, le_antisymm h.1.2 h.2.2]
end

@[simp, norm_cast] lemma coe_inj : (I : set (ι → ℝ)) = J ↔ I = J :=
injective_coe.eq_iff

@[ext] lemma ext (H : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
injective_coe $ set.ext H

lemma ne_of_disjoint_coe (h : disjoint (I : set (ι → ℝ)) J) : I ≠ J :=
mt coe_inj.2 $ h.ne I.coe_ne_empty

instance : partial_order (box ι) :=
{ le := (≤),
  .. partial_order.lift (coe : box ι → set (ι → ℝ)) injective_coe }

/-- Closed box corresponding to `I : box_integral.box ι`. -/
protected def Icc : box ι ↪o set (ι → ℝ) :=
order_embedding.of_map_le_iff (λ I : box ι, Icc I.lower I.upper) (λ I J, (le_tfae I J).out 2 0)

lemma Icc_def : I.Icc = Icc I.lower I.upper := rfl

@[simp] lemma upper_mem_Icc (I : box ι) : I.upper ∈ I.Icc := right_mem_Icc.2 I.lower_le_upper
@[simp] lemma lower_mem_Icc (I : box ι) : I.lower ∈ I.Icc := left_mem_Icc.2 I.lower_le_upper

protected lemma is_compact_Icc (I : box ι) : is_compact I.Icc := is_compact_Icc

lemma Icc_eq_pi : I.Icc = pi univ (λ i, Icc (I.lower i) (I.upper i)) := (pi_univ_Icc _ _).symm

lemma le_iff_Icc : I ≤ J ↔ I.Icc ⊆ J.Icc := (le_tfae I J).out 0 2

lemma antitone_lower : antitone (λ I : box ι, I.lower) :=
λ I J H, (le_iff_bounds.1 H).1

lemma monotone_upper : monotone (λ I : box ι, I.upper) :=
λ I J H, (le_iff_bounds.1 H).2

lemma coe_subset_Icc : ↑I ⊆ I.Icc := λ x hx, ⟨λ i, (hx i).1.le, λ i, (hx i).2⟩

/-!
### Supremum of two boxes
-/

/-- `I ⊔ J` is the least box that includes both `I` and `J`. Since `↑I ∪ ↑J` is usually not a box,
`↑(I ⊔ J)` is larger than `↑I ∪ ↑J`. -/
instance : has_sup (box ι) :=
⟨λ I J, ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
  λ i, (min_le_left _ _).trans_lt $ (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩⟩

instance : semilattice_sup (box ι) :=
{ le_sup_left := λ I J, le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩,
  le_sup_right := λ I J, le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩,
  sup_le := λ I₁ I₂ J h₁ h₂, le_iff_bounds.2 ⟨le_inf (antitone_lower h₁) (antitone_lower h₂),
    sup_le (monotone_upper h₁) (monotone_upper h₂)⟩,
  .. box.partial_order, .. box.has_sup }


/-!
### `with_bot (box ι)`

In this section we define coercion from `with_bot (box ι)` to `set (ι → ℝ)` by sending `⊥` to `∅`.
-/

instance with_bot_coe : has_coe_t (with_bot (box ι)) (set (ι → ℝ)) := ⟨λ o, o.elim ∅ coe⟩

@[simp, norm_cast] lemma coe_bot : ((⊥ : with_bot (box ι)) : set (ι → ℝ)) = ∅ := rfl

@[simp, norm_cast] lemma coe_coe : ((I : with_bot (box ι)) : set (ι → ℝ)) = I := rfl

lemma is_some_iff : ∀ {I : with_bot (box ι)}, I.is_some ↔ (I : set (ι → ℝ)).nonempty
| ⊥ := by { erw option.is_some, simp }
| (I : box ι) := by { erw option.is_some, simp [I.nonempty_coe] }

lemma bUnion_coe_eq_coe (I : with_bot (box ι)) :
  (⋃ (J : box ι) (hJ : ↑J = I), (J : set (ι → ℝ))) = I :=
by induction I using with_bot.rec_bot_coe; simp [with_bot.coe_eq_coe]

@[simp, norm_cast] lemma with_bot_coe_subset_iff {I J : with_bot (box ι)} :
  (I : set (ι → ℝ)) ⊆ J ↔ I ≤ J :=
begin
  induction I using with_bot.rec_bot_coe, { simp },
  induction J using with_bot.rec_bot_coe, { simp [subset_empty_iff] },
  simp
end

@[simp, norm_cast] lemma with_bot_coe_inj {I J : with_bot (box ι)} :
  (I : set (ι → ℝ)) = J ↔ I = J :=
by simp only [subset.antisymm_iff, ← le_antisymm_iff,  with_bot_coe_subset_iff]

/-- Make a `with_bot (box ι)` from a pair of corners `l u : ι → ℝ`. If `l i < u i` for all `i`,
then the result is `⟨l, u, _⟩ : box ι`, otherwise it is `⊥`. In any case, the result interpreted
as a set in `ι → ℝ` is the set `{x : ι → ℝ | ∀ i, x i ∈ Ioc (l i) (u i)}`.  -/
def mk' (l u : ι → ℝ) : with_bot (box ι) :=
if h : ∀ i, l i < u i then ↑(⟨l, u, h⟩ : box ι) else ⊥

@[simp] lemma mk'_eq_bot {l u : ι → ℝ} : mk' l u = ⊥ ↔ ∃ i, u i ≤ l i :=
by { rw mk', split_ifs; simpa using h }

@[simp] lemma mk'_eq_coe {l u : ι → ℝ} : mk' l u = I ↔ l = I.lower ∧ u = I.upper :=
begin
  cases I with lI uI hI, rw mk', split_ifs,
  { simp [with_bot.coe_eq_coe] },
  { suffices : l = lI → u ≠ uI, by simpa,
    rintro rfl rfl, exact h hI }
end

@[simp] lemma coe_mk' (l u : ι → ℝ) : (mk' l u : set (ι → ℝ)) = pi univ (λ i, Ioc (l i) (u i)) :=
begin
  rw mk', split_ifs,
  { exact coe_eq_pi _ },
  { rcases not_forall.mp h with ⟨i, hi⟩,
    rw [coe_bot, univ_pi_eq_empty], exact Ioc_eq_empty hi }
end

instance : has_inf (with_bot (box ι)) :=
⟨λ I, with_bot.rec_bot_coe (λ J, ⊥) (λ I J, with_bot.rec_bot_coe ⊥
  (λ J, mk' (I.lower ⊔ J.lower) (I.upper ⊓ J.upper)) J) I⟩

@[simp] lemma coe_inf (I J : with_bot (box ι)) : (↑(I ⊓ J) : set (ι → ℝ)) = I ∩ J :=
begin
  induction I using with_bot.rec_bot_coe, { change ∅ = _, simp },
  induction J using with_bot.rec_bot_coe, { change ∅ = _, simp },
  change ↑(mk' _ _) = _,
  simp only [coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, pi.sup_apply, pi.inf_apply, coe_mk',
    coe_coe]
end

instance : lattice (with_bot (box ι)) :=
{ inf_le_left := λ I J,
    begin
      rw [← with_bot_coe_subset_iff, coe_inf],
      exact inter_subset_left _ _
    end,
  inf_le_right := λ I J,
    begin
      rw [← with_bot_coe_subset_iff, coe_inf],
      exact inter_subset_right _ _
    end,
  le_inf := λ I J₁ J₂ h₁ h₂,
    begin
      simp only [← with_bot_coe_subset_iff, coe_inf] at *,
      exact subset_inter h₁ h₂
    end,
  .. with_bot.semilattice_sup, .. box.with_bot.has_inf }

@[simp, norm_cast] lemma disjoint_with_bot_coe {I J : with_bot (box ι)} :
  disjoint (I : set (ι → ℝ)) J ↔ disjoint I J :=
by { simp only [disjoint_iff_inf_le, ← with_bot_coe_subset_iff, coe_inf], refl }

lemma disjoint_coe : disjoint (I : with_bot (box ι)) J ↔ disjoint (I : set (ι → ℝ)) J :=
disjoint_with_bot_coe.symm

lemma not_disjoint_coe_iff_nonempty_inter :
  ¬disjoint (I : with_bot (box ι)) J ↔ (I ∩ J : set (ι → ℝ)).nonempty :=
by rw [disjoint_coe, set.not_disjoint_iff_nonempty_inter]

/-!
### Hyperface of a box in `ℝⁿ⁺¹ = fin (n + 1) → ℝ`
-/

/-- Face of a box in `ℝⁿ⁺¹ = fin (n + 1) → ℝ`: the box in `ℝⁿ = fin n → ℝ` with corners at
`I.lower ∘ fin.succ_above i` and `I.upper ∘ fin.succ_above i`. -/
@[simps { simp_rhs := tt }] def face {n} (I : box (fin (n + 1))) (i : fin (n + 1)) : box (fin n) :=
⟨I.lower ∘ fin.succ_above i, I.upper ∘ fin.succ_above i, λ j, I.lower_lt_upper _⟩

@[simp] lemma face_mk {n} (l u : fin (n + 1) → ℝ) (h : ∀ i, l i < u i) (i : fin (n + 1)) :
  face ⟨l, u, h⟩ i = ⟨l ∘ fin.succ_above i, u ∘ fin.succ_above i, λ j, h _⟩ :=
rfl

@[mono] lemma face_mono {n} {I J : box (fin (n + 1))} (h : I ≤ J) (i : fin (n + 1)) :
  face I i ≤ face J i :=
λ x hx i, Ioc_subset_Ioc ((le_iff_bounds.1 h).1 _) ((le_iff_bounds.1 h).2 _) (hx _)

lemma monotone_face {n} (i : fin (n + 1)) : monotone (λ I, face I i) := λ I J h, face_mono h i

lemma maps_to_insert_nth_face_Icc {n} (I : box (fin (n + 1))) {i : fin (n + 1)} {x : ℝ}
  (hx : x ∈ Icc (I.lower i) (I.upper i)) :
  maps_to (i.insert_nth x) (I.face i).Icc I.Icc :=
λ y hy, fin.insert_nth_mem_Icc.2 ⟨hx, hy⟩

lemma maps_to_insert_nth_face {n} (I : box (fin (n + 1))) {i : fin (n + 1)} {x : ℝ}
  (hx : x ∈ Ioc (I.lower i) (I.upper i)) :
  maps_to (i.insert_nth x) (I.face i) I :=
λ y hy, by simpa only [mem_coe, mem_def, i.forall_iff_succ_above, hx, fin.insert_nth_apply_same,
  fin.insert_nth_apply_succ_above, true_and]

lemma continuous_on_face_Icc {X} [topological_space X] {n} {f : (fin (n + 1) → ℝ) → X}
  {I : box (fin (n + 1))} (h : continuous_on f I.Icc) {i : fin (n + 1)} {x : ℝ}
  (hx : x ∈ Icc (I.lower i) (I.upper i)) :
  continuous_on (f ∘ i.insert_nth x) (I.face i).Icc :=
h.comp (continuous_on_const.fin_insert_nth i continuous_on_id) (I.maps_to_insert_nth_face_Icc hx)

/-!
### Covering of the interior of a box by a monotone sequence of smaller boxes
-/

/-- The interior of a box. -/
protected def Ioo : box ι →o set (ι → ℝ) :=
{ to_fun := λ I, pi univ (λ i, Ioo (I.lower i) (I.upper i)),
  monotone' := λ I J h, pi_mono $ λ i hi, Ioo_subset_Ioo ((le_iff_bounds.1 h).1 i)
    ((le_iff_bounds.1 h).2 i) }

lemma Ioo_subset_coe (I : box ι) : I.Ioo ⊆ I := λ x hx i, Ioo_subset_Ioc_self (hx i trivial)

protected lemma Ioo_subset_Icc (I : box ι) : I.Ioo ⊆ I.Icc := I.Ioo_subset_coe.trans coe_subset_Icc

lemma Union_Ioo_of_tendsto [finite ι] {I : box ι} {J : ℕ → box ι} (hJ : monotone J)
  (hl : tendsto (lower ∘ J) at_top (𝓝 I.lower)) (hu : tendsto (upper ∘ J) at_top (𝓝 I.upper)) :
  (⋃ n, (J n).Ioo) = I.Ioo :=
have hl' : ∀ i, antitone (λ n, (J n).lower i),
  from λ i, (monotone_eval i).comp_antitone (antitone_lower.comp_monotone hJ),
have hu' : ∀ i, monotone (λ n, (J n).upper i),
  from λ i, (monotone_eval i).comp (monotone_upper.comp hJ),
calc (⋃ n, (J n).Ioo) = pi univ (λ i, ⋃ n, Ioo ((J n).lower i) ((J n).upper i)) :
  Union_univ_pi_of_monotone (λ i, (hl' i).Ioo (hu' i))
... = I.Ioo :
  pi_congr rfl (λ i hi, Union_Ioo_of_mono_of_is_glb_of_is_lub (hl' i) (hu' i)
    (is_glb_of_tendsto_at_top (hl' i) (tendsto_pi_nhds.1 hl _))
    (is_lub_of_tendsto_at_top (hu' i) (tendsto_pi_nhds.1 hu _)))

lemma exists_seq_mono_tendsto (I : box ι) : ∃ J : ℕ →o box ι, (∀ n, (J n).Icc ⊆ I.Ioo) ∧
  tendsto (lower ∘ J) at_top (𝓝 I.lower) ∧ tendsto (upper ∘ J) at_top (𝓝 I.upper) :=
begin
  choose a b ha_anti hb_mono ha_mem hb_mem hab ha_tendsto hb_tendsto
    using λ i, exists_seq_strict_anti_strict_mono_tendsto (I.lower_lt_upper i),
  exact ⟨⟨λ k, ⟨flip a k, flip b k, λ i, hab _ _ _⟩,
    λ k l hkl, le_iff_bounds.2 ⟨λ i, (ha_anti i).antitone hkl, λ i, (hb_mono i).monotone hkl⟩⟩,
    λ n x hx i hi, ⟨(ha_mem _ _).1.trans_le (hx.1 _), (hx.2 _).trans_lt (hb_mem _ _).2⟩,
    tendsto_pi_nhds.2 ha_tendsto, tendsto_pi_nhds.2 hb_tendsto⟩
end

section distortion

variable [fintype ι]

/-- The distortion of a box `I` is the maximum of the ratios of the lengths of its edges.
It is defined as the maximum of the ratios
`nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`. -/
def distortion (I : box ι) : ℝ≥0 :=
finset.univ.sup $ λ i : ι, nndist I.lower I.upper / nndist (I.lower i) (I.upper i)

lemma distortion_eq_of_sub_eq_div {I J : box ι} {r : ℝ}
  (h : ∀ i, I.upper i - I.lower i = (J.upper i - J.lower i) / r) :
  distortion I = distortion J :=
begin
  simp only [distortion, nndist_pi_def, real.nndist_eq', h, map_div₀],
  congr' 1 with i,
  have : 0 < r,
  { by_contra hr,
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 $ J.lower_le_upper i) (not_lt.1 hr),
    rw ← h at this,
    exact this.not_lt (sub_pos.2 $ I.lower_lt_upper i) },
  simp_rw [nnreal.finset_sup_div, div_div_div_cancel_right _ ((map_ne_zero real.nnabs).2 this.ne')],
end

lemma nndist_le_distortion_mul (I : box ι) (i : ι) :
  nndist I.lower I.upper ≤ I.distortion * nndist (I.lower i) (I.upper i) :=
calc nndist I.lower I.upper =
  (nndist I.lower I.upper / nndist (I.lower i) (I.upper i)) *  nndist (I.lower i) (I.upper i) :
  (div_mul_cancel _ $ mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
... ≤ I.distortion * nndist (I.lower i) (I.upper i) :
  mul_le_mul_right' (finset.le_sup $ finset.mem_univ i) _

lemma dist_le_distortion_mul (I : box ι) (i : ι) :
  dist I.lower I.upper ≤ I.distortion * (I.upper i - I.lower i) :=
have A : I.lower i - I.upper i < 0, from sub_neg.2 (I.lower_lt_upper i),
by simpa only [← nnreal.coe_le_coe, ← dist_nndist, nnreal.coe_mul, real.dist_eq,
  abs_of_neg A, neg_sub] using I.nndist_le_distortion_mul i

lemma diam_Icc_le_of_distortion_le (I : box ι) (i : ι) {c : ℝ≥0} (h : I.distortion ≤ c) :
  diam I.Icc ≤ c * (I.upper i - I.lower i) :=
have (0 : ℝ) ≤ c * (I.upper i - I.lower i),
  from mul_nonneg c.coe_nonneg (sub_nonneg.2 $ I.lower_le_upper _),
diam_le_of_forall_dist_le this $ λ x hx y hy,
  calc dist x y ≤ dist I.lower I.upper : real.dist_le_of_mem_pi_Icc hx hy
  ... ≤ I.distortion * (I.upper i - I.lower i) : I.dist_le_distortion_mul i
  ... ≤ c * (I.upper i - I.lower i) :
    mul_le_mul_of_nonneg_right h (sub_nonneg.2 (I.lower_le_upper i))

end distortion

end box

end box_integral
