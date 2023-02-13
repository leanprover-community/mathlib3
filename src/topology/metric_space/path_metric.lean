/-
Copyright (c) 2023 Junyan Xu, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Rémi Bottinelli
-/
import analysis.bounded_variation
import topology.path_connected
import topology.metric_space.arclength
import topology.metric_space.lipschitz

/-!
# Path Metric

TODO

-/
open_locale nnreal ennreal big_operators unit_interval
open set unit_interval
noncomputable theory

alias evariation_on.eq_of_eq_on ← set.eq_on.evariation_on_eq

namespace path

variables {E : Type*} [pseudo_emetric_space E] {x y z : E} (p : path x y) (q : path y z)

/-- The length of `p : path x y` is its `evariation_on` its whole domain. -/
def length : ℝ≥0∞ := evariation_on p set.univ

lemma edist_le_length : edist x y ≤ p.length :=
by { simp_rw [length, ← p.source, ← p.target], exact evariation_on.edist_le _ trivial trivial }

-- TODO : move to `data/set/image.lean#870` after `set.subsingleton.image` ?
lemma _root_.set.subsingleton_image_of_const {α β : Type*} (b : β) (s : set α) :
  ((λ _, b) '' s).subsingleton := by
{ rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩, refl }

lemma length_refl (x : E) : (path.refl x).length = 0 :=
evariation_on.constant_on (set.subsingleton_image_of_const _ _)

lemma length_symm : p.symm.length = p.length :=
evariation_on.comp_eq_of_antitone_on _ _ (unit_interval.antitone_symm.antitone_on _)
  (set.maps_to_univ _ _) $
  set.surjective_iff_surj_on_univ.1 $ unit_interval.bijective_symm.surjective

lemma length_trans : (p.trans q).length = p.length + q.length :=
begin
  rw [length, evariation_on.split_univ _ (div_two 1),
    (p.trans_eq_on_left q).evariation_on_eq, (p.trans_eq_on_right q).evariation_on_eq],
  congr' 1; apply evariation_on.comp_eq_of_monotone_on _ _ _ (set.maps_to_univ _ _),
  { refine λ t ht, ⟨div_two t, div_two_mem_Iic t, _⟩,
    dsimp only, rw [two_mul_div_two, set.proj_Icc_of_mem _ t.prop],
    ext, refl },
  work_on_goal 2 { refine λ t ht, ⟨unit_interval.symm
      (div_two $ unit_interval.symm t), (symm_mem_Ici_iff _).2 (div_two_mem_Iic _), _⟩,
    dsimp only, rw [coe_symm_eq, mul_sub, mul_one, two_mul_div_two, sub_right_comm,
      (_ : (2 - 1 : ℝ) = 1), ← coe_symm_eq, unit_interval.symm_symm, set.proj_Icc_of_mem _ t.prop],
    { ext, refl }, norm_num },
  all_goals { apply ((set.monotone_proj_Icc _).comp $ λ x y h, _).monotone_on },
  { exact mul_le_mul_of_nonneg_left h zero_le_two },
  { exact sub_le_sub_right (mul_le_mul_of_nonneg_left h zero_le_two) _ },
end

lemma comp_length_le {F : Type*} [pseudo_emetric_space F] {φ : E → F} {K : ℝ≥0}
  (hφ : lipschitz_with K φ) : (p.map hφ.continuous).length ≤ ↑K * p.length :=
lipschitz_on_with.comp_evariation_on_le (hφ.lipschitz_on_with set.univ) (set.maps_to_univ _ _)

/-- An alternative definition of `path.length`. -/
lemma evariation_on_extend_unit_interval_eq_length :
  evariation_on p.extend I = p.length := arclength_Icc_extend zero_le_one p

lemma arclength_on_zero_one_eq_length : arclength p 0 1 = p.length :=
by rw [length, arclength, unit_interval.univ_eq_Icc]

lemma length_of_continuous_on {X : Type*} {f : ℝ → X} {s t : ℝ} (hst : s ≤ t)
  [pseudo_emetric_space X] (hf : continuous_on f (set.Icc s t)) :
  (of_continuous_on hst hf).length = arclength f s t :=
begin
  apply evariation_on.comp_eq_of_monotone_on _ _ (monotone.monotone_on _ _) _ (λ x hx, _),
  { exact (monotone_affine_of_le hst).comp (λ _ _, id) },
  { exact λ x hx, affine_maps_to_I hst x.2 },
  { obtain ⟨y, hy, h'⟩ := affine_surj_on_I hx, exact ⟨⟨y, hy⟩, trivial, h'⟩ },
end

end path

section path_emetric

/-- The type synonym for the pseudo-emetric space `E` endowed with its path pseudo-emetric. -/
def path_emetric (E : Type*) := E

variables {E : Type*}

instance [h : inhabited E] : inhabited (path_emetric E) := ⟨h.1⟩

/-- Casting from `E` to `path_emetric E`. -/
def to_path_emetric : E ≃ path_emetric E := equiv.refl _

/-- Casting from `path_emetric E` to `E`. -/
def from_path_emetric : path_emetric E ≃ E := equiv.refl _

lemma from_to_path_emetric (x : E) : from_path_emetric (to_path_emetric x) = x := rfl
lemma to_from_path_emetric (x : path_emetric E) : to_path_emetric (from_path_emetric x) = x := rfl

local notation `of` := to_path_emetric
local notation `fo` := from_path_emetric

variables [pseudo_emetric_space E]

/--
The path pseudo-emetric on `path_emetric E`:
The distance between two points is the infimum of the length of paths joining them
-/
instance : pseudo_emetric_space (path_emetric E) :=
{ edist := λ x y, ⨅ p : path (fo x) (fo y), p.length,
  edist_self := λ x, le_antisymm (infi_le_of_le _ $ (path.length_refl _).le) zero_le',
  edist_comm := λ x y, by apply le_antisymm;
    exact le_infi (λ p, (infi_le _ _).trans_eq p.length_symm),
  edist_triangle := λ x y z, begin
    simp_rw [ennreal.infi_add, ennreal.add_infi],
    exact le_infi₂ (λ p q, (infi_le _ _).trans_eq $ p.length_trans q),
  end }

/-- `E` is a length space if the path emetric on `E` is equal to its original metric. -/
class length_space (E) [pseudo_emetric_space E] : Prop :=
(isom : isometry (of : E → path_emetric E))

lemma edist_le_edist_of (x y : E) : edist x y ≤ edist (of x) (of y) :=
le_infi $ λ p, p.edist_le_length

lemma from_length_emetric_nonexpanding :
  lipschitz_with 1 (from_path_emetric : path_emetric E → E) :=
λ x y, by { rw [ennreal.coe_one, one_mul], exact edist_le_edist_of x y }

lemma continuous_from_length_emetric : continuous (from_path_emetric : path_emetric E → E) :=
from_length_emetric_nonexpanding.continuous

lemma path_emetric.edist_le_arclength {f : ℝ → E} {s t : ℝ} (hst : s ≤ t)
  (hf : continuous_on f (set.Icc s t)) : edist (of $ f s) (of $ f t) ≤ arclength f s t :=
(infi_le _ $ path.of_continuous_on hst hf).trans_eq $ path.length_of_continuous_on _ _

lemma path_emetric.edist_le_max {f : ℝ → E} (s t : ℝ) (hf : continuous_on f (set.uIcc s t)) :
  edist (of $ f s) (of $ f t) ≤ max (arclength f s t) (arclength f t s) :=
begin
  obtain hst | hts := le_total s t,
  { rw max_eq_left ((arclength_eq_zero f hst).trans_le $ zero_le _),
    exact path_emetric.edist_le_arclength hst (hf.mono set.Icc_subset_uIcc) },
  { rw [max_eq_right ((arclength_eq_zero f hts).trans_le $ zero_le _), edist_comm],
    exact path_emetric.edist_le_arclength hts (hf.mono set.Icc_subset_uIcc') },
end

lemma path_emetric.continuous_of_locally_bounded_variation {f : ℝ → E} {s : set ℝ}
  (hconn : s.ord_connected) (hcont : continuous_on f s)
  (fbdd : has_locally_bounded_variation_on f s) : continuous_on (of ∘ f) s :=
λ x hx, begin
  simp_rw [continuous_within_at, emetric.tendsto_nhds, edist_comm],
  have := (continuous_on_arclength f x hconn fbdd hcont x hx).max
    (continuous_on_arclength' f x hconn fbdd hcont x hx),
  dsimp only at this, rw [arclength_self, max_self] at this,
  exact λ ε hε, (ennreal.nhds_zero_basis.tendsto_right_iff.1 this ε hε).mp
    (filter.eventually_inf_principal.2 $ filter.eventually_of_forall $ λ y hy h,
    (path_emetric.edist_le_max x y $ hcont.mono $ hconn.uIcc_subset hx hy).trans_lt h),
end

/--
If `p : path x y` has finite length, the composite `to_path_emetric ∘ e` is continuous,
hence defining a `path (of x) (of y)`.
-/
@[simps] def path.of_length_ne_top {x y : E} (p : path x y) (hp : p.length ≠ ⊤) :
  path (of x) (of y) :=
begin
  refine ⟨⟨of ∘ p, _⟩, p.source, p.target⟩,
  convert continuous_on_iff_continuous_restrict.1
    (path_emetric.continuous_of_locally_bounded_variation
      set.ord_connected_Icc p.continuous_extend.continuous_on $
      has_bounded_variation_on.has_locally_bounded_variation_on _),
  { ext, rw p.extend_extends' },
  { rwa ← p.evariation_on_extend_unit_interval_eq_length at hp },
end

/-- Every continuous curve, rectifiable or not, has the same length in the path metric. -/
lemma path_emetric.evariation_of_eq_evariation {f : ℝ → E}
  {s : set ℝ} (hconn : s.ord_connected) (hcont : continuous_on f s) :
  evariation_on (of ∘ f) s = evariation_on f s :=
begin
  refine (supr_le _).antisymm
    (supr_le $ λ u, trans (finset.sum_le_sum $ λ i hi, edist_le_edist_of _ _) $ le_supr _ u),
  rintro ⟨n, u, um, us⟩,
  refine (finset.sum_le_sum $ λ i hi, _).trans _,
  { exact λ i, arclength f (u i) (u $ i+1) },
  { rw edist_comm, exact path_emetric.edist_le_arclength
      (um $ i.le_succ) (hcont.mono $ hconn.out (us i) (us $ i+1)) },
  { rw arclength_sum f um, apply evariation_on.mono f (hconn.out (us 0) (us n)) },
end

lemma path.length_of_length_ne_top {x y : E} (p : path x y) (hp : p.length ≠ ⊤) :
  (p.of_length_ne_top hp).length = p.length :=
begin
  simp_rw [← path.evariation_on_extend_unit_interval_eq_length,
           ← path_emetric.evariation_of_eq_evariation
           set.ord_connected_Icc p.continuous_extend.continuous_on],
  refl,
end

lemma path.length_eq {x y : E} (p : path (of x) (of y)) :
  (p.map continuous_from_length_emetric).length = p.length :=
begin
  by_cases h : (p.map continuous_from_length_emetric).length = ⊤,
  { symmetry,
    simpa only [h, ennreal.coe_one, one_mul, top_le_iff] using
      path.comp_length_le p from_length_emetric_nonexpanding, },
  { rw ←(path.length_of_length_ne_top _ h),
    congr' with _,
    refl, },
end

instance (E) [pseudo_emetric_space E] : length_space (path_emetric E) :=
⟨λ x y, begin
  refine (le_infi $ λ p, _).antisymm (edist_le_edist_of x y),
  by_cases p.length = ⊤, { rw h, exact le_top },
  rw ← p.length_of_length_ne_top h,
  exact infi_le _ _,
end⟩

end path_emetric
