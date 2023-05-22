/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.constructions.pi
import measure_theory.integral.interval_integral
import measure_theory.integral.mean_inequalities
import measure_theory.constructions.prod.integral
import geometry.manifold.cont_mdiff_map

/-!
# Marginals of multivariate functions
-/


noncomputable theory

open_locale classical big_operators topology ennreal

variables {ι ι' ι'' : Type*}
section finset
open finset

namespace real

lemma prod_rpow {ι} (s : finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
  ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r :=
sorry

end real

variables {α β γ : Type*}

lemma equiv.finset_image_univ_eq_univ [fintype α] [fintype β] (f : α ≃ β) :
  univ.image f = univ :=
finset.image_univ_of_surjective f.surjective

variables [comm_monoid β]

-- very similar to `equiv.prod_comp_finset` in #16948
lemma finset.prod_comp_equiv {s : finset α} (f : γ → β) (g : α ≃ γ) :
  ∏ a in s, f (g a) = ∏ b in s.image g, f b :=
begin
  refine prod_bij' (λ x _, g x) (λ a ha, finset.mem_image_of_mem _ ha) (λ _ _, rfl)
    (λ a _, g.symm a) _ (λ a _, g.symm_apply_apply a) (λ a _, g.apply_symm_apply a),
  simp only [finset.mem_image, exists_imp_distrib], rintro _ _ _ rfl, simpa
end

lemma prod_univ_comp_equiv [fintype α] [fintype γ] (f : γ → β) (g : α ≃ γ) :
  ∏ a, f (g a) = ∏ b, f b :=
g.prod_comp f -- by rw [prod_comp_equiv f g, g.finset_image_univ_eq_univ]


namespace finset

lemma insert_compl_insert [fintype ι] {s : finset ι} {i : ι} (hi : i ∉ s) :
  insert i (insert i s)ᶜ = sᶜ :=
by simp_rw [@eq_compl_comm _ _ s, compl_insert, compl_erase, compl_compl, erase_insert hi]

@[simp, to_additive] lemma mul_prod_eq_prod_insert_none {α} {M} [comm_monoid M]
  (f : α → M) (x : M)
  (s : finset α) : x * ∏ i in s, f i = ∏ i in s.insert_none, i.elim x f :=
(prod_insert_none (λ i, i.elim x f) _).symm

end finset
end finset

section calculus

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [fintype ι]
variables {E : ι → Type*} [∀ i, normed_add_comm_group (E i)] [∀ i, normed_space 𝕜 (E i)]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

-- ⇑(fderiv ℝ (λ (x_1 : ℝ), update x i x_1) y)


lemma fderiv_update {x : Π i, E i} {i : ι} (y : E i) :
  fderiv 𝕜 (function.update x i) y =
  continuous_linear_map.pi (function.update 0 i (continuous_linear_map.id 𝕜 (E i))) :=
sorry

lemma continuous_linear_map.norm_le_norm_pi (f : Πi, F →L[𝕜] E i) (i : ι) :
  ‖f i‖ ≤ ‖continuous_linear_map.pi f‖ :=
sorry

lemma continuous_linear_map.norm_pi [nonempty ι] (f : Πi, F →L[𝕜] E i) :
  ‖continuous_linear_map.pi f‖ = (finset.univ.image $ λ i, ‖f i‖).max' (finset.univ_nonempty.image _) :=
sorry

variable (E)
lemma continuous_linear_map.norm_pi_update_eq_one {i : ι} :
  ‖continuous_linear_map.pi (function.update 0 i (continuous_linear_map.id 𝕜 (E i)))‖ = 1 :=
sorry

end calculus

section logic

open sum

@[simp] lemma imp_and_neg_imp_iff (p q : Prop) [decidable p] : (p → q) ∧ (¬ p → q) ↔ q :=
by simp_rw [imp_iff_or_not, not_not, ← or_and_distrib_left, not_and_self, or_false]

@[simp]
lemma cast_sum_rec {α β : Type*} {P : α ⊕ β → Sort*} (f : Π i, P (inl i)) (g : Π j, P (inr j))
  (x y : α ⊕ β) (h : x = y) :
  cast (congr_arg P h) (@sum.rec _ _ _ f g x) = @sum.rec _ _ _ f g y :=
by { cases h, refl }

end logic

namespace equiv
open _root_.set

attribute [simps] equiv.Pi_congr_left
attribute [simps apply symm_apply] subtype_equiv_right

variables {α : ι → Type*}

lemma Pi_congr_left_symm_preimage_pi (f : ι' ≃ ι) (s : set ι) (t : ∀ i, set (α i)) :
  (f.Pi_congr_left α).symm ⁻¹' (f ⁻¹' s).pi (λ i', t $ f i') = s.pi t :=
begin
  ext, simp_rw [mem_preimage, set.mem_pi, Pi_congr_left_symm_apply],
  convert f.forall_congr_left, refl
end

lemma Pi_congr_left_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, set (α i)) :
  f.Pi_congr_left α ⁻¹' pi univ t = pi univ (λ i, t (f i)) :=
begin
  apply set.ext, rw [← (f.Pi_congr_left α).symm.forall_congr_left],
  intro x, simp only [mem_univ_pi, mem_preimage, apply_symm_apply, Pi_congr_left_symm_apply],
  exact f.forall_congr_left.symm
end

open sum

/--  The type of dependent functions on a sum type `ι ⊕ ι'` is equivalent to the type of pairs of
  functions on `ι` and on `ι'`. This is a dependent version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps]
def Pi_sum (π : ι ⊕ ι' → Type*) : ((Π i, π (inl i)) × (Π i', π (inr i'))) ≃ Π i, π i :=
{ to_fun := λ f, sum.rec f.1 f.2,
  inv_fun := λ g, ⟨λ i, g (inl i), λ i', g (inr i')⟩,
  left_inv := λ f, prod.ext rfl rfl,
  right_inv := λ g, by { ext (i|i); refl } }

def Pi_sum' (π : ι → Type*) (π' : ι' → Type*) :
  ((Π i, π i) × (Π i', π' i')) ≃ Π i, sum.elim π π' i :=
equiv.Pi_sum (sum.elim π π')

lemma set.union_apply_left' {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  {a : α} (ha : a ∈ s) : equiv.set.union H ⟨a, set.mem_union_left _ ha⟩ = sum.inl ⟨a, ha⟩ :=
dif_pos ha

lemma set.union_apply_right' {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  {a : α} (ha : a ∈ t) : equiv.set.union H ⟨a, set.mem_union_right _ ha⟩ = sum.inr ⟨a, ha⟩ :=
dif_neg $ λ h, H ⟨h, ha⟩

lemma sum_rec_congr (P : ι ⊕ ι' → Sort*) (f : Π i, P (inl i)) (g : Π i, P (inr i)) {x y : ι ⊕ ι'}
  (h : x = y) : @sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@sum.rec _ _ _ f g y) :=
by { cases h, refl }

lemma Pi_congr_left_sum_inl (π : ι'' → Type*) (e : ι ⊕ ι' ≃ ι'')
  (f : Π i, π (e (inl i))) (g : Π i, π (e (inr i))) (i : ι) :
  Pi_congr_left π e (Pi_sum (π ∘ e) (f, g)) (e (inl i)) = f i :=
by simp_rw [Pi_congr_left_apply, Pi_sum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inl i)),
    cast_cast, cast_eq]

lemma Pi_congr_left_sum_inr (π : ι'' → Type*) (e : ι ⊕ ι' ≃ ι'')
  (f : Π i, π (e (inl i))) (g : Π i, π (e (inr i))) (j : ι') :
  Pi_congr_left π e (Pi_sum (π ∘ e) (f, g)) (e (inr j)) = g j :=
by simp_rw [Pi_congr_left_apply, Pi_sum_apply, sum_rec_congr _ _ _ (e.symm_apply_apply (inr j)),
    cast_cast, cast_eq]

end equiv

namespace option

lemma elim_comp {ι α β} (h : α → β) {f : ι → α} {x : α} {i : option ι} :
  i.elim (h x) (λ j, h (f j)) = h (i.elim x f) :=
by cases i; refl

lemma elim_comp₂ {ι α β γ} (h : α → β → γ) {f : ι → α} {x : α} {g : ι → β} {y : β} {i : option ι} :
  i.elim (h x y) (λ j, h (f j) (g j)) = h (i.elim x f) (i.elim y g) :=
by cases i; refl

lemma elim_apply {α β ι : Type*} {f : ι → α → β} {x : α → β} {i : option ι} {y : α} :
  i.elim x f y = i.elim (x y) (λ j, f j y) :=
by rw [elim_comp (λ f : α → β, f y)]

end option

open function measure_theory.outer_measure measurable_space equiv

section function

open set

variables {α : ι → Type*}

/-- Given one value over a unique, we get a dependent function. -/
def unique_elim [unique ι] (x : α (default : ι)) (i : ι) : α i :=
by { rw [unique.eq_default i], exact x }

@[simp] lemma unique_elim_default [unique ι] (x : α (default : ι)) :
  unique_elim x (default : ι) = x :=
rfl

lemma unique_elim_preimage [unique ι] (t : ∀ i, set (α i)) :
  unique_elim ⁻¹'  pi univ t = t (default : ι) :=
by { ext, simp [unique.forall_iff] }

lemma pred_update {α} {β : α → Type*} (P : ∀ ⦃a⦄, β a → Prop)
  (f : Π a, β a) (a' : α) (v : β a') (a : α) :
  P (update f a' v a) ↔ (a = a' ∧ P v) ∨ (a ≠ a' ∧ P (f a)) :=
by { rw [update], split_ifs, { subst h, simp }, { rw [← ne.def] at h, simp [h] }}

lemma surjective_decode_iget (α : Type*) [encodable α] [inhabited α] :
  surjective (λ n, (encodable.decode α n).iget) :=
λ x, ⟨encodable.encode x, by simp_rw [encodable.encodek]⟩

end function

section set
open set

/-- `s ∪ t` (using finset union) is equivalent to `s ∪ t` (using set union) -/
-- @[simps apply symm_apply]
def equiv.finset_union {α} (s t : finset α) : ((s ∪ t : finset α) : set α) ≃ (s ∪ t : set α) :=
subtype_equiv_right $ by simp

def finset_union_equiv_sum {α} (s t : finset α) (h : disjoint s t) : (s ∪ t : finset α) ≃ s ⊕ t :=
(equiv.finset_union s t).trans $ equiv.set.union $ by { rw [← finset.coe_inter], exact h.le_bot }

@[simp]
lemma finset_union_equiv_sum_symm_inl {α} {s t : finset α} (h : disjoint s t) (x : s) :
  (finset_union_equiv_sum s t h).symm (sum.inl x) = ⟨x, finset.mem_union.mpr $ or.inl x.2⟩ :=
rfl

@[simp]
lemma finset_union_equiv_sum_symm_inr {α} {s t : finset α} (h : disjoint s t) (y : t) :
  (finset_union_equiv_sum s t h).symm (sum.inr y) = ⟨y, finset.mem_union.mpr $ or.inr y.2⟩ :=
rfl

@[simp]
lemma finset_union_equiv_sum_symm_inl' {α} {s t : finset α} (h : disjoint s t) (x : α)
  (hx : x ∈ s) (h2x : x ∈ s ∪ t) :
  (finset_union_equiv_sum s t h).symm (sum.inl ⟨x, hx⟩) = ⟨x, h2x⟩ :=
rfl

@[simp]
lemma finset_union_equiv_sum_symm_inr' {α} {s t : finset α} (h : disjoint s t) (y : t) :
  (finset_union_equiv_sum s t h).symm (sum.inr y) = ⟨y, finset.mem_union.mpr $ or.inr y.2⟩ :=
rfl


@[simp]
lemma finset_union_equiv_sum_left {α} {s t : finset α} (h : disjoint s t) (x : s ∪ t)
  (hx : ↑x ∈ s) :
  finset_union_equiv_sum s t h x = sum.inl ⟨x, hx⟩ :=
sorry -- equiv.set.union_apply_left _ $ finset.mem_coe.mp hx

@[simp]
lemma finset_union_equiv_sum_right {α} {s t : finset α} (h : disjoint s t) (x : s ∪ t)
  (hx : ↑x ∈ t) :
  finset_union_equiv_sum s t h x = sum.inr ⟨x, hx⟩ :=
sorry

lemma Union_univ_pi {ι ι₂} {α : ι → Type*} (t : ∀ i, ι₂ → set (α i)) :
  (⋃ (x : ι → ι₂), pi univ (λ i, t i (x i))) = pi univ (λ i, ⋃ (j : ι₂), t i j) :=
by { ext, simp [classical.skolem] }

lemma eval_preimage {ι} {α : ι → Type*} {i : ι} {s : set (α i)} :
  eval i ⁻¹' s = pi univ (update (λ i, univ) i s) :=
by { ext x, simp [@forall_update_iff _ (λ i, set (α i)) _ _ _ _ (λ i' y, x i' ∈ y)] }

lemma eval_preimage' {ι} {α : ι → Type*} {i : ι} {s : set (α i)} :
  eval i ⁻¹' s = pi {i} (update (λ i, univ) i s) :=
by { ext, simp }

lemma mem_pi_univ {ι : Type*} {α : ι → Type*} (t : ∀ i, set (α i)) (x : ∀ i, α i) :
  x ∈ pi univ t ↔ ∀ i, x i ∈ t i :=
by simp

lemma pi_univ_ite {ι} {α : ι → Type*} (s : set ι) (t : ∀ i, set (α i)) :
  pi univ (λ i, if i ∈ s then t i else univ) = s.pi t :=
by { ext, simp_rw [set.mem_pi], apply forall_congr, intro i, split_ifs; simp [h] }

lemma pi_univ_eq_Inter {ι} {α : ι → Type*} (t : ∀ i, set (α i)) :
  pi univ t = ⋂ i, eval i ⁻¹' t i :=
by simp_rw [pi_def, mem_univ, Inter_true]

end set

section measurable
open set

variables {α : ι → Type*}

lemma measurable_unique_elim [unique ι] [∀ i, measurable_space (α i)] :
  measurable (unique_elim : α (default : ι) → Π i, α i) :=
by { simp_rw [measurable_pi_iff, unique.forall_iff, unique_elim_default], exact measurable_id }

lemma measurable_set.univ_pi_fintype {δ} {π : δ → Type*} [∀ i, measurable_space (π i)] [fintype δ]
  {t : Π i, set (π i)} (ht : ∀ i, measurable_set (t i)) : measurable_set (pi univ t) :=
measurable_set.pi finite_univ.countable (λ i _, ht i)


end measurable


section measurable_on_family


variables {α : ι → Type*}
variables [∀ i, measurable_space (α i)]
variables (α)
lemma measurable_eq_mp {i i' : ι} (h : i = i') : measurable (congr_arg α h).mp :=
by { cases h, exact measurable_id }

lemma measurable.eq_mp {β} [measurable_space β] {i i' : ι} (h : i = i') {f : β → α i}
  (hf : measurable f) : measurable (λ x, (congr_arg α h).mp (f x)) :=
(measurable_eq_mp α h).comp hf
variables {α}

lemma measurable_Pi_congr_left (f : ι' ≃ ι) : measurable (Pi_congr_left α f) :=
begin
  rw measurable_pi_iff,
  intro i,
  apply measurable.eq_mp α (f.apply_symm_apply i),
  exact measurable_pi_apply (f.symm i)
end

end measurable_on_family

open finset


namespace measure_theory

lemma subsingleton.measurable_singleton_class {α} [measurable_space α] [subsingleton α] :
  measurable_singleton_class α :=
begin
  refine ⟨λ i, _⟩,
  convert measurable_set.univ,
  simp [set.eq_univ_iff_forall],
end

/-- A version of Hölder with multiple arguments -/
theorem integral_prod_norm_pow_le {α} [measurable_space α] {μ : measure α} (s : finset ι)
  {f : ι → α → ℝ} (h2f : ∀ i ∈ s, 0 ≤ f i) {p : ι → ℝ} (hp : ∑ i in s, p i = 1)
  (h2p : ∀ i ∈ s, 0 ≤ p i)
  (hf : ∀ i ∈ s, mem_ℒp (f i) (ennreal.of_real $ p i) μ) :
  ∫ a, ∏ i in s, f i a ^ p i ∂μ ≤ ∏ i in s, (∫ a, f i a ∂μ) ^ p i :=
sorry

namespace measure

variables {α : ι → Type*}
variables [∀ i, measurable_space (α i)]
variables [fintype ι] [fintype ι']
variables {m : Π i, outer_measure (α i)}
variables [Π i, measurable_space (α i)] {μ : Π i, measure (α i)}
variables [∀ i, sigma_finite (μ i)]

variable (μ)

/-- Some properties of `measure.pi` -/

lemma pi_unique_left [unique ι] : measure.pi μ = map unique_elim (μ (default : ι)) :=
begin
  apply pi_eq, intros s hs,
  rw [map_apply measurable_unique_elim (measurable_set.univ_pi_fintype hs), unique_elim_preimage],
  symmetry, convert prod_singleton, rw [finset.ext_iff, unique.forall_iff], simp
end

open _root_.sum

lemma pi_map_left (f : ι' ≃ ι) :
  map (f.Pi_congr_left α) (measure.pi (λ i', μ (f i'))) = measure.pi μ :=
begin
  refine (pi_eq _).symm, intros s hs,
  rw [map_apply _ (measurable_set.univ_pi_fintype hs)],
  { simp_rw [Pi_congr_left_preimage_univ_pi, pi_pi _ _,
    prod_univ_comp_equiv (λ i, μ i (s i)) f] },
  { apply measurable_Pi_congr_left }
end

lemma pi_sum {π : ι ⊕ ι' → Type*} [∀ i, measurable_space (π i)] (μ : ∀ i, measure (π i))
  [∀ i, sigma_finite (μ i)] :
  map (equiv.Pi_sum π) ((measure.pi (λ i, μ (sum.inl i))).prod (measure.pi (λ i, μ (sum.inr i)))) =
  measure.pi μ :=
begin
  refine (pi_eq $ λ s hs, _).symm,
  rw [map_apply],
  all_goals {sorry}
end

end measure

section

variables {α E : Type*} [measurable_space α] [normed_add_comm_group E]

lemma measurable.has_finite_integral_dirac {f : α → E}
  (hf : measurable (λ x, ‖f x‖₊ : α → ℝ≥0∞)) {x : α} : has_finite_integral f (measure.dirac x) :=
begin
  rw [has_finite_integral, lintegral_dirac' _ hf],
  exact ennreal.coe_lt_top
end

lemma has_finite_integral_dirac [measurable_singleton_class α] {f : α → E} {x : α} :
  has_finite_integral f (measure.dirac x) :=
begin
  rw [has_finite_integral, lintegral_dirac],
  exact ennreal.coe_lt_top
end

lemma strongly_measurable.integrable_dirac [measurable_space E] [borel_space E]
  {f : α → E}
  (hf : strongly_measurable f) {x : α} : integrable f (measure.dirac x) :=
⟨hf.ae_strongly_measurable, hf.measurable.ennnorm.has_finite_integral_dirac⟩


end

section marginal

open finset topological_space
variables {δ : Type*} {π : δ → Type*} [∀ x, measurable_space (π x)]
variables {μ : ∀ i, measure (π i)} [∀ i, sigma_finite (μ i)]
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  [measurable_space E] [borel_space E]



lemma integral_of_is_empty {α} [measurable_space α] [is_empty α] (μ : measure α) (f : α → E) :
  ∫ x, f x ∂μ = 0 :=
begin
  convert integral_zero_measure f,
end

lemma _root_.has_compact_support.integral_deriv_eq {f : ℝ → E} (hf : cont_diff ℝ 1 f)
  (h2f : has_compact_support f) (b : ℝ) :
  ∫ x in set.Iic b, deriv f x = f b :=
begin
  sorry
end


variables {s t : finset δ} {f g : (Π i, π i) → E} {x y : Π i, π i} {i : δ}

def update' (s : finset δ) (f : (Π i, π i) → E) (x : Π i, π i) : (Π i : s, π i) → E :=
  λ y, f (λ i, if hi : i ∈ s then y ⟨i, hi⟩ else x i)

lemma update'_empty {y} : update' ∅ f x y = f x := rfl

lemma measurable_update_aux :
  measurable (λ y i, if hi : i ∈ s then y ⟨i, hi⟩ else x i : (Π i : s, π i) → Π i, π i) :=
begin
  rw measurable_pi_iff, intro i,
  by_cases h : i ∈ s,
  { simp [h, measurable_pi_apply] },
  { simp [h] }
end

/-- The integrand of `marginal _ _ f` is measurable if `f` is. -/
lemma _root_.measurable.update' (hf : measurable f) {s : finset δ}
  {x : Π i, π i} : measurable (update' s f x) :=
hf.comp measurable_update_aux

/-- The integrand of `marginal _ _ f` is measurable if `f` is. -/
lemma _root_.measure_theory.strongly_measurable.update'
  (hf : strongly_measurable f) {s : finset δ} {x : Π i, π i} :
  strongly_measurable (update' s f x) :=
hf.comp_measurable measurable_update_aux

-- def update'_comp (h : s ⊆ t) : update' s f x ∘ (λ (z : Π (i : t), π i) i, z ⟨i, h i.2⟩) =
--   update' t f x :=
-- begin
--   ext x,
--   simp_rw [function.comp, update'],
--   congr', ext i,
--   split_ifs; try {refl},
--   exfalso, exact h_2 (h h_1),
-- end

/-- `f` is integrable w.r.t. coordinates `xᵢ` where `i ∈ s`. -/
def integrable_wrt (μ : ∀ i, measure (π i)) (s : finset δ) (f : (Π i, π i) → E) : Prop :=
strongly_measurable f ∧
∀ (x : Π i, π i), has_finite_integral (update' s f x) (measure.pi (λ i : s, μ i))

lemma integrable_wrt_empty : integrable_wrt μ ∅ f ↔ strongly_measurable f :=
begin
  simp_rw [integrable_wrt, and_iff_left_iff_imp],
  intros hf x,
  simp_rw [measure.pi_of_empty (λ i : (∅ : finset δ), μ i)],
  haveI : measurable_singleton_class (Π i : (∅ : finset δ), π i),
  { exact subsingleton.measurable_singleton_class },
  exact has_finite_integral_dirac,
end

lemma integrable_wrt.integrable_update' (hf : integrable_wrt μ s f) :
  integrable (update' s f x) (measure.pi (λ i : s, μ i)) :=
⟨hf.1.update'.ae_strongly_measurable, hf.2 x⟩

/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s`. -/
def marginal (μ : ∀ i, measure (π i)) (s : finset δ) (f : (Π i, π i) → E) (x : Π i, π i) :
  E :=
∫ y : Π i : s, π i, update' s f x y ∂(measure.pi (λ i : s, μ i))

/- Note: this notation is not a binder. This is more convenient since it returns a function. -/
notation `∫⋯∫_` s `, ` f ` ∂` μ:70 := marginal μ s f
notation `∫⋯∫_` s `, ` f := marginal volume s f

lemma _root_.measurable.marginal (hf : strongly_measurable f) :
  strongly_measurable (∫⋯∫_ s, f ∂μ) :=
begin
  refine measure_theory.strongly_measurable.integral_prod_right _,
  sorry
end

lemma marginal_empty (f : (Π i, π i) → E) : ∫⋯∫_ ∅, f ∂μ = f :=
begin
  ext x,
  simp_rw [marginal, measure.pi_of_empty (λ i : (∅ : finset δ), μ i)],
  exact integral_dirac' _ _ (subsingleton.strongly_measurable' _)
end

/-- The marginal distribution is independent of the variables in `s`. -/
lemma marginal_eq {x y : Π i, π i} (f : (Π i, π i) → E)
  (h : ∀ i ∉ s, x i = y i) : (∫⋯∫_ s, f ∂μ) x = (∫⋯∫_ s, f ∂μ) y :=
by { dsimp [marginal, update'], rcongr, exact h _ ‹_› }

variable (μ)
lemma marginal_update (x : Π i, π i) (f : (Π i, π i) → E) {i : δ} (y : π i)
  (hi : i ∈ s) : (∫⋯∫_ s, f ∂μ) (function.update x i y) = (∫⋯∫_ s, f ∂μ) x :=
begin
  refine marginal_eq f (λ j hj, _),
  have : j ≠ i,
  { rintro rfl, exact hj hi },
  apply update_noteq this,
end


lemma marginal_union (f : (Π i, π i) → E) (hf : integrable_wrt μ (s ∪ t) f)
  (hst : disjoint s t) :
  ∫⋯∫_ s ∪ t, f ∂μ = ∫⋯∫_ s, ∫⋯∫_ t, f ∂μ ∂μ :=
begin
  ext x,
  simp_rw [marginal, update', ← measure.pi_map_left _ (finset_union_equiv_sum s t hst).symm],
  rw [integral_map, ← measure.pi_sum, integral_map, integral_prod],
  dsimp only [finset_union_equiv_sum_symm_inl, finset_union_equiv_sum_symm_inr, subtype.coe_mk],
  congr' 1, ext x, congr' 1, ext y, congr' 1, ext i,
  by_cases his : i ∈ s; by_cases hit : i ∈ t; simp only [his, hit, dif_pos, dif_neg,
    finset.mem_union, true_or, false_or, not_false_iff],
  { exfalso, exact finset.disjoint_left.mp hst his hit },
  -- this is ugly, but applying lemmas basically doesn't work because of dependent types
  { change Pi_congr_left (λ (b : ↥(s ∪ t)), π ↑b) (finset_union_equiv_sum s t hst).symm
      (Pi_sum (λ (i : s ⊕ t), π ↑((finset_union_equiv_sum s t hst).symm i)) (x, y))
      ((finset_union_equiv_sum s t hst).symm $ sum.inl ⟨i, his⟩) = x ⟨i, his⟩,
    rw [Pi_congr_left_sum_inl] },
  { change Pi_congr_left (λ (b : ↥(s ∪ t)), π ↑b) (finset_union_equiv_sum s t hst).symm
      (Pi_sum (λ (i : s ⊕ t), π ↑((finset_union_equiv_sum s t hst).symm i)) (x, y))
      ((finset_union_equiv_sum s t hst).symm $ sum.inr ⟨i, hit⟩) = y ⟨i, hit⟩,
    rw [Pi_congr_left_sum_inr] },
  -- simp_rw [cast_sum_rec],
  -- simp only [Pi_congr_left_apply, Pi_sum_apply, dif_neg, not_false_iff],
  -- dsimp only [equiv.symm_symm],

  -- dsimp only [e, set.union_symm_apply_left],
  all_goals {sorry},
end

lemma marginal_union' (f : (Π i, π i) → E) (hf : measurable f) {s t : finset δ}
  (hst : disjoint s t) :
  ∫⋯∫_ s ∪ t, f ∂μ = ∫⋯∫_ t, ∫⋯∫_ s, f ∂μ ∂μ :=
begin
  ext x,
  simp_rw [marginal, ← measure.pi_map_left _ (finset_union_equiv_sum s t hst).symm],
  rw [integral_map, ← measure.pi_sum, integral_map, integral_prod],
  dsimp only [finset_union_equiv_sum_symm_inl, finset_union_equiv_sum_symm_inr, subtype.coe_mk],
  congr' 1,
  -- dsimp only [e, set.union_symm_apply_left],
  all_goals {sorry},

  --
  -- { symmetry, congr' with x, congr' with y, congr' with i, symmetry,
        -- by_cases his : i ∈ s; by_cases hit : i ∈ t,
  --   { exact false.elim (this ⟨his, hit⟩) },
  --   all_goals { simp only [his, hit, Pi_congr_left_apply, dif_pos, or_false, false_or,
  --     measure.equiv.Pi_sum_apply, dif_neg, not_false_iff, finset.mem_union] },
  --   all_goals { dsimp only [e, trans_apply, finset_union_apply, set.union_apply_left,
  --   set.union_apply_right, subtype.coe_mk], rw [← heq_iff_eq], refine (eq_mpr_heq _ _).trans _ },
  --   exact congr_arg_heq _ (set.union_apply_left' this his),
  --   exact congr_arg_heq _ (set.union_apply_right' this hit) },

end
variable {μ}

lemma marginal_singleton (f : (Π i, π i) → E) (hf : measurable f) (i : δ) :
  ∫⋯∫_ {i}, f ∂μ = λ x, ∫ xᵢ, f (function.update x i xᵢ) ∂(μ i) :=
begin
  letI : unique ({i} : finset δ) :=
    ⟨⟨⟨i, mem_singleton_self i⟩⟩, λ j, subtype.ext $ mem_singleton.mp j.2⟩,
  ext x,
  simp_rw [marginal, update', measure.pi_unique_left _],
  rw [integral_map],
  congr' with y, congr' with j,
  by_cases hj : j = i,
  { cases hj.symm, simp only [dif_pos, mem_singleton, update_same],
    exact @unique_elim_default _ (λ i : (({i} : finset δ) : set δ), π i) _ y },
  { simp [hj] },
  { exact measurable.ae_measurable measurable_unique_elim },
  sorry,
end

lemma integral_update (f : (Π i, π i) → E) (hf : measurable f) (i : δ) (x : Π i, π i) :
  (∫ xᵢ, f (function.update x i xᵢ) ∂(μ i)) = (∫⋯∫_ {i}, f ∂μ) x :=
by simp_rw [marginal_singleton f hf i]

-- lemma marginal_insert (f : (Π i, π i) → E) (hf : measurable f) {i : δ}
--   (hi : i ∉ s) :
--   ∫⋯∫_ insert i s, f ∂μ = λ x, ∫ xᵢ, (∫⋯∫_ s, λ x, f (function.update x i xᵢ) ∂μ) x ∂(μ i) :=
-- begin
--   ext x,
--   rw [insert_eq, marginal_union, marginal_singleton],
--   dsimp only,
-- end

lemma marginal_insert_rev (f : (Π i, π i) → E) (hf : measurable f) {i : δ}
  (hi : i ∉ s) (x : Π i, π i) :
  ∫ xᵢ, (∫⋯∫_ s, f ∂μ) (function.update x i xᵢ) ∂(μ i) = (∫⋯∫_ insert i s, f ∂μ) x :=
begin
  rw [insert_eq, marginal_union, marginal_singleton],
  dsimp only,
end

open filter
lemma marginal_mono_of_nonneg {f g : (Π i, π i) → ℝ} (hf : 0 ≤ f) (hg : integrable_wrt μ s g)
  (hfg : f ≤ g) : ∫⋯∫_ s, f ∂μ ≤ ∫⋯∫_ s, g ∂μ :=
λ x, integral_mono_of_nonneg (eventually_of_forall $ λ x, hf _) hg.integrable_update'
  (eventually_of_forall $ λ y, hfg _)

lemma marginal_mono {f g : (Π i, π i) → ℝ}
  (hf : integrable_wrt μ s f) (hg : integrable_wrt μ s g) (hfg : f ≤ g) :
  ∫⋯∫_ s, f ∂μ ≤ ∫⋯∫_ s, g ∂μ :=
λ x, integral_mono hf.integrable_update' hg.integrable_update' (λ y, hfg _)

lemma marginal_univ [fintype δ] (f : (Π i, π i) → E) :
  ∫⋯∫_ univ, f ∂μ = λ _, ∫ x, f x ∂(measure.pi μ) :=
begin
  let e : { j // j ∈ univ} ≃ δ := equiv.subtype_univ_equiv mem_univ,
  ext x,
  simp_rw [marginal, update', ← measure.pi_map_left μ e],
  rw [integral_map], congr' with y, congr' with i, simp [e], dsimp [e], refl,
  sorry, sorry
end

end marginal

end measure_theory

open measure_theory

section sobolev

open topological_space
variables {E : Type*} [normed_add_comm_group E] [second_countable_topology E] -- todo: remove
  [normed_space ℝ E] [complete_space E] [measurable_space E] [borel_space E]
variables [fintype ι] {π : ι → Type*} [Π i, measurable_space (π i)]
  (μ : Π i, measure (π i)) [∀ i, sigma_finite (μ i)] (u : (ι → ℝ) → E)

def rhs_aux (f : (Π i, π i) → ℝ) (s : finset ι) : (Π i, π i) → ℝ :=
(marginal μ s f) ^ ((s.card : ℝ) / (fintype.card ι - 1)) *
∏ i in sᶜ, marginal μ (insert i s) f ^ ((1 : ℝ) / (fintype.card ι - 1))

lemma marginal_rhs_aux_le (f : (Π i, π i) → ℝ) (hf : ∀ x, 0 ≤ f x) (s : finset ι) (i : ι) (hi : i ∉ s) :
  ∫⋯∫_{i}, rhs_aux μ f s ∂μ ≤ rhs_aux μ f (insert i s) :=
begin
    simp_rw [rhs_aux, ← insert_compl_insert hi],
    rw [prod_insert (not_mem_compl.mpr $ mem_insert_self i s)],
    rw [mul_left_comm, mul_prod_eq_prod_insert_none],
    simp_rw [marginal_singleton _ sorry],
    have := λ x xᵢ, marginal_update μ x f xᵢ (s.mem_insert_self i),
    simp_rw [pi.mul_apply, pi.pow_apply, this],
    clear this,
    simp_rw [integral_mul_left, prod_apply, option.elim_comp₂, pi.pow_apply],
    intro x, dsimp only,
    have h1 : (0 : ℝ) ≤ (∫⋯∫_(insert i s), f ∂μ) x ^ ((1 : ℝ) / (fintype.card ι - 1)) :=
    sorry,

    refine (mul_le_mul_of_nonneg_left (integral_prod_norm_pow_le _ _ _ _ _) h1).trans_eq _,
    { sorry },
    { sorry },
    { sorry },
    { sorry }, -- automatic if we switch to Lebesgue
    simp_rw [prod_insert_none],
    dsimp,
    simp_rw [marginal_insert_rev _ sorry hi],
    rw [← mul_assoc],
    congr,
    { convert (real.rpow_add_of_nonneg _ _ _).symm,
      sorry,
      sorry,
      sorry,
      sorry, },
    simp_rw [prod_apply, pi.pow_apply],
    refine prod_congr rfl (λ j hj, _),
    congr' 1,
    rw [insert.comm],
    have h2 : i ∉ insert j s,
    { sorry },
    simp_rw [marginal_insert_rev _ sorry h2]
end


lemma marginal_rhs_aux_empty_le (f : (Π i, π i) → ℝ) (hf : ∀ x, 0 ≤ f x) (s : finset ι) :
  ∫⋯∫_s, rhs_aux μ f ∅ ∂μ ≤ rhs_aux μ f s :=
begin
  induction s using finset.induction with i s hi ih,
  { rw [marginal_empty], refl', },
  { have hi' : disjoint {i} s := sorry,
    conv_lhs { rw [finset.insert_eq, marginal_union μ _ sorry hi'] },
    refine (marginal_mono sorry sorry ih).trans _,
    exact marginal_rhs_aux_le μ f hf s i hi }
end

lemma integral_prod_integral_pow_le (f : (Π i, π i) → ℝ) (hf : ∀ x, 0 ≤ f x) :
  ∫ x, ∏ i, (∫ xᵢ, f (function.update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (fintype.card ι - 1)) ∂measure.pi μ ≤
  (∫ x, f x ∂measure.pi μ)  ^ ((fintype.card ι : ℝ) / (fintype.card ι - 1)) :=
begin
  casesI is_empty_or_nonempty (Π i, π i),
  { simp_rw [integral_of_is_empty, real.zero_rpow_nonneg] },
  inhabit (Π i, π i),
  have := marginal_rhs_aux_empty_le μ f hf finset.univ default,
  simp_rw [rhs_aux, marginal_univ, finset.compl_univ, finset.prod_empty, marginal_empty,
    finset.card_empty, nat.cast_zero, zero_div, finset.compl_empty, mul_one,
    pi.mul_def, pi.pow_apply, real.rpow_zero, one_mul, finset.prod_fn, pi.pow_apply,
    insert_emptyc_eq, marginal_singleton f sorry] at this,
  exact this,
end

/-- The Sobolev inequality -/
theorem integral_pow_le (hu : cont_diff ℝ 1 u) (h2u : has_compact_support u) :
  ∫ x, ‖u x‖ ^ ((fintype.card ι : ℝ) / (fintype.card ι - 1)) ≤
  (∫ x, ‖fderiv ℝ u x‖)  ^ ((fintype.card ι : ℝ) / (fintype.card ι - 1)) :=
begin
  refine le_trans _ (integral_prod_integral_pow_le (λ _, volume) _ $ λ x, norm_nonneg _),
  refine integral_mono sorry sorry (λ x, _),
  dsimp only,
  simp_rw [div_eq_mul_inv, one_mul, real.rpow_mul sorry, real.prod_rpow _ sorry],
  refine real.rpow_le_rpow sorry _ sorry,
  norm_cast,
  rw [← card_univ, ← prod_const],
  refine prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, _),
  have h3u : cont_diff ℝ 1 (λ t, u (update x i t)),
  { sorry },
  have h4u : has_compact_support (λ t, u (update x i t)),
  { sorry },
  have := h4u.integral_deriv_eq h3u (x i),
  dsimp only at this,
  simp_rw [update_eq_self] at this,
  rw [← this],
  refine (norm_integral_le_integral_norm _).trans _,
  refine (set_integral_mono_set sorry sorry _).trans _,
  exact set.univ,
  refine (set.subset_univ _).eventually_le,
  rw [integral_univ],
  refine integral_mono sorry sorry (λ y, _),
  dsimp only,
  rw fderiv.comp y (hu.differentiable le_rfl).differentiable_at sorry,
  rw [continuous_linear_map.comp_apply],
  refine (continuous_linear_map.le_op_norm _ _).trans _,
  conv_rhs { rw [← mul_one ‖_‖] },
  simp_rw [fderiv_update],
  refine mul_le_mul_of_nonneg_left _ (norm_nonneg _),
  refine (continuous_linear_map.le_op_norm _ _).trans_eq _,
  rw [norm_one, mul_one],
  exact continuous_linear_map.norm_pi_update_eq_one (λ _, ℝ)
end

/-- The Sobolev inequality -/
theorem lintegral_pow_le : ∫⁻ x, ‖u x‖₊ ^ ((fintype.card ι : ℝ) / (fintype.card ι - 1)) ≤
  (∫⁻ x, ‖fderiv ℝ u x‖₊)  ^ ((fintype.card ι : ℝ) / (fintype.card ι - 1)) :=
begin
  sorry
end


end sobolev
