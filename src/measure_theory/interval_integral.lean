import measure_theory.set_integral
import measure_theory.lebesgue_measure

noncomputable theory
open topological_space (second_countable_topology)
open measure_theory set classical

open_locale classical

variables {α β 𝕜 E F : Type*} [decidable_linear_order α] [measurable_space α] [normed_group E]

def interval_integrable (f : α → E) (μ : measure α) (a b : α) :=
integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ

namespace interval_integrable

section

variables {f : α → E} {a b c : α} {μ : measure α}

@[symm] lemma symm (h : interval_integrable f μ a b) : interval_integrable f μ b a :=
h.symm

@[refl] lemma refl : interval_integrable f μ a a :=
by split; simp

@[trans] lemma trans  (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  interval_integrable f μ a c :=
⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
  (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

lemma neg (h : interval_integrable f μ a b) : interval_integrable (-f) μ a b :=
⟨h.1.neg, h.2.neg⟩

end

lemma smul [normed_field 𝕜] [normed_space 𝕜 E] {f : α → E} {a b : α} {μ : measure α}
  (h : interval_integrable f μ a b) (r : 𝕜) :
  interval_integrable (r • f) μ a b :=
⟨h.1.smul r, h.2.smul r⟩

variables [measurable_space E] [opens_measurable_space E] {f g : α → E} {a b : α} {μ : measure α}

lemma add (hfm : measurable f) (hfi : interval_integrable f μ a b)
  (hgm : measurable g) (hgi : interval_integrable g μ a b) :
  interval_integrable (f + g) μ a b :=
⟨hfi.1.add hfm hgm hgi.1, hfi.2.add hfm hgm hgi.2⟩

lemma sub (hfm : measurable f) (hfi : interval_integrable f μ a b)
  (hgm : measurable g) (hgi : interval_integrable g μ a b) :
  interval_integrable (f - g) μ a b :=
⟨hfi.1.sub hfm hgm hgi.1, hfi.2.sub hfm hgm hgi.2⟩

end interval_integrable

variables [second_countable_topology E] [complete_space E] [normed_space ℝ E]
  [measurable_space E] [borel_space E]

def interval_integral (f : α → E) (a b : α) (μ : measure α) :=
∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ

notation `∫` binders ` in ` a `..` b `, ` r:(scoped:60 f, f) ` ∂` μ:70 := interval_integral r a b μ
notation `∫` binders ` in ` a `..` b `, ` r:(scoped:60 f, interval_integral f a b volume) := r

namespace interval_integral

variables {a b c : α} {f g : α → E} {μ : measure α}

lemma integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ :=
by simp [interval_integral, h]

@[simp] lemma integral_same : ∫ x in a..a, f x ∂μ = 0 :=
sub_self _

lemma integral_symm (a b) : ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, neg_sub]

lemma integral_of_ge (h : b ≤ a) : ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ :=
by simp only [integral_symm b, integral_of_le h]

lemma integral_add (hfm : measurable f) (hfi : interval_integrable f μ a b)
  (hgm : measurable g) (hgi : interval_integrable g μ a b) :
  ∫ x in a..b, f x + g x ∂μ = ∫ x in a..b, f x ∂μ + ∫ x in a..b, g x ∂μ :=
begin
  simp only [interval_integral, integral_add hfm hfi.1 hgm hgi.1,
    integral_add hfm hfi.2 hgm hgi.2],
  abel
end

@[simp] lemma integral_neg : ∫ x in a..b, -f x ∂μ = -∫ x in a..b, f x ∂μ :=
begin
  simp only [interval_integral, integral_neg],
  abel
end

variables [topological_space α] [opens_measurable_space α] [order_closed_topology α]

lemma integral_cocycle (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ + ∫ x in c..a, f x ∂μ = 0 :=
begin
  have hac := hab.trans hbc,
  simp only [interval_integral, ← add_sub_comm, sub_eq_zero],
  iterate 4 { rw ← integral_union },
  { suffices : Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc b a ∪ Ioc c b ∪ Ioc a c, by rw this,
    rw [Ioc_union_Ioc_union_Ioc_cycle, union_right_comm, Ioc_union_Ioc_union_Ioc_cycle,
      min_left_comm, max_left_comm] },
  all_goals { simp [*, is_measurable.union, is_measurable_Ioc, Ioc_disjoint_Ioc_same,
    Ioc_disjoint_Ioc_same.symm, hab.1, hab.2, hbc.1, hbc.2, hac.1, hac.2] }
end

lemma integral_add_adjacent_intervals (hfm : measurable f) (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ :=
by rw [← add_neg_eq_zero, ← integral_symm, integral_cocycle hfm hab hbc]

lemma integral_cases (f : α → E) (a b) :
  ∫ x in a..b, f x ∂μ ∈ ({∫ x in Ioc (min a b) (max a b), f x ∂μ,
    -∫ x in Ioc (min a b) (max a b), f x ∂μ} : set E) :=
(le_total a b).imp (λ h, by simp [h, integral_of_le]) (λ h, by simp [h, integral_of_ge])

lemma norm_integral_eq_norm_integral_Ioc :
  ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ioc (min a b) (max a b), f x ∂μ∥ :=
(integral_cases f a b).elim (congr_arg _) (λ h, (congr_arg _ h).trans (norm_neg _))

lemma norm_integral_le_integral_norm_Ioc :
  ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in Ioc (min a b) (max a b), ∥f x∥ ∂μ :=
calc ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ioc (min a b) (max a b), f x ∂μ∥ :
  norm_integral_eq_norm_integral_Ioc
... ≤ ∫ x in Ioc (min a b) (max a b), ∥f x∥ ∂μ :
  norm_integral_le_integral_norm f

lemma norm_integral_le_abs_integral_norm : ∥∫ x in a..b, f x ∂μ∥ ≤ abs (∫ x in a..b, ∥f x∥ ∂μ) :=
begin
  simp only [← real.norm_eq_abs, norm_integral_eq_norm_integral_Ioc],
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)
end

lemma norm_integral_le_of_le_const {a b C : ℝ} {f : ℝ → E}
  (h : ∀ x ∈ Ico (min a b) (max a b), ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x∥ ≤ C * abs (b - a) :=
begin
  refine le_trans norm_integral_le_integral_norm_Ioc _,
  
end

end interval_integral
