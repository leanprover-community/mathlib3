import topology.coarse_structure.basic
import topology.metric_space.basic
import topology.uniform_space.basic
import data.real.nnreal

open set filter coarse_space
open_locale uniformity filter nnreal coarse_space

variables {α β γ : Type*} {a b : α} {s t : set (α × α)}
variables [metric_space α] [metric_space β]


lemma metric.directed_of_cocontrolled :
  directed ge (λ (r : ℝ≥0), 𝓟 {p : α × α | dist p.fst p.snd ≤ ↑r}ᶜ) :=
begin
  intros x y, use max x y,
  simp, tauto,
end

lemma metric.mem_cocontrolled_dist' :
  s ∈ (⨅ r:ℝ≥0, 𝓟 ({p:α×α | dist p.1 p.2 ≤ r}ᶜ)) ↔ (∃ r:ℝ≥0, ∀ {a b : α}, (a,b) ∈ sᶜ → dist a b ≤ r) :=
begin
  rw mem_infi_of_directed metric.directed_of_cocontrolled,
  apply exists_congr, intro r, simp [subset_def],
  apply forall_congr, intro x, apply forall_congr, intro y,
  split, repeat {intro, contrapose, simp, assumption,},
end

instance coarse_of_bounded_space : coarse_space α :=
{ cocontrolled := (⨅ r:ℝ≥0, 𝓟 ({p:α×α | dist p.1 p.2 ≤ r}ᶜ)),
  corefl := by {
    have lm : 𝓟 ({p : α × α | dist p.fst p.snd ≤ 1}ᶜ) ≤ 𝓟 coid_rel,
    by {
      simp only [principal_le_iff, mem_principal],
      intros V hV,
      refine subset.trans _ hV,
      rintro ⟨x,y⟩,
      simp only [not_le, mem_set_of_eq, nmem_coid_rel, ne.def, mem_compl_eq],
      intro v,
      apply dist_ne_zero.mp,
      show dist x y ≠ 0, by linarith, -- why do I need to do this?
    },
    refine trans _ lm,
    simp only [metric.mem_cocontrolled_dist', filter.le_def],
    intros s hs, use 1,
    simp only [true_and, zero_le_one, prod.forall, ge_iff_le, mem_compl_eq],
    simp [compl_subset_comm] at hs,
    intros a b in_s,
    simpa using hs in_s,
  },
  symm := by {
    intros f hf,
    simp only [ge_iff_le, mem_map],
    simp only [metric.mem_cocontrolled_dist'] at *,
    simp at *,
    conv in (∃ (r : ℝ≥0), ∀ (a b : α), (b, a) ∉ f → nndist a b ≤ r)
    begin
      congr, funext,
      rw forall_swap,
      find (nndist _ _) {rw nndist_comm},
    end,
    tauto,
  },
  cocomp := by {
    intro s,
    rw filter.mem_lift'_sets,
    show monotone (λ (s : set (α × α)), s □ s), by {exact cocomp_rel.monotone monotone_id monotone_id},
    rintro ⟨t, ⟨h, cocomp_subset⟩⟩,
    have comp_subset : sᶜ ⊆ tᶜ ○ tᶜ, by {rw ←compl_subset_compl, simpa,},
    rw metric.mem_cocontrolled_dist' at *,
    rcases h with ⟨r, diam_compl_t⟩,
    use 2*r,
    rintro x y mem_compl_s,
    rcases comp_subset mem_compl_s with ⟨z, xz_mem_compl_t, zy_mem_compl_t⟩,
    have : dist x z ≤ r ∧ dist z y ≤ r,
    by exact ⟨diam_compl_t xz_mem_compl_t, diam_compl_t zy_mem_compl_t⟩,
    have := dist_triangle x z y,
    simp only [nonneg.coe_mul, nnreal.coe_bit0, nonneg.coe_one],
    linarith,
  }
}

@[simp]
lemma metric.mem_cocontrolled_dist :
  s ∈ 𝓒' α ↔ (∃ r:ℝ≥0, ∀ {a b : α}, (a,b) ∈ sᶜ → dist a b ≤ r) :=
begin
  exact metric.mem_cocontrolled_dist',
end

@[simp]
lemma metric.mem_controlled_dist :
  s ∈ 𝓒 α ↔ (∃ (r : ℝ≥0) , ∀ {a b : α}, (a, b) ∈ s → dist a b ≤ r) :=
by simp

theorem mem.cocontrolled_basis_dist :
  (𝓒' α).has_basis (λ r : ℝ≥0, true) (λ r, {p:α×α | dist p.1 p.2 > r}) :=
begin
  rw filter.has_basis_iff, intro t,
  rw metric.mem_cocontrolled_dist, split,
  {
    rintro ⟨r, compl_t_bounded_by_r⟩, use r,
    rw [←compl_subset_compl, subset_def],
    simpa,
  },
  {
    rintro ⟨r, r_ge_0, coball_subset_t⟩, use r,
    rw [←compl_subset_compl, subset_def] at coball_subset_t,
    simp [mem_compl_iff] at *,
    tauto,
  }
end

lemma metric.coarse_bounded_iff (b : set α) : coarse_space.bounded b ↔ emetric.diam b ≠ ⊤ :=
sorry

lemma metric.coarse_proper_iff (f : α → β) :
  coarse_space.proper f ↔ (∀ b : set β, emetric.diam b ≠ ⊤ → emetric.diam (f ⁻¹' b) ≠ ⊤) :=
sorry

lemma metric.bornologous_iff (f : α → β) : coarse_space.bornologous f
  ↔ (∀ (R : ℝ≥0), ∃ (S : ℝ≥0), ∀ x y, dist x y < R → dist (f x) (f y) < S) :=
sorry
