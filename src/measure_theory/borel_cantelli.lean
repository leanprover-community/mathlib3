import measure_theory.measure_space tactic

universe u

open measure_theory filter finset
open_locale filter topological_space big_operators

section
variables {α : Type u} [complete_lattice α]

lemma supr_le_eq_supr_add {u : ℕ → α} (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) :=
begin
  apply le_antisymm;
  simp only [supr_le_iff],
  { exact λ i hi, le_Sup ⟨i - n, by { dsimp only [], congr, omega }⟩ },
  { exact λ i, le_Sup ⟨i + n, by simp⟩ }
end

lemma limsup_eq_infi_supr_of_nat' {u : ℕ → α} : limsup at_top u = ⨅n:ℕ, ⨆i, u (i + n) :=
by simp only [limsup_eq_infi_supr_of_nat, supr_le_eq_supr_add]

end

section

lemma nnreal.sub_lt_iff {a b c : nnreal} (h : b ≤ a) : a - b < c ↔ a < b + c :=
by simp only [←nnreal.coe_lt_coe, nnreal.coe_sub h, nnreal.coe_add, sub_lt_iff_lt_add']

lemma lt_top_of_lt_tsum_lt_top {α : Type*} {f : α → ennreal} (hf : (∑' i, f i) < ⊤) :
  ∀ x, f x < ⊤ :=
begin
  contrapose! hf,
  rcases hf with ⟨x, hx⟩,
  exact le_trans hx (ennreal.le_tsum _)
end

lemma to_nnreal_of_sum_lt_top {α : Type*} {f : α → ennreal} (hf : (∑' i, f i) < ⊤) (x : α) :
  (((ennreal.to_nnreal ∘ f) x : nnreal) : ennreal) = f x :=
ennreal.coe_to_nnreal $ ennreal.lt_top_iff_ne_top.1 $ lt_top_of_lt_tsum_lt_top hf _

lemma summable_to_nnreal {α : Type u} {f : α → ennreal} (hf : (∑' i, f i) < ⊤) :
  summable (ennreal.to_nnreal ∘ f) :=
by simpa only [←ennreal.tsum_coe_ne_top_iff_summable, ←ennreal.lt_top_iff_ne_top,
  to_nnreal_of_sum_lt_top hf] using hf

lemma nnreal.not_lt_zero {a : nnreal} : ¬(a < 0) := by simp

lemma le_has_sum {α : Type*} [topological_space α] [ordered_add_comm_monoid α]
  [order_closed_topology α] {β : Type*} {f : β → α} {a : α} (hf : has_sum f a) (x : β)
  (hx : ∀ y ≠ x, 0 ≤ f y) : f x ≤ a :=
calc f x = ∑ x in {x}, f x : finset.sum_singleton.symm
... ≤ a : sum_le_has_sum _ (by { convert hx, simp }) hf

lemma le_has_sum' {α : Type*} [topological_space α] [canonically_ordered_add_monoid α]
  [order_closed_topology α] {β : Type*} {f : β → α} {a : α} (hf : has_sum f a) (x : β) :
  f x ≤ a :=
le_has_sum hf x $ λ _ _, zero_le _

lemma le_tsum {α : Type*} [topological_space α] [ordered_add_comm_monoid α]
  [order_closed_topology α] {β : Type*} {f : β → α} (hf : summable f) (x : β)
  (hx : ∀ y ≠ x, 0 ≤ f y) : f x ≤ ∑' x, f x :=
le_has_sum (summable.has_sum hf) x hx

lemma le_tsum' {α : Type*} [topological_space α] [canonically_ordered_add_monoid α]
  [order_closed_topology α] {β : Type*} {f : β → α} (hf : summable f) (x : β) :
  f x ≤ ∑' x, f x :=
le_tsum hf x $ λ _ _, zero_le _

lemma nnreal.sub_eq_iff {a b c : nnreal} (h : b ≤ a) : a - b = c ↔ a = c + b :=
by rw [←nnreal.eq_iff, nnreal.coe_sub h, ←nnreal.eq_iff, nnreal.coe_add, sub_eq_iff_eq_add]

lemma nnreal.summable_shift (f : ℕ → nnreal) (hf : summable f) (k : ℕ) :
  summable (λ i, f (i + k)) :=
nnreal.summable_comp_injective hf $ add_left_injective k

lemma nnreal.sum_add_tsum_nat_add {f : ℕ → nnreal} (k : ℕ) (hf : summable f) :
  (∑' i, f i) = (∑ i in range k, f i) + ∑' i, f (i + k) :=
by rw [←nnreal.coe_eq, nnreal.coe_tsum, nnreal.coe_add, nnreal.coe_sum, nnreal.coe_tsum,
  sum_add_tsum_nat_add k (nnreal.summable_coe.2 hf)]

lemma nnreal.zero_le {a : nnreal} : 0 ≤ a := a.2

lemma has_sum_zero_iff {α : Type*} {β : Type*} [topological_space α]
  [canonically_ordered_add_monoid α] [order_closed_topology α] {f : β → α} :
  has_sum f 0 ↔ ∀ x, f x = 0 :=
begin
  split,
  { contrapose!,
    exact λ ⟨x, hx⟩ h, irrefl _ (lt_of_lt_of_le (zero_lt_iff_ne_zero.2 hx) (le_has_sum' h x)) },
  { intro h,
    convert has_sum_zero,
    exact funext h }
end

lemma tsum_eq_zero_iff {α : Type*} {β : Type*} [topological_space α]
  [canonically_ordered_add_monoid α] [order_closed_topology α] {f : β → α} (hf : summable f) :
  (∑' i, f i) = 0 ↔ ∀ x, f x = 0 :=
by rw [←has_sum_zero_iff, hf.has_sum_iff]

lemma nnreal.tendsto_sum_add
  (f : ℕ → nnreal) (hf : summable f) : tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0) :=
begin
  by_cases h : ∀ i, f i = 0,
  { simp only [h, tsum_zero],
    exact tendsto_const_nhds },
  refine tendsto_order.2 ⟨λ a ha, false.elim (nnreal.not_lt_zero ha), λ a ha, _⟩,
  have hf' := summable.has_sum hf,
  rw [nnreal.has_sum_iff_tendsto_nat, tendsto_order] at hf',
  rcases hf' with ⟨hf', -⟩,
  simp only [ge_iff_le, eventually_at_top] at ⊢ hf',
  have tsum_sub_lt : (∑' i, f i) - a < ∑' i, f i,
  { refine nnreal.sub_lt_self _ ha,
    contrapose! h,
    simpa only [←tsum_eq_zero_iff hf, le_zero_iff] using h },
  rcases hf' _ tsum_sub_lt with ⟨n, hn⟩,
  refine ⟨n, λ m hm, _⟩,
  specialize hn m hm,
  by_cases h : a ≤ ∑' i, f i,
  { have sum_le_tsum : ∑ i in range m, f i ≤ ∑' i, f i,
    { exact sum_le_tsum _ (λ _ _, nnreal.zero_le) hf },
    rw [nnreal.sub_lt_iff h, add_comm, ←nnreal.sub_lt_iff sum_le_tsum] at hn,
    convert hn,
    symmetry,
    rw [nnreal.sub_eq_iff sum_le_tsum, add_comm, nnreal.sum_add_tsum_nat_add _ hf] },
  { push_neg at h,
    refine lt_of_le_of_lt _ h,
    exact tsum_le_tsum_of_inj (λ k, k + m) (add_left_injective m) (λ _ _, nnreal.zero_le)
      (λ _, le_refl _) (nnreal.summable_shift _ hf _) hf }
end

lemma ennreal.tendsto_sum_add (f : ℕ → ennreal) (hf : (∑' i, f i) < ⊤) :
  tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0) :=
begin
  have : ∀ i, (∑' k, (((ennreal.to_nnreal ∘ f) (k + i) : nnreal) : ennreal)) =
    (∑' k, (ennreal.to_nnreal ∘ f) (k + i) : nnreal) :=
    λ i, (ennreal.coe_tsum (nnreal.summable_shift _ (summable_to_nnreal hf) _)).symm,
  simp only [λ x, (to_nnreal_of_sum_lt_top hf x).symm, ←ennreal.coe_zero,
    this, ennreal.tendsto_coe] { single_pass := tt },
  exact nnreal.tendsto_sum_add _ (summable_to_nnreal hf)
end

end

section

variables {α : Type u} [measurable_space α] {μ : measure α}

/-- The Borel-Cantelli lemma. -/
lemma measure_limsup_eq_zero {s : ℕ → set α} (hs : ∀ i, is_measurable (s i))
  (hs' : (∑' i, μ (s i)) < ⊤) : μ (limsup at_top s) = 0 :=
begin
  rw limsup_eq_infi_supr_of_nat',

  refine tendsto_nhds_unique
    (tendsto_measure_Inter (λ i, is_measurable.Union (λ b, hs (b + i))) _
      ⟨0, lt_of_le_of_lt (measure_Union_le s) hs'⟩)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (ennreal.tendsto_sum_add (μ ∘ s) hs')
      (eventually_of_forall (by simp only [forall_const, zero_le]))
      (eventually_of_forall (λ i, measure_Union_le _))),

  intros n m hnm x hx,
  simp only [set.mem_Union] at hx ⊢,
  rcases hx with ⟨i, hi⟩,
  use i + (m - n),
  convert hi using 2,
  omega
end

end
