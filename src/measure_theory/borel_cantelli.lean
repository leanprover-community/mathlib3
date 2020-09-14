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

/- lemma sub_lt_iff {a b c : ennreal} (h : b < a) : a - b < c ↔ a < b + c :=
begin
  cases a; cases b,
  { exact false.elim (ne_of_lt h rfl) },
  { simp },
  { simp only [ennreal.none_eq_top, not_top_lt] at h,
    contradiction },
  cases c,
  { simp only [ennreal.none_eq_top, ennreal.coe_lt_top, iff_true, ennreal.some_eq_coe,
      ennreal.add_top, ←ennreal.coe_sub] },
  { simp only [ennreal.some_eq_coe, ennreal.coe_lt_coe] at *,
    rw [←ennreal.coe_sub, ennreal.coe_lt_coe, nnreal.sub_lt_iff (le_of_lt h), ←ennreal.coe_add,
      ennreal.coe_lt_coe] }
end-/

lemma exists_coe_of_sum_lt_top {α : Type u} {f : α → ennreal} (hf : (∑' i, f i) < ⊤) :
  ∃ g : α → nnreal, (∀ x, f x = g x) ∧ summable g :=
begin
  have : ∀ i, f i < ⊤,
  { contrapose! hf,
    rcases hf with ⟨x, hx⟩,
    rw top_le_iff at hx,
    convert @ennreal.le_tsum _ f x,
    exact hx.symm },
  let g : α → nnreal := λ x, classical.some (ennreal.lt_iff_exists_coe.1 (this x)),
  have hg : ∀ x, f x = g x := λ x, (classical.some_spec (ennreal.lt_iff_exists_coe.1 (this x))).1,
  refine ⟨g, ⟨hg, _⟩⟩,
  simp only [←ennreal.tsum_coe_ne_top_iff_summable, ←hg, ←ennreal.lt_top_iff_ne_top, hf]
end

lemma nnreal.not_lt_zero {a : nnreal} : ¬(a < 0) := by simp

lemma le_tsum {α : Type*} [topological_space α] [ordered_add_comm_monoid α]
  [order_closed_topology α] {β : Type*} {f : β → α} (hf : summable f) (x : β)
  (hx : ∀ y ≠ x, 0 ≤ f y) : f x ≤ ∑' x, f x :=
calc f x = ∑ x in {x}, f x : finset.sum_singleton.symm
... ≤ ∑' x, f x : sum_le_tsum _ (by { convert hx, simp }) hf

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
    rcases not_forall.1 h with ⟨n, hn⟩,
    exact lt_of_lt_of_le (zero_lt_iff_ne_zero.2 hn) (le_tsum hf n (λ y _, nnreal.zero_le)) },
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
  rcases exists_coe_of_sum_lt_top hf with ⟨g, ⟨hg : ∀ x, f x = g x, hg'⟩⟩,
  have : ∀ i, (∑' k, (g (k + i) : ennreal)) = (∑' k, g (k + i) : nnreal),
  { intro i, rw ennreal.coe_tsum (nnreal.summable_shift g hg' _) },
  simp only [hg, ←ennreal.coe_zero, this, ennreal.tendsto_coe],
  exact nnreal.tendsto_sum_add g hg'
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
