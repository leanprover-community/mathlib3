import measure_theory.l1_space

noncomputable theory
open lattice set filter topological_space
local attribute [instance] classical.prop_decidable

universes u v
variables {α : Type u} {β : Type v} {ι : Type*}
----------------------------------------------------------------------------------------------------
namespace set
/-- Enumerate elements in a countable set.-/
def enumerate {s : set α} (h : countable s) (default : α): ℕ → α :=
assume n, match @encodable.decode s (h.to_encodable) n with
        | (some y) := y
        | (none)   := default
        end

lemma subset_range_enumerate {s : set α} (h : countable s) (default : α) :
   s ⊆ range (enumerate h default) :=
assume x hx, ⟨@encodable.encode s h.to_encodable ⟨x, hx⟩, by simp [enumerate, encodable.encodek]⟩

end set

open set

section enumerate
variables [topological_space β] [separable_space β]

lemma closure_range_enumerate {D : set β} (D_countable : countable D) (D_dense : closure D = univ)
  (default : β) : closure (range (enumerate D_countable default)) = univ :=
dense_of_subset_dense (subset_range_enumerate D_countable default) D_dense

end enumerate -- section

----------------------------------------------------------------------------------------------------
section finite
-- (if p x then f x else g x) has finite range
lemma range_ite_subset' {p : Prop} {f g : α → β} : range (if p then f else g) ⊆ range f ∪ range g :=
begin
  by_cases h : p, {rw if_pos h, exact subset_union_left _ _},
  {rw if_neg h, exact subset_union_right _ _}
end

lemma range_ite_subset {p : α → Prop} {f g : α → β} :
 range (λ x, if p x then f x else g x) ⊆ range f ∪ range g :=
begin
  rw range_subset_iff, intro x, by_cases h : p x,
  simp [if_pos h, mem_union, mem_range_self],
  simp [if_neg h, mem_union, mem_range_self]
end

lemma finite_range_ite {p : α → Prop} {f g : α → β} (hf : finite (range f)) (hg : finite (range g)) :
  finite (range (λ x, if p x then f x else g x)) :=
finite_subset (finite_union hf hg) range_ite_subset

-- constant functions have finite range
lemma finite_range_const {c : β} : finite (range (λ x : α, c)) :=
finite_subset (finite_singleton c) range_const_subset

-- nat.find_greatest has finite range
open nat

lemma range_find_greatest_subset {P : α → ℕ → Prop} {b : ℕ}:
  range (λ x, nat.find_greatest (P x) b) ⊆ ↑(finset.range (b + 1)) :=
by { rw range_subset_iff, assume x, simp [lt_succ_iff, find_greatest_le] }


lemma finite_range_find_greatest {P : α → ℕ → Prop} {b : ℕ} :
  finite (range (λ x, nat.find_greatest (P x) b)) :=
finite_subset (finset.finite_to_set $ finset.range (b + 1))
( by { rw range_subset_iff, assume x, simp [lt_succ_iff, find_greatest_le] } )

lemma find_greatest_eq_zero {P : ℕ → Prop} : ∀ {b}, (∀ n ≤ b, ¬ P n) → nat.find_greatest P b = 0
| 0       h := find_greatest_zero
| (n + 1) h :=
begin
  have := nat.find_greatest_of_not (h (n + 1) (le_refl _)),
  rw this, exact find_greatest_eq_zero (assume k hk, h k (le_trans hk $ nat.le_succ _))
end

lemma find_greatest_of_ne_zero {P : ℕ → Prop} :
  ∀ {b m}, nat.find_greatest P b = m → m ≠ 0  → P m
| 0       m rfl h := by { have := @find_greatest_zero P _, contradiction }
| (b + 1) m rfl h :=
classical.by_cases
  (assume hb : P (b + 1), by { have := find_greatest_eq hb, rw this, exact hb })
  (assume hb : ¬ P (b + 1), find_greatest_of_ne_zero (find_greatest_of_not hb).symm h)

end finite -- section

----------------------------------------------------------------------------------------------------

section measurable
-- open ball is a borel measurable set
lemma is_measurable_ball [metric_space α] {x : α} {ε : ℝ} : is_measurable (metric.ball x ε) :=
  measure_theory.is_measurable_of_is_open metric.is_open_ball
-- singleton set is a borel measurable set
lemma is_measurable_singleton [topological_space α] [t1_space α] {x : α} : @is_measurable α _ ({x}) :=
measure_theory.is_measurable_of_is_closed is_closed_singleton
-- any function from ℕ to α is a measurable function
lemma measurable_from_nat [measurable_space α] {f : ℕ → α} : measurable f :=
assume s hs, show is_measurable {n : ℕ | f n ∈ s}, from trivial

lemma measurable_to_nat [measurable_space α] {f : α → ℕ} :
(∀ k, is_measurable {x | f x = k }) → measurable f :=
begin
  assume h s hs, show is_measurable {x | f x ∈ s},
  have : {x | f x ∈ s} = ⋃ (n ∈ s), {x | f x = n}, { ext, simp },
  rw this, simp [is_measurable.Union, is_measurable.Union_Prop, h]
end

lemma measurable_find_greatest [measurable_space α] {p : ℕ → α → Prop} :
  ∀ {N}, (∀ k ≤ N, is_measurable {x | nat.find_greatest (λ n, p n x) N = k}) → measurable (λ x, nat.find_greatest (λ n, p n x) N)
| 0 := assume h s hs, show is_measurable {x : α | (nat.find_greatest (λ n, p n x) 0) ∈ s},
begin
  by_cases h : 0 ∈ s,
  { convert is_measurable.univ, simp only [nat.find_greatest_zero, h] },
  { convert is_measurable.empty, simp only [nat.find_greatest_zero, h], refl }
end
| (n + 1) := assume h,
begin
  apply measurable_to_nat, assume k, by_cases hk : k ≤ n + 1,
  { exact h k hk },
  { have := is_measurable.empty, rw ← set_of_false at this, convert this, funext, rw eq_false,
    assume h, rw ← h at hk, have := nat.find_greatest_le, contradiction }
end

end measurable -- section

section convergence
#check archimedean.arch

#check exists_nat_one_div_lt


#check dist_self

#check one_div_le_one_div_of_le

lemma inv_pos_of_nat {n : ℕ} : 0 < ((n : ℝ) + 1)⁻¹  :=
  inv_pos $ add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

lemma one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : ℝ) + 1) :=
by { rw one_div_eq_inv, exact inv_pos_of_nat }

lemma nat.cast_add_one_pos (n : ℕ) : 0 < (n : ℝ) + 1 :=
  add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

lemma exists_nat_one_div_lt_and [linear_ordered_field α] [archimedean α]
  {ε₁ ε₂ : α} (hε₁ : ε₁ > 0) (hε₂ : ε₂ > 0) :
  ∃ n : ℕ, 1 / (n + 1: α) < ε₁ ∧ 1 / (n + 1: α) < ε₂ :=
let ⟨n₁, h₁⟩ := exists_nat_one_div_lt hε₁ in
let ⟨n₂, h₂⟩ := exists_nat_one_div_lt hε₂ in
let n        := max n₁ n₂ in
⟨n, ⟨
  calc
    1 / (n + 1 : α) ≤ 1 / (n₁ + 1 : α) : one_div_le_one_div_of_le
    (add_pos_of_nonneg_of_pos n₁.cast_nonneg zero_lt_one)
    (add_le_add_right (nat.cast_le.2 (le_max_left _ _)) _)
    ... < ε₁ : h₁
 ,
  calc
    1 / (n + 1 : α) ≤ 1 / (n₂ + 1 : α) : one_div_le_one_div_of_le
    (add_pos_of_nonneg_of_pos n₂.cast_nonneg zero_lt_one)
    (add_le_add_right (nat.cast_le.2 (le_max_right _ _)) _)
    ... < ε₂ : h₂⟩⟩

#check @metric.mem_closure_iff'

lemma mem_closure_range_iff {α : Type u} [metric_space α] {e : ℕ → α} {a : α} :
  a ∈ closure (range e) ↔ ∀ε>0, ∃ k : ℕ, dist a (e k) < ε :=
iff.intro
( assume ha ε hε,
  let ⟨b, ⟨hb, hab⟩⟩ := metric.mem_closure_iff'.1 ha ε hε in
  let ⟨k, hk⟩ := mem_range.1 hb in
  ⟨k, by { rw hk, exact hab }⟩ )
( assume h, metric.mem_closure_iff'.2 (assume ε hε,
  let ⟨k, hk⟩ := h ε hε in
  ⟨e k, ⟨mem_range.2 ⟨k, rfl⟩, hk⟩⟩) )

lemma mem_closure_range_iff_nat {α : Type u} [metric_space α] {e : ℕ → α} {a : α} :
  a ∈ closure (range e) ↔ ∀n : ℕ, ∃ k : ℕ, dist a (e k) < 1 / ((n : ℝ) + 1) :=
⟨assume ha n,
  mem_closure_range_iff.1 ha (1 / ((n : ℝ) + 1)) one_div_pos_of_nat
,
 assume h, mem_closure_range_iff.2 $ assume ε hε,
  let ⟨n, hn⟩ := exists_nat_one_div_lt hε in
  let ⟨k, hk⟩ := h n  in
  ⟨k, calc
  dist a (e k) < 1 / ((n : ℝ) + 1) : hk
  ... < ε : hn⟩
⟩


end convergence -- section

#check mem_Inter

section other_lemmas

lemma exists_of_forall {p : α → Prop} [inhabited α] : (∀ N, p N) → ∃ N, p N :=
λ h, ⟨default α, h $ default α⟩

#check nat.cast_nonneg

lemma not_mem_Union_iff {A : ℕ → ℕ → set α} {x : α} : (∀ {M k}, x ∉ A M k) ↔ x ∉ ⋃ M k, A M k := by simp

-- @[simp] lemma ennreal.of_real_three : ennreal.of_real 3 = 3 :=
-- sorry


end other_lemmas -- section

namespace measure_theory
open ennreal
variables [measure_space α] [normed_group β] [second_countable_topology β]

local infixr ` →ₛ `:25 := simple_func

lemma simple_func_sequence_tendsto {f : α → β} (hf : measurable f) :
  ∃ (F : ℕ → (α →ₛ β)), ∀ x : α, tendsto (λ n, F n x) at_top (nhds (f x)) ∧
   ∀ n, ∥F n x∥ ≤ ∥f x∥ + ∥f x∥:=
-- enumerate a countable dense subset {e k} of β
let ⟨D, ⟨D_countable, D_dense⟩⟩ := separable_space.exists_countable_closure_eq_univ β in
let e := enumerate D_countable 0 in
let E := range e in
have E_dense : closure E = univ := closure_range_enumerate D_countable D_dense 0,
-- A' N k is a ball of radius 1 / (N + 1) around point e k
let A' (N k : ℕ) : set α :=
  f ⁻¹' (metric.ball (e k) (1 / (N+1 : ℝ)) \ metric.ball 0 (1 / (N+1 : ℝ))) in
let A N := disjointed (A' N) in
have is_measurable_A' : ∀ {N k}, is_measurable (A' N k) :=
  λ N k, hf.preimage $ is_measurable.inter is_measurable_ball $ is_measurable.compl is_measurable_ball,
have is_measurable_A : ∀ {N k}, is_measurable (A N k) :=
 λ N, is_measurable.disjointed $ λ k, is_measurable_A',
have A_subset_A' : ∀ {N k x}, x ∈ A N k → x ∈ A' N k := λ N k, inter_subset_left _ _,
have dist_ek_fx' : ∀ {x N k}, x ∈ A' N k → (dist (e k) (f x) < 1 / (N+1 : ℝ)) :=
 λ x N k, by { rw [dist_comm], simpa using (λ a b, a) },
have dist_ek_fx : ∀ {x N k}, x ∈ A N k → (dist (e k) (f x) < 1 / (N+1 : ℝ)) :=
 λ x N k h, dist_ek_fx' (A_subset_A' h),
have norm_fx' : ∀ {x N k}, x ∈ A' N k → (1 / (N+1 : ℝ)) ≤ ∥f x∥ := λ x N k, by simp [ball_0_eq],
have norm_fx : ∀ {x N k}, x ∈ A N k → (1 / (N+1 : ℝ)) ≤ ∥f x∥ := λ x N k h, norm_fx' (A_subset_A' h),
-- construct the desired sequence of simple functions
let M N x := nat.find_greatest (λ M, x ∈ ⋃ k ≤ N, (A M k)) N in
let k N x := nat.find_greatest (λ k, x ∈ A (M N x) k) N in
let F N x := if x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k then e (k N x) else 0 in
-- prove properties of the construction above
have k_unique : ∀ {M k k' x},  x ∈ A M k ∧ x ∈ A M k' → k = k' := λ M k k' x h,
begin
  by_contradiction k_ne_k',
  have : A M k ∩ A M k' ≠ ∅, rw ne_empty_iff_exists_mem, use x, exact h,
  have : A M k ∩ A M k' = ∅  := disjoint_disjointed' k k' k_ne_k',
  contradiction
end,
have x_mem_Union_k : ∀ {N x}, (x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k) → x ∈ ⋃ k ≤ N, A (M N x) k :=
  λ N x h,
    @nat.find_greatest_spec (λ M, x ∈ ⋃ k ≤ N, (A M k)) _ N (
    let ⟨M, hM⟩ := mem_Union.1 (h) in
    let ⟨hM₁, hM₂⟩ := mem_Union.1 hM in ⟨M, ⟨hM₁, hM₂⟩⟩),
have x_mem_A : ∀ {N x}, (x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k) → x ∈ A (M N x) (k N x) :=
  λ N x h,
    @nat.find_greatest_spec (λ k, x ∈ A (M N x) k) _ N (
    let ⟨k, hk⟩ := mem_Union.1 (x_mem_Union_k h) in
    let ⟨hk₁, hk₂⟩ := mem_Union.1 hk in ⟨k, ⟨hk₁, hk₂⟩⟩),
have x_mem_A' : ∀ {N x}, (x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k) → x ∈ A' (M N x) (k N x) :=
  λ N x h, mem_of_subset_of_mem (inter_subset_left _ _) (x_mem_A h),
-- prove that for all N, (F N) has finite range
have F_finite : ∀ {N}, finite (range (F N)) :=
begin
  assume N, apply finite_range_ite,
  { rw range_comp, apply finite_image, exact finite_range_find_greatest },
  { exact finite_range_const }
end,
-- prove that for all N, (F N) is a measurable function
have F_measurable : ∀ {N}, measurable (F N) :=
begin
  assume N, refine measurable.if _ _ measurable_const,
  -- show `is_measurable {a : α | a ∈ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k}`
  rw set_of_mem_eq, simp [is_measurable.Union, is_measurable.Union_Prop, is_measurable_A],
  -- show `measurable (λ (x : α), e (k N x))`
  apply measurable.comp measurable_from_nat, apply measurable_find_greatest,
  assume k' k'_le_N, by_cases k'_eq_0 : k' = 0,
  -- if k' = 0
  have : {x | k N x = 0} = (-⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k) ∪
                    (⋃ (m ≤ N), A m 0 - ⋃ m' (hmm' : m < m') (hm'N : m' ≤ N) (k ≤ N), A m' k),
  { ext, split,
    { rw [mem_set_of_eq, mem_union_eq, or_iff_not_imp_left, mem_compl_eq, not_not_mem],
      assume k_eq_0 x_mem,
      simp only [not_exists, exists_prop, mem_Union, not_and, sub_eq_diff, mem_diff],
      refine ⟨M N x, ⟨nat.find_greatest_le, ⟨by { rw ← k_eq_0, exact x_mem_A x_mem} , _⟩⟩⟩,
      assume m hMm hmN k k_le_N, have := nat.find_greatest_is_greatest _ m ⟨hMm, hmN⟩,
      { simp only [not_exists, exists_prop, mem_Union, not_and] at this, exact this k k_le_N },
      exact ⟨M N x, ⟨nat.find_greatest_le, x_mem_Union_k x_mem⟩⟩ },
    { simp only [mem_set_of_eq, mem_union_eq, mem_compl_eq],
      by_cases x_mem : (x ∉ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k),
      { intro, apply find_greatest_eq_zero, assume k k_le_N hx,
        have : x ∈ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k,
          { rw [mem_Union], use M N x,
            rw mem_Union, use nat.find_greatest_le,
            rw mem_Union, use k, rw mem_Union, use k_le_N, assumption },
        contradiction },
      { rw not_not_mem at x_mem, assume h, cases h, contradiction,
        simp only [not_exists, exists_prop, mem_Union, not_and, sub_eq_diff, mem_diff] at h,
        rcases h with ⟨m, ⟨m_le_N, ⟨hx, hm⟩⟩⟩,
        by_cases m_lt_M : m < M N x,
        { have := hm (M N x) m_lt_M nat.find_greatest_le (k N x) nat.find_greatest_le,
          have := x_mem_A x_mem,
          contradiction },
        rw not_lt at m_lt_M, by_cases m_gt_M : m > M N x,
        { have := nat.find_greatest_is_greatest _ m ⟨m_gt_M, m_le_N⟩,
          have : x ∈ ⋃ k ≤ N, A m k, { rw mem_Union, use 0, rw mem_Union, use zero_le _, exact hx },
          contradiction,
          use m, split, exact m_le_N, rw mem_Union, use 0, rw mem_Union, use zero_le _, exact hx },
        rw not_lt at m_gt_M, have M_eq_m := le_antisymm m_lt_M m_gt_M,
        rw ← k'_eq_0, exact k_unique ⟨x_mem_A x_mem, by { rw [k'_eq_0, M_eq_m], exact hx }⟩ } } },
  -- end of `have`
  rw [k'_eq_0, this], apply is_measurable.union,
  { apply is_measurable.compl,
    simp [is_measurable.Union, is_measurable.Union_Prop, is_measurable_A] },
  { simp [is_measurable.Union, is_measurable.Union_Prop, is_measurable.diff, is_measurable_A] },
  -- if k' ≠ 0
  have : {x | k N x = k'} = ⋃(m ≤ N), A m k' - ⋃m' (hmm' : m < m') (hm'N : m' ≤ N) (k ≤ N), A m' k,
  { ext,
    split,
    { rw [mem_set_of_eq],
      assume k_eq_k',
      have x_mem : x ∈ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k,
      { have := find_greatest_of_ne_zero k_eq_k' k'_eq_0,
        simp only [mem_Union], use M N x, use nat.find_greatest_le, use k', use k'_le_N,
        assumption },
      simp only [not_exists, exists_prop, mem_Union, not_and, sub_eq_diff, mem_diff],
      refine ⟨M N x, ⟨nat.find_greatest_le, ⟨by { rw ← k_eq_k', exact x_mem_A x_mem} , _⟩⟩⟩,
      assume m hMm hmN k k_le_N, have := nat.find_greatest_is_greatest _ m ⟨hMm, hmN⟩,
      { simp only [not_exists, exists_prop, mem_Union, not_and] at this, exact this k k_le_N },
      exact ⟨M N x, ⟨nat.find_greatest_le, x_mem_Union_k x_mem⟩⟩ },
    { simp only [mem_set_of_eq, mem_union_eq, mem_compl_eq], assume h,
      have x_mem : x ∈ ⋃ (M : ℕ) (H : M ≤ N) (k : ℕ) (H : k ≤ N), A M k,
      { simp only [not_exists, exists_prop, mem_Union, not_and, sub_eq_diff, mem_diff] at h,
        rcases h with ⟨m, ⟨hm, ⟨hx, _⟩⟩⟩,
        simp only [mem_Union], use m, use hm, use k', use k'_le_N, assumption },
      simp only [not_exists, exists_prop, mem_Union, not_and, sub_eq_diff, mem_diff] at h,
      rcases h with ⟨m, ⟨m_le_N, ⟨hx, hm⟩⟩⟩,
      by_cases m_lt_M : m < M N x,
      { have := hm (M N x) m_lt_M nat.find_greatest_le (k N x) nat.find_greatest_le,
        have := x_mem_A x_mem,
        contradiction },
      rw not_lt at m_lt_M, by_cases m_gt_M : m > M N x,
      { have := nat.find_greatest_is_greatest _ m ⟨m_gt_M, m_le_N⟩,
        have : x ∈ ⋃ k ≤ N, A m k :=
          by { rw mem_Union, use k', rw mem_Union, use k'_le_N, exact hx },
        contradiction,
        { use m, split, exact m_le_N, rw mem_Union, use k', rw mem_Union, use k'_le_N, exact hx }},
      rw not_lt at m_gt_M, have M_eq_m := le_antisymm m_lt_M m_gt_M,
      exact k_unique ⟨x_mem_A x_mem, by { rw M_eq_m, exact hx }⟩ } },
  -- end of `have`
  rw this, simp [is_measurable.Union, is_measurable.Union_Prop, is_measurable.diff, is_measurable_A]
end,
-- start of proof
⟨λ N, ⟨F N, λ x, measurable.preimage F_measurable is_measurable_singleton, F_finite⟩,
λ x, ⟨
-- The pointwise convergence part of the theorem
metric.tendsto_at_top.2 $ λ ε hε, classical.by_cases
--first case : f x = 0
( assume fx_eq_0 : f x = 0,
  have x_not_mem_A' : ∀ {M k}, x ∉ A' M k := λ M k,
  begin
    simp only [mem_preimage_eq, fx_eq_0, metric.mem_ball, one_div_eq_inv, norm_zero,
               not_and, not_lt, add_comm, not_le, dist_zero_right, mem_diff],
    assume h, rw add_comm, exact inv_pos_of_nat
  end,
  have x_not_mem_A  : ∀ {M k}, x ∉ A M k :=
    by { assume M k h, have := disjointed_subset h, exact absurd this x_not_mem_A' },
  have F_eq_0 : ∀ {N}, F N x = 0 := λ N, by simp [F, if_neg, mem_Union, x_not_mem_A],
  -- end of `have`
  exists_of_forall $ λ n N hN, show dist (F N x) (f x) < ε,
                                  by {rw [fx_eq_0, F_eq_0, dist_self], exact hε} )
--second case : f x ≠ 0
( assume fx_ne_0 : f x ≠ 0,
  let ⟨N₀, ⟨norm_fx_gt, ε_gt⟩⟩ := exists_nat_one_div_lt_and ((norm_pos_iff _).2 fx_ne_0) hε in
  have x_mem_Union_k_N₀ : x ∈ ⋃ k, A N₀ k :=
    let ⟨k, hk⟩ := mem_closure_range_iff_nat.1 (by { rw E_dense, exact mem_univ (f x) }) N₀ in
    begin
      rw [Union_disjointed, mem_Union], use k,
      rw [mem_preimage_eq], simp, rw [← one_div_eq_inv, add_comm],
      exact ⟨hk , le_of_lt norm_fx_gt⟩
    end,
  let ⟨k₀, x_mem_A⟩ := mem_Union.1 x_mem_Union_k_N₀ in
  let n := max N₀ k₀ in
  have x_mem_Union_Union : ∀ {N} (hN : n ≤ N), x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k := assume N hN,
    mem_Union.2
      ⟨N₀, mem_Union.2
        ⟨le_trans (le_max_left _ _) hN, mem_Union.2
          ⟨k₀, mem_Union.2 ⟨le_trans (le_max_right _ _) hN, x_mem_A⟩⟩⟩⟩,
  have FN_eq : ∀ {N} (hN : n ≤ N), F N x = e (k N x) := assume N hN, if_pos $ x_mem_Union_Union hN,
  -- start of proof
  ⟨n, assume N hN,
  have N₀_le_N : N₀ ≤ N := le_trans (le_max_left _ _) hN,
  have k₀_le_N : k₀ ≤ N := le_trans (le_max_right _ _) hN,
  show dist (F N x) (f x) < ε, from
  calc
    dist (F N x) (f x) = dist (e (k N x)) (f x) : by rw FN_eq hN
    ... < 1 / ((M N x : ℝ) + 1) :
    begin
      have := x_mem_A' (x_mem_Union_Union hN),
      rw [mem_preimage_eq, mem_diff, metric.mem_ball, dist_comm] at this, exact this.1
    end
    ... ≤ 1 / ((N₀ : ℝ) + 1)  :
    @one_div_le_one_div_of_le _ _  ((N₀ : ℝ) + 1) ((M N x : ℝ) + 1) (nat.cast_add_one_pos N₀)
    (add_le_add_right (nat.cast_le.2 (nat.le_find_greatest N₀_le_N
    begin rw mem_Union, use k₀, rw mem_Union, use k₀_le_N, exact x_mem_A end)) 1)
    ... < ε : ε_gt ⟩ ),

-- second part of the theorem
assume N, show ∥F N x∥ ≤ ∥f x∥ + ∥f x∥, from
classical.by_cases
( assume h : x ∈ ⋃ M ≤ N, ⋃ k ≤ N, A M k,
  calc
    ∥F N x∥ = dist (F N x) 0 : by simp
    ... = dist (e (k N x)) 0 : begin simp only [F], rw if_pos h end
    ... ≤ dist (e (k N x)) (f x) + dist (f x) 0 : dist_triangle _ _ _
    ... = dist (e (k N x)) (f x) + ∥f x∥ : by simp
    ... ≤ 1 / ((M N x : ℝ) + 1) + ∥f x∥ :
      le_of_lt $ add_lt_add_right (dist_ek_fx (x_mem_A h)) _
    ... ≤ ∥f x∥ + ∥f x∥ : add_le_add_right (norm_fx (x_mem_A h) ) _)
( assume h : x ∉ ⋃ M ≤ N, ⋃ k ≤ N, A M k,
  have F_eq_0 : F N x = 0 := if_neg h,
  by { simp only [F_eq_0, norm_zero], exact add_nonneg (norm_nonneg _) (norm_nonneg _) } )⟩⟩

lemma simple_func_sequence_tendsto' {f : α → β} (hfm : measurable f)
  (hfi : integrable f) : ∃ (F : ℕ → (α →ₛ β)), (∀n, integrable (F n)) ∧
   tendsto (λ n, ∫⁻ x,  nndist (F n x) (f x)) at_top  (nhds 0) :=
let ⟨F, hF⟩ := simple_func_sequence_tendsto hfm in
let G : ℕ → α → ennreal := λn x, nndist (F n x) (f x) in
let g : α → ennreal := λx, nnnorm (f x) + nnnorm (f x) + nnnorm (f x) in
have hF_meas : ∀ n, measurable (G n) := λ n, measurable.comp measurable_coe $
  measurable_nndist (F n).measurable hfm,
have hg_meas : measurable g := measurable.comp measurable_coe $ measurable_add
  (measurable_add (measurable_nnnorm hfm) (measurable_nnnorm hfm)) (measurable_nnnorm hfm),
have h_bound : ∀ n, ∀ₘ x, G n x ≤ g x := λ n, all_ae_of_all $ λ x, coe_le_coe.2 $
  calc
    nndist (F n x) (f x) ≤ nndist (F n x) 0 + nndist 0 (f x) : nndist_triangle _ _ _
    ... = nnnorm (F n x) + nnnorm (f x) : by simp [nndist_eq_nnnorm]
    ... ≤ nnnorm (f x) + nnnorm (f x) + nnnorm (f x) : by { simp [nnreal.coe_le, (hF x).2] },
have h_finite : lintegral g < ⊤ :=
calc
  (∫⁻ x, nnnorm (f x) + nnnorm (f x) + nnnorm (f x)) =
    (∫⁻ x, nnnorm (f x)) + (∫⁻ x, nnnorm (f x)) + (∫⁻ x, nnnorm (f x)) :
  by rw [lintegral_add, lintegral_add]; simp only [measurable_coe_nnnorm hfm, measurable_add]
    ... < ⊤ : by { simp only [and_self, add_lt_top], exact hfi},
have h_lim : ∀ₘ x, tendsto (λ n, G n x) at_top (nhds 0) := all_ae_of_all $ λ x,
  begin
    apply (@tendsto_coe ℕ at_top (λ n, nndist (F n x) (f x)) 0).2,
    apply (@nnreal.tendsto_coe ℕ at_top (λ n, nndist (F n x) (f x)) 0).1,
    apply tendsto_iff_dist_tendsto_zero.1 (hF x).1
  end,
begin
  use F, split,
  { assume n, exact
    calc
      (∫⁻ a, nnnorm (F n a)) ≤ ∫⁻ a, nnnorm (f a) + nnnorm (f a) :
        lintegral_le_lintegral _ _
          (by { assume a, simp only [coe_add.symm, coe_le_coe], exact (hF a).2 n })
       ... = (∫⁻ a, nnnorm (f a)) + (∫⁻ a, nnnorm (f a)) :
         lintegral_add (measurable_coe_nnnorm hfm) (measurable_coe_nnnorm hfm)
       ... < ⊤ : by simp only [add_lt_top, and_self]; exact hfi },
  convert @dominated_convergence_nn _ _ G (λ a, 0) g
              hF_meas measurable_const hg_meas h_bound h_finite h_lim,
  simp only [lintegral_zero]
end




----------------------------------------------------------------------------------------------------
end measure_theory --namespace
