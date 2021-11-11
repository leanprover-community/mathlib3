import data.finset
import data.nat.digits
import data.matrix.notation
import combinatorics.pigeonhole
import .mathlib
import analysis.asymptotics.asymptotics
import analysis.inner_product_space.basic
import analysis.inner_product_space.pi_L2

section
variables {α : Type*} [add_comm_monoid α] (s : set α)

def has_three_ap := ∃ x y z ∈ s, x ≠ y ∧ x + z = y + y

lemma has_three_ap_mono {t₁ t₂ : set α} : t₁ ⊆ t₂ → has_three_ap t₁ → has_three_ap t₂ :=
λ h ⟨x, y, z, hx, hy, hz, nxy, e⟩, ⟨x, y, z, h hx, h hy, h hz, nxy, e⟩

lemma not_has_three_ap_iff :
  ¬has_three_ap s ↔ ∀ x y z ∈ s, x + z = y + y → x = y :=
by simp only [has_three_ap, not_exists, not_and, ne.def, not_imp_not]

@[simp] lemma empty_has_no_three_ap : ¬has_three_ap (∅ : set α) :=
by simp [not_has_three_ap_iff]

instance {α : Type*} [decidable_eq α] [add_comm_monoid α] {s : finset α} :
  decidable (has_three_ap (s : set α)) :=
decidable_of_iff (∃ (x ∈ s) (y ∈ s) (z ∈ s), x ≠ y ∧ x + z = y + y) (by simp [has_three_ap])
end

open finset

def roth_number (N : ℕ) : ℕ :=
nat.find_greatest (λ m, ∃ s ⊆ range N, s.card = m ∧ ¬ has_three_ap (s : set ℕ)) N

lemma roth_number_spec (N : ℕ) :
  ∃ A ⊆ range N, A.card = roth_number N ∧ ¬ has_three_ap (A : set ℕ) :=
@nat.find_greatest_spec (λ m, ∃ s ⊆ range N, s.card = m ∧ ¬ has_three_ap (s : set ℕ)) _ N
  ⟨0, nat.zero_le _, ∅, by simp⟩

lemma roth_number_le (N : ℕ) : roth_number N ≤ N := nat.find_greatest_le

lemma roth_number_monotone : monotone roth_number :=
monotone_nat_of_le_succ $ λ n,
begin
  obtain ⟨A, hA₁, hA₂, hA₃⟩ := roth_number_spec n,
  refine nat.le_find_greatest ((roth_number_le _).trans (nat.le_succ _)) ⟨A, _, hA₂, hA₃⟩,
  exact hA₁.trans (by simp),
end

lemma le_roth_number_of_not_has_three_ap {N k : ℕ} (A : finset ℕ) (hA : A ⊆ range N)
  (hA' : ¬ has_three_ap (A : set ℕ)) (hA'' : A.card = k) :
  k ≤ roth_number N :=
nat.le_find_greatest (by simpa [←hA''] using card_le_of_subset hA) ⟨A, hA, hA'', hA'⟩

lemma roth_number_subadditive (N M : ℕ) :
  roth_number (N + M) ≤ roth_number N + roth_number M :=
begin
  obtain ⟨A, hA, hA', hA''⟩ := roth_number_spec (N + M),
  let A₁ := A ∩ range N,
  let A₂ := (A \ range N).image (λ i, i - N),
  have hA₂ : A₂ ⊆ range M,
  { refine (image_subset_image (sdiff_subset_sdiff hA (subset.refl _))).trans _,
    simp only [subset_iff, mem_image, and_imp, exists_prop, forall_exists_index, mem_sdiff,
      mem_range, not_lt],
    rintro x n hn hN rfl,
    rwa tsub_lt_iff_left hN },
  have hA₁A : (A₁ : set ℕ) ⊆ A,
  { rw finset.coe_subset,
    apply inter_subset_left },
  have hA₁'' : ¬has_three_ap (A₁ : set ℕ) := λ i, hA'' (has_three_ap_mono hA₁A i),
  have hA₂'' : ¬has_three_ap (A₂ : set ℕ),
  { rw not_has_three_ap_iff at ⊢ hA'',
    simp only [and_imp, forall_exists_index, set.mem_image, set.mem_diff, mem_range, mem_coe,
      not_lt, coe_image, coe_sdiff],
    rintro _ _ _ x hx hx₁ rfl y hy hy₁ rfl z hz hz₁ rfl h,
    rw tsub_left_inj hx₁ hy₁,
    rw [←nat.add_sub_assoc hz₁, ←nat.add_sub_assoc hy₁, ←nat.sub_add_comm hx₁,
      ←nat.sub_add_comm hy₁, tsub_tsub, tsub_tsub,
      tsub_left_inj (add_le_add hx₁ hz₁) (add_le_add hy₁ hy₁)] at h,
    apply hA'' _ _ _ hx hy hz h },
  have Asplit : A₁.card + A₂.card = A.card,
  { rw [card_image_of_inj_on, add_comm, ←card_disjoint_union (disjoint_sdiff_inter _ _),
      sdiff_union_inter],
    simp only [set.inj_on, set.mem_diff, mem_coe, mem_sdiff, mem_range, not_lt, and_imp],
    intros x₁ hx₁ hx₁' x₂ hx₂ hx₂' i,
    rwa tsub_left_inj hx₁' hx₂' at i },
  have : A₁.card ≤ _ :=
    le_roth_number_of_not_has_three_ap _ (inter_subset_right A (range N)) hA₁'' rfl,
  rw [←hA', ←Asplit],
  exact add_le_add ‹_› (le_roth_number_of_not_has_three_ap _ hA₂ hA₂'' rfl),
end

open asymptotics filter

lemma trivial_roth_bound' : is_O_with 1 (λ N, (roth_number N : ℝ)) (λ N, (N : ℝ)) at_top :=
is_O_with.of_bound $
 by simpa only [one_mul, real.norm_coe_nat, nat.cast_le] using eventually_of_forall roth_number_le

lemma trivial_roth_bound : is_O (λ N, (roth_number N : ℝ)) (λ N, (N : ℝ)) at_top :=
is_O_iff_is_O_with.2 ⟨1, trivial_roth_bound'⟩

section explicit_values

lemma roth_number_upper_bound {N M : ℕ}
  (h : ∀ x ∈ powerset_len M (range N), has_three_ap ((x : finset ℕ) : set ℕ)) :
  roth_number N < M :=
begin
  obtain ⟨A, hA₁, hA₂, hA₃⟩ := roth_number_spec N,
  rw [←hA₂, ←not_le],
  intro h₁,
  obtain ⟨B, BA, rfl⟩ := exists_smaller_set A M h₁,
  have : ¬has_three_ap (B : set ℕ) := λ i, hA₃ (has_three_ap_mono BA i),
  apply hA₃ (has_three_ap_mono BA (h _ _)),
  rw mem_powerset_len,
  exact ⟨BA.trans hA₁, rfl⟩,
end

lemma has_three_ap_iff {s : finset ℕ} :
  (∃ (x ∈ s) (y ∈ s), x < y ∧ y + (y - x) ∈ s) ↔ has_three_ap (s : set ℕ) :=
begin
  simp only [has_three_ap, exists_prop, mem_coe, exists_and_distrib_left, ne.def],
  split,
  { rintro ⟨x, hx, y, xy, hy, hz⟩,
    refine ⟨x, y, xy.ne, _, hz, hy, hx, _⟩,
    rw [←nat.add_sub_assoc xy.le, ←nat.add_sub_assoc (le_add_right xy.le),
      nat.add_sub_cancel_left] },
  { rintro ⟨x, y, xy, z, hz, hy, hx, e⟩,
    cases lt_or_gt_of_ne xy,
    { refine ⟨x, hx, y, h, hy, _⟩,
      rwa [←nat.add_sub_assoc h.le, ←e, nat.add_sub_cancel_left] },
    { have zy : z < y,
      { rwa [←add_lt_add_iff_right y, ←e, add_comm, add_lt_add_iff_right] },
      refine ⟨z, hz, y, zy, hy, _⟩,
      rwa [←nat.add_sub_assoc zy.le, ←e, nat.add_sub_cancel] } }
end

def has_three_ap_nat_dec {s : finset ℕ} : decidable (has_three_ap (s : set ℕ)) :=
decidable_of_iff _ has_three_ap_iff

local attribute [instance] has_three_ap_nat_dec

@[simp] lemma roth_number_zero : roth_number 0 = 0 := rfl
@[simp] lemma roth_number_one : roth_number 1 = 1 := rfl
@[simp] lemma roth_number_two : roth_number 2 = 2 := rfl
@[simp] lemma roth_number_three : roth_number 3 = 2 := rfl
@[simp] lemma roth_number_four : roth_number 4 = 3 := rfl
@[simp] lemma roth_number_five : roth_number 5 = 4 := rfl
@[simp] lemma roth_number_six : roth_number 6 = 4 := rfl
@[simp] lemma roth_number_seven : roth_number 7 = 4 := rfl
@[simp] lemma roth_number_eight : roth_number 8 = 4 := rfl
@[simp] lemma roth_number_nine : roth_number 9 = 5 := rfl
@[simp] lemma roth_number_ten : roth_number 10 = 5 := dec_trivial
@[simp] lemma roth_number_eleven : roth_number 11 = 6 :=
begin
  apply le_antisymm,
  { simpa using roth_number_subadditive 3 8 },
  { apply le_roth_number_of_not_has_three_ap {0,1,3,7,8,10},
    { simp [subset_iff] },
    { dec_trivial },
    { simp }, },
end

@[simp] lemma roth_number_twelve : roth_number 12 = 6 :=
begin
  apply le_antisymm,
  { rw ←nat.lt_succ_iff,
    apply roth_number_upper_bound,
    dec_trivial },
  simpa using roth_number_monotone (show 11 ≤ 12, by norm_num),
end

@[simp] lemma roth_number_thirteen : roth_number 13 = 7 :=
begin
  apply le_antisymm,
  { simpa using roth_number_subadditive 12 1 },
  apply le_roth_number_of_not_has_three_ap {0,1,3,4,9,10,12},
  { simp [subset_iff] },
  { dec_trivial },
  { simp },
end

@[simp] lemma roth_number_fourteen : roth_number 14 = 8 :=
begin
  apply le_antisymm,
  { simpa using roth_number_subadditive 12 2 },
  apply le_roth_number_of_not_has_three_ap {0,1,3,4,9,10,12,13}, -- unique example
  { simp [subset_iff] },
  { dec_trivial },
  { simp },
end

lemma roth_number_dec_upper_bound {N M : ℕ}
  (h₂ : roth_number N ≤ M)
  (h : ∀ s ∈ (powerset_len M (range N)).filter (λ (s : finset ℕ), ¬has_three_ap (s : set ℕ)),
          ∃ z ∈ s, N ≤ z + z ∧ z + z - N ∈ s) :
  roth_number (N+1) ≤ M :=
begin
  apply nat.le_of_lt_succ,
  change roth_number (N+1) < M.succ,
  apply roth_number_upper_bound,
  simp only [range_succ, powerset_len_succ_insert not_mem_range_self, mem_union, mem_image,
    or_imp_distrib, forall_and_distrib, and_imp, coe_insert, forall_exists_index,
    forall_apply_eq_imp_iff₂],
  split,
  { simp only [mem_powerset_len, and_imp],
    rintro x hx₁ hx₂,
    by_contra,
    rw ←not_lt at h₂,
    apply h₂ (le_roth_number_of_not_has_three_ap _ hx₁ h hx₂) },
  intros s hs,
  by_cases hs₁ : has_three_ap (s : set ℕ),
  { apply has_three_ap_mono (set.subset_insert _ _) hs₁ },
  simp only [and_imp, exists_prop, mem_filter, exists_and_distrib_left] at h,
  obtain ⟨x, hx₁, hx₂, hx₃⟩ := h s hs hs₁,
  refine ⟨x + x - N, x, N, or.inr hx₃, or.inr hx₂, or.inl rfl, _, nat.sub_add_cancel hx₁⟩,
  simp only [mem_powerset_len] at hs,
  rw [ne.def, nat.sub_eq_iff_eq_add hx₁, add_right_inj],
  apply (mem_range.1 (hs.1 hx₂)).ne,
end

-- @[simp] lemma roth_number_fifteen : roth_number 15 = 8 :=
-- begin
--   apply le_antisymm,
--   { refine roth_number_dec_upper_bound (by simp) _,
--     dec_trivial },
--   simpa using roth_number_monotone (show 14 ≤ 15, by norm_num),
--   -- dec_trivial,
-- end
-- @[simp] lemma roth_number_sixteen : roth_number 16 = 8 := sorry
-- @[simp] lemma roth_number_seventeen : roth_number 17 = 8 := sorry
-- @[simp] lemma roth_number_eighteen : roth_number 18 = 8 :=
-- begin
--   apply le_antisymm,
--   { refine roth_number_dec_upper_bound (by simp) _,
--     dec_trivial
--     },
--   simpa using roth_number_monotone (show 14 ≤ 18, by norm_num),
--   -- dec_trivial,
-- end

-- lemma roth_number_nineteen_le : roth_number 19 ≤ 8 :=
-- begin

-- end

-- @[simp] lemma roth_number_nineteen : roth_number 19 = 8 :=
-- begin
--   apply le_antisymm,
--   { rw ←nat.lt_succ_iff,
--     apply roth_number_upper_bound,

--   },
--   simpa using roth_number_monotone (show 14 ≤ 19, by norm_num)
-- end

end explicit_values

namespace behrend

open_locale big_operators

def sphere (n d : ℕ) : finset (fin n → ℕ) :=
fintype.pi_finset (λ _, range d)

lemma mem_sphere {n d : ℕ} (x : fin n → ℕ) : x ∈ sphere n d ↔ ∀ i, x i < d := by simp [sphere]

lemma bound_of_mem_sphere {n d : ℕ} {x : fin n → ℕ} (hx : x ∈ sphere n d) : ∀ i, x i < d :=
(mem_sphere _).1 hx

def sphere_slice (n d k : ℕ) : finset (fin n → ℕ) :=
(sphere n d).filter (λ x, ∑ i, x i^2 = k)

lemma sphere_slice_zero {n d : ℕ} : sphere_slice n d 0 ⊆ {λ _, 0} :=
begin
  intros x hx,
  simp only [sphere_slice, nat.succ_pos', sum_eq_zero_iff, mem_filter, mem_univ, forall_true_left,
    pow_eq_zero_iff] at hx,
  simp only [mem_singleton, function.funext_iff],
  apply hx.2
end

def from_digits {n : ℕ} (d : ℕ) (a : fin n → ℕ) : ℕ :=
∑ i, a i * d^(i : ℕ)

@[simp] lemma from_digits_zero (d : ℕ) (a : fin 0 → ℕ) : from_digits d a = 0 :=
by simp [from_digits]

lemma from_digits_succ {n d : ℕ} (a : fin (n+1) → ℕ) :
  from_digits d a = a 0 + (∑ (x : fin n), a x.succ * d ^ (x : ℕ)) * d :=
by simp [from_digits, fin.sum_univ_succ, pow_succ', ←mul_assoc, ←sum_mul]

lemma from_digits_succ' {n d : ℕ} (a : fin (n+1) → ℕ) :
  from_digits d a = a 0 + (from_digits d (a ∘ fin.succ)) * d :=
from_digits_succ _

lemma finset.sum_mod {α : Type*} (s : finset α) {m : ℕ} (f : α → ℕ) :
  (∑ i in s, f i) % m = (∑ i in s, (f i % m)) % m :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simp },
  rw [sum_insert hi, sum_insert hi, nat.add_mod, ih, nat.add_mod],
  simp,
end

lemma sphere_to_nat_mod {n d : ℕ} (a : fin n.succ → ℕ) :
  from_digits d a % d = a 0 % d :=
by rw [from_digits_succ, nat.add_mul_mod_self_right]

lemma sphere_to_nat_eq_iff {n d : ℕ} {x₁ x₂ : fin n.succ → ℕ}
  (hx₁ : ∀ i, x₁ i < d) (hx₂ : ∀ i, x₂ i < d) :
  from_digits d x₁ = from_digits d x₂ ↔
    x₁ 0 = x₂ 0 ∧ from_digits d (x₁ ∘ fin.succ) = from_digits d (x₂ ∘ fin.succ) :=
begin
  split,
  { intro h,
    have : from_digits d x₁ % d = from_digits d x₂ % d,
    { rw h },
    simp only [sphere_to_nat_mod, nat.mod_eq_of_lt (hx₁ _), nat.mod_eq_of_lt (hx₂ _)] at this,
    refine ⟨this, _⟩,
    rw [from_digits_succ, from_digits_succ, this, add_right_inj, mul_eq_mul_right_iff] at h,
    apply or.resolve_right h,
    apply (lt_of_le_of_lt (nat.zero_le _) (hx₁ 0)).ne' },
  rintro ⟨h₁, h₂⟩,
  rw [from_digits_succ', from_digits_succ', h₁, h₂],
end

lemma weird_thing : ∀ {d : ℕ}, d ≤ 2 * d - 1
| 0 := by simp
| (n+1) := by simp [mul_add, two_mul]

lemma sphere_to_nat_inj_on {n d : ℕ} :
  set.inj_on (from_digits d) {x : fin n → ℕ | ∀ i, x i < d} :=
begin
  simp only [set.inj_on, set.mem_set_of_eq],
  intros x₁ hx₁ x₂ hx₂ h,
  induction n with n ih,
  { simp },
  ext i,
  have x := (sphere_to_nat_eq_iff hx₁ hx₂).1 h,
  refine fin.cases x.1 (function.funext_iff.1 (ih (λ _, _) (λ _, _) x.2)) i,
  { exact hx₁ _ },
  { exact hx₂ _ },
end

lemma from_digits_monotone {n : ℕ} (d : ℕ) :
  monotone (from_digits d : (fin n → ℕ) → ℕ) :=
begin
  intros x₁ x₂ h,
  induction n with n ih,
  { simp },
  rw [from_digits_succ', from_digits_succ'],
  exact add_le_add (h 0) (nat.mul_le_mul_right d (ih (λ i, h i.succ))),
end

lemma from_digits_two_add {n d : ℕ} {x y : fin n → ℕ}
  (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) :
  from_digits (2 * d - 1) (x + y) = from_digits (2 * d - 1) x + from_digits (2 * d - 1) y :=
begin
  induction n with n ih,
  { simp [from_digits_zero] },
  simp only [from_digits_succ', pi.add_apply, add_add_add_comm, add_right_inj, ←add_mul,
    ←@ih (x ∘ fin.succ) (y ∘ fin.succ) (λ _, hx _) (λ _, hy _)],
  refl,
end

-- lemma sum_mul_sq_le_sq_mul_sq' {α : Type*} (s : finset α) (f g : α → ℝ)  :
--   (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * (∑ i in s, (g i)^2) :=
-- begin
--   simp only [←finset.sum_finset_coe _ s, pow_two],
--   exact real_inner_mul_inner_self_le (show euclidean_space ℝ s, from f ∘ coe)
--     (show euclidean_space ℝ s, from g ∘ coe),
-- end

-- theorem inner_eq_norm_mul_iff_real {F : Type u_3} [inner_product_space ℝ F] {x y : F} :
-- inner x y = ∥x∥ * ∥y∥ ↔ ∥y∥ • x = ∥x∥ • y

lemma sphere_strictly_convex {F : Type*} [inner_product_space ℝ F] {x y : F}
  (h : ∥x∥ = ∥y∥) (hx : x ≠ 0) (hxy : x ≠ y) : ∥(1/2 : ℝ) • (x + y)∥ < ∥x∥ :=
begin
  have := @inner_eq_norm_mul_iff_real _ _ x y,
  apply lt_of_pow_lt_pow 2 (norm_nonneg _) _,
  rw [norm_smul, mul_pow, norm_add_sq_real, h, add_right_comm, ←two_mul, ←mul_add, ←mul_assoc],
  suffices : inner x y < ∥y∥^2,
  { norm_num,
    linarith },
  apply lt_of_le_of_ne,
  { simpa [h, sq] using real_inner_le_norm x y },
  rw h at this,
  simp only [←sq] at this,
  rw [ne.def, this],
  refine (smul_right_injective _ _).ne hxy,
  rw ←h,
  simpa [←h] using hx,
end

lemma slice_norm {n d k : ℕ} {x : fin n → ℕ} (hx : x ∈ sphere_slice n d k) :
  @has_norm.norm (euclidean_space ℝ (fin n)) _ (coe ∘ x : fin n → ℝ) =
  real.sqrt k :=
begin
  rw pi_Lp.norm_eq_of_L2,
  simp only [real.norm_coe_nat, function.comp_app, ←nat.cast_pow, ←nat.cast_sum],
  congr' 2,
  simp only [sphere_slice, mem_filter] at hx,
  apply hx.2
end

lemma not_has_three_ap_slice (n d : ℕ) {k : ℕ} :
  ¬has_three_ap (sphere_slice n d k : set (fin n → ℕ)) :=
begin
  simp only [has_three_ap, not_exists, exists_prop, not_and, mem_coe, exists_and_distrib_left,
    ne.def],
  intros x y xy z hz hy hx i,
  rcases nat.eq_zero_or_pos k with rfl | hk,
  { apply xy,
    rw mem_singleton.1 (sphere_slice_zero hx),
    rw mem_singleton.1 (sphere_slice_zero hy) },
  let x' : euclidean_space ℝ (fin n) := (coe ∘ x : fin n → ℝ),
  let y' : euclidean_space ℝ (fin n) := (coe ∘ y : fin n → ℝ),
  let z' : euclidean_space ℝ (fin n) := (coe ∘ z : fin n → ℝ),
  have : x' + z' = y' + y',
  { simpa [function.funext_iff, ←nat.cast_add] using i },
  have nxy : x' ≠ y',
  { simpa [function.funext_iff] using xy },
  have nxz : x' ≠ z',
  { intro t,
    apply nxy,
    rw [←t, ←two_smul ℝ x', ←two_smul ℝ y'] at this,
    exact smul_right_injective _ (by norm_num) this },
  have yeq : (1 / 2 : ℝ) • (x' + z') = y',
  { rw [one_div, inv_smul_eq_iff₀ (show (2 : ℝ) ≠ 0, by norm_num)],
    simp only [function.funext_iff, pi.add_apply] at i,
    ext j,
    simp only [algebra.id.smul_eq_mul, pi.add_apply, pi.smul_apply, ←nat.cast_add, two_mul,
      nat.cast_inj, i] },
  have xz : ∥x'∥ = ∥z'∥,
  { simp only [slice_norm hx, slice_norm hz] },
  have i₂ := @sphere_strictly_convex (euclidean_space ℝ (fin n)) _ x' z' xz _ nxz,
  { rw [yeq, slice_norm hx, slice_norm hy] at i₂,
    simpa using i₂ },
  suffices : ∥x'∥ ≠ 0,
  { simpa using this },
  rw slice_norm hx,
  simp [hk.ne'],
end

lemma sum_bound {n d : ℕ} {x y : fin n → ℕ} (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) :
  ∀ i, (x + y) i < 2 * d - 1 :=
begin
  intro i,
  rw [←nat.pred_eq_sub_one, nat.lt_pred_iff, nat.lt_iff_add_one_le, nat.succ_eq_add_one,
    pi.add_apply, add_right_comm _ (y i), add_assoc, two_mul],
  apply add_le_add (nat.succ_le_of_lt (hx i)) (nat.succ_le_of_lt (hy i))
end

lemma not_has_three_ap_image_slice {n d k : ℕ} :
  ¬has_three_ap ((finset.image (from_digits (2 * d - 1)) (sphere_slice n d k)) : set ℕ) :=
begin
  rw not_has_three_ap_iff,
  simp only [and_imp, forall_exists_index, set.mem_image, mem_coe, coe_image],
  rintro _ _ _ x hx rfl y hy rfl z hz rfl,
  have hx' : ∀ i, x i < d := bound_of_mem_sphere (mem_filter.1 hx).1,
  have hy' : ∀ i, y i < d := bound_of_mem_sphere (mem_filter.1 hy).1,
  have hz' : ∀ i, z i < d := bound_of_mem_sphere (mem_filter.1 hz).1,
  rw [←from_digits_two_add hx' hz', ←from_digits_two_add hy' hy'],
  rintro (t : from_digits (2 * d - 1) (x + z) = from_digits (2 * d - 1) (y + y)),
  rw sphere_to_nat_inj_on.eq_iff (λ i, (hx' i).trans_le weird_thing)
    (λ i, (hy' i).trans_le weird_thing),
  rw sphere_to_nat_inj_on.eq_iff (sum_bound hx' hz') (sum_bound hy' hy') at t,
  change x + z = y + y at t,
  change x = y,
  have i := not_has_three_ap_slice n d,
  simp only [not_has_three_ap_iff] at i,
  apply i _ _ _ hx hy hz t,
end

@[simp] lemma sphere_size {n d : ℕ} : (sphere n d).card = d ^ n :=
by simp [sphere]

lemma sum_squares_bound_of_le {n d : ℕ} :
  ∀ (x : fin n → ℕ), x ∈ sphere n d → (∑ (i : fin n), (x i)^2 ≤ n * (d - 1)^2) :=
begin
  intros x hx,
  simp only [mem_sphere] at hx,
  have : ∀ i, x i^2 ≤ (d - 1)^2,
  { intro i,
    apply nat.pow_le_pow_of_le_left,
    apply nat.le_pred_of_lt (hx i) },
  apply (finset.sum_le_of_forall_le univ _ _ (λ i _, this i)).trans,
  simp,
end

lemma le_of_mem_sphere {n d : ℕ} : ∀ x ∈ sphere n d, x ≤ (λ i, d - 1) :=
λ x hx i, nat.le_pred_of_lt (bound_of_mem_sphere hx i)

lemma from_digits_le_of_mem_sphere {n d : ℕ} :
  ∀ x ∈ sphere n d, from_digits (2 * d - 1) x ≤ ∑ (i : fin n), (d - 1) * (2 * d - 1)^(i : ℕ) :=
λ x hx, from_digits_monotone (2 * d - 1) (le_of_mem_sphere x hx)

lemma sum_fin {β : Type*} [add_comm_monoid β] (n : ℕ) (f : ℕ → β) :
  ∑ (i : fin n), f i = ∑ i in range n, f i :=
(sum_subtype (range n) (by simp) f).symm

lemma digits_sum_eq {n d : ℕ} :
  ∑ (i : fin n), (d - 1) * (2 * d - 1)^(i : ℕ) = ((2 * d - 1)^n - 1) / 2 :=
begin
  apply (nat.div_eq_of_eq_mul_left zero_lt_two _).symm,
  rcases nat.eq_zero_or_pos d with rfl | hd,
  { simp only [mul_zero, nat.zero_sub, zero_mul, sum_const_zero, tsub_eq_zero_iff_le, zero_pow_eq],
    split_ifs; simp },
  have : ((2 * d - 2) + 1) = 2 * d - 1,
  { rw ←tsub_tsub_assoc (nat.le_mul_of_pos_right hd) one_le_two },
  rw [sum_fin n (λ i, (d - 1) * (2 * d - 1)^(i : ℕ)), ←mul_sum, mul_right_comm,
    nat.mul_sub_right_distrib, mul_comm d, one_mul, ←this, ←geom_sum_def, ←geom_sum_mul_add,
    nat.add_sub_cancel, mul_comm],
end

lemma digits_sum_le {n d : ℕ} (hd : 0 < d) :
  ∑ (i : fin n), (d - 1) * (2 * d - 1)^(i : ℕ) < (2 * d - 1)^n :=
begin
  rw digits_sum_eq,
  apply (nat.div_le_self _ _).trans_lt (nat.pred_lt (pow_pos (hd.trans_le weird_thing) _).ne'),
end

lemma behrend_bound_aux1 {n d k N : ℕ} (hd : 0 < d) (hN : (2 * d - 1)^n ≤ N):
  (sphere_slice n d k).card ≤ roth_number N :=
begin
  refine le_roth_number_of_not_has_three_ap _ _
    not_has_three_ap_image_slice (card_image_of_inj_on _),
  { simp only [subset_iff, mem_image, and_imp, forall_exists_index, mem_range,
      forall_apply_eq_imp_iff₂, sphere_slice, mem_filter],
    rintro _ x hx _ rfl,
    apply ((from_digits_le_of_mem_sphere x hx).trans_lt (digits_sum_le hd)).trans_le hN },
  refine set.inj_on.mono (λ x, _) sphere_to_nat_inj_on,
  simp only [mem_coe, sphere_slice, mem_filter, mem_sphere, and_imp, set.mem_set_of_eq],
  exact λ h₁ h₂ i, (h₁ i).trans_le weird_thing,
end

lemma large_slice_aux (n d : ℕ) :
  ∃ k ∈ range (n * (d - 1)^2 + 1),
    (↑(d ^ n) / (↑(n * (d - 1)^2) + 1) : ℝ) ≤ (sphere_slice n d k).card :=
begin
  apply exists_le_card_fiber_of_mul_le_card_of_maps_to',
  { intros x hx,
    rw [mem_range, nat.lt_succ_iff],
    apply sum_squares_bound_of_le _ hx },
  { simp },
  { rw [card_range, nsmul_eq_mul, mul_div_assoc', nat.cast_add_one, mul_div_cancel_left],
    { simp },
    exact (nat.cast_add_one_pos _).ne' }
end

lemma large_slice {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
  ∃ k, (d ^ n / ↑(n * d^2) : ℝ) ≤ (sphere_slice n d k).card :=
begin
  obtain ⟨k, -, hk⟩ := large_slice_aux n d,
  refine ⟨k, _⟩,
  rw ←nat.cast_pow,
  refine (div_le_div_of_le_left _ _ _).trans hk,
  { exact nat.cast_nonneg _ },
  { exact nat.cast_add_one_pos _ },
  simp only [←le_sub_iff_add_le', nat.cast_mul, ←mul_sub, nat.cast_pow, nat.cast_sub hd, sub_sq,
    one_pow, nat.cast_one, mul_one, sub_add, sub_sub_self],
  apply one_le_mul_of_one_le_of_one_le,
  { rwa nat.one_le_cast },
  rw le_sub_iff_add_le,
  norm_num,
  exact le_mul_of_one_le_right zero_le_two (nat.one_le_cast.2 hd),
end
-- d ^ n / (n * d^2) ≤ (sphere_slice n d k).card

lemma behrend_bound_aux2 {n d N : ℕ} (hd : 0 < d) (hn : 0 < n) (hN : (2 * d - 1)^n ≤ N):
  (d ^ n / ↑(n * d^2) : ℝ) ≤ roth_number N :=
begin
  obtain ⟨k, _⟩ := large_slice hn hd,
  apply h.trans,
  rw nat.cast_le,
  apply behrend_bound_aux1 hd hN,
end

end behrend
