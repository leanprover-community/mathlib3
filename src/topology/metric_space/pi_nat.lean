/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.baire
import topology.metric_space.hausdorff_distance

/-!
# Study of spaces `Π (n : ℕ), E n`
-/

noncomputable theory
open_locale classical
open topological_space set metric

local attribute [simp] pow_le_pow_iff one_lt_two inv_le_inv

variable {E : ℕ → Type*}

namespace pi_nat

/-! ### The first_diff function -/

lemma exists_index_ne_of_ne {x y : Π n, E n} (h : x ≠ y) :
  ∃ n, x n ≠ y n :=
begin
  contrapose! h,
  ext1 n,
  exact h n
end

/-- In a product space `Π n, E n`, then `first_diff x y` is the first index at which `x` and `y`
differ. If `x = y`, then by convention we set `first_diff x x = 0`. -/
@[irreducible, pp_nodot] def first_diff (x y : Π n, E n) : ℕ :=
if h : x ≠ y then nat.find (exists_index_ne_of_ne h) else 0

lemma apply_first_diff_ne {x y : Π n, E n} (h : x ≠ y) :
  x (first_diff x y) ≠ y (first_diff x y) :=
begin
  rw [first_diff, dif_pos h],
  exact nat.find_spec (exists_index_ne_of_ne h),
end

lemma apply_eq_of_lt_first_diff {x y : Π n, E n} {n : ℕ} (hn : n < first_diff x y) :
  x n = y n :=
begin
  rw first_diff at hn,
  split_ifs at hn,
  { convert nat.find_min (exists_index_ne_of_ne h) hn,
    simp },
  { exact (not_lt_zero' hn).elim }
end

lemma first_diff_comm (x y : Π n, E n) :
  first_diff x y = first_diff y x :=
begin
  rcases eq_or_ne x y with rfl|hxy, { refl },
  rcases lt_trichotomy (first_diff x y) (first_diff y x) with h|h|h,
  { exact (apply_first_diff_ne hxy (apply_eq_of_lt_first_diff h).symm).elim },
  { exact h },
  { exact (apply_first_diff_ne hxy.symm (apply_eq_of_lt_first_diff h).symm).elim }
end

lemma min_first_diff_le (x y z : Π n, E n) (h : x ≠ z) :
  min (first_diff x y) (first_diff y z) ≤ first_diff x z :=
begin
  by_contra' H,
  have : x (first_diff x z) = z (first_diff x z), from calc
    x (first_diff x z) = y (first_diff x z) :
      apply_eq_of_lt_first_diff (H.trans_le (min_le_left _ _))
    ... = z ((first_diff x z)) : apply_eq_of_lt_first_diff (H.trans_le (min_le_right _ _)),
  exact (apply_first_diff_ne h this).elim,
end

/-! ### Cylinders -/

/-- In a product space `Π n, E n`, the cylinder set of length `n` around `x`, denoted
`cylinder x n`, is the set of sequences `y` that coincide with `x` on the first `n` symbols, i.e.,
such that `y i = x i` for all `i < n`.
-/
def cylinder (x : Π n, E n) (n : ℕ) : set (Π n, E n) :=
{y | ∀ i, i < n → y i = x i}

lemma cylinder_eq_pi (x : Π n, E n) (n : ℕ) :
  cylinder x n = set.pi (finset.range n : set ℕ) (λ (i : ℕ), {x i}) :=
by { ext y, simp [cylinder] }

@[simp] lemma cylinder_zero (x : Π n, E n) : cylinder x 0 = univ :=
by simp [cylinder_eq_pi]

lemma cylinder_anti (x : Π n, E n) {m n : ℕ} (h : m ≤ n) : cylinder x n ⊆ cylinder x m :=
λ y hy i hi, hy i (hi.trans_le h)

@[simp] lemma mem_cylinder_iff {x y : Π n, E n} {n : ℕ} :
  y ∈ cylinder x n ↔ ∀ i, i < n → y i = x i :=
iff.rfl

lemma self_mem_cylinder (x : Π n, E n) (n : ℕ) :
  x ∈ cylinder x n :=
by simp

lemma mem_cylinder_iff_eq {x y : Π n, E n} {n : ℕ} :
  y ∈ cylinder x n ↔ cylinder y n = cylinder x n :=
begin
  split,
  { assume hy,
    apply subset.antisymm,
    { assume z hz i hi,
      rw ← hy i hi,
      exact hz i hi },
    { assume z hz i hi,
      rw hy i hi,
      exact hz i hi } },
  { assume h,
    rw ← h,
    exact self_mem_cylinder _ _ }
end

lemma mem_cylinder_comm (x y : Π n, E n) (n : ℕ) :
  y ∈ cylinder x n ↔ x ∈ cylinder y n :=
by simp [mem_cylinder_iff_eq, eq_comm]

lemma mem_cylinder_iff_le_first_diff {x y : Π n, E n} (hne : x ≠ y) (i : ℕ) :
  x ∈ cylinder y i ↔ i ≤ first_diff x y :=
begin
  split,
  { assume h,
    by_contra',
    exact apply_first_diff_ne hne (h _ this) },
  { assume hi j hj,
    exact apply_eq_of_lt_first_diff (hj.trans_le hi) }
end

lemma mem_cylinder_first_diff (x y : Π n, E n) :
  x ∈ cylinder y (first_diff x y) :=
λ i hi, apply_eq_of_lt_first_diff hi

lemma cylinder_eq_cylinder_of_le_first_diff (x y : Π n, E n) {n : ℕ} (hn : n ≤ first_diff x y) :
  cylinder x n = cylinder y n :=
begin
  rw ← mem_cylinder_iff_eq,
  assume i hi,
  exact apply_eq_of_lt_first_diff (hi.trans_le hn),
end

/-!
### A distance function on `Π n, E n`

We define a distance function on `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is the first
index at which `x` and `y` differ. When each `E n` has the discrete topology, this distance will
define the right topology on the product space. We do not record a global `has_dist` instance nor
a `metric_space`instance, as other distances may be used on these spaces, but we register them as
local instances in this section.
-/

/-- The distance function on a product space `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is
the first index at which `x` and `y` differ. -/
protected def has_dist : has_dist (Π n, E n) :=
⟨λ x y, if h : x ≠ y then (1/2 : ℝ) ^ (first_diff x y) else 0⟩

local attribute [instance] pi_nat.has_dist

lemma dist_eq_of_ne {x y : Π n, E n} (h : x ≠ y) :
  dist x y = (1/2 : ℝ) ^ (first_diff x y) :=
by simp [dist, h]

protected lemma dist_self (x : Π n, E n) : dist x x = 0 :=
by simp [dist]

protected lemma dist_comm (x y : Π n, E n) : dist x y = dist y x :=
by simp [dist, @eq_comm _ x y, first_diff_comm]

protected lemma dist_nonneg (x y : Π n, E n) : 0 ≤ dist x y :=
begin
  rcases eq_or_ne x y with rfl|h,
  { simp [dist] },
  { simp [dist, h] }
end

lemma dist_triangle_nonarch (x y z : Π n, E n) :
  dist x z ≤ max (dist x y) (dist y z) :=
begin
  rcases eq_or_ne x z with rfl|hxz,
  { simp [pi_nat.dist_self x, pi_nat.dist_nonneg] },
  rcases eq_or_ne x y with rfl|hxy,
  { simp },
  rcases eq_or_ne y z with rfl|hyz,
  { simp },
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv, one_div, inv_pow₀, zero_lt_bit0,
    ne.def, not_false_iff, le_max_iff, zero_lt_one, pow_le_pow_iff, one_lt_two, pow_pos,
    min_le_iff.1 (min_first_diff_le x y z hxz)],
end

lemma mem_cylinder_iff_dist_le {x y : Π n, E n} {n : ℕ} :
  y ∈ cylinder x n ↔ dist y x ≤ (1/2)^n :=
begin
  rcases eq_or_ne y x with rfl|hne, { simp [pi_nat.dist_self] },
  suffices : (∀ (i : ℕ), i < n → y i = x i) ↔ n ≤ first_diff y x,
    by simpa [dist_eq_of_ne hne],
  split,
  { assume hy,
    by_contra' H,
    exact apply_first_diff_ne hne (hy _ H) },
  { assume h i hi,
    exact apply_eq_of_lt_first_diff (hi.trans_le h) }
end

lemma apply_eq_of_dist_lt {x y : Π n, E n} {n : ℕ} (h : dist x y < (1/2) ^ n) {i : ℕ}
  (hi : i ≤ n) :
  x i = y i :=
begin
  rcases eq_or_ne x y with rfl|hne, { refl },
  have : n < first_diff x y,
    by simpa [dist_eq_of_ne hne, inv_lt_inv, pow_lt_pow_iff, one_lt_two] using h,
  exact apply_eq_of_lt_first_diff (hi.trans_lt this),
end

variables (E) [∀ n, topological_space (E n)] [∀ n, discrete_topology (E n)]

lemma is_topological_basis_cylinders  :
  is_topological_basis {s : set (Π n, E n) | ∃ (x : Π n, E n) (n : ℕ), s = cylinder x n} :=
begin
  apply is_topological_basis_of_open_of_nhds,
  { rintros u ⟨x, n, rfl⟩,
    rw cylinder_eq_pi,
    exact is_open_set_pi (finset.range n).finite_to_set (λ a ha, is_open_discrete _) },
  { assume x u hx u_open,
    obtain ⟨v, ⟨U, F, hUF, rfl⟩, xU, Uu⟩ : ∃ (v : set (Π (i : ℕ), E i))
      (H : v ∈ {S : set (Π (i : ℕ), E i) | ∃ (U : Π (i : ℕ), set (E i)) (F : finset ℕ),
        (∀ (i : ℕ), i ∈ F → U i ∈ {s : set (E i) | is_open s}) ∧ S = (F : set ℕ).pi U}),
          x ∈ v ∧ v ⊆ u :=
      (is_topological_basis_pi (λ (n : ℕ), is_topological_basis_opens)).exists_subset_of_mem_open
        hx u_open,
    rcases finset.bdd_above F with ⟨n, hn⟩,
    refine ⟨cylinder x (n+1), ⟨x, n+1, rfl⟩, self_mem_cylinder _ _, subset.trans _ Uu⟩,
    assume y hy,
    suffices : ∀ (i : ℕ), i ∈ F → y i ∈ U i, by simpa,
    assume i hi,
    have : y i = x i := mem_cylinder_iff.1 hy i ((hn hi).trans_lt (lt_add_one n)),
    rw this,
    simp only [mem_pi, finset.mem_coe] at xU,
    exact xU i hi }
end

variable {E}

lemma is_open_iff_dist (s : set (Π n, E n)) :
  is_open s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s :=
begin
  split,
  { assume hs x hx,
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ : ∃ (v : set (Π (n : ℕ), E n))
      (H : v ∈ {s | ∃ (x : Π (n : ℕ), E n) (n : ℕ), s = cylinder x n}), x ∈ v ∧ v ⊆ s :=
        (is_topological_basis_cylinders E).exists_subset_of_mem_open hx hs,
    rw ← mem_cylinder_iff_eq.1 h'x at h's,
    exact ⟨(1/2 : ℝ)^n, by simp,
      λ y hy, h's (λ i hi, (apply_eq_of_dist_lt hy hi.le).symm)⟩ },
  { assume h,
    apply (is_topological_basis_cylinders E).is_open_iff.2 (λ x hx, _),
    rcases h x hx with ⟨ε, εpos, hε⟩,
    obtain ⟨n, hn⟩ : ∃ (n : ℕ), (1/2 : ℝ) ^ n < ε := exists_pow_lt_of_lt_one εpos one_half_lt_one,
    refine ⟨cylinder x n, ⟨x, n, rfl⟩, self_mem_cylinder x n, λ y hy, hε y _⟩,
    rw pi_nat.dist_comm,
    exact (mem_cylinder_iff_dist_le.1 hy).trans_lt hn }
end

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete topology,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default. -/
protected def metric_space_of_discrete : metric_space (Π n, E n) :=
begin
  refine metric_space.of_metrizable dist pi_nat.dist_self pi_nat.dist_comm _
    is_open_iff_dist _,
  { assume x y z,
    calc dist x z ≤ max (dist x y) (dist y z) :
      dist_triangle_nonarch x y z
    ... ≤ dist x y + dist y z :
      max_le_add_of_nonneg (pi_nat.dist_nonneg _ _) (pi_nat.dist_nonneg _ _) },
  { assume x y hxy,
    rcases eq_or_ne x y with rfl|h, { refl },
    simp [dist_eq_of_ne h] at hxy,
    exact (two_ne_zero (pow_eq_zero hxy)).elim }
end

local attribute [instance] pi_nat.metric_space_of_discrete

instance : complete_space (Π n, E n) :=
begin
  refine metric.complete_of_convergent_controlled_sequences (λ n, (1/2)^n) (by simp) _,
  assume u hu,
  refine ⟨λ n, u n n, tendsto_pi_nhds.2 (λ i, _)⟩,
  refine tendsto_const_nhds.congr' _,
  filter_upwards [filter.Ici_mem_at_top i] with n hn,
  exact apply_eq_of_dist_lt (hu i i n le_rfl hn) le_rfl,
end

/-!
### Retractions inside product spaces
-/

lemma exists_disjoint_cylinder {s : set (Π n, E n)} (hs : is_closed s) {x : Π n, E n} (hx : x ∉ s) :
  ∃ n, disjoint s (cylinder x n) :=
begin
  unfreezingI { rcases eq_empty_or_nonempty s with rfl|hne },
  { exact ⟨0, by simp⟩ },
  have A : 0 < inf_dist x s := (hs.not_mem_iff_inf_dist_pos hne).1 hx,
  obtain ⟨n, hn⟩ : ∃ n, (1/2 : ℝ)^n < inf_dist x s := exists_pow_lt_of_lt_one A (one_half_lt_one),
  refine ⟨n, _⟩,
  apply disjoint_left.2 (λ y ys hy, _),
  apply lt_irrefl (inf_dist x s),
  calc inf_dist x s ≤ dist x y : inf_dist_le_dist_of_mem ys
  ... ≤ (1/2)^n : by { rw mem_cylinder_comm at hy, exact mem_cylinder_iff_dist_le.1 hy }
  ... < inf_dist x s : hn
end

/-- Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this space, then
`shortest_prefix_diff x s` if the smallest `n` for which there is no element of `s` having the same
prefix of length `n` as `x`. If there is no such `n`, then use `0` by convention. -/
def shortest_prefix_diff {E : ℕ → Type*} (x : (Π n, E n)) (s : set (Π n, E n)) : ℕ :=
if h : ∃ n, disjoint s (cylinder x n) then nat.find h else 0

lemma first_diff_lt_shortest_prefix_diff {s : set (Π n, E n)} (hs : is_closed s)
  {x y : (Π n, E n)} (hx : x ∉ s) (hy : y ∈ s) :
  first_diff x y < shortest_prefix_diff x s :=
begin
  have A := exists_disjoint_cylinder hs hx,
  rw [shortest_prefix_diff, dif_pos A],
  have B := nat.find_spec A,
  contrapose! B,
  rw not_disjoint_iff_nonempty_inter,
  refine ⟨y, hy, _⟩,
  rw mem_cylinder_comm,
  exact cylinder_anti y B (mem_cylinder_first_diff x y)
end

lemma shortest_prefix_diff_pos {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty)
  {x : (Π n, E n)} (hx : x ∉ s) :
  0 < shortest_prefix_diff x s :=
begin
  rcases hne with ⟨y, hy⟩,
  exact (zero_le _).trans_lt (first_diff_lt_shortest_prefix_diff hs hx hy)
end

/-- Given a point `x` in a product space `Π (n : ℕ), E n`, and `s` a subset of this space, then
`longest_prefix x s` if the largest `n` for which there is an element of `s` having the same
prefix of length `n` as `x`. If there is no such `n`, use `0` by convention. -/
def longest_prefix {E : ℕ → Type*} (x : (Π n, E n)) (s : set (Π n, E n)) : ℕ :=
shortest_prefix_diff x s - 1

lemma first_diff_le_longest_prefix {s : set (Π n, E n)} (hs : is_closed s)
  {x y : (Π n, E n)} (hx : x ∉ s) (hy : y ∈ s) :
  first_diff x y ≤ longest_prefix x s :=
begin
  rw [longest_prefix, le_tsub_iff_right],
  { exact first_diff_lt_shortest_prefix_diff hs hx hy },
  { exact shortest_prefix_diff_pos hs ⟨y, hy⟩ hx }
end

lemma inter_cylinder_longest_prefix_nonempty
  {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty) {x : (Π n, E n)} (hx : x ∉ s) :
  (s ∩ cylinder x (longest_prefix x s)).nonempty :=
begin
  have A := exists_disjoint_cylinder hs hx,
  have B : longest_prefix x s < shortest_prefix_diff x s :=
    nat.pred_lt (shortest_prefix_diff_pos hs hne hx).ne',
  rw [longest_prefix, shortest_prefix_diff, dif_pos A] at B ⊢,
  obtain ⟨y, ys, hy⟩ : ∃ (y : Π (n : ℕ), E n), y ∈ s ∧ x ∈ cylinder y (nat.find A - 1),
  { have := nat.find_min A B,
    push_neg at this,
    simp_rw [not_disjoint_iff, mem_cylinder_comm] at this,
    exact this },
  refine ⟨y, ys, _⟩,
  rw mem_cylinder_iff_eq at hy ⊢,
  rw hy
end

lemma disjoint_cylinder_of_longest_prefix_lt
  {s : set (Π n, E n)} (hs : is_closed s)
  {x : (Π n, E n)} (hx : x ∉ s) {n : ℕ} (hn : longest_prefix x s < n) :
  disjoint s (cylinder x n) :=
begin
  rcases eq_empty_or_nonempty s with h's|hne, { simp [h's] },
  contrapose! hn,
  rcases not_disjoint_iff_nonempty_inter.1 hn with ⟨y, ys, hy⟩,
  apply le_trans _ (first_diff_le_longest_prefix hs hx ys),
  apply (mem_cylinder_iff_le_first_diff (ne_of_mem_of_not_mem ys hx).symm _).1,
  rwa mem_cylinder_comm,
end

/-- If two points `x, y` coincide up to length `n`, and the longest common prefix of `x` with `s`
is strictly shorter, then the longest common prefix of `y` with `s` is the same, and both
cylinders of this length based at `x` and `y` coincide. -/
lemma cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff
  {x y : Π n, E n} {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty)
  (H : longest_prefix x s < first_diff x y) (xs : x ∉ s) (ys : y ∉ s) :
  cylinder x (longest_prefix x s) = cylinder y (longest_prefix y s) :=
begin
  have l_eq : longest_prefix y s = longest_prefix x s,
  { rcases lt_trichotomy (longest_prefix y s) (longest_prefix x s) with L|L|L,
    { have Ax : (s ∩ cylinder x (longest_prefix x s)).nonempty :=
        inter_cylinder_longest_prefix_nonempty hs hne xs,
      have Z := disjoint_cylinder_of_longest_prefix_lt hs ys L,
      rw first_diff_comm at H,
      rw [cylinder_eq_cylinder_of_le_first_diff _ _ H.le] at Z,
      exact (Ax.not_disjoint Z).elim },
    { exact L },
    { have Ay : (s ∩ cylinder y (longest_prefix y s)).nonempty :=
        inter_cylinder_longest_prefix_nonempty hs hne ys,
      have A'y : (s ∩ cylinder y (longest_prefix x s).succ).nonempty :=
        Ay.mono (inter_subset_inter_right s (cylinder_anti _ L)),
      have Z := disjoint_cylinder_of_longest_prefix_lt hs xs (nat.lt_succ_self _),
      rw cylinder_eq_cylinder_of_le_first_diff _ _ H at Z,
      exact (A'y.not_disjoint Z).elim } },
  rw [l_eq, ← mem_cylinder_iff_eq],
  exact cylinder_anti y H.le (mem_cylinder_first_diff x y)
end

/-- Given a closed nonempty subset `s` of `Π n, E n`, there exists a Lipschitz retraction onto this
set, i.e., a Lipschitz map with range equal to `s`, equal to the identity on `s`. -/
theorem exists_lipschitz_retraction_of_is_closed
  {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty) :
  ∃ f : (Π n, E n) → (Π n, E n), (∀ x ∈ s, f x = x) ∧ (range f = s) ∧ lipschitz_with 1 f :=
begin
  /- The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise, consider the longest
  prefix `w` that `x` shares with an element of `s`, and let `f x = z_w` where `z_w` is an element
  of `s` starting with `w`. All the desired properties are clear, except the fact that `f`
  is `1`-Lipschitz: if two points `x, y` belong to a common cylinder of length `n`, one should show
  that their images also belong to a common cylinder of length `n`. This is a case analysis:
  * if both `x, y ∈ s`, then this is clear.
  * if `x ∈ s` but `y ∉ s`, then the longest prefix `w` of `y` shared by an element of `s` is of
  length at least `n` (because of `x`), and then `f y` starts with `w` and therefore stays in the
  same length `n` cylinder.
  * if `x ∉ s`, `y ∉ s`, let `w` be the longest prefix of `x` shared by an element of `s`. If its
  length is `< n`, then it is also the longest prefix of `y`, and we get `f x = f y = z_w`.
  Otherwise, `f x` remains in the same `n`-cylinder as `x`. Similarly for `y`. Finally, `f x` and
  `f y` are again in the same `n`-cylinder, as desired. -/
  set f := λ x, if h : x ∈ s then x
    else (inter_cylinder_longest_prefix_nonempty hs hne h).some with hf,
  have fs : ∀ x ∈ s, f x = x := λ x xs, by simp [xs],
  refine ⟨f, fs, _, _⟩,
  -- check that the range of `f` is `s`.
  { apply subset.antisymm,
    { rintros x ⟨y, rfl⟩,
      by_cases hy : y ∈ s, { rwa fs y hy },
      simpa [hf, dif_neg hy]
        using (inter_cylinder_longest_prefix_nonempty hs hne hy).some_spec.1 },
    { assume x hx,
      rw ← fs x hx,
      exact mem_range_self _ } },
  -- check that `f` is `1`-Lipschitz, by a case analysis.
  { apply lipschitz_with.mk_one (λ x y, _),
    -- exclude the trivial cases where `x = y`, or `f x = f y`.
    rcases eq_or_ne x y with rfl|hxy, { simp },
    rcases eq_or_ne (f x) (f y) with h'|hfxfy, { simp [h', dist_nonneg] },
    have I2 : cylinder x (first_diff x y) = cylinder y (first_diff x y),
    { rw ← mem_cylinder_iff_eq,
      apply mem_cylinder_first_diff },
    suffices : first_diff x y ≤ first_diff (f x) (f y),
      by simpa [dist_eq_of_ne hxy, dist_eq_of_ne hfxfy],
    -- case where `x ∈ s`
    by_cases xs : x ∈ s,
    { rw [fs x xs] at ⊢ hfxfy,
      -- case where `y ∈ s`, trivial
      by_cases ys : y ∈ s, { rw [fs y ys] },
      -- case where `y ∉ s`
      have A : (s ∩ cylinder y (longest_prefix y s)).nonempty :=
        inter_cylinder_longest_prefix_nonempty hs hne ys,
      have fy : f y = A.some, by simp_rw [hf, dif_neg ys],
      have I : cylinder A.some (first_diff x y) = cylinder y (first_diff x y),
        { rw [← mem_cylinder_iff_eq, first_diff_comm],
          apply cylinder_anti y _ A.some_spec.2,
          exact first_diff_le_longest_prefix hs ys xs },
        rwa [← fy, ← I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_first_diff hfxfy.symm,
             first_diff_comm _ x] at I },
    -- case where `x ∉ s`
    { by_cases ys : y ∈ s,
      -- case where `y ∈ s` (similar to the above)
      { have A : (s ∩ cylinder x (longest_prefix x s)).nonempty :=
          inter_cylinder_longest_prefix_nonempty hs hne xs,
        have fx : f x = A.some, by simp_rw [hf, dif_neg xs],
        have I : cylinder A.some (first_diff x y) = cylinder x (first_diff x y),
        { rw ← mem_cylinder_iff_eq,
          apply cylinder_anti x _ A.some_spec.2,
          apply first_diff_le_longest_prefix hs xs ys },
        rw fs y ys at ⊢ hfxfy,
        rwa [← fx, I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_first_diff hfxfy] at I },
      -- case where `y ∉ s`
      { have Ax : (s ∩ cylinder x (longest_prefix x s)).nonempty :=
          inter_cylinder_longest_prefix_nonempty hs hne xs,
        have fx : f x = Ax.some, by simp_rw [hf, dif_neg xs],
        have Ay : (s ∩ cylinder y (longest_prefix y s)).nonempty :=
          inter_cylinder_longest_prefix_nonempty hs hne ys,
        have fy : f y = Ay.some, by simp_rw [hf, dif_neg ys],
        -- case where the common prefix to `x` and `s`, or `y` and `s`, is shorter than the
        -- common part to `x` and `y` -- then `f x = f y`.
        by_cases H : longest_prefix x s < first_diff x y ∨ longest_prefix y s < first_diff x y,
        { have : cylinder x (longest_prefix x s) = cylinder y (longest_prefix y s),
          { cases H,
            { exact cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff hs hne H xs ys },
            { symmetry,
              rw first_diff_comm at H,
              exact cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff hs hne H ys xs } },
          rw [fx, fy] at hfxfy,
          apply (hfxfy _).elim,
          congr' },
        -- case where the common prefix to `x` and `s` is long, as well as the common prefix to
        -- `y` and `s`. Then all points remain in the same cylinders.
        { push_neg at H,
          have I1 : cylinder Ax.some (first_diff x y) = cylinder x (first_diff x y),
          { rw ← mem_cylinder_iff_eq,
            exact cylinder_anti x H.1 Ax.some_spec.2 },
          have I3 : cylinder y (first_diff x y) = cylinder Ay.some (first_diff x y),
          { rw [eq_comm, ← mem_cylinder_iff_eq],
            exact cylinder_anti y H.2 Ay.some_spec.2 },
          have : cylinder Ax.some (first_diff x y) = cylinder Ay.some (first_diff x y),
            by rw [I1, I2, I3],
          rw [← fx, ← fy, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_first_diff hfxfy] at this,
          exact this } } } }
end

/-- Given a closed nonempty subset `s` of `Π n, E n`, there exists a retraction onto this
set, i.e., a continuous map with range equal to `s`, equal to the identity on `s`. -/
theorem exists_retraction_of_is_closed
  {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty) :
  ∃ f : (Π n, E n) → (Π n, E n), (∀ x ∈ s, f x = x) ∧ (range f = s) ∧ continuous f :=
begin
  rcases exists_lipschitz_retraction_of_is_closed hs hne with ⟨f, fs, frange, hf⟩,
  exact ⟨f, fs, frange, hf.continuous⟩
end

end pi_nat
