/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import tactic.ring_exp
import topology.metric_space.hausdorff_distance

/-!
# Topological study of spaces `Π (n : ℕ), E n`

When `E n` are topological spaces, the space `Π (n : ℕ), E n` is naturally a topological space
(with the product topology). When `E n` are uniform spaces, it also inherits a uniform structure.
However, it does not inherit a canonical metric space structure of the `E n`. Nevertheless, one
can put a noncanonical metric space structure (or rather, several of them). This is done in this
file.

## Main definitions and results

One can define a combinatorial distance on `Π (n : ℕ), E n`, as follows:

* `pi_nat.cylinder x n` is the set of points `y` with `x i = y i` for `i < n`.
* `pi_nat.first_diff x y` is the first index at which `x i ≠ y i`.
* `pi_nat.dist x y` is equal to `(1/2) ^ (first_diff x y)`. It defines a distance
  on `Π (n : ℕ), E n`, compatible with the topology when the `E n` have the discrete topology.
* `pi_nat.metric_space`: the metric space structure, given by this distance. Not registered as an
  instance. This space is a complete metric space.
* `pi_nat.metric_space_of_discrete_uniformity`: the same metric space structure, but adjusting the
  uniformity defeqness when the `E n` already have the discrete uniformity. Not registered as an
  instance
* `pi_nat.metric_space_nat_nat`: the particular case of `ℕ → ℕ`, not registered as an instance.

These results are used to construct continuous functions on `Π n, E n`:

* `pi_nat.exists_retraction_of_is_closed`: given a nonempty closed subset `s` of `Π (n : ℕ), E n`,
  there exists a retraction onto `s`, i.e., a continuous map from the whole space to `s`
  restricting to the identity on `s`.
* `exists_nat_nat_continuous_surjective_of_complete_space`: given any nonempty complete metric
  space with second-countable topology, there exists a continuous surjection from `ℕ → ℕ` onto
  this space.

One can also put distances on `Π (i : ι), E i` when the spaces `E i` are metric spaces (not discrete
in general), and `ι` is countable.

* `pi_countable.dist` is the distance on `Π i, E i` given by
    `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`.
* `pi_countable.metric_space` is the corresponding metric space structure, adjusted so that
  the uniformity is definitionally the product uniformity. Not registered as an instance.
-/

noncomputable theory
open_locale classical topological_space filter
open topological_space set metric filter function

local attribute [simp] pow_le_pow_iff one_lt_two inv_le_inv

variable {E : ℕ → Type*}

namespace pi_nat

/-! ### The first_diff function -/

/-- In a product space `Π n, E n`, then `first_diff x y` is the first index at which `x` and `y`
differ. If `x = y`, then by convention we set `first_diff x x = 0`. -/
@[irreducible, pp_nodot] def first_diff (x y : Π n, E n) : ℕ :=
if h : x ≠ y then nat.find (ne_iff.1 h) else 0

lemma apply_first_diff_ne {x y : Π n, E n} (h : x ≠ y) :
  x (first_diff x y) ≠ y (first_diff x y) :=
begin
  rw [first_diff, dif_pos h],
  exact nat.find_spec (ne_iff.1 h),
end

lemma apply_eq_of_lt_first_diff {x y : Π n, E n} {n : ℕ} (hn : n < first_diff x y) :
  x n = y n :=
begin
  rw first_diff at hn,
  split_ifs at hn,
  { convert nat.find_min (ne_iff.1 h) hn,
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

lemma Union_cylinder_update (x : Π n, E n) (n : ℕ) :
  (⋃ k, cylinder (update x n k) (n+1)) = cylinder x n :=
begin
  ext y,
  simp only [mem_cylinder_iff, mem_Union],
  split,
  { rintros ⟨k, hk⟩ i hi,
    simpa [hi.ne] using hk i (nat.lt_succ_of_lt hi) },
  { assume H,
    refine ⟨y n, λ i hi, _⟩,
    rcases nat.lt_succ_iff_lt_or_eq.1 hi with h'i|rfl,
    { simp [H i h'i, h'i.ne] },
    { simp } },
end

lemma update_mem_cylinder (x : Π n, E n) (n : ℕ) (y : E n) :
  update x n y ∈ cylinder x n :=
mem_cylinder_iff.2 (λ i hi, by simp [hi.ne])

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
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv, one_div, inv_pow, zero_lt_bit0,
    ne.def, not_false_iff, le_max_iff, zero_lt_one, pow_le_pow_iff, one_lt_two, pow_pos,
    min_le_iff.1 (min_first_diff_le x y z hxz)],
end

protected lemma dist_triangle (x y z : Π n, E n) :
  dist x z ≤ dist x y + dist y z :=
calc dist x z ≤ max (dist x y) (dist y z) :
  dist_triangle_nonarch x y z
... ≤ dist x y + dist y z :
  max_le_add_of_nonneg (pi_nat.dist_nonneg _ _) (pi_nat.dist_nonneg _ _)

protected lemma eq_of_dist_eq_zero (x y : Π n, E n) (hxy : dist x y = 0) : x = y :=
begin
  rcases eq_or_ne x y with rfl|h, { refl },
  simp [dist_eq_of_ne h] at hxy,
  exact (two_ne_zero (pow_eq_zero hxy)).elim
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

/-- A function to a pseudo-metric-space is `1`-Lipschitz if and only if points in the same cylinder
of length `n` are sent to points within distance `(1/2)^n`.
Not expressed using `lipschitz_with` as we don't have a metric space structure -/
lemma lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder
  {α : Type*} [pseudo_metric_space α] {f : (Π n, E n) → α} :
  (∀ (x y : Π n, E n), dist (f x) (f y) ≤ dist x y) ↔
    (∀ x y n, y ∈ cylinder x n → dist (f x) (f y) ≤ (1/2)^n) :=
begin
  split,
  { assume H x y n hxy,
    apply (H x y).trans,
    rw pi_nat.dist_comm,
    exact mem_cylinder_iff_dist_le.1 hxy },
  { assume H x y,
    rcases eq_or_ne x y with rfl|hne, { simp [pi_nat.dist_nonneg] },
    rw dist_eq_of_ne hne,
    apply H x y (first_diff x y),
    rw first_diff_comm,
    exact mem_cylinder_first_diff _ _ }
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
    simp only [set.mem_pi, finset.mem_coe] at xU,
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
`y` differ. Not registered as a global instance by default.
Warning: this definition makes sure that the topology is defeq to the original product topology,
but it does not take care of a possible uniformity. If the `E n` have a uniform structure, then
there will be two non-defeq uniform structures on `Π n, E n`, the product one and the one coming
from the metric structure. In this case, use `metric_space_of_discrete_uniformity` instead. -/
protected def metric_space : metric_space (Π n, E n) :=
metric_space.of_metrizable dist pi_nat.dist_self pi_nat.dist_comm pi_nat.dist_triangle
  is_open_iff_dist pi_nat.eq_of_dist_eq_zero

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete uniformity,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default. -/
protected def metric_space_of_discrete_uniformity {E : ℕ → Type*} [∀ n, uniform_space (E n)]
  (h : ∀ n, uniformity (E n) = 𝓟 id_rel) : metric_space (Π n, E n) :=
begin
  haveI : ∀ n, discrete_topology (E n) := λ n, discrete_topology_of_discrete_uniformity (h n),
  exact
  { dist_triangle := pi_nat.dist_triangle,
    dist_comm := pi_nat.dist_comm,
    dist_self := pi_nat.dist_self,
    eq_of_dist_eq_zero := pi_nat.eq_of_dist_eq_zero,
    to_uniform_space := Pi.uniform_space _,
    uniformity_dist :=
    begin
      simp [Pi.uniformity, comap_infi, gt_iff_lt, preimage_set_of_eq, comap_principal,
        pseudo_metric_space.uniformity_dist, h, id_rel],
      apply le_antisymm,
      { simp only [le_infi_iff, le_principal_iff],
        assume ε εpos,
        obtain ⟨n, hn⟩ : ∃ n, (1/2 : ℝ)^n < ε := exists_pow_lt_of_lt_one εpos (by norm_num),
        apply @mem_infi_of_Inter _ _ _ _ _ (finset.range n).finite_to_set
          (λ i, {p : (Π (n : ℕ), E n) × Π (n : ℕ), E n | p.fst i = p.snd i}),
        { simp only [mem_principal, set_of_subset_set_of, imp_self, implies_true_iff] },
        { rintros ⟨x, y⟩ hxy,
          simp only [finset.mem_coe, finset.mem_range, Inter_coe_set, mem_Inter, mem_set_of_eq]
            at hxy,
          apply lt_of_le_of_lt _ hn,
          rw [← mem_cylinder_iff_dist_le, mem_cylinder_iff],
          exact hxy } },
      { simp only [le_infi_iff, le_principal_iff],
        assume n,
        refine mem_infi_of_mem ((1/2)^n) _,
        refine mem_infi_of_mem (by norm_num) _,
        simp only [mem_principal, set_of_subset_set_of, prod.forall],
        assume x y hxy,
        exact apply_eq_of_dist_lt hxy le_rfl }
    end }
end

/-- Metric space structure on `ℕ → ℕ` where the distance is given by `dist x y = (1/2)^n`,
where `n` is the smallest index where `x` and `y` differ.
Not registered as a global instance by default. -/
def metric_space_nat_nat : metric_space (ℕ → ℕ) :=
pi_nat.metric_space_of_discrete_uniformity (λ n, rfl)

local attribute [instance] pi_nat.metric_space

protected lemma complete_space : complete_space (Π n, E n) :=
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

We show that, in a space `Π (n : ℕ), E n` where each `E n` is discrete, there is a retraction on
any closed nonempty subset `s`, i.e., a continuous map `f` from the whole space to `s` restricting
to the identity on `s`. The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise,
consider the longest prefix `w` that `x` shares with an element of `s`, and let `f x = z_w`
where `z_w` is an element of `s` starting with `w`.
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
  {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty) (x : (Π n, E n)) :
  (s ∩ cylinder x (longest_prefix x s)).nonempty :=
begin
  by_cases hx : x ∈ s, { exact ⟨x, hx, self_mem_cylinder _ _⟩ },
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
is strictly shorter than `n`, then the longest common prefix of `y` with `s` is the same, and both
cylinders of this length based at `x` and `y` coincide. -/
lemma cylinder_longest_prefix_eq_of_longest_prefix_lt_first_diff
  {x y : Π n, E n} {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty)
  (H : longest_prefix x s < first_diff x y) (xs : x ∉ s) (ys : y ∉ s) :
  cylinder x (longest_prefix x s) = cylinder y (longest_prefix y s) :=
begin
  have l_eq : longest_prefix y s = longest_prefix x s,
  { rcases lt_trichotomy (longest_prefix y s) (longest_prefix x s) with L|L|L,
    { have Ax : (s ∩ cylinder x (longest_prefix x s)).nonempty :=
        inter_cylinder_longest_prefix_nonempty hs hne x,
      have Z := disjoint_cylinder_of_longest_prefix_lt hs ys L,
      rw first_diff_comm at H,
      rw [cylinder_eq_cylinder_of_le_first_diff _ _ H.le] at Z,
      exact (Ax.not_disjoint Z).elim },
    { exact L },
    { have Ay : (s ∩ cylinder y (longest_prefix y s)).nonempty :=
        inter_cylinder_longest_prefix_nonempty hs hne y,
      have A'y : (s ∩ cylinder y (longest_prefix x s).succ).nonempty :=
        Ay.mono (inter_subset_inter_right s (cylinder_anti _ L)),
      have Z := disjoint_cylinder_of_longest_prefix_lt hs xs (nat.lt_succ_self _),
      rw cylinder_eq_cylinder_of_le_first_diff _ _ H at Z,
      exact (A'y.not_disjoint Z).elim } },
  rw [l_eq, ← mem_cylinder_iff_eq],
  exact cylinder_anti y H.le (mem_cylinder_first_diff x y)
end

/-- Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a Lipschitz retraction
onto this set, i.e., a Lipschitz map with range equal to `s`, equal to the identity on `s`. -/
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
  set f := λ x, if x ∈ s then x else (inter_cylinder_longest_prefix_nonempty hs hne x).some with hf,
  have fs : ∀ x ∈ s, f x = x := λ x xs, by simp [xs],
  refine ⟨f, fs, _, _⟩,
  -- check that the range of `f` is `s`.
  { apply subset.antisymm,
    { rintros x ⟨y, rfl⟩,
      by_cases hy : y ∈ s, { rwa fs y hy },
      simpa [hf, if_neg hy] using (inter_cylinder_longest_prefix_nonempty hs hne y).some_spec.1 },
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
        inter_cylinder_longest_prefix_nonempty hs hne y,
      have fy : f y = A.some, by simp_rw [hf, if_neg ys],
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
          inter_cylinder_longest_prefix_nonempty hs hne x,
        have fx : f x = A.some, by simp_rw [hf, if_neg xs],
        have I : cylinder A.some (first_diff x y) = cylinder x (first_diff x y),
        { rw ← mem_cylinder_iff_eq,
          apply cylinder_anti x _ A.some_spec.2,
          apply first_diff_le_longest_prefix hs xs ys },
        rw fs y ys at ⊢ hfxfy,
        rwa [← fx, I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_first_diff hfxfy] at I },
      -- case where `y ∉ s`
      { have Ax : (s ∩ cylinder x (longest_prefix x s)).nonempty :=
          inter_cylinder_longest_prefix_nonempty hs hne x,
        have fx : f x = Ax.some, by simp_rw [hf, if_neg xs],
        have Ay : (s ∩ cylinder y (longest_prefix y s)).nonempty :=
          inter_cylinder_longest_prefix_nonempty hs hne y,
        have fy : f y = Ay.some, by simp_rw [hf, if_neg ys],
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

/-- Given a closed nonempty subset `s` of `Π (n : ℕ), E n`, there exists a retraction onto this
set, i.e., a continuous map with range equal to `s`, equal to the identity on `s`. -/
theorem exists_retraction_of_is_closed
  {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty) :
  ∃ f : (Π n, E n) → (Π n, E n), (∀ x ∈ s, f x = x) ∧ (range f = s) ∧ continuous f :=
begin
  rcases exists_lipschitz_retraction_of_is_closed hs hne with ⟨f, fs, frange, hf⟩,
  exact ⟨f, fs, frange, hf.continuous⟩
end

theorem exists_retraction_subtype_of_is_closed
  {s : set (Π n, E n)} (hs : is_closed s) (hne : s.nonempty) :
  ∃ f : (Π n, E n) → s, (∀ x : s, f x = x) ∧ surjective f ∧ continuous f :=
begin
  obtain ⟨f, fs, f_range, f_cont⟩ : ∃ f : (Π n, E n) → (Π n, E n),
    (∀ x ∈ s, f x = x) ∧ (range f = s) ∧ continuous f :=
      exists_retraction_of_is_closed hs hne,
  have A : ∀ x, f x ∈ s, by simp [← f_range],
  have B : ∀ (x : s), cod_restrict f s A x = x,
  { assume x,
    apply subtype.coe_injective.eq_iff.1,
    simpa only using fs x.val x.property },
  exact ⟨cod_restrict f s A, B, λ x, ⟨x, B x⟩, continuous_subtype_mk _ f_cont⟩,
end

end pi_nat

open pi_nat

/-- Any nonempty complete second countable metric space is the continuous image of the
fundamental space `ℕ → ℕ`. For a version of this theorem in the context of Polish spaces, see
`exists_nat_nat_continuous_surjective_of_polish_space`. -/
lemma exists_nat_nat_continuous_surjective_of_complete_space
  (α : Type*) [metric_space α] [complete_space α] [second_countable_topology α] [nonempty α] :
  ∃ (f : (ℕ → ℕ) → α), continuous f ∧ surjective f :=
begin
  /- First, we define a surjective map from a closed subset `s` of `ℕ → ℕ`. Then, we compose
  this map with a retraction of `ℕ → ℕ` onto `s` to obtain the desired map.
  Let us consider a dense sequence `u` in `α`. Then `s` is the set of sequences `xₙ` such that the
  balls `closed_ball (u xₙ) (1/2^n)` have a nonempty intersection. This set is closed, and we define
  `f x` there to be the unique point in the intersection. This function is continuous and surjective
  by design. -/
  letI : metric_space (ℕ → ℕ) := pi_nat.metric_space_nat_nat,
  have I0 : (0 : ℝ) < 1/2, by norm_num,
  have I1 : (1/2 : ℝ) < 1, by norm_num,
  rcases exists_dense_seq α with ⟨u, hu⟩,
  let s : set (ℕ → ℕ) := {x | (⋂ (n : ℕ), closed_ball (u (x n)) ((1/2)^n)).nonempty},
  let g : s → α := λ x, x.2.some,
  have A : ∀ (x : s) (n : ℕ), dist (g x) (u ((x : ℕ → ℕ) n)) ≤ (1/2)^n :=
    λ x n, (mem_Inter.1 x.2.some_mem n : _),
  have g_cont : continuous g,
  { apply continuous_iff_continuous_at.2 (λ y, _),
    apply continuous_at_of_locally_lipschitz zero_lt_one 4 (λ x hxy, _),
    rcases eq_or_ne x y with rfl|hne, { simp },
    have hne' : x.1 ≠ y.1 := subtype.coe_injective.ne hne,
    have dist' : dist x y = dist x.1 y.1 := rfl,
    let n := first_diff x.1 y.1 - 1,
    have diff_pos : 0 < first_diff x.1 y.1,
    { by_contra' h,
      apply apply_first_diff_ne hne',
      rw [le_zero_iff.1 h],
      apply apply_eq_of_dist_lt _ le_rfl,
      exact hxy },
    have hn : first_diff x.1 y.1 = n + 1 := (nat.succ_pred_eq_of_pos diff_pos).symm,
    rw [dist', dist_eq_of_ne hne', hn],
    have B : x.1 n = y.1 n := mem_cylinder_first_diff x.1 y.1 n (nat.pred_lt diff_pos.ne'),
    calc dist (g x) (g y) ≤ dist (g x) (u (x.1 n)) + dist (g y) (u (x.1 n)) :
      dist_triangle_right _ _ _
    ... = dist (g x) (u (x.1 n)) + dist (g y) (u (y.1 n)) : by rw ← B
    ... ≤ (1/2)^n + (1/2)^n : add_le_add (A x n) (A y n)
    ... = 4 * (1 / 2) ^ (n + 1) : by ring_exp },
  have g_surj : surjective g,
  { assume y,
    have : ∀ (n : ℕ), ∃ j, y ∈ closed_ball (u j) ((1/2)^n),
    { assume n,
      rcases hu.exists_dist_lt y (by simp : (0 : ℝ) < (1/2)^n) with ⟨j, hj⟩,
      exact ⟨j, hj.le⟩ },
    choose x hx using this,
    have I : (⋂ (n : ℕ), closed_ball (u (x n)) ((1 / 2) ^ n)).nonempty := ⟨y, mem_Inter.2 hx⟩,
    refine ⟨⟨x, I⟩, _⟩,
    refine dist_le_zero.1 _,
    have J : ∀ (n : ℕ), dist (g ⟨x, I⟩) y ≤ (1/2)^n + (1/2)^n := λ n, calc
      dist (g ⟨x, I⟩) y ≤ dist (g ⟨x, I⟩) (u (x n)) + dist y (u (x n)) : dist_triangle_right _ _ _
      ... ≤ (1/2)^n + (1/2)^n : add_le_add (A ⟨x, I⟩ n) (hx n),
    have L : tendsto (λ (n : ℕ), (1/2 : ℝ)^n + (1/2)^n) at_top (𝓝 (0 + 0)) :=
      (tendsto_pow_at_top_nhds_0_of_lt_1 I0.le I1).add (tendsto_pow_at_top_nhds_0_of_lt_1 I0.le I1),
    rw add_zero at L,
    exact ge_of_tendsto' L J },
  have s_closed : is_closed s,
  { refine is_closed_iff_cluster_pt.mpr _,
    assume x hx,
    have L : tendsto (λ (n : ℕ), diam (closed_ball (u (x n)) ((1 / 2) ^ n))) at_top (𝓝 0),
    { have : tendsto (λ (n : ℕ), (2 : ℝ) * (1/2)^n) at_top (𝓝 (2 * 0)) :=
        (tendsto_pow_at_top_nhds_0_of_lt_1 I0.le I1).const_mul _,
      rw mul_zero at this,
      exact squeeze_zero (λ n, diam_nonneg) (λ n, diam_closed_ball (pow_nonneg I0.le _)) this },
    refine nonempty_Inter_of_nonempty_bInter (λ n, is_closed_ball) (λ n, bounded_closed_ball) _ L,
    assume N,
    obtain ⟨y, hxy, ys⟩ : ∃ y, y ∈ ball x ((1 / 2) ^ N) ∩ s :=
      cluster_pt_principal_iff.1 hx _ (ball_mem_nhds x (pow_pos I0 N)),
    have E : (⋂ (n : ℕ) (H : n ≤ N), closed_ball (u (x n)) ((1 / 2) ^ n))
            = ⋂ (n : ℕ) (H : n ≤ N), closed_ball (u (y n)) ((1 / 2) ^ n),
    { congr,
      ext1 n,
      congr,
      ext1 hn,
      have : x n = y n := apply_eq_of_dist_lt (mem_ball'.1 hxy) hn,
      rw this },
    rw E,
    apply nonempty.mono _ ys,
    apply Inter_subset_Inter₂ },
  obtain ⟨f, -, f_surj, f_cont⟩ :
    ∃ f : (ℕ → ℕ) → s, (∀ x : s, f x = x) ∧ surjective f ∧ continuous f,
  { apply exists_retraction_subtype_of_is_closed s_closed,
    simpa only [nonempty_coe_sort] using g_surj.nonempty },
  exact ⟨g ∘ f, g_cont.comp f_cont, g_surj.comp f_surj⟩,
end

namespace pi_countable

/-!
### Products of (possibly non-discrete) metric spaces
-/

variables {ι : Type*} [encodable ι] {F : ι → Type*} [∀ i, metric_space (F i)]
open encodable

/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.
It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`. -/
protected def has_dist : has_dist (Π i, F i) :=
⟨λ x y, ∑' (i : ι), min ((1/2)^(encode i)) (dist (x i) (y i))⟩

local attribute [instance] pi_countable.has_dist

lemma dist_eq_tsum (x y : Π i, F i) :
  dist x y = ∑' (i : ι), min ((1/2)^(encode i)) (dist (x i) (y i)) := rfl

lemma dist_summable (x y : Π i, F i) :
  summable (λ (i : ι), min ((1/2)^(encode i)) (dist (x i) (y i))) :=
begin
  refine summable_of_nonneg_of_le (λ i, _) (λ i, min_le_left _ _) summable_geometric_two_encode,
  exact le_min (pow_nonneg (by norm_num) _) (dist_nonneg)
end

lemma min_dist_le_dist_pi (x y : Π i, F i) (i : ι) :
  min ((1/2)^(encode i)) (dist (x i) (y i)) ≤ dist x y :=
le_tsum (dist_summable x y) i (λ j hj, le_min (by simp) (dist_nonneg))

lemma dist_le_dist_pi_of_dist_lt {x y : Π i, F i} {i : ι} (h : dist x y < (1/2)^(encode i)) :
  dist (x i) (y i) ≤ dist x y :=
by simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_dist_le_dist_pi x y i)

open_locale big_operators topological_space
open filter

open_locale nnreal

variable (E)

/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`,
defining the right topology and uniform structure. It is highly non-canonical, though, and therefore
not registered as a global instance.
The distance we use here is `dist x y = ∑' n, min (1/2)^(encode i) (dist (x n) (y n))`. -/
protected def metric_space : metric_space (Π i, F i) :=
{ dist_self := λ x, by simp [dist_eq_tsum],
  dist_comm := λ x y, by simp [dist_eq_tsum, dist_comm],
  dist_triangle := λ x y z,
  begin
    have I : ∀ i, min ((1/2)^(encode i)) (dist (x i) (z i)) ≤
      min ((1/2)^(encode i)) (dist (x i) (y i)) + min ((1/2)^(encode i)) (dist (y i) (z i)) :=
    λ i, calc
      min ((1/2)^(encode i)) (dist (x i) (z i))
        ≤ min ((1/2)^(encode i)) (dist (x i) (y i) + dist (y i) (z i)) :
          min_le_min le_rfl (dist_triangle _ _ _)
      ... = min ((1/2)^(encode i)) (min ((1/2)^(encode i)) (dist (x i) (y i))
            + min ((1/2)^(encode i)) (dist (y i) (z i))) :
        begin
          convert congr_arg (coe : ℝ≥0 → ℝ)
            (min_add_distrib ((1/2 : ℝ≥0)^(encode i)) (nndist (x i) (y i)) (nndist (y i) (z i)));
          simp
        end
      ... ≤ min ((1/2)^(encode i)) (dist (x i) (y i)) + min ((1/2)^(encode i)) (dist (y i) (z i)) :
          min_le_right _ _,
    calc dist x z ≤ ∑' i, (min ((1/2)^(encode i)) (dist (x i) (y i))
                          + min ((1/2)^(encode i)) (dist (y i) (z i))) :
      tsum_le_tsum I (dist_summable x z) ((dist_summable x y).add (dist_summable y z))
    ... = dist x y + dist y z : tsum_add (dist_summable x y) (dist_summable y z)
  end,
  eq_of_dist_eq_zero :=
  begin
    assume x y hxy,
    ext1 n,
    rw [← dist_le_zero, ← hxy],
    apply dist_le_dist_pi_of_dist_lt,
    rw hxy,
    simp
  end,
  to_uniform_space := Pi.uniform_space _,
  uniformity_dist :=
  begin
    have I0 : (0 : ℝ) ≤ 1/2, by norm_num,
    have I1 : (1/2 : ℝ) < 1, by norm_num,
    simp only [Pi.uniformity, comap_infi, gt_iff_lt, preimage_set_of_eq, comap_principal,
      pseudo_metric_space.uniformity_dist],
    apply le_antisymm,
    { simp only [le_infi_iff, le_principal_iff],
      assume ε εpos,
      obtain ⟨K, hK⟩ : ∃ (K : finset ι), ∑' (i : {j // j ∉ K}), (1/2 : ℝ)^(encode (i : ι)) < ε/2 :=
        ((tendsto_order.1 (tendsto_tsum_compl_at_top_zero (λ (i : ι), (1/2 : ℝ)^(encode i)))).2
           _ (half_pos εpos)).exists,
      obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ℝ) (δpos : 0 < δ), (K.card : ℝ) * δ ≤ ε/2,
      { rcases nat.eq_zero_or_pos K.card with hK|hK,
        { exact ⟨1, zero_lt_one,
                  by simpa only [hK, nat.cast_zero, zero_mul] using (half_pos εpos).le⟩ },
        { have Kpos : 0 < (K.card : ℝ) := nat.cast_pos.2 hK,
          refine ⟨(ε / 2) / (K.card : ℝ), (div_pos (half_pos εpos) Kpos), le_of_eq _⟩,
          field_simp [Kpos.ne'],
          ring } },
      apply @mem_infi_of_Inter _ _ _ _ _ K.finite_to_set
        (λ i, {p : (Π (i : ι), F i) × Π (i : ι), F i | dist (p.fst i) (p.snd i) < δ}),
      { rintros ⟨i, hi⟩,
        refine mem_infi_of_mem δ (mem_infi_of_mem δpos _),
        simp only [prod.forall, imp_self, mem_principal] },
      { rintros ⟨x, y⟩ hxy,
        simp only [mem_Inter, mem_set_of_eq, set_coe.forall, finset.mem_range, finset.mem_coe]
          at hxy,
        calc dist x y = ∑' (i : ι), min ((1/2)^(encode i)) (dist (x i) (y i)) : rfl
        ... = ∑ i in K, min ((1/2)^(encode i)) (dist (x i) (y i))
             + ∑' (i : (↑K : set ι)ᶜ), min ((1/2)^(encode (i : ι))) (dist (x i) (y i)) :
          (sum_add_tsum_compl (dist_summable _ _)).symm
        ... ≤ ∑ i in K, (dist (x i) (y i))
             + ∑' (i : (↑K : set ι)ᶜ), (1/2)^(encode (i : ι)) :
          begin
            refine add_le_add (finset.sum_le_sum (λ i hi, min_le_right _ _)) _,
            refine tsum_le_tsum (λ i, min_le_left _ _) _ _,
            { apply summable.subtype (dist_summable x y) (↑K : set ι)ᶜ },
            { apply summable.subtype summable_geometric_two_encode (↑K : set ι)ᶜ }
          end
        ... < (∑ i in K, δ) + ε / 2 :
          begin
            apply add_lt_add_of_le_of_lt _ hK,
            apply finset.sum_le_sum (λ i hi, _),
            apply (hxy i _).le,
            simpa using hi
          end
        ... ≤ ε / 2 + ε / 2 :
          add_le_add_right (by simpa only [finset.sum_const, nsmul_eq_mul] using hδ) _
        ... = ε : add_halves _ } },
    { simp only [le_infi_iff, le_principal_iff],
      assume i ε εpos,
      refine mem_infi_of_mem (min ((1/2)^(encode i)) ε) _,
      have : 0 < min ((1/2)^(encode i)) ε := lt_min (by simp) εpos,
      refine mem_infi_of_mem this _,
      simp only [and_imp, prod.forall, set_of_subset_set_of, lt_min_iff, mem_principal],
      assume x y hn hε,
      calc dist (x i) (y i) ≤ dist x y : dist_le_dist_pi_of_dist_lt hn
      ... < ε : hε }
  end }

end pi_countable
