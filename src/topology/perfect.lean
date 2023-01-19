/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import topology.separation
import topology.bases
import topology.metric_space.pi_nat

/-!
# Perfect Sets

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.
* `set.scheme β α`: A `β`-scheme on `α`, a collection of subsets of `α` indexed by `list β`.
  Used to construct maps `(β → ℕ) → α` as limiting objects.

## Main Statements

* `perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_is_closed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.
* `exists_nat_bool_injection_of_perfect_nonempty`: A perfect nonempty set in a complete metric space
  admits an embedding from the Cantor space.

## Implementation Notes

We do not require perfect sets to be nonempty.

We define a nonstandard predicate, `preperfect`, which drops the closed-ness requirement
from the definition of perfect. In T1 spaces, this is equivalent to having a perfect closure,
see `preperfect_iff_perfect_closure`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, Cantor-Bendixson.

-/

open_locale topological_space filter
open topological_space filter set

section basic

variables {α : Type*} [topological_space α] {C : set α}

/-- If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`. -/
theorem acc_pt.nhds_inter {x : α} {U : set α} (h_acc : acc_pt x (𝓟 C)) (hU : U ∈ 𝓝 x) :
  acc_pt x (𝓟 (U ∩ C)) :=
begin
  have : 𝓝[≠] x ≤ 𝓟 U,
  { rw le_principal_iff,
    exact mem_nhds_within_of_mem_nhds hU, },
  rw [acc_pt, ← inf_principal, ← inf_assoc, inf_of_le_left this],
  exact h_acc,
end

/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `C` is nonempty and `α` is a T1 space, this is equivalent to the closure of `C` being perfect.
See `preperfect_iff_perfect_closure`.-/
def preperfect (C : set α) : Prop := ∀ x ∈ C, acc_pt x (𝓟 C)

/-- A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty.-/
structure perfect (C : set α) : Prop :=
(closed : is_closed C)
(acc : preperfect C)

lemma preperfect_iff_nhds : preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x :=
by simp only [preperfect, acc_pt_iff_nhds]

/-- The intersection of a preperfect set and an open set is preperfect-/
theorem preperfect.open_inter {U : set α} (hC : preperfect C) (hU : is_open U) :
  preperfect (U ∩ C) :=
begin
  rintros x ⟨xU, xC⟩,
  apply (hC _ xC).nhds_inter,
  exact hU.mem_nhds xU,
end

/-- The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`-/
theorem preperfect.perfect_closure (hC : preperfect C) : perfect (closure C) :=
begin
  split, { exact is_closed_closure },
  intros x hx,
  by_cases h : x ∈ C; apply acc_pt.mono _ (principal_mono.mpr subset_closure),
  { exact hC _ h },
  have : {x}ᶜ ∩ C = C := by simp [h],
  rw [acc_pt, nhds_within, inf_assoc, inf_principal, this],
  rw [closure_eq_cluster_pts] at hx,
  exact hx,
end

/-- In a T1 space, being preperfect is equivalent to having perfect closure.-/
theorem preperfect_iff_perfect_closure [t1_space α] :
  preperfect C ↔ perfect (closure C) :=
begin
  split; intro h, { exact h.perfect_closure },
  intros x xC,
  have H : acc_pt x (𝓟 (closure C)) := h.acc _ (subset_closure xC),
  rw acc_pt_iff_frequently at *,
  have : ∀ y , y ≠ x ∧ y ∈ closure C → ∃ᶠ z in 𝓝 y, z ≠ x ∧ z ∈ C,
  { rintros y ⟨hyx, yC⟩,
    simp only [← mem_compl_singleton_iff, @and_comm _ (_ ∈ C) , ← frequently_nhds_within_iff,
      hyx.nhds_within_compl_singleton, ← mem_closure_iff_frequently],
    exact yC, },
  rw ← frequently_frequently_nhds,
  exact H.mono this,
end

theorem perfect.closure_nhds_inter {U : set α} (hC : perfect C) (x : α) (xC : x ∈ C) (xU : x ∈ U)
  (Uop : is_open U) : perfect (closure (U ∩ C)) ∧ (closure (U ∩ C)).nonempty :=
begin
  split,
  { apply preperfect.perfect_closure,
    exact (hC.acc).open_inter Uop, },
  apply nonempty.closure,
  exact ⟨x, ⟨xU, xC⟩⟩,
end

/-- Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect subsets
This is the main inductive step in the proof of the Cantor-Bendixson Theorem-/
lemma perfect.splitting [t2_5_space α] (hC : perfect C) (hnonempty : C.nonempty) :
  ∃ C₀ C₁ : set α, (perfect C₀ ∧ C₀.nonempty ∧ C₀ ⊆ C) ∧
  (perfect C₁ ∧ C₁.nonempty ∧ C₁ ⊆ C) ∧ disjoint C₀ C₁ :=
begin
  cases hnonempty with y yC,
  obtain ⟨x, xC, hxy⟩ : ∃ x ∈ C, x ≠ y,
  { have := hC.acc _ yC,
    rw acc_pt_iff_nhds at this,
    rcases this univ (univ_mem) with ⟨x, xC, hxy⟩,
    exact ⟨x, xC.2, hxy⟩, },
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy,
  use [closure (U ∩ C), closure (V ∩ C)],
  split; rw ← and_assoc,
  { refine ⟨hC.closure_nhds_inter x xC xU Uop, _⟩,
    rw hC.closed.closure_subset_iff,
    exact inter_subset_right _ _, },
  split,
  { refine ⟨hC.closure_nhds_inter y yC yV Vop, _⟩,
    rw hC.closed.closure_subset_iff,
    exact inter_subset_right _ _, },
  apply disjoint.mono _ _ hUV; apply closure_mono; exact inter_subset_left _ _,
end

section kernel

/-- The **Cantor-Bendixson Theorem**: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set.-/
theorem exists_countable_union_perfect_of_is_closed [second_countable_topology α]
  (hclosed : is_closed C) :
  ∃ V D : set α, (V.countable) ∧ (perfect D) ∧ (C = V ∪ D) :=
begin
  obtain ⟨b, bct, bnontrivial, bbasis⟩ := topological_space.exists_countable_basis α,
  let v := {U ∈ b | (U ∩ C).countable},
  let V := ⋃ U ∈ v, U,
  let D := C \ V,
  have Vct : (V ∩ C).countable,
  { simp only [Union_inter, mem_sep_iff],
    apply countable.bUnion,
    { exact countable.mono (inter_subset_left _ _) bct, },
    { exact inter_subset_right _ _, }, },
  refine ⟨V ∩ C, D, Vct, ⟨_, _⟩, _⟩,
  { refine hclosed.sdiff (is_open_bUnion (λ U, _)),
    exact λ ⟨Ub, _⟩, is_topological_basis.is_open bbasis Ub, },
  { rw preperfect_iff_nhds,
    intros x xD E xE,
    have : ¬ (E ∩ D).countable,
    { intro h,
      obtain ⟨U, hUb, xU, hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E,
      { exact (is_topological_basis.mem_nhds_iff bbasis).mp xE, },
      have hU_cnt : (U ∩ C).countable,
      { apply @countable.mono _ _ ((E ∩ D) ∪ (V ∩ C)),
        { rintros y ⟨yU, yC⟩,
          by_cases y ∈ V,
          { exact mem_union_right _ (mem_inter h yC), },
          { exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩), }, },
        exact countable.union h Vct, },
      have : U ∈ v := ⟨hUb, hU_cnt⟩,
      apply xD.2,
      exact mem_bUnion this xU, },
    by_contradiction h,
    push_neg at h,
    exact absurd (countable.mono h (set.countable_singleton _)) this, },
  { rw [inter_comm, inter_union_diff], },
end

/-- Any uncountable closed set in a second countable space contains a nonempty perfect subset.-/
theorem exists_perfect_nonempty_of_is_closed_of_not_countable [second_countable_topology α]
  (hclosed : is_closed C) (hunc : ¬ C.countable) :
  ∃ D : set α, perfect D ∧ D.nonempty ∧ D ⊆ C :=
begin
  rcases exists_countable_union_perfect_of_is_closed hclosed with ⟨V, D, Vct, Dperf, VD⟩,
  refine ⟨D, ⟨Dperf, _⟩⟩,
  split,
  { rw nonempty_iff_ne_empty,
    by_contradiction,
    rw [h, union_empty] at VD,
    rw VD at hunc,
    contradiction, },
  rw VD,
  exact subset_union_right _ _,
end

end kernel
end basic

section scheme

/-- A `β`-scheme on `α` is a function from `list β` to `set α`.
We typically think of this as a "tree" of subsets of `α`, and use the appropriate terminology
(branch, children, etc.).
The usefulness of such a scheme is that a map `(ℕ → β) → α` can often be thought of as
a sort of "limiting object" of a `β`-scheme on `α`. -/
def set.scheme (β α : Type*) := list β → set α

namespace set.scheme
open list metric function
open_locale classical

variables {β α : Type*} (A : set.scheme β α)

/-- `res x n`, or the restriction of `x` to `n`,
is the list of length `n` whose `m`-th entry is `x m`.-/
def res (x : ℕ → β) : ℕ → list β
  | 0            := nil
  | (nat.succ n) := (res n).concat (x n)

@[simp] lemma res_zero (x : ℕ → α) : res x 0 = @nil α := rfl
@[simp] lemma res_succ (x : ℕ → α) (n : ℕ) : res x n.succ = (res x n).concat (x n) := rfl

@[simp] lemma res_length (x : ℕ → α) (n : ℕ) : (res x n).length = n :=
begin
  induction n with n ih,
  { refl },
  simp[ih],
end

/-- The restrictions of `x` and `y` to `n` are equal if and only if `x m = y m` for all `m < n`.-/
lemma res_eq_iff (x y : ℕ → α) (n : ℕ) : res x n = res y n ↔ ∀ m < n, x m = y m :=
begin
  split; intro h; induction n with n ih, { simp },
  { intros m hm,
    rw nat.lt_succ_iff_lt_or_eq at hm,
    rw [← reverse_inj] at h,
    simp only [res_succ, concat_eq_append, reverse_append, reverse_singleton,
      singleton_append, reverse_inj] at h,
    cases hm with hm hm,
    { exact ih h.2 _ hm },
    rw hm,
    exact h.1, },
  { simp },
  simp only [res_succ],
  rw [ih _, h _ (nat.lt_succ_self _)],
  intros m hmn,
  exact h m (hmn.trans (nat.lt_succ_self _)),
end

/-- Two infinite sequences are equal if and only if all their restrictions are.-/
theorem eq_iff_res_eq (x y : ℕ → α) : (∀ n, res x n = res y n) ↔ x = y :=
begin
  split; intro h,
  { ext n,
    specialize h n.succ,
    rw res_eq_iff at h,
    exact h _ (nat.lt_succ_self _), },
  rw h,
  simp,
end

/-- `cylinder x n` is equal to the set of sequences `y` with the same restriction to `n` as `x`.-/
theorem cylinder_eq_res (x : ℕ → α) (n : ℕ) : pi_nat.cylinder x n = {y | res y n = res x n} :=
begin
  ext y,
  dsimp[pi_nat.cylinder],
  rw res_eq_iff,
end

/-- From a `β`-scheme on `α` `A`, we define a partial function from `(ℕ → β)` to `α`
which sends each infinite sequence `x` to an element of the intersection along the
branch corresponding to `x`, if it exists.
We call this the map induced by the scheme. -/
noncomputable def map : Σ s : set (ℕ → β), s → α :=
⟨λ x, set.nonempty ⋂ n : ℕ, A (res x n), λ ⟨x, hx⟩, hx.some⟩

/-- A scheme is antitone if each set contains its children.  -/
def antitone : Prop := ∀ l : list β, ∀ a : β, A (l.concat a) ⊆ A l

/-- A useful strengthening of being antitone is to require that each set contains
the closure of each of its children. -/
def closure_antitone [topological_space α] : Prop :=
∀ l : list β, ∀ a : β, closure(A (l.concat a)) ⊆ A l

/-- A scheme is disjoint if the children of each set of pairwise disjoint. -/
def disjoint : Prop := ∀ l : list β, ∀ a b : β, a ≠ b →
  disjoint (A (l.concat a)) (A (l.concat b))

/-- A scheme on a metric space has vanishing diameter if diameter approaches 0 along each branch. -/
def vanishing_diam [pseudo_metric_space α] : Prop :=
∀ x : ℕ → β, tendsto (λ n : ℕ, emetric.diam (A (res x n))) at_top (𝓝 0)

variable {A}

/-- If `x` is in the domain of the induced map of a scheme `A`,
its image under this map is in each set along the corresponding branch. -/
lemma map_mem {x : ℕ → β} (hx : x ∈ A.map.1) (n : ℕ) : A.map.2 ⟨x, hx⟩ ∈ A (res x n) :=
begin
  have := hx.some_mem,
  rw mem_Inter at this,
  exact this n,
end

lemma antitone_of_closure_antitoine [topological_space α] (hA : closure_antitone A) : antitone A :=
λ l a, subset_closure.trans (hA l a)

lemma closure_antitone_of_antitone_of_is_closed [topological_space α] (hanti : antitone A)
  (hclosed : ∀ l, is_closed (A l)) : closure_antitone A :=
begin
  intros l a,
  rw (hclosed _).closure_eq,
  apply hanti,
end

lemma small_dist_of_vanishing_diam [pseudo_metric_space α] (hA : vanishing_diam A)
  (ε : ℝ) (ε_pos : ε > 0) (x : ℕ → β) :
  ∃ n : ℕ, ∀ y z ∈ A (res x n), dist y z < ε :=
begin
  specialize hA x,
  rw ennreal.tendsto_at_top_zero at hA,
  cases hA (ennreal.of_real (ε / 2))
    (by { simp only [gt_iff_lt, ennreal.of_real_pos], linarith }) with n hn,
  use n,
  intros y hy z hz,
  rw [← ennreal.of_real_lt_of_real_iff ε_pos, ← edist_dist],
  apply lt_of_le_of_lt (emetric.edist_le_diam_of_mem hy hz),
  apply lt_of_le_of_lt (hn _ (le_refl _)),
  rw ennreal.of_real_lt_of_real_iff ε_pos,
  linarith,
end

/-- A scheme with vanishing diameter along each branch induces a continuous map. -/
theorem map_continuous_of_vanishing_diam [pseudo_metric_space α] [topological_space β]
  [discrete_topology β] (hA : vanishing_diam A) : continuous A.map.2 :=
begin
  rw metric.continuous_iff',
  rintros ⟨x, hx⟩ ε ε_pos,
  cases small_dist_of_vanishing_diam hA _ ε_pos x with n hn,
  rw _root_.eventually_nhds_iff,
  refine ⟨coe ⁻¹' (pi_nat.cylinder x n), _, _, by simp⟩,
  { rintros ⟨y, hy⟩ hyx,
    rw [mem_preimage, subtype.coe_mk, cylinder_eq_res, mem_set_of] at hyx,
    apply hn,
    { rw ← hyx,
      apply map_mem, },
    apply map_mem, },
  apply continuous_subtype_coe.is_open_preimage,
  apply pi_nat.is_open_cylinder,
end

/-- A scheme with vanishing diameter such that each set contains the closure of its children
induces a total map. -/
theorem map_total_of_vanishing_diam_of_closure_antitone [pseudo_metric_space α] [complete_space α]
  (hdiam : vanishing_diam A) (hanti : closure_antitone A) (hnonempty : ∀ l, (A l).nonempty ) :
  A.map.1 = univ :=
begin
  rw eq_univ_iff_forall,
  intro x,
  have : ∀ n : ℕ, (A (res x n)).nonempty := λ n, hnonempty _,
  choose u hu using this,
  have umem : ∀ n m : ℕ, n ≤ m → u m ∈ A (res x n),
  { have : _root_.antitone (λ n : ℕ, A (res x n)),
    { refine antitone_nat_of_succ_le _,
      intro n,
      rw res_succ,
      apply antitone_of_closure_antitoine hanti, },
    intros n m hnm,
    exact this hnm (hu _), },
  have : cauchy_seq u,
  { rw metric.cauchy_seq_iff,
    intros ε ε_pos,
    cases small_dist_of_vanishing_diam hdiam _ ε_pos x with n hn,
    use n,
    intros m₀ hm₀ m₁ hm₁,
    apply hn; apply umem; assumption, },
  cases cauchy_seq_tendsto_of_complete this with y hy,
  use y,
  rw mem_Inter,
  intro n,
  apply hanti _ (x n),
  apply mem_closure_of_tendsto hy,
  rw [← res_succ, eventually_at_top],
  use n.succ,
  intros m hm,
  exact umem _ _ hm,
end

/-- A scheme where the children of each set are pairwise disjoint induces an injective map. -/
theorem map_injective_of_disjoint (hA : disjoint A) : injective A.map.2 :=
begin
  rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
  rw [← subtype.val_inj, ← eq_iff_res_eq],
  intro n,
  induction n with n ih, { simp },
  simp only [res_succ],
  suffices : x n = y n, { rw [ih, this] },
  contrapose hA,
  simp only [disjoint, ne.def, not_forall, exists_prop],
  refine ⟨res x n, _, _, hA, _⟩,
  rw not_disjoint_iff,
  use A.map.2 ⟨x, hx⟩,
  split,
  { rw ← res_succ,
    apply map_mem, },
  rw [hxy, ih, ← res_succ],
  apply map_mem,
end

end set.scheme
end scheme

section cantor_inj

open function
variables {α : Type*} [metric_space α] {C : set α} (hC : perfect C)
include hC

lemma perfect.small_diam_aux (ε : ennreal) (ε_pos : ε > 0) {x : α} (xC : x ∈ C) :
  let D := closure (emetric.ball x (ε / 2) ∩ C) in
  perfect D ∧ D.nonempty ∧ D ⊆ C ∧ emetric.diam D ≤ ε :=
begin
  have : x ∈ (emetric.ball x (ε / 2)),
  { apply emetric.mem_ball_self,
    rw ennreal.div_pos_iff,
    exact ⟨ne_of_gt ε_pos, by norm_num⟩, },
  have := hC.closure_nhds_inter x xC this emetric.is_open_ball,
  refine ⟨this.1, this.2, _, _⟩,
  { rw is_closed.closure_subset_iff hC.closed,
    apply inter_subset_right, },
  rw emetric.diam_closure,
  apply le_trans (emetric.diam_mono (inter_subset_left _ _)),
  convert emetric.diam_ball,
  rw [mul_comm, ennreal.div_mul_cancel]; norm_num,
end

variable (hnonempty : C.nonempty)
include hnonempty

/-- A refinement of `perfect.splitting` for metric spaces, where we also control
the diameter of the new perfect sets. -/
lemma perfect.small_diam_splitting (ε : ennreal) (ε_pos : ε > 0) : ∃ C₀ C₁ : set α,
  (perfect C₀ ∧ C₀.nonempty ∧ C₀ ⊆ C ∧ emetric.diam C₀ ≤ ε) ∧
  (perfect C₁ ∧ C₁.nonempty ∧ C₁ ⊆ C ∧ emetric.diam C₁ ≤ ε) ∧ disjoint C₀ C₁ :=
begin
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩,
  cases non0 with x₀ hx₀,
  cases non1 with x₁ hx₁,
  rcases perf0.small_diam_aux _ ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩,
  rcases perf1.small_diam_aux _ ε_pos hx₁ with ⟨perf1', non1', sub1', diam1⟩,
  refine ⟨closure (emetric.ball x₀ (ε / 2) ∩ D₀), closure (emetric.ball x₁ (ε / 2) ∩ D₁),
    ⟨perf0', non0', sub0'.trans sub0, diam0⟩, ⟨perf1', non1', sub1'.trans sub1, diam1⟩, _⟩,
  apply disjoint.mono _ _ hdisj; assumption,
end

open set.scheme

/-- Any nonempty perfect set in a complete metric space admits a continuous injection
from the cantor space, `ℕ → bool`. -/
theorem exists_nat_bool_injection_of_perfect_nonempty [complete_space α]
  (hC : perfect C) (hnonempty : C.nonempty) :
  ∃ f : (ℕ → bool) → α, (range f) ⊆ C ∧ continuous f ∧ injective f :=
begin
  let u : ℕ → ennreal := λ n, n⁻¹,
  have upos : ∀ n, 0 < (u n) := λ n, by simp,
  let P := subtype (λ E : set α, perfect E ∧ E.nonempty),
  choose C0 C1 h0 h1 hdisj using @perfect.small_diam_splitting α infer_instance,
  change ∀ {C} {hC : perfect C} {hnonempty : C.nonempty} {ε : ennreal} {ε_pos : ε > 0}, _ at h0,
  change ∀ {C} {hC : perfect C} {hnonempty : C.nonempty} {ε : ennreal} {ε_pos : ε > 0}, _ at h1,
  change ∀ {C} {hC : perfect C} {hnonempty : C.nonempty} {ε : ennreal} {ε_pos : ε > 0}, _ at hdisj,
  let DP : list bool → P := λ l,
  begin
    induction l using list.reverse_rec_on with l a ih, { exact ⟨C, ⟨hC, hnonempty⟩⟩ },
    cases a,
    { use C0 ih.property.1 ih.property.2 (u l.length.succ) (upos _),
      exact ⟨h0.1, h0.2.1⟩, },
    use C1 ih.property.1 ih.property.2 (u l.length.succ) (upos _),
    exact ⟨h1.1, h1.2.1⟩,
  end,
  let D : set.scheme bool α := λ l, (DP l).val,
  have Ddef : ∀ l : list bool, ∀ a : bool, D (l.concat a) = bool.rec --this is terrible
    (C0 (DP l).property.1 (DP l).property.2 (u l.length.succ) (upos l.length.succ))
    (C1 (DP l).property.1 (DP l).property.2 (u l.length.succ) (upos l.length.succ)) a,
  { intros l a,
    dsimp[D, DP, list.reverse_rec_on],
    rw list.reverse_concat,
    dsimp,
    rw list.reverse_reverse,
    cases a; refl, },
  have hanti : closure_antitone D,
  { refine closure_antitone_of_antitone_of_is_closed _ (λ l, (DP l).property.1.closed),
    intros l a,
    rw Ddef,
    cases a,
    { exact h0.2.2.1, },
    exact h1.2.2.1, },
  have hdiam : vanishing_diam D,
  { intro x,
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ennreal.tendsto_inv_nat_nhds_zero; intro n,
    { exact zero_le' },
    cases n, { simp },
    dsimp,
    rw [Ddef, res_length],
    cases (x n),
    { exact h0.2.2.2, },
    exact h1.2.2.2, },
  have hdisj : disjoint D,
  { intros l a b hab,
    cases a; cases b; try { contradiction }; rw[Ddef, Ddef],
    { exact hdisj, },
    exact hdisj.symm,  },
  have hdom : ∀ {x : ℕ → bool}, x ∈ D.map.1 := λ x,
    by simp[map_total_of_vanishing_diam_of_closure_antitone hdiam hanti (λ l, (DP l).property.2)],
  refine ⟨λ x, D.map.2 ⟨x, hdom⟩, _, _, _⟩,
  { rintros y ⟨x, rfl⟩,
    convert map_mem hdom 0,
    dsimp[D, DP, list.reverse_rec_on],
    refl, },
  { continuity,
    exact map_continuous_of_vanishing_diam hdiam, },
  intros x y hxy,
  have := map_injective_of_disjoint hdisj hxy,
  rwa ← subtype.val_inj at this,
end

end cantor_inj
