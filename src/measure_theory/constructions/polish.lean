/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.polish
import measure_theory.constructions.borel_space

/-!
# The Borel sigma-algebra on Polish spaces

We discuss several results pertaining to the relationship between the topology and the Borel
structure on Polish spaces.

## Main definitions and results

First, we define the class of analytic sets and establish its basic properties.

* `measure_theory.analytic_set s`: a set in a topological space is analytic if it is the continuous
  image of a Polish space. Equivalently, it is empty, or the image of `ℕ → ℕ`.
* `measure_theory.analytic_set.image_of_continuous`: a continuous image of an analytic set is
  analytic.
* `measurable_set.analytic_set`: in a Polish space, any Borel-measurable set is analytic.

Then, we show Lusin's theorem that two disjoint analytic sets can be separated by Borel sets.

* `measurably_separable s t` states that there exists a measurable set containing `s` and disjoint
  from `t`.
* `analytic_set.measurably_separable` shows that two disjoint analytic sets are separated by a
  Borel set.

Finally, we prove the Lusin-Souslin theorem that a continuous injective image of a Borel subset of
a Polish space is Borel. The proof of this nontrivial result relies on the above results on
analytic sets.

* `measurable_set.image_of_continuous_on_inj_on` asserts that, if `s` is a Borel measurable set in
  a Polish space, then the image of `s` under a continuous injective map is still Borel measurable.
* `continuous.measurable_embedding` states that a continuous injective map on a Polish space
  is a measurable embedding for the Borel sigma-algebra.
* `continuous_on.measurable_embedding` is the same result for a map restricted to a measurable set
  on which it is continuous.
* `measurable.measurable_embedding` states that a measurable injective map from a Polish space
  to a second-countable topological space is a measurable embedding.
* `is_clopenable_iff_measurable_set`: in a Polish space, a set is clopenable (i.e., it can be made
  open and closed by using a finer Polish topology) if and only if it is Borel-measurable.
-/

open set function polish_space pi_nat topological_space metric filter
open_locale topology measure_theory filter

variables {α : Type*} [topological_space α] {ι : Type*}

namespace measure_theory

/-! ### Analytic sets -/

/-- An analytic set is a set which is the continuous image of some Polish space. There are several
equivalent characterizations of this definition. For the definition, we pick one that avoids
universe issues: a set is analytic if and only if it is a continuous image of `ℕ → ℕ` (or if it
is empty). The above more usual characterization is given
in `analytic_set_iff_exists_polish_space_range`.

Warning: these are analytic sets in the context of descriptive set theory (which is why they are
registered in the namespace `measure_theory`). They have nothing to do with analytic sets in the
context of complex analysis. -/
@[irreducible] def analytic_set (s : set α) : Prop :=
s = ∅ ∨ ∃ (f : (ℕ → ℕ) → α), continuous f ∧ range f = s

lemma analytic_set_empty : analytic_set (∅ : set α) :=
begin
  rw analytic_set,
  exact or.inl rfl
end

lemma analytic_set_range_of_polish_space
  {β : Type*} [topological_space β] [polish_space β] {f : β → α} (f_cont : continuous f) :
  analytic_set (range f) :=
begin
  casesI is_empty_or_nonempty β,
  { rw range_eq_empty,
    exact analytic_set_empty },
  { rw analytic_set,
    obtain ⟨g, g_cont, hg⟩ : ∃ (g : (ℕ → ℕ) → β), continuous g ∧ surjective g :=
      exists_nat_nat_continuous_surjective β,
    refine or.inr ⟨f ∘ g, f_cont.comp g_cont, _⟩,
    rwa hg.range_comp }
end

/-- The image of an open set under a continuous map is analytic. -/
lemma _root_.is_open.analytic_set_image {β : Type*} [topological_space β] [polish_space β]
  {s : set β} (hs : is_open s) {f : β → α} (f_cont : continuous f) :
  analytic_set (f '' s) :=
begin
  rw image_eq_range,
  haveI : polish_space s := hs.polish_space,
  exact analytic_set_range_of_polish_space (f_cont.comp continuous_subtype_coe),
end

/-- A set is analytic if and only if it is the continuous image of some Polish space. -/
theorem analytic_set_iff_exists_polish_space_range {s : set α} :
  analytic_set s ↔ ∃ (β : Type) (h : topological_space β) (h' : @polish_space β h) (f : β → α),
    @continuous _ _ h _ f ∧ range f = s :=
begin
  split,
  { assume h,
    rw analytic_set at h,
    cases h,
    { refine ⟨empty, by apply_instance, by apply_instance, empty.elim, continuous_bot, _⟩,
      rw h,
      exact range_eq_empty _ },
    { exact ⟨ℕ → ℕ, by apply_instance, by apply_instance, h⟩ } },
  { rintros ⟨β, h, h', f, f_cont, f_range⟩,
    resetI,
    rw ← f_range,
    exact analytic_set_range_of_polish_space f_cont }
end

/-- The continuous image of an analytic set is analytic -/
lemma analytic_set.image_of_continuous_on {β : Type*} [topological_space β]
  {s : set α} (hs : analytic_set s) {f : α → β} (hf : continuous_on f s) :
  analytic_set (f '' s) :=
begin
  rcases analytic_set_iff_exists_polish_space_range.1 hs with ⟨γ, γtop, γpolish, g, g_cont, gs⟩,
  resetI,
  have : f '' s = range (f ∘ g), by rw [range_comp, gs],
  rw this,
  apply analytic_set_range_of_polish_space,
  apply hf.comp_continuous g_cont (λ x, _),
  rw ← gs,
  exact mem_range_self _
end

lemma analytic_set.image_of_continuous {β : Type*} [topological_space β]
  {s : set α} (hs : analytic_set s) {f : α → β} (hf : continuous f) :
  analytic_set (f '' s) :=
hs.image_of_continuous_on hf.continuous_on

/-- A countable intersection of analytic sets is analytic. -/
theorem analytic_set.Inter [hι : nonempty ι] [countable ι] [t2_space α]
  {s : ι → set α} (hs : ∀ n, analytic_set (s n)) :
  analytic_set (⋂ n, s n) :=
begin
  unfreezingI { rcases hι with ⟨i₀⟩ },
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
  Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
  `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, and the
  range of `x ↦ f 0 (x 0)` on `t` is exactly `⋂ n, s n`, so this set is analytic. -/
  choose β hβ h'β f f_cont f_range using λ n, analytic_set_iff_exists_polish_space_range.1 (hs n),
  resetI,
  let γ := Π n, β n,
  let t : set γ := ⋂ n, {x | f n (x n) = f i₀ (x i₀)},
  have t_closed : is_closed t,
  { apply is_closed_Inter,
    assume n,
    exact is_closed_eq ((f_cont n).comp (continuous_apply n))
      ((f_cont i₀).comp (continuous_apply i₀)) },
  haveI : polish_space t := t_closed.polish_space,
  let F : t → α := λ x, f i₀ ((x : γ) i₀),
  have F_cont : continuous F :=
    (f_cont i₀).comp ((continuous_apply i₀).comp continuous_subtype_coe),
  have F_range : range F = ⋂ (n : ι), s n,
  { apply subset.antisymm,
    { rintros y ⟨x, rfl⟩,
      apply mem_Inter.2 (λ n, _),
      have : f n ((x : γ) n) = F x := (mem_Inter.1 x.2 n : _),
      rw [← this, ← f_range n],
      exact mem_range_self _ },
    { assume y hy,
      have A : ∀ n, ∃ (x : β n), f n x = y,
      { assume n,
        rw [← mem_range, f_range n],
        exact mem_Inter.1 hy n },
      choose x hx using A,
      have xt : x ∈ t,
      { apply mem_Inter.2 (λ n, _),
        simp [hx] },
        refine ⟨⟨x, xt⟩, _⟩,
        exact hx i₀ } },
  rw ← F_range,
  exact analytic_set_range_of_polish_space F_cont,
end

/-- A countable union of analytic sets is analytic. -/
theorem analytic_set.Union [countable ι] {s : ι → set α} (hs : ∀ n, analytic_set (s n)) :
  analytic_set (⋃ n, s n) :=
begin
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
  Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
  coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using λ n, analytic_set_iff_exists_polish_space_range.1 (hs n),
  resetI,
  let γ := Σ n, β n,
  let F : γ → α := by { rintros ⟨n, x⟩, exact f n x },
  have F_cont : continuous F := continuous_sigma f_cont,
  have F_range : range F = ⋃ n, s n,
  { rw [range_sigma_eq_Union_range],
    congr,
    ext1 n,
    rw ← f_range n },
  rw ← F_range,
  exact analytic_set_range_of_polish_space F_cont,
end

theorem _root_.is_closed.analytic_set [polish_space α] {s : set α} (hs : is_closed s) :
  analytic_set s :=
begin
  haveI : polish_space s := hs.polish_space,
  rw ← @subtype.range_val α s,
  exact analytic_set_range_of_polish_space continuous_subtype_coe,
end

/-- Given a Borel-measurable set in a Polish space, there exists a finer Polish topology making
it clopen. This is in fact an equivalence, see `is_clopenable_iff_measurable_set`. -/
lemma _root_.measurable_set.is_clopenable [polish_space α] [measurable_space α] [borel_space α]
  {s : set α} (hs : measurable_set s) :
  is_clopenable s :=
begin
  revert s,
  apply measurable_set.induction_on_open,
  { exact λ u hu, hu.is_clopenable },
  { exact λ u hu h'u, h'u.compl },
  { exact λ f f_disj f_meas hf, is_clopenable.Union hf }
end

theorem _root_.measurable_set.analytic_set
  {α : Type*} [t : topological_space α] [polish_space α] [measurable_space α] [borel_space α]
  {s : set α} (hs : measurable_set s) :
  analytic_set s :=
begin
  /- For a short proof (avoiding measurable induction), one sees `s` as a closed set for a finer
  topology `t'`. It is analytic for this topology. As the identity from `t'` to `t` is continuous
  and the image of an analytic set is analytic, it follows that `s` is also analytic for `t`. -/
  obtain ⟨t', t't, t'_polish, s_closed, s_open⟩ :
    ∃ t' : topological_space α, t' ≤ t ∧ @polish_space α t' ∧ is_closed[t'] s ∧ is_open[t'] s :=
    hs.is_clopenable,
  have A := @is_closed.analytic_set α t' t'_polish s s_closed,
  convert @analytic_set.image_of_continuous α t' α t s A id (continuous_id_of_le t't),
  simp only [id.def, image_id'],
end

/-- Given a Borel-measurable function from a Polish space to a second-countable space, there exists
a finer Polish topology on the source space for which the function is continuous. -/
lemma _root_.measurable.exists_continuous {α β : Type*}
  [t : topological_space α] [polish_space α] [measurable_space α] [borel_space α]
  [tβ : topological_space β] [second_countable_topology β] [measurable_space β] [borel_space β]
  {f : α → β} (hf : measurable f) :
  ∃ (t' : topological_space α), t' ≤ t ∧ @continuous α β t' tβ f ∧ @polish_space α t' :=
begin
  obtain ⟨b, b_count, -, hb⟩ : ∃b : set (set β), b.countable ∧ ∅ ∉ b ∧ is_topological_basis b :=
    exists_countable_basis β,
  haveI : encodable b := b_count.to_encodable,
  have : ∀ (s : b), is_clopenable (f ⁻¹' s),
  { assume s,
    apply measurable_set.is_clopenable,
    exact hf (hb.is_open s.2).measurable_set },
  choose T Tt Tpolish Tclosed Topen using this,
  obtain ⟨t', t'T, t't, t'_polish⟩ :
    ∃ (t' : topological_space α), (∀ i, t' ≤ T i) ∧ (t' ≤ t) ∧ @polish_space α t' :=
      exists_polish_space_forall_le T Tt Tpolish,
  refine ⟨t', t't, _, t'_polish⟩,
  apply hb.continuous _ (λ s hs, _),
  exact t'T ⟨s, hs⟩ _ (Topen ⟨s, hs⟩),
end

/-! ### Separating sets with measurable sets -/

/-- Two sets `u` and `v` in a measurable space are measurably separable if there
exists a measurable set containing `u` and disjoint from `v`.
This is mostly interesting for Borel-separable sets. -/
def measurably_separable {α : Type*} [measurable_space α] (s t : set α) : Prop :=
∃ u, s ⊆ u ∧ disjoint t u ∧ measurable_set u

lemma measurably_separable.Union [countable ι]
  {α : Type*} [measurable_space α] {s t : ι → set α}
  (h : ∀ m n, measurably_separable (s m) (t n)) :
  measurably_separable (⋃ n, s n) (⋃ m, t m) :=
begin
  choose u hsu htu hu using h,
  refine ⟨⋃ m, (⋂ n, u m n), _, _, _⟩,
  { refine Union_subset (λ m, subset_Union_of_subset m _),
    exact subset_Inter (λ n, hsu m n) },
  { simp_rw [disjoint_Union_left, disjoint_Union_right],
    assume n m,
    apply disjoint.mono_right _ (htu m n),
    apply Inter_subset },
  { refine measurable_set.Union (λ m, _),
    exact measurable_set.Inter (λ n, hu m n) }
end

/-- The hard part of the Lusin separation theorem saying that two disjoint analytic sets are
contained in disjoint Borel sets (see the full statement in `analytic_set.measurably_separable`).
Here, we prove this when our analytic sets are the ranges of functions from `ℕ → ℕ`.
-/
lemma measurably_separable_range_of_disjoint [t2_space α] [measurable_space α] [borel_space α]
  {f g : (ℕ → ℕ) → α} (hf : continuous f) (hg : continuous g) (h : disjoint (range f) (range g)) :
  measurably_separable (range f) (range g) :=
begin
  /- We follow [Kechris, *Classical Descriptive Set Theory* (Theorem 14.7)][kechris1995].
  If the ranges are not Borel-separated, then one can find two cylinders of length one whose images
  are not Borel-separated, and then two smaller cylinders of length two whose images are not
  Borel-separated, and so on. One thus gets two sequences of cylinders, that decrease to two
  points `x` and `y`. Their images are different by the disjointness assumption, hence contained
  in two disjoint open sets by the T2 property. By continuity, long enough cylinders around `x`
  and `y` have images which are separated by these two disjoint open sets, a contradiction.
  -/
  by_contra hfg,
  have I : ∀ n x y, (¬(measurably_separable (f '' (cylinder x n)) (g '' (cylinder y n))))
    → ∃ x' y', x' ∈ cylinder x n ∧ y' ∈ cylinder y n ∧
                ¬(measurably_separable (f '' (cylinder x' (n+1))) (g '' (cylinder y' (n+1)))),
  { assume n x y,
    contrapose!,
    assume H,
    rw [← Union_cylinder_update x n, ← Union_cylinder_update y n, image_Union, image_Union],
    refine measurably_separable.Union (λ i j, _),
    exact H _ _ (update_mem_cylinder _ _ _) (update_mem_cylinder _ _ _) },
  -- consider the set of pairs of cylinders of some length whose images are not Borel-separated
  let A := {p : ℕ × (ℕ → ℕ) × (ℕ → ℕ) //
              ¬(measurably_separable (f '' (cylinder p.2.1 p.1)) (g '' (cylinder p.2.2 p.1)))},
  -- for each such pair, one can find longer cylinders whose images are not Borel-separated either
  have : ∀ (p : A), ∃ (q : A), q.1.1 = p.1.1 + 1 ∧ q.1.2.1 ∈ cylinder p.1.2.1 p.1.1
    ∧ q.1.2.2 ∈ cylinder p.1.2.2 p.1.1,
  { rintros ⟨⟨n, x, y⟩, hp⟩,
    rcases I n x y hp with ⟨x', y', hx', hy', h'⟩,
    exact ⟨⟨⟨n+1, x', y'⟩, h'⟩, rfl, hx', hy'⟩ },
  choose F hFn hFx hFy using this,
  let p0 : A := ⟨⟨0, λ n, 0, λ n, 0⟩, by simp [hfg]⟩,
  -- construct inductively decreasing sequences of cylinders whose images are not separated
  let p : ℕ → A := λ n, F^[n] p0,
  have prec : ∀ n, p (n+1) = F (p n) := λ n, by simp only [p, iterate_succ'],
  -- check that at the `n`-th step we deal with cylinders of length `n`
  have pn_fst : ∀ n, (p n).1.1 = n,
  { assume n,
    induction n with n IH,
    { refl },
    { simp only [prec, hFn, IH] } },
  -- check that the cylinders we construct are indeed decreasing, by checking that the coordinates
  -- are stationary.
  have Ix : ∀ m n, m + 1 ≤ n → (p n).1.2.1 m = (p (m+1)).1.2.1 m,
  { assume m,
    apply nat.le_induction,
    { refl },
    assume n hmn IH,
    have I : (F (p n)).val.snd.fst m = (p n).val.snd.fst m,
    { apply hFx (p n) m,
      rw pn_fst,
      exact hmn },
    rw [prec, I, IH] },
  have Iy : ∀ m n, m + 1 ≤ n → (p n).1.2.2 m = (p (m+1)).1.2.2 m,
  { assume m,
    apply nat.le_induction,
    { refl },
    assume n hmn IH,
    have I : (F (p n)).val.snd.snd m = (p n).val.snd.snd m,
    { apply hFy (p n) m,
      rw pn_fst,
      exact hmn },
    rw [prec, I, IH] },
  -- denote by `x` and `y` the limit points of these two sequences of cylinders.
  set x : ℕ → ℕ := λ n, (p (n+1)).1.2.1 n with hx,
  set y : ℕ → ℕ := λ n, (p (n+1)).1.2.2 n with hy,
  -- by design, the cylinders around these points have images which are not Borel-separable.
  have M : ∀ n, ¬(measurably_separable (f '' (cylinder x n)) (g '' (cylinder y n))),
  { assume n,
    convert (p n).2 using 3,
    { rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff],
      assume i hi,
      rw hx,
      exact (Ix i n hi).symm },
    { rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff],
      assume i hi,
      rw hy,
      exact (Iy i n hi).symm } },
  -- consider two open sets separating `f x` and `g y`.
  obtain ⟨u, v, u_open, v_open, xu, yv, huv⟩ :
    ∃ u v : set α, is_open u ∧ is_open v ∧ f x ∈ u ∧ g y ∈ v ∧ disjoint u v,
  { apply t2_separation,
    exact disjoint_iff_forall_ne.1 h _ (mem_range_self _) _ (mem_range_self _) },
  letI : metric_space (ℕ → ℕ) := metric_space_nat_nat,
  obtain ⟨εx, εxpos, hεx⟩ : ∃ (εx : ℝ) (H : εx > 0), metric.ball x εx ⊆ f ⁻¹' u,
  { apply metric.mem_nhds_iff.1,
    exact hf.continuous_at.preimage_mem_nhds (u_open.mem_nhds xu) },
  obtain ⟨εy, εypos, hεy⟩ : ∃ (εy : ℝ) (H : εy > 0), metric.ball y εy ⊆ g ⁻¹' v,
  { apply metric.mem_nhds_iff.1,
    exact hg.continuous_at.preimage_mem_nhds (v_open.mem_nhds yv) },
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), (1/2 : ℝ)^n < min εx εy :=
    exists_pow_lt_of_lt_one (lt_min εxpos εypos) (by norm_num),
  -- for large enough `n`, these open sets separate the images of long cylinders around `x` and `y`
  have B : measurably_separable (f '' (cylinder x n)) (g '' (cylinder y n)),
  { refine ⟨u, _, _, u_open.measurable_set⟩,
    { rw image_subset_iff,
      apply subset.trans _ hεx,
      assume z hz,
      rw mem_cylinder_iff_dist_le at hz,
      exact hz.trans_lt (hn.trans_le (min_le_left _ _)) },
    { refine disjoint.mono_left _ huv.symm,
      change g '' cylinder y n ⊆ v,
      rw image_subset_iff,
      apply subset.trans _ hεy,
      assume z hz,
      rw mem_cylinder_iff_dist_le at hz,
      exact hz.trans_lt (hn.trans_le (min_le_right _ _)) } },
  -- this is a contradiction.
  exact M n B
end

/-- The Lusin separation theorem: if two analytic sets are disjoint, then they are contained in
disjoint Borel sets. -/
theorem analytic_set.measurably_separable [t2_space α] [measurable_space α] [borel_space α]
  {s t : set α} (hs : analytic_set s) (ht : analytic_set t) (h : disjoint s t) :
  measurably_separable s t :=
begin
  rw analytic_set at hs ht,
  rcases hs with rfl|⟨f, f_cont, rfl⟩,
  { refine ⟨∅, subset.refl _, by simp, measurable_set.empty⟩ },
  rcases ht with rfl|⟨g, g_cont, rfl⟩,
  { exact ⟨univ, subset_univ _, by simp, measurable_set.univ⟩ },
  exact measurably_separable_range_of_disjoint f_cont g_cont h,
end

/-! ### Injective images of Borel sets -/

variables {γ : Type*} [tγ : topological_space γ] [polish_space γ]
include tγ

/-- The Lusin-Souslin theorem: the range of a continuous injective function defined on a Polish
space is Borel-measurable. -/
theorem measurable_set_range_of_continuous_injective {β : Type*}
  [topological_space β] [t2_space β] [measurable_space β] [borel_space β]
  {f : γ → β} (f_cont : continuous f) (f_inj : injective f) :
  measurable_set (range f) :=
begin
  /- We follow [Fremlin, *Measure Theory* (volume 4, 423I)][fremlin_vol4].
  Let `b = {s i}` be a countable basis for `α`. When `s i` and `s j` are disjoint, their images are
  disjoint analytic sets, hence by the separation theorem one can find a Borel-measurable set
  `q i j` separating them.
  Let `E i = closure (f '' s i) ∩ ⋂ j, q i j \ q j i`. It contains `f '' (s i)` and it is
  measurable. Let `F n = ⋃ E i`, where the union is taken over those `i` for which `diam (s i)`
  is bounded by some number `u n` tending to `0` with `n`.
  We claim that `range f = ⋂ F n`, from which the measurability is obvious. The inclusion `⊆` is
  straightforward. To show `⊇`, consider a point `x` in the intersection. For each `n`, it belongs
  to some `E i` with `diam (s i) ≤ u n`. Pick a point `y i ∈ s i`. We claim that for such `i`
  and `j`, the intersection `s i ∩ s j` is nonempty: if it were empty, then thanks to the
  separating set `q i j` in the definition of `E i` one could not have `x ∈ E i ∩ E j`.
  Since these two sets have small diameter, it follows that `y i` and `y j` are close.
  Thus, `y` is a Cauchy sequence, converging to a limit `z`. We claim that `f z = x`, completing
  the proof.
  Otherwise, one could find open sets `v` and `w` separating `f z` from `x`. Then, for large `n`,
  the image `f '' (s i)` would be included in `v` by continuity of `f`, so its closure would be
  contained in the closure of `v`, and therefore it would be disjoint from `w`. This is a
  contradiction since `x` belongs both to this closure and to `w`. -/
  letI := upgrade_polish_space γ,
  obtain ⟨b, b_count, b_nonempty, hb⟩ :
    ∃ b : set (set γ), b.countable ∧ ∅ ∉ b ∧ is_topological_basis b := exists_countable_basis γ,
  haveI : encodable b := b_count.to_encodable,
  let A := {p : b × b // disjoint (p.1 : set γ) p.2},
  -- for each pair of disjoint sets in the topological basis `b`, consider Borel sets separating
  -- their images, by injectivity of `f` and the Lusin separation theorem.
  have : ∀ (p : A), ∃ (q : set β), f '' (p.1.1 : set γ) ⊆ q ∧ disjoint (f '' (p.1.2 : set γ)) q
    ∧ measurable_set q,
  { assume p,
    apply analytic_set.measurably_separable ((hb.is_open p.1.1.2).analytic_set_image f_cont)
      ((hb.is_open p.1.2.2).analytic_set_image f_cont),
    exact disjoint.image p.2 (f_inj.inj_on univ) (subset_univ _) (subset_univ _) },
  choose q hq1 hq2 q_meas using this,
  -- define sets `E i` and `F n` as in the proof sketch above
  let E : b → set β := λ s, closure (f '' s) ∩
    (⋂ (t : b) (ht : disjoint s.1 t.1), q ⟨(s, t), ht⟩ \ q ⟨(t, s), ht.symm⟩),
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
    ∃ (u : ℕ → ℝ), strict_anti u ∧ (∀ (n : ℕ), 0 < u n) ∧ tendsto u at_top (𝓝 0) :=
      exists_seq_strict_anti_tendsto (0 : ℝ),
  let F : ℕ → set β := λ n, ⋃ (s : b) (hs : bounded s.1 ∧ diam s.1 ≤ u n), E s,
  -- it is enough to show that `range f = ⋂ F n`, as the latter set is obviously measurable.
  suffices : range f = ⋂ n, F n,
  { have E_meas : ∀ (s : b), measurable_set (E s),
    { assume b,
      refine is_closed_closure.measurable_set.inter _,
      refine measurable_set.Inter (λ s, _),
      exact measurable_set.Inter (λ hs, (q_meas _).diff (q_meas _)) },
    have F_meas : ∀ n, measurable_set (F n),
    { assume n,
      refine measurable_set.Union (λ s, _),
      exact measurable_set.Union (λ hs, E_meas _) },
    rw this,
    exact measurable_set.Inter (λ n, F_meas n) },
  -- we check both inclusions.
  apply subset.antisymm,
  -- we start with the easy inclusion `range f ⊆ ⋂ F n`. One just needs to unfold the definitions.
  { rintros x ⟨y, rfl⟩,
    apply mem_Inter.2 (λ n, _),
    obtain ⟨s, sb, ys, hs⟩ : ∃ (s : set γ) (H : s ∈ b), y ∈ s ∧ s ⊆ ball y (u n / 2),
    { apply hb.mem_nhds_iff.1,
      exact ball_mem_nhds _ (half_pos (u_pos n)) },
    have diam_s : diam s ≤ u n,
    { apply (diam_mono hs bounded_ball).trans,
      convert diam_ball (half_pos (u_pos n)).le,
      ring },
    refine mem_Union.2 ⟨⟨s, sb⟩, _⟩,
    refine mem_Union.2 ⟨⟨metric.bounded.mono hs bounded_ball, diam_s⟩, _⟩,
    apply mem_inter (subset_closure (mem_image_of_mem _ ys)),
    refine mem_Inter.2 (λ t, mem_Inter.2 (λ ht, ⟨_, _⟩)),
    { apply hq1,
      exact mem_image_of_mem _ ys },
    { apply disjoint_left.1 (hq2 ⟨(t, ⟨s, sb⟩), ht.symm⟩),
      exact mem_image_of_mem _ ys } },
  -- Now, let us prove the harder inclusion `⋂ F n ⊆ range f`.
  { assume x hx,
    -- pick for each `n` a good set `s n` of small diameter for which `x ∈ E (s n)`.
    have C1 : ∀ n, ∃ (s : b) (hs : bounded s.1 ∧ diam s.1 ≤ u n), x ∈ E s :=
      λ n, by simpa only [mem_Union] using mem_Inter.1 hx n,
    choose s hs hxs using C1,
    have C2 : ∀ n, (s n).1.nonempty,
    { assume n,
      rw nonempty_iff_ne_empty,
      assume hn,
      have := (s n).2,
      rw hn at this,
      exact b_nonempty this },
    -- choose a point `y n ∈ s n`.
    choose y hy using C2,
    have I : ∀ m n, ((s m).1 ∩ (s n).1).nonempty,
    { assume m n,
      rw ← not_disjoint_iff_nonempty_inter,
      by_contra' h,
      have A : x ∈ q ⟨(s m, s n), h⟩ \ q ⟨(s n, s m), h.symm⟩,
      { have := mem_Inter.1 (hxs m).2 (s n), exact (mem_Inter.1 this h : _) },
      have B : x ∈ q ⟨(s n, s m), h.symm⟩ \ q ⟨(s m, s n), h⟩,
      { have := mem_Inter.1 (hxs n).2 (s m), exact (mem_Inter.1 this h.symm : _) },
      exact A.2 B.1 },
    -- the points `y n` are nearby, and therefore they form a Cauchy sequence.
    have cauchy_y : cauchy_seq y,
    { have : tendsto (λ n, 2 * u n) at_top (𝓝 0), by simpa only [mul_zero] using u_lim.const_mul 2,
      apply cauchy_seq_of_le_tendsto_0' (λ n, 2 * u n) (λ m n hmn, _) this,
      rcases I m n with ⟨z, zsm, zsn⟩,
      calc dist (y m) (y n) ≤ dist (y m) z + dist z (y n) : dist_triangle _ _ _
      ... ≤ u m + u n :
        add_le_add ((dist_le_diam_of_mem (hs m).1 (hy m) zsm).trans (hs m).2)
                   ((dist_le_diam_of_mem (hs n).1 zsn (hy n)).trans (hs n).2)
      ... ≤ 2 * u m : by linarith [u_anti.antitone hmn] },
    haveI : nonempty γ := ⟨y 0⟩,
    -- let `z` be its limit.
    let z := lim at_top y,
    have y_lim : tendsto y at_top (𝓝 z) := cauchy_y.tendsto_lim,
    suffices : f z = x, by { rw ← this, exact mem_range_self _ },
    -- assume for a contradiction that `f z ≠ x`.
    by_contra' hne,
    -- introduce disjoint open sets `v` and `w` separating `f z` from `x`.
    obtain ⟨v, w, v_open, w_open, fzv, xw, hvw⟩ := t2_separation hne,
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ > (0 : ℝ), ball z δ ⊆ f ⁻¹' v,
    { apply metric.mem_nhds_iff.1,
      exact f_cont.continuous_at.preimage_mem_nhds (v_open.mem_nhds fzv) },
    obtain ⟨n, hn⟩ : ∃ n, u n + dist (y n) z < δ,
    { have : tendsto (λ n, u n + dist (y n) z) at_top (𝓝 0),
        by simpa only [add_zero] using u_lim.add (tendsto_iff_dist_tendsto_zero.1 y_lim),
      exact ((tendsto_order.1 this).2 _ δpos).exists },
    -- for large enough `n`, the image of `s n` is contained in `v`, by continuity of `f`.
    have fsnv : f '' (s n) ⊆ v,
    { rw image_subset_iff,
      apply subset.trans _ hδ,
      assume a ha,
      calc dist a z ≤ dist a (y n) + dist (y n) z : dist_triangle _ _ _
      ... ≤ u n + dist (y n) z :
        add_le_add_right ((dist_le_diam_of_mem (hs n).1 ha (hy n)).trans (hs n).2) _
      ... < δ : hn },
    -- as `x` belongs to the closure of `f '' (s n)`, it belongs to the closure of `v`.
    have : x ∈ closure v := closure_mono fsnv (hxs n).1,
    -- this is a contradiction, as `x` is supposed to belong to `w`, which is disjoint from
    -- the closure of `v`.
    exact disjoint_left.1 (hvw.closure_left w_open) this xw }
end

theorem _root_.is_closed.measurable_set_image_of_continuous_on_inj_on
  {β : Type*} [topological_space β] [t2_space β] [measurable_space β] [borel_space β]
  {s : set γ} (hs : is_closed s) {f : γ → β} (f_cont : continuous_on f s) (f_inj : inj_on f s) :
  measurable_set (f '' s) :=
begin
  rw image_eq_range,
  haveI : polish_space s := is_closed.polish_space hs,
  apply measurable_set_range_of_continuous_injective,
  { rwa continuous_on_iff_continuous_restrict at f_cont },
  { rwa inj_on_iff_injective at f_inj }
end


variables [measurable_space γ] [hγb : borel_space γ]
{β : Type*} [tβ : topological_space β] [t2_space β] [measurable_space β] [borel_space β]
{s : set γ} {f : γ → β}
include tβ hγb

/-- The Lusin-Souslin theorem: if `s` is Borel-measurable in a Polish space, then its image under
a continuous injective map is also Borel-measurable. -/
theorem _root_.measurable_set.image_of_continuous_on_inj_on
  (hs : measurable_set s) (f_cont : continuous_on f s) (f_inj : inj_on f s) :
  measurable_set (f '' s) :=
begin
  obtain ⟨t', t't, t'_polish, s_closed, s_open⟩ :
    ∃ (t' : topological_space γ), t' ≤ tγ ∧ @polish_space γ t' ∧ is_closed[t'] s ∧
      is_open[t'] s := hs.is_clopenable,
  exact @is_closed.measurable_set_image_of_continuous_on_inj_on γ t' t'_polish β _ _ _ _ s
    s_closed f (f_cont.mono_dom t't) f_inj,
end

/-- The Lusin-Souslin theorem: if `s` is Borel-measurable in a Polish space, then its image under
a measurable injective map taking values in a second-countable topological space
is also Borel-measurable. -/
theorem _root_.measurable_set.image_of_measurable_inj_on [second_countable_topology β]
  (hs : measurable_set s) (f_meas : measurable f) (f_inj : inj_on f s) :
  measurable_set (f '' s) :=
begin
  -- for a finer Polish topology, `f` is continuous. Therefore, one may apply the corresponding
  -- result for continuous maps.
  obtain ⟨t', t't, f_cont, t'_polish⟩ :
    ∃ (t' : topological_space γ), t' ≤ tγ ∧ @continuous γ β t' tβ f ∧ @polish_space γ t' :=
      f_meas.exists_continuous,
  have M : measurable_set[@borel γ t'] s :=
    @continuous.measurable γ γ t' (@borel γ t')
      (@borel_space.opens_measurable γ t' (@borel γ t') (by { constructor, refl }))
      tγ _ _ _ (continuous_id_of_le t't) s hs,
  exact @measurable_set.image_of_continuous_on_inj_on γ t' t'_polish
    (@borel γ t') (by { constructor, refl }) β _ _ _ _ s f M
    (@continuous.continuous_on γ β t' tβ f s f_cont) f_inj,
end

/-- An injective continuous function on a Polish space is a measurable embedding. -/
theorem _root_.continuous.measurable_embedding (f_cont : continuous f) (f_inj : injective f) :
  measurable_embedding f :=
{ injective := f_inj,
  measurable := f_cont.measurable,
  measurable_set_image' := λ u hu,
    hu.image_of_continuous_on_inj_on f_cont.continuous_on (f_inj.inj_on _) }

/-- If `s` is Borel-measurable in a Polish space and `f` is continuous injective on `s`, then
the restriction of `f` to `s` is a measurable embedding. -/
theorem _root_.continuous_on.measurable_embedding (hs : measurable_set s)
  (f_cont : continuous_on f s) (f_inj : inj_on f s) :
  measurable_embedding (s.restrict f) :=
{ injective := inj_on_iff_injective.1 f_inj,
  measurable := (continuous_on_iff_continuous_restrict.1 f_cont).measurable,
  measurable_set_image' :=
  begin
    assume u hu,
    have A : measurable_set ((coe : s → γ) '' u) :=
      (measurable_embedding.subtype_coe hs).measurable_set_image.2 hu,
    have B : measurable_set (f '' ((coe : s → γ) '' u)) :=
      A.image_of_continuous_on_inj_on (f_cont.mono (subtype.coe_image_subset s u))
        (f_inj.mono ((subtype.coe_image_subset s u))),
    rwa ← image_comp at B,
  end }

/-- An injective measurable function from a Polish space to a second-countable topological space
is a measurable embedding. -/
theorem _root_.measurable.measurable_embedding [second_countable_topology β]
  (f_meas : measurable f) (f_inj : injective f) :
  measurable_embedding f :=
{ injective := f_inj,
  measurable := f_meas,
  measurable_set_image' := λ u hu, hu.image_of_measurable_inj_on f_meas (f_inj.inj_on _) }

omit tβ

/-- In a Polish space, a set is clopenable if and only if it is Borel-measurable. -/
lemma is_clopenable_iff_measurable_set :
  is_clopenable s ↔ measurable_set s :=
begin
  -- we already know that a measurable set is clopenable. Conversely, assume that `s` is clopenable.
  refine ⟨λ hs, _, λ hs, hs.is_clopenable⟩,
  -- consider a finer topology `t'` in which `s` is open and closed.
  obtain ⟨t', t't, t'_polish, s_closed, s_open⟩ :
    ∃ (t' : topological_space γ), t' ≤ tγ ∧ @polish_space γ t' ∧ is_closed[t'] s ∧
      is_open[t'] s := hs,
  -- the identity is continuous from `t'` to `tγ`.
  have C : @continuous γ γ t' tγ id := continuous_id_of_le t't,
  -- therefore, it is also a measurable embedding, by the Lusin-Souslin theorem
  have E := @continuous.measurable_embedding γ t' t'_polish (@borel γ t') (by { constructor, refl })
    γ tγ (polish_space.t2_space γ) _ _ id C injective_id,
  -- the set `s` is measurable for `t'` as it is closed.
  have M : @measurable_set γ (@borel γ t') s :=
    @is_closed.measurable_set γ s t' (@borel γ t')
      (@borel_space.opens_measurable γ t' (@borel γ t') (by { constructor, refl })) s_closed,
  -- therefore, its image under the measurable embedding `id` is also measurable for `tγ`.
  convert E.measurable_set_image.2 M,
  simp only [id.def, image_id'],
end

omit hγb

/-- The set of points for which a measurable sequence of functions converges is measurable. -/
@[measurability] lemma measurable_set_exists_tendsto
  [hγ : opens_measurable_space γ] [countable ι] {l : filter ι}
  [l.is_countably_generated] {f : ι → β → γ} (hf : ∀ i, measurable (f i)) :
  measurable_set {x | ∃ c, tendsto (λ n, f n x) l (𝓝 c)} :=
begin
  by_cases hl : l.ne_bot,
  swap, { rw not_ne_bot at hl, simp [hl] },
  letI := upgrade_polish_space γ,
  rcases l.exists_antitone_basis with ⟨u, hu⟩,
  simp_rw ← cauchy_map_iff_exists_tendsto,
  change measurable_set {x | _ ∧ _},
  have : ∀ x, ((map (λ i, f i x) l) ×ᶠ (map (λ i, f i x) l)).has_antitone_basis
    (λ n, ((λ i, f i x) '' u n) ×ˢ ((λ i, f i x) '' u n)) := λ x, hu.map.prod hu.map,
  simp_rw [and_iff_right (hl.map _), filter.has_basis.le_basis_iff (this _).to_has_basis
    metric.uniformity_basis_dist_inv_nat_succ, set.set_of_forall],
  refine measurable_set.bInter set.countable_univ (λ K _, _),
  simp_rw set.set_of_exists,
  refine measurable_set.bUnion set.countable_univ (λ N hN, _),
  simp_rw [prod_image_image_eq, image_subset_iff, prod_subset_iff, set.set_of_forall],
  exact measurable_set.bInter (to_countable (u N)) (λ i _,
    measurable_set.bInter (to_countable (u N)) (λ j _,
    measurable_set_lt (measurable.dist (hf i) (hf j)) measurable_const)),
end

end measure_theory
