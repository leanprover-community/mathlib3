/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

Type of bounded continuous functions taking values in a metric space, with
the uniform distance.
-/

import analysis.normed_space data.real.cau_seq_filter tactic.tidy

noncomputable theory
local attribute [instance] classical.decidable_inhabited classical.prop_decidable

open set lattice filter

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/--A locally uniform limit of continuous functions is continuous-/
lemma continuous_of_locally_uniform_limit_of_continuous [topological_space α] [metric_space β]
  {F : ℕ → α → β} {f : α → β}
  (L : ∀x:α, ∃s ∈ (nhds x).sets, ∀ε>(0:ℝ), ∃N, ∀y∈s, dist (F N y) (f y) ≤ ε)
  (C : ∀(n : ℕ), continuous (F n)) :
  continuous f :=
begin
  rw continuous_topo_metric,
  intros x ε εpos,
  have ε4pos : ε / 4 > 0 := by linarith,
  rcases L x with ⟨r, r_set, hr⟩,
  rcases hr (ε/4) ε4pos with ⟨N, hN⟩,
  rcases continuous_topo_metric.1 (C N) x (ε/4) ε4pos with ⟨s, ⟨s_set, hs⟩⟩,
  existsi r ∩ s,
  existsi (nhds x).inter_sets r_set s_set,
  intros y yrs,
  calc dist (f y) (f x) ≤ dist (f y) (F N y) + dist (F N y) (F N x) + dist (F N x) (f x) : dist_triangle4 _ _ _ _
      ... ≤ (ε/4) + (ε/4) + (ε/4) :
      begin
        apply_rules [add_le_add, le_of_lt (hs y yrs.2), hN x (mem_of_nhds r_set)],
        rw dist_comm,
        apply hN _ yrs.1,
      end
      ... < ε : by linarith
end

/--A uniform limit of continuous functions is continuous-/
lemma continuous_of_uniform_limit_of_continuous [topological_space α] {β : Type v} [metric_space β]
  {F : ℕ → α → β} {f : α → β}
  (L : ∀ε>(0:ℝ), ∃N, ∀y, dist (F N y) (f y) ≤ ε)
  (C : ∀(n : ℕ), continuous (F n)) :
  continuous f :=
begin
  apply @continuous_of_locally_uniform_limit_of_continuous _ _ _ _ F f _ C,
  exact λx, ⟨univ, by simpa [filter.univ_mem_sets] using L⟩
end

/--A Lipschitz function is continuous-/
lemma continuous_of_lipschitz [metric_space α] [metric_space β] {C : ℝ}
  {f : α → β} (H : ∀x y, dist (f x) (f y) ≤ C * dist x y) : continuous f :=
begin
  rw continuous_of_metric,
  intros x ε εpos,
  have : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1),
  existsi (ε/max C 1),
  simp only [exists_prop],
  split,
  { apply div_pos εpos ‹0 < max C 1› },
  { intros y hy, calc
      dist (f y) (f x) ≤ C * dist y x : H y x
      ... ≤ max C 1 * dist y x : mul_le_mul_of_nonneg_right (le_max_left C 1) (dist_nonneg)
      ... < max C 1 * (ε/max C 1) : mul_lt_mul_of_pos_left hy ‹0 < max C 1›
      ... = ε : mul_div_cancel' _ (ne_of_gt ‹0 < max C 1›) }
end

/--The type of bounded continuous functions from a topological space to a metric space-/
def bounded_continuous_function (α : Type u) (β : Type v) [topological_space α] [metric_space β] : Type (max u v) :=
  {f : α → β // continuous f ∧ ∃C, ∀x y:α, dist (f x) (f y) ≤ C}

namespace bounded_continuous_function

section
variables [topological_space α] [metric_space β] [metric_space γ]
variables {f g : bounded_continuous_function α β} {x : α} {C : ℝ}

instance : has_coe_to_fun (bounded_continuous_function α β) :=  ⟨_, subtype.val⟩

lemma bounded_range : bounded (range f) :=
bounded_range_iff.2 (f.property.2)

/--If a function is continuous on a compact space, it is automatically bounded,
and therefore gives rise to an element of the type of bounded continuous functions-/
def mk_of_compact [compact_space α] (f : α → β) (hf : continuous f) : bounded_continuous_function α β :=
⟨f, ⟨hf, by apply bounded_range_iff.1; rw ← image_univ; apply bounded_of_compact (compact_image compact_univ hf)⟩⟩

/--If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions-/
def mk_of_discrete [discrete_topology α] (f : α → β) (hf : ∃C, ∀x y, dist (f x) (f y) ≤ C) :
  bounded_continuous_function α β :=
⟨f, ⟨continuous_of_discrete_topology, hf⟩⟩

/--The uniform distance between two bounded continuous functions-/
instance : has_dist (bounded_continuous_function α β) :=
⟨λf g, Inf {C | C ≥ 0 ∧ ∀ x : α, dist (f x) (g x) ≤ C}⟩

lemma dist_eq : dist f g = Inf {C | C ≥ 0 ∧ ∀ x : α, dist (f x) (g x) ≤ C} := rfl

@[extensionality] lemma ext (H : ∀x, f x = g x) : f = g :=
by apply subtype.eq; apply funext; assumption

/--On an empty space, bounded continuous functions are at distance 0-/
lemma dist_zero_of_empty (e : (univ : set α) = ∅) : dist f g = 0 :=
have A : {C | C ≥ 0 ∧ ∀ x : α, dist (f x) (g x) ≤ C} = {C | C ≥ 0} :=
begin
  apply eq_of_subset_of_subset,
  { exact λC h, h.1 },
  { exact λC h, ⟨h, λx, by simpa [e] using ne_empty_of_mem (mem_univ x)⟩}
end,
by rw [dist_eq, A]; simp

/--The pointwise distance is controlled by the distance between functions, by definition-/
lemma dist_coe_le_dist : dist (f x) (g x) ≤ dist f g :=
have A : ∃C, C ≥ 0 ∧ ∀ y : α, dist (f y) (g y) ≤ C :=
begin
  rcases f.2 with ⟨_, Cf, hCf⟩, /- hCf : ∀ (x y : α), dist (f.val x) (f.val y) ≤ Cf -/
  rcases g.2 with ⟨_, Cg, hCg⟩, /- hCg : ∀ (x y : α), dist (g.val x) (g.val y) ≤ Cg -/
  let C := max 0 (Cf + dist (f x) (g x) + Cg),
  have : ∀ y, dist (f y) (g y) ≤ C := assume y, calc
    dist (f y) (g y) ≤ dist (f y) (f x) + dist (f x) (g x) + dist (g x) (g y) : dist_triangle4 _ _ _ _
                 ... ≤ Cf + dist (f x) (g x) + Cg : add_le_add (add_le_add_right (hCf _ _) _) (hCg _ _)
                 ... ≤ C : le_max_right _ _,
  exact ⟨C, ⟨le_max_left _ _, this⟩⟩
end,
le_cInf (ne_empty_iff_exists_mem.2 A) $ λb hb, hb.2 x

/--The distance between two functions is controlled by the supremum of the pointwise distances-/
lemma dist_le_of_forall_dist_le (H : ∀x:α, dist (f x) (g x) ≤ C) (Cnonneg : C ≥ (0 : ℝ)) :
  dist f g ≤ C :=
begin
  have a : bdd_below {C | C ≥ 0 ∧ ∀x, dist (f x) (g x) ≤ C} :=
    ⟨0, begin intros y hy, simp at hy, exact hy.1 end⟩,
  have b : C ∈ {C | C ≥ 0 ∧ ∀x, dist (f x) (g x) ≤ C} :=
    by simp; exact ⟨Cnonneg, H⟩,
  show dist f g ≤ C, from cInf_le a b
end

/-This lemma will be needed in the proof of the metric space instance, but it will become
useless afterwards as it will be superceded by the general result that the distance is nonnegative
is metric spaces.-/
private lemma dist_nonneg' : 0 ≤ dist f g :=
have A : (univ : set α) = ∅ → 0 ≤ dist f g := λh, by simp [dist_zero_of_empty h, le_refl],
have B : (univ : set α) ≠ ∅ → 0 ≤ dist f g :=
begin
  intro H, /- H : univ ≠ ∅ -/
  rcases exists_mem_of_ne_empty H with ⟨x, _⟩, /- x : α -/
  calc 0 ≤ dist (f x) (g x) : dist_nonneg
     ... ≤ dist f g : dist_coe_le_dist
end,
show 0 ≤ dist f g, from classical.by_cases A B

/--The type of bounded continuous functions, with the uniform distance, is a metric space.-/
instance : metric_space (bounded_continuous_function α β) :=
{ dist_self := assume f,
  begin
    have A : (univ : set α) = ∅ → dist f f = 0 := λh, dist_zero_of_empty h,
    have B : (univ : set α) ≠ ∅ → dist f f = 0,
    { intro H, /- H : univ ≠ ∅ -/
      rcases exists_mem_of_ne_empty H with ⟨x, _⟩, /- x : α -/
      have a : dist (f x) (f x) ≤ dist f f := dist_coe_le_dist,
      simp only [dist_self] at a,
      have b : dist f f ≤ 0 := dist_le_of_forall_dist_le (by simp [le_refl]) (le_refl _),
      show dist f f = 0, from le_antisymm b a },
    show dist f f = 0, from classical.by_cases A B
  end,
  eq_of_dist_eq_zero := assume f g hfg, /- hfg : dist f g = 0 -/
  begin
    ext x, /- x : α, goal f x = g x -/
    have a : dist (f x) (g x) ≤ 0 := by rw ← hfg; apply dist_coe_le_dist,
    show f x = g x, by simpa using le_antisymm a dist_nonneg,
  end,
  dist_comm := assume f g, show dist f g = dist g f, by rw [dist_eq, dist_eq]; simp [dist_comm],
  dist_triangle := assume f g h,
  begin
    have a : ∀x, dist (f x) (h x) ≤ dist f g + dist g h := λx,
      calc dist (f x) (h x) ≤ dist (f x) (g x) + dist (g x) (h x) : dist_triangle _ _ _
                        ... ≤ dist f g + dist g h : add_le_add dist_coe_le_dist dist_coe_le_dist,
    have b : 0 + 0 ≤ dist f g + dist g h := add_le_add dist_nonneg' dist_nonneg',
    simp only [add_zero] at b,
    show dist f h ≤ dist f g + dist g h, from dist_le_of_forall_dist_le a b
  end }

/--If the target space is inhabited, so is the space of bounded continuous functions-/
instance [inhabited β] : inhabited (bounded_continuous_function α β) :=
{ default := ⟨λx, default β, ⟨continuous_const, ⟨0, by simp [le_refl]⟩⟩⟩ }

/-- The evaluation map is continuous, as a joint function of `u` and `x`-/
theorem continuous_eval : continuous (λ(p : (bounded_continuous_function α β) × α), p.1 p.2) :=
begin
  apply continuous_topo_metric.2,
  rintros ⟨f, x⟩ ε εpos, /- f : bounded_continuous_function α β, x : α, ε : ℝ, εpos : ε > 0 -/
  /- use the continuity of `f` to find a neighborhood of `x` where it varies at most by ε/2-/
  rcases (continuous_topo_metric.1 (f.property.1)) x (ε/2) (half_pos εpos) with ⟨nx, nx_nbd, Hnx⟩,
  /- nx : set α, nx_nbd : nx ∈ (nhds x).sets, Hnx : ∀ (b : α), b ∈ nx → dist (f.val b) (f.val x) < ε / 2-/
  have A : ∀g y, dist g f < ε / 2 → y ∈ nx → dist (g y) (f x) < ε := λg y hg hy, calc
    dist (g y) (f x) ≤ dist (g y) (f y) + dist (f y) (f x) : dist_triangle _ _ _
                 ... ≤ dist g f + dist (f y) (f x) : add_le_add_right (dist_coe_le_dist) _
                 ... < ε/2 + ε/2 : add_lt_add hg (Hnx _ hy)
                 ... = ε : add_halves _,
  have B : set.prod (ball f (ε/2)) nx ∈ (nhds (f, x)).sets :=
    prod_mem_nhds_sets (ball_mem_nhds _ (half_pos εpos)) nx_nbd,
  /- The product set `set.prod (ball f (ε/2)) nx` is a set around `(f, x)` where the
  evaluation map varies by at most ε.-/
  existsi set.prod (ball f (ε/2)) nx,
  simp only [and_imp, exists_prop, mem_ball, prod.forall, set.mem_prod],
  dsimp,
  exact ⟨B, A⟩,
end

/-- In particular, when `x` is fixed, `f → f x` is continuous-/
theorem continuous_evalx {x : α} : continuous (λ(f : (bounded_continuous_function α β)), f x) :=
continuous.comp (continuous.prod_mk continuous_id continuous_const) continuous_eval

/--When `f` is fixed, `x → f x` is also continuous, by definition-/
theorem continuous_evalf {f : bounded_continuous_function α β} : continuous (λx, f x) :=
f.property.1

/--Bounded continuous functions taking values in a complete space form a complete space.-/
instance [complete_space β] : complete_space (bounded_continuous_function α β) :=
begin
  refine complete_of_cauchy_seq_tendsto _,
  intros f hf,
  /- f : ℕ → bounded_continuous_function α β, hf : cauchy_seq f.
  We have to show that `f n` converges to a bounded continuous function.
  For this, we prove pointwise convergence to define the limit, then check
  it is a continuous bounded function, and then check the norm convergence. -/
  rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, ⟨b_bound, b_lim⟩⟩,
  have I : ∀ x n m N, N ≤ n → N ≤ m → dist (f n x) (f m x) ≤ b N := λx n m N hn hm,
    calc dist (f n x) (f m x) ≤ dist (f n) (f m) : dist_coe_le_dist
                          ... ≤ b N : b_bound n m N hn hm,
  have A : ∀x, cauchy_seq (λn, f n x) := λx, cauchy_seq_iff_le_tendsto_0.2 ⟨b, ⟨I x, b_lim⟩⟩,
  have B : ∀x, ∃y, tendsto (λn, f n x) at_top (nhds y) := λx, cauchy_seq_tendsto_of_complete (A x),
  choose F hF using B,
  /- F : α → β,  hF : ∀ (x : α), tendsto (λ (n : ℕ), f n x) at_top (nhds (F x))
  `F` is the desired limit function. Check that it is uniformly approximated by `f N`-/
  have b_bound_x : ∀x N, dist (f N x) (F x) ≤ b N,
  { intros x N,
    have a : tendsto (λn, dist (f N x) (f n x)) at_top (nhds (dist (f N x) (F x))) :=
      tendsto_dist tendsto_const_nhds (hF x),
    have b : tendsto (λn, b N) at_top (nhds (b N)) := tendsto_const_nhds,
    apply le_of_tendsto_of_tendsto (by simp) a b _ ,
    simp only [filter.mem_at_top_sets, set.mem_set_of_eq],
    exact ⟨N, λn hn, I x N n N (le_refl N) hn⟩ },
  /- Check that `F` is continuous -/
  have F_cont : continuous F,
  { refine continuous_of_uniform_limit_of_continuous _ (λN, (f N).property.1),
    assume ε εpos,
    rw tendsto_at_top_metric at b_lim,
    rcases b_lim ε εpos with ⟨N, hN⟩,
    exact ⟨N, λy, calc
      dist (f N y) (F y) ≤ b N : b_bound_x y N
      ... ≤ dist (b N) 0 : begin simp, show b N ≤ abs(b N), from le_abs_self _ end
      ... ≤ ε : le_of_lt (hN N (le_refl N))⟩ },
  /- Check that `F` is bounded -/
  have F_bound : ∃C, ∀x y, dist (F x) (F y) ≤ C,
  { rcases (f 0).property.2 with ⟨C, hC⟩,
    existsi b 0 + C + b 0,
    intros x y,
    calc dist (F x) (F y) ≤ dist (F x) (f 0 x) + dist (f 0 x) (f 0 y) + dist (f 0 y) (F y) : dist_triangle4 _ _ _ _
         ... = dist (f 0 x) (F x) + dist (f 0 x) (f 0 y) + dist (f 0 y) (F y) : by simp [dist_comm]
         ... ≤ b 0 + C + b 0 : add_le_add (add_le_add (b_bound_x x 0) (hC x y)) (b_bound_x y 0) },
  /- We can now define the bounded continuous function `flim` associated to `F`-/
  let flim := (⟨F, ⟨F_cont, F_bound⟩⟩ : bounded_continuous_function α β),
  /- Check that `flim` is close to `f N` in distance terms-/
  have : ∀N, dist (f N) flim ≤ b N,
  { intros N,
    apply dist_le_of_forall_dist_le,
    { exact λx, b_bound_x x N },
    { simpa using b_bound N N N (le_refl N) (le_refl N) }},
  /- Deduce that `f N` tends to `flim`-/
  have : tendsto f at_top (nhds flim),
  { apply tendsto_iff_dist_tendsto_zero.2,
    apply squeeze_zero _ ‹∀N, dist (f N) flim ≤ b N› ‹tendsto b at_top (nhds 0)›,
    exact λn, dist_nonneg },
  exact ⟨flim, this⟩
end

/--Composition (in the target) of a bounded continuous function with a Lipschitz map again
gives a bounded continuous function-/
def comp {G : β → γ} (H : ∀x y, dist (G x) (G y) ≤ C * dist x y)
  (f : bounded_continuous_function α β) : bounded_continuous_function α γ :=
⟨λx, G (f x),
begin
  split,
  { apply continuous.comp f.property.1 (continuous_of_lipschitz H) },
  { rcases f.property.2 with ⟨D, hD⟩,
    existsi max C 0 * D,
    intros x y,
    calc dist (G (f x)) (G (f y)) ≤ C * (dist (f x) (f y)) : H _ _
      ... ≤ max C 0 * (dist (f x) (f y)) : mul_le_mul_of_nonneg_right (le_max_left C 0) (dist_nonneg)
      ... ≤ max C 0 * D : mul_le_mul_of_nonneg_left (hD _ _) (le_max_right C 0) }
end⟩

/--The composition operator (in the target) with a Lipschitz map is continuous-/
lemma continuous_comp {G : β → γ} (H : ∀x y, dist (G x) (G y) ≤ C * dist x y) :
  continuous ((comp H) : bounded_continuous_function α β → bounded_continuous_function α γ) :=
have A : ∀f g : bounded_continuous_function α β, dist (comp H f) (comp H g) ≤ max C 0 * dist f g :=
begin
  intros f g,
  apply dist_le_of_forall_dist_le,
  { assume x,
    show dist (G (f x)) (G (g x)) ≤ max C 0 * dist f g, calc
      dist (G (f x)) (G (g x)) ≤ C * dist (f x) (g x) : H _ _
      ... ≤ max C 0 * dist (f x) (g x) : mul_le_mul_of_nonneg_right (le_max_left C 0) (dist_nonneg)
      ... ≤ max C 0 * dist f g : mul_le_mul_of_nonneg_left dist_coe_le_dist (le_max_right C 0) },
  { show max C 0 * dist f g ≥ 0, from mul_nonneg (le_max_right C 0) dist_nonneg }
end,
continuous_of_lipschitz A

/--Restriction (in the target) of a bounded continuous function taking values in a subset-/
def restr (s : set β) (f : bounded_continuous_function α β) (H : ∀x, f x ∈ s) : bounded_continuous_function α s :=
⟨λx, ⟨f x, H x⟩, ⟨continuous_subtype_mk _ f.property.1, by cases f; cases f_property; assumption⟩⟩

end --section

namespace Arzela_Ascoli
section
variables [topological_space α] [compact_space α] [metric_space β]
variables {f g : bounded_continuous_function α β} {x : α} {C : ℝ}

/-Arzela-Ascoli theorem asserts that, on a compact space, a set of functions sharing
a common modulus of continuity and taking values in a compact set forms a compact
subset for the topology of uniform convergence. In this section, we prove this theorem
and several useful variations around it.-/

/--First version, with pointwise equicontinuity and range in a compact space-/
theorem compact_of_closed_of_compact_space_of_equicontinuous [compact_space β]
  (A : set (bounded_continuous_function α β))
  (closed : is_closed A)
  (H : ∀(x:α) (ε > 0), ∃U ∈ (nhds x).sets, ∀ (y z ∈ U) (f : bounded_continuous_function α β),
    f ∈ A → dist (f y) (f z) < ε) :
  compact A :=
begin
  apply compact_of_totally_bounded_is_closed _ closed,
  show totally_bounded A,
  { apply totally_bounded_of_finite_discretization,
    intros ε εpos,
    /-We have to find a finite discretization of `u`, i.e., finite information
    that is sufficient to reconstruct `u` up to ε. This information will be
    provided by the values of `u` on a sufficiently dense set tα,
    slightly translated to fit in a finite (ε/8)-dense set tβ in the image. Such
    sets exist by compactness of the source and range. Then, to check that these
    data determine the function up to ε, one uses the control on the modulus of
    continuity to extend the closeness on tα to closeness everywhere. -/
    have εpos8 : ε/8 > 0 := by linarith,
    have : ∀x:α, ∃U, x ∈ U ∧ is_open U ∧ (∀ (y z ∈ U) (f : bounded_continuous_function α β),
      f ∈ A → dist (f y) (f z) < ε/8),
    { assume x,
      rcases H x _ εpos8 with ⟨U, nhdsU, hU⟩,
      rcases mem_nhds_sets_iff.1 nhdsU with ⟨V, V_sub_U, openV, hV⟩,
      exact ⟨V, hV, openV, λy z hy hz f hf, hU y z (V_sub_U hy) (V_sub_U hz) f hf⟩ },
    choose U hU using this,
    /-For all x, the set hU x is an open set containing x on which the elements of A
    fluctuate by at most ε/8.
    We extract finitely many of these sets that cover the whole space, by compactness-/
    have : ∃tα ⊆ (univ : set α), finite tα ∧ univ ⊆ ⋃x∈tα, U x,
    { refine compact_elim_finite_subcover_image compact_univ _ _,
      show ∀ (x : α), x ∈ univ → is_open (U x), from λx hx, (hU x).2.1,
      show univ ⊆ ⋃ (i : α) (H : i ∈ univ), U i, from λx hx, mem_bUnion (mem_univ _) (hU x).1 },
    rcases this with ⟨tα, _, ⟨finite_tα, htα⟩⟩,
    /- tα : set α, finite_tα : finite tα, htα : univ ⊆ ⋃x ∈ tα, U x-/
    have : ∃tβ ⊆ (univ : set β), (finite tβ ∧ univ ⊆ (⋃y∈tβ, ball y (ε/8))) :=
      finite_cover_balls_of_compact compact_univ εpos8,
    rcases this with ⟨tβ, _, ⟨finite_tβ, htβ⟩⟩,
    /-tβ : set β, finite_tβ : finite tβ, htβ : univ ⊆ ⋃y ∈ tβ, ball y (ε / 2)-/
    have fin_univ : finite (univ : set (tα → tβ)) :=
      finite_fun_of_finite_of_finite finite_tα finite_tβ,
    /- Associate to every point `y` in the space a nearby point `F y` in tβ -/
    have : ∀ y, ∃z∈tβ, dist y z < ε/8 :=
      λy, by simpa using htβ (mem_univ y),
    choose F hF using this,
    simp only [exists_prop] at hF,
    /- F : β → β, hF : ∀ (y : β), F y ∈ tβ ∧ dist y (F y) < ε/8-/

    /-Associate to every function a discrete approximation, mapping each point in `tα`
    to a point in `tβ` close to its true image by the function.-/
    let approx : (bounded_continuous_function α β) → (tα → tβ) := λf a, ⟨F (f a), (hF (f a)).1⟩,
    /-If two functions have the same approximation, then they are within distance ε-/
    have main : ∀f g ∈ A, approx f = approx g → dist f g < ε,
    { assume f g hf hg f_eq_g,
      have : ∀x, dist (f x) (g x) ≤ ε/2 := λx,
      begin
        have : ∃x', x' ∈ tα ∧ x ∈ U x' := mem_bUnion_iff.1 (htα (mem_univ x)),
        rcases this with ⟨x', ⟨x'tα, hx'⟩⟩,
        have F_f_g : F (f x') = F (g x') := calc
          F (f x') = approx f ⟨x', x'tα⟩ : rfl
          ... = approx g ⟨x', x'tα⟩ : by rw [f_eq_g]
          ... = F (g x') : rfl,
        have fxx' : dist (f x) (f x') ≤ ε/8 := le_of_lt ((hU x').2.2 _ _ hx' ((hU x').1) _ hf),
        have gx'x : dist (g x') (g x) ≤ ε/8 := le_of_lt ((hU x').2.2 _ _ ((hU x').1) hx' _ hg),
        have : dist (f x') (g x') ≤ ε/4 := calc
          dist (f x') (g x') ≤ dist (f x') (F (f x')) + dist (g x') (F (f x')) : dist_triangle_right _ _ _
            ... = dist (f x') (F (f x')) + dist (g x') (F (g x')) : by rw [← F_f_g]
            ... ≤ ε/8 + ε/8 : add_le_add (le_of_lt (hF (f x')).2) (le_of_lt (hF (g x')).2)
            ... = ε/4 : by ring,
        calc dist (f x) (g x) ≤ dist (f x) (f x') + dist (f x') (g x') + dist (g x') (g x) : dist_triangle4 _ _ _ _
                ... ≤ ε/8 + ε/4 + ε/8 : add_le_add (add_le_add (fxx') (this)) (gx'x)
                ... = ε/2 : by ring,
      end,
      calc dist f g ≤ ε/2 : dist_le_of_forall_dist_le this (le_of_lt (half_pos εpos))
             ... < ε : half_lt_self εpos },
    /-The discretization constructed above is good enough to conclude-/
    existsi [(tα → tβ), univ, approx],
    simpa [fin_univ] using main }
end

/--Second version, with pointwise equicontinuity and range in a compact subset-/
theorem compact_of_closed_of_compact_range_of_equicontinuous
  (s : set β) (hs : compact s)
  (A : set (bounded_continuous_function α β))
  (closed : is_closed A)
  (in_s : ∀(f : bounded_continuous_function α β) (x : α), f ∈ A → f x ∈ s)
  (H : ∀(x:α) (ε > 0), ∃U ∈ (nhds x).sets, ∀ (y z ∈ U) (f : bounded_continuous_function α β),
    f ∈ A → dist (f y) (f z) < ε) :
  compact A :=
/-This version is deduced from the previous one by restricting to the compact type in the target,
using compactness there and then lifting everything to the original space.-/
begin
  have M : ∀x y : s, dist (x : β) y ≤ 1 * dist x y :=
    begin intros x y, cases y, cases x, dsimp at *, simp at *, refl end,
  let F : bounded_continuous_function α s → bounded_continuous_function α β := comp M,
  let B := F⁻¹' A,
  have : compact B,
  { haveI : compact_space s := ⟨compact_iff_compact_univ.1 hs⟩,
    apply compact_of_closed_of_compact_space_of_equicontinuous,
    show is_closed B, from continuous_iff_is_closed.1 (continuous_comp M) _ closed,
    assume x ε εpos,
    rcases H x ε εpos with ⟨U, U_nhds, hU⟩,
    existsi [U, U_nhds],
    assume y z hy hz f hf,
    calc dist (f y) (f z) = dist (F f y) (F f z) : rfl
                        ... < ε : hU y z hy hz (F f) hf },
  have : A ⊆ F '' B,
  { assume f hf,
    let g := restr s f (λx, in_s f x hf),
    have fg : f = F g := by ext; by refl,
    have : g ∈ B := by simp [B, fg.symm, hf],
    rw fg,
    apply mem_image_of_mem F ‹g ∈ B› },
  apply compact_of_is_closed_subset (compact_image ‹compact B› (continuous_comp M)) closed this
end

/--Third (main) version, with pointwise equicontinuity and range in a compact subset, but
without closedness. The closure is then compact-/
theorem compact_closure_of_equicontinuous_of_compact_range
  (s : set β) (hs : compact s)
  (A : set (bounded_continuous_function α β))
  (in_s : ∀(f : bounded_continuous_function α β) (x : α), f ∈ A → f x ∈ s)
  (H : ∀(x:α) (ε > 0), ∃U ∈ (nhds x).sets, ∀ (y z ∈ U) (f : bounded_continuous_function α β),
    f ∈ A → dist (f y) (f z) < ε) :
  compact (closure A) :=
/-This version is deduced from the previous one by checking that the closure of A, in
addition to being closed, still satisfies the properties of compact range and equicontinuity-/
begin
  apply compact_of_closed_of_compact_range_of_equicontinuous s hs (closure A) (is_closed_closure),
  show ∀ (f : bounded_continuous_function α β) (x : α), f ∈ closure A → f x ∈ s,
  { assume f x hf,
    have : f x ∈ closure s,
    { apply mem_closure_iff'.2,
      assume ε εpos,
      rcases mem_closure_iff'.1 hf ε εpos with ⟨g, gA, dist_fg⟩,
      exact ⟨g x, in_s g x gA, lt_of_le_of_lt dist_coe_le_dist dist_fg⟩ },
    rwa closure_eq_iff_is_closed.2 (closed_of_compact _ hs) at this },
  show ∀ (x:α) (ε > 0), ∃ U ∈ (nhds x).sets,
       ∀ y z ∈ U, ∀ (f : bounded_continuous_function α β), f ∈ closure A → dist (f y) (f z) < ε,
  { assume x ε εpos,
    have ε3pos : ε/3 > 0 := by linarith,
    rcases H x (ε/3) ε3pos with ⟨U, U_set, hU⟩,
    existsi [U, U_set],
    assume y z hy hz f hf,
    rcases mem_closure_iff'.1 hf (ε/3) ε3pos with ⟨g, gA, dist_fg⟩,
    calc dist (f y) (f z) ≤ dist (f y) (g y) + dist (g y) (g z) + dist (g z) (f z) : dist_triangle4 _ _ _ _
        ... ≤ dist f g + dist (g y) (g z) + dist g f :
          add_le_add (add_le_add dist_coe_le_dist (le_refl _)) dist_coe_le_dist
        ... < ε/3 + ε/3 + ε/3 :
          by apply add_lt_add (add_lt_add dist_fg (hU y z hy hz g gA)); rwa dist_comm at dist_fg
        ... = ε : by ring }
end

/-To apply the previous theorems, one needs to check the equicontinuity. An important
instance is when the source space is a metric space, and there is a fixed modulus of continuity
for all the functions in the set A-/

lemma equicontinuous_of_continuity_modulus {α : Type u} [metric_space α]
  (b : ℝ → ℝ) (b_lim : tendsto b (nhds 0) (nhds 0))
  (A : set (bounded_continuous_function α β))
  (H : ∀(x y:α) (f : bounded_continuous_function α β), f ∈ A → dist (f x) (f y) ≤ b (dist x y)) :
  ∀(x:α) (ε > 0), ∃U ∈ (nhds x).sets, ∀ (y z ∈ U) (f : bounded_continuous_function α β),
    f ∈ A → dist (f y) (f z) < ε :=
begin
  assume x ε εpos,
  rw [tendsto_nhds_of_metric] at b_lim,
  rcases b_lim ε εpos with ⟨δ, δpos, hδ⟩,
  existsi [ball x (δ/2), ball_mem_nhds x (half_pos δpos)],
  assume y z hy hz f hf,
  have : dist y z < δ := calc
    dist y z ≤ dist y x + dist z x : dist_triangle_right _ _ _
    ... < δ/2 + δ/2 : add_lt_add hy hz
    ... = δ : add_halves _,
  calc
    dist (f y) (f z) ≤ b (dist y z) : H y z f hf
    ... ≤ abs(b(dist y z)) : le_abs_self _
    ... = dist (b(dist y z)) 0 : by simp [real.dist_eq]
    ... < ε : hδ (by simpa [real.dist_eq] using this),
end

end --section
end Arzela_Ascoli --namespace


section normed_group
/-In this section, if β is a normed group, then we show that the space of bounded
continuous functions from α to β inherits a normed group structure, by using
pointwise operations and checking that they are compatible with the uniform distance.-/

variables [topological_space α] [normed_group β]
variables {f g : bounded_continuous_function α β} {x : α} {C : ℝ}

instance : has_zero (bounded_continuous_function α β) :=
{ zero := ⟨λx, 0, ⟨continuous_const,  ⟨0, by simp [le_refl]⟩⟩⟩ }

@[simp] lemma coe_zero : (0 : bounded_continuous_function α β) x = 0 := rfl

instance : has_norm (bounded_continuous_function α β) :=
{ norm := λu, dist u 0 }

lemma norm_coe_le_norm : norm (f x) ≤ norm f := calc
  norm (f x) = dist (f x) ((0 : bounded_continuous_function α β) x) : by simp [dist_zero_right]
  ... ≤ dist f 0 : dist_coe_le_dist
  ... = norm f : rfl

/--The pointwise sum of two bounded continuous functions is again bounded continuous.-/
instance : has_add (bounded_continuous_function α β) :=
{ add := λf g, ⟨λx, f x + g x, ⟨continuous_add f.property.1 g.property.1,
    ⟨(norm f + norm g) + (norm f + norm g), λx y,
      have A : ∀x, dist (f x + g x) 0 ≤ norm f + norm g := λx, calc
        dist (f x + g x) 0 = norm (f x + g x) : by rw dist_zero_right
        ... ≤ norm (f x) + norm (g x) : norm_triangle _ _
        ... ≤ norm f + norm g : add_le_add norm_coe_le_norm norm_coe_le_norm,
      calc dist (f x + g x) (f y + g y) ≤ dist (f x + g x) 0 + dist (f y + g y) 0 : dist_triangle_right _ _ _
          ... ≤ (norm f + norm g) + (norm f + norm g) : add_le_add (A x) (A y) ⟩⟩⟩ }

/--The pointwise opposite of a bounded continuous function is again bounded continuous.-/
instance : has_neg (bounded_continuous_function α β) :=
{ neg := λf, ⟨λx, -f x, ⟨continuous_neg f.property.1, begin
    have : ∀a b : β, dist (-a) (-b) = dist a b :=
      λa b, by rw [dist_eq_norm, dist_eq_norm, norm_sub_rev]; simp,
    simp only [this],
    exact f.property.2
  end⟩⟩ }

@[simp] lemma coe_add : (f + g) x = f x + g x := rfl
@[simp] lemma coe_neg : (-f) x = - (f x) := rfl
lemma forall_coe_zero_iff_zero : (∀x, f x = 0) ↔ f = 0 :=
⟨by intros Hf; apply ext; simpa, by intros Hf; rw [Hf]; simp⟩

instance : add_comm_group (bounded_continuous_function α β) :=
{ add_assoc    := assume f g h, by ext; simp,
  zero_add     := assume f, by ext; simp,
  add_zero     := assume f, by ext; simp,
  add_left_neg := assume f, by ext; simp,
  add_comm     := assume f g, by ext; simp,
  ..bounded_continuous_function.has_add,
  ..bounded_continuous_function.has_neg,
  ..bounded_continuous_function.has_zero }

@[simp] lemma coe_diff : (f-g) x = f x - g x := rfl

instance : normed_group (bounded_continuous_function α β) :=
{ dist_eq := assume f g,
  begin
    have A : dist f g ≤ norm (f - g),
    { refine dist_le_of_forall_dist_le (λx, _) dist_nonneg,
      calc dist (f x) (g x) = dist ((f - g) x) ((0 : bounded_continuous_function α β) x) : by simp [dist_eq_norm]
           ... ≤ dist (f - g) 0 : dist_coe_le_dist },
    have B : norm (f - g) ≤ dist f g,
    { refine dist_le_of_forall_dist_le (λx, _) dist_nonneg,
      calc dist (f x - g x) 0 = dist (f x) (g x) : by simp [dist_eq_norm]
           ... ≤ dist f g : dist_coe_le_dist },
    exact le_antisymm A B
  end,
  ..bounded_continuous_function.add_comm_group,
  ..bounded_continuous_function.has_norm }

lemma abs_diff_coe_le_dist : norm (f x - g x) ≤ dist f g :=
calc norm (f x - g x) = norm ((f - g) x) : by simp
                  ... ≤ norm (f - g) : norm_coe_le_norm
                  ... = dist f g : (normed_group.dist_eq _ _).symm

lemma coe_le_coe_add_dist {f g : bounded_continuous_function α ℝ} : f x ≤ g x + dist f g :=
begin
  have : f x - g x ≤ abs (f x - g x) := le_abs_self _,
  have : abs (f x - g x) ≤ dist f g :=
    by rw ← real.norm_eq_abs; exact abs_diff_coe_le_dist,
  by linarith
end

/-- Constructing a bounded continuous function from a continuous function taking values in a normed
group, that is pointwise bounded-/
def normed_group.mk (f : α  → β) (C : ℝ) (H : ∀x, norm (f x) ≤ C) (Hf : continuous f) :
  bounded_continuous_function α β :=
⟨λn, f n, ⟨Hf, ⟨C + C, λm n,
  calc dist (f m) (f n) ≤ dist (f m) 0 + dist (f n) 0 : dist_triangle_right _ _ _
       ... = norm (f m) + norm (f n) : by simp
       ... ≤ C + C : add_le_add (H m) (H n) ⟩⟩⟩

/-- Constructing a bounded continuous function from a function on a discrete space taking values
in a normed group, that is pointwise bounded-/
def normed_group.mk_of_discrete [discrete_topology α] (f : α  → β) (C : ℝ) (H : ∀x, norm (f x) ≤ C) :
  bounded_continuous_function α β :=
bounded_continuous_function.normed_group.mk f C H continuous_of_discrete_topology

end normed_group --section
end bounded_continuous_function --namespace