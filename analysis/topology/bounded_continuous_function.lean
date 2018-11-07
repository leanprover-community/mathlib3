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
lemma continuous_of_uniform_limit_of_continuous {α : Type u} [topological_space α] {β : Type v} [metric_space β]
  {F : ℕ → α → β} {f : α → β}
  (L : ∀ε>(0:ℝ), ∃N, ∀y, dist (F N y) (f y) ≤ ε)
  (C : ∀(n : ℕ), continuous (F n)) :
  continuous f :=
begin
  apply @continuous_of_locally_uniform_limit_of_continuous _ _ _ _ F f _ C,
  exact λx, ⟨univ, by simpa [filter.univ_mem_sets] using L⟩
end

/--A Lipschitz function is continuous-/
lemma continuous_of_lipschitz {α : Type u} {β : Type v} [metric_space α] [metric_space β] {C : ℝ}
  {f : α → β} (H : ∀x y, dist (f x) (f y) ≤ C * dist x y) : continuous f :=
begin
  rw continuous_of_metric,
  intros x ε εpos,
  have : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1),
  existsi (ε/max C 1),
  simp,
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
  { exact λC h, ⟨h, begin assume x, simpa using ne_empty_of_mem (mem_univ x) end⟩}
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
lemma dist_nonneg' : 0 ≤ dist f g :=
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
    have B : (univ : set α) ≠ ∅ → dist f f = 0 :=
    begin
      intro H, /- H : univ ≠ ∅ -/
      rcases exists_mem_of_ne_empty H with ⟨x, _⟩, /- x : α -/
      have a : dist (f x) (f x) ≤ dist f f := dist_coe_le_dist,
      simp at a,
      have b : dist f f ≤ 0 := dist_le_of_forall_dist_le (by simp [le_refl]) (le_refl _),
      show dist f f = 0, from le_antisymm b a,
    end,
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
    simp at b,
    show dist f h ≤ dist f g + dist g h, from dist_le_of_forall_dist_le a b
  end }

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
  simp,
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
  have b_bound_x : ∀x N, dist (f N x) (F x) ≤ b N :=
  begin
    intros x N,
    have a : tendsto (λn, dist (f N x) (f n x)) at_top (nhds (dist (f N x) (F x))) :=
      tendsto_dist tendsto_const_nhds (hF x),
    have b : tendsto (λn, b N) at_top (nhds (b N)) := tendsto_const_nhds,
    apply le_of_tendsto (by simp) a b _ ,
    simp,
    exact ⟨N, λn hn, I x N n N (le_refl N) hn⟩,
  end,
  /- Check that `F` is continuous -/
  have F_cont : continuous F :=
  begin
    have : ∀ε>(0:ℝ), ∃N, ∀y, dist (f N y) (F y) ≤ ε :=
    begin
      assume ε εpos,
      rw tendsto_at_top_metric at b_lim,
      rcases b_lim ε εpos with ⟨N, hN⟩,
      exact ⟨N, λy, calc
        dist (f N y) (F y) ≤ b N : b_bound_x y N
        ... ≤ dist (b N) 0 : begin simp, show b N ≤ abs(b N), from le_abs_self _ end
        ... ≤ ε : le_of_lt (hN N (le_refl N))⟩
    end,
    exact continuous_of_uniform_limit_of_continuous this (λN, (f N).property.1)
  end,
  /- Check that `F` is bounded -/
  have F_bound : ∃C, ∀x y, dist (F x) (F y) ≤ C :=
  begin
    rcases (f 0).property.2 with ⟨C, hC⟩,
    existsi b 0 + C + b 0,
    intros x y,
    calc dist (F x) (F y) ≤ dist (F x) (f 0 x) + dist (f 0 x) (f 0 y) + dist (f 0 y) (F y) : dist_triangle4 _ _ _ _
         ... = dist (f 0 x) (F x) + dist (f 0 x) (f 0 y) + dist (f 0 y) (F y) : by simp [dist_comm]
         ... ≤ b 0 + C + b 0 : add_le_add (add_le_add (b_bound_x x 0) (hC x y)) (b_bound_x y 0)
  end,
  /- We can now define the bounded continuous function `flim` associated to `F`-/
  let flim := (⟨F, ⟨F_cont, F_bound⟩⟩ : bounded_continuous_function α β),
  /- Check that `flim` is close to `f N` in distance terms-/
  have : ∀N, dist (f N) flim ≤ b N :=
  begin
    intros N,
    apply dist_le_of_forall_dist_le,
    { exact λx, b_bound_x x N },
    { simpa using b_bound N N N (le_refl N) (le_refl N) }
  end,
  /- Deduce that `f N` tends to `flim`-/
  have : tendsto f at_top (nhds flim) :=
  begin
    apply tendsto_iff_dist_tendsto_zero.2,
    apply squeeze_zero _ ‹∀N, dist (f N) flim ≤ b N› ‹tendsto b at_top (nhds 0)›,
    show ∀ (n : ℕ), 0 ≤ dist (f n) flim, from λn, dist_nonneg,
  end,
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

/--Arzelà–Ascoli theorem, saying that, on a compact space, a set of functions sharing
a common modulus of continuity and taking values in a compact set forms a compact
subset for the topology of uniform convergence. First version where the range is
a compact space-/
theorem compact_of_equicontinuous_of_compact_space {α : Type u} [metric_space α] [compact_space α] [compact_space β]
  {b : ℝ → ℝ} (b_lim : tendsto b (nhds 0) (nhds 0)) :
  compact {f : bounded_continuous_function α β | ∀x y, dist (f x) (f y) ≤ b (dist x y)} :=
begin
  apply compact_of_totally_bounded_is_closed,
  /-We need to show that our set is closed and totally bounded (i.e., covered by finitely many
  balls of radius ε, for any ε>0. Closedness is obvious from the expression of the set.-/
  show is_closed {f : bounded_continuous_function α β | ∀ (x y : α), dist (f x) (f y) ≤ b (dist x y)},
  begin
    have a : is_closed (⋂x y, {f : bounded_continuous_function α β | dist (f x) (f y) ≤ b (dist x y)}) :=
    begin
      apply is_closed_Inter _,
      assume x,
      apply is_closed_Inter _,
      assume y,
      let D := (λf : bounded_continuous_function α β, dist (f x) (f y)),
      have : continuous D := continuous_dist continuous_evalx continuous_evalx,
      have A : {f : bounded_continuous_function α β | dist (f x) (f y) ≤ b (dist x y)}
             = D⁻¹' {r | r ≤ b (dist x y)} := rfl,
      rw A,
      apply continuous_iff_is_closed.1 ‹continuous D› _ _,
      simp [is_closed_le'],
    end,
    have : {f : bounded_continuous_function α β | ∀ (x y : α), dist (f x) (f y) ≤ b (dist x y)}
      = (⋂x y, {f : bounded_continuous_function α β | dist (f x) (f y) ≤ b (dist x y)}) := by ext1; simp,
    rw this,
    exact a
  end,
  /- Let us now show that our set is totally bounded-/
  show totally_bounded {f : bounded_continuous_function α β | ∀x y, dist (f x) (f y) ≤ b (dist x y)},
  begin
    apply totally_bounded_of_finite_discretization,
    intros ε εpos,
    /-We have to find a finite discretization of `u`, i.e., finite information
    that is sufficient to reconstruct `u` up to ε. This information will be
    provided by the values of `u` on a finite δ-dense set tα (where δ is suitably small),
    slightly translated to fit in a finite (ε/8)-dense set tβ in the image. Such
    sets exist by compactness of the source and range. Then, to check that these
    data determine the function up to ε, one uses the control on the modulus of
    continuity to extend the closeness on tα to closeness everywhere. -/
    have εpos8 : ε/8 > 0 := by linarith,
    rw [tendsto_nhds_of_metric] at b_lim,
    rcases b_lim (ε/8) εpos8 with ⟨δ, δpos, hδ⟩,
    have : ∃tα ⊆ (univ : set α), (finite tα ∧ univ ⊆ (⋃x∈tα, ball x δ)) :=
      finite_cover_balls_of_compact compact_univ δpos,
    rcases this with ⟨tα, _, ⟨finite_tα, htα⟩⟩,
    /- tα : set α, finite_tα : finite tα, htα : univ ⊆ ⋃x ∈ tα, ball x δ-/
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
    simp at hF,
    /- F : β → β, hF : ∀ (y : β), F y ∈ tβ ∧ dist y (F y) < ε/8-/

    /-Associate to every function a discrete approximation, mapping each point in `tα`
    to a point in `tβ` close to its true image by the function.-/
    let approx : (bounded_continuous_function α β) → (tα → tβ) := λf a, ⟨F (f a), (hF (f a)).1⟩,
    /-If two functions have the same approximation, then they are within distance ε-/
    have main : ∀f g ∈ {f : bounded_continuous_function α β | ∀ (x y : α), dist (f x) (f y) ≤ b (dist x y)},
      approx f = approx g → dist f g < ε :=
    begin
      assume f g hf hg f_eq_g,
      simp at hf hg,
      have : ∀x, dist (f x) (g x) ≤ ε/2 := λx,
      begin
        have : ∃x' ∈ tα, dist x x' < δ := by simpa using htα (mem_univ x),
        rcases this with ⟨x', ⟨x'tα, hx'⟩⟩,
        have F_f_g : F (f x') = F (g x') := calc
          F (f x') = approx f ⟨x', x'tα⟩ : rfl
          ... = approx g ⟨x', x'tα⟩ : by rw [f_eq_g]
          ... = F (g x') : rfl,
        have bxx' : b (dist x x') ≤ ε/8 := calc
          b (dist x x') ≤ abs(b(dist x x')) : le_abs_self _
            ... = dist (b(dist x x')) 0 : by simp [real.dist_eq]
            ... ≤ ε/8 : le_of_lt (hδ (by simpa [real.dist_eq] using hx')),
        have bx'x : b (dist x' x) ≤ ε/8 := by rwa [dist_comm],
        have : dist (f x') (g x') ≤ ε/4 := calc
          dist (f x') (g x') ≤ dist (f x') (F (f x')) + dist (g x') (F (f x')) : dist_triangle_right _ _ _
            ... = dist (f x') (F (f x')) + dist (g x') (F (g x')) : by rw [← F_f_g]
            ... ≤ ε/8 + ε/8 : add_le_add (le_of_lt (hF (f x')).2) (le_of_lt (hF (g x')).2)
            ... = ε/4 : by ring,
        calc dist (f x) (g x) ≤ dist (f x) (f x') + dist (f x') (g x') + dist (g x') (g x) : dist_triangle4 _ _ _ _
                ... ≤ b(dist x x') + ε/4 + b(dist x' x) : add_le_add (add_le_add (hf x x') (this)) (hg x' x)
                ... ≤ ε/8 + ε/4 + ε/8 : add_le_add (add_le_add bxx' (le_refl _)) bx'x
                ... = ε/2 : by ring,
      end,
      calc dist f g ≤ ε/2 : dist_le_of_forall_dist_le this (le_of_lt (half_pos εpos))
             ... < ε : half_lt_self εpos,
    end,
    /-The discretization constructed above is good enough to conclude-/
    existsi [(tα → tβ), univ, approx],
    simp at main,
    simp [fin_univ],
    exact main,
  end
end

/-Arzelà–Ascoli theorem, saying that, on a compact space, a set of functions sharing
a common modulus of continuity and taking values in a compact set forms a compact
subset for the topology of uniform convergence. Second version where the range is
contained in a given compact set. This version follows from the first one, by reformulating
it from the compact subtype to the compact subset.-/
theorem compact_of_equicontinuous_of_compact_range {α : Type u} [metric_space α] [compact_space α]
  {b : ℝ → ℝ} (b_lim : tendsto b (nhds 0) (nhds 0))
  (s : set β) (hs : compact s):
  compact {f : bounded_continuous_function α β | (∀x y, dist (f x) (f y) ≤ b (dist x y)) ∧ range f ⊆ s} :=
begin
  have H : ∀x y : s, dist (x : β) y ≤ 1 * dist x y :=
    begin intros x y, cases y, cases x, dsimp at *, simp at *, refl end,
  let F : bounded_continuous_function α s → bounded_continuous_function α β := comp H,
  have A : F '' {f : bounded_continuous_function α s | (∀x y, dist (f x) (f y) ≤ b (dist x y))}
    = {f : bounded_continuous_function α β | (∀x y, dist (f x) (f y) ≤ b (dist x y)) ∧ range f ⊆ s} :=
  begin
    have : ∀f x, F f x ∈ s := λf x, subtype.mem _,
    ext f,
    split,
    { simp [range_subset_iff], tidy },
    { simp [range_subset_iff],
      intros hdist hrange,
      existsi (restr s f hrange),
      tidy },
  end,
  rw ← A,
  show compact (F '' {f : bounded_continuous_function α s | (∀x y, dist (f x) (f y) ≤ b (dist x y))}),
  begin
    apply compact_image _ (continuous_comp H),
    haveI : compact_space s := ⟨compact_iff_compact_univ.1 hs⟩,
    exact compact_of_equicontinuous_of_compact_space b_lim
  end
end

end --section

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
{ add := λf g, ⟨λx, f x + g x,
  begin
    split,
    { apply continuous_add f.property.1 g.property.1 },
    { existsi (norm f + norm g) + (norm f + norm g),
      have A : ∀x, dist (f x + g x) 0 ≤ norm f + norm g := λx, calc
        dist (f x + g x) 0 = norm (f x + g x) : by rw dist_zero_right
        ... ≤ norm (f x) + norm (g x) : norm_triangle _ _
        ... ≤ norm f + norm g : add_le_add norm_coe_le_norm norm_coe_le_norm,
      intros x y,
      calc dist (f x + g x) (f y + g y) ≤ dist (f x + g x) 0 + dist (f y + g y) 0 : dist_triangle_right _ _ _
          ... ≤ (norm f + norm g) + (norm f + norm g) : add_le_add (A x) (A y) }
  end⟩ }

/--The pointwise opposite of a bounded continuous function is again bounded continuous.-/
instance : has_neg (bounded_continuous_function α β) :=
{ neg := λf, ⟨λx, -f x,
  begin
    split,
    { apply continuous_neg f.property.1 },
    { have : ∀a b : β, dist (-a) (-b) = dist a b :=
      begin
        intros a b,
        rw [dist_eq_norm, dist_eq_norm, norm_sub_rev],
        simp,
      end,
      simp [this],
      exact f.property.2 }
  end⟩ }

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
    have A : dist f g ≤ norm (f - g) :=
    begin
      apply dist_le_of_forall_dist_le _ dist_nonneg,
      assume x,
      calc dist (f x) (g x) = dist ((f - g) x) ((0 : bounded_continuous_function α β) x) : by simp [dist_eq_norm]
           ... ≤ dist (f - g) 0 : dist_coe_le_dist
    end,
    have B : norm (f - g) ≤ dist f g :=
    begin
      apply dist_le_of_forall_dist_le _ dist_nonneg,
      assume x,
      calc dist (f x - g x) 0 = dist (f x) (g x) : by simp [dist_eq_norm]
           ... ≤ dist f g : dist_coe_le_dist
    end,
    exact le_antisymm A B
  end,
  ..bounded_continuous_function.add_comm_group,
  ..bounded_continuous_function.has_norm
}

end normed_group --section
end bounded_continuous_function --namespace