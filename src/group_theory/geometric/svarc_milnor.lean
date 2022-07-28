
/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Georgi Kocharyan.
-/

-- Source of proof: Geometric group theory: An introduction (Clara Löh)

import .cayley_graph
import .geodesic_space
import .isom_action
import .quasi_iso
import topology.metric_space.isometry
import .marked_group




open classical
open_locale big_operators pointwise

variables {α β : Type*} [inhabited β] [group α] [inhabited α]

-- if x and y in the metric space are close together, the translates of s they are in
-- only differ by an element of the generating set
lemma intS  (c : ℝ) (b : ℝ) (cpos: c > 0) (bnonneg: b ≥ 0)  [quasigeodesic_space β c b cpos bnonneg]
  [isom_action α β] (s : set β) (g : α) (h : α) (x : β) (y : β) (hx: x ∈ g • s)
  (hy : y ∈ h • s) (hd : dist x y ≤ 2*b)
  : ∃ t ∈ (proper_action_set α (set_closed_ball s (2*b))), g*t = h
   :=
begin
use g⁻¹*h,
split,
have hy' : y ∈ set_closed_ball (g • s) (2*b),
  {use x, split, exact hx, rw dist_comm, exact hd,},
rw ← isom_of_set_closed_ball at hy',
have hy'' : y ∈ h • (set_closed_ball s (2*b)),
rcases hy with ⟨ w, ⟨ ws, hw ⟩⟩,
use w,
split,
{ apply self_set_closed_ball, linarith, exact ws },
exact hw, rw proper_action_set, dsimp,
have i1 : g⁻¹ • y ∈ (g⁻¹ * g) • (set_closed_ball s (2 * b)),
  { apply isom_img_mul, exact hy', },
rw [mul_left_inv, one_smul] at i1,
have i2 : g⁻¹ • y ∈ (g⁻¹ * h) • (set_closed_ball s (2 * b)),
  { apply isom_img_mul, exact hy'', },
apply set.nonempty.ne_empty,
rw set.nonempty_def,
use g⁻¹ • y,
exact ⟨i1, i2⟩,
simp,
end

lemma proper_closed_under_inv (k : ℝ) (knonneg : 0 ≤ k)
 (c : ℝ) (b : ℝ) (cpos: c > 0) (bnonneg: 0 ≤ b)
  (s : set β) (t : α)
 [quasigeodesic_space β c b cpos bnonneg] [isom_action α β]
 (ht : t ∈ (proper_action_set α (set_closed_ball s k))) : (t⁻¹) ∈ (proper_action_set α (set_closed_ball s k)) :=
begin
apply set.ne_empty_iff_nonempty.2,
rw set.nonempty_def,
have h : ∃ (x : β), x ∈ set_closed_ball s k ∩ t • set_closed_ball s k,
{ rw ← set.nonempty_def,
  rw ← set.ne_empty_iff_nonempty,
  exact ht, },
rcases h with ⟨x, ⟨hx1, ⟨y, ⟨hy1, hy2⟩⟩⟩⟩,
use y,
split,
{ exact hy1, },
use x,
split,
{ exact hx1, },
rw inv_smul_eq_iff,
exact hy2.symm,
end

lemma closure_mul (g' : α) (K : set α) (hg : g' ∈ subgroup.closure K)(g : α) :
 (∃ k ∈ K, g'*k = g) → g ∈ subgroup.closure K :=
begin
  rintros ⟨k, hk, rfl⟩,
  apply mul_mem hg,
  apply set.mem_of_subset_of_mem (@subgroup.subset_closure α _ K) hk
end

variables (c : ℝ) (b : ℝ) (cpos: 0 < c) (bpos: 0 < b)

lemma sm_aux  [quasigeodesic_space β c b cpos (le_of_lt bpos)]
  [isom_action α β] (s : set β) (htrans: translates_cover α s)
  (f : ℝ → β) (x : β) (xs : x ∈ s) (n : ℕ)
   : ∀ (g : α) (L : ℝ) (Lnonneg : L ≥ 0) (hL' : L ≤ (n : ℝ)*(b/c)),
    ((∃ y ∈ g • s, quasigeodesic L Lnonneg f x y c b) → g ∈ subgroup.closure (proper_action_set α (set_closed_ball s (2*b)))) :=
begin
induction n with d hd,
rintros g L Lnonneg hL ⟨ y, ⟨hy, qg⟩⟩,
norm_cast at hL,
rw zero_mul at hL,
-- if the quasigeodesic has length 0, the end points differ by an element of S
have Lzero : L = 0, by apply le_antisymm hL Lnonneg,
have gfix : x = y,
  have : quasigeodesic 0 (by linarith) f x y c b,
    finish,
  exact degenerate_quasigeodesic f x y c b this,
apply subgroup.subset_closure,
rw ← one_smul α s at xs,
have dzero : dist x y ≤ 2*b,
  begin
    rw [gfix, dist_self y],
    exact mul_nonneg zero_le_two bpos.le,
  end,
have hg : ∃ (t : α) (H : t ∈ proper_action_set α (set_closed_ball s (2 * b))), 1 * t = g,
from intS c b cpos (le_of_lt bpos) s 1 g x y xs hy dzero,
rcases hg with ⟨t, ht, tg⟩,
rw one_mul at tg,
rw ← tg,
exact ht,
-- truncate quasigeodesic to length where we can apply induction hypothesis
let L' := (d : real)*(b/c),
have L'nonneg : L' ≥ 0,
  { apply mul_nonneg, exact nat.cast_nonneg d, apply (le_of_lt (div_pos bpos cpos)), },
rintros g L Lnonneg hL ⟨y, ⟨hy, qg⟩⟩,
by_cases L ≤ d*(b/c),
  apply hd g L Lnonneg h,
  use y,
  exact ⟨hy, qg⟩,
have hL' : L' ≤ L,
  apply le_of_lt,
  apply lt_of_not_ge,
  exact h,
have hq : quasigeodesic L' L'nonneg f x (f L') c b,
  from trunc_quasigeodesic L Lnonneg f x y c b hL' L'nonneg qg,
simp at hd,
rw [nat.succ_eq_one_add, nat.cast_add, nat.cast_one] at hL,
rw ← lt_iff_not_le at h,
--simp at *,
-- endpoint of new quasigeodesic is covered
have L'cov : ∃ g' : α, (f L') ∈ g' • s, from exists_cover_element htrans (f L'),
cases L'cov with g' hg',
have g'_mem_closure : g' ∈ subgroup.closure (proper_action_set α (set_closed_ball s (2 * b))),
  from hd g' L' L'nonneg le_rfl (f L') hg' hq,
have smalldistdom : abs (L' - L) ≤ b/c,
{ rw [ abs_sub_comm, abs_of_nonneg, sub_le_iff_le_add', ← one_mul (b/c), ← add_mul],
  rwa add_comm,
  linarith, },
have cnonneg : c ≠ 0, from ne_of_gt cpos,
have smalldistimg : dist (f L') (f L) ≤ 2*b,
  calc
    dist (f L') (f L) ≤ c * abs(L' - L) + b : (qg.2.2 L' ⟨L'nonneg, hL'⟩ L ⟨Lnonneg, le_rfl⟩).2
    ...               ≤ c * (b/c) + b : add_le_add_right (mul_le_mul_of_nonneg_left smalldistdom cpos.le) _
    ...               = b + b : by {congr' 1, field_simp, rw mul_comm, }
    ...               = 2*b : by linarith,
apply closure_mul g' (proper_action_set α (set_closed_ball s (2 * b))) g'_mem_closure g,
apply intS c b cpos (le_of_lt bpos) s g' g (f L') (f L) hg' _ smalldistimg,
rw qg.2.1,
exact hy,
end



theorem top_iff_subset (S : set α) : ⊤ = subgroup.closure S ↔ ∀ x : α, x ∈ subgroup.closure S :=
begin
split,
{ intros h x,
  rw ← h,
  trivial, },
  intro h,
  ext1,
  split,
  { intro g,
    exact h x, },
  intro g,
  trivial,
end

variable (S : Type*)

open function
open set
open geometric_group_theory
open metric



lemma free_group.range_lift (f : S → α) : range (free_group.lift f) = subgroup.closure (range f) :=
  by simp only [← @free_group.lift.range_eq_closure S α _ f, monoid_hom.coe_range]

lemma top_closure_to_surj_hom (f: S → α) (hf: ⊤ = subgroup.closure (range f)) :
  surjective (free_group.lift f) :=
begin
  rw ← range_iff_surjective,
  rw free_group.range_lift,
  rw ← hf,
  refl,
end

lemma arch' {x y : ℝ} (xpos: x > 0) (ypos: y > 0)
  : ∃ n:ℕ, (n:ℝ)*x ≤ y ∧ y < (n+1 :ℝ)*x :=
begin
  use nat.floor (y/x),
  rw ← le_div_iff xpos,
  split,
  apply nat.floor_le,
  exact (div_pos ypos xpos).le,
  rw ← div_lt_iff xpos,
  apply nat.lt_floor_add_one,
end

lemma arch'' {x y : ℝ} (xpos: x > 0) (ynonneg: 0 ≤ y)
  : ∃ n:ℕ, ((n:ℝ)-1)*x ≤ y ∧ y < (n:ℝ)*x :=
begin
  by_cases hy : y ≤ 0,
    use (1 : ℕ),
    have yzero : y = 0, from le_antisymm hy ynonneg,
    rw yzero,
    simp,
    exact xpos,
  have ypos : 0 < y,
  rw lt_iff_le_not_le,
  exact ⟨ynonneg, hy⟩,
  have := arch' xpos ypos,
  cases this with n hn,
  use (n+1),
  simp [hn],
end
-- Svarc-Milnor part 1: S generates G

theorem metric_svarcmilnor1
  [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (s : set β) (htrans: translates_cover α s) (finitediam : bounded s)
   : ⊤ = subgroup.closure (proper_action_set α (set_closed_ball s (2*b))) :=
begin
  rw top_iff_subset,
  intro g,

-- construct an element of s called t

  let x' : β, exact default,
  have := exists_cover_element htrans x',
  rcases this with ⟨a, ⟨t, ⟨ts, ht⟩⟩ ⟩,

-- connect t and g • t via a quasigeodesic and then apply sm_aux to get that g is generated

  have h : conn_by_quasigeodesic' t (g • t) c b, by apply quasigeodesic_space.quasigeodesics t (g • t),
  rcases h with ⟨ L, Lnonneg, f, qif⟩,
  have harch : ∃ n : ℕ, L ≤ (n : real)*(b/c),
    have := archimedean.arch L (div_pos bpos cpos),
      simp at this,
      exact this,
  cases harch with n hn,
  apply sm_aux c b cpos bpos s htrans f t ts n g L Lnonneg hn,
  use g • t,
  split, use t,
  exact ⟨ts, rfl⟩,
  exact qif,
end

-- The marking corresponding to the setting of Svarc-Milnor

def sm_marking [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  {s : set β} (htrans: translates_cover α s) (finitediam : bounded s)
  : marking α $ proper_action_set α (set_closed_ball s (2*b)) :=

{   to_fun_surjective := begin
    apply top_closure_to_surj_hom,
    rw subtype.range_coe,
    exact metric_svarcmilnor1 c b cpos bpos s htrans finitediam,
  end,
  ..free_group.lift coe,
}

-- auxiliary lemmas about metric spaces

-- the map x to g.x has quasi-dense image

lemma svarcmilnor_qdense
  [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (s : set β) (htrans: translates_cover α s) (finitediam : metric.bounded s) (x : β) (xs : x ∈ s)
   : has_quasidense_image (λ g : α, g • x) :=
begin
  cases finitediam with k hk,
  have knonneg : k ≥ 0,
    rw ← dist_self x,
    apply hk x xs x xs,
  use (k+1),
  split,
  { linarith, },
  intro y,
  have h : ∃ g : α, y ∈ g • s, from exists_cover_element htrans y,
  rcases h with ⟨g, ⟨z, hz⟩ ⟩,
  use g,
  dsimp at *,
  rw ← hz.2,
  rw dist_smul_smul,
  have dxz : dist x z ≤ k, from hk x xs z hz.1,
  linarith,
end

-- there is a constant bounding the distance between x and s.x for all s in the generating set

lemma proper_action_set_bound (b : ℝ) (bnonneg : 0 ≤ b) [pseudo_metric_space β] [isom_action α β]
  (s : set β) (finitediam : bounded s)
  (x : β) (xs : x ∈ s)
  : ∃ k > 0, ∀ t ∈ proper_action_set α (set_closed_ball s (2*b)), dist x (t • x) ≤ k :=
  begin
  cases finitediam with k hk,
  have knonneg : k ≥ 0,
  { rw ← dist_self x,
    exact hk x xs x xs, },
  use 2*(k+2*b)+1,
  split, linarith,
  intros t ht,
  have h : ∃ y : β, y ∈ set_closed_ball s (2*b) ∩ (t • (set_closed_ball s (2*b))),
    rw ← set.nonempty_def,
    rw ← set.ne_empty_iff_nonempty,
    exact ht,
  rcases h with ⟨y, ⟨⟨z, ⟨zs, hz⟩⟩, ⟨a, ⟨⟨m, ⟨ms, hm⟩⟩, ha⟩⟩⟩ ⟩,
  have dxy : dist x y ≤ k + 2*b,
  { apply le_trans (dist_triangle x z y),
    apply add_le_add (hk x xs z zs),
    rwa dist_comm, },
  have dyt : dist y (t • x) ≤ k + 2*b,
    rw ← ha,
    rw dist_smul_smul,
  { apply le_trans (dist_triangle a m x),
    rw add_comm,
    apply add_le_add (hk m ms x xs),
    exact hm, },
  apply le_trans (dist_triangle x y (t • x)),
  linarith,
  end

-- auxiliary lemmas about word metric
open geometric_group_theory
open classical

-- generalisation of sm_aux: g is not only in closure, but word length is bounded by expression involving length of quasi-geodesic
-- proof is very similar to sm_aux - can we do both in one?

lemma wm_aux  [quasigeodesic_space β c b cpos (le_of_lt bpos)]
  [isom_action α β] (s : set β)
  (htrans: translates_cover α s) (finitediam : bounded s)
  (f : ℝ → β) (x : β) (xs : x ∈ s) (n : ℕ)
   : ∀ (g : marked (sm_marking c b cpos bpos htrans finitediam))
    (L : ℝ) (Lnonneg : L ≥ 0) (hL' : L ≤ (n : ℝ)*(b/c)),
    ((∃ y ∈ g • s, quasigeodesic L Lnonneg f x y c b) → dist 1 g ≤ n+1) :=
begin
  let m := marked (sm_marking c b cpos bpos htrans finitediam),
  induction n with d hd,
  rintros g L Lnonneg hL ⟨ y, ⟨hy, qg⟩⟩,
  rw [nat.cast_zero, zero_add],
  norm_cast at hL,
  rw zero_mul at hL,
  have Lzero : L = 0, from antisymm hL Lnonneg,
  have gfix : x = y,
  { apply degenerate_quasigeodesic f x y c b,
    split, exact qg.1,
    split, rw ← Lzero, exact qg.2.1,
    dsimp,
    rintros m ⟨mnonneg, mnonpos⟩ n ⟨nnonneg, nnonpos⟩,
    have mzero : m = 0, from le_antisymm mnonpos mnonneg,
    have nzero : n = 0, from le_antisymm nnonpos nnonneg,
    rw [mzero, nzero],
    simp [bpos.le], },
  have hg : g ∈ proper_action_set α (set_closed_ball s (2*b)),
    apply set.nonempty.ne_empty,
    rw set.nonempty_def,
    use x,
    split,
    { apply self_set_closed_ball,
      apply (mul_pos two_pos bpos).le,
      exact xs, },
    rw isom_of_set_closed_ball,
    rw gfix,
    apply self_set_closed_ball,
    apply (mul_pos two_pos bpos).le,
    exact hy,
  apply gen_norm_le_one_sub, simp [hg],
  let L' := (d : real)*(b/c),
  have L'nonneg : L' ≥ 0,
    { apply mul_nonneg, exact nat.cast_nonneg d, apply (le_of_lt (div_pos bpos cpos)), },
  rintros g L Lnonneg hL ⟨y, ⟨hy, qg⟩⟩,
  by_cases L ≤ d*(b/c),
    have dg : dist 1 g ≤ d+1,
      apply hd g L Lnonneg h,
      use y,
      exact ⟨hy, qg⟩,
    rw [nat.succ_eq_one_add, nat.cast_add, nat.cast_one],
    linarith,
  have hL' : L' ≤ L,
    apply le_of_lt,
    apply lt_of_not_ge,
    exact h,
  have := trunc_quasigeodesic L Lnonneg f x y c b hL' L'nonneg qg,
  simp at hd,
  rw [nat.succ_eq_one_add, nat.cast_add, nat.cast_one] at hL,
  rw ← lt_iff_not_le at h,
  have L'cov : ∃ g' : m, (f L') ∈ g' • s, from exists_cover_element htrans (f L'),
  cases L'cov with g' hg',
  have g'norm : dist 1 g' ≤ d+1,
    from hd g' L' L'nonneg le_rfl (f L') hg' this,
  have smalldistdom : abs (L' - L) ≤ b/c,
  { rw [ abs_sub_comm, abs_of_nonneg, sub_le_iff_le_add', ← one_mul (b/c), ← add_mul, add_comm],
  exact hL,
  linarith, },
  have cnonneg : c ≠ 0, from ne_of_gt cpos,
  have smalldistimg : dist (f L') (f L) ≤ 2*b,
  calc
    dist (f L') (f L) ≤ c * abs(L' - L) + b : (qg.2.2 L' ⟨L'nonneg, hL'⟩ L ⟨Lnonneg, le_rfl⟩).2
    ...               ≤ c * (b/c) + b : add_le_add_right (mul_le_mul_of_nonneg_left smalldistdom cpos.le) _
    ...               = b + b : by {congr' 1, field_simp, rw mul_comm, }
    ...               = 2*b : by linarith,
  rw dist_to_norm,
  have grel : ∃ (k ∈ proper_action_set α (set_closed_ball s (2 * b))), g' * k = g,
    apply intS c b cpos (le_of_lt bpos) s g' g (f L') (f L) hg' _ smalldistimg,
    rw qg.2.1,
    exact hy,
  rcases grel with ⟨k, ⟨hk, grel⟩⟩,
  rw ← grel,
  rw dist_to_norm at g'norm,
  apply gen_set_mul_right'_sub,
  exact hk,
  simp [g'norm],
end

-- easier to apply version of wm_aux

lemma word_metric_bound_of_quasigeodesic

  (s : set β) (L : ℝ) (Lnonneg : L ≥ 0) (f : ℝ → β)
  (x : β) (xs : x ∈ s)  [quasigeodesic_space β c b cpos bpos.le] [isom_action α β]
  (htrans: translates_cover α s) (finitediam : bounded s)
  (g : marked (sm_marking c b cpos bpos htrans finitediam))
  (hf : quasigeodesic L Lnonneg f x (g • x) c b) (n : ℕ)
  (hL : L ≤ ((n : ℝ)*(b/c))) : dist 1 g ≤ (n+1) :=
  begin
    apply wm_aux c b cpos bpos s htrans finitediam f x xs n g L Lnonneg hL,
    use g • x,
    split, use x,
    exact ⟨xs, rfl⟩,
    exact hf,
  end

-- generalisation of proper_action_set_bound: for a general group element expression is bounded by a constant times word length

lemma gen_bound
  (s : set β) (x : β) (xs : x ∈ s)
  [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (htrans: translates_cover α s) (finitediam : bounded s) :
  ∃ k > 0, ∀ g : marked (sm_marking c b cpos bpos htrans finitediam),
  dist x (g • x) ≤ k * dist 1 g :=
begin
  let m := marked (sm_marking c b cpos bpos htrans finitediam),
  have h : ∃ k > 0, ∀ t ∈ proper_action_set α (set_closed_ball s (2*b)), dist x (t • x) ≤ k, from proper_action_set_bound b bpos.le s finitediam x xs,
  rcases h with ⟨k, ⟨kpos, hk⟩⟩,
  use k, split, exact kpos,
  intros g,
  have h : ∃ n : ℕ, dist 1 g ≤ n, from exists_nat_ge (dist 1 g),
  cases h with n hn,
  revert g,
  induction n with d hd,
  { intros g hn,
    norm_cast at hn,
    have gd : dist 1 g = 0, from le_antisymm hn dist_nonneg,
    rw [dist_to_norm, zero_norm_iff_one] at gd,
    rw gd, simp, },
    intros g hn,
    by_cases gn : g = 1,
    { rw gn,
      simp, },

  -- construct a shorter word that is related to original word

    have h : ∃ y : m, (∃ t ∈ proper_action_set α (set_closed_ball s (2*b)), t * y = g) ∧ ∥y∥ = ∥g∥ - 1,
      have := gen_div_left_sub g gn,
        rcases this with ⟨y, ⟨hyor, hynorm⟩⟩,
      use y,
      refine ⟨_, hynorm⟩,
      cases hyor,
      { exact hyor, },
      { rcases hyor with ⟨t, ht, ht'⟩,
        use t⁻¹,
        refine ⟨_, ht'⟩,
        apply proper_closed_under_inv,
        linarith,
        exact ht, },

-- apply induction hypothesis to this shorter word and get bound for original word

    rcases h with ⟨y, ⟨⟨t, ⟨ht1, ht2⟩⟩, hy⟩⟩,
    rw ← ht2,
    apply @le_trans _ _ (dist x ((t * y) • x)) (dist x (t • x) + dist (t • x) ((t * y) • x))  _ _,
    rw ← smul_smul,
    rw dist_smul_smul,
    rw ht2,
    have h : dist x (t • x) ≤ k, from hk t ht1,
      rw [nat.succ_eq_one_add, nat.cast_add, nat.cast_one] at hn,
      rw dist_to_norm at hn,
    have hy' : dist 1 y ≤ d,
    { rw dist_to_norm,
      linarith, },
    have h2 : dist x (y • x) ≤ k * ((dist 1 g)-1),
    { begin
        rw dist_to_norm,
        rw ← hy,
        rw ← dist_to_norm,
        apply hd y hy',
      end, },
    linarith,
    apply dist_triangle,
end

theorem metric_svarcmilnor2
  {s : set β} (x : β) (xs : x ∈ s)  [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (htrans: translates_cover α s) (finitediam : bounded s)
   : is_QI (λ g : marked (sm_marking c b cpos bpos htrans finitediam), g • x) :=
begin
let m := marked (sm_marking c b cpos bpos htrans finitediam),

-- know that quasi-isometry is equivalent to quasidense image and quasi-isometric embedding

apply QIE_with_quasidense_image_is_QI,
have hk : ∃ k > 0, ∀ g : m, dist x (g • x) ≤ k * (dist 1 g),
 from gen_bound c b cpos bpos s x xs htrans finitediam,
rcases hk with ⟨k, ⟨kpos, hk⟩⟩,

-- we set up relevant constants that will show up in calculations later

apply QIE_from_different_constants _ k 1 ((c^2)/b) (b + 2*(b/(c^2))) kpos zero_lt_one,
apply div_pos (sq_pos_of_pos cpos) bpos,
apply add_pos bpos (mul_pos (two_pos) (div_pos bpos (sq_pos_of_pos cpos))),
intros g h,
dsimp,
rw dist_smul_inv,

-- upper bound: follows from gen_bound

calc
  dist x ((g⁻¹ * h) • x )                      ≤ k * dist 1 (g⁻¹ * h)  : hk (g⁻¹*h)
  ...                                          = k * dist g h : by simp
  ...                                          ≤ k * dist g h + 1 : by linarith,
intros g h,
simp only [one_div_div],
have h : conn_by_quasigeodesic' x ((g⁻¹ * h) • x) c b,
  by apply quasigeodesic_space.quasigeodesics x (of_marked(g⁻¹ * h) • x),
rcases h with ⟨ L, Lnonneg, f, ⟨f0, fL, hf⟩⟩,
have hn : ∃ n : ℕ, ((n-1):ℝ)*(b/c) ≤ L ∧ L < (n : ℝ)*(b/c), from arch'' (div_pos bpos cpos) Lnonneg,
rcases hn with ⟨n, ⟨L1, L2⟩ ⟩,
rw dist_smul_inv,

-- lower bound: follows from word_metric_bound_of_quasigeodesic
calc
  dist x ((g⁻¹ * h) • x)                     = dist (f 0) (f L) : by rw [f0, fL]
  ...                                        ≥ (1/c) * |0 - L| - b : (hf 0 ⟨le_rfl, Lnonneg⟩ L ⟨Lnonneg, le_rfl⟩).1
  ...                                        = (1/c) * L - b : by {rw zero_sub, rw abs_neg, rw abs_of_nonneg Lnonneg,}
  ...                                        ≥ (1/c) * (((n:ℝ)-1)*(b/c)) - b : sub_le_sub_right ((@mul_le_mul_left _ _ (((n:ℝ) - 1)*(b/c)) L (1/c) (div_pos (one_pos) cpos)).2 L1 ) _
  ...                                        = (n : ℝ) * (b/c)*(1/c) - (b + (b/c) * (1/c)) : by linarith
  ...                                        = (n : ℝ) * (b/c^2) - (b + b/c^2) : sorry
  ...                                        = ((n : ℝ)+1) * (b/c^2) - (b + 2*(b/c^2)) : by linarith
  ...                                        ≥ (dist 1 (g⁻¹ * h))* (b/c^2)  - (b + 2*(b/c^2)) : sub_le_sub_right ((@mul_le_mul_right _ _  (dist 1 (g⁻¹ * h)) ((n : ℝ)+1) (b/c^2) (div_pos bpos (sq_pos_of_pos cpos))).2 (word_metric_bound_of_quasigeodesic c b cpos bpos s L Lnonneg f x xs htrans finitediam (g⁻¹*h) ⟨f0, fL, hf⟩ (n) L2.le) ) _
  ...                                        = b/c^2 * (dist g h) - (b + 2*(b/c^2)) : by {rw mul_comm, simp,},
apply svarcmilnor_qdense c b cpos bpos s htrans finitediam x xs,
end

-- in the following we try and compute a specific example, namely that Z is quasi-isometric to R.

-- R is quasigeodesic (1,1), need both positive for theorem to apply

noncomputable instance : quasigeodesic_space ℝ 1 1 (one_pos) (by linarith) :=
{
  quasigeodesics := begin
    intros x y,
    wlog h : y ≥ x,
    exact le_total x y,
    use [y - x, sub_nonneg.2 h, (λ a, x+a)],
    split;
    simp,
    intros m hm1 hm2 n hn1 hn2,
    split;
    repeat {rw add_comm,
    apply le_add_of_nonneg_left,
    exact one_pos.le,},
    use [x - y, sub_nonneg.2 h, (λ a, x-a)],
    split;
    simp,
    intros m hm1 hm2 n hn1 hn2,
    split;
    repeat {rw add_comm,
    apply le_add_of_nonneg_left,
    exact one_pos.le,},
  end

}

/- Svarc milnor allows conclusion of quasiisometry given a 'nice' action of the group.#check
   Here we have the translation action of Z on R. -/

instance translation_action : isom_action (multiplicative ℤ) ℝ := {
  smul := (λ n x, ((multiplicative.to_add n) : ℝ)+x),
  one_smul := by simp,
  mul_smul := begin
    intros x y b,
    simp,
    rw add_assoc,
  end,
  isom := by {intros b x y, simp,} }

-- conditions of svarc-milnor with s = [0,1].

theorem translates_cover_interval : translates_cover (multiplicative ℤ) ({x : ℝ| 0 ≤ x ∧ x ≤ 1}) :=
begin
  intro x,
  rw mem_Union,
  have := exists_of_exists_unique (@exists_unique_zsmul_near_of_pos ℝ _ _ (1 : ℝ) (one_pos) x),
  simp at this,
  rcases this with ⟨y, hy1, hy2⟩,
  use [multiplicative.of_add y, x-y],
  simp,
  split,
    rw add_comm at hy2,
    exact ⟨hy1, hy2.le⟩,
  sorry
end

theorem interval_finitediam : bounded {x : ℝ| 0 ≤ x ∧ x ≤ 1} :=
begin
  use 1,
  intros x hx y hy,
  dsimp at *,
  apply abs_le.2,
  split;
  linarith,
end

noncomputable def mult_Z_marking := sm_marking 1 1 (one_pos) (one_pos) translates_cover_interval interval_finitediam

-- there exists a quasiisometry from a (marking of) Z to R, namely the inclusion

theorem Z_qI_to_R : ∃ f : marked (mult_Z_marking) → ℝ, is_QI f :=
begin
 use λ n : marked (mult_Z_marking), (n • 0),
 apply metric_svarcmilnor2 1 1 one_pos one_pos,
 exact ⟨le_rfl, one_pos.le⟩,
end
