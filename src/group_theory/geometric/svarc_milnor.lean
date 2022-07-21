
/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Georgi Kocharyan.
-/
import .cayley_graph
import .geodesic_space
import .isom_action
import .quasi_iso
import topology.metric_space.isometry


open classical
open_locale big_operators pointwise

variables {α β : Type*} [inhabited β] [group α] [inhabited α]


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
have hy'' : y ∈ isom_img h (set_closed_ball s (2*b)),
rcases hy with ⟨ w, ⟨ ws, hw ⟩⟩, dsimp at hw,
use w,
split,
{ apply self_set_closed_ball, linarith, exact ws },
exact hw, rw proper_action_set, dsimp,
have i1 : g⁻¹ • y ∈ isom_img (g⁻¹ * g) (set_closed_ball s (2 * b)),
  { apply isom_img_mul, exact hy', },
simp at i1,
rw ← isom_img_one at i1,
have i2 : g⁻¹ • y ∈ isom_img (g⁻¹ * h) (set_closed_ball s (2 * b)),
  { apply isom_img_mul, exact hy'', },
apply set.nonempty.ne_empty,
rw set.nonempty_def,
use g⁻¹ • y,
exact ⟨i1, i2⟩,
simp,
end

-- lemma intS'  (c : ℝ) (b : ℝ) (cpos: c > 0) (bnonneg: b ≥ 0)  [quasigeodesic_space β c b cpos bnonneg]
--   [isom_action α β] (s : set β) (g : α) (h : α) (x : β) (y : β) (hx: x ∈ g • s)
--   (hy : y ∈ h • s) (hd : dist x y ≤ 2*b)
--   : g⁻¹ * h ∈ (@proper_action_set α _ _ _ _ (set_closed_ball s (2*b))) :=
-- begin
--   have h : ∃ t ∈ (@proper_action_set α _ _ _ _ (set_closed_ball s (2*b))), g*t = h,
--     apply intS c b cpos bnonneg s g h x y hx hy hd,
--   rcases h with ⟨t, ⟨ht1, ht2⟩ ⟩,
--   have hi : t = g⁻¹ * h,
--     rw ← ht2, simp,
--   rw ← hi,
--   exact ht1,
-- end

-- namespace list

-- theorem subdiv {L : ℝ} (Lnonneg : L ≥ 0) {d : ℝ} (dpos : d > 0)
--  : ∃ l : list ℝ, l.head = 0 ∧ (l.reverse).head = L ∧ (∀ i : ℕ, (l.inth i)-(l.inth (i-1)) ≤ d ∧ l.inth i ≥ 0 ∧ l.inth i ≤ L) :=
-- begin
-- sorry
-- end

-- def right_inv_list (g : α) : list α → list α
-- | nil := [g]
-- | (cons a l) :=  (g* a⁻¹) :: ((a*(l.head)) :: (erasep (λ x, true) (right_inv_list l)))


-- lemma prod_of_inv (g : α) (l : list α) : g = list.prod (right_inv_list g l) :=
-- begin
-- sorry
-- end

lemma closure_mul (g' : α) (K : set α) (hg : g' ∈ subgroup.closure K)(g : α) : (∃ k ∈ K, g'*k = g) → g ∈ subgroup.closure K :=
sorry

lemma sm_aux (c : ℝ) (b : ℝ) (cpos: c > 0) (bpos: b > 0)  [quasigeodesic_space β c b cpos (le_of_lt bpos)]
  [isom_action α β] (s : set β) (htrans: translates_cover α s) (f : ℝ → β) (x : β) (xs : x ∈ s) (n : ℕ)
   : ∀ (g : α) (L : ℝ) (Lnonneg : L ≥ 0) (hL' : L ≤ (n : ℝ)*(b/c)), ((∃ y ∈ g • s, quasigeodesic L Lnonneg f x y c b) → g ∈ subgroup.closure (proper_action_set α (set_closed_ball s (2*b)))) :=
begin
-- have harch : ∃ n : ℕ, L ≤ (n : real)*b/c,
-- --apply real.archimedean.arch,
--   sorry,
-- cases harch with n hn,
induction n with d hd,
rintros g L Lnonneg hL ⟨ y, ⟨hy, qg⟩⟩,
simp at hL,
have Lzero : L = 0, by apply le_antisymm hL Lnonneg,
have gfix : y = x,
  apply degenerate_quasigeodesic f y x c b,
  -- rw Lzero at qg,
  sorry,
apply subgroup.subset_closure,
rw @isom_img_one α β _ _ _ s at xs,
have dzero : dist x y ≤ 2*b,
  begin
    rw gfix,
    rw dist_self x,
    apply mul_nonneg,
    linarith,
    exact le_of_lt bpos,
  end,
have hg : ∃ (t : α) (H : t ∈ proper_action_set α (set_closed_ball s (2 * b))), 1 * t = g, from intS c b cpos (le_of_lt bpos) s 1 g x y xs hy dzero,
simp at hg,
exact hg,
let L' := (d : real)*(b/c),
have L'nonneg : L' ≥ 0,
  { apply mul_nonneg, simp, apply (le_of_lt (div_pos bpos cpos)), },
rintros g L Lnonneg hL ⟨y, ⟨hy, qg⟩⟩,
by_cases L ≤ d*(b/c),
  apply hd g L Lnonneg h,
  use y,
  exact ⟨hy, qg⟩,
have hL' : L' ≤ L,
  apply le_of_lt,
  apply lt_of_not_ge,
  exact h,
have hq : quasigeodesic L' L'nonneg f x (f L') c b, from trunc_quasigeodesic L Lnonneg f x y c b hL' L'nonneg qg,
simp at *,
have L'cov : ∃ g' : α, (f L') ∈ isom_img g' s, from exists_cover_element htrans (f L'),
cases L'cov with g' hg',
have g'_mem_closure : g' ∈ subgroup.closure (proper_action_set α (set_closed_ball s (2 * b))),
  from hd g' L' L'nonneg le_rfl (f L') hg' hq,
have smalldistdom : abs (L' - L) ≤ b/c,
{ rw abs_sub_comm,
  rw abs_of_nonneg,
  simp,
  rw ← one_mul (b/c),
  rw ← add_mul,
  rwa add_comm,
  linarith, },
have smalldistimg : dist (f L') (f L) ≤ 2*b,
  calc
    dist (f L') (f L) ≤ c * abs(L' - L) + b : begin exact (qg.2.2 L' ⟨L'nonneg, hL'⟩ L ⟨Lnonneg, le_rfl⟩).2, end
    ...               ≤ c * (b/c) + b : begin exact add_le_add (mul_le_mul_of_nonneg_left smalldistdom (le_of_lt cpos)) (le_rfl), end
    ...               = b + b : by sorry
    ...               = 2*b : by linarith,
apply closure_mul g' (proper_action_set α (set_closed_ball s (2 * b))) g'_mem_closure g,
apply intS c b cpos (le_of_lt bpos) s g' g (f L') (f L) hg' _ smalldistimg,
rw qg.2.1,
exact hy,
end

-- Svarc-Milnor part 1: S generates G

theorem metric_svarcmilnor1  (c : ℝ) (b : ℝ) (cpos: c > 0) (bpos: b > 0)
  [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (s : set β) (htrans: translates_cover α s) (finitediam : metric.bounded s)
   : α = subgroup.closure (proper_action_set α (set_closed_ball s (2*b))) :=
begin
  rw generates_iff_subset,
  intro g,
  let x' : β, exact default,
  let a := cover_element htrans x',
  have snonempty: ∃ x, x ∈ s,
    sorry,
  let x := classical.some snonempty,
  have xs : x ∈ s, from classical.some_spec snonempty,
  -- have imgnonempty: ∃ x, x ∈ g • s,
  --   use g • x,
  --   apply isom_img_self,
  --   apply classical.some_spec snonempty,
  -- let y := classical.some imgnonempty,
  have h : conn_by_quasigeodesic' x (g • x) c b, by apply quasigeodesic_space.quasigeodesics x (g • x),
  rcases h with ⟨ L, Lnonneg, f, qif⟩,
  have harch : ∃ n : ℕ, L ≤ (n : real)*(b/c),
  --  apply archimedean.arch L (div_pos bpos cpos),
    sorry,
  cases harch with n hn,
  apply sm_aux c b cpos bpos s htrans f x xs n g L Lnonneg hn,
  use g • x,
  exact ⟨isom_img_self g s xs, qif⟩,

end


variables (c : ℝ) (b : ℝ) (cpos: c > 0) (bpos: b > 0)



open metric

-- auxiliary lemmas about metric spaces

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
  rw ← dist_of_isom,
  have dxz : dist x z ≤ k, from hk x xs z hz.1,
  linarith,
end

lemma proper_action_set_bound (b : ℝ) [pseudo_metric_space β] [isom_action α β]
  (s : set β) (finitediam : metric.bounded s)
  (x : β) (xs : x ∈ s)
  : ∃ k : ℝ, ∀ t ∈ proper_action_set α (set_closed_ball s (2*b)), dist x (t • x) ≤ k :=
  begin
  cases finitediam with k hk,
  use 2*(k+2*b),
  intros t ht,
  have h : ∃ y : β, y ∈ set_closed_ball s (2*b) ∩ (isom_img t (set_closed_ball s (2*b))),
    rw ← set.nonempty_def,
    rw ← set.ne_empty_iff_nonempty,
    exact ht,
  rcases h with ⟨y, ⟨⟨z, ⟨zs, hz⟩⟩, ⟨a, ⟨⟨m, ⟨ms, hm⟩⟩, ha⟩⟩⟩ ⟩,
  have dxy : dist x y ≤ k + 2*b,
  { apply le_trans (dist_triangle x z y),
    apply add_le_add (hk x xs z zs),
    rwa dist_comm, },
  dsimp at ha,
  have dyt : dist y (t • x) ≤ k + 2*b,
    rw ← ha,
    rw ← dist_of_isom,
  { apply le_trans (dist_triangle a m x),
    rw add_comm,
    apply add_le_add (hk m ms x xs),
    exact hm, },
  apply le_trans (dist_triangle x y (t • x)),
  linarith,
  end

variables (s : set β) [quasigeodesic_space β c b cpos (le_of_lt bpos)]
  [isom_action α β]
  (htrans: @translates_cover α β _ _ _ s) (finitediam : metric.bounded s)

-- auxiliary lemmas about word metric

lemma word_metric_bound_of_quasigeodesic
  (L : ℝ) (Lnonneg : L ≥ 0) (f : ℝ → β)
  (g : α) (x : β)
  (hf : quasigeodesic L Lnonneg f x (g • x) c b) (n : ℕ)
  (hL : (n:ℝ)*(b/c) ≤ L ∧ L < ((n : ℝ)+1)*(b/c)) :
  ((@word_metric α _ _ (@proper_action_set α β _ _ _ (set_closed_ball s (2*b)))
  (metric_svarcmilnor1 c b cpos bpos s htrans finitediam))).dist 1 g ≤ n := sorry

variables (g : α)

#check (((@word_metric α _ _ (@proper_action_set α β _ _ _ (set_closed_ball s (2*b)))
 (metric_svarcmilnor1 c b cpos bpos s htrans finitediam))).dist) g g

lemma gen_bound
  :
  ∃ k > 0, ∀ g : α, ∀ x ∈ s, dist x (g • x) ≤
  k * (@word_metric α _ _ (@proper_action_set α β _ _ _ (set_closed_ball s (2*b)))
   (metric_svarcmilnor1 c b cpos bpos s htrans finitediam)).dist 1 g :=
  sorry


-- notation `cayleydist` := word_metric
--(@word_metric α _ _ (@proper_action_set α β _ _ _ (set_closed_ball s (2*b))) (metric_svarcmilnor1 c b cpos bpos s htrans finitediam)).dist

theorem metric_svarcmilnor2
  (x : β) (xs : x ∈ s)
   : @is_QI α β (@word_metric α _ _ (@proper_action_set α β _ _ _ (set_closed_ball s (2*b)))
    (metric_svarcmilnor1 c b cpos bpos s htrans finitediam)) _ (λ g : α, g • x) :=
begin
let cayleydist := (@word_metric α _ _ (@proper_action_set α β _ _ _ (set_closed_ball s (2*b)))
  (metric_svarcmilnor1 c b cpos bpos s htrans finitediam)).dist,
apply QIE_with_quasidense_image_is_QI,
have hk : ∃ k > 0, ∀ g : α, ∀ x ∈ s, dist x (g • x) ≤ k * (cayleydist 1 g), from gen_bound c b cpos bpos s htrans finitediam,
rcases hk with ⟨k, ⟨kpos, hk⟩⟩,
apply QIE_from_different_constants _ k 1 ((c^2)/b) (b + (b/(c^2))) kpos zero_lt_one,
apply div_pos (sq_pos_of_pos cpos) bpos,
apply add_pos bpos (div_pos bpos (sq_pos_of_pos cpos)),
intros g h,
simp,
have coverx : ∃ a : α, x ∈ isom_img a s,
begin
rw ← set.mem_Union, exact htrans x,
end,
rcases coverx with ⟨a, ⟨z, ⟨zs, hz⟩⟩⟩,
dsimp at hz,
rw ← hz,
rw dist_of_inv_isom,
repeat {rw smul_smul,},

rw dist_of_inv (@proper_action_set α β _ _ _ (set_closed_ball  s (2*b))) (metric_svarcmilnor1 c b cpos bpos s htrans finitediam) g h,

end
