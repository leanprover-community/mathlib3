
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
-- dsimp at hw,
use w,
split,
{ apply self_set_closed_ball, linarith, exact ws },
exact hw, rw proper_action_set, dsimp,
have i1 : g⁻¹ • y ∈ (g⁻¹ * g) • (set_closed_ball s (2 * b)),
  { apply isom_img_mul, exact hy', },
simp at i1,
-- rw ← one_smul α (set_closed_ball s (2 * b)) at i1,
have i2 : g⁻¹ • y ∈ (g⁻¹ * h) • (set_closed_ball s (2 * b)),
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

variables (c : ℝ) (b : ℝ) (cpos: 0 < c) (bpos: 0 < b)

lemma sm_aux  [quasigeodesic_space β c b cpos (le_of_lt bpos)]
  [isom_action α β] (s : set β) (htrans: translates_cover α s)
  (f : ℝ → β) (x : β) (xs : x ∈ s) (n : ℕ)
   : ∀ (g : α) (L : ℝ) (Lnonneg : L ≥ 0) (hL' : L ≤ (n : ℝ)*(b/c)),
    ((∃ y ∈ g • s, quasigeodesic L Lnonneg f x y c b) → g ∈ subgroup.closure (proper_action_set α (set_closed_ball s (2*b)))) :=
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
rw ← one_smul α s at xs,
have dzero : dist x y ≤ 2*b,
  begin
    rw gfix,
    rw dist_self x,
    apply mul_nonneg,
    linarith,
    exact le_of_lt bpos,
  end,
have hg : ∃ (t : α) (H : t ∈ proper_action_set α (set_closed_ball s (2 * b))), 1 * t = g,
from intS c b cpos (le_of_lt bpos) s 1 g x y xs hy dzero,
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
have L'cov : ∃ g' : α, (f L') ∈ g' • s, from exists_cover_element htrans (f L'),
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
    dist (f L') (f L) ≤ c * abs(L' - L) + b : (qg.2.2 L' ⟨L'nonneg, hL'⟩ L ⟨Lnonneg, le_rfl⟩).2
    ...               ≤ c * (b/c) + b : add_le_add_right (mul_le_mul_of_nonneg_left smalldistdom cpos.le) _
    ...               = b + b : by sorry
    ...               = 2*b : by linarith,
apply closure_mul g' (proper_action_set α (set_closed_ball s (2 * b))) g'_mem_closure g,
apply intS c b cpos (le_of_lt bpos) s g' g (f L') (f L) hg' _ smalldistimg,
rw qg.2.1,
exact hy,
end



theorem top_iff_subset (S : set α) : ⊤ = subgroup.closure S ↔ ∀ x : α, x ∈ subgroup.closure S :=
sorry

variable (S : Type*)

open function
open set
open geometric_group_theory
open metric


lemma free_group.range_lift (f : S → α) : range (free_group.lift f) = subgroup.closure (range f) :=
sorry


lemma top_closure_to_surj_hom (f: S → α) (hf: ⊤ = subgroup.closure (range f)) :
  surjective (free_group.lift f) :=
begin
  rw ← range_iff_surjective,
  rw free_group.range_lift,
  rw ← hf,
  refl,
end




-- Svarc-Milnor part 1: S generates G

theorem metric_svarcmilnor1
  [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (s : set β) (htrans: translates_cover α s) (finitediam : bounded s)
   : ⊤ = subgroup.closure (proper_action_set α (set_closed_ball s (2*b))) :=
begin
  rw top_iff_subset,
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
  simp,
  exact ⟨xs, qif⟩,
end

-- The marking corresponding to the setting of Svarc-Milnor

def sm_marking [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (s : set β) (htrans: translates_cover α s) (finitediam : bounded s)
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

lemma proper_action_set_bound (b : ℝ) [pseudo_metric_space β] [isom_action α β]
  (s : set β) (finitediam : bounded s)
  (x : β) (xs : x ∈ s)
  : ∃ k : ℝ, ∀ t ∈ proper_action_set α (set_closed_ball s (2*b)), dist x (t • x) ≤ k :=
  begin
  cases finitediam with k hk,
  use 2*(k+2*b),
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

lemma word_metric_bound_of_quasigeodesic

  (s : set β) (L : ℝ) (Lnonneg : L ≥ 0) (f : ℝ → β)
  (x : β)  [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (htrans: translates_cover α s) (finitediam : bounded s)
  (g : marked (sm_marking c b cpos bpos s htrans finitediam))
  (hf : quasigeodesic L Lnonneg f x (g • x) c b) (n : ℕ)
  (hL : ((n-1):ℝ)*(b/c) ≤ L ∧ L < ((n : ℝ)*(b/c))) :
  dist 1 g ≤ n := sorry

-- generalisation of proper_action_set_bound: for a general group element expression is bounded by a constant times word length

lemma gen_bound
  (s : set β) [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (htrans: translates_cover α s) (finitediam : bounded s) :
  ∃ k > 0, ∀ g : marked (sm_marking c b cpos bpos s htrans finitediam),
   ∀ x ∈ s, dist x (g • x) ≤ k * dist 1 g :=
  sorry

-- have coverx : ∃ a : α, x ∈ isom_img a s,
-- begin
-- rw ← set.mem_Union, exact htrans x,
-- end,



-- rcases coverx with ⟨a, ⟨z, ⟨zs, hz⟩⟩⟩,
-- dsimp at hz,
-- rw ← hz,
-- rw dist_of_inv_isom,
-- repeat {rw smul_smul,},


theorem metric_svarcmilnor2
  (s : set β) (x : β) (xs : x ∈ s)  [quasigeodesic_space β c b cpos (le_of_lt bpos)] [isom_action α β]
  (htrans: translates_cover α s) (finitediam : bounded s)
   : is_QI (λ g : marked (sm_marking c b cpos bpos s htrans finitediam), g • x) :=
begin
let m := marked (sm_marking c b cpos bpos s htrans finitediam),

-- know that quasi-isometry is equivalent to quasidense image and quasi-isometric embedding

apply QIE_with_quasidense_image_is_QI,
have hk : ∃ k > 0, ∀ g : m, ∀ x ∈ s, dist x (g • x) ≤ k * (dist 1 g),
 from gen_bound c b cpos bpos s htrans finitediam,
rcases hk with ⟨k, ⟨kpos, hk⟩⟩,

-- we set up relevant constants that will show up in calculations later

apply QIE_from_different_constants _ k 1 ((c^2)/b) (b + (b/(c^2))) kpos zero_lt_one,
apply div_pos (sq_pos_of_pos cpos) bpos,
apply add_pos bpos (div_pos bpos (sq_pos_of_pos cpos)),
intros g h,
simp,
rw dist_smul_inv,

-- upper bound: follows from gen_bound

calc
  dist x ((g⁻¹ * h) • x )                      ≤ k * dist 1 (g⁻¹ * h)  : hk (g⁻¹*h) x xs
  ...                                          = k * dist g h : by simp
  ...                                          ≤ k * dist g h + 1 : by linarith,
intros g h, simp,
rw add_comm,
rw ← sub_le_iff_le_add',
have h : conn_by_quasigeodesic' x ((g⁻¹ * h) • x) c b, by apply quasigeodesic_space.quasigeodesics x (of_marked(g⁻¹ * h) • x),
rcases h with ⟨ L, Lnonneg, f, ⟨f0, fL, hf⟩⟩,
have hn : ∃ n : ℕ, ((n-1):ℝ)*(b/c) ≤ L ∧ L < (n : ℝ)*(b/c),
  { sorry, },
rcases hn with ⟨n, ⟨L1, L2⟩ ⟩,
rw dist_smul_inv,

-- lower bound: follows from word_metric_bound_of_quasigeodesic
calc
  dist x ((g⁻¹ * h) • x)                     = dist (f 0) (f L) : by rw [f0, fL]
  ...                                        ≥ (1/c) * |0 - L| - b : (hf 0 ⟨le_rfl, Lnonneg⟩ L ⟨Lnonneg, le_rfl⟩).1
  ...                                        = (1/c) * L - b : by sorry
  ...                                        ≥ (1/c) * (((n:ℝ)-1)*(b/c)) - b : sub_le_sub_right ((@mul_le_mul_left _ _ (((n:ℝ) - 1)*(b/c)) L (1/c) (div_pos (one_pos) cpos)).2 L1 ) _
  ...                                        = (n : ℝ) * (b/c)*(1/c) - (b + (b/c) * (1/c)) : by linarith
  ...                                        = (n : ℝ) * (b/c^2) - (b + b/c^2) : sorry
  ...                                        ≥ (dist 1 (g⁻¹ * h))* (b/c^2)  - (b + b/c^2) : sub_le_sub_right ((@mul_le_mul_right _ _  (dist 1 (g⁻¹ * h)) (n : ℝ) (b/c^2) (div_pos bpos (sq_pos_of_pos cpos))).2 (word_metric_bound_of_quasigeodesic c b cpos bpos s L Lnonneg f x htrans finitediam (g⁻¹*h) ⟨f0, fL, hf⟩ n ⟨L1, L2⟩) ) _
  ...                                        ≥ b/c^2 * (dist g h) - (b + b/c^2) : by {rw mul_comm, simp,},
apply svarcmilnor_qdense c b cpos bpos s htrans finitediam x xs,
end
