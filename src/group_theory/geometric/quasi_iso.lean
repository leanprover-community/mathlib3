/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clara Löh
-/
import topology.metric_space.basic

/-!
# Quasi-isometric embeddings and quasi-isometries

We define quasi-isometries as quasi-isometric embeddings that admit a quasi-inverse quasi-isometric
embedding. We then prove that a quasi-isometric embedding is a quasi-isometry if and only if it has
quasi-dense image.
-/

variables {X Y : Type*} [pseudo_metric_space X] [pseudo_metric_space Y]

-- quasi-isometric embeddings
def is_QIE_lower (f : X → Y) (c b : ℝ) := ∀ x x', 1/c * dist x x' - b ≤ dist (f x) (f x')
def is_QIE_upper (f : X → Y) (c b : ℝ) := ∀ x x', dist (f x) (f x') ≤ c * dist x x' + b

def is_QIE' (f : X → Y) (c b : ℝ) := is_QIE_upper f c b ∧ is_QIE_lower f c b

def is_QIE (f : X → Y) := ∃ c, ∃ b, 0 < c ∧ 0 < b ∧ is_QIE' f c b

-- finite distance
def has_fin_dist' (f g : X → Y) (c : ℝ) := ∀ x, dist (f x) (g x) ≤ c

def has_fin_dist (f g : X → Y) := ∃ c : ℝ, 0 < c ∧ has_fin_dist' f g c

def are_quasi_inverse (f : X → Y) (g : Y → X) := has_fin_dist (g ∘ f) id ∧ has_fin_dist (f ∘ g) id

-- quasi-isometry
def is_QI (f : X → Y) := is_QIE f ∧ ∃ g : Y → X, is_QIE g ∧ are_quasi_inverse f g

/-! ### Two lemmas on quasi-isometric embeddings -/

-- rewriting the lower estimate for quasi-isometric embeddings
lemma QIE_lower_est (f : X → Y) (c b : ℝ) (c_pos : 0 < c) (f_is_QIE : is_QIE' f c b) :
  ∀ x x', dist x x' ≤ c * dist (f x) (f x') + c * b :=
λ x x',
  calc dist x x'
         = c * (1/c * dist x x' - b) + c * b
         : by simp [div_self, c_pos.ne', mul_sub]
     ... ≤ c * dist (f x) (f x') + c * b
         : add_le_add_right (mul_le_mul_of_nonneg_left (f_is_QIE.2 x x') c_pos.le) _

-- Sometimes, it is convenient to be able to use different constants for the upper/lower estimates
lemma QIE_from_different_constants (f : X → Y) (c1 b1 c2 b2 : ℝ) (c1_pos : 0 < c1) (b1_pos : 0 < b1)
  (c2_pos : 0 < c2) (b2_pos : 0 < b2) (f_QIE_upper : is_QIE_upper f c1 b1)
  (f_QIE_lower : is_QIE_lower f c2 b2) : is_QIE f :=
begin
  refine ⟨c1 + c2, b1 + b2, _⟩,
  let c := c1 + c2,
  let b := b1 + b2,

  have b_pos : 0 < b := add_pos b1_pos b2_pos,
  have c1_leq_c : c1 ≤ c, by simp [le_of_lt c2_pos],
  have b1_leq_b : b1 ≤ b, by simp [le_of_lt b2_pos],
  have b_leq_b2 : -b ≤ -b2, by simp [le_of_lt b1_pos],
  have c2_leq_c' : c2 ≤ c, by simp [le_of_lt c1_pos],
  have c2_leq_c : 1/c2 ≥ 1/c, by simp [c2_leq_c', inv_le_inv_of_le c2_pos],

  refine ⟨add_pos c1_pos c2_pos, b_pos, λ x x', _, λ x x', _⟩,
  { calc dist (f x) (f x')
           ≤ c1 * dist x x' + b1
           : f_QIE_upper x x'
       ... ≤ c1 * dist x x' + b
           : add_le_add_left b1_leq_b (c1 * dist x x')
       ... ≤ c * dist x x' + b
           : by {apply add_le_add_right,
                 exact mul_le_mul_of_nonneg_right c1_leq_c dist_nonneg} },
  { calc dist (f x) (f x')
           ≥ 1/c2 * dist x x' - b2
           : f_QIE_lower x x'
       ... ≥ 1/c2 * dist x x' - b
           : add_le_add_left b_leq_b2 _
       ... ≥ 1/c * dist x x' - b
           : by {apply add_le_add_right,
                 exact mul_le_mul_of_nonneg_right c2_leq_c dist_nonneg} }
end


/-! ### An alternative characterisation of quasi-isometries -/

-- We show that a quasi-isometric embedding is a quasi-isometry
-- if and only if it has quasi-dense image.
-- We show the two implications separately:

def has_quasidense_image' {X Y : Type*} [pseudo_metric_space Y] (f : X → Y) (c : ℝ) : Prop :=
∀ y, ∃ x, dist (f x) y ≤ c

def has_quasidense_image  {X Y : Type*} [pseudo_metric_space Y] (f : X → Y) :=
∃ c, 0 < c ∧ has_quasidense_image' f c

-- Quasi-isometries have quasi-dense image:
theorem QI_has_quasidense_image (f : X → Y) (f_is_QI : is_QI f) : has_quasidense_image f :=
begin
  obtain ⟨g, is_QIE_g, fg_qinv⟩ := f_is_QI.2,
  obtain ⟨c, c_pos, fg_c_close_to_id⟩ := fg_qinv.2,
  exact ⟨c, c_pos, λ y, ⟨g y, fg_c_close_to_id y⟩⟩,
end

-- Quasi-isometric embeddings with quasi-dense image are quasi-isometries:

-- Preparation:
-- Quasi-inverses of quasi-isometric embeddings
-- are quasi-isometric embeddings
lemma quasiinverse_of_QIE_is_QIE (f : X → Y) (g : Y → X) (f_is_QIE : is_QIE f)
  (fg_qinv : are_quasi_inverse f g) : is_QIE g :=
begin
  -- We choose constants witnessing that
  -- f is a quasi-isometric embedding and that
  -- f and g are quasi-inverse to each other:
  rcases f_is_QIE with ⟨cf, bf, cf_pos, bf_pos,
                        f_is_QIE_upper, f_is_QIE_lower⟩,
  rcases fg_qinv with ⟨⟨c_gf, c_gf_pos, gf_close_to_id⟩,
                       ⟨c_fg, c_fg_pos, fg_close_to_id⟩⟩,
  have f_is_cfbf_QIE : is_QIE' f cf bf,
       by exact ⟨f_is_QIE_upper, f_is_QIE_lower⟩,

  -- We combine these constants appropriately:
  let c1 := cf,
  let b1 := cf * (2 * c_fg + bf),
  let c2 := cf,
  let b2 := 1/cf * (2 * c_fg + bf),
  have c1_pos : c1 > 0,
       by exact cf_pos,
  have b1_pos : b1 > 0,
       by {apply mul_pos cf_pos,
           apply add_pos _ bf_pos,
           simp [mul_pos _ c_fg_pos]},
  have c2_pos : c2 > 0,
       by exact cf_pos,
  have b2_pos : b2 > 0,
       by {apply mul_pos,
           apply one_div_pos.mpr cf_pos,
           apply add_pos _ bf_pos,
           simp [mul_pos _ c_fg_pos]},

  -- The upper estimate for g:
  have g_is_QIE_upper : is_QIE_upper g c1 b1, by
  begin
    unfold is_QIE_upper,
    assume y y' : Y,
    let x  := g y,
    let x' := g y',

    have dist_f_estimate : dist (f x) (f x') ≤ dist y y' + 2 * c_fg,
    by calc dist (f x) (f x')
              ≤ dist (f x) y + dist y (f x')
              : by simp [dist_triangle]
          ... ≤ dist (f x) y + dist y y' + dist y' (f x')
              : by {ring_nf,simp [dist_triangle y y' (f x')]}
          ... ≤ c_fg + dist y y' + dist y' (f x')
              : by {simp, exact fg_close_to_id y}
          ... ≤ c_fg + dist y y' + c_fg
              : by {simp,rw[dist_comm],exact fg_close_to_id y'}
          ... ≤ dist y y' + 2 *c_fg
              : by ring_nf,

    calc dist (g y) (g y')
           = dist x x'
           : by  refl
       ... ≤ cf * dist (f x) (f x') + cf * bf
           : QIE_lower_est f cf bf cf_pos f_is_cfbf_QIE x x'
       ... ≤ cf * (dist y y' + 2 * c_fg) + cf * bf
           : by simp [le_of_lt cf_pos,mul_le_mul_of_nonneg_left,
                     dist_f_estimate]
       ... = cf * dist y y' + cf * (2 * c_fg + bf)
           : by ring
       ... ≤ c1 * dist y y' + b1
           : by refl,
  end,

  -- The lower estimate for g:
  have g_is_QIE_lower : is_QIE_lower g c2 b2, by
  begin
    unfold is_QIE_lower,
    assume y y' : Y,
    let x  := g y,
    let x' := g y',

    have cf_times_claim :
         cf * dist (g y) (g y') ≥ dist y y' - cf * b2,
    by calc cf * dist (g y) (g y')
             = cf * dist x x'
             : by refl
         ... ≥ dist (f x) (f x') - bf
             : by {simp,exact f_is_QIE_upper x x'}
         ... ≥ dist (f x) y' - dist (f x') y' - bf
             : by simp [dist_triangle]
         ... ≥ dist y' y - dist (f x) y - dist (f x') y' - bf
             : by simp [dist_triangle_left y' y (f x)]
         ... ≥ dist y' y - c_fg - dist (f x') y' - bf
             : by {simp, exact fg_close_to_id y}
         ... ≥ dist y' y - c_fg - c_fg - bf
             : by {simp, exact fg_close_to_id y'}
         ... ≥ dist y y' - cf * (1/cf * (2 * c_fg + bf))
             : by {simp [ne_of_gt cf_pos,dist_comm], ring_nf}
         ... = dist y y' - cf * b2
             : by refl,

    have cf_inv_nonneg : 0 ≤ cf⁻¹,
         by simp [inv_nonneg.mpr (le_of_lt cf_pos)],

    calc dist (g y) (g y')
           = 1/cf * (cf * dist (g y) (g y'))
           : by simp [ne_of_gt cf_pos]
       ... ≥ 1/cf * (dist y y' - cf * b2)
           : by simp [mul_le_mul_of_nonneg_left cf_times_claim
                                               cf_inv_nonneg]
       ... = 1/cf * dist y y' - 1/cf * cf * b2
           : by ring
       ... = 1/c2 * dist y y' - b2
           : by simp [ne_of_gt cf_pos],
  end,

  show is_QIE g,
       by exact QIE_from_different_constants g
                  c1 b1 c2 b2
                  c1_pos b1_pos c2_pos b2_pos
                  g_is_QIE_upper g_is_QIE_lower,
end

theorem QIE_with_quasidense_image_is_QI

     (f : X → Y)
     (f_is_QIE : is_QIE f)
     (f_qdense_im : has_quasidense_image f)
   : is_QI f
:=
begin
  -- We obtain a quasi-inverse from the quasi-density of the image
  -- and the axiom of choice:
  rcases f_qdense_im with ⟨c, c_pos, f_has_c_dense_im⟩,
  rcases classical.axiom_of_choice f_has_c_dense_im
         with ⟨g, fg_c_close_to_id⟩,
  dsimp at g,
  dsimp at fg_c_close_to_id,
  suffices : are_quasi_inverse f g,
  { exact ⟨f_is_QIE, g, quasiinverse_of_QIE_is_QIE f g f_is_QIE this, this⟩ },
    have fg_close_to_id : has_fin_dist (f ∘ g) id, by
    begin
      unfold has_fin_dist,
      unfold has_fin_dist',
      use c,
      split,
      show 0 < c,
           by exact c_pos,

      assume y : Y,
      calc dist ((f ∘ g) y) y
             = dist (f (g y)) y : by refl
         ... ≤ c                : fg_c_close_to_id y,
    end,

    -- Conversely, also g ∘ f has finite distance from id;
    have gf_close_to_id : has_fin_dist (g ∘ f) id, by
    begin
      unfold has_fin_dist,
      unfold has_fin_dist',
      -- we choose QIE-constants for f ...
      rcases f_is_QIE with ⟨cf, bf, cf_pos, bf_pos, f_is_cfbf_QIE⟩,
      -- ... and construct a suitably large constant c':
      let c' := cf * c + cf * bf,
      use c',
      split,
      show c' > 0,
           by {apply add_pos,
               apply mul_pos cf_pos,
               exact c_pos,
               apply mul_pos cf_pos bf_pos},

      assume x,
      show dist ((g ∘ f) x) x ≤ c', by
      begin
        let x_fx := g (f x),
        calc dist ((g ∘ f) x) x
               = dist x_fx x
               : by refl
           ... ≤ cf * dist (f x_fx) (f x) + cf * bf
               : QIE_lower_est f cf bf cf_pos f_is_cfbf_QIE x_fx x
           ... ≤ cf * c + cf * bf
               : by simp [fg_c_close_to_id (f x),
                         le_of_lt cf_pos, mul_le_mul_of_nonneg_left]
           ... ≤ c'
               : by refl,
      end,
    end,

    show are_quasi_inverse f g,
         by exact ⟨gf_close_to_id, fg_close_to_id⟩,
end
