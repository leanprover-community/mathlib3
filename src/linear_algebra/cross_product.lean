import data.matrix.basic    -- also imports `algebra.module.linear_map`
import data.matrix.notation -- also imports `data.fin.vec_notation`
import linear_algebra.basic

-- TODO should it be inside a namespace?

variables {R : Type*} [comm_ring R] -- [has_mul R] [add_comm_group R]


/-- cross product of two 3D vectors -/
def cross_product (a b : fin 3 → R) : (fin 3 → R) :=
  ![ (a 1)*(b 2) - (a 2)*(b 1) , (a 2)*(b 0) - (a 0)*(b 2) , (a 0)*(b 1) - (a 1)*(b 0) ]

local infix `×₃`: 68 := cross_product
local infix `⬝` : 67 := matrix.dot_product


section smalltest
  -- TODO remove before pull request
  def c : (fin 3 → ℤ) := ![1, 2, 3]
  def d : (fin 3 → ℤ) := ![4, 5, 6]
  #eval c ⬝ d
  #eval d ⬝ c
  #eval c ×₃ d
  #eval d ×₃ c
  #eval c ⬝ c
  #eval d ⬝ d
  #eval c ×₃ c
  #eval d ×₃ d
  #eval c ⬝ c ×₃ d
  #eval d ⬝ c ×₃ d
  #eval c ×₃ d ⬝ c
  #eval c ×₃ d ⬝ d
end smalltest


private lemma wtf : ∀ x : ℕ, x < 3 → x ≠ 0 → x ≠ 1 → x ≠ 2 → false :=
begin
  dec_trivial,
end

private lemma omfg (y : fin 3) (n₀ : y ≠ 0) (n₁ : y ≠ 1) (n₂ : y ≠ 2) : false :=
begin
  cases y,
  apply wtf y_val; finish,
end

private meta def finish_cross_prod : tactic unit :=
`[ rw cross_product, rw cross_product, finish ]

/-- cross product is anti-commutative -/
lemma cross_product_anticomm (v w : fin 3 → R) :
  v ×₃ w = - (w ×₃ v) :=
begin
  ext i,
  by_cases h₀ : i = 0,
  { rw h₀ at *,
    finish_cross_prod },
  by_cases h₁ : i = 1,
  { rw h₁ at *,
    finish_cross_prod },
  by_cases h₂ : i = 2,
  { rw h₂ at *,
    finish_cross_prod },
  -- TODO is there a better way how to do the decomposition into cases above?
  exfalso,
  exact omfg i h₀ h₁ h₂,
  -- TODO can the lemmata `wtf` and `omfg` be removed?
end

/-- vector sum of cross product with flipped cross product yields the zero vector -/
lemma cross_product_anticomm' (v w : fin 3 → R) :
  v ×₃ w + w ×₃ v = 0 :=
begin
  rw add_eq_zero_iff_eq_neg,
  apply cross_product_anticomm,
end

/-- cross product of a vector with itself yields the zero vector -/
lemma cross_product_self_eq_zero_vector (v : fin 3 → R) :
  v ×₃ v = 0 :=
begin
  unfold cross_product,
  simp,
  split; ring_nf; tauto,
end


private lemma dot_product_unfold (a b c d e f : R) :
  matrix.dot_product ![a, b, c] ![d, e, f] = a*d + b*e + c*f :=
begin
  simp [add_assoc],
end

/-- cross product of two vectors is perpendicular to the first vector -/
lemma cross_product_perpendicular_first_arg (v w : fin 3 → R) :
  v ⬝ (v ×₃ w) = 0 :=
begin
  unfold cross_product,
  calc v ⬝ ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0]
       = (v 0) * (v 1 * w 2 - v 2 * w 1)
       + (v 1) * (v 2 * w 0 - v 0 * w 2)
       + (v 2) * (v 0 * w 1 - v 1 * w 0)
           : by apply dot_product_unfold
  ...  = 0 : by ring,
end

/-- cross product of two vectors is perpendicular to the second vector -/
lemma cross_product_perpendicular_second_arg (v w : fin 3 → R) :
  w ⬝ (v ×₃ w) = 0 :=
begin
  rw cross_product_anticomm,
  rw matrix.dot_product_neg,
  rw cross_product_perpendicular_first_arg,
  exact neg_zero,
end


/-- TODO -/
lemma triple_product_equality (u v w : fin 3 → R) :
  u ⬝ (v ×₃ w) = v ⬝ (w ×₃ u) :=
begin
  unfold cross_product,
  -- TODO how can I unpack `u` into `![u 1, u 2, u 3]` in order to call `dot_product_unfold` then?
  sorry,
end


#check (fin 3 → R) →ₗ[R] (fin 3 → R) →ₗ[R] (fin 3 → R) -- TODO prove multilinearity
