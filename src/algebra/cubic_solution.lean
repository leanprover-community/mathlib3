import algebra.invertible
import tactic.linarith
import tactic.field_simp
import order.filter.at_top_bot

section fields
variables {F : Type*}

def cube_root_unity_a [field F] (root_three_i : F) : F :=
  (-1 + root_three_i)/2

def cube_root_unity_b [field F] (root_three_i : F) : F :=
  (-1 - root_three_i)/2

lemma multiply_out_cubed [field F] (x y : F) : (x + y) * (x + y) * (x + y) =
        (x * x * x) + (3 * x * x * y) + (3 * x * y * y) + (y * y * y) :=
begin
  ring,
end

/- If F isn't of characteristic 2, 2^3 ≠ 0 also.-/
lemma eight_ne_zero [field F] (two_ne_zero : (2 : F) ≠ (0 : F)) : (8 : F) ≠ (0 : F) :=
begin
  have cubed : (2 : F) * (2 : F) * (2 : F) = (8 : F),
    ring,
  rw <- cubed, clear cubed,
  exact mul_ne_zero (mul_ne_zero two_ne_zero two_ne_zero) two_ne_zero,
end

lemma twenty_seven_ne_zero [field F] (three_ne_zero : (3 : F) ≠ (0 : F)) :
  (27 : F) ≠ (0 : F) :=
begin
  have cubed : (3 : F) * (3 : F) * (3 : F) = (27 : F),
    ring,
  rw <- cubed, clear cubed,
  exact mul_ne_zero (mul_ne_zero three_ne_zero three_ne_zero) three_ne_zero,
end

@[simp] lemma cubrt_unity_a_correct [field F] (root_three_i : F)
    (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
    (cube_root_unity_a root_three_i) * (cube_root_unity_a root_three_i) * (cube_root_unity_a root_three_i)
     = 1 :=
begin
  unfold cube_root_unity_a,
  have simp_numerator : (-1 + root_three_i) * (-1 + root_three_i) * (-1 + root_three_i) = 8,
    rw multiply_out_cubed, rw rt3_i_correct,
    repeat {rw mul_neg_one}, repeat {rw neg_neg},
    rw mul_assoc (-3) root_three_i root_three_i, rw rt3_i_correct,
    ring,
  calc (-1 + root_three_i) / 2 * ((-1 + root_three_i) / 2) * ((-1 + root_three_i) / 2)
       = (-1 + root_three_i) * (-1 + root_three_i) / (2 * 2) * ((-1 + root_three_i) / 2)
          : by rw div_mul_div
   ... = ((-1 + root_three_i) * (-1 + root_three_i) * (-1 + root_three_i) / (2 * 2 * 2))
          : by rw div_mul_div
   ... = 8 / (2 * 2 * 2) : by rw simp_numerator
   ... = 8 / 8 : by ring_nf
   ... = 1 : by rw div_self (eight_ne_zero two_ne_zero),
end

@[simp] lemma cubrt_unity_b_correct [field F] (root_three_i : F)
    (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
    (cube_root_unity_b root_three_i) * (cube_root_unity_b root_three_i) * (cube_root_unity_b root_three_i)
     = 1 :=
begin
  have switch_roots : (cube_root_unity_b root_three_i) = (cube_root_unity_a (- root_three_i)),
    unfold cube_root_unity_b, unfold cube_root_unity_a, ring_nf,
  rw switch_roots, clear switch_roots,
  have neg_rt3_i_correct : (-root_three_i) * (-root_three_i) = (-3),
    rw neg_mul_neg, exact rt3_i_correct,
  exact cubrt_unity_a_correct (-root_three_i) neg_rt3_i_correct two_ne_zero,
end

@[simp] lemma cube_roots_unity_sum_zero [field F] (root_three_i : F)
    (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
    (cube_root_unity_a root_three_i) + (cube_root_unity_b root_three_i) = -1 :=
begin
  unfold cube_root_unity_a, unfold cube_root_unity_b,
  field_simp, ring,
end

@[simp] lemma cubrt_unity_a_ne_zero [field F] (root_three_i : F)
  (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
  (cube_root_unity_a root_three_i) ≠ 0 :=
begin
  have one_ne_zero : 1 ≠ (0 : F), simp,
  intros h, rw <- cubrt_unity_a_correct at one_ne_zero,
  rw h at one_ne_zero, simp at one_ne_zero, cc,
  repeat {assumption},
end

@[simp] lemma cubrt_unity_a_reciprocal [field F] (root_three_i : F)
    (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
    1/(cube_root_unity_a root_three_i) = (cube_root_unity_b root_three_i) :=
begin
  have root_ne_zero : (cube_root_unity_a root_three_i) ≠ 0,
    exact cubrt_unity_a_ne_zero root_three_i rt3_i_correct two_ne_zero,
  field_simp, unfold cube_root_unity_a, unfold cube_root_unity_b,
  field_simp, rw left_distrib, rw sub_eq_add_neg, repeat {rw right_distrib},
  rw neg_mul_comm root_three_i root_three_i,
  rw <- neg_mul_eq_mul_neg root_three_i root_three_i,
  rw rt3_i_correct, ring,
end

@[simp] lemma cubrt_unity_b_ne_zero [field F] (root_three_i : F)
  (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
  (cube_root_unity_b root_three_i) ≠ 0 :=
begin
  rw <- cubrt_unity_a_reciprocal root_three_i rt3_i_correct two_ne_zero, apply one_div_ne_zero,
  exact cubrt_unity_a_ne_zero root_three_i rt3_i_correct two_ne_zero,
end

@[simp] lemma cubrt_unity_b_reciprocal [field F] (root_three_i : F)
    (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
    1/(cube_root_unity_b root_three_i) = (cube_root_unity_a root_three_i) :=
begin
  have tmp : ∀(a b : F), 1 / a = 1 / b -> a = b,
    intros a b h, simp at h, exact h,
  apply tmp, rw one_div_one_div, symmetry,
  exact cubrt_unity_a_reciprocal root_three_i rt3_i_correct two_ne_zero,
end

@[simp] lemma cubrts_unity_mul_one [field F] (root_three_i : F)
    (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
    (cube_root_unity_a root_three_i) * (cube_root_unity_b root_three_i) = 1 :=
begin
  rw <- cubrt_unity_a_reciprocal root_three_i rt3_i_correct two_ne_zero,
  rw mul_div_cancel',
  exact cubrt_unity_a_ne_zero root_three_i rt3_i_correct two_ne_zero,
end

@[simp] lemma cubrt_unity_a_squ [field F] (root_three_i : F)
    (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
    (cube_root_unity_a root_three_i) * (cube_root_unity_a root_three_i) = (cube_root_unity_b root_three_i)
 :=
begin
  have h : (cube_root_unity_a root_three_i) *
              (cube_root_unity_a root_three_i) *
              (cube_root_unity_a root_three_i)
               / (cube_root_unity_a root_three_i) = 1 * (cube_root_unity_b root_three_i),
    rw cubrt_unity_a_correct root_three_i rt3_i_correct two_ne_zero,
    rw cubrt_unity_a_reciprocal root_three_i rt3_i_correct two_ne_zero,
    rw one_mul,
  rw mul_div_cancel at h, rw one_mul at h, exact h,
  exact cubrt_unity_a_ne_zero root_three_i rt3_i_correct two_ne_zero,
end

@[simp] lemma cubrt_unity_b_squ [field F] (root_three_i : F)
    (rt3_i_correct : root_three_i * root_three_i = (-3))
    (two_ne_zero : (2 : F) ≠ (0 : F)) :
    (cube_root_unity_b root_three_i) * (cube_root_unity_b root_three_i) = (cube_root_unity_a root_three_i)
 :=
begin
  have h : (cube_root_unity_a root_three_i) ≠ 0,
    exact cubrt_unity_a_ne_zero root_three_i rt3_i_correct two_ne_zero,
  rw [<- cubrt_unity_a_reciprocal] {occs := occurrences.pos [2]},
  field_simp, rw cubrt_unity_a_squ, repeat {assumption},
end

def depressed_cubic_solution_sqrt [field F] (c d : F) : F :=
  ((d * d) / (2 * 2)) + ((c * c * c)/27)

def depressed_cubic_solution_cube_root [field F] (d root  : F) : F :=
  -(d / 2) + root

def depressed_cubic_solution [field F] (c cubrt : F) : F :=
  cubrt + (-c / (3 * cubrt))

lemma add_three_thirds [field F] (x : F) (three_ne_zero : (3 : F) ≠ (0 : F)) :
  (x / 3) + (x / 3) + (x / 3) = x :=
begin
  repeat {rw div_add_div_same}, ring_nf, rw mul_comm, rw mul_div_cancel x three_ne_zero,
end

lemma rationalise_denominator [field F] (num den sqrt square : F) :
  (den - sqrt ≠ (0 : F)) ->
  (sqrt * sqrt = square) ->
  (num / (den + sqrt)) = (num * (den - sqrt)) / ((den * den) - square) :=
begin
  intros ne_zero h_sqrt, rw <- h_sqrt, clear h_sqrt,
  have two_squares : (den * den - sqrt * sqrt) = (den + sqrt) * (den - sqrt),
    ring,
  rw two_squares, clear two_squares,
  rw <- div_mul_div, rw div_self ne_zero, simp,
end

lemma tmp_nonzero [field F] (c d sqrt : F) (not_char_three : (3 : F) ≠ (0 : F)):
    (sqrt * sqrt = depressed_cubic_solution_sqrt c d) ->
    (c ≠ (0 : F)) ->
       (sqrt -(d / 2) ≠ (0 : F)) :=
begin
  intros h_sqrt c_ne_zero, intros h,
  rw sub_eq_zero at h, symmetry' at h,
  have h_squ : (-(d / 2)) * (-(d / 2)) = (sqrt * sqrt),
    rw h, clear h,
    rw neg_mul_neg,
  clear h,
  rw h_sqrt at h_squ, unfold depressed_cubic_solution_sqrt at h_squ,
  have tmp2 : -(d / 2) * -(d / 2) = (d * d) / (2 * 2),
    rw neg_mul_neg, rw div_mul_div,
  rw tmp2 at h_squ, clear tmp2, symmetry' at h_squ,
  have h_iszero : c * c * c / 27 = 0,
    rw add_right_eq_self at h_squ, exact h_squ,
  clear h_sqrt,
  have ne_zero : c * c * c ≠ (0 : F),
    exact mul_ne_zero (mul_ne_zero c_ne_zero c_ne_zero) c_ne_zero,
  exact div_ne_zero ne_zero (twenty_seven_ne_zero not_char_three) h_iszero,
end

/- The cubic formula involves dividing by multiples of three and of two,
     so we need additional arguments to assert that the relevant field
     is neither of characteristic 2 nor 3.-/
lemma depressed_cubic_solution_correct [field F] (c d x sqrt cubrt : F)
    (c_ne_zero : c ≠ (0 : F))
    (two_ne_zero : (2 : F) ≠ (0 : F)) (three_ne_zero : (3 : F) ≠ (0 : F)) :
  (sqrt * sqrt) = (depressed_cubic_solution_sqrt c d) ->
  (cubrt * cubrt * cubrt) = (depressed_cubic_solution_cube_root d sqrt) ->
  (x = (depressed_cubic_solution c cubrt) -> (x * x * x) + (c * x) + d = 0) :=
begin
  intros h_sqrt h_cubrt, unfold depressed_cubic_solution,
  have cubrt_ne_zero : cubrt ≠ (0 : F),
    intros h, unfold depressed_cubic_solution_cube_root at h_cubrt,
    symmetry' at h_cubrt, rw h at h_cubrt, rw mul_zero at h_cubrt,
    rw add_comm at h_cubrt, rw <- sub_eq_add_neg at h_cubrt,
    exact tmp_nonzero c d sqrt three_ne_zero h_sqrt c_ne_zero h_cubrt,
  intros h,
  rw h, clear h, repeat {rw right_distrib},
                 repeat {rw left_distrib}, repeat {rw right_distrib},
  rw h_cubrt,
  rw neg_div, repeat {rw <- neg_mul_eq_mul_neg}, repeat {rw <- neg_mul_eq_neg_mul},
  repeat {rw neg_neg}, repeat {rw div_mul_div},
  repeat {rw mul_assoc}, repeat {rw mul_comm (3 : F) (_ * _)},
  rw mul_comm (3 : F) cubrt, repeat {rw <- mul_assoc},
  rw h_cubrt, clear h_cubrt,

  /- We need to do some boring rearranging to eliminate the fractional powers
      of the cube root.-/
  rw div_mul_eq_mul_div_comm cubrt c (cubrt * 3),
  have cancel_cubrt : (c / (cubrt * 3)) * cubrt = c / 3,
    rw mul_comm _ cubrt, rw mul_div_comm,
    rw div_mul_right (3 : F) cubrt_ne_zero,
    rw <- div_eq_mul_one_div,
  rw mul_assoc _ cubrt (c / (cubrt * 3)),
  rw mul_assoc _ (c / (cubrt * 3)) cubrt,
  repeat {rw mul_comm cubrt (c / (cubrt * 3))},
  repeat {rw cancel_cubrt}, clear cancel_cubrt,
  rw div_mul_right (3 : F) cubrt_ne_zero,
  rw mul_div_comm c 1 3, rw one_mul,
  rw mul_comm (c / 3) cubrt,
  repeat {rw add_assoc}, rw add_comm (c / 3 * (c / (cubrt * 3))) _,
  rw <- add_assoc (-(cubrt * (c / 3))) (-(cubrt * (c / 3))) _,
  rw <- neg_add, rw add_assoc, rw <- add_assoc (-_) (-(cubrt * (c / 3))) _,
  rw <- neg_add,
  rw <- mul_div_assoc, rw add_three_thirds (cubrt * c) three_ne_zero,
  repeat {rw <- add_assoc _ (c * cubrt) _, rw add_comm _ (c * cubrt),
          rw add_assoc (c * cubrt) _ _},
  rw mul_comm cubrt c,
  rw add_assoc (c * cubrt) _ _, rw <- add_assoc (-(c * cubrt)) (c * cubrt),
  rw <- sub_eq_neg_add (c * cubrt) (c * cubrt), rw sub_self, rw zero_add,

  repeat {rw mul_assoc cubrt _ _}, rw mul_comm ((c * c)/_) cubrt,
  rw mul_div_comm cubrt (c * c), rw div_mul_right _ cubrt_ne_zero,
  rw add_comm (-(c * c * c / _)) _,
  rw add_comm _ (c / 3 * (c / (cubrt * 3))),

  have tmp_1 : (c * c * (1 / (cubrt * (3 * 3)))) = ((c * (c / (cubrt * 3))) / 3),
    field_simp, ring,
  rw tmp_1, clear tmp_1,
  have tmp_2 : (c / 3 * (c / (cubrt * 3))) = ((c * (c / (cubrt * 3))) / 3),
    field_simp, ring,
  rw tmp_2, clear tmp_2,
  repeat {rw add_assoc},
  rw <- add_assoc (c * (c / (cubrt * 3)) / 3) (c * (c / (cubrt * 3)) / 3) _,
  rw <- add_assoc (c * (c / (cubrt * 3)) / 3 + c * (c / (cubrt * 3)) / 3) (c * (c / (cubrt * 3)) / 3) _,
  rw add_three_thirds _ three_ne_zero,
  rw <- add_assoc (c * _) (-_) _, rw add_comm (c * _) (-_),
  rw <- sub_eq_neg_add, rw sub_self, rw zero_add,

  unfold depressed_cubic_solution_cube_root,
  have tmp : (c * c * c / ((-(d / 2) + sqrt) * 3 * 3 * 3)) =
             (c * c * c) / (-(d / 2) + sqrt) * 1 / (3 * 3 * 3),
    field_simp, ring_nf, rw <- mul_assoc, rw <- mul_assoc,
  rw tmp, clear tmp,
  have neg_sqrt : -sqrt * -sqrt = depressed_cubic_solution_sqrt c d,
    rw neg_mul_neg, exact h_sqrt,
  have nonzero : -(d / 2) - sqrt ≠ 0,
    rw sub_eq_add_neg, rw add_comm, rw <- sub_eq_add_neg,
    exact tmp_nonzero c d (-sqrt) three_ne_zero neg_sqrt c_ne_zero,
  rw rationalise_denominator (c * c * c) (-(d/2)) sqrt (depressed_cubic_solution_sqrt c d)
	    nonzero h_sqrt,
  unfold depressed_cubic_solution_sqrt,
  rw neg_mul_neg, rw div_mul_div, rw sub_add_eq_sub_sub,
  rw sub_self,
  field_simp, ring,
end

def depressed_cubic_x [field F] (a b x : F) : F :=
    x + (b / (3 * a))

def depressed_cubic_x_term [field F] (a b c : F) : F :=
    (3 * a * c - (b * b)) / (3 * a * a)

def depressed_cubic_constant [field F] (a b c d : F) : F :=
    (((2 * b * b * b) - (9 * a * b * c)) / (27 * a * a * a)) + (d / a)

lemma convert_cubic_to_depressed [field F] (a b c d x : F)
    (a_ne_zero : a ≠ 0) (three_ne_zero : (3 : F) ≠ (0 : F)) :
  (a * x * x * x) + (b * x * x) + (c * x) + d =
  a * (((depressed_cubic_x a b x) * (depressed_cubic_x a b x) * (depressed_cubic_x a b x))
  + (depressed_cubic_x_term a b c) * (depressed_cubic_x a b x)
  + (depressed_cubic_constant a b c d)) :=
begin
  unfold depressed_cubic_constant, unfold depressed_cubic_x_term,
  unfold depressed_cubic_x,
  have tmp : ∀ (a b : F), (a - b = 0) -> (a = b),
    intros a b h, have h1 : (a - b + b) = (0 + b), rw h, simp at h1, exact h1,
  apply tmp, field_simp, clear tmp,
  rw mul_div_assoc, rw div_mul_left a_ne_zero,
  have tmp : 3 * a * (3 * a) * (3 * a) = (27 * a * a) * a,
    ring,
  rw tmp, clear tmp, repeat {rw mul_assoc (27 * a * a)},
  have den_ne_zero : (27 * a * a) ≠ 0,
    repeat {apply mul_ne_zero}, exact twenty_seven_ne_zero three_ne_zero, repeat {assumption},
  field_simp, ring,
end

def cubic_formula [field F] (a b c cubrt : F) : F :=
  depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt - (b / (3 * a))

def cubic_formula_cubrt [field F] (a b c d sqrt : F) : F :=
  depressed_cubic_solution_cube_root (depressed_cubic_constant a b c d) sqrt

def cubic_formula_sqrt [field F] (a b c d : F) : F :=
  depressed_cubic_solution_sqrt (depressed_cubic_x_term a b c) (depressed_cubic_constant a b c d)

lemma cubic_solution [field F] (a b c d x sqrt cubrt : F)
  (a_ne_zero : a ≠ 0) (two_ne_zero : (2 : F) ≠ 0) (three_ne_zero : (3 : F) ≠ 0)
  (int_quantity_ne_zero : (depressed_cubic_x_term a b c ≠ 0)):

  (sqrt * sqrt = (cubic_formula_sqrt a b c d)) ->
  (cubrt * cubrt * cubrt = (cubic_formula_cubrt a b c d sqrt)) ->
  (x = (cubic_formula a b c cubrt)) ->
  (a * x * x * x) + (b * x * x) + (c * x) + d = 0 :=
begin
  intros h_sqrt h_cubrt h_x,
  unfold cubic_formula at h_x,
  rw convert_cubic_to_depressed a b c d x a_ne_zero three_ne_zero,
  have h : depressed_cubic_x a b x = depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt,
    unfold depressed_cubic_x, rw h_x, ring,
  rw h,
  have triv : depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt =
              depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt,
    refl,
  unfold cubic_formula_sqrt at h_sqrt,
  unfold cubic_formula_cubrt at h_cubrt,
  have eq_zero : (depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt * depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt * depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt + depressed_cubic_x_term a b c * depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt + depressed_cubic_constant a b c d)
                  = 0,
    exact depressed_cubic_solution_correct (depressed_cubic_x_term a b c) (depressed_cubic_constant a b c d) (depressed_cubic_solution (depressed_cubic_x_term a b c) cubrt) sqrt cubrt int_quantity_ne_zero two_ne_zero three_ne_zero h_sqrt h_cubrt triv,
  rw eq_zero, ring,
end

lemma multiply_out_cubic [field F] (x a b c : F) :
  (x + a) * (x + b) * (x + c) =
  x * x * x + (a + b + c) * x * x + (a * b + a * c + b * c) * x + (a * b * c) :=
begin
  ring,
end

lemma depressed_cubic_solution_unique [field F] (c d x sqrt cubrt rt3_i : F)
      (two_ne_zero : (2 : F) ≠ (0 : F)) (three_ne_zero : (3 : F) ≠ (0 : F))
      (c_ne_zero : c ≠ (0 : F)) :
  (sqrt * sqrt) = (depressed_cubic_solution_sqrt c d) ->
  (cubrt * cubrt * cubrt) = (depressed_cubic_solution_cube_root d sqrt) ->
  (rt3_i * rt3_i = (-3)) ->
  (x ≠ (depressed_cubic_solution c cubrt)) ->
   (x ≠ (depressed_cubic_solution c (cubrt * (cube_root_unity_a rt3_i)))) ->
   (x ≠ (depressed_cubic_solution c (cubrt * (cube_root_unity_b rt3_i)))) ->
  ((x * x * x) + (c * x) + d ≠ 0) :=
begin
  intros h_sqrt h_cubrt h_rt3i,
  have cubrt_ne_zero : cubrt ≠ 0,
    intros cubrt_zero, rw cubrt_zero at h_cubrt, rw mul_zero at h_cubrt,
    symmetry' at h_cubrt, unfold depressed_cubic_solution_cube_root at h_cubrt,
    rw add_comm at h_cubrt, rw <- sub_eq_add_neg at h_cubrt,
    exact tmp_nonzero c d sqrt three_ne_zero h_sqrt c_ne_zero h_cubrt,
  have h : (x - depressed_cubic_solution c cubrt) *
           (x - depressed_cubic_solution c (cubrt * cube_root_unity_a rt3_i)) *
           (x - depressed_cubic_solution c (cubrt * cube_root_unity_b rt3_i))
           =
           x * x * x + c * x + d,
    repeat {rw sub_eq_add_neg}, rw multiply_out_cubic,
    have x_squ : (-depressed_cubic_solution c cubrt + -depressed_cubic_solution c (cubrt * cube_root_unity_a rt3_i) + -depressed_cubic_solution c (cubrt * cube_root_unity_b rt3_i))
                  = 0,
      unfold depressed_cubic_solution, field_simp,
      repeat {rw <- mul_assoc}, rw div_mul_eq_div_mul_one_div _ _ (cube_root_unity_a _),
      rw cubrt_unity_a_reciprocal,
      rw div_mul_eq_div_mul_one_div _ _ (cube_root_unity_b _),
      rw cubrt_unity_b_reciprocal,
      field_simp,
      unfold cube_root_unity_a, unfold cube_root_unity_b, field_simp, ring,
      repeat {assumption},
    repeat {rw <- add_assoc}, repeat {rw mul_comm _ cubrt}, rw x_squ, clear x_squ,
    repeat {rw zero_mul}, rw add_zero,
    have x_term : (-depressed_cubic_solution c cubrt *
                        -depressed_cubic_solution c (cubrt * cube_root_unity_a rt3_i) +
                   -depressed_cubic_solution c cubrt *
                        -depressed_cubic_solution c (cubrt * cube_root_unity_b rt3_i) +
                    -depressed_cubic_solution c (cubrt * cube_root_unity_a rt3_i) *
                        -depressed_cubic_solution c (cubrt * cube_root_unity_b rt3_i))
                  = c,
      unfold depressed_cubic_solution, field_simp,
      repeat {rw <- mul_assoc}, rw div_mul_eq_div_mul_one_div _ _ (cube_root_unity_a _),
      rw cubrt_unity_a_reciprocal,
      rw div_mul_eq_div_mul_one_div _ _ (cube_root_unity_b _),
      rw cubrt_unity_b_reciprocal,
      field_simp,
      repeat {rw mul_comm _ (cube_root_unity_a _)}, repeat {rw mul_comm _ (cube_root_unity_b _)},
      simp only [left_distrib, right_distrib, <- neg_mul_eq_mul_neg, <- neg_mul_eq_neg_mul],
      rw mul_comm (cube_root_unity_b rt3_i) c, rw mul_assoc c (cube_root_unity_b _) _,
      rw <- mul_assoc (cube_root_unity_b _) (cube_root_unity_a _) _,
      rw mul_comm (cube_root_unity_b _) (cube_root_unity_a _), rw cubrts_unity_mul_one,
      rw mul_assoc (cube_root_unity_a rt3_i), rw mul_comm (cube_root_unity_a rt3_i),
      rw mul_assoc (cube_root_unity_b rt3_i), repeat {rw mul_assoc _ (cube_root_unity_a _)},
      rw <- mul_assoc (cube_root_unity_a _) (cube_root_unity_b _) _,
      rw cubrts_unity_mul_one,
      rw <- mul_assoc (cube_root_unity_a _) (cube_root_unity_a _) _,
      rw cubrt_unity_a_squ,
      repeat {rw mul_assoc _ (cube_root_unity_b _) _},
      rw <- mul_assoc (cube_root_unity_b _) (cube_root_unity_b _) _,
      rw cubrt_unity_b_squ,
      unfold cube_root_unity_a, unfold cube_root_unity_b, field_simp, ring,
      repeat {assumption},
    repeat {rw mul_comm _ cubrt}, rw x_term, clear x_term,
    have constant_term : (-depressed_cubic_solution c cubrt * -depressed_cubic_solution c (cubrt * cube_root_unity_a rt3_i) * -depressed_cubic_solution c (cubrt * cube_root_unity_b rt3_i))
                          = d,
      have four_ne_zero : (4 : F) ≠ 0,
        have tmp : (4 : F) = 2 * 2, ring, rw tmp,
        exact mul_ne_zero two_ne_zero two_ne_zero,
      have twenty_seven_ne_zero : (27 : F) ≠ 0,
        have tmp : (27 : F) = 3 * (3 * 3), ring, rw tmp,
        exact mul_ne_zero three_ne_zero (mul_ne_zero three_ne_zero three_ne_zero),
      unfold depressed_cubic_solution,
      repeat {rw div_mul_eq_div_mul_one_div},
      repeat {rw cubrt_unity_a_reciprocal}, repeat {rw cubrt_unity_b_reciprocal},
      field_simp,
      have unfold : (c + -(cubrt * (3 * cubrt))) * (c * cube_root_unity_b rt3_i + -(cubrt * cube_root_unity_a rt3_i * (3 * cubrt))) * (c * cube_root_unity_a rt3_i + -(cubrt * cube_root_unity_b rt3_i * (3 * cubrt)))
              =
              c ^ 3 * ((cube_root_unity_a rt3_i) * (cube_root_unity_b rt3_i)) -
              3 * (c * cubrt) ^ 2 * (((cube_root_unity_a rt3_i) * (cube_root_unity_b rt3_i)) + ((cube_root_unity_a rt3_i) * (cube_root_unity_a rt3_i)) + ((cube_root_unity_b rt3_i) * (cube_root_unity_b rt3_i))) +
              9 * c * cubrt ^ 4 * (((cube_root_unity_a rt3_i) * (cube_root_unity_b rt3_i)) + ((cube_root_unity_a rt3_i) * (cube_root_unity_a rt3_i)) + ((cube_root_unity_b rt3_i) * (cube_root_unity_b rt3_i))) -
              27 * (cubrt ^ 6) * ((cube_root_unity_a rt3_i) * (cube_root_unity_b rt3_i)),
        ring,
      rw unfold, clear unfold,
      rw cubrts_unity_mul_one, rw cubrt_unity_a_squ, rw cubrt_unity_b_squ,
      rw add_assoc _ (cube_root_unity_b rt3_i) (cube_root_unity_a rt3_i),
      rw add_comm (cube_root_unity_b rt3_i) (cube_root_unity_a rt3_i),
      rw cube_roots_unity_sum_zero, rw add_right_neg, repeat {rw mul_zero},
      rw mul_one, rw sub_zero, rw add_zero, rw mul_one,
      have tmp : (cubrt ^ 6) = (cubrt * cubrt * cubrt) * (cubrt * cubrt * cubrt),
        ring, rw tmp, clear tmp,
      have tmp : (3 * cubrt * (3 * cubrt) * (3 * cubrt)) = 27 * (cubrt * cubrt * cubrt),
        ring, rw tmp, clear tmp,
      rw h_cubrt, unfold depressed_cubic_solution_cube_root,
      have unfold : ((-(d / 2) + sqrt) * (-(d / 2) + sqrt)) =
                      d * d / 4 - d * sqrt + sqrt * sqrt,
        field_simp, ring,
      rw unfold, clear unfold, rw h_sqrt, unfold depressed_cubic_solution_sqrt,
      field_simp, ring,
      repeat {assumption},
    rw constant_term,
  intros h_s1 h_s2 h_s3, rw <- sub_ne_zero at h_s1, rw <- sub_ne_zero at h_s2, rw <- sub_ne_zero at h_s3,
  rw <- h, clear h,
  apply mul_ne_zero, apply mul_ne_zero, repeat {assumption},
end

lemma cubic_solution_unique [field F] (a b c d x sqrt cubrt rt3_i : F)
      (a_ne_zero : a ≠ (0 : F))
      (one_ne_zero : (1 : F) ≠ (0 : F)) (two_ne_zero : (2 : F) ≠ (0 : F)) (three_ne_zero : (3 : F) ≠ (0 : F))
      (int_quantity_ne_zero : (depressed_cubic_x_term a b c ≠ 0)) :
  (sqrt * sqrt = (cubic_formula_sqrt a b c d)) ->
  (cubrt * cubrt * cubrt = (cubic_formula_cubrt a b c d sqrt)) ->
  (rt3_i * rt3_i = (-3)) ->
  (x ≠ (cubic_formula a b c cubrt)) ->
   (x ≠ (cubic_formula a b c (cubrt * (cube_root_unity_a rt3_i)))) ->
   (x ≠ (cubic_formula a b c (cubrt * (cube_root_unity_b rt3_i)))) ->
  ((a * x * x * x) + (b * x * x) + (c * x) + d ≠ 0) :=
begin
  have twenty_seven_ne_zero : (27 : F) ≠ 0,
    have tmp : (27 : F) = 3 * (3 * 3), ring, rw tmp, clear tmp,
    exact mul_ne_zero three_ne_zero (mul_ne_zero three_ne_zero three_ne_zero),

  unfold cubic_formula, intros h_sqrt h_cubrt h_rt3i h_solution1 h_solution2 h_solution3,
  /- Divide through by the a (which we know isn't zero)... -/
  have tmp : (1 * x * x * x) + (b / a * x * x) + (c / a * x) + (d / a) ≠ 0 ->
             (a * x * x * x) + (b * x * x)     + (c * x)     + d       ≠ 0,
    intros h_tmp, field_simp at h_tmp, field_simp,
    have tmp_tmp : a * x * x * x = x * x * x * a, ring,
    rw tmp_tmp, exact h_tmp,
  apply tmp, clear tmp,
  rw convert_cubic_to_depressed, rw one_mul,

  have x_term_simplify : (depressed_cubic_x_term a b c) = (depressed_cubic_x_term 1 (b / a) (c / a)),
    unfold depressed_cubic_x_term, field_simp, ring,
  rw <- x_term_simplify, clear x_term_simplify,
  have minor : b / a / (3 * 1) = b / (3 * a), field_simp, left, rw mul_comm,
  apply depressed_cubic_solution_unique
        (depressed_cubic_x_term a b c)
        (depressed_cubic_constant 1 (b / a) (c / a) (d / a))
        (depressed_cubic_x 1 (b / a) x) sqrt cubrt rt3_i,
  repeat {assumption},

  rw h_sqrt, unfold cubic_formula_sqrt, unfold depressed_cubic_x_term,
             unfold depressed_cubic_constant, unfold depressed_cubic_solution_sqrt,
  field_simp, ring,

  rw h_cubrt, unfold cubic_formula_cubrt,
              unfold depressed_cubic_constant, unfold depressed_cubic_solution_cube_root,
  field_simp, ring,

  all_goals {unfold depressed_cubic_x, rw minor},
  all_goals {have tmp : ∀ (rt : F),
                	x ≠ depressed_cubic_solution (depressed_cubic_x_term a b c) rt - b / (3 * a) ->
                	x + b / (3 * a) ≠ depressed_cubic_solution (depressed_cubic_x_term a b c) rt,
    intros rt h1 h2, rw <- h2 at h1, simp at h1, cc},
  exact tmp _ h_solution1,
  exact tmp _ h_solution2,
  exact tmp _ h_solution3,
end

end fields
