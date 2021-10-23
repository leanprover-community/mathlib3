import algebra.invertible
import tactic.linarith
import order.filter.at_top_bot
import algebra.cubic_solution

section field
variables {F : Type*}

def quartic_expression [field F] (x a b c d e : F) : F :=
  ((x * x * x * x * a) + (x * x * x * b) + (x * x * c) + (x * d) + e)

def depressed_quartic_squ_coefficient [field F] (b c : F) : F :=
  (c - (3 * b * b)/8)

def depressed_quartic_linear_coefficient [field F] (b c d : F) : F :=
  (b * b * b) / 8 - (b * c) / 2 + d

def depressed_quartic_constant [field F] (b c d e : F) : F :=
  -(3 * b * b * b * b) / 256 + (c * b * b) / 16 - (b * d) / 4 + e

lemma convert_quartic_to_depressed [field F] (b c d e x : F) (two_ne_zero : (2 : F) ≠ 0) :
  (quartic_expression x 1 b c d e) =
  (quartic_expression (x + (b / 4)) 1 0
                      (depressed_quartic_squ_coefficient b c)
                      (depressed_quartic_linear_coefficient b c d)
                      (depressed_quartic_constant b c d e)) :=
begin
  unfold quartic_expression, unfold depressed_quartic_squ_coefficient,
  unfold depressed_quartic_linear_coefficient, unfold depressed_quartic_constant,
  have h256 : (256 : F) = (16 : F) * (16 : F), ring, rw h256, clear h256,
  have h16 : (16 : F) = (4 : F) * (4 : F), ring, rw h16, clear h16,
  have h8 : (8 : F) = (4 : F) * (2 : F), ring, rw h8, clear h8,
  have h4 : (4 : F) = (2 : F) * (2 : F), ring, rw h4, clear h4,
  field_simp, ring,
end

lemma factorise_depressed_quartic_simultaneous [field F] (c d e x p q s : F)
  (two_ne_zero : (2 : F) ≠ 0) (p_ne_zero : p ≠ 0) :
  (c + p * p = s + q) ->
  (d / p = s - q) ->
  (e = s * q) ->
  (quartic_expression x 1 0 c d e) = (x * x + p * x + q) * (x * x - p * x + s) :=
begin
  intros h1 h2 h3, unfold quartic_expression,
  have mul_quad : (x * x + p * x + q) * (x * x - p * x + s) =
                  (x * x * x * x) + (s + q - p * p) * x * x + (p * s - p * q) * x + s * q,
    ring,
  rw mul_quad, clear mul_quad,
  rw <- h1, rw <- h3, rw sub_eq_add_neg (p * s) (p * q),
  rw neg_mul_eq_mul_neg, rw <- left_distrib, rw <- sub_eq_add_neg,
  rw <- h2,
  field_simp, ring,
end

lemma depressed_quartic_simultaneous_solution [field F] (c d e p q s cubrt sqrt : F)
    (one_ne_zero : (1 : F) ≠ 0) (two_ne_zero : (2 : F) ≠ 0) (three_ne_zero : (3 : F) ≠ 0)
    (p_ne_zero : p ≠ 0) (int_quantity_ne_zero : depressed_cubic_x_term 1 (2 * c) (c * c - 4 * e) ≠ 0) :
    (sqrt * sqrt = (cubic_formula_sqrt 1 (2 * c) (c * c - 4 * e) (- d * d))) ->
    (cubrt * cubrt * cubrt = (cubic_formula_cubrt 1 (2 * c) (c * c - 4 * e) (- d * d)) sqrt) ->
    (p * p) = (cubic_formula 1 (2 * c) (c * c - 4 * e) cubrt) ->
    (s = (c + (p * p) + (d / p)) / 2) ->
    (q = (c + (p * p) - (d / p)) / 2) ->
    ((c + p * p = s + q) /\ (d / p = s - q) /\ (e = s * q)) :=
begin
  intros h_sqrt h_cubrt h_p h_s h_q, split,
  rw h_s, rw h_q, field_simp, ring, split,
  rw h_s, rw h_q, field_simp, ring,

  rw h_s, rw h_q, field_simp,
  have h_cubic : 1 * (p * p) * (p * p) * (p * p) + ((2 * c) * (p * p) * (p * p)) + (c * c - 4 * e) * (p * p) + (-d * d) = 0,
    apply cubic_solution, repeat {assumption},
  rw <- neg_inj, rw <- add_eq_zero_iff_neg_eq,
  simp only [sub_eq_add_neg, left_distrib, right_distrib,
                <- neg_mul_eq_mul_neg, <- neg_mul_eq_neg_mul],
  simp only [sub_eq_add_neg, left_distrib, right_distrib,
                <- neg_mul_eq_mul_neg, <- neg_mul_eq_neg_mul] at h_cubic,
  ring_nf, ring_nf at h_cubic, rw <- neg_inj, rw neg_zero, rw <- h_cubic, ring,
end

lemma depressed_quartic_to_quadratic_product [field F] (x c d e sqrt_p sqrt_cubic cubrt: F)
    (one_ne_zero : (1 : F) ≠ 0) (two_ne_zero : (2 : F) ≠ 0) (three_ne_zero : (3 : F) ≠ 0)
    (sqrt_p_ne_zero : sqrt_p ≠ 0) (int_quantity_ne_zero : depressed_cubic_x_term 1 (2 * c) (c * c - 4 * e) ≠ 0)
    :
    (sqrt_cubic * sqrt_cubic = (cubic_formula_sqrt 1 (2 * c) (c * c - 4 * e) (- d * d))) ->
    (cubrt * cubrt * cubrt = (cubic_formula_cubrt 1 (2 * c) (c * c - 4 * e) (- d * d)) sqrt_cubic) ->
    (sqrt_p * sqrt_p = (cubic_formula 1 (2 * c) (c * c - 4 * e) cubrt)) ->
  (quartic_expression x 1 0 c d e) =
        (x * x + sqrt_p * x + ((c + (sqrt_p * sqrt_p) - (d / sqrt_p)) / 2)) *
        (x * x - sqrt_p * x + ((c + (sqrt_p * sqrt_p) + (d / sqrt_p)) / 2)) :=
begin
  intros h_sqrt_cubic, intros h_cubrt, intros h_sqrt_p,
  apply factorise_depressed_quartic_simultaneous, repeat {assumption},
  field_simp, ring,
  field_simp, ring,
  rw <- neg_inj, rw <- add_eq_zero_iff_neg_eq, field_simp,
  rw [mul_comm sqrt_p 2] {occs := occurrences.pos [1]}, rw mul_assoc 2 sqrt_p _,
  rw <- mul_assoc sqrt_p sqrt_p _,
  simp only [left_distrib, right_distrib, <- neg_mul_eq_mul_neg, <- neg_mul_eq_neg_mul, sub_eq_add_neg],
  repeat {rw mul_assoc}, rw mul_comm c sqrt_p,
  repeat {rw <- mul_assoc sqrt_p sqrt_p _, rw h_sqrt_p},
  set p := cubic_formula 1 (2 * c) (c * c - 4 * e) cubrt with hp,
  rw add_comm _ (d * (sqrt_p * p)),
  have swap : ∀ (x1 x2 x3 : F), x1 * (x2 * x3) = x3 * (x2 * x1), intros, ring,
  rw swap d sqrt_p p, rw swap d sqrt_p c, clear swap, repeat {rw add_assoc},
  rw <- add_assoc (-(p * (sqrt_p * d))) (p * (sqrt_p * d)),
  have tmp : -(p * (sqrt_p * d)) + p * (sqrt_p * d) = 0, ring, rw tmp, clear tmp,
  rw zero_add,
  rw add_comm (c * (sqrt_p * d)) _, repeat {rw add_assoc}, rw add_comm (-(c * (sqrt_p * d))) _,
  repeat {rw add_assoc},
  have tmp : (c * (sqrt_p * d)) + -(c * (sqrt_p * d)) = 0, ring, rw tmp, clear tmp,
  rw add_zero,
  rw <- neg_inj, rw neg_zero,
  have finale : -(e * (2 * (p * 2)) + -(c * (p * c) + (c * (p * p) + (p * (p * c) + (p * (p * p) + -(d * d))))))
                = (1 * p * p * p) + (2 * c * p * p) + ((c * c - 4 * e) * p) + (-d * d),
    ring,
  rw finale, apply cubic_solution, repeat {assumption},
end

/- In a submission to the standard library, I'd use the work in the existing
    quadratic_discriminant.lean.  However, I need some things that aren't
    already in there, and I don't want to mix my work with the existing
    work in the same file, as that would leave it ambiguous what I'd done
    when it comes to mark the project.  Hence, I move all the work that
    I need out to here.-/
def quadratic_formula [field F] (b sqrt : F) : F := (sqrt - b) / 2
def quadratic_discriminant [field F] (b c : F) : F := (b * b) - (4 * c)

lemma quadratic_formula_correct [field F] (b c sqrt x : F) (two_ne_zero : (2 : F) ≠ 0)
              (h_sqrt : sqrt * sqrt = quadratic_discriminant b c) :
              (x = quadratic_formula b sqrt) -> ((x * x) + (b * x) + c = 0) :=
begin
  have tmp : sqrt * sqrt = sqrt ^ 2, ring, rw tmp at h_sqrt, clear tmp,
  unfold quadratic_formula, intros hx, rw hx, field_simp, ring_nf,
  rw h_sqrt, unfold quadratic_discriminant, ring,
end

lemma quadratic_formula_factorise [field F] (b c sqrt x : F) (two_ne_zero : (2 : F) ≠ 0)
              (h_sqrt : sqrt * sqrt = quadratic_discriminant b c) :
              ((x * x) + (b * x) + c) =
              (x - (quadratic_formula b sqrt)) * (x - (quadratic_formula b (- sqrt))) :=
begin
  have tmp : sqrt * sqrt = sqrt ^ 2, ring, rw tmp at h_sqrt, clear tmp,
  unfold quadratic_formula, field_simp, ring_nf, rw h_sqrt, unfold quadratic_discriminant,
  ring,
end


lemma depressed_quartic_solution [field F] (x c d e sqrt_p sqrt_cubic sqrt_quadratic cubrt: F)
    (one_ne_zero : (1 : F) ≠ 0) (two_ne_zero : (2 : F) ≠ 0) (three_ne_zero : (3 : F) ≠ 0)
    (sqrt_p_ne_zero : sqrt_p ≠ 0) (int_quantity_ne_zero : depressed_cubic_x_term 1 (2 * c) (c * c - 4 * e) ≠ 0) :
    (sqrt_cubic * sqrt_cubic = (cubic_formula_sqrt 1 (2 * c) (c * c - 4 * e) (- d * d))) ->
    (cubrt * cubrt * cubrt = (cubic_formula_cubrt 1 (2 * c) (c * c - 4 * e) (- d * d)) sqrt_cubic) ->
    (sqrt_p * sqrt_p = (cubic_formula 1 (2 * c) (c * c - 4 * e) cubrt)) ->
    (sqrt_quadratic * sqrt_quadratic = (quadratic_discriminant sqrt_p ((c + (sqrt_p * sqrt_p) - (d / sqrt_p)) / 2))) ->
    (x = quadratic_formula sqrt_p sqrt_quadratic) -> (quartic_expression x 1 0 c d e = 0) :=
begin
  intros h_sqrt_cubic h_cubrt_cubic h_sqrt_p h_sqrt_quadratic h_x,
  rw depressed_quartic_to_quadratic_product x c d e sqrt_p sqrt_cubic cubrt
            one_ne_zero two_ne_zero three_ne_zero sqrt_p_ne_zero int_quantity_ne_zero
            h_sqrt_cubic h_cubrt_cubic h_sqrt_p,
  rw quadratic_formula_correct sqrt_p ((c + (sqrt_p * sqrt_p) - (d / sqrt_p)) / 2) sqrt_quadratic x two_ne_zero h_sqrt_quadratic h_x,
  rw zero_mul,
end

lemma quartic_solution [field F] (x b c d e sqrt_p sqrt_cubic sqrt_quadratic cubrt: F)
    (one_ne_zero : (1 : F) ≠ 0) (two_ne_zero : (2 : F) ≠ 0) (three_ne_zero : (3 : F) ≠ 0)
    (sqrt_p_ne_zero : sqrt_p ≠ 0) (int_quantity_ne_zero : depressed_cubic_x_term 1 (2 * (depressed_quartic_squ_coefficient b c)) ((depressed_quartic_squ_coefficient b c) * (depressed_quartic_squ_coefficient b c) - 4 * (depressed_quartic_constant b c d e)) ≠ 0) :
    (sqrt_cubic * sqrt_cubic = (cubic_formula_sqrt 1 (2 * (depressed_quartic_squ_coefficient b c)) ((depressed_quartic_squ_coefficient b c) * (depressed_quartic_squ_coefficient b c) - 4 * (depressed_quartic_constant b c d e)) (- (depressed_quartic_linear_coefficient b c d) * (depressed_quartic_linear_coefficient b c d)))) ->
    (cubrt * cubrt * cubrt = (cubic_formula_cubrt 1 (2 * (depressed_quartic_squ_coefficient b c)) ((depressed_quartic_squ_coefficient b c) * (depressed_quartic_squ_coefficient b c) - 4 * (depressed_quartic_constant b c d e)) (- (depressed_quartic_linear_coefficient b c d) * (depressed_quartic_linear_coefficient b c d))) sqrt_cubic) ->
    (sqrt_p * sqrt_p = (cubic_formula 1 (2 * (depressed_quartic_squ_coefficient b c)) ((depressed_quartic_squ_coefficient b c) * (depressed_quartic_squ_coefficient b c) - 4 * (depressed_quartic_constant b c d e)) cubrt)) ->
    (sqrt_quadratic * sqrt_quadratic = (quadratic_discriminant sqrt_p (((depressed_quartic_squ_coefficient b c) + (sqrt_p * sqrt_p) - ((depressed_quartic_linear_coefficient b c d) / sqrt_p)) / 2))) ->
    (x = (quadratic_formula sqrt_p sqrt_quadratic) - (b / 4)) -> (quartic_expression x 1 b c d e = 0) :=
begin
  intros h_sqrt_cubic h_cubrt_cubic h_sqrt_p h_sqrt_quadratic h_x,
  rw convert_quartic_to_depressed,
  apply depressed_quartic_solution (x + b / 4) (depressed_quartic_squ_coefficient b c) (depressed_quartic_linear_coefficient b c d) (depressed_quartic_constant b c d e)
                                    sqrt_p sqrt_cubic sqrt_quadratic cubrt,
  any_goals {assumption},
    rw h_x, simp,
end

lemma depressed_quartic_to_linear_product [field F] (x c d e sqrt_p sqrt_cubic sqrt_discrim_a sqrt_discrim_b cubrt: F)
    (one_ne_zero : (1 : F) ≠ 0) (two_ne_zero : (2 : F) ≠ 0) (three_ne_zero : (3 : F) ≠ 0)
    (sqrt_p_ne_zero : sqrt_p ≠ 0) (int_quantity_ne_zero : depressed_cubic_x_term 1 (2 * c) (c * c - 4 * e) ≠ 0)
    :
    (sqrt_cubic * sqrt_cubic = (cubic_formula_sqrt 1 (2 * c) (c * c - 4 * e) (- d * d))) ->
    (cubrt * cubrt * cubrt = (cubic_formula_cubrt 1 (2 * c) (c * c - 4 * e) (- d * d)) sqrt_cubic) ->
    (sqrt_p * sqrt_p = (cubic_formula 1 (2 * c) (c * c - 4 * e) cubrt)) ->
    (sqrt_discrim_a * sqrt_discrim_a = (quadratic_discriminant sqrt_p ((c + (sqrt_p * sqrt_p) - (d / sqrt_p)) / 2))) ->
    (sqrt_discrim_b * sqrt_discrim_b = (quadratic_discriminant (- sqrt_p) ((c + (sqrt_p * sqrt_p) + (d / sqrt_p)) / 2))) ->
  (quartic_expression x 1 0 c d e) =
        (x - (quadratic_formula sqrt_p sqrt_discrim_a)) *
        (x - (quadratic_formula sqrt_p (- sqrt_discrim_a))) *
        (x - (quadratic_formula (- sqrt_p) sqrt_discrim_b)) *
        (x - (quadratic_formula (- sqrt_p) (- sqrt_discrim_b))) :=
begin
  intros h_sqrt_cubic h_cubrt h_sqrt_p h_discrim_a h_discrim_b,
  rw depressed_quartic_to_quadratic_product x c d e sqrt_p sqrt_cubic cubrt
                one_ne_zero two_ne_zero three_ne_zero sqrt_p_ne_zero int_quantity_ne_zero
                h_sqrt_cubic h_cubrt h_sqrt_p,
  rw quadratic_formula_factorise
        sqrt_p ((c + sqrt_p * sqrt_p - d / sqrt_p) / 2) sqrt_discrim_a x,
  have tmp : (x * x - sqrt_p * x) = (x * x + (- sqrt_p) * x), ring, rw tmp, clear tmp,
  rw quadratic_formula_factorise
        (- sqrt_p) ((c + sqrt_p * sqrt_p + d / sqrt_p) / 2) sqrt_discrim_b x,
  ring, repeat {assumption},
end

lemma quartic_to_linear_product [field F] (x b c d e sqrt_p sqrt_cubic sqrt_discrim_a sqrt_discrim_b cubrt: F)
    (one_ne_zero : (1 : F) ≠ 0) (two_ne_zero : (2 : F) ≠ 0) (three_ne_zero : (3 : F) ≠ 0)
    (sqrt_p_ne_zero : sqrt_p ≠ 0) (int_quantity_ne_zero : depressed_cubic_x_term 1 (2 * (depressed_quartic_squ_coefficient b c)) ((depressed_quartic_squ_coefficient b c) * (depressed_quartic_squ_coefficient b c) - 4 * (depressed_quartic_constant b c d e)) ≠ 0)
    :
    (sqrt_cubic * sqrt_cubic = (cubic_formula_sqrt 1 (2 * (depressed_quartic_squ_coefficient b c)) ((depressed_quartic_squ_coefficient b c) * (depressed_quartic_squ_coefficient b c) - 4 * (depressed_quartic_constant b c d e)) (- (depressed_quartic_linear_coefficient b c d) * (depressed_quartic_linear_coefficient b c d)))) ->
    (cubrt * cubrt * cubrt = (cubic_formula_cubrt 1 (2 * (depressed_quartic_squ_coefficient b c)) ((depressed_quartic_squ_coefficient b c) * (depressed_quartic_squ_coefficient b c) - 4 * (depressed_quartic_constant b c d e)) (- (depressed_quartic_linear_coefficient b c d) * (depressed_quartic_linear_coefficient b c d))) sqrt_cubic) ->
    (sqrt_p * sqrt_p = (cubic_formula 1 (2 * (depressed_quartic_squ_coefficient b c)) ((depressed_quartic_squ_coefficient b c) * (depressed_quartic_squ_coefficient b c) - 4 * (depressed_quartic_constant b c d e)) cubrt)) ->
    (sqrt_discrim_a * sqrt_discrim_a = (quadratic_discriminant sqrt_p (((depressed_quartic_squ_coefficient b c) + (sqrt_p * sqrt_p) - ((depressed_quartic_linear_coefficient b c d) / sqrt_p)) / 2))) ->
    (sqrt_discrim_b * sqrt_discrim_b = (quadratic_discriminant (- sqrt_p) (((depressed_quartic_squ_coefficient b c) + (sqrt_p * sqrt_p) + ((depressed_quartic_linear_coefficient b c d) / sqrt_p)) / 2))) ->
  (quartic_expression x 1 b c d e) =
        ((x + b/4) - (quadratic_formula sqrt_p sqrt_discrim_a)) *
        ((x + b/4) - (quadratic_formula sqrt_p (- sqrt_discrim_a))) *
        ((x + b/4) - (quadratic_formula (- sqrt_p) sqrt_discrim_b)) *
        ((x + b/4) - (quadratic_formula (- sqrt_p) (- sqrt_discrim_b))) :=
begin
  intros h_sqrt_cubic h_cubrt h_sqrt_p h_discrim_a h_discrim_b,
  rw convert_quartic_to_depressed, apply depressed_quartic_to_linear_product,
  repeat {assumption},
end

end field
