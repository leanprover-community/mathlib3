#exit
import all

open norm_cast

run_cmd test_classifiers make_guess get_label

/- classifiers disagree -/

/- firt classifier can't guess -/
#check @num.cast_to_znum
  -- first:  none
  -- second: (some push)
#check @linear_map.coe_restrict_scalars_eq_coe
  -- first:  none
  -- second: (some push)
#check @continuous_linear_map.restrict_scalars_coe_eq_coe'
  -- first:  none
  -- second: (some push)
#check @continued_fraction.coe_to_generalized_continued_fraction
  -- first:  none
  -- second: (some push)

/- second classifier can't guess -/

/- classifiers agree -/
#check @int.coe_nat_zero
  -- first:  (some push)
  -- second: (some push)
#check @int.coe_nat_one
  -- first:  (some push)
  -- second: (some push)
#check @int.nat_abs_of_nat
  -- first:  (some elim)
  -- second: (some elim)
#check @int.coe_nat_succ
  -- first:  (some move)
  -- second: (some move)
#check @int.coe_nat_add
  -- first:  (some move)
  -- second: (some move)
#check @int.coe_nat_sub
  -- first:  (some move)
  -- second: (some move)
#check @int.coe_nat_mul
  -- first:  (some move)
  -- second: (some move)
#check @ite_cast
  -- first:  (some move)
  -- second: (some move)
#check @coe_monoid_hom'
  -- first:  (some squash)
  -- second: (some squash)
#check @coe_add_monoid_hom'
  -- first:  (some squash)
  -- second: (some squash)
#check @nat.cast_zero
  -- first:  (some push)
  -- second: (some push)
#check @nat.cast_succ
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_one
  -- first:  (some push)
  -- second: (some push)
#check @nat.cast_add
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_bit0
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_bit1
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_pred
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_sub
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_mul
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_le
  -- first:  (some elim)
  -- second: (some elim)
#check @nat.cast_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @nat.cast_id
  -- first:  (some push)
  -- second: (some push)
#check @nat.cast_min
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_max
  -- first:  (some move)
  -- second: (some move)
#check @nat.abs_cast
  -- first:  (some elim)
  -- second: (some elim)
#check @nat.cast_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @int.coe_nat_le
  -- first:  (some elim)
  -- second: (some elim)
#check @int.coe_nat_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @int.coe_nat_inj'
  -- first:  (some elim)
  -- second: (some elim)
#check @int.coe_nat_abs
  -- first:  (some elim)
  -- second: (some elim)
#check @int.coe_nat_div
  -- first:  (some move)
  -- second: (some move)
#check @int.coe_nat_dvd
  -- first:  (some elim)
  -- second: (some elim)
#check @int.cast_zero
  -- first:  (some push)
  -- second: (some push)
#check @int.cast_coe_nat
  -- first:  (some squash)
  -- second: (some squash)
#check @int.cast_neg_succ_of_nat
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_one
  -- first:  (some push)
  -- second: (some push)
#check @int.cast_sub_nat_nat
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_neg_of_nat
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_add
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_neg
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_sub
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @int.cast_mul
  -- first:  (some move)
  -- second: (some move)
#check @int.coe_nat_bit0
  -- first:  (some move)
  -- second: (some move)
#check @int.coe_nat_bit1
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_bit0
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_bit1
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_le
  -- first:  (some elim)
  -- second: (some elim)
#check @int.cast_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @int.cast_id
  -- first:  (some push)
  -- second: (some push)
#check @int.cast_min
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_max
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_abs
  -- first:  (some move)
  -- second: (some move)
#check @nat.cast_pow
  -- first:  (some move)
  -- second: (some move)
#check @int.coe_nat_pow
  -- first:  (some move)
  -- second: (some move)
#check @int.cast_pow
  -- first:  (some move)
  -- second: (some move)
#check @rat.coe_int_num
  -- first:  (some elim)
  -- second: (some elim)
#check @rat.coe_int_denom
  -- first:  (some elim)
  -- second: (some elim)
#check @rat.coe_nat_num
  -- first:  (some elim)
  -- second: (some elim)
#check @rat.coe_nat_denom
  -- first:  (some elim)
  -- second: (some elim)
#check @rat.cast_coe_int
  -- first:  (some squash)
  -- second: (some squash)
#check @rat.cast_coe_nat
  -- first:  (some squash)
  -- second: (some squash)
#check @rat.cast_zero
  -- first:  (some push)
  -- second: (some push)
#check @rat.cast_one
  -- first:  (some push)
  -- second: (some push)
#check @rat.cast_mk_of_ne_zero
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_add_of_ne_zero
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_neg
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_sub_of_ne_zero
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_mul_of_ne_zero
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_inv_of_ne_zero
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_div_of_ne_zero
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @rat.cast_add
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_sub
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_mul
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_bit0
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_bit1
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_mk
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_inv
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_div
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_pow
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_le
  -- first:  (some elim)
  -- second: (some elim)
#check @rat.cast_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @rat.cast_id
  -- first:  (some push)
  -- second: (some push)
#check @rat.cast_min
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_max
  -- first:  (some move)
  -- second: (some move)
#check @rat.cast_abs
  -- first:  (some move)
  -- second: (some move)
#check @pos_num.cast_one
  -- first:  (some push)
  -- second: (some push)
#check @pos_num.cast_bit0
  -- first:  (some move)
  -- second: (some move)
#check @pos_num.cast_bit1
  -- first:  (some move)
  -- second: (some move)
#check @pos_num.cast_to_nat
  -- first:  (some squash)
  -- second: (some squash)
#check @pos_num.to_nat_to_int
  -- first:  (some squash)
  -- second: (some squash)
#check @pos_num.cast_to_int
  -- first:  (some squash)
  -- second: (some squash)
#check @pos_num.add_to_nat
  -- first:  (some move)
  -- second: (some move)
#check @pos_num.mul_to_nat
  -- first:  (some move)
  -- second: (some move)
#check @pos_num.lt_to_nat
  -- first:  (some elim)
  -- second: (some elim)
#check @pos_num.le_to_nat
  -- first:  (some elim)
  -- second: (some elim)
#check @num.add_of_nat
  -- first:  (some move)
  -- second: (some move)
#check @num.cast_zero
  -- first:  (some push)
  -- second: (some push)
#check @num.cast_one
  -- first:  (some push)
  -- second: (some push)
#check @num.cast_to_nat
  -- first:  (some squash)
  -- second: (some squash)
#check @num.to_nat_to_int
  -- first:  (some squash)
  -- second: (some squash)
#check @num.cast_to_int
  -- first:  (some squash)
  -- second: (some squash)
#check @num.to_of_nat
  -- first:  (some squash)
  -- second: (some squash)
#check @num.of_nat_cast
  -- first:  (some squash)
  -- second: (some squash)
#check @num.of_nat_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @num.add_to_nat
  -- first:  (some move)
  -- second: (some move)
#check @num.mul_to_nat
  -- first:  (some move)
  -- second: (some move)
#check @num.lt_to_nat
  -- first:  (some elim)
  -- second: (some elim)
#check @num.le_to_nat
  -- first:  (some elim)
  -- second: (some elim)
#check @num.of_to_nat
  -- first:  (some squash)
  -- second: (some squash)
#check @num.to_nat_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @num.dvd_to_nat
  -- first:  (some elim)
  -- second: (some elim)
#check @pos_num.to_nat_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @pos_num.cast_add
  -- first:  (some move)
  -- second: (some move)
#check @pos_num.cast_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @pos_num.cast_mul
  -- first:  (some move)
  -- second: (some move)
#check @pos_num.cast_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @pos_num.cast_le
  -- first:  (some elim)
  -- second: (some elim)
#check @num.cast_add
  -- first:  (some move)
  -- second: (some move)
#check @num.cast_bit0
  -- first:  (some move)
  -- second: (some move)
#check @num.cast_bit1
  -- first:  (some move)
  -- second: (some move)
#check @num.cast_mul
  -- first:  (some move)
  -- second: (some move)
#check @num.cast_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @num.cast_le
  -- first:  (some elim)
  -- second: (some elim)
#check @num.cast_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @znum.cast_zero
  -- first:  (some push)
  -- second: (some push)
#check @znum.cast_one
  -- first:  (some push)
  -- second: (some push)
#check @znum.cast_zneg
  -- first:  (some move)
  -- second: (some move)
#check @znum.neg_of_int
  -- first:  (some move)
  -- second: (some move)
#check @znum.cast_to_int
  -- first:  (some squash)
  -- second: (some squash)
#check @znum.cast_bit0
  -- first:  (some move)
  -- second: (some move)
#check @znum.cast_bit1
  -- first:  (some move)
  -- second: (some move)
#check @num.sub_to_nat
  -- first:  (some move)
  -- second: (some move)
#check @znum.cast_add
  -- first:  (some move)
  -- second: (some move)
#check @znum.mul_to_int
  -- first:  (some move)
  -- second: (some move)
#check @znum.of_to_int
  -- first:  (some squash)
  -- second: (some squash)
#check @znum.to_of_int
  -- first:  (some squash)
  -- second: (some squash)
#check @znum.of_int_cast
  -- first:  (some squash)
  -- second: (some squash)
#check @znum.of_nat_cast
  -- first:  (some squash)
  -- second: (some squash)
#check @znum.lt_to_int
  -- first:  (some elim)
  -- second: (some elim)
#check @znum.le_to_int
  -- first:  (some elim)
  -- second: (some elim)
#check @znum.cast_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @znum.cast_le
  -- first:  (some elim)
  -- second: (some elim)
#check @znum.cast_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @znum.dvd_to_int
  -- first:  (some elim)
  -- second: (some elim)
#check @num.div_to_nat
  -- first:  (some move)
  -- second: (some move)
#check @num.mod_to_nat
  -- first:  (some move)
  -- second: (some move)
#check @znum.div_to_int
  -- first:  (some move)
  -- second: (some move)
#check @znum.mod_to_int
  -- first:  (some move)
  -- second: (some move)
#check @enat.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @enat.coe_one
  -- first:  (some push)
  -- second: (some push)
#check @enat.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @enat.coe_le_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @enat.coe_lt_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @ring_equiv.coe_mul_equiv'
  -- first:  (some squash)
  -- second: (some squash)
#check @ring_equiv.coe_add_equiv'
  -- first:  (some squash)
  -- second: (some squash)
#check @cast_fpow
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.coe_mul
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.coe_div
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.coe_inv
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.coe_pow
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.sum_coe
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.prod_coe
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.smul_coe
  -- first:  (some move)
  -- second: (some move)
#check @nnreal.coe_nat_cast
  -- first:  (some squash)
  -- second: (some squash)
#check @nnreal.coe_le
  -- first:  (some elim)
  -- second: (some elim)
#check @nnreal.coe_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @nnreal.coe_pos
  -- first:  (some elim)
  -- second: (some elim)
#check @nnreal.coe_eq
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.to_nnreal_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @ennreal.coe_one
  -- first:  (some push)
  -- second: (some push)
#check @ennreal.coe_eq_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_le_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_lt_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_eq_zero
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.zero_eq_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_eq_one
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.one_eq_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_nonneg
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_pos
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_mul
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_bit0
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_bit1
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_pow
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_finset_sum
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_finset_prod
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.zero_lt_coe_iff
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.one_le_coe_iff
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_le_one_iff
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_lt_one_iff
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.one_lt_coe_iff
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.coe_nat
  -- first:  (some squash)
  -- second: (some squash)
#check @ennreal.coe_min
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_max
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_sub
  -- first:  (some move)
  -- second: (some move)
#check @ennreal.coe_div
  -- first:  (some move)
  -- second: (some move)
#check @rat.dist_cast
  -- first:  (some elim)
  -- second: (some elim)
#check @int.dist_cast_real
  -- first:  (some elim)
  -- second: (some elim)
#check @int.dist_cast_rat
  -- first:  (some elim)
  -- second: (some elim)
#check @nnreal.has_sum_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @nnreal.summable_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @nnreal.coe_tsum
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_re
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.of_real_im
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.of_real_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.of_real_zero
  -- first:  (some push)
  -- second: (some push)
#check @complex.of_real_one
  -- first:  (some push)
  -- second: (some push)
#check @complex.of_real_add
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_bit0
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_bit1
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_neg
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_mul
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_sub
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_pow
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_inv
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_div
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_fpow
  -- first:  (some move)
  -- second: (some move)
#check @complex.of_real_int_cast
  -- first:  (some squash)
  -- second: (some squash)
#check @complex.of_real_nat_cast
  -- first:  (some squash)
  -- second: (some squash)
#check @complex.of_real_rat_cast
  -- first:  (some squash)
  -- second: (some squash)
#check @complex.nat_cast_re
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.nat_cast_im
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.int_cast_re
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.int_cast_im
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.rat_cast_re
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.rat_cast_im
  -- first:  (some elim)
  -- second: (some elim)
#check @complex.abs_cast_nat
  -- first:  (some elim)
  -- second: (some elim)
#check @multiplicity.int.coe_nat_multiplicity
  -- first:  (some elim)
  -- second: (some elim)
#check @continuous_linear_map.coe_coe
  -- first:  (some squash)
  -- second: (some squash)
#check @continuous_linear_map.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @continuous_linear_map.coe_zero'
  -- first:  (some push)
  -- second: (some push)
#check @continuous_linear_map.coe_id
  -- first:  (some push)
  -- second: (some push)
#check @continuous_linear_map.coe_id'
  -- first:  (some push)
  -- second: (some push)
#check @continuous_linear_map.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_add'
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_neg
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_neg'
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_sub
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_sub'
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_comp
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_comp'
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_apply
  -- first:  (some move)
  -- second: (some move)
#check @continuous_linear_map.coe_apply'
  -- first:  (some move)
  -- second: (some move)
#check @int.norm_cast_real
  -- first:  (some elim)
  -- second: (some elim)
#check @rat.norm_cast_real
  -- first:  (some elim)
  -- second: (some elim)
#check @int.norm_cast_rat
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.tendsto_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @ennreal.has_sum_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @linear_map_with_bound_coe
  -- first:  (some push)
  -- second: (some push)
#check @continuous_linear_map.restrict_scalars_coe_eq_coe
  -- first:  (some move)
  -- second: (some move)
#check @cardinal.nat_cast_pow
  -- first:  (some move)
  -- second: (some move)
#check @cardinal.nat_cast_le
  -- first:  (some elim)
  -- second: (some elim)
#check @cardinal.nat_cast_lt
  -- first:  (some elim)
  -- second: (some elim)
#check @cardinal.nat_cast_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @cardinal.nat_succ
  -- first:  (some move)
  -- second: (some move)
#check @uniform_space.completion.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @uniform_space.completion.coe_neg
  -- first:  (some move)
  -- second: (some move)
#check @uniform_space.completion.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @uniform_space.completion.coe_one
  -- first:  (some push)
  -- second: (some push)
#check @uniform_space.completion.coe_mul
  -- first:  (some move)
  -- second: (some move)
#check @free_ring.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @free_ring.coe_one
  -- first:  (some push)
  -- second: (some push)
#check @free_ring.coe_neg
  -- first:  (some move)
  -- second: (some move)
#check @free_ring.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @free_ring.coe_sub
  -- first:  (some move)
  -- second: (some move)
#check @free_ring.coe_mul
  -- first:  (some move)
  -- second: (some move)
#check @mv_polynomial.coeff_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @mv_polynomial.coe_monomial
  -- first:  (some move)
  -- second: (some move)
#check @mv_polynomial.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @mv_polynomial.coe_one
  -- first:  (some push)
  -- second: (some push)
#check @mv_polynomial.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @mv_polynomial.coe_mul
  -- first:  (some move)
  -- second: (some move)
#check @mv_polynomial.coe_C
  -- first:  (some move)
  -- second: (some move)
#check @mv_polynomial.coe_X
  -- first:  (some push)
  -- second: (some push)
#check @polynomial.coeff_coe
  -- first:  (some elim)
  -- second: (some elim)
#check @polynomial.coe_monomial
  -- first:  (some move)
  -- second: (some move)
#check @polynomial.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @polynomial.coe_one
  -- first:  (some push)
  -- second: (some push)
#check @polynomial.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @polynomial.coe_mul
  -- first:  (some move)
  -- second: (some move)
#check @polynomial.coe_C
  -- first:  (some move)
  -- second: (some move)
#check @polynomial.coe_X
  -- first:  (some push)
  -- second: (some push)
#check @generalized_continued_fraction.pair.coe_to_generalized_continued_fraction_pair
  -- first:  (some move)
  -- second: (some move)
#check @generalized_continued_fraction.coe_to_generalized_continued_fraction
  -- first:  (some move)
  -- second: (some move)
#check @simple_continued_fraction.coe_to_generalized_continued_fraction
  -- first:  (some push)
  -- second: (some push)
#check @continued_fraction.coe_to_simple_continued_fraction
  -- first:  (some push)
  -- second: (some push)
#check @padic.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @padic.coe_neg
  -- first:  (some move)
  -- second: (some move)
#check @padic.coe_mul
  -- first:  (some move)
  -- second: (some move)
#check @padic.coe_sub
  -- first:  (some move)
  -- second: (some move)
#check @padic.coe_div
  -- first:  (some move)
  -- second: (some move)
#check @padic.coe_one
  -- first:  (some push)
  -- second: (some push)
#check @padic.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @padic.coe_inj
  -- first:  (some elim)
  -- second: (some elim)
#check @padic_int.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @padic_int.coe_mul
  -- first:  (some move)
  -- second: (some move)
#check @padic_int.coe_neg
  -- first:  (some move)
  -- second: (some move)
#check @padic_int.coe_sub
  -- first:  (some move)
  -- second: (some move)
#check @padic_int.coe_one
  -- first:  (some push)
  -- second: (some push)
#check @padic_int.coe_coe
  -- first:  (some squash)
  -- second: (some squash)
#check @padic_int.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @padic_int.cast_pow
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.eq_iff
  -- first:  (some elim)
  -- second: (some elim)
#check @measure_theory.l1.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @measure_theory.l1.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.coe_neg
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.coe_sub
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.coe_smul
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.coe_pos_part
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.simple_func.eq_iff
  -- first:  (some elim)
  -- second: (some elim)
#check @measure_theory.l1.simple_func.eq_iff'
  -- first:  (some elim)
  -- second: (some elim)
#check @measure_theory.l1.simple_func.coe_zero
  -- first:  (some push)
  -- second: (some push)
#check @measure_theory.l1.simple_func.coe_add
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.simple_func.coe_neg
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.simple_func.coe_sub
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.simple_func.coe_smul
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.simple_func.coe_pos_part
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.simple_func.coe_neg_part
  -- first:  (some move)
  -- second: (some move)
#check @measure_theory.l1.integral_coe_eq_integral
  -- first:  (some elim)
  -- second: (some elim)
