import all
.
#check module.oriented
run_cmd find_library_diamonds 0 1 [``module.oriented] -- 799 total
-- run_cmd find_library_diamonds 755 1 --lots
-- run_cmd find_library_diamonds 637 1
-- run_cmd find_library_diamonds 247 1 -- long?
-- run_cmd find_library_diamonds 437 1 long
-- run_cmd find_library_diamonds 473 1 long
-- run_cmd find_library_diamonds 514 1 -- oom
-- run_cmd find_library_diamonds 523 1 --slow/oom
-- run_cmd find_library_diamonds 538 1 -- slow/oom
#check char_p -- good example of prop, should be skipped
#check topological_ring -- good example of prop, should be skipped

-- also metric versions
example : punit.uniform_space = pseudo_metric_space.to_uniform_space := by refl
example : empty.uniform_space = pseudo_metric_space.to_uniform_space := by refl

-- probably delete pos_num dvd
example : pos_num.has_dvd = monoid_has_dvd := by refl

example : filter.applicative = alternative.to_applicative := by refl

-- encodable
example : rat.encodable = denumerable.to_encodable := by refl
-- maybe Scott shouldn't be reducible?
example : Scott.topological_space ereal = ereal.topological_space := by refl
example : Scott.topological_space ennreal = ennreal.topological_space := by refl
example : Scott.topological_space punit = punit.topological_space := by refl
example : Scott.topological_space Prop = sierpinski_space := by refl
-- do we want circle to be irreducible?
example : circle.measurable_space = subtype.measurable_space := by refl
example : circle.measure_theory.measure_space = set_coe.measure_space _ := by refl
example : AddCommGroup.has_zero_object = category_theory.abelian.has_zero_object := by refl
example : Module.forget₂_AddCommGroup_full = category_theory.equivalence.full_of_equivalence _ := by refl
example : simplex_category.skeletal_functor.category_theory.full = category_theory.equivalence.full_of_equivalence _ := by refl
example : Fintype.skeleton.incl.category_theory.full = category_theory.equivalence.full_of_equivalence _ := by refl
--category_theory.is_iso 409 very slow
-- 410 oom probably mono or sometihn
-- second of these is low prio so probably not an issue
example : unit.fintype = fintype.of_subsingleton' _ := by refl
example : punit.fintype = fintype.of_subsingleton' _ := by refl

-- unit fintype of subsingleton
-- punit fintype of subsingleton'
-- lots similar to this? not such a big deal
example : punit.mul_distrib_mul_action = mul_aut.apply_mul_distrib_mul_action := by refl

-- maybe just delete enat.lattice?
example : enat.lattice = lattice_of_linear_order := by refl
--same
example : enat.lattice = complete_lattice.to_lattice _ := by refl

--comes from
-- noncomputable instance : conditionally_complete_linear_order_bot ℝ≥0 :=
-- nonneg.conditionally_complete_linear_order_bot real.Sup_empty.le
example : nnreal.semilattice_inf = lattice.to_semilattice_inf _ := by refl



#check znum_coe


example : pnat.has_well_founded = has_well_founded_of_has_sizeof _ := by refl
example : sort.inhabited = prop.inhabited := by refl

#print real.has_sizeof_inst
#print default_has_sizeof
example : Module.category_theory.linear = category_theory.linear.preadditive_int_linear := by refl

example : pgame.short_0 = pgame.short.of_pempty := by refl--: (pgame.mk pempty pempty pempty.elim pempty.elim).short

-- run_cmd find_library_diamonds
  -- some examples
  -- ``nat.decidable_eq, ``decidable_eq_of_decidable_le,
  -- ``real.has_neg, ``sub_neg_monoid.to_has_neg,
  -- ``algebra_rat, ``algebra.id,

example : (decidable_eq_of_decidable_le : decidable_eq bool) = (by apply_instance) := by refl
example {M : Type*} [cancel_comm_monoid_with_zero M] [normalized_gcd_monoid M] [unique (units M)] :
  normalization_monoid_of_unique_units = @normalized_gcd_monoid.to_normalization_monoid M _ _ :=
by refl


example :
  nat.decidable_eq = decidable_eq_of_decidable_le :=
by refl
