import number_theory.number_field.norm
import field_theory.is_alg_closed.basic
import ring_theory.norm

section instances

--local attribute [-instance] algebraic_closure.algebra

section algebraic_closure

variables (F K : Type*) [field F] [field K] [algebra F K]

variable (K)

-- Make this work for is_alg_closure
lemma algebraic_closure.char_zero [char_zero K] : char_zero (algebraic_closure K) :=
algebra_rat.char_zero (algebraic_closure K)


variables (A : Type*) [field A] [algebra K A] [is_alg_closure K A] [algebra F A]
  [is_scalar_tower F K A]

lemma is_alg_closure.char_zero [char_zero K] : char_zero A := sorry

lemma is_alg_closure.of_algebraic (h : algebra.is_algebraic F K) : is_alg_closure F A :=
⟨is_alg_closure.alg_closed K, algebra.is_algebraic_trans h is_alg_closure.algebraic⟩

lemma is_alg_closure.normal_of_algebraic (h : algebra.is_algebraic F K) : normal F A :=
by { haveI := is_alg_closure.of_algebraic F K A h, apply_instance, }

lemma is_alg_closure.is_galois_of_algebraic (h : algebra.is_algebraic F K) [char_zero F] :
  is_galois F A :=
by { haveI := is_alg_closure.of_algebraic F K A h, apply_instance, }

-- instance is_alg_closure.algebra_of_algebraic : algebra F A := sorry

-- example : normal F A := sorry

-- -- Do we need that? What about is_alg_closure? and is_separable?

-- instance algebraic_closure.char_zero : char_zero A := algebra_rat.char_zero _

end algebraic_closure

section is_scalar_tower

variables {F K A : Type*} [field F] [field K] [field A] [algebra F K] [algebra F A] [algebra K A]
  [is_scalar_tower F K A]

instance normal_closure_alg_closure.is_scalar_tower : is_scalar_tower F (normal_closure F K A) A :=
is_scalar_tower.subalgebra' F A A _

end is_scalar_tower

section is_galois

variables (k K F : Type*) [field k] [field K] [field F] [algebra k K] [algebra k F]
  [algebra K F] [is_scalar_tower k K F] [is_galois k F]

instance is_galois.normal_closure : is_galois k (normal_closure k K F) :=
{ to_is_separable := is_separable_tower_bot_of_is_separable k _ F }

end is_galois

section number_field

variables (F K A : Type*) [field K] [field F] [field A]
variables [number_field K] [number_field F] [algebra F K]
variables [char_zero A] [algebra K A] [algebra F A]
variables [is_scalar_tower F K A]

lemma number_field.finite_dimensional_algebra : finite_dimensional F K :=
finite_dimensional.right ℚ F K

-- local attribute [-instance] algebraic_closure.algebra
-- local attribute [-instance] algebra_rat

instance number_field.normal_closure : number_field (normal_closure F K A) :=
{ to_char_zero := char_zero.of_module _ A,
  to_finite_dimensional :=
  begin
    convert finite_dimensional.trans ℚ F _,
    exact (normal_closure F K A).module',
    apply_instance,
    haveI :=  number_field.finite_dimensional_algebra F K,
    convert normal_closure.is_finite_dimensional F K A,
  end }

end number_field

#exit

noncomputable instance i2 : algebra K (algebraic_closure K) := algebraic_closure.algebra K

instance : char_zero (normal_closure ℚ K (algebraic_closure K)) := sorry

-- noncomputable instance : algebra ℚ (normal_closure ℚ K (algebraic_closure K)) := algebra_rat

instance : number_field (normal_closure ℚ K (algebraic_closure K)) := sorry

instance : is_galois ℚ (normal_closure ℚ K (algebraic_closure K)) := sorry

instance i3 : is_galois K  (normal_closure ℚ K (algebraic_closure K)) := sorry

end instances

#exit

section normal_closure

variables (F K A : Type*) [field F] [field K] [field A] [algebra F K] [algebra F A] [algebra K A]
[is_scalar_tower F K A]

-- instance [char_zero F] : char_zero (normal_closure F K A) :=
--  char_zero_of_injective_algebra_map (algebra_map F _).injective

instance normal_closure_alg_closure.is_scalar_tower : is_scalar_tower F (normal_closure F K A) A :=
is_scalar_tower.subalgebra' F A A _

-- TODO. [is_separable F K] should be enough
instance [is_separable F A] : is_separable F (normal_closure F K A) :=
is_separable_tower_bot_of_is_separable F _ A

noncomputable instance [char_zero F] : char_zero (normal_closure F K A) := sorry

lemma normal_algebra_closure_of_is_algebraic [is_alg_closure K A] (h : algebra.is_algebraic F K) :
  normal F A := sorry

instance normal_closure.is_galois [normal F A] [is_separable F A] :
  is_galois F (normal_closure F K A) := { }

variables [number_field F] [number_field K]

instance : number_field (normal_closure F K A) :=
{ to_finite_dimensional :=
  begin
    haveI : finite_dimensional F K := finite_dimensional.right ℚ F K,
    exact finite_dimensional.trans ℚ F (normal_closure F K A),
  end, }



end normal_closure

#exit

open_locale number_field

/- section galois_closure

variables (F K L : Type*) [field F] [field K] [number_field F] [number_field K] [field L]
  [algebra K L] [is_alg_closure K L] [algebra F K] [algebra F L] [is_scalar_tower F K L]

instance : number_field (normal_closure F K L) :=
{ to_char_zero :=
    char_zero_of_injective_algebra_map (algebra_map F _).injective,
  to_finite_dimensional :=
  begin
    haveI : finite_dimensional F K := sorry,
    have := normal_closure.is_finite_dimensional F K L,
  end,
}

end galois_closure -/

-- section normal

-- variables {F K L : Type*} [field F] [field K] [field L] [algebra F K] [algebra F L]
--   [algebra K L] [is_scalar_tower F K L] [is_alg_closure K L]

-- lemma is_alg_closed.normal.of_algebraic (h : algebra.is_algebraic F K) : normal F L :=
-- normal.of_alg_equiv (is_alg_closure.equiv_of_algebraic F K L (algebraic_closure F) h).symm

-- end normal
