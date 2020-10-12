import linear_algebra.finite_dimensional
import ring_theory.ideal.basic
import algebra.field
import ring_theory.subring
import ring_theory.integral_closure
import ring_theory.fractional_ideal
import data.rat.basic
import ring_theory.algebraic
import field_theory.separable
import field_theory.normal
import data.padics.padic_integers
import algebra.category.CommRing.basic
import category_theory.concrete_category.bundled
import algebra.free_monoid

open function
open_locale classical big_operators

def is_integrally_closed_domain (R : Type*) [comm_ring R] : Prop := ∀ {r s : R}, s ≠ 0 → (∃ (n : ℕ) (f : ℕ → R)
(hf : f 0 = 1), ∑ ij in finset.nat.antidiagonal n, f ij.1 * r ^ ij.2 * s ^ ij.1 = 0) → s ∣ r

class dedekind_id (R : Type*) [integral_domain R] : Prop :=
    (noetherian : is_noetherian_ring R)
    (int_closed : is_integrally_closed_domain R)
    (max_nonzero_primes : ∀ P : ideal R, P ≠ ⊥ → P.is_prime → P.is_maximal)

class number_field (K : Type*) :=
   (fld : field K)
   (alg : algebra ℚ K)
   (fd : finite_dimensional ℚ K)

instance field_of_number_field (K : Type*) [number_field K] : field K := _inst_1.fld

instance algebra_of_number_field (K : Type*) [number_field K] : algebra ℚ K := _inst_1.alg

instance infinite_of_number_field (K : Type*) [number_field K] : infinite K := begin
  let f : ℤ → K := (λ n, (n : ℚ) • (1 : K)),
  apply infinite.of_injective f,
  intros x y hxy,
  have hxy2 : (x : ℚ) • (1 : K) = (y : ℚ) • (1 : K), exact hxy,
  have h : 0 = ((x : ℚ) - (y : ℚ)) • (1 : K), calc 0 = (x : ℚ) • (1 : K) - (y : ℚ) • (1 : K) : by rw sub_eq_zero.mpr hxy
  ... = (x : ℚ) • (1 : K) + (-((y : ℚ) • (1 : K))) : sub_eq_add_neg (↑x • 1) (↑y • 1)
  ... = (x : ℚ) • (1 : K) + ((-(y : ℚ)) • (1 : K)) : by rw neg_smul
  ... = ((x : ℚ) + (-(y : ℚ))) • (1 : K) : by rw add_smul
  ... = ((x : ℚ) - (y : ℚ)) • (1 : K) : by rw sub_eq_add_neg,
  have h2 : ((x : ℚ) - (y : ℚ)) = 0 ∨ (1 : K) = 0, {exact (@smul_eq_zero ℚ K _ _ _ ((x : ℚ) - (y : ℚ)) (1 : K)).1 (eq.symm h)},
  cases h2, {have h3 : (x : ℚ) = (y : ℚ), exact sub_eq_zero.mp h2,
    exact (rat.coe_int_inj (x : ℤ) (y : ℤ)).1 h3},
  {exfalso, revert h2, simp}
end

def number_ring (K : Type*) [number_field K] := @integral_closure ℤ K _ (@field.to_comm_ring K _inst_1.fld) _

theorem integral_domain_of_number_ring (K : Type*) [number_field K] : integral_domain (number_ring K) :=
(number_ring K).integral_domain

example (K : Type*) [field K] (x : K) (h : x ≠ 0): x * (field.inv x) = 1 := field.mul_inv_cancel h

/-- A predicate to express that a ring is a field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms. -/
structure is_field' (R : Type*) [ring R] : Prop :=
    (exists_pair_ne : ∃ (x y : R), x ≠ y)
    (mul_comm : ∀ (x y : R), x * y = y * x)
    (mul_inv_cancel' : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1)

/-- Every field satisfies the predicate for integral domains. -/
lemma field.to_is_field' (R : Type*) [field R] : is_field' R :=
    {mul_inv_cancel' := λ a ha, ⟨a⁻¹, field.mul_inv_cancel ha⟩,
   .. (‹_› : field R) }

noncomputable def is_field'.to_field (R : Type*) [ring R] (h : is_field' R) : field R :=
    {inv := (λ a, if ha : a = 0 then 0 else classical.some (is_field'.mul_inv_cancel' h ha)),
    inv_zero := (dif_pos rfl),
    mul_inv_cancel := (λ a ha, begin
        convert classical.some_spec (is_field'.mul_inv_cancel' h ha),
        exact dif_neg ha
    end),
    .._inst_1, ..h}

/-- There is a unique inverse in a field.
-/
lemma uniq_inv_of_is_field' (R : Type*) [comm_ring R] [is_field' R]: ∀ (x : R), x ≠ 0 → ∃! (y : R), x * y = 1 := begin
    intros x hx,
    apply exists_unique_of_exists_of_unique,
        {exact _inst_2.mul_inv_cancel' hx},
    intros y z hxy hxz,
    calc y = y * 1 : eq.symm (mul_one y)
    ... = y * (x * z) : by rw hxz
    ... = (y * x) * z : eq.symm (mul_assoc y x z)
    ... = (x * y) * z : by rw mul_comm y x
    ... = 1 * z : by rw hxy
    ... = z : one_mul z
end

/-- If the quotient of a `comm_ring` by an ideal is a field, then the ideal is maximal
-/
lemma maximal_ideal_of_is_field_quotient (R : Type*) [comm_ring R] (I : ideal R)
[@is_field' I.quotient (comm_ring.to_ring (ideal.quotient I))] : I.is_maximal := begin
    apply ideal.is_maximal_iff.2,
    split, {intro h,
        rcases (_inst_2.exists_pair_ne) with ⟨⟨x⟩, ⟨y⟩, hxy⟩,
        apply hxy,
        apply ideal.quotient.eq.2,
        rw ←mul_one (x-y),
        apply submodule.smul_mem',
        exact h},
    {intros J x hIJ hxnI hxJ,
        have hxn0 : (ideal.quotient.mk I x) ≠ 0,
        {exact @mt ((ideal.quotient.mk I x) = 0) (x ∈ I) ideal.quotient.eq_zero_iff_mem.1 hxnI},
        have hinvx : ∃ (y : I.quotient), (ideal.quotient.mk I x) * y = 1, {exact _inst_2.mul_inv_cancel' hxn0},
        rcases hinvx with ⟨⟨y⟩, hy⟩,
        change (ideal.quotient.mk I x) * (ideal.quotient.mk I y) = 1 at hy,
        rw ←((ideal.quotient.mk I).map_mul x y) at hy,
        have hxy1I : x*y-1 ∈ I, exact ideal.quotient.eq.1 hy,
        have hxy1J : x*y-1 ∈ J, exact hIJ hxy1I,
        have hxyJ : x*y ∈ J, exact ideal.mul_mem_right J hxJ,
        have hend : x*y-(x*y-1) ∈ J, exact ideal.sub_mem J hxyJ hxy1J,
        have h1 : 1 = x*y-(x*y-1), by ring,
        rw h1,
        exact hend}
end

/-- The quotient of a ring by an ideal is a field iff the ideal is maximal.
-/
theorem maximal_ideal_iff_is_field_quotient (R : Type*) [comm_ring R] (I : ideal R) :
I.is_maximal ↔ (@is_field' I.quotient (comm_ring.to_ring (ideal.quotient I))) := begin
    split,
    {intro h,
        exact @field.to_is_field' I.quotient (@ideal.quotient.field _ _ I h)},
    {intro h,
        exact @maximal_ideal_of_is_field_quotient R _ I h,}
end

instance dedekind_domain_of_number_ring (K : Type*) [number_field K] : dedekind_id (number_ring K) := {
  noetherian := sorry,
  int_closed := sorry,
  max_nonzero_primes := (begin
    intros P hP hPp,
    have hid : integral_domain P.quotient, exact @ideal.quotient.integral_domain _ _ P hPp,
    have hfin : fintype P.quotient, {sorry},
    have hf : is_field' (P.quotient), {sorry},
    exact @maximal_ideal_of_is_field_quotient (number_ring K) _ P hf,
  end)}

noncomputable theory
open_locale classical

open finite_dimensional
open ring.fractional_ideal

namespace number_field

variables (K : Type*) [number_field K]

variables (g : fraction_map (number_ring K) K)

def fractional_ideal := { Q : ring.fractional_ideal g // is_unit Q }

@[ext]
lemma ext {I J : fractional_ideal K g} : (I.1 : submodule (number_ring K) g.codomain) = J.1.1 → I = J :=
begin
  rw <-subtype.val_eq_coe,
  rw subtype.ext_iff_val,
  rw subtype.ext_iff_val,
  rintros,
  assumption,
end

instance : no_zero_divisors (ring.fractional_ideal g) :=
begin sorry, end

instance : has_mul (fractional_ideal K g) :=
begin
  constructor,
  rintros a b,
  use a.1*b.1,
  apply is_unit.mul,
  use a.2,
  use b.2,
end

lemma blossom (I J : fractional_ideal K g) : (I * J).val = I.val * J.val :=
begin
  split,
end

lemma blossom' (I J : ring.fractional_ideal g) : (I * J).val = I.val * J.val :=
begin
  split,
end

instance : has_one (fractional_ideal K g) :=
begin
  use 1,
  simp,
end

lemma idk (I J : ring.fractional_ideal g) : (I/J).val = I.val / J.val :=
begin
  by_cases J=0,
  subst J,
  unfold has_div.div,
  simp,
  sorry,
  sorry,
end

lemma work (I J : ring.fractional_ideal g) : I/J = I * J⁻¹ :=
begin
  unfold has_div.div,
  split_ifs,
  rw h,
  simp,
  right,
  unfold has_inv.inv,
  unfold has_div.div,
  split_ifs,
  assumption,

  exfalso,
  simp at h_1,
  assumption,

  ext x,
  unfold has_inv.inv,
  unfold has_div.div,
  split_ifs,
  split,

  rintros h,
  simp at *,

  sorry,
  sorry,
end

@[simp] lemma coe_one : (1 : fractional_ideal K g).1 = 1 := rfl

lemma mul_one' (I : ring.fractional_ideal g) : I = I * 1 :=
begin
  simp only [mul_one],
end

noncomputable instance fractional_ideal_has_div :
  has_div (fractional_ideal K g) :=
begin
  constructor,
  rintros I J,
  use I.1 / J.1,
  sorry,
--  by_contra,
--  simp at a,
--  rw submodule.ext at a,

--  apply left_ne_zero_of_mul I.1 J.1,

--  cases I with I1 I2,
--  apply I2,
--  simp at a,
--  rw <-mul_left_cancel_iff (ring.fractional_ideal g) J.1 (I1 / ↑J) 0 at a,
--  rw subtype.ext_iff_val at a,
--  rw subtype.val_eq_coe at a,
--  rw subtype.val_eq_coe at a,
--  simp at *,

--  rw mul_left_inj J.1.1 _ _ at a,
end

noncomputable instance : has_inv (fractional_ideal K g) := ⟨λ I, 1 / I⟩

lemma pls_work (I : ring.fractional_ideal g) (h : I ≠ 0) : I * (1 / I) = 1 :=
begin
  rw [ring.fractional_ideal.div_nonzero h],
  apply le_antisymm,
  {
    apply submodule.mul_le.mpr _,
    intros x hx y hy,
    rw [mul_comm],
    sorry,
--    exact submodule.mem_div_iff_forall_mul_mem.mp hy x hx,
  },
  {
    sorry,
  },
end

instance is_group : group (fractional_ideal K g) :=
begin
  constructor,
  {
    rintros a,
    rw subtype.ext_iff_val,
    rw blossom,
    have h : a⁻¹.val = a.val⁻¹,
    split,
    rw h,
    rw coe_one,
    unfold has_inv.inv,
    simp,

    sorry,

--    rw inv_mul_eq_one,
--    apply ring.fractional_ideal.coe_inv_of_nonzero,

--    use a.2,
  },
  {
    rintros a b c,
    rw subtype.ext_iff_val,
    repeat{rw blossom},
    rw subtype.ext_iff_val,
    repeat{rw blossom'},
    rw submodule.mul_assoc,
  },
  {
    rintros a,
    rw subtype.ext_iff_val,
    rw subtype.ext_iff_val,
    simp,
    cases a,
    sorry,
  },
  {
    rintros a,
    sorry,
  },
end

def principal_fractional_ideal : subgroup (fractional_ideal K g) :=
{
  carrier := { P : fractional_ideal K g | ∃ a : K, P.1 = ring.fractional_ideal.span_singleton a },
  one_mem' := sorry,
  mul_mem' := sorry,
  inv_mem' := sorry,
}

def class_group := quotient_group.quotient (principal_fractional_ideal K g)

instance class_number_is_finite : fintype (class_group K g) :=
begin
  sorry,
end

def class_number := fintype.card (class_group K g)

-- def equiv (I J : ring.fractional_ideal g) : Prop := ∃ a : number_ring K, (ideal.span{a})*I = J

-- theorem symmetricity : symmetric (equiv g) :=


def gal_ext (F L : Type*) [field F] [field L] [algebra F L] := (is_separable F L) ∧ (normal F L)

def gal_grp (F L : Type*) [field F] [field L] [algebra F L] : (Type : Type 1) := {σ : ring_aut L | ∀ x : F, σ (x • (1:L)) = (x • (1:L)) }

class zp_ext (L : Type*) [field L] (p : ℕ) [fact p.prime] ( h : ℕ → set L ) :=
( blah2 : ∀ i : ℕ, number_field (h i) )
( blah : ∀ i j : ℕ, i < j ↔ (h i) ⊂ (h j) )
( blah4 : ∀ i : ℕ, algebra (h 0) (h i) )
( blah3 : ∀ i : ℕ, gal_ext (h 0) (h i) )
( blah5 : ∀ i : ℕ, gal_grp (h 0) (h i) = zmod (p^i) )
( blah6 : L = ⋃ (i : ℕ), (h i) )

instance nth_ext (L : Type*) [field L] (p : ℕ) ( n : ℕ ) [fact p.prime] ( h : ℕ → set L ) [ zp_ext L p h ] : number_field (h n) := zp_ext.blah2 p n

variables {p : ℕ} [fact p.prime]

variables (L : Type 0) [field L] ( h : ℕ → set L ) [zp_ext L p h] (n : ℕ) [ gn : (fraction_map (number_ring (h n)) (h n) ) ]

instance any_ext : ∀ m : ℕ, number_field (h m) :=
begin
  sorry,
end

lemma ne : ∀ m : ℕ, nonempty ( fraction_map (number_ring (h m)) (h m) ) :=
begin
  sorry,
end

def class_no_tower' : ℕ → ℕ := λ m, class_number (h m) (classical.choice (ne L h m) )

-- def nth_class_no_for_tower : ℕ := class_number (h n) gn

theorem main : ∃ N : ℕ, ∀ m ≥ N, ∃ a b c : ℕ, padic_val_rat p (class_number (h m) (classical.choice (ne L h m) ) ) = a*p^m + b*m + c :=
begin
sorry,
end

-- def class_no_tower : ℕ → ℕ := λ n, (nth_class_no_for_tower L h n gn)

-- (localization_map (non_zero_divisors (number_ring (h n)) ) : fraction_map (number_ring (h n)) (h n) )
-- theorem main (L : Type*) [field L] ( h : ℕ → set L ) [zp_ext L p h] [∀ n : ℕ, number_field (h n)] [f : en = class_number (h n) _ ]

end number_field
