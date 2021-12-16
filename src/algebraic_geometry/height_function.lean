import data.real.basic
import algebra.category.Group.abelian
import group_theory.finiteness
import data.set.finite
import some_lemmas

noncomputable theory

open_locale classical pointwise big_operators
open finset

universe u

variable (A : Ab.{u})

structure height_function :=
(to_fun : A → ℝ)
(nonneg : ∀ P, 0 ≤ to_fun P)
(C1 : A → ℝ) (C1_nonneg : ∀ a, 0 ≤ C1 a)
(height_add_le : ∀ (Q P : A), to_fun (P + Q) ≤ 2 * to_fun P + C1 Q)
(m : ℕ)
(hm : 2 ≤ m)
(C2 : ℝ) (C2_nonneg : 0 ≤ C2)
(height_nsmul_ge : ∀ (P : A), ↑m^2 * to_fun P - C2 ≤ to_fun (m • P))
(finite : ∀ (C : ℝ), set.finite { P : A | to_fun P < C })

lemma height_function.height_nsmul_ge' (f : height_function A) :
  ∀ P : A, f.to_fun P ≤ (f.m^2)⁻¹ * (f.to_fun (f.m • P) + f.C2) := λ P,
have ineq1 : _ := f.height_nsmul_ge P,
begin
  rw [sub_le_iff_le_add] at ineq1,
  rwa [←inv_mul_le_iff, inv_inv₀],
  rw [inv_pos],
  apply pow_pos, norm_cast, linarith [f.hm],
end

lemma height_function.height_sub_le (f : height_function A) :
  ∀ (Q P : A), f.to_fun (P - Q) ≤ 2 * f.to_fun P + f.C1 (- Q) := λ Q P,
have ineq1 : _ := f.height_add_le (-Q) P,
begin
  rw [sub_eq_add_neg],
  exact ineq1,
end



variables (m : ℕ)
local notation A`/`m := A⧸(m • (⊤ : add_subgroup A))

variable [fin_quot : fintype (A/m)]
include fin_quot
def represents : finset A :=
  image (λ (q : A/m), Exists.some (add_mk_surjective A _ q))
    (fin_quot.elems)

variables {A}
lemma represents_represent_A_quot_mA :
  ∀ (a : A/m), ∃ (q : A), q ∈ represents A m ∧ quotient_add_group.mk q = a := λ a,
begin
  have mem1 : a ∈ fin_quot.elems := fintype.complete a,
    have mem2 : Exists.some (add_mk_surjective A _ a) ∈ represents A m,
      rw [represents, mem_image], use a, refine ⟨mem1, rfl⟩,
    refine ⟨_, mem2, _⟩,
    exact Exists.some_spec (add_mk_surjective A _ a)
end

def new_aux (P : A) : ∃ (p : A × represents A m), P = m • p.1 + p.2 :=
have mem1 : quotient_add_group.mk P ∈ fin_quot.elems, from fintype.complete _,
begin
  obtain ⟨a, ha1, ha2⟩ := represents_represent_A_quot_mA m (quotient_add_group.mk P),
  rw [quotient_add_group.eq', mem_smul A m ⊤] at ha2,
  obtain ⟨q, hq⟩ := ha2,
  refine ⟨⟨q, ⟨a, ha1⟩⟩, _⟩, dsimp only,
  rw [←hq, add_assoc, add_comm P, ←add_assoc, ←subtype.val_eq_coe, neg_add_self, zero_add],
end

abbreviation next (P : A) : A := (Exists.some (new_aux m P)).1
abbreviation next_rep (P : A) : represents A m := (Exists.some (new_aux m P)).2
abbreviation next_prop (P : A) := Exists.some_spec (new_aux m P)
lemma property_next (P : A) : m • (next m P) = P - (next_rep m P) :=
suffices h : P = m • (next m P) + (next_rep m P), by rw [eq_sub_iff_add_eq, ←h],
by convert next_prop m P

variable (f : height_function A)
omit fin_quot

variables [fin_quot_f : fintype (A/f.m)] [non_empty_quot_f : nonempty (A/f.m)]
include fin_quot_f non_empty_quot_f

lemma nemp1 : (image (λ a, f.C1 (-a)) (represents A f.m)).nonempty :=
begin
  apply non_empty_quot_f.elim, intro a,
  simp_rw [finset.nonempty, mem_image],
  obtain ⟨x, hx⟩ := represents_represent_A_quot_mA f.m a,
  use f.C1 (- x), use x, refine ⟨hx.1, rfl⟩,
end

def C1' : ℝ :=
finset.max' (image (λ a, f.C1 (-a)) (represents A f.m)) (nemp1 f)

lemma C1'_is_max :
  ∀ (a : represents A f.m), (f.C1 (-a)) ≤ C1' f := λ a,
begin
  unfold C1',
  apply finset.le_max' (image (λ a, f.C1 (-a)) (represents A f.m)),
  rw [mem_image], use a, refine ⟨a.2, rfl⟩,
end

lemma C1'_nonneg : 0 ≤ C1' f :=
have H : _ := nemp1 f,
begin
  rw finset.nonempty at H,
  obtain ⟨x, hx⟩ := H,
  rw mem_image at hx,
  obtain ⟨a, ha1, ha2⟩ := hx,
  refine le_trans _ (C1'_is_max f ⟨a, ha1⟩),
  apply f.C1_nonneg,
end

lemma property_next_height (P : A) :
  f.to_fun (next f.m P) ≤ (f.m ^ 2)⁻¹ * (2 * f.to_fun P + C1' f + f.C2) :=
have ineq1 : _ := height_function.height_nsmul_ge' A f (next f.m P),
have ineq2 : _ := height_function.height_sub_le A f (next_rep f.m P) P,
have ineq3 : 2 * f.to_fun P + f.C1 (-(next_rep f.m P)) ≤ 2 * f.to_fun P + C1' f,
begin
  apply add_le_add, refl, apply C1'_is_max,
end,
have ineq4 : f.to_fun (P - (next_rep f.m P)) ≤ 2 * f.to_fun P + C1' f, from le_trans ineq2 ineq3,
begin
  refine le_trans ineq1 _,
  rw [mul_add, mul_add], apply add_le_add,
  apply mul_le_mul, refl, refine le_trans _ ineq4,
  rw property_next, apply f.nonneg,
  rw inv_nonneg, norm_cast, apply pow_nonneg (show 0 ≤ f.m, by linarith) 2,
  refl
end

lemma property_next_height_iterated (P : A) (n : ℕ) :
  f.to_fun ((next f.m)^[n.succ] P) ≤
  2^n.succ * ((f.m^2)⁻¹)^n.succ * f.to_fun P +
  (f.m^2)⁻¹ * (∑ i in finset.range n.succ,2^(i+1)) * (C1' f + f.C2) :=
have ineq1 : _ := property_next_height f P,
begin
  induction n with n ih,

  { rw [pow_one, function.iterate_one, pow_one, finset.range_one,
      finset.sum_singleton, zero_add, pow_one],
    apply le_trans ineq1, rw [add_assoc, mul_add], apply add_le_add,
    rw ←mul_assoc, apply mul_le_mul, rw mul_comm, refl,
    exact f.nonneg _, apply mul_nonneg, norm_num, rw inv_nonneg,
    norm_cast, apply pow_nonneg, linarith [f.hm], apply mul_le_mul,
    rw le_mul_iff_one_le_right, norm_num,
    rw inv_pos, norm_cast, apply pow_pos, linarith [f.hm], refl,
    apply add_nonneg, exact C1'_nonneg f, exact f.C2_nonneg,
    apply mul_nonneg, rw inv_nonneg, norm_cast, apply pow_nonneg, linarith [f.hm], norm_num, },

  { have ineq2 := property_next_height f ((next f.m)^[n.succ] P),
    rw [function.iterate_succ'],
    apply le_trans ineq2,
    have ineq3 := mul_le_mul (show (2 : ℝ) ≤ 2, by refl) ih (f.nonneg _) (by norm_num),
    rw [mul_add, ←mul_assoc, ←mul_assoc, show (2 : ℝ) * 2^n.succ = 2^n.succ.succ, by sorry,
      ←mul_assoc, ←mul_assoc, mul_comm (2 : ℝ) ((f.m) ^ 2)⁻¹, mul_assoc (↑(f.m) ^ 2)⁻¹,
      finset.mul_sum] at ineq3,
    have ineq4 := add_le_add ineq3 (show C1' f + f.C2 ≤ C1' f + f.C2, by refl),
    rw [←add_assoc] at ineq4,
    sorry }
end

-- lemma property_next_height_iterated (P : A) (n : ℕ) :
--   f.to_fun ((next f.m)^[n.succ] P) ≤ (2^(n.succ))⁻¹ * f.to_fun P + 2⁻¹ * (C1' f + f.C2) :=
-- have ineq1 : _ := property_next_height f P,
-- have ineq2 : 4 ≤ ((f.m : ℝ)^2), begin
--   rw show (4:ℝ) = 2^2, by norm_num, norm_cast,
--   rw nat.pow_le_iff_le_left, exact f.hm, linarith,
-- end,
-- have ineq3 : ((f.m : ℝ)^2)⁻¹ ≤ 4⁻¹, begin
--   rw inv_le_inv, exact ineq2,
--   apply pow_pos, norm_cast, linarith [f.hm], linarith,
-- end,
-- have ineq4 : ((f.m : ℝ) ^ 2)⁻¹ * 2 ≤ 4⁻¹ * 2, begin
--   apply mul_le_mul, exact ineq3, refl, linarith,
--   rw inv_nonneg, linarith,
-- end,
-- begin
--   induction n with n ih,

--   { rw [function.iterate_one, pow_one],
--     apply le_trans ineq1 _,
--     rw [add_assoc, mul_add, ←mul_assoc],
--     apply add_le_add, apply mul_le_mul,
--     apply le_trans ineq4, norm_num, refl,
--     exact f.nonneg _, norm_num,
--     apply mul_le_mul, apply le_trans ineq3,
--     norm_num, refl, sorry,
--     norm_num,
--     -- linarith [ineq3],

--      },
--   {  },
-- end

theorem descent :
  add_subgroup.fg (⊤ : add_subgroup A) :=
begin
  sorry
end
