import data.real.basic
import algebra.category.Group.abelian
import group_theory.finiteness
import data.set.finite
import some_lemmas

noncomputable theory

open_locale classical pointwise
open finset

universe u

variable (A : Ab.{u})

structure height_function :=
(to_fun : A → ℝ)
(nonneg : ∀ P, 0 ≤ to_fun P)
(C1 : A → ℝ)
(height_add_le : ∀ (Q P : A), to_fun (P + Q) ≤ 2 * to_fun P + C1 Q)
(m : ℕ)
(hm : 2 ≤ m)
(C2 : ℝ)
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

def C1' : ℝ :=
have nemp : (image (λ a, f.C1 (-a)) (represents A f.m)).nonempty, begin
  simp_rw [finset.nonempty, mem_image],
  sorry
end,
finset.max' (image (λ a, f.C1 (-a)) (represents A f.m)) nemp

lemma C1'_is_max :
  ∀ (a : represents A f.m), (f.C1 (-a)) ≤ C1' f :=
begin
  sorry
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

theorem descent :
  add_subgroup.fg (⊤ : add_subgroup A) :=
begin
  sorry
end
