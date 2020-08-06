import linear_algebra.finite_dimensional
import order.zorn
import ring_theory.fractional_ideal
import ring_theory.polynomial.rational_root
import ring_theory.ideal_over
import set_theory.cardinal
import tactic

/-- A ring `R` is (at most) one-dimensional if all nonzero prime ideals are maximal. -/
def ring.is_one_dimensional (R : Type*) [comm_ring R] :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

lemma principal_ideal_ring.is_one_dimensional (R : Type*) [integral_domain R]
  [is_principal_ideal_ring R] :
  ring.is_one_dimensional R :=
λ p nonzero prime, by { haveI := prime, exact ideal.is_prime.to_maximal_ideal nonzero }

variables {R K : Type*}

lemma integral_closure.is_one_dimensional [comm_ring R] [nontrivial R] [integral_domain K] [algebra R K]
  (h : is_one_dimensional R) :
  is_one_dimensional (integral_closure R K) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end

-- TODO: `class is_dedekind_domain`?
structure is_dedekind_domain [comm_ring R] [comm_ring K] (f : fraction_map R K) :=
(is_one_dimensional : is_one_dimensional R)
(is_noetherian_ring : is_noetherian_ring R)
(is_integrally_closed : integral_closure R f.codomain = ⊥)

lemma integrally_closed_iff_integral_implies_integer
  [comm_ring R] [comm_ring K] {f : fraction_map R K} :
  integral_closure R f.codomain = ⊥ ↔ ∀ x : f.codomain, is_integral R x → f.is_integer x :=
subalgebra.ext_iff.trans
  ⟨ λ h x hx, algebra.mem_bot.mp ((h x).mp hx),
    λ h x, iff.trans
      ⟨λ hx, h x hx, λ ⟨y, hy⟩, hy ▸ is_integral_algebra_map⟩
      (@algebra.mem_bot R f.codomain _ _ _ _).symm⟩

-- TODO: instance instead of def?
def principal_ideal_ring.to_dedekind_domain [integral_domain R] [is_principal_ideal_ring R]
  [field K] (f : fraction_map R K) :
  is_dedekind_domain f :=
{ is_one_dimensional := principal_ideal_ring.is_one_dimensional R,
  is_noetherian_ring := principal_ideal_ring.is_noetherian_ring,
  is_integrally_closed := @unique_factorization_domain.integrally_closed R _ _
    (principal_ideal_ring.to_unique_factorization_domain) _ _}

namespace dedekind_domain

variables {S : Type*} [integral_domain R] [integral_domain S] [algebra R S]
variables {L : Type*} [field K] [field L] {f : fraction_map R K}

open finsupp polynomial

lemma smul_mul_fae (a₁ a₂ : α) (b : β) : b • (a₁ * a₂) = b * a₁ * a₂ :=
by sorry,

lemma smul_mul (a₁ a₂ : f.codomain) (b : R) : b • (a₁ * a₂) = f.to_map b * a₁ * a₂ :=
begin
sorry,
end


lemma maximal_ideal_invertible_of_dedekind (h : is_dedekind_domain f) {M : ideal R}
  (hM : ideal.is_maximal M) : is_unit (M : fractional_ideal f) :=
-- ⟨⟨M, M⁻¹, _, _⟩, rfl⟩
begin
let M1 := {x : K | ∀ y ∈ M, f.is_integer (x * f.to_map y)},
let M1 : fractional_ideal f,
{use M1,
  {intros y h,simp,use 0,simp,},
  {intros a b ha hb,intros y h,rw add_mul a b (f.to_map y),
  apply localization_map.is_integer_add,apply ha,exact h,apply hb,exact h,},
      {intros c x h y h,
      apply smul_mul_fae c},
      exact dec_trivial,
  --    {intros c x h1 y h,
  --    rw algebra.smul_mul_assoc,
  --    apply localization_map.is_integer_smul,
  --    exact h1 y h,},
  --      sorry,
  --with the old version of smul_mul (called now smul_mul_fae), and my code above, no sorry was needed
},
have hprod : ↑M*M1=1,
    -- {have incl : ↑ M < ↑ M*M1, sorry,
    --  have h_Mneq1 : ∀ I : ideal R, M < I →  I = ⊤,
    --     sorry,--exact and.elim_left hM M,
    --     -- specialize h_Mneq1 M*M1,--Lean is complaining because M*M1 is not an ideal in R
    --      sorry,
  {apply le_antisymm,
    {apply fractional_ideal.mul_le.mpr,
      intros y hy x hx,
      have hxy : localization_map.is_integer f (x*y),
        {
        rw fractional_ideal.mem_coe at hy,
        rcases hy with ⟨s,hs⟩,simp * at *,
        rcases hs with ⟨h_s_inM,h_sy⟩,
        subst h_sy,
        exact hx s h_s_inM,
        },
      apply fractional_ideal.mem_one_iff.mpr,
      cases hxy, use hxy_w,
      finish,
    },
    {have incl : ↑ M < ↑ M*M1,
        sorry,
         sorry,},
       },
apply is_unit_of_mul_eq_one ↑M M1 hprod,
end


lemma fractional_ideal_invertible_of_dedekind (h : is_dedekind_domain f) (I : fractional_ideal f) :
  I * I⁻¹ = 1 :=
begin
  sorry
end
-/
/- If L is a finite extension of K, the integral closure of R in L is a Dedekind domain. -/
def closure_in_field_extension [algebra f.codomain L] [algebra R L] [is_algebra_tower R f.codomain L]
  [finite_dimensional f.codomain L] (h : is_dedekind_domain f) :
  is_dedekind_domain (integral_closure.fraction_map_of_finite_extension L f) :=
{ is_noetherian_ring := is_noetherian_ring_of_is_noetherian_coe_submodule _ _ (is_noetherian_of_submodule_of_noetherian _ _ _ _),
  is_one_dimensional := integral_closure.is_one_dimensional h.is_one_dimensional,
  is_integrally_closed := integral_closure_idem }

end dedekind_domain
