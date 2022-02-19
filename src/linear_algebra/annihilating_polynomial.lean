import data.polynomial
import ring_theory.principal_ideal_domain
import algebra.module.linear_map
import field_theory.minpoly
import linear_algebra
import ring_theory.ideal.operations
import ring_theory.polynomial_algebra

namespace alg_hom

variables {R A B : Type*}
variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

lemma same_value (f: A →ₐ[R] B) (a: A) : f a = f.to_ring_hom a := rfl

end alg_hom

variables {A M B : Type*}

variables [comm_ring A] [add_comm_group M] [module A M]

/- An A-module endomorphism u gives an ideal in the polynomial algebra

{ p ∈ A[x] | p(u) = 0 }, where p(u) is defined using polynomial.aeval -/
noncomputable def annihilating_ideal (u: M →ₗ[A] M) : ideal (polynomial A) :=
  ring_hom.ker (polynomial.aeval u).to_ring_hom

lemma mem_annihilating_ideal_iff_aeval_0 (u: M →ₗ[A] M) (p: polynomial A)
 : (p ∈ annihilating_ideal u) ↔ (polynomial.aeval u) p = 0 :=
begin
  split,
  intros hp,
  exact (ring_hom.mem_ker (polynomial.aeval u).to_ring_hom).2 hp,
  intros hup0,
  exact (ring_hom.mem_ker (polynomial.aeval u).to_ring_hom).1 hup0,
end

variables {𝕜 V: Type*}
variables [field 𝕜] [add_comm_group V] [module 𝕜 V]

/-- Since `𝕜[x]` is a principal ideal domain there is a polynomial `g` such that
 `span 𝕜 {g} = annihilating_ideal u` -/
noncomputable def annihilating_ideal_generator (u: V →ₗ[𝕜] V) : polynomial 𝕜 :=
  submodule.is_principal.generator (annihilating_ideal u)

lemma annihilating_ideal_generator_aeval_0 (u: V →ₗ[𝕜] V) :
 polynomial.aeval u (annihilating_ideal_generator u) = 0 :=
begin
  rw alg_hom.same_value,
  rw annihilating_ideal_generator,
  let gen_u_member: _ := submodule.is_principal.generator_mem (annihilating_ideal u),
  exact (ring_hom.mem_ker (polynomial.aeval u).to_ring_hom).1 gen_u_member,
end

lemma mem_iff_generator_dvd (u: V →ₗ[𝕜] V) (p : polynomial 𝕜) :
 p ∈ annihilating_ideal u ↔ annihilating_ideal_generator u ∣ p :=
 submodule.is_principal.mem_iff_generator_dvd (annihilating_ideal u)

lemma non_zero_gen_of_non_zero_mem (u: V →ₗ[𝕜] V) (p: polynomial 𝕜) (g: polynomial 𝕜) :
  p ∈ annihilating_ideal u → (p ≠ 0) → (g = annihilating_ideal_generator u) → g ≠ 0 :=
begin
  intros hp pnz hg,
  by_contradiction,
  cases (mem_iff_generator_dvd u p).1 hp with q hq,
  rw ← hg at hq,
  rw h at hq,
  rw zero_mul at hq,
  exact pnz hq,
end

lemma mem_iff_deg_ge_deg_generator (u: V →ₗ[𝕜] V) (p: polynomial 𝕜) (g: polynomial 𝕜) :
  p ∈ annihilating_ideal u → (p ≠ 0) → (g = annihilating_ideal_generator u) →
  polynomial.degree p ≥ polynomial.degree g :=
begin
  intros hp hpnz hg,
  norm_num,
  apply polynomial.degree_le_of_dvd hpnz,
  cases (mem_iff_generator_dvd u p).1 hp with q hpgq,
  rw ← hg at hpgq,
  exact dvd.intro q (eq.symm hpgq),
end

lemma minpoly_eq_monic_annihilating_ideal_generator (u: V →ₗ[𝕜] V) (g: polynomial 𝕜) :
  (g = annihilating_ideal_generator u) → (g.monic) →
  g = minpoly 𝕜 u :=
begin
  intros hg hgm,
  apply minpoly.unique,
  { apply hgm, },
  { rw hg,
    apply annihilating_ideal_generator_aeval_0, },
  { intros q hqm heval,
    apply mem_iff_deg_ge_deg_generator u,
    exact (mem_annihilating_ideal_iff_aeval_0 u q).2 heval,
    exact polynomial.monic.ne_zero hqm,
    apply hg, },
end
