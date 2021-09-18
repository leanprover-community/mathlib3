/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.direct_limit
import field_theory.is_alg_closed.basic

/-!
# Algebraically Closed Field

In this file we define the typeclass for algebraically closed fields and algebraic closures,
and prove some of their properties.

## Main Definitions

- `is_alg_closed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
polynomial in `k` splits.

- `is_alg_closure k K` is the typeclass saying `K` is an algebraic closure of `k`.

- `is_alg_closed.lift` is a map from an algebraic extension `L` of `K`, into any algebraically
  closed extension of `K`.

## TODO

Show that any two algebraic closures are isomorphic

## Tags

algebraic closure, algebraically closed

-/
universes u v w
noncomputable theory
open_locale classical big_operators
open polynomial

variables (k : Type u) [field k]

namespace algebraic_closure

open mv_polynomial

/-- The subtype of monic irreducible polynomials -/
@[reducible] def monic_irreducible : Type u :=
{ f : polynomial k // monic f ∧ irreducible f }

/-- Sends a monic irreducible polynomial `f` to `f(x_f)` where `x_f` is a formal indeterminate. -/
def eval_X_self (f : monic_irreducible k) : mv_polynomial (monic_irreducible k) k :=
polynomial.eval₂ mv_polynomial.C (X f) f

/-- The span of `f(x_f)` across monic irreducible polynomials `f` where `x_f` is an
indeterminate. -/
def span_eval : ideal (mv_polynomial (monic_irreducible k) k) :=
ideal.span $ set.range $ eval_X_self k

/-- Given a finset of monic irreducible polynomials, construct an algebra homomorphism to the
splitting field of the product of the polynomials sending each indeterminate `x_f` represented by
the polynomial `f` in the finset to a root of `f`. -/
def to_splitting_field (s : finset (monic_irreducible k)) :
  mv_polynomial (monic_irreducible k) k →ₐ[k] splitting_field (∏ x in s, x : polynomial k) :=
mv_polynomial.aeval $ λ f,
  if hf : f ∈ s
  then root_of_splits _
    ((splits_prod_iff _ $ λ (j : monic_irreducible k) _, j.2.2.ne_zero).1
      (splitting_field.splits _) f hf)
    (mt is_unit_iff_degree_eq_zero.2 f.2.2.not_unit)
  else 37

theorem to_splitting_field_eval_X_self {s : finset (monic_irreducible k)} {f} (hf : f ∈ s) :
  to_splitting_field k s (eval_X_self k f) = 0 :=
by { rw [to_splitting_field, eval_X_self, ← alg_hom.coe_to_ring_hom, hom_eval₂,
         alg_hom.coe_to_ring_hom, mv_polynomial.aeval_X, dif_pos hf,
         ← algebra_map_eq, alg_hom.comp_algebra_map],
  exact map_root_of_splits _ _ _ }

theorem span_eval_ne_top : span_eval k ≠ ⊤ :=
begin
  rw [ideal.ne_top_iff_one, span_eval, ideal.span, ← set.image_univ,
    finsupp.mem_span_image_iff_total],
  rintros ⟨v, _, hv⟩,
  replace hv := congr_arg (to_splitting_field k v.support) hv,
  rw [alg_hom.map_one, finsupp.total_apply, finsupp.sum, alg_hom.map_sum, finset.sum_eq_zero] at hv,
  { exact zero_ne_one hv },
  intros j hj,
  rw [smul_eq_mul, alg_hom.map_mul, to_splitting_field_eval_X_self k hj, mul_zero]
end

/-- A random maximal ideal that contains `span_eval k` -/
def max_ideal : ideal (mv_polynomial (monic_irreducible k) k) :=
classical.some $ ideal.exists_le_maximal _ $ span_eval_ne_top k

instance max_ideal.is_maximal : (max_ideal k).is_maximal :=
(classical.some_spec $ ideal.exists_le_maximal _ $ span_eval_ne_top k).1

theorem le_max_ideal : span_eval k ≤ max_ideal k :=
(classical.some_spec $ ideal.exists_le_maximal _ $ span_eval_ne_top k).2

/-- The first step of constructing `algebraic_closure`: adjoin a root of all monic polynomials -/
def adjoin_monic : Type u :=
(max_ideal k).quotient

instance adjoin_monic.field : field (adjoin_monic k) :=
ideal.quotient.field _

instance adjoin_monic.inhabited : inhabited (adjoin_monic k) := ⟨37⟩

/-- The canonical ring homomorphism to `adjoin_monic k`. -/
def to_adjoin_monic : k →+* adjoin_monic k :=
(ideal.quotient.mk _).comp C

instance adjoin_monic.algebra : algebra k (adjoin_monic k) :=
(to_adjoin_monic k).to_algebra

theorem adjoin_monic.algebra_map : algebra_map k (adjoin_monic k) = (ideal.quotient.mk _).comp C :=
rfl

theorem adjoin_monic.is_integral (z : adjoin_monic k) : is_integral k z :=
let ⟨p, hp⟩ := ideal.quotient.mk_surjective z in hp ▸
mv_polynomial.induction_on p (λ x, is_integral_algebra_map) (λ p q, is_integral_add)
  (λ p f ih, @is_integral_mul _ _ _ _ _ _ (ideal.quotient.mk _ _) ih ⟨f, f.2.1,
    by { erw [adjoin_monic.algebra_map, ← hom_eval₂,
              ideal.quotient.eq_zero_iff_mem],
      exact le_max_ideal k (ideal.subset_span ⟨f, rfl⟩) }⟩)

theorem adjoin_monic.exists_root {f : polynomial k} (hfm : f.monic) (hfi : irreducible f) :
  ∃ x : adjoin_monic k, f.eval₂ (to_adjoin_monic k) x = 0 :=
⟨ideal.quotient.mk _ $ X (⟨f, hfm, hfi⟩ : monic_irreducible k),
 by { rw [to_adjoin_monic, ← hom_eval₂, ideal.quotient.eq_zero_iff_mem],
      exact le_max_ideal k (ideal.subset_span $ ⟨_, rfl⟩) }⟩

/-- The `n`th step of constructing `algebraic_closure`, together with its `field` instance. -/
def step_aux (n : ℕ) : Σ α : Type u, field α :=
nat.rec_on n ⟨k, infer_instance⟩ $ λ n ih, ⟨@adjoin_monic ih.1 ih.2, @adjoin_monic.field ih.1 ih.2⟩

/-- The `n`th step of constructing `algebraic_closure`. -/
def step (n : ℕ) : Type u :=
(step_aux k n).1

instance step.field (n : ℕ) : field (step k n) :=
(step_aux k n).2

instance step.inhabited (n) : inhabited (step k n) := ⟨37⟩

/-- The canonical inclusion to the `0`th step. -/
def to_step_zero : k →+* step k 0 :=
ring_hom.id k

/-- The canonical ring homomorphism to the next step. -/
def to_step_succ (n : ℕ) : step k n →+* step k (n + 1) :=
@to_adjoin_monic (step k n) (step.field k n)

instance step.algebra_succ (n) : algebra (step k n) (step k (n + 1)) :=
(to_step_succ k n).to_algebra

theorem to_step_succ.exists_root {n} {f : polynomial (step k n)}
  (hfm : f.monic) (hfi : irreducible f) :
  ∃ x : step k (n + 1), f.eval₂ (to_step_succ k n) x = 0 :=
@adjoin_monic.exists_root _ (step.field k n) _ hfm hfi

/-- The canonical ring homomorphism to a step with a greater index. -/
def to_step_of_le (m n : ℕ) (h : m ≤ n) : step k m →+* step k n :=
{ to_fun := nat.le_rec_on h (λ n, to_step_succ k n),
  map_one' := begin
    induction h with n h ih, { exact nat.le_rec_on_self 1 },
    rw [nat.le_rec_on_succ h, ih, ring_hom.map_one]
  end,
  map_mul' := λ x y, begin
    induction h with n h ih, { simp_rw nat.le_rec_on_self },
    simp_rw [nat.le_rec_on_succ h, ih, ring_hom.map_mul]
  end,
  map_zero' := begin
    induction h with n h ih, { exact nat.le_rec_on_self 0 },
    rw [nat.le_rec_on_succ h, ih, ring_hom.map_zero]
  end,
  map_add' := λ x y, begin
    induction h with n h ih, { simp_rw nat.le_rec_on_self },
    simp_rw [nat.le_rec_on_succ h, ih, ring_hom.map_add]
  end }

@[simp] lemma coe_to_step_of_le (m n : ℕ) (h : m ≤ n) :
  (to_step_of_le k m n h : step k m → step k n) = nat.le_rec_on h (λ n, to_step_succ k n) :=
rfl

instance step.algebra (n) : algebra k (step k n) :=
(to_step_of_le k 0 n n.zero_le).to_algebra

instance step.scalar_tower (n) : is_scalar_tower k (step k n) (step k (n + 1)) :=
is_scalar_tower.of_algebra_map_eq $ λ z,
  @nat.le_rec_on_succ (step k) 0 n n.zero_le (n + 1).zero_le (λ n, to_step_succ k n) z

theorem step.is_integral (n) : ∀ z : step k n, is_integral k z :=
nat.rec_on n (λ z, is_integral_algebra_map) $ λ n ih z,
  is_integral_trans ih _ (adjoin_monic.is_integral (step k n) z : _)

instance to_step_of_le.directed_system :
  directed_system (step k) (λ i j h, to_step_of_le k i j h) :=
⟨λ i x h, nat.le_rec_on_self x, λ i₁ i₂ i₃ h₁₂ h₂₃ x, (nat.le_rec_on_trans h₁₂ h₂₃ x).symm⟩

end algebraic_closure

/-- The canonical algebraic closure of a field, the direct limit of adding roots to the field for
each polynomial over the field. -/
def algebraic_closure : Type u :=
ring.direct_limit (algebraic_closure.step k) (λ i j h, algebraic_closure.to_step_of_le k i j h)

namespace algebraic_closure

instance : field (algebraic_closure k) :=
field.direct_limit.field _ _

instance : inhabited (algebraic_closure k) := ⟨37⟩

/-- The canonical ring embedding from the `n`th step to the algebraic closure. -/
def of_step (n : ℕ) : step k n →+* algebraic_closure k :=
ring.direct_limit.of _ _ _

instance algebra_of_step (n) : algebra (step k n) (algebraic_closure k) :=
(of_step k n).to_algebra

theorem of_step_succ (n : ℕ) : (of_step k (n + 1)).comp (to_step_succ k n) = of_step k n :=
ring_hom.ext $ λ x, show ring.direct_limit.of (step k) (λ i j h, to_step_of_le k i j h) _ _ = _,
  by { convert ring.direct_limit.of_f n.le_succ x, ext x, exact (nat.le_rec_on_succ' x).symm }

theorem exists_of_step (z : algebraic_closure k) : ∃ n x, of_step k n x = z :=
ring.direct_limit.exists_of z

-- slow
theorem exists_root {f : polynomial (algebraic_closure k)}
  (hfm : f.monic) (hfi : irreducible f) :
  ∃ x : algebraic_closure k, f.eval x = 0 :=
begin
  have : ∃ n p, polynomial.map (of_step k n) p = f,
  { convert ring.direct_limit.polynomial.exists_of f },
  unfreezingI { obtain ⟨n, p, rfl⟩ := this },
  rw monic_map_iff at hfm,
  have := hfm.irreducible_of_irreducible_map (of_step k n) p hfi,
  obtain ⟨x, hx⟩ := to_step_succ.exists_root k hfm this,
  refine ⟨of_step k (n + 1) x, _⟩,
  rw [← of_step_succ k n, eval_map, ← hom_eval₂, hx, ring_hom.map_zero]
end

instance : is_alg_closed (algebraic_closure k) :=
is_alg_closed.of_exists_root _ $ λ f, exists_root k

instance {R : Type*} [comm_semiring R] [alg : algebra R k] :
  algebra R (algebraic_closure k) :=
((of_step k 0).comp (@algebra_map _ _ _ _ alg)).to_algebra

lemma algebra_map_def {R : Type*} [comm_semiring R] [alg : algebra R k] :
  algebra_map R (algebraic_closure k) = ((of_step k 0 : k →+* _).comp (@algebra_map _ _ _ _ alg)) :=
rfl

instance {R S : Type*} [comm_semiring R] [comm_semiring S]
  [algebra R S] [algebra S k] [algebra R k] [is_scalar_tower R S k] :
  is_scalar_tower R S (algebraic_closure k) :=
is_scalar_tower.of_algebra_map_eq (λ x,
  ring_hom.congr_arg _ (is_scalar_tower.algebra_map_apply R S k x : _))

/-- Canonical algebra embedding from the `n`th step to the algebraic closure. -/
def of_step_hom (n) : step k n →ₐ[k] algebraic_closure k :=
{ commutes' := λ x, ring.direct_limit.of_f n.zero_le x,
  .. of_step k n }

theorem is_algebraic : algebra.is_algebraic k (algebraic_closure k) :=
λ z, (is_algebraic_iff_is_integral _).2 $ let ⟨n, x, hx⟩ := exists_of_step k z in
hx ▸ is_integral_alg_hom (of_step_hom k n) (step.is_integral k n x)

instance : is_alg_closure k (algebraic_closure k) :=
⟨algebraic_closure.is_alg_closed k, is_algebraic k⟩

end algebraic_closure

/--
Every element `f` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `K`
has non-empty spectrum:
that is, there is some `c : K` so `f - c • 1` is not invertible.
-/
-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
lemma exists_spectrum_of_is_alg_closed_of_finite_dimensional (𝕜 : Type*) [field 𝕜] [is_alg_closed 𝕜]
  {A : Type*} [nontrivial A] [ring A] [algebra 𝕜 A] [I : finite_dimensional 𝕜 A] (f : A) :
  ∃ c : 𝕜, ¬ is_unit (f - algebra_map 𝕜 A c) :=
begin
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := is_integral_of_noetherian I f,
  have nu : ¬ is_unit (aeval f p), { rw [←aeval_def] at h_eval_p, rw h_eval_p, simp, },
  rw [eq_prod_roots_of_monic_of_splits_id h_mon (is_alg_closed.splits p),
    ←multiset.prod_to_list, alg_hom.map_list_prod] at nu,
  replace nu := mt list.prod_is_unit nu,
  simp only [not_forall, exists_prop, aeval_C, multiset.mem_to_list,
    list.mem_map, aeval_X, exists_exists_and_eq_and, multiset.mem_map, alg_hom.map_sub] at nu,
  exact ⟨nu.some, nu.some_spec.2⟩,
end
