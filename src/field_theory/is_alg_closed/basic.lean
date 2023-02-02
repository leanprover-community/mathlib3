/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import field_theory.perfect_closure
import field_theory.separable
import ring_theory.adjoin.field
import ring_theory.localization.integral

/-!
# Algebraically Closed Field

In this file we define the typeclass for algebraically closed fields and algebraic closures,
and prove some of their properties.

## Main Definitions

- `is_alg_closed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
polynomial in `k` splits.

- `is_alg_closure R K` is the typeclass saying `K` is an algebraic closure of `R`, where `R` is a
  commutative ring. This means that the map from `R` to `K` is injective, and `K` is
  algebraically closed and algebraic over `R`

- `is_alg_closed.lift` is a map from an algebraic extension `L` of `R`, into any algebraically
  closed extension of `R`.

- `is_alg_closure.equiv` is a proof that any two algebraic closures of the
  same field are isomorphic.

## Tags

algebraic closure, algebraically closed

-/
universes u v w

open_locale classical big_operators polynomial
open polynomial

variables (k : Type u) [field k]

/-- Typeclass for algebraically closed fields.

To show `polynomial.splits p f` for an arbitrary ring homomorphism `f`,
see `is_alg_closed.splits_codomain` and `is_alg_closed.splits_domain`.
-/
class is_alg_closed : Prop :=
(splits : ∀ p : k[X], p.splits $ ring_hom.id k)

/-- Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

See also `is_alg_closed.splits_domain` for the case where `K` is algebraically closed.
-/
theorem is_alg_closed.splits_codomain {k K : Type*} [field k] [is_alg_closed k] [field K]
  {f : K →+* k} (p : K[X]) : p.splits f :=
by { convert is_alg_closed.splits (p.map f), simp [splits_map_iff] }

/-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

See also `is_alg_closed.splits_codomain` for the case where `k` is algebraically closed.
-/
theorem is_alg_closed.splits_domain {k K : Type*} [field k] [is_alg_closed k] [field K]
  {f : k →+* K} (p : k[X]) : p.splits f :=
polynomial.splits_of_splits_id _ $ is_alg_closed.splits _

namespace is_alg_closed

variables {k}

theorem exists_root [is_alg_closed k] (p : k[X]) (hp : p.degree ≠ 0) : ∃ x, is_root p x :=
exists_root_of_splits _ (is_alg_closed.splits p) hp

lemma exists_pow_nat_eq [is_alg_closed k] (x : k) {n : ℕ} (hn : 0 < n) : ∃ z, z ^ n = x :=
begin
  rcases exists_root (X ^ n - C x) _ with ⟨z, hz⟩, swap,
  { rw degree_X_pow_sub_C hn x,
    exact ne_of_gt (with_bot.coe_lt_coe.2 hn) },
  use z,
  simp only [eval_C, eval_X, eval_pow, eval_sub, is_root.def] at hz,
  exact sub_eq_zero.1 hz
end

lemma exists_eq_mul_self [is_alg_closed k] (x : k) : ∃ z, x = z * z :=
begin
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩,
  exact ⟨z, sq z⟩
end

lemma roots_eq_zero_iff [is_alg_closed k] {p : k[X]} :
  p.roots = 0 ↔ p = polynomial.C (p.coeff 0) :=
begin
  refine ⟨λ h, _, λ hp, by rw [hp, roots_C]⟩,
  cases (le_or_lt (degree p) 0) with hd hd,
  { exact eq_C_of_degree_le_zero hd },
  { obtain ⟨z, hz⟩ := is_alg_closed.exists_root p hd.ne',
    rw [←mem_roots (ne_zero_of_degree_gt hd), h] at hz,
    simpa using hz }
end

theorem exists_eval₂_eq_zero_of_injective {R : Type*} [ring R] [is_alg_closed k] (f : R →+* k)
  (hf : function.injective f) (p : R[X]) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf]) in
⟨x, by rwa [eval₂_eq_eval_map, ← is_root]⟩

theorem exists_eval₂_eq_zero {R : Type*} [field R] [is_alg_closed k] (f : R →+* k)
  (p : R[X]) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
exists_eval₂_eq_zero_of_injective f f.injective p hp

variables (k)

theorem exists_aeval_eq_zero_of_injective {R : Type*} [comm_ring R] [is_alg_closed k] [algebra R k]
  (hinj : function.injective (algebra_map R k)) (p : R[X]) (hp : p.degree ≠ 0) :
  ∃ x : k, aeval x p = 0 :=
exists_eval₂_eq_zero_of_injective (algebra_map R k) hinj p hp

theorem exists_aeval_eq_zero {R : Type*} [field R] [is_alg_closed k] [algebra R k]
  (p : R[X]) (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
exists_eval₂_eq_zero (algebra_map R k) p hp

theorem of_exists_root (H : ∀ p : k[X], p.monic → irreducible p → ∃ x, p.eval x = 0) :
  is_alg_closed k :=
⟨λ p, or.inr $ λ q hq hqp,
 have irreducible (q * C (leading_coeff q)⁻¹),
   by { rw ← coe_norm_unit_of_ne_zero hq.ne_zero,
        exact (associated_normalize _).irreducible hq },
 let ⟨x, hx⟩ := H (q * C (leading_coeff q)⁻¹) (monic_mul_leading_coeff_inv hq.ne_zero) this in
 degree_mul_leading_coeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root this hx⟩

lemma degree_eq_one_of_irreducible [is_alg_closed k] {p : k[X]}
  (hp : irreducible p) :
  p.degree = 1 :=
degree_eq_one_of_irreducible_of_splits hp (is_alg_closed.splits_codomain _)

lemma algebra_map_surjective_of_is_integral {k K : Type*} [field k] [ring K] [is_domain K]
  [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_integral k K) :
  function.surjective (algebra_map k K) :=
begin
  refine λ x, ⟨-((minpoly k x).coeff 0), _⟩,
  have hq : (minpoly k x).leading_coeff = 1 := minpoly.monic (hf x),
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k
    (minpoly.irreducible (hf x)),
  have : (aeval x (minpoly k x)) = 0 := minpoly.aeval k x,
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul,
    aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at this,
  exact (ring_hom.map_neg (algebra_map k K) ((minpoly k x).coeff 0)).symm ▸ this.symm,
end

lemma algebra_map_surjective_of_is_integral'
  {k K : Type*} [field k] [comm_ring K] [is_domain K]
  [hk : is_alg_closed k] (f : k →+* K) (hf : f.is_integral) : function.surjective f :=
@algebra_map_surjective_of_is_integral k K _ _ _ _ f.to_algebra hf

lemma algebra_map_surjective_of_is_algebraic {k K : Type*} [field k] [ring K] [is_domain K]
  [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_algebraic k K) :
  function.surjective (algebra_map k K) :=
algebra_map_surjective_of_is_integral (algebra.is_algebraic_iff_is_integral.mp hf)

end is_alg_closed

/-- Typeclass for an extension being an algebraic closure. -/
class is_alg_closure (R : Type u) (K : Type v) [comm_ring R]
  [field K] [algebra R K] [no_zero_smul_divisors R K] : Prop :=
(alg_closed : is_alg_closed K)
(algebraic : algebra.is_algebraic R K)

theorem is_alg_closure_iff (K : Type v) [field K] [algebra k K] :
  is_alg_closure k K ↔ is_alg_closed K ∧ algebra.is_algebraic k K :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

namespace lift

/- In this section, the homomorphism from any algebraic extension into an algebraically
  closed extension is proven to exist. The assumption that M is algebraically closed could probably
  easily be switched to an assumption that M contains all the roots of polynomials in K -/
variables {K : Type u} {L : Type v} {M : Type w} [field K] [field L] [algebra K L]
  [field M] [algebra K M] [is_alg_closed M] (hL : algebra.is_algebraic K L)

variables (K L M)
include hL
open subalgebra alg_hom function

/-- This structure is used to prove the existence of a homomorphism from any algebraic extension
into an algebraic closure -/
structure subfield_with_hom :=
(carrier : subalgebra K L)
(emb : carrier →ₐ[K] M)

variables {K L M hL}

namespace subfield_with_hom
variables {E₁ E₂ E₃ : subfield_with_hom K L M hL}

instance : has_le (subfield_with_hom K L M hL) :=
{ le := λ E₁ E₂, ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x }

noncomputable instance : inhabited (subfield_with_hom K L M hL) :=
⟨{ carrier := ⊥,
   emb := (algebra.of_id K M).comp (algebra.bot_equiv K L).to_alg_hom }⟩

lemma le_def : E₁ ≤ E₂ ↔ ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x :=
iff.rfl

lemma compat (h : E₁ ≤ E₂) : ∀ x, E₂.emb (inclusion h.fst x) = E₁.emb x :=
by { rw le_def at h, cases h, assumption }

instance : preorder (subfield_with_hom K L M hL) :=
{ le := (≤),
  le_refl := λ E, ⟨le_rfl, by simp⟩,
  le_trans := λ E₁ E₂ E₃ h₁₂ h₂₃,
    ⟨le_trans h₁₂.fst h₂₃.fst,
    λ _, by erw [← inclusion_inclusion h₁₂.fst h₂₃.fst, compat, compat]⟩ }

open lattice

lemma maximal_subfield_with_hom_chain_bounded (c : set (subfield_with_hom K L M hL))
  (hc : is_chain (≤) c) :
  ∃ ub : subfield_with_hom K L M hL, ∀ N, N ∈ c → N ≤ ub :=
if hcn : c.nonempty then
let ub : subfield_with_hom K L M hL :=
by haveI : nonempty c := set.nonempty.to_subtype hcn; exact
{ carrier := ⨆ i : c, (i : subfield_with_hom K L M hL).carrier,
  emb := subalgebra.supr_lift
    (λ i : c, (i : subfield_with_hom K L M hL).carrier)
    (λ i j, let ⟨k, hik, hjk⟩ := directed_on_iff_directed.1 hc.directed_on i j in
      ⟨k, hik.fst, hjk.fst⟩)
    (λ i, (i : subfield_with_hom K L M hL).emb)
    begin
      assume i j h,
      ext x,
      cases hc.total i.prop j.prop with hij hji,
      { simp [← hij.snd x] },
      { erw [alg_hom.comp_apply, ← hji.snd (inclusion h x),
          inclusion_inclusion, inclusion_self, alg_hom.id_apply x] }
    end _ rfl } in
⟨ub, λ N hN, ⟨(le_supr (λ i : c, (i : subfield_with_hom K L M hL).carrier) ⟨N, hN⟩ : _),
  begin
    intro x,
    simp [ub],
    refl
  end⟩⟩
else by { rw [set.not_nonempty_iff_eq_empty] at hcn, simp [hcn], }

variables (hL M)

lemma exists_maximal_subfield_with_hom : ∃ E : subfield_with_hom K L M hL,
  ∀ N, E ≤ N → N ≤ E :=
exists_maximal_of_chains_bounded
  maximal_subfield_with_hom_chain_bounded (λ _ _ _, le_trans)

/-- The maximal `subfield_with_hom`. We later prove that this is equal to `⊤`. -/
noncomputable def maximal_subfield_with_hom : subfield_with_hom K L M hL :=
classical.some (exists_maximal_subfield_with_hom M hL)

lemma maximal_subfield_with_hom_is_maximal :
  ∀ (N : subfield_with_hom K L M hL),
    (maximal_subfield_with_hom M hL) ≤ N → N ≤ (maximal_subfield_with_hom M hL) :=
classical.some_spec (exists_maximal_subfield_with_hom M hL)

lemma maximal_subfield_with_hom_eq_top :
  (maximal_subfield_with_hom M hL).carrier = ⊤ :=
begin
  rw [eq_top_iff],
  intros x _,
  let p := minpoly K x,
  let N : subalgebra K L := (maximal_subfield_with_hom M hL).carrier,
  letI : field N := (subalgebra.is_field_of_algebraic N hL).to_field,
  letI : algebra N M := (maximal_subfield_with_hom M hL).emb.to_ring_hom.to_algebra,
  cases is_alg_closed.exists_aeval_eq_zero M (minpoly N x)
    (ne_of_gt (minpoly.degree_pos
      (is_algebraic_iff_is_integral.1
        (algebra.is_algebraic_of_larger_base _ _ hL x)))) with y hy,
  let O : subalgebra N L := algebra.adjoin N {(x : L)},
  let larger_emb := ((adjoin_root.lift_hom (minpoly N x) y hy).comp
     (alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly N x).to_alg_hom),
  have hNO : N ≤ O.restrict_scalars K,
  { intros z hz,
    show algebra_map N L ⟨z, hz⟩ ∈ O,
    exact O.algebra_map_mem _ },
  let O' : subfield_with_hom K L M hL :=
  { carrier := O.restrict_scalars K,
    emb := larger_emb.restrict_scalars K },
  have hO' : maximal_subfield_with_hom M hL ≤ O',
  { refine ⟨hNO, _⟩,
    intros z,
    show O'.emb (algebra_map N O z) = algebra_map N M z,
    simp only [O', restrict_scalars_apply, alg_hom.commutes] },
  refine (maximal_subfield_with_hom_is_maximal M hL O' hO').fst _,
  exact algebra.subset_adjoin (set.mem_singleton x),
end

end subfield_with_hom
end lift

namespace is_alg_closed

variables {K : Type u} [field K] {L : Type v} {M : Type w} [field L] [algebra K L]
  [field M] [algebra K M] [is_alg_closed M] (hL : algebra.is_algebraic K L)

variables (K L M)
include hL

/-- Less general version of `lift`. -/
@[irreducible] private noncomputable def lift_aux : L →ₐ[K] M :=
(lift.subfield_with_hom.maximal_subfield_with_hom M hL).emb.comp $
  eq.rec_on (lift.subfield_with_hom.maximal_subfield_with_hom_eq_top M hL).symm algebra.to_top

omit hL

variables {R : Type u} [comm_ring R]
variables {S : Type v} [comm_ring S] [is_domain S] [algebra R S]
  [algebra R M] [no_zero_smul_divisors R S]
  [no_zero_smul_divisors R M]
  (hS : algebra.is_algebraic R S)
variables {M}

include hS

private lemma fraction_ring.is_algebraic :
  by letI : is_domain R := (no_zero_smul_divisors.algebra_map_injective R S).is_domain _; exact
  algebra.is_algebraic (fraction_ring R) (fraction_ring S) :=
begin
  introsI inst x,
  exact (is_fraction_ring.is_algebraic_iff R (fraction_ring R) (fraction_ring S)).1
    ((is_fraction_ring.is_algebraic_iff' R S (fraction_ring S)).1 hS x)
end

/-- A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R. -/
@[irreducible] noncomputable def lift : S →ₐ[R] M :=
begin
  letI : is_domain R := (no_zero_smul_divisors.algebra_map_injective R S).is_domain _,
  have hfRfS : algebra.is_algebraic (fraction_ring R) (fraction_ring S) :=
    fraction_ring.is_algebraic hS,
  let f : fraction_ring S →ₐ[fraction_ring R] M :=
    lift_aux (fraction_ring R) (fraction_ring S) M hfRfS,
  exact (f.restrict_scalars R).comp ((algebra.of_id S (fraction_ring S)).restrict_scalars R),
end

omit hS
@[priority 100]
noncomputable instance perfect_ring (p : ℕ) [fact p.prime] [char_p k p]
  [is_alg_closed k] : perfect_ring k p :=
perfect_ring.of_surjective k p $ λ x, is_alg_closed.exists_pow_nat_eq _ $ ne_zero.pos p

/-- Algebraically closed fields are infinite since `Xⁿ⁺¹ - 1` is separable when `#K = n` -/
@[priority 500]
instance {K : Type*} [field K] [is_alg_closed K] : infinite K :=
begin
  apply infinite.of_not_fintype,
  introsI hfin,
  set n := fintype.card K with hn,
  set f := (X : K[X]) ^ (n + 1) - 1 with hf,
  have hfsep : separable f := separable_X_pow_sub_C 1 (by simp) one_ne_zero,
  apply nat.not_succ_le_self (fintype.card K),
  have hroot : n.succ = fintype.card (f.root_set K),
  { erw [card_root_set_eq_nat_degree hfsep (is_alg_closed.splits_domain _),
         nat_degree_X_pow_sub_C] },
  rw hroot,
  exact fintype.card_le_of_injective coe subtype.coe_injective,
end

end is_alg_closed

namespace is_alg_closure

variables (K : Type*) (J : Type*) (R : Type u) (S : Type*) [field K] [field J] [comm_ring R]
  (L : Type v) (M : Type w) [field L] [field M] [algebra R M] [no_zero_smul_divisors R M]
  [is_alg_closure R M] [algebra K M] [is_alg_closure K M]
  [comm_ring S] [algebra S L] [no_zero_smul_divisors S L] [is_alg_closure S L]

local attribute [instance] is_alg_closure.alg_closed

section
variables [algebra R L] [no_zero_smul_divisors R L] [is_alg_closure R L]

/-- A (random) isomorphism between two algebraic closures of `R`. -/
noncomputable def equiv : L ≃ₐ[R] M :=
let f : L →ₐ[R] M := is_alg_closed.lift is_alg_closure.algebraic in
alg_equiv.of_bijective f
  ⟨ring_hom.injective f.to_ring_hom,
    begin
      letI : algebra L M := ring_hom.to_algebra f,
      letI : is_scalar_tower R L M :=
        is_scalar_tower.of_algebra_map_eq (by simp [ring_hom.algebra_map_to_algebra]),
      show function.surjective (algebra_map L M),
      exact is_alg_closed.algebra_map_surjective_of_is_algebraic
        (algebra.is_algebraic_of_larger_base_of_injective
          (no_zero_smul_divisors.algebra_map_injective R _) is_alg_closure.algebraic),
    end⟩

end

section equiv_of_algebraic

variables [algebra R S] [algebra R L] [is_scalar_tower R S L]
variables [algebra K J] [algebra J L] [is_alg_closure J L] [algebra K L]
  [is_scalar_tower K J L]


/-- A (random) isomorphism between an algebraic closure of `R` and an algebraic closure of
  an algebraic extension of `R` -/
noncomputable def equiv_of_algebraic' [nontrivial S] [no_zero_smul_divisors R S]
  (hRL : algebra.is_algebraic R L) : L ≃ₐ[R] M :=
begin
  letI : no_zero_smul_divisors R L :=
    no_zero_smul_divisors.of_algebra_map_injective begin
      rw [is_scalar_tower.algebra_map_eq R S L],
      exact function.injective.comp
        (no_zero_smul_divisors.algebra_map_injective _ _)
        (no_zero_smul_divisors.algebra_map_injective _ _)
    end,
  letI : is_alg_closure R L :=
  { alg_closed := by apply_instance,
    algebraic := hRL },
  exact is_alg_closure.equiv _ _ _
end

/-- A (random) isomorphism between an algebraic closure of `K` and an algebraic closure
  of an algebraic extension of `K` -/
noncomputable def equiv_of_algebraic (hKJ : algebra.is_algebraic K J) : L ≃ₐ[K] M :=
equiv_of_algebraic' K J _ _ (algebra.is_algebraic_trans hKJ is_alg_closure.algebraic)

end equiv_of_algebraic

section equiv_of_equiv

variables {R S}

/-- Used in the definition of `equiv_of_equiv` -/
noncomputable def equiv_of_equiv_aux (hSR : S ≃+* R) :
  { e : L ≃+* M // e.to_ring_hom.comp (algebra_map S L) =
    (algebra_map R M).comp hSR.to_ring_hom }:=
begin
  letI : algebra R S := ring_hom.to_algebra hSR.symm.to_ring_hom,
  letI : algebra S R := ring_hom.to_algebra hSR.to_ring_hom,
  letI : is_domain R := (no_zero_smul_divisors.algebra_map_injective R M).is_domain _,
  letI : is_domain S := (no_zero_smul_divisors.algebra_map_injective S L).is_domain _,
  have : algebra.is_algebraic R S,
    from λ x, begin
      rw [← ring_equiv.symm_apply_apply hSR x],
      exact is_algebraic_algebra_map _
    end,
  letI : algebra R L := ring_hom.to_algebra ((algebra_map S L).comp (algebra_map R S)),
  haveI : is_scalar_tower R S L := is_scalar_tower.of_algebra_map_eq (λ _, rfl),
  haveI : is_scalar_tower S R L := is_scalar_tower.of_algebra_map_eq
    (by simp [ring_hom.algebra_map_to_algebra]),
  haveI : no_zero_smul_divisors R S :=
    no_zero_smul_divisors.of_algebra_map_injective hSR.symm.injective,
  refine ⟨equiv_of_algebraic' R S L M (algebra.is_algebraic_of_larger_base_of_injective
      (show function.injective (algebra_map S R), from hSR.injective)
      is_alg_closure.algebraic) , _⟩,
  ext,
  simp only [ring_equiv.to_ring_hom_eq_coe, function.comp_app, ring_hom.coe_comp,
    alg_equiv.coe_ring_equiv, ring_equiv.coe_to_ring_hom],
  conv_lhs { rw [← hSR.symm_apply_apply x] },
  show equiv_of_algebraic' R S L M _ (algebra_map R L (hSR x)) = _,
  rw [alg_equiv.commutes]
end

/-- Algebraic closure of isomorphic fields are isomorphic -/
noncomputable def equiv_of_equiv (hSR : S ≃+* R) : L ≃+* M :=
equiv_of_equiv_aux L M hSR

@[simp] lemma equiv_of_equiv_comp_algebra_map (hSR : S ≃+* R) :
  (↑(equiv_of_equiv L M hSR) : L →+* M).comp (algebra_map S L) =
  (algebra_map R M).comp hSR :=
(equiv_of_equiv_aux L M hSR).2

@[simp] lemma equiv_of_equiv_algebra_map (hSR : S ≃+* R) (s : S):
  equiv_of_equiv L M hSR (algebra_map S L s) =
  algebra_map R M (hSR s) :=
ring_hom.ext_iff.1 (equiv_of_equiv_comp_algebra_map L M hSR) s

@[simp] lemma equiv_of_equiv_symm_algebra_map (hSR : S ≃+* R) (r : R):
  (equiv_of_equiv L M hSR).symm (algebra_map R M r) =
  algebra_map S L (hSR.symm r) :=
(equiv_of_equiv L M hSR).injective (by simp)

@[simp] lemma equiv_of_equiv_symm_comp_algebra_map (hSR : S ≃+* R) :
  ((equiv_of_equiv L M hSR).symm : M →+* L).comp (algebra_map R M) =
  (algebra_map S L).comp hSR.symm :=
ring_hom.ext_iff.2 (equiv_of_equiv_symm_algebra_map L M hSR)

end equiv_of_equiv

end is_alg_closure

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K/F` an algebraic extension
  of fields. Then the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
  the roots in `A` of the minimal polynomial of `x` over `F`. -/
lemma algebra.is_algebraic.range_eval_eq_root_set_minpoly {F K} (A) [field F] [field K] [field A]
  [is_alg_closed A] [algebra F K] (hK : algebra.is_algebraic F K) [algebra F A] (x : K) :
  set.range (λ ψ : K →ₐ[F] A, ψ x) = (minpoly F x).root_set A :=
begin
  have := algebra.is_algebraic_iff_is_integral.1 hK,
  ext a, rw [mem_root_set_of_ne (minpoly.ne_zero (this x))]; [skip, apply_instance],
  refine ⟨_, λ ha, _⟩,
  { rintro ⟨ψ, rfl⟩, rw [aeval_alg_hom_apply ψ x, minpoly.aeval, map_zero] },
  let Fx := adjoin_root (minpoly F x),
  have hx : aeval x (minpoly F x) = 0 := minpoly.aeval F x,
  letI : algebra Fx A := (adjoin_root.lift (algebra_map F A) a ha).to_algebra,
  letI : algebra Fx K := (adjoin_root.lift (algebra_map F K) x hx).to_algebra,
  haveI : is_scalar_tower F Fx A := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ a ha),
  haveI : is_scalar_tower F Fx K := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ x hx),
  haveI : fact (irreducible $ minpoly F x) := ⟨minpoly.irreducible $ this x⟩,
  let ψ₀ : K →ₐ[Fx] A := is_alg_closed.lift (algebra.is_algebraic_of_larger_base F Fx hK),
  exact ⟨ψ₀.restrict_scalars F, (congr_arg ψ₀ (adjoin_root.lift_root hx).symm).trans $
    (ψ₀.commutes _).trans $ adjoin_root.lift_root ha⟩,
end
