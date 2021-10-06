/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import field_theory.splitting_field
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

- `is_alg_closure.equiv` is a proof that any two algebraic closures of the
  same field are isomorphic.

## TODO

Show that any two algebraic closures are isomorphic

## Tags

algebraic closure, algebraically closed

-/
universes u v w

open_locale classical big_operators
open polynomial

variables (k : Type u) [field k]

/-- Typeclass for algebraically closed fields.

To show `polynomial.splits p f` for an arbitrary ring homomorphism `f`,
see `is_alg_closed.splits_codomain` and `is_alg_closed.splits_domain`.
-/
class is_alg_closed : Prop :=
(splits : ∀ p : polynomial k, p.splits $ ring_hom.id k)

/-- Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

See also `is_alg_closed.splits_domain` for the case where `K` is algebraically closed.
-/
theorem is_alg_closed.splits_codomain {k K : Type*} [field k] [is_alg_closed k] [field K]
  {f : K →+* k} (p : polynomial K) : p.splits f :=
by { convert is_alg_closed.splits (p.map f), simp [splits_map_iff] }

/-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

See also `is_alg_closed.splits_codomain` for the case where `k` is algebraically closed.
-/
theorem is_alg_closed.splits_domain {k K : Type*} [field k] [is_alg_closed k] [field K]
  {f : k →+* K} (p : polynomial k) : p.splits f :=
polynomial.splits_of_splits_id _ $ is_alg_closed.splits _

namespace is_alg_closed

variables {k}

theorem exists_root [is_alg_closed k] (p : polynomial k) (hp : p.degree ≠ 0) : ∃ x, is_root p x :=
exists_root_of_splits _ (is_alg_closed.splits p) hp

theorem exists_eval₂_eq_zero_of_injective {R : Type*} [ring R] [is_alg_closed k] (f : R →+* k)
  (hf : function.injective f) (p : polynomial R) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf]) in
⟨x, by rwa [eval₂_eq_eval_map, ← is_root]⟩

theorem exists_eval₂_eq_zero {R : Type*} [field R] [is_alg_closed k] (f : R →+* k)
  (p : polynomial R) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
exists_eval₂_eq_zero_of_injective f f.injective p hp

variables (k)

theorem exists_aeval_eq_zero_of_injective {R : Type*} [comm_ring R] [is_alg_closed k] [algebra R k]
  (hinj : function.injective (algebra_map R k)) (p : polynomial R) (hp : p.degree ≠ 0) :
  ∃ x : k, aeval x p = 0 :=
exists_eval₂_eq_zero_of_injective (algebra_map R k) hinj p hp

theorem exists_aeval_eq_zero {R : Type*} [field R] [is_alg_closed k] [algebra R k]
  (p : polynomial R) (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
exists_eval₂_eq_zero (algebra_map R k) p hp

theorem of_exists_root (H : ∀ p : polynomial k, p.monic → irreducible p → ∃ x, p.eval x = 0) :
  is_alg_closed k :=
⟨λ p, or.inr $ λ q hq hqp,
 have irreducible (q * C (leading_coeff q)⁻¹),
   by { rw ← coe_norm_unit_of_ne_zero hq.ne_zero,
        exact (associated_normalize _).irreducible hq },
 let ⟨x, hx⟩ := H (q * C (leading_coeff q)⁻¹) (monic_mul_leading_coeff_inv hq.ne_zero) this in
 degree_mul_leading_coeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root this hx⟩

lemma degree_eq_one_of_irreducible [is_alg_closed k] {p : polynomial k} (h_nz : p ≠ 0)
  (hp : irreducible p) :
  p.degree = 1 :=
degree_eq_one_of_irreducible_of_splits h_nz hp (is_alg_closed.splits_codomain _)

lemma algebra_map_surjective_of_is_integral {k K : Type*} [field k] [domain K]
  [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_integral k K) :
  function.surjective (algebra_map k K) :=
begin
  refine λ x, ⟨-((minpoly k x).coeff 0), _⟩,
  have hq : (minpoly k x).leading_coeff = 1 := minpoly.monic (hf x),
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k
    (minpoly.ne_zero (hf x)) (minpoly.irreducible (hf x)),
  have : (aeval x (minpoly k x)) = 0 := minpoly.aeval k x,
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul,
    aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at this,
  exact (ring_hom.map_neg (algebra_map k K) ((minpoly k x).coeff 0)).symm ▸ this.symm,
end

lemma algebra_map_surjective_of_is_integral' {k K : Type*} [field k] [integral_domain K]
  [hk : is_alg_closed k] (f : k →+* K) (hf : f.is_integral) : function.surjective f :=
@algebra_map_surjective_of_is_integral k K _ _ _ f.to_algebra hf

lemma algebra_map_surjective_of_is_algebraic {k K : Type*} [field k] [domain K]
  [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_algebraic k K) :
  function.surjective (algebra_map k K) :=
algebra_map_surjective_of_is_integral ((is_algebraic_iff_is_integral' k).mp hf)

end is_alg_closed

/-- Typeclass for an extension being an algebraic closure. -/
class is_alg_closure (K : Type v) [field K] [algebra k K] : Prop :=
(alg_closed : is_alg_closed K)
(algebraic : algebra.is_algebraic k K)

theorem is_alg_closure_iff (K : Type v) [field K] [algebra k K] :
  is_alg_closure k K ↔ is_alg_closed K ∧ algebra.is_algebraic k K :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

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

namespace lift
/- In this section, the homomorphism from any algebraic extension into an algebraically
  closed extension is proven to exist. The assumption that M is algebraically closed could probably
  easily be switched to an assumption that M contains all the roots of polynomials in K -/
variables {K : Type u} {L : Type v} {M : Type w} [field K] [field L] [algebra K L]
  [field M] [algebra K M] [is_alg_closed M] (hL : algebra.is_algebraic K L)

variables (K L M)
include hL
open zorn subalgebra alg_hom function

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
  le_refl := λ E, ⟨le_refl _, by simp⟩,
  le_trans := λ E₁ E₂ E₃ h₁₂ h₂₃,
    ⟨le_trans h₁₂.fst h₂₃.fst,
    λ _, by erw [← inclusion_inclusion h₁₂.fst h₂₃.fst, compat, compat]⟩ }

open lattice

lemma maximal_subfield_with_hom_chain_bounded (c : set (subfield_with_hom K L M hL))
  (hc : chain (≤) c) (hcn  : c.nonempty) :
  ∃ ub : subfield_with_hom K L M hL, ∀ N, N ∈ c → N ≤ ub :=
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

variables (hL M)

lemma exists_maximal_subfield_with_hom : ∃ E : subfield_with_hom K L M hL,
  ∀ N, E ≤ N → N ≤ E :=
zorn.exists_maximal_of_nonempty_chains_bounded
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
  letI : field N := is_field.to_field _ (subalgebra.is_field_of_algebraic N hL),
  letI : algebra N M := (maximal_subfield_with_hom M hL).emb.to_ring_hom.to_algebra,
  cases is_alg_closed.exists_aeval_eq_zero M (minpoly N x)
    (ne_of_gt (minpoly.degree_pos
      ((is_algebraic_iff_is_integral _).1
        (algebra.is_algebraic_of_larger_base _ _ hL x)))) with y hy,
  let O : subalgebra N L := algebra.adjoin N {(x : L)},
  let larger_emb := ((adjoin_root.lift_hom (minpoly N x) y hy).comp
     (alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly N x).to_alg_hom),
  have hNO : N ≤ N.under O,
  { intros z hz,
    show algebra_map N L ⟨z, hz⟩ ∈ O,
    exact O.algebra_map_mem _ },
  let O' : subfield_with_hom K L M hL :=
  { carrier := N.under O,
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

/-- A (random) hom from an algebraic extension of K into an algebraically closed extension of K -/
@[irreducible] noncomputable def lift : L →ₐ[K] M :=
(lift.subfield_with_hom.maximal_subfield_with_hom M hL).emb.comp $
  eq.rec_on (lift.subfield_with_hom.maximal_subfield_with_hom_eq_top M hL).symm algebra.to_top

end is_alg_closed

namespace is_alg_closure

variables (J : Type*) (K : Type u) [field J] [field K] (L : Type v) (M : Type w) [field L]
  [field M] [algebra K M] [is_alg_closure K M]

local attribute [instance] is_alg_closure.alg_closed

section
variables [algebra K L] [is_alg_closure K L]

/-- A (random) isomorphism between two algebraic closures of `K`. -/
noncomputable def equiv : L ≃ₐ[K] M :=
let f : L →ₐ[K] M := is_alg_closed.lift K L M is_alg_closure.algebraic in
alg_equiv.of_bijective f
  ⟨ring_hom.injective f.to_ring_hom,
    begin
      letI : algebra L M := ring_hom.to_algebra f,
      letI : is_scalar_tower K L M :=
        is_scalar_tower.of_algebra_map_eq (by simp [ring_hom.algebra_map_to_algebra]),
      show function.surjective (algebra_map L M),
      exact is_alg_closed.algebra_map_surjective_of_is_algebraic
        (algebra.is_algebraic_of_larger_base K L is_alg_closure.algebraic),
    end⟩

end

section equiv_of_algebraic

variables [algebra K J] [algebra J L] [is_alg_closure J L] [algebra K L]
  [is_scalar_tower K J L]

/-- An equiv between an algebraic closure of `K` and an algebraic closure of an algebraic
  extension of `K` -/
noncomputable def equiv_of_algebraic (hKJ : algebra.is_algebraic K J) : L ≃ₐ[K] M :=
begin
  letI : is_alg_closure K L :=
  { alg_closed := by apply_instance,
    algebraic := algebra.is_algebraic_trans hKJ is_alg_closure.algebraic  },
  exact is_alg_closure.equiv _ _ _
end

end equiv_of_algebraic

section equiv_of_equiv

variables [algebra J L] [is_alg_closure J L]

variables {J K}

/-- Used in the definition of `equiv_of_equiv` -/
noncomputable def equiv_of_equiv_aux (hJK : J ≃+* K) :
  { e : L ≃+* M // e.to_ring_hom.comp (algebra_map J L) =
    (algebra_map K M).comp hJK.to_ring_hom }:=
begin
  letI : algebra K J := ring_hom.to_algebra hJK.symm.to_ring_hom,
  have : algebra.is_algebraic K J,
    from λ x, begin
      rw [← ring_equiv.symm_apply_apply hJK x],
      exact is_algebraic_algebra_map _
    end,
  letI : algebra K L := ring_hom.to_algebra ((algebra_map J L).comp (algebra_map K J)),
  letI : is_scalar_tower K J L := is_scalar_tower.of_algebra_map_eq (λ _, rfl),
  refine ⟨equiv_of_algebraic J K L M this, _⟩,
  ext,
  simp only [ring_equiv.to_ring_hom_eq_coe, function.comp_app, ring_hom.coe_comp,
    alg_equiv.coe_ring_equiv, ring_equiv.coe_to_ring_hom],
  conv_lhs { rw [← hJK.symm_apply_apply x] },
  show equiv_of_algebraic J K L M this (algebra_map K L (hJK x)) = _,
  rw [alg_equiv.commutes]
end

/-- Algebraic closure of isomorphic fields are isomorphic -/
noncomputable def equiv_of_equiv (hJK : J ≃+* K) : L ≃+* M :=
equiv_of_equiv_aux L M hJK

@[simp] lemma equiv_of_equiv_comp_algebra_map (hJK : J ≃+* K) :
  (↑(equiv_of_equiv L M hJK) : L →+* M).comp (algebra_map J L) =
  (algebra_map K M).comp hJK :=
(equiv_of_equiv_aux L M hJK).2

@[simp] lemma equiv_of_equiv_algebra_map (hJK : J ≃+* K) (j : J):
  equiv_of_equiv L M hJK (algebra_map J L j) =
  algebra_map K M (hJK j) :=
ring_hom.ext_iff.1 (equiv_of_equiv_comp_algebra_map L M hJK) j

@[simp] lemma equiv_of_equiv_symm_algebra_map (hJK : J ≃+* K) (k : K):
  (equiv_of_equiv L M hJK).symm (algebra_map K M k) =
  algebra_map J L (hJK.symm k) :=
(equiv_of_equiv L M hJK).injective (by simp)

@[simp] lemma equiv_of_equiv_symm_comp_algebra_map (hJK : J ≃+* K) :
  ((equiv_of_equiv L M hJK).symm : M →+* L).comp (algebra_map K M) =
  (algebra_map J L).comp hJK.symm :=
ring_hom.ext_iff.2 (equiv_of_equiv_symm_algebra_map L M hJK)

end equiv_of_equiv

end is_alg_closure
