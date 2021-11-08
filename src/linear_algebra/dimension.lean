/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Scott Morrison
-/
import linear_algebra.dfinsupp
import linear_algebra.std_basis
import linear_algebra.isomorphisms
import set_theory.cofinality
import linear_algebra.invariant_basis_number

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `module.rank : cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

* The rank of a linear map is defined as the rank of its range.

## Main statements

* `linear_map.dim_le_of_injective`: the source of an injective linear map has dimension
  at most that of the target.
* `linear_map.dim_le_of_surjective`: the target of a surjective linear map has dimension
  at most that of that source.
* `basis_fintype_of_finite_spans`:
  the existence of a finite spanning set implies that any basis is finite.
* `infinite_basis_le_maximal_linear_independent`:
  if `b` is an infinite basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the cardinality of `b` is bounded by the cardinality of `s`.

For modules over rings satisfying the rank condition

* `basis.le_span`:
  the cardinality of a basis is bounded by the cardinality of any spanning set

For modules over rings satisfying the strong rank condition

* `linear_independent_le_span`:
  For any linearly independent family `v : ι → M`
  and any finite spanning set `w : set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linear_independent_le_basis`:
  If `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.

For modules over rings with invariant basis number
(including all commutative rings and all noetherian rings)

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.

For vector spaces (i.e. modules over a field), we have

* `dim_quotient_add_dim`: if `V₁` is a submodule of `V`, then
  `module.rank (V/V₁) + module.rank V₁ = module.rank V`.
* `dim_range_add_dim_ker`: the rank-nullity theorem.

## Implementation notes

There is a naming discrepancy: most of the theorem names refer to `dim`,
even though the definition is of `module.rank`.
This reflects that `module.rank` was originally called `dim`, and only defined for vector spaces.

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `V`, `V'`, ... all live in different universes,
and `V₁`, `V₂`, ... all live in the same universe.
-/

noncomputable theory

universes u v v' v'' u₁' w w'

variables {K : Type u} {V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}
variables {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open_locale classical big_operators cardinal

open basis submodule function set

section module

section
variables [semiring K] [add_comm_monoid V] [module K V]
include K

variables (K V)

/-- The rank of a module, defined as a term of type `cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.

For a free module over any ring satisfying the strong rank condition
(e.g. left-noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

The definition is marked as protected to avoid conflicts with `_root_.rank`,
the rank of a linear map.
-/
protected def module.rank : cardinal :=
cardinal.sup.{v v} (λ ι : {s : set V // linear_independent K (coe : s → V)}, #ι.1)

end

section
variables {R : Type u} [ring R]
variables {M : Type v} [add_comm_group M] [module R M]
variables {M' : Type v'} [add_comm_group M'] [module R M']
variables {M₁ : Type v} [add_comm_group M₁] [module R M₁]

theorem linear_map.lift_dim_le_of_injective (f : M →ₗ[R] M') (i : injective f) :
  cardinal.lift.{v'} (module.rank R M) ≤ cardinal.lift.{ v} (module.rank R M') :=
begin
  dsimp [module.rank],
  fapply cardinal.lift_sup_le_lift_sup',
  { rintro ⟨s, li⟩,
    use f '' s,
    convert (li.map' f (linear_map.ker_eq_bot.mpr i)).comp
      (equiv.set.image ⇑f s i).symm (equiv.injective _),
    ext ⟨-, ⟨x, ⟨h, rfl⟩⟩⟩,
    simp, },
  { rintro ⟨s, li⟩,
    exact cardinal.lift_mk_le'.mpr ⟨(equiv.set.image f s i).to_embedding⟩, }
end

theorem linear_map.dim_le_of_injective (f : M →ₗ[R] M₁) (i : injective f) :
  module.rank R M ≤ module.rank R M₁ :=
cardinal.lift_le.1 (f.lift_dim_le_of_injective i)

theorem dim_le {n : ℕ}
  (H : ∀ s : finset M, linear_independent R (λ i : s, (i : M)) → s.card ≤ n) :
  module.rank R M ≤ n :=
begin
  apply cardinal.sup_le.mpr,
  rintro ⟨s, li⟩,
  exact linear_independent_bounded_of_finset_linear_independent_bounded H _ li,
end

lemma lift_dim_range_le (f : M →ₗ[R] M') :
  cardinal.lift.{v} (module.rank R f.range) ≤ cardinal.lift.{v'} (module.rank R M) :=
begin
  dsimp [module.rank],
  apply cardinal.lift_sup_le,
  rintro ⟨s, li⟩,
  apply le_trans,
  swap 2,
  apply cardinal.lift_le.mpr,
  refine (cardinal.le_sup _ ⟨range_splitting f '' s, _⟩),
  { apply linear_independent.of_comp f.range_restrict,
    convert li.comp (equiv.set.range_splitting_image_equiv f s) (equiv.injective _) using 1, },
  { exact (cardinal.lift_mk_eq'.mpr ⟨equiv.set.range_splitting_image_equiv f s⟩).ge, },
end

lemma dim_range_le (f : M →ₗ[R] M₁) : module.rank R f.range ≤ module.rank R M :=
by simpa using lift_dim_range_le f

lemma lift_dim_map_le (f : M →ₗ[R] M') (p : submodule R M) :
  cardinal.lift.{v} (module.rank R (p.map f)) ≤ cardinal.lift.{v'} (module.rank R p) :=
begin
  have h := lift_dim_range_le (f.comp (submodule.subtype p)),
  rwa [linear_map.range_comp, range_subtype] at h,
end

lemma dim_map_le (f : M →ₗ[R] M₁) (p : submodule R M) : module.rank R (p.map f) ≤ module.rank R p :=
by simpa using lift_dim_map_le f p

lemma dim_le_of_submodule (s t : submodule R M) (h : s ≤ t) :
  module.rank R s ≤ module.rank R t :=
(of_le h).dim_le_of_injective $ assume ⟨x, hx⟩ ⟨y, hy⟩ eq,
  subtype.eq $ show x = y, from subtype.ext_iff_val.1 eq

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
theorem linear_equiv.lift_dim_eq (f : M ≃ₗ[R] M') :
  cardinal.lift.{v'} (module.rank R M) = cardinal.lift.{v} (module.rank R M') :=
begin
  apply le_antisymm,
  { exact f.to_linear_map.lift_dim_le_of_injective f.injective, },
  { exact f.symm.to_linear_map.lift_dim_le_of_injective f.symm.injective, },
end

/-- Two linearly equivalent vector spaces have the same dimension. -/
theorem linear_equiv.dim_eq (f : M ≃ₗ[R] M₁) :
  module.rank R M = module.rank R M₁ :=
cardinal.lift_inj.1 f.lift_dim_eq

lemma dim_eq_of_injective (f : M →ₗ[R] M₁) (h : injective f) :
  module.rank R M = module.rank R f.range :=
(linear_equiv.of_injective f h).dim_eq

/-- Pushforwards of submodules along a `linear_equiv` have the same dimension. -/
lemma linear_equiv.dim_map_eq (f : M ≃ₗ[R] M₁) (p : submodule R M) :
  module.rank R (p.map (f : M →ₗ[R] M₁)) = module.rank R p :=
(f.of_submodule p).dim_eq.symm

variables (R M)

@[simp] lemma dim_top : module.rank R (⊤ : submodule R M) = module.rank R M :=
begin
  have : (⊤ : submodule R M) ≃ₗ[R] M := linear_equiv.of_top ⊤ rfl,
  rw this.dim_eq,
end

variables {R M}

lemma dim_range_of_surjective (f : M →ₗ[R] M') (h : surjective f) :
  module.rank R f.range = module.rank R M' :=
by rw [linear_map.range_eq_top.2 h, dim_top]

lemma dim_submodule_le (s : submodule R M) : module.rank R s ≤ module.rank R M :=
begin
  rw ←dim_top R M,
  exact dim_le_of_submodule _ _ le_top,
end

lemma linear_map.dim_le_of_surjective (f : M →ₗ[R] M₁) (h : surjective f) :
  module.rank R M₁ ≤ module.rank R M :=
begin
  rw ←dim_range_of_surjective f h,
  apply dim_range_le,
end

theorem dim_quotient_le (p : submodule R M) :
  module.rank R p.quotient ≤ module.rank R M :=
(mkq p).dim_le_of_surjective (surjective_quot_mk _)

variables [nontrivial R]

lemma {m} cardinal_lift_le_dim_of_linear_independent
  {ι : Type w} {v : ι → M} (hv : linear_independent R v) :
  cardinal.lift.{(max v m)} (#ι) ≤ cardinal.lift.{(max w m)} (module.rank R M) :=
begin
  apply le_trans,
  { exact cardinal.lift_mk_le.mpr
      ⟨(equiv.of_injective _ hv.injective).to_embedding⟩, },
  { simp only [cardinal.lift_le],
    apply le_trans,
    swap,
    exact cardinal.le_sup _ ⟨range v, hv.coe_range⟩,
    exact le_refl _, },
end

lemma cardinal_lift_le_dim_of_linear_independent'
  {ι : Type w} {v : ι → M} (hv : linear_independent R v) :
  cardinal.lift.{v} (#ι) ≤ cardinal.lift.{w} (module.rank R M) :=
cardinal_lift_le_dim_of_linear_independent.{u v w 0} hv

lemma cardinal_le_dim_of_linear_independent
  {ι : Type v} {v : ι → M} (hv : linear_independent R v) :
  #ι ≤ module.rank R M :=
by simpa using cardinal_lift_le_dim_of_linear_independent hv

lemma cardinal_le_dim_of_linear_independent'
  {s : set M} (hs : linear_independent R (λ x, x : s → M)) :
  #s ≤ module.rank R M :=
cardinal_le_dim_of_linear_independent hs

variables (R M)

@[simp] lemma dim_punit : module.rank R punit = 0 :=
begin
  apply le_bot_iff.mp,
  apply cardinal.sup_le.mpr,
  rintro ⟨s, li⟩,
  apply le_bot_iff.mpr,
  apply cardinal.mk_emptyc_iff.mpr,
  simp only [subtype.coe_mk],
  by_contradiction h,
  have ne : s.nonempty := ne_empty_iff_nonempty.mp h,
  simpa using linear_independent.ne_zero (⟨_, ne.some_mem⟩ : s) li,
end

@[simp] lemma dim_bot : module.rank R (⊥ : submodule R M) = 0 :=
begin
  have : (⊥ : submodule R M) ≃ₗ[R] punit := bot_equiv_punit,
  rw [this.dim_eq, dim_punit],
end

variables {R M}

/--
Over any nontrivial ring, the existence of a finite spanning set implies that any basis is finite.
-/
-- One might hope that a finite spanning set implies that any linearly independent set is finite.
-- While this is true over a division ring
-- (simply because any linearly independent set can be extended to a basis),
-- I'm not certain what more general statements are possible.
def basis_fintype_of_finite_spans (w : set M) [fintype w] (s : span R w = ⊤)
  {ι : Type w} (b : basis ι R M) : fintype ι :=
begin
  -- We'll work by contradiction, assuming `ι` is infinite.
  apply fintype_of_not_infinite _,
  introI i,
  -- Let `S` be the union of the supports of `x ∈ w` expressed as linear combinations of `b`.
  -- This is a finite set since `w` is finite.
  let S : finset ι := finset.univ.sup (λ x : w, (b.repr x).support),
  let bS : set M := b '' S,
  have h : ∀ x ∈ w, x ∈ span R bS,
  { intros x m,
    rw [←b.total_repr x, finsupp.span_image_eq_map_total, submodule.mem_map],
    use b.repr x,
    simp only [and_true, eq_self_iff_true, finsupp.mem_supported],
    change (b.repr x).support ≤ S,
    convert (finset.le_sup (by simp : (⟨x, m⟩ : w) ∈ finset.univ)),
    refl, },
  -- Thus this finite subset of the basis elements spans the entire module.
  have k : span R bS = ⊤ := eq_top_iff.2 (le_trans s.ge (span_le.2 h)),

  -- Now there is some `x : ι` not in `S`, since `ι` is infinite.
  obtain ⟨x, nm⟩ := infinite.exists_not_mem_finset S,
  -- However it must be in the span of the finite subset,
  have k' : b x ∈ span R bS, { rw k, exact mem_top, },
  -- giving the desire contradiction.
  refine b.linear_independent.not_mem_span_image _ k',
  exact nm,
end

/--
Over any ring `R`, if `b` is a basis for a module `M`,
and `s` is a maximal linearly independent set,
then the union of the supports of `x ∈ s` (when written out in the basis `b`) is all of `b`.
-/
-- From [Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
lemma union_support_maximal_linear_independent_eq_range_basis
  {ι : Type w} (b : basis ι R M)
  {κ : Type w'} (v : κ → M) (i : linear_independent R v) (m : i.maximal) :
  (⋃ k, ((b.repr (v k)).support : set ι)) = univ :=
begin
  -- If that's not the case,
  by_contradiction h,
  simp only [←ne.def, ne_univ_iff_exists_not_mem, mem_Union, not_exists_not,
    finsupp.mem_support_iff, finset.mem_coe] at h,
  -- We have some basis element `b b'` which is not in the support of any of the `v i`.
  obtain ⟨b', w⟩ := h,
  -- Using this, we'll construct a linearly independent family strictly larger than `v`,
  -- by also using this `b b'`.
  let v' : option κ → M := λ o, o.elim (b b') v,
  have r : range v ⊆ range v',
  { rintro - ⟨k, rfl⟩,
    use some k,
    refl, },
  have r' : b b' ∉ range v,
  { rintro ⟨k, p⟩,
    simpa [w] using congr_arg (λ m, (b.repr m) b') p, },
  have r'' : range v ≠ range v',
  { intro e,
    have p : b b' ∈ range v', { use none, refl, },
    rw ←e at p,
    exact r' p, },
  have inj' : injective v',
  { rintros (_|k) (_|k) z,
    { refl, },
    { exfalso, exact r' ⟨k, z.symm⟩, },
    { exfalso, exact r' ⟨k, z⟩, },
    { congr, exact i.injective z, }, },
  -- The key step in the proof is checking that this strictly larger family is linearly independent.
  have i' : linear_independent R (coe : range v' → M),
  { rw [linear_independent_subtype_range inj', linear_independent_iff],
    intros l z,
    rw [finsupp.total_option] at z,
    simp only [v', option.elim] at z,
    change _ + finsupp.total κ M R v l.some = 0 at z,
    -- We have some linear combination of `b b'` and the `v i`, which we want to show is trivial.
    -- We'll first show the coefficient of `b b'` is zero,
    -- by expressing the `v i` in the basis `b`, and using that the `v i` have no `b b'` term.
    have l₀ : l none = 0,
    { rw ←eq_neg_iff_add_eq_zero at z,
      replace z := eq_neg_of_eq_neg z,
      apply_fun (λ x, b.repr x b') at z,
      simp only [repr_self, linear_equiv.map_smul, mul_one, finsupp.single_eq_same, pi.neg_apply,
        finsupp.smul_single', linear_equiv.map_neg, finsupp.coe_neg] at z,
      erw finsupp.congr_fun (finsupp.apply_total R (b.repr : M →ₗ[R] ι →₀ R) v l.some) b' at z,
      simpa [finsupp.total_apply, w] using z, },
    -- Then all the other coefficients are zero, because `v` is linear independent.
    have l₁ : l.some = 0,
    { rw [l₀, zero_smul, zero_add] at z,
      exact linear_independent_iff.mp i _ z, },
    -- Finally we put those facts together to show the linear combination is trivial.
    ext (_|a),
    { simp only [l₀, finsupp.coe_zero, pi.zero_apply], },
    { erw finsupp.congr_fun l₁ a,
      simp only [finsupp.coe_zero, pi.zero_apply], }, },
  dsimp [linear_independent.maximal] at m,
  specialize m (range v') i' r,
  exact r'' m,
end

/--
Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
lemma infinite_basis_le_maximal_linear_independent'
  {ι : Type w} (b : basis ι R M) [infinite ι]
  {κ : Type w'} (v : κ → M) (i : linear_independent R v) (m : i.maximal) :
  cardinal.lift.{w'} (#ι) ≤ cardinal.lift.{w} (#κ) :=
begin
  let Φ := λ k : κ, (b.repr (v k)).support,
  have w₁ : #ι ≤ #(set.range Φ),
  { apply cardinal.le_range_of_union_finset_eq_top,
    exact union_support_maximal_linear_independent_eq_range_basis b v i m, },
  have w₂ :
    cardinal.lift.{w'} (#(set.range Φ)) ≤ cardinal.lift.{w} (#κ) :=
    cardinal.mk_range_le_lift,
  exact (cardinal.lift_le.mpr w₁).trans w₂,
end

/--
Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
-- (See `infinite_basis_le_maximal_linear_independent'` for the more general version
-- where the index types can live in different universes.)
lemma infinite_basis_le_maximal_linear_independent
  {ι : Type w} (b : basis ι R M) [infinite ι]
  {κ : Type w} (v : κ → M) (i : linear_independent R v) (m : i.maximal) :
  #ι ≤ #κ :=
cardinal.lift_le.mp (infinite_basis_le_maximal_linear_independent' b v i m)

lemma complete_lattice.independent.subtype_ne_bot_le_rank [no_zero_smul_divisors R M]
  {V : ι → submodule R M} (hV : complete_lattice.independent V) :
  cardinal.lift.{v} (#{i : ι // V i ≠ ⊥}) ≤ cardinal.lift.{w} (module.rank R M) :=
begin
  set I := {i : ι // V i ≠ ⊥},
  have hI : ∀ i : I, ∃ v ∈ V i, v ≠ (0:M),
  { intros i,
    rw ← submodule.ne_bot_iff,
    exact i.prop },
  choose v hvV hv using hI,
  have : linear_independent R v,
  { exact (hV.comp _ subtype.coe_injective).linear_independent _ hvV hv },
  exact cardinal_lift_le_dim_of_linear_independent' this
end

end

section rank_zero

variables {R : Type u} {M : Type v}
variables [ring R] [nontrivial R] [add_comm_group M] [module R M] [no_zero_smul_divisors R M]

lemma dim_zero_iff_forall_zero : module.rank R M = 0 ↔ ∀ x : M, x = 0 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { contrapose! h,
    obtain ⟨x, hx⟩ := h,
    suffices : 1 ≤ module.rank R M,
    { intro h, exact lt_irrefl _ (lt_of_lt_of_le cardinal.zero_lt_one (h ▸ this)) },
    suffices : linear_independent R (λ (y : ({x} : set M)), ↑y),
    { simpa using (cardinal_le_dim_of_linear_independent this), },
    exact linear_independent_singleton hx },
  { have : (⊤ : submodule R M) = ⊥,
    { ext x, simp [h x] },
    rw [←dim_top, this, dim_bot] }
end

lemma dim_zero_iff : module.rank R M = 0 ↔ subsingleton M :=
dim_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

lemma dim_pos_iff_exists_ne_zero : 0 < module.rank R M ↔ ∃ x : M, x ≠ 0 :=
begin
  rw ←not_iff_not,
  simpa using dim_zero_iff_forall_zero
end

lemma dim_pos_iff_nontrivial : 0 < module.rank R M ↔ nontrivial M :=
dim_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

lemma dim_pos [h : nontrivial M] : 0 < module.rank R M :=
dim_pos_iff_nontrivial.2 h

end rank_zero

section invariant_basis_number

variables {R : Type u} [ring R] [invariant_basis_number R]
variables {M : Type v} [add_comm_group M] [module R M]

/-- The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities. -/
theorem mk_eq_mk_of_basis (v : basis ι R M) (v' : basis ι' R M) :
  cardinal.lift.{w'} (#ι) = cardinal.lift.{w} (#ι') :=
begin
  haveI := nontrivial_of_invariant_basis_number R,
  by_cases h : #ι < ω,
  { -- `v` is a finite basis, so by `basis_fintype_of_finite_spans` so is `v'`.
    haveI : fintype ι := (cardinal.lt_omega_iff_fintype.mp h).some,
    haveI : fintype (range v) := set.fintype_range ⇑v,
    haveI := basis_fintype_of_finite_spans _ v.span_eq v',
    -- We clean up a little:
    rw [cardinal.fintype_card, cardinal.fintype_card],
    simp only [cardinal.lift_nat_cast, cardinal.nat_cast_inj],
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_lequiv R,
    exact (((finsupp.linear_equiv_fun_on_fintype R R ι).symm.trans v.repr.symm) ≪≫ₗ
      v'.repr) ≪≫ₗ (finsupp.linear_equiv_fun_on_fintype R R ι'), },
  { -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linear_independent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linear_independent` again
    -- we see they have the same cardinality.
    simp only [not_lt] at h,
    haveI : infinite ι := cardinal.infinite_iff.mpr h,
    have w₁ :=
      infinite_basis_le_maximal_linear_independent' v _ v'.linear_independent v'.maximal,
    haveI : infinite ι' := cardinal.infinite_iff.mpr (begin
      apply cardinal.lift_le.{w' w}.mp,
      have p := (cardinal.lift_le.mpr h).trans w₁,
      rw cardinal.lift_omega at ⊢ p,
      exact p,
    end),
    have w₂ :=
      infinite_basis_le_maximal_linear_independent' v' _ v.linear_independent v.maximal,
    exact le_antisymm w₁ w₂, }
end

/-- Given two basis indexed by `ι` and `ι'` of an `R`-module, where `R` satisfies the invariant
basis number property, an equiv `ι ≃ ι' `. -/
def basis.index_equiv (v : basis ι R M) (v' : basis ι' R M) : ι ≃ ι' :=
nonempty.some (cardinal.lift_mk_eq.1 (cardinal.lift_max.2 (mk_eq_mk_of_basis v v')))

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : basis ι R M) (v' : basis ι' R M) :
  #ι = #ι' :=
cardinal.lift_inj.1 $ mk_eq_mk_of_basis v v'

end invariant_basis_number

section rank_condition

variables {R : Type u} [ring R] [rank_condition R]
variables {M : Type v} [add_comm_group M] [module R M]

/--
An auxiliary lemma for `basis.le_span`.

If `R` satisfies the rank condition,
then for any finite basis `b : basis ι R M`,
and any finite spanning set `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
lemma basis.le_span'' {ι : Type*} [fintype ι] (b : basis ι R M)
  {w : set M} [fintype w] (s : span R w = ⊤) :
  fintype.card ι ≤ fintype.card w :=
begin
   -- We construct an surjective linear map `(w → R) →ₗ[R] (ι → R)`,
   -- by expressing a linear combination in `w` as a linear combination in `ι`.
   fapply card_le_of_surjective' R,
   { exact b.repr.to_linear_map.comp (finsupp.total w M R coe), },
   { apply surjective.comp,
    apply linear_equiv.surjective,
    rw [←linear_map.range_eq_top, finsupp.range_total],
    simpa using s, },
end

/--
Another auxiliary lemma for `basis.le_span`, which does not require assuming the basis is finite,
but still assumes we have a finite spanning set.
-/
lemma basis_le_span' {ι : Type*} (b : basis ι R M)
  {w : set M} [fintype w] (s : span R w = ⊤) :
  #ι ≤ fintype.card w :=
begin
  haveI := nontrivial_of_invariant_basis_number R,
  haveI := basis_fintype_of_finite_spans w s b,
  rw cardinal.fintype_card ι,
  simp only [cardinal.nat_cast_le],
  exact basis.le_span'' b s,
end

/--
If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning set.
-/
-- Note that if `R` satisfies the strong rank condition,
-- this also follows from `linear_independent_le_span` below.
theorem basis.le_span {J : set M} (v : basis ι R M)
   (hJ : span R J = ⊤) : #(range v) ≤ #J :=
begin
  haveI := nontrivial_of_invariant_basis_number R,
  casesI fintype_or_infinite J,
  { rw [←cardinal.lift_le, cardinal.mk_range_eq_of_injective v.injective, cardinal.fintype_card J],
    convert cardinal.lift_le.{w v}.2 (basis_le_span' v hJ),
    simp, },
  { have := cardinal.mk_range_eq_of_injective v.injective,
    let S : J → set ι := λ j, ↑(v.repr j).support,
    let S' : J → set M := λ j, v '' S j,
    have hs : range v ⊆ ⋃ j, S' j,
    { intros b hb,
      rcases mem_range.1 hb with ⟨i, hi⟩,
      have : span R J ≤ comap v.repr.to_linear_map (finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 (λ j hj x hx, ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩),
      rw hJ at this,
      replace : v.repr (v i) ∈ (finsupp.supported R R (⋃ j, S j)) := this trivial,
      rw [v.repr_self, finsupp.mem_supported,
        finsupp.support_single_ne_zero one_ne_zero] at this,
      { subst b,
        rcases mem_Union.1 (this (finset.mem_singleton_self _)) with ⟨j, hj⟩,
        exact mem_Union.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩ },
      { apply_instance } },
    refine le_of_not_lt (λ IJ, _),
    suffices : #(⋃ j, S' j) < #(range v),
    { exact not_le_of_lt this ⟨set.embedding_of_subset _ _ hs⟩ },
    refine lt_of_le_of_lt (le_trans cardinal.mk_Union_le_sum_mk
      (cardinal.sum_le_sum _ (λ _, cardinal.omega) _)) _,
    { exact λ j, le_of_lt (cardinal.lt_omega_iff_finite.2 $ (finset.finite_to_set _).image _) },
    { simpa } },
end

end rank_condition

section strong_rank_condition

variables {R : Type u} [ring R] [strong_rank_condition R]
variables {M : Type v} [add_comm_group M] [module R M]

open submodule

-- An auxiliary lemma for `linear_independent_le_span'`,
-- with the additional assumption that the linearly independent family is finite.
lemma linear_independent_le_span_aux'
  {ι : Type*} [fintype ι] (v : ι → M) (i : linear_independent R v)
  (w : set M) [fintype w] (s : range v ≤ span R w) :
  fintype.card ι ≤ fintype.card w :=
begin
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R,
  { apply finsupp.total,
    exact λ i, span.repr R w ⟨v i, s (mem_range_self i)⟩, },
  { intros f g h,
    apply_fun finsupp.total w M R coe at h,
    simp only [finsupp.total_total, submodule.coe_mk, span.finsupp_total_repr] at h,
    rw [←sub_eq_zero, ←linear_map.map_sub] at h,
    exact sub_eq_zero.mp (linear_independent_iff.mp i _ h), },
end

/--
If `R` satisfies the strong rank condition,
then any linearly independent family `v : ι → M`
contained in the span of some finite `w : set M`,
is itself finite.
-/
def linear_independent_fintype_of_le_span_fintype
  {ι : Type*} (v : ι → M) (i : linear_independent R v)
  (w : set M) [fintype w] (s : range v ≤ span R w) : fintype ι :=
fintype_of_finset_card_le (fintype.card w) (λ t, begin
  let v' := λ x : (t : set ι), v x,
  have i' : linear_independent R v' := i.comp _ subtype.val_injective,
  have s' : range v' ≤ span R w := (range_comp_subset_range _ _).trans s,
  simpa using linear_independent_le_span_aux' v' i' w s',
end)

/--
If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
contained in the span of some finite `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
lemma linear_independent_le_span' {ι : Type*} (v : ι → M) (i : linear_independent R v)
  (w : set M) [fintype w] (s : range v ≤ span R w) :
  #ι ≤ fintype.card w :=
begin
  haveI : fintype ι := linear_independent_fintype_of_le_span_fintype v i w s,
  rw cardinal.fintype_card,
  simp only [cardinal.nat_cast_le],
  exact linear_independent_le_span_aux' v i w s,
end

/--
If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
and any finite spanning set `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
lemma linear_independent_le_span {ι : Type*} (v : ι → M) (i : linear_independent R v)
  (w : set M) [fintype w] (s : span R w = ⊤) :
  #ι ≤ fintype.card w :=
begin
  apply linear_independent_le_span' v i w,
  rw s,
  exact le_top,
end

/-- A linearly-independent family of vectors in a module over a ring satisfying the strong rank
condition must be finite if the module is Noetherian. -/
noncomputable def fintype_of_is_noetherian_linear_independent [is_noetherian R M]
  {v : ι → M} (hi : linear_independent R v) : fintype ι :=
begin
  have hfg : (⊤ : submodule R M).fg,
  { exact is_noetherian_def.mp infer_instance ⊤, },
  rw submodule.fg_def at hfg,
  choose s hs hs' using hfg,
  haveI : fintype s := hs.fintype,
  apply linear_independent_fintype_of_le_span_fintype v hi s,
  simp only [hs', set.subset_univ, submodule.top_coe, set.le_eq_subset],
end

/-- A linearly-independent subset of a module over a ring satisfying the strong rank condition
must be finite if the module is Noetherian. -/
lemma finite_of_is_noetherian_linear_independent [is_noetherian R M]
  {s : set M} (hi : linear_independent R (coe : s → M)) : s.finite :=
⟨fintype_of_is_noetherian_linear_independent hi⟩

/--
An auxiliary lemma for `linear_independent_le_basis`:
we handle the case where the basis `b` is infinite.
-/
lemma linear_independent_le_infinite_basis
  {ι : Type*} (b : basis ι R M) [infinite ι]
  {κ : Type*} (v : κ → M) (i : linear_independent R v) :
  #κ ≤ #ι :=
begin
  by_contradiction,
  rw [not_le, ← cardinal.mk_finset_eq_mk ι] at h,
  let Φ := λ k : κ, (b.repr (v k)).support,
  obtain ⟨s, w : infinite ↥(Φ ⁻¹' {s})⟩ := cardinal.exists_infinite_fiber Φ h (by apply_instance),
  let v' := λ k : Φ ⁻¹' {s}, v k,
  have i' : linear_independent R v' := i.comp _ subtype.val_injective,
  have w' : fintype (Φ ⁻¹' {s}),
  { apply linear_independent_fintype_of_le_span_fintype v' i' (s.image b),
    rintros m ⟨⟨p,⟨rfl⟩⟩,rfl⟩,
    simp only [set_like.mem_coe, subtype.coe_mk, finset.coe_image],
    apply basis.mem_span_repr_support, },
  exactI w.false,
end

/--
Over any ring `R` satisfying the strong rank condition,
if `b` is a basis for a module `M`,
and `s` is a linearly independent set,
then the cardinality of `s` is bounded by the cardinality of `b`.
-/
lemma linear_independent_le_basis
  {ι : Type*} (b : basis ι R M)
  {κ : Type*} (v : κ → M) (i : linear_independent R v) :
  #κ ≤ #ι :=
begin
  -- We split into cases depending on whether `ι` is infinite.
  cases fintype_or_infinite ι; resetI,
  { -- When `ι` is finite, we have `linear_independent_le_span`,
    rw cardinal.fintype_card ι,
    haveI : nontrivial R := nontrivial_of_invariant_basis_number R,
    rw fintype.card_congr (equiv.of_injective b b.injective),
    exact linear_independent_le_span v i (range b) b.span_eq, },
  { -- and otherwise we have `linear_indepedent_le_infinite_basis`.
    exact linear_independent_le_infinite_basis b v i, },
end

/-- In an `n`-dimensional space, the rank is at most `m`. -/
lemma basis.card_le_card_of_linear_independent_aux
  {R : Type*} [ring R] [strong_rank_condition R]
  (n : ℕ) {m : ℕ} (v : fin m → fin n → R) :
  linear_independent R v → m ≤ n :=
λ h, by simpa using (linear_independent_le_basis (pi.basis_fun R (fin n)) v h)

/--
Over any ring `R` satisfying the strong rank condition,
if `b` is an infinite basis for a module `M`,
then every maximal linearly independent set has the same cardinality as `b`.

This proof (along with some of the lemmas above) comes from
[Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
-/
-- When the basis is not infinite this need not be true!
lemma maximal_linear_independent_eq_infinite_basis
  {ι : Type*} (b : basis ι R M) [infinite ι]
  {κ : Type*} (v : κ → M) (i : linear_independent R v) (m : i.maximal) :
  #κ = #ι :=
begin
  apply le_antisymm,
  { exact linear_independent_le_basis b v i, },
  { haveI : nontrivial R := nontrivial_of_invariant_basis_number R,
    exact infinite_basis_le_maximal_linear_independent b v i m, }
end

theorem basis.mk_eq_dim'' {ι : Type v} (v : basis ι R M) :
  #ι = module.rank R M :=
begin
  haveI := nontrivial_of_invariant_basis_number R,
  apply le_antisymm,
  { transitivity,
    swap,
    apply cardinal.le_sup,
    exact ⟨set.range v, by { convert v.reindex_range.linear_independent, ext, simp }⟩,
    exact (cardinal.mk_range_eq v v.injective).ge, },
  { apply cardinal.sup_le.mpr,
    rintro ⟨s, li⟩,
    apply linear_independent_le_basis v _ li, },
end

-- By this stage we want to have a complete API for `module.rank`,
-- so we set it `irreducible` here, to keep ourselves honest.
attribute [irreducible] module.rank

theorem basis.mk_range_eq_dim (v : basis ι R M) :
  #(range v) = module.rank R M :=
v.reindex_range.mk_eq_dim''

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
lemma dim_eq_card_basis {ι : Type w} [fintype ι] (h : basis ι R M) :
  module.rank R M = fintype.card ι :=
by {haveI := nontrivial_of_invariant_basis_number R,
  rw [←h.mk_range_eq_dim, cardinal.fintype_card, set.card_range_of_injective h.injective] }

lemma basis.card_le_card_of_linear_independent {ι : Type*} [fintype ι]
  (b : basis ι R M) {ι' : Type*} [fintype ι'] {v : ι' → M} (hv : linear_independent R v) :
  fintype.card ι' ≤ fintype.card ι :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  simpa [dim_eq_card_basis b, cardinal.fintype_card] using
    cardinal_lift_le_dim_of_linear_independent' hv
end

lemma basis.card_le_card_of_submodule (N : submodule R M) [fintype ι] (b : basis ι R M)
  [fintype ι'] (b' : basis ι' R N) : fintype.card ι' ≤ fintype.card ι :=
b.card_le_card_of_linear_independent (b'.linear_independent.map' N.subtype N.ker_subtype)

lemma basis.card_le_card_of_le
  {N O : submodule R M} (hNO : N ≤ O) [fintype ι] (b : basis ι R O) [fintype ι']
  (b' : basis ι' R N) : fintype.card ι' ≤ fintype.card ι :=
b.card_le_card_of_linear_independent
  (b'.linear_independent.map' (submodule.of_le hNO) (N.ker_of_le O _))

theorem basis.mk_eq_dim (v : basis ι R M) :
  cardinal.lift.{v} (#ι) = cardinal.lift.{w} (module.rank R M) :=
begin
  haveI := nontrivial_of_invariant_basis_number R,
  rw [←v.mk_range_eq_dim, cardinal.mk_range_eq_of_injective v.injective]
end

theorem {m} basis.mk_eq_dim' (v : basis ι R M) :
  cardinal.lift.{(max v m)} (#ι) = cardinal.lift.{(max w m)} (module.rank R M) :=
by simpa using v.mk_eq_dim

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
lemma basis.nonempty_fintype_index_of_dim_lt_omega {ι : Type*}
  (b : basis ι R M) (h : module.rank R M < cardinal.omega) :
  nonempty (fintype ι) :=
by rwa [← cardinal.lift_lt, ← b.mk_eq_dim,
        -- ensure `omega` has the correct universe
        cardinal.lift_omega, ← cardinal.lift_omega.{u_1 v},
        cardinal.lift_lt, cardinal.lt_omega_iff_fintype] at h

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
noncomputable def basis.fintype_index_of_dim_lt_omega {ι : Type*}
  (b : basis ι R M) (h : module.rank R M < cardinal.omega) :
  fintype ι :=
classical.choice (b.nonempty_fintype_index_of_dim_lt_omega h)

/-- If a module has a finite dimension, all bases are indexed by a finite set. -/
lemma basis.finite_index_of_dim_lt_omega {ι : Type*} {s : set ι}
  (b : basis s R M) (h : module.rank R M < cardinal.omega) :
  s.finite :=
finite_def.2 (b.nonempty_fintype_index_of_dim_lt_omega h)

lemma dim_span {v : ι → M} (hv : linear_independent R v) :
  module.rank R ↥(span R (range v)) = #(range v) :=
begin
  haveI := nontrivial_of_invariant_basis_number R,
  rw [←cardinal.lift_inj, ← (basis.span hv).mk_eq_dim,
    cardinal.mk_range_eq_of_injective (@linear_independent.injective ι R M v _ _ _ _ hv)]
end

lemma dim_span_set {s : set M} (hs : linear_independent R (λ x, x : s → M)) :
  module.rank R ↥(span R s) = #s :=
by { rw [← @set_of_mem_eq _ s, ← subtype.range_coe_subtype], exact dim_span hs }

/-- If `N` is a submodule in a free, finitely generated module,
do induction on adjoining a linear independent element to a submodule. -/
def submodule.induction_on_rank [is_domain R] [fintype ι] (b : basis ι R M)
  (P : submodule R M → Sort*) (ih : ∀ (N : submodule R M),
    (∀ (N' ≤ N) (x ∈ N), (∀ (c : R) (y ∈ N'), c • x + y = (0 : M) → c = 0) → P N') →
    P N)
  (N : submodule R M) : P N :=
submodule.induction_on_rank_aux b P ih (fintype.card ι) N (λ s hs hli,
  by simpa using b.card_le_card_of_linear_independent hli)

/-- If `S` a finite-dimensional ring extension of `R` which is free as an `R`-module,
then the rank of an ideal `I` of `S` over `R` is the same as the rank of `S`.
-/
lemma ideal.rank_eq {R S : Type*} [comm_ring R] [strong_rank_condition R] [ring S] [is_domain S]
  [algebra R S] {n m : Type*} [fintype n] [fintype m]
  (b : basis n R S) {I : ideal S} (hI : I ≠ ⊥) (c : basis m R I) :
  fintype.card m = fintype.card n :=
begin
  obtain ⟨a, ha⟩ := submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI),
  have : linear_independent R (λ i, b i • a),
  { have hb := b.linear_independent,
    rw fintype.linear_independent_iff at ⊢ hb,
    intros g hg,
    apply hb g,
    simp only [← smul_assoc, ← finset.sum_smul, smul_eq_zero] at hg,
    exact hg.resolve_right ha },
  exact le_antisymm
    (b.card_le_card_of_linear_independent (c.linear_independent.map' (submodule.subtype I)
      (linear_map.ker_eq_bot.mpr subtype.coe_injective)))
    (c.card_le_card_of_linear_independent this),
end

variables (R)

@[simp] lemma dim_self : module.rank R R = 1 :=
by rw [←cardinal.lift_inj, ← (basis.singleton punit R).mk_eq_dim, cardinal.mk_punit]

end strong_rank_condition

section division_ring
variables [division_ring K] [add_comm_group V] [module K V] [add_comm_group V₁] [module K V₁]
variables {K V}

/-- If a vector space has a finite dimension, the index set of `basis.of_vector_space` is finite. -/
lemma basis.finite_of_vector_space_index_of_dim_lt_omega (h : module.rank K V < cardinal.omega) :
  (basis.of_vector_space_index K V).finite :=
finite_def.2 $ (basis.of_vector_space K V).nonempty_fintype_index_of_dim_lt_omega h

variables [add_comm_group V'] [module K V']

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_lift_dim_eq
  (cond : cardinal.lift.{v'} (module.rank K V) = cardinal.lift.{v} (module.rank K V')) :
  nonempty (V ≃ₗ[K] V') :=
begin
  let B := basis.of_vector_space K V,
  let B' := basis.of_vector_space K V',
  have : cardinal.lift.{v' v} (#_) = cardinal.lift.{v v'} (#_),
    by rw [B.mk_eq_dim'', cond, B'.mk_eq_dim''],
  exact (cardinal.lift_mk_eq.{v v' 0}.1 this).map (B.equiv B')
end

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_dim_eq (cond : module.rank K V = module.rank K V₁) :
  nonempty (V ≃ₗ[K] V₁) :=
nonempty_linear_equiv_of_lift_dim_eq $ congr_arg _ cond

section

variables (V V' V₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def linear_equiv.of_lift_dim_eq
  (cond : cardinal.lift.{v'} (module.rank K V) = cardinal.lift.{v} (module.rank K V')) :
  V ≃ₗ[K] V' :=
classical.choice (nonempty_linear_equiv_of_lift_dim_eq cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def linear_equiv.of_dim_eq (cond : module.rank K V = module.rank K V₁) : V ≃ₗ[K] V₁ :=
classical.choice (nonempty_linear_equiv_of_dim_eq cond)

end

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem linear_equiv.nonempty_equiv_iff_lift_dim_eq :
  nonempty (V ≃ₗ[K] V') ↔
    cardinal.lift.{v'} (module.rank K V) = cardinal.lift.{v} (module.rank K V') :=
⟨λ ⟨h⟩, linear_equiv.lift_dim_eq h, λ h, nonempty_linear_equiv_of_lift_dim_eq h⟩

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem linear_equiv.nonempty_equiv_iff_dim_eq :
  nonempty (V ≃ₗ[K] V₁) ↔ module.rank K V = module.rank K V₁ :=
⟨λ ⟨h⟩, linear_equiv.dim_eq h, λ h, nonempty_linear_equiv_of_dim_eq h⟩

-- TODO how far can we generalise this?
-- When `s` is finite, we could prove this for any ring satisfying the strong rank condition
-- using `linear_independent_le_span'`
lemma dim_span_le (s : set V) : module.rank K (span K s) ≤ #s :=
begin
  obtain ⟨b, hb, hsab, hlib⟩ := exists_linear_independent K s,
  convert cardinal.mk_le_mk_of_subset hb,
  rw [← hsab, dim_span_set hlib]
end

lemma dim_span_of_finset (s : finset V) :
  module.rank K (span K (↑s : set V)) < cardinal.omega :=
calc module.rank K (span K (↑s : set V)) ≤ #(↑s : set V) : dim_span_le ↑s
                             ... = s.card : by rw [cardinal.finset_card, finset.coe_sort_coe]
                             ... < cardinal.omega : cardinal.nat_lt_omega _

theorem dim_prod : module.rank K (V × V₁) = module.rank K V + module.rank K V₁ :=
begin
  let b := basis.of_vector_space K V,
  let c := basis.of_vector_space K V₁,
  rw [← cardinal.lift_inj,
      ← (basis.prod b c).mk_eq_dim,
      cardinal.lift_add, ← cardinal.mk_ulift,
      ← b.mk_eq_dim, ← c.mk_eq_dim,
      ← cardinal.mk_ulift, ← cardinal.mk_ulift,
      cardinal.add_def (ulift _)],
  exact cardinal.lift_inj.1 (cardinal.lift_mk_eq.2
      ⟨equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm ⟩),
end

section fintype
variable [fintype η]
variables [∀i, add_comm_group (φ i)] [∀i, module K (φ i)]

open linear_map

lemma dim_pi : module.rank K (Πi, φ i) = cardinal.sum (λi, module.rank K (φ i)) :=
begin
  let b := assume i, basis.of_vector_space K (φ i),
  let this : basis (Σ j, _) K (Π j, φ j) := pi.basis b,
  rw [← cardinal.lift_inj, ← this.mk_eq_dim],
  simp [← (b _).mk_range_eq_dim]
end

lemma dim_fun {V η : Type u} [fintype η] [add_comm_group V] [module K V] :
  module.rank K (η → V) = fintype.card η * module.rank K V :=
by rw [dim_pi, cardinal.sum_const', cardinal.fintype_card]

lemma dim_fun_eq_lift_mul :
  module.rank K (η → V) = (fintype.card η : cardinal.{max u₁' v}) *
    cardinal.lift.{u₁'} (module.rank K V) :=
by rw [dim_pi, cardinal.sum_const, cardinal.fintype_card, cardinal.lift_nat_cast]

lemma dim_fun' : module.rank K (η → K) = fintype.card η :=
by rw [dim_fun_eq_lift_mul, dim_self, cardinal.lift_one, mul_one, cardinal.nat_cast_inj]

lemma dim_fin_fun (n : ℕ) : module.rank K (fin n → K) = n :=
by simp [dim_fun']

end fintype

end division_ring

section field
variables [field K] [add_comm_group V] [module K V] [add_comm_group V₁] [module K V₁]
variables [add_comm_group V'] [module K V']
variables {K V}

theorem dim_quotient_add_dim (p : submodule K V) :
  module.rank K p.quotient + module.rank K p = module.rank K V :=
by classical; exact let ⟨f⟩ := quotient_prod_linear_equiv p in dim_prod.symm.trans f.dim_eq

/-- rank-nullity theorem -/
theorem dim_range_add_dim_ker (f : V →ₗ[K] V₁) :
  module.rank K f.range + module.rank K f.ker = module.rank K V :=
begin
  haveI := λ (p : submodule K V), classical.dec_eq p.quotient,
  rw [← f.quot_ker_equiv_range.dim_eq, dim_quotient_add_dim]
end

lemma dim_eq_of_surjective (f : V →ₗ[K] V₁) (h : surjective f) :
  module.rank K V = module.rank K V₁ + module.rank K f.ker :=
by rw [← dim_range_add_dim_ker f, ← dim_range_of_surjective f h]

section
variables [add_comm_group V₂] [module K V₂]
variables [add_comm_group V₃] [module K V₃]
open linear_map

/-- This is mostly an auxiliary lemma for `dim_sup_add_dim_inf_eq`. -/
lemma dim_add_dim_split
  (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂) (ce : V₁ →ₗ[K] V₃)
  (hde : ⊤ ≤ db.range ⊔ eb.range)
  (hgd : ker cd = ⊥)
  (eq : db.comp cd = eb.comp ce)
  (eq₂ : ∀d e, db d = eb e → (∃c, cd c = d ∧ ce c = e)) :
  module.rank K V + module.rank K V₁ = module.rank K V₂ + module.rank K V₃ :=
have hf : surjective (coprod db eb),
begin
  refine (range_eq_top.1 $ top_unique $ _),
  rwa [← map_top, ← prod_top, map_coprod_prod, ←range_eq_map, ←range_eq_map]
end,
begin
  conv {to_rhs, rw [← dim_prod, dim_eq_of_surjective _ hf] },
  congr' 1,
  apply linear_equiv.dim_eq,
  refine linear_equiv.of_bijective _ _ _,
  { refine cod_restrict _ (prod cd (- ce)) _,
    { assume c,
      simp only [add_eq_zero_iff_eq_neg, linear_map.prod_apply, mem_ker,
        coprod_apply, neg_neg, map_neg, neg_apply],
      exact linear_map.ext_iff.1 eq c } },
  { rw [← ker_eq_bot, ker_cod_restrict, ker_prod, hgd, bot_inf_eq] },
  { rw [← range_eq_top, eq_top_iff, range_cod_restrict, ← map_le_iff_le_comap,
      map_top, range_subtype],
    rintros ⟨d, e⟩,
    have h := eq₂ d (-e),
    simp only [add_eq_zero_iff_eq_neg, linear_map.prod_apply, mem_ker, set_like.mem_coe,
      prod.mk.inj_iff, coprod_apply, map_neg, neg_apply, linear_map.mem_range] at ⊢ h,
    assume hde,
    rcases h hde with ⟨c, h₁, h₂⟩,
    refine ⟨c, h₁, _⟩,
    rw [h₂, _root_.neg_neg] }
end

lemma dim_sup_add_dim_inf_eq (s t : submodule K V) :
  module.rank K (s ⊔ t : submodule K V) + module.rank K (s ⊓ t : submodule K V) =
    module.rank K s + module.rank K t :=
dim_add_dim_split (of_le le_sup_left) (of_le le_sup_right) (of_le inf_le_left) (of_le inf_le_right)
  begin
    rw [← map_le_map_iff' (ker_subtype $ s ⊔ t), map_sup, map_top,
      ← linear_map.range_comp, ← linear_map.range_comp, subtype_comp_of_le, subtype_comp_of_le,
      range_subtype, range_subtype, range_subtype],
    exact le_refl _
  end
  (ker_of_le _ _ _)
  begin ext ⟨x, hx⟩, refl end
  begin
    rintros ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ eq,
    have : b₁ = b₂ := congr_arg subtype.val eq,
    subst this,
    exact ⟨⟨b₁, hb₁, hb₂⟩, rfl, rfl⟩
  end

lemma dim_add_le_dim_add_dim (s t : submodule K V) :
  module.rank K (s ⊔ t : submodule K V) ≤ module.rank K s + module.rank K t :=
by { rw [← dim_sup_add_dim_inf_eq], exact self_le_add_right _ _ }

end

lemma exists_mem_ne_zero_of_dim_pos {s : submodule K V} (h : 0 < module.rank K s) :
  ∃ b : V, b ∈ s ∧ b ≠ 0 :=
exists_mem_ne_zero_of_ne_bot $ assume eq, by rw [eq, dim_bot] at h; exact lt_irrefl _ h

section rank

-- TODO This definition, and some of the results about it, could be generalized to arbitrary rings.
/-- `rank f` is the rank of a `linear_map f`, defined as the dimension of `f.range`. -/
def rank (f : V →ₗ[K] V') : cardinal := module.rank K f.range

lemma rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ module.rank K V :=
by { rw [← dim_range_add_dim_ker f], exact self_le_add_right _ _ }

lemma rank_le_range (f : V →ₗ[K] V₁) : rank f ≤ module.rank K V₁ :=
dim_submodule_le _

lemma rank_add_le (f g : V →ₗ[K] V') : rank (f + g) ≤ rank f + rank g :=
calc rank (f + g) ≤ module.rank K (f.range ⊔ g.range : submodule K V') :
  begin
    refine dim_le_of_submodule _ _ _,
    exact (linear_map.range_le_iff_comap.2 $ eq_top_iff'.2 $
      assume x, show f x + g x ∈ (f.range ⊔ g.range : submodule K V'), from
        mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩)
  end
  ... ≤ rank f + rank g : dim_add_le_dim_add_dim _ _

@[simp] lemma rank_zero : rank (0 : V →ₗ[K] V') = 0 :=
by rw [rank, linear_map.range_zero, dim_bot]

lemma rank_finset_sum_le {η} (s : finset η) (f : η → V →ₗ[K] V') :
  rank (∑ d in s, f d) ≤ ∑ d in s, rank (f d) :=
@finset.sum_hom_rel _ _ _ _ _ (λa b, rank a ≤ b) f (λ d, rank (f d)) s (le_of_eq rank_zero)
      (λ i g c h, le_trans (rank_add_le _ _) (add_le_add_left h _))

variables [add_comm_group V''] [module K V'']

lemma rank_comp_le1 (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') : rank (f.comp g) ≤ rank f :=
begin
  refine dim_le_of_submodule _ _ _,
  rw [linear_map.range_comp],
  exact linear_map.map_le_range,
end

variables [add_comm_group V'₁] [module K V'₁]

lemma rank_comp_le2 (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) : rank (f.comp g) ≤ rank g :=
by rw [rank, rank, linear_map.range_comp]; exact dim_map_le _ _

end rank

-- TODO The remainder of this file could be generalized to arbitrary rings.


/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `finite_dimensional.fin_basis`.
-/
def basis.of_dim_eq_zero {ι : Type*} [is_empty ι] (hV : module.rank K V = 0) :
  basis ι K V :=
begin
  haveI : subsingleton V := dim_zero_iff.1 hV,
  exact basis.empty _
end

@[simp] lemma basis.of_dim_eq_zero_apply {ι : Type*} [is_empty ι]
  (hV : module.rank K V = 0) (i : ι) :
  basis.of_dim_eq_zero hV i = 0 :=
rfl

lemma le_dim_iff_exists_linear_independent {c : cardinal} :
  c ≤ module.rank K V ↔ ∃ s : set V, #s = c ∧ linear_independent K (coe : s → V) :=
begin
  split,
  { intro h,
    let t := basis.of_vector_space K V,
    rw [← t.mk_eq_dim'', cardinal.le_mk_iff_exists_subset] at h,
    rcases h with ⟨s, hst, hsc⟩,
    exact ⟨s, hsc, (of_vector_space_index.linear_independent K V).mono hst⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact cardinal_le_dim_of_linear_independent si }
end

lemma le_dim_iff_exists_linear_independent_finset {n : ℕ} :
  ↑n ≤ module.rank K V ↔
    ∃ s : finset V, s.card = n ∧ linear_independent K (coe : (s : set V) → V) :=
begin
  simp only [le_dim_iff_exists_linear_independent, cardinal.mk_eq_nat_iff_finset],
  split,
  { rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩,
    exact ⟨t, rfl, si⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩ }
end

lemma le_rank_iff_exists_linear_independent {c : cardinal} {f : V →ₗ[K] V'} :
  c ≤ rank f ↔
  ∃ s : set V, cardinal.lift.{v'} (#s) = cardinal.lift.{v} c ∧
    linear_independent K (λ x : s, f x) :=
begin
  rcases f.range_restrict.exists_right_inverse_of_surjective f.range_range_restrict with ⟨g, hg⟩,
  have fg : left_inverse f.range_restrict g, from linear_map.congr_fun hg,
  refine ⟨λ h, _, _⟩,
  { rcases le_dim_iff_exists_linear_independent.1 h with ⟨s, rfl, si⟩,
    refine ⟨g '' s, cardinal.mk_image_eq_lift _ _ fg.injective, _⟩,
    replace fg : ∀ x, f (g x) = x, by { intro x, convert congr_arg subtype.val (fg x) },
    replace si : linear_independent K (λ x : s, f (g x)),
      by simpa only [fg] using si.map' _ (ker_subtype _),
    exact si.image_of_comp s g f },
  { rintro ⟨s, hsc, si⟩,
    have : linear_independent K (λ x : s, f.range_restrict x),
      from linear_independent.of_comp (f.range.subtype) (by convert si),
    convert cardinal_le_dim_of_linear_independent this.image,
    rw [← cardinal.lift_inj, ← hsc, cardinal.mk_image_eq_of_inj_on_lift],
    exact inj_on_iff_injective.2 this.injective }
end

lemma le_rank_iff_exists_linear_independent_finset {n : ℕ} {f : V →ₗ[K] V'} :
  ↑n ≤ rank f ↔ ∃ s : finset V, s.card = n ∧ linear_independent K (λ x : (s : set V), f x) :=
begin
  simp only [le_rank_iff_exists_linear_independent, cardinal.lift_nat_cast,
    cardinal.lift_eq_nat_iff, cardinal.mk_eq_nat_iff_finset],
  split,
  { rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩,
    exact ⟨t, rfl, si⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩ }
end

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
lemma dim_le_one_iff : module.rank K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v :=
begin
  let b := basis.of_vector_space K V,
  split,
  { intro hd,
    rw [← b.mk_eq_dim'', cardinal.le_one_iff_subsingleton, subsingleton_coe] at hd,
    rcases eq_empty_or_nonempty (of_vector_space_index K V) with hb | ⟨⟨v₀, hv₀⟩⟩,
    { use 0,
      have h' : ∀ v : V, v = 0, { simpa [hb, submodule.eq_bot_iff] using b.span_eq.symm },
      intro v,
      simp [h' v] },
    { use v₀,
      have h' : (K ∙ v₀) = ⊤, { simpa [hd.eq_singleton_of_mem hv₀] using b.span_eq },
      intro v,
      have hv : v ∈ (⊤ : submodule K V) := mem_top,
      rwa [←h', mem_span_singleton] at hv } },
  { rintros ⟨v₀, hv₀⟩,
    have h : (K ∙ v₀) = ⊤,
    { ext, simp [mem_span_singleton, hv₀] },
    rw [←dim_top, ←h],
    convert dim_span_le _,
    simp }
end

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
lemma dim_submodule_le_one_iff (s : submodule K V) : module.rank K s ≤ 1 ↔ ∃ v₀ ∈ s, s ≤ K ∙ v₀ :=
begin
  simp_rw [dim_le_one_iff, le_span_singleton_iff],
  split,
  { rintro ⟨⟨v₀, hv₀⟩, h⟩,
    use [v₀, hv₀],
    intros v hv,
    obtain ⟨r, hr⟩ := h ⟨v, hv⟩,
    use r,
    simp_rw [subtype.ext_iff, coe_smul, submodule.coe_mk] at hr,
    exact hr },
  { rintro ⟨v₀, hv₀, h⟩,
    use ⟨v₀, hv₀⟩,
    rintro ⟨v, hv⟩,
    obtain ⟨r, hr⟩ := h v hv,
    use r,
    simp_rw [subtype.ext_iff, coe_smul, submodule.coe_mk],
    exact hr }
end

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
lemma dim_submodule_le_one_iff' (s : submodule K V) : module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K ∙ v₀ :=
begin
  rw dim_submodule_le_one_iff,
  split,
  { rintros ⟨v₀, hv₀, h⟩,
    exact ⟨v₀, h⟩ },
  { rintros ⟨v₀, h⟩,
    by_cases hw : ∃ w : V, w ∈ s ∧ w ≠ 0,
    { rcases hw with ⟨w, hw, hw0⟩,
      use [w, hw],
      rcases mem_span_singleton.1 (h hw) with ⟨r', rfl⟩,
      have h0 : r' ≠ 0,
      { rintro rfl,
        simpa using hw0 },
      rwa span_singleton_smul_eq _ h0 },
    { push_neg at hw,
      rw ←submodule.eq_bot_iff at hw,
      simp [hw] } }
end

end field

end module
