/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import ring_theory.nakayama
import data.set_like.fintype

/-!
# Artinian rings and modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


A module satisfying these equivalent conditions is said to be an *Artinian* R-module
if every decreasing chain of submodules is eventually constant, or equivalently,
if the relation `<` on submodules is well founded.

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `is_artinian R M` is the proposition that `M` is a Artinian `R`-module. It is a class,
  implemented as the predicate that the `<` relation on submodules is well founded.
* `is_artinian_ring R` is the proposition that `R` is a left Artinian ring.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

## Tags

Artinian, artinian, Artinian ring, Artinian module, artinian ring, artinian module

-/
open set
open_locale big_operators pointwise

/--
`is_artinian R M` is the proposition that `M` is an Artinian `R`-module,
implemented as the well-foundedness of submodule inclusion.
-/
class is_artinian (R M) [semiring R] [add_comm_monoid M] [module R M] : Prop :=
(well_founded_submodule_lt [] : well_founded ((<) : submodule R M → submodule R M → Prop))

section
variables {R M P N : Type*}

variables [ring R] [add_comm_group M] [add_comm_group P] [add_comm_group N]
variables [module R M] [module R P] [module R N]
open is_artinian
include R

theorem is_artinian_of_injective (f : M →ₗ[R] P) (h : function.injective f)
  [is_artinian R P] : is_artinian R M :=
⟨subrelation.wf
  (λ A B hAB, show A.map f < B.map f,
    from submodule.map_strict_mono_of_injective h hAB)
  (inv_image.wf (submodule.map f) (is_artinian.well_founded_submodule_lt R P))⟩

instance is_artinian_submodule' [is_artinian R M] (N : submodule R M) : is_artinian R N :=
is_artinian_of_injective N.subtype subtype.val_injective

lemma is_artinian_of_le {s t : submodule R M} [ht : is_artinian R t]
   (h : s ≤ t) : is_artinian R s :=
is_artinian_of_injective (submodule.of_le h) (submodule.of_le_injective h)

variable (M)
theorem is_artinian_of_surjective (f : M →ₗ[R] P) (hf : function.surjective f)
  [is_artinian R M] : is_artinian R P :=
⟨subrelation.wf
  (λ A B hAB, show A.comap f < B.comap f,
    from submodule.comap_strict_mono_of_surjective hf hAB)
  (inv_image.wf (submodule.comap f) (is_artinian.well_founded_submodule_lt _ _))⟩
variable {M}

theorem is_artinian_of_linear_equiv (f : M ≃ₗ[R] P)
  [is_artinian R M] : is_artinian R P :=
is_artinian_of_surjective _ f.to_linear_map f.to_equiv.surjective

theorem is_artinian_of_range_eq_ker
  [is_artinian R M] [is_artinian R P]
  (f : M →ₗ[R] N) (g : N →ₗ[R] P)
  (hf : function.injective f)
  (hg : function.surjective g)
  (h : f.range = g.ker) :
  is_artinian R N :=
⟨well_founded_lt_exact_sequence
  (is_artinian.well_founded_submodule_lt _ _)
  (is_artinian.well_founded_submodule_lt _ _)
  f.range
  (submodule.map f)
  (submodule.comap f)
  (submodule.comap g)
  (submodule.map g)
  (submodule.gci_map_comap hf)
  (submodule.gi_map_comap hg)
  (by simp [submodule.map_comap_eq, inf_comm])
  (by simp [submodule.comap_map_eq, h])⟩

instance is_artinian_prod [is_artinian R M]
  [is_artinian R P] : is_artinian R (M × P) :=
is_artinian_of_range_eq_ker
  (linear_map.inl R M P)
  (linear_map.snd R M P)
  linear_map.inl_injective
  linear_map.snd_surjective
  (linear_map.range_inl R M P)

@[priority 100]
instance is_artinian_of_finite [finite M] : is_artinian R M :=
⟨finite.well_founded_of_trans_of_irrefl _⟩

local attribute [elab_as_eliminator] finite.induction_empty_option

instance is_artinian_pi {R ι : Type*} [finite ι] : Π {M : ι → Type*} [ring R]
  [Π i, add_comm_group (M i)], by exactI Π [Π i, module R (M i)],
  by exactI Π [∀ i, is_artinian R (M i)], is_artinian R (Π i, M i) :=
finite.induction_empty_option
  (begin
    introsI α β e hα M _ _ _ _,
    exact is_artinian_of_linear_equiv
      (linear_equiv.Pi_congr_left R M e)
  end)
  (by { introsI M _ _ _ _, apply_instance })
  (begin
     introsI α _ ih M _ _ _ _,
     exact is_artinian_of_linear_equiv
        (linear_equiv.pi_option_equiv_prod R).symm,
  end)
  ι

/-- A version of `is_artinian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance is_artinian_pi' {R ι M : Type*} [ring R] [add_comm_group M] [module R M] [finite ι]
  [is_artinian R M] : is_artinian R (ι → M) :=
is_artinian_pi

end

open is_artinian submodule function

section ring

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

theorem is_artinian_iff_well_founded :
  is_artinian R M ↔ well_founded ((<) : submodule R M → submodule R M → Prop) :=
⟨λ h, h.1, is_artinian.mk⟩

variables {R M}

lemma is_artinian.finite_of_linear_independent [nontrivial R] [is_artinian R M]
  {s : set M} (hs : linear_independent R (coe : s → M)) : s.finite :=
begin
  refine classical.by_contradiction (λ hf, (rel_embedding.well_founded_iff_no_descending_seq.1
    (well_founded_submodule_lt R M)).elim' _),
  have f : ℕ ↪ s, from set.infinite.nat_embedding s hf,
  have : ∀ n, (coe ∘ f) '' {m | n ≤ m} ⊆ s,
  { rintros n x ⟨y, hy₁, rfl⟩, exact (f y).2 },
  have : ∀ a b : ℕ, a ≤ b ↔
    span R ((coe ∘ f) '' {m | b ≤ m}) ≤ span R ((coe ∘ f) '' {m | a ≤ m}),
  { assume a b,
    rw [span_le_span_iff hs (this b) (this a),
      set.image_subset_image_iff (subtype.coe_injective.comp f.injective),
      set.subset_def],
    simp only [set.mem_set_of_eq],
    exact ⟨λ hab x, le_trans hab, λ h, (h _ le_rfl)⟩ },
  exact ⟨⟨λ n, span R ((coe ∘ f) '' {m | n ≤ m}),
      λ x y, by simp [le_antisymm_iff, (this _ _).symm] {contextual := tt}⟩,
    begin
      intros a b,
      conv_rhs { rw [gt, lt_iff_le_not_le, this, this, ← lt_iff_le_not_le] },
      simp
    end⟩
end

/-- A module is Artinian iff every nonempty set of submodules has a minimal submodule among them.
-/
theorem set_has_minimal_iff_artinian :
  (∀ a : set $ submodule R M, a.nonempty → ∃ M' ∈ a, ∀ I ∈ a, ¬ I < M') ↔ is_artinian R M :=
by rw [is_artinian_iff_well_founded, well_founded.well_founded_iff_has_min]

theorem is_artinian.set_has_minimal [is_artinian R M] (a : set $ submodule R M) (ha : a.nonempty) :
  ∃ M' ∈ a, ∀ I ∈ a, ¬ I < M' :=
set_has_minimal_iff_artinian.mpr ‹_› a ha

/-- A module is Artinian iff every decreasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_artinian :
  (∀ (f : ℕ →o (submodule R M)ᵒᵈ), ∃ n, ∀ m, n ≤ m → f n = f m) ↔ is_artinian R M :=
by { rw is_artinian_iff_well_founded, exact well_founded.monotone_chain_condition.symm }

namespace is_artinian

variables [is_artinian R M]

theorem monotone_stabilizes (f : ℕ →o (submodule R M)ᵒᵈ) : ∃ n, ∀ m, n ≤ m → f n = f m :=
monotone_stabilizes_iff_artinian.mpr ‹_› f

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
lemma induction {P : submodule R M → Prop} (hgt : ∀ I, (∀ J < I, P J) → P I) (I : submodule R M) :
  P I :=
(well_founded_submodule_lt R M).recursion I hgt

/--
For any endomorphism of a Artinian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem exists_endomorphism_iterate_ker_sup_range_eq_top (f : M →ₗ[R] M) :
  ∃ n : ℕ, n ≠ 0 ∧ (f ^ n).ker ⊔ (f ^ n).range = ⊤ :=
begin
  obtain ⟨n, w⟩ := monotone_stabilizes (f.iterate_range.comp ⟨λ n, n+1, λ n m w, by linarith⟩),
  specialize w ((n + 1) + n) (by linarith),
  dsimp at w,
  refine ⟨n + 1, nat.succ_ne_zero _, _⟩,
  simp_rw [eq_top_iff', mem_sup],
  intro x,
  have : (f^(n + 1)) x ∈ (f ^ ((n + 1) + n + 1)).range,
  { rw ← w, exact mem_range_self _ },
  rcases this with ⟨y, hy⟩,
  use x - (f ^ (n+1)) y,
  split,
  { rw [linear_map.mem_ker, linear_map.map_sub, ← hy, sub_eq_zero, pow_add],
    simp [iterate_add_apply], },
  { use (f^ (n+1)) y,
    simp }
end

/-- Any injective endomorphism of an Artinian module is surjective. -/
theorem surjective_of_injective_endomorphism (f : M →ₗ[R] M) (s : injective f) : surjective f :=
begin
  obtain ⟨n, ne, w⟩ := exists_endomorphism_iterate_ker_sup_range_eq_top f,
  rw [linear_map.ker_eq_bot.mpr (linear_map.iterate_injective s n), bot_sup_eq,
    linear_map.range_eq_top] at w,
  exact linear_map.surjective_of_iterate_surjective ne w,
end

/-- Any injective endomorphism of an Artinian module is bijective. -/
theorem bijective_of_injective_endomorphism (f : M →ₗ[R] M) (s : injective f) : bijective f :=
⟨s, surjective_of_injective_endomorphism f s⟩

/--
A sequence `f` of submodules of a artinian module,
with the supremum `f (n+1)` and the infinum of `f 0`, ..., `f n` being ⊤,
is eventually ⊤.
-/
lemma disjoint_partial_infs_eventually_top (f : ℕ → submodule R M)
  (h : ∀ n, disjoint (partial_sups (order_dual.to_dual ∘ f) n) (order_dual.to_dual (f (n+1)))) :
  ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊤  :=
begin
  -- A little off-by-one cleanup first:
  rsuffices ⟨n, w⟩ : ∃ n : ℕ, ∀ m, n ≤ m → order_dual.to_dual f (m+1) = ⊤,
  { use n+1,
    rintros (_|m) p,
    { cases p, },
    { apply w,
      exact nat.succ_le_succ_iff.mp p }, },

  obtain ⟨n, w⟩ := monotone_stabilizes (partial_sups (order_dual.to_dual ∘ f)),
  refine ⟨n, λ m p, _⟩,
  exact (h m).eq_bot_of_ge (sup_eq_left.1 $ (w (m + 1) $ le_add_right p).symm.trans $ w m p)
end

end is_artinian

end ring

section comm_ring

variables {R : Type*} (M : Type*) [comm_ring R] [add_comm_group M] [module R M] [is_artinian R M]

namespace is_artinian

lemma range_smul_pow_stabilizes (r : R) : ∃ n : ℕ, ∀ m, n ≤ m →
  (r^n • linear_map.id : M →ₗ[R] M).range = (r^m • linear_map.id : M →ₗ[R] M).range :=
monotone_stabilizes
⟨λ n, (r^n • linear_map.id : M →ₗ[R] M).range,
 λ n m h x ⟨y, hy⟩, ⟨r ^ (m - n) • y,
   by { dsimp at ⊢ hy, rw [←smul_assoc, smul_eq_mul, ←pow_add, ←hy, add_tsub_cancel_of_le h] }⟩⟩

variables {M}

lemma exists_pow_succ_smul_dvd (r : R) (x : M) :
  ∃ (n : ℕ) (y : M), r ^ n.succ • y = r ^ n • x :=
begin
  obtain ⟨n, hn⟩ := is_artinian.range_smul_pow_stabilizes M r,
  simp_rw [set_like.ext_iff] at hn,
  exact ⟨n, by simpa using hn n.succ n.le_succ (r ^ n • x)⟩,
end

end is_artinian

end comm_ring

-- TODO: Prove this for artinian modules
-- /--
-- If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-- -/
-- universe w
-- variables {N : Type w} [add_comm_group N] [module R N]
-- noncomputable def is_noetherian.equiv_punit_of_prod_injective [is_noetherian R M]
--   (f : M × N →ₗ[R] M) (i : injective f) : N ≃ₗ[R] punit.{w+1} :=
-- begin
--   apply nonempty.some,
--   obtain ⟨n, w⟩ := is_noetherian.disjoint_partial_sups_eventually_bot (f.tailing i)
--     (f.tailings_disjoint_tailing i),
--   specialize w n (le_refl n),
--   apply nonempty.intro,
--   refine (f.tailing_linear_equiv i n).symm.trans _,
--   rw w,
--   exact submodule.bot_equiv_punit,
-- end

/-- A ring is Artinian if it is Artinian as a module over itself.

Strictly speaking, this should be called `is_left_artinian_ring` but we omit the `left_` for
convenience in the commutative case. For a right Artinian ring, use `is_artinian Rᵐᵒᵖ R`. -/
@[reducible] def is_artinian_ring (R) [ring R] := is_artinian R R

theorem is_artinian_ring_iff {R} [ring R] : is_artinian_ring R ↔ is_artinian R R :=
iff.rfl

theorem ring.is_artinian_of_zero_eq_one {R} [ring R] (h01 : (0 : R) = 1) : is_artinian_ring R :=
have _ := subsingleton_of_zero_eq_one h01, by exactI infer_instance

theorem is_artinian_of_submodule_of_artinian (R M) [ring R] [add_comm_group M] [module R M]
  (N : submodule R M) (h : is_artinian R M) : is_artinian R N :=
by apply_instance

theorem is_artinian_of_quotient_of_artinian (R) [ring R] (M) [add_comm_group M] [module R M]
  (N : submodule R M) (h : is_artinian R M) : is_artinian R (M ⧸ N) :=
is_artinian_of_surjective M (submodule.mkq N) (submodule.quotient.mk_surjective N)

/-- If `M / S / R` is a scalar tower, and `M / R` is Artinian, then `M / S` is
also Artinian. -/
theorem is_artinian_of_tower (R) {S M} [comm_ring R] [ring S]
  [add_comm_group M] [algebra R S] [module S M] [module R M] [is_scalar_tower R S M]
  (h : is_artinian R M) : is_artinian S M :=
begin
  rw is_artinian_iff_well_founded at h ⊢,
  refine (submodule.restrict_scalars_embedding R S M).well_founded h
end

theorem is_artinian_of_fg_of_artinian {R M} [ring R] [add_comm_group M] [module R M]
  (N : submodule R M) [is_artinian_ring R] (hN : N.fg) : is_artinian R N :=
let ⟨s, hs⟩ := hN in
begin
  haveI := classical.dec_eq M,
  haveI := classical.dec_eq R,
  have : ∀ x ∈ s, x ∈ N, from λ x hx, hs ▸ submodule.subset_span hx,
  refine @@is_artinian_of_surjective ((↑s : set M) → R) _ _ _ (pi.module _ _ _)
    _ _ _ is_artinian_pi,
  { fapply linear_map.mk,
    { exact λ f, ⟨∑ i in s.attach, f i • i.1, N.sum_mem (λ c _, N.smul_mem _ $ this _ c.2)⟩ },
    { intros f g, apply subtype.eq,
      change ∑ i in s.attach, (f i + g i) • _ = _,
      simp only [add_smul, finset.sum_add_distrib], refl },
    { intros c f, apply subtype.eq,
      change ∑ i in s.attach, (c • f i) • _ = _,
      simp only [smul_eq_mul, mul_smul],
      exact finset.smul_sum.symm } },
  rintro ⟨n, hn⟩, change n ∈ N at hn,
  rw [← hs, ← set.image_id ↑s, finsupp.mem_span_image_iff_total] at hn,
  rcases hn with ⟨l, hl1, hl2⟩,
  refine ⟨λ x, l x, subtype.ext _⟩,
  change ∑ i in s.attach, l i • (i : M) = n,
  rw [@finset.sum_attach M M s _ (λ i, l i • i), ← hl2,
      finsupp.total_apply, finsupp.sum, eq_comm],
  refine finset.sum_subset hl1 (λ x _ hx, _),
  rw [finsupp.not_mem_support_iff.1 hx, zero_smul]
end

lemma is_artinian_of_fg_of_artinian' {R M} [ring R] [add_comm_group M] [module R M]
  [is_artinian_ring R] (h : (⊤ : submodule R M).fg) : is_artinian R M :=
have is_artinian R (⊤ : submodule R M), from is_artinian_of_fg_of_artinian _ h,
by exactI is_artinian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl)

/-- In a module over a artinian ring, the submodule generated by finitely many vectors is
artinian. -/
theorem is_artinian_span_of_finite (R) {M} [ring R] [add_comm_group M] [module R M]
  [is_artinian_ring R] {A : set M} (hA : A.finite) : is_artinian R (submodule.span R A) :=
is_artinian_of_fg_of_artinian _ (submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem function.surjective.is_artinian_ring {R} [ring R] {S} [ring S] {F} [ring_hom_class F R S]
  {f : F} (hf : function.surjective f) [H : is_artinian_ring R] : is_artinian_ring S :=
begin
  rw [is_artinian_ring_iff, is_artinian_iff_well_founded] at H ⊢,
  exact (ideal.order_embedding_of_surjective f hf).well_founded H,
end

instance is_artinian_ring_range {R} [ring R] {S} [ring S] (f : R →+* S) [is_artinian_ring R] :
  is_artinian_ring f.range :=
f.range_restrict_surjective.is_artinian_ring

namespace is_artinian_ring

open is_artinian

variables {R : Type*} [comm_ring R] [is_artinian_ring R]

lemma is_nilpotent_jacobson_bot : is_nilpotent (ideal.jacobson (⊥ : ideal R)) :=
begin
  let Jac := ideal.jacobson (⊥ : ideal R),
  let f : ℕ →o (ideal R)ᵒᵈ := ⟨λ n, Jac ^ n, λ _ _ h, ideal.pow_le_pow h⟩,
  obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → Jac ^ n = Jac ^ m := is_artinian.monotone_stabilizes f,
  refine ⟨n, _⟩,
  let J : ideal R := annihilator (Jac ^ n),
  suffices : J = ⊤,
  { have hJ : J • Jac ^ n = ⊥ := annihilator_smul (Jac ^ n),
    simpa only [this, top_smul, ideal.zero_eq_bot] using hJ },
  by_contradiction hJ, change J ≠ ⊤ at hJ,
  rcases is_artinian.set_has_minimal {J' : ideal R | J < J'} ⟨⊤, hJ.lt_top⟩
    with ⟨J', hJJ' : J < J', hJ' : ∀ I, J < I → ¬ I < J'⟩,
  rcases set_like.exists_of_lt hJJ' with ⟨x, hxJ', hxJ⟩,
  obtain rfl : J ⊔ ideal.span {x} = J',
  { apply eq_of_le_of_not_lt _ (hJ' (J ⊔ ideal.span {x}) _),
    { exact (sup_le hJJ'.le (span_le.2 (singleton_subset_iff.2 hxJ'))) },
    { rw set_like.lt_iff_le_and_exists,
      exact ⟨le_sup_left, ⟨x, mem_sup_right (mem_span_singleton_self x), hxJ⟩⟩ } },
  have : J ⊔ Jac • ideal.span {x} ≤ J ⊔ ideal.span {x},
    from sup_le_sup_left (smul_le.2 (λ _ _ _, submodule.smul_mem _ _)) _,
  have : Jac * ideal.span {x} ≤ J, --Need version 4 of Nakayamas lemma on Stacks
  { classical, by_contradiction H,
    refine H (smul_sup_le_of_le_smul_of_le_jacobson_bot
      (fg_span_singleton _) le_rfl (this.eq_of_not_lt (hJ' _ _)).ge),
    exact lt_of_le_of_ne le_sup_left (λ h, H $ h.symm ▸ le_sup_right) },
  have : ideal.span {x} * Jac ^ (n + 1) ≤ ⊥,
    calc ideal.span {x} * Jac ^ (n + 1) = ideal.span {x} * Jac * Jac ^ n :
      by rw [pow_succ, ← mul_assoc]
    ... ≤ J * Jac ^ n : mul_le_mul (by rwa mul_comm) le_rfl
    ... = ⊥ : by simp [J],
  refine hxJ (mem_annihilator.2 (λ y hy, (mem_bot R).1 _)),
  refine this (mul_mem_mul (mem_span_singleton_self x) _),
  rwa [← hn (n + 1) (nat.le_succ _)]
end

section localization

variables (S : submonoid R) (L : Type*) [comm_ring L] [algebra R L] [is_localization S L]

include S

/-- Localizing an artinian ring can only reduce the amount of elements. -/
theorem localization_surjective : function.surjective (algebra_map R L) :=
begin
  intro r',
  obtain ⟨r₁, s, rfl⟩ := is_localization.mk'_surjective S r',
  obtain ⟨r₂, h⟩ : ∃ r : R, is_localization.mk' L 1 s = algebra_map R L r,
  swap, { exact ⟨r₁ * r₂, by rw [is_localization.mk'_eq_mul_mk'_one, map_mul, h]⟩ },
  obtain ⟨n, r, hr⟩ := is_artinian.exists_pow_succ_smul_dvd (s : R) (1 : R),
  use r,
  rw [smul_eq_mul, smul_eq_mul, pow_succ', mul_assoc] at hr,
  apply_fun algebra_map R L at hr,
  simp only [map_mul, ←submonoid.coe_pow] at hr,
  rw [←is_localization.mk'_one L, is_localization.mk'_eq_iff_eq, mul_one, submonoid.coe_one,
      ←(is_localization.map_units L (s ^ n)).mul_left_cancel hr, map_mul],
end

lemma localization_artinian : is_artinian_ring L :=
(localization_surjective S L).is_artinian_ring

/-- `is_artinian_ring.localization_artinian` can't be made an instance, as it would make `S` + `R`
into metavariables. However, this is safe. -/
instance : is_artinian_ring (localization S) := localization_artinian S _

end localization

end is_artinian_ring
