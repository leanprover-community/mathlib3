/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import linear_algebra.basic
import linear_algebra.prod
import linear_algebra.pi
import data.set_like.fintype

open set
open_locale big_operators pointwise

/--
`is_artinian R M` is the proposition that `M` is an Artinian `R`-module,
implemented as the well-foundedness of submodule inclusion.
-/
class is_artinian (R M) [semiring R] [add_comm_monoid M] [module R M] : Prop :=
(well_founded_submodule_lt : well_founded ((<) : submodule R M → submodule R M → Prop))

section
variables {R : Type*} {M : Type*} {P : Type*} {N : Type*}
variables [ring R] [add_comm_group M] [add_comm_group P] [add_comm_group N]
variables [module R M] [module R P] [module R N]
open is_artinian
include R

theorem is_artinian_of_injective (f : M →ₗ[R] P) (h : function.injective f)
  [is_artinian R P] : is_artinian R M :=
⟨subrelation.wf
  (λ A B hAB, show A.map f < B.map f,
    from submodule.map_strict_mono_of_injective h hAB)
  (inv_image.wf (submodule.map f) is_artinian.well_founded_submodule_lt)⟩

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
  (inv_image.wf (submodule.comap f) is_artinian.well_founded_submodule_lt)⟩
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
  is_artinian.well_founded_submodule_lt
  is_artinian.well_founded_submodule_lt
  f.range
  (submodule.map f)
  (submodule.comap f)
  (submodule.comap g)
  (submodule.map g)
  (submodule.gci_map_comap hf)
  (submodule.gi_map_comap hg)
  (by simp [linear_map.map_comap_eq, inf_comm])
  (by simp [linear_map.comap_map_eq, h])⟩

instance is_artinian_prod [is_artinian R M]
  [is_artinian R P] : is_artinian R (M × P) :=
is_artinian_of_range_eq_ker
  (linear_map.inl R M P)
  (linear_map.snd R M P)
  linear_map.inl_injective
  linear_map.snd_surjective
  (linear_map.range_inl R M P)

instance is_artinian_of_fintype [fintype M] : is_artinian R M :=
⟨fintype.well_founded_of_trans_of_irrefl _⟩

local attribute [elab_as_eliminator] fintype.induction_empty_option
#print pi_option
instance is_artinian_pi {R ι : Type*} [fintype ι] : Π {M : ι → Type*} [ring R]
  [Π i, add_comm_group (M i)], by exactI Π [Π i, module R (M i)],
  by exactI Π [∀ i, is_artinian R (M i)], is_artinian R (Π i, M i) :=
fintype.induction_empty_option
  (begin
    introsI α β e hα M _ _ _ _,
    exact is_artinian_of_linear_equiv
      (linear_equiv.Pi_congr_left R M e)
  end)
  (by { introsI M _ _ _ _, apply_instance })
  (begin
     introsI α _ ih M _ _ _ _,
  end)
  ι

/-- A version of `is_noetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance is_noetherian_pi' {R ι M : Type*} [ring R] [add_comm_group M] [module R M] [fintype ι]
  [is_noetherian R M] : is_noetherian R (ι → M) :=
is_noetherian_pi

end

open is_noetherian submodule function

section
variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

theorem is_noetherian_iff_well_founded :
  is_noetherian R M ↔ well_founded ((>) : submodule R M → submodule R M → Prop) :=
begin
  rw (complete_lattice.well_founded_characterisations $ submodule R M).out 0 3,
  exact ⟨λ ⟨h⟩, λ k, (fg_iff_compact k).mp (h k), λ h, ⟨λ k, (fg_iff_compact k).mpr (h k)⟩⟩,
end

variables (R M)

lemma well_founded_submodule_gt (R M) [ring R] [add_comm_group M] [module R M] :
  ∀ [is_noetherian R M], well_founded ((>) : submodule R M → submodule R M → Prop) :=
is_noetherian_iff_well_founded.mp

variables {R M}

lemma finite_of_linear_independent [nontrivial R] [is_noetherian R M]
  {s : set M} (hs : linear_independent R (coe : s → M)) : s.finite :=
begin
  refine classical.by_contradiction (λ hf, (rel_embedding.well_founded_iff_no_descending_seq.1
    (well_founded_submodule_gt R M)).elim' _),
  have f : ℕ ↪ s, from @infinite.nat_embedding s ⟨λ f, hf ⟨f⟩⟩,
  have : ∀ n, (coe ∘ f) '' {m | m ≤ n} ⊆ s,
  { rintros n x ⟨y, hy₁, hy₂⟩, subst hy₂, exact (f y).2 },
  have : ∀ a b : ℕ, a ≤ b ↔
    span R ((coe ∘ f) '' {m | m ≤ a}) ≤ span R ((coe ∘ f) '' {m | m ≤ b}),
  { assume a b,
    rw [span_le_span_iff hs (this a) (this b),
      set.image_subset_image_iff (subtype.coe_injective.comp f.injective),
      set.subset_def],
    exact ⟨λ hab x (hxa : x ≤ a), le_trans hxa hab, λ hx, hx a (le_refl a)⟩ },
  exact ⟨⟨λ n, span R ((coe ∘ f) '' {m | m ≤ n}),
      λ x y, by simp [le_antisymm_iff, (this _ _).symm] {contextual := tt}⟩,
    by dsimp [gt]; simp only [lt_iff_le_not_le, (this _ _).symm]; tauto⟩
end

/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
theorem set_has_maximal_iff_noetherian :
  (∀ a : set $ submodule R M, a.nonempty → ∃ M' ∈ a, ∀ I ∈ a, M' ≤ I → I = M') ↔
  is_noetherian R M :=
by rw [is_noetherian_iff_well_founded, well_founded.well_founded_iff_has_max']

/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
  (∀ (f : ℕ →ₘ submodule R M), ∃ n, ∀ m, n ≤ m → f n = f m)
    ↔ is_noetherian R M :=
by rw [is_noetherian_iff_well_founded, well_founded.monotone_chain_condition]

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
lemma is_noetherian.induction [is_noetherian R M] {P : submodule R M → Prop}
  (hgt : ∀ I, (∀ J > I, P J) → P I) (I : submodule R M) : P I :=
well_founded.recursion (well_founded_submodule_gt R M) I hgt

/--
For any endomorphism of a Noetherian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot
  [I : is_noetherian R M] (f : M →ₗ[R] M) : ∃ n : ℕ, n ≠ 0 ∧ (f ^ n).ker ⊓ (f ^ n).range = ⊥ :=
begin
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I
    (f.iterate_ker.comp ⟨λ n, n+1, λ n m w, by linarith⟩),
  specialize w (2 * n + 1) (by linarith),
  dsimp at w,
  refine ⟨n+1, nat.succ_ne_zero _, _⟩,
  rw eq_bot_iff,
  rintros - ⟨h, ⟨y, rfl⟩⟩,
  rw [mem_bot, ←linear_map.mem_ker, w],
  erw linear_map.mem_ker at h ⊢,
  change ((f ^ (n + 1)) * (f ^ (n + 1))) y = 0 at h,
  rw ←pow_add at h,
  convert h using 3,
  linarith,
end

/-- Any surjective endomorphism of a Noetherian module is injective. -/
theorem is_noetherian.injective_of_surjective_endomorphism [is_noetherian R M]
  (f : M →ₗ[R] M) (s : surjective f) : injective f :=
begin
  obtain ⟨n, ne, w⟩ := is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot f,
  rw [linear_map.range_eq_top.mpr (linear_map.iterate_surjective s n), inf_top_eq,
    linear_map.ker_eq_bot] at w,
  exact linear_map.injective_of_iterate_injective ne w,
end

/-- Any surjective endomorphism of a Noetherian module is bijective. -/
theorem is_noetherian.bijective_of_surjective_endomorphism [is_noetherian R M]
  (f : M →ₗ[R] M) (s : surjective f) : bijective f :=
⟨is_noetherian.injective_of_surjective_endomorphism f s, s⟩

/--
A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
lemma is_noetherian.disjoint_partial_sups_eventually_bot [I : is_noetherian R M]
  (f : ℕ → submodule R M) (h : ∀ n, disjoint (partial_sups f n) (f (n+1))) :
  ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ :=
begin
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m+1) = ⊥,
  { obtain ⟨n, w⟩ := t,
    use n+1,
    rintros (_|m) p,
    { cases p, },
    { apply w,
      exact nat.succ_le_succ_iff.mp p }, },

  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partial_sups f),
  exact ⟨n, (λ m p,
    eq_bot_of_disjoint_absorbs (h m) ((eq.symm (w (m + 1) (le_add_right p))).trans (w m p)))⟩
end

universe w
variables {N : Type w} [add_comm_group N] [module R N]

/--
If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
noncomputable def is_noetherian.equiv_punit_of_prod_injective [is_noetherian R M]
  (f : M × N →ₗ[R] M) (i : injective f) : N ≃ₗ[R] punit.{w+1} :=
begin
  apply nonempty.some,
  obtain ⟨n, w⟩ := is_noetherian.disjoint_partial_sups_eventually_bot (f.tailing i)
    (f.tailings_disjoint_tailing i),
  specialize w n (le_refl n),
  apply nonempty.intro,
  refine (f.tailing_linear_equiv i n).symm.trans _,
  rw w,
  exact submodule.bot_equiv_punit,
end

end

/--
A ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
class is_noetherian_ring (R) [ring R] extends is_noetherian R R : Prop

theorem is_noetherian_ring_iff {R} [ring R] : is_noetherian_ring R ↔ is_noetherian R R :=
⟨λ h, h.1, @is_noetherian_ring.mk _ _⟩

/-- A commutative ring is Noetherian if and only if all its ideals are finitely-generated. -/
lemma is_noetherian_ring_iff_ideal_fg (R : Type*) [comm_ring R] :
  is_noetherian_ring R ↔ ∀ I : ideal R, I.fg :=
is_noetherian_ring_iff.trans is_noetherian_def

@[priority 80] -- see Note [lower instance priority]
instance ring.is_noetherian_of_fintype (R M) [fintype M] [ring R] [add_comm_group M] [module R M] :
  is_noetherian R M :=
by letI := classical.dec; exact
⟨assume s, ⟨to_finset s, by rw [set.coe_to_finset, submodule.span_eq]⟩⟩

theorem ring.is_noetherian_of_zero_eq_one {R} [ring R] (h01 : (0 : R) = 1) : is_noetherian_ring R :=
by haveI := subsingleton_of_zero_eq_one h01;
   haveI := fintype.of_subsingleton (0:R);
   exact is_noetherian_ring_iff.2 (ring.is_noetherian_of_fintype R R)

theorem is_noetherian_of_submodule_of_noetherian (R M) [ring R] [add_comm_group M] [module R M]
  (N : submodule R M) (h : is_noetherian R M) : is_noetherian R N :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  exact order_embedding.well_founded (submodule.map_subtype.order_embedding N).dual h,
end

theorem is_noetherian_of_quotient_of_noetherian (R) [ring R] (M) [add_comm_group M] [module R M]
  (N : submodule R M) (h : is_noetherian R M) : is_noetherian R N.quotient :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  exact order_embedding.well_founded (submodule.comap_mkq.order_embedding N).dual h,
end

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem is_noetherian_of_tower (R) {S M} [comm_ring R] [ring S]
  [add_comm_group M] [algebra R S] [module S M] [module R M] [is_scalar_tower R S M]
  (h : is_noetherian R M) : is_noetherian S M :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  refine (submodule.restrict_scalars_embedding R S M).dual.well_founded h
end

theorem is_noetherian_of_fg_of_noetherian {R M} [ring R] [add_comm_group M] [module R M]
  (N : submodule R M) [is_noetherian_ring R] (hN : N.fg) : is_noetherian R N :=
let ⟨s, hs⟩ := hN in
begin
  haveI := classical.dec_eq M,
  haveI := classical.dec_eq R,
  letI : is_noetherian R R := by apply_instance,
  have : ∀ x ∈ s, x ∈ N, from λ x hx, hs ▸ submodule.subset_span hx,
  refine @@is_noetherian_of_surjective ((↑s : set M) → R) _ _ _ (pi.module _ _ _)
    _ _ _ is_noetherian_pi,
  { fapply linear_map.mk,
    { exact λ f, ⟨∑ i in s.attach, f i • i.1, N.sum_mem (λ c _, N.smul_mem _ $ this _ c.2)⟩ },
    { intros f g, apply subtype.eq,
      change ∑ i in s.attach, (f i + g i) • _ = _,
      simp only [add_smul, finset.sum_add_distrib], refl },
    { intros c f, apply subtype.eq,
      change ∑ i in s.attach, (c • f i) • _ = _,
      simp only [smul_eq_mul, mul_smul],
      exact finset.smul_sum.symm } },
  rw linear_map.range_eq_top,
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

lemma is_noetherian_of_fg_of_noetherian' {R M} [ring R] [add_comm_group M] [module R M]
  [is_noetherian_ring R] (h : (⊤ : submodule R M).fg) : is_noetherian R M :=
have is_noetherian R (⊤ : submodule R M), from is_noetherian_of_fg_of_noetherian _ h,
by exactI is_noetherian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl)

/-- In a module over a noetherian ring, the submodule generated by finitely many vectors is
noetherian. -/
theorem is_noetherian_span_of_finite (R) {M} [ring R] [add_comm_group M] [module R M]
  [is_noetherian_ring R] {A : set M} (hA : finite A) : is_noetherian R (submodule.span R A) :=
is_noetherian_of_fg_of_noetherian _ (submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem is_noetherian_ring_of_surjective (R) [comm_ring R] (S) [comm_ring S]
  (f : R →+* S) (hf : function.surjective f)
  [H : is_noetherian_ring R] : is_noetherian_ring S :=
begin
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at H ⊢,
  exact order_embedding.well_founded (ideal.order_embedding_of_surjective f hf).dual H,
end

instance is_noetherian_ring_range {R} [comm_ring R] {S} [comm_ring S] (f : R →+* S)
  [is_noetherian_ring R] : is_noetherian_ring f.range :=
is_noetherian_ring_of_surjective R f.range f.range_restrict
  f.range_restrict_surjective

theorem is_noetherian_ring_of_ring_equiv (R) [comm_ring R] {S} [comm_ring S]
  (f : R ≃+* S) [is_noetherian_ring R] : is_noetherian_ring S :=
is_noetherian_ring_of_surjective R S f.to_ring_hom f.to_equiv.surjective

namespace submodule
variables {R : Type*} {A : Type*} [comm_ring R] [ring A] [algebra R A]
variables (M N : submodule R A)

theorem fg_mul (hm : M.fg) (hn : N.fg) : (M * N).fg :=
let ⟨m, hfm, hm⟩ := fg_def.1 hm, ⟨n, hfn, hn⟩ := fg_def.1 hn in
fg_def.2 ⟨m * n, hfm.mul hfn, span_mul_span R m n ▸ hm ▸ hn ▸ rfl⟩

lemma fg_pow (h : M.fg) (n : ℕ) : (M ^ n).fg :=
nat.rec_on n
(⟨{1}, by simp [one_eq_span]⟩)
(λ n ih, by simpa [pow_succ] using fg_mul _ _ h ih)

end submodule

section primes

variables {R : Type*} [comm_ring R] [is_noetherian_ring R]

/--In a noetherian ring, every ideal contains a product of prime ideals
([samuel, § 3.3, Lemma 3])-/

lemma exists_prime_spectrum_prod_le (I : ideal R) :
  ∃ (Z : multiset (prime_spectrum R)), multiset.prod (Z.map (coe : subtype _ → ideal R)) ≤ I :=
begin
  refine is_noetherian.induction (λ (M : ideal R) hgt, _) I,
  by_cases h_prM : M.is_prime,
  { use {⟨M, h_prM⟩},
    rw [multiset.map_singleton, multiset.prod_singleton, subtype.coe_mk],
    exact le_rfl },
  by_cases htop : M = ⊤,
  { rw htop,
    exact ⟨0, le_top⟩ },
  have lt_add : ∀ z ∉ M, M < M + span R {z},
  { intros z hz,
    refine lt_of_le_of_ne le_sup_left (λ m_eq, hz _),
    rw m_eq,
    exact mem_sup_right (mem_span_singleton_self z) },
  obtain ⟨x, hx, y, hy, hxy⟩ := (ideal.not_is_prime_iff.mp h_prM).resolve_left htop,
  obtain ⟨Wx, h_Wx⟩ := hgt (M + span R {x}) (lt_add _ hx),
  obtain ⟨Wy, h_Wy⟩ := hgt (M + span R {y}) (lt_add _ hy),
  use Wx + Wy,
  rw [multiset.map_add, multiset.prod_add],
  apply le_trans (submodule.mul_le_mul h_Wx h_Wy),
  rw add_mul,
  apply sup_le (show M * (M + span R {y}) ≤ M, from ideal.mul_le_right),
  rw mul_add,
  apply sup_le (show span R {x} * M ≤ M, from ideal.mul_le_left),
  rwa [span_mul_span, singleton_mul_singleton, span_singleton_le_iff_mem],
end

variables {A : Type*} [integral_domain A] [is_noetherian_ring A]

/--In a noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as
  product or prime ideals ([samuel, § 3.3, Lemma 3])
-/

lemma exists_prime_spectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬ is_field A) {I : ideal A}
  (h_nzI: I ≠ ⊥) :
  ∃ (Z : multiset (prime_spectrum A)), multiset.prod (Z.map (coe : subtype _ → ideal A)) ≤ I ∧
    multiset.prod (Z.map (coe : subtype _ → ideal A)) ≠ ⊥ :=
begin
  revert h_nzI,
  refine is_noetherian.induction (λ (M : ideal A) hgt, _) I,
  intro h_nzM,
  have hA_nont : nontrivial A,
  apply is_integral_domain.to_nontrivial (integral_domain.to_is_integral_domain A),
  by_cases h_topM : M = ⊤,
  { rcases h_topM with rfl,
    obtain ⟨p_id, h_nzp, h_pp⟩ : ∃ (p : ideal A), p ≠ ⊥ ∧ p.is_prime,
    { apply ring.not_is_field_iff_exists_prime.mp h_fA },
    use [({⟨p_id, h_pp⟩} : multiset (prime_spectrum A)), le_top],
    rwa [multiset.map_singleton, multiset.prod_singleton, subtype.coe_mk] },
  by_cases h_prM : M.is_prime,
  { use ({⟨M, h_prM⟩} : multiset (prime_spectrum A)),
    rw [multiset.map_singleton, multiset.prod_singleton, subtype.coe_mk],
    exact ⟨le_rfl, h_nzM⟩ },
  obtain ⟨x, hx, y, hy, h_xy⟩ := (ideal.not_is_prime_iff.mp h_prM).resolve_left h_topM,
  have lt_add : ∀ z ∉ M, M < M + span A {z},
  { intros z hz,
    refine lt_of_le_of_ne le_sup_left (λ m_eq, hz _),
    rw m_eq,
    exact mem_sup_right (mem_span_singleton_self z) },
  obtain ⟨Wx, h_Wx_le, h_Wx_ne⟩ := hgt (M + span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx)),
  obtain ⟨Wy, h_Wy_le, h_Wx_ne⟩ := hgt (M + span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy)),
  use Wx + Wy,
  rw [multiset.map_add, multiset.prod_add],
  refine ⟨le_trans (submodule.mul_le_mul h_Wx_le h_Wy_le) _, mt ideal.mul_eq_bot.mp _⟩,
  { rw add_mul,
    apply sup_le (show M * (M + span A {y}) ≤ M, from ideal.mul_le_right),
    rw mul_add,
    apply sup_le (show span A {x} * M ≤ M, from ideal.mul_le_left),
    rwa [span_mul_span, singleton_mul_singleton, span_singleton_le_iff_mem] },
  { rintro (hx | hy); contradiction },
end

end primes
