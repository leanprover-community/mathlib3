/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import tactic.subtype_instance
import tactic.noncomm_ring
import ring_theory.adjoin
import ring_theory.nilpotent
import order.filter.at_top_bot
import linear_algebra.finite_dimensional

/-!

# Dedekind finite rings


## References

* Lam, First Course in Noncommutative Ring Theory
* https://ysharifi.wordpress.com/2010/09/17/dedekind-finite-rings/
* The Factorization Theory of Power Monoids - Antoniou,
  https://etd.ohiolink.edu/apexprod/rws_etd/send_file/send?accession=osu1586355818066608&disposition=inline

-/
namespace dedekind_finite

section

variables (R : Type*)

/-- A (noncommutative) monoid is Dedekind-finite if for any pair of elements `a b : R` with
  `a * b = 1` we have `b * a = 1`, i.e. multiplication is commutative on inverse pairs.
  This concept is often studied for rings, but can be defined more generally for monoids, and some
  results hold for monoids without any additive structure.

  This is implemented as a mixin for `monoid R`.  -/
class is_dedekind_finite [monoid R] : Prop :=
(inv_comm : ∀ a b : R, a * b = 1 → b * a = 1)

@[priority 100]
instance is_dedekind_finite_of_comm_ring [comm_monoid R] : is_dedekind_finite R :=
⟨λ a b h, h ▸ mul_comm b a⟩

end
section

instance is_dedekind_finite_pi {ι : Type*} {α : ι → Type*} [∀ i, monoid $ α i]
  [∀ i, is_dedekind_finite $ α i] : is_dedekind_finite (Π i, α i) :=
by pi_instance

end

section
variables (R : Type*)

--instance subring.is_dedekind_finite [ring R] [is_dedekind_finite R] (S : set R)
-- [is_subring S] : is_dedekind_finite S :=
--by subtype_instance

-- def is_nilpotent {R : Type*} [ring R] (a : R) := ∃ n : ℕ, a^n = 0
def nilpotents [ring R] : set R := { a : R | is_nilpotent a }
-- TODO would be nice to set this up as the radical of the zero ideal but currently there doesn't
--  seem to be much about one-sided ideals in non-comm rings

class is_reduced_ring [ring R] :=
(no_nilpotents : ∀ a : R, is_nilpotent a → a = 0)

lemma nilpotents_of_reduced [ring R] [is_reduced_ring R] : nilpotents R = {0} :=
begin
  apply set.eq_of_subset_of_subset,
  { rw set.subset_singleton_iff,
    exact is_reduced_ring.no_nilpotents, },
  { rw set.singleton_subset_iff,
    exact submonoid.mem_powers 0, }
end

class is_reversible [monoid_with_zero R] : Prop :=
(zero_div_comm : ∀ a b : R, a * b = 0 → b * a = 0)

@[priority 100]
instance is_reversible_of_domain [monoid_with_zero R] [no_zero_divisors R] : is_reversible R :=
⟨λ a b h,
  begin
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h with rfl | rfl,
    { rw [mul_zero], },
    { rw [zero_mul], },
  end⟩


@[priority 100]
instance reversible_of_reduced [ring R] [is_reduced_ring R] : is_reversible R :=
⟨λ a b h,
  begin
    apply is_reduced_ring.no_nilpotents (b * a),
    use [2],
    rw [pow_two, ← mul_assoc, mul_assoc b, h, mul_zero, zero_mul],
  end⟩

@[priority 100]
instance reversible_of_comm_ring [comm_ring R] : is_reversible R :=
⟨λ a b h, h ▸ mul_comm b a⟩

@[priority 100]
instance is_dedekind_finite_of_reversible [ring R] [is_reversible R] :
  is_dedekind_finite R :=
⟨λ a b h,
  begin
    have : b * (b * a - 1) = 0 := is_reversible.zero_div_comm _ _
      (calc (b * a - 1) * b = b * (a * b) - b : by rw [sub_mul, one_mul, mul_assoc]
                       ...  = 0               : by rw [h, mul_one, sub_self]),
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, sub_eq_zero] at this,
    apply_fun ((*) a) at this,
    rw [h] at this,
    calc b * a = a * (b^2 * a) * b * a : by simp [this]
        ...    = a * b^2 * (a * b) * a : by simp [mul_assoc] -- I feel like ac_refl should do this
        ...    = a * b^2 * a           : by simp [h]
        ...    = 1                     : by assoc_rw [this],
  end⟩

@[priority 100]
instance is_dedekind_finite_of_reduced [ring R] [is_reduced_ring R] :
  is_dedekind_finite R := by apply_instance


variable [ring R]

open linear_map
open function

-- variables {γ : Type*} [preorder γ] [decidable_rel ((≤) : γ → γ → Prop)]

-- open filter
-- def strict_monotone_inc_subseq {f : ℕ → γ} (h : ∀ n, ∃ m, f n < f (n + m)) :
-- ℕ → ℕ
-- -- ∃ g : ℕ → ℕ, strict_mono g ∧ strict_mono (f ∘ g) :=
-- -- begin
-- --   have : tendsto f at_top at_top,
-- --   { rw tendsto_at_top_at_top,
-- --   sorry;
-- --     by_contra, },
-- --   sorry
-- --   -- have := strict_mono_subseq_of_tendsto_at_top this,
-- -- end

-- | 0       := 0
-- | (n + 1) := (strict_monotone_inc_subseq n) + nat.find (h (strict_monotone_inc_subseq n))

-- lemma strict_monotone_inc_subseq_spec (f : ℕ → γ) (h : ∀ n, ∃ m, f n < f (n + m)) :
--   strict_mono (f ∘ strict_monotone_inc_subseq h) :=
-- strict_mono_nat_of_lt_succ (λ n, nat.find_spec (h (strict_monotone_inc_subseq h n)))

-- TODO artinian version of ring stuff?
open_locale classical

@[simp] theorem ker_one {R : Type*} [ring R] {M : Type*} [add_comm_group M] [module R M] :
  ker (1 : M →ₗ[R] M) = ⊥ := rfl

-- Oops turns out this is already in mathlib now
-- theorem noeth_mod_surj_inj {R : Type*} [ring R] {M : Type*} [add_comm_group M] [module R M]
--   [is_noetherian R M] {f : M →ₗ[R] M} (f_surj : function.surjective f) : function.injective f :=
-- begin
--   have := well_founded_submodule_gt R M,
--   rw rel_embedding.well_founded_iff_no_descending_seq at this,
--   suffices : ∃ n, ∀ m : ℕ, (f ^ n).ker = (f ^ (n + m)).ker,
--   { obtain ⟨n, hn⟩ := this,
--     by_cases hne : n = 0,
--     { simpa [hne, ← ker_eq_bot] using (hn 1).symm, },
--     have pow_surj := iterate_surjective f_surj n,
--     have : (f ^ n).ker ⊓ linear_map.range (f ^ n) = ⊥,
--     { ext,
--       rw [submodule.mem_inf, mem_ker, mem_range, submodule.mem_bot],
--       split,
--       { rintro ⟨h₁, ⟨y, h₂⟩⟩,
--         rw ← h₂ at h₁, rw ← linear_map.comp_apply at h₁,
--         have : f * f = f.comp f := mul_eq_comp f f,
--         rw [← mul_eq_comp, ←pow_add] at h₁, rw ← mem_ker at h₁,
--         have : ker (f ^ n) = ker (f ^ (n + n)) := hn n,
--         rw ← this at h₁, rw mem_ker at h₁,
--         rw h₁ at h₂, exact h₂.symm, },
--       intro a,
--       rw [a, map_zero],
--       use 0,
--       rw map_zero, },
--     have range_eq_top : range (f ^ n) = ⊤ := range_eq_top.mpr pow_surj,
--     have : (f ^ n).ker = ⊥,
--     { simpa [range_eq_top] using this, },
--     have : function.injective ⇑(f ^ n) := ker_eq_bot.mp this,
--     exact injective_of_iterate_injective hne this, },
--   contrapose! this,
--   rw [not_is_empty_iff],
--   refine nonempty.intro _,
--   have h_ker_lt :
--     ∀ n, ∃ (m : ℕ), (λ (n : ℕ), (f ^ n).ker) n < (λ (n : ℕ), (f ^ n).ker) (n + m),
--   { intro n,
--     simp only,
--     have h_ker_le : ∀ n m : ℕ, (f ^ n).ker ≤ (f ^ (n + m)).ker,
--     { intros n m x hx,
--       rw add_comm,
--       rw [mem_ker, pow_apply] at hx,
--       simp [mem_ker, pow_add, hx, mul_apply, pow_apply, map_zero], },
--     cases this n with m hm,
--     exact ⟨m, lt_of_le_of_ne (h_ker_le n m) hm⟩, },
--   refine rel_embedding.of_monotone
--     ((λ (n : ℕ), (f ^ n).ker) ∘ strict_monotone_inc_subseq h_ker_lt) _,
--   intros a b hab,
--   exact strict_monotone_inc_subseq_spec (λ n, (f ^ n).ker) h_ker_lt hab,
-- end


@[priority 100]
instance is_dedekind_finite_of_noetherian [is_noetherian_ring R] : is_dedekind_finite R :=
⟨λ a b h,
  begin
    have : is_linear_map R _ := is_linear_map.is_linear_map_smul' b,
    set f : R →ₗ[R] R := is_linear_map.mk' _ this,
    have f_surj : function.surjective f := λ x, ⟨x * a, by simp [mul_assoc, h]⟩,
    have f_inj := is_noetherian.injective_of_surjective_endomorphism f f_surj,
    exact sub_eq_zero.mp (f_inj (
        calc f (b * a - 1) = (b * a - 1) * b : by simp only [is_linear_map.mk'_apply,
                                                              smul_eq_mul, sub_eq_add_neg]
                       ... = b * a * b - b   : by rw [sub_mul, one_mul]
                       ... = 0               : by rw [mul_assoc, h, mul_one, sub_self]
                       ... = f 0             : by simp only [zero_mul, is_linear_map.mk'_apply,
                                                              smul_eq_mul])),
    /-
    have := well_founded_submodule_gt R R,
    rw order_embedding.well_founded_iff_no_descending_seq at this,
    set ordf : ℕ → submodule R R := λ n, linear_map.ker (iterate f n),

    suffices : ∃ n, ordf n = ordf (n + 1),
    begin
        obtain ⟨n, hn⟩ := this,
        have pow_surj := iterate_surj f_surj n,
        obtain ⟨c, hc⟩ := pow_surj (b * a - 1),
        have :=
        calc iterate f (n + 1) c = f (b * a - 1)   : by rw [iterate_succ', comp_apply, hc]
                            ...  = (b * a - 1) * b : by simp [f]
                            ...  = 0               : by rw [sub_mul, one_mul, mul_assoc, h,
                                                              mul_one, sub_self],
        rw ← linear_map.mem_ker at this,
        dsimp only [ordf] at hn,
        rw ← hn at this,
        rw linear_map.mem_ker at this,
        rw this at hc,
        exact sub_eq_zero.mp (eq.symm hc),
    end,

    by_contradiction ho,
    apply this,
    push_neg at ho,
    have : ∀ n, ordf n ≤ ordf (n + 1),
    { intros n x hx, simp [ordf, iterate_succ'] at hx ⊢, rw [hx, zero_mul], },
    have : ∀ n, ordf (n + 1) > ordf n := λ n, lt_of_le_of_ne (this n) (ho n),
    have := order_embedding.nat_gt _ this,
    exact nonempty.intro this,-/
  end⟩


@[priority 80] -- see Note [lower instance priority]
instance ring.is_noetherian_ring_of_fintype (R) [fintype R] [ring R] :
  is_noetherian_ring R := by rw is_noetherian_ring_iff; refine ring.is_noetherian_of_fintype R R
-- TODO this should be global

@[priority 100]
instance is_dedekind_finite_of_finite [fintype R] : is_dedekind_finite R :=
begin
  apply_instance,
  --TODO why is this needed?
  -- haveI inst : is_noetherian R R := ring.is_noetherian_of_fintype R R,
  -- haveI := is_noetherian_ring_iff.mpr inst,
  -- exact dedekind_finite.is_dedekind_finite_of_noetherian R,
end
end

section

variable {R : Type*}

lemma pow_mul_pow_eq_pow_sub_mul_pow_sub_of_mul_eq_one [monoid R] {a b : R} (hab : a * b = 1) :
  ∀ (i j : ℕ), a ^ i * b ^ j = b ^ (j - i) * a ^ (i - j)
| 0       0       := by simp
| (i + 1) 0       := by simp
| 0       (j + 1) := by simp
| (i + 1) (j + 1) := begin
  rw [pow_succ', pow_succ],
  assoc_rw hab,
  rw [mul_one, pow_mul_pow_eq_pow_sub_mul_pow_sub_of_mul_eq_one i j,
      nat.succ_sub_succ_eq_sub, nat.succ_sub_succ_eq_sub],
end

private def e [ring R] (a b : R) (i j : ℕ) : R := b ^ i * (1 - b * a) * a ^ j
lemma left_mul [ring R] {a b : R} (hab : a * b = 1) : a * (1 - b * a) = 0 :=
by rw [mul_sub, ← mul_assoc, hab, mul_one, one_mul, sub_self]
lemma right_mul [ring R] {a b : R} (hab : a * b = 1) : (1 - b * a) * b = 0 :=
by rw [sub_mul, mul_assoc, hab, mul_one, one_mul, sub_self]
lemma idemp [ring R] {a b : R} (hab : a * b = 1) : (1 - b * a) * (1 - b * a) = (1 - b * a) :=
begin
  assoc_rw [sub_mul, mul_sub, mul_sub, hab],
  simp,
end

lemma e_orthogonal [ring R] {a b : R} (hab : a * b = 1) {i j k l : ℕ} :
  e a b i j * e a b k l = if j = k then e a b i l else (0 : R) :=
begin
  rw [e, e, e],
  assoc_rw [pow_mul_pow_eq_pow_sub_mul_pow_sub_of_mul_eq_one hab],
  rcases lt_trichotomy j k with H | rfl | H,
  { rw [if_neg (ne_of_lt H),
        show k - j = k - j - 1 + 1, from (nat.succ_pred_eq_of_pos (tsub_pos_of_lt H)).symm,
        pow_succ],
    assoc_rw right_mul hab,
    simp [H], },
  { simp only [mul_one, if_true, eq_self_iff_true, tsub_self, pow_zero],
    assoc_rw idemp hab, },
  { rw [if_neg (ne_of_gt H),
        show j - k = j - k - 1 + 1, from (nat.succ_pred_eq_of_pos (tsub_pos_of_lt H)).symm,
        pow_succ'],
    assoc_rw left_mul hab,
    simp [H], },
end

lemma e_pow_two_eq_zero_of_ne [ring R] {a b : R} (hab : a * b = 1) {i j : ℕ} (hij : i ≠ j) :
  e a b i j ^ 2 = 0 :=
by rw [pow_two, e_orthogonal hab, if_neg (ne.symm hij)]

open_locale classical

lemma is_dedekind_finite_of_fin_nilpotents (R : Type*) [ring R] (h : (nilpotents R).finite) :
  is_dedekind_finite R :=
begin
  apply is_dedekind_finite.mk,
  contrapose! h,
  rintro ⟨hinf⟩,
  haveI : infinite (nilpotents R),
  { rcases h with ⟨a, b, hab, hba⟩,
    refine infinite.of_injective
      (λ n, ⟨e a b (n + 1) 0, 2, e_pow_two_eq_zero_of_ne hab n.succ_ne_zero⟩) _,
    intros n m hnm,
    rw [subtype.mk_eq_mk] at hnm,
    by_contradiction h,
    have : e a b 0 (n + 1) * e a b (m + 1) 0 = 0,
    { rw [e_orthogonal hab, if_neg],
      intro hmn,
      exact h ((add_left_inj 1).mp hmn) },
    apply absurd _ hba.symm,
    rw ← sub_eq_zero,
    calc 1 - b * a
         = e a b 0 0                         : by rw [e, pow_zero, pow_zero, mul_one, one_mul]
    ...  = e a b 0 (n + 1) * e a b (n + 1) 0 : by rw [e_orthogonal hab, if_pos rfl]
    ...  = e a b 0 (n + 1) * e a b (m + 1) 0 : by rw hnm
    ...  = 0                                 : this, },
  exact infinite.not_fintype hinf,
end

end
end dedekind_finite
#lint
