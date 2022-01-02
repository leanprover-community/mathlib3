/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.ring
import algebra.smul_with_zero
import group_theory.group_action.pi
import data.finset.locally_finite

/-!
# Incidence algebras
-/

open finset
open_locale big_operators

variables (𝕄 𝕜 α : Type*)

/-- The `𝕜`-incidence algebra over `α`. -/
structure incidence_algebra [has_zero 𝕜] [has_le α] :=
(to_fun : α → α → 𝕜)
(eq_zero_of_not_le' {a b : α} : ¬ a ≤ b → to_fun a b = 0)

namespace incidence_algebra
section zero
variables [has_zero 𝕜] [has_le α]

instance fun_like : fun_like (incidence_algebra 𝕜 α) α (λ _, α → 𝕜) :=
⟨to_fun, λ f g h, by { cases f, cases g, congr' }⟩

variables {𝕜 α}

lemma eq_zero_of_not_le {a b : α} (h : ¬ a ≤ b) (f : incidence_algebra 𝕜 α) : f a b = 0 :=
eq_zero_of_not_le' _ h

lemma le_of_ne_zero {f : incidence_algebra 𝕜 α} {a b : α} : f a b ≠ 0 → a ≤ b :=
not_imp_comm.1 $ eq_zero_of_not_le' _

-- completely uninteresting lemmas about coercion to function, that all homs need
section coes

-- Fallback `has_coe_to_fun` instance to help the elaborator
instance : has_coe_to_fun (incidence_algebra 𝕜 α) (λ _, α → α → 𝕜) := ⟨to_fun⟩

-- this must come after the coe_to_fun definitions
initialize_simps_projections incidence_algebra (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : incidence_algebra 𝕜 α) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : α → α → 𝕜) (h) : (mk f h : α → α → 𝕜) = f := rfl

protected lemma congr_fun {f g : incidence_algebra 𝕜 α} (h : f = g) (a b : α) : f a b = g a b :=
congr_arg (λ f : incidence_algebra 𝕜 α, f a b) h

protected lemma congr_arg (f : incidence_algebra 𝕜 α) {a₁ a₂ b₁ b₂ : α} (ha : a₁ = a₂)
  (hb : b₁ = b₂) :
  f a₁ b₁ = f a₂ b₂ :=
congr_arg2 f ha hb

lemma coe_inj ⦃f g : incidence_algebra 𝕜 α⦄ (h : (f : α → α → 𝕜) = g) : f = g :=
by { cases f, cases g, cases h, refl }

@[ext] lemma ext ⦃f g : incidence_algebra 𝕜 α⦄ (h : ∀ a b (hab : a ≤ b), f a b = g a b) : f = g :=
begin
  refine coe_inj (funext $ λ a, funext $ λ b, _),
  by_cases hab : a ≤ b,
  { exact h _ _ hab },
  { rw [eq_zero_of_not_le hab, eq_zero_of_not_le hab] }
end

lemma ext_iff {f g : incidence_algebra 𝕜 α} : f = g ↔ ∀ a b, f a b = g a b :=
⟨incidence_algebra.congr_fun, λ h, ext $ λ a b _, h _ _⟩

@[simp] lemma mk_coe (f : incidence_algebra 𝕜 α) (h) : mk f h = f := ext $ λ _ _ _, rfl

end coes

variables {𝕜 α}

instance : has_zero (incidence_algebra 𝕜 α) := ⟨⟨λ _ _, 0, λ _ _ _, rfl⟩⟩

@[simp] lemma zero_apply (a b : α) : (0 : incidence_algebra 𝕜 α) a b = 0 := rfl

end zero

section add
variables [add_zero_class 𝕜] [has_le α]

instance : has_add (incidence_algebra 𝕜 α) :=
⟨λ f g, ⟨f + g, λ a b h, by simp_rw [pi.add_apply, eq_zero_of_not_le h, zero_add]⟩⟩

@[simp] lemma add_apply (f g : incidence_algebra 𝕜 α) (a b : α) :
  (f + g) a b = f a b + g a b := rfl

end add

instance [add_monoid 𝕜] [has_le α] : add_monoid (incidence_algebra 𝕜 α) :=
{ add := (+),
  add_assoc := λ f g h, by { ext, exact add_assoc _ _ _ },
  zero := 0,
  zero_add := λ f, by { ext, exact zero_add _ },
  add_zero := λ f, by { ext, exact add_zero _ } }

instance [add_comm_monoid 𝕜] [has_le α] : add_comm_monoid (incidence_algebra 𝕜 α) :=
{ add_comm := λ f g, by { ext, exact add_comm _ _ },
  .. incidence_algebra.add_monoid 𝕜 α }

section add_group
variables [add_group 𝕜] [has_le α]

instance : has_neg (incidence_algebra 𝕜 α) :=
⟨λ f, ⟨-f, λ a b h, by simp_rw [pi.neg_apply, eq_zero_of_not_le h, neg_zero]⟩⟩

instance : has_sub (incidence_algebra 𝕜 α) :=
⟨λ f g, ⟨f - g, λ a b h, by simp_rw [pi.sub_apply, eq_zero_of_not_le h, sub_zero]⟩⟩

@[simp] lemma neg_apply (f : incidence_algebra 𝕜 α) (a b : α) : (-f) a b = -f a b := rfl

@[simp] lemma sub_apply (f g : incidence_algebra 𝕜 α) (a b : α) : (f - g) a b = f a b - g a b := rfl

instance : add_group (incidence_algebra 𝕜 α) :=
{ sub_eq_add_neg := λ f g, by { ext, exact sub_eq_add_neg _ _ },
  add_left_neg := λ f, by { ext, exact add_left_neg _ },
  .. incidence_algebra.add_monoid 𝕜 α,
  .. incidence_algebra.has_neg 𝕜 α,
  .. incidence_algebra.has_sub 𝕜 α }

end add_group

instance [add_comm_group 𝕜] [has_le α] : add_comm_group (incidence_algebra 𝕜 α) :=
{ .. incidence_algebra.add_group 𝕜 α, .. incidence_algebra.add_comm_monoid 𝕜 α }

section smul_with_zero
variables [has_zero 𝕄] [has_zero 𝕜] [smul_with_zero 𝕄 𝕜] [has_le α]

instance : has_scalar 𝕄 (incidence_algebra 𝕜 α) :=
⟨λ c f, ⟨c • f, λ a b h, by rw [pi.smul_apply, pi.smul_apply, eq_zero_of_not_le h, smul_zero']⟩⟩

@[simp] lemma smul_apply (c : 𝕄) (f : incidence_algebra 𝕜 α) (a b : α) : (c • f) a b = c • f a b :=
rfl

instance : smul_with_zero 𝕄 (incidence_algebra 𝕜 α) :=
{ smul := (•),
  smul_zero := λ m, by { ext, exact smul_zero' _ _ },
  zero_smul := λ m, by { ext, exact zero_smul _ _ } }

end smul_with_zero

section one
variables [preorder α] [decidable_eq α] [has_zero 𝕜] [has_one 𝕜]

instance : has_one (incidence_algebra 𝕜 α) :=
⟨⟨λ a b, if a = b then 1 else 0, λ a b h, ite_eq_right_iff.2 $ λ H, (h H.le).elim⟩⟩

@[simp] lemma one_apply (a b : α) : (1 : incidence_algebra 𝕜 α) a b = if a = b then 1 else 0 := rfl

end one

section mul
variables [preorder α] [locally_finite_order α] [add_comm_monoid 𝕜] [has_mul 𝕜]

instance : has_mul (incidence_algebra 𝕜 α) :=
⟨λ f g, ⟨λ a b, ∑ x in Icc a b, f a x * g x b, λ a b h, by rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp] lemma mul_apply (f g : incidence_algebra 𝕜 α) (a b : α) :
  (f * g) a b = ∑ x in Icc a b, f a x * g x b := rfl

end mul

instance [semiring 𝕜] [decidable_eq α] [preorder α] [locally_finite_order α] :
  semiring (incidence_algebra 𝕜 α) :=
{ mul := (*),
  mul_assoc := λ f g h, begin
    ext a b,
    simp only [mul_apply, sum_mul, mul_sum],
    rw finset.sum_sigma',
    rw finset.sum_sigma',
    dsimp,
    apply' sum_bij (λ (x : Σ i : α, α) hx, (sigma.mk x.snd x.fst : Σ i : α, α)),
    { rintro ⟨a_1_fst, a_1_snd⟩ ha,
      simp only [mem_sigma, mem_Icc] at *,
      tidy,
      exact le_trans ha_right_right ha_left_right, },
    { rintro ⟨a_1_fst, a_1_snd⟩ ha,
      simp [mul_assoc], },
    { rintro ⟨a₁_fst, a₁_snd⟩ ⟨a₂_fst, a₂_snd⟩ ha₁ ha₂ ⟨⟩,
      refl, },
    { rintro ⟨b_1_fst, b_1_snd⟩ H,
      simp only [exists_prop, sigma.exists, mem_sigma, heq_iff_eq, sigma.mk.inj_iff, mem_Icc] at *,
      use [b_1_snd, b_1_fst],
      simp only [and_true, eq_self_iff_true],
      tidy,
      exact le_trans H_left_left H_right_left, },
  end,
  one := (1),
  one_mul := λ f, begin
    ext a b,
    simp_rw [mul_apply, one_apply, sum_boole_mul],
    exact ite_eq_left_iff.2 (not_imp_comm.1 $ λ h, left_mem_Icc.2 $ le_of_ne_zero $ ne.symm h),
  end,
  mul_one := λ f, begin
    ext a b,
    simp_rw [mul_apply, one_apply, eq_comm, sum_mul_boole],
    convert (ite_eq_left_iff.2 $ not_imp_comm.1 $
      λ h, right_mem_Icc.2 $ le_of_ne_zero $ ne.symm h).symm,
  end,
  zero := 0,
  zero_mul := λ f, by { ext, exact sum_eq_zero (λ x _, zero_mul _) },
  mul_zero := λ f, by { ext, exact sum_eq_zero (λ x _, mul_zero _) },
  left_distrib := λ f g h,
    by { ext, exact eq.trans (sum_congr rfl (λ x _, left_distrib _ _ _)) sum_add_distrib },
  right_distrib := λ f g h,
    by { ext, exact eq.trans (sum_congr rfl (λ x _, right_distrib _ _ _)) sum_add_distrib },
  .. incidence_algebra.add_comm_monoid 𝕜 α }

section zeta
variables [has_zero 𝕜] [has_one 𝕜] [has_le α] [@decidable_rel α (≤)]

def zeta : incidence_algebra 𝕜 α := ⟨λ a b, if a ≤ b then 1 else 0, λ a b h, if_neg h⟩

variables {𝕜 α}

@[simp] lemma zeta_apply (a b : α) : zeta 𝕜 α a b = if a ≤ b then 1 else 0 := rfl

lemma zeta_of_le {a b : α} (h : a ≤ b) : zeta 𝕜 α a b = 1 := if_pos h

end zeta

lemma zeta_mul_zeta [add_comm_monoid 𝕜] [mul_one_class 𝕜] [preorder α] [locally_finite_order α]
  [@decidable_rel α (≤)] (a b : α) :
  (zeta 𝕜 α * zeta 𝕜 α) a b = (Icc a b).card :=
begin
  rw [mul_apply, card_eq_sum_ones, nat.cast_sum, nat.cast_one],
  refine sum_congr rfl (λ x hx, _),
  rw mem_Icc at hx,
  rw [zeta_of_le hx.1, zeta_of_le hx.2, one_mul],
end

section mu
variables [add_comm_group 𝕜] [has_one 𝕜] [preorder α] [locally_finite_order α] [decidable_eq α]

def mu_aux (a : α) : α → 𝕜
| b := if h : a = b then 1 else
  -∑ x in (Ico a b).attach,
    have (Icc a x).card < (Icc a b).card, from card_lt_card sorry,
    mu_aux x
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ b, (Icc a b).card)⟩] }

lemma mu_aux_apply (a b : α) :
  mu_aux 𝕜 α a b = if a = b then 1 else -∑ x in (Ico a b).attach, mu_aux 𝕜 α a x :=
by { convert has_well_founded.wf.fix_eq _ _, refl }

def mu : incidence_algebra 𝕜 α := ⟨mu_aux 𝕜 α, λ a b, not_imp_comm.1 $ λ h, begin
  rw mu_aux_apply at h,
  split_ifs at h with hab hab,
  { exact hab.le },
  { rw neg_eq_zero at h,
    obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h,
    exact (nonempty_Ico.1 ⟨x, hx⟩).le }
end⟩

variables {𝕜 α}

lemma mu_apply (a b : α) : mu 𝕜 α a b = if a = b then 1 else -∑ x in Ico a b, mu 𝕜 α a x :=
by rw [mu, coe_mk, mu_aux_apply, sum_attach]

lemma mu_apply_of_eq {a b : α} (h : a = b) : mu 𝕜 α a b = 1 :=
by rw [mu_apply, if_pos h]

@[simp]
lemma mu_apply_self (a : α) : mu 𝕜 α a a = 1 := mu_apply_of_eq rfl

lemma mu_apply_of_ne {a b : α} (h : a ≠ b) : mu 𝕜 α a b = -∑ x in Ico a b, mu 𝕜 α a x :=
by rw [mu_apply, if_neg h]

-- lemma mu_apply_of_ne' {a b : α} (h : a ≠ b) : mu 𝕜 α a b = -∑ x in Ioc a b, mu 𝕜 α x b :=
-- begin
--   induction hi : (Icc a b).card generalizing a b,
--   { simp only [card_eq_zero, Icc_eq_empty_iff] at hi,
--     rw Ioc_eq_empty _,
--     rw eq_zero_of_not_le hi,
--     simp,
--     intro hh,
--     apply hi,
--     exact le_of_lt hh, },
--   -- intro hne,
--   by_cases hab : a ≤ b,
--   { conv in (mu _ _ _ _) { rw mu_apply, },
--     rw sum_ite,
--     rw filter_eq',
--     simp [hab],
--     have hIcc : Icc a b = Ioc a b ∪ {a},
--     sorry,
--     sorry,
--     -- rw [hIcc, sum_union, sum_singleton, this, add_neg_self],
--      },
--   { have : ∀ x ∈ Icc a b, ¬ x ≤ b,
--     { intros x hx hn, apply hab, rw [mem_Icc] at hx, exact le_trans hx.1 hn},
--     conv in (mu _ _ _ _) { rw eq_zero_of_not_le (this x H), },
--     simp, },
-- end

lemma mu_spec_of_ne_right {a b : α} (h : a ≠ b) : ∑ (x : α) in Icc a b, (mu 𝕜 α) a x = 0 :=
begin
  have : mu 𝕜 α a b = _ := mu_apply_of_ne h,
  have hIcc : Icc a b = Ico a b ∪ {b},
  sorry,
  rw [hIcc, sum_union, sum_singleton, this, add_neg_self],
  simp,
end
end mu

section mu'
variables [add_comm_group 𝕜] [has_one 𝕜] [preorder α] [locally_finite_order α] [decidable_eq α]

-- this is the reversed definition of mu, which is equal to mu but easiest to prove equal
-- by showing that zeta * mu = 1 and mu' * zeta = 1
-- therefore mu' should be an implementation detail and not used
private def mu'_aux (b : α) : α → 𝕜
| a := if h : a = b then 1 else
  -∑ x in (Ioc a b).attach,
    have (Icc ↑x b).card < (Icc a b).card, from card_lt_card sorry,
    mu'_aux x
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ a, (Icc a b).card)⟩] }

private lemma mu'_aux_apply (a b : α) :
  mu'_aux 𝕜 α b a = if a = b then 1 else -∑ x in (Ioc a b).attach, mu'_aux 𝕜 α b x :=
by { convert has_well_founded.wf.fix_eq _ _, refl }

private def mu' : incidence_algebra 𝕜 α := ⟨λ a b, mu'_aux 𝕜 α b a, λ a b, not_imp_comm.1 $ λ h, begin
  rw mu'_aux_apply at h,
  split_ifs at h with hab hab,
  { exact hab.le },
  { rw neg_eq_zero at h,
    obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h,
    exact (nonempty_Ioc.1 ⟨x, hx⟩).le }
end⟩
variables {𝕜 α}

lemma mu'_apply (a b : α) : mu' 𝕜 α a b = if a = b then 1 else -∑ x in Ioc a b, mu' 𝕜 α x b :=
by rw [mu', coe_mk, mu'_aux_apply, sum_attach]

lemma mu'_apply_of_ne {a b : α} (h : a ≠ b) : mu' 𝕜 α a b = -∑ x in Ioc a b, mu' 𝕜 α x b :=
by rw [mu'_apply, if_neg h]

lemma mu'_spec_of_ne_left {a b : α} (h : a ≠ b) : ∑ (x : α) in Icc a b, (mu' 𝕜 α) x b = 0 :=
begin
  have : mu' 𝕜 α a b = _ := mu'_apply_of_ne h,
  have hIcc : Icc a b = Ioc a b ∪ {a},
  sorry,
  rw [hIcc, sum_union, sum_singleton, this, add_neg_self],
  simp,
end

lemma mu'_apply_of_eq {a b : α} (h : a = b) : mu' 𝕜 α a b = 1 :=
by rw [mu'_apply, if_pos h]

@[simp]
lemma mu'_apply_self (a : α) : mu' 𝕜 α a a = 1 := mu'_apply_of_eq rfl
end mu'

section order_dual
variables [add_comm_group 𝕜] [has_one 𝕜] [preorder α] [locally_finite_order α] [decidable_eq α]
open order_dual
lemma mu_dual (a b : α) : mu 𝕜 (order_dual α) (to_dual a) (to_dual b) = mu 𝕜 α b a :=
begin
  -- I think this is probably also true and maybe helpful
  sorry,
end
end order_dual

section mu_zeta
variables [add_comm_group 𝕜] [mul_one_class 𝕜] [partial_order α] [locally_finite_order α]
  [decidable_eq α] [@decidable_rel α (≤)]

lemma mu_mul_zeta : mu 𝕜 α * zeta 𝕜 α = 1 :=
begin
  ext a b,
  rw [mul_apply, one_apply],
  split_ifs with he,
  { simp [he] },
  { simp only [mul_one, zeta_apply, mul_ite],
    conv in (ite _ _ _) {
      rw [if_pos (mem_Icc.mp H).2], },
    rw mu_spec_of_ne_right he, },
end

lemma zeta_mul_mu' : zeta 𝕜 α * mu' 𝕜 α = 1 :=
begin
  ext a b,
  rw [mul_apply, one_apply],
  split_ifs with he,
  { simp [he], },
  { simp only [zeta_apply, one_mul, ite_mul],
    conv in (ite _ _ _) {
      rw [if_pos (mem_Icc.mp H).1], },
    rw mu'_spec_of_ne_left he, },
end
end mu_zeta

section mu_eq_mu'
variables [ring 𝕜] [partial_order α] [locally_finite_order α]
  [decidable_eq α] [@decidable_rel α (≤)]

lemma mu_eq_mu' : mu 𝕜 α = mu' 𝕜 α := left_inv_eq_right_inv (mu_mul_zeta 𝕜 α) (zeta_mul_mu' 𝕜 α)

lemma mu_apply_of_ne' {a b : α} (h : a ≠ b) : mu 𝕜 α a b = -∑ x in Ioc a b, mu 𝕜 α x b :=
begin
  rw mu_eq_mu',
  exact mu'_apply_of_ne h,
end

lemma zeta_mul_mu : zeta 𝕜 α * mu 𝕜 α = 1 :=
begin
  rw mu_eq_mu',
  exact zeta_mul_mu' 𝕜 α,
end

lemma mu_spec_of_ne_left {a b : α} (h : a ≠ b) : ∑ (x : α) in Icc a b, (mu 𝕜 α) x b = 0 :=
by rw [mu_eq_mu', mu'_spec_of_ne_left h]

end mu_eq_mu'

section inversion_top
variables [ring 𝕜] [partial_order α] [order_top α] [locally_finite_order α]
  [decidable_eq α]

lemma Ici_eq_Ioi_union (x : α) : Ici x = Ioi x ∪ {x} := sorry

/-- A general form of Möbius inversion. Based on Theorem 2.1.2 of Incidence Algebras by Spiegel and
O'Donnell.-/
lemma moebius_inversion_top (f g : α → 𝕜) (h : ∀ x, g x = ∑ y in Ici x, f y) (x : α) :
  f x = ∑ y in Ici x, mu 𝕜 α x y * g y :=
by letI : @decidable_rel α (≤) := classical.dec_rel _; symmetry; calc
  ∑ y in Ici x, mu 𝕜 α x y * g y
      = ∑ y in Ici x, mu 𝕜 α x y * ∑ z in Ici y, f z : by simp_rw [h]
  ... = ∑ y in Ici x, mu 𝕜 α x y * ∑ z in Ici y, zeta 𝕜 α y z * f z : by {
        simp_rw [zeta_apply],
        conv in (ite _ _ _)
        { rw if_pos (mem_Ici.mp H), },
        simp, }
  ... = ∑ y in Ici x, ∑ z in Ici y, mu 𝕜 α x y * zeta 𝕜 α y z * f z : by simp [mul_sum]
  ... = ∑ z in Ici x, ∑ y in Icc x z, mu 𝕜 α x y * zeta 𝕜 α y z * f z : sorry
  ... = ∑ z in Ici x, (mu 𝕜 α * zeta 𝕜 α) x z * f z : by {
        conv in ((mu _ _ * zeta _ _) _ _) { rw [mul_apply] },
        simp_rw [sum_mul], }
  ... = ∑ y in Ici x, ∑ z in Ici y, (1 : incidence_algebra 𝕜 α) x z * f z : by {
        simp [mu_mul_zeta 𝕜 α, Ici_eq_Ioi_union, sum_union],
        conv in (ite _ _ _) { rw if_neg (not_lt_of_le $ (mem_Ioi.mp H).le) },
        conv in (ite _ _ _) { rw if_neg (ne_of_lt $ mem_Ioi.mp H) },
        simp, }
  ... = f x : by { simp [one_apply, Ici_eq_Ioi_union, sum_union],
        conv in (ite _ _ _) { rw if_neg (not_lt_of_le $ (mem_Ioi.mp H).le) },
        conv in (ite _ _ _) { rw if_neg (ne_of_lt $ mem_Ioi.mp H) },
        simp, }

end inversion_top

section inversion_bot
variables [ring 𝕜] [partial_order α] [order_bot α] [locally_finite_order α]
  [decidable_eq α]

/-- A general form of Möbius inversion. Based on Theorem 2.1.3 of Incidence Algebras by Spiegel and
O'Donnell. -/
lemma moebius_inversion_bot (f g : α → 𝕜) (h : ∀ x, g x = ∑ y in Iic x, f y) (x : α) :
  f x = ∑ y in Iic x, mu 𝕜 α y x * g y :=
begin
  convert @moebius_inversion_top 𝕜 (order_dual α) _ _ _ _ _ f g h x,
  ext y,
  erw mu_dual,
end

end inversion_bot

section prod
variables {β γ : Type*} [ring 𝕜] [partial_order β] [partial_order γ] [locally_finite_order β]
  [locally_finite_order γ] [decidable_eq β] [decidable_eq γ]
  [decidable_rel ((≤) : β → β → Prop)] [decidable_rel ((≤) : γ → γ → Prop)]
  [decidable_rel ((≤) : β × γ → β × γ → Prop)]

lemma zeta_prod_eq (x y : β) (u v : γ) :
  zeta 𝕜 (β × γ) (x, u) (y, v) = zeta 𝕜 β x y * zeta 𝕜 γ u v :=
by simp [ite_and]

lemma zeta_prod_eq' (a b : β × γ) :
  zeta 𝕜 (β × γ) a b = zeta 𝕜 β a.fst b.fst * zeta 𝕜 γ a.snd b.snd :=
begin
  cases a,
  cases b,
  rw zeta_prod_eq,
end

variables (β γ)
/-- A description of `mu` in a product of incidence algebras -/
def mu_prod : incidence_algebra 𝕜 (β × γ) :=
{ to_fun := λ xu yv : β × γ, mu 𝕜 β xu.fst yv.fst * mu 𝕜 γ xu.snd yv.snd,
  eq_zero_of_not_le' := begin
    intros a b hab,
    cases a,
    cases b,
    rw [prod.mk_le_mk, not_and_distrib] at hab,
    cases hab; simp [eq_zero_of_not_le hab],
end }

variables {β γ}

lemma mu_prod_apply (x y : β) (u v : γ) : mu_prod 𝕜 β γ (x, u) (y, v) = mu 𝕜 β x y * mu 𝕜 γ u v :=
rfl
lemma mu_prod_apply' (a b : β × γ) : mu_prod 𝕜 β γ a b = mu 𝕜 β a.fst b.fst * mu 𝕜 γ a.snd b.snd :=
rfl
lemma one_prod_apply (x y : β) (u v : γ) : (1 : incidence_algebra 𝕜 (β × γ)) (x, u) (y, v) =
  (1 : incidence_algebra 𝕜 β) x y * (1 : incidence_algebra 𝕜 γ) u v :=
by simp [ite_and]

lemma prod_Icc (a b : β × γ) : Icc a b = (Icc a.fst b.fst).product (Icc a.snd b.snd) := rfl

lemma mu_prod_eq (x y : β) (u v : γ) : mu 𝕜 (β × γ) (x, u) (y, v) = mu 𝕜 β x y * mu 𝕜 γ u v :=
begin
  suffices : mu_prod 𝕜 β γ * zeta 𝕜 (β × γ) = 1,
  { sorry },
  clear x y u v,
  ext ⟨x, u⟩ ⟨y, v⟩,
  simp_rw [mul_apply, zeta_prod_eq', mu_prod_apply', prod_Icc],
  convert_to ∑ (x_1 : β × γ) in (Icc (x, u).fst (y, v).fst).product (Icc (x, u).snd (y, v).snd),
    (mu 𝕜 β) x x_1.fst * (zeta 𝕜 β) x_1.fst y * ((mu 𝕜 γ) u x_1.snd * (zeta 𝕜 γ) x_1.snd v) = _,
  { simp [mul_comm, mul_assoc], },
  rw ← sum_mul_sum (Icc x y) (Icc u v)
    (λ x_1f, (mu 𝕜 β) x x_1f * (zeta 𝕜 β) x_1f y)
    (λ x_1s, (mu 𝕜 γ) u x_1s * (zeta 𝕜 γ) x_1s v),
  rw one_prod_apply,
  congr; rw [← mu_mul_zeta, mul_apply],
end

end prod

section euler
variables [add_comm_group 𝕜] [has_one 𝕜] [preorder α] [bounded_order α] [locally_finite_order α]
  [decidable_eq α]

/-- The Euler characteristic of a finite bounded order. -/
def euler_char : 𝕜 := mu 𝕜 α ⊥ ⊤

end euler
end incidence_algebra
