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
    sorry
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
variables [add_comm_monoid 𝕜] [has_one 𝕜] [preorder α] [locally_finite_order α] [decidable_eq α]

def mu_aux (a : α) : α → 𝕜
| b := if h : a = b then 1 else
  ∑ x in (Ico a b).attach,
    have (Icc a x).card < (Icc a b).card, from card_lt_card sorry,
    mu_aux x
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ b, (Icc a b).card)⟩] }

lemma mu_aux_apply (a b : α) :
  mu_aux 𝕜 α a b = if a = b then 1 else ∑ x in (Ico a b).attach, mu_aux 𝕜 α a x :=
by { convert has_well_founded.wf.fix_eq _ _, refl }

def mu : incidence_algebra 𝕜 α := ⟨mu_aux 𝕜 α, λ a b, not_imp_comm.1 $ λ h, begin
  rw mu_aux_apply at h,
  split_ifs at h with hab hab,
  { exact hab.le },
  { obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h,
    exact (nonempty_Ico.1 ⟨x, hx⟩).le }
end⟩

variables {𝕜 α}

lemma mu_apply (a b : α) : mu 𝕜 α a b = if a = b then 1 else ∑ x in Ico a b, mu 𝕜 α a x :=
by rw [mu, coe_mk, mu_aux_apply, sum_attach]

end mu

section mu_zeta
variables [add_comm_monoid 𝕜] [mul_one_class 𝕜] [preorder α] [locally_finite_order α]
  [decidable_eq α] [@decidable_rel α (≤)]

lemma mu_mul_zeta : mu 𝕜 α * zeta 𝕜 α = 1 :=
begin
  ext a b,
  rw [mul_apply, one_apply],
  sorry
end

lemma zeta_mul_mu : zeta 𝕜 α * mu 𝕜 α = 1 :=
begin
  ext a b,
  rw [mul_apply, one_apply],
  sorry
end

end mu_zeta

section euler
variables [add_comm_monoid 𝕜] [has_one 𝕜] [preorder α] [bounded_order α] [locally_finite_order α]
  [decidable_eq α]

/-- The Euler characteristic of a finite bounded order. -/
def euler_char : 𝕜 := mu 𝕜 α ⊥ ⊤

end euler
end incidence_algebra
