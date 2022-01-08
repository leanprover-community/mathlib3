/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import algebra.big_operators.ring
import algebra.module.basic
import group_theory.group_action.basic
import group_theory.group_action.pi
import data.finset.locally_finite

/-!
# Incidence algebras


## TODOs
Here are some additions to this file that could be made in the future

- Generalize the construction of `mu` to invert any element of the incidence algebra `f` which has
  `f x x` a unit for all `x`.
- Give formulae for higher powers of zeta.
- A formula for the möbius function on a pi type similar to the one for products
- More examples / applications to different posets.
- Connection with Galois insertions
- Finsum version of Möbius inversion that holds even when an order doesn't have top/bot?
-/

open finset
open_locale big_operators

namespace finset

section
variables {α β : Type*} [preorder α] [preorder β] [locally_finite_order α] [locally_finite_order β]
  [decidable_rel ((≤) : α → α → Prop)] [decidable_rel ((≤) : β → β → Prop)]
lemma prod_Icc (a b : α × β) : Icc a b = (Icc a.fst b.fst).product (Icc a.snd b.snd) := rfl
end
section pre
variables {α : Type*} [preorder α] [locally_finite_order α] {a b c : α}

lemma Icc_ssubset_Icc_left (hab : a ≤ b) (h : c < b) : Icc a c ⊂ Icc a b :=
begin
  classical,
  rw finset.ssubset_iff,
  use b,
  simp only [hab, true_and, mem_Icc],
  refine ⟨λ hh, lt_irrefl c (h.trans_le hh),
    insert_subset.mpr ⟨right_mem_Icc.mpr hab, finset.subset_iff.mpr (λ x hx, _)⟩⟩,
  rw [mem_Icc] at ⊢ hx,
  exact ⟨hx.1, (hx.2.trans_lt h).le⟩,
end

lemma Icc_ssubset_Icc_right (hab : a ≤ b) (h : a < c) : Icc c b ⊂ Icc a b :=
@Icc_ssubset_Icc_left (order_dual α) _ _ _ _ _ hab h

lemma card_Icc_lt_card_Icc_left (hab : a ≤ b) (h : c < b) : (Icc a c).card < (Icc a b).card :=
card_lt_card (Icc_ssubset_Icc_left hab h)

lemma card_Icc_lt_card_Icc_right (hab : a ≤ b) (h : a < c) : (Icc c b).card < (Icc a b).card :=
@card_Icc_lt_card_Icc_left (order_dual α) _ _ _ _ _ hab h

end pre
variables {α : Type*} [partial_order α] [locally_finite_order α] {a b : α}

@[simp] lemma Ioc_insert_left [decidable_eq α] (h : a ≤ b) : insert a (Ioc a b) = Icc a b :=
@Ico_insert_right (order_dual α) _ _ _ _ _ h
local attribute [simp] Ico_insert_right

lemma Icc_eq_cons_Ioc (h : a ≤ b) : Icc a b = (Ioc a b).cons a left_not_mem_Ioc :=
finset.coe_inj.mp (by { classical, simp [h] })

lemma Icc_eq_cons_Ico (h : a ≤ b) : Icc a b = (Ico a b).cons b right_not_mem_Ico :=
finset.coe_inj.mp (by { classical, simp [h] })

section order_top
variables [order_top α]

@[simp]
lemma Ioi_insert [decidable_eq α] (a : α) : insert a (Ioi a) = Ici a := Ioc_insert_left le_top

lemma Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a left_not_mem_Ioc :=
finset.coe_inj.mp (by { classical, simp })

end order_top

section sum
variables {β : Type*} [add_comm_monoid β] {f : α → β}

lemma sum_Icc_eq_add_sum_Ioc (h : a ≤ b) : ∑ x in Icc a b, f x = f a + ∑ x in Ioc a b, f x :=
by rw [Icc_eq_cons_Ioc h, sum_cons]

section order_top
variables [order_top α]

lemma sum_Ici_eq_add_sum_Ioi (a : α) : ∑ x in Ici a, f x = f a + ∑ x in Ioi a, f x :=
sum_Icc_eq_add_sum_Ioc le_top

end order_top
end sum
end finset

open finset
open_locale big_operators

variables (𝕄 F 𝕜 𝕝 𝕞 α β : Type*)

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

/-! ### Additive and multiplicative structure -/

variables {𝕜 α}

instance : has_zero (incidence_algebra 𝕜 α) := ⟨⟨λ _ _, 0, λ _ _ _, rfl⟩⟩
instance : inhabited (incidence_algebra 𝕜 α) := ⟨0⟩

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

-- section smul_with_zero
-- variables [has_zero 𝕄] [has_zero 𝕜] [smul_with_zero 𝕄 𝕜] [has_le α]

-- instance : has_scalar 𝕄 (incidence_algebra 𝕜 α) :=
-- ⟨λ c f, ⟨c • f, λ a b h, by rw [pi.smul_apply, pi.smul_apply, eq_zero_of_not_le h, smul_zero']⟩⟩

-- @[simp] lemma smul_apply (c : 𝕄) (f : incidence_algebra 𝕜 α) (a b : α) : (c • f) a b
-- = c • f a b :=
-- rfl

-- instance : smul_with_zero 𝕄 (incidence_algebra 𝕜 α) :=
-- { smul := (•),
--   smul_zero := λ m, by { ext, exact smul_zero' _ _ },
--   zero_smul := λ m, by { ext, exact zero_smul _ _ } }

-- end smul_with_zero

section one
variables [preorder α] [decidable_eq α] [has_zero 𝕜] [has_one 𝕜]

instance : has_one (incidence_algebra 𝕜 α) :=
⟨⟨λ a b, if a = b then 1 else 0, λ a b h, ite_eq_right_iff.2 $ λ H, (h H.le).elim⟩⟩

@[simp] lemma one_apply (a b : α) : (1 : incidence_algebra 𝕜 α) a b = if a = b then 1 else 0 := rfl

end one

section co_union_lemmas
variables {α}
variables [partial_order α] [locally_finite_order α] [decidable_eq α]
-- TODO fix names of these lemmas
-- TODO copy more API from data.set.intervals.basic to finset
lemma Ici_eq_Ioi_union [order_top α] (x : α) : Ici x = Ioi x ∪ {x} := finset.coe_inj.mp (by simp)
lemma Iic_eq_Iio_union [order_bot α] (x : α) : Iic x = Iio x ∪ {x} := finset.coe_inj.mp (by simp)
lemma Icc_eq_Ico_union {x y : α} (hxy : x ≤ y) : Icc x y = Ico x y ∪ {y} :=
finset.coe_inj.mp (by simp [hxy, set.Ico_union_right])
lemma Icc_eq_Ioc_union {x y : α} (hxy : x ≤ y) : Icc x y = Ioc x y ∪ {x} :=
finset.coe_inj.mp (by simp [hxy, set.Ioc_union_left])
end co_union_lemmas

section mul
variables [preorder α] [locally_finite_order α] [add_comm_monoid 𝕜] [has_mul 𝕜]

instance : has_mul (incidence_algebra 𝕜 α) :=
⟨λ f g, ⟨λ a b, ∑ x in Icc a b, f a x * g x b, λ a b h, by rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp] lemma mul_apply (f g : incidence_algebra 𝕜 α) (a b : α) :
  (f * g) a b = ∑ x in Icc a b, f a x * g x b := rfl

end mul

instance [preorder α] [locally_finite_order α] [non_unital_non_assoc_semiring 𝕜] :
  non_unital_non_assoc_semiring (incidence_algebra 𝕜 α) :=
{ mul := (*),
  zero := 0,
  zero_mul := λ f, by { ext, exact sum_eq_zero (λ x _, zero_mul _) },
  mul_zero := λ f, by { ext, exact sum_eq_zero (λ x _, mul_zero _) },
  left_distrib := λ f g h,
    by { ext, exact eq.trans (sum_congr rfl $ λ x _, left_distrib _ _ _) sum_add_distrib },
  right_distrib := λ f g h,
    by { ext, exact eq.trans (sum_congr rfl $ λ x _, right_distrib _ _ _) sum_add_distrib },
  .. incidence_algebra.add_comm_monoid 𝕜 α }

instance [preorder α] [locally_finite_order α] [decidable_eq α] [non_assoc_semiring 𝕜] :
  non_assoc_semiring (incidence_algebra 𝕜 α) :=
{ mul := (*),
  zero := 0,
  one := 1,
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
  .. incidence_algebra.non_unital_non_assoc_semiring 𝕜 α }

instance [preorder α] [locally_finite_order α] [decidable_eq α] [semiring 𝕜] :
  semiring (incidence_algebra 𝕜 α) :=
{ mul := (*),
  mul_assoc := λ f g h, begin
    ext a b,
    simp only [mul_apply, sum_mul, mul_sum],
    rw [sum_sigma', sum_sigma'],
    dsimp,
    apply' sum_bij (λ (x : Σ i : α, α) hx, (sigma.mk x.snd x.fst : Σ i : α, α)),
    { rintro c hc,
      simp only [mem_sigma, mem_Icc] at hc,
      simp only [mem_sigma, mem_Icc],
      exact ⟨⟨hc.2.1, hc.2.2.trans hc.1.2⟩, hc.2.2, hc.1.2⟩ },
    { rintro c hc,
      simp only [mul_assoc] },
    { rintro ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ hc hd ⟨⟩,
      refl },
    { rintro c hc,
      simp only [exists_prop, sigma.exists, mem_sigma, heq_iff_eq, sigma.mk.inj_iff, mem_Icc] at *,
      exact ⟨c.2, c.1, ⟨⟨hc.1.1.trans hc.2.1, hc.2.2⟩, hc.1.1, hc.2.1⟩, c.eta.symm⟩ }
  end,
  one := 1,
  zero := 0,
  .. incidence_algebra.non_assoc_semiring 𝕜 α }

instance [preorder α] [locally_finite_order α] [decidable_eq α] [ring 𝕜] :
  ring (incidence_algebra 𝕜 α) :=
{ .. incidence_algebra.semiring 𝕜 α, .. incidence_algebra.add_group 𝕜 α }

/-! ### Scalar multiplication -/

section smul
variables [preorder α] [locally_finite_order α] [add_comm_monoid 𝕜] [add_comm_monoid 𝕝]
  [has_scalar 𝕜 𝕝]

instance : has_scalar (incidence_algebra 𝕜 α) (incidence_algebra 𝕝 α) :=
⟨λ f g, ⟨λ a b, ∑ x in Icc a b, f a x • g x b, λ a b h, by rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp] lemma smul_apply (f : incidence_algebra 𝕜 α) (g : incidence_algebra 𝕝 α) (a b : α) :
  (f • g) a b = ∑ x in Icc a b, f a x • g x b := rfl

end smul

instance [preorder α] [locally_finite_order α] [add_comm_monoid 𝕜] [monoid 𝕜] [semiring 𝕝]
  [add_comm_monoid 𝕞] [has_scalar 𝕜 𝕝] [module 𝕝 𝕞] [distrib_mul_action 𝕜 𝕞]
  [is_scalar_tower 𝕜 𝕝 𝕞] :
  is_scalar_tower (incidence_algebra 𝕜 α) (incidence_algebra 𝕝 α) (incidence_algebra 𝕞 α) :=
⟨λ f g h, begin
  ext a b,
  simp only [smul_apply, sum_smul, smul_sum],
  rw [sum_sigma', sum_sigma'],
  dsimp,
  apply' sum_bij (λ (x : Σ i : α, α) hx, (sigma.mk x.snd x.fst : Σ i : α, α)),
  { rintro c hc,
    simp only [mem_sigma, mem_Icc] at hc,
    simp only [mem_sigma, mem_Icc],
    exact ⟨⟨hc.2.1, hc.2.2.trans hc.1.2⟩, hc.2.2, hc.1.2⟩ },
  { rintro c hc,
    simp only [smul_assoc] },
  { rintro ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ hc hd ⟨⟩,
    refl },
  { rintro c hc,
    simp only [exists_prop, sigma.exists, mem_sigma, heq_iff_eq, sigma.mk.inj_iff, mem_Icc] at *,
    exact ⟨c.2, c.1, ⟨⟨hc.1.1.trans hc.2.1, hc.2.2⟩, hc.1.1, hc.2.1⟩, c.eta.symm⟩ }
end⟩

instance [preorder α] [locally_finite_order α] [decidable_eq α] [semiring 𝕜] [semiring 𝕝]
  [module 𝕜 𝕝] :
  module (incidence_algebra 𝕜 α) (incidence_algebra 𝕝 α) :=
{ smul := (•),
  one_smul := λ f, begin
    ext a b,
    simp [ite_smul, hab],
  end,
  mul_smul := λ f g h, begin
    convert smul_assoc _ _ _,
    ext a b,
    refl,
    apply_instance,
  end,
  smul_add := λ f g h,
    by { ext, exact eq.trans (sum_congr rfl $ λ x _, smul_add _ _ _) sum_add_distrib },
  add_smul := λ f g h,
    by { ext, exact eq.trans (sum_congr rfl $ λ x _, add_smul _ _ _) sum_add_distrib },
  zero_smul := λ f, by { ext, exact sum_eq_zero (λ x _, zero_smul _ _) },
  smul_zero := λ f, by { ext, exact sum_eq_zero (λ x _, smul_zero _) } }

/-! ### The Zeta and Möbius functions -/

section zeta
variables [has_zero 𝕜] [has_one 𝕜] [has_le α] [@decidable_rel α (≤)]

/-- The zeta function of the incidence algebra is the function that assigns 1 to every nonempty
interval, convolution with this function sums functions over intervals. -/
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

/-- The moebius function of the incidence algebra as a bare function defined recursively. -/
def mu_aux (a : α) : α → 𝕜
| b := if h : a = b then 1 else
  -∑ x in (Ico a b).attach,
    have ha : a ≤ x, begin cases x, rw mem_Ico at x_property, exact x_property.1, end,
    have hb : ↑x < b, begin cases x, rw mem_Ico at x_property, exact x_property.2, end,
    have (Icc a x).card < (Icc a b).card, from card_Icc_lt_card_Icc_left (ha.trans_lt hb).le hb,
    mu_aux x
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ b, (Icc a b).card)⟩] }

lemma mu_aux_apply (a b : α) :
  mu_aux 𝕜 α a b = if a = b then 1 else -∑ x in (Ico a b).attach, mu_aux 𝕜 α a x :=
by { convert has_well_founded.wf.fix_eq _ _, refl }

/-- The moebius function which inverts `zeta` as an element of the incidence algebra. -/
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

end mu
section mu_spec
-- we need partial order for this
variables [add_comm_group 𝕜] [has_one 𝕜] [partial_order α] [locally_finite_order α] [decidable_eq α]
variables {𝕜 α}

lemma mu_spec_of_ne_right {a b : α} (h : a ≠ b) : ∑ (x : α) in Icc a b, (mu 𝕜 α) a x = 0 :=
begin
  have : mu 𝕜 α a b = _ := mu_apply_of_ne h,
  by_cases hab : a ≤ b,
  { rw [Icc_eq_Ico_union hab, sum_union, sum_singleton, this, add_neg_self],
    simp, },
  { have : ∀ x ∈ Icc a b, ¬ a ≤ x,
    { intros x hx hn, apply hab, rw [mem_Icc] at hx, exact le_trans hn hx.2 },
    conv in (mu _ _ _ _) { rw eq_zero_of_not_le (this x H), },
    exact sum_const_zero, },
end
end mu_spec

section mu'
variables [add_comm_group 𝕜] [has_one 𝕜] [preorder α] [locally_finite_order α] [decidable_eq α]

-- this is the reversed definition of mu, which is equal to mu but easiest to prove equal
-- by showing that zeta * mu = 1 and mu' * zeta = 1
-- therefore mu' should be an implementation detail and not used
private def mu'_aux (b : α) : α → 𝕜
| a := if h : a = b then 1 else
  -∑ x in (Ioc a b).attach,
    have ha : a < x, begin cases x, rw mem_Ioc at x_property, exact x_property.1, end,
    have hb : ↑x ≤ b, begin cases x, rw mem_Ioc at x_property, exact x_property.2, end,
    have (Icc ↑x b).card < (Icc a b).card, from card_Icc_lt_card_Icc_right (ha.le.trans hb) ha,
    mu'_aux x
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ a, (Icc a b).card)⟩] }

private lemma mu'_aux_apply (a b : α) :
  mu'_aux 𝕜 α b a = if a = b then 1 else -∑ x in (Ioc a b).attach, mu'_aux 𝕜 α b x :=
by { convert has_well_founded.wf.fix_eq _ _, refl }

private def mu' : incidence_algebra 𝕜 α :=
⟨λ a b, mu'_aux 𝕜 α b a, λ a b, not_imp_comm.1 $ λ h, begin
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

lemma mu'_apply_of_eq {a b : α} (h : a = b) : mu' 𝕜 α a b = 1 :=
by rw [mu'_apply, if_pos h]

@[simp]
lemma mu'_apply_self (a : α) : mu' 𝕜 α a a = 1 := mu'_apply_of_eq rfl
end mu'

section mu'_spec
-- we need partial order for this
variables [add_comm_group 𝕜] [has_one 𝕜] [partial_order α] [locally_finite_order α] [decidable_eq α]
variables {𝕜 α}


lemma mu'_spec_of_ne_left {a b : α} (h : a ≠ b) : ∑ (x : α) in Icc a b, (mu' 𝕜 α) x b = 0 :=
begin
  have : mu' 𝕜 α a b = _ := mu'_apply_of_ne h,
  by_cases hab : a ≤ b,
  { rw [Icc_eq_Ioc_union hab, sum_union, sum_singleton, this, add_right_neg],
    simp, },
  { have : ∀ x ∈ Icc a b, ¬ x ≤ b,
    { intros x hx hn, apply hab, rw [mem_Icc] at hx, exact le_trans hx.1 hn },
    conv in (mu' _ _ _ _) { rw eq_zero_of_not_le (this x H), },
    exact sum_const_zero, },
end
end mu'_spec

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
    conv in (ite _ _ _) { rw [if_pos (mem_Icc.mp H).2] },
    rw mu_spec_of_ne_right he }
end

lemma zeta_mul_mu' : zeta 𝕜 α * mu' 𝕜 α = 1 :=
begin
  ext a b,
  rw [mul_apply, one_apply],
  split_ifs with he,
  { simp [he] },
  { simp only [zeta_apply, one_mul, ite_mul],
    conv in (ite _ _ _) { rw [if_pos (mem_Icc.mp H).1] },
    rw mu'_spec_of_ne_left he }
end

end mu_zeta

section mu_eq_mu'
variables [ring 𝕜] [partial_order α] [locally_finite_order α]
  [decidable_eq α]

lemma mu_eq_mu' : mu 𝕜 α = mu' 𝕜 α :=
begin
  letI : @decidable_rel α (≤) := classical.dec_rel _,
  exact left_inv_eq_right_inv (mu_mul_zeta 𝕜 α) (zeta_mul_mu' 𝕜 α)
end

lemma mu_apply_of_ne' {a b : α} (h : a ≠ b) : mu 𝕜 α a b = -∑ x in Ioc a b, mu 𝕜 α x b :=
begin
  rw mu_eq_mu',
  exact mu'_apply_of_ne h,
end

lemma zeta_mul_mu [@decidable_rel α (≤)] : zeta 𝕜 α * mu 𝕜 α = 1 :=
begin
  rw mu_eq_mu',
  exact zeta_mul_mu' 𝕜 α,
end

lemma mu_spec_of_ne_left {a b : α} (h : a ≠ b) : ∑ (x : α) in Icc a b, (mu 𝕜 α) x b = 0 :=
by rw [mu_eq_mu', mu'_spec_of_ne_left h]

end mu_eq_mu'

section order_dual
variables [ring 𝕜] [partial_order α] [locally_finite_order α] [decidable_eq α]

open order_dual
lemma mu_dual (a b : α) : mu 𝕜 (order_dual α) (to_dual a) (to_dual b) = mu 𝕜 α b a :=
begin
  letI : @decidable_rel α (≤) := classical.dec_rel _,
  let mud : incidence_algebra 𝕜 (order_dual α) := { to_fun := λ a b, mu 𝕜 α b a,
    eq_zero_of_not_le' := λ a b hab, eq_zero_of_not_le hab (mu 𝕜 α) },
  suffices : mu 𝕜 (order_dual α) = mud,
  { rw [this], refl, },
  suffices : mud * zeta 𝕜 (order_dual α) = 1,
  { rw ← mu_mul_zeta at this,
    apply_fun (* (mu 𝕜 (order_dual α))) at this,
    symmetry,
    simpa [mul_assoc, zeta_mul_mu] using this, },
  clear a b,
  ext a b,
  simp only [mul_boole, one_apply, mul_apply, coe_mk, zeta_apply],
  by_cases h : a = b,
  { simp [h], },
  { simp only [h, if_false],
    conv in (ite _ _ _)
    { rw if_pos (mem_Icc.mp H).2 },
    change ∑ (x : α) in (Icc b a : finset α), (mu 𝕜 α) x a = 0,
    exact mu_spec_of_ne_left _ _ (ne.symm h), },
end
end order_dual

section inversion_top
variables {α} [ring 𝕜] [partial_order α] [order_top α] [locally_finite_order α]
  [decidable_eq α] {a b : α}

/-- A general form of Möbius inversion. Based on Theorem 2.1.2 of Incidence Algebras by Spiegel and
O'Donnell. -/
lemma moebius_inversion_top (f g : α → 𝕜) (h : ∀ x, g x = ∑ y in Ici x, f y) (x : α) :
  f x = ∑ y in Ici x, mu 𝕜 α x y * g y :=
by letI : @decidable_rel α (≤) := classical.dec_rel _; symmetry; calc
  ∑ y in Ici x, mu 𝕜 α x y * g y
      = ∑ y in Ici x, mu 𝕜 α x y * ∑ z in Ici y, f z : by simp_rw [h]
  ... = ∑ y in Ici x, mu 𝕜 α x y * ∑ z in Ici y, zeta 𝕜 α y z * f z : by
      { simp_rw [zeta_apply],
        conv in (ite _ _ _)
        { rw if_pos (mem_Ici.mp H) },
        simp }
  ... = ∑ y in Ici x, ∑ z in Ici y, mu 𝕜 α x y * zeta 𝕜 α y z * f z : by simp [mul_sum]
  ... = ∑ z in Ici x, ∑ y in Icc x z, mu 𝕜 α x y * zeta 𝕜 α y z * f z : by
      { erw sum_sigma' (Ici x) (λ y, Ici y),
        erw sum_sigma' (Ici x) (λ z, Icc x z),
        simp only [mul_boole, zero_mul, ite_mul, zeta_apply],
        refine sum_bij (λ X hX, ⟨X.snd, X.fst⟩) _ _ _ _,
        { intros X hX,
          simp only [mem_Ici, mem_sigma, mem_Icc] at *,
          exact ⟨hX.1.trans hX.2, hX⟩, },
        { intros X hX,
          simp only at *, },
        { intros X Y ha hb h,
          simp [sigma.ext_iff] at *,
          rwa and_comm, },
        { intros X hX,
          use [⟨X.snd, X.fst⟩],
          simp only [and_true, mem_Ici, eq_self_iff_true, sigma.eta, mem_sigma, mem_Icc] at *,
          exact hX.2, }, }
  ... = ∑ z in Ici x, (mu 𝕜 α * zeta 𝕜 α) x z * f z : by
      { conv in ((mu _ _ * zeta _ _) _ _) { rw [mul_apply] },
        simp_rw [sum_mul] }
  ... = ∑ y in Ici x, ∑ z in Ici y, (1 : incidence_algebra 𝕜 α) x z * f z : by
      { simp [mu_mul_zeta 𝕜 α, sum_Ici_eq_add_sum_Ioi],
        conv in (ite _ _ _) { rw if_neg (ne_of_lt $ mem_Ioi.mp H) },
        conv in (ite _ _ _) { rw if_neg (not_lt_of_le $ (mem_Ioi.mp H).le) },
        simp }
  ... = f x : by { simp [one_apply, sum_Ici_eq_add_sum_Ioi],
        conv in (ite _ _ _) { rw if_neg (ne_of_lt $ mem_Ioi.mp H) },
        conv in (ite _ _ _) { rw if_neg (not_lt_of_le $ (mem_Ioi.mp H).le) },
        simp }

end inversion_top

section inversion_bot
variables [ring 𝕜] [partial_order α] [order_bot α] [locally_finite_order α] [decidable_eq α]

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
section preorder
variables {α β} [ring 𝕜] [preorder α] [preorder β]

section decidable_le
variables [decidable_rel ((≤) : α → α → Prop)] [decidable_rel ((≤) : β → β → Prop)]

lemma zeta_prod_apply (a b : α × β) : zeta 𝕜 (α × β) a b = zeta 𝕜 α a.1 b.1 * zeta 𝕜 β a.2 b.2 :=
by simp [ite_and, prod.le_def]

lemma zeta_prod_mk (a₁ a₂ : α) (b₁ b₂ : β) :
  zeta 𝕜 (α × β) (a₁, b₁) (a₂, b₂) = zeta 𝕜 α a₁ a₂ * zeta 𝕜 β b₁ b₂ :=
zeta_prod_apply _ _ _
end decidable_le

variables {α β}

variables [decidable_eq α] [decidable_eq β]
lemma one_prod_apply (a b : α × β) :
  (1 : incidence_algebra 𝕜 (α × β)) a b =
  (1 : incidence_algebra 𝕜 α) a.1 b.1 * (1 : incidence_algebra 𝕜 β) a.2 b.2 :=
by simp [ite_and, prod.ext_iff]

lemma one_prod_mk (a₁ a₂ : α) (b₁ b₂ : β) :
  (1 : incidence_algebra 𝕜 (α × β)) (a₁, b₁) (a₂, b₂) =
    (1 : incidence_algebra 𝕜 α) a₁ a₂ * (1 : incidence_algebra 𝕜 β) b₁ b₂ :=
one_prod_apply _ _ _

variables (α β)
variables [locally_finite_order α] [locally_finite_order β]

/-- A description of `mu` in a product of incidence algebras -/
def mu_prod : incidence_algebra 𝕜 (α × β) :=
{ to_fun := λ xu yv : α × β, mu 𝕜 α xu.fst yv.fst * mu 𝕜 β xu.snd yv.snd,
  eq_zero_of_not_le' := begin
    rintros ⟨a⟩ ⟨b⟩ hab,
    rw [prod.mk_le_mk, not_and_distrib] at hab,
    cases hab; simp [eq_zero_of_not_le hab],
end }

variables {α β}

lemma mu_prod_mk (x y : α) (u v : β) : mu_prod 𝕜 α β (x, u) (y, v) = mu 𝕜 α x y * mu 𝕜 β u v := rfl
lemma mu_prod_apply (a b : α × β) : mu_prod 𝕜 α β a b = mu 𝕜 α a.fst b.fst * mu 𝕜 β a.snd b.snd :=
rfl


end preorder

section partial_order
variables {α β} [ring 𝕜] [partial_order α] [partial_order β] [locally_finite_order α]
  [locally_finite_order β] [decidable_eq α] [decidable_eq β] [decidable_rel ((≤) : α → α → Prop)]
  [decidable_rel ((≤) : β → β → Prop)]

/-- The Möbius function on a product order. Based on Theorem 2.1.13 of Incidence Algebras
by Spiegel and O'Donnell. -/
lemma mu_prod_eq (x y : α) (u v : β) : mu 𝕜 (α × β) (x, u) (y, v) = mu 𝕜 α x y * mu 𝕜 β u v :=
begin
  suffices : mu 𝕜 (α × β) = mu_prod 𝕜 α β,
  { simp [this, mu_prod_apply] },
  suffices : mu_prod 𝕜 α β * zeta 𝕜 (α × β) = 1,
  { rw ← mu_mul_zeta at this,
    apply_fun (* (mu 𝕜 (α × β))) at this,
    symmetry,
    simpa [mul_assoc, zeta_mul_mu] using this },
  clear x y u v,
  ext ⟨x, u⟩ ⟨y, v⟩,
  simp_rw [mul_apply, zeta_prod_apply, mu_prod_apply, prod_Icc],
  convert_to ∑ (x_1 : α × β) in (Icc (x, u).fst (y, v).fst).product (Icc (x, u).snd (y, v).snd),
    (mu 𝕜 α) x x_1.fst * (zeta 𝕜 α) x_1.fst y * ((mu 𝕜 β) u x_1.snd * (zeta 𝕜 β) x_1.snd v) = _,
  { simp [mul_comm, mul_assoc] },
  rw ← sum_mul_sum (Icc x y) (Icc u v)
    (λ x_1f, (mu 𝕜 α) x x_1f * (zeta 𝕜 α) x_1f y)
    (λ x_1s, (mu 𝕜 β) u x_1s * (zeta 𝕜 β) x_1s v),
  rw one_prod_apply,
  congr; rw [← mu_mul_zeta, mul_apply],
end

end partial_order
end prod

section euler
variables [add_comm_group 𝕜] [has_one 𝕜] [preorder α] [bounded_order α] [locally_finite_order α]
  [decidable_eq α]

/-- The Euler characteristic of a finite bounded order. -/
def euler_char : 𝕜 := mu 𝕜 α ⊥ ⊤

end euler
end incidence_algebra
