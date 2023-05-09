/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import algebra.algebra.basic
import algebra.big_operators.ring
import algebra.module.big_operators
import group_theory.group_action.basic
import group_theory.group_action.pi
import data.finset.locally_finite

/-!
# Incidence algebras

Given a locally finite order `α` the incidence algebra over `α` is the type of functions from
non-empty intervals of `α` to some algebraic codomain.
This algebra has a natural multiplication operation whereby the product of two such functions
is defined on an interval by summing over all divisions into two subintervals the product of the
values of the original pair of functions.
This structure allows us to interpret many natural invariants of the intervals (such as their
cardinality) as elements of the incidence algebra. For instance the cardinality function, viewed as
an element of the incidence algebra, is simply the square of the function that takes constant value
one on all intervals. This constant function is called the zeta function, after
its connection with the Riemann zeta function.
The incidence algebra is a good setting for proving many inclusion-exclusion type principles, these
go under the name Möbius inversion, and are essentially due to the fact that the zeta function has
a multiplicative inverse in the incidence algebra, an inductively definable function called the
Möbius function that generalizes the Möbius function in number theory.


## References

- Aigner - Combinatorial Theory, Chapter IV
- Jacobson - Basic Algebra I, 8.6
- Rota - On the foundations of Combinatorial Theory
- Spiegel, O'Donnell - Incidence Algebras
- Kung, Rota, Yan - Combinatorics: The Rota Way, Chapter 3

## TODOs

Here are some additions to this file that could be made in the future:
- Generalize the construction of `mu` to invert any element of the incidence algebra `f` which has
  `f x x` a unit for all `x`.
- Give formulae for higher powers of zeta.
- A formula for the möbius function on a pi type similar to the one for products
- More examples / applications to different posets.
- Connection with Galois insertions
- Finsum version of Möbius inversion that holds even when an order doesn't have top/bot?
- Connect this theory to (infinite) matrices, giving maps of the incidence algebra to matrix rings
- Connect to the more advanced theory of arithmetic functions, and Dirichlet convolution.
-/

-- TODO: Rename `prod.Icc_eq` to `finset.Icc_prod_eq` to match `set.Icc_prod_eq`

open finset
open_locale big_operators

namespace finset

section
variables {α β : Type*} [preorder α] [preorder β] [locally_finite_order α] [locally_finite_order β]
  [decidable_rel ((≤) : α → α → Prop)] [decidable_rel ((≤) : β → β → Prop)]
lemma prod_Icc (a b : α × β) : Icc a b = (Icc a.fst b.fst).product (Icc a.snd b.snd) := by rw prod.Icc_eq
end
section pre
variables {α : Type*} [preorder α] [locally_finite_order α] {a b c : α}

lemma card_Icc_lt_card_Icc_left (hab : a ≤ b) (h : c < b) : (Icc a c).card < (Icc a b).card :=
card_lt_card (Icc_ssubset_Icc_right hab le_rfl h)

lemma card_Icc_lt_card_Icc_right (hab : a ≤ b) (h : a < c) : (Icc c b).card < (Icc a b).card :=
@card_Icc_lt_card_Icc_left αᵒᵈ _ _ _ _ _ hab h

end pre

variables {α β : Type*} [partial_order α] [comm_monoid β] {f : α → β} {a b : α}

section locally_finite_order
variables [locally_finite_order α]

@[to_additive] lemma mul_prod_Ico (h : a ≤ b) : f b * ∏ x in Ico a b, f x = ∏ x in Icc a b, f x :=
by rw [Icc_eq_cons_Ico h, prod_cons]

@[to_additive] lemma mul_prod_Ioc (h : a ≤ b) : f a * ∏ x in Ioc a b, f x = ∏ x in Icc a b, f x :=
by rw [Icc_eq_cons_Ioc h, prod_cons]

end locally_finite_order

section locally_finite_order_top
variables [locally_finite_order_top α]

@[to_additive] lemma mul_prod_Ioi (a : α) : f a * ∏ x in Ioi a, f x = ∏ x in Ici a, f x :=
by rw [Ici_eq_cons_Ioi, prod_cons]

end locally_finite_order_top

section locally_finite_order_bot
variables [locally_finite_order_bot α]

@[to_additive] lemma mul_prod_Iio (a : α) : f a * ∏ x in Iio a, f x = ∏ x in Iic a, f x :=
by rw [Iic_eq_cons_Iio, prod_cons]

end locally_finite_order_bot
end finset

@[simp] lemma smul_boole {M A} [has_zero A] [smul_zero_class M A] (P : Prop) [decidable P] (a : M)
  (b : A) : a • (if P then b else 0) = if P then (a • b) else 0 :=
by rw [smul_ite, smul_zero]

@[simp] lemma boole_smul {M A} [semiring M] [add_comm_monoid A] [module M A] (P : Prop)
  [decidable P] (a : A) : (if P then (1 : M) else 0) • a = if P then a else 0 :=
by rw [ite_smul, one_smul, zero_smul]

open finset order_dual
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

variables {𝕜 α} {a b : α}

lemma apply_eq_zero_of_not_le (h : ¬ a ≤ b) (f : incidence_algebra 𝕜 α) : f a b = 0 :=
eq_zero_of_not_le' _ h

lemma le_of_ne_zero {f : incidence_algebra 𝕜 α} : f a b ≠ 0 → a ≤ b :=
not_imp_comm.1 $ eq_zero_of_not_le' _

-- completely uninteresting lemmas about coercion to function, that all homs need
section coes

-- Fallback `has_coe_to_fun` instance to help the elaborator
instance : has_coe_to_fun (incidence_algebra 𝕜 α) (λ _, α → α → 𝕜) := fun_like.has_coe_to_fun

-- this must come after the coe_to_fun definitions
initialize_simps_projections incidence_algebra (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : incidence_algebra 𝕜 α) : f.to_fun = f := rfl

@[simp, norm_cast] lemma coe_mk (f : α → α → 𝕜) (h) : (mk f h : α → α → 𝕜) = f := rfl

protected lemma congr_fun {f g : incidence_algebra 𝕜 α} (h : f = g) (a b : α) : f a b = g a b :=
congr_arg (λ f : incidence_algebra 𝕜 α, f a b) h

protected lemma congr_arg (f : incidence_algebra 𝕜 α) {a₁ a₂ b₁ b₂ : α} (ha : a₁ = a₂)
  (hb : b₁ = b₂) :
  f a₁ b₁ = f a₂ b₂ :=
congr_arg2 f ha hb

@[simp] lemma coe_inj {f g : incidence_algebra 𝕜 α} : (f : α → α → 𝕜) = g ↔ f = g :=
fun_like.coe_injective.eq_iff

@[ext] lemma ext ⦃f g : incidence_algebra 𝕜 α⦄ (h : ∀ a b (hab : a ≤ b), f a b = g a b) : f = g :=
begin
  refine fun_like.coe_injective (funext₂ $ λ a b, _),
  by_cases hab : a ≤ b,
  { exact h _ _ hab },
  { rw [apply_eq_zero_of_not_le hab, apply_eq_zero_of_not_le hab] }
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
⟨λ f g, ⟨f + g, λ a b h, by simp_rw [pi.add_apply, apply_eq_zero_of_not_le h, zero_add]⟩⟩

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
⟨λ f, ⟨-f, λ a b h, by simp_rw [pi.neg_apply, apply_eq_zero_of_not_le h, neg_zero]⟩⟩

instance : has_sub (incidence_algebra 𝕜 α) :=
⟨λ f g, ⟨f - g, λ a b h, by simp_rw [pi.sub_apply, apply_eq_zero_of_not_le h, sub_zero]⟩⟩

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

/-! ### Scalar multiplication betwen incidence algebras -/

section smul
variables [preorder α] [locally_finite_order α] [add_comm_monoid 𝕜] [add_comm_monoid 𝕝]
  [has_smul 𝕜 𝕝]

instance : has_smul (incidence_algebra 𝕜 α) (incidence_algebra 𝕝 α) :=
⟨λ f g, ⟨λ a b, ∑ x in Icc a b, f a x • g x b, λ a b h, by rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp] lemma smul_apply (f : incidence_algebra 𝕜 α) (g : incidence_algebra 𝕝 α) (a b : α) :
  (f • g) a b = ∑ x in Icc a b, f a x • g x b := rfl

end smul

instance [preorder α] [locally_finite_order α] [add_comm_monoid 𝕜] [monoid 𝕜] [semiring 𝕝]
  [add_comm_monoid 𝕞] [has_smul 𝕜 𝕝] [module 𝕝 𝕞] [distrib_mul_action 𝕜 𝕞]
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

section smul_with_zero
variables [has_zero 𝕜] [has_zero 𝕝] [smul_with_zero 𝕜 𝕝] [has_le α]

instance incidence_algebra.has_smul_right : has_smul 𝕜 (incidence_algebra 𝕝 α) :=
⟨λ c f, ⟨c • f, λ a b h, by rw [pi.smul_apply, pi.smul_apply, apply_eq_zero_of_not_le h, smul_zero]⟩⟩

@[simp] lemma smul_apply' (c : 𝕜) (f : incidence_algebra 𝕝 α) (a b : α) : (c • f) a b = c • f a b :=
rfl

instance incidence_algebra.smul_with_zero_right : smul_with_zero 𝕜 (incidence_algebra 𝕝 α) :=
{ smul := (•),
  smul_zero := λ m, by { ext, exact smul_zero _ },
  zero_smul := λ m, by { ext, exact zero_smul _ _ } }

end smul_with_zero

instance incidence_algebra.module_right [preorder α] [semiring 𝕜] [add_comm_monoid 𝕝] [module 𝕜 𝕝] :
  module 𝕜 (incidence_algebra 𝕝 α) :=
{ smul := (•),
  one_smul := λ f, by { ext, exact one_smul _ _ },
  mul_smul := λ c d f, by { ext, exact mul_smul _ _ _ },
  smul_add := λ c f g, by { ext, exact smul_add _ _ _ },
  add_smul := λ c f g, by { ext, exact add_smul _ _ _ },
  .. incidence_algebra.smul_with_zero_right 𝕜 𝕝 α }

lemma smul_smul_smul_comm {α β γ δ : Type*} [has_smul α β] [has_smul α γ] [has_smul β δ]
  [has_smul α δ] [has_smul γ δ] [is_scalar_tower α β δ] [is_scalar_tower α γ δ]
  [smul_comm_class β γ δ] (a : α) (b : β) (c : γ) (d : δ) :
  (a • b) • (c • d) = (a • c) • b • d :=
by { rw [smul_assoc, smul_assoc, smul_comm b], apply_instance }

instance incidence_algebra.algebra_right [partial_order α] [locally_finite_order α] [decidable_eq α]
  [comm_semiring 𝕜] [comm_semiring 𝕝] [algebra 𝕜 𝕝] :
  algebra 𝕜 (incidence_algebra 𝕝 α) :=
{ smul := (•),
  to_fun := λ c, algebra_map 𝕜 𝕝 c • 1,
  map_one' := by { ext,
    simp only [mul_boole, one_apply, algebra.id.smul_eq_mul, smul_apply', map_one] },
  map_mul' := λ c d, begin
    ext,
    obtain rfl | h := eq_or_ne a b,
    { simp only [smul_boole, one_apply, algebra.id.smul_eq_mul, mul_apply, algebra.mul_smul_comm,
        boole_smul, smul_apply', ←ite_and, algebra_map_smul, map_mul, algebra.smul_mul_assoc,
        if_pos rfl, eq_comm, and_self, Icc_self],
      simp only [mul_one, if_true, algebra.mul_smul_comm, smul_boole, zero_mul, ite_mul, sum_ite_eq,
        algebra.smul_mul_assoc, mem_singleton],
      rw [algebra.algebra_map_eq_smul_one, algebra.algebra_map_eq_smul_one],
      simp only [mul_one, algebra.mul_smul_comm, algebra.smul_mul_assoc, if_pos rfl] },
    { simp only [true_and, if_t_t, le_refl, one_apply, mul_one, algebra.id.smul_eq_mul, mul_apply,
        algebra.mul_smul_comm, smul_boole, zero_mul, smul_apply', algebra_map_smul, ←ite_and,
        ite_mul, mul_ite, map_mul, mem_Icc, sum_ite_eq, mul_zero, smul_zero, algebra.smul_mul_assoc,
        if_pos rfl, if_neg h],
      refine (sum_eq_zero $ λ x _, _).symm,
      exact if_neg (λ hx, h $ hx.2.trans hx.1) }
  end,
  map_zero' := by rw [map_zero, zero_smul],
  map_add' := λ c d, by rw [map_add, add_smul],
  commutes' := λ c f, by { classical, ext, simp [if_pos hab] },
  smul_def' := λ c f, by { classical, ext, simp [if_pos hab] } }

/-! ### The Lambda function -/

section lambda
variables [has_zero 𝕜] [has_one 𝕜] [preorder α] [decidable_eq α] [@decidable_rel α (⋖)]

/-- The lambda function of the incidence algebra is the function that assigns `1` to every nonempty
interval of cardinality one or two. -/
def lambda : incidence_algebra 𝕜 α :=
⟨λ a b, if a = b ∨ a ⋖ b then 1 else 0, λ a b h, if_neg (λ hh, h (hh.elim eq.le covby.le))⟩

variables {𝕜 α}

@[simp] lemma lambda_apply (a b : α) : lambda 𝕜 α a b = if a = b ∨ a ⋖ b then 1 else 0 := rfl

end lambda

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

lemma zeta_mul_zeta [semiring 𝕜] [preorder α] [locally_finite_order α]
  [@decidable_rel α (≤)] (a b : α) :
  (zeta 𝕜 α * zeta 𝕜 α) a b = (Icc a b).card :=
begin
  rw [mul_apply, card_eq_sum_ones, nat.cast_sum, nat.cast_one],
  refine sum_congr rfl (λ x hx, _),
  rw mem_Icc at hx,
  rw [zeta_of_le hx.1, zeta_of_le hx.2, one_mul],
end

lemma zeta_mul_kappa [semiring 𝕜] [preorder α] [locally_finite_order α]
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

/-- The Möbius function of the incidence algebra as a bare function defined recursively. -/
def mu_aux (a : α) : α → 𝕜
| b := if h : a = b then 1 else -∑ x in (Ico a b).attach,
    let h := mem_Ico.1 x.2 in
    have (Icc a x).card < (Icc a b).card :=
      card_lt_card (Icc_ssubset_Icc_right (h.1.trans h.2.le) le_rfl h.2),
    mu_aux x
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ b, (Icc a b).card)⟩] }

lemma mu_aux_apply (a b : α) :
  mu_aux 𝕜 α a b = if a = b then 1 else -∑ x in (Ico a b).attach, mu_aux 𝕜 α a x :=
by { convert has_well_founded.wf.fix_eq _ _, refl }

/-- The Möbius function which inverts `zeta` as an element of the incidence algebra. -/
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

lemma mu_apply_of_eq {a b : α} (h : a = b) : mu 𝕜 α a b = 1 := by rw [mu_apply, if_pos h]

@[simp] lemma mu_apply_self (a : α) : mu 𝕜 α a a = 1 := mu_apply_of_eq rfl

lemma mu_apply_of_ne {a b : α} (h : a ≠ b) : mu 𝕜 α a b = -∑ x in Ico a b, mu 𝕜 α a x :=
by rw [mu_apply, if_neg h]

end mu

section mu_spec
variables {𝕜 α} [add_comm_group 𝕜] [has_one 𝕜] [partial_order α] [locally_finite_order α]
  [decidable_eq α]

-- we need partial order for this
lemma mu_spec_of_ne_right {a b : α} (h : a ≠ b) : ∑ x in Icc a b, mu 𝕜 α a x = 0 :=
begin
  have : mu 𝕜 α a b = _ := mu_apply_of_ne h,
  by_cases hab : a ≤ b,
  { rw [←add_sum_Ico hab, this, neg_add_self] },
  { have : ∀ x ∈ Icc a b, ¬ a ≤ x,
    { intros x hx hn, apply hab, rw [mem_Icc] at hx, exact le_trans hn hx.2 },
    conv in (mu _ _ _ _) { rw apply_eq_zero_of_not_le (this x H) },
    exact sum_const_zero },
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
    let h := mem_Ioc.1 x.2 in
    have (Icc ↑x b).card < (Icc a b).card :=
      card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl),
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

lemma mu'_apply_of_eq {a b : α} (h : a = b) : mu' 𝕜 α a b = 1 := by rw [mu'_apply, if_pos h]

@[simp] lemma mu'_apply_self (a : α) : mu' 𝕜 α a a = 1 := mu'_apply_of_eq rfl

end mu'

section mu'_spec
-- we need partial order for this
variables [add_comm_group 𝕜] [has_one 𝕜] [partial_order α] [locally_finite_order α] [decidable_eq α]
variables {𝕜 α}

lemma mu'_spec_of_ne_left {a b : α} (h : a ≠ b) : ∑ x in Icc a b, (mu' 𝕜 α) x b = 0 :=
begin
  have : mu' 𝕜 α a b = _ := mu'_apply_of_ne h,
  by_cases hab : a ≤ b,
  { rw [←add_sum_Ioc hab, this, neg_add_self] },
  { have : ∀ x ∈ Icc a b, ¬ x ≤ b,
    { intros x hx hn, apply hab, rw [mem_Icc] at hx, exact le_trans hx.1 hn },
    conv in (mu' _ _ _ _) { rw apply_eq_zero_of_not_le (this x H) },
    exact sum_const_zero }
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
variables [ring 𝕜] [partial_order α] [locally_finite_order α] [decidable_eq α]

lemma mu_eq_mu' : mu 𝕜 α = mu' 𝕜 α := left_inv_eq_right_inv (mu_mul_zeta 𝕜 α) (zeta_mul_mu' 𝕜 α)

lemma mu_apply_of_ne' {a b : α} (h : a ≠ b) : mu 𝕜 α a b = -∑ x in Ioc a b, mu 𝕜 α x b :=
by { rw mu_eq_mu', exact mu'_apply_of_ne h }

lemma zeta_mul_mu [@decidable_rel α (≤)] : zeta 𝕜 α * mu 𝕜 α = 1 :=
by { rw mu_eq_mu', exact zeta_mul_mu' 𝕜 α }

lemma mu_spec_of_ne_left {a b : α} (h : a ≠ b) : ∑ x in Icc a b, mu 𝕜 α x b = 0 :=
by rw [mu_eq_mu', mu'_spec_of_ne_left h]

end mu_eq_mu'

section order_dual
variables [ring 𝕜] [partial_order α] [locally_finite_order α] [decidable_eq α]

lemma mu_dual (a b : α) : mu 𝕜 αᵒᵈ (to_dual a) (to_dual b) = mu 𝕜 α b a :=
begin
  letI : @decidable_rel α (≤) := classical.dec_rel _,
  let mud : incidence_algebra 𝕜 αᵒᵈ := { to_fun := λ a b, mu 𝕜 α b a,
    eq_zero_of_not_le' := λ a b hab, apply_eq_zero_of_not_le hab _ },
  suffices : mu 𝕜 αᵒᵈ = mud,
  { rw [this], refl },
  suffices : mud * zeta 𝕜 αᵒᵈ = 1,
  { rw ← mu_mul_zeta at this,
    apply_fun (* (mu 𝕜 αᵒᵈ)) at this,
    symmetry,
    simpa [mul_assoc, zeta_mul_mu] using this },
  clear a b,
  ext a b,
  simp only [mul_boole, one_apply, mul_apply, coe_mk, zeta_apply],
  by_cases h : a = b,
  { simp [h] },
  { simp only [h, if_false],
    conv in (ite _ _ _)
    { rw if_pos (mem_Icc.mp H).2 },
    change ∑ x in (Icc b a : finset α), mu 𝕜 α x a = 0,
    exact mu_spec_of_ne_left _ _ (ne.symm h) }
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
          exact ⟨hX.1.trans hX.2, hX⟩ },
        { intros X hX,
          simp only at * },
        { intros X Y ha hb h,
          simp [sigma.ext_iff] at *,
          rwa and_comm },
        { intros X hX,
          use [⟨X.snd, X.fst⟩],
          simp only [and_true, mem_Ici, eq_self_iff_true, sigma.eta, mem_sigma, mem_Icc] at *,
          exact hX.2 } }
  ... = ∑ z in Ici x, (mu 𝕜 α * zeta 𝕜 α) x z * f z : by
      { conv in ((mu _ _ * zeta _ _) _ _) { rw [mul_apply] },
        simp_rw [sum_mul] }
  ... = ∑ y in Ici x, ∑ z in Ici y, (1 : incidence_algebra 𝕜 α) x z * f z : by
      { simp [mu_mul_zeta 𝕜 α, ←add_sum_Ioi],
        conv in (ite _ _ _) { rw if_neg (ne_of_lt $ mem_Ioi.mp H) },
        conv in (ite _ _ _) { rw if_neg (not_lt_of_le $ (mem_Ioi.mp H).le) },
        simp }
  ... = f x : by { simp [one_apply, ←add_sum_Ioi],
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
  convert @moebius_inversion_top 𝕜 αᵒᵈ _ _ _ _ _ f g h x,
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
    cases hab; simp [apply_eq_zero_of_not_le hab],
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
    mu 𝕜 α x x_1.fst * (zeta 𝕜 α) x_1.fst y * ((mu 𝕜 β) u x_1.snd * (zeta 𝕜 β) x_1.snd v) = _,
  { simp [mul_comm, mul_assoc] },
  rw ← sum_mul_sum (Icc x y) (Icc u v)
    (λ x_1f, mu 𝕜 α x x_1f * (zeta 𝕜 α) x_1f y)
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
