/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import algebra.module.pi
import algebra.module.linear_map
import algebra.big_operators.basic
import data.set.finite
import group_theory.submonoid.membership

/-!
# Dependent functions with finite support

For a non-dependent version see `data/finsupp.lean`.
-/

universes u u₁ u₂ v v₁ v₂ v₃ w x y l

open_locale big_operators

variables (ι : Type u) {γ : Type w} (β : ι → Type v) {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace dfinsupp

variable [Π i, has_zero (β i)]

/-- An auxiliary structure used in the definition of of `dfinsupp`,
the type used to make infinite direct sum of modules over a ring. -/
structure pre : Type (max u v) :=
(to_fun : Π i, β i)
(pre_support : multiset ι)
(zero : ∀ i, i ∈ pre_support ∨ to_fun i = 0)

instance inhabited_pre : inhabited (pre ι β) :=
⟨⟨λ i, 0, ∅, λ i, or.inr rfl⟩⟩

instance : setoid (pre ι β) :=
{ r := λ x y, ∀ i, x.to_fun i = y.to_fun i,
  iseqv := ⟨λ f i, rfl, λ f g H i, (H i).symm,
    λ f g h H1 H2 i, (H1 i).trans (H2 i)⟩ }

end dfinsupp

variable {ι}
/-- A dependent function `Π i, β i` with finite support. -/
@[reducible]
def dfinsupp [Π i, has_zero (β i)] : Type* :=
quotient (dfinsupp.pre.setoid ι β)
variable {β}

notation `Π₀` binders `, ` r:(scoped f, dfinsupp f) := r
infix ` →ₚ `:25 := dfinsupp

namespace dfinsupp

section basic
variables [Π i, has_zero (β i)] [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]

instance : has_coe_to_fun (Π₀ i, β i) (λ _, Π i, β i) :=
⟨λ f, quotient.lift_on f pre.to_fun $ λ _ _, funext⟩

instance : has_zero (Π₀ i, β i) := ⟨⟦⟨0, ∅, λ i, or.inr rfl⟩⟧⟩
instance : inhabited (Π₀ i, β i) := ⟨0⟩

@[simp]
lemma coe_pre_mk (f : Π i, β i) (s : multiset ι) (hf) :
  ⇑(⟦⟨f, s, hf⟩⟧ : Π₀ i, β i) = f := rfl

@[simp] lemma coe_zero : ⇑(0 : Π₀ i, β i) = 0 := rfl
lemma zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0 := rfl

lemma coe_fn_injective : @function.injective (Π₀ i, β i) (Π i, β i) coe_fn :=
λ f g H, quotient.induction_on₂ f g (λ _ _ H, quotient.sound H) (congr_fun H)

@[ext] lemma ext {f g : Π₀ i, β i} (H : ∀ i, f i = g i) : f = g :=
coe_fn_injective (funext H)

lemma ext_iff {f g : Π₀ i, β i} : f = g ↔ ∀ i, f i = g i :=
coe_fn_injective.eq_iff.symm.trans function.funext_iff

/-- The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `map_range f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `dfinsupp.map_range.add_monoid_hom`
* `dfinsupp.map_range.add_equiv`
* `dfinsupp.map_range.linear_map`
* `dfinsupp.map_range.linear_equiv`
-/
def map_range (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) : (Π₀ i, β₁ i) → Π₀ i, β₂ i :=
quotient.map
  (λ x, ⟨λ i, f i (x.1 i), x.2, λ i, (x.3 i).imp_right $ λ H, by rw [H, hf]⟩)
  (λ x y H i, by simp only [H i])

@[simp] lemma map_range_apply
  (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) :
  map_range f hf g i = f i (g i) :=
quotient.induction_on g $ λ x, rfl

@[simp] lemma map_range_id (h : ∀ i, id (0 : β₁ i) = 0 := λ i, rfl) (g : Π₀ (i : ι), β₁ i) :
  map_range (λ i, (id : β₁ i → β₁ i)) h g = g :=
by { ext, simp only [map_range_apply, id.def] }

lemma map_range_comp (f : Π i, β₁ i → β₂ i) (f₂ : Π i, β i → β₁ i)
  (hf : ∀ i, f i 0 = 0) (hf₂ : ∀ i, f₂ i 0 = 0) (h : ∀ i, (f i ∘ f₂ i) 0 = 0)
  (g : Π₀ (i : ι), β i) :
  map_range (λ i, f i ∘ f₂ i) h g = map_range f hf (map_range f₂ hf₂ g) :=
by { ext, simp only [map_range_apply] }

@[simp] lemma map_range_zero (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
  map_range f hf (0 : Π₀ i, β₁ i) = 0 :=
by { ext, simp only [map_range_apply, coe_zero, pi.zero_apply, hf] }

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i 0 0 = 0`.
Then `zip_with f hf` is a binary operation `Π₀ i, β₁ i → Π₀ i, β₂ i → Π₀ i, β i`. -/
def zip_with (f : Π i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) :
  (Π₀ i, β₁ i) → (Π₀ i, β₂ i) → (Π₀ i, β i) :=
begin
  refine quotient.map₂
    (λ x y, ⟨λ i, f i (x.1 i) (y.1 i), x.2 + y.2, λ i, _⟩) _,
  { cases x.3 i with h1 h1,
    { left, rw multiset.mem_add, left, exact h1 },
    cases y.3 i with h2 h2,
    { left, rw multiset.mem_add, right, exact h2 },
    right, rw [h1, h2, hf] },
  exact λ x₁ x₂ H1 y₁ y₂ H2 i, by simp only [H1 i, H2 i]
end

@[simp] lemma zip_with_apply
  (f : Π i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i) (g₂ : Π₀ i, β₂ i) (i : ι) :
  zip_with f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
quotient.induction_on₂ g₁ g₂ $ λ _ _, rfl

end basic

section algebra

instance [Π i, add_zero_class (β i)] : has_add (Π₀ i, β i) :=
⟨zip_with (λ _, (+)) (λ _, add_zero 0)⟩

lemma add_apply [Π i, add_zero_class (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
  (g₁ + g₂) i = g₁ i + g₂ i :=
zip_with_apply _ _ g₁ g₂ i

@[simp] lemma coe_add [Π i, add_zero_class (β i)] (g₁ g₂ : Π₀ i, β i) :
  ⇑(g₁ + g₂) = g₁ + g₂ :=
funext $ add_apply g₁ g₂

instance [Π i, add_zero_class (β i)] : add_zero_class (Π₀ i, β i) :=
{ zero      := 0,
  add       := (+),
  zero_add  := λ f, ext $ λ i, by simp only [add_apply, zero_apply, zero_add],
  add_zero  := λ f, ext $ λ i, by simp only [add_apply, zero_apply, add_zero] }

instance [Π i, add_monoid (β i)] : add_monoid (Π₀ i, β i) :=
{ add_monoid .
  zero      := 0,
  add       := (+),
  add_assoc := λ f g h, ext $ λ i, by simp only [add_apply, add_assoc],
  .. dfinsupp.add_zero_class }

/-- Coercion from a `dfinsupp` to a pi type is an `add_monoid_hom`. -/
def coe_fn_add_monoid_hom [Π i, add_zero_class (β i)] : (Π₀ i, β i) →+ (Π i, β i) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add }

/-- Evaluation at a point is an `add_monoid_hom`. This is the finitely-supported version of
`pi.eval_add_monoid_hom`. -/
def eval_add_monoid_hom [Π i, add_zero_class (β i)] (i : ι) : (Π₀ i, β i) →+ β i :=
(pi.eval_add_monoid_hom β i).comp coe_fn_add_monoid_hom

instance [Π i, add_comm_monoid (β i)] : add_comm_monoid (Π₀ i, β i) :=
{ add_comm := λ f g, ext $ λ i, by simp only [add_apply, add_comm],
  nsmul := λ n v, v.map_range (λ _, (•) n) (λ _, smul_zero _),
  nsmul_zero' := λ n, ext $ λ i, by simp only [map_range_apply, zero_apply, zero_smul],
  nsmul_succ' := λ n z, ext $ λ i, by simp only [map_range_apply, add_apply,
    nat.succ_eq_one_add, add_smul, one_smul],
  .. dfinsupp.add_monoid }

@[simp] lemma coe_finset_sum {α} [Π i, add_comm_monoid (β i)] (s : finset α) (g : α → Π₀ i, β i) :
  ⇑(∑ a in s, g a) = ∑ a in s, g a :=
(coe_fn_add_monoid_hom : _ →+ (Π i, β i)).map_sum g s

@[simp] lemma finset_sum_apply {α} [Π i, add_comm_monoid (β i)] (s : finset α) (g : α → Π₀ i, β i)
  (i : ι) :
  (∑ a in s, g a) i = ∑ a in s, g a i :=
(eval_add_monoid_hom i : _ →+ β i).map_sum g s

instance [Π i, add_group (β i)] : has_neg (Π₀ i, β i) :=
⟨λ f, f.map_range (λ _, has_neg.neg) (λ _, neg_zero)⟩

lemma neg_apply [Π i, add_group (β i)] (g : Π₀ i, β i) (i : ι) : (- g) i = - g i :=
map_range_apply _ _ g i

@[simp] lemma coe_neg [Π i, add_group (β i)] (g : Π₀ i, β i) : ⇑(- g) = - g :=
funext $ neg_apply g

instance [Π i, add_group (β i)] : has_sub (Π₀ i, β i) :=
⟨zip_with (λ _, has_sub.sub) (λ _, sub_zero 0)⟩

lemma sub_apply [Π i, add_group (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
  (g₁ - g₂) i = g₁ i - g₂ i :=
zip_with_apply _ _ g₁ g₂ i

@[simp] lemma coe_sub [Π i, add_group (β i)] (g₁ g₂ : Π₀ i, β i) :
  ⇑(g₁ - g₂) = g₁ - g₂ :=
funext $ sub_apply g₁ g₂

instance [Π i, add_group (β i)] : add_group (Π₀ i, β i) :=
{ add_left_neg := λ f, ext $ λ i, by simp only [add_apply, neg_apply, zero_apply, add_left_neg],
  sub_eq_add_neg := λ f g, ext $ λ i,
    by simp only [sub_apply, add_apply, neg_apply, sub_eq_add_neg],
  .. dfinsupp.add_monoid,
  .. dfinsupp.has_sub,
  .. dfinsupp.has_neg }

instance [Π i, add_comm_group (β i)] : add_comm_group (Π₀ i, β i) :=
{ gsmul := λ n v, v.map_range (λ _, (•) n) (λ _, smul_zero _),
  gsmul_neg' := λ n f, ext $ λ i, by
    rw [neg_apply, map_range_apply, map_range_apply, gsmul_neg_succ_of_nat, nsmul_eq_smul_cast ℤ,
      int.nat_cast_eq_coe_nat],
  gsmul_zero' := λ n, ext $ λ i, by simp only [map_range_apply, zero_apply, zero_smul],
  gsmul_succ' := λ n f, ext $ λ i, by simp [map_range_apply, add_smul, add_comm],
  ..@dfinsupp.add_comm_monoid _ β _,
  ..dfinsupp.add_group }

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
instance [monoid γ] [Π i, add_monoid (β i)] [Π i, distrib_mul_action γ (β i)] :
  has_scalar γ (Π₀ i, β i) :=
⟨λc v, v.map_range (λ _, (•) c) (λ _, smul_zero _)⟩

lemma smul_apply [monoid γ] [Π i, add_monoid (β i)]
  [Π i, distrib_mul_action γ (β i)] (b : γ) (v : Π₀ i, β i) (i : ι) :
  (b • v) i = b • (v i) :=
map_range_apply _ _ v i

@[simp] lemma coe_smul [monoid γ] [Π i, add_monoid (β i)]
  [Π i, distrib_mul_action γ (β i)] (b : γ) (v : Π₀ i, β i) :
  ⇑(b • v) = b • v :=
funext $ smul_apply b v

instance {δ : Type*} [monoid γ] [monoid δ]
  [Π i, add_monoid (β i)] [Π i, distrib_mul_action γ (β i)] [Π i, distrib_mul_action δ (β i)]
  [Π i, smul_comm_class γ δ (β i)] :
  smul_comm_class γ δ (Π₀ i, β i) :=
{ smul_comm := λ r s m, ext $ λ i, by simp only [smul_apply, smul_comm r s (m i)] }

instance {δ : Type*} [monoid γ] [monoid δ]
  [Π i, add_monoid (β i)] [Π i, distrib_mul_action γ (β i)] [Π i, distrib_mul_action δ (β i)]
  [has_scalar γ δ] [Π i, is_scalar_tower γ δ (β i)] :
  is_scalar_tower γ δ (Π₀ i, β i) :=
{ smul_assoc := λ r s m, ext $ λ i, by simp only [smul_apply, smul_assoc r s (m i)] }

/-- Dependent functions with finite support inherit a `distrib_mul_action` structure from such a
structure on each coordinate. -/
instance [monoid γ] [Π i, add_monoid (β i)] [Π i, distrib_mul_action γ (β i)] :
  distrib_mul_action γ (Π₀ i, β i) :=
{ smul_zero := λ c, ext $ λ i, by simp only [smul_apply, smul_zero, zero_apply],
  smul_add := λ c x y, ext $ λ i, by simp only [add_apply, smul_apply, smul_add],
  one_smul := λ x, ext $ λ i, by simp only [smul_apply, one_smul],
  mul_smul := λ r s x, ext $ λ i, by simp only [smul_apply, smul_smul],
  ..dfinsupp.has_scalar }

/-- Dependent functions with finite support inherit a module structure from such a structure on
each coordinate. -/
instance [semiring γ] [Π i, add_comm_monoid (β i)] [Π i, module γ (β i)] :
  module γ (Π₀ i, β i) :=
{ zero_smul := λ c, ext $ λ i, by simp only [smul_apply, zero_smul, zero_apply],
  add_smul := λ c x y, ext $ λ i, by simp only [add_apply, smul_apply, add_smul],
  ..dfinsupp.distrib_mul_action }

end algebra

section filter_and_subtype_domain

/-- `filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
def filter [Π i, has_zero (β i)] (p : ι → Prop) [decidable_pred p] : (Π₀ i, β i) → Π₀ i, β i :=
quotient.map
  (λ x, ⟨λ i, if p i then x.1 i else 0, x.2, λ i, (x.3 i).imp_right $ λ H, by rw [H, if_t_t]⟩)
  (λ x y H i, by simp only [H i])

@[simp] lemma filter_apply [Π i, has_zero (β i)]
  (p : ι → Prop) [decidable_pred p] (i : ι) (f : Π₀ i, β i) :
  f.filter p i = if p i then f i else 0 :=
quotient.induction_on f $ λ x, rfl

lemma filter_apply_pos [Π i, has_zero (β i)]
  {p : ι → Prop} [decidable_pred p] (f : Π₀ i, β i) {i : ι} (h : p i) :
  f.filter p i = f i :=
by simp only [filter_apply, if_pos h]

lemma filter_apply_neg [Π i, has_zero (β i)]
  {p : ι → Prop} [decidable_pred p] (f : Π₀ i, β i) {i : ι} (h : ¬ p i) :
  f.filter p i = 0 :=
by simp only [filter_apply, if_neg h]

lemma filter_pos_add_filter_neg [Π i, add_zero_class (β i)] (f : Π₀ i, β i)
  (p : ι → Prop) [decidable_pred p] :
  f.filter p + f.filter (λi, ¬ p i) = f :=
ext $ λ i, by simp only [add_apply, filter_apply]; split_ifs; simp only [add_zero, zero_add]

@[simp] lemma filter_zero [Π i, has_zero (β i)] (p : ι → Prop) [decidable_pred p] :
  (0 : Π₀ i, β i).filter p = 0 :=
by { ext, simp }

@[simp] lemma filter_add [Π i, add_zero_class (β i)] (p : ι → Prop) [decidable_pred p]
  (f g : Π₀ i, β i) :
  (f + g).filter p = f.filter p + g.filter p :=
by { ext, simp [ite_add_zero] }

@[simp] lemma filter_smul [monoid γ] [Π i, add_monoid (β i)] [Π i, distrib_mul_action γ (β i)]
  (p : ι → Prop) [decidable_pred p] (r : γ) (f : Π₀ i, β i) :
  (r • f).filter p = r • f.filter p :=
by { ext, simp [smul_ite] }

variables (γ β)

/-- `dfinsupp.filter` as an `add_monoid_hom`. -/
@[simps]
def filter_add_monoid_hom [Π i, add_zero_class (β i)] (p : ι → Prop) [decidable_pred p] :
  (Π₀ i, β i) →+ (Π₀ i, β i) :=
{ to_fun := filter p,
  map_zero' := filter_zero p,
  map_add' := filter_add p }

/-- `dfinsupp.filter` as a `linear_map`. -/
@[simps]
def filter_linear_map [semiring γ] [Π i, add_comm_monoid (β i)] [Π i, module γ (β i)]
  (p : ι → Prop) [decidable_pred p] :
  (Π₀ i, β i) →ₗ[γ] (Π₀ i, β i) :=
{ to_fun := filter p,
  map_add' := filter_add p,
  map_smul' := filter_smul p }

variables {γ β}

@[simp] lemma filter_neg [Π i, add_group (β i)] (p : ι → Prop) [decidable_pred p]
  (f : Π₀ i, β i) :
  (-f).filter p = -f.filter p :=
(filter_add_monoid_hom β p).map_neg f

@[simp] lemma filter_sub [Π i, add_group (β i)] (p : ι → Prop) [decidable_pred p]
  (f g : Π₀ i, β i) :
  (f - g).filter p = f.filter p - g.filter p :=
(filter_add_monoid_hom β p).map_sub f g

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtype_domain [Π i, has_zero (β i)] (p : ι → Prop) [decidable_pred p] :
  (Π₀ i, β i) → Π₀ i : subtype p, β i :=
quotient.map
  (λ x, ⟨λ i, x.1 (i : ι), (x.2.filter p).attach.map $ λ j, ⟨j, (multiset.mem_filter.1 j.2).2⟩,
      λ i, (x.3 i).imp_left $ λ H, multiset.mem_map.2
        ⟨⟨i, multiset.mem_filter.2 ⟨H, i.2⟩⟩, multiset.mem_attach _ _, subtype.eta _ _⟩⟩)
  (λ x y H i, H i)

@[simp] lemma subtype_domain_zero [Π i, has_zero (β i)] {p : ι → Prop} [decidable_pred p] :
  subtype_domain p (0 : Π₀ i, β i) = 0 :=
rfl

@[simp] lemma subtype_domain_apply [Π i, has_zero (β i)] {p : ι → Prop} [decidable_pred p]
  {i : subtype p} {v : Π₀ i, β i} :
  (subtype_domain p v) i = v i :=
quotient.induction_on v $ λ x, rfl

@[simp] lemma subtype_domain_add [Π i, add_zero_class (β i)] {p : ι → Prop} [decidable_pred p]
  (v v' : Π₀ i, β i) :
  (v + v').subtype_domain p = v.subtype_domain p + v'.subtype_domain p :=
ext $ λ i, by simp only [add_apply, subtype_domain_apply]

@[simp] lemma subtype_domain_smul [monoid γ] [Π i, add_monoid (β i)]
  [Π i, distrib_mul_action γ (β i)] {p : ι → Prop} [decidable_pred p] (r : γ) (f : Π₀ i, β i) :
  (r • f).subtype_domain p = r • f.subtype_domain p :=
quotient.induction_on f $ λ x, rfl

variables (γ β)

/-- `subtype_domain` but as an `add_monoid_hom`. -/
@[simps] def subtype_domain_add_monoid_hom [Π i, add_zero_class (β i)]
  (p : ι → Prop) [decidable_pred p] : (Π₀ i : ι, β i) →+ Π₀ i : subtype p, β i :=
{ to_fun := subtype_domain p,
  map_zero' := subtype_domain_zero,
  map_add' := subtype_domain_add }

/-- `dfinsupp.subtype_domain` as a `linear_map`. -/
@[simps]
def subtype_domain_linear_map [semiring γ] [Π i, add_comm_monoid (β i)] [Π i, module γ (β i)]
  (p : ι → Prop) [decidable_pred p] :
  (Π₀ i, β i) →ₗ[γ] (Π₀ i : subtype p, β i) :=
{ to_fun := subtype_domain p,
  map_add' := subtype_domain_add,
  map_smul' := subtype_domain_smul }

variables {γ β}

@[simp]
lemma subtype_domain_neg [Π i, add_group (β i)] {p : ι → Prop} [decidable_pred p] {v : Π₀ i, β i} :
  (- v).subtype_domain p = - v.subtype_domain p :=
ext $ λ i, by simp only [neg_apply, subtype_domain_apply]

@[simp] lemma subtype_domain_sub [Π i, add_group (β i)] {p : ι → Prop} [decidable_pred p]
  {v v' : Π₀ i, β i} :
  (v - v').subtype_domain p = v.subtype_domain p - v'.subtype_domain p :=
ext $ λ i, by simp only [sub_apply, subtype_domain_apply]

end filter_and_subtype_domain


variable [dec : decidable_eq ι]
include dec

section basic
variable [Π i, has_zero (β i)]

omit dec
lemma finite_support (f : Π₀ i, β i) : set.finite {i | f i ≠ 0} :=
begin
  classical,
  exact quotient.induction_on f (λ x, x.2.to_finset.finite_to_set.subset (λ i H,
    multiset.mem_to_finset.2 ((x.3 i).resolve_right H)))
end
include dec

/-- Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `finset`. -/
def mk (s : finset ι) (x : Π i : (↑s : set ι), β (i : ι)) : Π₀ i, β i :=
⟦⟨λ i, if H : i ∈ s then x ⟨i, H⟩ else 0, s.1,
λ i, if H : i ∈ s then or.inl H else or.inr $ dif_neg H⟩⟧

@[simp] lemma mk_apply {s : finset ι} {x : Π i : (↑s : set ι), β i} {i : ι} :
  (mk s x : Π i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else 0 :=
rfl

theorem mk_injective (s : finset ι) : function.injective (@mk ι β _ _ s) :=
begin
  intros x y H,
  ext i,
  have h1 : (mk s x : Π i, β i) i = (mk s y : Π i, β i) i, {rw H},
  cases i with i hi,
  change i ∈ s at hi,
  dsimp only [mk_apply, subtype.coe_mk] at h1,
  simpa only [dif_pos hi] using h1
end

omit dec
/-- Given `fintype ι`, `equiv_fun_on_fintype` is the `equiv` between `Π₀ i, β i` and `Π i, β i`.
  (All dependent functions on a finite type are finitely supported.) -/
@[simps apply] def equiv_fun_on_fintype [fintype ι] : (Π₀ i, β i) ≃ (Π i, β i) :=
{ to_fun := coe_fn,
  inv_fun := λ f, ⟦⟨f, finset.univ.1, λ i, or.inl $ finset.mem_univ_val _⟩⟧,
  left_inv := λ x, coe_fn_injective rfl,
  right_inv := λ x, rfl }

@[simp] lemma equiv_fun_on_fintype_symm_coe [fintype ι] (f : Π₀ i, β i) :
  equiv_fun_on_fintype.symm f = f :=
equiv.symm_apply_apply _ _
include dec

/-- The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`. -/
def single (i : ι) (b : β i) : Π₀ i, β i :=
mk {i} $ λ j, eq.rec_on (finset.mem_singleton.1 j.prop).symm b

@[simp] lemma single_apply {i i' b} :
  (single i b : Π₀ i, β i) i' = (if h : i = i' then eq.rec_on h b else 0) :=
begin
  dsimp only [single],
  by_cases h : i = i',
  { have h1 : i' ∈ ({i} : finset ι) := finset.mem_singleton.2 h.symm,
    simp only [mk_apply, dif_pos h, dif_pos h1], refl },
  { have h1 : i' ∉ ({i} : finset ι) := finset.not_mem_singleton.2 (ne.symm h),
    simp only [mk_apply, dif_neg h, dif_neg h1] }
end

lemma single_eq_pi_single {i b} : ⇑(single i b : Π₀ i, β i) = pi.single i b :=
begin
  ext i',
  simp only [pi.single, function.update],
  split_ifs,
  { simp [h] },
  { simp [ne.symm h] }
end

@[simp] lemma single_zero (i) : (single i 0 : Π₀ i, β i) = 0 :=
quotient.sound $ λ j, if H : j ∈ ({i} : finset _)
then by dsimp only; rw [dif_pos H]; cases finset.mem_singleton.1 H; refl
else dif_neg H

@[simp] lemma single_eq_same {i b} : (single i b : Π₀ i, β i) i = b :=
by simp only [single_apply, dif_pos rfl]

lemma single_eq_of_ne {i i' b} (h : i ≠ i') : (single i b : Π₀ i, β i) i' = 0 :=
by simp only [single_apply, dif_neg h]

lemma single_injective {i} : function.injective (single i : β i → Π₀ i, β i) :=
λ x y H, congr_fun (mk_injective _ H) ⟨i, by simp⟩

/-- Like `finsupp.single_eq_single_iff`, but with a `heq` due to dependent types -/
lemma single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
  dfinsupp.single i xi = dfinsupp.single j xj ↔ i = j ∧ xi == xj ∨ xi = 0 ∧ xj = 0 :=
begin
  split,
  { intro h,
    by_cases hij : i = j,
    { subst hij,
      exact or.inl ⟨rfl, heq_of_eq (dfinsupp.single_injective h)⟩, },
    { have h_coe : ⇑(dfinsupp.single i xi) = dfinsupp.single j xj := congr_arg coe_fn h,
      have hci := congr_fun h_coe i,
      have hcj := congr_fun h_coe j,
      rw dfinsupp.single_eq_same at hci hcj,
      rw dfinsupp.single_eq_of_ne (ne.symm hij) at hci,
      rw dfinsupp.single_eq_of_ne (hij) at hcj,
      exact or.inr ⟨hci, hcj.symm⟩, }, },
  { rintros (⟨hi, hxi⟩ | ⟨hi, hj⟩),
    { subst hi,
      rw eq_of_heq hxi, },
    { rw [hi, hj, dfinsupp.single_zero, dfinsupp.single_zero], }, },
end

@[simp] lemma single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0 :=
begin
  rw [←single_zero i, single_eq_single_iff],
  simp,
end

lemma filter_single (p : ι → Prop) [decidable_pred p] (i : ι) (x : β i) :
  (single i x).filter p = if p i then single i x else 0 :=
begin
  ext j,
  have := apply_ite (λ x : Π₀ i, β i, x j) (p i) (single i x) 0,
  dsimp at this,
  rw [filter_apply, this],
  obtain rfl | hij := decidable.eq_or_ne i j,
  { refl, },
  { rw [single_eq_of_ne hij, if_t_t, if_t_t], },
end

@[simp] lemma filter_single_pos {p : ι → Prop} [decidable_pred p] (i : ι) (x : β i) (h : p i) :
  (single i x).filter p = single i x :=
by rw [filter_single, if_pos h]

@[simp] lemma filter_single_neg {p : ι → Prop} [decidable_pred p] (i : ι) (x : β i) (h : ¬p i) :
  (single i x).filter p = 0 :=
by rw [filter_single, if_neg h]

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `dfinsupp`s. -/
lemma single_eq_of_sigma_eq
  {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : sigma β) = ⟨j, xj⟩) :
  dfinsupp.single i xi = dfinsupp.single j xj :=
by { cases h, refl }

@[simp] lemma equiv_fun_on_fintype_single [fintype ι] (i : ι) (m : β i) :
  (@dfinsupp.equiv_fun_on_fintype ι β _ _) (dfinsupp.single i m) = pi.single i m :=
by { ext, simp [dfinsupp.single_eq_pi_single], }

@[simp] lemma equiv_fun_on_fintype_symm_single [fintype ι] (i : ι) (m : β i) :
  (@dfinsupp.equiv_fun_on_fintype ι β _ _).symm (pi.single i m) = dfinsupp.single i m :=
by { ext i', simp only [← single_eq_pi_single, equiv_fun_on_fintype_symm_coe] }

/-- Redefine `f i` to be `0`. -/
def erase (i : ι) : (Π₀ i, β i) → Π₀ i, β i :=
quotient.map
  (λ x, ⟨λ j, if j = i then 0 else x.1 j, x.2,
          λ j, (x.3 j).imp_right $ λ H, by simp only [H, if_t_t]⟩)
  (λ x y H j, if h : j = i then by simp only [if_pos h] else by simp only [if_neg h, H j])

@[simp] lemma erase_apply {i j : ι} {f : Π₀ i, β i} :
  (f.erase i) j = if j = i then 0 else f j :=
quotient.induction_on f $ λ x, rfl

@[simp] lemma erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0 :=
by simp

lemma erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' ≠ i) : (f.erase i) i' = f i' :=
by simp [h]

lemma erase_eq_sub_single {β : ι → Type*} [Π i, add_group (β i)] (f : Π₀ i, β i) (i : ι) :
  f.erase i = f - single i (f i) :=
begin
  ext j,
  rcases eq_or_ne i j with rfl|h,
  { simp },
  { simp [erase_ne h.symm, single_eq_of_ne h] }
end

@[simp] lemma erase_zero (i : ι) : erase i (0 : Π₀ i, β i) = 0 :=
ext $ λ _, if_t_t _ _

@[simp] lemma filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) : f.filter (≠ i) = f.erase i :=
begin
  ext1 j,
  simp only [dfinsupp.filter_apply, dfinsupp.erase_apply, ite_not],
end

@[simp] lemma filter_ne_eq_erase' (f : Π₀ i, β i) (i : ι) : f.filter ((≠) i) = f.erase i :=
begin
  rw ←filter_ne_eq_erase f i,
  congr' with j,
  exact ne_comm,
end

lemma erase_single (j : ι) (i : ι) (x : β i) :
  (single i x).erase j = if i = j then 0 else single i x :=
by rw [←filter_ne_eq_erase, filter_single, ite_not]

@[simp] lemma erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0 :=
by rw [erase_single, if_pos rfl]

@[simp] lemma erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) : (single i x).erase j = single i x :=
by rw [erase_single, if_neg h]

section update

variables (f : Π₀ i, β i) (i : ι) (b : β i) [decidable (b = 0)]

/-- Replace the value of a `Π₀ i, β i` at a given point `i : ι` by a given value `b : β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `function.update`. -/
def update : Π₀ i, β i :=
quotient.map (λ (x : pre _ _), ⟨function.update x.to_fun i b,
  if b = 0 then x.pre_support.erase i else i ::ₘ x.pre_support,
  begin
    intro j,
    rcases eq_or_ne i j with rfl|hi,
    { split_ifs with hb,
      { simp [hb] },
      { simp } },
    { cases x.zero j with hj hj,
      { split_ifs;
        simp [multiset.mem_erase_of_ne hi.symm, hj] },
      { simp [function.update_noteq hi.symm, hj] } }
  end⟩)
  (λ x y h j,
    show function.update x.to_fun i b j = function.update y.to_fun i b j,
    by rw (funext h : x.to_fun = y.to_fun)) f

variables (j : ι)

@[simp] lemma coe_update : (f.update i b : Π (i : ι), β i) = function.update f i b :=
quotient.induction_on f (λ _, rfl)
@[simp] lemma update_self [decidable (f i = 0)] : f.update i (f i) = f :=
by { ext, simp }

@[simp] lemma update_eq_erase [decidable ((0 : β i) = 0)] : f.update i 0 = f.erase i :=
begin
  ext j,
  rcases eq_or_ne i j with rfl|hi,
  { simp },
  { simp [hi.symm] }
end

lemma update_eq_single_add_erase {β : ι → Type*} [Π i, add_zero_class (β i)] (f : Π₀ i, β i) (i : ι)
  (b : β i) [decidable (b = 0)] :
  f.update i b = single i b + f.erase i :=
begin
  ext j,
  rcases eq_or_ne i j with rfl|h,
  { simp },
  { simp [function.update_noteq h.symm, h, erase_ne, h.symm] }
end

lemma update_eq_erase_add_single {β : ι → Type*} [Π i, add_zero_class (β i)] (f : Π₀ i, β i) (i : ι)
  (b : β i) [decidable (b = 0)] :
  f.update i b = f.erase i + single i b :=
begin
  ext j,
  rcases eq_or_ne i j with rfl|h,
  { simp },
  { simp [function.update_noteq h.symm, h, erase_ne, h.symm] }
end

lemma update_eq_sub_add_single {β : ι → Type*} [Π i, add_group (β i)] (f : Π₀ i, β i) (i : ι)
  (b : β i) [decidable (b = 0)] :
  f.update i b = f - single i (f i) + single i b :=
by rw [update_eq_erase_add_single f i b, erase_eq_sub_single f i]

end update

end basic

section add_monoid

variable [Π i, add_zero_class (β i)]

@[simp] lemma single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b₂) = single i b₁ + single i b₂ :=
ext $ assume i',
begin
  by_cases h : i = i',
  { subst h, simp only [add_apply, single_eq_same] },
  { simp only [add_apply, single_eq_of_ne h, zero_add] }
end

@[simp] lemma erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ + f₂) = erase i f₁ + erase i f₂ :=
ext $ λ _, by simp [ite_zero_add]

variables (β)

/-- `dfinsupp.single` as an `add_monoid_hom`. -/
@[simps] def single_add_hom (i : ι) : β i →+ Π₀ i, β i :=
{ to_fun := single i, map_zero' := single_zero i, map_add' := single_add i }

/-- `dfinsupp.erase` as an `add_monoid_hom`. -/
@[simps] def erase_add_hom (i : ι) : (Π₀ i, β i) →+ Π₀ i, β i :=
{ to_fun := erase i, map_zero' := erase_zero i, map_add' := erase_add i }

variables {β}

@[simp] lemma single_neg {β : ι → Type v} [Π i, add_group (β i)] (i : ι) (x : β i) :
  single i (-x) = -single i x :=
(single_add_hom β i).map_neg x

@[simp] lemma single_sub {β : ι → Type v} [Π i, add_group (β i)] (i : ι) (x y : β i) :
  single i (x - y) = single i x - single i y :=
(single_add_hom β i).map_sub x y

@[simp] lemma erase_neg {β : ι → Type v} [Π i, add_group (β i)] (i : ι) (f : Π₀ i, β i) :
  (-f).erase i = -f.erase i :=
(erase_add_hom β i).map_neg f

@[simp] lemma erase_sub {β : ι → Type v} [Π i, add_group (β i)] (i : ι) (f g : Π₀ i, β i) :
  (f - g).erase i = f.erase i - g.erase i :=
(erase_add_hom β i).map_sub f g

lemma single_add_erase (i : ι) (f : Π₀ i, β i) : single i (f i) + f.erase i = f :=
ext $ λ i',
if h : i = i'
then by subst h; simp only [add_apply, single_apply, erase_apply, dif_pos rfl, if_pos, add_zero]
else by simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (ne.symm h), zero_add]

lemma erase_add_single (i : ι) (f : Π₀ i, β i) : f.erase i + single i (f i) = f :=
ext $ λ i',
if h : i = i'
then by subst h; simp only [add_apply, single_apply, erase_apply, dif_pos rfl, if_pos, zero_add]
else by simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (ne.symm h), add_zero]

protected theorem induction {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i)
  (h0 : p 0) (ha : ∀i b (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (single i b + f)) :
  p f :=
begin
  refine quotient.induction_on f (λ x, _),
  cases x with f s H, revert f H,
  apply multiset.induction_on s,
  { intros f H, convert h0, ext i, exact (H i).resolve_left id },
  intros i s ih f H,
  by_cases H1 : i ∈ s,
  { have H2 : ∀ j, j ∈ s ∨ f j = 0,
    { intro j, cases H j with H2 H2,
      { cases multiset.mem_cons.1 H2 with H3 H3,
        { left, rw H3, exact H1 },
        { left, exact H3 } },
      right, exact H2 },
    have H3 : (⟦{to_fun := f, pre_support := i ::ₘ s, zero := H}⟧ : Π₀ i, β i)
      = ⟦{to_fun := f, pre_support := s, zero := H2}⟧,
    { exact quotient.sound (λ i, rfl) },
    rw H3, apply ih },
  have H2 : p (erase i ⟦{to_fun := f, pre_support := i ::ₘ s, zero := H}⟧),
  { dsimp only [erase, quotient.map_mk],
    have H2 : ∀ j, j ∈ s ∨ ite (j = i) 0 (f j) = 0,
    { intro j, cases H j with H2 H2,
      { cases multiset.mem_cons.1 H2 with H3 H3,
        { right, exact if_pos H3 },
        { left, exact H3 } },
      right, split_ifs; [refl, exact H2] },
    have H3 : (⟦{to_fun := λ (j : ι), ite (j = i) 0 (f j),
         pre_support := i ::ₘ s, zero := _}⟧ : Π₀ i, β i)
      = ⟦{to_fun := λ (j : ι), ite (j = i) 0 (f j), pre_support := s, zero := H2}⟧ :=
      quotient.sound (λ i, rfl),
    rw H3, apply ih },
  have H3 : single i _ + _ = (⟦{to_fun := f, pre_support := i ::ₘ s, zero := H}⟧ : Π₀ i, β i) :=
    single_add_erase _ _,
  rw ← H3,
  change p (single i (f i) + _),
  cases classical.em (f i = 0) with h h,
  { rw [h, single_zero, zero_add], exact H2 },
  refine ha _ _ _ _ h H2,
  rw erase_same
end

lemma induction₂ {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i)
  (h0 : p 0) (ha : ∀i b (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (f + single i b)) :
  p f :=
dfinsupp.induction f h0 $ λ i b f h1 h2 h3,
have h4 : f + single i b = single i b + f,
{ ext j, by_cases H : i = j,
  { subst H, simp [h1] },
  { simp [H] } },
eq.rec_on h4 $ ha i b f h1 h2 h3

@[simp] lemma add_closure_Union_range_single :
  add_submonoid.closure (⋃ i : ι, set.range (single i : β i → (Π₀ i, β i))) = ⊤ :=
top_unique $ λ x hx, (begin
  apply dfinsupp.induction x,
  exact add_submonoid.zero_mem _,
  exact λ a b f ha hb hf, add_submonoid.add_mem _
    (add_submonoid.subset_closure $ set.mem_Union.2 ⟨a, set.mem_range_self _⟩) hf
end)

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
lemma add_hom_ext {γ : Type w} [add_zero_class γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
  (H : ∀ (i : ι) (y : β i), f (single i y) = g (single i y)) :
  f = g :=
begin
  refine add_monoid_hom.eq_of_eq_on_mdense add_closure_Union_range_single (λ f hf, _),
  simp only [set.mem_Union, set.mem_range] at hf,
  rcases hf with ⟨x, y, rfl⟩,
  apply H
end

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext] lemma add_hom_ext' {γ : Type w} [add_zero_class γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
  (H : ∀ x, f.comp (single_add_hom β x) = g.comp (single_add_hom β x)) :
  f = g :=
add_hom_ext $ λ x, add_monoid_hom.congr_fun (H x)

end add_monoid

@[simp] lemma mk_add [Π i, add_zero_class (β i)] {s : finset ι} {x y : Π i : (↑s : set ι), β i} :
  mk s (x + y) = mk s x + mk s y :=
ext $ λ i, by simp only [add_apply, mk_apply]; split_ifs; [refl, rw zero_add]

@[simp] lemma mk_zero [Π i, has_zero (β i)] {s : finset ι} :
  mk s (0 : Π i : (↑s : set ι), β i.1) = 0 :=
ext $ λ i, by simp only [mk_apply]; split_ifs; refl

@[simp] lemma mk_neg [Π i, add_group (β i)] {s : finset ι} {x : Π i : (↑s : set ι), β i.1} :
  mk s (-x) = -mk s x :=
ext $ λ i, by simp only [neg_apply, mk_apply]; split_ifs; [refl, rw neg_zero]

@[simp] lemma mk_sub [Π i, add_group (β i)] {s : finset ι} {x y : Π i : (↑s : set ι), β i.1} :
  mk s (x - y) = mk s x - mk s y :=
ext $ λ i, by simp only [sub_apply, mk_apply]; split_ifs; [refl, rw sub_zero]

/-- If `s` is a subset of `ι` then `mk_add_group_hom s` is the canonical additive
group homomorphism from $\prod_{i\in s}\beta_i$ to $\prod_{\mathtt{i : \iota}}\beta_i.$-/
def mk_add_group_hom [Π i, add_group (β i)] (s : finset ι) :
  (Π (i : (s : set ι)), β ↑i) →+ (Π₀ (i : ι), β i) :=
{ to_fun := mk s,
  map_zero' := mk_zero,
  map_add' := λ _ _, mk_add }

section
variables [monoid γ] [Π i, add_monoid (β i)] [Π i, distrib_mul_action γ (β i)]

@[simp] lemma mk_smul {s : finset ι} (c : γ) (x : Π i : (↑s : set ι), β (i : ι)) :
  mk s (c • x) = c • mk s x :=
ext $ λ i, by simp only [smul_apply, mk_apply]; split_ifs; [refl, rw smul_zero]

@[simp] lemma single_smul {i : ι} (c : γ) (x : β i) :
  single i (c • x) = c • single i x :=
ext $ λ i, by simp only [smul_apply, single_apply]; split_ifs; [cases h, rw smul_zero]; refl

end

section support_basic

variables [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]

/-- Set `{i | f x ≠ 0}` as a `finset`. -/
def support (f : Π₀ i, β i) : finset ι :=
quotient.lift_on f (λ x, x.2.to_finset.filter $ λ i, x.1 i ≠ 0) $
begin
  intros x y Hxy,
  ext i, split,
  { intro H,
    rcases finset.mem_filter.1 H with ⟨h1, h2⟩,
    rw Hxy i at h2,
    exact finset.mem_filter.2 ⟨multiset.mem_to_finset.2 $ (y.3 i).resolve_right h2, h2⟩ },
  { intro H,
    rcases finset.mem_filter.1 H with ⟨h1, h2⟩,
    rw ← Hxy i at h2,
    exact finset.mem_filter.2 ⟨multiset.mem_to_finset.2 $ (x.3 i).resolve_right h2, h2⟩ },
end

@[simp] theorem support_mk_subset {s : finset ι} {x : Π i : (↑s : set ι), β i.1} :
  (mk s x).support ⊆ s :=
λ i H, multiset.mem_to_finset.1 (finset.mem_filter.1 H).1

@[simp] theorem mem_support_to_fun (f : Π₀ i, β i) (i) : i ∈ f.support ↔ f i ≠ 0 :=
begin
  refine quotient.induction_on f (λ x, _),
  dsimp only [support, quotient.lift_on_mk],
  rw [finset.mem_filter, multiset.mem_to_finset],
  exact and_iff_right_of_imp (x.3 i).resolve_right
end

theorem eq_mk_support (f : Π₀ i, β i) : f = mk f.support (λ i, f i) :=
begin
  change f = mk f.support (λ i, f i.1),
  ext i,
  by_cases h : f i ≠ 0; [skip, rw [not_not] at h];
    simp [h]
end

@[simp] lemma support_zero : (0 : Π₀ i, β i).support = ∅ := rfl

lemma mem_support_iff (f : Π₀ i, β i) : ∀i:ι, i ∈ f.support ↔ f i ≠ 0 :=
f.mem_support_to_fun

@[simp] lemma support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0 :=
⟨λ H, ext $ by simpa [finset.ext_iff] using H, by simp {contextual:=tt}⟩

instance decidable_zero : decidable_pred (eq (0 : Π₀ i, β i)) :=
λ f, decidable_of_iff _ $ support_eq_empty.trans eq_comm

lemma support_subset_iff {s : set ι} {f : Π₀ i, β i} :
  ↑f.support ⊆ s ↔ (∀i∉s, f i = 0) :=
by simp [set.subset_def];
   exact forall_congr (assume i, not_imp_comm)

lemma support_single_ne_zero {i : ι} {b : β i} (hb : b ≠ 0) : (single i b).support = {i} :=
begin
  ext j, by_cases h : i = j,
  { subst h, simp [hb] },
  simp [ne.symm h, h]
end

lemma support_single_subset {i : ι} {b : β i} : (single i b).support ⊆ {i} :=
support_mk_subset

section map_range_and_zip_with

variables [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]

lemma map_range_def [Π i (x : β₁ i), decidable (x ≠ 0)]
  {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
  map_range f hf g = mk g.support (λ i, f i.1 (g i.1)) :=
begin
  ext i,
  by_cases h : g i ≠ 0; simp at h; simp [h, hf]
end

@[simp] lemma map_range_single {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {i : ι} {b : β₁ i} :
  map_range f hf (single i b) = single i (f i b) :=
dfinsupp.ext $ λ i', by by_cases i = i'; [{subst i', simp}, simp [h, hf]]

variables [Π i (x : β₁ i), decidable (x ≠ 0)] [Π i (x : β₂ i), decidable (x ≠ 0)]

lemma support_map_range {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
  (map_range f hf g).support ⊆ g.support :=
by simp [map_range_def]

lemma zip_with_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
  [dec : decidable_eq ι] [Π (i : ι), has_zero (β i)] [Π (i : ι), has_zero (β₁ i)]
  [Π (i : ι), has_zero (β₂ i)] [Π (i : ι) (x : β₁ i), decidable (x ≠ 0)]
  [Π (i : ι) (x : β₂ i), decidable (x ≠ 0)]
  {f : Π i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0}
  {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
  zip_with f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) (λ i, f i.1 (g₁ i.1) (g₂ i.1)) :=
begin
  ext i,
  by_cases h1 : g₁ i ≠ 0; by_cases h2 : g₂ i ≠ 0;
    simp only [not_not, ne.def] at h1 h2; simp [h1, h2, hf]
end

lemma support_zip_with {f : Π i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0}
  {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
  (zip_with f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support :=
by simp [zip_with_def]

end map_range_and_zip_with

lemma erase_def (i : ι) (f : Π₀ i, β i) :
  f.erase i = mk (f.support.erase i) (λ j, f j.1) :=
by { ext j, by_cases h1 : j = i; by_cases h2 : f j ≠ 0; simp at h2; simp [h1, h2] }

@[simp] lemma support_erase (i : ι) (f : Π₀ i, β i) :
  (f.erase i).support = f.support.erase i :=
by { ext j, by_cases h1 : j = i; by_cases h2 : f j ≠ 0; simp at h2; simp [h1, h2] }

lemma support_update_ne_zero (f : Π₀ i, β i) (i : ι) {b : β i} [decidable (b = 0)] (h : b ≠ 0) :
  support (f.update i b) = insert i f.support :=
begin
  ext j,
  rcases eq_or_ne i j with rfl|hi,
  { simp [h] },
  { simp [hi.symm] }
end

lemma support_update (f : Π₀ i, β i) (i : ι) (b : β i) [decidable (b = 0)] :
  support (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support :=
begin
  ext j,
  split_ifs with hb,
  { simp only [hb, update_eq_erase, support_erase] },
  { rw [support_update_ne_zero f _ hb] }
end

section filter_and_subtype_domain

variables {p : ι → Prop} [decidable_pred p]

lemma filter_def (f : Π₀ i, β i) :
  f.filter p = mk (f.support.filter p) (λ i, f i.1) :=
by ext i; by_cases h1 : p i; by_cases h2 : f i ≠ 0;
 simp at h2; simp [h1, h2]

@[simp] lemma support_filter (f : Π₀ i, β i) :
  (f.filter p).support = f.support.filter p :=
by ext i; by_cases h : p i; simp [h]

lemma subtype_domain_def (f : Π₀ i, β i) :
  f.subtype_domain p = mk (f.support.subtype p) (λ i, f i) :=
by ext i; by_cases h1 : p i; by_cases h2 : f i ≠ 0;
try {simp at h2}; dsimp; simp [h1, h2, ← subtype.val_eq_coe]

@[simp] lemma support_subtype_domain {f : Π₀ i, β i} :
  (subtype_domain p f).support = f.support.subtype p :=
by ext i; by_cases h1 : p i; by_cases h2 : f i ≠ 0;
try {simp at h2}; dsimp; simp [h1, h2]

end filter_and_subtype_domain

end support_basic

lemma support_add [Π i, add_zero_class (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  {g₁ g₂ : Π₀ i, β i} :
  (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
support_zip_with

@[simp] lemma support_neg [Π i, add_group (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  {f : Π₀ i, β i} :
  support (-f) = support f :=
by ext i; simp

lemma support_smul {γ : Type w} [semiring γ] [Π i, add_comm_monoid (β i)] [Π i, module γ (β i)]
  [Π ( i : ι) (x : β i), decidable (x ≠ 0)]
  (b : γ) (v : Π₀ i, β i) : (b • v).support ⊆ v.support :=
support_map_range

instance [Π i, has_zero (β i)] [Π i, decidable_eq (β i)] : decidable_eq (Π₀ i, β i) :=
assume f g, decidable_of_iff (f.support = g.support ∧ (∀i∈f.support, f i = g i))
  ⟨assume ⟨h₁, h₂⟩, ext $ assume i,
      if h : i ∈ f.support then h₂ i h else
        have hf : f i = 0, by rwa [f.mem_support_iff, not_not] at h,
        have hg : g i = 0, by rwa [h₁, g.mem_support_iff, not_not] at h,
        by rw [hf, hg],
    by intro h; subst h; simp⟩

section prod_and_sum

/-- `prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g i (f i)` over the support of `f`."]
def prod [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)] [comm_monoid γ]
  (f : Π₀ i, β i) (g : Π i, β i → γ) : γ :=
∏ i in f.support, g i (f i)

@[to_additive]
lemma prod_map_range_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
  [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]
  [Π i (x : β₁ i), decidable (x ≠ 0)] [Π i (x : β₂ i), decidable (x ≠ 0)] [comm_monoid γ]
  {f : Π i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : Π i, β₂ i → γ}
  (h0 : ∀i, h i 0 = 1) :
  (map_range f hf g).prod h = g.prod (λi b, h i (f i b)) :=
begin
  rw [map_range_def],
  refine (finset.prod_subset support_mk_subset _).trans _,
  { intros i h1 h2,
    dsimp, simp [h1] at h2, dsimp at h2,
    simp [h1, h2, h0] },
  { refine finset.prod_congr rfl _,
    intros i h1,
    simp [h1] }
end

@[to_additive]
lemma prod_zero_index [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {h : Π i, β i → γ} : (0 : Π₀ i, β i).prod h = 1 :=
rfl

@[to_additive]
lemma prod_single_index [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)] [comm_monoid γ]
  {i : ι} {b : β i} {h : Π i, β i → γ} (h_zero : h i 0 = 1) :
  (single i b).prod h = h i b :=
begin
  by_cases h : b ≠ 0,
  { simp [dfinsupp.prod, support_single_ne_zero h] },
  { rw [not_not] at h, simp [h, prod_zero_index, h_zero], refl }
end

@[to_additive]
lemma prod_neg_index [Π i, add_group (β i)] [Π i (x : β i), decidable (x ≠ 0)] [comm_monoid γ]
  {g : Π₀ i, β i} {h : Π i, β i → γ} (h0 : ∀i, h i 0 = 1) :
  (-g).prod h = g.prod (λi b, h i (- b)) :=
prod_map_range_index h0

omit dec
@[to_additive]
lemma prod_comm {ι₁ ι₂ : Sort*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*}
  [decidable_eq ι₁] [decidable_eq ι₂] [Π i, has_zero (β₁ i)] [Π i, has_zero (β₂ i)]
  [Π i (x : β₁ i), decidable (x ≠ 0)] [Π i (x : β₂ i), decidable (x ≠ 0)] [comm_monoid γ]
  (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : Π i, β₁ i → Π i, β₂ i → γ) :
  f₁.prod (λ i₁ x₁, f₂.prod $ λ i₂ x₂, h i₁ x₁ i₂ x₂) =
  f₂.prod (λ i₂ x₂, f₁.prod $ λ i₁ x₁, h i₁ x₁ i₂ x₂) := finset.prod_comm

@[simp] lemma sum_apply {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i (x : β₁ i), decidable (x ≠ 0)]
  [Π i, add_comm_monoid (β i)]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i} {i₂ : ι} :
  (f.sum g) i₂ = f.sum (λi₁ b, g i₁ b i₂) :=
(eval_add_monoid_hom i₂ : (Π₀ i, β i) →+ β i₂).map_sum  _ f.support

include dec

lemma support_sum {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i (x : β₁ i), decidable (x ≠ 0)]
  [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i} :
  (f.sum g).support ⊆ f.support.bUnion (λi, (g i (f i)).support) :=
have ∀i₁ : ι, f.sum (λ (i : ι₁) (b : β₁ i), (g i b) i₁) ≠ 0 →
    (∃ (i : ι₁), f i ≠ 0 ∧ ¬ (g i (f i)) i₁ = 0),
  from assume i₁ h,
  let ⟨i, hi, ne⟩ := finset.exists_ne_zero_of_sum_ne_zero h in
  ⟨i, (f.mem_support_iff i).mp hi, ne⟩,
by simpa [finset.subset_iff, mem_support_iff, finset.mem_bUnion, sum_apply] using this

@[simp, to_additive] lemma prod_one [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {f : Π₀ i, β i} :
  f.prod (λi b, (1 : γ)) = 1 :=
finset.prod_const_one

@[simp, to_additive] lemma prod_mul [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {f : Π₀ i, β i} {h₁ h₂ : Π i, β i → γ} :
  f.prod (λi b, h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
finset.prod_mul_distrib

@[simp, to_additive] lemma prod_inv [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_group γ] {f : Π₀ i, β i} {h : Π i, β i → γ} :
  f.prod (λi b, (h i b)⁻¹) = (f.prod h)⁻¹ :=
((comm_group.inv_monoid_hom : γ →* γ).map_prod _ f.support).symm

@[to_additive]
lemma prod_add_index [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {f g : Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
  (f + g).prod h = f.prod h * g.prod h :=
have f_eq : ∏ i in f.support ∪ g.support, h i (f i) = f.prod h,
  from (finset.prod_subset (finset.subset_union_left _ _) $
    by simp [mem_support_iff, h_zero] {contextual := tt}).symm,
have g_eq : ∏ i in f.support ∪ g.support, h i (g i) = g.prod h,
  from (finset.prod_subset (finset.subset_union_right _ _) $
    by simp [mem_support_iff, h_zero] {contextual := tt}).symm,
calc ∏ i in (f + g).support, h i ((f + g) i) =
      ∏ i in f.support ∪ g.support, h i ((f + g) i) :
    finset.prod_subset support_add $
      by simp [mem_support_iff, h_zero] {contextual := tt}
  ... = (∏ i in f.support ∪ g.support, h i (f i)) *
      (∏ i in f.support ∪ g.support, h i (g i)) :
    by simp [h_add, finset.prod_mul_distrib]
  ... = _ : by rw [f_eq, g_eq]

@[to_additive]
lemma _root_.submonoid.dfinsupp_prod_mem [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] (S : submonoid γ)
  (f : Π₀ i, β i) (g : Π i, β i → γ) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.prod g ∈ S :=
S.prod_mem $ λ i hi, h _ $ (f.mem_support_iff _).mp hi

/--
When summing over an `add_monoid_hom`, the decidability assumption is not needed, and the result is
also an `add_monoid_hom`.
-/
def sum_add_hom [Π i, add_zero_class (β i)] [add_comm_monoid γ] (φ : Π i, β i →+ γ) :
  (Π₀ i, β i) →+ γ :=
{ to_fun := (λ f,
    quotient.lift_on f (λ x, ∑ i in x.2.to_finset, φ i (x.1 i)) $ λ x y H,
    begin
      have H1 : x.2.to_finset ∩ y.2.to_finset ⊆ x.2.to_finset, from finset.inter_subset_left _ _,
      have H2 : x.2.to_finset ∩ y.2.to_finset ⊆ y.2.to_finset, from finset.inter_subset_right _ _,
      refine (finset.sum_subset H1 _).symm.trans
          ((finset.sum_congr rfl _).trans (finset.sum_subset H2 _)),
      { intros i H1 H2, rw finset.mem_inter at H2, rw H i,
        simp only [multiset.mem_to_finset] at H1 H2,
        rw [(y.3 i).resolve_left (mt (and.intro H1) H2), add_monoid_hom.map_zero] },
      { intros i H1, rw H i },
      { intros i H1 H2, rw finset.mem_inter at H2, rw ← H i,
        simp only [multiset.mem_to_finset] at H1 H2,
        rw [(x.3 i).resolve_left (mt (λ H3, and.intro H3 H1) H2), add_monoid_hom.map_zero] }
    end),
  map_add' := assume f g,
  begin
    refine quotient.induction_on f (λ x, _),
    refine quotient.induction_on g (λ y, _),
    change ∑ i in _, _ = (∑ i in _, _) + (∑ i in _, _),
    simp only, conv { to_lhs, congr, skip, funext, rw add_monoid_hom.map_add },
    simp only [finset.sum_add_distrib],
    congr' 1,
    { refine (finset.sum_subset _ _).symm,
      { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inl },
      { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
        rw [(x.3 i).resolve_left H2, add_monoid_hom.map_zero] } },
    { refine (finset.sum_subset _ _).symm,
      { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inr },
      { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
        rw [(y.3 i).resolve_left H2, add_monoid_hom.map_zero] } }
  end,
  map_zero' := rfl }

@[simp] lemma sum_add_hom_single [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (φ : Π i, β i →+ γ) (i) (x : β i) : sum_add_hom φ (single i x) = φ i x :=
(add_zero _).trans $ congr_arg (φ i) $ show (if H : i ∈ ({i} : finset _) then x else 0) = x,
from dif_pos $ finset.mem_singleton_self i

@[simp] lemma sum_add_hom_comp_single [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (f : Π i, β i →+ γ) (i : ι) :
  (sum_add_hom f).comp (single_add_hom β i) = f i :=
add_monoid_hom.ext $ λ x, sum_add_hom_single f i x

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
lemma sum_add_hom_apply [Π i, add_zero_class (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [add_comm_monoid γ] (φ : Π i, β i →+ γ) (f : Π₀ i, β i) :
  sum_add_hom φ f = f.sum (λ x, φ x) :=
begin
  refine quotient.induction_on f (λ x, _),
  change ∑ i in _, _ = (∑ i in finset.filter _ _, _),
  rw [finset.sum_filter, finset.sum_congr rfl],
  intros i _,
  dsimp only,
  split_ifs,
  refl,
  rw [(not_not.mp h), add_monoid_hom.map_zero],
end

lemma _root_.add_submonoid.dfinsupp_sum_add_hom_mem [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (S : add_submonoid γ) (f : Π₀ i, β i) (g : Π i, β i →+ γ) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
  dfinsupp.sum_add_hom g f ∈ S :=
begin
  classical,
  rw dfinsupp.sum_add_hom_apply,
  convert S.dfinsupp_sum_mem _ _ _,
  exact h
end

/-- The supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom`; that is, every element in the `supr` can be produced from taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them. -/
lemma _root_.add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom [add_comm_monoid γ]
  (S : ι → add_submonoid γ) : supr S = (dfinsupp.sum_add_hom (λ i, (S i).subtype)).mrange :=
begin
  apply le_antisymm,
  { apply supr_le _,
    intros i y hy,
    exact ⟨dfinsupp.single i ⟨y, hy⟩, dfinsupp.sum_add_hom_single _ _ _⟩, },
  { rintros x ⟨v, rfl⟩,
    exact add_submonoid.dfinsupp_sum_add_hom_mem _ v _ (λ i _, (le_supr S i : S i ≤ _) (v i).prop) }
end

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom` composed with `dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `supr` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
lemma _root_.add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom (p : ι → Prop)
  [decidable_pred p] [add_comm_monoid γ] (S : ι → add_submonoid γ) :
  (⨆ i (h : p i), S i) =
    ((sum_add_hom (λ i, (S i).subtype)).comp (filter_add_monoid_hom _ p)).mrange :=
begin
  apply le_antisymm,
  { apply bsupr_le _,
    intros i hi y hy,
    refine ⟨dfinsupp.single i ⟨y, hy⟩, _⟩,
    rw [add_monoid_hom.comp_apply, filter_add_monoid_hom_apply, filter_single_pos _ _ hi],
    exact sum_add_hom_single _ _ _, },
  { rintros x ⟨v, rfl⟩,
    refine add_submonoid.dfinsupp_sum_add_hom_mem _ _ _ (λ i hi, _),
    refine add_submonoid.mem_supr_of_mem i _,
    by_cases hp : p i,
    { simp [hp], },
    { simp [hp] }, }
end

lemma _root_.add_submonoid.mem_supr_iff_exists_dfinsupp [add_comm_monoid γ]
  (S : ι → add_submonoid γ) (x : γ) :
  x ∈ supr S ↔ ∃ f : Π₀ i, S i, dfinsupp.sum_add_hom (λ i, (S i).subtype) f = x :=
set_like.ext_iff.mp (add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom S) x

/-- A variant of `add_submonoid.mem_supr_iff_exists_dfinsupp` with the RHS fully unfolded. -/
lemma _root_.add_submonoid.mem_supr_iff_exists_dfinsupp' [add_comm_monoid γ]
  (S : ι → add_submonoid γ) [Π i (x : S i), decidable (x ≠ 0)] (x : γ) :
  x ∈ supr S ↔ ∃ f : Π₀ i, S i, f.sum (λ i xi, ↑xi) = x :=
begin
  rw add_submonoid.mem_supr_iff_exists_dfinsupp,
  simp_rw sum_add_hom_apply,
  congr',
end

lemma _root_.add_submonoid.mem_bsupr_iff_exists_dfinsupp (p : ι → Prop)
  [decidable_pred p] [add_comm_monoid γ] (S : ι → add_submonoid γ) (x : γ) :
  x ∈ (⨆ i (h : p i), S i) ↔
    ∃ f : Π₀ i, S i, dfinsupp.sum_add_hom (λ i, (S i).subtype) (f.filter p) = x :=
set_like.ext_iff.mp (add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom p S) x

omit dec
lemma sum_add_hom_comm {ι₁ ι₂ : Sort*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} {γ : Type*}
  [decidable_eq ι₁] [decidable_eq ι₂] [Π i, add_zero_class (β₁ i)] [Π i, add_zero_class (β₂ i)]
  [add_comm_monoid γ]
  (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : Π i j, β₁ i →+ β₂ j →+ γ) :
  sum_add_hom (λ i₂, sum_add_hom (λ i₁, h i₁ i₂) f₁) f₂ =
  sum_add_hom (λ i₁, sum_add_hom (λ i₂, (h i₁ i₂).flip) f₂) f₁ :=
begin
  refine quotient.induction_on₂ f₁ f₂ (λ x₁ x₂, _),
  simp only [sum_add_hom, add_monoid_hom.finset_sum_apply, quotient.lift_on_mk,
    add_monoid_hom.coe_mk, add_monoid_hom.flip_apply],
  exact finset.sum_comm,
end

include dec
/-- The `dfinsupp` version of `finsupp.lift_add_hom`,-/
@[simps apply symm_apply]
def lift_add_hom [Π i, add_zero_class (β i)] [add_comm_monoid γ] :
  (Π i, β i →+ γ) ≃+ ((Π₀ i, β i) →+ γ) :=
{ to_fun := sum_add_hom,
  inv_fun := λ F i, F.comp (single_add_hom β i),
  left_inv := λ x, by { ext, simp },
  right_inv := λ ψ, by { ext, simp },
  map_add' := λ F G, by { ext, simp } }

/-- The `dfinsupp` version of `finsupp.lift_add_hom_single_add_hom`,-/
@[simp] lemma lift_add_hom_single_add_hom [Π i, add_comm_monoid (β i)] :
  lift_add_hom (single_add_hom β) = add_monoid_hom.id (Π₀ i, β i) :=
lift_add_hom.to_equiv.apply_eq_iff_eq_symm_apply.2 rfl

/-- The `dfinsupp` version of `finsupp.lift_add_hom_apply_single`,-/
lemma lift_add_hom_apply_single [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (f : Π i, β i →+ γ) (i : ι) (x : β i) :
  lift_add_hom f (single i x) = f i x :=
by simp

/-- The `dfinsupp` version of `finsupp.lift_add_hom_comp_single`,-/
lemma lift_add_hom_comp_single [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (f : Π i, β i →+ γ) (i : ι) :
  (lift_add_hom f).comp (single_add_hom β i) = f i :=
by simp

/-- The `dfinsupp` version of `finsupp.comp_lift_add_hom`,-/
lemma comp_lift_add_hom {δ : Type*} [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  [add_comm_monoid δ] (g : γ →+ δ) (f : Π i, β i →+ γ) :
  g.comp (lift_add_hom f) = lift_add_hom (λ a, g.comp (f a)) :=
lift_add_hom.symm_apply_eq.1 $ funext $ λ a,
  by rw [lift_add_hom_symm_apply, add_monoid_hom.comp_assoc, lift_add_hom_comp_single]

@[simp]
lemma sum_add_hom_zero [Π i, add_zero_class (β i)] [add_comm_monoid γ] :
  sum_add_hom (λ i, (0 : β i →+ γ)) = 0 :=
(lift_add_hom : (Π i, β i →+ γ) ≃+ _).map_zero

@[simp]
lemma sum_add_hom_add [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  (g : Π i, β i →+ γ) (h : Π i, β i →+ γ) :
  sum_add_hom (λ i, g i + h i) = sum_add_hom g + sum_add_hom h :=
lift_add_hom.map_add _ _

@[simp]
lemma sum_add_hom_single_add_hom [Π i, add_comm_monoid (β i)] :
  sum_add_hom (single_add_hom β) = add_monoid_hom.id _ :=
lift_add_hom_single_add_hom

lemma comp_sum_add_hom {δ : Type*} [Π i, add_zero_class (β i)] [add_comm_monoid γ]
  [add_comm_monoid δ] (g : γ →+ δ) (f : Π i, β i →+ γ) :
  g.comp (sum_add_hom f) = sum_add_hom (λ a, g.comp (f a)) :=
comp_lift_add_hom _ _

lemma sum_sub_index [Π i, add_group (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [add_comm_group γ] {f g : Π₀ i, β i}
  {h : Π i, β i → γ} (h_sub : ∀i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) :
  (f - g).sum h = f.sum h - g.sum h :=
begin
  have := (lift_add_hom (λ a, add_monoid_hom.of_map_sub (h a) (h_sub a))).map_sub f g,
  rw [lift_add_hom_apply, sum_add_hom_apply, sum_add_hom_apply, sum_add_hom_apply] at this,
  exact this,
end

@[to_additive]
lemma prod_finset_sum_index {γ : Type w} {α : Type x}
  [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ]
  {s : finset α} {g : α → Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
  ∏ i in s, (g i).prod h = (∑ i in s, g i).prod h :=
begin
  classical,
  exact finset.induction_on s
  (by simp [prod_zero_index])
  (by simp [prod_add_index, h_zero, h_add] {contextual := tt})
end

@[to_additive]
lemma prod_sum_index {ι₁ : Type u₁} [decidable_eq ι₁] {β₁ : ι₁ → Type v₁}
  [Π i₁, has_zero (β₁ i₁)] [Π i (x : β₁ i), decidable (x ≠ 0)]
  [Π i, add_comm_monoid (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ]
  {f : Π₀ i₁, β₁ i₁} {g : Π i₁, β₁ i₁ → Π₀ i, β i}
  {h : Π i, β i → γ} (h_zero : ∀i, h i 0 = 1) (h_add : ∀i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
  (f.sum g).prod h = f.prod (λi b, (g i b).prod h) :=
(prod_finset_sum_index h_zero h_add).symm

@[simp] lemma sum_single [Π i, add_comm_monoid (β i)]
  [Π i (x : β i), decidable (x ≠ 0)] {f : Π₀ i, β i} :
  f.sum single = f :=
begin
  have := add_monoid_hom.congr_fun lift_add_hom_single_add_hom f,
  rw [lift_add_hom_apply, sum_add_hom_apply] at this,
  exact this,
end

@[to_additive]
lemma prod_subtype_domain_index [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]
  [comm_monoid γ] {v : Π₀ i, β i} {p : ι → Prop} [decidable_pred p]
  {h : Π i, β i → γ} (hp : ∀ x ∈ v.support, p x) :
  (v.subtype_domain p).prod (λi b, h i b) = v.prod h :=
finset.prod_bij (λp _, p)
  (by simp) (by simp)
  (assume ⟨a₀, ha₀⟩ ⟨a₁, ha₁⟩, by simp)
  (λ i hi, ⟨⟨i, hp i hi⟩, by simpa using hi, rfl⟩)

omit dec
lemma subtype_domain_sum [Π i, add_comm_monoid (β i)]
  {s : finset γ} {h : γ → Π₀ i, β i} {p : ι → Prop} [decidable_pred p] :
  (∑ c in s, h c).subtype_domain p = ∑ c in s, (h c).subtype_domain p :=
(subtype_domain_add_monoid_hom β p).map_sum  _ s

lemma subtype_domain_finsupp_sum {δ : γ → Type x} [decidable_eq γ]
  [Π c, has_zero (δ c)] [Π c (x : δ c), decidable (x ≠ 0)]
  [Π i, add_comm_monoid (β i)]
  {p : ι → Prop} [decidable_pred p]
  {s : Π₀ c, δ c} {h : Π c, δ c → Π₀ i, β i} :
  (s.sum h).subtype_domain p = s.sum (λc d, (h c d).subtype_domain p) :=
subtype_domain_sum

end prod_and_sum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/

section map_range
omit dec

variables [Π i, add_zero_class (β i)] [Π i, add_zero_class (β₁ i)] [Π i, add_zero_class (β₂ i)]

lemma map_range_add (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0)
  (hf' : ∀ i x y, f i (x + y) = f i x + f i y) (g₁ g₂ : Π₀ i, β₁ i):
  map_range f hf (g₁ + g₂) = map_range f hf g₁ + map_range f hf g₂ :=
begin
  ext,
  simp only [map_range_apply f, coe_add, pi.add_apply, hf']
end

/-- `dfinsupp.map_range` as an `add_monoid_hom`. -/
@[simps apply]
def map_range.add_monoid_hom (f : Π i, β₁ i →+ β₂ i) : (Π₀ i, β₁ i) →+ (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, f i x) (λ i, (f i).map_zero),
  map_zero' := map_range_zero _ _,
  map_add' := map_range_add _ _ (λ i, (f i).map_add) }

@[simp]
lemma map_range.add_monoid_hom_id :
  map_range.add_monoid_hom (λ i, add_monoid_hom.id (β₂ i)) = add_monoid_hom.id _ :=
add_monoid_hom.ext map_range_id

lemma map_range.add_monoid_hom_comp (f : Π i, β₁ i →+ β₂ i) (f₂ : Π i, β i →+ β₁ i):
  map_range.add_monoid_hom (λ i, (f i).comp (f₂ i)) =
    (map_range.add_monoid_hom f).comp (map_range.add_monoid_hom f₂) :=
add_monoid_hom.ext $ map_range_comp (λ i x, f i x) (λ i x, f₂ i x) _ _ _

/-- `dfinsupp.map_range.add_monoid_hom` as an `add_equiv`. -/
@[simps apply]
def map_range.add_equiv (e : Π i, β₁ i ≃+ β₂ i) : (Π₀ i, β₁ i) ≃+ (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, e i x) (λ i, (e i).map_zero),
  inv_fun := map_range (λ i x, (e i).symm x) (λ i, (e i).symm.map_zero),
  left_inv := λ x, by rw ←map_range_comp; { simp_rw add_equiv.symm_comp_self, simp },
  right_inv := λ x, by rw ←map_range_comp; { simp_rw add_equiv.self_comp_symm, simp },
  .. map_range.add_monoid_hom (λ i, (e i).to_add_monoid_hom) }

@[simp]
lemma map_range.add_equiv_refl :
  (map_range.add_equiv $ λ i, add_equiv.refl (β₁ i)) = add_equiv.refl _ :=
add_equiv.ext map_range_id

lemma map_range.add_equiv_trans (f : Π i, β i ≃+ β₁ i) (f₂ : Π i, β₁ i ≃+ β₂ i):
  map_range.add_equiv (λ i, (f i).trans (f₂ i)) =
    (map_range.add_equiv f).trans (map_range.add_equiv f₂) :=
add_equiv.ext $ map_range_comp (λ i x, f₂ i x) (λ i x, f i x) _ _ _

@[simp]
lemma map_range.add_equiv_symm (e : Π i, β₁ i ≃+ β₂ i) :
  (map_range.add_equiv e).symm = map_range.add_equiv (λ i, (e i).symm) := rfl

end map_range

end dfinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `add_monoid_hom.map_sum`, `add_monoid_hom.coe_sum`, and
`add_monoid_hom.sum_apply` for `dfinsupp.sum` and `dfinsupp.sum_add_hom` instead of `finset.sum`.

We provide these for `add_monoid_hom`, `monoid_hom`, `ring_hom`, `add_equiv`, and `mul_equiv`.

Lemmas for `linear_map` and `linear_equiv` are in another file.
-/
section

variables [decidable_eq ι]

namespace monoid_hom
variables {R S : Type*}
variables [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]

@[simp, to_additive]
lemma map_dfinsupp_prod [comm_monoid R] [comm_monoid S]
  (h : R →* S) (f : Π₀ i, β i) (g : Π i, β i → R) :
  h (f.prod g) = f.prod (λ a b, h (g a b)) := h.map_prod _ _

@[to_additive]
lemma coe_dfinsupp_prod [monoid R] [comm_monoid S]
  (f : Π₀ i, β i) (g : Π i, β i → R →* S) :
  ⇑(f.prod g) = f.prod (λ a b, (g a b)) := coe_prod _ _

@[simp, to_additive]
lemma dfinsupp_prod_apply [monoid R] [comm_monoid S]
  (f : Π₀ i, β i) (g : Π i, β i → R →* S) (r : R) :
  (f.prod g) r = f.prod (λ a b, (g a b) r) := finset_prod_apply _ _ _

end monoid_hom

namespace ring_hom
variables {R S : Type*}
variables [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]

@[simp]
lemma map_dfinsupp_prod [comm_semiring R] [comm_semiring S]
  (h : R →+* S) (f : Π₀ i, β i) (g : Π i, β i → R) :
  h (f.prod g) = f.prod (λ a b, h (g a b)) := h.map_prod _ _

@[simp]
lemma map_dfinsupp_sum [non_assoc_semiring R] [non_assoc_semiring S]
  (h : R →+* S) (f : Π₀ i, β i) (g : Π i, β i → R) :
  h (f.sum g) = f.sum (λ a b, h (g a b)) := h.map_sum _ _

end ring_hom

namespace mul_equiv
variables {R S : Type*}
variables [Π i, has_zero (β i)] [Π i (x : β i), decidable (x ≠ 0)]

@[simp, to_additive]
lemma map_dfinsupp_prod [comm_monoid R] [comm_monoid S]
  (h : R ≃* S) (f : Π₀ i, β i) (g : Π i, β i → R) :
  h (f.prod g) = f.prod (λ a b, h (g a b)) := h.map_prod _ _

end mul_equiv

/-! The above lemmas, repeated for `dfinsupp.sum_add_hom`. -/

namespace add_monoid_hom
variables {R S : Type*}

open dfinsupp

@[simp]
lemma map_dfinsupp_sum_add_hom [add_comm_monoid R] [add_comm_monoid S] [Π i, add_zero_class (β i)]
  (h : R →+ S) (f : Π₀ i, β i) (g : Π i, β i →+ R) :
  h (sum_add_hom g f) = sum_add_hom (λ i, h.comp (g i)) f :=
congr_fun (comp_lift_add_hom h g) f

@[simp]
lemma dfinsupp_sum_add_hom_apply [add_zero_class R] [add_comm_monoid S] [Π i, add_zero_class (β i)]
  (f : Π₀ i, β i) (g : Π i, β i →+ R →+ S) (r : R) :
  (sum_add_hom g f) r = sum_add_hom (λ i, (eval r).comp (g i)) f :=
map_dfinsupp_sum_add_hom (eval r) f g

lemma coe_dfinsupp_sum_add_hom [add_zero_class R] [add_comm_monoid S] [Π i, add_zero_class (β i)]
  (f : Π₀ i, β i) (g : Π i, β i →+ R →+ S) :
  ⇑(sum_add_hom g f) = sum_add_hom (λ i, (coe_fn R S).comp (g i)) f :=
map_dfinsupp_sum_add_hom (coe_fn R S) f g

end add_monoid_hom

namespace ring_hom
variables {R S : Type*}

open dfinsupp

@[simp]
lemma map_dfinsupp_sum_add_hom [non_assoc_semiring R] [non_assoc_semiring S]
  [Π i, add_zero_class (β i)] (h : R →+* S) (f : Π₀ i, β i) (g : Π i, β i →+ R) :
  h (sum_add_hom g f) = sum_add_hom (λ i, h.to_add_monoid_hom.comp (g i)) f :=
add_monoid_hom.congr_fun (comp_lift_add_hom h.to_add_monoid_hom g) f

end ring_hom

namespace add_equiv
variables {R S : Type*}

open dfinsupp

@[simp]
lemma map_dfinsupp_sum_add_hom [add_comm_monoid R] [add_comm_monoid S] [Π i, add_zero_class (β i)]
  (h : R ≃+ S) (f : Π₀ i, β i) (g : Π i, β i →+ R) :
  h (sum_add_hom g f) = sum_add_hom (λ i, h.to_add_monoid_hom.comp (g i)) f :=
add_monoid_hom.congr_fun (comp_lift_add_hom h.to_add_monoid_hom g) f

end add_equiv

end
