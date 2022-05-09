/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
import algebra.group.opposite

/-!
# Monoid, group etc structures on `M × N`

In this file we define one-binop (`monoid`, `group` etc) structures on `M × N`. We also prove
trivial `simp` lemmas, and define the following operations on `monoid_hom`s:

* `fst M N : M × N →* M`, `snd M N : M × N →* N`: projections `prod.fst` and `prod.snd`
  as `monoid_hom`s;
* `inl M N : M →* M × N`, `inr M N : N →* M × N`: inclusions of first/second monoid
  into the product;
* `f.prod g : `M →* N × P`: sends `x` to `(f x, g x)`;
* `f.coprod g : M × N →* P`: sends `(x, y)` to `f x * g y`;
* `f.prod_map g : M × N → M' × N'`: `prod.map f g` as a `monoid_hom`,
  sends `(x, y)` to `(f x, g y)`.

## Main declarations

* `mul_mul_hom`/`mul_monoid_hom`/`mul_monoid_with_zero_hom`: Multiplication bundled as a
  multiplicative/monoid/monoid with zero homomorphism.
* `div_monoid_hom`/`div_monoid_with_zero_hom`: Division bundled as a monoid/monoid with zero
  homomorphism.
-/

variables {A : Type*} {B : Type*} {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

namespace prod

@[to_additive]
instance [has_mul M] [has_mul N] : has_mul (M × N) := ⟨λ p q, ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[simp, to_additive]
lemma fst_mul [has_mul M] [has_mul N] (p q : M × N) : (p * q).1 = p.1 * q.1 := rfl
@[simp, to_additive]
lemma snd_mul [has_mul M] [has_mul N] (p q : M × N) : (p * q).2 = p.2 * q.2 := rfl
@[simp, to_additive]
lemma mk_mul_mk [has_mul M] [has_mul N] (a₁ a₂ : M) (b₁ b₂ : N) :
  (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl
@[simp, to_additive]
lemma swap_mul [has_mul M] [has_mul N] (p q : M × N) : (p * q).swap = p.swap * q.swap := rfl
@[to_additive]
lemma mul_def [has_mul M] [has_mul N] (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) := rfl

@[to_additive]
instance [has_one M] [has_one N] : has_one (M × N) := ⟨(1, 1)⟩

@[simp, to_additive]
lemma fst_one [has_one M] [has_one N] : (1 : M × N).1 = 1 := rfl
@[simp, to_additive]
lemma snd_one [has_one M] [has_one N] : (1 : M × N).2 = 1 := rfl
@[to_additive]
lemma one_eq_mk [has_one M] [has_one N] : (1 : M × N) = (1, 1) := rfl
@[simp, to_additive]
lemma mk_eq_one [has_one M] [has_one N] {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 :=
mk.inj_iff
@[simp, to_additive]
lemma swap_one [has_one M] [has_one N] : (1 : M × N).swap = 1 := rfl

@[to_additive]
lemma fst_mul_snd [mul_one_class M] [mul_one_class N] (p : M × N) :
  (p.fst, 1) * (1, p.snd) = p :=
ext (mul_one p.1) (one_mul p.2)

@[to_additive]
instance [has_inv M] [has_inv N] : has_inv (M × N) := ⟨λp, (p.1⁻¹, p.2⁻¹)⟩

@[simp, to_additive]
lemma fst_inv [has_inv G] [has_inv H] (p : G × H) : (p⁻¹).1 = (p.1)⁻¹ := rfl
@[simp, to_additive]
lemma snd_inv [has_inv G] [has_inv H] (p : G × H) : (p⁻¹).2 = (p.2)⁻¹ := rfl
@[simp, to_additive]
lemma inv_mk [has_inv G] [has_inv H] (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) := rfl
@[simp, to_additive]
lemma swap_inv [has_inv G] [has_inv H] (p : G × H) : (p⁻¹).swap = p.swap⁻¹ := rfl

@[to_additive]
instance [has_involutive_inv M] [has_involutive_inv N] : has_involutive_inv (M × N) :=
{ inv_inv := λ a, ext (inv_inv _) (inv_inv _),
  ..prod.has_inv }

@[to_additive]
instance [has_div M] [has_div N] : has_div (M × N) := ⟨λ p q, ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[simp, to_additive] lemma fst_div [has_div G] [has_div H] (a b : G × H) : (a / b).1 = a.1 / b.1 :=
rfl
@[simp, to_additive] lemma snd_div [has_div G] [has_div H] (a b : G × H) : (a / b).2 = a.2 / b.2 :=
rfl
@[simp, to_additive] lemma mk_div_mk [has_div G] [has_div H] (x₁ x₂ : G) (y₁ y₂ : H) :
  (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) := rfl
@[simp, to_additive] lemma swap_div [has_div G] [has_div H] (a b : G × H) :
  (a / b).swap = a.swap / b.swap := rfl

instance [mul_zero_class M] [mul_zero_class N] : mul_zero_class (M × N) :=
{ zero_mul := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨zero_mul _, zero_mul _⟩,
  mul_zero := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨mul_zero _, mul_zero _⟩,
  .. prod.has_zero, .. prod.has_mul }

@[to_additive]
instance [semigroup M] [semigroup N] : semigroup (M × N) :=
{ mul_assoc := assume a b c, mk.inj_iff.mpr ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩,
  .. prod.has_mul }

@[to_additive]
instance [comm_semigroup G] [comm_semigroup H] : comm_semigroup (G × H) :=
{ mul_comm := assume a b, mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩,
  .. prod.semigroup }

instance [semigroup_with_zero M] [semigroup_with_zero N] : semigroup_with_zero (M × N) :=
{ .. prod.mul_zero_class, .. prod.semigroup }

@[to_additive]
instance [mul_one_class M] [mul_one_class N] : mul_one_class (M × N) :=
{ one_mul := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨one_mul _, one_mul _⟩,
  mul_one := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨mul_one _, mul_one _⟩,
  .. prod.has_mul, .. prod.has_one }

@[to_additive]
instance [monoid M] [monoid N] : monoid (M × N) :=
{ npow := λ z a, ⟨monoid.npow z a.1, monoid.npow z a.2⟩,
  npow_zero' := λ z, ext (monoid.npow_zero' _) (monoid.npow_zero' _),
  npow_succ' := λ z a, ext (monoid.npow_succ' _ _) (monoid.npow_succ' _ _),
  .. prod.semigroup, .. prod.mul_one_class }

@[to_additive prod.sub_neg_monoid]
instance [div_inv_monoid G] [div_inv_monoid H] : div_inv_monoid (G × H) :=
{ div_eq_mul_inv := λ a b, mk.inj_iff.mpr ⟨div_eq_mul_inv _ _, div_eq_mul_inv _ _⟩,
  zpow := λ z a, ⟨div_inv_monoid.zpow z a.1, div_inv_monoid.zpow z a.2⟩,
  zpow_zero' := λ z, ext (div_inv_monoid.zpow_zero' _) (div_inv_monoid.zpow_zero' _),
  zpow_succ' := λ z a, ext (div_inv_monoid.zpow_succ' _ _) (div_inv_monoid.zpow_succ' _ _),
  zpow_neg' := λ z a, ext (div_inv_monoid.zpow_neg' _ _) (div_inv_monoid.zpow_neg' _ _),
  .. prod.monoid, .. prod.has_inv, .. prod.has_div }

@[to_additive subtraction_monoid]
instance [division_monoid G] [division_monoid H] : division_monoid (G × H) :=
{ mul_inv_rev := λ a b, ext (mul_inv_rev _ _) (mul_inv_rev _ _),
  inv_eq_of_mul := λ a b h, ext (inv_eq_of_mul_eq_one_right $ congr_arg fst h)
    (inv_eq_of_mul_eq_one_right $ congr_arg snd h),
  .. prod.div_inv_monoid, .. prod.has_involutive_inv }

@[to_additive subtraction_comm_monoid]
instance [division_comm_monoid G] [division_comm_monoid H] : division_comm_monoid (G × H) :=
{ .. prod.division_monoid, .. prod.comm_semigroup }

@[to_additive]
instance [group G] [group H] : group (G × H) :=
{ mul_left_inv := assume a, mk.inj_iff.mpr ⟨mul_left_inv _, mul_left_inv _⟩,
  .. prod.div_inv_monoid }

@[to_additive]
instance [left_cancel_semigroup G] [left_cancel_semigroup H] :
  left_cancel_semigroup (G × H) :=
{ mul_left_cancel := λ a b c h, prod.ext (mul_left_cancel (prod.ext_iff.1 h).1)
    (mul_left_cancel (prod.ext_iff.1 h).2),
  .. prod.semigroup }

@[to_additive]
instance [right_cancel_semigroup G] [right_cancel_semigroup H] :
  right_cancel_semigroup (G × H) :=
{ mul_right_cancel := λ a b c h, prod.ext (mul_right_cancel (prod.ext_iff.1 h).1)
    (mul_right_cancel (prod.ext_iff.1 h).2),
  .. prod.semigroup }

@[to_additive]
instance [left_cancel_monoid M] [left_cancel_monoid N] : left_cancel_monoid (M × N) :=
{ .. prod.left_cancel_semigroup, .. prod.monoid }

@[to_additive]
instance [right_cancel_monoid M] [right_cancel_monoid N] : right_cancel_monoid (M × N) :=
{ .. prod.right_cancel_semigroup, .. prod.monoid }

@[to_additive]
instance [cancel_monoid M] [cancel_monoid N] : cancel_monoid (M × N) :=
{ .. prod.right_cancel_monoid, .. prod.left_cancel_monoid }

@[to_additive]
instance [comm_monoid M] [comm_monoid N] : comm_monoid (M × N) :=
{ .. prod.comm_semigroup, .. prod.monoid }

@[to_additive]
instance [cancel_comm_monoid M] [cancel_comm_monoid N] : cancel_comm_monoid (M × N) :=
{ .. prod.left_cancel_monoid, .. prod.comm_monoid }

instance [mul_zero_one_class M] [mul_zero_one_class N] : mul_zero_one_class (M × N) :=
{ .. prod.mul_zero_class, .. prod.mul_one_class }

instance [monoid_with_zero M] [monoid_with_zero N] : monoid_with_zero (M × N) :=
{ .. prod.monoid, .. prod.mul_zero_one_class }

instance [comm_monoid_with_zero M] [comm_monoid_with_zero N] : comm_monoid_with_zero (M × N) :=
{ .. prod.comm_monoid, .. prod.monoid_with_zero }

@[to_additive]
instance [comm_group G] [comm_group H] : comm_group (G × H) :=
{ .. prod.comm_semigroup, .. prod.group }

end prod

namespace mul_hom

section prod

variables (M N) [has_mul M] [has_mul N] [has_mul P]

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[to_additive "Given additive magmas `A`, `B`, the natural projection homomorphism
from `A × B` to `A`"]
def fst : (M × N) →ₙ* M := ⟨prod.fst, λ _ _, rfl⟩

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive "Given additive magmas `A`, `B`, the natural projection homomorphism
from `A × B` to `B`"]
def snd : (M × N) →ₙ* N := ⟨prod.snd, λ _ _, rfl⟩

variables {M N}

@[simp, to_additive] lemma coe_fst : ⇑(fst M N) = prod.fst := rfl
@[simp, to_additive] lemma coe_snd : ⇑(snd M N) = prod.snd := rfl

/-- Combine two `monoid_hom`s `f : M →ₙ* N`, `g : M →ₙ* P` into
`f.prod g : M →ₙ* (N × P)` given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive prod "Combine two `add_monoid_hom`s `f : add_hom M N`, `g : add_hom M P` into
`f.prod g : add_hom M (N × P)` given by `(f.prod g) x = (f x, g x)`"]
protected def prod (f : M →ₙ* N) (g : M →ₙ* P) : M →ₙ* (N × P) :=
{ to_fun := pi.prod f g,
  map_mul' := λ x y, prod.ext (f.map_mul x y) (g.map_mul x y) }

@[to_additive coe_prod]
lemma coe_prod (f : M →ₙ* N) (g : M →ₙ* P) : ⇑(f.prod g) = pi.prod f g := rfl

@[simp, to_additive prod_apply]
lemma prod_apply (f : M →ₙ* N) (g : M →ₙ* P) (x) : f.prod g x = (f x, g x) := rfl

@[simp, to_additive fst_comp_prod]
lemma fst_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (fst N P).comp (f.prod g) = f :=
ext $ λ x, rfl

@[simp, to_additive snd_comp_prod]
lemma snd_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (snd N P).comp (f.prod g) = g :=
ext $ λ x, rfl

@[simp, to_additive prod_unique]
lemma prod_unique (f : M →ₙ* (N × P)) :
  ((fst N P).comp f).prod ((snd N P).comp f) = f :=
ext $ λ x, by simp only [prod_apply, coe_fst, coe_snd, comp_apply, prod.mk.eta]

end prod

section prod_map

variables {M' : Type*} {N' : Type*} [has_mul M] [has_mul N] [has_mul M'] [has_mul N'] [has_mul P]
  (f : M →ₙ* M') (g : N →ₙ* N')

/-- `prod.map` as a `monoid_hom`. -/
@[to_additive prod_map "`prod.map` as an `add_monoid_hom`"]
def prod_map : (M × N) →ₙ* (M' × N') := (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prod_map_def]
lemma prod_map_def : prod_map f g = (f.comp (fst M N)).prod (g.comp (snd M N)) := rfl

@[simp, to_additive coe_prod_map]
lemma coe_prod_map : ⇑(prod_map f g) = prod.map f g := rfl

@[to_additive prod_comp_prod_map]
lemma prod_comp_prod_map (f : P →ₙ* M) (g : P →ₙ* N)
  (f' : M →ₙ* M') (g' : N →ₙ* N') :
  (f'.prod_map g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
rfl

end prod_map

section coprod

variables [has_mul M] [has_mul N] [comm_semigroup P] (f : M →ₙ* P) (g : N →ₙ* P)

/-- Coproduct of two `mul_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive "Coproduct of two `add_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : (M × N) →ₙ* P := f.comp (fst M N) * g.comp (snd M N)

@[simp, to_additive]
lemma coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 := rfl

@[to_additive]
lemma comp_coprod {Q : Type*} [comm_semigroup Q]
  (h : P →ₙ* Q) (f : M →ₙ* P) (g : N →ₙ* P) :
  h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
ext $ λ x, by simp

end coprod

end mul_hom

namespace monoid_hom

variables (M N) [mul_one_class M] [mul_one_class N]

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`.-/
@[to_additive "Given additive monoids `A`, `B`, the natural projection homomorphism
from `A × B` to `A`"]
def fst : M × N →* M := ⟨prod.fst, rfl, λ _ _, rfl⟩

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`.-/
@[to_additive "Given additive monoids `A`, `B`, the natural projection homomorphism
from `A × B` to `B`"]
def snd : M × N →* N := ⟨prod.snd, rfl, λ _ _, rfl⟩

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[to_additive "Given additive monoids `A`, `B`, the natural inclusion homomorphism
from `A` to `A × B`."]
def inl : M →* M × N :=
⟨λ x, (x, 1), rfl, λ _ _, prod.ext rfl (one_mul 1).symm⟩

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[to_additive "Given additive monoids `A`, `B`, the natural inclusion homomorphism
from `B` to `A × B`."]
def inr : N →* M × N :=
⟨λ y, (1, y), rfl, λ _ _, prod.ext (one_mul 1).symm rfl⟩

variables {M N}

@[simp, to_additive] lemma coe_fst : ⇑(fst M N) = prod.fst := rfl
@[simp, to_additive] lemma coe_snd : ⇑(snd M N) = prod.snd := rfl

@[simp, to_additive] lemma inl_apply (x) : inl M N x = (x, 1) := rfl
@[simp, to_additive] lemma inr_apply (y) : inr M N y = (1, y) := rfl

@[simp, to_additive] lemma fst_comp_inl : (fst M N).comp (inl M N) = id M := rfl
@[simp, to_additive] lemma snd_comp_inl : (snd M N).comp (inl M N) = 1 := rfl
@[simp, to_additive] lemma fst_comp_inr : (fst M N).comp (inr M N) = 1 := rfl
@[simp, to_additive] lemma snd_comp_inr : (snd M N).comp (inr M N) = id N := rfl

section prod

variable [mul_one_class P]

/-- Combine two `monoid_hom`s `f : M →* N`, `g : M →* P` into `f.prod g : M →* N × P`
given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive prod "Combine two `add_monoid_hom`s `f : M →+ N`, `g : M →+ P` into
`f.prod g : M →+ N × P` given by `(f.prod g) x = (f x, g x)`"]
protected def prod (f : M →* N) (g : M →* P) : M →* N × P :=
{ to_fun := pi.prod f g,
  map_one' := prod.ext f.map_one g.map_one,
  map_mul' := λ x y, prod.ext (f.map_mul x y) (g.map_mul x y) }

@[to_additive coe_prod]
lemma coe_prod (f : M →* N) (g : M →* P) : ⇑(f.prod g) = pi.prod f g := rfl

@[simp, to_additive prod_apply]
lemma prod_apply (f : M →* N) (g : M →* P) (x) : f.prod g x = (f x, g x) := rfl

@[simp, to_additive fst_comp_prod]
lemma fst_comp_prod (f : M →* N) (g : M →* P) : (fst N P).comp (f.prod g) = f :=
ext $ λ x, rfl

@[simp, to_additive snd_comp_prod]
lemma snd_comp_prod (f : M →* N) (g : M →* P) : (snd N P).comp (f.prod g) = g :=
ext $ λ x, rfl

@[simp, to_additive prod_unique]
lemma prod_unique (f : M →* N × P) :
  ((fst N P).comp f).prod ((snd N P).comp f) = f :=
ext $ λ x, by simp only [prod_apply, coe_fst, coe_snd, comp_apply, prod.mk.eta]

end prod

section prod_map

variables {M' : Type*} {N' : Type*} [mul_one_class M'] [mul_one_class N'] [mul_one_class P]
  (f : M →* M') (g : N →* N')

/-- `prod.map` as a `monoid_hom`. -/
@[to_additive prod_map "`prod.map` as an `add_monoid_hom`"]
def prod_map : M × N →* M' × N' := (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prod_map_def]
lemma prod_map_def : prod_map f g = (f.comp (fst M N)).prod (g.comp (snd M N)) := rfl

@[simp, to_additive coe_prod_map]
lemma coe_prod_map : ⇑(prod_map f g) = prod.map f g := rfl

@[to_additive prod_comp_prod_map]
lemma prod_comp_prod_map (f : P →* M) (g : P →* N) (f' : M →* M') (g' : N →* N') :
  (f'.prod_map g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
rfl

end prod_map

section coprod

variables [comm_monoid P] (f : M →* P) (g : N →* P)

/-- Coproduct of two `monoid_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 * g p.2`. -/
@[to_additive "Coproduct of two `add_monoid_hom`s with the same codomain:
`f.coprod g (p : M × N) = f p.1 + g p.2`."]
def coprod : M × N →* P := f.comp (fst M N) * g.comp (snd M N)

@[simp, to_additive]
lemma coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 := rfl

@[simp, to_additive]
lemma coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
ext $ λ x, by simp [coprod_apply]

@[simp, to_additive]
lemma coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
ext $ λ x, by simp [coprod_apply]

@[simp, to_additive] lemma coprod_unique (f : M × N →* P) :
  (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
ext $ λ x, by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]

@[simp, to_additive] lemma coprod_inl_inr {M N : Type*} [comm_monoid M] [comm_monoid N] :
  (inl M N).coprod (inr M N) = id (M × N) :=
coprod_unique (id $ M × N)

@[to_additive]
lemma comp_coprod {Q : Type*} [comm_monoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
  h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
ext $ λ x, by simp

end coprod

end monoid_hom

namespace mul_equiv

section
variables {M N} [mul_one_class M] [mul_one_class N]

/-- The equivalence between `M × N` and `N × M` given by swapping the components
is multiplicative. -/
@[to_additive prod_comm "The equivalence between `M × N` and `N × M` given by swapping the
components is additive."]
def prod_comm : M × N ≃* N × M :=
{ map_mul' := λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩, rfl, ..equiv.prod_comm M N }

@[simp, to_additive coe_prod_comm] lemma coe_prod_comm :
  ⇑(prod_comm : M × N ≃* N × M) = prod.swap := rfl

@[simp, to_additive coe_prod_comm_symm] lemma coe_prod_comm_symm :
  ⇑((prod_comm : M × N ≃* N × M).symm) = prod.swap := rfl

end

section
variables {M N} [monoid M] [monoid N]

/-- The monoid equivalence between units of a product of two monoids, and the product of the
    units of each monoid. -/
@[to_additive prod_add_units "The additive monoid equivalence between additive units of a product
of two additive monoids, and the product of the additive units of each additive monoid."]
def prod_units : (M × N)ˣ ≃* Mˣ × Nˣ :=
{ to_fun := (units.map (monoid_hom.fst M N)).prod (units.map (monoid_hom.snd M N)),
  inv_fun := λ u, ⟨(u.1, u.2), (↑u.1⁻¹, ↑u.2⁻¹), by simp, by simp⟩,
  left_inv := λ u, by simp,
  right_inv := λ ⟨u₁, u₂⟩, by simp [units.map],
  map_mul' := monoid_hom.map_mul _ }

end

end mul_equiv

namespace units

open mul_opposite

/-- Canonical homomorphism of monoids from `αˣ` into `α × αᵐᵒᵖ`.
Used mainly to define the natural topology of `αˣ`. -/
@[to_additive "Canonical homomorphism of additive monoids from `add_units α` into `α × αᵃᵒᵖ`.
Used mainly to define the natural topology of `add_units α`."]
def embed_product (α : Type*) [monoid α] : αˣ →* α × αᵐᵒᵖ :=
{ to_fun := λ x, ⟨x, op ↑x⁻¹⟩,
  map_one' := by simp only [inv_one, eq_self_iff_true, units.coe_one, op_one, prod.mk_eq_one,
    and_self],
  map_mul' := λ x y, by simp only [mul_inv_rev, op_mul, units.coe_mul, prod.mk_mul_mk] }

end units

/-! ### Multiplication and division as homomorphisms -/

section bundled_mul_div
variables {α : Type*}

/-- Multiplication as a multiplicative homomorphism. -/
@[to_additive "Addition as an additive homomorphism.", simps]
def mul_mul_hom [comm_semigroup α] : (α × α) →ₙ* α :=
{ to_fun := λ a, a.1 * a.2,
  map_mul' := λ a b, mul_mul_mul_comm _ _ _ _ }

/-- Multiplication as a monoid homomorphism. -/
@[to_additive "Addition as an additive monoid homomorphism.", simps]
def mul_monoid_hom [comm_monoid α] : α × α →* α :=
{ map_one' := mul_one _,
  .. mul_mul_hom }

/-- Multiplication as a multiplicative homomorphism with zero. -/
@[simps]
def mul_monoid_with_zero_hom [comm_monoid_with_zero α] : α × α →*₀ α :=
{ map_zero' := mul_zero _,
  .. mul_monoid_hom }

/-- Division as a monoid homomorphism. -/
@[to_additive "Subtraction as an additive monoid homomorphism.", simps]
def div_monoid_hom [comm_group α] : α × α →* α :=
{ to_fun := λ a, a.1 / a.2,
  map_one' := div_one _,
  map_mul' := λ a b, mul_div_mul_comm _ _ _ _ }

/-- Division as a multiplicative homomorphism with zero. -/
@[simps]
def div_monoid_with_zero_hom [comm_group_with_zero α] : α × α →*₀ α :=
{ to_fun := λ a, a.1 / a.2,
  map_zero' := zero_div _,
  map_one' := div_one _,
  map_mul' := λ a b, mul_div_mul_comm _ _ _ _ }

end bundled_mul_div
