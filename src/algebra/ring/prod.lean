/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Chris Hughes, Mario Carneiro, Yury Kudryashov
-/
import data.int.cast.prod
import algebra.group.prod
import algebra.ring.equiv
import algebra.order.monoid.prod

/-!
# Semiring, ring etc structures on `R × S`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define two-binop (`semiring`, `ring` etc) structures on `R × S`. We also prove
trivial `simp` lemmas, and define the following operations on `ring_hom`s and similarly for
`non_unital_ring_hom`s:

* `fst R S : R × S →+* R`, `snd R S : R × S →+* S`: projections `prod.fst` and `prod.snd`
  as `ring_hom`s;
* `f.prod g : `R →+* S × T`: sends `x` to `(f x, g x)`;
* `f.prod_map g : `R × S → R' × S'`: `prod.map f g` as a `ring_hom`,
  sends `(x, y)` to `(f x, g y)`.
-/

variables {α β R R' S S' T T' : Type*}

namespace prod

/-- Product of two distributive types is distributive. -/
instance [distrib R] [distrib S] : distrib (R × S) :=
{ left_distrib := λ a b c, mk.inj_iff.mpr ⟨left_distrib _ _ _, left_distrib _ _ _⟩,
  right_distrib := λ a b c, mk.inj_iff.mpr ⟨right_distrib _ _ _, right_distrib _ _ _⟩,
  .. prod.has_add, .. prod.has_mul }

/-- Product of two `non_unital_non_assoc_semiring`s is a `non_unital_non_assoc_semiring`. -/
instance [non_unital_non_assoc_semiring R] [non_unital_non_assoc_semiring S] :
  non_unital_non_assoc_semiring (R × S) :=
{ .. prod.add_comm_monoid, .. prod.mul_zero_class, .. prod.distrib }

/-- Product of two `non_unital_semiring`s is a `non_unital_semiring`. -/
instance [non_unital_semiring R] [non_unital_semiring S] :
  non_unital_semiring (R × S) :=
{ .. prod.non_unital_non_assoc_semiring, .. prod.semigroup }

/-- Product of two `non_assoc_semiring`s is a `non_assoc_semiring`. -/
instance [non_assoc_semiring R] [non_assoc_semiring S] :
  non_assoc_semiring (R × S) :=
{ .. prod.non_unital_non_assoc_semiring, .. prod.mul_one_class, .. prod.add_monoid_with_one }

/-- Product of two semirings is a semiring. -/
instance [semiring R] [semiring S] : semiring (R × S) :=
{ .. prod.add_comm_monoid, .. prod.monoid_with_zero, .. prod.distrib, .. prod.add_monoid_with_one }

/-- Product of two `non_unital_comm_semiring`s is a `non_unital_comm_semiring`. -/
instance [non_unital_comm_semiring R] [non_unital_comm_semiring S] :
  non_unital_comm_semiring (R × S) :=
{ .. prod.non_unital_semiring, .. prod.comm_semigroup }

/-- Product of two commutative semirings is a commutative semiring. -/
instance [comm_semiring R] [comm_semiring S] : comm_semiring (R × S) :=
{ .. prod.semiring, .. prod.comm_monoid }

instance [non_unital_non_assoc_ring R] [non_unital_non_assoc_ring S] :
  non_unital_non_assoc_ring (R × S) :=
{ .. prod.add_comm_group, .. prod.non_unital_non_assoc_semiring }

instance [non_unital_ring R] [non_unital_ring S] :
  non_unital_ring (R × S) :=
{ .. prod.add_comm_group, .. prod.non_unital_semiring }

instance [non_assoc_ring R] [non_assoc_ring S] :
  non_assoc_ring (R × S) :=
{ .. prod.add_comm_group, .. prod.non_assoc_semiring, .. prod.add_group_with_one }

/-- Product of two rings is a ring. -/
instance [ring R] [ring S] : ring (R × S) :=
{ .. prod.add_comm_group, .. prod.add_group_with_one, .. prod.semiring }

/-- Product of two `non_unital_comm_ring`s is a `non_unital_comm_ring`. -/
instance [non_unital_comm_ring R] [non_unital_comm_ring S] : non_unital_comm_ring (R × S) :=
{ .. prod.non_unital_ring, .. prod.comm_semigroup }

/-- Product of two commutative rings is a commutative ring. -/
instance [comm_ring R] [comm_ring S] : comm_ring (R × S) :=
{ .. prod.ring, .. prod.comm_monoid }

end prod

namespace non_unital_ring_hom

variables (R S) [non_unital_non_assoc_semiring R] [non_unital_non_assoc_semiring S]

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`.-/
def fst : R × S →ₙ+* R := { to_fun := prod.fst, .. mul_hom.fst R S, .. add_monoid_hom.fst R S }

/-- Given non-unital semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`.-/
def snd : R × S →ₙ+* S := { to_fun := prod.snd, .. mul_hom.snd R S, .. add_monoid_hom.snd R S }

variables {R S}

@[simp] lemma coe_fst : ⇑(fst R S) = prod.fst := rfl
@[simp] lemma coe_snd : ⇑(snd R S) = prod.snd := rfl

section prod

variables [non_unital_non_assoc_semiring T] (f : R →ₙ+* S) (g : R →ₙ+* T)

/-- Combine two non-unital ring homomorphisms `f : R →ₙ+* S`, `g : R →ₙ+* T` into
`f.prod g : R →ₙ+* S × T` given by `(f.prod g) x = (f x, g x)` -/
protected def prod (f : R →ₙ+* S) (g : R →ₙ+* T) : R →ₙ+* S × T :=
{ to_fun := λ x, (f x, g x),
  .. mul_hom.prod (f : mul_hom R S) (g : mul_hom R T),
  .. add_monoid_hom.prod (f : R →+ S) (g : R →+ T) }

@[simp] lemma prod_apply (x) : f.prod g x = (f x, g x) := rfl

@[simp] lemma fst_comp_prod : (fst S T).comp (f.prod g) = f :=
ext $ λ x, rfl

@[simp] lemma snd_comp_prod : (snd S T).comp (f.prod g) = g :=
ext $ λ x, rfl

lemma prod_unique (f : R →ₙ+* S × T) :
  ((fst S T).comp f).prod ((snd S T).comp f) = f :=
ext $ λ x, by simp only [prod_apply, coe_fst, coe_snd, comp_apply, prod.mk.eta]

end prod

section prod_map

variables [non_unital_non_assoc_semiring R'] [non_unital_non_assoc_semiring S']
  [non_unital_non_assoc_semiring T]
variables (f : R →ₙ+* R') (g : S →ₙ+* S')

/-- `prod.map` as a `non_unital_ring_hom`. -/
def prod_map : R × S →ₙ+* R' × S' := (f.comp (fst R S)).prod (g.comp (snd R S))

lemma prod_map_def : prod_map f g = (f.comp (fst R S)).prod (g.comp (snd R S)) := rfl

@[simp]
lemma coe_prod_map : ⇑(prod_map f g) = prod.map f g := rfl

lemma prod_comp_prod_map (f : T →ₙ+* R) (g : T →ₙ+* S) (f' : R →ₙ+* R') (g' : S →ₙ+* S') :
  (f'.prod_map g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
rfl

end prod_map

end non_unital_ring_hom

namespace ring_hom

variables (R S) [non_assoc_semiring R] [non_assoc_semiring S]

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `R`.-/
def fst : R × S →+* R := { to_fun := prod.fst, .. monoid_hom.fst R S, .. add_monoid_hom.fst R S }

/-- Given semirings `R`, `S`, the natural projection homomorphism from `R × S` to `S`.-/
def snd : R × S →+* S := { to_fun := prod.snd, .. monoid_hom.snd R S, .. add_monoid_hom.snd R S }

variables {R S}

@[simp] lemma coe_fst : ⇑(fst R S) = prod.fst := rfl
@[simp] lemma coe_snd : ⇑(snd R S) = prod.snd := rfl

section prod

variables [non_assoc_semiring T] (f : R →+* S) (g : R →+* T)

/-- Combine two ring homomorphisms `f : R →+* S`, `g : R →+* T` into `f.prod g : R →+* S × T`
given by `(f.prod g) x = (f x, g x)` -/
protected def prod (f : R →+* S) (g : R →+* T) : R →+* S × T :=
{ to_fun := λ x, (f x, g x),
  .. monoid_hom.prod (f : R →* S) (g : R →* T), .. add_monoid_hom.prod (f : R →+ S) (g : R →+ T) }

@[simp] lemma prod_apply (x) : f.prod g x = (f x, g x) := rfl

@[simp] lemma fst_comp_prod : (fst S T).comp (f.prod g) = f :=
ext $ λ x, rfl

@[simp] lemma snd_comp_prod : (snd S T).comp (f.prod g) = g :=
ext $ λ x, rfl

lemma prod_unique (f : R →+* S × T) :
  ((fst S T).comp f).prod ((snd S T).comp f) = f :=
ext $ λ x, by simp only [prod_apply, coe_fst, coe_snd, comp_apply, prod.mk.eta]

end prod

section prod_map

variables [non_assoc_semiring R'] [non_assoc_semiring S'] [non_assoc_semiring T]
variables (f : R →+* R') (g : S →+* S')

/-- `prod.map` as a `ring_hom`. -/
def prod_map : R × S →+* R' × S' := (f.comp (fst R S)).prod (g.comp (snd R S))

lemma prod_map_def : prod_map f g = (f.comp (fst R S)).prod (g.comp (snd R S)) := rfl

@[simp]
lemma coe_prod_map : ⇑(prod_map f g) = prod.map f g := rfl

lemma prod_comp_prod_map (f : T →+* R) (g : T →+* S) (f' : R →+* R') (g' : S →+* S') :
  (f'.prod_map g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
rfl

end prod_map

end ring_hom

namespace ring_equiv
variables {R S} [non_assoc_semiring R] [non_assoc_semiring S]

/-- Swapping components as an equivalence of (semi)rings. -/
def prod_comm : R × S ≃+* S × R :=
{ ..add_equiv.prod_comm, ..mul_equiv.prod_comm }

@[simp] lemma coe_prod_comm : ⇑(prod_comm : R × S ≃+* S × R) = prod.swap := rfl
@[simp] lemma coe_prod_comm_symm : ⇑((prod_comm : R × S ≃+* S × R).symm) = prod.swap := rfl

@[simp] lemma fst_comp_coe_prod_comm :
  (ring_hom.fst S R).comp ↑(prod_comm : R × S ≃+* S × R) = ring_hom.snd R S :=
ring_hom.ext $ λ _, rfl

@[simp] lemma snd_comp_coe_prod_comm :
  (ring_hom.snd S R).comp ↑(prod_comm : R × S ≃+* S × R) = ring_hom.fst R S :=
ring_hom.ext $ λ _, rfl

variables (R S) [subsingleton S]

/-- A ring `R` is isomorphic to `R × S` when `S` is the zero ring -/
@[simps] def prod_zero_ring : R ≃+* R × S :=
{ to_fun := λ x, (x, 0),
  inv_fun := prod.fst,
  map_add' := by simp,
  map_mul' := by simp,
  left_inv := λ x, rfl,
  right_inv := λ x, by cases x; simp }

/-- A ring `R` is isomorphic to `S × R` when `S` is the zero ring -/
@[simps] def zero_ring_prod : R ≃+* S × R :=
{ to_fun := λ x, (0, x),
  inv_fun := prod.snd,
  map_add' := by simp,
  map_mul' := by simp,
  left_inv := λ x, rfl,
  right_inv := λ x, by cases x; simp }

end ring_equiv

/-- The product of two nontrivial rings is not a domain -/
lemma false_of_nontrivial_of_product_domain (R S : Type*) [ring R] [ring S]
  [is_domain (R × S)] [nontrivial R] [nontrivial S] : false :=
begin
  have := no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero
    (show ((0 : R), (1 : S)) * (1, 0) = 0, by simp),
  rw [prod.mk_eq_zero,prod.mk_eq_zero] at this,
  rcases this with (⟨_,h⟩|⟨h,_⟩),
  { exact zero_ne_one h.symm },
  { exact zero_ne_one h.symm }
end

/-! ### Order -/

instance [ordered_semiring α] [ordered_semiring β] : ordered_semiring (α × β) :=
{ add_le_add_left := λ _ _, add_le_add_left,
  zero_le_one := ⟨zero_le_one, zero_le_one⟩,
  mul_le_mul_of_nonneg_left := λ a b c hab hc,
    ⟨mul_le_mul_of_nonneg_left hab.1 hc.1, mul_le_mul_of_nonneg_left hab.2 hc.2⟩,
  mul_le_mul_of_nonneg_right := λ a b c hab hc,
    ⟨mul_le_mul_of_nonneg_right hab.1 hc.1, mul_le_mul_of_nonneg_right hab.2 hc.2⟩,
  ..prod.semiring, ..prod.partial_order _ _ }

instance [ordered_comm_semiring α] [ordered_comm_semiring β] : ordered_comm_semiring (α × β) :=
{ ..prod.comm_semiring, ..prod.ordered_semiring }

instance [ordered_ring α] [ordered_ring β] : ordered_ring (α × β) :=
{ mul_nonneg := λ a b ha hb, ⟨mul_nonneg ha.1 hb.1, mul_nonneg ha.2 hb.2⟩,
  ..prod.ring, ..prod.ordered_semiring }

instance [ordered_comm_ring α] [ordered_comm_ring β] : ordered_comm_ring (α × β) :=
{ ..prod.comm_ring, ..prod.ordered_ring }
