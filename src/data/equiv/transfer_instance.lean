/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.equiv.basic
import algebra.field
import algebra.module
import algebra.algebra.basic
import algebra.group.type_tags
import ring_theory.ideal.local_ring

/-!
# Transfer algebraic structures across `equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

## Tags

equiv, group, ring, field, module, algebra
-/

universes u v
variables {α : Type u} {β : Type v}

namespace equiv


section instances

variables (e : α ≃ β)

/-- Transfer `has_one` across an `equiv` -/
@[to_additive "Transfer `has_zero` across an `equiv`"]
protected def has_one [has_one β] : has_one α := ⟨e.symm 1⟩
@[to_additive]
lemma one_def [has_one β] : @has_one.one _ (equiv.has_one e) = e.symm 1 := rfl

/-- Transfer `has_mul` across an `equiv` -/
@[to_additive "Transfer `has_add` across an `equiv`"]
protected def has_mul [has_mul β] : has_mul α := ⟨λ x y, e.symm (e x * e y)⟩
@[to_additive]
lemma mul_def [has_mul β] (x y : α) :
  @has_mul.mul _ (equiv.has_mul e) x y = e.symm (e x * e y) := rfl

/-- Transfer `has_div` across an `equiv` -/
@[to_additive "Transfer `has_sub` across an `equiv`"]
protected def has_div [has_div β] : has_div α := ⟨λ x y, e.symm (e x / e y)⟩
@[to_additive]
lemma div_def [has_div β] (x y : α) :
@has_div.div _ (equiv.has_div e) x y = e.symm (e x / e y) := rfl

/-- Transfer `has_inv` across an `equiv` -/
@[to_additive "Transfer `has_neg` across an `equiv`"]
protected def has_inv [has_inv β] : has_inv α := ⟨λ x, e.symm (e x)⁻¹⟩
@[to_additive]
lemma inv_def [has_inv β] (x : α) : @has_inv.inv _ (equiv.has_inv e) x = e.symm (e x)⁻¹ := rfl

/-- Transfer `has_scalar` across an `equiv` -/
protected def has_scalar {R : Type*} [has_scalar R β] : has_scalar R α  :=
⟨λ r x, e.symm (r • (e x))⟩
lemma smul_def {R : Type*} [has_scalar R β] (r : R) (x : α) :
  @has_scalar.smul _ _ (equiv.has_scalar e) r x = e.symm (r • (e x)) := rfl

/--
An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β`
where the multiplicative structure on `α` is
the one obtained by transporting a multiplicative structure on `β` back along `e`.
-/
@[to_additive
"An equivalence `e : α ≃ β` gives a additive equivalence `α ≃+ β`
where the additive structure on `α` is
the one obtained by transporting an additive structure on `β` back along `e`."]
def mul_equiv (e : α ≃ β) [has_mul β] :
  by { letI := equiv.has_mul e, exact α ≃* β } :=
begin
  introsI,
  exact
  { map_mul' := λ x y, by { apply e.symm.injective, simp, refl, },
    ..e }
end

@[simp, to_additive] lemma mul_equiv_apply (e : α ≃ β) [has_mul β] (a : α) :
  (mul_equiv e) a = e a := rfl

@[to_additive] lemma mul_equiv_symm_apply (e : α ≃ β) [has_mul β] (b : β) :
  by { letI := equiv.has_mul e, exact (mul_equiv e).symm b = e.symm b } :=
begin
  intros, refl,
end

/--
An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ring_equiv (e : α ≃ β) [has_add β] [has_mul β] :
  by { letI := equiv.has_add e, letI := equiv.has_mul e, exact α ≃+* β } :=
begin
  introsI,
  exact
  { map_add' := λ x y, by { apply e.symm.injective, simp, refl, },
    map_mul' := λ x y, by { apply e.symm.injective, simp, refl, },
    ..e }
end

@[simp] lemma ring_equiv_apply (e : α ≃ β) [has_add β] [has_mul β] (a : α) :
  (ring_equiv e) a = e a := rfl

lemma ring_equiv_symm_apply (e : α ≃ β) [has_add β] [has_mul β] (b : β) :
  by { letI := equiv.has_add e, letI := equiv.has_mul e, exact (ring_equiv e).symm b = e.symm b } :=
begin
  intros, refl,
end

/-- Transfer `semigroup` across an `equiv` -/
@[to_additive "Transfer `add_semigroup` across an `equiv`"]
protected def semigroup [semigroup β] : semigroup α :=
let mul := e.has_mul in
by resetI; apply e.injective.semigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `semigroup_with_zero` across an `equiv` -/
protected def semigroup_with_zero [semigroup_with_zero β] : semigroup_with_zero α :=
let mul := e.has_mul, zero := e.has_zero in
by resetI; apply e.injective.semigroup_with_zero _; intros; exact e.apply_symm_apply _

/-- Transfer `comm_semigroup` across an `equiv` -/
@[to_additive "Transfer `add_comm_semigroup` across an `equiv`"]
protected def comm_semigroup [comm_semigroup β] : comm_semigroup α :=
let mul := e.has_mul in
by resetI; apply e.injective.comm_semigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `mul_zero_class` across an `equiv` -/
protected def mul_zero_class [mul_zero_class β] : mul_zero_class α :=
let zero := e.has_zero, mul := e.has_mul in
by resetI; apply e.injective.mul_zero_class _; intros; exact e.apply_symm_apply _

/-- Transfer `mul_one_class` across an `equiv` -/
@[to_additive "Transfer `add_zero_class` across an `equiv`"]
protected def mul_one_class [mul_one_class β] : mul_one_class α :=
let one := e.has_one, mul := e.has_mul in
by resetI; apply e.injective.mul_one_class _; intros; exact e.apply_symm_apply _

/-- Transfer `mul_zero_one_class` across an `equiv` -/
protected def mul_zero_one_class [mul_zero_one_class β] : mul_zero_one_class α :=
let zero := e.has_zero, one := e.has_one,mul := e.has_mul in
by resetI; apply e.injective.mul_zero_one_class _; intros; exact e.apply_symm_apply _

/-- Transfer `monoid` across an `equiv` -/
@[to_additive "Transfer `add_monoid` across an `equiv`"]
protected def monoid [monoid β] : monoid α :=
let one := e.has_one, mul := e.has_mul in
by resetI; apply e.injective.monoid _; intros; exact e.apply_symm_apply _

/-- Transfer `comm_monoid` across an `equiv` -/
@[to_additive "Transfer `add_comm_monoid` across an `equiv`"]
protected def comm_monoid [comm_monoid β] : comm_monoid α :=
let one := e.has_one, mul := e.has_mul in
by resetI; apply e.injective.comm_monoid _; intros; exact e.apply_symm_apply _

/-- Transfer `group` across an `equiv` -/
@[to_additive "Transfer `add_group` across an `equiv`"]
protected def group [group β] : group α :=
let one := e.has_one, mul := e.has_mul, inv := e.has_inv, div := e.has_div in
by resetI; apply e.injective.group _; intros; exact e.apply_symm_apply _

/-- Transfer `comm_group` across an `equiv` -/
@[to_additive "Transfer `add_comm_group` across an `equiv`"]
protected def comm_group [comm_group β] : comm_group α :=
let one := e.has_one, mul := e.has_mul, inv := e.has_inv, div := e.has_div in
by resetI; apply e.injective.comm_group _; intros; exact e.apply_symm_apply _

/-- Transfer `non_unital_non_assoc_semiring` across an `equiv` -/
protected def non_unital_non_assoc_semiring [non_unital_non_assoc_semiring β] :
  non_unital_non_assoc_semiring α :=
let zero := e.has_zero, add := e.has_add, mul := e.has_mul in
by resetI; apply e.injective.non_unital_non_assoc_semiring _; intros; exact e.apply_symm_apply _

/-- Transfer `non_unital_semiring` across an `equiv` -/
protected def non_unital_semiring [non_unital_semiring β] :  non_unital_semiring α :=
let zero := e.has_zero, add := e.has_add, mul := e.has_mul in
by resetI; apply e.injective.non_unital_semiring _; intros; exact e.apply_symm_apply _

/-- Transfer `non_assoc_semiring` across an `equiv` -/
protected def non_assoc_semiring [non_assoc_semiring β] : non_assoc_semiring α :=
let zero := e.has_zero, add := e.has_add, one := e.has_one, mul := e.has_mul in
by resetI; apply e.injective.non_assoc_semiring _; intros; exact e.apply_symm_apply _

/-- Transfer `semiring` across an `equiv` -/
protected def semiring [semiring β] : semiring α :=
let zero := e.has_zero, add := e.has_add, one := e.has_one, mul := e.has_mul in
by resetI; apply e.injective.semiring _; intros; exact e.apply_symm_apply _

/-- Transfer `comm_semiring` across an `equiv` -/
protected def comm_semiring [comm_semiring β] : comm_semiring α :=
let zero := e.has_zero, add := e.has_add, one := e.has_one, mul := e.has_mul in
by resetI; apply e.injective.comm_semiring _; intros; exact e.apply_symm_apply _

/-- Transfer `ring` across an `equiv` -/
protected def ring [ring β] : ring α :=
let zero := e.has_zero, add := e.has_add, one := e.has_one, mul := e.has_mul, neg := e.has_neg,
  sub := e.has_sub in
by resetI; apply e.injective.ring _; intros; exact e.apply_symm_apply _

/-- Transfer `comm_ring` across an `equiv` -/
protected def comm_ring [comm_ring β] : comm_ring α :=
let zero := e.has_zero, add := e.has_add, one := e.has_one, mul := e.has_mul, neg := e.has_neg,
  sub := e.has_sub in
by resetI; apply e.injective.comm_ring _; intros; exact e.apply_symm_apply _

/-- Transfer `nonzero` across an `equiv` -/
protected theorem nontrivial [nontrivial β] : nontrivial α :=
e.surjective.nontrivial

/-- Transfer `is_domain` across an `equiv` -/
protected theorem is_domain [ring α] [ring β] [is_domain β] (e : α ≃+* β) : is_domain α :=
function.injective.is_domain e.to_ring_hom e.injective

/-- Transfer `division_ring` across an `equiv` -/
protected def division_ring [division_ring β] : division_ring α :=
let zero := e.has_zero, add := e.has_add, one := e.has_one, mul := e.has_mul, neg := e.has_neg,
  sub := e.has_sub, inv := e.has_inv, div := e.has_div in
by resetI; apply e.injective.division_ring _; intros; exact e.apply_symm_apply _

/-- Transfer `field` across an `equiv` -/
protected def field [field β] : field α :=
let zero := e.has_zero, add := e.has_add, one := e.has_one, mul := e.has_mul, neg := e.has_neg,
  sub := e.has_sub, inv := e.has_inv, div := e.has_div in
by resetI; apply e.injective.field _; intros; exact e.apply_symm_apply _

section R
variables (R : Type*)
include R

section
variables [monoid R]

/-- Transfer `mul_action` across an `equiv` -/
protected def mul_action (e : α ≃ β) [mul_action R β] : mul_action R α :=
{ one_smul := by simp [smul_def],
  mul_smul := by simp [smul_def, mul_smul],
  ..equiv.has_scalar e }

/-- Transfer `distrib_mul_action` across an `equiv` -/
protected def distrib_mul_action (e : α ≃ β) [add_comm_monoid β] :
  begin
    letI := equiv.add_comm_monoid e,
    exact Π [distrib_mul_action R β], distrib_mul_action R α
  end :=
begin
  intros,
  letI := equiv.add_comm_monoid e,
  exact (
  { smul_zero := by simp [zero_def, smul_def],
    smul_add := by simp [add_def, smul_def, smul_add],
    ..equiv.mul_action R e } : distrib_mul_action R α)
end

end

section
variables [semiring R]

/-- Transfer `module` across an `equiv` -/
protected def module (e : α ≃ β) [add_comm_monoid β] :
  begin
    letI := equiv.add_comm_monoid e,
    exact Π [module R β], module R α
  end :=
begin
  introsI,
  exact (
  { zero_smul := by simp [zero_def, smul_def],
    add_smul := by simp [add_def, smul_def, add_smul],
    ..equiv.distrib_mul_action R e } : module R α)
end

/--
An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linear_equiv (e : α ≃ β) [add_comm_monoid β] [module R β] :
  begin
    letI := equiv.add_comm_monoid e,
    letI := equiv.module R e,
    exact α ≃ₗ[R] β
  end :=
begin
  introsI,
  exact
  { map_smul' := λ r x, by { apply e.symm.injective, simp, refl, },
    ..equiv.add_equiv e }
end

end

section
variables [comm_semiring R]

/-- Transfer `algebra` across an `equiv` -/
protected def algebra (e : α ≃ β) [semiring β] :
  begin
    letI := equiv.semiring e,
    exact Π [algebra R β], algebra R α
  end :=
begin
  introsI,
  fapply ring_hom.to_algebra',
  { exact ((ring_equiv e).symm : β →+* α).comp (algebra_map R β), },
  { intros r x,
    simp only [function.comp_app, ring_hom.coe_comp],
    have p := ring_equiv_symm_apply e,
    dsimp at p,
    erw p, clear p,
    apply (ring_equiv e).injective,
    simp only [(ring_equiv e).map_mul],
    simp [algebra.commutes], }
end

/--
An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def alg_equiv (e : α ≃ β) [semiring β] [algebra R β] :
  begin
    letI := equiv.semiring e,
    letI := equiv.algebra R e,
    exact α ≃ₐ[R] β
  end :=
begin
  introsI,
  exact
  { commutes' := λ r, by { apply e.symm.injective, simp, refl, },
    ..equiv.ring_equiv e }
end

end
end R

end instances
end equiv

namespace ring_equiv

protected lemma local_ring {A B : Type*} [comm_ring A] [local_ring A] [comm_ring B] (e : A ≃+* B) :
  local_ring B :=
begin
  haveI := e.symm.to_equiv.nontrivial,
  refine @local_of_surjective A B _ _ _ _ e e.to_equiv.surjective,
end

end ring_equiv
