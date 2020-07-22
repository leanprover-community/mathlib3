import algebra.group.basic tactic.pi_instances

namespace pi
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

@[to_additive] instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) := ⟨λ _, 1⟩
@[simp, to_additive] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

@[to_additive]
instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) := ⟨λ f g i, f i * g i⟩
@[simp, to_additive] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

@[to_additive] instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) := ⟨λ f i, (f i)⁻¹⟩
@[simp, to_additive] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl

@[to_additive add_semigroup]
instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive add_comm_semigroup]
instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive add_monoid]
instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive add_comm_monoid]
instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

@[to_additive add_group]
instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, .. };
  tactic.pi_instance_derive_field

@[to_additive add_comm_group]
instance comm_group [∀ i, comm_group $ f i] : comm_group (Π i : I, f i) :=
by refine_struct { one := (1 : Π i, f i), mul := (*), inv := has_inv.inv, .. };
  tactic.pi_instance_derive_field

@[to_additive add_left_cancel_semigroup]
instance left_cancel_semigroup [∀ i, left_cancel_semigroup $ f i] :
  left_cancel_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

@[to_additive add_right_cancel_semigroup]
instance right_cancel_semigroup [∀ i, right_cancel_semigroup $ f i] :
  right_cancel_semigroup (Π i : I, f i) :=
by refine_struct { mul := (*) }; tactic.pi_instance_derive_field

end pi
