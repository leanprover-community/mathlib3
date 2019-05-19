/-
Copyright (c) 2019 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hoang Le Truong.

If β is a semigroup, group, ring, module over γ,... then 
(α → β) is a semigroup, group, ring, module over γ,... 

-/
import   algebra.module   


universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} 
local attribute [instance] classical.prop_decidable

namespace map

protected def has_zero [has_zero β] : has_zero (α → β) := ⟨λ x, 0⟩
lemma zero_def [has_zero β] (x:α) : @has_zero.zero _ map.has_zero  x = 0 := rfl

protected def has_one [has_one β] : has_one (α → β )  := ⟨λ x, (1:β)   ⟩
lemma one_def [has_one β] (x:α) : @has_one.one _ map.has_one x = 1 := rfl

protected def has_mul [has_mul β] : has_mul (α → β ) := ⟨λ x y, λ z,  x z * y z⟩
lemma mul_def [has_mul β] (x y : α→ β) (z:α) : @has_mul.mul _ map.has_mul x y z=  (x z) * (y z) := rfl

protected def has_add [has_add β] : has_add(α → β ) := ⟨λ f g, λ z,  f z + g z⟩ 
lemma add_def [has_add β] (x y : α→ β) (z:α) :  @has_add.add _ map.has_add x y z = x z +  y z := rfl

protected def has_inv [has_inv β] : has_inv (α → β ) := ⟨λ x, λ y,  (x y )⁻¹⟩
lemma inv_def [has_inv β] (x : α → β ) (y: α) : @has_inv.inv _ map.has_inv x y = (x y)⁻¹ := rfl

protected def has_neg [has_neg β] : has_neg (α → β ) := ⟨λ x, λ y, -x y⟩
lemma neg_def [has_neg β] (x : α → β ) (y:α) : @has_neg.neg _ map.has_neg x y = - x y := rfl

protected def has_scalar [has_scalar γ β] : has_scalar γ (α → β ) := ⟨λ a x , λ y, a • x y⟩
lemma smul_def [has_scalar γ β] (a:γ) (x : α → β ) (y:α) : @has_scalar.smul _ _ map.has_scalar a x y =  a • x y := rfl

protected def semigroup [semigroup β] : semigroup (α → β) :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..map.has_mul }

protected def comm_semigroup [comm_semigroup β] : comm_semigroup (α → β )  :=
{ mul_comm := by { repeat{intro}, ext1, simp [mul_def, mul_comm]}
  ..map.semigroup }

protected def monoid [monoid β] : monoid (α → β )  :=
{  monoid.
   mul       := map.has_mul.mul,
   mul_assoc := by simp [mul_def, mul_assoc],
   one       := λ x:α, (1:β),
   one_mul   := by {intro, ext1, simp [mul_def, map.one_def]},
   mul_one   := by {intro, ext1, simp [mul_def, map.one_def]}}

protected def comm_monoid [comm_monoid β] : comm_monoid (α→ β) :=
{ ..map.comm_semigroup,
  ..map.monoid  }

protected def group [group β] : group (α→ β ) :=
{ group.
  mul          := map.has_mul.mul,
  mul_assoc    := by simp [mul_def, mul_assoc],
  one          := λ x:α, (1:β),
  one_mul      := by {intro, ext1, simp [mul_def, map.one_def]},
  mul_one      := by {intro, ext1, simp [mul_def, map.one_def]},
  mul_left_inv := by {intro, ext1, simp [mul_def, inv_def,map.one_def]}, 
  ..map.has_inv }

protected def comm_group [comm_group β] : comm_group (α→ β ) :=
{ ..map.group,
  ..map.comm_semigroup }

protected def add_semigroup [add_semigroup β] : add_semigroup (α → β ) :=
@additive.add_semigroup _ (@map.semigroup _ _  multiplicative.semigroup)

protected def add_comm_semigroup [add_comm_semigroup β] : add_comm_semigroup (α → β ) :=
@additive.add_comm_semigroup _ (@map.comm_semigroup _ _  multiplicative.comm_semigroup)

protected def add_monoid [add_monoid β] : add_monoid (α → β ) :=
@additive.add_monoid _ (@map.monoid _ _  multiplicative.monoid)

protected def add_comm_monoid [add_comm_monoid β] : add_comm_monoid (α → β) :=
@additive.add_comm_monoid _ (@map.comm_monoid _ _ multiplicative.comm_monoid)

protected def add_group [add_group β] : add_group (α → β ) :=
@additive.add_group _ (@map.group _ _  multiplicative.group)

protected def add_comm_group [add_comm_group β] : add_comm_group (α → β ) :=
@additive.add_comm_group _ (@map.comm_group _ _  multiplicative.comm_group)

protected def semiring [semiring β] : semiring (α → β) :=
{    mul           := map.has_mul.mul,
     mul_assoc     := by simp [mul_def, mul_assoc],
     one           := λ x:α, (1:β),
     zero          := λ x:α, (0:β),
     one_mul       := by {intro, ext1, simp [mul_def, map.one_def]},
     mul_one       := by {intro, ext1, simp [mul_def, map.one_def]},
     right_distrib := by {repeat{intro}, ext1, simp [mul_def, add_def, add_mul]},
     left_distrib  := by {repeat{intro}, ext1, simp [mul_def, add_def, mul_add]},
     zero_mul      := by {repeat{intro}, ext1, simp [mul_def, zero_def]},
     mul_zero      := by {repeat{intro}, ext1, simp [mul_def, zero_def]},
     ..map.has_mul ,
     ..map.has_add ,
     ..map.add_comm_monoid  }

protected def comm_semiring [comm_semiring β] : comm_semiring (α → β )  :=
{ ..map.semiring,
  ..map.comm_monoid  }

protected def ring [ring β] : ring (α → β )  :=
{ ..map.semiring,
  ..map.add_comm_group  }

protected def comm_ring [comm_ring β] : comm_ring (α→ β ) :=
{ ..map.comm_monoid,
  ..map.ring  }

protected def mul_action [monoid γ][mul_action γ β] :mul_action γ (α →β ):= 
{ one_smul := by {repeat{intro}, simp[smul_def] },
  mul_smul := by {repeat{intro},ext1, simp[smul_def,mul_smul] },
  ..map.has_scalar} 

instance  add_monoid'[add_monoid β] : add_monoid (α → β) := map.add_monoid

protected def distrib_mul_action [monoid γ] [add_monoid β]   [distrib_mul_action γ β] : distrib_mul_action γ (α → β):=
{ smul_add := by {repeat{intro}, ext1,simp[smul_def,add_def,smul_add ]},
  smul_zero := by {repeat{intro}, ext1,simp only [smul_def], by library_search },
 ..map.mul_action}

instance  add_comm_monoid'[add_comm_monoid β] : add_comm_monoid(α → β) := map.add_comm_monoid

protected def semimodule [semiring γ] [add_comm_monoid β] [semimodule γ β ]: semimodule γ (α → β):=
{  add_smul := by {repeat{intro}, ext1,simp[smul_def,add_def,add_smul ]},
   zero_smul := by {repeat{intro}, ext1,simp only [smul_def], by library_search},
  ..map.distrib_mul_action}

instance  add_comm_group'[add_comm_group β] : add_comm_group(α → β) := map.add_comm_group

protected def module  [ring γ][add_comm_group β ] [module γ β] : module γ (α→ β ) :={..map.semimodule}

protected def vector_space  [discrete_field γ][add_comm_group β ] [vector_space γ β] : vector_space γ (α→ β ) :={..map.semimodule}

end map
