/-
Copyright (c) 2019 Hoang Le Truong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hoang Le Truong.

If α is a semigroup, a comm_semigroup, a comm_monoid,a add_semigroup, a add_comm_semigroup, a add_comm_monoid, a mul_action, 
a distrib_mul_action, so is roption α. 
-/

import   algebra.module data.pfun

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} 

namespace roption
noncomputable theory

instance [has_zero α] : has_zero (roption α) := ⟨some (0:α)⟩
@[simp] lemma zero_def [has_zero α] : (0 : roption α ) = ⟨true, λ _, (0:α)⟩ := rfl

instance [has_one α] :  has_one (roption α)  :=⟨some (1:α)⟩
@[simp] lemma one_def [has_one α] : (1 : roption α) = ⟨true, λ _, (1:α)⟩ := rfl

attribute [to_additive roption.has_zero] roption.has_one
attribute [to_additive roption.zero_def] roption.one_def

instance [has_add α] : has_add (roption α) := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, x.get (h.1)+ y.get (h.2)⟩⟩
@[simp] lemma add_def [has_add α] (x y : roption α) : x+y = ⟨x.dom ∧ y.dom, λ h, x.get (h.1)+ y.get (h.2)  ⟩ := rfl

instance [has_mul α] : has_mul (roption α) := ⟨λ x y, ⟨x.dom ∧  y.dom, λ h, x.get (h.1) * y.get (h.2)⟩⟩
@[simp] lemma mul_def  [has_mul α] (x y : roption α) : x * y = ⟨x.dom ∧ y.dom , λ h,  x.get (h.1) * y.get (h.2)⟩ := rfl

attribute [to_additive roption.has_add] roption.has_mul
attribute [to_additive roption.add_def] roption.mul_def

instance [has_neg α] : has_neg (roption α) := ⟨λ x, ⟨x.dom , λ h, -x.get h⟩⟩
@[simp] lemma neg_def [has_neg α] (x : roption α) : - x = ⟨x.dom , λ h, - x.get h⟩ := rfl

instance [has_inv α] : has_inv (roption α) := ⟨λ x, ⟨x.dom , λ h, (x.get h)⁻¹⟩⟩
@[simp] lemma inv_def [has_inv α ] (x : roption α) : x⁻¹ = ⟨x.dom , λ h, (x.get h)⁻¹⟩ := rfl

attribute [to_additive roption.has_neg] roption.has_inv
attribute [to_additive roption.neg_def] roption.inv_def

instance [has_scalar α β] : has_scalar α (roption β) := ⟨λ a f, ⟨f.dom, λ h, a • (f.get h)⟩⟩
@[simp] lemma smul_def [has_scalar α β] (a:α) (x: roption β) : a • x = ⟨x.dom , λ h, a • x.get h⟩ := rfl

instance [semigroup α] : semigroup (roption α) :=
{ mul_assoc := λ x y z, roption.ext' and.assoc (λ _ _, mul_assoc _ _ _),
  ..roption.has_mul}

instance [comm_semigroup α ] : comm_semigroup (roption α) :=
{ mul_comm := λ x y, roption.ext' and.comm (λ _ _, mul_comm _ _)
  ..roption.semigroup}


instance [monoid α ] : monoid (roption α) :=
{ monoid.
   mul       := roption.has_mul.mul,
   mul_assoc := λ x y z, roption.ext' and.assoc (λ _ _, mul_assoc _ _ _),
   one       := some(1:α),
   one_mul   := λ x, roption.ext' (true_and _) (λ _ _, one_mul _),
   mul_one   := λ x, roption.ext' (and_true _) (λ _ _, mul_one _)}

instance [comm_monoid α] : comm_monoid (roption α) :=
{ ..roption.comm_semigroup,
  ..roption.monoid}

instance [add_semigroup α] : add_semigroup (roption α) :=
{ add_assoc  := λ x y z, roption.ext' and.assoc (λ _ _, add_assoc _ _ _)
  ..roption.has_add}

instance [add_comm_semigroup α] : add_comm_semigroup (roption α) :=
{ add_comm := λ x y, roption.ext' and.comm (λ _ _, add_comm _ _)
  ..roption.add_semigroup}

instance [add_monoid α] : add_monoid (roption α) :=
{ add_monoid.
  add       := roption.has_add.add,
  add_assoc := λ x y z, roption.ext' and.assoc (λ _ _, add_assoc _ _ _),
  zero      := roption.has_zero.zero,
  zero_add  := λ x, roption.ext' (true_and _) (λ _ _, zero_add _),
  add_zero  := λ x, roption.ext' (and_true _) (λ _ _,add_zero _)}

instance [add_comm_monoid α] : add_comm_monoid (roption α) :=
{ add_comm := λ x y, roption.ext' and.comm (λ _ _, add_comm _ _),
  ..roption.add_monoid}

instance [monoid β] [mul_action β α] : mul_action β (roption α) := 
{ one_smul := λ x, roption.ext' (by simp[one_def,smul_def]) (by { intros, simp[smul_def,one_def,one_smul]}),
  mul_smul :=  λ a b x, roption.ext'  (by simp[smul_def] ) (by { intros, simp[smul_def,mul_smul]}) ,
  ..roption.has_scalar} 

instance [monoid β] [add_monoid α] [distrib_mul_action β α] : distrib_mul_action β (roption α) :=
{ smul_add   := λ a x y, roption.ext' (by simp[add_def,smul_def] ) (by{ intros, simp[smul_def,add_def,smul_add]}),
  smul_zero  := λ x, roption.ext' (by simp[zero_def,smul_def]) (by{ intros, simp[smul_def,zero_def,smul_zero]}),
  ..roption.mul_action}

end roption
