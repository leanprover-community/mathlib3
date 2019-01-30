/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.equiv.basic data.polynomial linear_algebra.multivariate_polynomial

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace equiv

section group
variables [group α]

protected def mul_left (a : α) : α ≃ α :=
{ to_fun    := λx, a * x,
  inv_fun   := λx, a⁻¹ * x,
  left_inv  := assume x, show a⁻¹ * (a * x) = x, from inv_mul_cancel_left a x,
  right_inv := assume x, show a * (a⁻¹ * x) = x, from mul_inv_cancel_left a x }

attribute [to_additive equiv.add_left._proof_1] equiv.mul_left._proof_1
attribute [to_additive equiv.add_left._proof_2] equiv.mul_left._proof_2
attribute [to_additive equiv.add_left] equiv.mul_left

protected def mul_right (a : α) : α ≃ α :=
{ to_fun    := λx, x * a,
  inv_fun   := λx, x * a⁻¹,
  left_inv  := assume x, show (x * a) * a⁻¹ = x, from mul_inv_cancel_right x a,
  right_inv := assume x, show (x * a⁻¹) * a = x, from inv_mul_cancel_right x a }

attribute [to_additive equiv.add_right._proof_1] equiv.mul_right._proof_1
attribute [to_additive equiv.add_right._proof_2] equiv.mul_right._proof_2
attribute [to_additive equiv.add_right] equiv.mul_right

protected def inv (α) [group α] : α ≃ α :=
{ to_fun    := λa, a⁻¹,
  inv_fun   := λa, a⁻¹,
  left_inv  := assume a, inv_inv a,
  right_inv := assume a, inv_inv a }

attribute [to_additive equiv.neg._proof_1] equiv.inv._proof_1
attribute [to_additive equiv.neg._proof_2] equiv.inv._proof_2
attribute [to_additive equiv.neg] equiv.inv

def units_equiv_ne_zero (α : Type*) [field α] : units α ≃ {a : α | a ≠ 0} :=
⟨λ a, ⟨a.1, units.ne_zero _⟩, λ a, units.mk0 _ a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

@[simp] lemma coe_units_equiv_ne_zero [field α] (a : units α) :
  ((units_equiv_ne_zero α a) : α) = a := rfl

end group

section instances

variables (e : α ≃ β)

protected def has_zero [has_zero β] : has_zero α := ⟨e.symm 0⟩
lemma zero_def [has_zero β] : @has_zero.zero _ (equiv.has_zero e) = e.symm 0 := rfl

protected def has_one [has_one β] : has_one α := ⟨e.symm 1⟩
lemma one_def [has_one β] : @has_one.one _ (equiv.has_one e) = e.symm 1 := rfl

protected def has_mul [has_mul β] : has_mul α := ⟨λ x y, e.symm (e x * e y)⟩
lemma mul_def [has_mul β] (x y : α) :
  @has_mul.mul _ (equiv.has_mul e) x y = e.symm (e x * e y) := rfl

protected def has_add [has_add β] : has_add α := ⟨λ x y, e.symm (e x + e y)⟩
lemma add_def [has_add β] (x y : α) :
  @has_add.add _ (equiv.has_add e) x y = e.symm (e x + e y) := rfl

protected def has_inv [has_inv β] : has_inv α := ⟨λ x, e.symm (e x)⁻¹⟩
lemma inv_def [has_inv β] (x : α) : @has_inv.inv _ (equiv.has_inv e) x = e.symm (e x)⁻¹ := rfl

protected def has_neg [has_neg β] : has_neg α := ⟨λ x, e.symm (-e x)⟩
lemma neg_def [has_neg β] (x : α) : @has_neg.neg _ (equiv.has_neg e) x = e.symm (-e x) := rfl

protected def semigroup [semigroup β] : semigroup α :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..equiv.has_mul e }

protected def comm_semigroup [comm_semigroup β] : comm_semigroup α :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..equiv.semigroup e }

protected def monoid [monoid β] : monoid α :=
{ one_mul := by simp [mul_def, one_def],
  mul_one := by simp [mul_def, one_def],
  ..equiv.semigroup e,
  ..equiv.has_one e }

protected def comm_monoid [comm_monoid β] : comm_monoid α :=
{ ..equiv.comm_semigroup e,
  ..equiv.monoid e }

protected def group [group β] : group α :=
{ mul_left_inv := by simp [mul_def, inv_def, one_def],
  ..equiv.monoid e,
  ..equiv.has_inv e }

protected def comm_group [comm_group β] : comm_group α :=
{ ..equiv.group e,
  ..equiv.comm_semigroup e }

protected def add_semigroup [add_semigroup β] : add_semigroup α :=
@additive.add_semigroup _ (@equiv.semigroup _ _ e multiplicative.semigroup)

protected def add_comm_semigroup [add_comm_semigroup β] : add_comm_semigroup α :=
@additive.add_comm_semigroup _ (@equiv.comm_semigroup _ _ e multiplicative.comm_semigroup)

protected def add_monoid [add_monoid β] : add_monoid α :=
@additive.add_monoid _ (@equiv.monoid _ _ e multiplicative.monoid)

protected def add_comm_monoid [add_comm_monoid β] : add_comm_monoid α :=
@additive.add_comm_monoid _ (@equiv.comm_monoid _ _ e multiplicative.comm_monoid)

protected def add_group [add_group β] : add_group α :=
@additive.add_group _ (@equiv.group _ _ e multiplicative.group)

protected def add_comm_group [add_comm_group β] : add_comm_group α :=
@additive.add_comm_group _ (@equiv.comm_group _ _ e multiplicative.comm_group)

protected def semiring [semiring β] : semiring α :=
{ right_distrib := by simp [mul_def, add_def, add_mul],
  left_distrib := by simp [mul_def, add_def, mul_add],
  zero_mul := by simp [mul_def, zero_def],
  mul_zero := by simp [mul_def, zero_def],
  ..equiv.has_zero e,
  ..equiv.has_mul e,
  ..equiv.has_add e,
  ..equiv.monoid e,
  ..equiv.add_comm_monoid e }

protected def comm_semiring [comm_semiring β] : comm_semiring α :=
{ ..equiv.semiring e,
  ..equiv.comm_monoid e }

protected def ring [ring β] : ring α :=
{ ..equiv.semiring e,
  ..equiv.add_comm_group e }

protected def comm_ring [comm_ring β] : comm_ring α :=
{ ..equiv.comm_monoid e,
  ..equiv.ring e }

protected def zero_ne_one_class [zero_ne_one_class β] : zero_ne_one_class α :=
{ zero_ne_one := by simp [zero_def, one_def],
  ..equiv.has_zero e,
  ..equiv.has_one e }

protected def nonzero_comm_ring [nonzero_comm_ring β] : nonzero_comm_ring α :=
{ ..equiv.zero_ne_one_class e,
  ..equiv.comm_ring e }

protected def domain [domain β] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by simp [mul_def, zero_def, equiv.eq_symm_apply],
  ..equiv.has_zero e,
  ..equiv.zero_ne_one_class e,
  ..equiv.has_mul e,
  ..equiv.ring e }

protected def integral_domain [integral_domain β] : integral_domain α :=
{ ..equiv.domain e,
  ..equiv.nonzero_comm_ring e }

protected def division_ring [division_ring β] : division_ring α :=
{ inv_mul_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact inv_mul_cancel,
  mul_inv_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact mul_inv_cancel,
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.domain e,
  ..equiv.has_inv e }

protected def field [field β] : field α :=
{ ..equiv.integral_domain e,
  ..equiv.division_ring e }

protected def discrete_field [discrete_field β] : discrete_field α :=
{ has_decidable_eq := equiv.decidable_eq e,
  inv_zero := by simp [mul_def, inv_def, zero_def],
  ..equiv.has_mul e,
  ..equiv.has_inv e,
  ..equiv.has_zero e,
  ..equiv.field e }

end instances
end equiv

structure ring_equiv (α β : Type*) [ring α] [ring β] extends α ≃ β :=
(hom : is_ring_hom to_fun)

infix ` ≃r `:50 := ring_equiv

namespace ring_equiv

variables [ring α] [ring β] [ring γ]

instance {e : α ≃r β} : is_ring_hom e.to_equiv := hom _

protected def refl (α : Type*) [ring α] : α ≃r α :=
{ hom := is_ring_hom.id, .. equiv.refl α }

protected def symm {α β : Type*} [ring α] [ring β] (e : α ≃r β) : β ≃r α :=
{ hom := ⟨(equiv.symm_apply_eq _).2 e.hom.1.symm,
    λ x y, (equiv.symm_apply_eq _).2 $ show _ = e.to_equiv.to_fun _, by rw [e.2.2, e.1.4, e.1.4],
    λ x y, (equiv.symm_apply_eq _).2 $ show _ = e.to_equiv.to_fun _, by rw [e.2.3, e.1.4, e.1.4]⟩,
  .. e.to_equiv.symm }

protected def trans {α β γ : Type*} [ring α] [ring β] [ring γ]
  (e₁ : α ≃r β) (e₂ : β ≃r γ) : α ≃r γ :=
{ hom := is_ring_hom.comp _ _, .. e₁.1.trans e₂.1  }

end ring_equiv

namespace mv_polynomial

variables (α) [comm_ring α]
variables [decidable_eq α] [decidable_eq β] [decidable_eq γ] [decidable_eq δ]

def pempty_ring_equiv : mv_polynomial pempty α ≃r α :=
{ to_fun    := mv_polynomial.eval₂ id $ pempty.elim,
  inv_fun   := C,
  left_inv  := is_id _ (by apply_instance) (assume a, by rw [eval₂_C]; refl) (assume a, a.elim),
  right_inv := λ r, eval₂_C _ _ _,
  hom       := eval₂.is_ring_hom _ _ }

def punit_ring_equiv : mv_polynomial punit α ≃r polynomial α :=
{ to_fun    := eval₂ polynomial.C (λu:punit, polynomial.X),
  inv_fun   := polynomial.eval₂ mv_polynomial.C (X punit.star),
  left_inv  :=
    begin
      refine is_id _ _ _ _,
      apply is_semiring_hom.comp (eval₂ polynomial.C (λu:punit, polynomial.X)) _; apply_instance,
      { assume a, rw [eval₂_C, polynomial.eval₂_C] },
      { rintros ⟨⟩, rw [eval₂_X, polynomial.eval₂_X] }
    end,
  right_inv := assume p, polynomial.induction_on p
    (assume a, by rw [polynomial.eval₂_C, mv_polynomial.eval₂_C])
    (assume p q hp hq, by rw [polynomial.eval₂_add, mv_polynomial.eval₂_add, hp, hq])
    (assume p n hp,
      by rw [polynomial.eval₂_mul, polynomial.eval₂_pow, polynomial.eval₂_X, polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]),
  hom       := eval₂.is_ring_hom _ _ }

def ring_equiv_of_equiv (e : β ≃ γ) : mv_polynomial β α ≃r mv_polynomial γ α :=
{ to_fun    := rename e,
  inv_fun   := rename e.symm,
  left_inv  := λ p, by simp only [rename_rename, (∘), e.inverse_apply_apply]; exact rename_id p,
  right_inv := λ p, by simp only [rename_rename, (∘), e.apply_inverse_apply]; exact rename_id p,
  hom       := rename.is_ring_hom e }

def ring_equiv_congr [comm_ring γ] (e : α ≃r γ) : mv_polynomial β α ≃r mv_polynomial β γ :=
{ to_fun    := map e.to_fun,
  inv_fun   := map e.symm.to_fun,
  left_inv  := assume p,
    have (e.symm.to_equiv.to_fun ∘ e.to_equiv.to_fun) = id,
    { ext a, exact e.to_equiv.inverse_apply_apply a },
    by simp only [map_map, this, map_id],
  right_inv := assume p,
    have (e.to_equiv.to_fun ∘ e.symm.to_equiv.to_fun) = id,
    { ext a, exact e.to_equiv.apply_inverse_apply a },
    by simp only [map_map, this, map_id],
  hom       := map.is_ring_hom e.to_fun }

section
variables (β γ δ)

instance ring_on_sum : ring (mv_polynomial (β ⊕ γ) α) := by apply_instance
instance ring_on_iter : ring (mv_polynomial β (mv_polynomial γ α)) := by apply_instance

def sum_to_iter : mv_polynomial (β ⊕ γ) α → mv_polynomial β (mv_polynomial γ α) :=
eval₂ (C ∘ C) (λbc, sum.rec_on bc X (C ∘ X))

instance is_semiring_hom_C_C :
  is_semiring_hom (C ∘ C : α → mv_polynomial β (mv_polynomial γ α)) :=
@is_semiring_hom.comp _ _ _ _ C mv_polynomial.is_semiring_hom _ _ C mv_polynomial.is_semiring_hom

instance is_semiring_hom_sum_to_iter : is_semiring_hom (sum_to_iter α β γ) :=
eval₂.is_semiring_hom _ _

lemma sum_to_iter_C (a : α) : sum_to_iter α β γ (C a) = C (C a) :=
eval₂_C _ _ a

lemma sum_to_iter_Xl (b : β) : sum_to_iter α β γ (X (sum.inl b)) = X b :=
eval₂_X _ _ (sum.inl b)

lemma sum_to_iter_Xr (c : γ) : sum_to_iter α β γ (X (sum.inr c)) = C (X c) :=
eval₂_X _ _ (sum.inr c)

def iter_to_sum : mv_polynomial β (mv_polynomial γ α) → mv_polynomial (β ⊕ γ) α :=
eval₂ (eval₂ C (X ∘ sum.inr)) (X ∘ sum.inl)

section

instance is_semiring_hom_iter_to_sum : is_semiring_hom (iter_to_sum α β γ) :=
eval₂.is_semiring_hom _ _

end

lemma iter_to_sum_C_C (a : α) : iter_to_sum α β γ (C (C a)) = C a :=
eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

lemma iter_to_sum_X (b : β) : iter_to_sum α β γ (X b) = X (sum.inl b) :=
eval₂_X _ _ _

lemma iter_to_sum_C_X (c : γ) : iter_to_sum α β γ (C (X c)) = X (sum.inr c) :=
eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

def mv_polynomial_equiv_mv_polynomial [comm_ring δ]
  (f : mv_polynomial β α → mv_polynomial γ δ) (hf : is_semiring_hom f)
  (g : mv_polynomial γ δ → mv_polynomial β α) (hg : is_semiring_hom g)
  (hfgC : ∀a, f (g (C a)) = C a)
  (hfgX : ∀n, f (g (X n)) = X n)
  (hgfC : ∀a, g (f (C a)) = C a)
  (hgfX : ∀n, g (f (X n)) = X n) :
  mv_polynomial β α ≃r mv_polynomial γ δ :=
{ to_fun    := f, inv_fun := g,
  left_inv  := is_id _ (is_semiring_hom.comp _ _) hgfC hgfX,
  right_inv := is_id _ (is_semiring_hom.comp _ _) hfgC hfgX,
  hom       := is_ring_hom.of_semiring f }

def sum_ring_equiv : mv_polynomial (β ⊕ γ) α ≃r mv_polynomial β (mv_polynomial γ α) :=
begin
  apply @mv_polynomial_equiv_mv_polynomial α (β ⊕ γ) _ _ _ _ _ _ _ _
    (sum_to_iter α β γ) _ (iter_to_sum α β γ) _,
  { assume p,
    apply @hom_eq_hom _ _ _ _ _ _ _ _ _ _ _ _ _ p,
    apply_instance,
    { apply @is_semiring_hom.comp _ _ _ _ _ _ _ _ _ _,
      apply_instance,
      apply @is_semiring_hom.comp _ _ _ _ _ _ _ _ _ _,
      apply_instance,
      { apply @mv_polynomial.is_semiring_hom },
      { apply mv_polynomial.is_semiring_hom_iter_to_sum α β γ },
      { apply mv_polynomial.is_semiring_hom_sum_to_iter α β γ } },
    { apply mv_polynomial.is_semiring_hom },
    { assume a, rw [iter_to_sum_C_C α β γ, sum_to_iter_C α β γ] },
    { assume c, rw [iter_to_sum_C_X α β γ, sum_to_iter_Xr α β γ] } },
  { assume b, rw [iter_to_sum_X α β γ, sum_to_iter_Xl α β γ] },
  { assume a, rw [sum_to_iter_C α β γ, iter_to_sum_C_C α β γ] },
  { assume n, cases n with b c,
    { rw [sum_to_iter_Xl, iter_to_sum_X] },
    { rw [sum_to_iter_Xr, iter_to_sum_C_X] } },
  { apply mv_polynomial.is_semiring_hom_sum_to_iter α β γ },
  { apply mv_polynomial.is_semiring_hom_iter_to_sum α β γ }
end

instance option_ring : ring (mv_polynomial (option β) α) :=
mv_polynomial.ring

instance polynomial_ring : ring (polynomial (mv_polynomial β α)) :=
@comm_ring.to_ring _ polynomial.comm_ring

instance polynomial_ring2 : ring (mv_polynomial β (polynomial α)) :=
by apply_instance

def option_equiv_left : mv_polynomial (option β) α ≃r polynomial (mv_polynomial β α) :=
(ring_equiv_of_equiv α $ (equiv.option_equiv_sum_punit β).trans (equiv.sum_comm _ _)).trans $
(sum_ring_equiv α _ _).trans $
punit_ring_equiv _

def option_equiv_right : mv_polynomial (option β) α ≃r mv_polynomial β (polynomial α) :=
(ring_equiv_of_equiv α $ equiv.option_equiv_sum_punit.{0} β).trans $
(sum_ring_equiv α β unit).trans $
ring_equiv_congr (mv_polynomial unit α) (punit_ring_equiv α)

end

end mv_polynomial
