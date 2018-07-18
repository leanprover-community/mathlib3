import data.set.finite group_theory.coset

universes u v
variables {α : Type u} {β : Type v} [group α]

class is_group_action (f : α → β → β) : Prop :=
(one : ∀ a : β, f (1 : α) a = a)
(mul : ∀ (x y : α) (a : β), f (x * y) a = f x (f y a))

namespace is_group_action

variables (f : α → β → β) [is_group_action f] 

@[simp] lemma one_apply (a : β) : f 1 a = a := is_group_action.one f a

lemma mul_apply (x y : α) (a : β) : f (x * y) a = f x (f y a) := is_group_action.mul _ _ _ _

lemma bijective (g : α) : function.bijective (f g) :=
function.bijective_iff_has_inverse.2 ⟨f (g⁻¹), 
  λ a, by rw [← mul_apply f, inv_mul_self, one_apply f],
  λ a, by rw [← mul_apply f, mul_inv_self, one_apply f]⟩ 

def orbit (a : β) := set.range (λ x : α, f x a)

lemma mem_orbit_iff {f : α → β → β} [is_group_action f] {a b : β} :
  b ∈ orbit f a ↔ ∃ x : α, f x a = b :=
iff.rfl

@[simp] lemma mem_orbit (a : β) (x : α) :
  f x a ∈ orbit f a :=
⟨x, rfl⟩

@[simp] lemma mem_orbit_self (a : β) :
  a ∈ orbit f a :=
⟨1, show f 1 a = a, by simp [one_apply f]⟩

lemma orbit_eq_iff {f : α → β → β} [is_group_action f] {a b : β} : 
  a ∈ orbit f b ↔ orbit f a = orbit f b :=
⟨λ ⟨x, (hx : f x b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : f y a = c)⟩, ⟨y * x,
  show f (y * x) b = c, by rwa [mul_apply f, hx]⟩,
λ ⟨y, (hy : f y b = c)⟩, ⟨y * x⁻¹,
  show f (y * x⁻¹) a = c, by
    conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
      mul_apply f, hx]}⟩⟩), λ h, h ▸ mem_orbit_self _ _⟩

instance orbit_fintype (a : β) [fintype α] [decidable_eq β] :
fintype (orbit f a) := set.fintype_range _

def stabilizer (a : β) : set α :=
{x : α | f x a = a}

lemma mem_stabilizer_iff {f : α → β → β} [is_group_action f] {a : β} {x : α} :
  x ∈ stabilizer f a ↔ f x a = a :=
iff.rfl

instance (a : β) : is_subgroup (stabilizer f a) :=
{ one_mem := one_apply _ _,
  mul_mem := λ x y (hx : f x a = a) (hy : f y a = a),
    show f (x * y) a = a, by rw mul_apply f; simp *,
  inv_mem := λ x (hx : f x a = a), show f x⁻¹ a = a,
    by rw [← hx, ← mul_apply f, inv_mul_self, one_apply f, hx] }

noncomputable lemma orbit_equiv_left_cosets (a : β) :
  orbit f a ≃ left_cosets (stabilizer f a) :=
by letI := left_rel (stabilizer f a); exact
equiv.symm (@equiv.of_bijective _ _ 
  (λ x : left_cosets (stabilizer f a), quotient.lift_on x 
    (λ x, (⟨f x a, mem_orbit _ _ _⟩ : orbit f a)) 
    (λ g h (H : _ = _), subtype.eq $ (is_group_action.bijective f (g⁻¹)).1
      $ show f g⁻¹ (f g a) = f g⁻¹ (f h a),
      by rw [← mul_apply f, ← mul_apply f, H, inv_mul_self, one_apply f])) 
⟨λ g h, quotient.induction_on₂ g h (λ g h H, quotient.sound $
  have H : f g a = f h a := subtype.mk.inj H, 
  show f (g⁻¹ * h) a = a,
  by rw [mul_apply f, ← H, ← mul_apply f, inv_mul_self, one_apply f]), 
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨⟦g⟧, subtype.eq hgb⟩⟩)

def fixed_points : set β := {a : β | ∀ x, x ∈ stabilizer f a}

lemma mem_fixed_points {f : α → β → β} [is_group_action f] {a : β} :
  a ∈ fixed_points f ↔ ∀ x : α, f x a = a := iff.rfl

lemma mem_fixed_points' {f : α → β → β} [is_group_action f] {a : β} : a ∈ fixed_points f ↔
  (∀ b, b ∈ orbit f a → b = a) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, mem_stabilizer_iff.2 (h _ (mem_orbit _ _ _))⟩

end is_group_action