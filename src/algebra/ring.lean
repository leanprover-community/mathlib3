/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import algebra.group data.set.basic

universes u v
variable {α : Type u}

section
variable [semiring α]

theorem mul_two (n : α) : n * 2 = n + n :=
(left_distrib n 1 1).trans (by simp)

theorem bit0_eq_two_mul (n : α) : bit0 n = 2 * n :=
(two_mul _).symm

variable (α)
lemma zero_ne_one_or_forall_eq_0 : (0 : α) ≠ 1 ∨ (∀a:α, a = 0) :=
by haveI := classical.dec;
   refine not_or_of_imp (λ h a, _); simpa using congr_arg ((*) a) h.symm

lemma eq_zero_of_zero_eq_one (h : (0 : α) = 1) : (∀a:α, a = 0) :=
(zero_ne_one_or_forall_eq_0 α).neg_resolve_left h

theorem subsingleton_of_zero_eq_one (h : (0 : α) = 1) : subsingleton α :=
⟨λa b, by rw [eq_zero_of_zero_eq_one α h a, eq_zero_of_zero_eq_one α h b]⟩

end

namespace units
variables [ring α] {a b : α}

instance : has_neg (units α) := ⟨λu, ⟨-↑u, -↑u⁻¹, by simp, by simp⟩ ⟩

@[simp] protected theorem coe_neg (u : units α) : (↑-u : α) = -u := rfl

@[simp] protected theorem neg_inv (u : units α) : (-u)⁻¹ = -u⁻¹ := rfl

@[simp] protected theorem neg_neg (u : units α) : - -u = u :=
units.ext $ neg_neg _

@[simp] protected theorem neg_mul (u₁ u₂ : units α) : -u₁ * u₂ = -(u₁ * u₂) :=
units.ext $ neg_mul_eq_neg_mul_symm _ _

@[simp] protected theorem mul_neg (u₁ u₂ : units α) : u₁ * -u₂ = -(u₁ * u₂) :=
units.ext $ (neg_mul_eq_mul_neg _ _).symm

@[simp] protected theorem neg_mul_neg (u₁ u₂ : units α) : -u₁ * -u₂ = u₁ * u₂ := by simp

protected theorem neg_eq_neg_one_mul (u : units α) : -u = -1 * u := by simp

end units

instance [semiring α] : semiring (with_zero α) :=
{ left_distrib := λ a b c, begin
    cases a with a, {refl},
    cases b with b; cases c with c; try {refl},
    exact congr_arg some (left_distrib _ _ _)
  end,
  right_distrib := λ a b c, begin
    cases c with c,
    { change (a + b) * 0 = a * 0 + b * 0, simp },
    cases a with a; cases b with b; try {refl},
    exact congr_arg some (right_distrib _ _ _)
  end,
  ..with_zero.add_comm_monoid,
  ..with_zero.mul_zero_class,
  ..with_zero.monoid }

attribute [refl] dvd_refl
attribute [trans] dvd.trans

class is_semiring_hom {α : Type u} {β : Type v} [semiring α] [semiring β] (f : α → β) : Prop :=
(map_zero : f 0 = 0)
(map_one : f 1 = 1)
(map_add : ∀ {x y}, f (x + y) = f x + f y)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)

namespace is_semiring_hom

variables {β : Type v} [semiring α] [semiring β]
variables (f : α → β) [is_semiring_hom f] {x y : α}

instance id : is_semiring_hom (@id α) := by refine {..}; intros; refl

instance comp {γ} [semiring γ] (g : β → γ) [is_semiring_hom g] :
  is_semiring_hom (g ∘ f) :=
{ map_zero := by simp [map_zero f]; exact map_zero g,
  map_one := by simp [map_one f]; exact map_one g,
  map_add := λ x y, by simp [map_add f]; rw map_add g; refl,
  map_mul := λ x y, by simp [map_mul f]; rw map_mul g; refl }

instance : is_add_monoid_hom f :=
{ ..‹is_semiring_hom f› }

instance : is_monoid_hom f :=
{ ..‹is_semiring_hom f› }

end is_semiring_hom

section
  variables [ring α] (a b c d e : α)

  lemma mul_neg_one (a : α) : a * -1 = -a := by simp

  lemma neg_one_mul (a : α) : -1 * a = -a := by simp

  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp
      ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin simp [h] end) (λ h,
                                                    begin simp [h.symm] end)
      ... ↔ (a - b) * e + c = d   : begin simp [@sub_eq_add_neg α, @right_distrib α] end

  theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
  assume h,
  calc
    (a - b) * e + c = (a * e + c) - b * e : begin simp [@sub_eq_add_neg α, @right_distrib α] end
                ... = d                   : begin rw h, simp [@add_sub_cancel α] end

  theorem ne_zero_and_ne_zero_of_mul_ne_zero {a b : α} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  begin
    split,
    { intro ha, apply h, simp [ha] },
    { intro hb, apply h, simp [hb] }
  end

end

@[simp] lemma zero_dvd_iff [comm_semiring α] {a : α} : 0 ∣ a ↔ a = 0 :=
⟨eq_zero_of_zero_dvd, λ h, by rw h⟩

section comm_ring
  variable [comm_ring α]

  @[simp] lemma dvd_neg (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

  @[simp] lemma neg_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

  theorem dvd_add_left {a b c : α} (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  (dvd_add_iff_left h).symm

  theorem dvd_add_right {a b c : α} (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
  (dvd_add_iff_right h).symm

end comm_ring

class is_ring_hom {α : Type u} {β : Type v} [ring α] [ring β] (f : α → β) : Prop :=
(map_one : f 1 = 1)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_add : ∀ {x y}, f (x + y) = f x + f y)

namespace is_ring_hom

variables {β : Type v} [ring α] [ring β]

def of_semiring (f : α → β) [H : is_semiring_hom f] : is_ring_hom f := {..H}

variables (f : α → β) [is_ring_hom f] {x y : α}

lemma map_zero : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [map_add f]; simp
     ... = 0 : by simp

lemma map_neg : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [map_add f]; simp
        ... = -f x : by simp [map_zero f]

lemma map_sub : f (x - y) = f x - f y :=
by simp [map_add f, map_neg f]

instance id : is_ring_hom (@id α) := by refine {..}; intros; refl

instance comp {γ} [ring γ] (g : β → γ) [is_ring_hom g] :
  is_ring_hom (g ∘ f) :=
{ map_add := λ x y, by simp [map_add f]; rw map_add g; refl,
  map_mul := λ x y, by simp [map_mul f]; rw map_mul g; refl,
  map_one := by simp [map_one f]; exact map_one g }

instance : is_semiring_hom f :=
{ map_zero := map_zero f, ..‹is_ring_hom f› }

instance : is_add_group_hom f :=
⟨λ _ _, map_add f⟩

end is_ring_hom

set_option old_structure_cmd true

class nonzero_comm_semiring (α : Type*) extends comm_semiring α, zero_ne_one_class α

class nonzero_comm_ring (α : Type*) extends comm_ring α, zero_ne_one_class α

instance nonzero_comm_ring.to_nonzero_comm_semiring {α : Type*} [I : nonzero_comm_ring α] :
  nonzero_comm_semiring α :=
{ zero_ne_one := by convert zero_ne_one,
  ..show comm_semiring α, by apply_instance }

instance integral_domain.to_nonzero_comm_ring (α : Type*) [id : integral_domain α] :
  nonzero_comm_ring α :=
{ ..id }

lemma units.coe_ne_zero [nonzero_comm_semiring α] (u : units α) : (u : α) ≠ 0 :=
λ h : u.1 = 0, by simpa [h, zero_ne_one] using u.3

def nonzero_comm_ring.of_ne [comm_ring α] {x y : α} (h : x ≠ y) : nonzero_comm_ring α :=
{ one := 1,
  zero := 0,
  zero_ne_one := λ h01, h $ by rw [← one_mul x, ← one_mul y, ← h01, zero_mul, zero_mul],
  ..show comm_ring α, by apply_instance }

def nonzero_comm_semiring.of_ne [comm_semiring α] {x y : α} (h : x ≠ y) : nonzero_comm_semiring α :=
{ one := 1,
  zero := 0,
  zero_ne_one := λ h01, h $ by rw [← one_mul x, ← one_mul y, ← h01, zero_mul, zero_mul],
  ..show comm_semiring α, by apply_instance }

/-- A domain is a ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`. Alternatively, a domain
  is an integral domain without assuming commutativity of multiplication. -/
class domain (α : Type u) extends ring α, no_zero_divisors α, zero_ne_one_class α

section domain
  variable [domain α]

  @[simp] theorem mul_eq_zero {a b : α} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, λo,
    or.elim o (λh, by rw h; apply zero_mul) (λh, by rw h; apply mul_zero)⟩

  @[simp] theorem zero_eq_mul {a b : α} : 0 = a * b ↔ a = 0 ∨ b = 0 :=
  by rw [eq_comm, mul_eq_zero]

  theorem mul_ne_zero' {a b : α} (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a * b ≠ 0 :=
  λ h, or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) h₁ h₂

  theorem domain.mul_right_inj {a b c : α} (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
  by rw [← sub_eq_zero, ← mul_sub_right_distrib, mul_eq_zero];
     simp [ha]; exact sub_eq_zero

  theorem domain.mul_left_inj {a b c : α} (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  by rw [← sub_eq_zero, ← mul_sub_left_distrib, mul_eq_zero];
     simp [ha]; exact sub_eq_zero

  theorem eq_zero_of_mul_eq_self_right' {a b : α} (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  by apply (mul_eq_zero.1 _).resolve_right (sub_ne_zero.2 h₁);
     rw [mul_sub_left_distrib, mul_one, sub_eq_zero, h₂]

  theorem eq_zero_of_mul_eq_self_left' {a b : α} (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  by apply (mul_eq_zero.1 _).resolve_left (sub_ne_zero.2 h₁);
     rw [mul_sub_right_distrib, one_mul, sub_eq_zero, h₂]

  theorem mul_ne_zero_comm' {a b : α} (h : a * b ≠ 0) : b * a ≠ 0 :=
  mul_ne_zero' (ne_zero_of_mul_ne_zero_left h) (ne_zero_of_mul_ne_zero_right h)

end domain

/- integral domains -/

section
  variables [s : integral_domain α] (a b c d e : α)
  include s

  instance integral_domain.to_domain : domain α := {..s}

  theorem eq_of_mul_eq_mul_right_of_ne_zero {a b c : α} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have b * a - c * a = 0, by simp [h],
  have (b - c) * a = 0, by rw [mul_sub_right_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
  eq_of_sub_eq_zero this

  theorem eq_of_mul_eq_mul_left_of_ne_zero {a b c : α} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, by simp [h],
  have a * (b - c) = 0, by rw [mul_sub_left_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
  eq_of_sub_eq_zero this

  theorem mul_dvd_mul_iff_left {a b c : α} (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr $ λ d, by rw [mul_assoc, domain.mul_left_inj ha]

  theorem mul_dvd_mul_iff_right {a b c : α} (hc : c ≠ 0) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr $ λ d, by rw [mul_right_comm, domain.mul_right_inj hc]

  lemma units.inv_eq_self_iff (u : units α) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
  by conv {to_lhs, rw [inv_eq_iff_mul_eq_one, ← mul_one (1 : units α), units.ext_iff, units.coe_mul,
    units.coe_mul, mul_self_eq_mul_self_iff, ← units.ext_iff, ← units.coe_neg, ← units.ext_iff] }

end

/- units in various rings -/

namespace units

section comm_semiring
variables [comm_semiring α] (a b : α) (u : units α)

@[simp] lemma coe_dvd : ↑u ∣ a := ⟨↑u⁻¹ * a, by simp⟩

@[simp] lemma dvd_coe_mul : a ∣ b * u ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, units.mul_inv_cancel_right]⟩)
  (assume ⟨c, eq⟩, eq.symm ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _)

@[simp] lemma dvd_coe : a ∣ ↑u ↔ a ∣ 1 :=
suffices a ∣ 1 * ↑u ↔ a ∣ 1, by simpa,
dvd_coe_mul _ _ _

@[simp] lemma coe_mul_dvd : a * u ∣ b ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u, eq.symm ▸ by ac_refl⟩)
  (assume h, suffices a * ↑u ∣ b * 1, by simpa, mul_dvd_mul h (coe_dvd _ _))

end comm_semiring

section domain
variables [domain α]

@[simp] theorem ne_zero : ∀(u : units α), (↑u : α) ≠ 0
| ⟨u, v, (huv : 0 * v = 1), hvu⟩ rfl := by simpa using huv

end domain

end units
