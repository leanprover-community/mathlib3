/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import algebra.group tactic data.set.basic

universe u
variable {α : Type u}

section
  variable [semiring α]

  theorem mul_two (n : α) : n * 2 = n + n :=
  (left_distrib n 1 1).trans (by simp)
  
  theorem bit0_eq_two_mul (n : α) : bit0 n = 2 * n :=
  (two_mul _).symm
end

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
                ... = d                   : begin rewrite h, simp [@add_sub_cancel α] end

  theorem ne_zero_and_ne_zero_of_mul_ne_zero {a b : α} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  begin
    split,
    { intro ha, apply h, simp [ha] },
    { intro hb, apply h, simp [hb] }
  end

end

section comm_ring
  variable [comm_ring α]

  @[simp] lemma dvd_neg (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

  @[simp] lemma neg_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩
end comm_ring

def is_unit {α : Type u} [comm_ring α] (x : α) := ∃ y, x * y = 1
def nonunits (α : Type u) [comm_ring α] : set α := { x | ¬∃ y, x * y = 1 }

class is_hom {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) : Prop :=
(map_add : ∀ {x y}, f (x + y) = f x + f y)
(map_mul : ∀ {x y}, f (x * y) = f x * f y)
(map_one : f 1 = 1)

namespace is_hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_hom f] {x y : α}

attribute [simp] map_add
attribute [simp] map_mul
attribute [simp] map_one

@[simp] lemma map_zero : f 0 = 0 :=
calc f 0 = f (0 + 0) - f 0 : by rw [map_add f]; simp
     ... = 0 : by simp

@[simp] lemma map_neg : f (-x) = -f x :=
calc f (-x) = f (-x + x) - f x : by rw [map_add f]; simp
        ... = -f x : by simp [map_zero f]

@[simp] lemma map_sub : f (x - y) = f x - f y :=
by simp [map_add f, map_neg f]

end is_hom

class is_ideal (α : Type u) [comm_ring α] (S : set α) : Prop :=
(zero_mem : (0 : α) ∈ S)
(add_mem : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → x * y ∈ S)

namespace is_ideal

variables {α : Type u} [comm_ring α] {S : set α} [is_ideal α S] {x y z : α}
include S

attribute [simp] zero_mem

lemma neg_mem : x ∈ S → -x ∈ S :=
λ hx, have h : x * -1 ∈ S, from is_ideal.mul_mem hx, by simpa using h

lemma sub_mem : x ∈ S → y ∈ S → x - y ∈ S :=
λ hx hy, have h : x + -y ∈ S, from add_mem hx $ neg_mem hy, by simpa using h

lemma mem_of_mem_of_add_mem : x ∈ S → x + y ∈ S → y ∈ S :=
λ hx hxy, calc
    y = y + x - x : eq.symm $ add_sub_cancel y x
  ... = x + y - x : congr_arg (λ z, z - x) $ add_comm y x
  ... ∈ S : sub_mem hxy hx

lemma mem_of_mem_of_add_mem' : y ∈ S → x + y ∈ S → x ∈ S :=
λ hy hxy, calc
    x = x + y - y : eq.symm $ add_sub_cancel x y
  ... ∈ S : sub_mem hxy hy

lemma mem_of_mem_of_sub_mem : x ∈ S → x - y ∈ S → y ∈ S :=
λ hx hxy, calc
    y = x - (x - y) : eq.symm $ sub_sub_cancel x y
  ... ∈ S : sub_mem hx hxy

lemma mem_of_mem_of_sub_mem' : y ∈ S → x - y ∈ S → x ∈ S :=
λ hy hxy, calc
    x = x - y + y : eq.symm $ sub_add_cancel x y
  ... ∈ S : add_mem hxy hy

lemma mul_mem' : y ∈ S → x * y ∈ S :=
λ hy, have h : y * x ∈ S, from mul_mem hy, by rwa [mul_comm]

end is_ideal

@[reducible] def zero_ideal (α : Type u) [comm_ring α] : set α := {(0:α)}
instance zero_ideal.is_ideal (α : Type u) [comm_ring α] : is_ideal α $ zero_ideal α :=
by refine {..}; intros; simp [set.mem_singleton_iff] at *; simp [*]

@[reducible] def univ_ideal (α : Type u) [comm_ring α] : set α := set.univ
instance univ_ideal.is_ideal (α : Type u) [comm_ring α] : is_ideal α $ univ_ideal α :=
by refine {..}; intros; trivial

theorem is_ideal.eq_univ_of_contains_unit {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
(∃ x:α, x ∈ S ∧ is_unit x) → S = set.univ :=
λ ⟨x, hx, y, hy⟩, set.ext $ λ z, ⟨λ hz, trivial, λ hz, calc
   z = (x * y) * z : by simp [hy]
 ... = x * (y * z) : mul_assoc x y z
 ... ∈ S : is_ideal.mul_mem hx⟩

theorem is_ideal.univ_of_one_mem {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
(1:α) ∈ S → S = set.univ :=
λ h, set.ext $ λ z, ⟨λ hz, trivial, λ hz, by simpa using (is_ideal.mul_mem h : 1 * z ∈ S)⟩

instance is_ideal.hom_preimage {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
(f : α → β) [is_hom f] (S : set β) [is_ideal β S] : is_ideal α (f ⁻¹' S) :=
{ zero_mem := by simp [is_hom.map_zero f],
  add_mem  := λ x y (hx : f x ∈ S) hy, by simp [is_hom.map_add f, is_ideal.add_mem hx hy],
  mul_mem  := λ x y (hx : f x ∈ S), by simp [is_hom.map_mul f, is_ideal.mul_mem hx] }

class is_prime_ideal {α : Type u} [comm_ring α] (S : set α) extends is_ideal α S : Prop :=
(ne_univ_ideal : S ≠ univ_ideal α)
(mem_or_mem_of_mul_mem : ∀ {x y : α}, x * y ∈ S → x ∈ S ∨ y ∈ S)

theorem mem_or_mem_of_mul_eq_zero {α : Type u} [comm_ring α] (S : set α) [is_prime_ideal S] :
  ∀ {x y : α}, x * y = 0 → x ∈ S ∨ y ∈ S :=
λ x y hxy, have x * y ∈ S, by rw hxy; from is_ideal.zero_mem S,
is_prime_ideal.mem_or_mem_of_mul_mem this

class is_maximal_ideal {α : Type u} [comm_ring α] (S : set α) extends is_ideal α S : Prop :=
mk' ::
  (ne_univ_ideal : S ≠ univ_ideal α)
  (eq_or_univ_of_subset : ∀ (T : set α) [is_ideal α T], S ⊆ T → T = S ∨ T = univ_ideal α)

theorem is_maximal_ideal.mk {α : Type u} [comm_ring α] (S : set α) [is_ideal α S] :
  (1:α) ∉ S → (∀ x (T : set α) [is_ideal α T], S ⊆ T → x ∉ S → x ∈ T → (1:α) ∈ T) → is_maximal_ideal S :=
λ h₁ h₂,
{ _inst_2 with
  ne_univ_ideal := λ hu, have (1:α) ∈ S, by rw hu; trivial, h₁ this,
  eq_or_univ_of_subset := λ T ht hst, or.cases_on (classical.em $ ∃ x, x ∉ S ∧ x ∈ T)
    (λ ⟨x, hxns, hxt⟩, or.inr $ @@is_ideal.univ_of_one_mem _ T ht $ @@h₂ x T ht hst hxns hxt)
    (λ hnts, or.inl $ set.ext $ λ x,
       ⟨λ hxt, classical.by_contradiction $ λ hxns, hnts ⟨x, hxns, hxt⟩,
        λ hxs, hst hxs⟩) }

theorem not_unit_of_mem_maximal_ideal {α : Type u} [comm_ring α] (S : set α) [is_maximal_ideal S] : S ⊆ nonunits α :=
λ x hx hxy, is_maximal_ideal.ne_univ_ideal S $ is_ideal.eq_univ_of_contains_unit S ⟨x, hx, hxy⟩

class local_ring (α : Type u) [comm_ring α] :=
(S : set α)
(max : is_maximal_ideal S)
(unique : ∀ T [is_maximal_ideal T], S = T)

instance local_of_nonunits_ideal {α : Type u} [comm_ring α] : (0:α) ≠ 1 →  (∀ x y ∈ nonunits α, x + y ∈ nonunits α) → local_ring α :=
λ hnze h, have hi : is_ideal α (nonunits α), from
{ zero_mem := λ ⟨y, hy⟩, hnze $ by simpa using hy,
  add_mem  := h,
  mul_mem  := λ x y hx ⟨z, hz⟩, hx ⟨y * z, by simpa [mul_assoc] using hz⟩ },
{ S := nonunits α,
  max := @@is_maximal_ideal.mk _ (nonunits α) hi (λ ho, ho ⟨1, mul_one 1⟩) $
    λ x T ht hst hxns hxt, have hxu : _, from classical.by_contradiction hxns,
    let ⟨y, hxy⟩ := hxu in by rw ← hxy; exact is_ideal.mul_mem hxt,
  unique := λ T hmt, or.cases_on (@@is_maximal_ideal.eq_or_univ_of_subset _ hmt (nonunits α) hi $
      λ z hz, @@not_unit_of_mem_maximal_ideal _ T hmt hz) id $
    (λ htu, false.elim $ ((set.set_eq_def _ _).1 htu 1).2 trivial ⟨1, mul_one 1⟩) }

set_option old_structure_cmd true
/-- A domain is a ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`. Alternatively, a domain
  is an integral domain without assuming commutativity of multiplication. -/
class domain (α : Type u) extends ring α, no_zero_divisors α, zero_ne_one_class α

section domain
  variable [domain α]

  theorem mul_eq_zero {a b : α} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, λo,
    or.elim o (λh, by rw h; apply zero_mul) (λh, by rw h; apply mul_zero)⟩

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
  have (b - c) * a = 0, by rewrite [mul_sub_right_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
  eq_of_sub_eq_zero this

  theorem eq_of_mul_eq_mul_left_of_ne_zero {a b c : α} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have a * b - a * c = 0, by simp [h],
  have a * (b - c) = 0, by rewrite [mul_sub_left_distrib, this],
  have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
  eq_of_sub_eq_zero this

  theorem mul_dvd_mul_iff_left {a b c : α} (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr $ λ d, by rw [mul_assoc, domain.mul_left_inj ha]

  theorem mul_dvd_mul_iff_right {a b c : α} (hc : c ≠ 0) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr $ λ d, by rw [mul_right_comm, domain.mul_right_inj hc]

end
