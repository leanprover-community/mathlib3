import algebra.ring

universes u

variables (α : Type u)

class is_division_ring [ring α] : Prop :=
(exists_inv : ∀ {x : α}, x ≠ 0 → ∃ y, x * y = 1)

theorem mul_eq_one_comm {α} [ring α] [is_division_ring α] {x y : α} (hxy : x * y = 1) : y * x = 1 :=
classical.by_cases
  (assume hy0 : y = 0, by rw [← hxy, hy0, zero_mul, mul_zero])
  (assume hy0 : y ≠ 0, let ⟨z, hz⟩ := is_division_ring.exists_inv hy0 in
    by rw [← mul_one x, ← hz, ← mul_assoc x, hxy, one_mul])

inductive pre_to_field : Type u
| of : α → pre_to_field
| add : pre_to_field → pre_to_field → pre_to_field
| mul : pre_to_field → pre_to_field → pre_to_field
| inv : pre_to_field → pre_to_field

namespace pre_to_field

variables {α}

def rel [semiring α] : (pre_to_field α) → α → Prop
| (of p)    z := p = z
| (add p q) z := ∃ x y, rel p x ∧ rel q y ∧ x + y = z
| (mul p q) z := ∃ x y, rel p x ∧ rel q y ∧ x * y = z
| (inv p)   z := rel p 0 ∧ z = 0 ∨ ∃ x, rel p x ∧ x * z = 1

def neg [has_neg α] : pre_to_field α → pre_to_field α
| (of p)    := of (-p)
| (add x y) := add (neg x) (neg y)
| (mul x y) := mul (neg x) y
| (inv x)   := inv (neg x)

theorem rel_neg [ring α] : Π {p} {z : α}, rel p z → rel (neg p) (-z)
| (of p)    z hpz                   := congr_arg has_neg.neg hpz
| (add p q) z ⟨x, y, hpx, hqy, hxyz⟩ := ⟨-x, -y, rel_neg hpx, rel_neg hqy, by rw [← hxyz, neg_add]⟩
| (mul p q) z ⟨x, y, hpx, hqy, hxyz⟩ := ⟨-x, y, rel_neg hpx, hqy, by rw [← hxyz, neg_mul_eq_neg_mul]⟩
| (inv p)   z (or.inl ⟨hp0, hz0⟩)    := or.inl ⟨@neg_zero α _ ▸ rel_neg hp0, neg_eq_zero.2 hz0⟩
| (inv p)   z (or.inr ⟨x, hpx, hxz⟩) := or.inr ⟨-x, rel_neg hpx, by rw [neg_mul_neg, hxz]⟩

variables [ring α] [is_division_ring α]

lemma unique_rel (p : pre_to_field α) :
  ∃!x, rel p x :=
pre_to_field.rec_on p
  (λ x, ⟨x, rfl, λ y hxy, hxy.symm⟩)
  (λ p q ⟨x, hpx, hpx2⟩ ⟨y, hqy, hqy2⟩, ⟨x+y, ⟨x, y, hpx, hqy, rfl⟩,
    λ z ⟨x', y', hpx', hqy', hxyz⟩, hpx2 x' hpx' ▸ hqy2 y' hqy' ▸ hxyz.symm⟩)
  (λ p q ⟨x, hpx, hpx2⟩ ⟨y, hqy, hqy2⟩, ⟨x*y, ⟨x, y, hpx, hqy, rfl⟩,
    λ z ⟨x', y', hpx', hqy', hxyz⟩, hpx2 x' hpx' ▸ hqy2 y' hqy' ▸ hxyz.symm⟩)
  (λ p ⟨x, hpx, hpx2⟩, classical.by_cases
    (assume hx0 : x = 0, ⟨0, or.inl ⟨hx0 ▸ hpx, rfl⟩, λ y hy,
      or.cases_on hy and.right $ λ ⟨z, hpz, hzy⟩,
      by rw [← one_mul y, ← hzy, hpx2 z hpz, hx0, zero_mul, zero_mul]⟩)
    (assume hx0 : x ≠ 0, let ⟨y, hxy⟩ := is_division_ring.exists_inv hx0 in
      ⟨y, or.inr ⟨x, hpx, hxy⟩, λ z hz, or.cases_on hz
        (λ ⟨hp0, hz0⟩, by rw [hz0, ← one_mul y, ← hxy, ← hpx2 0 hp0, zero_mul, zero_mul])
        (λ ⟨s, hps, hsz⟩, by rw [← mul_one y, ← hsz, ← mul_assoc, hpx2 s hps, mul_eq_one_comm hxy, one_mul])⟩))

variables (α)

instance : setoid (pre_to_field α) :=
{ r := λ p q, ∃ x, rel p x ∧ rel q x,
  iseqv := ⟨λ p, let ⟨x, hx⟩ := unique_rel p in ⟨x, hx.1, hx.1⟩,
    λ p q ⟨x, hpx, hqx⟩, ⟨x, hqx, hpx⟩,
    λ p q r ⟨x, hpx, hqx⟩ ⟨y, hqy, hry⟩, ⟨x, hpx, unique_of_exists_unique (unique_rel q) hqy hqx ▸ hry⟩⟩ }

end pre_to_field


def to_field [ring α] [is_division_ring α] : Type u :=
quotient (pre_to_field.setoid α)

namespace to_field

variables {α} [ring α] [is_division_ring α]

def mk (x : α) : to_field α :=
⟦pre_to_field.of x⟧

variables (α)

theorem mk.bijective : function.bijective (@mk α _ _) :=
⟨λ x y H, let ⟨z, hxz, hyz⟩ := quotient.exact H in eq.trans hxz hyz.symm,
λ x, quotient.induction_on x $ λ p, let ⟨z, hz⟩ := pre_to_field.unique_rel p in
⟨z, quotient.sound ⟨z, rfl, hz.1⟩⟩⟩

instance : has_add (to_field α) :=
⟨λ x y, quotient.lift_on₂ x y (λ p q, ⟦pre_to_field.add p q⟧) $ λ p q r s ⟨x, hpx, hrx⟩ ⟨y, hqy, hsy⟩, quotient.sound
⟨x + y, ⟨x, y, hpx, hqy, rfl⟩, ⟨x, y, hrx, hsy, rfl⟩⟩⟩

instance : has_neg (to_field α) :=
⟨λ x, quotient.lift_on x (λ p, ⟦pre_to_field.neg p⟧) $ λ p q ⟨x, hpx, hqx⟩, quotient.sound
⟨-x, pre_to_field.rel_neg hpx, pre_to_field.rel_neg hqx⟩⟩

instance : has_mul (to_field α) :=
⟨λ x y, quotient.lift_on₂ x y (λ p q, ⟦pre_to_field.mul p q⟧) $ λ p q r s ⟨x, hpx, hrx⟩ ⟨y, hqy, hsy⟩, quotient.sound
⟨x * y, ⟨x, y, hpx, hqy, rfl⟩, ⟨x, y, hrx, hsy, rfl⟩⟩⟩

instance : has_inv (to_field α) :=
⟨λ x, quotient.lift_on x (λ p, ⟦pre_to_field.inv p⟧) $ λ p q ⟨x, hpx, hqx⟩, quotient.sound $
classical.by_cases
  (assume hx0 : x = 0, ⟨0, or.inl ⟨hx0 ▸ hpx, rfl⟩, or.inl ⟨hx0 ▸ hqx, rfl⟩⟩)
  (assume hx0 : x ≠ 0, let ⟨y, hy⟩ := is_division_ring.exists_inv hx0 in ⟨y, or.inr ⟨x, hpx, hy⟩, or.inr ⟨x, hqx, hy⟩⟩)⟩

variables {α}

@[elab_as_eliminator] protected lemma induction_on
  {C : to_field α → Prop} (x : to_field α)
  (ih : ∀ z, C (mk z)) : C x :=
let ⟨z, hz⟩ := (mk.bijective α).2 x in hz ▸ ih z

@[elab_as_eliminator] protected lemma induction_on₂
  {C : to_field α → to_field α → Prop} (x y : to_field α)
  (ih : ∀ p q, C (mk p) (mk q)) : C x y :=
to_field.induction_on x $ λ p, to_field.induction_on y $ λ q, ih p q

@[elab_as_eliminator] protected lemma induction_on₃
  {C : to_field α → to_field α → to_field α → Prop} (x y z : to_field α)
  (ih : ∀ p q r, C (mk p) (mk q) (mk r)) : C x y z :=
to_field.induction_on x $ λ p, to_field.induction_on y $ λ q, to_field.induction_on z $ λ r, ih p q r

@[simp] lemma mk_add (x y : α) : mk (x + y) = mk x + mk y :=
quotient.sound ⟨x + y, rfl, ⟨x, y, rfl, rfl, rfl⟩⟩

@[simp] lemma mk_neg (x : α) : mk (-x) = -mk x := rfl

@[simp] lemma mk_mul (x y : α) : mk (x * y) = mk x * mk y :=
quotient.sound ⟨x * y, rfl, ⟨x, y, rfl, rfl, rfl⟩⟩

lemma mk_inv {x y : α} (hxy : x * y = 1) : (mk x)⁻¹ = mk y :=
quotient.sound ⟨y, or.inr ⟨x, rfl, hxy⟩, rfl⟩

variables (α)
instance : ring (to_field α) :=
{ zero := mk 0,
  one := mk 1,
  add_assoc := λ x y z, to_field.induction_on₃ x y z $ λ p q r,
    by rw [← mk_add, ← mk_add, ← mk_add, ← mk_add, add_assoc],
  zero_add := λ x, to_field.induction_on x $ λ p,
    by rw [← mk_add, zero_add],
  add_zero := λ x, to_field.induction_on x $ λ p,
    by rw [← mk_add, add_zero],
  add_left_neg := λ x, to_field.induction_on x $ λ p,
    by rw [← mk_neg, ← mk_add, add_left_neg]; refl,
  add_comm := λ x y, to_field.induction_on₂ x y $ λ p q,
    by rw [← mk_add, ← mk_add, add_comm],
  mul_assoc := λ x y z, to_field.induction_on₃ x y z $ λ p q r,
    by rw [← mk_mul, ← mk_mul, ← mk_mul, ← mk_mul, mul_assoc],
  one_mul := λ x, to_field.induction_on x $ λ p,
    by rw [← mk_mul, one_mul],
  mul_one := λ x, to_field.induction_on x $ λ p,
    by rw [← mk_mul, mul_one],
  left_distrib := λ x y z, to_field.induction_on₃ x y z $ λ p q r,
    by rw [← mk_add, ← mk_mul, ← mk_mul, ← mk_mul, ← mk_add, mul_add],
  right_distrib := λ x y z, to_field.induction_on₃ x y z $ λ p q r,
    by rw [← mk_add, ← mk_mul, ← mk_mul, ← mk_mul, ← mk_add, add_mul],
  .. to_field.has_add α,
  .. to_field.has_neg α,
  .. to_field.has_mul α }

@[simp] lemma mk_zero : mk (0 : α) = 0 := rfl
@[simp] lemma mk_one : mk (1 : α) = 1 := rfl

instance : is_ring_hom (@mk α _ _) :=
⟨mk_one α, mk_mul, mk_add⟩

end to_field

namespace to_field

instance [comm_ring α] [is_division_ring α] : comm_ring (to_field α) :=
{ mul_comm := λ x y, to_field.induction_on₂ x y $ λ p q,
    by rw [← mk_mul, ← mk_mul, mul_comm],
  .. to_field.ring α }

instance [nonzero_comm_ring α] [is_division_ring α] : field (to_field α) :=
{ zero_ne_one := λ H, zero_ne_one $ (mk.bijective α).1 H,
  mul_inv_cancel := λ x, to_field.induction_on x $ λ p hp0,
    let ⟨y, hy⟩ := is_division_ring.exists_inv (mt (congr_arg mk) hp0) in
    by rw [mk_inv hy, ← mk_mul, hy, mk_one],
  inv_mul_cancel := λ x, to_field.induction_on x $ λ p hp0,
    let ⟨y, hy⟩ := is_division_ring.exists_inv (mt (congr_arg mk) hp0) in
    by rw [mk_inv hy, ← mk_mul, mul_eq_one_comm hy, mk_one],
  .. to_field.comm_ring α,
  .. to_field.has_inv α }

end to_field
