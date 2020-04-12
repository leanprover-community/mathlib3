/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/

import algebra.char_p data.equiv.ring

/-!
# The perfect closure of a field
-/

universes u v

/-- A perfect field is a field of characteristic p that has p-th root. -/
class perfect_field (α : Type u) [field α] (p : ℕ) [char_p α p] [nat.prime p] : Type u :=
(pth_root' : α → α)
(frobenius_pth_root' : ∀ x, frobenius α p (pth_root' x) = x)

/-- Frobenius automorphism of a perfect field. -/
def frobenius_equiv (α : Type u) [field α] (p : ℕ) [char_p α p] [nat.prime p] [perfect_field α p] :
  α ≃+* α :=
{ inv_fun := perfect_field.pth_root' p,
  left_inv := λ x, frobenius_inj α p $ perfect_field.frobenius_pth_root' _,
  right_inv := perfect_field.frobenius_pth_root',
  .. frobenius α p }

/-- `p`-th root of a number in a `perfect_field` as a `ring_hom`. -/
def pth_root (α : Type u) [field α] (p : ℕ) [nat.prime p] [char_p α p] [perfect_field α p] :
  α →+* α :=
(frobenius_equiv α p).symm.to_ring_hom

section

variables {α : Type u} [field α] {β : Type v} [field β] (f : α →* β) (g : α →+* β)
  {p : ℕ} [nat.prime p] [char_p α p] [perfect_field α p] [char_p β p] [perfect_field β p]

@[simp] lemma coe_frobenius_equiv : ⇑(frobenius_equiv α p) = frobenius α p := rfl

@[simp] lemma  coe_frobenius_equiv_symm : ⇑(frobenius_equiv α p).symm = pth_root α p := rfl

@[simp] theorem frobenius_pth_root (x : α) : frobenius α p (pth_root α p x) = x :=
(frobenius_equiv α p).apply_symm_apply x

@[simp] theorem pth_root_frobenius (x : α) : pth_root α p (frobenius α p x) = x :=
(frobenius_equiv α p).symm_apply_apply x

theorem eq_pth_root_iff {x y : α} : x = pth_root α p y ↔ frobenius α p x = y :=
(frobenius_equiv α p).to_equiv.eq_symm_apply

theorem pth_root_eq_iff {x y : α} : pth_root α p x = y ↔ x = frobenius α p y :=
(frobenius_equiv α p).to_equiv.symm_apply_eq

theorem monoid_hom.map_pth_root (x : α) : f (pth_root α p x) = pth_root β p (f x) :=
eq_pth_root_iff.2 $ by rw [← f.map_frobenius, frobenius_pth_root]

theorem monoid_hom.map_iterate_pth_root (x : α) (n : ℕ) :
  f (pth_root α p^[n] x) = (pth_root β p^[n] (f x)) :=
(nat.iterate₁ $ λ x, (f.map_pth_root x).symm).symm

theorem ring_hom.map_pth_root (x : α) :
  g (pth_root α p x) = pth_root β p (g x) :=
g.to_monoid_hom.map_pth_root x

theorem ring_hom.map_iterate_pth_root (x : α) (n : ℕ) :
  g (pth_root α p^[n] x) = (pth_root β p^[n] (g x)) :=
g.to_monoid_hom.map_iterate_pth_root x n

end

section

variables (α : Type u) [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p]

/-- `perfect_closure α p` is the quotient by this relation. -/
inductive perfect_closure.r : (ℕ × α) → (ℕ × α) → Prop
| intro : ∀ n x, perfect_closure.r (n, x) (n+1, frobenius α p x)
run_cmd tactic.mk_iff_of_inductive_prop `perfect_closure.r `perfect_closure.r_iff

/-- The perfect closure is the smallest extension that makes frobenius surjective. -/
def perfect_closure : Type u := quot (perfect_closure.r α p)

end

namespace perfect_closure

variables (α : Type u)

section ring

variables [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p]

/-- Constructor for `perfect_closure`. -/
def mk (x : ℕ × α) : perfect_closure α p := quot.mk (r α p) x

@[simp] lemma quot_mk_eq_mk (x : ℕ × α) :
  (quot.mk (r α p) x : perfect_closure α p) = mk α p x := rfl

variables {α p}

/-- Lift a function `ℕ × α → β` to a function on `perfect_closure α p`. -/
@[elab_as_eliminator]
def lift_on {β : Type*} (x : perfect_closure α p) (f : ℕ × α → β)
  (hf : ∀ x y, r α p x y → f x = f y) : β :=
quot.lift_on x f hf

@[simp] lemma lift_on_mk {β : Sort*} (f : ℕ × α → β)
  (hf : ∀ x y, r α p x y → f x = f y) (x : ℕ × α) :
  (mk α p x).lift_on f hf = f x :=
rfl

@[elab_as_eliminator]
lemma induction_on (x : perfect_closure α p) {q : perfect_closure α p → Prop}
  (h : ∀ x, q (mk α p x)) : q x :=
quot.induction_on x h

variables (α p)

private lemma mul_aux_left (x1 x2 y : ℕ × α) (H : r α p x1 x2) :
  mk α p (x1.1 + y.1, ((frobenius α p)^[y.1] x1.2) * ((frobenius α p)^[x1.1] y.2)) =
  mk α p (x2.1 + y.1, ((frobenius α p)^[y.1] x2.2) * ((frobenius α p)^[x2.1] y.2)) :=
match x1, x2, H with
| _, _, r.intro n x := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_mul, nat.succ_add]; apply r.intro
end

private lemma mul_aux_right (x y1 y2 : ℕ × α) (H : r α p y1 y2) :
  mk α p (x.1 + y1.1, ((frobenius α p)^[y1.1] x.2) * ((frobenius α p)^[x.1] y1.2)) =
  mk α p (x.1 + y2.1, ((frobenius α p)^[y2.1] x.2) * ((frobenius α p)^[x.1] y2.2)) :=
match y1, y2, H with
| _, _, r.intro n y := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_mul]; apply r.intro
end

instance : has_mul (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.lift (λ y:ℕ×α, mk α p
    (x.1 + y.1, ((frobenius α p)^[y.1] x.2) * ((frobenius α p)^[x.1] y.2))) (mul_aux_right α p x))
  (λ x1 x2 (H : r α p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
mul_aux_left α p x1 x2 y H)⟩

@[simp] lemma mk_mul_mk (x y : ℕ × α) :
  mk α p x * mk α p y = mk α p
    (x.1 + y.1, ((frobenius α p)^[y.1] x.2) * ((frobenius α p)^[x.1] y.2)) :=
rfl

instance : comm_monoid (perfect_closure α p) :=
{ mul_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, congr_arg (quot.mk _) $
    by simp only [add_assoc, mul_assoc, nat.iterate₂ (frobenius_mul _),
      ← nat.iterate_add, add_comm, add_left_comm],
  one := mk α p (0, 1),
  one_mul := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_one _), nat.iterate_zero, one_mul, zero_add]),
  mul_one := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_one _), nat.iterate_zero, mul_one, add_zero]),
  mul_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩, quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $ by simp only [add_comm, mul_comm])),
  .. (infer_instance : has_mul (perfect_closure α p)) }

lemma one_def : (1 : perfect_closure α p) = mk α p (0, 1) := rfl

instance : inhabited (perfect_closure α p) := ⟨1⟩

private lemma add_aux_left (x1 x2 y : ℕ × α) (H : r α p x1 x2) :
  mk α p (x1.1 + y.1, ((frobenius α p)^[y.1] x1.2) + ((frobenius α p)^[x1.1] y.2)) =
  mk α p (x2.1 + y.1, ((frobenius α p)^[y.1] x2.2) + ((frobenius α p)^[x2.1] y.2)) :=
match x1, x2, H with
| _, _, r.intro n x := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_add, nat.succ_add]; apply r.intro
end

private lemma add_aux_right (x y1 y2 : ℕ × α) (H : r α p y1 y2) :
  mk α p (x.1 + y1.1, ((frobenius α p)^[y1.1] x.2) + ((frobenius α p)^[x.1] y1.2)) =
  mk α p (x.1 + y2.1, ((frobenius α p)^[y2.1] x.2) + ((frobenius α p)^[x.1] y2.2)) :=
match y1, y2, H with
| _, _, r.intro n y := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_add]; apply r.intro
end

instance : has_add (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.lift (λ y:ℕ×α, mk α p
    (x.1 + y.1, ((frobenius α p)^[y.1] x.2) + ((frobenius α p)^[x.1] y.2))) (add_aux_right α p x))
  (λ x1 x2 (H : r α p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
add_aux_left α p x1 x2 y H)⟩

@[simp] lemma mk_add_mk (x y : ℕ × α) :
  mk α p x + mk α p y =
    mk α p (x.1 + y.1, ((frobenius α p)^[y.1] x.2) + ((frobenius α p)^[x.1] y.2)) := rfl

instance : has_neg (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, mk α p (x.1, -x.2)) (λ x y (H : r α p x y), match x, y, H with
| _, _, r.intro n x := quot.sound $ by rw ← frobenius_neg; apply r.intro
end)⟩

@[simp] lemma neg_mk (x : ℕ × α) : - mk α p x = mk α p (x.1, -x.2) := rfl

instance : has_zero (perfect_closure α p) := ⟨mk α p (0, 0)⟩

lemma zero_def : (0 : perfect_closure α p) = mk α p (0, 0) := rfl

theorem mk_zero (n : ℕ) : mk α p (n, 0) = 0 :=
by induction n with n ih; [refl, rw ← ih]; symmetry; apply quot.sound;
have := r.intro n (0:α); rwa [frobenius_zero α p] at this

theorem r.sound (m n : ℕ) (x y : α) (H : frobenius α p^[m] x = y) :
  mk α p (n, x) = mk α p (m + n, y) :=
by subst H; induction m with m ih; [simp only [zero_add, nat.iterate_zero],
  rw [ih, nat.succ_add, nat.iterate_succ']]; apply quot.sound; apply r.intro

instance : comm_ring (perfect_closure α p) :=
{ add_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, congr_arg (quot.mk _) $
    by simp only [add_assoc, nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, add_comm, add_left_comm],
  zero := 0,
  zero_add := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_zero α p), nat.iterate_zero, zero_add]),
  add_zero := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_zero α p), nat.iterate_zero, add_zero]),
  add_left_neg := λ e, quot.induction_on e (λ ⟨n, x⟩,
    by simp only [quot_mk_eq_mk, neg_mk, mk_add_mk,
      nat.iterate₁ (frobenius_neg α p), add_left_neg, mk_zero]),
  add_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩, quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $ by simp only [add_comm])),
  left_distrib := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, show quot.mk _ _ = quot.mk _ _,
    by simp only [add_assoc, add_comm, add_left_comm]; apply r.sound;
    simp only [nat.iterate₂ (frobenius_mul p), nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, mul_add, add_comm, add_left_comm],
  right_distrib := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, show quot.mk _ _ = quot.mk _ _,
    by simp only [add_assoc, add_comm _ s, add_left_comm _ s]; apply r.sound;
    simp only [nat.iterate₂ (frobenius_mul p), nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, add_mul, add_comm, add_left_comm],
  .. (infer_instance : has_add (perfect_closure α p)),
  .. (infer_instance : has_neg (perfect_closure α p)),
  .. (infer_instance : comm_monoid (perfect_closure α p)) }

theorem eq_iff' (x y : ℕ × α) : mk α p x = mk α p y ↔
    ∃ z, (frobenius α p^[y.1 + z] x.2) = (frobenius α p^[x.1 + z] y.2) :=
begin
  split,
  { intro H,
    replace H := quot.exact _ H,
    induction H,
    case eqv_gen.rel : x y H
    { cases H with n x, exact ⟨0, rfl⟩ },
    case eqv_gen.refl : H
    { exact ⟨0, rfl⟩ },
    case eqv_gen.symm : x y H ih
    { cases ih with w ih, exact ⟨w, ih.symm⟩ },
    case eqv_gen.trans : x y z H1 H2 ih1 ih2
    { cases ih1 with z1 ih1,
      cases ih2 with z2 ih2,
      existsi z2+(y.1+z1),
      rw [← add_assoc, nat.iterate_add, ih1],
      rw [← nat.iterate_add, add_comm, nat.iterate_add, ih2],
      rw [← nat.iterate_add],
      simp only [add_comm, add_left_comm] } },
  intro H,
  cases x with m x,
  cases y with n y,
  cases H with z H, dsimp only at H,
  rw [r.sound α p (n+z) m x _ rfl, r.sound α p (m+z) n y _ rfl, H],
  rw [add_assoc, add_comm, add_comm z]
end

theorem nat_cast (n x : ℕ) : (x : perfect_closure α p) = mk α p (n, x) :=
begin
  induction n with n ih,
  { induction x with x ih, {refl},
    rw [nat.cast_succ, nat.cast_succ, ih], refl },
  rw ih, apply quot.sound,
  conv {congr, skip, skip, rw ← frobenius_nat_cast α p x},
  apply r.intro
end

theorem int_cast (x : ℤ) : (x : perfect_closure α p) = mk α p (0, x) :=
by induction x; simp only [int.cast_of_nat, int.cast_neg_succ_of_nat, nat_cast α p 0]; refl

theorem nat_cast_eq_iff (x y : ℕ) : (x : perfect_closure α p) = y ↔ (x : α) = y :=
begin
  split; intro H,
  { rw [nat_cast α p 0, nat_cast α p 0, eq_iff'] at H,
    cases H with z H,
    simpa only [zero_add, nat.iterate₀ (frobenius_nat_cast α p _)] using H },
  rw [nat_cast α p 0, nat_cast α p 0, H]
end

instance : char_p (perfect_closure α p) p :=
begin
  constructor, intro x, rw ← char_p.cast_eq_zero_iff α,
  rw [← nat.cast_zero, nat_cast_eq_iff, nat.cast_zero]
end

theorem frobenius_mk (x : ℕ × α) :
  (frobenius (perfect_closure α p) p : perfect_closure α p → perfect_closure α p)
    (mk α p x) = mk _ _ (x.1, x.2^p) :=
begin
  simp only [frobenius_def], cases x with n x, dsimp only,
  suffices : ∀ p':ℕ, mk α p (n, x) ^ p' = mk α p (n, x ^ p'),
  { apply this },
  intro p, induction p with p ih,
  case nat.zero { apply r.sound, rw [(frobenius _ _).iterate_map_one, pow_zero] },
  case nat.succ {
    rw [pow_succ, ih],
    symmetry,
    apply r.sound,
    simp only [pow_succ, (frobenius _ _).iterate_map_mul]
  }
end

/-- Embedding of `α` into `perfect_closure α p` -/
def of : α →+* perfect_closure α p :=
{ to_fun := λ x, mk _ _ (0, x),
  map_one' := rfl,
  map_mul' := λ x y, rfl,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

lemma of_apply (x : α) : of α p x = mk _ _ (0, x) := rfl

end ring

theorem eq_iff [integral_domain α] (p : ℕ) [nat.prime p] [char_p α p]
  (x y : ℕ × α) : quot.mk (r α p) x = quot.mk (r α p) y ↔
    (frobenius α p^[y.1] x.2) = (frobenius α p^[x.1] y.2) :=
(eq_iff' α p x y).trans ⟨λ ⟨z, H⟩, nat.iterate_inj (frobenius_inj α p) z _ _ $
  by simpa only [add_comm, nat.iterate_add] using H,
λ H, ⟨0, H⟩⟩

section field

variables [field α] (p : ℕ) [nat.prime p] [char_p α p]

instance : has_inv (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.mk (r α p) (x.1, x.2⁻¹)) (λ x y (H : r α p x y), match x, y, H with
| _, _, r.intro n x := quot.sound $ by simp only [frobenius_def]; rw ← inv_pow'; apply r.intro
end)⟩

instance : field (perfect_closure α p) :=
{ zero_ne_one := λ H, zero_ne_one ((eq_iff _ _ _ _).1 H),
  mul_inv_cancel := λ e, induction_on e $ λ ⟨m, x⟩ H,
    have _ := mt (eq_iff _ _ _ _).2 H, (eq_iff _ _ _ _).2
      (by simp only [(frobenius _ _).iterate_map_one, (frobenius α p).iterate_map_zero,
        nat.iterate_zero, ← (frobenius _ p).iterate_map_mul] at this ⊢;
        rw [mul_inv_cancel this, (frobenius _ _).iterate_map_one]),
  inv_zero := congr_arg (quot.mk (r α p)) (by rw [inv_zero]),
  .. (infer_instance : has_inv (perfect_closure α p)),
  .. (infer_instance : comm_ring (perfect_closure α p)) }


instance : perfect_field (perfect_closure α p) p :=
{ pth_root' := λ e, lift_on e (λ x, mk α p (x.1 + 1, x.2)) (λ x y H,
    match x, y, H with
    | _, _, r.intro n x := quot.sound (r.intro _ _)
    end),
  frobenius_pth_root' := λ e, induction_on e (λ ⟨n, x⟩,
    by { simp only [lift_on_mk, frobenius_mk], exact (quot.sound $ r.intro _ _).symm }) }

theorem eq_pth_root (x : ℕ × α) :
  mk α p x = (pth_root (perfect_closure α p) p^[x.1] (of α p x.2)) :=
begin
  rcases x with ⟨m, x⟩,
  induction m with m ih, {refl},
  rw [nat.iterate_succ', ← ih]; refl
end

/-- Given a field `α` of characteristic `p` and a perfect field `β` of the same characteristic,
any homomorphism `α →+* β` can be lifted to `perfect_closure α p`. -/
def lift (β : Type v) [field β] [char_p β p] [perfect_field β p] :
  (α →+* β) ≃ (perfect_closure α p →+* β) :=
begin
  refine_struct { .. },
  field to_fun { intro f,
    refine_struct { .. },
    field to_fun { refine λ e, lift_on e (λ x, pth_root β p^[x.1] (f x.2)) _,
      rintro a b ⟨n⟩,
      simp only [f.map_frobenius, nat.iterate_succ, pth_root_frobenius] },
    field map_one' { exact f.map_one },
    field map_zero' { exact f.map_zero },
    field map_mul' { rintro ⟨x⟩ ⟨y⟩,
      simp only [quot_mk_eq_mk, lift_on_mk, mk_mul_mk, ring_hom.map_iterate_frobenius,
        ring_hom.iterate_map_mul, ring_hom.map_mul],
      rw [nat.iterate_add, nat.iterate_cancel, add_comm, nat.iterate_add, nat.iterate_cancel];
        exact pth_root_frobenius },
    field map_add' { rintro ⟨x⟩ ⟨y⟩,
      simp only [quot_mk_eq_mk, lift_on_mk, mk_add_mk, ring_hom.map_iterate_frobenius,
        ring_hom.iterate_map_add, ring_hom.map_add],
      rw [nat.iterate_add, nat.iterate_cancel, add_comm x.1, nat.iterate_add, nat.iterate_cancel];
        exact pth_root_frobenius } },
  field inv_fun { exact λ f, f.comp (of α p) },
  field left_inv { intro f, ext x, refl },
  field right_inv { intro f, ext ⟨x⟩,
    simp only [ring_hom.coe_mk, quot_mk_eq_mk, ring_hom.comp_apply, lift_on_mk],
    rw [eq_pth_root, ring_hom.map_iterate_pth_root] }
end

end field

end perfect_closure
