/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau

The perfect closure of a field.
-/

import algebra.char_p

universes u v

/-- A perfect field is a field of characteristic p that has p-th root. -/
class perfect_field (α : Type u) [field α] (p : ℕ) [char_p α p] : Type u :=
(pth_root : α → α)
(frobenius_pth_root : ∀ x, frobenius α p (pth_root x) = x)

theorem frobenius_pth_root (α : Type u) [field α] (p : ℕ) [char_p α p] [perfect_field α p] (x : α) :
  frobenius α p (perfect_field.pth_root p x) = x :=
perfect_field.frobenius_pth_root p x

theorem pth_root_frobenius (α : Type u) [field α] (p : ℕ) [nat.prime p] [char_p α p] [perfect_field α p] (x : α) :
  perfect_field.pth_root p (frobenius α p x) = x :=
frobenius_inj α p _ _ (by rw frobenius_pth_root)

instance pth_root.is_ring_hom (α : Type u) [field α] (p : ℕ) [nat.prime p] [char_p α p] [perfect_field α p] :
  is_ring_hom (@perfect_field.pth_root α _ p _ _) :=
{ map_one := frobenius_inj α p _ _ (by rw [frobenius_pth_root, frobenius_one]),
  map_mul := λ x y, frobenius_inj α p _ _ (by simp only [frobenius_pth_root, frobenius_mul]),
  map_add := λ x y, frobenius_inj α p _ _ (by simp only [frobenius_pth_root, frobenius_add]) }

theorem is_ring_hom.pth_root {α : Type u} [field α] (p : ℕ) [nat.prime p] [char_p α p] [perfect_field α p]
  {β : Type v} [field β] [char_p β p] [perfect_field β p] (f : α → β) [is_ring_hom f] {x : α} :
  f (perfect_field.pth_root p x) = perfect_field.pth_root p (f x) :=
frobenius_inj β p _ _ (by rw [← is_monoid_hom.map_frobenius f, frobenius_pth_root, frobenius_pth_root])

inductive perfect_closure.r (α : Type u) [monoid α] (p : ℕ) : (ℕ × α) → (ℕ × α) → Prop
| intro : ∀ n x, perfect_closure.r (n, x) (n+1, frobenius α p x)
run_cmd tactic.mk_iff_of_inductive_prop `perfect_closure.r `perfect_closure.r_iff

/-- The perfect closure is the smallest extension that makes frobenius surjective. -/
def perfect_closure (α : Type u) [monoid α] (p : ℕ) : Type u :=
quot (perfect_closure.r α p)

namespace perfect_closure

variables (α : Type u)

private lemma mul_aux_left [comm_monoid α] (p : ℕ) (x1 x2 y : ℕ × α) (H : r α p x1 x2) :
  quot.mk (r α p) (x1.1 + y.1, ((frobenius α p)^[y.1] x1.2) * ((frobenius α p)^[x1.1] y.2)) =
  quot.mk (r α p) (x2.1 + y.1, ((frobenius α p)^[y.1] x2.2) * ((frobenius α p)^[x2.1] y.2)) :=
match x1, x2, H with
| _, _, r.intro _ n x := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_mul, nat.succ_add]; apply r.intro
end

private lemma mul_aux_right [comm_monoid α] (p : ℕ) (x y1 y2 : ℕ × α) (H : r α p y1 y2) :
  quot.mk (r α p) (x.1 + y1.1, ((frobenius α p)^[y1.1] x.2) * ((frobenius α p)^[x.1] y1.2)) =
  quot.mk (r α p) (x.1 + y2.1, ((frobenius α p)^[y2.1] x.2) * ((frobenius α p)^[x.1] y2.2)) :=
match y1, y2, H with
| _, _, r.intro _ n y := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_mul]; apply r.intro
end

instance [comm_monoid α] (p : ℕ) : has_mul (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.lift (λ y:ℕ×α, quot.mk (r α p)
    (x.1 + y.1, ((frobenius α p)^[y.1] x.2) * ((frobenius α p)^[x.1] y.2))) (mul_aux_right α p x))
  (λ x1 x2 (H : r α p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
mul_aux_left α p x1 x2 y H)⟩

instance [comm_monoid α] (p : ℕ) : comm_monoid (perfect_closure α p) :=
{ mul_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, congr_arg (quot.mk _) $
    by simp only [add_assoc, mul_assoc, nat.iterate₂ (frobenius_mul _ _),
      (nat.iterate_add _ _ _ _).symm, add_comm, add_left_comm],
  one := quot.mk _ (0, 1),
  one_mul := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_one _ _), nat.iterate_zero, one_mul, zero_add]),
  mul_one := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_one _ _), nat.iterate_zero, mul_one, add_zero]),
  mul_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩, quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $ by simp only [add_comm, mul_comm])),
  .. (infer_instance : has_mul (perfect_closure α p)) }

private lemma add_aux_left [comm_ring α] (p : ℕ) (hp : nat.prime p) [char_p α p]
  (x1 x2 y : ℕ × α) (H : r α p x1 x2) :
  quot.mk (r α p) (x1.1 + y.1, ((frobenius α p)^[y.1] x1.2) + ((frobenius α p)^[x1.1] y.2)) =
  quot.mk (r α p) (x2.1 + y.1, ((frobenius α p)^[y.1] x2.2) + ((frobenius α p)^[x2.1] y.2)) :=
match x1, x2, H with
| _, _, r.intro _ n x := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_add, nat.succ_add]; apply r.intro
end

private lemma add_aux_right [comm_ring α] (p : ℕ) (hp : nat.prime p) [char_p α p]
  (x y1 y2 : ℕ × α) (H : r α p y1 y2) :
  quot.mk (r α p) (x.1 + y1.1, ((frobenius α p)^[y1.1] x.2) + ((frobenius α p)^[x.1] y1.2)) =
  quot.mk (r α p) (x.1 + y2.1, ((frobenius α p)^[y2.1] x.2) + ((frobenius α p)^[x.1] y2.2)) :=
match y1, y2, H with
| _, _, r.intro _ n y := quot.sound $ by rw [← nat.iterate_succ, nat.iterate_succ',
    nat.iterate_succ', ← frobenius_add]; apply r.intro
end

instance [comm_ring α] (p : ℕ) [hp : nat.prime p] [char_p α p] : has_add (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.lift (λ y:ℕ×α, quot.mk (r α p)
    (x.1 + y.1, ((frobenius α p)^[y.1] x.2) + ((frobenius α p)^[x.1] y.2))) (add_aux_right α p hp x))
  (λ x1 x2 (H : r α p x1 x2), funext $ λ e, quot.induction_on e $ λ y,
add_aux_left α p hp x1 x2 y H)⟩

instance [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] : has_neg (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.mk (r α p) (x.1, -x.2)) (λ x y (H : r α p x y), match x, y, H with
| _, _, r.intro _ n x := quot.sound $ by rw ← frobenius_neg; apply r.intro
end)⟩

theorem mk_zero [comm_ring α] (p : ℕ) [nat.prime p] (n : ℕ) : quot.mk (r α p) (n, 0) = quot.mk (r α p) (0, 0) :=
by induction n with n ih; [refl, rw ← ih]; symmetry; apply quot.sound;
have := r.intro p n (0:α); rwa [frobenius_zero α p] at this

theorem r.sound [monoid α] (p m n : ℕ) (x y : α) (H : frobenius α p^[m] x = y) :
  quot.mk (r α p) (n, x) = quot.mk (r α p) (m + n, y) :=
by subst H; induction m with m ih; [simp only [zero_add, nat.iterate_zero],
  rw [ih, nat.succ_add, nat.iterate_succ']]; apply quot.sound; apply r.intro

instance [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] : comm_ring (perfect_closure α p) :=
{ add_assoc := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, congr_arg (quot.mk _) $
    by simp only [add_assoc, nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, add_comm, add_left_comm],
  zero := quot.mk _ (0, 0),
  zero_add := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_zero α p), nat.iterate_zero, zero_add]),
  add_zero := λ e, quot.induction_on e (λ ⟨n, x⟩, congr_arg (quot.mk _) $
    by simp only [nat.iterate₀ (frobenius_zero α p), nat.iterate_zero, add_zero]),
  add_left_neg := λ e, quot.induction_on e (λ ⟨n, x⟩, show quot.mk _ _ = _,
    by simp only [nat.iterate₁ (frobenius_neg α p), add_left_neg, mk_zero]; refl),
  add_comm := λ e f, quot.induction_on e (λ ⟨m, x⟩, quot.induction_on f (λ ⟨n, y⟩,
    congr_arg (quot.mk _) $ by simp only [add_comm])),
  left_distrib := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, show quot.mk _ _ = quot.mk _ _,
    by simp only [add_assoc, add_comm, add_left_comm]; apply r.sound;
    simp only [nat.iterate₂ (frobenius_mul α p), nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, mul_add, add_comm, add_left_comm],
  right_distrib := λ e f g, quot.induction_on e $ λ ⟨m, x⟩, quot.induction_on f $ λ ⟨n, y⟩,
    quot.induction_on g $ λ ⟨s, z⟩, show quot.mk _ _ = quot.mk _ _,
    by simp only [add_assoc, add_comm _ s, add_left_comm _ s]; apply r.sound;
    simp only [nat.iterate₂ (frobenius_mul α p), nat.iterate₂ (frobenius_add α p),
      (nat.iterate_add _ _ _ _).symm, add_mul, add_comm, add_left_comm],
  .. (infer_instance : has_add (perfect_closure α p)),
  .. (infer_instance : has_neg (perfect_closure α p)),
  .. (infer_instance : comm_monoid (perfect_closure α p)) }

instance [discrete_field α] (p : ℕ) [nat.prime p] [char_p α p] : has_inv (perfect_closure α p) :=
⟨quot.lift (λ x:ℕ×α, quot.mk (r α p) (x.1, x.2⁻¹)) (λ x y (H : r α p x y), match x, y, H with
| _, _, r.intro _ n x := quot.sound $ by simp only [frobenius]; rw inv_pow'; apply r.intro
end)⟩

theorem eq_iff' [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p]
  (x y : ℕ × α) : quot.mk (r α p) x = quot.mk (r α p) y ↔
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

theorem eq_iff [integral_domain α] (p : ℕ) [nat.prime p] [char_p α p]
  (x y : ℕ × α) : quot.mk (r α p) x = quot.mk (r α p) y ↔
    (frobenius α p^[y.1] x.2) = (frobenius α p^[x.1] y.2) :=
(eq_iff' α p x y).trans ⟨λ ⟨z, H⟩, nat.iterate_inj (frobenius_inj α p) z _ _ $
  by simpa only [add_comm, nat.iterate_add] using H,
λ H, ⟨0, H⟩⟩

instance [discrete_field α] (p : ℕ) [nat.prime p] [char_p α p] : discrete_field (perfect_closure α p) :=
{ zero_ne_one := λ H, zero_ne_one ((eq_iff _ _ _ _).1 H),
  mul_inv_cancel := λ e, quot.induction_on e $ λ ⟨m, x⟩ H,
    have _ := mt (eq_iff _ _ _ _).2 H, (eq_iff _ _ _ _).2
      (by simp only [nat.iterate₀ (frobenius_one _ _), nat.iterate₀ (frobenius_zero α p),
        nat.iterate_zero, (nat.iterate₂ (frobenius_mul α p)).symm] at this ⊢;
        rw [mul_inv_cancel this, nat.iterate₀ (frobenius_one _ _)]),
  inv_mul_cancel := λ e, quot.induction_on e $ λ ⟨m, x⟩ H,
    have _ := mt (eq_iff _ _ _ _).2 H, (eq_iff _ _ _ _).2
      (by simp only [nat.iterate₀ (frobenius_one _ _), nat.iterate₀ (frobenius_zero α p),
        nat.iterate_zero, (nat.iterate₂ (frobenius_mul α p)).symm] at this ⊢;
        rw [inv_mul_cancel this, nat.iterate₀ (frobenius_one _ _)]),
  has_decidable_eq := λ e f, quot.rec_on_subsingleton e $ λ ⟨m, x⟩,
    quot.rec_on_subsingleton f $ λ ⟨n, y⟩,
    decidable_of_iff' _ (eq_iff α p _ _),
  inv_zero := congr_arg (quot.mk (r α p)) (by rw [inv_zero]),
  .. (infer_instance : has_inv (perfect_closure α p)),
  .. (infer_instance : comm_ring (perfect_closure α p)) }

theorem frobenius_mk [comm_monoid α] (p : ℕ) (x : ℕ × α) :
  frobenius (perfect_closure α p) p (quot.mk (r α p) x) = quot.mk _ (x.1, x.2^p) :=
begin
  unfold frobenius, cases x with n x, dsimp only,
  suffices : ∀ p':ℕ, (quot.mk (r α p) (n, x) ^ p' : perfect_closure α p) = quot.mk (r α p) (n, x ^ p'),
  { apply this },
  intro p, induction p with p ih,
  case nat.zero { apply r.sound, rw [nat.iterate₀ (frobenius_one _ _), pow_zero] },
  case nat.succ {
    rw [pow_succ, ih],
    symmetry,
    apply r.sound,
    simp only [pow_succ, nat.iterate₂ (frobenius_mul _ _)]
  }
end

def frobenius_equiv [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] :
  perfect_closure α p ≃ perfect_closure α p :=
{ to_fun := frobenius (perfect_closure α p) p,
  inv_fun := λ e, quot.lift_on e (λ x, quot.mk (r α p) (x.1 + 1, x.2)) (λ x y H,
    match x, y, H with
    | _, _, r.intro _ n x := quot.sound (r.intro _ _ _)
    end),
  left_inv := λ e, quot.induction_on e (λ ⟨m, x⟩, by rw frobenius_mk;
    symmetry; apply quot.sound; apply r.intro),
  right_inv := λ e, quot.induction_on e (λ ⟨m, x⟩, by rw frobenius_mk;
    symmetry; apply quot.sound; apply r.intro) }

theorem frobenius_equiv_apply [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] {x : perfect_closure α p} :
  frobenius_equiv α p x = frobenius _ p x :=
rfl

theorem nat_cast [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] (n x : ℕ) :
  (x : perfect_closure α p) = quot.mk (r α p) (n, x) :=
begin
  induction n with n ih,
  { induction x with x ih, {refl},
    rw [nat.cast_succ, nat.cast_succ, ih], refl },
  rw ih, apply quot.sound,
  conv {congr, skip, skip, rw ← frobenius_nat_cast α p x},
  apply r.intro
end

theorem int_cast [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] (x : ℤ) :
  (x : perfect_closure α p) = quot.mk (r α p) (0, x) :=
by induction x; simp only [int.cast_of_nat, int.cast_neg_succ_of_nat, nat_cast α p 0]; refl

theorem nat_cast_eq_iff [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] (x y : ℕ) :
  (x : perfect_closure α p) = y ↔ (x : α) = y :=
begin
  split; intro H,
  { rw [nat_cast α p 0, nat_cast α p 0, eq_iff'] at H,
    cases H with z H,
    simpa only [zero_add, nat.iterate₀ (frobenius_nat_cast α p _)] using H },
  rw [nat_cast α p 0, nat_cast α p 0, H]
end

instance [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] : char_p (perfect_closure α p) p :=
begin
  constructor, intro x, rw ← char_p.cast_eq_zero_iff α,
  rw [← nat.cast_zero, nat_cast_eq_iff, nat.cast_zero]
end

instance [discrete_field α] (p : ℕ) [nat.prime p] [char_p α p] : perfect_field (perfect_closure α p) p :=
{ pth_root := (frobenius_equiv α p).symm,
  frobenius_pth_root := (frobenius_equiv α p).apply_inverse_apply }

def of [monoid α] (p : ℕ) (x : α) : perfect_closure α p :=
quot.mk _ (0, x)

instance [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] : is_ring_hom (of α p) :=
{ map_one := rfl,
  map_mul := λ x y, rfl,
  map_add := λ x y, rfl }

theorem eq_pth_root [discrete_field α] (p : ℕ) [nat.prime p] [char_p α p] (m : ℕ) (x : α) :
  quot.mk (r α p) (m, x) = (perfect_field.pth_root p^[m] (of α p x) : perfect_closure α p) :=
begin
  unfold of,
  induction m with m ih, {refl},
  rw [nat.iterate_succ', ← ih]; refl
end

def UMP [discrete_field α] (p : ℕ) [nat.prime p] [char_p α p]
  (β : Type v) [discrete_field β] [char_p β p] [perfect_field β p] :
  { f : α → β // is_ring_hom f } ≃ { f : perfect_closure α p → β // is_ring_hom f } :=
{ to_fun := λ f, ⟨λ e, quot.lift_on e (λ x, perfect_field.pth_root p^[x.1] (f.1 x.2))
      (λ x y H, match x, y, H with | _, _, r.intro _ n x := by letI := f.2;
        simp only [is_monoid_hom.map_frobenius f.1, nat.iterate_succ, pth_root_frobenius]
      end),
    show f.1 1 = 1, from f.2.1,
    λ j k, quot.induction_on j $ λ ⟨m, x⟩, quot.induction_on k $ λ ⟨n, y⟩,
      show (perfect_field.pth_root p^[_] _) = (perfect_field.pth_root p^[_] _) * (perfect_field.pth_root p^[_] _),
      by letI := f.2; simp only [is_ring_hom.map_mul f.1, (nat.iterate₁ (λ x, (is_monoid_hom.map_frobenius f.1 p x).symm)).symm,
          @nat.iterate₂ β _ (*) (λ x y, is_ring_hom.map_mul (perfect_field.pth_root p))];
        rw [nat.iterate_add, nat.iterate_cancel (pth_root_frobenius β p),
          add_comm, nat.iterate_add, nat.iterate_cancel (pth_root_frobenius β p)],
    λ j k, quot.induction_on j $ λ ⟨m, x⟩, quot.induction_on k $ λ ⟨n, y⟩,
      show (perfect_field.pth_root p^[_] _) = (perfect_field.pth_root p^[_] _) + (perfect_field.pth_root p^[_] _),
      by letI := f.2; simp only [is_ring_hom.map_add f.1, (nat.iterate₁ (λ x, (is_monoid_hom.map_frobenius f.1 p x).symm)).symm,
          @nat.iterate₂ β _ (+) (λ x y, is_ring_hom.map_add (perfect_field.pth_root p))];
        rw [nat.iterate_add, nat.iterate_cancel (pth_root_frobenius β p),
          add_comm m, nat.iterate_add, nat.iterate_cancel (pth_root_frobenius β p)]⟩,
  inv_fun := λ f, ⟨f.1 ∘ of α p, @@is_ring_hom.comp _ _ _ _ _ _ f.2⟩,
  left_inv := λ ⟨f, hf⟩, subtype.eq rfl,
  right_inv := λ ⟨f, hf⟩, subtype.eq $ funext $ λ i, quot.induction_on i $ λ ⟨m, x⟩,
    show perfect_field.pth_root p^[m] (f _) = f _,
    by resetI; rw [eq_pth_root, @nat.iterate₁ _ _ _ _ f (λ x:perfect_closure α p, (is_ring_hom.pth_root p f).symm)] }

end perfect_closure
