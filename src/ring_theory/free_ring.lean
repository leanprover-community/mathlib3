/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin
-/
import group_theory.free_abelian_group

universes u v

def free_ring (α : Type u) : Type u :=
free_abelian_group $ free_monoid α

namespace free_ring

variables (α : Type u)

instance : ring (free_ring α) := free_abelian_group.ring _

instance : inhabited (free_ring α) := ⟨0⟩

variables {α}
def of (x : α) : free_ring α :=
free_abelian_group.of [x]

@[elab_as_eliminator] protected lemma induction_on
  {C : free_ring α → Prop} (z : free_ring α)
  (hn1 : C (-1)) (hb : ∀ b, C (of b))
  (ha : ∀ x y, C x → C y → C (x + y))
  (hm : ∀ x y, C x → C y → C (x * y)) : C z :=
have hn : ∀ x, C x → C (-x), from λ x ih, neg_one_mul x ▸ hm _ _ hn1 ih,
have h1 : C 1, from neg_neg (1 : free_ring α) ▸ hn _ hn1,
free_abelian_group.induction_on z
  (add_left_neg (1 : free_ring α) ▸ ha _ _ hn1 h1)
  (λ m, list.rec_on m h1 $ λ a m ih, hm _ _ (hb a) ih)
  (λ m ih, hn _ ih)
  ha

section lift

variables {β : Type v} [ring β] (f : α → β)

def lift : free_ring α → β :=
free_abelian_group.lift $ λ L, (list.map f L).prod

@[simp] lemma lift_zero : lift f 0 = 0 := rfl

@[simp] lemma lift_one : lift f 1 = 1 :=
free_abelian_group.lift.of _ _

@[simp] lemma lift_of (x : α) : lift f (of x) = f x :=
(free_abelian_group.lift.of _ _).trans $ one_mul _

@[simp] lemma lift_add (x y) : lift f (x + y) = lift f x + lift f y :=
free_abelian_group.lift.add _ _ _

@[simp] lemma lift_neg (x) : lift f (-x) = -lift f x :=
free_abelian_group.lift.neg _ _

@[simp] lemma lift_sub (x y) : lift f (x - y) = lift f x - lift f y :=
free_abelian_group.lift.sub _ _ _

@[simp] lemma lift_mul (x y) : lift f (x * y) = lift f x * lift f y :=
begin
  refine free_abelian_group.induction_on y (mul_zero _).symm _ _ _,
  { intros L2,
    conv_lhs { dsimp only [free_abelian_group.mul_def] },
    rw [free_abelian_group.lift.of, lift, free_abelian_group.lift.of],
    refine free_abelian_group.induction_on x (zero_mul _).symm _ _ _,
    { intros L1, iterate 3 { rw free_abelian_group.lift.of },
      show list.prod (list.map f (_ ++ _)) = _, rw [list.map_append, list.prod_append] },
    { intros L1 ih, iterate 3 { rw free_abelian_group.lift.neg }, rw [ih, neg_mul_eq_neg_mul] },
    { intros x1 x2 ih1 ih2, iterate 3 { rw free_abelian_group.lift.add }, rw [ih1, ih2, add_mul] } },
  { intros L2 ih, rw [mul_neg_eq_neg_mul_symm, lift_neg, lift_neg, mul_neg_eq_neg_mul_symm, ih] },
  { intros y1 y2 ih1 ih2, rw [mul_add, lift_add, lift_add, mul_add, ih1, ih2] },
end

instance : is_ring_hom (lift f) :=
{ map_one := lift_one f,
  map_mul := lift_mul f,
  map_add := lift_add f }

@[simp] lemma lift_pow (x) (n : ℕ) : lift f (x ^ n) = lift f x ^ n :=
is_semiring_hom.map_pow _ x n

@[simp] lemma lift_comp_of (f : free_ring α → β) [is_ring_hom f] : lift (f ∘ of) = f :=
funext $ λ x, free_ring.induction_on x
  (by rw [lift_neg, lift_one, is_ring_hom.map_neg f, is_ring_hom.map_one f])
  (lift_of _)
  (λ x y ihx ihy, by rw [lift_add, is_ring_hom.map_add f, ihx, ihy])
  (λ x y ihx ihy, by rw [lift_mul, is_ring_hom.map_mul f, ihx, ihy])

end lift

variables {β : Type v} (f : α → β)

def map : free_ring α → free_ring β :=
lift $ of ∘ f

@[simp] lemma map_zero : map f 0 = 0 := rfl
@[simp] lemma map_one : map f 1 = 1 := rfl
@[simp] lemma map_of (x : α) : map f (of x) = of (f x) := lift_of _ _
@[simp] lemma map_add (x y) : map f (x + y) = map f x + map f y := lift_add _ _ _
@[simp] lemma map_neg (x) : map f (-x) = -map f x := lift_neg _ _
@[simp] lemma map_sub (x y) : map f (x - y) = map f x - map f y := lift_sub _ _ _
@[simp] lemma map_mul (x y) : map f (x * y) = map f x * map f y := lift_mul _ _ _
@[simp] lemma map_pow (x) (n : ℕ) : map f (x ^ n) = (map f x) ^ n := lift_pow _ _ _

end free_ring
