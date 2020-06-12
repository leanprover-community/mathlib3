/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin
-/
import group_theory.free_abelian_group
import deprecated.ring

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

def lift : free_ring α →+* β :=
{ map_mul' := λ x y,
  begin
    refine free_abelian_group.induction_on y (mul_zero _).symm _ _ _;
      simp only [add_monoid_hom.to_fun_eq_coe],
    { intros L2,
      simp only [free_abelian_group.lift.of],
      refine free_abelian_group.induction_on x (zero_mul _).symm _ _ _,
      { intros L1, iterate 2 { erw free_abelian_group.lift.of },
        show list.prod (list.map f (_ ++ _)) = _, rw [list.map_append, list.prod_append] },
      { intros L1 ih,
        rw [←neg_mul_eq_neg_mul, add_monoid_hom.map_neg, add_monoid_hom.map_neg, ih, neg_mul_eq_neg_mul] },
      { intros x1 x2 ih1 ih2,
        rw [add_mul, add_monoid_hom.map_add, add_monoid_hom.map_add, ih1, ih2, add_mul] } },
    { intros L2 ih, simp only [mul_neg_eq_neg_mul_symm, add_monoid_hom.map_neg, ih] },
    { intros y1 y2 ih1 ih2, simp only [mul_add, add_monoid_hom.map_add, ih1, ih2] },
  end,
  map_one' := free_abelian_group.lift.of _ _,
  ..free_abelian_group.lift $ λ L, (list.map f L).prod }

@[simp] lemma lift_of (x : α) : lift f (of x) = f x :=
(free_abelian_group.lift.of _ _).trans $ one_mul _

@[simp] lemma lift_pow (x) (n : ℕ) : lift f (x ^ n) = lift f x ^ n :=
is_monoid_hom.map_pow _ x n

@[simp] lemma lift_comp_of (f : free_ring α →+* β) : lift (f ∘ of) = f :=
ring_hom.ext $ λ x, free_ring.induction_on x
  (by simp only [ring_hom.map_neg, ring_hom.map_one])
  (lift_of _)
  (λ x y ihx ihy, by simp only [ring_hom.map_add, ihx, ihy])
  (λ x y ihx ihy, by simp only [ring_hom.map_mul, ihx, ihy])

end lift

variables {β : Type v} (f : α → β)

def map : free_ring α →+* free_ring β :=
lift $ of ∘ f

@[simp] lemma map_of (x : α) : map f (of x) = of (f x) := lift_of _ _

end free_ring
