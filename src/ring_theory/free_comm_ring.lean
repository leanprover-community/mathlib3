import group_theory.free_abelian_group

universes u v

def free_comm_ring (α : Type u) : Type u :=
free_abelian_group $ multiset α

namespace free_comm_ring

variables (α : Type u)

instance : add_comm_group (free_comm_ring α) :=
{ .. free_abelian_group.add_comm_group (multiset α) }

instance : semigroup (free_comm_ring α) :=
{ mul := λ x, free_abelian_group.lift $ λ s2, free_abelian_group.lift (λ s1, free_abelian_group.of $ s1 + s2) x,
  mul_assoc := λ x y z, begin
    unfold has_mul.mul,
    refine free_abelian_group.induction_on z rfl _ _ _,
    { intros s3, rw [free_abelian_group.lift.of, free_abelian_group.lift.of],
      refine free_abelian_group.induction_on y rfl _ _ _,
      { intros s2, iterate 3 { rw free_abelian_group.lift.of },
        refine free_abelian_group.induction_on x rfl _ _ _,
        { intros s1, iterate 3 { rw free_abelian_group.lift.of }, rw add_assoc },
        { intros s1 ih, iterate 3 { rw free_abelian_group.lift.neg }, rw ih },
        { intros x1 x2 ih1 ih2, iterate 3 { rw free_abelian_group.lift.add }, rw [ih1, ih2] } },
      { intros s2 ih, iterate 4 { rw free_abelian_group.lift.neg }, rw ih },
      { intros y1 y2 ih1 ih2, iterate 4 { rw free_abelian_group.lift.add }, rw [ih1, ih2] } },
    { intros s3 ih, iterate 3 { rw free_abelian_group.lift.neg }, rw ih },
    { intros z1 z2 ih1 ih2, iterate 2 { rw free_abelian_group.lift.add }, rw [ih1, ih2],
      exact (free_abelian_group.lift.add _ _ _).symm }
  end }

instance : ring (free_comm_ring α) :=
{ one := free_abelian_group.of 0,
  mul_one := λ x, begin
    unfold has_mul.mul semigroup.mul has_one.one,
    rw free_abelian_group.lift.of,
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intros s, rw [free_abelian_group.lift.of, add_zero] },
    { intros s ih, rw [free_abelian_group.lift.neg, ih] },
    { intros x1 x2 ih1 ih2, rw [free_abelian_group.lift.add, ih1, ih2] }
  end,
  one_mul := λ x, begin
    unfold has_mul.mul semigroup.mul has_one.one,
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intros s, rw [free_abelian_group.lift.of, free_abelian_group.lift.of, zero_add] },
    { intros s ih, rw [free_abelian_group.lift.neg, ih] },
    { intros x1 x2 ih1 ih2, rw [free_abelian_group.lift.add, ih1, ih2] }
  end,
  left_distrib := λ x y z, free_abelian_group.lift.add _ _ _,
  right_distrib := λ x y z, begin
    unfold has_mul.mul semigroup.mul,
    refine free_abelian_group.induction_on z rfl _ _ _,
    { intros s, iterate 3 { rw free_abelian_group.lift.of }, rw free_abelian_group.lift.add, refl },
    { intros s ih, iterate 3 { rw free_abelian_group.lift.neg }, rw [ih, neg_add], refl },
    { intros z1 z2 ih1 ih2, iterate 3 { rw free_abelian_group.lift.add }, rw [ih1, ih2],
      rw [add_assoc, add_assoc], congr' 1, apply add_left_comm }
  end,
  .. free_comm_ring.add_comm_group α,
  .. free_comm_ring.semigroup α }

instance : comm_ring (free_comm_ring α) :=
{ mul_comm := λ x y, begin
    refine free_abelian_group.induction_on x (zero_mul y) _ _ _,
    { intros s, refine free_abelian_group.induction_on y (zero_mul _).symm _ _ _,
      { intros t, unfold has_mul.mul semigroup.mul ring.mul,
        iterate 4 { rw free_abelian_group.lift.of }, rw add_comm },
      { intros t ih, rw [mul_neg_eq_neg_mul_symm, ih, neg_mul_eq_neg_mul] },
      { intros y1 y2 ih1 ih2, rw [mul_add, add_mul, ih1, ih2] } },
    { intros s ih, rw [neg_mul_eq_neg_mul_symm, ih, neg_mul_eq_mul_neg] },
    { intros x1 x2 ih1 ih2, rw [add_mul, mul_add, ih1, ih2] }
  end
  .. free_comm_ring.ring α }

variables {α}
def of (x : α) : free_comm_ring α :=
free_abelian_group.of [x]

section lift

variables {β : Type v} [comm_ring β] (f : α → β)

def lift : free_comm_ring α → β :=
free_abelian_group.lift $ λ s, (s.map f).prod

@[simp] lemma lift_zero : lift f 0 = 0 := rfl

@[simp] lemma lift_one : lift f 1 = 1 :=
free_abelian_group.lift.of _ _

@[simp] lemma lift_of (x : α) : lift f (of x) = f x :=
(free_abelian_group.lift.of _ _).trans $ mul_one _

@[simp] lemma lift_add (x y) : lift f (x + y) = lift f x + lift f y :=
free_abelian_group.lift.add _ _ _

@[simp] lemma lift_neg (x) : lift f (-x) = -lift f x :=
free_abelian_group.lift.neg _ _

@[simp] lemma lift_sub (x y) : lift f (x - y) = lift f x - lift f y :=
free_abelian_group.lift.sub _ _ _

@[simp] lemma lift_mul (x y) : lift f (x * y) = lift f x * lift f y :=
begin
  refine free_abelian_group.induction_on y (mul_zero _).symm _ _ _,
  { intros s2, conv { to_lhs, dsimp only [(*), mul_zero_class.mul, semiring.mul, ring.mul, semigroup.mul] },
    rw [free_abelian_group.lift.of, lift, free_abelian_group.lift.of],
    refine free_abelian_group.induction_on x (zero_mul _).symm _ _ _,
    { intros s1, iterate 3 { rw free_abelian_group.lift.of }, rw [multiset.map_add, multiset.prod_add] },
    { intros s1 ih, iterate 3 { rw free_abelian_group.lift.neg }, rw [ih, neg_mul_eq_neg_mul] },
    { intros x1 x2 ih1 ih2, iterate 3 { rw free_abelian_group.lift.add }, rw [ih1, ih2, add_mul] } },
  { intros s2 ih, rw [mul_neg_eq_neg_mul_symm, lift_neg, lift_neg, mul_neg_eq_neg_mul_symm, ih] },
  { intros y1 y2 ih1 ih2, rw [mul_add, lift_add, lift_add, mul_add, ih1, ih2] },
end

instance : is_ring_hom (lift f) :=
{ map_one := lift_one f,
  map_mul := lift_mul f,
  map_add := lift_add f }

@[simp] lemma lift_pow (x) (n : ℕ) : lift f (x ^ n) = lift f x ^ n :=
is_semiring_hom.map_pow _ x n

theorem lift_unique (f : free_comm_ring α → β) [is_ring_hom f] : f = lift (f ∘ of) :=
funext $ λ x, @@free_abelian_group.lift.ext _ _ _
  (is_ring_hom.is_add_group_hom f)
  (is_ring_hom.is_add_group_hom $ lift $ f ∘ of)
  (λ s, multiset.induction_on s ((is_ring_hom.map_one f).trans $ eq.symm $ lift_one _)
    (λ hd tl ih, show f (of hd * free_abelian_group.of tl) = lift (f ∘ of) (of hd * free_abelian_group.of tl),
      by rw [is_ring_hom.map_mul f, lift_mul, lift_of, ih]))

end lift

variables {β : Type v} (f : α → β)

def map : free_comm_ring α → free_comm_ring β :=
lift $ of ∘ f

instance : monad free_comm_ring :=
{ map := λ _ _, map,
  pure := λ _, of,
  bind := λ _ _ x f, lift f x }

end free_comm_ring
