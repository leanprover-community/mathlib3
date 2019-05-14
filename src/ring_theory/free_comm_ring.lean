import group_theory.free_abelian_group data.equiv.algebra data.equiv.functor data.polynomial
import ring_theory.ideal_operations ring_theory.free_ring

universes u v

variables (α : Type u)

def free_comm_ring (α : Type u) : Type u :=
free_abelian_group $ multiplicative $ multiset α

namespace free_comm_ring

instance : comm_ring (free_comm_ring α) := free_abelian_group.comm_ring _

variables {α}
def of (x : α) : free_comm_ring α :=
free_abelian_group.of ([x] : multiset α)

@[elab_as_eliminator] protected lemma induction_on
  {C : free_comm_ring α → Prop} (z : free_comm_ring α)
  (hn1 : C (-1)) (hb : ∀ b, C (of b))
  (ha : ∀ x y, C x → C y → C (x + y))
  (hm : ∀ x y, C x → C y → C (x * y)) : C z :=
have hn : ∀ x, C x → C (-x), from λ x ih, neg_one_mul x ▸ hm _ _ hn1 ih,
have h1 : C 1, from neg_neg (1 : free_comm_ring α) ▸ hn _ hn1,
free_abelian_group.induction_on z
  (add_left_neg (1 : free_comm_ring α) ▸ ha _ _ hn1 h1)
  (λ m, multiset.induction_on m h1 $ λ a m ih, hm _ _ (hb a) ih)
  (λ m ih, hn _ ih)
  ha
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
  { intros s2, conv { to_lhs, dsimp only [(*), mul_zero_class.mul, semiring.mul, ring.mul, semigroup.mul, comm_ring.mul] },
    rw [free_abelian_group.lift.of, lift, free_abelian_group.lift.of],
    refine free_abelian_group.induction_on x (zero_mul _).symm _ _ _,
    { intros s1, iterate 3 { rw free_abelian_group.lift.of },
      calc _ = multiset.prod ((multiset.map f s1) + (multiset.map f s2)) :
          by {congr' 1, exact multiset.map_add _ _ _}
         ... = _ : multiset.prod_add _ _ },
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

@[simp] lemma lift_comp_of (f : free_comm_ring α → β) [is_ring_hom f] : lift (f ∘ of) = f :=
funext $ λ x, free_comm_ring.induction_on x
  (by rw [lift_neg, lift_one, is_ring_hom.map_neg f, is_ring_hom.map_one f])
  (lift_of _)
  (λ x y ihx ihy, by rw [lift_add, is_ring_hom.map_add f, ihx, ihy])
  (λ x y ihx ihy, by rw [lift_mul, is_ring_hom.map_mul f, ihx, ihy])

end lift

variables {β : Type v} (f : α → β)

def map : free_comm_ring α → free_comm_ring β :=
lift $ of ∘ f

@[simp] lemma map_zero : map f 0 = 0 := rfl
@[simp] lemma map_one : map f 1 = 1 := rfl
@[simp] lemma map_of (x : α) : map f (of x) = of (f x) := lift_of _ _
@[simp] lemma map_add (x y) : map f (x + y) = map f x + map f y := lift_add _ _ _
@[simp] lemma map_neg (x) : map f (-x) = -map f x := lift_neg _ _
@[simp] lemma map_sub (x y) : map f (x - y) = map f x - map f y := lift_sub _ _ _
@[simp] lemma map_mul (x y) : map f (x * y) = map f x * map f y := lift_mul _ _ _
@[simp] lemma map_pow (x) (n : ℕ) : map f (x ^ n) = (map f x) ^ n := lift_pow _ _ _

end free_comm_ring

instance free_ring_to_free_comm_ring (α) :
  has_coe (free_ring α) (free_comm_ring α) :=
⟨free_ring.lift free_comm_ring.of⟩

namespace free_ring_to_free_comm_ring
open function
variable (α)

instance : is_ring_hom (coe : free_ring α → free_comm_ring α) :=
free_ring.is_ring_hom free_comm_ring.of

@[simp] protected lemma coe_zero : ↑(0 : free_ring α) = (0 : free_comm_ring α) := rfl
@[simp] protected lemma coe_one : ↑(1 : free_ring α) = (1 : free_comm_ring α) := rfl

variable {α}

@[simp] protected lemma coe_of (a : α) : ↑(free_ring.of a) = free_comm_ring.of a :=
free_ring.lift_of _ _
@[simp] protected lemma coe_neg (x : free_ring α) : ↑(-x) = -(x : free_comm_ring α) :=
free_ring.lift_neg _ _
@[simp] protected lemma coe_add (x y : free_ring α) : ↑(x + y) = (x : free_comm_ring α) + y :=
free_ring.lift_add _ _ _
@[simp] protected lemma coe_sub (x y : free_ring α) : ↑(x - y) = (x : free_comm_ring α) - y :=
free_ring.lift_sub _ _ _
@[simp] protected lemma coe_mul (x y : free_ring α) : ↑(x * y) = (x : free_comm_ring α) * y :=
free_ring.lift_mul _ _ _

variable (α)

protected lemma surjective : surjective (coe : free_ring α → free_comm_ring α) :=
λ x,
begin
  apply free_comm_ring.induction_on x,
  { use -1, refl },
  { intro x, use free_ring.of x, refl },
  { rintros _ _ ⟨x, rfl⟩ ⟨y, rfl⟩, use x + y, exact free_ring.lift_add _ _ _ },
  { rintros _ _ ⟨x, rfl⟩ ⟨y, rfl⟩, use x * y, exact free_ring.lift_mul _ _ _ }
end

lemma coe_eq :
  (coe : free_ring α → free_comm_ring α) =
  @functor.map free_abelian_group _ _ _ (λ (l : list α), (l : multiset α)) :=
begin
  funext,
  apply @free_abelian_group.lift.ext _ _ _
    (coe : free_ring α → free_comm_ring α) _ _ (free_abelian_group.lift.is_add_group_hom _),
  intros x,
  change free_ring.lift free_comm_ring.of (free_abelian_group.of x) = _,
  change _ = free_abelian_group.of (↑x),
  induction x with hd tl ih, {refl},
  simp only [*, free_ring.lift, free_comm_ring.of, free_abelian_group.of, free_abelian_group.lift,
    free_group.of, free_group.to_group, free_group.to_group.aux,
    mul_one, free_group.quot_lift_mk, abelianization.lift.of, bool.cond_tt, list.prod_cons,
    cond, list.prod_nil, list.map] at *,
  refl
end

def subsingleton_equiv [subsingleton α] :
  free_ring α ≃r free_comm_ring α :=
{ to_equiv := @functor.map_equiv _ _ free_abelian_group _ _ $ multiset.subsingleton_equiv α,
  hom :=
  begin
    delta functor.map_equiv,
    rw congr_arg is_ring_hom _,
    work_on_goal 2 { symmetry, exact coe_eq α },
    apply_instance
  end }

instance [subsingleton α] : comm_ring (free_ring α) :=
{ mul_comm := λ x y,
  by rw [← (subsingleton_equiv α).left_inv (y * x),
        is_ring_hom.map_mul ((subsingleton_equiv α).to_equiv).to_fun,
        mul_comm,
        ← is_ring_hom.map_mul ((subsingleton_equiv α).to_equiv).to_fun,
        (subsingleton_equiv α).left_inv],
  .. free_ring.ring α }

end free_ring_to_free_comm_ring

variables [decidable_eq α]

def free_comm_ring_equiv_mv_polynomial_int :
  free_comm_ring α ≃r mv_polynomial α ℤ :=
{ to_fun  := free_comm_ring.lift $ λ a, mv_polynomial.X a,
  inv_fun := mv_polynomial.eval₂ coe free_comm_ring.of,
  hom := by apply_instance,
  left_inv :=
  begin
    intro x,
    haveI : is_semiring_hom (coe : int → free_comm_ring α) :=
      @@is_ring_hom.is_semiring_hom _ _ _ (@@int.cast.is_ring_hom _),
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intro s,
      refine multiset.induction_on s rfl _,
      intros hd tl ih,
      show mv_polynomial.eval₂ coe free_comm_ring.of
        (free_comm_ring.lift (λ a, mv_polynomial.X a)
        (free_comm_ring.of hd * free_abelian_group.of tl)) =
        free_comm_ring.of hd * free_abelian_group.of tl,
      rw [free_comm_ring.lift_mul, free_comm_ring.lift_of,
        mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X, ih] },
    { intros s ih,
      rw [free_comm_ring.lift_neg, ← neg_one_mul, mv_polynomial.eval₂_mul,
        ← mv_polynomial.C_1, ← mv_polynomial.C_neg, mv_polynomial.eval₂_C,
        int.cast_neg, int.cast_one, neg_one_mul, ih] },
    { intros x₁ x₂ ih₁ ih₂, rw [free_comm_ring.lift_add, mv_polynomial.eval₂_add, ih₁, ih₂] }
  end,
  right_inv :=
  begin
    intro x,
    haveI : is_semiring_hom (coe : int → free_comm_ring α) :=
      @@is_ring_hom.is_semiring_hom _ _ _ (@@int.cast.is_ring_hom _),
    have : ∀ i : ℤ, free_comm_ring.lift (λ (a : α), mv_polynomial.X a) ↑i = mv_polynomial.C i,
    { exact λ i, int.induction_on i
      (by rw [int.cast_zero, free_comm_ring.lift_zero, mv_polynomial.C_0])
      (λ i ih, by rw [int.cast_add, int.cast_one, free_comm_ring.lift_add,
        free_comm_ring.lift_one, ih, mv_polynomial.C_add, mv_polynomial.C_1])
      (λ i ih, by rw [int.cast_sub, int.cast_one, free_comm_ring.lift_sub,
        free_comm_ring.lift_one, ih, mv_polynomial.C_sub, mv_polynomial.C_1]) },
    apply mv_polynomial.induction_on x,
    { intro i, rw [mv_polynomial.eval₂_C, this] },
    { intros p q ihp ihq, rw [mv_polynomial.eval₂_add, free_comm_ring.lift_add, ihp, ihq] },
    { intros p a ih,
      rw [mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X,
        free_comm_ring.lift_mul, free_comm_ring.lift_of, ih] }
  end }

def free_comm_ring_pempty_equiv_int : free_comm_ring pempty.{u+1} ≃r ℤ :=
ring_equiv.trans (free_comm_ring_equiv_mv_polynomial_int _) (mv_polynomial.pempty_ring_equiv _)

def free_comm_ring_punit_equiv_polynomial_int : free_comm_ring punit.{u+1} ≃r polynomial ℤ :=
ring_equiv.trans (free_comm_ring_equiv_mv_polynomial_int _) (mv_polynomial.punit_ring_equiv _)

open free_ring_to_free_comm_ring

def free_ring_pempty_equiv_int : free_ring pempty.{u+1} ≃r ℤ :=
ring_equiv.trans (subsingleton_equiv _) free_comm_ring_pempty_equiv_int

def free_ring_punit_equiv_polynomial_int : free_ring punit.{u+1} ≃r polynomial ℤ :=
ring_equiv.trans (subsingleton_equiv _) free_comm_ring_punit_equiv_polynomial_int
