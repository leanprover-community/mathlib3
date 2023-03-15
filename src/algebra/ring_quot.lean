/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.algebra.hom
import ring_theory.ideal.quotient

/-!
# Quotients of non-commutative rings

Unfortunately, ideals have only been developed in the commutative case as `ideal`,
and it's not immediately clear how one should formalise ideals in the non-commutative case.

In this file, we directly define the quotient of a semiring by any relation,
by building a bigger relation that represents the ideal generated by that relation.

We prove the universal properties of the quotient, and recommend avoiding relying on the actual
definition, which is made irreducible for this purpose.

Since everything runs in parallel for quotients of `R`-algebras, we do that case at the same time.
-/

universes u₁ u₂ u₃ u₄

variables {R : Type u₁} [semiring R]
variables {S : Type u₂} [comm_semiring S]
variables {A : Type u₃} [semiring A] [algebra S A]

namespace ring_con

instance (c : ring_con A) : algebra S c.quotient :=
{ smul := (•),
  to_ring_hom := c.mk'.comp (algebra_map S A),
  commutes' := λ r, quotient.ind' $ by exact λ a, congr_arg quotient.mk' $ algebra.commutes _ _,
  smul_def' := λ r, quotient.ind' $ by exact λ a, congr_arg quotient.mk' $ algebra.smul_def _ _ }

end ring_con

namespace ring_quot

/--
Given an arbitrary relation `r` on a ring, we strengthen it to a relation `rel r`,
such that the equivalence relation generated by `rel r` has `x ~ y` if and only if
`x - y` is in the ideal generated by elements `a - b` such that `r a b`.
-/
inductive rel (r : R → R → Prop) : R → R → Prop
| of ⦃x y : R⦄ (h : r x y) : rel x y
| add_left ⦃a b c⦄ : rel a b → rel (a + c) (b + c)
| mul_left ⦃a b c⦄ : rel a b → rel (a * c) (b * c)
| mul_right ⦃a b c⦄ : rel b c → rel (a * b) (a * c)

theorem rel.add_right {r : R → R → Prop} ⦃a b c : R⦄ (h : rel r b c) : rel r (a + b) (a + c) :=
by { rw [add_comm a b, add_comm a c], exact rel.add_left h }

theorem rel.neg {R : Type u₁} [ring R] {r : R → R → Prop} ⦃a b : R⦄ (h : rel r a b) :
  rel r (-a) (-b) :=
by simp only [neg_eq_neg_one_mul a, neg_eq_neg_one_mul b, rel.mul_right h]

theorem rel.sub_left {R : Type u₁} [ring R] {r : R → R → Prop} ⦃a b c : R⦄ (h : rel r a b) :
  rel r (a - c) (b - c) :=
by simp only [sub_eq_add_neg, h.add_left]

theorem rel.sub_right {R : Type u₁} [ring R] {r : R → R → Prop} ⦃a b c : R⦄ (h : rel r b c) :
  rel r (a - b) (a - c) :=
by simp only [sub_eq_add_neg, h.neg.add_right]

theorem rel.smul {r : A → A → Prop} (k : S) ⦃a b : A⦄ (h : rel r a b) : rel r (k • a) (k • b) :=
by simp only [algebra.smul_def, rel.mul_right h]

/-- `eqv_gen (ring_quot.rel r)` is a ring congruence. -/
def ring_con (r : R → R → Prop) : ring_con R :=
{ r := eqv_gen (rel r),
  iseqv := eqv_gen.is_equivalence _,
  add' := λ a b c d hab hcd, begin
    induction hab with a' b' hab e a' b' hab' _ c' d' e hcd' hde' ihcd' ihde' generalizing c d,
    { refine (eqv_gen.rel _ _ hab.add_left).trans _ _ _ _,
      induction hcd with c' d' hcd f c' d' hcd' habcd' c' d' f' hcd' hdf' hbcd' hbcf',
      { exact (eqv_gen.rel _ _ hcd.add_right), },
      { exact (eqv_gen.refl _), },
      { exact (habcd'.symm _ _), },
      { exact hbcd'.trans _ _ _ hbcf', }, },
    { induction hcd with c' d' hcd f c' d' hcd' habcd' c' d' f' hcd' hdf' hbcd' hbcf',
      { exact (eqv_gen.rel _ _ hcd.add_right), },
      { exact (eqv_gen.refl _), },
      { exact (eqv_gen.symm _ _ habcd'), },
      { exact hbcd'.trans _ _ _ hbcf' }, },
    { exact (hab_ih _ _ $ hcd.symm _ _).symm _ _, },
    { exact (ihcd' _ _ hcd).trans _ _ _ (ihde' _ _ $ eqv_gen.refl _), },
  end,
  mul' := λ a b c d hab hcd, begin
    induction hab with a' b' hab e a' b' hab' _ c' d' e hcd' hde' ihcd' ihde' generalizing c d,
    { refine (eqv_gen.rel _ _ hab.mul_left).trans _ _ _ _,
      induction hcd with c' d' hcd f c' d' hcd' habcd' c' d' f' hcd' hdf' hbcd' hbcf',
      { exact (eqv_gen.rel _ _ hcd.mul_right), },
      { exact (eqv_gen.refl _), },
      { exact (habcd'.symm _ _), },
      { exact hbcd'.trans _ _ _ hbcf', }, },
    { induction hcd with c' d' hcd f c' d' hcd' habcd' c' d' f' hcd' hdf' hbcd' hbcf',
      { exact (eqv_gen.rel _ _ hcd.mul_right), },
      { exact (eqv_gen.refl _), },
      { exact (eqv_gen.symm _ _ habcd'), },
      { exact hbcd'.trans _ _ _ hbcf' }, },
    { exact (hab_ih _ _ $ hcd.symm _ _).symm _ _, },
    { exact (ihcd' _ _ hcd).trans _ _ _ (ihde' _ _ $ eqv_gen.refl _), },
  end }

lemma eqv_gen_rel_eq (r : R → R → Prop) : eqv_gen (rel r) = ring_con_gen.rel r :=
begin
  ext x₁ x₂,
  split,
  { intro h,
    induction h with x₃ x₄ h₃₄,
    { induction h₃₄ with _ dfg h₃₄ x₃ x₄ x₅ h₃₄',
      { exact ring_con_gen.rel.of _ _ ‹_› },
      { exact h₃₄_ih.add (ring_con_gen.rel.refl _) },
      { exact h₃₄_ih.mul (ring_con_gen.rel.refl _) },
      { exact (ring_con_gen.rel.refl _).mul h₃₄_ih} },
    { exact ring_con_gen.rel.refl _ },
    { exact ring_con_gen.rel.symm ‹_› },
    { exact ring_con_gen.rel.trans ‹_› ‹_› } },
  { intro h,
    induction h,
    { exact eqv_gen.rel _ _ (rel.of ‹_›), },
    { exact (ring_quot.ring_con r).refl _, },
    { exact (ring_quot.ring_con r).symm ‹_›, },
    { exact (ring_quot.ring_con r).trans ‹_› ‹_›, },
    { exact (ring_quot.ring_con r).add ‹_› ‹_›, },
    { exact (ring_quot.ring_con r).mul ‹_› ‹_›, } }
end

end ring_quot

/-- The quotient of a ring by an arbitrary relation. -/
structure ring_quot (r : R → R → Prop) :=
(to_quot : quot (ring_quot.rel r))

namespace ring_quot

variable (r : R → R → Prop)

@[irreducible] private def nat_cast (n : ℕ) : ring_quot r := ⟨quot.mk _ n⟩
@[irreducible] private def zero : ring_quot r := ⟨quot.mk _ 0⟩
@[irreducible] private def one : ring_quot r := ⟨quot.mk _ 1⟩
@[irreducible] private def add : ring_quot r → ring_quot r → ring_quot r
| ⟨a⟩ ⟨b⟩ := ⟨quot.map₂ (+) rel.add_right rel.add_left a b⟩
@[irreducible] private def mul : ring_quot r → ring_quot r → ring_quot r
| ⟨a⟩ ⟨b⟩ := ⟨quot.map₂ (*) rel.mul_right rel.mul_left a b⟩
@[irreducible] private def neg {R : Type u₁} [ring R] (r : R → R → Prop) : ring_quot r → ring_quot r
| ⟨a⟩:= ⟨quot.map (λ a, -a) rel.neg a⟩
@[irreducible] private def sub {R : Type u₁} [ring R] (r : R → R → Prop) :
  ring_quot r → ring_quot r → ring_quot r
| ⟨a⟩ ⟨b⟩ := ⟨quot.map₂ has_sub.sub rel.sub_right rel.sub_left a b⟩
@[irreducible] private def npow (n : ℕ) : ring_quot r → ring_quot r
| ⟨a⟩ := ⟨quot.lift
          (λ a, quot.mk (ring_quot.rel r) (a ^ n))
          (λ a b (h : rel r a b), begin
            -- note we can't define a `rel.pow` as `rel` isn't reflexive so `rel r 1 1` isn't true
            dsimp only,
            induction n,
            { rw [pow_zero, pow_zero] },
            { rw [pow_succ, pow_succ],
              simpa only [mul] using congr_arg2 (λ x y, mul r ⟨x⟩ ⟨y⟩) (quot.sound h) n_ih }
          end)
          a⟩
@[irreducible] private def smul [algebra S R] (n : S) : ring_quot r → ring_quot r
| ⟨a⟩ := ⟨quot.map (λ a, n • a) (rel.smul n) a⟩

instance : has_zero (ring_quot r) := ⟨zero r⟩
instance : has_one (ring_quot r) := ⟨one r⟩
instance : has_add (ring_quot r) := ⟨add r⟩
instance : has_mul (ring_quot r) := ⟨mul r⟩
instance : has_pow (ring_quot r) ℕ := ⟨λ x n, npow r n x⟩
instance {R : Type u₁} [ring R] (r : R → R → Prop) : has_neg (ring_quot r) := ⟨neg r⟩
instance {R : Type u₁} [ring R] (r : R → R → Prop) : has_sub (ring_quot r) := ⟨sub r⟩
instance [algebra S R] : has_smul S (ring_quot r) := ⟨smul r⟩

lemma zero_quot : (⟨quot.mk _ 0⟩ : ring_quot r) = 0 := show _ = zero r, by rw zero
lemma one_quot : (⟨quot.mk _ 1⟩ : ring_quot r) = 1 := show _ = one r, by rw one
lemma add_quot {a b} : (⟨quot.mk _ a⟩ + ⟨quot.mk _ b⟩ : ring_quot r) = ⟨quot.mk _ (a + b)⟩ :=
by { show add r _ _ = _, rw add, refl }
lemma mul_quot {a b} : (⟨quot.mk _ a⟩ * ⟨quot.mk _ b⟩ : ring_quot r) = ⟨quot.mk _ (a * b)⟩ :=
by { show mul r _ _ = _, rw mul, refl }
lemma pow_quot {a} {n : ℕ}: (⟨quot.mk _ a⟩ ^ n : ring_quot r) = ⟨quot.mk _ (a ^ n)⟩ :=
by { show npow r _ _ = _, rw npow }
lemma neg_quot {R : Type u₁} [ring R] (r : R → R → Prop) {a} :
  (-⟨quot.mk _ a⟩ : ring_quot r) = ⟨quot.mk _ (-a)⟩ :=
by { show neg r _ = _, rw neg, refl }
lemma sub_quot {R : Type u₁} [ring R] (r : R → R → Prop) {a b} :
  (⟨quot.mk _ a⟩ - ⟨ quot.mk _ b⟩ : ring_quot r) = ⟨quot.mk _ (a - b)⟩ :=
by { show sub r _ _ = _, rw sub, refl }
lemma smul_quot [algebra S R] {n : S} {a : R} :
  (n • ⟨quot.mk _ a⟩ : ring_quot r) = ⟨quot.mk _ (n • a)⟩ :=
by { show smul r _ _ = _, rw smul, refl }

instance (r : R → R → Prop) : semiring (ring_quot r) :=
{ add           := (+),
  mul           := (*),
  zero          := 0,
  one           := 1,
  nat_cast      := nat_cast r,
  nat_cast_zero := by simp [nat.cast, nat_cast, ← zero_quot],
  nat_cast_succ := by simp [nat.cast, nat_cast, ← one_quot, add_quot],
  add_assoc     := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [add_quot, add_assoc] },
  zero_add      := by { rintros ⟨⟨⟩⟩, simp [add_quot, ← zero_quot] },
  add_zero      := by { rintros ⟨⟨⟩⟩, simp [add_quot, ← zero_quot], },
  zero_mul      := by { rintros ⟨⟨⟩⟩, simp [mul_quot, ← zero_quot], },
  mul_zero      := by { rintros ⟨⟨⟩⟩, simp [mul_quot, ← zero_quot], },
  add_comm      := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [add_quot, add_comm], },
  mul_assoc     := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [mul_quot, mul_assoc] },
  one_mul       := by { rintros ⟨⟨⟩⟩, simp [mul_quot, ← one_quot] },
  mul_one       := by { rintros ⟨⟨⟩⟩, simp [mul_quot, ← one_quot] },
  left_distrib  := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [mul_quot, add_quot, left_distrib] },
  right_distrib := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [mul_quot, add_quot, right_distrib] },
  npow          := λ n x, x ^ n,
  npow_zero'    := by { rintros ⟨⟨⟩⟩, simp [pow_quot, ← one_quot] },
  npow_succ'    := by { rintros n ⟨⟨⟩⟩, simp [pow_quot, mul_quot, pow_succ] },
  nsmul         := (•),
  nsmul_zero'   := by { rintros ⟨⟨⟩⟩, simp [smul_quot, ← zero_quot] },
  nsmul_succ'   := by { rintros n ⟨⟨⟩⟩, simp [smul_quot, add_quot, add_mul, add_comm] } }

instance {R : Type u₁} [ring R] (r : R → R → Prop) : ring (ring_quot r) :=
{ neg           := has_neg.neg,
  add_left_neg  := by { rintros ⟨⟨⟩⟩, simp [neg_quot, add_quot, ← zero_quot], },
  sub            := has_sub.sub,
  sub_eq_add_neg := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [neg_quot, sub_quot, add_quot, sub_eq_add_neg] },
  zsmul          := (•),
  zsmul_zero'   := by { rintros ⟨⟨⟩⟩, simp [smul_quot, ← zero_quot] },
  zsmul_succ'   := by { rintros n ⟨⟨⟩⟩, simp [smul_quot, add_quot, add_mul, add_comm] },
  zsmul_neg'   := by { rintros n ⟨⟨⟩⟩, simp [smul_quot, neg_quot, add_mul] },
  .. (ring_quot.semiring r) }

instance {R : Type u₁} [comm_semiring R] (r : R → R → Prop) : comm_semiring (ring_quot r) :=
{ mul_comm := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [mul_quot, mul_comm], }
  .. (ring_quot.semiring r) }

instance {R : Type u₁} [comm_ring R] (r : R → R → Prop) : comm_ring (ring_quot r) :=
{ .. (ring_quot.comm_semiring r),
  .. (ring_quot.ring r) }

instance (r : R → R → Prop) : inhabited (ring_quot r) := ⟨0⟩

instance [algebra S R] (r : R → R → Prop) : algebra S (ring_quot r) :=
{ smul      := (•),
  to_fun    := λ r, ⟨quot.mk _ (algebra_map S R r)⟩,
  map_one'  := by simp [← one_quot],
  map_mul'  := by simp [mul_quot],
  map_zero' := by simp [← zero_quot],
  map_add'  := by simp [add_quot],
  commutes' := λ r, by { rintro ⟨⟨a⟩⟩, simp [algebra.commutes, mul_quot] },
  smul_def' := λ r, by { rintro ⟨⟨a⟩⟩, simp [smul_quot, algebra.smul_def, mul_quot], }, }

/--
The quotient map from a ring to its quotient, as a homomorphism of rings.
-/
@[irreducible] def mk_ring_hom (r : R → R → Prop) : R →+* ring_quot r :=
{ to_fun := λ x, ⟨quot.mk _ x⟩,
  map_one'  := by simp [← one_quot],
  map_mul'  := by simp [mul_quot],
  map_zero' := by simp [← zero_quot],
  map_add'  := by simp [add_quot], }

lemma mk_ring_hom_rel {r : R → R → Prop} {x y : R} (w : r x y) :
  mk_ring_hom r x = mk_ring_hom r y :=
by simp [mk_ring_hom, quot.sound (rel.of w)]

lemma mk_ring_hom_surjective (r : R → R → Prop) : function.surjective (mk_ring_hom r) :=
by { dsimp [mk_ring_hom], rintro ⟨⟨⟩⟩, simp, }

@[ext]
lemma ring_quot_ext {T : Type u₄} [semiring T] {r : R → R → Prop} (f g : ring_quot r →+* T)
  (w : f.comp (mk_ring_hom r) = g.comp (mk_ring_hom r)) : f = g :=
begin
  ext,
  rcases mk_ring_hom_surjective r x with ⟨x, rfl⟩,
  exact (ring_hom.congr_fun w x : _),
end

variables  {T : Type u₄} [semiring T]

/--
Any ring homomorphism `f : R →+* T` which respects a relation `r : R → R → Prop`
factors uniquely through a morphism `ring_quot r →+* T`.
-/
@[irreducible] def lift {r : R → R → Prop} :
  {f : R →+* T // ∀ ⦃x y⦄, r x y → f x = f y} ≃ (ring_quot r →+* T) :=
{ to_fun := λ f', let f := (f' : R →+* T) in
  { to_fun := λ x, quot.lift f
    begin
      rintros _ _ r,
      induction r,
      case of : _ _ r { exact f'.prop r, },
      case add_left : _ _ _ _ r' { simp [r'], },
      case mul_left : _ _ _ _ r' { simp [r'], },
      case mul_right : _ _ _ _ r' { simp [r'], },
    end x.to_quot,
    map_zero' := by simp [← zero_quot, f.map_zero],
    map_add' := by { rintros ⟨⟨x⟩⟩ ⟨⟨y⟩⟩, simp [add_quot, f.map_add x y], },
    map_one' := by simp [← one_quot, f.map_one],
    map_mul' := by { rintros ⟨⟨x⟩⟩ ⟨⟨y⟩⟩, simp [mul_quot, f.map_mul x y] }, },
  inv_fun := λ F, ⟨F.comp (mk_ring_hom r), λ x y h, by { dsimp, rw mk_ring_hom_rel h, }⟩,
  left_inv := λ f, by { ext, simp [mk_ring_hom] },
  right_inv := λ F, by { ext, simp [mk_ring_hom] } }

@[simp]
lemma lift_mk_ring_hom_apply (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
  lift ⟨f, w⟩ (mk_ring_hom r x) = f x :=
by { simp_rw [lift, mk_ring_hom], refl }

-- note this is essentially `lift.symm_apply_eq.mp h`
lemma lift_unique (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y)
  (g : ring_quot r →+* T) (h : g.comp (mk_ring_hom r) = f) : g = lift ⟨f, w⟩ :=
by { ext, simp [h], }

lemma eq_lift_comp_mk_ring_hom {r : R → R → Prop} (f : ring_quot r →+* T) :
  f = lift ⟨f.comp (mk_ring_hom r), λ x y h, by { dsimp, rw mk_ring_hom_rel h, }⟩ :=
begin
  conv_lhs { rw ← lift.apply_symm_apply f },
  rw lift,
  refl,
end


section comm_ring
/-!
We now verify that in the case of a commutative ring, the `ring_quot` construction
agrees with the quotient by the appropriate ideal.
-/

variables {B : Type u₁} [comm_ring B]

/-- The universal ring homomorphism from `ring_quot r` to `B ⧸ ideal.of_rel r`. -/
def ring_quot_to_ideal_quotient (r : B → B → Prop) :
  ring_quot r →+* B ⧸ ideal.of_rel r :=
lift
  ⟨ideal.quotient.mk (ideal.of_rel r),
    λ x y h, ideal.quotient.eq.2 $ submodule.mem_Inf.mpr (λ p w, w ⟨x, y, h, sub_add_cancel x y⟩)⟩

@[simp] lemma ring_quot_to_ideal_quotient_apply (r : B → B → Prop) (x : B) :
  ring_quot_to_ideal_quotient r (mk_ring_hom r x) = ideal.quotient.mk _ x :=
begin
  simp_rw [ring_quot_to_ideal_quotient, lift, mk_ring_hom],
  refl
end

/-- The universal ring homomorphism from `B ⧸ ideal.of_rel r` to `ring_quot r`. -/
def ideal_quotient_to_ring_quot (r : B → B → Prop) :
  B ⧸ ideal.of_rel r →+* ring_quot r :=
ideal.quotient.lift (ideal.of_rel r) (mk_ring_hom r)
begin
  refine λ x h, submodule.span_induction h _ _ _ _,
  { rintro y ⟨a, b, h, su⟩,
    symmetry' at su,
    rw ←sub_eq_iff_eq_add at su,
    rw [ ← su, ring_hom.map_sub, mk_ring_hom_rel h, sub_self], },
  { simp, },
  { intros a b ha hb, simp [ha, hb], },
  { intros a x hx, simp [hx], },
end

@[simp] lemma ideal_quotient_to_ring_quot_apply (r : B → B → Prop) (x : B) :
  ideal_quotient_to_ring_quot r (ideal.quotient.mk _ x) = mk_ring_hom r x := rfl

/--
The ring equivalence between `ring_quot r` and `(ideal.of_rel r).quotient`
-/
def ring_quot_equiv_ideal_quotient (r : B → B → Prop) :
  ring_quot r ≃+* B ⧸ ideal.of_rel r :=
ring_equiv.of_hom_inv (ring_quot_to_ideal_quotient r) (ideal_quotient_to_ring_quot r)
  (begin
    ext,
    simp_rw [ring_quot_to_ideal_quotient, lift, mk_ring_hom],
    dsimp,
    rw [mk_ring_hom],
    refl
  end)
  (begin
    ext,
    simp_rw [ring_quot_to_ideal_quotient, lift, mk_ring_hom],
    dsimp,
    rw [mk_ring_hom],
    refl
  end)

end comm_ring

section star_ring

variables [star_ring R] (r) (hr : ∀ a b, r a b → r (star a) (star b))
include hr

theorem rel.star ⦃a b : R⦄ (h : rel r a b) :
  rel r (star a) (star b) :=
begin
  induction h,
  { exact rel.of (hr _ _ h_h) },
  { rw [star_add, star_add], exact rel.add_left h_ih, },
  { rw [star_mul, star_mul], exact rel.mul_right h_ih, },
  { rw [star_mul, star_mul], exact rel.mul_left h_ih, },
end

@[irreducible] private def star' : ring_quot r → ring_quot r
| ⟨a⟩ := ⟨quot.map (star : R → R) (rel.star r hr) a⟩

lemma star'_quot (hr : ∀ a b, r a b → r (star a) (star b)) {a} :
  (star' r hr ⟨quot.mk _ a⟩ : ring_quot r) = ⟨quot.mk _ (star a)⟩ :=
by { show star' r _ _ = _, rw star', refl }

/-- Transfer a star_ring instance through a quotient, if the quotient is invariant to `star` -/
def star_ring {R : Type u₁} [semiring R] [star_ring R] (r : R → R → Prop)
  (hr : ∀ a b, r a b → r (star a) (star b)) :
  star_ring (ring_quot r) :=
{ star := star' r hr,
  star_involutive := by { rintros ⟨⟨⟩⟩, simp [star'_quot], },
  star_mul := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [star'_quot, mul_quot, star_mul], },
  star_add := by { rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩, simp [star'_quot, add_quot, star_add], } }

end star_ring

section algebra

variables (S)

/--
The quotient map from an `S`-algebra to its quotient, as a homomorphism of `S`-algebras.
-/
@[irreducible] def mk_alg_hom (s : A → A → Prop) : A →ₐ[S] ring_quot s :=
{ commutes' := λ r, by { simp [mk_ring_hom], refl },
  ..mk_ring_hom s }

@[simp]
lemma mk_alg_hom_coe (s : A → A → Prop) : (mk_alg_hom S s : A →+* ring_quot s) = mk_ring_hom s :=
by { simp_rw [mk_alg_hom, mk_ring_hom], refl }

lemma mk_alg_hom_rel {s : A → A → Prop} {x y : A} (w : s x y) :
  mk_alg_hom S s x = mk_alg_hom S s y :=
by simp [mk_alg_hom, mk_ring_hom, quot.sound (rel.of w)]

lemma mk_alg_hom_surjective (s : A → A → Prop) : function.surjective (mk_alg_hom S s) :=
by { dsimp [mk_alg_hom, mk_ring_hom], rintro ⟨⟨a⟩⟩, use a, refl, }

variables {B : Type u₄} [semiring B] [algebra S B]

@[ext]
lemma ring_quot_ext' {s : A → A → Prop}
  (f g : ring_quot s →ₐ[S] B) (w : f.comp (mk_alg_hom S s) = g.comp (mk_alg_hom S s)) : f = g :=
begin
  ext,
  rcases mk_alg_hom_surjective S s x with ⟨x, rfl⟩,
  exact (alg_hom.congr_fun w x : _),
end

/--
Any `S`-algebra homomorphism `f : A →ₐ[S] B` which respects a relation `s : A → A → Prop`
factors uniquely through a morphism `ring_quot s →ₐ[S]  B`.
-/
@[irreducible] def lift_alg_hom {s : A → A → Prop} :
  {f : A →ₐ[S] B // ∀ ⦃x y⦄, s x y → f x = f y} ≃ (ring_quot s →ₐ[S] B) :=
{ to_fun := λ f', let f := (f' : A →ₐ[S] B) in
  { to_fun := λ x, quot.lift f
    begin
      rintros _ _ r,
      induction r,
      case of : _ _ r { exact f'.prop r, },
      case add_left : _ _ _ _ r' { simp [r'], },
      case mul_left : _ _ _ _ r' { simp [r'], },
      case mul_right : _ _ _ _ r' { simp [r'], },
    end x.to_quot,
    map_zero' := by simp [← zero_quot, f.map_zero],
    map_add' := by { rintros ⟨⟨x⟩⟩ ⟨⟨y⟩⟩, simp [add_quot, f.map_add x y] },
    map_one' := by simp [← one_quot, f.map_one],
    map_mul' := by { rintros ⟨⟨x⟩⟩ ⟨⟨y⟩⟩, simp [mul_quot, f.map_mul x y], },
    commutes' := by { rintros x, simp [← one_quot, smul_quot, algebra.algebra_map_eq_smul_one] } },
  inv_fun := λ F, ⟨F.comp (mk_alg_hom S s), λ _ _ h, by { dsimp, erw mk_alg_hom_rel S h }⟩,
  left_inv := λ f, by { ext, simp [mk_alg_hom, mk_ring_hom] },
  right_inv := λ F, by { ext, simp [mk_alg_hom, mk_ring_hom] } }

@[simp]
lemma lift_alg_hom_mk_alg_hom_apply (f : A →ₐ[S] B) {s : A → A → Prop}
  (w : ∀ ⦃x y⦄, s x y → f x = f y) (x) :
  (lift_alg_hom S ⟨f, w⟩) ((mk_alg_hom S s) x) = f x :=
by { simp_rw [lift_alg_hom, mk_alg_hom, mk_ring_hom], refl, }

-- note this is essentially `(lift_alg_hom S).symm_apply_eq.mp h`
lemma lift_alg_hom_unique (f : A →ₐ[S] B) {s : A → A → Prop} (w : ∀ ⦃x y⦄, s x y → f x = f y)
  (g : ring_quot s →ₐ[S] B) (h : g.comp (mk_alg_hom S s) = f) : g = lift_alg_hom S ⟨f, w⟩ :=
by { ext, simp [h], }

lemma eq_lift_alg_hom_comp_mk_alg_hom {s : A → A → Prop} (f : ring_quot s →ₐ[S] B) :
  f = lift_alg_hom S ⟨f.comp (mk_alg_hom S s), λ x y h, by { dsimp, erw mk_alg_hom_rel S h, }⟩ :=
begin
  conv_lhs { rw ← ((lift_alg_hom S).apply_symm_apply f) },
  rw lift_alg_hom,
  refl,
end

end algebra

end ring_quot
