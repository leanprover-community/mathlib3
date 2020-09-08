/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie_algebra
import linear_algebra.tensor_algebra

/-!
# Universal enveloping algebra

Given a commutative ring `R` and a Lie algebra `L` over `R`, we construct the universal
enveloping algebra of `L`, together its universal property.

## Main definitions

  * `universal_enveloping_algebra`
  * `universal_enveloping_algebra.algebra`
  * `universal_enveloping_algebra.lift`
  * `universal_enveloping_algebra.ι_comp_lift`
  * `universal_enveloping_algebra.lift_unique`

## Implementation notes

The universal enveloping algebra is constructed as a quotient of the tensor algebra using the
`quot` function. We take this low-level approach because at the time of writing, quotients of
non-commutative rings have not yet been defined. This approach means that we must manually construct
the algebraic structure on the quotient, but this turns out not to be much trouble.

We emphasise that the implementation is immaterial because the universal enveloping algebra is
characterised up to unique isomorphism by its universal property, which we also provide.

## Tags

lie algebra, universal enveloping algebra, tensor algebra
-/

universes u₁ u₂ u₃ u₄

variables {R : Type u₁} [semiring R]
variables (S : Type u₂) [comm_semiring S]
variables {A : Type u₃} [semiring A] [algebra S A]

namespace ring_quot

/-- The quotient by the transitive closure of this relation is the universal enveloping algebra. -/
inductive rel (r : R → R → Prop) : R → R → Prop
| of {x y : R} (h : r x y) : rel x y
| add {a b c} : rel a b → rel (a + c) (b + c)
| mul_left {a b c} : rel a b → rel (a * c) (b * c)
| mul_right {a b c} : rel a b → rel (c * a) (c * b)

end ring_quot

/-- The universal enveloping algebra of a Lie algebra. -/
def ring_quot (r : R → R → Prop) := quot (ring_quot.rel r)

namespace ring_quot

instance (r : R → R → Prop) : semiring (ring_quot r) :=
{ add           := quot.map₂ (+)
    (λ c a b h, by { rw [add_comm c a, add_comm c b], exact rel.add h, })
    (λ _ _ _, rel.add),
  add_assoc     := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw add_assoc, refl, },
  zero          := quot.mk _ 0,
  zero_add      := by { rintros ⟨⟩, change quot.mk _ _ = _, rw zero_add, },
  add_zero      := by { rintros ⟨⟩, change quot.mk _ _ = _, rw add_zero, },
  zero_mul      := by { rintros ⟨⟩, change quot.mk _ _ = _, rw zero_mul, },
  mul_zero      := by { rintros ⟨⟩, change quot.mk _ _ = _, rw mul_zero, },
  add_comm      := by { rintros ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw add_comm, refl, },
  mul           := quot.map₂ (*) (λ _ _ _, rel.mul_right) (λ _ _ _, rel.mul_left),
  mul_assoc     := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw mul_assoc, refl, },
  one           := quot.mk _ 1,
  one_mul       := by { rintros ⟨⟩, change quot.mk _ _ = _, rw one_mul, },
  mul_one       := by { rintros ⟨⟩, change quot.mk _ _ = _, rw mul_one, },
  left_distrib  := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw left_distrib, refl, },
  right_distrib := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw right_distrib, refl, }, }

instance {R : Type u₁} [ring R] (r : R → R → Prop) : ring (ring_quot r) :=
{ neg           := quot.map (λ a, -a)
    (λ a b h, by simp only [neg_eq_neg_one_mul a, neg_eq_neg_one_mul b, rel.mul_right h]),
  add_left_neg  := by { rintros ⟨⟩, change quot.mk _ _ = _, rw add_left_neg, refl, },
  .. (ring_quot.semiring r) }

instance {R : Type u₁} [comm_semiring R] (r : R → R → Prop) : comm_semiring (ring_quot r) :=
{ mul_comm := by { rintros ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw mul_comm, refl, }
  .. (ring_quot.semiring r) }

-- TODO relate this to the existing quotient by an ideal!
instance {R : Type u₁} [comm_ring R] (r : R → R → Prop) : comm_ring (ring_quot r) :=
{ .. (ring_quot.comm_semiring r),
  .. (ring_quot.ring r) }

instance (s : A → A → Prop) : algebra S (ring_quot s) :=
{ smul      := λ r a, (quot.mk _ (r • 1)) * a,
  to_fun    := λ r, quot.mk _ (r • 1),
  map_one'  := by { rw one_smul, refl, },
  map_mul'  := λ r s, by { change _ = quot.mk _ _, simp [mul_smul], },
  map_zero' := by { rw zero_smul, refl, },
  map_add'  := λ r s, by { change _ = quot.mk _ _, rw add_smul, },
  commutes' := λ r, by { rintros ⟨a⟩, change quot.mk _ _ = quot.mk _ _, simp, },
  smul_def' := λ r u, rfl, }

instance (r : R → R → Prop) : inhabited (ring_quot r) := ⟨0⟩

def mk_ring_hom (r : R → R → Prop) : R →+* ring_quot r :=
{ to_fun := quot.mk _,
  map_one'  := rfl,
  map_mul'  := λ a b, rfl,
  map_zero' := rfl,
  map_add'  := λ a b, rfl, }

lemma mk_ring_hom_rel {r : R → R → Prop} {x y : R} (w : r x y) : mk_ring_hom r x = mk_ring_hom r y :=
quot.sound (rel.of w)

lemma mk_ring_hom_surjective (r : R → R → Prop) : function.surjective (mk_ring_hom r) :=
by { dsimp [mk_ring_hom], rintro ⟨⟩, simp, }

@[ext]
lemma ring_quot_ext {T : Type u₄} [semiring T] {r : R → R → Prop} (f g : ring_quot r →+* T)
  (w : f.comp (mk_ring_hom r) = g.comp (mk_ring_hom r)) : f = g :=
begin
  ext,
  rcases mk_ring_hom_surjective r x with ⟨x, rfl⟩,
  exact (congr_arg (λ h : R →+* T, h x) w), -- TODO should we have `ring_hom.congr` for this?
end

def mk_alg_hom (s : A → A → Prop) : A →ₐ[S] ring_quot s :=
{ commutes' := λ r, show quot.mk _ _ = quot.mk _ _, by rw [algebra.smul_def'', mul_one],
  ..mk_ring_hom s }

@[simp]
lemma mk_alg_hom_coe (s : A → A → Prop) : (mk_alg_hom S s : A →+* ring_quot s) = mk_ring_hom s :=
rfl

lemma mk_alg_hom_rel {s : A → A → Prop} {x y : A} (w : s x y) : mk_alg_hom S s x = mk_alg_hom S s y :=
quot.sound (rel.of w)

lemma mk_alg_hom_surjective (s : A → A → Prop) : function.surjective (mk_alg_hom S s) :=
by { dsimp [mk_alg_hom], rintro ⟨a⟩, use a, refl, }

@[ext]
lemma ring_quot_ext' {B : Type u₄} [semiring B] [algebra S B] {s : A → A → Prop} (f g : ring_quot s →ₐ[S] B)
  (w : f.comp (mk_alg_hom S s) = g.comp (mk_alg_hom S s)) : f = g :=
begin
  ext,
  rcases mk_alg_hom_surjective S s x with ⟨x, rfl⟩,
  exact (congr_arg (λ h : A →ₐ[S] B, h x) w), -- TODO should we have `alg_hom.congr` for this?
end

def lift {T : Type u₄} [semiring T] (f : R →+* T) {r : R → R → Prop} (w : ∀ {x y}, r x y → f x = f y) :
  ring_quot r →+* T :=
{ to_fun := quot.lift f
  begin
    rintros _ _ r,
    induction r with a b r a b c r r' a b c r r' a b c r r',
    { exact w r, },
    { simp [r'], },
    { simp [r'], },
    { simp [r'], },
  end,
  map_zero' := f.map_zero,
  map_add' := by { rintros ⟨x⟩ ⟨y⟩, exact f.map_add x y, },
  map_one' := f.map_one,
  map_mul' := by { rintros ⟨x⟩ ⟨y⟩, exact f.map_mul x y, }, }

@[simp]
lemma lift_mk_ring_hom {T : Type u₄} [semiring T] (f : R →+* T) {r : R → R → Prop} (w : ∀ {x y}, r x y → f x = f y) :
  (lift f @w).comp (mk_ring_hom r) = f :=
by { ext, simp, refl, }

lemma lift_unique {T : Type u₄} [semiring T] (f : R →+* T) {r : R → R → Prop} (w : ∀ {x y}, r x y → f x = f y)
  (g : ring_quot r →+* T) (h : g.comp (mk_ring_hom r) = f) : g = lift f @w :=
by { ext, simp [h], }

lemma eq_lift_comp_mk_ring_hom {T : Type u₄} [semiring T] {r : R → R → Prop} (f : ring_quot r →+* T) :
  f = lift (f.comp (mk_ring_hom r)) (by { intros x y h, dsimp, rw mk_ring_hom_rel h, }) :=
by { ext, simp, }

def lift_alg_hom {B : Type u₄} [semiring B] [algebra S B] (f : A →ₐ[S] B) {s : A → A → Prop}
  (w : ∀ {x y}, s x y → f x = f y) :
  ring_quot s →ₐ[S] B :=
{ to_fun := quot.lift f
  begin
    rintros _ _ r,
    induction r with a b r a b c r r' a b c r r' a b c r r',
    { exact w r, },
    { simp [r'], },
    { simp [r'], },
    { simp [r'], },
  end,
  map_zero' := f.map_zero,
  map_add' := by { rintros ⟨x⟩ ⟨y⟩, exact f.map_add x y, },
  map_one' := f.map_one,
  map_mul' := by { rintros ⟨x⟩ ⟨y⟩, exact f.map_mul x y, },
  commutes' :=
  begin
    rintros x,
    conv_rhs { rw [algebra.algebra_map_eq_smul_one, ←f.map_one, ←f.map_smul], },
    exact quot.lift_beta f @w (x • 1),
  end, }

@[simp]
lemma lift_alg_hom_mk_alg_hom {B : Type u₄} [semiring B] [algebra S B] (f : A →ₐ[S] B) {s : A → A → Prop} (w : ∀ {x y}, s x y → f x = f y) :
  (lift_alg_hom S f @w).comp (mk_alg_hom S s) = f :=
by { ext, simp, refl, }

lemma lift_alg_hom_unique {B : Type u₄} [semiring B] [algebra S B] (f : A →ₐ[S] B) {s : A → A → Prop} (w : ∀ {x y}, s x y → f x = f y)
  (g : ring_quot s →ₐ[S] B) (h : g.comp (mk_alg_hom S s) = f) : g = lift_alg_hom S f @w :=
by { ext, simp [h], }

lemma eq_lift_alg_hom_comp_mk_alg_hom {B : Type u₄} [semiring B] [algebra S B] (f : A →ₐ[S] B) {s : A → A → Prop} (f : ring_quot s →ₐ[S] B) :
  f = lift_alg_hom S (f.comp (mk_alg_hom S s)) (by { intros x y h, dsimp, rw mk_alg_hom_rel S h, }) :=
by { ext, simp, }

end ring_quot
