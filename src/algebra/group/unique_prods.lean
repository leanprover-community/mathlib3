/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finset.preimage

/-!
#  Unique products and related notions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A group `G` has *unique products* if for any two non-empty finite subsets `A, B ⊂ G`, there is an
element `g ∈ A * B` that can be written uniquely as a product of an element of `A` and an element
of `B`.  We call the formalization this property `unique_prods`.  Since the condition requires no
property of the group operation, we define it for a Type simply satisfying `has_mul`.  We also
introduce the analogous "additive" companion, `unique_sums` and link the two so that `to_additive`
converts `unique_prods` into `unique_sums`.

Here you can see several examples of Types that have `unique_sums/prods`
(`apply_instance` uses `covariants.to_unique_prods` and `covariants.to_unique_sums`).
```lean
import data.real.basic

example : unique_sums ℕ   := by apply_instance
example : unique_sums ℕ+  := by apply_instance
example : unique_sums ℤ   := by apply_instance
example : unique_sums ℚ   := by apply_instance
example : unique_sums ℝ   := by apply_instance
example : unique_prods ℕ+ := by apply_instance
```
-/

/--  Let `G` be a Type with multiplication, let `A B : finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `unique_mul A B a0 b0` asserts `a0 * b0` can be written in at
most one way as a product of an element of `A` and an element of `B`. -/
@[to_additive "Let `G` be a Type with addition, let `A B : finset G` be finite subsets and
let `a0 b0 : G` be two elements.  `unique_add A B a0 b0` asserts `a0 + b0` can be written in at
most one way as a sum of an element from `A` and an element from `B`."]
def unique_mul {G} [has_mul G] (A B : finset G) (a0 b0 : G) : Prop :=
∀ ⦃a b⦄, a ∈ A → b ∈ B → a * b = a0 * b0 → a = a0 ∧ b = b0

namespace unique_mul
variables {G H : Type*} [has_mul G] [has_mul H] {A B : finset G} {a0 b0 : G}

lemma mt {G} [has_mul G] {A B : finset G} {a0 b0 : G} (h : unique_mul A B a0 b0) :
  ∀ ⦃a b⦄, a ∈ A → b ∈ B → a ≠ a0 ∨ b ≠ b0 → a * b ≠ a0 * b0 :=
λ _ _ ha hb k, by { contrapose! k, exact h ha hb k }

@[to_additive]
lemma subsingleton (A B : finset G) (a0 b0 : G) (h : unique_mul A B a0 b0) :
  subsingleton { ab : G × G // ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
⟨λ ⟨⟨a, b⟩, ha, hb, ab⟩ ⟨⟨a', b'⟩, ha', hb', ab'⟩, subtype.ext $ prod.ext
  ((h ha hb ab).1.trans (h ha' hb' ab').1.symm) $ (h ha hb ab).2.trans (h ha' hb' ab').2.symm⟩

@[to_additive]
lemma set_subsingleton (A B : finset G) (a0 b0 : G) (h : unique_mul A B a0 b0) :
  set.subsingleton { ab : G × G | ab.1 ∈ A ∧ ab.2 ∈ B ∧ ab.1 * ab.2 = a0 * b0 } :=
begin
  rintros ⟨x1, y1⟩ (hx : x1 ∈ A ∧ y1 ∈ B ∧ x1 * y1 = a0 * b0)
          ⟨x2, y2⟩ (hy : x2 ∈ A ∧ y2 ∈ B ∧ x2 * y2 = a0 * b0),
  rcases h hx.1 hx.2.1 hx.2.2 with ⟨rfl, rfl⟩,
  rcases h hy.1 hy.2.1 hy.2.2 with ⟨rfl, rfl⟩,
  refl,
end

@[to_additive]
lemma iff_exists_unique (aA : a0 ∈ A) (bB : b0 ∈ B) :
  unique_mul A B a0 b0 ↔ ∃! ab ∈ A ×ˢ B, ab.1 * ab.2 = a0 * b0 :=
⟨λ _, ⟨(a0, b0), ⟨finset.mem_product.mpr ⟨aA, bB⟩, rfl, by simp⟩, by simpa⟩, λ h, h.elim2 begin
  rintro ⟨x1, x2⟩ _ _ J x y hx hy l,
  rcases prod.mk.inj_iff.mp (J (a0,b0) (finset.mk_mem_product aA bB) rfl) with ⟨rfl, rfl⟩,
  exact prod.mk.inj_iff.mp (J (x,y) (finset.mk_mem_product hx hy) l),
end⟩

@[to_additive]
lemma exists_iff_exists_exists_unique : (∃ a0 b0 : G, a0 ∈ A ∧ b0 ∈ B ∧ unique_mul A B a0 b0) ↔
  ∃ g : G, ∃! ab ∈ A ×ˢ B, ab.1 * ab.2 = g :=
⟨λ ⟨a0, b0, hA, hB, h⟩, ⟨_, (iff_exists_unique hA hB).mp h⟩, λ ⟨g, h⟩, begin
    have h' := h,
    rcases h' with ⟨⟨a,b⟩, ⟨hab, rfl, -⟩, -⟩,
    cases finset.mem_product.mp hab with ha hb,
    exact ⟨a, b, ha, hb, (iff_exists_unique ha hb).mpr h⟩,
  end⟩

/--  `unique_mul` is preserved by inverse images under injective, multiplicative maps. -/
@[to_additive "`unique_add` is preserved by inverse images under injective, additive maps."]
lemma mul_hom_preimage (f : G →ₙ* H) (hf : function.injective f) (a0 b0 : G) {A B : finset H}
  (u : unique_mul A B (f a0) (f b0)) :
  unique_mul (A.preimage f (set.inj_on_of_injective hf _))
    (B.preimage f (set.inj_on_of_injective hf _)) a0 b0 :=
begin
  intros a b ha hb ab,
  rw [← hf.eq_iff, ← hf.eq_iff],
  rw [← hf.eq_iff, map_mul, map_mul] at ab,
  exact u (finset.mem_preimage.mp ha) (finset.mem_preimage.mp hb) ab,
end

/--  `unique_mul` is preserved under multiplicative maps that are injective.

See `unique_mul.mul_hom_map_iff` for a version with swapped bundling. -/
@[to_additive "`unique_add` is preserved under additive maps that are injective.

See `unique_add.add_hom_map_iff` for a version with swapped bundling."]
lemma mul_hom_image_iff [decidable_eq H] (f : G →ₙ* H) (hf : function.injective f) :
  unique_mul (A.image f) (B.image f) (f a0) (f b0) ↔ unique_mul A B a0 b0 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { intros a b ha hb ab,
    rw [← hf.eq_iff, ← hf.eq_iff],
    rw [← hf.eq_iff, map_mul, map_mul] at ab,
    exact h (finset.mem_image.mpr ⟨_, ha, rfl⟩) (finset.mem_image.mpr ⟨_, hb, rfl⟩) ab},
  { intros a b aA bB ab,
    obtain ⟨a, ha, rfl⟩ : ∃ a' ∈ A, f a' = a := finset.mem_image.mp aA,
    obtain ⟨b, hb, rfl⟩ : ∃ b' ∈ B, f b' = b := finset.mem_image.mp bB,
    rw [hf.eq_iff, hf.eq_iff],
    rw [← map_mul, ← map_mul, hf.eq_iff] at ab,
    exact h ha hb ab },
end

/--  `unique_mul` is preserved under embeddings that are multiplicative.

See `unique_mul.mul_hom_image_iff` for a version with swapped bundling. -/
@[to_additive "`unique_add` is preserved under embeddings that are additive.

See `unique_add.add_hom_image_iff` for a version with swapped bundling."]
lemma mul_hom_map_iff (f : G ↪ H) (mul : ∀ x y, f (x * y) = f x * f y) :
  unique_mul (A.map f) (B.map f) (f a0) (f b0) ↔ unique_mul A B a0 b0 :=
begin
  classical,
  convert mul_hom_image_iff ⟨f, mul⟩ f.2;
  { ext,
    simp only [finset.mem_map, mul_hom.coe_mk, finset.mem_image] },
end

end unique_mul

/--  Let `G` be a Type with addition.  `unique_sums G` asserts that any two non-empty
finite subsets of `A` have the `unique_add` property, with respect to some element of their
sum `A + B`. -/
class unique_sums (G) [has_add G] : Prop :=
(unique_add_of_nonempty : ∀ {A B : finset G} (hA : A.nonempty) (hB : B.nonempty),
  ∃ (a0 ∈ A) (b0 ∈ B), unique_add A B a0 b0)

/--  Let `G` be a Type with multiplication.  `unique_prods G` asserts that any two non-empty
finite subsets of `G` have the `unique_mul` property, with respect to some element of their
product `A * B`. -/
class unique_prods (G) [has_mul G] : Prop :=
(unique_mul_of_nonempty : ∀ {A B : finset G} (hA : A.nonempty) (hB : B.nonempty),
  ∃ (a0 ∈ A) (b0 ∈ B), unique_mul A B a0 b0)

attribute [to_additive] unique_prods

namespace multiplicative

instance {M} [has_add M] [unique_sums M] : unique_prods (multiplicative M) :=
{ unique_mul_of_nonempty := λ A B hA hB, let A' : finset M := A in have hA': A'.nonempty := hA, by
    { obtain ⟨a0, hA0, b0, hB0, J⟩ := unique_sums.unique_add_of_nonempty hA' hB,
      exact ⟨of_add a0, hA0, of_add b0, hB0, λ a b aA bB H, J aA bB H⟩ } }

end multiplicative

namespace additive

instance {M} [has_mul M] [unique_prods M] : unique_sums (additive M) :=
{ unique_add_of_nonempty := λ A B hA hB, let A' : finset M := A in have hA': A'.nonempty := hA, by
    { obtain ⟨a0, hA0, b0, hB0, J⟩ := unique_prods.unique_mul_of_nonempty hA' hB,
      exact ⟨of_mul a0, hA0, of_mul b0, hB0, λ a b aA bB H, J aA bB H⟩ } }

end additive

@[to_additive] lemma eq_and_eq_of_le_of_le_of_mul_le {A} [has_mul A] [linear_order A]
  [covariant_class A A (*) (≤)] [covariant_class A A (function.swap (*)) (<)]
  [contravariant_class A A (*) (≤)]
  {a b a0 b0 : A} (ha : a0 ≤ a) (hb : b0 ≤ b) (ab : a * b ≤ a0 * b0) :
  a = a0 ∧ b = b0 :=
begin
  haveI := has_mul.to_covariant_class_right A,
  have ha' : ¬a0 * b0 < a * b → ¬a0 < a := mt (λ h, mul_lt_mul_of_lt_of_le h hb),
  have hb' : ¬a0 * b0 < a * b → ¬b0 < b := mt (λ h, mul_lt_mul_of_le_of_lt ha h),
  push_neg at ha' hb',
  exact ⟨ha.antisymm' (ha' ab), hb.antisymm' (hb' ab)⟩,
end

/--  This instance asserts that if `A` has a multiplication, a linear order, and multiplication
is 'very monotone', then `A` also has `unique_prods`. -/
@[priority 100,  -- see Note [lower instance priority]
to_additive "This instance asserts that if `A` has an addition, a linear order, and addition
is 'very monotone', then `A` also has `unique_sums`."]
instance covariants.to_unique_prods {A} [has_mul A] [linear_order A]
  [covariant_class A A (*) (≤)] [covariant_class A A (function.swap (*)) (<)]
  [contravariant_class A A (*) (≤)] : unique_prods A :=
{ unique_mul_of_nonempty := λ A B hA hB, ⟨_, A.min'_mem ‹_›, _, B.min'_mem ‹_›, λ a b ha hb ab,
    eq_and_eq_of_le_of_le_of_mul_le (finset.min'_le _ _ ‹_›) (finset.min'_le _ _ ‹_›) ab.le⟩ }
