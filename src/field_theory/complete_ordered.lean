/-
Copyright (c) 2020 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.archimedean
import data.equiv.ring
import algebra.pointwise
import order.conditionally_complete_lattice
import topology.instances.real
import analysis.special_functions.pow
import data.real.sqrt

/-!
# Conditionally complete linear ordered fields

This file shows that the reals are unique, or, more formally, given a type satisfying the common
axioms of the reals (field, conditionally complete, linearly ordered) that there is an equivalence
preserving these properties to the reals. This is `cut_ordered_ring_equiv`. Moreover this
equivalence is unique.

We introduce definitions of conditionally complete linear ordered fields, show all such are
archimedean, and define equivalences between these fields. We also construct the natural map from a
`linear_ordered_field` to such a field.

## Main definitions

* `conditionally_complete_linear_ordered_field` :
* `ordered_ring_equiv`      :
* `cut_map`      :

## Main results

* `ring_equiv_eq_cut_ordered_ring_equiv`:

## Notation

* `≃+*o`: equivalence of ordered rings.

## References

* https://mathoverflow.net/questions/362991/who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags
reals, conditionally complete, ordered field
-/

noncomputable theory
open_locale classical

open set

/-- The natural equiv between the rationals and the rationals as a set inside any characteristic 0
    division ring -/
def rat_equiv_of_char_zero (F : Type*) [division_ring F] [char_zero F] : ℚ ≃ range (coe : ℚ → F) :=
equiv.set.range coe rat.cast_injective

/-- The natural equiv between the rationals as a set inside any pair of characteristic 0
    division rings -/
def range_rat_equiv (F K : Type*) [division_ring F] [char_zero F] [division_ring K] [char_zero K] :
  range (coe : ℚ → F) ≃ range (coe : ℚ → K) :=
(rat_equiv_of_char_zero F).symm.trans (rat_equiv_of_char_zero K)

@[simp]
lemma range_rat_equiv_apply {F K : Type*} {q : ℚ}
  [division_ring F] [char_zero F] [division_ring K] [char_zero K] :
  range_rat_equiv F K ⟨q, mem_range_self q⟩ = ⟨q, mem_range_self q⟩ :=
by simp only [range_rat_equiv, rat_equiv_of_char_zero, equiv.set.range_apply,
  function.comp_app, subtype.mk_eq_mk, equiv.coe_trans, rat.cast_inj, equiv.symm_apply_eq]

/-- The function sending subsets of the rationals embedded inside of one characteristic zero
    division ring to the corresponding subset of a second such ring. -/
def cut_map (F K : Type*) [division_ring F] [char_zero F] [division_ring K] [char_zero K] :
  set (set.range (coe : ℚ → F)) → set (set.range (coe : ℚ → K)) :=
λ c, (range_rat_equiv F K) '' c

/- No longer used -/
lemma bdd_above_add {F : Type*} [ordered_add_comm_monoid F] {A B : set F} :
  bdd_above A → bdd_above B → bdd_above (A + B) :=
begin
  rintros ⟨bA, hbA⟩ ⟨bB, hbB⟩,
  use bA + bB,
  rintros x ⟨xa, xb, hxa, hxb, rfl⟩,
  exact add_le_add (hbA hxa) (hbB hxb),
end

/-- Equivalence commuting with multiplicative, additive and order structure. -/
@[nolint has_inhabited_instance]
structure ordered_ring_equiv (R S : Type*) [has_mul R] [has_add R] [has_mul S] [has_add S]
  [has_le R] [has_le S] extends R ≃+* S :=
(map_rel_iff' : ∀ {x y : R}, to_fun x ≤ to_fun y ↔ x ≤ y)

/-- Reinterpret an ordered ring equivalence as a ring equivalence. -/
add_decl_doc ordered_ring_equiv.to_ring_equiv

-- /-- Reinterpret an ordered ring equivalence as an equivalence of types. -/
-- add_decl_doc ordered_ring_equiv.to_equiv

namespace ordered_ring_equiv

infix ` ≃+*o `:25 := ordered_ring_equiv

variables {R S : Type*} [has_mul R] [has_add R] [has_le R] [has_mul S] [has_add S] [has_le S]

/-- Reinterpret an ordered ring equivalence as an order isomorphism. -/
def to_order_iso (f : R ≃+*o S) : R ≃o S := { ..f }

instance has_coe_to_ring_equiv : has_coe (R ≃+*o S) (R ≃+* S) := ⟨to_ring_equiv⟩
instance has_coe_to_equiv : has_coe (R ≃+*o S) (R ≃ S) := ⟨ring_equiv.to_equiv ∘ to_ring_equiv⟩
instance has_coe_to_order_iso : has_coe (R ≃+*o S) (R ≃o S) := ⟨to_order_iso⟩

instance : has_coe_to_fun (R ≃+*o S) := ⟨_, λ f, f.to_fun⟩

@[simp] lemma to_ring_equiv_eq_coe {f : R ≃+*o S} : f.to_ring_equiv = f := rfl
@[simp] lemma to_order_iso_eq_coe {f : R ≃+*o S} : f.to_order_iso = f := rfl
@[simp] lemma to_ring_equiv_to_fun_eq_coe_fun {f : R ≃+*o S} : (f : R ≃+* S).to_fun = f := rfl
@[simp] lemma to_ring_equiv_coe_fun_eq_coe_fun {f : R ≃+*o S} : ((f : R ≃+* S) : R → S) = f := rfl
@[simp] lemma to_order_iso_to_fun_eq_to_equiv {f : R ≃+*o S} : (f : R ≃o S).to_fun = f := rfl
@[simp] lemma to_order_iso_coe_fun_eq_to_equiv {f : R ≃+*o S} : ((f : R ≃o S) : R → S) = f := rfl
@[simp] lemma to_mul_equiv_to_fun_eq_to_equiv {f : R ≃+*o S} : ((f : R ≃* S) : R → S) = f := rfl
@[simp] lemma to_add_equiv_to_fun_eq_to_equiv {f : R ≃+*o S} : (f : R ≃+ S).to_fun = f := rfl
#lint

/-- A ring isomorphism preserves multiplication. -/
@[simp] lemma map_mul (e : R ≃+*o S) (x y : R) : e (x * y) = e x * e y := e.map_mul' x y

/-- A ring isomorphism preserves addition. -/
@[simp] lemma map_add (e : R ≃+*o S) (x y : R) : e (x + y) = e x + e y := e.map_add' x y

/-- A ring isomorphism preserves addition. -/
@[simp] lemma map_le (e : R ≃+*o S) (x y : R) : e x ≤ e y ↔ x ≤ y :=
begin
  have := e.map_rel_iff',
  convert @this x y
end

protected lemma congr_arg {f : R ≃+*o S} : Π {x x' : R}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : R ≃+*o S} (h : f = g) (x : R) : f x = g x := h ▸ rfl

/-- Two ordered ring isomorphisms agree if they are defined by the
  same underlying function. -/
@[ext] lemma ext {f g : R ≃+*o S} (h : ∀ x, f x = g x) : f = g :=
begin
  cases f, cases g, congr,
  apply ring_equiv.ext,
  intro x,
  convert h x,
end

lemma ext_iff {f g : R ≃+*o S} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, h ▸ rfl, ext⟩

@[norm_cast] lemma coe_ring_equiv (f : R ≃+*o S) (a : R) : (f : R ≃+* S) a = f a := rfl

@[norm_cast] lemma coe_mul_equiv (f : R ≃+*o S) (a : R) :
  (f : R ≃* S) a = f a := rfl

@[norm_cast] lemma coe_add_equiv (f : R ≃+*o S) (a : R) :
  (f : R ≃+ S) a = f a := rfl

variable (R)

/-- Identity map is an ordered ring isomorphism. -/
@[refl] protected def refl : R ≃+*o R :=
{ ..ring_equiv.refl _,
  ..rel_iso.refl _, }

variable {R}
@[simp] lemma refl_apply (x : R) : ordered_ring_equiv.refl R x = x := rfl

@[simp] lemma coe_add_equiv_refl : (ordered_ring_equiv.refl R : R ≃+ R) = add_equiv.refl R := rfl
@[simp] lemma coe_mul_equiv_refl : (ordered_ring_equiv.refl R : R ≃* R) = mul_equiv.refl R := rfl
@[simp] lemma coe_ring_equiv_refl : (ordered_ring_equiv.refl R : R ≃+* R) = ring_equiv.refl R := rfl
@[simp] lemma coe_order_iso_refl : (ordered_ring_equiv.refl R : R ≃o R) = rel_iso.refl _ := rfl

instance : inhabited (R ≃+*o R) := ⟨ordered_ring_equiv.refl R⟩

/-- Inverse map of an ordered ring isomorphism is an order isomorphism. -/
@[symm] protected def symm (f : R ≃+*o S) : S ≃+*o R :=
{ ..f.to_order_iso.symm,
  ..f.to_ring_equiv.symm, }

@[simp] lemma symm_symm (e : R ≃+*o S) : e.symm.symm = e := ext $ λ x, rfl

/-- Composition of two ordered ring isomorphisms is an order isomorphism. -/
@[trans] protected def trans {R S T : Type*} [has_mul R] [has_add R] [has_le R]
  [has_mul S] [has_add S] [has_le S]
  [has_mul T] [has_add T] [has_le T]
    (f₁ : R ≃+*o S) (f₂ : S ≃+*o T) : R ≃+*o T :=
{ ..f₁.to_ring_equiv.trans f₂.to_ring_equiv,
  ..f₁.to_order_iso.trans f₂.to_order_iso, }

@[simp] lemma trans_apply {R S T : Type*} [has_mul R] [has_add R] [has_le R]
  [has_mul S] [has_add S] [has_le S]
  [has_mul T] [has_add T] [has_le T]
    (f₁ : R ≃+*o S) (f₂ : S ≃+*o T) (a : R) : f₁.trans f₂ a = f₂ (f₁ a) := rfl

@[simp]
lemma trans_symm (e : R ≃+*o S) : e.trans e.symm = ordered_ring_equiv.refl R := ext (e : R ≃ S).3
@[simp]
lemma symm_trans (e : R ≃+*o S) : e.symm.trans e = ordered_ring_equiv.refl S := ext (e : R ≃ S).4

end ordered_ring_equiv

set_option old_structure_cmd true

/-- A field which is both linearly ordered and conditionally complete with respect to the order,
    this is an axiomatization of the reals. -/
class conditionally_complete_linear_ordered_field (F : Type*)
  extends linear_ordered_field F, conditionally_complete_linear_order F

-- TODO conditionally_complete_lattice or conditionally_complete_linear order?

/-- The reals are a conditionally complete linearly ordered field. -/
instance : conditionally_complete_linear_ordered_field ℝ := {
  ..real.linear_ordered_field,
  ..real.conditionally_complete_linear_order }

open real
/- TODO does this follow from intermediate_value_Icc -/
lemma exists_rat_sqr_btwn_rat_aux (x y : ℝ) (h : x < y) (hx : 0 ≤ x) :
  ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ ↑q^2 < y :=
begin
  have hy : (0 : ℝ) ≤ y := by linarith,
  rw ← sqrt_lt hx at h,
  obtain ⟨q, hqx, hqy⟩ := exists_rat_btwn h,
  have hq : (0 : ℝ) ≤ q :=
  begin
    transitivity x.sqrt,
    exact real.sqrt_nonneg x,
    exact le_of_lt hqx,
  end,
  refine ⟨q, _, _, _⟩,
  { assumption_mod_cast, },
  { rw [← real.sqrt_lt hx, real.sqrt_sqr hq], exact hqx },
  { rw [← real.sqrt_lt (pow_nonneg hq 2), real.sqrt_sqr hq], exact hqy },
end

theorem exists_rat_sqr_btwn_rat {x y : ℚ} (h : x < y) (hx : 0 ≤ x) :
  ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ q^2 < y :=
by apply_mod_cast exists_rat_sqr_btwn_rat_aux x y; assumption

/-- There is a rational square between any two elements of an archimedean ordered field -/
theorem exists_rat_sqr_btwn {F : Type*} [linear_ordered_field F] [archimedean F] {x y : F}
(h : x < y) (hx : 0 ≤ x) : ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ (q^2 : F) < y :=
begin
  obtain ⟨q1, hq1x, hq1y⟩ := exists_rat_btwn h,
  obtain ⟨q2, hq2x, hq1q2⟩ := exists_rat_btwn hq1x,
  norm_cast at hq1q2,
  have : (0 : F) ≤ q2 :=
  begin
    transitivity x,
    exact hx,
    exact (le_of_lt hq2x),
  end,
  obtain ⟨q, hqpos, hq⟩ := exists_rat_sqr_btwn_rat hq1q2 (by exact_mod_cast this),
  refine ⟨q, hqpos, _, _⟩,
  { transitivity (q2 : F),
    exact hq2x,
    exact_mod_cast hq.1, },
  { transitivity (q1 : F),
    exact_mod_cast hq.2,
    exact hq1y, }
end

/-- The lower cut of rationals inside a linear ordered field that are less than a given element of
    another linear ordered field. -/
def cut_image (F K : Type*) [linear_ordered_field F] [linear_ordered_field K] (x : F) : set K :=
λ k : K, k ∈ subtype.val '' ((cut_map F K) (λ t, t.val < x : set (set.range (coe : ℚ → F))))

lemma cut_image_nonempty (F K : Type*)
  [linear_ordered_field F] [archimedean F] [linear_ordered_field K] (x : F) :
(cut_image F K x).nonempty :=
begin
  obtain ⟨q, hq⟩ := exists_rat_lt x,
  simp only [cut_image, mem_image, exists_and_distrib_right, exists_eq_right, subtype.exists,
    subtype.coe_mk, subtype.val_eq_coe],
  use [q, mem_range_self q],
  rw [cut_map, mem_def],
  use [q, q, ⟨hq, range_rat_equiv_apply⟩],
end

lemma cut_image_bdd_above (F K : Type*) [linear_ordered_field F] [archimedean F]
  [linear_ordered_field K] (x : F) : bdd_above (cut_image F K x) :=
begin
  obtain ⟨q, hq⟩ := exists_rat_gt x,
  use q,
  simp only [cut_image, mem_image, exists_and_distrib_right, exists_eq_right, subtype.exists,
    subtype.coe_mk, subtype.val_eq_coe],
  rintros t ⟨⟨q2, rfl⟩, ⟨⟨f, ⟨q3, rfl⟩⟩, ⟨ht1, ht2⟩⟩⟩,
  erw range_rat_equiv_apply at ht2,
  simp only [subtype.mk_eq_mk, rat.cast_inj, rat.cast_le] at ht2 ⊢,
  rw ← ht2,
  suffices : (q3 : F) ≤ q,
  { exact_mod_cast this, },
  rw [mem_def, subtype.coe_mk] at ht1,
  exact le_of_lt (lt_trans ht1 hq),
end

lemma cut_image_subset (F K : Type*) [linear_ordered_field F] [linear_ordered_field K]
  {x y : F} (h : x ≤ y) : cut_image F K x ⊆ cut_image F K y :=
begin
  rintros t ⟨⟨y, ⟨q, rfl⟩⟩, ⟨⟨q2, ⟨q3, rfl⟩⟩, ht2, ht3⟩, rfl⟩,
  erw range_rat_equiv_apply at ht3,
  rw ← ht3,
  use ⟨q3, mem_range_self q3⟩,
  use ⟨q3, mem_range_self q3⟩,
  exact ⟨lt_of_lt_of_le ht2 h, range_rat_equiv_apply⟩,
end

lemma mem_cut_image_iff {F K : Type*} [linear_ordered_field F]
  [linear_ordered_field K] {x : F} {t : K} :
  t ∈ cut_image F K x ↔ ∃ (q : ℚ) (h : (q : K) = t), (q : F) < x :=
begin
  rw cut_image,
  simp only [mem_image, exists_and_distrib_right, exists_eq_right, subtype.exists, subtype.coe_mk,
    subtype.val_eq_coe],
  split,
  { rintros ⟨⟨q, _⟩, ⟨_, ⟨q2, rfl⟩⟩, hd, hh⟩,
    erw range_rat_equiv_apply at hh,
    simp only [subtype.mk_eq_mk, rat.cast_inj] at hh,
    exact ⟨q2, hh, hd⟩, },
  { rintro ⟨q, h, hx⟩,
    use [q, h, q, mem_range_self q],
    simp only [range_rat_equiv_apply, subtype.mk_eq_mk],
    exact ⟨hx, h⟩, },
end

lemma mem_cut_image_iff' {F K : Type*} [linear_ordered_field F] [linear_ordered_field K]
  {x : F} {q : ℚ} : (q : K) ∈ cut_image F K x ↔ (q : F) < x :=
begin
  rw mem_cut_image_iff,
  split,
  { rintros ⟨q2, h, he⟩,
    convert he,
    exact_mod_cast h.symm, },
  { intro h,
    use [q, rfl, h], },
end

lemma cut_image_ssubset (F K : Type*) [linear_ordered_field F] [archimedean F]
  [linear_ordered_field K] {x y : F} (h : x < y) : cut_image F K x ⊂ cut_image F K y :=
begin
  rw ssubset_iff_subset_ne,
  split,
  { exact cut_image_subset F K (le_of_lt h), },
  { obtain ⟨q, hqx, hqy⟩ := exists_rat_btwn h,
    have hy : (q : K) ∈ cut_image F K y := mem_cut_image_iff'.mpr hqy,
    have hx : (q : K) ∉ cut_image F K x := begin
      intro hh,
      rw mem_cut_image_iff' at hh,
      apply lt_irrefl x,
      transitivity (q : F),
      exact hqx,
      exact hh,
    end,
    intro ha,
    rw ← ha at hy,
    exact hx hy, }, -- TODO couldn't get ne_of_mem_of_not_mem to work ?
end

lemma cut_image_self (F : Type*) [linear_ordered_field F] (x : F) : cut_image F F x =
  set.Iio x ∩ set.range (coe : ℚ → F) :=
begin
  ext y,
  simp only [mem_cut_image_iff, mem_inter_eq, mem_Iio, mem_range],
  split,
  { rintro ⟨h, rfl, a⟩, exact ⟨a, h, rfl⟩ },
  { rintro ⟨h, a, rfl⟩, exact ⟨a, rfl, h⟩ }
end

lemma cut_image_rat {F K : Type*} [linear_ordered_field F] [linear_ordered_field K] {q : ℚ} :
  cut_image F K (q : F) = subtype.val '' (λ t, t.val < q : set (set.range (coe : ℚ → K))) :=
begin
  ext x,
  simp only [mem_cut_image_iff, mem_image, exists_prop, rat.cast_lt, exists_and_distrib_right,
    exists_eq_right, subtype.exists, subtype.coe_mk, subtype.val_eq_coe],
  split; intro h,
  { rcases h with ⟨q2, rfl, hq2⟩,
    use [q2, rat.cast_lt.mpr hq2], },
  { rcases h with ⟨⟨q2, rfl⟩, hq⟩,
    use [q2, rfl, rat.cast_lt.mp hq], },
end

lemma cut_image_add (F K : Type*) [linear_ordered_field F] [archimedean F] [linear_ordered_field K]
  (x y : F) : cut_image F K (x + y) = cut_image F K x + cut_image F K y :=
begin
  ext t,
  split; intro h,
  { rw mem_cut_image_iff at h,
    rcases h with ⟨q, rfl, h⟩,
    rw ← sub_lt_iff_lt_add at h,
    obtain ⟨q₁, hq₁q, hq₁xy⟩ := exists_rat_btwn h,
    refine ⟨q₁, q - q₁, _, _, by abel⟩; try {norm_cast};
    rw mem_cut_image_iff',
    assumption,
    push_cast,
    exact sub_lt.mp hq₁q, },
  { rcases h with ⟨tx, ty, htx, hty, rfl⟩,
    rw mem_cut_image_iff at *,
    rcases htx with ⟨qx, rfl, hx⟩,
    rcases hty with ⟨qy, rfl, hy⟩,
    use [qx + qy, by norm_cast],
    push_cast,
    exact add_lt_add hx hy, },
end

lemma lt_of_mul_self_lt_mul_self {F : Type*} [linear_ordered_field F] {a b : F} (ha : 0 ≤ a)
  (hb : 0 < b) (h : a * a < b * b) : a < b :=
begin
  rw [← sub_pos, mul_self_sub_mul_self] at h,
  rw ← sub_pos,
  exact (zero_lt_mul_left (lt_add_of_pos_of_le hb ha)).mp h,
end

lemma lt_of_pow_two_lt_pow_two {F : Type*} [linear_ordered_field F] {a b : F} (ha : 0 ≤ a)
  (hb : 0 < b) (h : a^2 < b^2) : a < b :=
by { rw [pow_two, pow_two] at h, exact lt_of_mul_self_lt_mul_self ha hb h}

namespace conditionally_complete_linear_ordered_field

variables {F : Type*} [conditionally_complete_linear_ordered_field F]

/-- Any conditionally complete linearly ordered field is archimedean. -/
@[priority 100] -- see Note [lower instance priority]
instance : archimedean F := archimedean_iff_nat_lt.mpr
begin
  by_contra h,
  push_neg at h,
  have : ∀ (b : F), b ∈ set.range (coe : ℕ → F) → b ≤ Sup (set.range (coe : ℕ → F)) - 1 :=
  begin
    obtain ⟨x, h⟩ := h,
    have : bdd_above (set.range (coe : ℕ → F)) :=
    begin
      use x,
      rintros _ ⟨n, rfl⟩,
      exact h n,
    end,
    rintro b ⟨n, rfl⟩,
    rw le_sub_iff_add_le,
    exact le_cSup _ _ this ⟨n + 1, nat.cast_succ n⟩,
  end,
  replace := cSup_le _ _ (set.range_nonempty (coe : ℕ → F)) this,
  linarith,
end

/-- The induced order preserving function from a linear ordered field to a conditionally complete
    linear ordered field, defined by taking the Sup in the codomain of all the rationals less than
    the input. -/
def induced_map (F K : Type*) [linear_ordered_field F]
  [conditionally_complete_linear_ordered_field K] : F → K :=
λ x, Sup (cut_image F K x)

lemma induced_map_le (F K : Type*) [linear_ordered_field F] [archimedean F]
[conditionally_complete_linear_ordered_field K]
  {x y : F} (h : x ≤ y) : induced_map F K x ≤ induced_map F K y :=
cSup_le_cSup (cut_image_bdd_above F K _) (cut_image_nonempty F K _) (cut_image_subset F K h)

lemma induced_map_rat (F K : Type*) [linear_ordered_field F] [archimedean F]
  [conditionally_complete_linear_ordered_field K] (q : ℚ) : induced_map F K (q : F) = q :=
begin
  rw induced_map,
  apply cSup_intro (cut_image_nonempty F K q),
  { intros x h,
    simp only [cut_image_rat, mem_image, exists_and_distrib_right, exists_eq_right, subtype.exists,
      subtype.coe_mk, subtype.val_eq_coe] at h,
    rcases h with ⟨⟨q, rfl⟩, h⟩,
    exact le_of_lt h, },
  { rintro w h,
    obtain ⟨q2, hq2w, hq2q⟩ := exists_rat_btwn h,
    use q2,
    simp only [cut_image_rat, mem_image, exists_eq, mem_range, exists_and_distrib_right,
      exists_eq_right, exists_prop_of_true, subtype.exists, rat.cast_inj, subtype.coe_mk,
      subtype.val_eq_coe],
    exact ⟨hq2q, hq2w⟩, },
end

lemma lt_induced_map_iff {F K : Type*} [linear_ordered_field F] [archimedean F]
  [conditionally_complete_linear_ordered_field K] {x : F} {t : K} :
  t < induced_map F K x ↔ ∃ (q : ℚ) (h : t < q), (q : F) < x :=
begin
  split,
  { intro h,
    obtain ⟨q, hqt, hqi⟩ := exists_rat_btwn h,
    use [q, hqt],
    rw induced_map at hqi,
    by_contra hx,
    push_neg at hx,
    have hs := cSup_le_cSup (cut_image_bdd_above F K _)
                (cut_image_nonempty F K x) (cut_image_subset F K hx),
    change _ ≤ induced_map F K q at hs,
    rw induced_map_rat at hs,
    apply lt_irrefl (q : K) (lt_of_lt_of_le hqi hs), },
  { rintro ⟨q, hqt, hqx⟩,
    transitivity (q : K),
    { exact hqt },
    { obtain ⟨q2, hq2q, hq2x⟩ := exists_rat_btwn hqx,
      rw induced_map,
      have : (q2 : K) ∈ cut_image F K x := mem_cut_image_iff'.mpr hq2x,
      apply lt_cSup_of_lt (cut_image_bdd_above F K x) this,
      exact_mod_cast hq2q, }, },
end

-- lemma induced_map_lt_iff {F K : Type*} [linear_ordered_field F] [archimedean F]
--   [conditionally_complete_linear_ordered_field K] {x : F} {t : K} :
--   induced_map F K x < t ↔ ∃ (q : ℚ) (h : (q : K) < t), x < q :=
-- begin
--   split,
--   { intro h,
--     obtain ⟨q, hqt, hqi⟩ := exists_rat_btwn h,
--     use [q, hqi],
--     rw induced_map at hqi,
--     by_contra hx,
--     push_neg at hx,
--     have hs := cSup_le_cSup (cut_image_bdd_above F K _)
--                 (cut_image_nonempty F K x) (cut_image_subset F K hx),
--     change _ ≤ induced_map F K q at hs,
--     rw induced_map_rat at hs,
--     apply lt_irrefl (q : K) (lt_of_lt_of_le hqi hs), },
--   { rintro ⟨q, hqt, hqx⟩,
--     transitivity (q : K),
--     { exact hqt },
--     { obtain ⟨q2, hq2q, hq2x⟩ := exists_rat_btwn hqx,
--       rw induced_map,
--       have : (q2 : K) ∈ cut_image F K x := mem_cut_image_iff'.mpr hq2x,
--       apply lt_cSup_of_lt (cut_image_bdd_above F K x) this,
--       exact_mod_cast hq2q, }, },
-- end

lemma pointwise_add_Sup (A B : set F) (hA : A.nonempty) (hB : B.nonempty)
  (hbA : bdd_above A) (hbB : bdd_above B) : Sup (A + B) = Sup A + Sup B :=
begin
  apply cSup_intro (nonempty.add hA hB),
  { rintros f ⟨a, b, ha, hb, rfl⟩,
    exact add_le_add (le_cSup _ _ hbA ha) (le_cSup _ _ hbB hb), },
  { intros w hw,
    have : w - Sup B < Sup A := sub_lt_iff_lt_add.mpr hw,
    obtain ⟨a, ha, halt⟩ := exists_lt_of_lt_cSup hA this,
    have : w - a < Sup B := sub_lt.mp halt,
    obtain ⟨b, hb, hblt⟩ := exists_lt_of_lt_cSup hB this,
    exact ⟨a + b, add_mem_add ha hb, sub_lt_iff_lt_add'.mp hblt⟩, }
end

lemma induced_map_add (F K : Type*) [linear_ordered_field F] [archimedean F]
  [conditionally_complete_linear_ordered_field K] (x y : F) :
  induced_map F K (x + y) = induced_map F K x + induced_map F K y :=
begin
  simp only [induced_map],
  rw [cut_image_add, pointwise_add_Sup],
  exact cut_image_nonempty F K x,
  exact cut_image_nonempty F K y,
  exact cut_image_bdd_above F K x,
  exact cut_image_bdd_above F K y
end

/-- induced_map as an additive homomorphism -/
def induced_add_map (F K : Type*) [linear_ordered_field F] [archimedean F]
  [conditionally_complete_linear_ordered_field K] : F →+ K :=
{ to_fun := induced_map F K,
  map_zero' := by exact_mod_cast induced_map_rat F K 0,
  map_add' := induced_map_add F K }

/-- Preparatory lemma for `induced_ring_map` -/
lemma le_induced_mul_self_of_mem_cut_image (F K : Type*) [linear_ordered_field F] [archimedean F]
  [conditionally_complete_linear_ordered_field K] (x : F) (hpos : 0 < x) (a : K)
  (ha : a ∈ cut_image F K (x * x)) : a ≤ induced_add_map F K x * induced_add_map F K x :=
begin
  rw mem_cut_image_iff at ha,
  rcases ha with ⟨q, rfl, ha⟩,
  by_cases hq : 0 ≤ (q : K),
  { have : 0 ≤ (q : F) := by exact_mod_cast hq,
    obtain ⟨q2, hqpos, hq21, hq22⟩ := exists_rat_sqr_btwn ha this,
    rw pow_two at hq22,
    have : (q2 : F) < x := lt_of_mul_self_lt_mul_self (rat.cast_nonneg.mpr hqpos) hpos hq22,
    rw ← @mem_cut_image_iff' F K at this,
    have : (q2 : K) ≤ induced_map F K x := le_cSup _ _ (cut_image_bdd_above F K x) this,
    transitivity (q2 : K)^2,
    apply le_of_lt,
    assumption_mod_cast,
    rw pow_two,
    have q2pos : (0 : K) ≤ q2 := by exact_mod_cast hqpos,
    exact mul_le_mul this this q2pos (le_trans _ _ _ q2pos this), },
  { transitivity (0 : K),
    push_neg at hq,
    exact le_of_lt hq,
    exact mul_self_nonneg (Sup (cut_image F K x)), },
end

/-- Preparatory lemma for `induced_ring_map` -/
lemma exists_mem_cut_image_mul_self_of_lt_induced_map_mul_self (F K : Type*)
  [linear_ordered_field F] [archimedean F] [conditionally_complete_linear_ordered_field K] (x : F)
  (hpos : 0 < x) (y : K) (hy : y < induced_add_map F K x * induced_add_map F K x) :
∃ a ∈ cut_image F K (x * x), y < a :=
begin
  by_cases hypos : 0 ≤ y,
  { obtain ⟨q2, hqpos, hq21, hq22⟩ := exists_rat_sqr_btwn hy hypos,
    rw pow_two at hq22,
    have : (q2 : K) < _ := lt_of_mul_self_lt_mul_self _ _ hq22,
    use (q2 : K)^2,
    split,
    norm_cast,
    rw mem_cut_image_iff',
    erw [induced_add_map, lt_induced_map_iff] at this,
    obtain ⟨q3, hq23, hh⟩ := this,
    rw pow_two,
    push_cast,
    have : (q2 : F) < x :=
    begin
      transitivity (q3 : F),
      assumption_mod_cast,
    end,
    apply mul_lt_mul'' this this,
    assumption_mod_cast,
    assumption_mod_cast,
    exact hq21,
    exact_mod_cast hqpos,
    simp only [induced_add_map, add_monoid_hom.coe_mk],
    rw lt_induced_map_iff,
    obtain ⟨q3, q30, q3x⟩ := exists_rat_btwn hpos,
    use q3,
    split,
    assumption_mod_cast, },
  { use ((0 : ℚ) : K),
    split,
    rw [mem_cut_image_iff', rat.cast_zero],
    exact linear_ordered_field.mul_pos _ _ hpos hpos,
    push_neg at hypos,
    rw [rat.cast_zero],
    exact hypos, },
end

/-- `induced_map` as a `ring_hom` -/
def induced_ring_map (F K : Type*) [linear_ordered_field F] [archimedean F]
  [conditionally_complete_linear_ordered_field K] :
F →+* K := ring_hom.mk_mul_self_of_two_ne_zero (induced_add_map F K) -- reduce to the case of x = y
begin
  intro x,
  -- reduce to the case of 0 < x
  suffices : ∀ (x : F) (hpos : 0 < x),
    induced_add_map F K (x * x) = induced_add_map F K x * induced_add_map F K x,
  begin
    rcases lt_trichotomy x 0 with h|rfl|h,
    { rw ← neg_pos at h,
      convert this (-x) h using 1,
      { simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg], },
      { simp only [neg_mul_eq_neg_mul_symm, add_monoid_hom.map_neg, mul_neg_eq_neg_mul_symm,
          neg_neg], }, },
    { simp only [mul_zero, add_monoid_hom.map_zero], },
    { exact this x h, },
  end,
  clear x,
  intros x hpos,
  -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less than
  -- (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
  apply cSup_intro (cut_image_nonempty F K _),
  exact le_induced_mul_self_of_mem_cut_image F K x hpos,
  exact exists_mem_cut_image_mul_self_of_lt_induced_map_mul_self F K x hpos,
end two_ne_zero begin convert induced_map_rat F K 1; rw [rat.cast_one], refl, end

@[simp]
lemma induced_map_inv_self (F K : Type*) [conditionally_complete_linear_ordered_field F]
  [conditionally_complete_linear_ordered_field K] (x : F) :
  induced_map K F (induced_map F K x) = x :=
begin
  rw [induced_map],
  apply cSup_intro (cut_image_nonempty K F (induced_map F K x)),
  { intros y hy,
    rw mem_cut_image_iff at hy,
    rcases hy with ⟨q, rfl, h⟩,
    rw induced_map at h,
    obtain ⟨y, hym, hyq⟩ := exists_lt_of_lt_cSup (cut_image_nonempty F K x) h,
    rw mem_cut_image_iff at hym,
    obtain ⟨q2, rfl, h⟩ := hym,
    apply le_of_lt,
    transitivity (q2 : F),
    assumption_mod_cast,
    assumption, },
  { intros w hw,
    obtain ⟨q, hqw, hqx⟩ := exists_rat_btwn hw,
    refine ⟨q, _, _⟩,
    { rw [mem_cut_image_iff', lt_induced_map_iff],
      obtain ⟨q2, hq2q, hq2x⟩ := exists_rat_btwn hqx,
      refine ⟨q2, _, _⟩,
      exact_mod_cast hq2q,
      exact_mod_cast hq2x, },
    { exact_mod_cast hqw, }, }
end

/-- The equivalence of ordered rings between two conditionally complete linearly ordered fields. -/
def cut_ordered_ring_equiv (F K : Type*)
  [conditionally_complete_linear_ordered_field F] [conditionally_complete_linear_ordered_field K] :
  F ≃+*o K :=
{ inv_fun := induced_map K F,
  left_inv := induced_map_inv_self F K,
  right_inv := induced_map_inv_self K F,
  map_rel_iff' := λ x y, begin
    refine ⟨λ h, _, induced_map_le _ _⟩,
    simpa [induced_ring_map, ring_hom.mk_mul_self_of_two_ne_zero, induced_add_map]
      using induced_map_le K F h,
  end,
  ..induced_ring_map F K }

lemma cut_ordered_equiv (F K : Type*)
  [conditionally_complete_linear_ordered_field F] [conditionally_complete_linear_ordered_field K] :
  (cut_ordered_ring_equiv F K : F → K) = induced_map F K := rfl

lemma cut_ordered_ring_equiv_symm (F K : Type*)
  [conditionally_complete_linear_ordered_field F] [conditionally_complete_linear_ordered_field K] :
  (cut_ordered_ring_equiv F K).symm = cut_ordered_ring_equiv K F := rfl

@[simp]
lemma cut_ordered_ring_equiv_self (F : Type*) [conditionally_complete_linear_ordered_field F] :
  cut_ordered_ring_equiv F F = ordered_ring_equiv.refl F :=
begin
  ext,
  simp,
  change induced_map F F x = x,
  rw induced_map,
  dsimp,
  rw cut_image_self,
  apply cSup_intro,
  { obtain ⟨q, h⟩ := exists_rat_lt x,
    refine ⟨q, h, mem_range_self _⟩, },
  { rintro y ⟨hlt, _⟩,
    exact le_of_lt hlt, },
  { rintro y hlt,
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hlt,
    refine ⟨q, ⟨hqx, mem_range_self _⟩, hyq⟩, }
end

@[simp] lemma ring_equiv_rat {F K : Type*} [division_ring F] [division_ring K]
  [char_zero F] [char_zero K] (f : F ≃+* K) (q : ℚ) : f q = q :=
begin
  suffices : (f.to_ring_hom.comp (rat.cast_hom F)) q = q,
  { simpa, },
  exact ring_hom.map_rat_cast _ q,
end

@[simp] lemma ordered_ring_equiv_rat {F K : Type*}
  [conditionally_complete_linear_ordered_field F] [conditionally_complete_linear_ordered_field K]
  (f : F ≃+*o K) (q : ℚ) : f q = q := ring_equiv_rat f.to_ring_equiv q

open ordered_ring_equiv

lemma ordered_ring_equiv_eq_cut_ordered_ring_equiv {F K : Type*}
  [conditionally_complete_linear_ordered_field F] [conditionally_complete_linear_ordered_field K]
  (f : F ≃+*o K) : f = cut_ordered_ring_equiv F K :=
begin
  ext,
  rw le_antisymm_iff, rw [← not_lt, ← not_lt],
  split; intro h;
  rcases exists_rat_btwn h with ⟨q, hq, hq₂⟩;
  rw ← ordered_ring_equiv_rat (cut_ordered_ring_equiv F K) at hq hq₂,
  work_on_goal 0 {
    rw ← ((cut_ordered_ring_equiv F K).symm : K ≃o F).lt_iff_lt at hq,
    rw ← (f.symm : K ≃o F).lt_iff_lt at hq₂, },
  work_on_goal 1 {
    rw ← ((cut_ordered_ring_equiv F K).symm : K ≃o F).lt_iff_lt at hq₂,
    rw ← (f.symm : K ≃o F).lt_iff_lt at hq, },
  all_goals {
    simp only [to_order_iso_coe_fun_eq_to_equiv, ordered_ring_equiv_rat, ← trans_apply, symm_trans,
      trans_symm, refl_apply] at hq hq₂,
    linarith, },
end

end conditionally_complete_linear_ordered_field
