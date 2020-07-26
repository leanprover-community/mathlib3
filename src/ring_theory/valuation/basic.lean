/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/

import algebra.linear_ordered_comm_group_with_zero
import algebra.group_power
import ring_theory.ideal_operations
import ring_theory.subring
import algebra.punit_instances

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative group with zero, that in addition satisfies the following two axioms:
 * `v 0 = 0`
 * `∀ x y, v (x + y) ≤ max (v x) (v y)`

`valuation R Γ₀`is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `is_equiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : valuation R Γ₁` and `v₂ : valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

The support of a valuation `v : valuation R Γ₀` is `supp v`. If `J` is an ideal of `R`
with `h : J ⊆ supp v` then the induced valuation
on R / J = `ideal.quotient J` is `on_quot v h`.

## Main definitions

* `valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `valuation.is_equiv`, the heterogeneous equivalence relation on valuations
* `valuation.supp`, the support of a valuation

-/

open_locale classical
noncomputable theory

local attribute [instance, priority 0] classical.DLO

open function ideal

-- universes u u₀ u₁ u₂ -- v is used for valuations

variables {R : Type*} -- This will be a ring, assumed commutative in some sections

variables {Γ₀   : Type*}  [linear_ordered_comm_group_with_zero Γ₀]
variables {Γ'₀  : Type*} [linear_ordered_comm_group_with_zero Γ'₀]
variables {Γ''₀ : Type*} [linear_ordered_comm_group_with_zero Γ''₀]

set_option old_structure_cmd true

section
variables (R) (Γ₀) [ring R]

/-- The type of Γ₀-valued valuations on R. -/
@[nolint has_inhabited_instance]
structure valuation extends R →* Γ₀ :=
(map_zero' : to_fun 0 = 0)
(map_add' : ∀ x y, to_fun (x + y) ≤ max (to_fun x) (to_fun y))

run_cmd tactic.add_doc_string `valuation.to_monoid_hom "The `monoid_hom` underlying a valuation."

end

namespace valuation

section basic
variables (R) (Γ₀) [ring R]

/-- A valuation is coerced to the underlying function R → Γ₀. -/
instance : has_coe_to_fun (valuation R Γ₀) := { F := λ _, R → Γ₀, coe := valuation.to_fun }

/-- A valuation is coerced to a monoid morphism R → Γ₀. -/
instance : has_coe (valuation R Γ₀) (R →* Γ₀) := ⟨valuation.to_monoid_hom⟩

variables {R} {Γ₀} (v : valuation R Γ₀) {x y z : R}

@[simp, norm_cast] lemma coe_coe : ((v : R →* Γ₀) : R → Γ₀) = v := rfl

@[simp] lemma map_zero : v 0 = 0 := v.map_zero'
@[simp] lemma map_one  : v 1 = 1 := v.map_one'
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.map_mul'
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ max (v x) (v y) := v.map_add'

@[simp] lemma map_pow  : ∀ x (n:ℕ), v (x^n) = (v x)^n :=
v.to_monoid_hom.map_pow

@[ext] lemma ext {v₁ v₂ : valuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
by { cases v₁, cases v₂, congr, funext r, exact h r }

lemma ext_iff {v₁ v₂ : valuation R Γ₀} : v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r :=
⟨λ h r, congr_arg _ h, ext⟩

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.

/-- A valuation gives a preorder on the underlying ring. -/
def to_preorder : preorder R := preorder.lift v

/-- If `v` is a valuation on a division ring then `v(x) = 0` iff `x = 0`. -/
@[simp] lemma zero_iff {K : Type*} [division_ring K]
  (v : valuation K Γ₀) {x : K} : v x = 0 ↔ x = 0 :=
begin
  split ; intro h,
  { contrapose! h,
    exact ((is_unit.mk0 _ h).map (v : K →* Γ₀)).ne_zero },
  { exact h.symm ▸ v.map_zero },
end

lemma ne_zero_iff {K : Type*} [division_ring K]
  (v : valuation K Γ₀) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
not_iff_not_of_iff v.zero_iff

@[simp] lemma map_inv {K : Type*} [division_ring K]
  (v : valuation K Γ₀) {x : K} : v x⁻¹ = (v x)⁻¹ :=
begin
  by_cases h : x = 0,
  { subst h, rw [inv_zero, v.map_zero, inv_zero] },
  { apply eq_inv_of_mul_right_eq_one,
    rw [← v.map_mul, mul_inv_cancel h, v.map_one] }
end

lemma map_units_inv (x : units R) : v (x⁻¹ : units R) = (v x)⁻¹ :=
eq_inv_of_mul_right_eq_one $ by rw [← v.map_mul, units.mul_inv, v.map_one]

@[simp] theorem unit_map_eq (u : units R) :
  (units.map (v : R →* Γ₀) u : Γ₀) = v u := rfl

theorem map_neg_one : v (-1) = 1 :=
begin
  apply eq_one_of_pow_eq_one (nat.succ_ne_zero 1) (_ : _ ^ 2 = _),
  rw [pow_two, ← v.map_mul, neg_one_mul, neg_neg, v.map_one],
end

@[simp] lemma map_neg (x : R) : v (-x) = v x :=
calc v (-x) = v (-1 * x)   : by rw [neg_one_mul]
        ... = v (-1) * v x : map_mul _ _ _
        ... = v x          : by rw [v.map_neg_one, one_mul]

lemma map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
calc v (x - y) = v (-(y - x)) : by rw show x - y = -(y-x), by abel
           ... = _ : map_neg _ _

lemma map_sub_le_max (x y : R) : v (x - y) ≤ max (v x) (v y) :=
calc v (x - y) = v (x + -y)         : by rw [sub_eq_add_neg]
           ... ≤ max (v x) (v $ -y) : v.map_add _ _
           ... = max (v x) (v y)    : by rw map_neg

lemma map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = max (v x) (v y) :=
begin
  suffices : ¬v (x + y) < max (v x) (v y),
    from or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this,
  intro h',
  wlog vyx : v y < v x using x y,
  { apply lt_or_gt_of_ne h.symm },
  { rw max_eq_left_of_lt vyx at h',
    apply lt_irrefl (v x),
    calc v x = v ((x+y) - y)         : by simp
         ... ≤ max (v $ x + y) (v y) : map_sub_le_max _ _ _
         ... < v x                   : max_lt h' vyx },
  { apply this h.symm,
    rwa [add_comm, max_comm] at h' }
end

lemma map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x :=
begin
  have := valuation.map_add_of_distinct_val v (ne_of_gt h).symm,
  rw max_eq_right (le_of_lt h) at this,
  simpa using this
end

/-- A ring homomorphism S → R induces a map valuation R Γ₀ → valuation S Γ₀ -/
def comap {S : Type*} [ring S] (f : S →+* R) (v : valuation R Γ₀) :
  valuation S Γ₀ :=
by refine_struct { to_fun := v ∘ f, .. }; intros;
  simp only [comp_app, map_one, map_mul, map_zero, map_add,
             f.map_one, f.map_mul, f.map_zero, f.map_add]

@[simp] lemma comap_id : v.comap (ring_hom.id R) = v := ext $ λ r, rfl

lemma comap_comp {S₁ : Type*} {S₂ : Type*} [ring S₁] [ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
  v.comap (g.comp f) = (v.comap g).comap f :=
ext $ λ r, rfl

/-- A ≤-preserving group homomorphism Γ₀ → Γ'₀ induces a map valuation R Γ₀ → valuation R Γ'₀. -/
def map (f : Γ₀ →* Γ'₀) (h₀ : f 0 = 0) (hf : monotone f) (v : valuation R Γ₀) : valuation R Γ'₀ :=
{ to_fun := f ∘ v,
  map_zero' := show f (v 0) = 0, by rw [v.map_zero, h₀],
  map_add' := λ r s,
    calc f (v (r + s)) ≤ f (max (v r) (v s))     : hf (v.map_add r s)
                   ... = max (f (v r)) (f (v s)) : hf.map_max,
  .. monoid_hom.comp f (v : R →* Γ₀) }

/-- Two valuations on R are defined to be equivalent if they induce the same preorder on R. -/
def is_equiv (v₁ : valuation R Γ₀) (v₂ : valuation R Γ'₀) : Prop :=
∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

end basic -- end of section

namespace is_equiv
variables [ring R]
variables {v : valuation R Γ₀}
variables {v₁ : valuation R Γ₀} {v₂ : valuation R Γ'₀} {v₃ : valuation R Γ''₀}

@[refl] lemma refl : v.is_equiv v :=
λ _ _, iff.refl _

@[symm] lemma symm (h : v₁.is_equiv v₂) : v₂.is_equiv v₁ :=
λ _ _, iff.symm (h _ _)

@[trans] lemma trans (h₁₂ : v₁.is_equiv v₂) (h₂₃ : v₂.is_equiv v₃) : v₁.is_equiv v₃ :=
λ _ _, iff.trans (h₁₂ _ _) (h₂₃ _ _)

lemma of_eq {v' : valuation R Γ₀} (h : v = v') : v.is_equiv v' :=
by { subst h }

lemma map {v' : valuation R Γ₀} (f : Γ₀ →* Γ'₀) (h₀ : f 0 = 0) (hf : monotone f) (inf : injective f)
  (h : v.is_equiv v') :
  (v.map f h₀ hf).is_equiv (v'.map f h₀ hf) :=
let H : strict_mono f := strict_mono_of_monotone_of_injective hf inf in
λ r s,
calc f (v r) ≤ f (v s) ↔ v r ≤ v s   : by rw H.le_iff_le
                   ... ↔ v' r ≤ v' s : h r s
                   ... ↔ f (v' r) ≤ f (v' s) : by rw H.le_iff_le

/-- `comap` preserves equivalence. -/
lemma comap {S : Type*} [ring S] (f : S →+* R) (h : v₁.is_equiv v₂) :
  (v₁.comap f).is_equiv (v₂.comap f) :=
λ r s, h (f r) (f s)

lemma val_eq (h : v₁.is_equiv v₂) {r s : R} :
  v₁ r = v₁ s ↔ v₂ r = v₂ s :=
by simpa only [le_antisymm_iff] using and_congr (h r s) (h s r)

lemma ne_zero (h : v₁.is_equiv v₂) {r : R} :
  v₁ r ≠ 0 ↔ v₂ r ≠ 0 :=
begin
  have : v₁ r ≠ v₁ 0 ↔ v₂ r ≠ v₂ 0 := not_iff_not_of_iff h.val_eq,
  rwa [v₁.map_zero, v₂.map_zero] at this,
end

end is_equiv -- end of namespace

lemma is_equiv_of_map_strict_mono [ring R] {v : valuation R Γ₀}
  (f : Γ₀ →* Γ'₀) (h₀ : f 0 = 0) (H : strict_mono f) :
  is_equiv (v.map f h₀ (H.monotone)) v :=
λ x y, ⟨H.le_iff_le.mp, λ h, H.monotone h⟩

lemma is_equiv_of_val_le_one {K : Type*} [division_ring K]
  (v : valuation K Γ₀) (v' : valuation K Γ'₀) (h : ∀ {x:K}, v x ≤ 1 ↔ v' x ≤ 1) :
  v.is_equiv v' :=
begin
  intros x y,
  by_cases hy : y = 0, { simp [hy, zero_iff], },
  rw show y = 1 * y, by rw one_mul,
  rw [← (inv_mul_cancel_right' hy x)],
  iterate 2 {rw [v.map_mul _ y, v'.map_mul _ y]},
  rw [v.map_one, v'.map_one],
  split; intro H,
  { apply mul_le_mul_right',
    replace hy := v.ne_zero_iff.mpr hy,
    replace H := le_of_le_mul_right hy H,
    rwa h at H, },
  { apply mul_le_mul_right',
    replace hy := v'.ne_zero_iff.mpr hy,
    replace H := le_of_le_mul_right hy H,
    rwa h, },
end

section supp
variables [comm_ring R]
variables (v : valuation R Γ₀)

/-- The support of a valuation `v : R → Γ₀` is the ideal of `R` where `v` vanishes. -/
def supp : ideal R :=
{ carrier   := {x | v x = 0},
  zero_mem' := map_zero v,
  add_mem'  := λ x y hx hy, le_zero_iff.mp $
    calc v (x + y) ≤ max (v x) (v y) : v.map_add x y
               ... ≤ 0               : max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy),
  smul_mem' := λ c x hx, calc v (c * x)
                        = v c * v x : map_mul v c x
                    ... = v c * 0 : congr_arg _ hx
                    ... = 0 : mul_zero _ }

@[simp] lemma mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 := iff.rfl
-- @[simp] lemma mem_supp_iff' (x : R) : x ∈ (supp v : set R) ↔ v x = 0 := iff.rfl

/-- The support of a valuation is a prime ideal. -/
instance : ideal.is_prime (supp v) :=
⟨λ (h : v.supp = ⊤), one_ne_zero $ show (1 : Γ₀) = 0,
from calc 1 = v 1 : v.map_one.symm
        ... = 0   : show (1:R) ∈ supp v, by { rw h, trivial },
 λ x y hxy, begin
    show v x = 0 ∨ v y = 0,
    change v (x * y) = 0 at hxy,
    rw [v.map_mul x y] at hxy,
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy
  end⟩

lemma map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a :=
begin
  have aux : ∀ a s, v s = 0 → v (a + s) ≤ v a,
  { intros a' s' h', refine le_trans (v.map_add a' s') (max_le (le_refl _) _), simp [h'], },
  apply le_antisymm (aux a s h),
  calc v a = v (a + s + -s) : by simp
       ... ≤ v (a + s)      : aux (a + s) (-s) (by rwa ←ideal.neg_mem_iff at h)
end

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
def on_quot_val {J : ideal R} (hJ : J ≤ supp v) :
  J.quotient → Γ₀ :=
λ q, quotient.lift_on' q v $ λ a b h,
calc v a = v (b + (a - b)) : by simp
     ... = v b             : v.map_add_supp b (hJ h)

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
def on_quot {J : ideal R} (hJ : J ≤ supp v) :
  valuation J.quotient Γ₀ :=
{ to_fun := v.on_quot_val hJ,
  map_zero' := v.map_zero,
  map_one'  := v.map_one,
  map_mul'  := λ xbar ybar, quotient.ind₂' v.map_mul xbar ybar,
  map_add'  := λ xbar ybar, quotient.ind₂' v.map_add xbar ybar }

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
ext $ λ r,
begin
  refine @quotient.lift_on_beta _ _ (J.quotient_rel) v (λ a b h, _) _,
  calc v a = v (b + (a - b)) : by simp
       ... = v b             : v.map_add_supp b (hJ h)
end

lemma comap_supp {S : Type*} [comm_ring S] (f : S →+* R) :
  supp (v.comap f) = ideal.comap f v.supp :=
ideal.ext $ λ x,
begin
  rw [mem_supp_iff, ideal.mem_comap, mem_supp_iff],
  refl,
end

lemma self_le_supp_comap (J : ideal R) (v : valuation (quotient J) Γ₀) :
  J ≤ (v.comap (ideal.quotient.mk J)).supp :=
by { rw [comap_supp, ← ideal.map_le_iff_le_comap], simp }

@[simp] lemma comap_on_quot_eq (J : ideal R) (v : valuation J.quotient Γ₀) :
  (v.comap (ideal.quotient.mk J)).on_quot (v.self_le_supp_comap J) = v :=
ext $ by { rintro ⟨x⟩, refl }

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
lemma supp_quot {J : ideal R} (hJ : J ≤ supp v) :
  supp (v.on_quot hJ) = (supp v).map (ideal.quotient.mk J) :=
begin
  apply le_antisymm,
  { rintro ⟨x⟩ hx,
    apply ideal.subset_span,
    exact ⟨x, hx, rfl⟩ },
  { rw ideal.map_le_iff_le_comap,
    intros x hx, exact hx }
end

lemma supp_quot_supp : supp (v.on_quot (le_refl _)) = 0 :=
by { rw supp_quot, exact ideal.map_quotient_self _ }

end supp -- end of section

end valuation
