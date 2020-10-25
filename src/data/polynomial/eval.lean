/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.induction
import data.polynomial.degree.basic
import deprecated.ring

/-!
# Theory of univariate polynomials

The main defs here are `eval₂`, `eval`, and `map`.
We give several lemmas about their interaction with each other and with module operations.
-/

noncomputable theory

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v w y
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

section
variables [semiring S]
variables (f : R →+* S) (x : S)

/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
def eval₂ : polynomial R →+ S := add_monoid_algebra.lift_nc f (powers_hom S x)

lemma eval₂_eq_sum {f : R →+* S} {x : S} : eval₂ f x p = p.sum (λ e a, f a * x ^ e) := rfl

lemma eval₂_congr {R S : Type*} [semiring R] [semiring S]
  {f g : R →+* S} {s t : S} {φ ψ : polynomial R} :
  f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ :=
by rintro rfl rfl rfl; refl

lemma eval₂_zero : eval₂ f x 0 = 0 := (eval₂ f x).map_zero

@[simp] lemma eval₂_monomial {n : ℕ} {r : R} : eval₂ f x (monomial n r) = (f r) * x^n :=
lift_nc_single _ _ _ _

@[simp] lemma eval₂_C : eval₂ f x (C a) = f a :=
(eval₂_monomial _ _).trans $ by rw [pow_zero, mul_one]

@[simp] lemma eval₂_X : eval₂ f x X = x :=
(eval₂_monomial _ _).trans $ by simp

-- Without an explicit universe level Lean uses `(max _ _)`
lemma eval₂_C_X {R : Type u} [semiring R] : eval₂ C (X : polynomial R) = add_monoid_hom.id _ :=
by { ext k x : 2, simp [C_mul_X_pow_eq_monomial] }

@[simp] lemma eval₂_X_pow {n : ℕ} : eval₂ f x (X^n) = x^n :=
begin
  rw X_pow_eq_monomial,
  convert eval₂_monomial f x,
  simp,
end

@[simp] lemma eval₂_add : eval₂ f x (p + q) = eval₂ f x p + eval₂ f x q :=
(eval₂ f x).map_add _ _

@[simp] lemma eval₂_one : eval₂ f x 1 = 1 := by rw [← C_1, eval₂_C, f.map_one]

lemma eval₂_bit0 : eval₂ f x (bit0 p) = bit0 (eval₂ f x p) :=
eval₂_add _ _

@[simp] lemma eval₂_bit1 : eval₂ f x (bit1 p) = bit1 (eval₂ f x p) :=
(eval₂ f x).map_bit1 (eval₂_one _ _) _

@[simp] lemma eval₂_smul (g : R →+* S) (p : polynomial R) (x : S) {s : R} :
  eval₂ g x (s • p) = g s • eval₂ g x p :=
lift_nc_smul _ _ _ _

@[simp] lemma eval₂_nat_cast (n : ℕ) : eval₂ f x n = n :=
(eval₂ f x).map_nat_cast (eval₂_one f x) _

@[simp] lemma eval₂_zero_left : eval₂ f 0 p = f (p.coeff 0) :=
begin
  rw [eval₂_eq_sum, coeff],
  refine trans (sum_eq_single 0 (λ n _ hn, _) _) _; [skip, by simp { contextual := tt}, by simp],
  simp [zero_pow (zero_lt_iff_ne_zero.2 hn)],
end

variables [semiring T]
lemma eval₂_sum (p : polynomial T) (g : ℕ → T → polynomial R) (x : S) :
  eval₂ f x (p.sum g) = p.sum (λ n a, eval₂ f x (g n a)) :=
(eval₂ f x).map_finsupp_sum _ _

lemma eval₂_finset_sum (s : finset ι) (g : ι → polynomial R) (x : S) :
  eval₂ f x (∑ i in s, g i) = ∑ i in s, eval₂ f x (g i) :=
(eval₂ f x).map_sum _ _

lemma eval₂_mul_noncomm (hf : ∀ k, commute (f $ q.coeff k) x) :
  eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q :=
lift_nc_mul _ _ p q $ λ k n hn, (hf k).pow_right n

@[simp] lemma eval₂_mul_X : eval₂ f x (p * X) = eval₂ f x p * x :=
begin
  refine trans (eval₂_mul_noncomm _ _ $ λ k, _) (by rw eval₂_X),
  rcases em (k = 1) with (rfl|hk),
  { simp },
  { simp [coeff_X_ne_one hk] }
end

@[simp] lemma eval₂_X_mul : eval₂ f x (X * p) = eval₂ f x p * x :=
by rw [X_mul, eval₂_mul_X]

lemma eval₂_list_prod_noncomm (ps : list (polynomial R))
  (hf : ∀ (p ∈ ps) k, commute (f $ coeff p k) x) :
  eval₂ f x ps.prod = (ps.map (polynomial.eval₂ f x)).prod :=
begin
  induction ps using list.reverse_rec_on with ps p ihp,
  { simp },
  { simp only [list.forall_mem_append, list.forall_mem_singleton] at hf,
    simp [eval₂_mul_noncomm _ _ hf.2, ihp hf.1] }
end

/-- `eval₂` as a `ring_hom` for noncommutative rings -/
def eval₂_ring_hom' (f : R →+* S) (x : S) (hf : ∀ a, commute (f a) x) : polynomial R →+* S :=
{ to_fun := eval₂ f x,
  map_add' := λ _ _, eval₂_add _ _,
  map_zero' := eval₂_zero _ _,
  map_mul' := λ p q, eval₂_mul_noncomm f x (λ k, hf $ coeff q k),
  map_one' := eval₂_one _ _ }

end

/-!
We next prove that eval₂ is multiplicative
as long as target ring is commutative
(even if the source ring is not).
-/
section eval₂
variables [comm_semiring S]
variables (f : R →+* S) (x : S)

/-- `eval₂` as a `ring_hom` -/
def eval₂_ring_hom (f : R →+* S) (x) : polynomial R →+* S :=
eval₂_ring_hom' f x $ λ y, commute.all _ _

@[simp] lemma coe_eval₂_ring_hom (f : R →+* S) (x) : ⇑(eval₂_ring_hom f x) = eval₂ f x := rfl

@[simp] lemma eval₂_mul : eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q :=
(eval₂_ring_hom f x).map_mul p q

lemma eval₂_mul_eq_zero_of_left (q : polynomial R) (hp : eval₂ f x p = 0) :
  eval₂ f x (p * q) = 0 :=
begin
  rw eval₂_mul f x,
  exact mul_eq_zero_of_left hp (eval₂ f x q)
end

lemma eval₂_mul_eq_zero_of_right (p : polynomial R) (hq : eval₂ f x q = 0) :
  eval₂ f x (p * q) = 0 :=
begin
  rw eval₂_mul f x,
  exact mul_eq_zero_of_right (eval₂ f x p) hq
end

lemma eval₂_pow (n : ℕ) : eval₂ f x (p ^ n) = eval₂ f x p ^ n := (eval₂_ring_hom _ _).map_pow _ _

lemma eval₂_eq_sum_range :
  eval₂ f x p = ∑ i in finset.range (p.nat_degree + 1), f (p.coeff i) * x^i :=
trans (congr_arg _ p.as_sum_range) (trans (eval₂_finset_sum f _ _ x) (congr_arg _ (by simp)))

end eval₂

section eval
variables {x : R}

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : R → polynomial R →+ R := eval₂ (ring_hom.id _)

lemma eval_eq_sum : eval x p = sum p (λ e a, a * x ^ e) := rfl

@[simp] lemma eval_C : eval x (C a) = a := eval₂_C _ _

@[simp] lemma eval_one : eval x 1 = 1 := eval₂_one _ _

@[simp] lemma eval_nat_cast {n : ℕ} : eval x n = n :=
(eval x).map_nat_cast eval_one n

@[simp] lemma eval_X : eval x X = x := eval₂_X _ _

@[simp] lemma eval_monomial {n a} : eval x (monomial n a) = a * x^n :=
eval₂_monomial _ _

@[simp] lemma eval_zero : eval x 0 = 0 :=  eval₂_zero _ _

@[simp] lemma eval_add : eval x (p + q) = eval x p + eval x q := eval₂_add _ _

@[simp] lemma eval_bit0 : eval x (bit0 p) = bit0 (eval x p) := eval₂_bit0 _ _

@[simp] lemma eval_bit1 : eval x (bit1 p) = bit1 (eval x p) := eval₂_bit1 _ _

@[simp] lemma eval_smul (p : polynomial R) (x : R) {s : R} :
  eval x (s • p) = s • eval x p :=
eval₂_smul _ _ _

lemma eval_sum [semiring S] (p : polynomial S) (f : ℕ → S → polynomial R) (x : R) :
  eval x (p.sum f) = p.sum (λ n a, eval x (f n a)) :=
eval₂_sum _ _ _ _

lemma eval_finset_sum (s : finset ι) (g : ι → polynomial R) (x : R) :
  eval x (∑ i in s, g i) = ∑ i in s, eval x (g i) := eval₂_finset_sum _ _ _ _

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : polynomial R) (a : R) : Prop := eval a p = 0

instance [decidable_eq R] : decidable (is_root p a) := (infer_instance : decidable (eval a p = 0))

@[simp] lemma is_root.def : is_root p a ↔ eval a p = 0 := iff.rfl

lemma coeff_zero_eq_eval_zero (p : polynomial R) :
  coeff p 0 = eval 0 p :=
(eval₂_zero_left $ ring_hom.id _).symm

lemma zero_is_root_of_coeff_zero_eq_zero {p : polynomial R} (hp : p.coeff 0 = 0) :
  is_root p 0 :=
by rwa coeff_zero_eq_eval_zero at hp

end eval

section comp

/-- The composition of polynomials as a polynomial. -/
def comp (p q : polynomial R) : polynomial R := eval₂ C q p

lemma comp_eq_sum_left : p.comp q = p.sum (λ e a, C a * q ^ e) :=
rfl

@[simp] lemma comp_X : p.comp X = p :=
add_monoid_hom.congr_fun (@eval₂_C_X R _) p

@[simp] lemma X_comp : X.comp p = p := eval₂_X _ _

@[simp] lemma comp_C : p.comp (C a) = C (eval a p) :=
by simp [comp, eval_eq_sum, eval₂_eq_sum, C.map_finsupp_sum]

@[simp] lemma C_comp : (C a).comp p = C a := eval₂_C _ _

@[simp] lemma comp_zero : p.comp 0 = C (eval 0 p) :=
by rw [← C_0, comp_C]

@[simp] lemma zero_comp : comp (0 : polynomial R) p = 0 :=
by rw [← C_0, C_comp]

@[simp] lemma comp_one : p.comp 1 = C (eval 1 p) :=
by rw [← C_1, comp_C]

@[simp] lemma one_comp : comp 1 p = 1 :=
by rw [← C_1, C_comp]

@[simp] lemma add_comp : (p + q).comp r = p.comp r + q.comp r := eval₂_add _ _

@[simp] lemma mul_comp {R : Type*} [comm_semiring R] (p q r : polynomial R) :
  (p * q).comp r = p.comp r * q.comp r := eval₂_mul _ _

@[simp] lemma bit0_comp : comp (bit0 p : polynomial R) q = bit0 (p.comp q) :=
eval₂_bit0 _ _

@[simp] lemma bit1_comp : comp (bit1 p : polynomial R) q = bit1 (p.comp q) :=
eval₂_bit1 _ _

lemma comp_assoc {R : Type*} [comm_semiring R] (φ ψ χ : polynomial R) :
  (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) :=
begin
  apply polynomial.induction_on φ;
  { intros, simp only [add_comp, mul_comp, C_comp, X_comp, pow_succ', ← mul_assoc, *] at * }
end

end comp

section map
variables [semiring S]
variables (f : R →+* S)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : polynomial R →+* polynomial S :=
eval₂_ring_hom' (C.comp f) X $ λ a, X_mul.symm

@[simp] lemma map_C : map f (C a) = C (f a) := eval₂_C _ _

@[simp] lemma map_X : map f X = X := eval₂_X _ _

@[simp] lemma map_monomial {n a} : map f (monomial n a) = monomial n (f a) :=
trans (eval₂_monomial (C.comp f) X) (C_mul_X_pow_eq_monomial _ _)

lemma map_zero : map f 0 = 0 := (map f).map_zero

lemma map_add : map f (p + q) = map f p + map f q := (map f).map_add _ _

lemma map_one : map f 1 = 1 := (map f).map_one

theorem map_nat_cast (n : ℕ) : map f n = n := (map f).map_nat_cast n

@[simp]
lemma coeff_map (n : ℕ) : coeff (map f p) n = f (coeff p n) :=
begin
  suffices : (lcoeff S n).to_add_monoid_hom.comp (map f : polynomial R →+ polynomial S) =
    (f : R →+ S).comp (lcoeff R n).to_add_monoid_hom, from add_monoid_hom.congr_fun this p,
  ext k x : 2,
  simp [coeff_monomial, apply_ite f]
end

lemma map_map [semiring T] (g : S →+* T) (p : polynomial R) : map g (map f p) = map (g.comp f) p :=
ext (by simp [coeff_map])

@[simp] lemma map_id : map (ring_hom.id _) p = p := ext $ by simp [coeff_map]

lemma eval_comp_map {x : S} : (eval x).comp (map f : polynomial R →+ polynomial S) = eval₂ f x :=
by { ext n y : 2, simp }

lemma eval₂_eq_eval_map {x : S} : eval₂ f x p = eval x (map f p) :=
add_monoid_hom.congr_fun (eval_comp_map f).symm p

lemma map_injective (hf : function.injective f): function.injective (map f) :=
λ p q h, ext $ λ m, hf $ by rw [← coeff_map f, ← coeff_map f, h]

variables {f}

lemma monic.map_eq_zero_iff (hp : p.monic) : map f p = 0 ↔ subsingleton S :=
begin
  split,
  { simp only [ext_iff, coeff_map, coeff_zero, ← subsingleton_iff_zero_eq_one],
    intro h,
    rw [← h (nat_degree p), ← leading_coeff, hp.leading_coeff, f.map_one] },
  { introI h,
    apply subsingleton.elim }
end

lemma monic.map_ne_zero (hp : p.monic) [nontrivial S] : map f p ≠ 0 :=
by rwa [ne.def, hp.map_eq_zero_iff, ← not_nontrivial_iff_subsingleton, not_not]

variables (f)

lemma map_list_prod (L : list (polynomial R)) : map f L.prod = (L.map $ map f).prod :=
(map f).map_list_prod L

lemma map_pow (n : ℕ) : map f (p ^ n) = map f p ^ n := (map f).map_pow p n

#check as_sum_range
lemma mem_map_range {p : polynomial S} :
  p ∈ set.range (map f) ↔ ∀ n, p.coeff n ∈ (set.range f) :=
begin
  split,
  { rintro ⟨p, rfl⟩ n, rw coeff_map, exact set.mem_range_self _ },
  { intro h, rw p.as_sum_range,
    apply is_add_submonoid.finset_sum_mem,
    intros i hi,
    rcases h i with ⟨c, hc⟩,
    use [C c * X^i],
    rw [map_mul, map_C, hc, map_pow, map_X] }
end

lemma eval₂_map [semiring T] (g : S →+* T) (x : T) :
  (p.map f).eval₂ g x = p.eval₂ (g.comp f) x :=
begin
  convert finsupp.sum_map_range_index _,
  { change map f p = map_range f _ p,
    ext,
    rw map_range_apply,
    exact coeff_map f a, },
  { exact f.map_zero, },
  { intro a, simp only [ring_hom.map_zero, zero_mul], },
end

lemma eval_map (x : S) : (p.map f).eval x = p.eval₂ f x :=
eval₂_map f (ring_hom.id _) x

end map

/-!
After having set up the basic theory of `eval₂`, `eval`, `comp`, and `map`,
we make `eval₂` irreducible.

Perhaps we can make the others irreducible too?
-/
attribute [irreducible] polynomial.eval₂

section hom_eval₂
-- TODO: Here we need commutativity in both `S` and `T`?
variables [comm_semiring S] [comm_semiring T]
variables (f : R →+* S) (g : S →+* T) (p)

lemma hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) :=
begin
  apply polynomial.induction_on p; clear p,
  { intros a, rw [eval₂_C, eval₂_C], refl, },
  { intros p q hp hq, simp only [hp, hq, eval₂_add, g.map_add] },
  { intros n a ih,
    simp only [eval₂_mul, eval₂_C, eval₂_X_pow, g.map_mul, g.map_pow],
    refl, }
end

end hom_eval₂


end semiring

section comm_semiring

section eval

variables [comm_semiring R] {p q : polynomial R} {x : R}

@[simp] lemma eval_mul : (p * q).eval x = p.eval x * q.eval x := eval₂_mul _ _

instance eval.is_semiring_hom : is_semiring_hom (eval x) := eval₂.is_semiring_hom _ _

@[simp] lemma eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n := eval₂_pow _ _ _

lemma eval₂_hom [comm_semiring S] (f : R →+* S) (x : R) :
  p.eval₂ f (f x) = f (p.eval x) :=
(ring_hom.comp_id f) ▸ (hom_eval₂ p (ring_hom.id R) f x).symm

lemma root_mul_left_of_is_root (p : polynomial R) {q : polynomial R} :
  is_root q a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, mul_zero]

lemma root_mul_right_of_is_root {p : polynomial R} (q : polynomial R) :
  is_root p a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, zero_mul]

/--
Polynomial evaluation commutes with finset.prod
-/
lemma eval_prod {ι : Type*} (s : finset ι) (p : ι → polynomial R) (x : R) :
  eval x (∏ j in s, p j) = ∏ j in s, eval x (p j) :=
begin
  classical,
  apply finset.induction_on s,
    { simp only [finset.prod_empty, eval_one] },
    { intros j s hj hpj,
      have h0 : ∏ i in insert j s, eval x (p i) = (eval x (p j)) * ∏ i in s, eval x (p i),
      { apply finset.prod_insert hj },
      rw [h0, ← hpj, finset.prod_insert hj, eval_mul] },
end

end eval

section map

variables [comm_semiring R] [comm_semiring S] (f : R →+* S)

lemma map_multiset_prod (m : multiset (polynomial R)) : m.prod.map f = (m.map $ map f).prod :=
eq.symm $ multiset.prod_hom _ (monoid_hom.of (map f))

lemma map_prod {ι : Type*} (g : ι → polynomial R) (s : finset ι) :
  (∏ i in s, g i).map f = ∏ i in s, (g i).map f :=
eq.symm $ prod_hom _ _

lemma map_sum {ι : Type*} (g : ι → polynomial R) (s : finset ι) :
  (∑ i in s, g i).map f = ∑ i in s, (g i).map f :=
eq.symm $ sum_hom _ _

lemma support_map_subset (p : polynomial R) : (map f p).support ⊆ p.support :=
begin
  intros x,
  simp only [mem_support_iff],
  contrapose!,
  change p.coeff x = 0 → (map f p).coeff x = 0,
  rw coeff_map,
  intro hx,
  rw hx,
  exact ring_hom.map_zero f,
end

lemma map_comp (p q : polynomial R) : map f (p.comp q) = (map f p).comp (map f q) :=
polynomial.induction_on p
  (by simp)
  (by simp {contextual := tt})
  (by simp [pow_succ', ← mul_assoc, polynomial.comp] {contextual := tt})

end map

end comm_semiring

section ring
variables [ring R] {p q r : polynomial R}

-- @[simp]
-- lemma C_eq_int_cast (n : ℤ) : C ↑n = (n : polynomial R) :=
-- (C : R →+* _).map_int_cast n

lemma C_neg : C (-a) = -C a := ring_hom.map_neg C a

lemma C_sub : C (a - b) = C a - C b := ring_hom.map_sub C a b

instance map.is_ring_hom {S} [ring S] (f : R →+* S) : is_ring_hom (map f) :=
by apply is_ring_hom.of_semiring

@[simp] lemma map_sub {S} [comm_ring S] (f : R →+* S) :
  (p - q).map f = p.map f - q.map f :=
is_ring_hom.map_sub _

@[simp] lemma map_neg {S} [comm_ring S] (f : R →+* S) :
  (-p).map f = -(p.map f) :=
is_ring_hom.map_neg _

@[simp] lemma eval_int_cast {n : ℤ} {x : R} : (n : polynomial R).eval x = n :=
by simp only [←C_eq_int_cast, eval_C]

@[simp] lemma eval₂_neg {S} [ring S] (f : R →+* S) {x : S} :
  (-p).eval₂ f x = -p.eval₂ f x :=
by rw [eq_neg_iff_add_eq_zero, ←eval₂_add, add_left_neg, eval₂_zero]

@[simp] lemma eval₂_sub {S} [ring S] (f : R →+* S) {x : S} :
  (p - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x :=
by rw [sub_eq_add_neg, eval₂_add, eval₂_neg, sub_eq_add_neg]

@[simp] lemma eval_neg (p : polynomial R) (x : R) : (-p).eval x = -p.eval x :=
eval₂_neg _

@[simp] lemma eval_sub (p q : polynomial R) (x : R) : (p - q).eval x = p.eval x - q.eval x :=
eval₂_sub _

lemma root_X_sub_C : is_root (X - C a) b ↔ a = b :=
by rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero_iff_eq, eq_comm]

@[simp] lemma neg_comp : (-p).comp q = -p.comp q := eval₂_neg _

@[simp] lemma sub_comp : (p - q).comp r = p.comp r - q.comp r := eval₂_sub _

end ring

section comm_ring
variables [comm_ring R] {p q : polynomial R}

instance eval₂.is_ring_hom {S} [comm_ring S]
  (f : R →+* S) {x : S} : is_ring_hom (eval₂ f x) :=
by apply is_ring_hom.of_semiring

instance eval.is_ring_hom {x : R} : is_ring_hom (eval x) := eval₂.is_ring_hom _

end comm_ring

end polynomial
