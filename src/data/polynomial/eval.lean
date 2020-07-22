/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.induction
import data.polynomial.degree.basic

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
def eval₂ (p : polynomial R) : S :=
p.sum (λ e a, f a * x ^ e)

@[simp] lemma eval₂_zero : (0 : polynomial R).eval₂ f x = 0 :=
finsupp.sum_zero_index

@[simp] lemma eval₂_C : (C a).eval₂ f x = f a :=
(sum_single_index $ by rw [f.map_zero, zero_mul]).trans $ by simp [pow_zero, mul_one]

@[simp] lemma eval₂_X : X.eval₂ f x = x :=
(sum_single_index $ by rw [f.map_zero, zero_mul]).trans $ by rw [f.map_one, one_mul, pow_one]

@[simp] lemma eval₂_monomial {n : ℕ} {r : R} : (monomial n r).eval₂ f x = (f r) * x^n :=
begin
  apply sum_single_index,
  simp,
end

@[simp] lemma eval₂_X_pow {n : ℕ} : (X^n).eval₂ f x = x^n :=
begin
  rw ←monomial_one_eq_X_pow,
  convert eval₂_monomial f x,
  simp,
end

@[simp] lemma eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x :=
finsupp.sum_add_index
  (λ _, by rw [f.map_zero, zero_mul])
  (λ _ _ _, by rw [f.map_add, add_mul])

@[simp] lemma eval₂_one : (1 : polynomial R).eval₂ f x = 1 :=
by rw [← C_1, eval₂_C, f.map_one]

@[simp] lemma eval₂_bit0 : (bit0 p).eval₂ f x = bit0 (p.eval₂ f x) :=
by rw [bit0, eval₂_add, bit0]

@[simp] lemma eval₂_bit1 : (bit1 p).eval₂ f x = bit1 (p.eval₂ f x) :=
by rw [bit1, eval₂_add, eval₂_bit0, eval₂_one, bit1]

@[simp] lemma eval₂_smul (g : R →+* S) (p : polynomial R) (x : S) {s : R} :
  eval₂ g x (s • p) = g s • eval₂ g x p :=
begin
  simp only [eval₂, sum_smul_index, forall_const, zero_mul, g.map_zero, g.map_mul, mul_assoc],
  -- Why doesn't `rw [←finsupp.mul_sum]` work?
  convert (@finsupp.mul_sum _ _ _ _ _ (g s) p (λ i a, (g a * x ^ i))).symm,
end

instance eval₂.is_add_monoid_hom : is_add_monoid_hom (eval₂ f x) :=
{ map_zero := eval₂_zero _ _, map_add := λ _ _, eval₂_add _ _ }


@[simp] lemma eval₂_nat_cast (n : ℕ) : (n : polynomial R).eval₂ f x = n :=
nat.rec_on n rfl $ λ n ih, by rw [n.cast_succ, eval₂_add, ih, eval₂_one, n.cast_succ]

variables [semiring T]
lemma eval₂_sum (p : polynomial T) (g : ℕ → T → polynomial R) (x : S) :
  (p.sum g).eval₂ f x = p.sum (λ n a, (g n a).eval₂ f x) :=
finsupp.sum_sum_index (by simp [is_add_monoid_hom.map_zero f])
  (by intros; simp [right_distrib, is_add_monoid_hom.map_add f])


lemma eval₂_finset_sum (s : finset ι) (g : ι → polynomial R) (x : S) :
  (∑ i in s, g i).eval₂ f x = ∑ i in s, (g i).eval₂ f x :=
begin
  classical,
  induction s using finset.induction with p hp s hs, simp,
  rw [sum_insert, eval₂_add, hs, sum_insert]; assumption,
end

end

/-!
We next prove that eval₂ is multiplicative
as long as target ring is commutative
(even if the source ring is not).
-/
section eval₂
variables [comm_semiring S]
variables (f : R →+* S) (x : S)

@[simp] lemma eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x :=
begin
  dunfold eval₂,
  rw [mul_def, finsupp.sum_mul _ p], simp only [finsupp.mul_sum _ q], rw [sum_sum_index],
  { apply sum_congr rfl, assume i hi, dsimp only, rw [sum_sum_index],
    { apply sum_congr rfl, assume j hj, dsimp only,
      rw [sum_single_index, f.map_mul, pow_add],
      { simp only [mul_assoc, mul_left_comm] },
      { rw [f.map_zero, zero_mul] } },
    { intro, rw [f.map_zero, zero_mul] },
    { intros, rw [f.map_add, add_mul] } },
  { intro, rw [f.map_zero, zero_mul] },
  { intros, rw [f.map_add, add_mul] }
end

instance eval₂.is_semiring_hom : is_semiring_hom (eval₂ f x) :=
⟨eval₂_zero _ _, eval₂_one _ _, λ _ _, eval₂_add _ _, λ _ _, eval₂_mul _ _⟩

/-- `eval₂` as a `ring_hom` -/
def eval₂_ring_hom (f : R →+* S) (x) : polynomial R →+* S :=
ring_hom.of (eval₂ f x)

@[simp] lemma coe_eval₂_ring_hom (f : R →+* S) (x) : ⇑(eval₂_ring_hom f x) = eval₂ f x := rfl

lemma eval₂_pow (n : ℕ) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n := (eval₂_ring_hom _ _).map_pow _ _

end eval₂

section eval
variables {x : R}

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : R → polynomial R → R := eval₂ (ring_hom.id _)

@[simp] lemma eval_C : (C a).eval x = a := eval₂_C _ _

@[simp] lemma eval_nat_cast {n : ℕ} : (n : polynomial R).eval x = n :=
by simp only [←C_eq_nat_cast, eval_C]

@[simp] lemma eval_X : X.eval x = x := eval₂_X _ _

@[simp] lemma eval_monomial {n a} : (monomial n a).eval x = a * x^n :=
eval₂_monomial _ _

@[simp] lemma eval_zero : (0 : polynomial R).eval x = 0 :=  eval₂_zero _ _

@[simp] lemma eval_add : (p + q).eval x = p.eval x + q.eval x := eval₂_add _ _

@[simp] lemma eval_one : (1 : polynomial R).eval x = 1 := eval₂_one _ _

@[simp] lemma eval_bit0 : (bit0 p).eval x = bit0 (p.eval x) := eval₂_bit0 _ _

@[simp] lemma eval_bit1 : (bit1 p).eval x = bit1 (p.eval x) := eval₂_bit1 _ _

@[simp] lemma eval_smul (p : polynomial R) (x : R) {s : R} :
  (s • p).eval x = s • p.eval x :=
eval₂_smul (ring_hom.id _) _ _

lemma eval_sum (p : polynomial R) (f : ℕ → R → polynomial R) (x : R) :
  (p.sum f).eval x = p.sum (λ n a, (f n a).eval x) :=
eval₂_sum _ _ _ _



/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : polynomial R) (a : R) : Prop := p.eval a = 0

instance [decidable_eq R] : decidable (is_root p a) := by unfold is_root; apply_instance

@[simp] lemma is_root.def : is_root p a ↔ p.eval a = 0 := iff.rfl

lemma coeff_zero_eq_eval_zero (p : polynomial R) :
  coeff p 0 = p.eval 0 :=
calc coeff p 0 = coeff p 0 * 0 ^ 0 : by simp
... = p.eval 0 : eq.symm $
  finset.sum_eq_single _ (λ b _ hb, by simp [zero_pow (nat.pos_of_ne_zero hb)]) (by simp)

lemma zero_is_root_of_coeff_zero_eq_zero {p : polynomial R} (hp : p.coeff 0 = 0) :
  is_root p 0 :=
by rwa coeff_zero_eq_eval_zero at hp

end eval

section comp

/-- The composition of polynomials as a polynomial. -/
def comp (p q : polynomial R) : polynomial R := p.eval₂ C q

@[simp] lemma comp_X : p.comp X = p :=
begin
  refine ext (λ n, _),
  rw [comp, eval₂],
  conv in (C _ * _) { rw ← single_eq_C_mul_X },
  congr,
  convert finsupp.sum_single _,
end

@[simp] lemma X_comp : X.comp p = p := eval₂_X _ _

@[simp] lemma comp_C : p.comp (C a) = C (p.eval a) :=
begin
  dsimp [comp, eval₂, eval, finsupp.sum],
  rw [← p.support.sum_hom (@C R _)],
  apply finset.sum_congr rfl; simp
end

@[simp] lemma C_comp : (C a).comp p = C a := eval₂_C _ _

@[simp] lemma comp_zero : p.comp (0 : polynomial R) = C (p.eval 0) :=
by rw [← C_0, comp_C]

@[simp] lemma zero_comp : comp (0 : polynomial R) p = 0 :=
by rw [← C_0, C_comp]

@[simp] lemma comp_one : p.comp 1 = C (p.eval 1) :=
by rw [← C_1, comp_C]

@[simp] lemma one_comp : comp (1 : polynomial R) p = 1 :=
by rw [← C_1, C_comp]

@[simp] lemma add_comp : (p + q).comp r = p.comp r + q.comp r := eval₂_add _ _

end comp

section map
variables [semiring S]
variables (f : R →+* S)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : polynomial R → polynomial S := eval₂ (C.comp f) X

instance is_semiring_hom_C_f : is_semiring_hom (C ∘ f) :=
is_semiring_hom.comp _ _

@[simp] lemma map_C : (C a).map f = C (f a) := eval₂_C _ _

@[simp] lemma map_X : X.map f = X := eval₂_X _ _

@[simp] lemma map_monomial {n a} : (monomial n a).map f = monomial n (f a) :=
begin
  dsimp only [map],
  rw [eval₂_monomial, single_eq_C_mul_X], refl,
end

@[simp] lemma map_zero : (0 : polynomial R).map f = 0 :=  eval₂_zero _ _

@[simp] lemma map_add : (p + q).map f = p.map f + q.map f := eval₂_add _ _

@[simp] lemma map_one : (1 : polynomial R).map f = 1 := eval₂_one _ _

@[simp] theorem map_nat_cast (n : ℕ) : (n : polynomial R).map f = n :=
nat.rec_on n rfl $ λ n ih, by rw [n.cast_succ, map_add, ih, map_one, n.cast_succ]

@[simp]
lemma coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) :=
begin
  rw [map, eval₂, coeff_sum],
  conv_rhs { rw [← sum_C_mul_X_eq p, coeff_sum, finsupp.sum,
    ← p.support.sum_hom f], },
  refine finset.sum_congr rfl (λ x hx, _),
  simp [function.comp, coeff_C_mul_X, is_semiring_hom.map_mul f],
  split_ifs; simp [is_semiring_hom.map_zero f],
end

lemma map_map [semiring T] (g : S →+* T)
  (p : polynomial R) : (p.map f).map g = p.map (g.comp f) :=
ext (by simp [coeff_map])

@[simp] lemma map_id : p.map (ring_hom.id _) = p := by simp [polynomial.ext_iff, coeff_map]

lemma eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp [hp, hq], },
  { intros n r, simp, }
end

lemma map_injective (hf : function.injective f): function.injective (map f) :=
λ p q h, ext $ λ m, hf $ by rw [← coeff_map f, ← coeff_map f, h]

open is_semiring_hom

-- If the rings were commutative, we could prove this just using `eval₂_mul`.
-- TODO this proof is just a hack job on the proof of `eval₂_mul`,
-- using that `X` is central. It should probably be golfed!
@[simp] lemma map_mul : (p * q).map f = p.map f * q.map f :=
begin
  dunfold map,
  dunfold eval₂,
  rw [mul_def, finsupp.sum_mul _ p], simp only [finsupp.mul_sum _ q], rw [sum_sum_index],
  { apply sum_congr rfl, assume i hi, dsimp only, rw [sum_sum_index],
    { apply sum_congr rfl, assume j hj, dsimp only,
      rw [sum_single_index, (C.comp f).map_mul, pow_add],
      { simp [←mul_assoc], conv_lhs { rw ←@X_pow_mul_assoc _ _ _ _ i }, },
      { simp, } },
    { intro, simp, },
    { intros, simp [add_mul], } },
  { intro, simp, },
  { intros, simp [add_mul], }
end

instance map.is_semiring_hom : is_semiring_hom (map f) :=
{ map_zero := eval₂_zero _ _,
  map_one := eval₂_one _ _,
  map_add := λ _ _, eval₂_add _ _,
  map_mul := λ _ _, map_mul f, }

@[simp] lemma map_pow (n : ℕ) : (p ^ n).map f = p.map f ^ n := is_semiring_hom.map_pow (map f) _ _

lemma mem_map_range {p : polynomial S} :
  p ∈ set.range (map f) ↔ ∀ n, p.coeff n ∈ (set.range f) :=
begin
  split,
  { rintro ⟨p, rfl⟩ n, rw coeff_map, exact set.mem_range_self _ },
  { intro h, rw p.as_sum,
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
polynomial.induction_on p
  (by simp)
  (by simp [f.map_add] {contextual := tt})
  (by simp [f.map_mul, eval_pow,
    f.map_pow, pow_succ', (mul_assoc _ _ _).symm] {contextual := tt})

lemma root_mul_left_of_is_root (p : polynomial R) {q : polynomial R} :
  is_root q a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, mul_zero]

lemma root_mul_right_of_is_root {p : polynomial R} (q : polynomial R) :
  is_root p a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, zero_mul]

end eval

end comm_semiring

section ring
variables [ring R] {p q : polynomial R}

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


end ring

section comm_ring
variables [comm_ring R] {p q : polynomial R}

instance eval₂.is_ring_hom {S} [comm_ring S]
  (f : R →+* S) {x : S} : is_ring_hom (eval₂ f x) :=
by apply is_ring_hom.of_semiring

instance eval.is_ring_hom {x : R} : is_ring_hom (eval x) := eval₂.is_ring_hom _

end comm_ring

end polynomial
