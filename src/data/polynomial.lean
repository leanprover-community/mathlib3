/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.monoid_algebra
import algebra.gcd_domain
import ring_theory.euclidean_domain
import ring_theory.multiplicity
import data.finset.nat_antidiagonal
import tactic.ring_exp

/-!
# Theory of univariate polynomials

Polynomials are represented as `add_monoid_algebra R ℕ`, where `R` is a commutative semiring.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

local attribute [instance, priority 10] is_semiring_hom.comp is_ring_hom.comp

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
def polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℕ

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v w x y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z}
  {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

instance : inhabited (polynomial R) := finsupp.inhabited
instance : semiring (polynomial R) := add_monoid_algebra.semiring
instance : has_scalar R (polynomial R) := add_monoid_algebra.has_scalar
instance : semimodule R (polynomial R) := add_monoid_algebra.semimodule

/-- The coercion turning a `polynomial` into the function which reports the coefficient of a given
monomial `X^n` -/
def coeff_coe_to_fun : has_coe_to_fun (polynomial R) :=
finsupp.has_coe_to_fun

local attribute [instance] coeff_coe_to_fun

@[simp] lemma support_zero : (0 : polynomial R).support = ∅ := rfl

/-- `monomial s a` is the monomial `a * X^s` -/
@[reducible]
def monomial (n : ℕ) (a : R) : polynomial R := finsupp.single n a

@[simp] lemma monomial_zero_right (n : ℕ) :
  monomial n (0 : R) = 0 :=
by simp [monomial]

lemma monomial_add (n : ℕ) (r s : R) :
  monomial n (r + s) = monomial n r + monomial n s :=
by simp [monomial]

/-- `X` is the polynomial variable (aka indeterminant). -/
def X : polynomial R := monomial 1 1

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
lemma X_mul : X * p = p * X :=
begin
  ext,
  simp [X, monomial, add_monoid_algebra.mul_apply, sum_single_index, add_comm],
end

lemma X_pow_mul {n : ℕ} : X^n * p = p * X^n :=
begin
  induction n with n ih,
  { simp, },
  { conv_lhs { rw pow_succ', },
    rw [mul_assoc, X_mul, ←mul_assoc, ih, mul_assoc, ←pow_succ'], }
end

lemma X_pow_mul_assoc {n : ℕ} : (p * X^n) * q = (p * q) * X^n :=
by rw [mul_assoc, X_pow_mul, ←mul_assoc]

/-- coeff p n is the coefficient of X^n in p -/
def coeff (p : polynomial R) := p.to_fun

@[simp] lemma coeff_mk (s) (f) (h) : coeff (finsupp.mk s f h : polynomial R) = f := rfl

instance [has_repr R] : has_repr (polynomial R) :=
⟨λ p, if p = 0 then "0"
  else (p.support.sort (≤)).foldr
    (λ n a, a ++ (if a = "" then "" else " + ") ++
      if n = 0
        then "C (" ++ repr (coeff p n) ++ ")"
        else if n = 1
          then if (coeff p n) = 1 then "X" else "C (" ++ repr (coeff p n) ++ ") * X"
          else if (coeff p n) = 1 then "X ^ " ++ repr n
            else "C (" ++ repr (coeff p n) ++ ") * X ^ " ++ repr n) ""⟩

theorem ext_iff {p q : polynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
⟨λ h n, h ▸ rfl, finsupp.ext⟩

@[ext] lemma ext {p q : polynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
(@ext_iff _ _ p q).2

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : polynomial R) : with_bot ℕ := p.support.sup some

lemma degree_lt_wf : well_founded (λp q : polynomial R, degree p < degree q) :=
inv_image.wf degree (with_bot.well_founded_lt nat.lt_wf)

instance : has_well_founded (polynomial R) := ⟨_, degree_lt_wf⟩

/-- `nat_degree p` forces `degree p` to ℕ, by defining nat_degree 0 = 0. -/
def nat_degree (p : polynomial R) : ℕ := (degree p).get_or_else 0

section coeff

lemma apply_eq_coeff : p n = coeff p n := rfl

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : polynomial R) n = 0 := rfl

-- FIXME rename `coeff_monomial`?
lemma coeff_single : coeff (single n a) m = if n = m then a else 0 :=
by { dsimp [single, finsupp.single], congr }

@[simp] lemma coeff_one_zero : coeff (1 : polynomial R) 0 = 1 :=
coeff_single

@[simp]
lemma coeff_add (p q : polynomial R) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := rfl

instance coeff.is_add_monoid_hom {n : ℕ} : is_add_monoid_hom (λ p : polynomial R, p.coeff n) :=
{ map_add  := λ p q, coeff_add p q n,
  map_zero := coeff_zero _ }

@[simp] lemma coeff_X_one : coeff (X : polynomial R) 1 = 1 := coeff_single

@[simp] lemma coeff_X_zero : coeff (X : polynomial R) 0 = 0 := coeff_single

lemma coeff_X : coeff (X : polynomial R) n = if 1 = n then 1 else 0 := coeff_single

lemma coeff_sum [semiring S] (n : ℕ) (f : ℕ → R → polynomial S) :
  coeff (p.sum f) n = p.sum (λ a b, coeff (f a b) n) := finsupp.sum_apply

@[simp] lemma coeff_smul (p : polynomial R) (r : R) (n : ℕ) :
coeff (r • p) n = r * coeff p n := finsupp.smul_apply

@[simp, priority 990]
lemma coeff_one (n : ℕ) : coeff (1 : polynomial R) n = if 0 = n then 1 else 0 :=
coeff_single

lemma coeff_mul (p q : polynomial R) (n : ℕ) :
  coeff (p * q) n = ∑ x in nat.antidiagonal n, coeff p x.1 * coeff q x.2 :=
have hite : ∀ a : ℕ × ℕ, ite (a.1 + a.2 = n) (coeff p (a.fst) * coeff q (a.snd)) 0 ≠ 0
    → a.1 + a.2 = n, from λ a ha, by_contradiction
  (λ h, absurd (eq.refl (0 : R)) (by rwa if_neg h at ha)),
calc coeff (p * q) n = ∑ a in p.support, ∑ b in q.support,
    ite (a + b = n) (coeff p a * coeff q b) 0 :
  by simp only [mul_def, coeff_sum, coeff_single]; refl
... = ∑ v in p.support.product q.support, ite (v.1 + v.2 = n) (coeff p v.1 * coeff q v.2) 0 :
  by rw sum_product
... = ∑ x in nat.antidiagonal n, coeff p x.1 * coeff q x.2 :
begin
  refine sum_bij_ne_zero (λ x _ _, x)
  (λ x _ hx, nat.mem_antidiagonal.2 (hite x hx)) (λ _ _ _ _ _ _ h, h)
  (λ x h₁ h₂, ⟨x, _, _, rfl⟩) _,
  { rw [mem_product, mem_support_iff, mem_support_iff],
    exact ne_zero_and_ne_zero_of_mul h₂ },
  { rw nat.mem_antidiagonal at h₁, rwa [if_pos h₁] },
  { intros x h hx, rw [if_pos (hite x hx)] }
end

@[simp] lemma mul_coeff_zero (p q : polynomial R) : coeff (p * q) 0 = coeff p 0 * coeff q 0 :=
by simp [coeff_mul]

lemma monomial_one_eq_X_pow : ∀{n}, monomial n (1 : R) = X^n
| 0     := rfl
| (n+1) :=
  calc monomial (n + 1) (1 : R) = monomial n 1 * X : by rw [X, single_mul_single, mul_one]
    ... = X^n * X : by rw [monomial_one_eq_X_pow]
    ... = X^(n+1) : by simp only [pow_add, pow_one]

lemma monomial_eq_smul_X {n} : monomial n (a : R) = a • X^n :=
begin
  calc monomial n a = monomial n (a * 1) : by simp
    ... = a • monomial n 1 : (smul_single' _ _ _).symm
    ... = a • X^n  : by rw monomial_one_eq_X_pow
end

@[simp] lemma coeff_X_pow (k n : ℕ) :
  coeff (X^k : polynomial R) n = if n = k then 1 else 0 :=
by rw [← monomial_one_eq_X_pow]; simp [monomial, single, eq_comm, coeff]; congr

theorem coeff_mul_X_pow (p : polynomial R) (n d : ℕ) :
  coeff (p * polynomial.X ^ n) (d + n) = coeff p d :=
begin
  rw [coeff_mul, sum_eq_single (d,n), coeff_X_pow, if_pos rfl, mul_one],
  { rintros ⟨i,j⟩ h1 h2, rw [coeff_X_pow, if_neg, mul_zero], rintro rfl, apply h2,
    rw [nat.mem_antidiagonal, add_right_cancel_iff] at h1, subst h1 },
  { exact λ h1, (h1 (nat.mem_antidiagonal.2 rfl)).elim }
end

@[simp] theorem coeff_mul_X (p : polynomial R) (n : ℕ) :
  coeff (p * X) (n + 1) = coeff p n :=
by simpa only [pow_one] using coeff_mul_X_pow p 1 n

theorem mul_X_pow_eq_zero {p : polynomial R} {n : ℕ}
  (H : p * X ^ n = 0) : p = 0 :=
ext $ λ k, (coeff_mul_X_pow p n k).symm.trans $ ext_iff.1 H (k+n)

end coeff

section C
/-- `C a` is the constant polynomial `a`. -/
def C : R →+* polynomial R := add_monoid_algebra.algebra_map' (ring_hom.id R)

@[simp] lemma monomial_zero_left (a : R) : monomial 0 a = C a := rfl

lemma single_eq_C_mul_X : ∀{n}, monomial n a = C a * X^n
| 0     := (mul_one _).symm
| (n+1) :=
  calc monomial (n + 1) a = monomial n a * X : by rw [X, single_mul_single, mul_one]
    ... = (C a * X^n) * X : by rw [single_eq_C_mul_X]
    ... = C a * X^(n+1) : by simp only [pow_add, mul_assoc, pow_one]

lemma sum_C_mul_X_eq (p : polynomial R) : p.sum (λn a, C a * X^n) = p :=
eq.trans (sum_congr rfl $ assume n hn, single_eq_C_mul_X.symm) (finsupp.sum_single _)

lemma sum_monomial_eq (p : polynomial R) : p.sum (λn a, monomial n a) = p :=
by simp only [single_eq_C_mul_X, sum_C_mul_X_eq]

@[elab_as_eliminator] protected lemma induction_on {M : polynomial R → Prop} (p : polynomial R)
  (h_C : ∀a, M (C a))
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (C a * X^n) → M (C a * X^(n+1))) :
  M p :=
have ∀{n:ℕ} {a}, M (C a * X^n),
begin
  assume n a,
  induction n with n ih,
  { simp only [pow_zero, mul_one, h_C] },
  { exact h_monomial _ _ ih }
end,
finsupp.induction p
  (suffices M (C 0), by { convert this, exact single_zero.symm, },
    h_C 0)
  (assume n a p _ _ hp, suffices M (C a * X^n + p), by { convert this, exact single_eq_C_mul_X },
    h_add _ _ this hp)

/--
To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_eliminator] protected lemma induction_on' {M : polynomial R → Prop} (p : polynomial R)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (monomial n a)) :
  M p :=
polynomial.induction_on p (h_monomial 0) h_add
(λ n a h, begin rw ←single_eq_C_mul_X at ⊢, exact h_monomial _ _, end)

lemma C_0 : C (0 : R) = 0 := single_zero

lemma C_1 : C (1 : R) = 1 := rfl

lemma C_mul : C (a * b) = C a * C b := C.map_mul a b

lemma C_add : C (a + b) = C a + C b := C.map_add a b

instance C.is_semiring_hom : is_semiring_hom (C : R → polynomial R) :=
C.is_semiring_hom

lemma C_pow : C (a ^ n) = C a ^ n := C.map_pow a n

@[simp]
lemma C_eq_nat_cast (n : ℕ) : C (n : R) = (n : polynomial R) :=
C.map_nat_cast n

@[simp]
lemma sum_C_index {a} {β} [add_comm_monoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a :=
sum_single_index h

end C

section coeff

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
by { convert coeff_single using 2, simp [eq_comm], }

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_single

lemma coeff_C_mul_X (x : R) (k n : ℕ) :
  coeff (C x * X^k : polynomial R) n = if n = k then x else 0 :=
by rw [← single_eq_C_mul_X]; simp [monomial, single, eq_comm, coeff]; congr

@[simp] lemma coeff_C_mul (p : polynomial R) : coeff (C a * p) n = a * coeff p n :=
begin
  conv in (a * _) { rw [← @sum_single _ _ _ p, coeff_sum] },
  rw [mul_def, ←monomial_zero_left, sum_single_index],
  { simp [coeff_single, finsupp.mul_sum, coeff_sum],
    apply sum_congr rfl,
    assume i hi, by_cases i = n; simp [h] },
  { simp [finsupp.sum] }
end

@[simp] lemma coeff_mul_C (p : polynomial R) (n : ℕ) (a : R) :
  coeff (p * C a) n = coeff p n * a :=
begin
  conv_rhs { rw [← @finsupp.sum_single _ _ _ p, coeff_sum] },
  rw [mul_def, ←monomial_zero_left], simp_rw [sum_single_index],
  { simp [coeff_single, finsupp.sum_mul, coeff_sum],
    apply sum_congr rfl,
    assume i hi, by_cases i = n; simp [h], },
end

theorem coeff_mul_monomial (p : polynomial R) (n d : ℕ) (r : R) :
  coeff (p * monomial n r) (d + n) = coeff p d * r :=
by rw [single_eq_C_mul_X, ←X_pow_mul, ←mul_assoc, coeff_mul_C, coeff_mul_X_pow]

theorem coeff_monomial_mul (p : polynomial R) (n d : ℕ) (r : R) :
  coeff (monomial n r * p) (d + n) = r * coeff p d :=
by rw [single_eq_C_mul_X, mul_assoc, coeff_C_mul, X_pow_mul, coeff_mul_X_pow]

-- This can already be proved by `simp`.
theorem coeff_mul_monomial_zero (p : polynomial R) (d : ℕ) (r : R) :
  coeff (p * monomial 0 r) d = coeff p d * r :=
coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.
theorem coeff_monomial_zero_mul (p : polynomial R) (d : ℕ) (r : R) :
  coeff (monomial 0 r * p) d = r * coeff p d :=
coeff_monomial_mul p 0 d r

end coeff

section C

lemma C_mul' (a : R) (f : polynomial R) : C a * f = a • f :=
ext $ λ n, coeff_C_mul f

lemma C_inj : C a = C b ↔ a = b :=
⟨λ h, coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

end C

section eval₂
variables [semiring S]

section
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

end

end eval₂

section eval
variable {x : R}

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

def comp (p q : polynomial R) : polynomial R := p.eval₂ C q


@[simp] lemma comp_X : p.comp X = p :=
begin
  refine ext (λ n, _),
  rw [comp, eval₂],
  conv in (C _ * _) { rw ← single_eq_C_mul_X },
  rw finsupp.sum_single
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

end semiring

section ring
variables [ring R]

instance : ring (polynomial R) := add_monoid_algebra.ring

end ring

section comm_semiring
variables [comm_semiring R] {p q r : polynomial R}

local attribute [instance] coeff_coe_to_fun

instance : comm_semiring (polynomial R) := add_monoid_algebra.comm_semiring

section
variables [semiring A] [algebra R A]

/-- Note that this instance also provides `algebra R (polynomial R)`. -/
instance algebra_of_algebra : algebra R (polynomial A) := add_monoid_algebra.algebra

lemma algebra_map_apply (r : R) :
  algebra_map R (polynomial A) r = C (algebra_map R A r) :=
rfl

end

section eval
variable {x : R}

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

section comp

lemma eval₂_comp [comm_semiring S] (f : R →+* S) {x : S} :
  (p.comp q).eval₂ f x = p.eval₂ f (q.eval₂ f x) :=
show (p.sum (λ e a, C a * q ^ e)).eval₂ f x = p.eval₂ f (eval₂ f x q),
by simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_sum]; refl

lemma eval_comp : (p.comp q).eval a = p.eval (q.eval a) := eval₂_comp _

instance : is_semiring_hom (λ q : polynomial R, q.comp p) :=
by unfold comp; apply_instance

@[simp] lemma mul_comp : (p * q).comp r = p.comp r * q.comp r := eval₂_mul _ _

end comp

end comm_semiring

section semiring

variables [semiring R] {p : polynomial R} [semiring S] {q : polynomial S}

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leading_coeff (p : polynomial R) : R := coeff p (nat_degree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def monic (p : polynomial R) := leading_coeff p = (1 : R)

lemma monic.def : monic p ↔ leading_coeff p = 1 := iff.rfl

instance monic.decidable [decidable_eq R] : decidable (monic p) :=
by unfold monic; apply_instance

@[simp] lemma monic.leading_coeff {p : polynomial R} (hp : p.monic) :
  leading_coeff p = 1 := hp

@[simp] lemma degree_zero : degree (0 : polynomial R) = ⊥ := rfl

@[simp] lemma nat_degree_zero : nat_degree (0 : polynomial R) = 0 := rfl

lemma degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
⟨λ h, by rw [degree, ← max_eq_sup_with_bot] at h;
  exact support_eq_empty.1 (max_eq_none.1 h),
λ h, h.symm ▸ rfl⟩

lemma degree_eq_nat_degree (hp : p ≠ 0) : degree p = (nat_degree p : with_bot ℕ) :=
let ⟨n, hn⟩ :=
  classical.not_forall.1 (mt option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp)) in
have hn : degree p = some n := not_not.1 hn,
by rw [nat_degree, hn]; refl

lemma degree_eq_iff_nat_degree_eq {p : polynomial R} {n : ℕ} (hp : p ≠ 0) :
  p.degree = n ↔ p.nat_degree = n :=
by rw [degree_eq_nat_degree hp, with_bot.coe_eq_coe]

lemma degree_eq_iff_nat_degree_eq_of_pos {p : polynomial R} {n : ℕ} (hn : n > 0) :
  p.degree = n ↔ p.nat_degree = n :=
begin
  split,
  { intro H, rwa ← degree_eq_iff_nat_degree_eq, rintro rfl,
    rw degree_zero at H, exact option.no_confusion H },
  { intro H, rwa degree_eq_iff_nat_degree_eq, rintro rfl,
    rw nat_degree_zero at H, rw H at hn, exact lt_irrefl _ hn }
end

lemma nat_degree_eq_of_degree_eq_some {p : polynomial R} {n : ℕ}
  (h : degree p = n) : nat_degree p = n :=
have hp0 : p ≠ 0, from λ hp0, by rw hp0 at h; exact option.no_confusion h,
option.some_inj.1 $ show (nat_degree p : with_bot ℕ) = n,
  by rwa [← degree_eq_nat_degree hp0]

@[simp] lemma degree_le_nat_degree : degree p ≤ nat_degree p :=
begin
  by_cases hp : p = 0, { rw hp, exact bot_le },
  rw [degree_eq_nat_degree hp],
  exact le_refl _
end

lemma nat_degree_eq_of_degree_eq {q : polynomial S}
  (h : degree p = degree q) : nat_degree p = nat_degree q :=
by unfold nat_degree; rw h

lemma le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : with_bot ℕ) ≤ degree p :=
show @has_le.le (with_bot ℕ) _ (some n : with_bot ℕ) (p.support.sup some : with_bot ℕ),
from finset.le_sup (finsupp.mem_support_iff.2 h)

lemma le_nat_degree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ nat_degree p :=
begin
  rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree],
  exact le_degree_of_ne_zero h,
  { assume h, subst h, exact h rfl }
end

lemma degree_le_degree (h : coeff q (nat_degree p) ≠ 0) : degree p ≤ degree q :=
begin
  by_cases hp : p = 0,
  { rw hp, exact bot_le },
  { rw degree_eq_nat_degree hp, exact le_degree_of_ne_zero h }
end

lemma degree_ne_of_nat_degree_ne {n : ℕ} :
  p.nat_degree ≠ n → degree p ≠ n :=
@option.cases_on _ (λ d, d.get_or_else 0 ≠ n → d ≠ n) p.degree
  (λ _ h, option.no_confusion h)
  (λ n' h, mt option.some_inj.mp h)

@[simp] lemma degree_C (ha : a ≠ 0) : degree (C a) = (0 : with_bot ℕ) :=
show sup (ite (a = 0) ∅ {0}) some = 0, by rw if_neg ha; refl

lemma degree_C_le : degree (C a) ≤ (0 : with_bot ℕ) :=
by by_cases h : a = 0; [rw [h, C_0], rw [degree_C h]]; [exact bot_le, exact le_refl _]

lemma degree_one_le : degree (1 : polynomial R) ≤ (0 : with_bot ℕ) :=
by rw [← C_1]; exact degree_C_le

@[simp] lemma nat_degree_C (a : R) : nat_degree (C a) = 0 :=
begin
  by_cases ha : a = 0,
  { have : C a = 0, { rw [ha, C_0] },
    rw [nat_degree, degree_eq_bot.2 this],
    refl },
  { rw [nat_degree, degree_C ha], refl }
end

@[simp] lemma nat_degree_one : nat_degree (1 : polynomial R) = 0 := nat_degree_C 1

@[simp] lemma nat_degree_nat_cast (n : ℕ) : nat_degree (n : polynomial R) = 0 :=
by simp only [←C_eq_nat_cast, nat_degree_C]

@[simp] lemma degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (C a * X ^ n) = n :=
by rw [← single_eq_C_mul_X, degree, support_single_ne_zero ha]; refl

lemma degree_monomial_le (n : ℕ) (a : R) : degree (C a * X ^ n) ≤ n :=
if h : a = 0 then by rw [h, C_0, zero_mul]; exact bot_le else le_of_eq (degree_monomial n h)

lemma coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

lemma coeff_eq_zero_of_nat_degree_lt {p : polynomial R} {n : ℕ} (h : p.nat_degree < n) :
  p.coeff n = 0 :=
begin
  apply coeff_eq_zero_of_degree_lt,
  by_cases hp : p = 0,
  { subst hp, exact with_bot.bot_lt_coe n },
  { rwa [degree_eq_nat_degree hp, with_bot.coe_lt_coe] }
end

@[simp] lemma coeff_nat_degree_succ_eq_zero {p : polynomial R} : p.coeff (p.nat_degree + 1) = 0 :=
coeff_eq_zero_of_nat_degree_lt (lt_add_one _)

-- TODO find a home (this file)
@[simp] lemma finset_sum_coeff (s : finset ι) (f : ι → polynomial R) (n : ℕ) :
  coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
(s.sum_hom (λ q : polynomial R, q.coeff n)).symm

-- We need the explicit `decidable` argument here because an exotic one shows up in a moment!
lemma ite_le_nat_degree_coeff (p : polynomial R) (n : ℕ) (I : decidable (n < 1 + nat_degree p)) :
  @ite (n < 1 + nat_degree p) I _ (coeff p n) 0 = coeff p n :=
begin
  split_ifs,
  { refl },
  { exact (coeff_eq_zero_of_nat_degree_lt (not_le.1 (λ w, h (nat.lt_one_add_iff.2 w)))).symm, }
end

lemma as_sum (p : polynomial R) :
  p = ∑ i in range (p.nat_degree + 1), C (p.coeff i) * X^i :=
begin
  ext n,
  simp only [add_comm, coeff_X_pow, coeff_C_mul, finset.mem_range,
    finset.sum_mul_boole, finset_sum_coeff, ite_le_nat_degree_coeff],
end

lemma monic.as_sum {p : polynomial R} (hp : p.monic) :
  p = X^(p.nat_degree) + (∑ i in finset.range p.nat_degree, C (p.coeff i) * X^i) :=
begin
  conv_lhs { rw [p.as_sum, finset.sum_range_succ] },
  suffices : C (p.coeff p.nat_degree) = 1,
  { rw [this, one_mul] },
  exact congr_arg C hp
end

lemma coeff_ne_zero_of_eq_degree {p : polynomial R} {n : ℕ} (hn : degree p = n) :
  coeff p n ≠ 0 :=
λ h, mem_support_iff.mp (mem_of_max hn) h

end semiring

section semiring
variables [semiring R] [add_comm_monoid S]

/--
We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.nat_degree < n`.
-/
lemma sum_over_range' (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0)
  (n : ℕ) (w : p.nat_degree < n) :
  p.sum f = ∑ (a : ℕ) in range n, f a (coeff p a) :=
begin
  rw finsupp.sum,
  apply finset.sum_bij_ne_zero (λ n _ _, n),
  { intros k h₁ h₂, simp only [mem_range],
    calc k ≤ p.nat_degree : _
       ... < n : w,
    rw finsupp.mem_support_iff at h₁,
    exact le_nat_degree_of_ne_zero h₁, },
  { intros, assumption },
  { intros b hb hb',
    refine ⟨b, _, hb', rfl⟩,
    rw finsupp.mem_support_iff,
    contrapose! hb',
    convert h b, },
  { intros, refl }
end

/--
We can reexpress a sum over `p.support` as a sum over `range (p.nat_degree + 1)`.
-/
-- See also `as_sum`.
lemma sum_over_range (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
  p.sum f = ∑ (a : ℕ) in range (p.nat_degree + 1), f a (coeff p a) :=
sum_over_range' p h (p.nat_degree + 1) (lt_add_one _)

end semiring

section semiring

variables [semiring R] {p q : polynomial R}

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

end map

section degree

lemma coeff_nat_degree_eq_zero_of_degree_lt (h : degree p < degree q) :
  coeff p (nat_degree q) = 0 :=
coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_nat_degree)

lemma ne_zero_of_degree_gt {n : with_bot ℕ} (h : n < degree p) : p ≠ 0 :=
mt degree_eq_bot.2 (ne.symm (ne_of_lt (lt_of_le_of_lt bot_le h)))

lemma eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) :=
begin
  refine ext (λ n, _),
  cases n,
  { simp },
  { have : degree p < ↑(nat.succ n) := lt_of_le_of_lt h (with_bot.some_lt_some.2 (nat.succ_pos _)),
    rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt this] }
end

lemma eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
eq_C_of_degree_le_zero (h ▸ le_refl _)

lemma degree_le_zero_iff : degree p ≤ 0 ↔ p = C (coeff p 0) :=
⟨eq_C_of_degree_le_zero, λ h, h.symm ▸ degree_C_le⟩

lemma degree_add_le (p q : polynomial R) : degree (p + q) ≤ max (degree p) (degree q) :=
calc degree (p + q) = ((p + q).support).sup some : rfl
  ... ≤ (p.support ∪ q.support).sup some : by convert sup_mono support_add
  ... = p.support.sup some ⊔ q.support.sup some : by convert sup_union
  ... = _ : with_bot.sup_eq_max _ _

@[simp] lemma leading_coeff_zero : leading_coeff (0 : polynomial R) = 0 := rfl

@[simp] lemma leading_coeff_eq_zero : leading_coeff p = 0 ↔ p = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_max (degree_eq_nat_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma leading_coeff_eq_zero_iff_deg_eq_bot : leading_coeff p = 0 ↔ degree p = ⊥ :=
by rw [leading_coeff_eq_zero, degree_eq_bot]

lemma degree_add_eq_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q :=
le_antisymm (max_eq_right_of_lt h ▸ degree_add_le _ _) $ degree_le_degree $
  begin
    rw [coeff_add, coeff_nat_degree_eq_zero_of_degree_lt h, zero_add],
    exact mt leading_coeff_eq_zero.1 (ne_zero_of_degree_gt h)
  end

lemma degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p :=
add_comm (C a) p ▸ degree_add_eq_of_degree_lt $ lt_of_le_of_lt degree_C_le hp

lemma degree_add_eq_of_leading_coeff_add_ne_zero (h : leading_coeff p + leading_coeff q ≠ 0) :
  degree (p + q) = max p.degree q.degree :=
le_antisymm (degree_add_le _ _) $
  match lt_trichotomy (degree p) (degree q) with
  | or.inl hlt :=
    by rw [degree_add_eq_of_degree_lt hlt, max_eq_right_of_lt hlt]; exact le_refl _
  | or.inr (or.inl heq) :=
    le_of_not_gt $
      assume hlt : max (degree p) (degree q) > degree (p + q),
      h $ show leading_coeff p + leading_coeff q = 0,
      begin
        rw [heq, max_self] at hlt,
        rw [leading_coeff, leading_coeff, nat_degree_eq_of_degree_eq heq, ← coeff_add],
        exact coeff_nat_degree_eq_zero_of_degree_lt hlt
      end
  | or.inr (or.inr hlt) :=
    by rw [add_comm, degree_add_eq_of_degree_lt hlt, max_eq_left_of_lt hlt]; exact le_refl _
  end

lemma degree_erase_le (p : polynomial R) (n : ℕ) : degree (p.erase n) ≤ degree p :=
by convert sup_mono (erase_subset _ _)

lemma degree_erase_lt (hp : p ≠ 0) : degree (p.erase (nat_degree p)) < degree p :=
lt_of_le_of_ne (degree_erase_le _ _) $
  (degree_eq_nat_degree hp).symm ▸ (by convert λ h, not_mem_erase _ _ (mem_of_max h))

lemma degree_sum_le (s : finset ι) (f : ι → polynomial R) :
  degree (∑ i in s, f i) ≤ s.sup (λ b, degree (f b)) :=
finset.induction_on s (by simp only [sum_empty, sup_empty, degree_zero, le_refl]) $
  assume a s has ih,
  calc degree (∑ i in insert a s, f i) ≤ max (degree (f a)) (degree (∑ i in s, f i)) :
    by rw sum_insert has; exact degree_add_le _ _
  ... ≤ _ : by rw [sup_insert, with_bot.sup_eq_max]; exact max_le_max (le_refl _) ih

lemma degree_mul_le (p q : polynomial R) : degree (p * q) ≤ degree p + degree q :=
calc degree (p * q) ≤ (p.support).sup (λi, degree (sum q (λj a, C (coeff p i * a) * X ^ (i + j)))) :
    by simp only [single_eq_C_mul_X.symm]; exact degree_sum_le _ _
  ... ≤ p.support.sup (λi, q.support.sup (λj, degree (C (coeff p i * coeff q j) * X ^ (i + j)))) :
    finset.sup_mono_fun (assume i hi,  degree_sum_le _ _)
  ... ≤ degree p + degree q :
    begin
      refine finset.sup_le (λ a ha, finset.sup_le (λ b hb, le_trans (degree_monomial_le _ _) _)),
      rw [with_bot.coe_add],
      rw mem_support_iff at ha hb,
      exact add_le_add (le_degree_of_ne_zero ha) (le_degree_of_ne_zero hb)
    end

lemma degree_pow_le (p : polynomial R) : ∀ n, degree (p ^ n) ≤ n •ℕ (degree p)
| 0     := by rw [pow_zero, zero_nsmul]; exact degree_one_le
| (n+1) := calc degree (p ^ (n + 1)) ≤ degree p + degree (p ^ n) :
    by rw pow_succ; exact degree_mul_le _ _
  ... ≤ _ : by rw succ_nsmul; exact add_le_add (le_refl _) (degree_pow_le _)

@[simp] lemma leading_coeff_monomial (a : R) (n : ℕ) : leading_coeff (C a * X ^ n) = a :=
begin
  by_cases ha : a = 0,
  { simp only [ha, C_0, zero_mul, leading_coeff_zero] },
  { rw [leading_coeff, nat_degree, degree_monomial _ ha, ← single_eq_C_mul_X],
    exact @finsupp.single_eq_same _ _ _ n a }
end

@[simp] lemma leading_coeff_C (a : R) : leading_coeff (C a) = a :=
suffices leading_coeff (C a * X^0) = a, by rwa [pow_zero, mul_one] at this,
leading_coeff_monomial a 0

@[simp] lemma leading_coeff_X : leading_coeff (X : polynomial R) = 1 :=
suffices leading_coeff (C (1:R) * X^1) = 1, by rwa [C_1, pow_one, one_mul] at this,
leading_coeff_monomial 1 1

@[simp] lemma monic_X : monic (X : polynomial R) := leading_coeff_X

@[simp] lemma leading_coeff_one : leading_coeff (1 : polynomial R) = 1 :=
suffices leading_coeff (C (1:R) * X^0) = 1, by rwa [C_1, pow_zero, mul_one] at this,
leading_coeff_monomial 1 0

@[simp] lemma monic_one : monic (1 : polynomial R) := leading_coeff_C _

lemma monic.ne_zero_of_zero_ne_one (h : (0:R) ≠ 1) {p : polynomial R} (hp : p.monic) :
  p ≠ 0 :=
by { contrapose! h, rwa [h] at hp }

lemma monic.ne_zero {R : Type*} [semiring R] [nonzero R] {p : polynomial R} (hp : p.monic) :
  p ≠ 0 :=
hp.ne_zero_of_zero_ne_one zero_ne_one

lemma leading_coeff_add_of_degree_lt (h : degree p < degree q) :
  leading_coeff (p + q) = leading_coeff q :=
have coeff p (nat_degree q) = 0, from coeff_nat_degree_eq_zero_of_degree_lt h,
by simp only [leading_coeff, nat_degree_eq_of_degree_eq (degree_add_eq_of_degree_lt h),
  this, coeff_add, zero_add]

lemma leading_coeff_add_of_degree_eq (h : degree p = degree q)
  (hlc : leading_coeff p + leading_coeff q ≠ 0) :
  leading_coeff (p + q) = leading_coeff p + leading_coeff q :=
have nat_degree (p + q) = nat_degree p,
  by apply nat_degree_eq_of_degree_eq;
    rw [degree_add_eq_of_leading_coeff_add_ne_zero hlc, h, max_self],
by simp only [leading_coeff, this, nat_degree_eq_of_degree_eq h, coeff_add]

@[simp] lemma coeff_mul_degree_add_degree (p q : polynomial R) :
  coeff (p * q) (nat_degree p + nat_degree q) = leading_coeff p * leading_coeff q :=
calc coeff (p * q) (nat_degree p + nat_degree q) =
    ∑ x in nat.antidiagonal (nat_degree p + nat_degree q),
    coeff p x.1 * coeff q x.2 : coeff_mul _ _ _
... = coeff p (nat_degree p) * coeff q (nat_degree q) :
  begin
    refine finset.sum_eq_single (nat_degree p, nat_degree q) _ _,
    { rintro ⟨i,j⟩ h₁ h₂, rw nat.mem_antidiagonal at h₁,
      by_cases H : nat_degree p < i,
      { rw [coeff_eq_zero_of_degree_lt
          (lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 H)), zero_mul] },
      { rw not_lt_iff_eq_or_lt at H, cases H,
        { subst H, rw add_left_cancel_iff at h₁, dsimp at h₁, subst h₁, exfalso, exact h₂ rfl },
        { suffices : nat_degree q < j,
          { rw [coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 this)), mul_zero] },
          { by_contra H', rw not_lt at H',
            exact ne_of_lt (nat.lt_of_lt_of_le
              (nat.add_lt_add_right H j) (nat.add_le_add_left H' _)) h₁ } } } },
    { intro H, exfalso, apply H, rw nat.mem_antidiagonal }
  end

lemma degree_mul_eq' (h : leading_coeff p * leading_coeff q ≠ 0) :
  degree (p * q) = degree p + degree q :=
have hp : p ≠ 0 := by refine mt _ h; exact λ hp, by rw [hp, leading_coeff_zero, zero_mul],
have hq : q ≠ 0 := by refine mt _ h; exact λ hq, by rw [hq, leading_coeff_zero, mul_zero],
le_antisymm (degree_mul_le _ _)
begin
  rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq],
  refine le_degree_of_ne_zero _,
  rwa coeff_mul_degree_add_degree
end

lemma nat_degree_mul_eq' (h : leading_coeff p * leading_coeff q ≠ 0) :
  nat_degree (p * q) = nat_degree p + nat_degree q :=
have hp : p ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, h $ by rw [h₁, zero_mul]),
have hq : q ≠ 0 := mt leading_coeff_eq_zero.2 (λ h₁, h $ by rw [h₁, mul_zero]),
have hpq : p * q ≠ 0 := λ hpq, by rw [← coeff_mul_degree_add_degree, hpq, coeff_zero] at h;
  exact h rfl,
option.some_inj.1 (show (nat_degree (p * q) : with_bot ℕ) = nat_degree p + nat_degree q,
  by rw [← degree_eq_nat_degree hpq, degree_mul_eq' h, degree_eq_nat_degree hp,
    degree_eq_nat_degree hq])

lemma leading_coeff_mul' (h : leading_coeff p * leading_coeff q ≠ 0) :
  leading_coeff (p * q) = leading_coeff p * leading_coeff q :=
begin
  unfold leading_coeff,
  rw [nat_degree_mul_eq' h, coeff_mul_degree_add_degree],
  refl
end

lemma leading_coeff_pow' : leading_coeff p ^ n ≠ 0 →
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
nat.rec_on n (by simp) $
λ n ih h,
have h₁ : leading_coeff p ^ n ≠ 0 :=
  λ h₁, h $ by rw [pow_succ, h₁, mul_zero],
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← ih h₁] at h,
by rw [pow_succ, pow_succ, leading_coeff_mul' h₂, ih h₁]

lemma degree_pow_eq' : ∀ {n}, leading_coeff p ^ n ≠ 0 →
  degree (p ^ n) = n •ℕ (degree p)
| 0     := λ h, by rw [pow_zero, ← C_1] at *;
  rw [degree_C h, zero_nsmul]
| (n+1) := λ h,
have h₁ : leading_coeff p ^ n ≠ 0 := λ h₁, h $
  by rw [pow_succ, h₁, mul_zero],
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← leading_coeff_pow' h₁] at h,
by rw [pow_succ, degree_mul_eq' h₂, succ_nsmul, degree_pow_eq' h₁]

lemma nat_degree_pow_eq' {n : ℕ} (h : leading_coeff p ^ n ≠ 0) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0 then
  if hn0 : n = 0 then by simp *
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else
have hpn : p ^ n ≠ 0, from λ hpn0,  have h1 : _ := h,
  by rw [← leading_coeff_pow' h1, hpn0, leading_coeff_zero] at h;
  exact h rfl,
option.some_inj.1 $ show (nat_degree (p ^ n) : with_bot ℕ) = (n * nat_degree p : ℕ),
  by rw [← degree_eq_nat_degree hpn, degree_pow_eq' h, degree_eq_nat_degree hp0,
    ← with_bot.coe_nsmul]; simp

@[simp] lemma leading_coeff_X_pow : ∀ n : ℕ, leading_coeff ((X : polynomial R) ^ n) = 1
| 0 := by simp
| (n+1) :=
if h10 : (1 : R) = 0
then by rw [pow_succ, ← one_mul X, ← C_1, h10]; simp
else
have h : leading_coeff (X : polynomial R) * leading_coeff (X ^ n) ≠ 0,
  by rw [leading_coeff_X, leading_coeff_X_pow n, one_mul];
    exact h10,
by rw [pow_succ, leading_coeff_mul' h, leading_coeff_X, leading_coeff_X_pow, one_mul]

lemma nat_degree_comp_le : nat_degree (p.comp q) ≤ nat_degree p * nat_degree q :=
if h0 : p.comp q = 0 then by rw [h0, nat_degree_zero]; exact nat.zero_le _
else with_bot.coe_le_coe.1 $
  calc ↑(nat_degree (p.comp q)) = degree (p.comp q) : (degree_eq_nat_degree h0).symm
  ... ≤ _ : degree_sum_le _ _
  ... ≤ _ : sup_le (λ n hn,
    calc degree (C (coeff p n) * q ^ n)
        ≤ degree (C (coeff p n)) + degree (q ^ n) : degree_mul_le _ _
    ... ≤ nat_degree (C (coeff p n)) + n •ℕ (degree q) :
      add_le_add degree_le_nat_degree (degree_pow_le _ _)
    ... ≤ nat_degree (C (coeff p n)) + n •ℕ (nat_degree q) :
      add_le_add_left' (nsmul_le_nsmul_of_le_right (@degree_le_nat_degree _ _ q) n)
    ... = (n * nat_degree q : ℕ) :
     by rw [nat_degree_C, with_bot.coe_zero, zero_add, ← with_bot.coe_nsmul,
       nsmul_eq_mul]; simp
    ... ≤ (nat_degree p * nat_degree q : ℕ) : with_bot.coe_le_coe.2 $
      mul_le_mul_of_nonneg_right
        (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.1 hn))
        (nat.zero_le _))

lemma degree_map_le [semiring S] (f : R →+* S) :
  degree (p.map f) ≤ degree p :=
if h : p.map f = 0 then by simp [h]
else begin
  rw [degree_eq_nat_degree h],
  refine le_degree_of_ne_zero (mt (congr_arg f) _),
  rw [← coeff_map f, is_semiring_hom.map_zero f],
  exact mt leading_coeff_eq_zero.1 h
end

lemma subsingleton_of_monic_zero (h : monic (0 : polynomial R)) :
  (∀ p q : polynomial R, p = q) ∧ (∀ a b : R, a = b) :=
by rw [monic.def, leading_coeff_zero] at h;
  exact ⟨λ p q, by rw [← mul_one p, ← mul_one q, ← C_1, ← h, C_0, mul_zero, mul_zero],
    λ a b, by rw [← mul_one a, ← mul_one b, ← h, mul_zero, mul_zero]⟩

lemma degree_map_eq_of_leading_coeff_ne_zero [semiring S] (f : R →+* S)
  (hf : f (leading_coeff p) ≠ 0) : degree (p.map f) = degree p :=
le_antisymm (degree_map_le f) $
  have hp0 : p ≠ 0, from λ hp0, by simpa [hp0, is_semiring_hom.map_zero f] using hf,
  begin
    rw [degree_eq_nat_degree hp0],
    refine le_degree_of_ne_zero _,
    rw [coeff_map], exact hf
  end

lemma monic_map [semiring S] (f : R →+* S) (hp : monic p) : monic (p.map f) :=
if h : (0 : S) = 1 then
  by haveI := subsingleton_of_zero_eq_one h;
  exact subsingleton.elim _ _
else
have f (leading_coeff p) ≠ 0,
  by rwa [show _ = _, from hp, is_semiring_hom.map_one f, ne.def, eq_comm],
by erw [monic, leading_coeff, nat_degree_eq_of_degree_eq
    (degree_map_eq_of_leading_coeff_ne_zero f this), coeff_map,
    ← leading_coeff, show _ = _, from hp, is_semiring_hom.map_one f]

lemma zero_le_degree_iff {p : polynomial R} : 0 ≤ degree p ↔ p ≠ 0 :=
by rw [ne.def, ← degree_eq_bot];
  cases degree p; exact dec_trivial

@[simp] lemma coeff_mul_X_zero (p : polynomial R) : coeff (p * X) 0 = 0 :=
by rw [coeff_mul, nat.antidiagonal_zero];
simp only [polynomial.coeff_X_zero, finset.sum_singleton, mul_zero]

lemma degree_nonneg_iff_ne_zero : 0 ≤ degree p ↔ p ≠ 0 :=
⟨λ h0p hp0, absurd h0p (by rw [hp0, degree_zero]; exact dec_trivial),
  λ hp0, le_of_not_gt (λ h, by simp [gt, degree_eq_bot, *] at *)⟩

lemma nat_degree_eq_zero_iff_degree_le_zero : p.nat_degree = 0 ↔ p.degree ≤ 0 :=
if hp0 : p = 0 then by simp [hp0]
else by rw [degree_eq_nat_degree hp0, ← with_bot.coe_zero, with_bot.coe_le_coe,
  nat.le_zero_iff]

end degree

section map
variables [semiring S]
variables (f : R →+* S)

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

variables [comm_semiring R] {p q : polynomial R}

section is_unit

lemma is_unit_C {x : R} : is_unit (C x) ↔ is_unit x :=
begin
  rw [is_unit_iff_dvd_one, is_unit_iff_dvd_one],
  split,
  { rintros ⟨g, hg⟩,
    replace hg := congr_arg (eval 0) hg,
    rw [eval_one, eval_mul, eval_C] at hg,
    exact ⟨g.eval 0, hg⟩ },
  { rintros ⟨y, hy⟩,
    exact ⟨C y, by rw [← C_mul, ← hy, C_1]⟩ }
end

lemma eq_one_of_is_unit_of_monic (hm : monic p) (hpu : is_unit p) : p = 1 :=
have degree p ≤ 0,
  from calc degree p ≤ degree (1 : polynomial R) :
    let ⟨u, hu⟩ := is_unit_iff_dvd_one.1 hpu in
    if hu0 : u = 0
    then begin
        rw [hu0, mul_zero] at hu,
        rw [← mul_one p, hu, mul_zero],
        simp
      end
    else have p.leading_coeff * u.leading_coeff ≠ 0,
        by rw [hm.leading_coeff, one_mul, ne.def, leading_coeff_eq_zero];
          exact hu0,
      by rw [hu, degree_mul_eq' this];
        exact le_add_of_nonneg_right' (degree_nonneg_iff_ne_zero.2 hu0)
  ... ≤ 0 : degree_one_le,
by rw [eq_C_of_degree_le_zero this, ← nat_degree_eq_zero_iff_degree_le_zero.2 this,
    ← leading_coeff, hm.leading_coeff, C_1]

end is_unit

end comm_semiring

instance subsingleton [subsingleton R] [semiring R] : subsingleton (polynomial R) :=
⟨λ _ _, ext (λ _, subsingleton.elim _ _)⟩

section semiring

variables [semiring R] {p q r : polynomial R}

lemma ne_zero_of_monic_of_zero_ne_one (hp : monic p) (h : (0 : R) ≠ 1) :
  p ≠ 0 := mt (congr_arg leading_coeff) $ by rw [monic.def.1 hp, leading_coeff_zero]; cc

lemma eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) :
  p = C (p.coeff 1) * X + C (p.coeff 0) :=
ext (λ n, nat.cases_on n (by simp)
  (λ n, nat.cases_on n (by simp [coeff_C])
    (λ m, have degree p < m.succ.succ, from lt_of_le_of_lt h dec_trivial,
      by simp [coeff_eq_zero_of_degree_lt this, coeff_C, nat.succ_ne_zero, coeff_X,
        nat.succ_inj', @eq_comm ℕ 0])))

lemma eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
  p = C (p.leading_coeff) * X + C (p.coeff 0) :=
(eq_X_add_C_of_degree_le_one (show degree p ≤ 1, from h ▸ le_refl _)).trans
  (by simp [leading_coeff, nat_degree_eq_of_degree_eq_some h])

theorem degree_C_mul_X_pow_le (r : R) (n : ℕ) : degree (C r * X^n) ≤ n :=
begin
  rw [← single_eq_C_mul_X],
  refine finset.sup_le (λ b hb, _),
  rw list.eq_of_mem_singleton (finsupp.support_single_subset hb),
  exact le_refl _
end

theorem degree_X_pow_le (n : ℕ) : degree (X^n : polynomial R) ≤ n :=
by simpa only [C_1, one_mul] using degree_C_mul_X_pow_le (1:R) n

theorem degree_X_le : degree (X : polynomial R) ≤ 1 :=
by simpa only [C_1, one_mul, pow_one] using degree_C_mul_X_pow_le (1:R) 1

section injective
open function
variables [semiring S] {f : R →+* S} (hf : function.injective f)
include hf

lemma degree_map_eq_of_injective (p : polynomial R) : degree (p.map f) = degree p :=
if h : p = 0 then by simp [h]
else degree_map_eq_of_leading_coeff_ne_zero _
  (by rw [← is_semiring_hom.map_zero f]; exact mt hf.eq_iff.1
    (mt leading_coeff_eq_zero.1 h))

lemma degree_map' (p : polynomial R) :
  degree (p.map f) = degree p :=
p.degree_map_eq_of_injective hf

lemma nat_degree_map' (p : polynomial R) :
  nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map' hf p)

lemma map_injective : injective (map f) :=
λ p q h, ext $ λ m, hf $
begin
  rw ext_iff at h,
  specialize h m,
  rw [coeff_map f, coeff_map f] at h,
  exact h
end

lemma leading_coeff_of_injective (p : polynomial R) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  delta leading_coeff,
  rw [coeff_map f, nat_degree_map' hf p]
end

lemma monic_of_injective {p : polynomial R} (hp : (p.map f).monic) : p.monic :=
begin
  apply hf,
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, is_semiring_hom.map_one f]
end

end injective

theorem monic_of_degree_le (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : monic p :=
decidable.by_cases
  (assume H : degree p < n, eq_of_zero_eq_one
    (H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
  (assume H : ¬degree p < n,
    by rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_le H1).resolve_left H])

theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) + p) :=
have H1 : degree p < n+1, from lt_of_le_of_lt H (with_bot.coe_lt_coe.2 (nat.lt_succ_self n)),
monic_of_degree_le (n+1)
  (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H1)))
  (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zero])

theorem monic_X_add_C (x : R) : monic (X + C x) :=
pow_one (X : polynomial R) ▸ monic_X_pow_add degree_C_le

theorem degree_le_iff_coeff_zero (f : polynomial R) (n : with_bot ℕ) :
  degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_bot ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_bot ℕ) ≤ n)) Hm,
  H1 $ (finsupp.mem_support_to_fun f m).2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  (finsupp.mem_support_to_fun f b).1 Hb $ H b $ lt_of_not_ge Hn⟩

theorem nat_degree_le_of_degree_le {p : polynomial R} {n : ℕ}
  (H : degree p ≤ n) : nat_degree p ≤ n :=
show option.get_or_else (degree p) 0 ≤ n, from match degree p, H with
| none,     H := zero_le _
| (some d), H := with_bot.coe_le_coe.1 H
end

lemma nat_degree_mul_le {p q : polynomial R} : nat_degree (p * q) ≤ nat_degree p + nat_degree q :=
begin
  apply nat_degree_le_of_degree_le,
  apply le_trans (degree_mul_le p q),
  rw with_bot.coe_add,
  refine add_le_add _ _; apply degree_le_nat_degree,
end

theorem leading_coeff_mul_X_pow {p : polynomial R} {n : ℕ} :
  leading_coeff (p * X ^ n) = leading_coeff p :=
decidable.by_cases
  (λ H : leading_coeff p = 0, by rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
  (λ H : leading_coeff p ≠ 0,
    by rw [leading_coeff_mul', leading_coeff_X_pow, mul_one];
      rwa [leading_coeff_X_pow, mul_one])

lemma monic_mul (hp : monic p) (hq : monic q) : monic (p * q) :=
if h0 : (0 : R) = 1 then by haveI := subsingleton_of_zero_eq_one h0;
  exact subsingleton.elim _ _
else
  have leading_coeff p * leading_coeff q ≠ 0, by simp [monic.def.1 hp, monic.def.1 hq, ne.symm h0],
  by rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mul]

lemma monic_pow (hp : monic p) : ∀ (n : ℕ), monic (p ^ n)
| 0     := monic_one
| (n+1) := monic_mul hp (monic_pow n)

end semiring

section comm_semiring

variables [comm_semiring R] {p q : polynomial R}

lemma multiplicity_finite_of_degree_pos_of_monic (hp : (0 : with_bot ℕ) < degree p)
  (hmp : monic p) (hq : q ≠ 0) : multiplicity.finite p q :=
have zn0 : (0 : R) ≠ 1, from λ h, by haveI := subsingleton_of_zero_eq_one h;
  exact hq (subsingleton.elim _ _),
⟨nat_degree q, λ ⟨r, hr⟩,
  have hp0 : p ≠ 0, from λ hp0, by simp [hp0] at hp; contradiction,
  have hr0 : r ≠ 0, from λ hr0, by simp * at *,
  have hpn1 : leading_coeff p ^ (nat_degree q + 1) = 1,
    by simp [show _ = _, from hmp],
  have hpn0' : leading_coeff p ^ (nat_degree q + 1) ≠ 0,
    from hpn1.symm ▸ zn0.symm,
  have hpnr0 : leading_coeff (p ^ (nat_degree q + 1)) * leading_coeff r ≠ 0,
    by simp only [leading_coeff_pow' hpn0', leading_coeff_eq_zero, hpn1,
      one_pow, one_mul, ne.def, hr0]; simp,
  have hpn0 : p ^ (nat_degree q + 1) ≠ 0,
    from mt leading_coeff_eq_zero.2 $
      by rw [leading_coeff_pow' hpn0', show _ = _, from hmp, one_pow]; exact zn0.symm,
  have hnp : 0 < nat_degree p,
    by rw [← with_bot.coe_lt_coe, ← degree_eq_nat_degree hp0];
    exact hp,
  begin
    have := congr_arg nat_degree hr,
    rw [nat_degree_mul_eq' hpnr0,  nat_degree_pow_eq' hpn0', add_mul, add_assoc] at this,
    exact ne_of_lt (lt_add_of_le_of_pos (le_mul_of_one_le_right' (nat.zero_le _) hnp)
      (add_pos_of_pos_of_nonneg (by rwa one_mul) (nat.zero_le _))) this
  end⟩

end comm_semiring

section nonzero_semiring
variables [semiring R] [nonzero R] {p q : polynomial R}

instance : nonzero (polynomial R) :=
{ zero_ne_one := λ (h : (0 : polynomial R) = 1), zero_ne_one $
    calc (0 : R) = eval 0 0 : eval_zero.symm
      ... = eval 0 1 : congr_arg _ h
      ... = 1 : eval_C }

@[simp] lemma degree_one : degree (1 : polynomial R) = (0 : with_bot ℕ) :=
degree_C (show (1 : R) ≠ 0, from zero_ne_one.symm)

@[simp] lemma degree_X : degree (X : polynomial R) = 1 :=
begin
  unfold X degree monomial single finsupp.support,
  rw if_neg (one_ne_zero : (1 : R) ≠ 0),
  refl
end

lemma X_ne_zero : (X : polynomial R) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

@[simp] lemma degree_X_pow : ∀ (n : ℕ), degree ((X : polynomial R) ^ n) = n
| 0 := by simp only [pow_zero, degree_one]; refl
| (n+1) :=
have h : leading_coeff (X : polynomial R) * leading_coeff (X ^ n) ≠ 0,
  by rw [leading_coeff_X, leading_coeff_X_pow n, one_mul];
    exact zero_ne_one.symm,
by rw [pow_succ, degree_mul_eq' h, degree_X, degree_X_pow, add_comm]; refl

@[simp] lemma not_monic_zero : ¬monic (0 : polynomial R) :=
by simpa only [monic, leading_coeff_zero] using (zero_ne_one : (0 : R) ≠ 1)

lemma ne_zero_of_monic (h : monic p) : p ≠ 0 :=
λ h₁, @not_monic_zero R _ _ (h₁ ▸ h)

end nonzero_semiring

section semiring
variables [semiring R] {p q : polynomial R}

/-- `dix_X p` return a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def div_X (p : polynomial R) : polynomial R :=
{ to_fun := λ n, p.coeff (n + 1),
  support := ⟨(p.support.filter (> 0)).1.map (λ n, n - 1),
    multiset.nodup_map_on begin
        simp only [finset.mem_def.symm, finset.mem_erase, finset.mem_filter],
        assume x hx y hy hxy,
        rwa [← @add_right_cancel_iff _ _ 1, nat.sub_add_cancel hx.2,
          nat.sub_add_cancel hy.2] at hxy
      end
      (p.support.filter (> 0)).2⟩,
  mem_support_to_fun := λ n,
    suffices (∃ (a : ℕ), (¬coeff p a = 0 ∧ a > 0) ∧ a - 1 = n) ↔
      ¬coeff p (n + 1) = 0,
    by simpa [finset.mem_def.symm, apply_eq_coeff],
    ⟨λ ⟨a, ha⟩, by rw [← ha.2, nat.sub_add_cancel ha.1.2]; exact ha.1.1,
      λ h, ⟨n + 1, ⟨h, nat.succ_pos _⟩, nat.succ_sub_one _⟩⟩ }

lemma div_X_mul_X_add (p : polynomial R) : div_X p * X + C (p.coeff 0) = p :=
ext $ λ n,
  nat.cases_on n
   (by simp)
   (by simp [coeff_C, nat.succ_ne_zero, coeff_mul_X, div_X])

@[simp] lemma div_X_C (a : R) : div_X (C a) = 0 :=
ext $ λ n, by cases n; simp [div_X, coeff_C]; simp [coeff]

lemma div_X_eq_zero_iff : div_X p = 0 ↔ p = C (p.coeff 0) :=
⟨λ h, by simpa [eq_comm, h] using div_X_mul_X_add p,
  λ h, by rw [h, div_X_C]⟩

lemma div_X_add : div_X (p + q) = div_X p + div_X q :=
ext $ by simp [div_X]

theorem nonzero.of_polynomial_ne (h : p ≠ q) : nonzero R :=
{ zero_ne_one := λ h01 : 0 = 1, h $
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] }

lemma degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * X).degree :=
by haveI := nonzero.of_polynomial_ne hp; exact
have leading_coeff p * leading_coeff X ≠ 0, by simpa,
by erw [degree_mul_eq' this, degree_eq_nat_degree hp,
    degree_X, ← with_bot.coe_one, ← with_bot.coe_add, with_bot.coe_lt_coe];
  exact nat.lt_succ_self _

lemma degree_div_X_lt (hp0 : p ≠ 0) : (div_X p).degree < p.degree :=
by haveI := nonzero.of_polynomial_ne hp0; exact
calc (div_X p).degree < (div_X p * X + C (p.coeff 0)).degree :
  if h : degree p ≤ 0
  then begin
      have h' : C (p.coeff 0) ≠ 0, by rwa [← eq_C_of_degree_le_zero h],
      rw [eq_C_of_degree_le_zero h, div_X_C, degree_zero, zero_mul, zero_add],
      exact lt_of_le_of_ne bot_le (ne.symm (mt degree_eq_bot.1 $
        by simp [h'])),
    end
  else
    have hXp0 : div_X p ≠ 0,
      by simpa [div_X_eq_zero_iff, -not_le, degree_le_zero_iff] using h,
    have leading_coeff (div_X p) * leading_coeff X ≠ 0, by simpa,
    have degree (C (p.coeff 0)) < degree (div_X p * X),
      from calc degree (C (p.coeff 0)) ≤ 0 : degree_C_le
         ... < 1 : dec_trivial
         ... = degree (X : polynomial R) : degree_X.symm
         ... ≤ degree (div_X p * X) :
          by rw [← zero_add (degree X), degree_mul_eq' this];
            exact add_le_add
              (by rw [zero_le_degree_iff, ne.def, div_X_eq_zero_iff];
                exact λ h0, h (h0.symm ▸ degree_C_le))
              (le_refl _),
    by rw [add_comm, degree_add_eq_of_degree_lt this];
      exact degree_lt_degree_mul_X hXp0
... = p.degree : by rw div_X_mul_X_add

@[elab_as_eliminator] noncomputable def rec_on_horner
  {M : polynomial R → Sort*} : Π (p : polynomial R),
  M 0 →
  (Π p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a)) →
  (Π p, p ≠ 0 → M p → M (p * X)) →
  M p
| p := λ M0 MC MX,
if hp : p = 0 then eq.rec_on hp.symm M0
else
have wf : degree (div_X p) < degree p,
  from degree_div_X_lt hp,
by rw [← div_X_mul_X_add p] at *;
  exact
  if hcp0 : coeff p 0 = 0
  then by rw [hcp0, C_0, add_zero];
    exact MX _ (λ h : div_X p = 0, by simpa [h, hcp0] using hp)
      (rec_on_horner _ M0 MC MX)
  else MC _ _ (coeff_mul_X_zero _) hcp0 (if hpX0 : div_X p = 0
    then show M (div_X p * X), by rw [hpX0, zero_mul]; exact M0
    else MX (div_X p) hpX0 (rec_on_horner _ M0 MC MX))
using_well_founded {dec_tac := tactic.assumption}

@[elab_as_eliminator] lemma degree_pos_induction_on
  {P : polynomial R → Prop} (p : polynomial R) (h0 : 0 < degree p)
  (hC : ∀ {a}, a ≠ 0 → P (C a * X))
  (hX : ∀ {p}, 0 < degree p → P p → P (p * X))
  (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + C a)) : P p :=
rec_on_horner p
  (λ h, by rw degree_zero at h; exact absurd h dec_trivial)
  (λ p a _ _ ih h0,
    have 0 < degree p,
      from lt_of_not_ge (λ h, (not_lt_of_ge degree_C_le) $
        by rwa [eq_C_of_degree_le_zero h, ← C_add] at h0),
    hadd this (ih this))
  (λ p _ ih h0',
    if h0 : 0 < degree p
    then hX h0 (ih h0)
    else by rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at *;
      exact hC (λ h : coeff p 0 = 0,
        by simpa [h, nat.not_lt_zero] using h0'))
  h0

end semiring

section semiring
variables [semiring R]

variable (R)
def lcoeff (n : ℕ) : polynomial R →ₗ[R] R :=
{ to_fun := λ f, coeff f n,
  map_add' := λ f g, coeff_add f g n,
  map_smul' := λ r p, coeff_smul p r n }
variable {R}

@[simp] lemma lcoeff_apply (n : ℕ) (f : polynomial R) : lcoeff R n f = coeff f n := rfl

lemma degree_pos_of_root {p : polynomial R} (hp : p ≠ 0) (h : is_root p a) : 0 < degree p :=
lt_of_not_ge $ λ hlt, begin
  have := eq_C_of_degree_le_zero hlt,
  rw [is_root, this, eval_C] at h,
  exact hp (finsupp.ext (λ n, show coeff p n = 0, from
    nat.cases_on n h (λ _, coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hlt
      (with_bot.coe_lt_coe.2 (nat.succ_pos _)))))),
end

lemma eq_C_of_nat_degree_le_zero {p : polynomial R} (h : nat_degree p ≤ 0) : p = C (coeff p 0) :=
begin
  refine polynomial.ext (λ n, _),
  cases n,
  { simp },
  { have : nat_degree p < nat.succ n := lt_of_le_of_lt h (nat.succ_pos _),
    rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_nat_degree_lt this] }
end

lemma nat_degree_pos_iff_degree_pos {p : polynomial R} :
  0 < nat_degree p ↔ 0 < degree p :=
⟨ λ h, ((degree_eq_iff_nat_degree_eq_of_pos h).mpr rfl).symm ▸ (with_bot.some_lt_some.mpr h),
  by { unfold nat_degree,
       cases degree p,
       { rintros ⟨_, ⟨⟩, _⟩ },
       { exact with_bot.some_lt_some.mp } } ⟩

variables [semiring S]

lemma nat_degree_pos_of_eval₂_root {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  0 < nat_degree p :=
lt_of_not_ge $ λ hlt, begin
  rw [eq_C_of_nat_degree_le_zero hlt, eval₂_C] at hz,
  refine hp (finsupp.ext (λ n, _)),
  cases n,
  { exact inj _ hz },
  { exact coeff_eq_zero_of_nat_degree_lt (lt_of_le_of_lt hlt (nat.succ_pos _)) }
end

lemma degree_pos_of_eval₂_root {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  0 < degree p :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_eval₂_root hp f hz inj)

end semiring

section ring
variables [ring R] {p q : polynomial R}

@[simp]
lemma C_eq_int_cast (n : ℤ) : C ↑n = (n : polynomial R) :=
(C : R →+* _).map_int_cast n

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

@[simp] lemma degree_neg (p : polynomial R) : degree (-p) = degree p :=
by unfold degree; rw support_neg

lemma degree_sub_le (p q : polynomial R) : degree (p - q) ≤ max (degree p) (degree q) :=
degree_neg q ▸ degree_add_le p (-q)

@[simp] lemma nat_degree_neg (p : polynomial R) : nat_degree (-p) = nat_degree p :=
by simp [nat_degree]

@[simp] lemma nat_degree_int_cast (n : ℤ) : nat_degree (n : polynomial R) = 0 :=
by simp only [←C_eq_int_cast, nat_degree_C]

@[simp] lemma coeff_neg (p : polynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := rfl

@[simp]
lemma coeff_sub (p q : polynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := rfl

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

lemma coeff_mul_X_sub_C {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - C r)) (a + 1) = coeff p a - coeff p (a + 1) * r :=
by simp [mul_sub]

end ring

section comm_ring
variables [comm_ring R] {p q : polynomial R}
instance : comm_ring (polynomial R) := add_monoid_algebra.comm_ring

instance eval₂.is_ring_hom {S} [comm_ring S]
  (f : R →+* S) {x : S} : is_ring_hom (eval₂ f x) :=
by apply is_ring_hom.of_semiring

instance eval.is_ring_hom {x : R} : is_ring_hom (eval x) := eval₂.is_ring_hom _

end comm_ring

section comm_semiring
variables [comm_semiring R] {p q : polynomial R}

section aeval
/-- `R[X]` is the generator of the category `R-Alg`. -/
instance polynomial (R : Type u) [comm_semiring R] : algebra R (polynomial R) :=
{ commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, (polynomial.C_mul' c p).symm,
  .. polynomial.semimodule, .. ring_hom.of polynomial.C }

variables (R) (A)

-- TODO this could be generalized: there's no need for `A` to be commutative,
-- we just need that `x` is central.
variables [comm_ring A] [algebra R A]
variables (x : A)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. -/
def aeval : polynomial R →ₐ[R] A :=
{ commutes' := λ r, eval₂_C _ _,
  ..eval₂_ring_hom (algebra_map R A) x }

variables {R A}

theorem aeval_def (p : polynomial R) : aeval R A x p = eval₂ (algebra_map R A) x p := rfl

@[simp] lemma aeval_X : aeval R A x X = x := eval₂_X _ x

@[simp] lemma aeval_C (r : R) : aeval R A x (C r) = algebra_map R A r := eval₂_C _ x

theorem eval_unique (φ : polynomial R →ₐ[R] A) (p) :
  φ p = eval₂ (algebra_map R A) (φ X) p :=
begin
  apply polynomial.induction_on p,
  { intro r, rw eval₂_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [φ.map_add, ih1, ih2, eval₂_add] },
  { intros n r ih,
    rw [pow_succ', ← mul_assoc, φ.map_mul, eval₂_mul (algebra_map R A), eval₂_X, ih] }
end

end aeval

end comm_semiring

section ring
variables [ring R] {p q : polynomial R}

lemma degree_sub_lt (hd : degree p = degree q)
  (hp0 : p ≠ 0) (hlc : leading_coeff p = leading_coeff q) :
  degree (p - q) < degree p :=
have hp : single (nat_degree p) (leading_coeff p) + p.erase (nat_degree p) = p :=
  finsupp.single_add_erase,
have hq : single (nat_degree q) (leading_coeff q) + q.erase (nat_degree q) = q :=
  finsupp.single_add_erase,
have hd' : nat_degree p = nat_degree q := by unfold nat_degree; rw hd,
have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0),
calc degree (p - q) = degree (erase (nat_degree q) p + -erase (nat_degree q) q) :
  by conv {to_lhs, rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]}
... ≤ max (degree (erase (nat_degree q) p)) (degree (erase (nat_degree q) q))
  : degree_neg (erase (nat_degree q) q) ▸ degree_add_le _ _
... < degree p : max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

lemma ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : monic q) : q ≠ 0
| h := begin
  rw [h, monic.def, leading_coeff_zero] at hq,
  rw [← mul_one p, ← C_1, ← hq, C_0, mul_zero] at hp,
  exact hp rfl
end

lemma div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : monic q) :
  degree (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) < degree p :=
have hp : leading_coeff p ≠ 0 := mt leading_coeff_eq_zero.1 h.2,
have hpq : leading_coeff (C (leading_coeff p) * X ^ (nat_degree p - nat_degree q)) *
    leading_coeff q ≠ 0,
  by rwa [leading_coeff_monomial, monic.def.1 hq, mul_one],
if h0 : p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q = 0
then h0.symm ▸ (lt_of_not_ge $ mt le_bot_iff.1 (mt degree_eq_bot.1 h.2))
else
  have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic h.2 hq,
  have hlt : nat_degree q ≤ nat_degree p := with_bot.coe_le_coe.1
    (by rw [← degree_eq_nat_degree h.2, ← degree_eq_nat_degree hq0];
    exact h.1),
  degree_sub_lt
  (by rw [degree_mul_eq' hpq, degree_monomial _ hp, degree_eq_nat_degree h.2,
      degree_eq_nat_degree hq0, ← with_bot.coe_add, nat.sub_add_cancel hlt])
  h.2
  (by rw [leading_coeff_mul' hpq, leading_coeff_monomial, monic.def.1 hq, mul_one])

noncomputable def div_mod_by_monic_aux : Π (p : polynomial R) {q : polynomial R},
  monic q → polynomial R × polynomial R
| p := λ q hq, if h : degree q ≤ degree p ∧ p ≠ 0 then
  let z := C (leading_coeff p) * X^(nat_degree p - nat_degree q)  in
  have wf : _ := div_wf_lemma h hq,
  let dm := div_mod_by_monic_aux (p - z * q) hq in
  ⟨z + dm.1, dm.2⟩
  else ⟨0, p⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic (p q : polynomial R) : polynomial R :=
if hq : monic q then (div_mod_by_monic_aux p hq).1 else 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q`. -/
def mod_by_monic (p q : polynomial R) : polynomial R :=
if hq : monic q then (div_mod_by_monic_aux p hq).2 else p

infixl  ` /ₘ ` : 70 := div_by_monic

infixl ` %ₘ ` : 70 := mod_by_monic

lemma degree_mod_by_monic_lt : ∀ (p : polynomial R) {q : polynomial R} (hq : monic q)
  (hq0 : q ≠ 0), degree (p %ₘ q) < degree q
| p := λ q hq hq0,
if h : degree q ≤ degree p ∧ p ≠ 0 then
  have wf : _ := div_wf_lemma ⟨h.1, h.2⟩ hq,
  have degree ((p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) %ₘ q) < degree q :=
      degree_mod_by_monic_lt (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q)
      hq hq0,
  begin
    unfold mod_by_monic at this ⊢,
    unfold div_mod_by_monic_aux,
    rw dif_pos hq at this ⊢,
    rw if_pos h,
    exact this
  end
else
  or.cases_on (not_and_distrib.1 h) begin
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h],
    exact lt_of_not_ge,
  end
  begin
    assume hp,
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h, not_not.1 hp],
    exact lt_of_le_of_ne bot_le
      (ne.symm (mt degree_eq_bot.1 hq0)),
  end
using_well_founded {dec_tac := tactic.assumption}

@[simp] lemma zero_mod_by_monic (p : polynomial R) : 0 %ₘ p = 0 :=
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma zero_div_by_monic (p : polynomial R) : 0 /ₘ p = 0 :=
begin
  unfold div_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma mod_by_monic_zero (p : polynomial R) : p %ₘ 0 = p :=
if h : monic (0 : polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold mod_by_monic div_mod_by_monic_aux; rw dif_neg h

@[simp] lemma div_by_monic_zero (p : polynomial R) : p /ₘ 0 = 0 :=
if h : monic (0 : polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold div_by_monic div_mod_by_monic_aux; rw dif_neg h

lemma div_by_monic_eq_of_not_monic (p : polynomial R) (hq : ¬monic q) : p /ₘ q = 0 := dif_neg hq

lemma mod_by_monic_eq_of_not_monic (p : polynomial R) (hq : ¬monic q) : p %ₘ q = p := dif_neg hq

lemma mod_by_monic_eq_self_iff (hq : monic q) (hq0 : q ≠ 0) : p %ₘ q = p ↔ degree p < degree q :=
⟨λ h, h ▸ degree_mod_by_monic_lt _ hq hq0,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold mod_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

theorem monic_X_sub_C (x : R) : monic (X - C x) :=
by simpa only [C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
monic_X_pow_add ((degree_neg p).symm ▸ H)

theorem degree_mod_by_monic_le (p : polynomial R) {q : polynomial R}
  (hq : monic q) : degree (p %ₘ q) ≤ degree q :=
decidable.by_cases
  (assume H : q = 0, by rw [monic, H, leading_coeff_zero] at hq;
    have : (0:polynomial R) = 1 := (by rw [← C_0, ← C_1, hq]);
    exact le_of_eq (congr_arg _ $ eq_of_zero_eq_one this (p %ₘ q) q))
  (assume H : q ≠ 0, le_of_lt $ degree_mod_by_monic_lt _ hq H)

end ring

section comm_ring
variables [comm_ring R] {p q : polynomial R}

lemma mod_by_monic_eq_sub_mul_div : ∀ (p : polynomial R) {q : polynomial R} (hq : monic q),
  p %ₘ q = p - q * (p /ₘ q)
| p := λ q hq,
  if h : degree q ≤ degree p ∧ p ≠ 0 then
    have wf : _ := div_wf_lemma h hq,
    have ih : _ := mod_by_monic_eq_sub_mul_div
      (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) hq,
    begin
      unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
      rw [dif_pos hq, if_pos h],
      rw [mod_by_monic, dif_pos hq] at ih,
      refine ih.trans _,
      unfold div_by_monic,
      rw [dif_pos hq, dif_pos hq, if_pos h, mul_add, sub_add_eq_sub_sub, mul_comm]
    end
  else
    begin
      unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
      rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]
    end
using_well_founded {dec_tac := tactic.assumption}

lemma mod_by_monic_add_div (p : polynomial R) {q : polynomial R} (hq : monic q) :
  p %ₘ q + q * (p /ₘ q) = p := eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

lemma div_by_monic_eq_zero_iff (hq : monic q) (hq0 : q ≠ 0) : p /ₘ q = 0 ↔ degree p < degree q :=
⟨λ h, by have := mod_by_monic_add_div p hq;
  rwa [h, mul_zero, add_zero, mod_by_monic_eq_self_iff hq hq0] at this,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold div_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

lemma degree_add_div_by_monic (hq : monic q) (h : degree q ≤ degree p) :
  degree q + degree (p /ₘ q) = degree p :=
if hq0 : q = 0 then
  have ∀ (p : polynomial R), p = 0,
    from λ p, (@subsingleton_of_monic_zero R _ (hq0 ▸ hq)).1 _ _,
  by rw [this (p /ₘ q), this p, this q]; refl
else
have hdiv0 : p /ₘ q ≠ 0 := by rwa [(≠), div_by_monic_eq_zero_iff hq hq0, not_lt],
have hlc : leading_coeff q * leading_coeff (p /ₘ q) ≠ 0 :=
  by rwa [monic.def.1 hq, one_mul, (≠), leading_coeff_eq_zero],
have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
  calc degree (p %ₘ q) < degree q : degree_mod_by_monic_lt _ hq hq0
  ... ≤ _ : by rw [degree_mul_eq' hlc, degree_eq_nat_degree hq0,
      degree_eq_nat_degree hdiv0, ← with_bot.coe_add, with_bot.coe_le_coe];
    exact nat.le_add_right _ _,
calc degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) : eq.symm (degree_mul_eq' hlc)
... = degree (p %ₘ q + q * (p /ₘ q)) : (degree_add_eq_of_degree_lt hmod).symm
... = _ : congr_arg _ (mod_by_monic_add_div _ hq)

lemma degree_div_by_monic_le (p q : polynomial R) : degree (p /ₘ q) ≤ degree p :=
if hp0 : p = 0 then by simp only [hp0, zero_div_by_monic, le_refl]
else if hq : monic q then
  have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic hp0 hq,
  if h : degree q ≤ degree p
  then by rw [← degree_add_div_by_monic hq h, degree_eq_nat_degree hq0,
      degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq hq0).1 (not_lt.2 h))];
    exact with_bot.coe_le_coe.2 (nat.le_add_left _ _)
  else
    by unfold div_by_monic div_mod_by_monic_aux;
      simp only [dif_pos hq, h, false_and, if_false, degree_zero, bot_le]
else (div_by_monic_eq_of_not_monic p hq).symm ▸ bot_le

lemma degree_div_by_monic_lt (p : polynomial R) {q : polynomial R} (hq : monic q)
  (hp0 : p ≠ 0) (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic hp0 hq,
if hpq : degree p < degree q
then begin
  rw [(div_by_monic_eq_zero_iff hq hq0).2 hpq, degree_eq_nat_degree hp0],
  exact with_bot.bot_lt_some _
end
else begin
  rw [← degree_add_div_by_monic hq (not_lt.1 hpq), degree_eq_nat_degree hq0,
        degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq hq0).1 hpq)],
  exact with_bot.coe_lt_coe.2 (nat.lt_add_of_pos_left
    (with_bot.coe_lt_coe.1 $ (degree_eq_nat_degree hq0) ▸ h0q))
end

lemma div_mod_by_monic_unique {f g} (q r : polynomial R) (hg : monic g)
  (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r :=
if hg0 : g = 0 then by split; exact (subsingleton_of_monic_zero
  (hg0 ▸ hg : monic (0 : polynomial R))).1 _ _
else
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g),
    from eq_of_sub_eq_zero
      (by rw [← sub_eq_zero_of_eq (h.1.trans (mod_by_monic_add_div f hg).symm)];
        simp [mul_add, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]),
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)),
    by simp [h₁],
  have h₄ : degree (r - f %ₘ g) < degree g,
    from calc degree (r - f %ₘ g) ≤ max (degree r) (degree (-(f %ₘ g))) :
      degree_add_le _ _
    ... < degree g : max_lt_iff.2 ⟨h.2, by rw degree_neg; exact degree_mod_by_monic_lt _ hg hg0⟩,
  have h₅ : q - (f /ₘ g) = 0,
    from by_contradiction
      (λ hqf, not_le_of_gt h₄ $
        calc degree g ≤ degree g + degree (q - f /ₘ g) :
          by erw [degree_eq_nat_degree hg0, degree_eq_nat_degree hqf,
              with_bot.coe_le_coe];
            exact nat.le_add_right _ _
        ... = degree (r - f %ₘ g) :
          by rw [h₂, degree_mul_eq']; simpa [monic.def.1 hg]),
  ⟨eq.symm $ eq_of_sub_eq_zero h₅,
    eq.symm $ eq_of_sub_eq_zero $ by simpa [h₅] using h₁⟩

lemma map_mod_div_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f :=
if h01 : (0 : S) = 1 then by haveI := subsingleton_of_zero_eq_one h01;
  exact ⟨subsingleton.elim _ _, subsingleton.elim _ _⟩
else
have h01R : (0 : R) ≠ 1, from mt (congr_arg f)
  (by rwa [is_semiring_hom.map_one f, is_semiring_hom.map_zero f]),
have map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q),
  from (div_mod_by_monic_unique ((p /ₘ q).map f) _ (monic_map f hq)
    ⟨eq.symm $ by rw [← map_mul, ← map_add, mod_by_monic_add_div _ hq],
    calc _ ≤ degree (p %ₘ q) : degree_map_le _
    ... < degree q : degree_mod_by_monic_lt _ hq
      $ (ne_zero_of_monic_of_zero_ne_one hq h01R)
    ... = _ : eq.symm $ degree_map_eq_of_leading_coeff_ne_zero _
      (by rw [monic.def.1 hq, is_semiring_hom.map_one f]; exact ne.symm h01)⟩),
⟨this.1.symm, this.2.symm⟩

lemma map_div_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f :=
(map_mod_div_by_monic f hq).1

lemma map_mod_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p %ₘ q).map f = p.map f %ₘ q.map f :=
(map_mod_div_by_monic f hq).2

lemma dvd_iff_mod_by_monic_eq_zero (hq : monic q) : p %ₘ q = 0 ↔ q ∣ p :=
⟨λ h, by rw [← mod_by_monic_add_div p hq, h, zero_add];
  exact dvd_mul_right _ _,
λ h, if hq0 : q = 0 then by rw hq0 at hq;
  exact (subsingleton_of_monic_zero hq).1 _ _
  else
  let ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h in
  by_contradiction (λ hpq0,
  have hmod : p %ₘ q = q * (r - p /ₘ q) :=
    by rw [mod_by_monic_eq_sub_mul_div _ hq, mul_sub, ← hr],
  have degree (q * (r - p /ₘ q)) < degree q :=
    hmod ▸ degree_mod_by_monic_lt _ hq hq0,
  have hrpq0 : leading_coeff (r - p /ₘ q) ≠ 0 :=
    λ h, hpq0 $ leading_coeff_eq_zero.1
      (by rw [hmod, leading_coeff_eq_zero.1 h, mul_zero, leading_coeff_zero]),
  have hlc : leading_coeff q * leading_coeff (r - p /ₘ q) ≠ 0 :=
    by rwa [monic.def.1 hq, one_mul],
  by rw [degree_mul_eq' hlc, degree_eq_nat_degree hq0,
      degree_eq_nat_degree (mt leading_coeff_eq_zero.2 hrpq0)] at this;
    exact not_lt_of_ge (nat.le_add_right _ _) (with_bot.some_lt_some.1 this))⟩

@[simp] lemma mod_by_monic_one (p : polynomial R) : p %ₘ 1 = 0 :=
(dvd_iff_mod_by_monic_eq_zero (by convert monic_one)).2 (one_dvd _)

@[simp] lemma div_by_monic_one (p : polynomial R) : p /ₘ 1 = p :=
by conv_rhs { rw [← mod_by_monic_add_div p monic_one] }; simp

variables [comm_ring S]

lemma nat_degree_pos_of_aeval_root [algebra R S] {p : polynomial R} (hp : p ≠ 0)
  {z : S} (hz : aeval R S z p = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < p.nat_degree :=
nat_degree_pos_of_eval₂_root hp (algebra_map R S) hz inj

lemma degree_pos_of_aeval_root [algebra R S] {p : polynomial R} (hp : p ≠ 0)
  {z : S} (hz : aeval R S z p = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < p.degree :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_aeval_root hp hz inj)

lemma root_X_sub_C : is_root (X - C a) b ↔ a = b :=
by rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero_iff_eq, eq_comm]

end comm_ring

section nonzero_ring
variables [ring R] [nonzero R] {p q : polynomial R}

@[simp] lemma degree_X_sub_C (a : R) : degree (X - C a) = 1 :=
begin
  rw [sub_eq_add_neg, add_comm, ← @degree_X R],
  by_cases ha : a = 0,
  { simp only [ha, C_0, neg_zero, zero_add] },
  exact degree_add_eq_of_degree_lt (by rw [degree_X, degree_neg, degree_C ha]; exact dec_trivial)
end

lemma degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  degree ((X : polynomial R) ^ n - C a) = n :=
have degree (-C a) < degree ((X : polynomial R) ^ n),
  from calc degree (-C a) ≤ 0 : by rw degree_neg; exact degree_C_le
  ... < degree ((X : polynomial R) ^ n) : by rwa [degree_X_pow];
    exact with_bot.coe_lt_coe.2 hn,
by rw [sub_eq_add_neg, add_comm, degree_add_eq_of_degree_lt this, degree_X_pow]

lemma X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) :
  (X : polynomial R) ^ n - C a ≠ 0 :=
mt degree_eq_bot.2 (show degree ((X : polynomial R) ^ n - C a) ≠ ⊥,
  by rw degree_X_pow_sub_C hn a; exact dec_trivial)

lemma nat_degree_X_sub_C {r : R} : (X - C r).nat_degree = 1 :=
by { apply nat_degree_eq_of_degree_eq_some, simp, }

lemma nat_degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} :
  (X ^ n - C r).nat_degree = n :=
by { apply nat_degree_eq_of_degree_eq_some, simp [degree_X_pow_sub_C hn], }

end nonzero_ring

section ring
variables [ring R]

lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : polynomial R) : p = 0 :=
by rw [←one_smul R p, ←h, zero_smul]

lemma nat_degree_X_sub_C_le {r : R} : (X - C r).nat_degree ≤ 1 :=
begin
  classical,
  by_cases h : (0 : R) = (1 : R),
  { calc (X - C r).nat_degree
         = (0 : polynomial R).nat_degree : congr_arg nat_degree (eq_zero_of_eq_zero h _)
     ... = 0 : nat_degree_zero
     ... ≤ 1 : zero_le 1, },
  { haveI : nonzero R := ⟨h⟩,
    exact le_of_eq nat_degree_X_sub_C, }
end

/--
The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
lemma eval_mul_X_sub_C {p : polynomial R} (r : R) :
  (p * (X - C r)).eval r = 0 :=
begin
  simp only [eval, eval₂, ring_hom.id_apply],
  have bound := calc
    (p * (X - C r)).nat_degree
         ≤ p.nat_degree + (X - C r).nat_degree : nat_degree_mul_le
     ... ≤ p.nat_degree + 1 : add_le_add_left nat_degree_X_sub_C_le _
     ... < p.nat_degree + 2 : lt_add_one _,
  rw sum_over_range' _ _ (p.nat_degree + 2) bound,
  swap,
  { simp, },
  rw sum_range_succ',
  conv_lhs {
    congr, apply_congr, skip,
    rw [coeff_mul_X_sub_C, sub_mul, mul_assoc, ←pow_succ],
  },
  simp [sum_range_sub', coeff_single],
end

end ring

section comm_ring

variables [comm_ring R] {p q : polynomial R}

@[simp] lemma mod_by_monic_X_sub_C_eq_C_eval (p : polynomial R) (a : R) :
  p %ₘ (X - C a) = C (p.eval a) :=
if h0 : (0 : R) = 1 then by letI := subsingleton_of_zero_eq_one h0; exact subsingleton.elim _ _
else
by letI : nonzero R := nonzero.of_ne h0; exact
have h : (p %ₘ (X - C a)).eval a = p.eval a :=
  by rw [mod_by_monic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero],
have degree (p %ₘ (X - C a)) < 1 :=
  degree_X_sub_C a ▸ degree_mod_by_monic_lt p (monic_X_sub_C a) ((degree_X_sub_C a).symm ▸
    ne_zero_of_monic (monic_X_sub_C _)),
have degree (p %ₘ (X - C a)) ≤ 0 :=
  begin
    cases (degree (p %ₘ (X - C a))),
    { exact bot_le },
    { exact with_bot.some_le_some.2 (nat.le_of_lt_succ (with_bot.some_lt_some.1 this)) }
  end,
begin
  rw [eq_C_of_degree_le_zero this, eval_C] at h,
  rw [eq_C_of_degree_le_zero this, h]
end

lemma mul_div_by_monic_eq_iff_is_root : (X - C a) * (p /ₘ (X - C a)) = p ↔ is_root p a :=
⟨λ h, by rw [← h, is_root.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
λ h : p.eval a = 0,
  by conv {to_rhs, rw ← mod_by_monic_add_div p (monic_X_sub_C a)};
    rw [mod_by_monic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩

lemma dvd_iff_is_root : (X - C a) ∣ p ↔ is_root p a :=
⟨λ h, by rwa [← dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _),
    mod_by_monic_X_sub_C_eq_C_eval, ← C_0, C_inj] at h,
  λ h, ⟨(p /ₘ (X - C a)), by rw mul_div_by_monic_eq_iff_is_root.2 h⟩⟩

lemma mod_by_monic_X (p : polynomial R) : p %ₘ X = C (p.eval 0) :=
by rw [← mod_by_monic_X_sub_C_eq_C_eval, C_0, sub_zero]

section multiplicity

def decidable_dvd_monic (p : polynomial R) (hq : monic q) : decidable (q ∣ p) :=
decidable_of_iff (p %ₘ q = 0) (dvd_iff_mod_by_monic_eq_zero hq)

open_locale classical

lemma multiplicity_X_sub_C_finite (a : R) (h0 : p ≠ 0) :
  multiplicity.finite (X - C a) p :=
multiplicity_finite_of_degree_pos_of_monic
  (have (0 : R) ≠ 1, from (λ h, by haveI := subsingleton_of_zero_eq_one h;
      exact h0 (subsingleton.elim _ _)),
    by haveI : nonzero R := ⟨this⟩; rw degree_X_sub_C; exact dec_trivial)
    (monic_X_sub_C _) h0

def root_multiplicity (a : R) (p : polynomial R) : ℕ :=
if h0 : p = 0 then 0
else let I : decidable_pred (λ n : ℕ, ¬(X - C a) ^ (n + 1) ∣ p) :=
  λ n, @not.decidable _ (decidable_dvd_monic p (monic_pow (monic_X_sub_C a) (n + 1))) in
by exactI nat.find (multiplicity_X_sub_C_finite a h0)

lemma root_multiplicity_eq_multiplicity (p : polynomial R) (a : R) :
  root_multiplicity a p = if h0 : p = 0 then 0 else
  (multiplicity (X - C a) p).get (multiplicity_X_sub_C_finite a h0) :=
by simp [multiplicity, root_multiplicity, roption.dom];
  congr; funext; congr

lemma pow_root_multiplicity_dvd (p : polynomial R) (a : R) :
  (X - C a) ^ root_multiplicity a p ∣ p :=
if h : p = 0 then by simp [h]
else by rw [root_multiplicity_eq_multiplicity, dif_neg h];
  exact multiplicity.pow_multiplicity_dvd _

lemma div_by_monic_mul_pow_root_multiplicity_eq
  (p : polynomial R) (a : R) :
  p /ₘ ((X - C a) ^ root_multiplicity a p) *
  (X - C a) ^ root_multiplicity a p = p :=
have monic ((X - C a) ^ root_multiplicity a p),
  from monic_pow (monic_X_sub_C _) _,
by conv_rhs { rw [← mod_by_monic_add_div p this,
    (dvd_iff_mod_by_monic_eq_zero this).2 (pow_root_multiplicity_dvd _ _)] };
  simp [mul_comm]

lemma eval_div_by_monic_pow_root_multiplicity_ne_zero
  {p : polynomial R} (a : R) (hp : p ≠ 0) :
  (p /ₘ ((X - C a) ^ root_multiplicity a p)).eval a ≠ 0 :=
begin
  haveI : nonzero R := nonzero.of_polynomial_ne hp,
  rw [ne.def, ← is_root.def, ← dvd_iff_is_root],
  rintros ⟨q, hq⟩,
  have := div_by_monic_mul_pow_root_multiplicity_eq p a,
  rw [mul_comm, hq, ← mul_assoc, ← pow_succ',
    root_multiplicity_eq_multiplicity, dif_neg hp] at this,
  exact multiplicity.is_greatest'
    (multiplicity_finite_of_degree_pos_of_monic
    (show (0 : with_bot ℕ) < degree (X - C a),
      by rw degree_X_sub_C; exact dec_trivial) (monic_X_sub_C _) hp)
    (nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
end

end multiplicity

end comm_ring

section integral_domain
variables [integral_domain R] {p q : polynomial R}

@[simp] lemma degree_mul_eq : degree (p * q) = degree p + degree q :=
if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, with_bot.bot_add]
else if hq0 : q = 0 then  by simp only [hq0, degree_zero, mul_zero, with_bot.add_bot]
else degree_mul_eq' $ mul_ne_zero (mt leading_coeff_eq_zero.1 hp0)
    (mt leading_coeff_eq_zero.1 hq0)

@[simp] lemma degree_pow_eq (p : polynomial R) (n : ℕ) :
  degree (p ^ n) = n •ℕ (degree p) :=
by induction n; [simp only [pow_zero, degree_one, zero_nsmul],
simp only [*, pow_succ, succ_nsmul, degree_mul_eq]]

@[simp] lemma leading_coeff_mul (p q : polynomial R) : leading_coeff (p * q) =
  leading_coeff p * leading_coeff q :=
begin
  by_cases hp : p = 0,
  { simp only [hp, zero_mul, leading_coeff_zero] },
  { by_cases hq : q = 0,
    { simp only [hq, mul_zero, leading_coeff_zero] },
    { rw [leading_coeff_mul'],
      exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) (mt leading_coeff_eq_zero.1 hq) } }
end

@[simp] lemma leading_coeff_pow (p : polynomial R) (n : ℕ) :
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
by induction n; [simp only [pow_zero, leading_coeff_one],
simp only [*, pow_succ, leading_coeff_mul]]

instance : integral_domain (polynomial R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h, begin
    have : leading_coeff 0 = leading_coeff a * leading_coeff b := h ▸ leading_coeff_mul a b,
    rw [leading_coeff_zero, eq_comm] at this,
    erw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero],
    exact eq_zero_or_eq_zero_of_mul_eq_zero this
  end,
  ..polynomial.nonzero,
  ..polynomial.comm_ring }

lemma nat_degree_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p * q) =
  nat_degree p + nat_degree q :=
by rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq),
    with_bot.coe_add, ← degree_eq_nat_degree hp,
    ← degree_eq_nat_degree hq, degree_mul_eq]

@[simp] lemma nat_degree_pow_eq (p : polynomial R) (n : ℕ) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0
then if hn0 : n = 0 then by simp [hp0, hn0]
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else nat_degree_pow_eq'
  (by rw [← leading_coeff_pow, ne.def, leading_coeff_eq_zero]; exact pow_ne_zero _ hp0)

lemma root_or_root_of_root_mul (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
by rw [is_root, eval_mul] at h;
  exact eq_zero_or_eq_zero_of_mul_eq_zero h

lemma degree_le_mul_left (p : polynomial R) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
if hp : p = 0 then by simp only [hp, zero_mul, le_refl]
else by rw [degree_mul_eq, degree_eq_nat_degree hp,
    degree_eq_nat_degree hq];
  exact with_bot.coe_le_coe.2 (nat.le_add_right _ _)

theorem nat_degree_le_of_dvd {p q : polynomial R} (h1 : p ∣ q) (h2 : q ≠ 0) : p.nat_degree ≤ q.nat_degree :=
begin
  rcases h1 with ⟨q, rfl⟩, rw mul_ne_zero_iff at h2,
  rw [nat_degree_mul_eq h2.1 h2.2], exact nat.le_add_right _ _
end

lemma exists_finset_roots : ∀ {p : polynomial R} (hp : p ≠ 0),
  ∃ s : finset R, (s.card : with_bot ℕ) ≤ degree p ∧ ∀ x, x ∈ s ↔ is_root p x
| p := λ hp, by haveI := classical.prop_decidable (∃ x, is_root p x); exact
if h : ∃ x, is_root p x
then
  let ⟨x, hx⟩ := h in
  have hpd : 0 < degree p := degree_pos_of_root hp hx,
  have hd0 : p /ₘ (X - C x) ≠ 0 :=
    λ h, by rw [← mul_div_by_monic_eq_iff_is_root.2 hx, h, mul_zero] at hp; exact hp rfl,
  have wf : degree (p /ₘ _) < degree p :=
    degree_div_by_monic_lt _ (monic_X_sub_C x) hp
    ((degree_X_sub_C x).symm ▸ dec_trivial),
  let ⟨t, htd, htr⟩ := @exists_finset_roots (p /ₘ (X - C x)) hd0 in
  have hdeg : degree (X - C x) ≤ degree p := begin
    rw [degree_X_sub_C, degree_eq_nat_degree hp],
    rw degree_eq_nat_degree hp at hpd,
    exact with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 hpd)
  end,
  have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)
    (ne_zero_of_monic (monic_X_sub_C x))).1 $ not_lt.2 hdeg,
  ⟨insert x t, calc (card (insert x t) : with_bot ℕ) ≤ card t + 1 :
    with_bot.coe_le_coe.2 $ finset.card_insert_le _ _
    ... ≤ degree p :
      by rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg,
          degree_X_sub_C, add_comm];
        exact add_le_add (le_refl (1 : with_bot ℕ)) htd,
  begin
    assume y,
    rw [mem_insert, htr, eq_comm, ← root_X_sub_C],
    conv {to_rhs, rw ← mul_div_by_monic_eq_iff_is_root.2 hx},
    exact ⟨λ h, or.cases_on h (root_mul_right_of_is_root _) (root_mul_left_of_is_root _),
      root_or_root_of_root_mul⟩
  end⟩
else
  ⟨∅, (degree_eq_nat_degree hp).symm ▸ with_bot.coe_le_coe.2 (nat.zero_le _),
    by simpa only [not_mem_empty, false_iff, not_exists] using h⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `roots p` noncomputably gives a finset containing all the roots of `p` -/
noncomputable def roots (p : polynomial R) : finset R :=
if h : p = 0 then ∅ else classical.some (exists_finset_roots h)

lemma card_roots (hp0 : p ≠ 0) : ((roots p).card : with_bot ℕ) ≤ degree p :=
begin
  unfold roots,
  rw dif_neg hp0,
  exact (classical.some_spec (exists_finset_roots hp0)).1
end

lemma card_roots' {p : polynomial R} (hp0 : p ≠ 0) : p.roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq $ degree_eq_nat_degree hp0))

lemma card_roots_sub_C {p : polynomial R} {a : R} (hp0 : 0 < degree p) :
  ((p - C a).roots.card : with_bot ℕ) ≤ degree p :=
calc ((p - C a).roots.card : with_bot ℕ) ≤ degree (p - C a) :
  card_roots $ mt sub_eq_zero.1 $ λ h, not_le_of_gt hp0 $ h.symm ▸ degree_C_le
... = degree p : by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

lemma card_roots_sub_C' {p : polynomial R} {a : R} (hp0 : 0 < degree p) :
  (p - C a).roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots_sub_C hp0) (le_of_eq $ degree_eq_nat_degree
  (λ h, by simp [*, lt_irrefl] at *)))

@[simp] lemma mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a :=
by unfold roots; rw dif_neg hp; exact (classical.some_spec (exists_finset_roots hp)).2 _

@[simp] lemma mem_roots_sub_C {p : polynomial R} {a x : R} (hp0 : 0 < degree p) :
  x ∈ (p - C a).roots ↔ p.eval x = a :=
(mem_roots (show p - C a ≠ 0, from mt sub_eq_zero.1 $ λ h,
    not_le_of_gt hp0 $ h.symm ▸ degree_C_le)).trans
  (by rw [is_root.def, eval_sub, eval_C, sub_eq_zero])

lemma card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  (roots ((X : polynomial R) ^ n - C a)).card ≤ n :=
with_bot.coe_le_coe.1 $
calc ((roots ((X : polynomial R) ^ n - C a)).card : with_bot ℕ)
      ≤ degree ((X : polynomial R) ^ n - C a) : card_roots (X_pow_sub_C_ne_zero hn a)
  ... = n : degree_X_pow_sub_C hn a

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nth_roots {R : Type*} [integral_domain R] (n : ℕ) (a : R) : finset R :=
roots ((X : polynomial R) ^ n - C a)

@[simp] lemma mem_nth_roots {R : Type*} [integral_domain R] {n : ℕ} (hn : 0 < n) {a x : R} :
  x ∈ nth_roots n a ↔ x ^ n = a :=
by rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a),
  is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero_iff_eq]

lemma card_nth_roots {R : Type*} [integral_domain R] (n : ℕ) (a : R) :
  (nth_roots n a).card ≤ n :=
if hn : n = 0
then if h : (X : polynomial R) ^ n - C a = 0
  then by simp only [nat.zero_le, nth_roots, roots, h, dif_pos rfl, card_empty]
  else with_bot.coe_le_coe.1 (le_trans (card_roots h)
   (by rw [hn, pow_zero, ← C_1, ← @is_ring_hom.map_sub _ _ _ _ (@C R _)];
      exact degree_C_le))
else by rw [← with_bot.coe_le_coe, ← degree_X_pow_sub_C (nat.pos_of_ne_zero hn) a];
  exact card_roots (X_pow_sub_C_ne_zero (nat.pos_of_ne_zero hn) a)

lemma coeff_comp_degree_mul_degree (hqd0 : nat_degree q ≠ 0) :
  coeff (p.comp q) (nat_degree p * nat_degree q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
if hp0 : p = 0 then by simp [hp0] else
calc coeff (p.comp q) (nat_degree p * nat_degree q)
  = p.sum (λ n a, coeff (C a * q ^ n) (nat_degree p * nat_degree q)) :
    by rw [comp, eval₂, coeff_sum]
... = coeff (C (leading_coeff p) * q ^ nat_degree p) (nat_degree p * nat_degree q) :
  finset.sum_eq_single _
  begin
    assume b hbs hbp,
    have hq0 : q ≠ 0, from λ hq0, hqd0 (by rw [hq0, nat_degree_zero]),
    have : coeff p b ≠ 0, rwa [← apply_eq_coeff, ← finsupp.mem_support_iff],
    dsimp [apply_eq_coeff],
    refine coeff_eq_zero_of_degree_lt _,
    rw [degree_mul_eq, degree_C this, degree_pow_eq, zero_add, degree_eq_nat_degree hq0,
      ← with_bot.coe_nsmul, nsmul_eq_mul, with_bot.coe_lt_coe, nat.cast_id],
    exact (mul_lt_mul_right (nat.pos_of_ne_zero hqd0)).2
      (lt_of_le_of_ne (with_bot.coe_le_coe.1 (by rw ← degree_eq_nat_degree hp0; exact le_sup hbs))
        hbp)
  end
  (by rw [finsupp.mem_support_iff, apply_eq_coeff, ← leading_coeff, ne.def, leading_coeff_eq_zero,
      classical.not_not]; simp {contextual := tt})
... = _ :
  have coeff (q ^ nat_degree p) (nat_degree p * nat_degree q) = leading_coeff (q ^ nat_degree p),
    by rw [leading_coeff, nat_degree_pow_eq],
  by rw [coeff_C_mul, this, leading_coeff_pow]

lemma nat_degree_comp : nat_degree (p.comp q) = nat_degree p * nat_degree q :=
le_antisymm nat_degree_comp_le
  (if hp0 : p = 0 then by rw [hp0, zero_comp, nat_degree_zero, zero_mul]
  else if hqd0 : nat_degree q = 0
  then have degree q ≤ 0, by rw [← with_bot.coe_zero, ← hqd0]; exact degree_le_nat_degree,
    by rw [eq_C_of_degree_le_zero this]; simp
  else le_nat_degree_of_ne_zero $
    have hq0 : q ≠ 0, from λ hq0, hqd0 $ by rw [hq0, nat_degree_zero],
    calc coeff (p.comp q) (nat_degree p * nat_degree q)
        = leading_coeff p * leading_coeff q ^ nat_degree p :
      coeff_comp_degree_mul_degree hqd0
    ... ≠ 0 : mul_ne_zero (mt leading_coeff_eq_zero.1 hp0)
      (pow_ne_zero _ (mt leading_coeff_eq_zero.1 hq0)))

lemma leading_coeff_comp (hq : nat_degree q ≠ 0) : leading_coeff (p.comp q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
by rw [← coeff_comp_degree_mul_degree hq, ← nat_degree_comp]; refl

lemma degree_eq_zero_of_is_unit (h : is_unit p) : degree p = 0 :=
let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h in
have hp0 : p ≠ 0, from λ hp0, by simpa [hp0] using hq,
have hq0 : q ≠ 0, from λ hp0, by simpa [hp0] using hq,
have nat_degree (1 : polynomial R) = nat_degree (p * q),
  from congr_arg _ hq,
by rw [nat_degree_one, nat_degree_mul_eq hp0 hq0, eq_comm,
    _root_.add_eq_zero_iff, ← with_bot.coe_eq_coe,
    ← degree_eq_nat_degree hp0] at this;
  exact this.1

@[simp] lemma degree_coe_units (u : units (polynomial R)) :
  degree (u : polynomial R) = 0 :=
degree_eq_zero_of_is_unit ⟨u, rfl⟩

@[simp] lemma nat_degree_coe_units (u : units (polynomial R)) :
  nat_degree (u : polynomial R) = 0 :=
nat_degree_eq_of_degree_eq_some (degree_coe_units u)

theorem is_unit_iff {f : polynomial R} : is_unit f ↔ ∃ r : R, is_unit r ∧ C r = f :=
⟨λ hf, ⟨f.coeff 0,
  is_unit_C.1 $ eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf) ▸ hf,
  (eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf)).symm⟩,
λ ⟨r, hr, hrf⟩, hrf ▸ is_unit_C.2 hr⟩

lemma coeff_coe_units_zero_ne_zero (u : units (polynomial R)) :
  coeff (u : polynomial R) 0 ≠ 0 :=
begin
  conv in (0) {rw [← nat_degree_coe_units u]},
  rw [← leading_coeff, ne.def, leading_coeff_eq_zero],
  exact units.coe_ne_zero _
end

lemma degree_eq_degree_of_associated (h : associated p q) : degree p = degree q :=
let ⟨u, hu⟩ := h in by simp [hu.symm]

lemma degree_eq_one_of_irreducible_of_root (hi : irreducible p) {x : R} (hx : is_root p x) :
  degree p = 1 :=
let ⟨g, hg⟩ := dvd_iff_is_root.2 hx in
have is_unit (X - C x) ∨ is_unit g, from hi.2 _ _ hg,
this.elim
  (λ h, have h₁ : degree (X - C x) = 1, from degree_X_sub_C x,
    have h₂ : degree (X - C x) = 0, from degree_eq_zero_of_is_unit h,
    by rw h₁ at h₂; exact absurd h₂ dec_trivial)
  (λ hgu, by rw [hg, degree_mul_eq, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zero])

lemma prime_of_degree_eq_one_of_monic (hp1 : degree p = 1)
  (hm : monic p) : prime p :=
have p = X - C (- p.coeff 0),
  by simpa [hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1,
⟨mt degree_eq_bot.2 $ hp1.symm ▸ dec_trivial,
  mt degree_eq_zero_of_is_unit (by simp [hp1]; exact dec_trivial),
    λ _ _, begin
      rw [this, dvd_iff_is_root, dvd_iff_is_root, dvd_iff_is_root,
        is_root, is_root, is_root, eval_mul, mul_eq_zero],
      exact id
    end⟩

lemma irreducible_of_degree_eq_one_of_monic (hp1 : degree p = 1)
  (hm : monic p) : irreducible p :=
irreducible_of_prime (prime_of_degree_eq_one_of_monic hp1 hm)

end integral_domain

section field
variables [field R] {p q : polynomial R}

lemma is_unit_iff_degree_eq_zero : is_unit p ↔ degree p = 0 :=
⟨degree_eq_zero_of_is_unit,
  λ h, have degree p ≤ 0, by simp [*, le_refl],
    have hc : coeff p 0 ≠ 0, from λ hc,
        by rw [eq_C_of_degree_le_zero this, hc] at h;
        simpa using h,
    is_unit_iff_dvd_one.2 ⟨C (coeff p 0)⁻¹, begin
      conv in p { rw eq_C_of_degree_le_zero this },
      rw [← C_mul, _root_.mul_inv_cancel hc, C_1]
    end⟩⟩

lemma degree_pos_of_ne_zero_of_nonunit (hp0 : p ≠ 0) (hp : ¬is_unit p) :
  0 < degree p :=
lt_of_not_ge (λ h, by rw [eq_C_of_degree_le_zero h] at hp0 hp;
  exact (hp $ is_unit.map' C $
    is_unit.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))))

lemma monic_mul_leading_coeff_inv (h : p ≠ 0) :
  monic (p * C (leading_coeff p)⁻¹) :=
by rw [monic, leading_coeff_mul, leading_coeff_C,
  mul_inv_cancel (show leading_coeff p ≠ 0, from mt leading_coeff_eq_zero.1 h)]

lemma degree_mul_leading_coeff_inv (p : polynomial R) (h : q ≠ 0) :
  degree (p * C (leading_coeff q)⁻¹) = degree p :=
have h₁ : (leading_coeff q)⁻¹ ≠ 0 :=
  inv_ne_zero (mt leading_coeff_eq_zero.1 h),
by rw [degree_mul_eq, degree_C h₁, add_zero]

def div (p q : polynomial R) :=
C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹))

def mod (p q : polynomial R) :=
p %ₘ (q * C (leading_coeff q)⁻¹)

private lemma quotient_mul_add_remainder_eq_aux (p q : polynomial R) :
  q * div p q + mod p q = p :=
if h : q = 0 then by simp only [h, zero_mul, mod, mod_by_monic_zero, zero_add]
else begin
  conv {to_rhs, rw ← mod_by_monic_add_div p (monic_mul_leading_coeff_inv h)},
  rw [div, mod, add_comm, mul_assoc]
end

private lemma remainder_lt_aux (p : polynomial R) (hq : q ≠ 0) :
  degree (mod p q) < degree q :=
by rw ← degree_mul_leading_coeff_inv q hq; exact
  degree_mod_by_monic_lt p (monic_mul_leading_coeff_inv hq)
    (mul_ne_zero hq (mt leading_coeff_eq_zero.2 (by rw leading_coeff_C;
      exact inv_ne_zero (mt leading_coeff_eq_zero.1 hq))))

instance : has_div (polynomial R) := ⟨div⟩

instance : has_mod (polynomial R) := ⟨mod⟩

lemma div_def : p / q = C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹)) := rfl

lemma mod_def : p % q = p %ₘ (q * C (leading_coeff q)⁻¹) := rfl

lemma mod_by_monic_eq_mod (p : polynomial R) (hq : monic q) : p %ₘ q = p % q :=
show p %ₘ q = p %ₘ (q * C (leading_coeff q)⁻¹), by simp only [monic.def.1 hq, inv_one, mul_one, C_1]

lemma div_by_monic_eq_div (p : polynomial R) (hq : monic q) : p /ₘ q = p / q :=
show p /ₘ q = C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹)),
by simp only [monic.def.1 hq, inv_one, C_1, one_mul, mul_one]

lemma mod_X_sub_C_eq_C_eval (p : polynomial R) (a : R) : p % (X - C a) = C (p.eval a) :=
mod_by_monic_eq_mod p (monic_X_sub_C a) ▸ mod_by_monic_X_sub_C_eq_C_eval _ _

lemma mul_div_eq_iff_is_root : (X - C a) * (p / (X - C a)) = p ↔ is_root p a :=
div_by_monic_eq_div p (monic_X_sub_C a) ▸ mul_div_by_monic_eq_iff_is_root

instance : euclidean_domain (polynomial R) :=
{ quotient := (/),
  quotient_zero := by simp [div_def],
  remainder := (%),
  r := _,
  r_well_founded := degree_lt_wf,
  quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq_aux,
  remainder_lt := λ p q hq, remainder_lt_aux _ hq,
  mul_left_not_lt := λ p q hq, not_lt_of_ge (degree_le_mul_left _ hq),
  .. polynomial.comm_ring,
  .. polynomial.nonzero }

lemma mod_eq_self_iff (hq0 : q ≠ 0) : p % q = p ↔ degree p < degree q :=
⟨λ h, h ▸ euclidean_domain.mod_lt _ hq0,
λ h, have ¬degree (q * C (leading_coeff q)⁻¹) ≤ degree p :=
  not_le_of_gt $ by rwa degree_mul_leading_coeff_inv q hq0,
begin
  rw [mod_def, mod_by_monic, dif_pos (monic_mul_leading_coeff_inv hq0)],
  unfold div_mod_by_monic_aux,
  simp only [this, false_and, if_false]
end⟩

lemma div_eq_zero_iff (hq0 : q ≠ 0) : p / q = 0 ↔ degree p < degree q :=
⟨λ h, by have := euclidean_domain.div_add_mod p q;
  rwa [h, mul_zero, zero_add, mod_eq_self_iff hq0] at this,
λ h, have hlt : degree p < degree (q * C (leading_coeff q)⁻¹),
    by rwa degree_mul_leading_coeff_inv q hq0,
  have hm : monic (q * C (leading_coeff q)⁻¹) := monic_mul_leading_coeff_inv hq0,
  by rw [div_def, (div_by_monic_eq_zero_iff hm (ne_zero_of_monic hm)).2 hlt, mul_zero]⟩

lemma degree_add_div (hq0 : q ≠ 0) (hpq : degree q ≤ degree p) :
  degree q + degree (p / q) = degree p :=
have degree (p % q) < degree (q * (p / q)) :=
  calc degree (p % q) < degree q : euclidean_domain.mod_lt _ hq0
  ... ≤ _ : degree_le_mul_left _ (mt (div_eq_zero_iff hq0).1 (not_lt_of_ge hpq)),
by conv {to_rhs, rw [← euclidean_domain.div_add_mod p q, add_comm,
    degree_add_eq_of_degree_lt this, degree_mul_eq]}

lemma degree_div_le (p q : polynomial R) : degree (p / q) ≤ degree p :=
if hq : q = 0 then by simp [hq]
else by rw [div_def, mul_comm, degree_mul_leading_coeff_inv _ hq];
  exact degree_div_by_monic_le _ _

lemma degree_div_lt (hp : p ≠ 0) (hq : 0 < degree q) : degree (p / q) < degree p :=
have hq0 : q ≠ 0, from λ hq0, by simpa [hq0] using hq,
by rw [div_def, mul_comm, degree_mul_leading_coeff_inv _ hq0];
  exact degree_div_by_monic_lt _ (monic_mul_leading_coeff_inv hq0) hp
    (by rw degree_mul_leading_coeff_inv _ hq0; exact hq)

@[simp] lemma degree_map [field k] (p : polynomial R) (f : R →+* k) :
  degree (p.map f) = degree p :=
p.degree_map_eq_of_injective f.injective

@[simp] lemma nat_degree_map [field k] (f : R →+* k) :
  nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map _ f)

@[simp] lemma leading_coeff_map [field k] (f : R →+* k) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
by simp [leading_coeff, coeff_map f]

lemma map_div [field k] (f : R →+* k) :
  (p / q).map f = p.map f / q.map f :=
if hq0 : q = 0 then by simp [hq0]
else
by rw [div_def, div_def, map_mul, map_div_by_monic f (monic_mul_leading_coeff_inv hq0)];
  simp [f.map_inv, leading_coeff, coeff_map f]

lemma map_mod [field k] (f : R →+* k) :
  (p % q).map f = p.map f % q.map f :=
if hq0 : q = 0 then by simp [hq0]
else by rw [mod_def, mod_def, leading_coeff_map f, ← f.map_inv, ← map_C f,
  ← map_mul f, map_mod_by_monic f (monic_mul_leading_coeff_inv hq0)]

@[simp] lemma map_eq_zero [field k] (f : R →+* k) :
  p.map f = 0 ↔ p = 0 :=
by simp [polynomial.ext_iff, f.map_eq_zero, coeff_map]

lemma exists_root_of_degree_eq_one (h : degree p = 1) : ∃ x, is_root p x :=
⟨-(p.coeff 0 / p.coeff 1),
  have p.coeff 1 ≠ 0,
    by rw ← nat_degree_eq_of_degree_eq_some h;
    exact mt leading_coeff_eq_zero.1 (λ h0, by simpa [h0] using h),
  by conv in p { rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1, by rw h; exact le_refl _)] };
    simp [is_root, mul_div_cancel' _ this]⟩

lemma coeff_inv_units (u : units (polynomial R)) (n : ℕ) :
  ((↑u : polynomial R).coeff n)⁻¹ = ((↑u⁻¹ : polynomial R).coeff n) :=
begin
  rw [eq_C_of_degree_eq_zero (degree_coe_units u), eq_C_of_degree_eq_zero (degree_coe_units u⁻¹),
    coeff_C, coeff_C, inv_eq_one_div],
  split_ifs,
  { rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
      coeff_zero_eq_eval_zero, ← eval_mul, ← units.coe_mul, inv_mul_self];
    simp },
  { simp }
end

instance : normalization_domain (polynomial R) :=
{ norm_unit := λ p, if hp0 : p = 0 then 1
    else ⟨C p.leading_coeff⁻¹, C p.leading_coeff,
      by rw [← C_mul, inv_mul_cancel, C_1];
       exact mt leading_coeff_eq_zero.1 hp0,
      by rw [← C_mul, mul_inv_cancel, C_1];
       exact mt leading_coeff_eq_zero.1 hp0,⟩,
  norm_unit_zero := dif_pos rfl,
  norm_unit_mul := λ p q hp0 hq0, begin
      rw [dif_neg hp0, dif_neg hq0, dif_neg (mul_ne_zero hp0 hq0)],
      apply units.ext,
      show C (leading_coeff (p * q))⁻¹ = C (leading_coeff p)⁻¹ * C (leading_coeff q)⁻¹,
      rw [leading_coeff_mul, mul_inv', C_mul, mul_comm]
    end,
  norm_unit_coe_units := λ u,
    have hu : degree ↑u⁻¹ = 0, from degree_eq_zero_of_is_unit ⟨u⁻¹, rfl⟩,
    begin
      apply units.ext,
      rw [dif_neg (units.coe_ne_zero u)],
      conv_rhs {rw eq_C_of_degree_eq_zero hu},
      refine C_inj.2 _,
      rw [← nat_degree_eq_of_degree_eq_some hu, leading_coeff,
        coeff_inv_units],
      simp
    end,
  ..polynomial.integral_domain }

lemma monic_normalize (hp0 : p ≠ 0) : monic (normalize p) :=
show leading_coeff (p * ↑(dite _ _ _)) = 1,
by rw dif_neg hp0; exact monic_mul_leading_coeff_inv hp0

lemma coe_norm_unit (hp : p ≠ 0) : (norm_unit p : polynomial R) = C p.leading_coeff⁻¹ :=
show ↑(dite _ _ _) = C p.leading_coeff⁻¹, by rw dif_neg hp; refl

@[simp] lemma degree_normalize : degree (normalize p) = degree p :=
if hp0 : p = 0 then by simp [hp0]
else by rw [normalize, degree_mul_eq, degree_eq_zero_of_is_unit (is_unit_unit _), add_zero]

lemma prime_of_degree_eq_one (hp1 : degree p = 1) : prime p :=
have prime (normalize p),
  from prime_of_degree_eq_one_of_monic (hp1 ▸ degree_normalize)
    (monic_normalize (λ hp0, absurd hp1 (hp0.symm ▸ by simp; exact dec_trivial))),
prime_of_associated normalize_associated this

lemma irreducible_of_degree_eq_one (hp1 : degree p = 1) : irreducible p :=
irreducible_of_prime (prime_of_degree_eq_one hp1)

theorem pairwise_coprime_X_sub {α : Type u} [field α] {I : Type v}
  {s : I → α} (H : function.injective s) :
  pairwise (is_coprime on (λ i : I, polynomial.X - polynomial.C (s i))) :=
λ i j hij, have h : s j - s i ≠ 0, from sub_ne_zero_of_ne $ function.injective.ne H hij.symm,
⟨polynomial.C (s j - s i)⁻¹, -polynomial.C (s j - s i)⁻¹,
by rw [neg_mul_eq_neg_mul_symm, ← sub_eq_add_neg, ← mul_sub, sub_sub_sub_cancel_left,
    ← polynomial.C_sub, ← polynomial.C_mul, inv_mul_cancel h, polynomial.C_1]⟩

end field

section derivative
variables [semiring R]

/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative (p : polynomial R) : polynomial R := p.sum (λn a, C (a * n) * X^(n - 1))

lemma coeff_derivative (p : polynomial R) (n : ℕ) :
  coeff (derivative p) n = coeff p (n + 1) * (n + 1) :=
begin
  rw [derivative],
  simp only [coeff_X_pow, coeff_sum, coeff_C_mul],
  rw [finsupp.sum, finset.sum_eq_single (n + 1), apply_eq_coeff],
  { rw [if_pos (nat.add_sub_cancel _ _).symm, mul_one, nat.cast_add, nat.cast_one] },
  { assume b, cases b,
    { intros, rw [nat.cast_zero, mul_zero, zero_mul] },
    { intros _ H, rw [nat.succ_sub_one b, if_neg (mt (congr_arg nat.succ) H.symm), mul_zero] } },
  { intro H, rw [not_mem_support_iff.1 H, zero_mul, zero_mul] }
end

@[simp] lemma derivative_zero : derivative (0 : polynomial R) = 0 :=
finsupp.sum_zero_index

lemma derivative_monomial (a : R) (n : ℕ) : derivative (C a * X ^ n) = C (a * n) * X^(n - 1) :=
by rw [← single_eq_C_mul_X, ← single_eq_C_mul_X, derivative, sum_single_index, single_eq_C_mul_X];
  simp only [zero_mul, C_0]; refl

@[simp] lemma derivative_C {a : R} : derivative (C a) = 0 :=
suffices derivative (C a * X^0) = C (a * 0:R) * X ^ 0,
  by simpa only [mul_one, zero_mul, C_0, mul_zero, pow_zero],
derivative_monomial a 0

@[simp] lemma derivative_X : derivative (X : polynomial R) = 1 :=
by simpa only [mul_one, one_mul, C_1, pow_one, nat.cast_one, pow_zero]
  using derivative_monomial (1:R) 1

@[simp] lemma derivative_one : derivative (1 : polynomial R) = 0 :=
derivative_C

@[simp] lemma derivative_add {f g : polynomial R} :
  derivative (f + g) = derivative f + derivative g :=
by refine finsupp.sum_add_index _ _; intros;
simp only [add_mul, zero_mul, C_0, C_add, C_mul]

/-- The formal derivative of polynomials, as additive homomorphism. -/
def derivative_hom (R : Type*) [semiring R] : polynomial R →+ polynomial R :=
{ to_fun := derivative,
  map_zero' := derivative_zero,
  map_add' := λ p q, derivative_add }

@[simp] lemma derivative_neg {R : Type*} [ring R] (f : polynomial R) :
  derivative (-f) = -derivative f :=
(derivative_hom R).map_neg f

@[simp] lemma derivative_sub {R : Type*} [ring R] (f g : polynomial R) :
  derivative (f - g) = derivative f - derivative g :=
(derivative_hom R).map_sub f g

instance : is_add_monoid_hom (derivative : polynomial R → polynomial R) :=
(derivative_hom R).is_add_monoid_hom

@[simp] lemma derivative_sum {s : finset ι} {f : ι → polynomial R} :
  derivative (∑ b in s, f b) = ∑ b in s, derivative (f b) :=
(derivative_hom R).map_sum f s

@[simp] lemma derivative_smul (r : R) (p : polynomial R) : derivative (r • p) = r • derivative p :=
by { ext, simp only [coeff_derivative, mul_assoc, coeff_smul], }

end derivative

section derivative
variables [comm_semiring R]

@[simp] lemma derivative_mul {f g : polynomial R} :
  derivative (f * g) = derivative f * g + f * derivative g :=
calc derivative (f * g) = f.sum (λn a, g.sum (λm b, C ((a * b) * (n + m : ℕ)) * X^((n + m) - 1))) :
  begin
    transitivity, exact derivative_sum,
    transitivity, { apply finset.sum_congr rfl, assume x hx, exact derivative_sum },
    apply finset.sum_congr rfl, assume n hn, apply finset.sum_congr rfl, assume m hm,
    transitivity,
    { apply congr_arg, exact single_eq_C_mul_X },
    exact derivative_monomial _ _
  end
  ... = f.sum (λn a, g.sum (λm b,
      (C (a * n) * X^(n - 1)) * (C b * X^m) + (C a * X^n) * (C (b * m) * X^(m - 1)))) :
    sum_congr rfl $ assume n hn, sum_congr rfl $ assume m hm,
      by simp only [nat.cast_add, mul_add, add_mul, C_add, C_mul];
      cases n; simp only [nat.succ_sub_succ, pow_zero];
      cases m; simp only [nat.cast_zero, C_0, nat.succ_sub_succ, zero_mul, mul_zero,
        nat.sub_zero, pow_zero, pow_add, one_mul, pow_succ, mul_comm, mul_left_comm]
  ... = derivative f * g + f * derivative g :
    begin
      conv { to_rhs, congr,
        { rw [← sum_C_mul_X_eq g] },
        { rw [← sum_C_mul_X_eq f] } },
      unfold derivative finsupp.sum,
      simp only [sum_add_distrib, finset.mul_sum, finset.sum_mul]
    end

lemma derivative_eval (p : polynomial R) (x : R) :
  p.derivative.eval x = p.sum (λ n a, (a * n)*x^(n-1)) :=
by simp [derivative, eval_sum, eval_pow, -alg_hom.map_nat_cast]

theorem derivative_pow_succ (p : polynomial R) (n : ℕ) :
  (p ^ (n + 1)).derivative = (n + 1) * (p ^ n) * p.derivative :=
nat.rec_on n (by rw [pow_one, nat.cast_zero, zero_add, one_mul, pow_zero, one_mul]) $ λ n ih,
by rw [pow_succ', derivative_mul, ih, mul_right_comm, ← add_mul,
    add_mul (n.succ : polynomial R), one_mul, pow_succ', mul_assoc, n.cast_succ]

theorem derivative_pow (p : polynomial R) (n : ℕ) :
  (p ^ n).derivative = n * (p ^ (n - 1)) * p.derivative :=
nat.cases_on n (by rw [pow_zero, derivative_one, nat.cast_zero, zero_mul, zero_mul]) $ λ n,
by rw [p.derivative_pow_succ n, n.succ_sub_one, n.cast_succ]

theorem derivative_map [comm_semiring S] (p : polynomial R) (f : R →+* S) :
  (p.map f).derivative = p.derivative.map f :=
polynomial.induction_on p
  (λ r, by rw [map_C, derivative_C, derivative_C, map_zero])
  (λ p q ihp ihq, by rw [map_add, derivative_add, ihp, ihq, derivative_add, map_add])
  (λ n r ih, by rw [map_mul, map_C, map_pow, map_X,
      derivative_mul, derivative_pow_succ, derivative_C, zero_mul, zero_add, derivative_X, mul_one,
      derivative_mul, derivative_pow_succ, derivative_C, zero_mul, zero_add, derivative_X, mul_one,
      map_mul, map_C, map_mul, map_pow, map_add, map_nat_cast, map_one, map_X])

/-- Chain rule for formal derivative of polynomials. -/
theorem derivative_eval₂_C (p q : polynomial R) :
  (p.eval₂ C q).derivative = p.derivative.eval₂ C q * q.derivative :=
polynomial.induction_on p
  (λ r, by rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
  (λ p₁ p₂ ih₁ ih₂, by rw [eval₂_add, derivative_add, ih₁, ih₂, derivative_add, eval₂_add, add_mul])
  (λ n r ih, by rw [pow_succ', ← mul_assoc, eval₂_mul, eval₂_X, derivative_mul, ih,
      @derivative_mul _ _ _ X, derivative_X, mul_one, eval₂_add, @eval₂_mul _ _ _ _ X, eval₂_X,
      add_mul, mul_right_comm])

theorem of_mem_support_derivative {p : polynomial R} {n : ℕ} (h : n ∈ p.derivative.support) :
  n + 1 ∈ p.support :=
finsupp.mem_support_iff.2 $ λ (h1 : p.coeff (n+1) = 0), finsupp.mem_support_iff.1 h $
show p.derivative.coeff n = 0, by rw [coeff_derivative, h1, zero_mul]

theorem degree_derivative_lt {p : polynomial R} (hp : p ≠ 0) : p.derivative.degree < p.degree :=
(finset.sup_lt_iff $ bot_lt_iff_ne_bot.2 $ mt degree_eq_bot.1 hp).2 $ λ n hp, lt_of_lt_of_le
(with_bot.some_lt_some.2 n.lt_succ_self) $ finset.le_sup $ of_mem_support_derivative hp

theorem nat_degree_derivative_lt {p : polynomial R} (hp : p.derivative ≠ 0) :
  p.derivative.nat_degree < p.nat_degree :=
have hp1 : p ≠ 0, from λ h, hp $ by rw [h, derivative_zero],
with_bot.some_lt_some.1 $ by { rw [nat_degree, option.get_or_else_of_ne_none $ mt degree_eq_bot.1 hp,
  nat_degree, option.get_or_else_of_ne_none $ mt degree_eq_bot.1 hp1], exact degree_derivative_lt hp1 }

theorem degree_derivative_le {p : polynomial R} : p.derivative.degree ≤ p.degree :=
if H : p = 0 then le_of_eq $ by rw [H, derivative_zero] else le_of_lt $ degree_derivative_lt H

/-- The formal derivative of polynomials, as linear homomorphism. -/
def derivative_lhom (R : Type*) [comm_ring R] : polynomial R →ₗ[R] polynomial R :=
{ to_fun    := derivative,
  map_add'  := λ p q, derivative_add,
  map_smul' := λ r p, derivative_smul r p }

/-- If `f` is a polynomial over a field, and `a : K` satisfies `f' a ≠ 0`,
then `f / (X - a)` is coprime with `X - a`.
Note that we do not assume `f a = 0`, because `f / (X - a) = (f - f a) / (X - a)`. -/
lemma is_coprime_of_is_root_of_eval_derivative_ne_zero {K : Type*} [field K]
  (f : polynomial K) (a : K) (hf' : f.derivative.eval a ≠ 0) :
  is_coprime (X - C a : polynomial K) (f /ₘ (X - C a)) :=
begin
  refine or.resolve_left (dvd_or_coprime (X - C a) (f /ₘ (X - C a))
    (irreducible_of_degree_eq_one (polynomial.degree_X_sub_C a))) _,
  contrapose! hf' with h,
  have key : (X - C a) * (f /ₘ (X - C a)) = f - (f %ₘ (X - C a)),
  { rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', mod_by_monic_eq_sub_mul_div],
    exact monic_X_sub_C a },
  replace key := congr_arg derivative key,
  simp only [derivative_X, derivative_mul, one_mul, sub_zero, derivative_sub,
    mod_by_monic_X_sub_C_eq_C_eval, derivative_C] at key,
  have : (X - C a) ∣ derivative f := key ▸ (dvd_add h (dvd_mul_right _ _)),
  rw [← dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _), mod_by_monic_X_sub_C_eq_C_eval] at this,
  rw [← C_inj, this, C_0],
end

end derivative

section domain
variables [integral_domain R]

lemma mem_support_derivative [char_zero R] (p : polynomial R) (n : ℕ) :
  n ∈ (derivative p).support ↔ n + 1 ∈ p.support :=
suffices (¬(coeff p (n + 1) = 0 ∨ ((n + 1:ℕ) : R) = 0)) ↔ coeff p (n + 1) ≠ 0,
  by simpa only [coeff_derivative, apply_eq_coeff, mem_support_iff, ne.def, mul_eq_zero],
by rw [nat.cast_eq_zero]; simp only [nat.succ_ne_zero, or_false]

@[simp] lemma degree_derivative_eq [char_zero R] (p : polynomial R) (hp : 0 < nat_degree p) :
  degree (derivative p) = (nat_degree p - 1 : ℕ) :=
le_antisymm
  (le_trans (degree_sum_le _ _) $ sup_le $ assume n hn,
    have n ≤ nat_degree p, begin
      rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree],
      { refine le_degree_of_ne_zero _, simpa only [mem_support_iff] using hn },
      { assume h, simpa only [h, support_zero] using hn }
    end,
    le_trans (degree_monomial_le _ _) $ with_bot.coe_le_coe.2 $ nat.sub_le_sub_right this _)
  begin
    refine le_sup _,
    rw [mem_support_derivative, nat.sub_add_cancel, mem_support_iff],
    { show ¬ leading_coeff p = 0,
      rw [leading_coeff_eq_zero],
      assume h, rw [h, nat_degree_zero] at hp,
      exact lt_irrefl 0 (lt_of_le_of_lt (zero_le _) hp), },
    exact hp
  end

end domain

section identities

/- @TODO: pow_add_expansion and pow_sub_pow_factor are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring

Maybe use data.nat.choose to prove it.
 -/

def pow_add_expansion {R : Type*} [comm_semiring R] (x y : R) : ∀ (n : ℕ),
  {k // (x + y)^n = x^n + n*x^(n-1)*y + k * y^2}
| 0 := ⟨0, by simp⟩
| 1 := ⟨0, by simp⟩
| (n+2) :=
  begin
    cases pow_add_expansion (n+1) with z hz,
    existsi x*z + (n+1)*x^n+z*y,
    calc (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) : by ring_exp
    ... = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) : by rw hz
    ... = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x*z + (n+1)*x^n+z*y) * y ^ 2 :
      by { push_cast, ring_exp! }
  end

variables [comm_ring R]

private def poly_binom_aux1 (x y : R) (e : ℕ) (a : R) :
  {k : R // a * (x + y)^e = a * (x^e + e*x^(e-1)*y + k*y^2)} :=
begin
  existsi (pow_add_expansion x y e).val,
  congr,
  apply (pow_add_expansion _ _ _).property
end

private lemma poly_binom_aux2 (f : polynomial R) (x y : R) :
  f.eval (x + y) = f.sum (λ e a, a * (x^e + e*x^(e-1)*y + (poly_binom_aux1 x y e a).val*y^2)) :=
begin
  unfold eval eval₂, congr, ext,
  apply (poly_binom_aux1 x y _ _).property
end

private lemma poly_binom_aux3 (f : polynomial R) (x y : R) : f.eval (x + y) =
  f.sum (λ e a, a * x^e) +
  f.sum (λ e a, (a * e * x^(e-1)) * y) +
  f.sum (λ e a, (a *(poly_binom_aux1 x y e a).val)*y^2) :=
by rw poly_binom_aux2; simp [left_distrib, finsupp.sum_add, mul_assoc]

def binom_expansion (f : polynomial R) (x y : R) :
  {k : R // f.eval (x + y) = f.eval x + (f.derivative.eval x) * y + k * y^2} :=
begin
  existsi f.sum (λ e a, a *((poly_binom_aux1 x y e a).val)),
  rw poly_binom_aux3,
  congr,
  { rw derivative_eval, symmetry,
    apply finsupp.sum_mul },
  { symmetry, apply finsupp.sum_mul }
end

def pow_sub_pow_factor (x y : R) : Π (i : ℕ), {z : R // x^i - y^i = z * (x - y)}
| 0 := ⟨0, by simp⟩
| 1 := ⟨1, by simp⟩
| (k+2) :=
  begin
    cases @pow_sub_pow_factor (k+1) with z hz,
    existsi z*x + y^(k+1),
    calc x ^ (k + 2) - y ^ (k + 2)
        = x * (x ^ (k + 1) - y ^ (k + 1)) + (x * y ^ (k + 1) - y ^ (k + 2)) : by ring_exp
    ... = x * (z * (x - y)) + (x * y ^ (k + 1) - y ^ (k + 2)) : by rw hz
    ... = (z * x + y ^ (k + 1)) * (x - y) : by ring_exp
  end

def eval_sub_factor (f : polynomial R) (x y : R) :
  {z : R // f.eval x - f.eval y = z * (x - y)} :=
begin
  refine ⟨f.sum (λ i r, r * (pow_sub_pow_factor x y i).val), _⟩,
  delta eval eval₂,
  rw ← finsupp.sum_sub,
  rw finsupp.sum_mul,
  delta finsupp.sum,
  congr, ext i r, dsimp,
  rw [mul_assoc, ←(pow_sub_pow_factor x y _).prop, mul_sub],
end

end identities

section integral_normalization

section semiring
variables [semiring R]

/-- If `f : polynomial R` is a nonzero polynomial with root `z`, `integral_normalization f` is
a monic polynomial with root `leading_coeff f * z`.

Moreover, `integral_normalization 0 = 0`.
-/
noncomputable def integral_normalization (f : polynomial R) : polynomial R :=
on_finset f.support
  (λ i, if f.degree = i then 1 else coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i))
  begin
    intros i h,
    apply mem_support_iff.mpr,
    split_ifs at h with hi,
    { exact coeff_ne_zero_of_eq_degree hi },
    { exact left_ne_zero_of_mul h },
  end

lemma integral_normalization_coeff_degree {f : polynomial R} {i : ℕ} (hi : f.degree = i) :
  (integral_normalization f).coeff i = 1 :=
if_pos hi

lemma integral_normalization_coeff_nat_degree {f : polynomial R} (hf : f ≠ 0) :
  (integral_normalization f).coeff (nat_degree f) = 1 :=
integral_normalization_coeff_degree (degree_eq_nat_degree hf)

lemma integral_normalization_coeff_ne_degree {f : polynomial R} {i : ℕ} (hi : f.degree ≠ i) :
  coeff (integral_normalization f) i = coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i) :=
if_neg hi

lemma integral_normalization_coeff_ne_nat_degree {f : polynomial R} {i : ℕ} (hi : i ≠ nat_degree f) :
  coeff (integral_normalization f) i = coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i) :=
integral_normalization_coeff_ne_degree (degree_ne_of_nat_degree_ne hi.symm)

lemma monic_integral_normalization {f : polynomial R} (hf : f ≠ 0) :
  monic (integral_normalization f) :=
begin
  apply monic_of_degree_le f.nat_degree,
  { refine finset.sup_le (λ i h, _),
    rw [integral_normalization, mem_support_iff, on_finset_apply] at h,
    split_ifs at h with hi,
    { exact le_trans (le_of_eq hi.symm) degree_le_nat_degree },
    { erw [with_bot.some_le_some],
      apply le_nat_degree_of_ne_zero,
      exact left_ne_zero_of_mul h } },
  { exact integral_normalization_coeff_nat_degree hf }
end

end semiring

variables [integral_domain R]

@[simp] lemma support_integral_normalization {f : polynomial R} (hf : f ≠ 0) :
  (integral_normalization f).support = f.support :=
begin
  ext i,
  simp only [integral_normalization, on_finset_apply, mem_support_iff],
  split_ifs with hi,
  { simp only [ne.def, not_false_iff, true_iff, one_ne_zero, hi],
    exact coeff_ne_zero_of_eq_degree hi },
  split,
  { intro h,
    exact left_ne_zero_of_mul h },
  { intro h,
    refine mul_ne_zero h (pow_ne_zero _ _),
    exact λ h, hf (leading_coeff_eq_zero.mp h) }
end

variables [comm_ring S]

lemma integral_normalization_eval₂_eq_zero {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  eval₂ f (z * f p.leading_coeff) (integral_normalization p) = 0 :=
calc eval₂ f (z * f p.leading_coeff) (integral_normalization p)
    = p.support.attach.sum
        (λ i, f (coeff (integral_normalization p) i.1 * p.leading_coeff ^ i.1) * z ^ i.1) :
      by { rw [eval₂, finsupp.sum, support_integral_normalization hp],
           simp only [mul_comm z, mul_pow, mul_assoc, ring_hom.map_pow, ring_hom.map_mul],
           exact finset.sum_attach.symm }
... = p.support.attach.sum
        (λ i, f (coeff p i.1 * p.leading_coeff ^ (nat_degree p - 1)) * z ^ i.1) :
      begin
        have one_le_deg : 1 ≤ nat_degree p :=
          nat.succ_le_of_lt (nat_degree_pos_of_eval₂_root hp f hz inj),
        congr,
        ext i,
        congr' 2,
        by_cases hi : i.1 = nat_degree p,
        { rw [hi, integral_normalization_coeff_degree, one_mul, leading_coeff, ←pow_succ,
              nat.sub_add_cancel one_le_deg],
          exact degree_eq_nat_degree hp },
        { have : i.1 ≤ p.nat_degree - 1 := nat.le_pred_of_lt (lt_of_le_of_ne
            (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.mp i.2)) hi),
          rw [integral_normalization_coeff_ne_nat_degree hi, mul_assoc, ←pow_add,
              nat.sub_add_cancel this] }
      end
... = f p.leading_coeff ^ (nat_degree p - 1) * eval₂ f z p :
      by { simp_rw [eval₂, finsupp.sum, λ i, mul_comm (coeff p i), ring_hom.map_mul,
                    ring_hom.map_pow, mul_assoc, ←finset.mul_sum],
           congr' 1,
           exact @finset.sum_attach _ _ p.support _ (λ i, f (p.coeff i) * z ^ i) }
... = 0 : by rw [hz, _root_.mul_zero]

lemma integral_normalization_aeval_eq_zero [algebra R S] {f : polynomial R} (hf : f ≠ 0)
  {z : S} (hz : aeval R S z f = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  aeval R S (z * algebra_map R S f.leading_coeff) (integral_normalization f) = 0 :=
integral_normalization_eval₂_eq_zero hf (algebra_map R S) hz inj

end integral_normalization

end polynomial

namespace is_integral_domain

variables {R : Type*} [comm_ring R]

/-- Lift evidence that `is_integral_domain R` to `is_integral_domain (polynomial R)`. -/
lemma polynomial (h : is_integral_domain R) : is_integral_domain (polynomial R) :=
@integral_domain.to_is_integral_domain _ (@polynomial.integral_domain _ (h.to_integral_domain _))

end is_integral_domain
