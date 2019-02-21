/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Jens Wagemaker

Theory of univariate polynomials, represented as `ℕ →₀ α`, where α is a commutative semiring.
-/
import data.finsupp algebra.gcd_domain ring_theory.euclidean_domain tactic.ring ring_theory.multiplicity

/-- `polynomial α` is the type of univariate polynomials over `α`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from α is called `C`. -/
def polynomial (α : Type*) [comm_semiring α] := ℕ →₀ α

open finsupp finset lattice

namespace polynomial
universes u v
variables {α : Type u} {β : Type v} {a b : α} {m n : ℕ}

section comm_semiring
variables [comm_semiring α] [decidable_eq α] {p q r : polynomial α}

instance : has_zero (polynomial α) := finsupp.has_zero
instance : has_one (polynomial α) := finsupp.has_one
instance : has_add (polynomial α) := finsupp.has_add
instance : has_mul (polynomial α) := finsupp.has_mul
instance : comm_semiring (polynomial α) := finsupp.to_comm_semiring
instance : decidable_eq (polynomial α) := finsupp.decidable_eq

def polynomial.has_coe_to_fun : has_coe_to_fun (polynomial α) :=
finsupp.has_coe_to_fun

local attribute [instance] finsupp.to_comm_semiring polynomial.has_coe_to_fun

@[simp] lemma support_zero : (0 : polynomial α).support = ∅ := rfl

/-- `C a` is the constant polynomial `a`. -/
def C (a : α) : polynomial α := single 0 a

/-- `X` is the polynomial variable (aka indeterminant). -/
def X : polynomial α := single 1 1

/-- coeff p n is the coefficient of X^n in p -/
def coeff (p : polynomial α) := p.to_fun

instance [has_repr α] : has_repr (polynomial α) :=
⟨λ p, if p = 0 then "0"
  else (p.support.sort (≤)).foldr
    (λ n a, a ++ (if a = "" then "" else " + ") ++
      if n = 0
        then "C (" ++ repr (coeff p n) ++ ")"
        else if n = 1
          then if (coeff p n) = 1 then "X" else "C (" ++ repr (coeff p n) ++ ") * X"
          else if (coeff p n) = 1 then "X ^ " ++ repr n
            else "C (" ++ repr (coeff p n) ++ ") * X ^ " ++ repr n) ""⟩

theorem ext {p q : polynomial α} : p = q ↔ ∀ n, coeff p n = coeff q n :=
⟨λ h n, h ▸ rfl, finsupp.ext⟩

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : polynomial α) : with_bot ℕ := p.support.sup some

def degree_lt_wf : well_founded (λp q : polynomial α, degree p < degree q) :=
inv_image.wf degree (with_bot.well_founded_lt nat.lt_wf)

/-- `nat_degree p` forces `degree p` to ℕ, by defining nat_degree 0 = 0. -/
def nat_degree (p : polynomial α) : ℕ := (degree p).get_or_else 0

lemma single_eq_C_mul_X : ∀{n}, single n a = C a * X^n
| 0     := (mul_one _).symm
| (n+1) :=
  calc single (n + 1) a = single n a * X : by rw [X, single_mul_single, mul_one]
    ... = (C a * X^n) * X : by rw [single_eq_C_mul_X]
    ... = C a * X^(n+1) : by simp only [pow_add, mul_assoc, pow_one]

lemma sum_C_mul_X_eq (p : polynomial α) : p.sum (λn a, C a * X^n) = p :=
eq.trans (sum_congr rfl $ assume n hn, single_eq_C_mul_X.symm) (finsupp.sum_single _)


@[elab_as_eliminator] protected lemma induction_on {M : polynomial α → Prop} (p : polynomial α)
  (h_C : ∀a, M (C a))
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : α), M (C a * X^n) → M (C a * X^(n+1))) :
  M p :=
have ∀{n:ℕ} {a}, M (C a * X^n),
begin
  assume n a,
  induction n with n ih,
  { simp only [pow_zero, mul_one, h_C] },
  { exact h_monomial _ _ ih }
end,
finsupp.induction p
  (suffices M (C 0), by simpa only [C, single_zero],
    h_C 0)
  (assume n a p _ _ hp, suffices M (C a * X^n + p), by rwa [single_eq_C_mul_X],
    h_add _ _ this hp)

@[simp] lemma C_0 : C (0 : α) = 0 := single_zero

@[simp] lemma C_1 : C (1 : α) = 1 := rfl

@[simp] lemma C_mul : C (a * b) = C a * C b :=
(@single_mul_single _ _ _ _ _ _ 0 0 a b).symm

@[simp] lemma C_add : C (a + b) = C a + C b := finsupp.single_add

instance C.is_semiring_hom : is_semiring_hom (C : α → polynomial α) :=
⟨C_0, C_1, λ _ _, C_add, λ _ _, C_mul⟩

@[simp] lemma C_pow : C (a ^ n) = C a ^ n := is_semiring_hom.map_pow _ _ _

section coeff

lemma apply_eq_coeff : p n = coeff p n := rfl

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : polynomial α) n = 0 := rfl

@[simp] lemma coeff_one_zero (n : ℕ) : coeff (1 : polynomial α) 0 = 1 := rfl

@[simp] lemma coeff_add (p q : polynomial α) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := rfl

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
by simp [coeff, eq_comm, C, single]; congr

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := rfl

@[simp] lemma coeff_X_one : coeff (X : polynomial α) 1 = 1 := rfl

@[simp] lemma coeff_X_zero : coeff (X : polynomial α) 0 = 0 := rfl

lemma coeff_X : coeff (X : polynomial α) n = if 1 = n then 1 else 0 := rfl

@[simp] lemma coeff_C_mul_X (x : α) (k n : ℕ) :
  coeff (C x * X^k : polynomial α) n = if n = k then x else 0 :=
by rw [← single_eq_C_mul_X]; simp [single, eq_comm, coeff]; congr

lemma coeff_sum [comm_semiring β] [decidable_eq β] (n : ℕ) (f : ℕ → α → polynomial β) :
  coeff (p.sum f) n = p.sum (λ a b, coeff (f a b) n) := finsupp.sum_apply

lemma coeff_single : coeff (single n a) m = if n = m then a else 0 := rfl

@[simp] lemma coeff_C_mul (p : polynomial α) : coeff (C a * p) n = a * coeff p n :=
begin
  conv in (a * _) { rw [← @sum_single _ _ _ _ _ p, coeff_sum] },
  rw [mul_def, C, sum_single_index],
  { simp [coeff_single, finsupp.mul_sum, coeff_sum],
    apply sum_congr rfl,
    assume i hi, by_cases i = n; simp [h] },
  simp
end

@[simp] lemma coeff_one (n : ℕ) :
  coeff (1 : polynomial α) n = if 0 = n then 1 else 0 := rfl

@[simp] lemma coeff_X_pow (k n : ℕ) :
  coeff (X^k : polynomial α) n = if n = k then 1 else 0 :=
by simpa only [C_1, one_mul] using coeff_C_mul_X (1:α) k n

lemma coeff_mul_left (p q : polynomial α) (n : ℕ) :
  coeff (p * q) n = (range (n+1)).sum (λ k, coeff p k * coeff q (n-k)) :=
have hite : ∀ a : ℕ × ℕ, ite (a.1 + a.2 = n) (coeff p (a.fst) * coeff q (a.snd)) 0 ≠ 0
    → a.1 + a.2 = n, from λ a ha, by_contradiction
  (λ h, absurd (eq.refl (0 : α)) (by rwa if_neg h at ha)),
calc coeff (p * q) n = sum (p.support) (λ a, sum (q.support)
    (λ b, ite (a + b = n) (coeff p a * coeff q b) 0)) :
  by simp only [finsupp.mul_def, coeff_sum, coeff_single]; refl
... = (p.support.product q.support).sum
    (λ v : ℕ × ℕ, ite (v.1 + v.2 = n) (coeff p v.1 * coeff q v.2) 0) :
  by rw sum_product
... = (range (n+1)).sum (λ k, coeff p k * coeff q (n-k)) :
  sum_bij_ne_zero (λ a _ _, a.1)
  (λ a _ ha, mem_range.2 (nat.lt_succ_of_le (hite a ha ▸ le_add_right (le_refl _))))
  (λ a₁ a₂ _ h₁ _ h₂ h, prod.ext h
    ((add_left_inj a₁.1).1 (by rw [hite a₁ h₁, h, hite a₂ h₂])))
  (λ a h₁ h₂, ⟨(a, n - a), mem_product.2
      ⟨mem_support_iff.2 (ne_zero_of_mul_ne_zero_right h₂),
      mem_support_iff.2 (ne_zero_of_mul_ne_zero_left h₂)⟩,
    by simpa [nat.add_sub_cancel' (nat.le_of_lt_succ (mem_range.1 h₁))],
    rfl⟩)
  (λ a _ ha, by rw [← hite a ha, if_pos rfl, nat.add_sub_cancel_left])

lemma coeff_mul_right (p q : polynomial α) (n : ℕ) :
  coeff (p * q) n = (range (n+1)).sum (λ k, coeff p (n-k) * coeff q k) :=
by rw [mul_comm, coeff_mul_left]; simp only [mul_comm]

theorem coeff_mul_X_pow (p : polynomial α) (n d : ℕ) :
  coeff (p * polynomial.X ^ n) (d + n) = coeff p d :=
begin
  rw [coeff_mul_right, sum_eq_single n, coeff_X_pow, if_pos rfl, mul_one, nat.add_sub_cancel],
  { intros b h1 h2, rw [coeff_X_pow, if_neg h2, mul_zero] },
  { exact λ h1, (h1 (mem_range.2 (nat.le_add_left _ _))).elim }
end

theorem coeff_mul_X (p : polynomial α) (n : ℕ) :
  coeff (p * X) (n + 1) = coeff p n :=
by simpa only [pow_one] using coeff_mul_X_pow p 1 n

theorem mul_X_pow_eq_zero {p : polynomial α} {n : ℕ}
  (H : p * X ^ n = 0) : p = 0 :=
ext.2 $ λ k, (coeff_mul_X_pow p n k).symm.trans $ ext.1 H (k+n)

end coeff

lemma C_inj : C a = C b ↔ a = b :=
⟨λ h, coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

section eval₂
variables [semiring β]
variables (f : α → β) (x : β)
open is_semiring_hom

/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
def eval₂ (p : polynomial α) : β :=
p.sum (λ e a, f a * x ^ e)

variables [is_semiring_hom f]

@[simp] lemma eval₂_C : (C a).eval₂ f x = f a :=
(sum_single_index $ by rw [map_zero f, zero_mul]).trans $ by rw [pow_zero, mul_one]

@[simp] lemma eval₂_X : X.eval₂ f x = x :=
(sum_single_index $ by rw [map_zero f, zero_mul]).trans $ by rw [map_one f, one_mul, pow_one]

@[simp] lemma eval₂_zero : (0 : polynomial α).eval₂ f x = 0 :=
finsupp.sum_zero_index

@[simp] lemma eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x :=
finsupp.sum_add_index
  (λ _, by rw [map_zero f, zero_mul])
  (λ _ _ _, by rw [map_add f, add_mul])

@[simp] lemma eval₂_one : (1 : polynomial α).eval₂ f x = 1 :=
by rw [← C_1, eval₂_C, map_one f]

instance eval₂.is_add_monoid_hom : is_add_monoid_hom (eval₂ f x) :=
⟨eval₂_zero _ _, λ _ _, eval₂_add _ _⟩

end eval₂

section eval₂
variables [comm_semiring β]
variables (f : α → β) [is_semiring_hom f] (x : β)
open is_semiring_hom

@[simp] lemma eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x :=
begin
  dunfold eval₂,
  rw [mul_def, finsupp.sum_mul _ p], simp only [finsupp.mul_sum _ q], rw [sum_sum_index],
  { apply sum_congr rfl, assume i hi, dsimp only, rw [sum_sum_index],
    { apply sum_congr rfl, assume j hj, dsimp only,
      rw [sum_single_index, map_mul f, pow_add],
      { simp only [mul_assoc, mul_left_comm] },
      { rw [map_zero f, zero_mul] } },
    { intro, rw [map_zero f, zero_mul] },
    { intros, rw [map_add f, add_mul] } },
  { intro, rw [map_zero f, zero_mul] },
  { intros, rw [map_add f, add_mul] }
end

instance eval₂.is_semiring_hom : is_semiring_hom (eval₂ f x) :=
⟨eval₂_zero _ _, eval₂_one _ _, λ _ _, eval₂_add _ _, λ _ _, eval₂_mul _ _⟩

lemma eval₂_pow (n : ℕ) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n := map_pow _ _ _

lemma eval₂_sum (p : polynomial α) (g : ℕ → α → polynomial α) (x : β) :
  (p.sum g).eval₂ f x = p.sum (λ n a, (g n a).eval₂ f x) :=
finsupp.sum_sum_index (by simp [is_add_monoid_hom.map_zero f])
  (by intros; simp [right_distrib, is_add_monoid_hom.map_add f])

end eval₂

section eval
variable {x : α}

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : α → polynomial α → α := eval₂ id

@[simp] lemma eval_C : (C a).eval x = a := eval₂_C _ _

@[simp] lemma eval_X : X.eval x = x := eval₂_X _ _

@[simp] lemma eval_zero : (0 : polynomial α).eval x = 0 :=  eval₂_zero _ _

@[simp] lemma eval_add : (p + q).eval x = p.eval x + q.eval x := eval₂_add _ _

@[simp] lemma eval_one : (1 : polynomial α).eval x = 1 := eval₂_one _ _

@[simp] lemma eval_mul : (p * q).eval x = p.eval x * q.eval x := eval₂_mul _ _

instance eval.is_semiring_hom : is_semiring_hom (eval x) := eval₂.is_semiring_hom _ _

@[simp] lemma eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n := eval₂_pow _ _ _

lemma eval_sum (p : polynomial α) (f : ℕ → α → polynomial α) (x : α) :
  (p.sum f).eval x = p.sum (λ n a, (f n a).eval x) :=
eval₂_sum _ _ _ _

lemma eval₂_hom [comm_semiring β] (f : α → β) [is_semiring_hom f] (x : α) :
  p.eval₂ f (f x) = f (p.eval x) :=
polynomial.induction_on p
  (by simp)
  (by simp [is_semiring_hom.map_add f] {contextual := tt})
  (by simp [is_semiring_hom.map_mul f, eval_pow,
    is_semiring_hom.map_pow f, pow_succ', (mul_assoc _ _ _).symm] {contextual := tt})

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : polynomial α) (a : α) : Prop := p.eval a = 0

instance : decidable (is_root p a) := by unfold is_root; apply_instance

@[simp] lemma is_root.def : is_root p a ↔ p.eval a = 0 := iff.rfl

lemma root_mul_left_of_is_root (p : polynomial α) {q : polynomial α} :
  is_root q a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, mul_zero]

lemma root_mul_right_of_is_root {p : polynomial α} (q : polynomial α) :
  is_root p a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, zero_mul]

lemma coeff_zero_eq_eval_zero (p : polynomial α) :
  coeff p 0 = p.eval 0 :=
calc coeff p 0 = coeff p 0 * 0 ^ 0 : by simp
... = p.eval 0 : eq.symm $
  finset.sum_eq_single _ (λ b _ hb, by simp [zero_pow (nat.pos_of_ne_zero hb)]) (by simp)

end eval

section comp

def comp (p q : polynomial α) : polynomial α := p.eval₂ C q

lemma eval₂_comp [comm_semiring β] (f : α → β) [is_semiring_hom f] {x : β} :
  (p.comp q).eval₂ f x = p.eval₂ f (q.eval₂ f x) :=
show (p.sum (λ e a, C a * q ^ e)).eval₂ f x = p.eval₂ f (eval₂ f x q),
by simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_sum]; refl

lemma eval_comp : (p.comp q).eval a = p.eval (q.eval a) := eval₂_comp _

@[simp] lemma comp_X : p.comp X = p :=
begin
  refine polynomial.ext.2 (λ n, _),
  rw [comp, eval₂],
  conv in (C _ * _) { rw ← single_eq_C_mul_X },
  rw finsupp.sum_single
end

@[simp] lemma X_comp : X.comp p = p := eval₂_X _ _

@[simp] lemma comp_C : p.comp (C a) = C (p.eval a) :=
begin
  dsimp [comp, eval₂, eval, finsupp.sum],
  rw [← sum_hom (@C α _ _)],
  apply finset.sum_congr rfl; simp
end

@[simp] lemma C_comp : (C a).comp p = C a := eval₂_C _ _

@[simp] lemma comp_zero : p.comp (0 : polynomial α) = C (p.eval 0) :=
by rw [← C_0, comp_C]

@[simp] lemma zero_comp : comp (0 : polynomial α) p = 0 :=
by rw [← C_0, C_comp]

@[simp] lemma comp_one : p.comp 1 = C (p.eval 1) :=
by rw [← C_1, comp_C]

@[simp] lemma one_comp : comp (1 : polynomial α) p = 1 :=
by rw [← C_1, C_comp]

instance : is_semiring_hom (λ q : polynomial α, q.comp p) :=
by unfold comp; apply_instance

@[simp] lemma add_comp : (p + q).comp r = p.comp r + q.comp r := eval₂_add _ _
@[simp] lemma mul_comp : (p * q).comp r = p.comp r * q.comp r := eval₂_mul _ _

end comp

section map
variables [comm_semiring β] [decidable_eq β]
variables (f : α → β)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : polynomial α → polynomial β := eval₂ (C ∘ f) X

variables [is_semiring_hom f]

@[simp] lemma map_C : (C a).map f = C (f a) := eval₂_C _ _

@[simp] lemma map_X : X.map f = X := eval₂_X _ _

@[simp] lemma map_zero : (0 : polynomial α).map f = 0 :=  eval₂_zero _ _

@[simp] lemma map_add : (p + q).map f = p.map f + q.map f := eval₂_add _ _

@[simp] lemma map_one : (1 : polynomial α).map f = 1 := eval₂_one _ _

@[simp] lemma map_mul : (p * q).map f = p.map f * q.map f := eval₂_mul _ _

instance map.is_semiring_hom : is_semiring_hom (map f) := eval₂.is_semiring_hom _ _

lemma map_pow (n : ℕ) : (p ^ n).map f = p.map f ^ n := eval₂_pow _ _ _

lemma coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) :=
begin
  rw [map, eval₂, coeff_sum],
  conv_rhs { rw [← sum_C_mul_X_eq p, coeff_sum, finsupp.sum,
    ← finset.sum_hom f], },
  refine finset.sum_congr rfl (λ x hx, _),
  simp [function.comp, coeff_C_mul_X, is_semiring_hom.map_mul f],
  split_ifs; simp [is_semiring_hom.map_zero f],
end

lemma map_map {γ : Type*} [comm_semiring γ] [decidable_eq γ] (g : β → γ) [is_semiring_hom g]
  (p : polynomial α) : (p.map f).map g = p.map (λ x, g (f x)) :=
polynomial.ext.2 (by simp [coeff_map])

lemma eval₂_map {γ : Type*} [comm_semiring γ] (g : β → γ) [is_semiring_hom g] (x : γ) :
  (p.map f).eval₂ g x = p.eval₂ (λ y, g (f y)) x :=
polynomial.induction_on p
  (by simp)
  (by simp [is_semiring_hom.map_add f] {contextual := tt})
  (by simp [is_semiring_hom.map_mul f,
    is_semiring_hom.map_pow f, pow_succ', (mul_assoc _ _ _).symm] {contextual := tt})

lemma eval_map (x : β) : (p.map f).eval x = p.eval₂ f x := eval₂_map _ _ _

@[simp] lemma map_id : p.map id = p := by simp [id, polynomial.ext, coeff_map]

end map

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leading_coeff (p : polynomial α) : α := coeff p (nat_degree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def monic (p : polynomial α) := leading_coeff p = (1 : α)

lemma monic.def : monic p ↔ leading_coeff p = 1 := iff.rfl

instance monic.decidable : decidable (monic p) :=
by unfold monic; apply_instance

@[simp] lemma degree_zero : degree (0 : polynomial α) = ⊥ := rfl

@[simp] lemma nat_degree_zero : nat_degree (0 : polynomial α) = 0 := rfl

@[simp] lemma degree_C (ha : a ≠ 0) : degree (C a) = (0 : with_bot ℕ) :=
show sup (ite (a = 0) ∅ {0}) some = 0, by rw if_neg ha; refl

lemma degree_C_le : degree (C a) ≤ (0 : with_bot ℕ) :=
by by_cases h : a = 0; [rw [h, C_0], rw [degree_C h]]; [exact bot_le, exact le_refl _]

lemma degree_one_le : degree (1 : polynomial α) ≤ (0 : with_bot ℕ) :=
by rw [← C_1]; exact degree_C_le

lemma degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
⟨λ h, by rw [degree, ← max_eq_sup_with_bot] at h;
  exact support_eq_empty.1 (max_eq_none.1 h),
λ h, h.symm ▸ rfl⟩

lemma degree_eq_nat_degree (hp : p ≠ 0) : degree p = (nat_degree p : with_bot ℕ) :=
let ⟨n, hn⟩ :=
  classical.not_forall.1 (mt option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp)) in
have hn : degree p = some n := not_not.1 hn,
by rw [nat_degree, hn]; refl

lemma nat_degree_eq_of_degree_eq_some {p : polynomial α} {n : ℕ}
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

lemma nat_degree_eq_of_degree_eq [comm_semiring β] [decidable_eq β] {q : polynomial β}
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

@[simp] lemma nat_degree_C (a : α) : nat_degree (C a) = 0 :=
begin
  by_cases ha : a = 0,
  { have : C a = 0, { rw [ha, C_0] },
    rw [nat_degree, degree_eq_bot.2 this],
    refl },
  { rw [nat_degree, degree_C ha], refl }
end

@[simp] lemma nat_degree_one : nat_degree (1 : polynomial α) = 0 := nat_degree_C 1

@[simp] lemma degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (C a * X ^ n) = n :=
by rw [← single_eq_C_mul_X, degree, support_single_ne_zero ha]; refl

lemma degree_monomial_le (n : ℕ) (a : α) : degree (C a * X ^ n) ≤ n :=
if h : a = 0 then by rw [h, C_0, zero_mul]; exact bot_le else le_of_eq (degree_monomial n h)

lemma coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

lemma coeff_nat_degree_eq_zero_of_degree_lt (h : degree p < degree q) : coeff p (nat_degree q) = 0 :=
coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_nat_degree)

lemma ne_zero_of_degree_gt {n : with_bot ℕ} (h : n < degree p) : p ≠ 0 :=
mt degree_eq_bot.2 (ne.symm (ne_of_lt (lt_of_le_of_lt bot_le h)))

lemma eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) :=
begin
  refine polynomial.ext.2 (λ n, _),
  cases n,
  { refl },
  { have : degree p < ↑(nat.succ n) := lt_of_le_of_lt h (with_bot.some_lt_some.2 (nat.succ_pos _)),
    rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt this] }
end

lemma eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
eq_C_of_degree_le_zero (h ▸ le_refl _)

lemma degree_add_le (p q : polynomial α) : degree (p + q) ≤ max (degree p) (degree q) :=
calc degree (p + q) = ((p + q).support).sup some : rfl
  ... ≤ (p.support ∪ q.support).sup some : sup_mono support_add
  ... = p.support.sup some ⊔ q.support.sup some : sup_union
  ... = _ : with_bot.sup_eq_max _ _

@[simp] lemma leading_coeff_zero : leading_coeff (0 : polynomial α) = 0 := rfl

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

lemma degree_erase_le (p : polynomial α) (n : ℕ) : degree (p.erase n) ≤ degree p :=
sup_mono (erase_subset _ _)

lemma degree_erase_lt (hp : p ≠ 0) : degree (p.erase (nat_degree p)) < degree p :=
lt_of_le_of_ne (degree_erase_le _ _) $
  (degree_eq_nat_degree hp).symm ▸ λ h, not_mem_erase _ _ (mem_of_max h)

lemma degree_sum_le [decidable_eq β] (s : finset β) (f : β → polynomial α) :
  degree (s.sum f) ≤ s.sup (λ b, degree (f b)) :=
finset.induction_on s (by simp only [sum_empty, sup_empty, degree_zero, le_refl]) $
  assume a s has ih,
  calc degree (sum (insert a s) f) ≤ max (degree (f a)) (degree (s.sum f)) :
    by rw sum_insert has; exact degree_add_le _ _
  ... ≤ _ : by rw [sup_insert, with_bot.sup_eq_max]; exact max_le_max (le_refl _) ih

lemma degree_mul_le (p q : polynomial α) : degree (p * q) ≤ degree p + degree q :=
calc degree (p * q) ≤ (p.support).sup (λi, degree (sum q (λj a, C (coeff p i * a) * X ^ (i + j)))) :
    by simp only [single_eq_C_mul_X.symm]; exact degree_sum_le _ _
  ... ≤ p.support.sup (λi, q.support.sup (λj, degree (C (coeff p i * coeff q j) * X ^ (i + j)))) :
    finset.sup_mono_fun (assume i hi,  degree_sum_le _ _)
  ... ≤ degree p + degree q :
    begin
      refine finset.sup_le (λ a ha, finset.sup_le (λ b hb, le_trans (degree_monomial_le _ _) _)),
      rw [with_bot.coe_add],
      rw mem_support_iff at ha hb,
      exact add_le_add' (le_degree_of_ne_zero ha) (le_degree_of_ne_zero hb)
    end

lemma degree_pow_le (p : polynomial α) : ∀ n, degree (p ^ n) ≤ add_monoid.smul n (degree p)
| 0     := by rw [pow_zero, add_monoid.zero_smul]; exact degree_one_le
| (n+1) := calc degree (p ^ (n + 1)) ≤ degree p + degree (p ^ n) :
    by rw pow_succ; exact degree_mul_le _ _
  ... ≤ _ : by rw succ_smul; exact add_le_add' (le_refl _) (degree_pow_le _)

@[simp] lemma leading_coeff_monomial (a : α) (n : ℕ) : leading_coeff (C a * X ^ n) = a :=
begin
  by_cases ha : a = 0,
  { simp only [ha, C_0, zero_mul, leading_coeff_zero] },
  { rw [leading_coeff, nat_degree, degree_monomial _ ha, ← single_eq_C_mul_X],
    exact @finsupp.single_eq_same _ _ _ _ _ n a }
end

@[simp] lemma leading_coeff_C (a : α) : leading_coeff (C a) = a :=
suffices leading_coeff (C a * X^0) = a, by rwa [pow_zero, mul_one] at this,
leading_coeff_monomial a 0

@[simp] lemma leading_coeff_X : leading_coeff (X : polynomial α) = 1 :=
suffices leading_coeff (C (1:α) * X^1) = 1, by rwa [C_1, pow_one, one_mul] at this,
leading_coeff_monomial 1 1

@[simp] lemma monic_X : monic (X : polynomial α) := leading_coeff_X

@[simp] lemma leading_coeff_one : leading_coeff (1 : polynomial α) = 1 :=
suffices leading_coeff (C (1:α) * X^0) = 1, by rwa [C_1, pow_zero, mul_one] at this,
leading_coeff_monomial 1 0

@[simp] lemma monic_one : monic (1 : polynomial α) := leading_coeff_C _

lemma leading_coeff_add_of_degree_lt (h : degree p < degree q) :
  leading_coeff (p + q) = leading_coeff q :=
have coeff p (nat_degree q) = 0, from coeff_nat_degree_eq_zero_of_degree_lt h,
by simp only [leading_coeff, nat_degree_eq_of_degree_eq (degree_add_eq_of_degree_lt h),
  this, coeff_add, zero_add]

lemma leading_coeff_add_of_degree_eq (h : degree p = degree q)
  (hlc : leading_coeff p + leading_coeff q ≠ 0) :
  leading_coeff (p + q) = leading_coeff p + leading_coeff q :=
have nat_degree (p + q) = nat_degree p,
  by apply nat_degree_eq_of_degree_eq; rw [degree_add_eq_of_leading_coeff_add_ne_zero hlc, h, max_self],
by simp only [leading_coeff, this, nat_degree_eq_of_degree_eq h, coeff_add]

@[simp] lemma coeff_mul_degree_add_degree (p q : polynomial α) :
  coeff (p * q) (nat_degree p + nat_degree q) = leading_coeff p * leading_coeff q :=
calc coeff (p * q) (nat_degree p + nat_degree q) =
    (range (nat_degree p + nat_degree q + 1)).sum
    (λ k, coeff p k * coeff q (nat_degree p + nat_degree q - k)) : coeff_mul_left _ _ _
... = coeff p (nat_degree p) * coeff q (nat_degree p + nat_degree q - nat_degree p) :
  finset.sum_eq_single _ (λ n hn₁ hn₂, (le_total n (nat_degree p)).elim
    (λ h, have degree q < (nat_degree p + nat_degree q - n : ℕ),
        from lt_of_le_of_lt degree_le_nat_degree
          (with_bot.coe_lt_coe.2 (nat.lt_sub_left_iff_add_lt.2
            (add_lt_add_right (lt_of_le_of_ne h hn₂) _))),
      by simp [coeff_eq_zero_of_degree_lt this])
    (λ h, have degree p < n, from lt_of_le_of_lt degree_le_nat_degree
        (with_bot.coe_lt_coe.2 (lt_of_le_of_ne h hn₂.symm)),
      by simp [coeff_eq_zero_of_degree_lt this]))
    (λ h, false.elim (h (mem_range.2 (lt_of_le_of_lt (nat.le_add_right _ _) (nat.lt_succ_self _)))))
... = _ : by simp [leading_coeff, nat.add_sub_cancel_left]

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
  by rw [← degree_eq_nat_degree hpq, degree_mul_eq' h, degree_eq_nat_degree hp, degree_eq_nat_degree hq])

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
  degree (p ^ n) = add_monoid.smul n (degree p)
| 0     := λ h, by rw [pow_zero, ← C_1] at *;
  rw [degree_C h, add_monoid.zero_smul]
| (n+1) := λ h,
have h₁ : leading_coeff p ^ n ≠ 0 := λ h₁, h $
  by rw [pow_succ, h₁, mul_zero],
have h₂ : leading_coeff p * leading_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← leading_coeff_pow' h₁] at h,
by rw [pow_succ, degree_mul_eq' h₂, succ_smul, degree_pow_eq' h₁]

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
    ← with_bot.coe_smul]; simp

@[simp] lemma leading_coeff_X_pow : ∀ n : ℕ, leading_coeff ((X : polynomial α) ^ n) = 1
| 0 := by simp
| (n+1) :=
if h10 : (1 : α) = 0
then by rw [pow_succ, ← one_mul X, ← C_1, h10]; simp
else
have h : leading_coeff (X : polynomial α) * leading_coeff (X ^ n) ≠ 0,
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
    ... ≤ nat_degree (C (coeff p n)) + add_monoid.smul n (degree q) :
      add_le_add' degree_le_nat_degree (degree_pow_le _ _)
    ... ≤ nat_degree (C (coeff p n)) + add_monoid.smul n (nat_degree q) :
      add_le_add_left' (add_monoid.smul_le_smul_of_le_right
        (@degree_le_nat_degree _ _ _ q) n)
    ... = (n * nat_degree q : ℕ) :
     by rw [nat_degree_C, with_bot.coe_zero, zero_add, ← with_bot.coe_smul,
       add_monoid.smul_eq_mul]; simp
    ... ≤ (nat_degree p * nat_degree q : ℕ) : with_bot.coe_le_coe.2 $
      mul_le_mul_of_nonneg_right
        (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.1 hn))
        (nat.zero_le _))

lemma degree_map_le [comm_semiring β] [decidable_eq β] (f : α → β) [is_semiring_hom f] :
  degree (p.map f) ≤ degree p :=
if h : p.map f = 0 then by simp [h]
else begin
  rw [degree_eq_nat_degree h],
  refine le_degree_of_ne_zero (mt (congr_arg f) _),
  rw [← coeff_map f, is_semiring_hom.map_zero f],
  exact mt leading_coeff_eq_zero.1 h
end

lemma subsingleton_of_monic_zero (h : monic (0 : polynomial α)) :
  (∀ p q : polynomial α, p = q) ∧ (∀ a b : α, a = b) :=
by rw [monic.def, leading_coeff_zero] at h;
  exact ⟨λ p q, by rw [← mul_one p, ← mul_one q, ← C_1, ← h, C_0, mul_zero, mul_zero],
    λ a b, by rw [← mul_one a, ← mul_one b, ← h, mul_zero, mul_zero]⟩

lemma degree_map_eq_of_leading_coeff_ne_zero [comm_semiring β] [decidable_eq β] (f : α → β)
  [is_semiring_hom f] (hf : f (leading_coeff p) ≠ 0) : degree (p.map f) = degree p :=
le_antisymm (degree_map_le f) $
  have hp0 : p ≠ 0, from λ hp0, by simpa [hp0, is_semiring_hom.map_zero f] using hf,
  begin
    rw [degree_eq_nat_degree hp0],
    refine le_degree_of_ne_zero _,
    rw [coeff_map], exact hf
  end

lemma degree_map_eq_of_injective [comm_semiring β] [decidable_eq β] (f : α → β) [is_semiring_hom f]
  (hf : function.injective f) : degree (p.map f) = degree p :=
if h : p = 0 then by simp [h]
else degree_map_eq_of_leading_coeff_ne_zero _
  (by rw [← is_semiring_hom.map_zero f]; exact mt hf.eq_iff.1
    (mt leading_coeff_eq_zero.1 h))

lemma monic_map [comm_semiring β] [decidable_eq β] (f : α → β)
  [is_semiring_hom f] (hp : monic p) : monic (p.map f) :=
if h : (0 : β) = 1 then
  by haveI := subsingleton_of_zero_eq_one β h;
  exact subsingleton.elim _ _
else
have f (leading_coeff p) ≠ 0,
  by rwa [show _ = _, from hp, is_semiring_hom.map_one f, ne.def, eq_comm],
by erw [monic, leading_coeff, nat_degree_eq_of_degree_eq
    (degree_map_eq_of_leading_coeff_ne_zero f this), coeff_map,
    ← leading_coeff, show _ = _, from hp, is_semiring_hom.map_one f]

lemma zero_le_degree_iff {p : polynomial α} : 0 ≤ degree p ↔ p ≠ 0 :=
by rw [ne.def, ← degree_eq_bot];
  cases degree p; exact dec_trivial

@[simp] lemma coeff_mul_X_zero (p : polynomial α) : coeff (p * X) 0 = 0 :=
by rw [coeff_mul_left, sum_range_succ]; simp

instance [subsingleton α] : subsingleton (polynomial α) :=
⟨λ _ _, polynomial.ext.2 (λ _, subsingleton.elim _ _)⟩

lemma ne_zero_of_monic_of_zero_ne_one (hp : monic p) (h : (0 : α) ≠ 1) :
  p ≠ 0 := mt (congr_arg leading_coeff) $ by rw [monic.def.1 hp, leading_coeff_zero]; cc

lemma eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) :
  p = C (p.coeff 1) * X + C (p.coeff 0) :=
polynomial.ext.2 (λ n, nat.cases_on n (by simp)
  (λ n, nat.cases_on n (by simp [coeff_C])
    (λ m, have degree p < m.succ.succ, from lt_of_le_of_lt h dec_trivial,
      by simp [coeff_eq_zero_of_degree_lt this, coeff_C, nat.succ_ne_zero, coeff_X,
        nat.succ_inj', @eq_comm ℕ 0])))

lemma eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
  p = C (p.leading_coeff) * X + C (p.coeff 0) :=
(eq_X_add_C_of_degree_le_one (show degree p ≤ 1, from h ▸ le_refl _)).trans
  (by simp [leading_coeff, nat_degree_eq_of_degree_eq_some h])

theorem degree_C_mul_X_pow_le (r : α) (n : ℕ) : degree (C r * X^n) ≤ n :=
begin
  rw [← single_eq_C_mul_X],
  refine finset.sup_le (λ b hb, _),
  rw list.eq_of_mem_singleton (finsupp.support_single_subset hb),
  exact le_refl _
end

theorem degree_X_pow_le (n : ℕ) : degree (X^n : polynomial α) ≤ n :=
by simpa only [C_1, one_mul] using degree_C_mul_X_pow_le (1:α) n

theorem degree_X_le : degree (X : polynomial α) ≤ 1 :=
by simpa only [C_1, one_mul, pow_one] using degree_C_mul_X_pow_le (1:α) 1

theorem monic_of_degree_le (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : monic p :=
decidable.by_cases
  (assume H : degree p < n, @subsingleton.elim _ (subsingleton_of_zero_eq_one α $
    H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
  (assume H : ¬degree p < n, by rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_le H1).resolve_left H])

theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) + p) :=
have H1 : degree p < n+1, from lt_of_le_of_lt H (with_bot.coe_lt_coe.2 (nat.lt_succ_self n)),
monic_of_degree_le (n+1)
  (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H1)))
  (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zero])

theorem monic_X_add_C (x : α) : monic (X + C x) :=
pow_one (X : polynomial α) ▸ monic_X_pow_add degree_C_le

theorem degree_le_iff_coeff_zero (f : polynomial α) (n : with_bot ℕ) :
  degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_bot ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_bot ℕ) ≤ n)) Hm,
  H1 $ (finsupp.mem_support_to_fun f m).2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  (finsupp.mem_support_to_fun f b).1 Hb $ H b $ lt_of_not_ge Hn⟩

theorem nat_degree_le_of_degree_le {p : polynomial α} {n : ℕ}
  (H : degree p ≤ n) : nat_degree p ≤ n :=
show option.get_or_else (degree p) 0 ≤ n, from match degree p, H with
| none,     H := zero_le _
| (some d), H := with_bot.coe_le_coe.1 H
end

theorem leading_coeff_mul_X_pow {p : polynomial α} {n : ℕ} :
  leading_coeff (p * X ^ n) = leading_coeff p :=
decidable.by_cases
  (assume H : leading_coeff p = 0, by rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
  (assume H : leading_coeff p ≠ 0,
    by rw [leading_coeff_mul', leading_coeff_X_pow, mul_one];
      rwa [leading_coeff_X_pow, mul_one])

lemma monic_mul (hp : monic p) (hq : monic q) : monic (p * q) :=
if h0 : (0 : α) = 1 then by haveI := subsingleton_of_zero_eq_one _ h0;
  exact subsingleton.elim _ _
else
  have leading_coeff p * leading_coeff q ≠ 0, by simp [monic.def.1 hp, monic.def.1 hq, ne.symm h0],
  by rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mul]

lemma monic_pow (hp : monic p) : ∀ (n : ℕ), monic (p ^ n)
| 0     := monic_one
| (n+1) := monic_mul hp (monic_pow n)

lemma multiplicity_finite_of_degree_pos_of_monic (hp : (0 : with_bot ℕ) < degree p)
  (hmp : monic p) (hq : q ≠ 0) : multiplicity.finite p q :=
have zn0 : (0 : α) ≠ 1, from λ h, by haveI := subsingleton_of_zero_eq_one _ h;
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
    exact ne_of_lt (lt_add_of_le_of_pos (le_mul_of_ge_one_right' (nat.zero_le _) hnp)
      (add_pos_of_pos_of_nonneg (by rwa one_mul) (nat.zero_le _))) this
  end⟩

end comm_semiring

section nonzero_comm_semiring
variables [nonzero_comm_semiring α] [decidable_eq α] {p q : polynomial α}

instance : nonzero_comm_semiring (polynomial α) :=
{ zero_ne_one := λ (h : (0 : polynomial α) = 1),
    @zero_ne_one α _ $
    calc (0 : α) = eval 0 0 : eval_zero.symm
      ... = eval 0 1 : congr_arg _ h
      ... = 1 : eval_C,
  ..polynomial.comm_semiring }

@[simp] lemma degree_one : degree (1 : polynomial α) = (0 : with_bot ℕ) :=
degree_C (show (1 : α) ≠ 0, from zero_ne_one.symm)

@[simp] lemma degree_X : degree (X : polynomial α) = 1 :=
begin
  unfold X degree single finsupp.support,
  rw if_neg (zero_ne_one).symm,
  refl
end

lemma X_ne_zero : (X : polynomial α) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

@[simp] lemma degree_X_pow : ∀ (n : ℕ), degree ((X : polynomial α) ^ n) = n
| 0 := by simp only [pow_zero, degree_one]; refl
| (n+1) :=
have h : leading_coeff (X : polynomial α) * leading_coeff (X ^ n) ≠ 0,
  by rw [leading_coeff_X, leading_coeff_X_pow n, one_mul];
    exact zero_ne_one.symm,
by rw [pow_succ, degree_mul_eq' h, degree_X, degree_X_pow, add_comm]; refl

@[simp] lemma not_monic_zero : ¬monic (0 : polynomial α) :=
by simpa only [monic, leading_coeff_zero] using zero_ne_one

lemma ne_zero_of_monic (h : monic p) : p ≠ 0 :=
λ h₁, @not_monic_zero α _ _ (h₁ ▸ h)

end nonzero_comm_semiring

section comm_ring
variables [comm_ring α] [decidable_eq α] {p q : polynomial α}
instance : comm_ring (polynomial α) := finsupp.to_comm_ring
instance : has_scalar α (polynomial α) := finsupp.to_has_scalar
-- TODO if this becomes a semimodule then the below lemma could be proved for semimodules
instance : module α (polynomial α) := finsupp.to_module ℕ α

-- TODO -- this is OK for semimodules
@[simp] lemma coeff_smul (p : polynomial α) (r : α) (n : ℕ) :
coeff (r • p) n = r * coeff p n := finsupp.smul_apply

-- TODO -- this is OK for semimodules
lemma C_mul' (a : α) (f : polynomial α) : C a * f = a • f :=
ext.2 $ λ n, coeff_C_mul f

variable (α)
def lcoeff (n : ℕ) : polynomial α →ₗ α :=
{ to_fun := λ f, coeff f n,
  add := λ f g, coeff_add f g n,
  smul := λ r p, coeff_smul p r n }
variable {α}

@[simp] lemma lcoeff_apply (n : ℕ) (f : polynomial α) : lcoeff α n f = coeff f n := rfl

instance C.is_ring_hom : is_ring_hom (@C α _ _) := by apply is_ring_hom.of_semiring

@[simp] lemma C_neg : C (-a) = -C a := is_ring_hom.map_neg C

@[simp] lemma C_sub : C (a - b) = C a - C b := is_ring_hom.map_sub C

instance eval₂.is_ring_hom {β} [comm_ring β]
  (f : α → β) [is_ring_hom f] {x : β} : is_ring_hom (eval₂ f x) :=
by apply is_ring_hom.of_semiring

instance eval.is_ring_hom {x : α} : is_ring_hom (eval x) := eval₂.is_ring_hom _

instance map.is_ring_hom {β} [comm_ring β] [decidable_eq β]
  (f : α → β) [is_ring_hom f] : is_ring_hom (map f) :=
eval₂.is_ring_hom (C ∘ f)

@[simp] lemma map_sub {β} [comm_ring β] [decidable_eq β]
  (f : α → β) [is_ring_hom f] : (p - q).map f = p.map f - q.map f := is_ring_hom.map_sub _

@[simp] lemma map_neg {β} [comm_ring β] [decidable_eq β]
  (f : α → β) [is_ring_hom f] : (-p).map f = -(p.map f) := is_ring_hom.map_neg _

@[simp] lemma degree_neg (p : polynomial α) : degree (-p) = degree p :=
by unfold degree; rw support_neg

@[simp] lemma coeff_neg (p : polynomial α) (n : ℕ) : coeff (-p) n = -coeff p n := rfl

@[simp] lemma coeff_sub (p q : polynomial α) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := rfl

@[simp] lemma eval_neg (p : polynomial α) (x : α) : (-p).eval x = -p.eval x :=
is_ring_hom.map_neg _

@[simp] lemma eval_sub (p q : polynomial α) (x : α) : (p - q).eval x = p.eval x - q.eval x :=
is_ring_hom.map_sub _

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

instance : has_well_founded (polynomial α) := ⟨_, degree_lt_wf⟩

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

def div_mod_by_monic_aux : Π (p : polynomial α) {q : polynomial α},
  monic q → polynomial α × polynomial α
| p := λ q hq, if h : degree q ≤ degree p ∧ p ≠ 0 then
  let z := C (leading_coeff p) * X^(nat_degree p - nat_degree q)  in
  have wf : _ := div_wf_lemma h hq,
  let dm := div_mod_by_monic_aux (p - z * q) hq in
  ⟨z + dm.1, dm.2⟩
  else ⟨0, p⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic (p q : polynomial α) : polynomial α :=
if hq : monic q then (div_mod_by_monic_aux p hq).1 else 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q`. -/
def mod_by_monic (p q : polynomial α) : polynomial α :=
if hq : monic q then (div_mod_by_monic_aux p hq).2 else p

infixl  ` /ₘ ` : 70 := div_by_monic

infixl ` %ₘ ` : 70 := mod_by_monic

lemma degree_mod_by_monic_lt : ∀ (p : polynomial α) {q : polynomial α} (hq : monic q)
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

lemma mod_by_monic_eq_sub_mul_div : ∀ (p : polynomial α) {q : polynomial α} (hq : monic q),
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

lemma mod_by_monic_add_div (p : polynomial α) {q : polynomial α} (hq : monic q) :
  p %ₘ q + q * (p /ₘ q) = p := eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

@[simp] lemma zero_mod_by_monic (p : polynomial α) : 0 %ₘ p = 0 :=
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma zero_div_by_monic (p : polynomial α) : 0 /ₘ p = 0 :=
begin
  unfold div_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma mod_by_monic_zero (p : polynomial α) : p %ₘ 0 = p :=
if h : monic (0 : polynomial α) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold mod_by_monic div_mod_by_monic_aux; rw dif_neg h

@[simp] lemma div_by_monic_zero (p : polynomial α) : p /ₘ 0 = 0 :=
if h : monic (0 : polynomial α) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold div_by_monic div_mod_by_monic_aux; rw dif_neg h

lemma div_by_monic_eq_of_not_monic (p : polynomial α) (hq : ¬monic q) : p /ₘ q = 0 := dif_neg hq

lemma mod_by_monic_eq_of_not_monic (p : polynomial α) (hq : ¬monic q) : p %ₘ q = p := dif_neg hq

lemma mod_by_monic_eq_self_iff (hq : monic q) (hq0 : q ≠ 0) : p %ₘ q = p ↔ degree p < degree q :=
⟨λ h, h ▸ degree_mod_by_monic_lt _ hq hq0,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold mod_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

lemma div_by_monic_eq_zero_iff (hq : monic q) (hq0 : q ≠ 0) : p /ₘ q = 0 ↔ degree p < degree q :=
⟨λ h, by have := mod_by_monic_add_div p hq;
  rwa [h, mul_zero, add_zero, mod_by_monic_eq_self_iff hq hq0] at this,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold div_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

lemma degree_add_div_by_monic (hq : monic q) (h : degree q ≤ degree p) :
  degree q + degree (p /ₘ q) = degree p :=
if hq0 : q = 0 then
  have ∀ (p : polynomial α), p = 0,
    from λ p, (@subsingleton_of_monic_zero α _ _ (hq0 ▸ hq)).1 _ _,
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

lemma degree_div_by_monic_le (p q : polynomial α) : degree (p /ₘ q) ≤ degree p :=
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

lemma degree_div_by_monic_lt (p : polynomial α) {q : polynomial α} (hq : monic q)
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

lemma div_mod_by_monic_unique {f g} (q r : polynomial α) (hg : monic g)
  (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r :=
if hg0 : g = 0 then by split; exact (subsingleton_of_monic_zero
  (hg0 ▸ hg : monic (0 : polynomial α))).1 _ _
else
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g),
    from eq_of_sub_eq_zero
      (by rw [← sub_eq_zero_of_eq (h.1.trans (mod_by_monic_add_div f hg).symm)];
        simp [mul_add, mul_comm]),
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

lemma map_mod_div_by_monic [comm_ring β] [decidable_eq β] (f : α → β) [is_semiring_hom f] (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f :=
if h01 : (0 : β) = 1 then by haveI := subsingleton_of_zero_eq_one β h01;
  exact ⟨subsingleton.elim _ _, subsingleton.elim _ _⟩
else
have h01α : (0 : α) ≠ 1, from mt (congr_arg f)
  (by rwa [is_semiring_hom.map_one f, is_semiring_hom.map_zero f]),
have map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q),
  from (div_mod_by_monic_unique ((p /ₘ q).map f) _ (monic_map f hq)
    ⟨eq.symm $ by rw [← map_mul, ← map_add, mod_by_monic_add_div _ hq],
    calc _ ≤ degree (p %ₘ q) : degree_map_le _
    ... < degree q : degree_mod_by_monic_lt _ hq
      $ (ne_zero_of_monic_of_zero_ne_one hq h01α)
    ... = _ : eq.symm $ degree_map_eq_of_leading_coeff_ne_zero _
      (by rw [monic.def.1 hq, is_semiring_hom.map_one f]; exact ne.symm h01)⟩),
⟨this.1.symm, this.2.symm⟩

lemma map_div_by_monic [comm_ring β] [decidable_eq β] (f : α → β) [is_semiring_hom f] (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f :=
(map_mod_div_by_monic f hq).1

lemma map_mod_by_monic [comm_ring β] [decidable_eq β] (f : α → β) [is_semiring_hom f] (hq : monic q) :
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

@[simp] lemma mod_by_monic_one (p : polynomial α) : p %ₘ 1 = 0 :=
(dvd_iff_mod_by_monic_eq_zero monic_one).2 (one_dvd _)

@[simp] lemma div_by_monic_one (p : polynomial α) : p /ₘ 1 = p :=
by conv_rhs { rw [← mod_by_monic_add_div p monic_one] }; simp

lemma degree_pos_of_root (hp : p ≠ 0) (h : is_root p a) : 0 < degree p :=
lt_of_not_ge $ λ hlt, begin
  have := eq_C_of_degree_le_zero hlt,
  rw [is_root, this, eval_C] at h,
  exact hp (finsupp.ext (λ n, show coeff p n = 0, from
    nat.cases_on n h (λ _, coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hlt
      (with_bot.coe_lt_coe.2 (nat.succ_pos _)))))),
end

theorem monic_X_sub_C (x : α) : monic (X - C x) :=
by simpa only [C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
monic_X_pow_add ((degree_neg p).symm ▸ H)

theorem degree_mod_by_monic_le (p : polynomial α) {q : polynomial α}
  (hq : monic q) : degree (p %ₘ q) ≤ degree q :=
decidable.by_cases
  (assume H : q = 0, by rw [monic, H, leading_coeff_zero] at hq;
    have : (0:polynomial α) = 1 := (by rw [← C_0, ← C_1, hq]);
    rw [eq_zero_of_zero_eq_one _ this (p %ₘ q), eq_zero_of_zero_eq_one _ this q]; exact le_refl _)
  (assume H : q ≠ 0, le_of_lt $ degree_mod_by_monic_lt _ hq H)

lemma root_X_sub_C : is_root (X - C a) b ↔ a = b :=
by rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero_iff_eq, eq_comm]

def nonzero_comm_ring.of_polynomial_ne (h : p ≠ q) : nonzero_comm_ring α :=
{ zero := 0,
  one := 1,
  zero_ne_one := λ h01, h $
    by rw [← one_mul p, ← one_mul q, ← C_1, ← h01, C_0, zero_mul, zero_mul],
  ..show comm_ring α, by apply_instance }

end comm_ring

section nonzero_comm_ring
variables [nonzero_comm_ring α] [decidable_eq α] {p q : polynomial α}

instance : nonzero_comm_ring (polynomial α) :=
{ ..polynomial.nonzero_comm_semiring,
  ..polynomial.comm_ring }

@[simp] lemma degree_X_sub_C (a : α) : degree (X - C a) = 1 :=
begin
  rw [sub_eq_add_neg, add_comm, ← @degree_X α],
  by_cases ha : a = 0,
  { simp only [ha, C_0, neg_zero, zero_add] },
  exact degree_add_eq_of_degree_lt (by rw [degree_X, degree_neg, degree_C ha]; exact dec_trivial)
end

lemma degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : α) :
  degree ((X : polynomial α) ^ n - C a) = n :=
have degree (-C a) < degree ((X : polynomial α) ^ n),
  from calc degree (-C a) ≤ 0 : by rw degree_neg; exact degree_C_le
  ... < degree ((X : polynomial α) ^ n) : by rwa [degree_X_pow];
    exact with_bot.coe_lt_coe.2 hn,
by rw [sub_eq_add_neg, add_comm, degree_add_eq_of_degree_lt this, degree_X_pow]

lemma X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : α) :
  (X : polynomial α) ^ n - C a ≠ 0 :=
mt degree_eq_bot.2 (show degree ((X : polynomial α) ^ n - C a) ≠ ⊥,
  by rw degree_X_pow_sub_C hn; exact dec_trivial)

end nonzero_comm_ring

section comm_ring

variables [comm_ring α] [decidable_eq α] {p q : polynomial α}

@[simp] lemma mod_by_monic_X_sub_C_eq_C_eval (p : polynomial α) (a : α) : p %ₘ (X - C a) = C (p.eval a) :=
if h0 : (0 : α) = 1 then by letI := subsingleton_of_zero_eq_one α h0; exact subsingleton.elim _ _
else
by letI : nonzero_comm_ring α := nonzero_comm_ring.of_ne h0; exact
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

lemma mod_by_monic_X (p : polynomial α) : p %ₘ X = C (p.eval 0) :=
by rw [← mod_by_monic_X_sub_C_eq_C_eval, C_0, sub_zero]

section multiplicity

def decidable_dvd_monic (p : polynomial α) (hq : monic q): decidable (q ∣ p) :=
decidable_of_iff (p %ₘ q = 0) (dvd_iff_mod_by_monic_eq_zero hq)

local attribute [instance, priority 0] classical.dec

lemma multiplicity_X_sub_C_finite (a : α) (h0 : p ≠ 0) :
  multiplicity.finite (X - C a) p :=
multiplicity_finite_of_degree_pos_of_monic
  (have (0 : α) ≠ 1, from (λ h, by haveI := subsingleton_of_zero_eq_one _ h;
      exact h0 (subsingleton.elim _ _)),
    by letI : nonzero_comm_ring α := { zero_ne_one := this, ..show comm_ring α, by apply_instance };
      rw degree_X_sub_C; exact dec_trivial)
    (monic_X_sub_C _) h0

def root_multiplicity (a : α) (p : polynomial α) : ℕ :=
if h0 : p = 0 then 0
else let I : decidable_pred (λ n : ℕ, ¬(X - C a) ^ (n + 1) ∣ p) :=
  λ n, @not.decidable _ (decidable_dvd_monic p (monic_pow (monic_X_sub_C a) (n + 1))) in
by exactI nat.find (multiplicity_X_sub_C_finite a h0)

lemma root_multiplicity_eq_multiplicity (p : polynomial α) (a : α) :
  root_multiplicity a p = if h0 : p = 0 then 0 else
  (multiplicity (X - C a) p).get (multiplicity_X_sub_C_finite a h0) :=
by simp [multiplicity, root_multiplicity, roption.dom];
  congr; funext; congr

lemma pow_root_multiplicity_dvd (p : polynomial α) (a : α) :
  (X - C a) ^ root_multiplicity a p ∣ p :=
if h : p = 0 then by simp [h]
else by rw [root_multiplicity_eq_multiplicity, dif_neg h];
  exact multiplicity.pow_multiplicity_dvd _

lemma div_by_monic_mul_pow_root_multiplicity_eq
  (p : polynomial α) (a : α) :
  p /ₘ ((X - C a) ^ root_multiplicity a p) *
  (X - C a) ^ root_multiplicity a p = p :=
have monic ((X - C a) ^ root_multiplicity a p),
  from monic_pow (monic_X_sub_C _) _,
by conv_rhs { rw [← mod_by_monic_add_div p this,
    (dvd_iff_mod_by_monic_eq_zero this).2 (pow_root_multiplicity_dvd _ _)] };
  simp [mul_comm]

lemma eval_div_by_monic_pow_root_multiplicity_ne_zero
  {p : polynomial α} (a : α) (hp : p ≠ 0) :
  (p /ₘ ((X - C a) ^ root_multiplicity a p)).eval a ≠ 0 :=
begin
  letI : nonzero_comm_ring α := nonzero_comm_ring.of_polynomial_ne hp,
  rw [ne.def, ← is_root.def, ← dvd_iff_is_root],
  rintros ⟨q, hq⟩,
  have := div_by_monic_mul_pow_root_multiplicity_eq p a,
  rw [mul_comm, hq, ← mul_assoc, ← pow_succ',
    root_multiplicity_eq_multiplicity, dif_neg hp] at this,
  exact multiplicity.is_greatest'
    (multiplicity_finite_of_degree_pos_of_monic
    (show (0 : with_bot ℕ) < degree (X - C a),
      by rw degree_X_sub_C; exact dec_trivial) _ hp)
    (nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
end

end multiplicity

end comm_ring

section integral_domain
variables [integral_domain α] [decidable_eq α] {p q : polynomial α}

@[simp] lemma degree_mul_eq : degree (p * q) = degree p + degree q :=
if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, with_bot.bot_add]
else if hq0 : q = 0 then  by simp only [hq0, degree_zero, mul_zero, with_bot.add_bot]
else degree_mul_eq' $ mul_ne_zero (mt leading_coeff_eq_zero.1 hp0)
    (mt leading_coeff_eq_zero.1 hq0)

@[simp] lemma degree_pow_eq (p : polynomial α) (n : ℕ) :
  degree (p ^ n) = add_monoid.smul n (degree p) :=
by induction n; [simp only [pow_zero, degree_one, add_monoid.zero_smul],
simp only [*, pow_succ, succ_smul, degree_mul_eq]]

@[simp] lemma leading_coeff_mul (p q : polynomial α) : leading_coeff (p * q) =
  leading_coeff p * leading_coeff q :=
begin
  by_cases hp : p = 0,
  { simp only [hp, zero_mul, leading_coeff_zero] },
  { by_cases hq : q = 0,
    { simp only [hq, mul_zero, leading_coeff_zero] },
    { rw [leading_coeff_mul'],
      exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) (mt leading_coeff_eq_zero.1 hq) } }
end

@[simp] lemma leading_coeff_pow (p : polynomial α) (n : ℕ) :
  leading_coeff (p ^ n) = leading_coeff p ^ n :=
by induction n; [simp only [pow_zero, leading_coeff_one],
simp only [*, pow_succ, leading_coeff_mul]]

instance : integral_domain (polynomial α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h, begin
    have : leading_coeff 0 = leading_coeff a * leading_coeff b := h ▸ leading_coeff_mul a b,
    rw [leading_coeff_zero, eq_comm] at this,
    rw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero],
    exact eq_zero_or_eq_zero_of_mul_eq_zero this
  end,
  ..polynomial.nonzero_comm_ring }

lemma nat_degree_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p * q) =
  nat_degree p + nat_degree q :=
by rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq),
    with_bot.coe_add, ← degree_eq_nat_degree hp,
    ← degree_eq_nat_degree hq, degree_mul_eq]

@[simp] lemma nat_degree_pow_eq (p : polynomial α) (n : ℕ) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0
then if hn0 : n = 0 then by simp [hp0, hn0]
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else nat_degree_pow_eq'
  (by rw [← leading_coeff_pow, ne.def, leading_coeff_eq_zero]; exact pow_ne_zero _ hp0)

lemma root_or_root_of_root_mul (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
by rw [is_root, eval_mul] at h;
  exact eq_zero_or_eq_zero_of_mul_eq_zero h

lemma degree_le_mul_left (p : polynomial α) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
if hp : p = 0 then by simp only [hp, zero_mul, le_refl]
else by rw [degree_mul_eq, degree_eq_nat_degree hp,
    degree_eq_nat_degree hq];
  exact with_bot.coe_le_coe.2 (nat.le_add_right _ _)

lemma exists_finset_roots : ∀ {p : polynomial α} (hp : p ≠ 0),
  ∃ s : finset α, (s.card : with_bot ℕ) ≤ degree p ∧ ∀ x, x ∈ s ↔ is_root p x
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
        exact add_le_add' (le_refl (1 : with_bot ℕ)) htd,
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
noncomputable def roots (p : polynomial α) : finset α :=
if h : p = 0 then ∅ else classical.some (exists_finset_roots h)

lemma card_roots (hp0 : p ≠ 0) : ((roots p).card : with_bot ℕ) ≤ degree p :=
begin
  unfold roots,
  rw dif_neg hp0,
  exact (classical.some_spec (exists_finset_roots hp0)).1
end

@[simp] lemma mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a :=
by unfold roots; rw dif_neg hp; exact (classical.some_spec (exists_finset_roots hp)).2 _

lemma card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : α) :
  (roots ((X : polynomial α) ^ n - C a)).card ≤ n :=
with_bot.coe_le_coe.1 $
calc ((roots ((X : polynomial α) ^ n - C a)).card : with_bot ℕ)
      ≤ degree ((X : polynomial α) ^ n - C a) : card_roots (X_pow_sub_C_ne_zero hn a)
  ... = n : degree_X_pow_sub_C hn a

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
noncomputable def nth_roots {α : Type*} [integral_domain α] (n : ℕ) (a : α) : finset α :=
by letI := classical.prop_decidable; exact
roots ((X : polynomial α) ^ n - C a)

@[simp] lemma mem_nth_roots {α : Type*} [integral_domain α] {n : ℕ} (hn : 0 < n) {a x : α} :
  x ∈ nth_roots n a ↔ x ^ n = a :=
by letI := classical.prop_decidable;
rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a),
  is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero_iff_eq]

lemma card_nth_roots {α : Type*} [integral_domain α] (n : ℕ) (a : α) :
  (nth_roots n a).card ≤ n :=
by letI := classical.prop_decidable; exact
if hn : n = 0
then if h : (X : polynomial α) ^ n - C a = 0
  then by simp only [nat.zero_le, nth_roots, roots, h, dif_pos rfl, card_empty]
  else with_bot.coe_le_coe.1 (le_trans (card_roots h)
    (by rw [hn, pow_zero, ← @C_1 α _ _, ← is_ring_hom.map_sub (@C α _ _)];
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
      ← with_bot.coe_smul, add_monoid.smul_eq_mul, with_bot.coe_lt_coe, nat.cast_id],
    exact (mul_lt_mul_right (nat.pos_of_ne_zero hqd0)).2
      (lt_of_le_of_ne (with_bot.coe_le_coe.1 (by rw ← degree_eq_nat_degree hp0; exact le_sup hbs)) hbp)
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

lemma leading_coeff_comp (hq : nat_degree q ≠ 0): leading_coeff (p.comp q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
by rw [← coeff_comp_degree_mul_degree hq, ← nat_degree_comp]; refl

lemma degree_eq_zero_of_is_unit (h : is_unit p) : degree p = 0 :=
let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h in
have hp0 : p ≠ 0, from λ hp0, by simpa [hp0] using hq,
have hq0 : q ≠ 0, from λ hp0, by simpa [hp0] using hq,
have nat_degree (1 : polynomial α) = nat_degree (p * q),
  from congr_arg _ hq,
by rw [nat_degree_one, nat_degree_mul_eq hp0 hq0, eq_comm,
    add_eq_zero_iff, ← with_bot.coe_eq_coe,
    ← degree_eq_nat_degree hp0] at this;
  exact this.1

@[simp] lemma degree_coe_units (u : units (polynomial α)) :
  degree (u : polynomial α) = 0 :=
degree_eq_zero_of_is_unit ⟨u, rfl⟩

@[simp] lemma nat_degree_coe_units (u : units (polynomial α)) :
  nat_degree (u : polynomial α) = 0 :=
nat_degree_eq_of_degree_eq_some (degree_coe_units u)

lemma coeff_coe_units_zero_ne_zero (u : units (polynomial α)) :
  coeff (u : polynomial α) 0 ≠ 0 :=
begin
  conv in (0) {rw [← nat_degree_coe_units u]},
  rw [← leading_coeff, ne.def, leading_coeff_eq_zero],
  exact units.coe_ne_zero _
end

lemma degree_eq_degree_of_associated (h : associated p q) : degree p = degree q :=
let ⟨u, hu⟩ := h in by simp [hu.symm]

end integral_domain

section field
variables [discrete_field α] {p q : polynomial α}
instance : vector_space α (polynomial α) :=
{ ..finsupp.to_module ℕ α }

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
  exact hp ⟨units.map C (units.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))), rfl⟩)

lemma irreducible_of_degree_eq_one (hp1 : degree p = 1) : irreducible p :=
⟨mt is_unit_iff_dvd_one.1 (λ ⟨q, hq⟩,
  absurd (congr_arg degree hq) (λ h,
    have degree q = 0, by rw [degree_one, degree_mul_eq, hp1, eq_comm,
      nat.with_bot.add_eq_zero_iff] at h; exact h.2,
    by simp [degree_mul_eq, this, degree_one, hp1] at h;
      exact absurd h dec_trivial)),
λ q r hpqr, begin
  have := congr_arg degree hpqr,
  rw [hp1, degree_mul_eq, eq_comm, nat.with_bot.add_eq_one_iff] at this,
  rw [is_unit_iff_degree_eq_zero, is_unit_iff_degree_eq_zero]; tautology
end⟩

lemma monic_mul_leading_coeff_inv (h : p ≠ 0) :
  monic (p * C (leading_coeff p)⁻¹) :=
by rw [monic, leading_coeff_mul, leading_coeff_C,
  mul_inv_cancel (show leading_coeff p ≠ 0, from mt leading_coeff_eq_zero.1 h)]

lemma degree_mul_leading_coeff_inv (p : polynomial α) (h : q ≠ 0) :
  degree (p * C (leading_coeff q)⁻¹) = degree p :=
have h₁ : (leading_coeff q)⁻¹ ≠ 0 :=
  inv_ne_zero (mt leading_coeff_eq_zero.1 h),
by rw [degree_mul_eq, degree_C h₁, add_zero]

def div (p q : polynomial α) :=
C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹))

def mod (p q : polynomial α) :=
p %ₘ (q * C (leading_coeff q)⁻¹)

private lemma quotient_mul_add_remainder_eq_aux (p q : polynomial α) :
  q * div p q + mod p q = p :=
if h : q = 0 then by simp only [h, zero_mul, mod, mod_by_monic_zero, zero_add]
else begin
  conv {to_rhs, rw ← mod_by_monic_add_div p (monic_mul_leading_coeff_inv h)},
  rw [div, mod, add_comm, mul_assoc]
end

private lemma remainder_lt_aux (p : polynomial α) (hq : q ≠ 0) :
  degree (mod p q) < degree q :=
by rw ← degree_mul_leading_coeff_inv q hq; exact
  degree_mod_by_monic_lt p (monic_mul_leading_coeff_inv hq)
    (mul_ne_zero hq (mt leading_coeff_eq_zero.2 (by rw leading_coeff_C;
      exact inv_ne_zero (mt leading_coeff_eq_zero.1 hq))))

instance : has_div (polynomial α) := ⟨div⟩

instance : has_mod (polynomial α) := ⟨mod⟩

lemma div_def : p / q = C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹)) := rfl

lemma mod_def : p % q = p %ₘ (q * C (leading_coeff q)⁻¹) := rfl

lemma mod_by_monic_eq_mod (p : polynomial α) (hq : monic q) : p %ₘ q = p % q :=
show p %ₘ q = p %ₘ (q * C (leading_coeff q)⁻¹), by simp only [monic.def.1 hq, inv_one, mul_one, C_1]

lemma div_by_monic_eq_div (p : polynomial α) (hq : monic q) : p /ₘ q = p / q :=
show p /ₘ q = C (leading_coeff q)⁻¹ * (p /ₘ (q * C (leading_coeff q)⁻¹)),
by simp only [monic.def.1 hq, inv_one, C_1, one_mul, mul_one]

lemma mod_X_sub_C_eq_C_eval (p : polynomial α) (a : α) : p % (X - C a) = C (p.eval a) :=
mod_by_monic_eq_mod p (monic_X_sub_C a) ▸ mod_by_monic_X_sub_C_eq_C_eval _ _

lemma mul_div_eq_iff_is_root : (X - C a) * (p / (X - C a)) = p ↔ is_root p a :=
div_by_monic_eq_div p (monic_X_sub_C a) ▸ mul_div_by_monic_eq_iff_is_root

instance : euclidean_domain (polynomial α) :=
{ quotient := (/),
  quotient_zero := by simp [div_def],
  remainder := (%),
  r := _,
  r_well_founded := degree_lt_wf,
  quotient_mul_add_remainder_eq := quotient_mul_add_remainder_eq_aux,
  remainder_lt := λ p q hq, remainder_lt_aux _ hq,
  mul_left_not_lt := λ p q hq, not_lt_of_ge (degree_le_mul_left _ hq) }

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

lemma degree_div_le (p q : polynomial α) : degree (p / q) ≤ degree p :=
if hq : q = 0 then by simp [hq]
else by rw [div_def, mul_comm, degree_mul_leading_coeff_inv _ hq];
  exact degree_div_by_monic_le _ _

lemma degree_div_lt (hp : p ≠ 0) (hq : 0 < degree q) : degree (p / q) < degree p :=
have hq0 : q ≠ 0, from λ hq0, by simpa [hq0] using hq,
by rw [div_def, mul_comm, degree_mul_leading_coeff_inv _ hq0];
  exact degree_div_by_monic_lt _ (monic_mul_leading_coeff_inv hq0) hp
    (by rw degree_mul_leading_coeff_inv _ hq0; exact hq)

@[simp] lemma degree_map [discrete_field β] (p : polynomial α) (f : α → β) [is_field_hom f] :
  degree (p.map f) = degree p :=
degree_map_eq_of_injective _ (is_field_hom.injective f)

@[simp] lemma nat_degree_map [discrete_field β] (f : α → β) [is_field_hom f] :
  nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map _ f)

@[simp] lemma leading_coeff_map [discrete_field β] (f : α → β) [is_field_hom f] :
  leading_coeff (p.map f) = f (leading_coeff p) :=
by simp [leading_coeff, coeff_map f]

lemma map_div [discrete_field β] (f : α → β) [is_field_hom f] :
  (p / q).map f = p.map f / q.map f :=
if hq0 : q = 0 then by simp [hq0]
else
by rw [div_def, div_def, map_mul, map_div_by_monic f (monic_mul_leading_coeff_inv hq0)];
  simp [is_field_hom.map_inv f, leading_coeff, coeff_map f]

lemma map_mod [discrete_field β] (f : α → β) [is_field_hom f] :
  (p % q).map f = p.map f % q.map f :=
if hq0 : q = 0 then by simp [hq0]
else by rw [mod_def, mod_def, leading_coeff_map f, ← is_field_hom.map_inv f, ← map_C f,
  ← map_mul f, map_mod_by_monic f (monic_mul_leading_coeff_inv hq0)]

@[simp] lemma map_eq_zero [discrete_field β] (f : α → β) [is_field_hom f] :
  p.map f = 0 ↔ p = 0 :=
by simp [polynomial.ext, is_field_hom.map_eq_zero f, coeff_map]

lemma exists_root_of_degree_eq_one (h : degree p = 1) : ∃ x, is_root p x :=
⟨-(p.coeff 0 / p.coeff 1),
  have p.coeff 1 ≠ 0,
    by rw ← nat_degree_eq_of_degree_eq_some h;
    exact mt leading_coeff_eq_zero.1 (λ h0, by simpa [h0] using h),
  by conv in p { rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1, by rw h; exact le_refl _)] };
    simp [is_root, mul_div_cancel' _ this]⟩

lemma coeff_inv_units (u : units (polynomial α)) (n : ℕ) :
  ((↑u : polynomial α).coeff n)⁻¹ = ((↑u⁻¹ : polynomial α).coeff n) :=
begin
  rw [eq_C_of_degree_eq_zero (degree_coe_units u), eq_C_of_degree_eq_zero (degree_coe_units u⁻¹),
    coeff_C, coeff_C, inv_eq_one_div],
  split_ifs,
  { rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
      coeff_zero_eq_eval_zero, ← eval_mul, ← units.coe_mul, inv_mul_self];
    simp },
  { simp }
end

instance : normalization_domain (polynomial α) :=
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

lemma coe_norm_unit (hp : p ≠ 0) : (norm_unit p : polynomial α) = C p.leading_coeff⁻¹ :=
show ↑(dite _ _ _) = C p.leading_coeff⁻¹, by rw dif_neg hp; refl

end field

section derivative
variables [comm_semiring α] [decidable_eq α]

/-- `derivative p` formal derivative of the polynomial `p` -/
def derivative (p : polynomial α) : polynomial α := p.sum (λn a, C (a * n) * X^(n - 1))

lemma coeff_derivative (p : polynomial α) (n : ℕ) : coeff (derivative p) n = coeff p (n + 1) * (n + 1) :=
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

@[simp] lemma derivative_zero : derivative (0 : polynomial α) = 0 :=
finsupp.sum_zero_index

lemma derivative_monomial (a : α) (n : ℕ) : derivative (C a * X ^ n) = C (a * n) * X^(n - 1) :=
by rw [← single_eq_C_mul_X, ← single_eq_C_mul_X, derivative, sum_single_index, single_eq_C_mul_X];
  simp only [zero_mul, C_0]; refl

@[simp] lemma derivative_C {a : α} : derivative (C a) = 0 :=
suffices derivative (C a * X^0) = C (a * 0:α) * X ^ 0,
  by simpa only [mul_one, zero_mul, C_0, mul_zero, pow_zero],
derivative_monomial a 0

@[simp] lemma derivative_X : derivative (X : polynomial α) = 1 :=
suffices derivative (C (1:α) * X^1) = C (1 * (1:ℕ)) * X ^ 0,
  by simpa only [mul_one, one_mul, C_1, pow_one, nat.cast_one, pow_zero],
derivative_monomial 1 1

@[simp] lemma derivative_one : derivative (1 : polynomial α) = 0 :=
derivative_C

@[simp] lemma derivative_add {f g : polynomial α} :
  derivative (f + g) = derivative f + derivative g :=
by refine finsupp.sum_add_index _ _; intros;
simp only [add_mul, zero_mul, C_0, C_add, C_mul]

instance : is_add_monoid_hom (derivative : polynomial α → polynomial α) :=
by refine_struct {..}; simp

@[simp] lemma derivative_sum {s : finset β} {f : β → polynomial α} :
  derivative (s.sum f) = s.sum (λb, derivative (f b)) :=
(finset.sum_hom derivative).symm

@[simp] lemma derivative_mul {f g : polynomial α} :
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

lemma derivative_eval (p : polynomial α) (x : α) : p.derivative.eval x = p.sum (λ n a, (a * n)*x^(n-1)) :=
by simp [derivative, eval_sum, eval_pow]

end derivative

section domain
variables [integral_domain α] [decidable_eq α]

lemma mem_support_derivative [char_zero α] (p : polynomial α) (n : ℕ) :
  n ∈ (derivative p).support ↔ n + 1 ∈ p.support :=
suffices (¬(coeff p (n + 1) = 0 ∨ ((n + 1:ℕ) : α) = 0)) ↔ coeff p (n + 1) ≠ 0,
  by simpa only [coeff_derivative, apply_eq_coeff, mem_support_iff, ne.def, mul_eq_zero],
by rw [nat.cast_eq_zero]; simp only [nat.succ_ne_zero, or_false]

@[simp] lemma degree_derivative_eq [char_zero α] (p : polynomial α) (hp : 0 < nat_degree p) :
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

def pow_add_expansion {α : Type*} [comm_semiring α] (x y : α) : ∀ (n : ℕ),
  {k // (x + y)^n = x^n + n*x^(n-1)*y + k * y^2}
| 0 := ⟨0, by simp⟩
| 1 := ⟨0, by simp⟩
| (n+2) :=
  begin
    cases pow_add_expansion (n+1) with z hz,
    rw [_root_.pow_succ, hz],
    existsi (x*z + (n+1)*x^n+z*y),
    simp [_root_.pow_succ],
    ring -- expensive!
  end

variables [comm_ring α] [decidable_eq α]

private def poly_binom_aux1 (x y : α) (e : ℕ) (a : α) :
  {k : α // a * (x + y)^e = a * (x^e + e*x^(e-1)*y + k*y^2)} :=
begin
  existsi (pow_add_expansion x y e).val,
  congr,
  apply (pow_add_expansion _ _ _).property
end

private lemma poly_binom_aux2 (f : polynomial α) (x y : α) :
  f.eval (x + y) = f.sum (λ e a, a * (x^e + e*x^(e-1)*y + (poly_binom_aux1 x y e a).val*y^2)) :=
begin
  unfold eval eval₂, congr, ext,
  apply (poly_binom_aux1 x y _ _).property
end

private lemma poly_binom_aux3 (f : polynomial α) (x y : α) : f.eval (x + y) =
  f.sum (λ e a, a * x^e) +
  f.sum (λ e a, (a * e * x^(e-1)) * y) +
  f.sum (λ e a, (a *(poly_binom_aux1 x y e a).val)*y^2) :=
by rw poly_binom_aux2; simp [left_distrib, finsupp.sum_add, mul_assoc]

def binom_expansion (f : polynomial α) (x y : α) :
  {k : α // f.eval (x + y) = f.eval x + (f.derivative.eval x) * y + k * y^2} :=
begin
  existsi f.sum (λ e a, a *((poly_binom_aux1 x y e a).val)),
  rw poly_binom_aux3,
  congr,
  { rw derivative_eval, symmetry,
    apply finsupp.sum_mul },
  { symmetry, apply finsupp.sum_mul }
end

def pow_sub_pow_factor (x y : α) : Π {i : ℕ},{z : α // x^i - y^i = z*(x - y)}
| 0 := ⟨0, by simp⟩ --sorry --false.elim $ not_lt_of_ge h zero_lt_one
| 1 := ⟨1, by simp⟩
| (k+2) :=
  begin
    cases pow_sub_pow_factor with z hz,
    existsi z*x + y^(k+1),
    rw [_root_.pow_succ x, _root_.pow_succ y, ←sub_add_sub_cancel (x*x^(k+1)) (x*y^(k+1)),
        ←mul_sub x, hz],
    simp only [_root_.pow_succ],
    ring
  end

def eval_sub_factor (f : polynomial α) (x y : α) :
  {z : α // f.eval x - f.eval y = z*(x - y)} :=
begin
  existsi f.sum (λ a b, b * (pow_sub_pow_factor x y).val),
  unfold eval eval₂,
  rw [←finsupp.sum_sub],
  have : finsupp.sum f (λ (a : ℕ) (b : α), b * (pow_sub_pow_factor x y).val) * (x - y) =
    finsupp.sum f (λ (a : ℕ) (b : α), b * (pow_sub_pow_factor x y).val * (x - y)),
  { apply finsupp.sum_mul },
  rw this,
  congr, ext e a,
  rw [mul_assoc, ←(pow_sub_pow_factor x y).property],
  simp [left_distrib]
end

end identities

end polynomial
