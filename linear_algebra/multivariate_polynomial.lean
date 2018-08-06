/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro

Multivariate Polynomial
-/
import data.finsupp linear_algebra.basic algebra.ring

open set function finsupp lattice

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `α` is the coefficient ring -/
def mv_polynomial (σ : Type*) (α : Type*) [comm_semiring α] := (σ →₀ ℕ) →₀ α

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}
variables [decidable_eq σ] [decidable_eq α]

section comm_semiring
variables [comm_semiring α] {p q : mv_polynomial σ α}

instance : has_zero (mv_polynomial σ α) := finsupp.has_zero
instance : has_one (mv_polynomial σ α) := finsupp.has_one
instance : has_add (mv_polynomial σ α) := finsupp.has_add
instance : has_mul (mv_polynomial σ α) := finsupp.has_mul
instance : comm_semiring (mv_polynomial σ α) := finsupp.to_comm_semiring

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (s : σ →₀ ℕ) (a : α) : mv_polynomial σ α := single s a

/-- `C a` is the constant polynomial with value `a` -/
def C (a : α) : mv_polynomial σ α := monomial 0 a

/-- `X n` is the polynomial with value X_n -/
def X (n : σ) : mv_polynomial σ α := monomial (single n 1) 1

@[simp] lemma C_0 : C 0 = (0 : mv_polynomial σ α) := by simp [C, monomial]; refl

@[simp] lemma C_1 : C 1 = (1 : mv_polynomial σ α) := rfl

@[simp] lemma C_mul_monomial : C a * monomial s a' = monomial s (a * a') :=
by simp [C, monomial, single_mul_single]

lemma C_add : (C (a + a') : mv_polynomial σ α) = C a + C a' := single_add

lemma C_mul : (C (a * a') : mv_polynomial σ α) = C a * C a' := C_mul_monomial.symm

instance : is_semiring_hom (C : α → mv_polynomial σ α) :=
{ map_zero := C_0,
  map_one := C_1,
  map_add := λ a a', C_add,
  map_mul := λ a a', C_mul }

lemma X_pow_eq_single : X n ^ e = monomial (single n e) (1 : α) :=
begin
  induction e,
  { simp [X], refl },
  { simp [pow_succ, e_ih],
    simp [X, monomial, single_mul_single, nat.succ_eq_add_one] }
end

lemma monomial_add_single : monomial (s + single n e) a = (monomial s a * X n ^ e):=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_single_add : monomial (single n e + s) a = (X n ^ e * monomial s a):=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_eq : monomial s a = C a * (s.prod $ λn e, X n ^ e : mv_polynomial σ α) :=
begin
  apply @finsupp.induction σ ℕ _ _ _ _ s,
  { simp [C, prod_zero_index]; exact (mul_one _).symm },
  { assume n e s hns he ih,
    simp [prod_add_index, prod_single_index, pow_zero, pow_add, (mul_assoc _ _ _).symm, ih.symm,
      monomial_add_single] }
end

@[recursor 7]
lemma induction_on {M : mv_polynomial σ α → Prop} (p : mv_polynomial σ α)
  (h_C : ∀a, M (C a)) (h_add : ∀p q, M p → M q → M (p + q)) (h_X : ∀p n, M p → M (p * X n)) :
  M p :=
have ∀s a, M (monomial s a),
begin
  assume s a,
  apply @finsupp.induction σ ℕ _ _ _ _ s,
  { show M (monomial 0 a), from h_C a, },
  { assume n e p hpn he ih,
    have : ∀e:ℕ, M (monomial p a * X n ^ e),
    { intro e,
      induction e,
      { simp [ih] },
      { simp [ih, pow_succ', (mul_assoc _ _ _).symm, h_X, e_ih] } },
    simp [monomial_add_single, this] }
end,
finsupp.induction p
  (by have : M (C 0) := h_C 0; rwa [C_0] at this)
  (assume s a p hsp ha hp, h_add _ _ (this s a) hp)

section map₂
variables [comm_semiring β]
variables (f : σ → β) (g : α → β) [is_semiring_hom g] 

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables
  and a ring hom `g` from the scalar ring to the target -/
def map₂ (p : mv_polynomial σ α) : β :=
p.sum (λs a, g a * s.prod (λn e, f n ^ e))

@[simp] lemma map₂_zero : (0 : mv_polynomial σ α).map₂ f g = 0 :=
finsupp.sum_zero_index

lemma map₂_add : (p + q).map₂ f g = p.map₂ f g + q.map₂ f g :=
finsupp.sum_add_index
  (by simp [is_semiring_hom.map_zero g])
  (by simp [add_mul, is_semiring_hom.map_add g])

lemma map₂_monomial : (monomial s a).map₂ f g = g a * s.prod (λn e, f n ^ e) :=
finsupp.sum_single_index (by simp [is_semiring_hom.map_zero g])

@[simp] lemma map₂_C : (C a).map₂ f g = g a :=
by simp [map₂_monomial, C, prod_zero_index]

@[simp] lemma map₂_one : (1 : mv_polynomial σ α).map₂ f g = 1 :=
(map₂_C _ _).trans (is_semiring_hom.map_one g)

@[simp] lemma map₂_X : (X n).map₂ f g = f n :=
by simp [map₂_monomial,
  is_semiring_hom.map_one g, X, prod_single_index, pow_one]

lemma map₂_mul_monomial :
  ∀{s a}, (p * monomial s a).map₂ f g = p.map₂ f g * g a * s.prod (λn e, f n ^ e) :=
begin
  apply mv_polynomial.induction_on p,
  { assume a' s a,
    simp [C_mul_monomial, map₂_monomial, is_semiring_hom.map_mul g] },
  { assume p q ih_p ih_q, simp [add_mul, map₂_add, ih_p, ih_q] },
  { assume p n ih s a,
    from calc (p * X n * monomial s a).map₂ f g = (p * monomial (single n 1 + s) a).map₂ f g :
        by simp [monomial_single_add, -add_comm, pow_one, mul_assoc]
      ... = (p * monomial (single n 1) 1).map₂ f g * g a * s.prod (λn e, f n ^ e) :
        by simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
          is_semiring_hom.map_one g, -add_comm] }
end

lemma map₂_mul : ∀{p}, (p * q).map₂ f g = p.map₂ f g * q.map₂ f g :=
begin
  apply mv_polynomial.induction_on q,
  { simp [C, map₂_monomial, map₂_mul_monomial, prod_zero_index] },
  { simp [mul_add, map₂_add] {contextual := tt} },
  { simp [X, map₂_monomial, map₂_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

instance map₂.is_semiring_hom : is_semiring_hom (map₂ f g) :=
{ map_zero := map₂_zero _ _,
  map_one := map₂_one _ _,
  map_add := λ p q, map₂_add _ _,
  map_mul := λ p q, map₂_mul _ _ }

end map₂

section eval
variables {f : σ → α}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval (f : σ → α) : mv_polynomial σ α → α := map₂ f id

@[simp] lemma eval_zero : (0 : mv_polynomial σ α).eval f = 0 := map₂_zero _ _

lemma eval_add : (p + q).eval f = p.eval f + q.eval f := map₂_add _ _

lemma eval_monomial : (monomial s a).eval f = a * s.prod (λn e, f n ^ e) :=
map₂_monomial _ _

@[simp] lemma eval_C : (C a).eval f = a := map₂_C _ _

@[simp] lemma eval_X : (X n).eval f = f n := map₂_X _ _

lemma eval_mul : (p * q).eval f = p.eval f * q.eval f := map₂_mul _ _

instance eval.is_semiring_hom : is_semiring_hom (eval f) :=
map₂.is_semiring_hom _ _

end eval

section map
variables [decidable_eq β] [comm_semiring β]
variables (f : α → β) [is_semiring_hom f]

-- `mv_polynomial σ` is a functor (incomplete)
def map : mv_polynomial σ α → mv_polynomial σ β := map₂ X (C ∘ f)

@[simp] theorem map_monomial (s : σ →₀ ℕ) (a : α) : map f (monomial s a) = monomial s (f a) :=
(map₂_monomial _ _).trans monomial_eq.symm

@[simp] theorem map_C (a : α) : map f (C a : mv_polynomial σ α) = C (f a) := map_monomial _ _ _

@[simp] theorem map_X (n : σ) : map f (X n : mv_polynomial σ α) = X n := map₂_X _ _

@[simp] theorem map_one : map f (1 : mv_polynomial σ α) = 1 := map₂_one _ _

@[simp] theorem map_add (p q : mv_polynomial σ α) :
  map f (p + q) = map f p + map f q := map₂_add _ _

@[simp] theorem map_mul (p q : mv_polynomial σ α) :
  map f (p * q) = map f p * map f q := map₂_mul _ _

end map

section vars

/-- `vars p` is the set of variables appearing in the polynomial `p` -/
def vars (p : mv_polynomial σ α) : finset σ := p.support.bind finsupp.support

@[simp] lemma vars_0 : (0 : mv_polynomial σ α).vars = ∅ :=
show (0 : (σ →₀ ℕ) →₀ α).support.bind finsupp.support = ∅, by simp

@[simp] lemma vars_monomial (h : a ≠ 0) : (monomial s a).vars = s.support :=
show (single s a : (σ →₀ ℕ) →₀ α).support.bind finsupp.support = s.support,
  by simp [support_single_ne_zero, h]

@[simp] lemma vars_C : (C a : mv_polynomial σ α).vars = ∅ :=
decidable.by_cases
  (assume h : a = 0, by simp [h])
  (assume h : a ≠ 0, by simp [C, h])

@[simp] lemma vars_X (h : 0 ≠ (1 : α)) : (X n : mv_polynomial σ α).vars = {n} :=
calc (X n : mv_polynomial σ α).vars = (single n 1).support : vars_monomial h.symm
  ... = {n} : by rw [support_single_ne_zero nat.zero_ne_one.symm]

end vars

section degree_of
/-- `degree_of n p` gives the highest power of X_n that appears in `p` -/
def degree_of (n : σ) (p : mv_polynomial σ α) : ℕ := p.support.sup (λs, s n)

end degree_of

section total_degree
/-- `total_degree p` gives the maximum |s| over the monomials X^s in `p` -/
def total_degree (p : mv_polynomial σ α) : ℕ := p.support.sup (λs, s.sum $ λn e, e)

end total_degree

end comm_semiring

section comm_ring
variable [comm_ring α]
instance : ring (mv_polynomial σ α) := finsupp.to_ring
instance : comm_ring (mv_polynomial σ α) := finsupp.to_comm_ring
instance : has_scalar α (mv_polynomial σ α) := finsupp.to_has_scalar
instance : module α (mv_polynomial σ α) := finsupp.to_module

instance C.is_ring_hom : is_ring_hom (C : α → mv_polynomial σ α) :=
is_ring_hom.of_semiring _

instance map₂.is_ring_hom [decidable_eq β] [comm_ring β]
  (f : σ → β) (g : α → β) [is_ring_hom g] : is_ring_hom (map₂ f g) :=
by apply is_ring_hom.of_semiring

instance eval.is_ring_hom (f : σ → α) : is_ring_hom (eval f) := map₂.is_ring_hom _ _

instance map.is_ring_hom [decidable_eq β] [comm_ring β]
  (f : α → β) [is_ring_hom f] :
  is_ring_hom (map f : mv_polynomial σ α → mv_polynomial σ β) :=
map₂.is_ring_hom _ _

end comm_ring

end mv_polynomial
