/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro

Multivariate Polynomial
-/
import data.finsupp linear_algebra.basic algebra.ring data.polynomial data.equiv.algebra

open set function finsupp lattice

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `α` is the coefficient ring -/
def mv_polynomial (σ : Type*) (α : Type*) [comm_semiring α] := (σ →₀ ℕ) →₀ α

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}
variables [decidable_eq σ] [decidable_eq α]

section comm_semiring
variables [comm_semiring α] {p q : mv_polynomial σ α}

instance : decidable_eq (mv_polynomial σ α) := finsupp.decidable_eq
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

lemma C_mul_monomial : C a * monomial s a' = monomial s (a * a') :=
by simp [C, monomial, single_mul_single]

@[simp] lemma C_add : (C (a + a') : mv_polynomial σ α) = C a + C a' := single_add

@[simp] lemma C_mul : (C (a * a') : mv_polynomial σ α) = C a * C a' := C_mul_monomial.symm

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

lemma hom_eq_hom [semiring γ]
  (f g : mv_polynomial σ α → γ) (hf : is_semiring_hom f) (hg : is_semiring_hom g)
  (hC : ∀a:α, f (C a) = g (C a)) (hX : ∀n:σ, f (X n) = g (X n)) (p : mv_polynomial σ α) :
  f p = g p :=
mv_polynomial.induction_on p hC
  begin assume p q hp hq, rw [is_semiring_hom.map_add f, is_semiring_hom.map_add g, hp, hq] end
  begin assume p n hp, rw [is_semiring_hom.map_mul f, is_semiring_hom.map_mul g, hp, hX] end

lemma is_id (f : mv_polynomial σ α → mv_polynomial σ α) (hf : is_semiring_hom f)
  (hC : ∀a:α, f (C a) = (C a)) (hX : ∀n:σ, f (X n) = (X n)) (p : mv_polynomial σ α) :
  f p = p :=
hom_eq_hom f id hf is_semiring_hom.id hC hX p

section eval₂
variables [comm_semiring β]
variables (f : α → β) (g : σ → β)

/-- Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target -/
def eval₂ (p : mv_polynomial σ α) : β :=
p.sum (λs a, f a * s.prod (λn e, g n ^ e))

@[simp] lemma eval₂_zero : (0 : mv_polynomial σ α).eval₂ f g = 0 :=
finsupp.sum_zero_index

variables [is_semiring_hom f]

@[simp] lemma eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g :=
finsupp.sum_add_index
  (by simp [is_semiring_hom.map_zero f])
  (by simp [add_mul, is_semiring_hom.map_add f])

@[simp] lemma eval₂_monomial : (monomial s a).eval₂ f g = f a * s.prod (λn e, g n ^ e) :=
finsupp.sum_single_index (by simp [is_semiring_hom.map_zero f])

@[simp] lemma eval₂_C (a) : (C a).eval₂ f g = f a :=
by simp [eval₂_monomial, C, prod_zero_index]

@[simp] lemma eval₂_one : (1 : mv_polynomial σ α).eval₂ f g = 1 :=
(eval₂_C _ _ _).trans (is_semiring_hom.map_one f)

@[simp] lemma eval₂_X (n) : (X n).eval₂ f g = g n :=
by simp [eval₂_monomial,
  is_semiring_hom.map_one f, X, prod_single_index, pow_one]

lemma eval₂_mul_monomial :
  ∀{s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.prod (λn e, g n ^ e) :=
begin
  apply mv_polynomial.induction_on p,
  { assume a' s a,
    simp [C_mul_monomial, eval₂_monomial, is_semiring_hom.map_mul f] },
  { assume p q ih_p ih_q, simp [add_mul, eval₂_add, ih_p, ih_q] },
  { assume p n ih s a,
    from calc (p * X n * monomial s a).eval₂ f g = (p * monomial (single n 1 + s) a).eval₂ f g :
        by simp [monomial_single_add, -add_comm, pow_one, mul_assoc]
      ... = (p * monomial (single n 1) 1).eval₂ f g * f a * s.prod (λn e, g n ^ e) :
        by simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
          is_semiring_hom.map_one f, -add_comm] }
end

lemma eval₂_mul : ∀{p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g :=
begin
  apply mv_polynomial.induction_on q,
  { simp [C, eval₂_monomial, eval₂_mul_monomial, prod_zero_index] },
  { simp [mul_add, eval₂_add] {contextual := tt} },
  { simp [X, eval₂_monomial, eval₂_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

lemma eval₂_pow {p:mv_polynomial σ α} : ∀{n:ℕ}, (p ^ n).eval₂ f g = (p.eval₂ f g)^n
| 0       := eval₂_one _ _
| (n + 1) := by rw [pow_add, pow_one, pow_add, pow_one, eval₂_mul, eval₂_pow]

instance eval₂.is_semiring_hom : is_semiring_hom (eval₂ f g) :=
{ map_zero := eval₂_zero _ _,
  map_one := eval₂_one _ _,
  map_add := λ p q, eval₂_add _ _,
  map_mul := λ p q, eval₂_mul _ _ }

lemma eval₂_comp_left {γ} [comm_semiring γ]
  (k : β → γ) [is_semiring_hom k]
  (f : α → β) [is_semiring_hom f] (g : σ → β)
  (p) : k (eval₂ f g p) = eval₂ (k ∘ f) (k ∘ g) p :=
by apply mv_polynomial.induction_on p; simp [
  eval₂_add, is_semiring_hom.map_add k,
  eval₂_mul, is_semiring_hom.map_mul k] {contextual := tt}

lemma eval₂_eta (p : mv_polynomial σ α) : eval₂ C X p = p :=
by apply mv_polynomial.induction_on p;
   simp [eval₂_add, eval₂_mul] {contextual := tt}

end eval₂

section eval
variables {f : σ → α}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval (f : σ → α) : mv_polynomial σ α → α := eval₂ id f

@[simp] lemma eval_zero : (0 : mv_polynomial σ α).eval f = 0 := eval₂_zero _ _

@[simp] lemma eval_add : (p + q).eval f = p.eval f + q.eval f := eval₂_add _ _

lemma eval_monomial : (monomial s a).eval f = a * s.prod (λn e, f n ^ e) :=
eval₂_monomial _ _

@[simp] lemma eval_C : ∀ a, (C a).eval f = a := eval₂_C _ _

@[simp] lemma eval_X : ∀ n, (X n).eval f = f n := eval₂_X _ _

@[simp] lemma eval_mul : (p * q).eval f = p.eval f * q.eval f := eval₂_mul _ _

instance eval.is_semiring_hom : is_semiring_hom (eval f) :=
eval₂.is_semiring_hom _ _

theorem eval_assoc {τ} [decidable_eq τ]
  (f : σ → mv_polynomial τ α) (g : τ → α)
  (p : mv_polynomial σ α) :
  p.eval (eval g ∘ f) = (eval₂ C f p).eval g :=
begin
  rw eval₂_comp_left (eval g),
  unfold eval, congr; funext a; simp
end

end eval

section map
variables [comm_semiring β] [decidable_eq β]
variables (f : α → β) [is_semiring_hom f]

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : mv_polynomial σ α → mv_polynomial σ β := eval₂ (C ∘ f) X

@[simp] theorem map_monomial (s : σ →₀ ℕ) (a : α) : map f (monomial s a) = monomial s (f a) :=
(eval₂_monomial _ _).trans monomial_eq.symm

@[simp] theorem map_C : ∀ (a : α), map f (C a : mv_polynomial σ α) = C (f a) := map_monomial _ _

@[simp] theorem map_X : ∀ (n : σ), map f (X n : mv_polynomial σ α) = X n := eval₂_X _ _

@[simp] theorem map_one : map f (1 : mv_polynomial σ α) = 1 := eval₂_one _ _

@[simp] theorem map_add (p q : mv_polynomial σ α) :
  map f (p + q) = map f p + map f q := eval₂_add _ _

@[simp] theorem map_mul (p q : mv_polynomial σ α) :
  map f (p * q) = map f p * map f q := eval₂_mul _ _

instance map.is_semiring_hom :
  is_semiring_hom (map f : mv_polynomial σ α → mv_polynomial σ β) :=
eval₂.is_semiring_hom _ _

theorem map_id : ∀ (p : mv_polynomial σ α), map id p = p := eval₂_eta

theorem map_map [comm_semiring γ] [decidable_eq γ]
  (g : β → γ) [is_semiring_hom g]
  (p : mv_polynomial σ α) :
  map g (map f p) = map (g ∘ f) p :=
(eval₂_comp_left (map g) (C ∘ f) X p).trans $
by congr; funext a; simp

theorem eval₂_eq_eval_map (g : σ → β) (p : mv_polynomial σ α) :
  p.eval₂ f g = (map f p).eval g :=
begin
  unfold map eval,
  rw eval₂_comp_left (eval₂ id g),
  congr; funext a; simp
end

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
variables {p q : mv_polynomial σ α}

instance : ring (mv_polynomial σ α) := finsupp.to_ring
instance : comm_ring (mv_polynomial σ α) := finsupp.to_comm_ring
instance : has_scalar α (mv_polynomial σ α) := finsupp.to_has_scalar
instance : module α (mv_polynomial σ α) := finsupp.to_module _ α

instance C.is_ring_hom : is_ring_hom (C : α → mv_polynomial σ α) :=
by apply is_ring_hom.of_semiring

variables (σ a a')
lemma C_sub : (C (a - a') : mv_polynomial σ α) = C a - C a' := is_ring_hom.map_sub _

@[simp] lemma C_neg : (C (-a) : mv_polynomial σ α) = -C a := is_ring_hom.map_neg _

variables {σ} (p)
theorem C_mul' : mv_polynomial.C a * p = a • p :=
begin
  apply finsupp.induction p,
  { exact (mul_zero $ mv_polynomial.C a).trans (@smul_zero α (mv_polynomial σ α) _ _ _ a).symm },
  intros p b f haf hb0 ih,
  rw [mul_add, ih, @smul_add α (mv_polynomial σ α) _ _ _ a], congr' 1,
  rw [finsupp.mul_def, finsupp.smul_single, mv_polynomial.C, mv_polynomial.monomial],
  rw [finsupp.sum_single_index, finsupp.sum_single_index, zero_add, smul_eq_mul],
  { rw [mul_zero, finsupp.single_zero] },
  { rw finsupp.sum_single_index,
    all_goals { rw [zero_mul, finsupp.single_zero] } }
end

section eval₂

variables [decidable_eq β] [comm_ring β]
variables (f : α → β) [is_ring_hom f] (g : σ → β)

instance eval₂.is_ring_hom : is_ring_hom (eval₂ f g) :=
by apply is_ring_hom.of_semiring

lemma eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g := is_ring_hom.map_sub _

@[simp] lemma eval₂_neg : (-p).eval₂ f g = -(p.eval₂ f g) := is_ring_hom.map_neg _

end eval₂

section eval

variables (f : σ → α)

instance eval.is_ring_hom : is_ring_hom (eval f) := eval₂.is_ring_hom _ _

lemma eval_sub : (p - q).eval f = p.eval f - q.eval f := is_ring_hom.map_sub _

@[simp] lemma eval_neg : (-p).eval f = -(p.eval f) := is_ring_hom.map_neg _

end eval

section map

variables [decidable_eq β] [comm_ring β]
variables (f : α → β) [is_ring_hom f]

instance map.is_ring_hom : is_ring_hom (map f : mv_polynomial σ α → mv_polynomial σ β) :=
eval₂.is_ring_hom _ _

lemma map_sub : (p - q).map f = p.map f - q.map f := is_ring_hom.map_sub _

@[simp] lemma map_neg : (-p).map f = -(p.map f) := is_ring_hom.map_neg _

end map

end comm_ring

section rename
variables {α} [comm_semiring α] [decidable_eq α] [decidable_eq β] [decidable_eq γ] [decidable_eq δ]

def rename (f : β → γ) : mv_polynomial β α → mv_polynomial γ α :=
eval₂ C (X ∘ f)

instance rename.is_semiring_hom (f : β → γ) :
  is_semiring_hom (rename f : mv_polynomial β α → mv_polynomial γ α) :=
by unfold rename; apply_instance

@[simp] lemma rename_C (f : β → γ) (a : α) : rename f (C a) = C a :=
eval₂_C _ _ _

@[simp] lemma rename_X (f : β → γ) (b : β) : rename f (X b : mv_polynomial β α) = X (f b) :=
eval₂_X _ _ _

lemma rename_rename (f : β → γ) (g : γ → δ) (p : mv_polynomial β α) :
  rename g (rename f p) = rename (g ∘ f) p :=
show rename g (eval₂ C (X ∘ f) p) = _,
  by simp only [eval₂_comp_left (rename g) C (X ∘ f) p, (∘), rename_C, rename_X]; refl

lemma rename_id (p : mv_polynomial β α) : rename id p = p :=
eval₂_eta p

end rename

instance rename.is_ring_hom
  {α} [comm_ring α] [decidable_eq α] [decidable_eq β] [decidable_eq γ] (f : β → γ) :
  is_ring_hom (rename f : mv_polynomial β α → mv_polynomial γ α) :=
@is_ring_hom.of_semiring (mv_polynomial β α) (mv_polynomial γ α) _ _ (rename f)
  (rename.is_semiring_hom f)

section equiv

variables (α) [comm_ring α]
variables [decidable_eq β] [decidable_eq γ] [decidable_eq δ]

def pempty_ring_equiv : mv_polynomial pempty α ≃r α :=
{ to_fun    := mv_polynomial.eval₂ id $ pempty.elim,
  inv_fun   := C,
  left_inv  := is_id _ (by apply_instance) (assume a, by rw [eval₂_C]; refl) (assume a, a.elim),
  right_inv := λ r, eval₂_C _ _ _,
  hom       := eval₂.is_ring_hom _ _ }

def punit_ring_equiv : mv_polynomial punit α ≃r polynomial α :=
{ to_fun    := eval₂ polynomial.C (λu:punit, polynomial.X),
  inv_fun   := polynomial.eval₂ mv_polynomial.C (X punit.star),
  left_inv  :=
    begin
      refine is_id _ _ _ _,
      apply is_semiring_hom.comp (eval₂ polynomial.C (λu:punit, polynomial.X)) _; apply_instance,
      { assume a, rw [eval₂_C, polynomial.eval₂_C] },
      { rintros ⟨⟩, rw [eval₂_X, polynomial.eval₂_X] }
    end,
  right_inv := assume p, polynomial.induction_on p
    (assume a, by rw [polynomial.eval₂_C, mv_polynomial.eval₂_C])
    (assume p q hp hq, by rw [polynomial.eval₂_add, mv_polynomial.eval₂_add, hp, hq])
    (assume p n hp,
      by rw [polynomial.eval₂_mul, polynomial.eval₂_pow, polynomial.eval₂_X, polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]),
  hom       := eval₂.is_ring_hom _ _ }

def ring_equiv_of_equiv (e : β ≃ γ) : mv_polynomial β α ≃r mv_polynomial γ α :=
{ to_fun    := rename e,
  inv_fun   := rename e.symm,
  left_inv  := λ p, by simp only [rename_rename, (∘), e.inverse_apply_apply]; exact rename_id p,
  right_inv := λ p, by simp only [rename_rename, (∘), e.apply_inverse_apply]; exact rename_id p,
  hom       := rename.is_ring_hom e }

def ring_equiv_congr [comm_ring γ] (e : α ≃r γ) : mv_polynomial β α ≃r mv_polynomial β γ :=
{ to_fun    := map e.to_fun,
  inv_fun   := map e.symm.to_fun,
  left_inv  := assume p,
    have (e.symm.to_equiv.to_fun ∘ e.to_equiv.to_fun) = id,
    { ext a, exact e.to_equiv.inverse_apply_apply a },
    by simp only [map_map, this, map_id],
  right_inv := assume p,
    have (e.to_equiv.to_fun ∘ e.symm.to_equiv.to_fun) = id,
    { ext a, exact e.to_equiv.apply_inverse_apply a },
    by simp only [map_map, this, map_id],
  hom       := map.is_ring_hom e.to_fun }

section
variables (β γ δ)

instance ring_on_sum : ring (mv_polynomial (β ⊕ γ) α) := by apply_instance
instance ring_on_iter : ring (mv_polynomial β (mv_polynomial γ α)) := by apply_instance

def sum_to_iter : mv_polynomial (β ⊕ γ) α → mv_polynomial β (mv_polynomial γ α) :=
eval₂ (C ∘ C) (λbc, sum.rec_on bc X (C ∘ X))

instance is_semiring_hom_C_C :
  is_semiring_hom (C ∘ C : α → mv_polynomial β (mv_polynomial γ α)) :=
@is_semiring_hom.comp _ _ _ _ C mv_polynomial.is_semiring_hom _ _ C mv_polynomial.is_semiring_hom

instance is_semiring_hom_sum_to_iter : is_semiring_hom (sum_to_iter α β γ) :=
eval₂.is_semiring_hom _ _

lemma sum_to_iter_C (a : α) : sum_to_iter α β γ (C a) = C (C a) :=
eval₂_C _ _ a

lemma sum_to_iter_Xl (b : β) : sum_to_iter α β γ (X (sum.inl b)) = X b :=
eval₂_X _ _ (sum.inl b)

lemma sum_to_iter_Xr (c : γ) : sum_to_iter α β γ (X (sum.inr c)) = C (X c) :=
eval₂_X _ _ (sum.inr c)

def iter_to_sum : mv_polynomial β (mv_polynomial γ α) → mv_polynomial (β ⊕ γ) α :=
eval₂ (eval₂ C (X ∘ sum.inr)) (X ∘ sum.inl)

section

instance is_semiring_hom_iter_to_sum : is_semiring_hom (iter_to_sum α β γ) :=
eval₂.is_semiring_hom _ _

end

lemma iter_to_sum_C_C (a : α) : iter_to_sum α β γ (C (C a)) = C a :=
eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

lemma iter_to_sum_X (b : β) : iter_to_sum α β γ (X b) = X (sum.inl b) :=
eval₂_X _ _ _

lemma iter_to_sum_C_X (c : γ) : iter_to_sum α β γ (C (X c)) = X (sum.inr c) :=
eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

def mv_polynomial_equiv_mv_polynomial [comm_ring δ]
  (f : mv_polynomial β α → mv_polynomial γ δ) (hf : is_semiring_hom f)
  (g : mv_polynomial γ δ → mv_polynomial β α) (hg : is_semiring_hom g)
  (hfgC : ∀a, f (g (C a)) = C a)
  (hfgX : ∀n, f (g (X n)) = X n)
  (hgfC : ∀a, g (f (C a)) = C a)
  (hgfX : ∀n, g (f (X n)) = X n) :
  mv_polynomial β α ≃r mv_polynomial γ δ :=
{ to_fun    := f, inv_fun := g,
  left_inv  := is_id _ (is_semiring_hom.comp _ _) hgfC hgfX,
  right_inv := is_id _ (is_semiring_hom.comp _ _) hfgC hfgX,
  hom       := is_ring_hom.of_semiring f }

def sum_ring_equiv : mv_polynomial (β ⊕ γ) α ≃r mv_polynomial β (mv_polynomial γ α) :=
begin
  apply @mv_polynomial_equiv_mv_polynomial α (β ⊕ γ) _ _ _ _ _ _ _ _
    (sum_to_iter α β γ) _ (iter_to_sum α β γ) _,
  { assume p,
    apply @hom_eq_hom _ _ _ _ _ _ _ _ _ _ _ _ _ p,
    apply_instance,
    { apply @is_semiring_hom.comp _ _ _ _ _ _ _ _ _ _,
      apply_instance,
      apply @is_semiring_hom.comp _ _ _ _ _ _ _ _ _ _,
      apply_instance,
      { apply @mv_polynomial.is_semiring_hom },
      { apply mv_polynomial.is_semiring_hom_iter_to_sum α β γ },
      { apply mv_polynomial.is_semiring_hom_sum_to_iter α β γ } },
    { apply mv_polynomial.is_semiring_hom },
    { assume a, rw [iter_to_sum_C_C α β γ, sum_to_iter_C α β γ] },
    { assume c, rw [iter_to_sum_C_X α β γ, sum_to_iter_Xr α β γ] } },
  { assume b, rw [iter_to_sum_X α β γ, sum_to_iter_Xl α β γ] },
  { assume a, rw [sum_to_iter_C α β γ, iter_to_sum_C_C α β γ] },
  { assume n, cases n with b c,
    { rw [sum_to_iter_Xl, iter_to_sum_X] },
    { rw [sum_to_iter_Xr, iter_to_sum_C_X] } },
  { apply mv_polynomial.is_semiring_hom_sum_to_iter α β γ },
  { apply mv_polynomial.is_semiring_hom_iter_to_sum α β γ }
end

instance option_ring : ring (mv_polynomial (option β) α) :=
mv_polynomial.ring

instance polynomial_ring : ring (polynomial (mv_polynomial β α)) :=
@comm_ring.to_ring _ polynomial.comm_ring

instance polynomial_ring2 : ring (mv_polynomial β (polynomial α)) :=
by apply_instance

def option_equiv_left : mv_polynomial (option β) α ≃r polynomial (mv_polynomial β α) :=
(ring_equiv_of_equiv α $ (equiv.option_equiv_sum_punit β).trans (equiv.sum_comm _ _)).trans $
(sum_ring_equiv α _ _).trans $
punit_ring_equiv _

def option_equiv_right : mv_polynomial (option β) α ≃r mv_polynomial β (polynomial α) :=
(ring_equiv_of_equiv α $ equiv.option_equiv_sum_punit.{0} β).trans $
(sum_ring_equiv α β unit).trans $
ring_equiv_congr (mv_polynomial unit α) (punit_ring_equiv α)

end

end equiv

end mv_polynomial
