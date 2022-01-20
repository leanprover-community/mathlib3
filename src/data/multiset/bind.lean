/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.big_operators.multiset

/-!
# Bind operation for multisets

This file defines a few basic operations on `multiset`, notably the monadic bind.

## Main declarations

* `multiset.join`: The join, aka union or sum, of multisets.
* `multiset.bind`: The bind of a multiset-indexed family of multisets.
* `multiset.product`: Cartesian product of two multisets.
* `multiset.sigma`: Disjoint sum of multisets in a sigma type.
-/

variables {α β γ δ : Type*}

namespace multiset

/-! ### Join -/

/-- `join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.
     join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2} -/
def join : multiset (multiset α) → multiset α := sum

lemma coe_join : ∀ L : list (list α),
  join (L.map (@coe _ (multiset α) _) : multiset (multiset α)) = L.join
| []       := rfl
| (l :: L) := congr_arg (λ s : multiset α, ↑l + s) (coe_join L)

@[simp] lemma join_zero : @join α 0 = 0 := rfl
@[simp] lemma join_cons (s S) : @join α (s ::ₘ S) = s + join S := sum_cons _ _
@[simp] lemma join_add (S T) : @join α (S + T) = join S + join T := sum_add _ _
@[simp] lemma singleton_join (a) : join ({a} : multiset (multiset α)) = a := sum_singleton _

@[simp] lemma mem_join {a S} : a ∈ @join α S ↔ ∃ s ∈ S, a ∈ s :=
multiset.induction_on S (by simp) $
  by simp [or_and_distrib_right, exists_or_distrib] {contextual := tt}

@[simp] lemma card_join (S) : card (@join α S) = sum (map card S) :=
multiset.induction_on S (by simp) (by simp)

lemma rel_join {r : α → β → Prop} {s t} (h : rel (rel r) s t) : rel r s.join t.join :=
begin
  induction h,
  case rel.zero { simp },
  case rel.cons : a b s t hab hst ih { simpa using hab.add ih }
end

/-! ### Bind -/

section bind
variables (a : α) (s t : multiset α) (f g : α → multiset β)

/-- `s.bind f` is the monad bind operation, defined as `(s.map f).join`. It is the union of `f a` as
`a` ranges over `s`. -/
def bind (s : multiset α) (f : α → multiset β) : multiset β := (s.map f).join

@[simp] lemma coe_bind (l : list α) (f : α → list β) : @bind α β l (λ a, f a) = l.bind f :=
by rw [list.bind, ←coe_join, list.map_map]; refl

@[simp] lemma zero_bind : bind 0 f = 0 := rfl
@[simp] lemma cons_bind : (a ::ₘ s).bind f = f a + s.bind f := by simp [bind]
@[simp] lemma singleton_bind : bind {a} f = f a := by simp [bind]
@[simp] lemma add_bind : (s + t).bind f = s.bind f + t.bind f := by simp [bind]
@[simp] lemma bind_zero : s.bind (λ a, 0 : α → multiset β) = 0 := by simp [bind, join, nsmul_zero]
@[simp] lemma bind_add : s.bind (λ a, f a + g a) = s.bind f + s.bind g := by simp [bind, join]

@[simp] lemma bind_cons (f : α → β) (g : α → multiset β) :
  s.bind (λ a, f a ::ₘ g a) = map f s + s.bind g :=
multiset.induction_on s (by simp) (by simp [add_comm, add_left_comm] {contextual := tt})

@[simp] lemma bind_singleton (f : α → β) : s.bind (λ x, ({f x} : multiset β)) = map f s :=
multiset.induction_on s (by rw [zero_bind, map_zero]) (by simp [singleton_add])

@[simp] lemma mem_bind {b s} {f : α → multiset β} : b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a :=
by simp [bind]; simp [-exists_and_distrib_right, exists_and_distrib_right.symm];
   rw exists_swap; simp [and_assoc]

@[simp] lemma card_bind : (s.bind f).card = (s.map (card ∘ f)).sum := by simp [bind]

lemma bind_congr {f g : α → multiset β} {m : multiset α} :
  (∀ a ∈ m, f a = g a) → bind m f = bind m g :=
by simp [bind] {contextual := tt}

lemma bind_hcongr {β' : Type*} {m : multiset α} {f : α → multiset β} {f' : α → multiset β'}
  (h : β = β') (hf : ∀a ∈ m, f a == f' a) :
  bind m f == bind m f' :=
begin subst h, simp at hf, simp [bind_congr hf] end

lemma map_bind (m : multiset α) (n : α → multiset β) (f : β → γ) :
  map f (bind m n) = bind m (λ a, map f (n a)) :=
multiset.induction_on m (by simp) (by simp {contextual := tt})

lemma bind_map (m : multiset α) (n : β → multiset γ) (f : α → β) :
  bind (map f m) n = bind m (λ a, n (f a)) :=
multiset.induction_on m (by simp) (by simp {contextual := tt})

lemma bind_assoc {s : multiset α} {f : α → multiset β} {g : β → multiset γ} :
  (s.bind f).bind g = s.bind (λ a, (f a).bind g) :=
multiset.induction_on s (by simp) (by simp {contextual := tt})

lemma bind_bind (m : multiset α) (n : multiset β) {f : α → β → multiset γ} :
  (bind m $ λ a, bind n $ λ b, f a b) = (bind n $ λ b, bind m $ λ a, f a b) :=
multiset.induction_on m (by simp) (by simp {contextual := tt})

lemma bind_map_comm (m : multiset α) (n : multiset β) {f : α → β → γ} :
  (bind m $ λ a, n.map $ λ b, f a b) = (bind n $ λ b, m.map $ λ a, f a b) :=
multiset.induction_on m (by simp) (by simp {contextual := tt})

@[simp, to_additive]
lemma prod_bind [comm_monoid β] (s : multiset α) (t : α → multiset β) :
  (s.bind t).prod = (s.map $ λ a, (t a).prod).prod :=
multiset.induction_on s (by simp) (assume a s ih, by simp [ih, cons_bind])

lemma rel_bind {r : α → β → Prop} {p : γ → δ → Prop} {s t} {f : α → multiset γ} {g : β → multiset δ}
  (h : (r ⇒ rel p) f g) (hst : rel r s t) :
  rel p (s.bind f) (t.bind g) :=
by { apply rel_join, rw rel_map, exact hst.mono (λ a ha b hb hr, h hr) }

lemma count_sum [decidable_eq α] {m : multiset β} {f : β → multiset α} {a : α} :
  count a (map f m).sum = sum (m.map $ λ b, count a $ f b) :=
multiset.induction_on m (by simp) ( by simp)

lemma count_bind [decidable_eq α] {m : multiset β} {f : β → multiset α} {a : α} :
  count a (bind m f) = sum (m.map $ λ b, count a $ f b) := count_sum

end bind

/-! ### Product of two multisets -/

section product
variables (a : α) (b : β) (s : multiset α) (t : multiset β)

/-- The multiplicity of `(a, b)` in `s.product t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`. -/
def product (s : multiset α) (t : multiset β) : multiset (α × β) := s.bind $ λ a, t.map $ prod.mk a

@[simp] lemma coe_product (l₁ : list α) (l₂ : list β) : @product α β l₁ l₂ = l₁.product l₂ :=
by { rw [product, list.product, ←coe_bind], simp }

@[simp] lemma zero_product : @product α β 0 t = 0 := rfl
--TODO: Add `product_zero`

@[simp] lemma cons_product : (a ::ₘ s).product t = map (prod.mk a) t + s.product t :=
by simp [product]

@[simp] lemma product_singleton : ({a} : multiset α).product ({b} : multiset β) = {(a, b)} :=
by simp only [product, bind_singleton, map_singleton]

@[simp] lemma add_product (s t : multiset α) (u : multiset β) :
  (s + t).product u = s.product u + product t u :=
by simp [product]

@[simp] lemma product_add (s : multiset α) : ∀ t u : multiset β,
  s.product (t + u) = s.product t + s.product u :=
multiset.induction_on s (λ t u, rfl) $ λ a s IH t u,
  by rw [cons_product, IH]; simp; cc

@[simp] lemma mem_product {s t} : ∀ {p : α × β}, p ∈ @product α β s t ↔ p.1 ∈ s ∧ p.2 ∈ t
| (a, b) := by simp [product, and.left_comm]

@[simp] lemma card_product : (s.product t).card = s.card * t.card :=
by simp [product, repeat, (∘), mul_comm]

end product

/-! ### Disjoint sum of multisets -/

section sigma
variables {σ : α → Type*} (a : α) (s : multiset α) (t : Π a, multiset (σ a))

/-- `sigma s t` is the dependent version of `product`. It is the sum of
  `(a, b)` as `a` ranges over `s` and `b` ranges over `t a`. -/
protected def sigma (s : multiset α) (t : Π a, multiset (σ a)) : multiset (Σ a, σ a) :=
s.bind $ λ a, (t a).map $ sigma.mk a

@[simp] lemma coe_sigma (l₁ : list α) (l₂ : Π a, list (σ a)) :
  @multiset.sigma α σ l₁ (λ a, l₂ a) = l₁.sigma l₂ :=
by rw [multiset.sigma, list.sigma, ←coe_bind]; simp

@[simp] lemma zero_sigma : @multiset.sigma α σ 0 t = 0 := rfl

@[simp] lemma cons_sigma : (a ::ₘ s).sigma t = (t a).map (sigma.mk a) + s.sigma t :=
by simp [multiset.sigma]

@[simp] lemma sigma_singleton (b : α → β) :
  ({a} : multiset α).sigma (λ a, ({b a} : multiset β)) = {⟨a, b a⟩} := rfl

@[simp] lemma add_sigma (s t : multiset α) (u : Π a, multiset (σ a)) :
  (s + t).sigma u = s.sigma u + t.sigma u :=
by simp [multiset.sigma]

@[simp] lemma sigma_add : ∀ t u : Π a, multiset (σ a),
  s.sigma (λ a, t a + u a) = s.sigma t + s.sigma u :=
multiset.induction_on s (λ t u, rfl) $ λ a s IH t u,
  by rw [cons_sigma, IH]; simp; cc

@[simp] lemma mem_sigma {s t} : ∀ {p : Σ a, σ a},
  p ∈ @multiset.sigma α σ s t ↔ p.1 ∈ s ∧ p.2 ∈ t p.1
| ⟨a, b⟩ := by simp [multiset.sigma, and_assoc, and.left_comm]

@[simp] lemma card_sigma :
  card (s.sigma t) = sum (map (λ a, card (t a)) s) :=
by simp [multiset.sigma, (∘)]

end sigma
end multiset
