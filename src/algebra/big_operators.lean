/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import data.finset
import data.nat.enat
import data.equiv.mul_add
import tactic.omega
import tactic.abel

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `finset`).

## Notation

We introduce the following notation, localized in `big_operators`.
To enable the notation, use `open_locale big_operators`.

Let `s` be a `finset α`, and `f : α → β` a function.

* `∏ x in s, f x` is notation for `finset.prod s f` (assuming `β` is a `comm_monoid`)
* `∑ x in s, f x` is notation for `finset.sum s f` (assuming `β` is an `add_comm_monoid`)
* `∏ x, f x` is notation for `finset.prod finset.univ f`
  (assuming `α` is a `fintype` and `β` is a `comm_monoid`)
* `∑ x, f x` is notation for `finset.sum finset.univ f`
  (assuming `α` is a `fintype` and `β` is an `add_comm_monoid`)

-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

theorem directed.finset_le {r : α → α → Prop} [is_trans α r]
  {ι} (hι : nonempty ι) {f : ι → α} (D : directed r f) (s : finset ι) :
  ∃ z, ∀ i ∈ s, r (f i) (f z) :=
show ∃ z, ∀ i ∈ s.1, r (f i) (f z), from
multiset.induction_on s.1 (let ⟨z⟩ := hι in ⟨z, λ _, false.elim⟩) $
λ i s ⟨j, H⟩, let ⟨k, h₁, h₂⟩ := D i j in
⟨k, λ a h, or.cases_on (multiset.mem_cons.1 h)
  (λ h, h.symm ▸ h₁)
  (λ h, trans (H _ h) h₂)⟩

theorem finset.exists_le {α : Type u} [nonempty α] [directed_order α] (s : finset α) :
  ∃ M, ∀ i ∈ s, i ≤ M :=
directed.finset_le (by apply_instance) directed_order.directed s

namespace finset

/-- `∏ x in s, f x` is the product of `f x` as `x` ranges over the elements of the finite set `s`. -/
@[to_additive "`∑ x in s, f` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`."]
protected def prod [comm_monoid β] (s : finset α) (f : α → β) : β := (s.1.map f).prod

end finset

/-
## Operator precedence of `∏` and `∑`

There is no established mathematical convention
for the operator precedence of big operators like `∏` and `∑`.
We will have to make a choice.

Online discussions, such as https://math.stackexchange.com/q/185538/30839
seem to suggest that `∏` and `∑` should have the same precedence,
and that this should be somewhere between `*` and `+`.
The latter have precedence levels `70` and `65` respectively,
and we therefore choose the level `67`.

In practice, this means that parentheses should be placed as follows:
```lean
∑ k in K, (a k + b k) = ∑ k in K, a k + ∑ k in K, b k →
  ∏ k in K, a k * b k = (∏ k in K, a k) * (∏ k in K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/

localized "notation `∑` binders `, ` r:(scoped:67 f, finset.sum finset.univ f) := r" in big_operators
localized "notation `∏` binders `, ` r:(scoped:67 f, finset.prod finset.univ f) := r" in big_operators

localized "notation `∑` binders ` in ` s `, ` r:(scoped:67 f, finset.sum s f) := r" in big_operators
localized "notation `∏` binders ` in ` s `, ` r:(scoped:67 f, finset.prod s f) := r" in big_operators

open_locale big_operators

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

@[to_additive] lemma prod_eq_multiset_prod [comm_monoid β] (s : finset α) (f : α → β) :
  ∏ x in s, f x = (s.1.map f).prod := rfl

@[to_additive]
theorem prod_eq_fold [comm_monoid β] (s : finset α) (f : α → β) : (∏ x in s, f x) = s.fold (*) 1 f := rfl

end finset

@[to_additive]
lemma monoid_hom.map_prod [comm_monoid β] [comm_monoid γ] (g : β →* γ) (f : α → β) (s : finset α) :
  g (∏ x in s, f x) = ∏ x in s, g (f x) :=
by simp only [finset.prod_eq_multiset_prod, g.map_multiset_prod, multiset.map_map]

@[to_additive]
lemma mul_equiv.map_prod [comm_monoid β] [comm_monoid γ] (g : β ≃* γ) (f : α → β) (s : finset α) :
  g (∏ x in s, f x) = ∏ x in s, g (f x) :=
g.to_monoid_hom.map_prod f s

lemma ring_hom.map_list_prod [semiring β] [semiring γ] (f : β →+* γ) (l : list β) :
  f l.prod = (l.map f).prod :=
f.to_monoid_hom.map_list_prod l

lemma ring_hom.map_list_sum [semiring β] [semiring γ] (f : β →+* γ) (l : list β) :
  f l.sum = (l.map f).sum :=
f.to_add_monoid_hom.map_list_sum l

lemma ring_hom.map_multiset_prod [comm_semiring β] [comm_semiring γ] (f : β →+* γ)
  (s : multiset β) :
  f s.prod = (s.map f).prod :=
f.to_monoid_hom.map_multiset_prod s

lemma ring_hom.map_multiset_sum [semiring β] [semiring γ] (f : β →+* γ) (s : multiset β) :
  f s.sum = (s.map f).sum :=
f.to_add_monoid_hom.map_multiset_sum s

lemma ring_hom.map_prod [comm_semiring β] [comm_semiring γ]
  (g : β →+* γ) (f : α → β) (s : finset α) :
  g (∏ x in s, f x) = ∏ x in s, g (f x) :=
g.to_monoid_hom.map_prod f s

lemma ring_hom.map_sum [semiring β] [semiring γ]
  (g : β →+* γ) (f : α → β) (s : finset α) :
  g (∑ x in s, f x) = ∑ x in s, g (f x) :=
g.to_add_monoid_hom.map_sum f s

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

section comm_monoid
variables [comm_monoid β]

@[simp, to_additive]
lemma prod_empty {α : Type u} {f : α → β} : (∏ x in (∅:finset α), f x) = 1 := rfl

@[simp, to_additive]
lemma prod_insert [decidable_eq α] :
  a ∉ s → (∏ x in (insert a s), f x) = f a * ∏ x in s, f x := fold_insert

/-- If a function applied at a point is 1, a product is unchanged by
adding that point, whether or not present, to a `finset`. -/
@[simp, to_additive "If a function applied at a point is 0, a sum is unchanged by
adding that point, whether or not present, to a `finset`."]
lemma prod_insert_one [decidable_eq α] (h : f a = 1) :
  ∏ x in insert a s, f x = ∏ x in s, f x :=
begin
  by_cases hm : a ∈ s,
  { simp_rw insert_eq_of_mem hm },
  { rw [prod_insert hm, h, one_mul] },
end

@[simp, to_additive]
lemma prod_singleton : (∏ x in (singleton a), f x) = f a :=
eq.trans fold_singleton $ mul_one _

@[to_additive]
lemma prod_pair [decidable_eq α] {a b : α} (h : a ≠ b) :
  (∏ x in ({a, b} : finset α), f x) = f a * f b :=
by rw [prod_insert (not_mem_singleton.2 h), prod_singleton]

@[simp, priority 1100] lemma prod_const_one : (∏ x in s, (1 : β)) = 1 :=
by simp only [finset.prod, multiset.map_const, multiset.prod_repeat, one_pow]
@[simp, priority 1100] lemma sum_const_zero {β} {s : finset α} [add_comm_monoid β] :
  (∑ x in s, (0 : β)) = 0 :=
@prod_const_one _ (multiplicative β) _ _
attribute [to_additive] prod_const_one

@[simp, to_additive]
lemma prod_image [decidable_eq α] {s : finset γ} {g : γ → α} :
  (∀x∈s, ∀y∈s, g x = g y → x = y) → (∏ x in (s.image g), f x) = ∏ x in s, f (g x) :=
fold_image

@[simp, to_additive]
lemma prod_map (s : finset α) (e : α ↪ γ) (f : γ → β) :
  (∏ x in (s.map e), f x) = ∏ x in s, f (e x) :=
by rw [finset.prod, finset.map_val, multiset.map_map]; refl

@[congr, to_additive]
lemma prod_congr (h : s₁ = s₂) : (∀x∈s₂, f x = g x) → s₁.prod f = s₂.prod g :=
by rw [h]; exact fold_congr
attribute [congr] finset.sum_congr

@[to_additive]
lemma prod_union_inter [decidable_eq α] :
  (∏ x in (s₁ ∪ s₂), f x) * (∏ x in (s₁ ∩ s₂), f x) = (∏ x in s₁, f x) * (∏ x in s₂, f x) :=
fold_union_inter

@[to_additive]
lemma prod_union [decidable_eq α] (h : disjoint s₁ s₂) :
  (∏ x in (s₁ ∪ s₂), f x) = (∏ x in s₁, f x) * (∏ x in s₂, f x) :=
by rw [←prod_union_inter, (disjoint_iff_inter_eq_empty.mp h)]; exact (mul_one _).symm

@[to_additive]
lemma prod_sdiff [decidable_eq α] (h : s₁ ⊆ s₂) :
  (∏ x in (s₂ \ s₁), f x) * (∏ x in s₁, f x) = (∏ x in s₂, f x) :=
by rw [←prod_union sdiff_disjoint, sdiff_union_of_subset h]

@[simp, to_additive]
lemma prod_sum_elim [decidable_eq (α ⊕ γ)]
  (s : finset α) (t : finset γ) (f : α → β) (g : γ → β) :
  ∏ x in s.image sum.inl ∪ t.image sum.inr, sum.elim f g x = (∏ x in s, f x) * (∏ x in t, g x) :=
begin
  rw [prod_union, prod_image, prod_image],
  { simp only [sum.elim_inl, sum.elim_inr] },
  { exact λ _ _ _ _, sum.inr.inj },
  { exact λ _ _ _ _, sum.inl.inj },
  { rintros i hi,
    erw [finset.mem_inter, finset.mem_image, finset.mem_image] at hi,
    rcases hi with ⟨⟨i, hi, rfl⟩, ⟨j, hj, H⟩⟩,
    cases H }
end

@[to_additive]
lemma prod_bind [decidable_eq α] {s : finset γ} {t : γ → finset α} :
  (∀x∈s, ∀y∈s, x ≠ y → disjoint (t x) (t y)) → (∏ x in (s.bind t), f x) = ∏ x in s, ∏ i in t x, f i :=
by haveI := classical.dec_eq γ; exact
finset.induction_on s (λ _, by simp only [bind_empty, prod_empty])
  (assume x s hxs ih hd,
  have hd' : ∀x∈s, ∀y∈s, x ≠ y → disjoint (t x) (t y),
    from assume _ hx _ hy, hd _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy),
  have ∀y∈s, x ≠ y,
    from assume _ hy h, by rw [←h] at hy; contradiction,
  have ∀y∈s, disjoint (t x) (t y),
    from assume _ hy, hd _ (mem_insert_self _ _) _ (mem_insert_of_mem hy) (this _ hy),
  have disjoint (t x) (finset.bind s t),
    from (disjoint_bind_right _ _ _).mpr this,
  by simp only [bind_insert, prod_insert hxs, prod_union this, ih hd'])

@[to_additive]
lemma prod_product {s : finset γ} {t : finset α} {f : γ×α → β} :
  (∏ x in s.product t, f x) = ∏ x in s, ∏ y in t, f (x, y) :=
begin
  haveI := classical.dec_eq α, haveI := classical.dec_eq γ,
  rw [product_eq_bind, prod_bind],
  { congr, funext, exact prod_image (λ _ _ _ _ H, (prod.mk.inj H).2) },
  simp only [disjoint_iff_ne, mem_image],
  rintros _ _ _ _ h ⟨_, _⟩ ⟨_, _, ⟨_, _⟩⟩ ⟨_, _⟩ ⟨_, _, ⟨_, _⟩⟩ _,
  apply h, cc
end


@[to_additive]
lemma prod_product' {s : finset γ} {t : finset α} {f : γ → α → β} :
  (∏ x in s.product t, f x.fst x.snd) = ∏ x in s, ∏ y in t, f x y :=
by rw prod_product

@[to_additive]
lemma prod_sigma {σ : α → Type*}
  {s : finset α} {t : Πa, finset (σ a)} {f : sigma σ → β} :
  (∏ x in s.sigma t, f x) = ∏ a in s, ∏ s in (t a), f ⟨a, s⟩ :=
by haveI := classical.dec_eq α; haveI := (λ a, classical.dec_eq (σ a)); exact
calc (∏ x in s.sigma t, f x) =
       ∏ x in s.bind (λa, (t a).image (λs, sigma.mk a s)), f x : by rw sigma_eq_bind
  ... = ∏ a in s, ∏ x in (t a).image (λs, sigma.mk a s), f x :
    prod_bind $ assume a₁ ha a₂ ha₂ h,
    by simp only [disjoint_iff_ne, mem_image];
    rintro ⟨_, _⟩ ⟨_, _, _⟩ ⟨_, _⟩ ⟨_, _, _⟩ ⟨_, _⟩; apply h; cc
  ... = ∏ a in s, ∏ s in t a, f ⟨a, s⟩ :
    prod_congr rfl $ λ _ _, prod_image $ λ _ _ _ _ _, by cc

@[to_additive]
lemma prod_image' [decidable_eq α] {s : finset γ} {g : γ → α} (h : γ → β)
  (eq : ∀c∈s, f (g c) = ∏ x in s.filter (λc', g c' = g c), h x) :
  (∏ x in s.image g, f x) = ∏ x in s, h x :=
begin
  letI := classical.dec_eq γ,
  rw [← image_bind_filter_eq s g] {occs := occurrences.pos [2]},
  rw [finset.prod_bind],
  { refine finset.prod_congr rfl (assume a ha, _),
    rcases finset.mem_image.1 ha with ⟨b, hb, rfl⟩,
    exact eq b hb },
  assume a₀ _ a₁ _ ne,
  refine (disjoint_iff_ne.2 _),
  assume c₀ h₀ c₁ h₁,
  rcases mem_filter.1 h₀ with ⟨h₀, rfl⟩,
  rcases mem_filter.1 h₁ with ⟨h₁, rfl⟩,
  exact mt (congr_arg g) ne
end

@[to_additive]
lemma prod_mul_distrib : ∏ x in s, (f x * g x) = (∏ x in s, f x) * (∏ x in s, g x) :=
eq.trans (by rw one_mul; refl) fold_op_distrib

@[to_additive]
lemma prod_comm {s : finset γ} {t : finset α} {f : γ → α → β} :
  (∏ x in s, ∏ y in t, f x y) = (∏ y in t, ∏ x in s, f x y) :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [prod_empty, prod_const_one] },
  { intros _ _ H ih,
    simp only [prod_insert H, prod_mul_distrib, ih] }
end

@[to_additive]
lemma prod_hom [comm_monoid γ] (s : finset α) {f : α → β} (g : β → γ) [is_monoid_hom g] :
  (∏ x in s, g (f x)) = g (∏ x in s, f x) :=
((monoid_hom.of g).map_prod f s).symm

@[to_additive]
lemma prod_hom_rel [comm_monoid γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {s : finset α}
  (h₁ : r 1 1) (h₂ : ∀a b c, r b c → r (f a * b) (g a * c)) : r (∏ x in s, f x) (∏ x in s, g x) :=
by { delta finset.prod, apply multiset.prod_hom_rel; assumption }

@[to_additive]
lemma prod_subset (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → f x = 1) : (∏ x in s₁, f x) = ∏ x in s₂, f x :=
by haveI := classical.dec_eq α; exact
have ∏ x in s₂ \ s₁, f x = ∏ x in s₂ \ s₁, 1,
  from prod_congr rfl $ by simpa only [mem_sdiff, and_imp],
by rw [←prod_sdiff h]; simp only [this, prod_const_one, one_mul]

-- If we use `[decidable_eq β]` here, some rewrites fail because they find a wrong `decidable`
-- instance first; `{∀x, decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
lemma prod_filter_ne_one [∀ x, decidable (f x ≠ 1)] :
  (∏ x in (s.filter $ λx, f x ≠ 1), f x) = (∏ x in s, f x) :=
prod_subset (filter_subset _) $ λ x,
  by { classical, rw [not_imp_comm, mem_filter], exact and.intro }

@[to_additive]
lemma prod_filter (p : α → Prop) [decidable_pred p] (f : α → β) :
  (∏ a in s.filter p, f a) = (∏ a in s, if p a then f a else 1) :=
calc (∏ a in s.filter p, f a) = ∏ a in s.filter p, if p a then f a else 1 :
    prod_congr rfl (assume a h, by rw [if_pos (mem_filter.1 h).2])
  ... = ∏ a in s, if p a then f a else 1 :
    begin
      refine prod_subset (filter_subset s) (assume x hs h, _),
      rw [mem_filter, not_and] at h,
      exact if_neg (h hs)
    end

@[to_additive]
lemma prod_eq_single {s : finset α} {f : α → β} (a : α)
  (h₀ : ∀b∈s, b ≠ a → f b = 1) (h₁ : a ∉ s → f a = 1) : (∏ x in s, f x) = f a :=
by haveI := classical.dec_eq α;
from classical.by_cases
  (assume : a ∈ s,
    calc (∏ x in s, f x) = ∏ x in {a}, f x :
      begin
        refine (prod_subset _ _).symm,
        { intros _ H, rwa mem_singleton.1 H },
        { simpa only [mem_singleton] }
      end
      ... = f a : prod_singleton)
  (assume : a ∉ s,
    (prod_congr rfl $ λ b hb, h₀ b hb $ by rintro rfl; cc).trans $
      prod_const_one.trans (h₁ this).symm)

@[to_additive]
lemma prod_attach {f : α → β} : (∏ x in s.attach, f x.val) = (∏ x in s, f x) :=
by haveI := classical.dec_eq α; exact
  calc (∏ x in s.attach, f x.val) = (∏ x in (s.attach).image subtype.val, f x) :
    by rw [prod_image]; exact assume x _ y _, subtype.eq
  ... = _ : by rw [attach_image_val]

/-- A product over `s.subtype p` equals one over `s.filter p`. -/
@[simp, to_additive "A sum over `s.subtype p` equals one over `s.filter p`."]
lemma prod_subtype_eq_prod_filter (f : α → β) {p : α → Prop} [decidable_pred p] :
  ∏ x in s.subtype p, f x = ∏ x in s.filter p, f x :=
begin
  conv_lhs {
    erw ←prod_map (s.subtype p) (function.embedding.subtype _) f
  },
  exact prod_congr (subtype_map _) (λ x hx, rfl)
end

/-- If all elements of a `finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive "If all elements of a `finset` satisfy the predicate `p`, a sum
over `s.subtype p` equals that sum over `s`."]
lemma prod_subtype_of_mem (f : α → β) {p : α → Prop} [decidable_pred p]
    (h : ∀ x ∈ s, p x) : ∏ x in s.subtype p, f x = ∏ x in s, f x :=
by simp_rw [prod_subtype_eq_prod_filter, filter_true_of_mem h]

/-- A product of a function over a `finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `finset`. -/
@[to_additive "A sum of a function over a `finset` in a subtype equals a
sum in the main type of a function that agrees with the first
function on that `finset`."]
lemma prod_subtype_map_embedding {p : α → Prop} {s : finset {x // p x}} {f : {x // p x} → β}
    {g : α → β} (h : ∀ x : {x // p x}, x ∈ s → g x = f x) :
  ∏ x in s.map (function.embedding.subtype _), g x = ∏ x in s, f x :=
begin
  rw finset.prod_map,
  exact finset.prod_congr rfl h
end

@[to_additive]
lemma prod_eq_one {f : α → β} {s : finset α} (h : ∀x∈s, f x = 1) : (∏ x in s, f x) = 1 :=
calc (∏ x in s, f x) = ∏ x in s, 1 : finset.prod_congr rfl h
  ... = 1 : finset.prod_const_one

@[to_additive] lemma prod_apply_dite {s : finset α} {p : α → Prop} {hp : decidable_pred p}
  (f : Π (x : α), p x → γ) (g : Π (x : α), ¬p x → γ) (h : γ → β) :
  (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
  (∏ x in (s.filter p).attach, h (f x.1 (mem_filter.mp x.2).2)) *
    (∏ x in (s.filter (λ x, ¬ p x)).attach, h (g x.1 (mem_filter.mp x.2).2)) :=
by letI := classical.dec_eq α; exact
calc ∏ x in s, h (if hx : p x then f x hx else g x hx)
    = ∏ x in s.filter p ∪ s.filter (λ x, ¬ p x), h (if hx : p x then f x hx else g x hx) :
  by rw [filter_union_filter_neg_eq]
... = (∏ x in s.filter p, h (if hx : p x then f x hx else g x hx)) *
    (∏ x in s.filter (λ x, ¬ p x), h (if hx : p x then f x hx else g x hx)) :
  prod_union (by simp [disjoint_right] {contextual := tt})
... = (∏ x in (s.filter p).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
    (∏ x in (s.filter (λ x, ¬ p x)).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) :
  congr_arg2 _ prod_attach.symm prod_attach.symm
... = (∏ x in (s.filter p).attach, h (f x.1 (mem_filter.mp x.2).2)) *
    (∏ x in (s.filter (λ x, ¬ p x)).attach, h (g x.1 (mem_filter.mp x.2).2)) :
  congr_arg2 _
    (prod_congr rfl (λ x hx, congr_arg h (dif_pos (mem_filter.mp x.2).2)))
    (prod_congr rfl (λ x hx, congr_arg h (dif_neg (mem_filter.mp x.2).2)))

@[to_additive] lemma prod_apply_ite {s : finset α}
  {p : α → Prop} {hp : decidable_pred p} (f g : α → γ) (h : γ → β) :
  (∏ x in s, h (if p x then f x else g x)) =
  (∏ x in s.filter p, h (f x)) * (∏ x in s.filter (λ x, ¬ p x), h (g x)) :=
trans (prod_apply_dite _ _ _) (congr_arg2 _ (@prod_attach _ _ _ _ (h ∘ f)) (@prod_attach _ _ _ _ (h ∘ g)))

@[to_additive] lemma prod_dite {s : finset α} {p : α → Prop} {hp : decidable_pred p}
  (f : Π (x : α), p x → β) (g : Π (x : α), ¬p x → β) :
  (∏ x in s, if hx : p x then f x hx else g x hx) =
  (∏ x in (s.filter p).attach, f x.1 (mem_filter.mp x.2).2) *
    (∏ x in (s.filter (λ x, ¬ p x)).attach, g x.1 (mem_filter.mp x.2).2) :=
by simp [prod_apply_dite _ _ (λ x, x)]

@[to_additive] lemma prod_ite {s : finset α}
  {p : α → Prop} {hp : decidable_pred p} (f g : α → β) :
  (∏ x in s, if p x then f x else g x) =
  (∏ x in s.filter p, f x) * (∏ x in s.filter (λ x, ¬ p x), g x) :=
by simp [prod_apply_ite _ _ (λ x, x)]

@[simp, to_additive]
lemma prod_dite_eq [decidable_eq α] (s : finset α) (a : α) (b : Π x : α, a = x → β) :
  (∏ x in s, (if h : a = x then b x h else 1)) = ite (a ∈ s) (b a rfl) 1 :=
begin
  split_ifs with h,
  { rw [finset.prod_eq_single a, dif_pos rfl],
    { intros, rw dif_neg, cc },
    { cc } },
  { rw finset.prod_eq_one,
    intros, rw dif_neg, intro, cc }
end

@[simp, to_additive]
lemma prod_dite_eq' [decidable_eq α] (s : finset α) (a : α) (b : Π x : α, x = a → β) :
  (∏ x in s, (if h : x = a then b x h else 1)) = ite (a ∈ s) (b a rfl) 1 :=
begin
  split_ifs with h,
  { rw [finset.prod_eq_single a, dif_pos rfl],
    { intros, rw dif_neg, cc },
    { cc } },
  { rw finset.prod_eq_one,
    intros, rw dif_neg, intro, cc }
end

@[simp, to_additive] lemma prod_ite_eq [decidable_eq α] (s : finset α) (a : α) (b : α → β) :
  (∏ x in s, (ite (a = x) (b x) 1)) = ite (a ∈ s) (b a) 1 :=
prod_dite_eq s a (λ x _, b x)

/--
  When a product is taken over a conditional whose condition is an equality test on the index
  and whose alternative is 1, then the product's value is either the term at that index or `1`.

  The difference with `prod_ite_eq` is that the arguments to `eq` are swapped.
-/
@[simp, to_additive] lemma prod_ite_eq' [decidable_eq α] (s : finset α) (a : α) (b : α → β) :
  (∏ x in s, (ite (x = a) (b x) 1)) = ite (a ∈ s) (b a) 1 :=
prod_dite_eq' s a (λ x _, b x)

/--
  Reorder a product.

  The difference with `prod_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function.
-/
@[to_additive]
lemma prod_bij {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Πa∈s, γ) (hi : ∀a ha, i a ha ∈ t) (h : ∀a ha, f a = g (i a ha))
  (i_inj : ∀a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀b∈t, ∃a ha, b = i a ha) :
  (∏ x in s, f x) = (∏ x in t, g x) :=
congr_arg multiset.prod
  (multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi h i_inj i_surj)

/--
  Reorder a product.

  The difference with `prod_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection.
-/
@[to_additive]
lemma prod_bij' {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Πa∈s, γ) (hi : ∀a ha, i a ha ∈ t) (h : ∀a ha, f a = g (i a ha))
  (j : Πa∈t, α) (hj : ∀a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
  (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) :
  (∏ x in s, f x) = (∏ x in t, g x) :=
begin
  refine prod_bij i hi h _ _,
  {intros a1 a2 h1 h2 eq, rw [←left_inv a1 h1, ←left_inv a2 h2], cc,},
  {intros b hb, use j b hb, use hj b hb, exact (right_inv b hb).symm,},
end

@[to_additive]
lemma prod_bij_ne_one {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Πa∈s, f a ≠ 1 → γ) (hi₁ : ∀a h₁ h₂, i a h₁ h₂ ∈ t)
  (hi₂ : ∀a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
  (hi₃ : ∀b∈t, g b ≠ 1 → ∃a h₁ h₂, b = i a h₁ h₂)
  (h : ∀a h₁ h₂, f a = g (i a h₁ h₂)) :
  (∏ x in s, f x) = (∏ x in t, g x) :=
by classical; exact
calc (∏ x in s, f x) = ∏ x in (s.filter $ λx, f x ≠ 1), f x : prod_filter_ne_one.symm
  ... = ∏ x in (t.filter $ λx, g x ≠ 1), g x :
    prod_bij (assume a ha, i a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
      (assume a ha, (mem_filter.mp ha).elim $ λh₁ h₂, mem_filter.mpr
        ⟨hi₁ a h₁ h₂, λ hg, h₂ (hg ▸ h a h₁ h₂)⟩)
      (assume a ha, (mem_filter.mp ha).elim $ h a)
      (assume a₁ a₂ ha₁ ha₂,
        (mem_filter.mp ha₁).elim $ λha₁₁ ha₁₂, (mem_filter.mp ha₂).elim $ λha₂₁ ha₂₂, hi₂ a₁ a₂ _ _ _ _)
      (assume b hb, (mem_filter.mp hb).elim $ λh₁ h₂,
        let ⟨a, ha₁, ha₂, eq⟩ := hi₃ b h₁ h₂ in ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, eq⟩)
  ... = (∏ x in t, g x) : prod_filter_ne_one

@[to_additive]
lemma nonempty_of_prod_ne_one (h : (∏ x in s, f x) ≠ 1) : s.nonempty :=
s.eq_empty_or_nonempty.elim (λ H, false.elim $ h $ H.symm ▸ prod_empty) id

@[to_additive]
lemma exists_ne_one_of_prod_ne_one (h : (∏ x in s, f x) ≠ 1) : ∃a∈s, f a ≠ 1 :=
begin
  classical,
  rw ← prod_filter_ne_one at h,
  rcases nonempty_of_prod_ne_one h with ⟨x, hx⟩,
  exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
end

lemma sum_range_succ {β} [add_comm_monoid β] (f : ℕ → β) (n : ℕ) :
  (∑ x in range (n + 1), f x) = f n + (∑ x in range n, f x) :=
by rw [range_succ, sum_insert not_mem_range_self]

@[to_additive]
lemma prod_range_succ (f : ℕ → β) (n : ℕ) :
  (∏ x in range (n + 1), f x) = f n * (∏ x in range n, f x) :=
by rw [range_succ, prod_insert not_mem_range_self]

lemma prod_range_succ' (f : ℕ → β) :
  ∀ n : ℕ, (∏ k in range (n + 1), f k) = (∏ k in range n, f (k+1)) * f 0
| 0       := (prod_range_succ _ _).trans $ mul_comm _ _
| (n + 1) := by rw [prod_range_succ (λ m, f (nat.succ m)), mul_assoc, ← prod_range_succ'];
                 exact prod_range_succ _ _

lemma sum_Ico_add {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (m n k : ℕ) :
  (∑ l in Ico m n, f (k + l)) = (∑ l in Ico (m + k) (n + k), f l) :=
Ico.image_add m n k ▸ eq.symm $ sum_image $ λ x hx y hy h, nat.add_left_cancel h

@[to_additive]
lemma prod_Ico_add (f : ℕ → β) (m n k : ℕ) :
  (∏ l in Ico m n, f (k + l)) = (∏ l in Ico (m + k) (n + k), f l) :=
@sum_Ico_add (additive β) _ f m n k

lemma sum_Ico_succ_top {δ : Type*} [add_comm_monoid δ] {a b : ℕ}
  (hab : a ≤ b) (f : ℕ → δ) : (∑ k in Ico a (b + 1), f k) = (∑ k in Ico a b, f k) + f b :=
by rw [Ico.succ_top hab, sum_insert Ico.not_mem_top, add_comm]

@[to_additive]
lemma prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
  (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b :=
@sum_Ico_succ_top (additive β) _ _ _ hab _

lemma sum_eq_sum_Ico_succ_bot {δ : Type*} [add_comm_monoid δ] {a b : ℕ}
  (hab : a < b) (f : ℕ → δ) : (∑ k in Ico a b, f k) = f a + (∑ k in Ico (a + 1) b, f k) :=
have ha : a ∉ Ico (a + 1) b, by simp,
by rw [← sum_insert ha, Ico.insert_succ_bot hab]

@[to_additive]
lemma prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
  (∏ k in Ico a b, f k) = f a * (∏ k in Ico (a + 1) b, f k) :=
@sum_eq_sum_Ico_succ_bot (additive β) _ _ _ hab _

@[to_additive]
lemma prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
  (∏ i in Ico m n, f i) * (∏ i in Ico n k, f i) = (∏ i in Ico m k, f i) :=
Ico.union_consecutive hmn hnk ▸ eq.symm $ prod_union $ Ico.disjoint_consecutive m n k

@[to_additive]
lemma prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
  (∏ k in range m, f k) * (∏ k in Ico m n, f k) = (∏ k in range n, f k) :=
Ico.zero_bot m ▸ Ico.zero_bot n ▸ prod_Ico_consecutive f (nat.zero_le m) h

@[to_additive]
lemma prod_Ico_eq_mul_inv {δ : Type*} [comm_group δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∏ k in Ico m n, f k) = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
eq_mul_inv_iff_mul_eq.2 $ by rw [mul_comm]; exact prod_range_mul_prod_Ico f h

lemma sum_Ico_eq_sub {δ : Type*} [add_comm_group δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∑ k in Ico m n, f k) = (∑ k in range n, f k) - (∑ k in range m, f k) :=
sum_Ico_eq_add_neg f h

@[to_additive]
lemma prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
  (∏ k in Ico m n, f k) = (∏ k in range (n - m), f (m + k)) :=
begin
  by_cases h : m ≤ n,
  { rw [← Ico.zero_bot, prod_Ico_add, zero_add, nat.sub_add_cancel h] },
  { replace h : n ≤ m :=  le_of_not_ge h,
     rw [Ico.eq_empty_of_le h, nat.sub_eq_zero_of_le h, range_zero, prod_empty, prod_empty] }
end

@[to_additive]
lemma prod_range_zero (f : ℕ → β) :
 (∏ k in range 0, f k) = 1 :=
by rw [range_zero, prod_empty]

lemma prod_range_one (f : ℕ → β) :
  (∏ k in range 1, f k) = f 0 :=
by { rw [range_one], apply @prod_singleton ℕ β 0 f }

lemma sum_range_one {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) :
  (∑ k in range 1, f k) = f 0 :=
@prod_range_one (multiplicative δ) _ f

attribute [to_additive finset.sum_range_one] prod_range_one


/-- To prove a property of a product, it suffices to prove that the property is multiplicative and holds on factors.
-/
@[to_additive "To prove a property of a sum, it suffices to prove that the property is additive and holds on summands."]
lemma prod_induction {M : Type*} [comm_monoid M] (f : α → M) (p : M → Prop)
(p_mul : ∀ a b, p a → p b → p (a * b)) (p_one : p 1) (p_s : ∀ x ∈ s, p $ f x) :
p $ ∏ x in s, f x :=
begin
  classical,
  induction s using finset.induction with x hx s hs, simpa,
  rw finset.prod_insert, swap, assumption,
  apply p_mul, apply p_s, simp,
  apply hs, intros a ha, apply p_s, simp [ha],
end

/-- For any product along `{0, ..., n-1}` of a commutative-monoid-valued function, we can verify that
it's equal to a different function just by checking ratios of adjacent terms.
This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
lemma prod_range_induction {M : Type*} [comm_monoid M]
  (f s : ℕ → M) (h0 : s 0 = 1) (h : ∀ n, s (n + 1) = s n * f n) (n : ℕ) :
  ∏ k in finset.range n, f k = s n :=
begin
  induction n with k hk,
  { simp only [h0, finset.prod_range_zero] },
  { simp only [hk, finset.prod_range_succ, h, mul_comm] }
end

/-- For any sum along `{0, ..., n-1}` of a commutative-monoid-valued function, we can verify that it's equal
to a different function just by checking differences of adjacent terms. This is a discrete analogue
of the fundamental theorem of calculus. -/
lemma sum_range_induction {M : Type*} [add_comm_monoid M]
  (f s : ℕ → M) (h0 : s 0 = 0) (h : ∀ n, s (n + 1) = s n + f n) (n : ℕ) :
  ∑ k in finset.range n, f k = s n :=
@prod_range_induction (multiplicative M) _ f s h0 h n

/-- A telescoping sum along `{0, ..., n-1}` of an additive commutative group valued function
reduces to the difference of the last and first terms.-/
lemma sum_range_sub {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  ∑ i in range n, (f (i+1) - f i) = f n - f 0 :=
by { apply sum_range_induction; abel, simp }

lemma sum_range_sub' {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  ∑ i in range n, (f i - f (i+1)) = f 0 - f n :=
by { apply sum_range_induction; abel, simp }

/-- A telescoping product along `{0, ..., n-1}` of a commutative group valued function
reduces to the ratio of the last and first factors.-/
lemma prod_range_div {M : Type*} [comm_group M] (f : ℕ → M) (n : ℕ) :
  ∏ i in range n, (f (i+1) * (f i)⁻¹) = f n * (f 0)⁻¹ :=
by apply @sum_range_sub (additive M)

lemma prod_range_div' {M : Type*} [comm_group M] (f : ℕ → M) (n : ℕ) :
  ∏ i in range n, (f i * (f (i+1))⁻¹) = (f 0) * (f n)⁻¹ :=
by apply @sum_range_sub' (additive M)

/-- A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function reduces to the difference of
the last and first terms when the function we are summing is monotone. -/
lemma sum_range_sub_of_monotone {f : ℕ → ℕ} (h : monotone f) (n : ℕ) :
  ∑ i in range n, (f (i+1) - f i) = f n - f 0 :=
begin
  refine sum_range_induction _ _ (nat.sub_self _) (λ n, _) _,
  have : f n ≤ f (n+1) := h (nat.le_succ _),
  have : f 0 ≤ f n := h (nat.zero_le _),
  omega
end

lemma prod_Ico_reflect (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
  ∏ j in Ico k m, f (n - j) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j :=
begin
  have : ∀ i < m, i ≤ n,
  { intros i hi,
    exact (add_le_add_iff_right 1).1 (le_trans (nat.lt_iff_add_one_le.1 hi) h) },
  cases lt_or_le k m with hkm hkm,
  { rw [← finset.Ico.image_const_sub (this _ hkm)],
    refine (prod_image _).symm,
    simp only [Ico.mem],
    rintros i ⟨ki, im⟩ j ⟨kj, jm⟩ Hij,
    rw [← nat.sub_sub_self (this _ im), Hij, nat.sub_sub_self (this _ jm)] },
  { simp [Ico.eq_empty_of_le, nat.sub_le_sub_left, hkm] }
end

lemma sum_Ico_reflect {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
  (h : m ≤ n + 1) :
  ∑ j in Ico k m, f (n - j) = ∑ j in Ico (n + 1 - m) (n + 1 - k), f j :=
@prod_Ico_reflect (multiplicative δ) _ f k m n h

lemma prod_range_reflect (f : ℕ → β) (n : ℕ) :
  ∏ j in range n, f (n - 1 - j) = ∏ j in range n, f j :=
begin
  cases n,
  { simp },
  { simp only [range_eq_Ico, nat.succ_sub_succ_eq_sub, nat.sub_zero],
    rw [prod_Ico_reflect _ _ (le_refl _)],
    simp }
end

lemma sum_range_reflect {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (n : ℕ) :
  ∑ j in range n, f (n - 1 - j) = ∑ j in range n, f j :=
@prod_range_reflect (multiplicative δ) _ f n

@[simp] lemma prod_const (b : β) : (∏ x in s, b) = b ^ s.card :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
by rw [prod_insert has, card_insert_of_not_mem has, pow_succ, ih])

lemma prod_pow (s : finset α) (n : ℕ) (f : α → β) :
  (∏ x in s, f x ^ n) = (∏ x in s, f x) ^ n :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [_root_.mul_pow] {contextual := tt})

lemma prod_nat_pow (s : finset α) (n : ℕ) (f : α → ℕ) :
  (∏ x in s, f x ^ n) = (∏ x in s, f x) ^ n :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [nat.mul_pow] {contextual := tt})

-- `to_additive` fails on this lemma, so we prove it manually below
lemma prod_flip {n : ℕ} (f : ℕ → β) :
  (∏ r in range (n + 1), f (n - r)) = (∏ k in range (n + 1), f k) :=
begin
  induction n with n ih,
  { rw [prod_range_one, prod_range_one] },
  { rw [prod_range_succ', prod_range_succ _ (nat.succ n), mul_comm],
    simp [← ih] }
end

@[to_additive]
lemma prod_involution {s : finset α} {f : α → β} :
  ∀ (g : Π a ∈ s, α)
  (h₁ : ∀ a ha, f a * f (g a ha) = 1)
  (h₂ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
  (h₃ : ∀ a ha, g a ha ∈ s)
  (h₄ : ∀ a ha, g (g a ha) (h₃ a ha) = a),
  (∏ x in s, f x) = 1 :=
by haveI := classical.dec_eq α;
haveI := classical.dec_eq β; exact
finset.strong_induction_on s
  (λ s ih g h₁ h₂ h₃ h₄,
    s.eq_empty_or_nonempty.elim (λ hs, hs.symm ▸ rfl)
      (λ ⟨x, hx⟩,
      have hmem : ∀ y ∈ (s.erase x).erase (g x hx), y ∈ s,
        from λ y hy, (mem_of_mem_erase (mem_of_mem_erase hy)),
      have g_inj : ∀ {x hx y hy}, g x hx = g y hy → x = y,
        from λ x hx y hy h, by rw [← h₄ x hx, ← h₄ y hy]; simp [h],
      have ih': ∏ y in erase (erase s x) (g x hx), f y = (1 : β) :=
        ih ((s.erase x).erase (g x hx))
          ⟨subset.trans (erase_subset _ _) (erase_subset _ _),
            λ h, not_mem_erase (g x hx) (s.erase x) (h (h₃ x hx))⟩
          (λ y hy, g y (hmem y hy))
          (λ y hy, h₁ y (hmem y hy))
          (λ y hy, h₂ y (hmem y hy))
          (λ y hy, mem_erase.2 ⟨λ (h : g y _ = g x hx), by simpa [g_inj h] using hy,
            mem_erase.2 ⟨λ (h : g y _ = x),
              have y = g x hx, from h₄ y (hmem y hy) ▸ by simp [h],
              by simpa [this] using hy, h₃ y (hmem y hy)⟩⟩)
          (λ y hy, h₄ y (hmem y hy)),
      if hx1 : f x = 1
      then ih' ▸ eq.symm (prod_subset hmem
        (λ y hy hy₁,
          have y = x ∨ y = g x hx, by simp [hy] at hy₁; tauto,
          this.elim (λ h, h.symm ▸ hx1)
            (λ h, h₁ x hx ▸ h ▸ hx1.symm ▸ (one_mul _).symm)))
      else by rw [← insert_erase hx, prod_insert (not_mem_erase _ _),
        ← insert_erase (mem_erase.2 ⟨h₂ x hx hx1, h₃ x hx⟩),
        prod_insert (not_mem_erase _ _), ih', mul_one, h₁ x hx]))

/-- The product of the composition of functions `f` and `g`, is the product
over `b ∈ s.image g` of `f b` to the power of the cardinality of the fibre of `b` -/
lemma prod_comp [decidable_eq γ] {s : finset α} (f : γ → β) (g : α → γ) :
  ∏ a in s, f (g a) = ∏ b in s.image g, f b ^ (s.filter (λ a, g a = b)).card  :=
calc ∏ a in s, f (g a)
    = ∏ x in (s.image g).sigma (λ b : γ, s.filter (λ a, g a = b)), f (g x.2) :
  prod_bij (λ a ha, ⟨g a, a⟩) (by simp; tauto) (λ _ _, rfl) (by simp) (by finish)
... = ∏ b in s.image g, ∏ a in s.filter (λ a, g a = b), f (g a) : prod_sigma
... = ∏ b in s.image g, ∏ a in s.filter (λ a, g a = b), f b :
  prod_congr rfl (λ b hb, prod_congr rfl (by simp {contextual := tt}))
... = ∏ b in s.image g, f b ^ (s.filter (λ a, g a = b)).card :
  prod_congr rfl (λ _ _, prod_const _)

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive]
lemma prod_powerset_insert [decidable_eq α] {s : finset α} {x : α} (h : x ∉ s) (f : finset α → β) :
  (∏ a in (insert x s).powerset, f a) =
    (∏ a in s.powerset, f a) * (∏ t in s.powerset, f (insert x t)) :=
begin
  rw [powerset_insert, finset.prod_union, finset.prod_image],
  { assume t₁ h₁ t₂ h₂ heq,
    rw [← finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₁ h),
        ← finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₂ h), heq] },
  { rw finset.disjoint_iff_ne,
    assume t₁ h₁ t₂ h₂,
    rcases finset.mem_image.1 h₂ with ⟨t₃, h₃, H₃₂⟩,
    rw ← H₃₂,
    exact ne_insert_of_not_mem _ _ (not_mem_of_mem_powerset_of_not_mem h₁ h) }
end

@[to_additive]
lemma prod_piecewise [decidable_eq α] (s t : finset α) (f g : α → β) :
  (∏ x in s, (t.piecewise f g) x) = (∏ x in s ∩ t, f x) * (∏ x in s \ t, g x) :=
by { rw [piecewise, prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter], }

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive]
lemma prod_cancels_of_partition_cancels (R : setoid α) [decidable_rel R.r]
  (h : ∀ x ∈ s, (∏ a in s.filter (λy, y ≈ x), f a) = 1) : (∏ x in s, f x) = 1 :=
begin
  suffices : ∏ xbar in s.image quotient.mk, ∏ y in s.filter (λ y, ⟦y⟧ = xbar), f y = (∏ x in s, f x),
  { rw [←this, ←finset.prod_eq_one],
    intros xbar xbar_in_s,
    rcases (mem_image).mp xbar_in_s with ⟨x, x_in_s, xbar_eq_x⟩,
    rw [←xbar_eq_x, filter_congr (λ y _, @quotient.eq _ R y x)],
    apply h x x_in_s },
  apply finset.prod_image' f,
  intros,
  refl
end

@[to_additive]
lemma prod_update_of_not_mem [decidable_eq α] {s : finset α} {i : α}
  (h : i ∉ s) (f : α → β) (b : β) : (∏ x in s, function.update f i b x) = (∏ x in s, f x) :=
begin
  apply prod_congr rfl (λj hj, _),
  have : j ≠ i, by { assume eq, rw eq at hj, exact h hj },
  simp [this]
end

lemma prod_update_of_mem [decidable_eq α] {s : finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
  (∏ x in s, function.update f i b x) = b * (∏ x in s \ (singleton i), f x) :=
by { rw [update_eq_piecewise, prod_piecewise], simp [h] }

/-- If a product of a `finset` of size at most 1 has a given value, so
do the terms in that product. -/
lemma eq_of_card_le_one_of_prod_eq {s : finset α} (hc : s.card ≤ 1) {f : α → β} {b : β}
    (h : ∏ x in s, f x = b) : ∀ x ∈ s, f x = b :=
begin
  intros x hx,
  by_cases hc0 : s.card = 0,
  { exact false.elim (card_ne_zero_of_mem hx hc0) },
  { have h1 : s.card = 1 := le_antisymm hc (nat.one_le_of_lt (nat.pos_of_ne_zero hc0)),
    rw card_eq_one at h1,
    cases h1 with x2 hx2,
    rw [hx2, mem_singleton] at hx,
    simp_rw hx2 at h,
    rw hx,
    rw prod_singleton at h,
    exact h }
end

/-- If a sum of a `finset` of size at most 1 has a given value, so do
the terms in that sum. -/
lemma eq_of_card_le_one_of_sum_eq [add_comm_monoid γ] {s : finset α} (hc : s.card ≤ 1)
    {f : α → γ} {b : γ} (h : ∑ x in s, f x = b) : ∀ x ∈ s, f x = b :=
begin
  intros x hx,
  by_cases hc0 : s.card = 0,
  { exact false.elim (card_ne_zero_of_mem hx hc0) },
  { have h1 : s.card = 1 := le_antisymm hc (nat.one_le_of_lt (nat.pos_of_ne_zero hc0)),
    rw card_eq_one at h1,
    cases h1 with x2 hx2,
    rw [hx2, mem_singleton] at hx,
    simp_rw hx2 at h,
    rw hx,
    rw sum_singleton at h,
    exact h }
end

attribute [to_additive eq_of_card_le_one_of_sum_eq] eq_of_card_le_one_of_prod_eq

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `finset`. -/
@[to_additive "If a function applied at a point is 0, a sum is unchanged by
removing that point, if present, from a `finset`."]
lemma prod_erase [decidable_eq α] (s : finset α) {f : α → β} {a : α} (h : f a = 1) :
  ∏ x in s.erase a, f x = ∏ x in s, f x :=
begin
  rw ←sdiff_singleton_eq_erase,
  apply prod_subset sdiff_subset_self,
  intros x hx hnx,
  rw sdiff_singleton_eq_erase at hnx,
  rwa eq_of_mem_of_not_mem_erase hx hnx
end

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `finset`. -/
@[to_additive "If a sum is 0 and the function is 0 except possibly at one
point, it is 0 everywhere on the `finset`."]
lemma eq_one_of_prod_eq_one {s : finset α} {f : α → β} {a : α} (hp : ∏ x in s, f x = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 :=
begin
  intros x hx,
  classical,
  by_cases h : x = a,
  { rw h,
    rw h at hx,
    rw [←prod_subset (singleton_subset_iff.2 hx)
                      (λ t ht ha, h1 t ht (not_mem_singleton.1 ha)),
        prod_singleton] at hp,
    exact hp },
  { exact h1 x hx h }
end

end comm_monoid

lemma sum_update_of_mem [add_comm_monoid β] [decidable_eq α] {s : finset α} {i : α}
  (h : i ∈ s) (f : α → β) (b : β) :
  (∑ x in s, function.update f i b x) = b + (∑ x in s \ (singleton i), f x) :=
by { rw [update_eq_piecewise, sum_piecewise], simp [h] }
attribute [to_additive] prod_update_of_mem

lemma sum_nsmul [add_comm_monoid β] (s : finset α) (n : ℕ) (f : α → β) :
  (∑ x in s, n •ℕ (f x)) = n •ℕ ((∑ x in s, f x)) :=
@prod_pow _ (multiplicative β) _ _ _ _
attribute [to_additive sum_nsmul] prod_pow

@[simp] lemma sum_const [add_comm_monoid β] (b : β) :
  (∑ x in s, b) = s.card •ℕ b :=
@prod_const _ (multiplicative β) _ _ _
attribute [to_additive] prod_const

lemma sum_comp [add_comm_monoid β] [decidable_eq γ] {s : finset α} (f : γ → β) (g : α → γ) :
  ∑ a in s, f (g a) = ∑ b in s.image g, (s.filter (λ a, g a = b)).card •ℕ (f b) :=
@prod_comp _ (multiplicative β) _ _ _ _ _ _
attribute [to_additive "The sum of the composition of functions `f` and `g`, is the sum
over `b ∈ s.image g` of `f b` times of the cardinality of the fibre of `b`"] prod_comp

lemma sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀x ∈ s, f x = m) :
  (∑ x in s, f x) = card s * m :=
begin
  rw [← nat.nsmul_eq_mul, ← sum_const],
  apply sum_congr rfl h₁
end

@[simp]
lemma sum_boole {s : finset α} {p : α → Prop} [semiring β] {hp : decidable_pred p} :
  (∑ x in s, if p x then (1 : β) else (0 : β)) = (s.filter p).card :=
by simp [sum_ite]

lemma sum_range_succ' [add_comm_monoid β] (f : ℕ → β) :
  ∀ n : ℕ, (∑ i in range (n + 1), f i) = (∑ i in range n, f (i + 1)) + f 0 :=
@prod_range_succ' (multiplicative β) _ _
attribute [to_additive] prod_range_succ'

lemma sum_flip [add_comm_monoid β] {n : ℕ} (f : ℕ → β) :
  (∑ i in range (n + 1), f (n - i)) = (∑ i in range (n + 1), f i) :=
@prod_flip (multiplicative β) _ _ _
attribute [to_additive] prod_flip

@[norm_cast]
lemma sum_nat_cast [add_comm_monoid β] [has_one β] (s : finset α) (f : α → ℕ) :
  ↑(∑ x in s, f x : ℕ) = (∑ x in s, (f x : β)) :=
(nat.cast_add_monoid_hom β).map_sum f s

@[norm_cast]
lemma prod_nat_cast [comm_semiring β] (s : finset α) (f : α → ℕ) :
  ↑(∏ x in s, f x : ℕ) = (∏ x in s, (f x : β)) :=
(nat.cast_ring_hom β).map_prod f s

protected lemma sum_nat_coe_enat (s : finset α) (f : α → ℕ) :
  (∑ x in s, (f x : enat)) = (∑ x  in s, f x : ℕ) :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp [has, ih] }
end

theorem dvd_sum [comm_semiring α] {a : α} {s : finset β} {f : β → α}
  (h : ∀ x ∈ s, a ∣ f x) : a ∣ ∑ x in s, f x :=
multiset.dvd_sum (λ y hy, by rcases multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx)

lemma le_sum_of_subadditive [add_comm_monoid α] [ordered_add_comm_monoid β]
  (f : α → β) (h_zero : f 0 = 0) (h_add : ∀x y, f (x + y) ≤ f x + f y) (s : finset γ) (g : γ → α) :
  f (∑ x in s, g x) ≤ ∑ x in s, f (g x) :=
begin
  refine le_trans (multiset.le_sum_of_subadditive f h_zero h_add _) _,
  rw [multiset.map_map],
  refl
end

lemma abs_sum_le_sum_abs [discrete_linear_ordered_field α] {f : β → α} {s : finset β} :
  abs (∑ x in s, f x) ≤ ∑ x in s, abs (f x) :=
le_sum_of_subadditive _ abs_zero abs_add s f

section comm_group
variables [comm_group β]

@[simp, to_additive]
lemma prod_inv_distrib : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹ :=
s.prod_hom has_inv.inv

end comm_group

@[simp] theorem card_sigma {σ : α → Type*} (s : finset α) (t : Π a, finset (σ a)) :
  card (s.sigma t) = ∑ a in s, card (t a) :=
multiset.card_sigma _ _

lemma card_bind [decidable_eq β] {s : finset α} {t : α → finset β}
  (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → disjoint (t x) (t y)) :
  (s.bind t).card = ∑ u in s, card (t u) :=
calc (s.bind t).card = ∑ i in s.bind t, 1 : by simp
... = ∑ a in s, ∑ i in t a, 1 : finset.sum_bind h
... = ∑ u in s, card (t u) : by simp

lemma card_bind_le [decidable_eq β] {s : finset α} {t : α → finset β} :
  (s.bind t).card ≤ ∑ a in s, (t a).card :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp)
  (λ a s has ih,
    calc ((insert a s).bind t).card ≤ (t a).card + (s.bind t).card :
    by rw bind_insert; exact finset.card_union_le _ _
    ... ≤ ∑ a in insert a s, card (t a) :
    by rw sum_insert has; exact add_le_add_left ih _)

theorem card_eq_sum_card_image [decidable_eq β] (f : α → β) (s : finset α) :
  s.card = ∑ a in s.image f, (s.filter (λ x, f x = a)).card :=
by letI := classical.dec_eq α; exact
calc s.card = ((s.image f).bind (λ a, s.filter (λ x, f x = a))).card :
  congr_arg _ (finset.ext $ λ x,
    ⟨λ hs, mem_bind.2 ⟨f x, mem_image_of_mem _ hs,
      mem_filter.2 ⟨hs, rfl⟩⟩,
    λ h, let ⟨a, ha₁, ha₂⟩ := mem_bind.1 h in by convert filter_subset s ha₂⟩)
... = ∑ a in s.image f, (s.filter (λ x, f x = a)).card :
  card_bind (by simp [disjoint_left, finset.ext_iff] {contextual := tt})

lemma gsmul_sum [add_comm_group β] {f : α → β} {s : finset α} (z : ℤ) :
  gsmul z (∑ a in s, f a) = ∑ a in s, gsmul z (f a) :=
(s.sum_hom (gsmul z)).symm

end finset

namespace finset
variables {s s₁ s₂ : finset α} {f g : α → β} {b : β} {a : α}

@[simp] lemma sum_sub_distrib [add_comm_group β] :
  ∑ x in s, (f x - g x) = (∑ x in s, f x) - (∑ x in s, g x) :=
sum_add_distrib.trans $ congr_arg _ sum_neg_distrib

section comm_monoid
variables [comm_monoid β]

lemma prod_pow_boole [decidable_eq α] (s : finset α) (f : α → β) (a : α) :
  (∏ x in s, (f x)^(ite (a = x) 1 0)) = ite (a ∈ s) (f a) 1 :=
by simp

end comm_monoid

section semiring
variables [semiring β]

lemma sum_mul : (∑ x in s, f x) * b = ∑ x in s, f x * b :=
(s.sum_hom (λ x, x * b)).symm

lemma mul_sum : b * (∑ x in s, f x) = ∑ x in s, b * f x :=
(s.sum_hom _).symm

lemma sum_mul_boole [decidable_eq α] (s : finset α) (f : α → β) (a : α) :
  (∑ x in s, (f x * ite (a = x) 1 0)) = ite (a ∈ s) (f a) 0 :=
by simp

lemma sum_boole_mul [decidable_eq α] (s : finset α) (f : α → β) (a : α) :
  (∑ x in s, (ite (a = x) 1 0) * f x) = ite (a ∈ s) (f a) 0 :=
by simp

end semiring

lemma sum_div [division_ring β] {s : finset α} {f : α → β} {b : β} :
  (∑ x in s, f x) / b = ∑ x in s, f x / b :=
calc (∑ x in s, f x) / b = ∑ x in s, f x * (1 / b) : by rw [div_eq_mul_one_div, sum_mul]
                     ... = ∑ x in s, f x / b : by { congr, ext, rw ← div_eq_mul_one_div (f x) b }

section comm_semiring
variables [comm_semiring β]

lemma prod_eq_zero (ha : a ∈ s) (h : f a = 0) : (∏ x in s, f x) = 0 :=
by haveI := classical.dec_eq α;
calc (∏ x in s, f x) = ∏ x in insert a (erase s a), f x : by rw insert_erase ha
                 ... = 0 : by rw [prod_insert (not_mem_erase _ _), h, zero_mul]

/-- The product over a sum can be written as a sum over the product of sets, `finset.pi`.
  `finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
lemma prod_sum {δ : α → Type*} [decidable_eq α] [∀a, decidable_eq (δ a)]
  {s : finset α} {t : Πa, finset (δ a)} {f : Πa, δ a → β} :
  (∏ a in s, ∑ b in (t a), f a b) =
    ∑ p in (s.pi t), ∏ x in s.attach, f x.1 (p x.1 x.2) :=
begin
  induction s using finset.induction with a s ha ih,
  { rw [pi_empty, sum_singleton], refl },
  { have h₁ : ∀x ∈ t a, ∀y ∈ t a, ∀h : x ≠ y,
        disjoint (image (pi.cons s a x) (pi s t)) (image (pi.cons s a y) (pi s t)),
    { assume x hx y hy h,
      simp only [disjoint_iff_ne, mem_image],
      rintros _ ⟨p₂, hp, eq₂⟩ _ ⟨p₃, hp₃, eq₃⟩ eq,
      have : pi.cons s a x p₂ a (mem_insert_self _ _) = pi.cons s a y p₃ a (mem_insert_self _ _),
      { rw [eq₂, eq₃, eq] },
      rw [pi.cons_same, pi.cons_same] at this,
      exact h this },
    rw [prod_insert ha, pi_insert ha, ih, sum_mul, sum_bind h₁],
    refine sum_congr rfl (λ b _, _),
    have h₂ : ∀p₁∈pi s t, ∀p₂∈pi s t, pi.cons s a b p₁ = pi.cons s a b p₂ → p₁ = p₂, from
      assume p₁ h₁ p₂ h₂ eq, pi_cons_injective ha eq,
    rw [sum_image h₂, mul_sum],
    refine sum_congr rfl (λ g _, _),
    rw [attach_insert, prod_insert, prod_image],
    { simp only [pi.cons_same],
      congr', ext ⟨v, hv⟩, congr',
      exact (pi.cons_ne (by rintro rfl; exact ha hv)).symm },
    { exact λ _ _ _ _, subtype.eq ∘ subtype.mk.inj },
    { simp only [mem_image], rintro ⟨⟨_, hm⟩, _, rfl⟩, exact ha hm } }
end

lemma sum_mul_sum {ι₁ : Type*} {ι₂ : Type*} (s₁ : finset ι₁) (s₂ : finset ι₂)
  (f₁ : ι₁ → β) (f₂ : ι₂ → β) :
  (∑ x₁ in s₁, f₁ x₁) * (∑ x₂ in s₂, f₂ x₂) = ∑ p in s₁.product s₂, f₁ p.1 * f₂ p.2 :=
by { rw [sum_product, sum_mul, sum_congr rfl], intros, rw mul_sum }

open_locale classical

/-- The product of `f a + g a` over all of `s` is the sum
  over the powerset of `s` of the product of `f` over a subset `t` times
  the product of `g` over the complement of `t`  -/
lemma prod_add (f g : α → β) (s : finset α) :
  ∏ a in s, (f a + g a) = ∑ t in s.powerset, ((∏ a in t, f a) * (∏ a in (s \ t), g a)) :=
calc ∏ a in s, (f a + g a)
    = ∏ a in s, ∑ p in ({true, false} : finset Prop), if p then f a else g a : by simp
... = ∑ p in (s.pi (λ _, {true, false}) : finset (Π a ∈ s, Prop)),
        ∏ a in s.attach, if p a.1 a.2 then f a.1 else g a.1 : prod_sum
... = ∑ t in s.powerset, (∏ a in t, f a) * (∏ a in (s \ t), g a) : begin
  refine eq.symm (sum_bij (λ t _ a _, a ∈ t) _ _ _ _),
  { simp [subset_iff]; tauto },
  { intros t ht,
    erw [prod_ite (λ a : {a // a ∈ s}, f a.1) (λ a : {a // a ∈ s}, g a.1)],
    refine congr_arg2 _
      (prod_bij (λ (a : α) (ha : a ∈ t), ⟨a, mem_powerset.1 ht ha⟩)
         _ _ _
        (λ b hb, ⟨b, by cases b; finish⟩))
      (prod_bij (λ (a : α) (ha : a ∈ s \ t), ⟨a, by simp * at *⟩)
        _ _ _
        (λ b hb, ⟨b, by cases b; finish⟩));
    intros; simp * at *; simp * at * },
  { finish [function.funext_iff, finset.ext_iff, subset_iff] },
  { assume f hf,
    exact ⟨s.filter (λ a : α, ∃ h : a ∈ s, f a h),
      by simp, by funext; intros; simp *⟩ }
end

/--  Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a `finset`
gives `(a + b)^s.card`.-/
lemma sum_pow_mul_eq_add_pow
  {α R : Type*} [comm_semiring R] (a b : R) (s : finset α) :
  (∑ t in s.powerset, a ^ t.card * b ^ (s.card - t.card)) = (a + b) ^ s.card :=
begin
  rw [← prod_const, prod_add],
  refine finset.sum_congr rfl (λ t ht, _),
  rw [prod_const, prod_const, ← card_sdiff (mem_powerset.1 ht)]
end

lemma prod_pow_eq_pow_sum {x : β} {f : α → ℕ} :
  ∀ {s : finset α}, (∏ i in s, x ^ (f i)) = x ^ (∑ x in s, f x) :=
begin
  apply finset.induction,
  { simp },
  { assume a s has H,
    rw [finset.prod_insert has, finset.sum_insert has, pow_add, H] }
end

end comm_semiring

section integral_domain /- add integral_semi_domain to support nat and ennreal -/
variables [integral_domain β]

lemma prod_eq_zero_iff : (∏ x in s, f x) = 0 ↔ (∃a∈s, f a = 0) :=
begin
  classical,
  apply finset.induction_on s,
  exact ⟨not.elim one_ne_zero, λ ⟨_, H, _⟩, H.elim⟩,
  assume a s ha ih,
  rw [prod_insert ha, mul_eq_zero, bex_def, exists_mem_insert, ih, ← bex_def]
end

theorem prod_ne_zero_iff : (∏ x in s, f x) ≠ 0 ↔ (∀ a ∈ s, f a ≠ 0) :=
by { rw [ne, prod_eq_zero_iff], push_neg }

end integral_domain

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

lemma sum_le_sum : (∀x∈s, f x ≤ g x) → (∑ x in s, f x) ≤ (∑ x in s, g x) :=
begin
  classical,
  apply finset.induction_on s,
  exact (λ _, le_refl _),
  assume a s ha ih h,
  have : f a + (∑ x in s, f x) ≤ g a + (∑ x in s, g x),
    from add_le_add (h _ (mem_insert_self _ _)) (ih $ assume x hx, h _ $ mem_insert_of_mem hx),
  by simpa only [sum_insert ha]
end

lemma sum_nonneg (h : ∀x∈s, 0 ≤ f x) : 0 ≤ (∑ x in s, f x) :=
le_trans (by rw [sum_const_zero]) (sum_le_sum h)

lemma sum_nonpos (h : ∀x∈s, f x ≤ 0) : (∑ x in s, f x) ≤ 0 :=
le_trans (sum_le_sum h) (by rw [sum_const_zero])

lemma sum_le_sum_of_subset_of_nonneg
  (h : s₁ ⊆ s₂) (hf : ∀x∈s₂, x ∉ s₁ → 0 ≤ f x) : (∑ x in s₁, f x) ≤ (∑ x in s₂, f x) :=
by classical;
calc (∑ x in s₁, f x) ≤ (∑ x in s₂ \ s₁, f x) + (∑ x in s₁, f x) :
    le_add_of_nonneg_left' $ sum_nonneg $ by simpa only [mem_sdiff, and_imp]
  ... = ∑ x in s₂ \ s₁ ∪ s₁, f x : (sum_union sdiff_disjoint).symm
  ... = (∑ x in s₂, f x)         : by rw [sdiff_union_of_subset h]

lemma sum_mono_set_of_nonneg (hf : ∀ x, 0 ≤ f x) : monotone (λ s, ∑ x in s, f x) :=
λ s₁ s₂ hs, sum_le_sum_of_subset_of_nonneg hs $ λ x _ _, hf x

lemma sum_eq_zero_iff_of_nonneg : (∀x∈s, 0 ≤ f x) → ((∑ x in s, f x) = 0 ↔ ∀x∈s, f x = 0) :=
begin
  classical,
  apply finset.induction_on s,
  exact λ _, ⟨λ _ _, false.elim, λ _, rfl⟩,
  assume a s ha ih H,
  have : ∀ x ∈ s, 0 ≤ f x, from λ _, H _ ∘ mem_insert_of_mem,
  rw [sum_insert ha, add_eq_zero_iff' (H _ $ mem_insert_self _ _) (sum_nonneg this),
    forall_mem_insert, ih this]
end

lemma sum_eq_zero_iff_of_nonpos : (∀x∈s, f x ≤ 0) → ((∑ x in s, f x) = 0 ↔ ∀x∈s, f x = 0) :=
@sum_eq_zero_iff_of_nonneg _ (order_dual β) _ _ _

lemma single_le_sum (hf : ∀x∈s, 0 ≤ f x) {a} (h : a ∈ s) : f a ≤ (∑ x in s, f x) :=
have ∑ x in {a}, f x ≤ (∑ x in s, f x),
  from sum_le_sum_of_subset_of_nonneg
  (λ x e, (mem_singleton.1 e).symm ▸ h) (λ x h _, hf x h),
by rwa sum_singleton at this

end ordered_add_comm_monoid

section canonically_ordered_add_monoid
variables [canonically_ordered_add_monoid β]

@[simp] lemma sum_eq_zero_iff : ∑ x in s, f x = 0 ↔ ∀ x ∈ s, f x = 0 :=
sum_eq_zero_iff_of_nonneg $ λ x hx, zero_le (f x)

lemma sum_le_sum_of_subset (h : s₁ ⊆ s₂) : (∑ x in s₁, f x) ≤ (∑ x in s₂, f x) :=
sum_le_sum_of_subset_of_nonneg h $ assume x h₁ h₂, zero_le _

lemma sum_mono_set (f : α → β) : monotone (λ s, ∑ x in s, f x) :=
λ s₁ s₂ hs, sum_le_sum_of_subset hs

lemma sum_le_sum_of_ne_zero (h : ∀x∈s₁, f x ≠ 0 → x ∈ s₂) :
  (∑ x in s₁, f x) ≤ (∑ x in s₂, f x) :=
by classical;
calc (∑ x in s₁, f x) = ∑ x in s₁.filter (λx, f x = 0), f x + ∑ x in s₁.filter (λx, f x ≠ 0), f x :
    by rw [←sum_union, filter_union_filter_neg_eq];
       exact disjoint_filter.2 (assume _ _ h n_h, n_h h)
  ... ≤ (∑ x in s₂, f x) : add_le_of_nonpos_of_le'
      (sum_nonpos $ by simp only [mem_filter, and_imp]; exact λ _ _, le_of_eq)
      (sum_le_sum_of_subset $ by simpa only [subset_iff, mem_filter, and_imp])

end canonically_ordered_add_monoid

section ordered_cancel_comm_monoid

variables [ordered_cancel_add_comm_monoid β]

theorem sum_lt_sum (Hle : ∀ i ∈ s, f i ≤ g i) (Hlt : ∃ i ∈ s, f i < g i) :
  (∑ x in s, f x) < (∑ x in s, g x) :=
begin
  classical,
  rcases Hlt with ⟨i, hi, hlt⟩,
  rw [← insert_erase hi, sum_insert (not_mem_erase _ _), sum_insert (not_mem_erase _ _)],
  exact add_lt_add_of_lt_of_le hlt (sum_le_sum $ λ j hj, Hle j  $ mem_of_mem_erase hj)
end

lemma sum_lt_sum_of_nonempty (hs : s.nonempty) (Hlt : ∀ x ∈ s, f x < g x) :
  (∑ x in s, f x) < (∑ x in s, g x) :=
begin
  apply sum_lt_sum,
  { intros i hi, apply le_of_lt (Hlt i hi) },
  cases hs with i hi,
  exact ⟨i, hi, Hlt i hi⟩,
end

lemma sum_lt_sum_of_subset [decidable_eq α]
  (h : s₁ ⊆ s₂) {i : α} (hi : i ∈ s₂ \ s₁) (hpos : 0 < f i) (hnonneg : ∀ j ∈ s₂ \ s₁, 0 ≤ f j) :
  (∑ x in s₁, f x) < (∑ x in s₂, f x) :=
calc (∑ x in s₁, f x) < (∑ x in insert i s₁, f x) :
begin
  simp only [mem_sdiff] at hi,
  rw sum_insert hi.2,
  exact lt_add_of_pos_left (∑ x in s₁, f x) hpos,
end
... ≤ (∑ x in s₂, f x) :
begin
  simp only [mem_sdiff] at hi,
  apply sum_le_sum_of_subset_of_nonneg,
  { simp [finset.insert_subset, h, hi.1] },
  { assume x hx h'x,
    apply hnonneg x,
    simp [mem_insert, not_or_distrib] at h'x,
    rw mem_sdiff,
    simp [hx, h'x] }
end

end ordered_cancel_comm_monoid

section decidable_linear_ordered_cancel_comm_monoid

variables [decidable_linear_ordered_cancel_add_comm_monoid β]

theorem exists_le_of_sum_le (hs : s.nonempty) (Hle : (∑ x in s, f x) ≤ ∑ x in s, g x) :
  ∃ i ∈ s, f i ≤ g i :=
begin
  classical,
  contrapose! Hle with Hlt,
  rcases hs with ⟨i, hi⟩,
  exact sum_lt_sum (λ i hi, le_of_lt (Hlt i hi)) ⟨i, hi, Hlt i hi⟩
end

lemma exists_pos_of_sum_zero_of_exists_nonzero (f : α → β)
  (h₁ : ∑ e in s, f e = 0) (h₂ : ∃ x ∈ s, f x ≠ 0) :
  ∃ x ∈ s, 0 < f x :=
begin
  contrapose! h₁,
  obtain ⟨x, m, x_nz⟩ : ∃ x ∈ s, f x ≠ 0 := h₂,
  apply ne_of_lt,
  calc ∑ e in s, f e < ∑ e in s, 0 : by { apply sum_lt_sum h₁ ⟨x, m, lt_of_le_of_ne (h₁ x m) x_nz⟩ }
                 ... = 0           : by rw [finset.sum_const, nsmul_zero],
end

end decidable_linear_ordered_cancel_comm_monoid

section linear_ordered_comm_ring
variables [linear_ordered_comm_ring β]
open_locale classical

/- this is also true for a ordered commutative multiplicative monoid -/
lemma prod_nonneg {s : finset α} {f : α → β}
  (h0 : ∀(x ∈ s), 0 ≤ f x) : 0 ≤ (∏ x in s, f x) :=
prod_induction f (λ x, 0 ≤ x) (λ _ _ ha hb, mul_nonneg ha hb) zero_le_one h0


/- this is also true for a ordered commutative multiplicative monoid -/
lemma prod_pos {s : finset α} {f : α → β} (h0 : ∀(x ∈ s), 0 < f x) : 0 < (∏ x in s, f x) :=
prod_induction f (λ x, 0 < x) (λ _ _ ha hb, mul_pos ha hb) zero_lt_one h0


/- this is also true for a ordered commutative multiplicative monoid -/
lemma prod_le_prod {s : finset α} {f g : α → β} (h0 : ∀(x ∈ s), 0 ≤ f x)
  (h1 : ∀(x ∈ s), f x ≤ g x) : (∏ x in s, f x) ≤ (∏ x in s, g x) :=
begin
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp [has], apply mul_le_mul,
      exact h1 a (mem_insert_self a s),
      apply ih (λ x H, h0 _ _) (λ x H, h1 _ _); exact (mem_insert_of_mem H),
      apply prod_nonneg (λ x H, h0 x (mem_insert_of_mem H)),
      apply le_trans (h0 a (mem_insert_self a s)) (h1 a (mem_insert_self a s)) }
end

end linear_ordered_comm_ring

section canonically_ordered_comm_semiring

variables [canonically_ordered_comm_semiring β]

lemma prod_le_prod' {s : finset α} {f g : α → β} (h : ∀ i ∈ s, f i ≤ g i) :
  (∏ x in s, f x) ≤ (∏ x in s, g x) :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp },
  { rw [finset.prod_insert has, finset.prod_insert has],
    apply canonically_ordered_semiring.mul_le_mul,
    { exact h _ (finset.mem_insert_self a s) },
    { exact ih (λ i hi, h _ (finset.mem_insert_of_mem hi)) } }
end

end canonically_ordered_comm_semiring

@[simp] lemma card_pi [decidable_eq α] {δ : α → Type*}
  (s : finset α) (t : Π a, finset (δ a)) :
  (s.pi t).card = ∏ a in s, card (t a) :=
multiset.card_pi _ _

theorem card_le_mul_card_image [decidable_eq β] {f : α → β} (s : finset α)
  (n : ℕ) (hn : ∀ a ∈ s.image f, (s.filter (λ x, f x = a)).card ≤ n) :
  s.card ≤ n * (s.image f).card :=
calc s.card = (∑ a in s.image f, (s.filter (λ x, f x = a)).card) :
  card_eq_sum_card_image _ _
... ≤ (∑ _ in s.image f, n) : sum_le_sum hn
... = _ : by simp [mul_comm]

@[simp] lemma prod_Ico_id_eq_fact : ∀ n : ℕ, ∏ x in Ico 1 (n + 1), x = nat.fact n
| 0 := rfl
| (n+1) := by rw [prod_Ico_succ_top $ nat.succ_le_succ $ zero_le n,
  nat.fact_succ, prod_Ico_id_eq_fact n, nat.succ_eq_add_one, mul_comm]

end finset

namespace finset
section gauss_sum

/-- Gauss' summation formula -/
lemma sum_range_id_mul_two (n : ℕ) :
  (∑ i in range n, i) * 2 = n * (n - 1) :=
calc (∑ i in range n, i) * 2 = (∑ i in range n, i) + (∑ i in range n, (n - 1 - i)) :
  by rw [sum_range_reflect (λ i, i) n, mul_two]
... = ∑ i in range n, (i + (n - 1 - i)) : sum_add_distrib.symm
... = ∑ i in range n, (n - 1) : sum_congr rfl $ λ i hi, nat.add_sub_cancel' $
  nat.le_pred_of_lt $ mem_range.1 hi
... = n * (n - 1) : by rw [sum_const, card_range, nat.nsmul_eq_mul]

/-- Gauss' summation formula -/
lemma sum_range_id (n : ℕ) : (∑ i in range n, i) = (n * (n - 1)) / 2 :=
by rw [← sum_range_id_mul_two n, nat.mul_div_cancel]; exact dec_trivial

end gauss_sum

lemma card_eq_sum_ones (s : finset α) : s.card = ∑ _ in s, 1 :=
by simp

end finset

section group

open list
variables [group α] [group β]

theorem is_group_anti_hom.map_prod (f : α → β) [is_group_anti_hom f] (l : list α) :
  f (prod l) = prod (map f (reverse l)) :=
by induction l with hd tl ih; [exact is_group_anti_hom.map_one f,
  simp only [prod_cons, is_group_anti_hom.map_mul f, ih, reverse_cons, map_append, prod_append,
    map_singleton, prod_cons, prod_nil, mul_one]]

theorem inv_prod : ∀ l : list α, (prod l)⁻¹ = prod (map (λ x, x⁻¹) (reverse l)) :=
-- TODO there is probably a cleaner proof of this
λ l, @is_group_anti_hom.map_prod _ _ _ _ _ inv_is_group_anti_hom l

end group

@[to_additive is_add_group_hom_finset_sum]
lemma is_group_hom_finset_prod {α β γ} [group α] [comm_group β] (s : finset γ)
  (f : γ → α → β) [∀c, is_group_hom (f c)] : is_group_hom (λa, ∏ c in s, f c a) :=
{ map_mul := assume a b, by simp only [λc, is_mul_hom.map_mul (f c), finset.prod_mul_distrib] }

attribute [instance] is_group_hom_finset_prod is_add_group_hom_finset_sum

namespace multiset
variables [decidable_eq α]

@[simp] lemma to_finset_sum_count_eq (s : multiset α) :
  (∑ a in s.to_finset, s.count a) = s.card :=
multiset.induction_on s rfl
  (assume a s ih,
    calc (∑ x in to_finset (a :: s), count x (a :: s)) =
      ∑ x in to_finset (a :: s), ((if x = a then 1 else 0) + count x s) :
        finset.sum_congr rfl $ λ _ _, by split_ifs;
        [simp only [h, count_cons_self, nat.one_add], simp only [count_cons_of_ne h, zero_add]]
      ... = card (a :: s) :
      begin
        by_cases a ∈ s.to_finset,
        { have : ∑ x in s.to_finset, ite (x = a) 1 0 = ∑ x in {a}, ite (x = a) 1 0,
          { rw [finset.sum_ite_eq', if_pos h, finset.sum_singleton, if_pos rfl], },
          rw [to_finset_cons, finset.insert_eq_of_mem h, finset.sum_add_distrib, ih, this,
            finset.sum_singleton, if_pos rfl, add_comm, card_cons] },
        { have ha : a ∉ s, by rwa mem_to_finset at h,
          have : ∑ x in to_finset s, ite (x = a) 1 0 = ∑ x in to_finset s, 0, from
            finset.sum_congr rfl (λ x hx, if_neg $ by rintro rfl; cc),
          rw [to_finset_cons, finset.sum_insert h, if_pos rfl, finset.sum_add_distrib, this,
            finset.sum_const_zero, ih, count_eq_zero_of_not_mem ha, zero_add, add_comm, card_cons] }
      end)

end multiset

namespace with_top
open finset
open_locale classical

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top [ordered_add_comm_monoid β] {s : finset α} {f : α → with_top β} :
  (∀a∈s, f a < ⊤) → (∑ x in s, f x) < ⊤ :=
λ h, sum_induction f (λ a, a < ⊤) (by { simp_rw add_lt_top, tauto }) zero_lt_top h


/-- A sum of finite numbers is still finite -/
lemma sum_lt_top_iff [canonically_ordered_add_monoid β] {s : finset α} {f : α → with_top β} :
  (∑ x in s, f x) < ⊤ ↔ (∀a∈s, f a < ⊤) :=
iff.intro (λh a ha, lt_of_le_of_lt (single_le_sum (λa ha, zero_le _) ha) h) sum_lt_top

/-- A sum of numbers is infinite iff one of them is infinite -/
lemma sum_eq_top_iff [canonically_ordered_add_monoid β] {s : finset α} {f : α → with_top β} :
  (∑ x in s, f x) = ⊤ ↔ (∃a∈s, f a = ⊤) :=
begin
  rw ← not_iff_not,
  push_neg,
  simp only [← lt_top_iff_ne_top],
  exact sum_lt_top_iff
end

end with_top
