import data.finsupp.basic

/-!
# Additive monoid structure on `α →₀ M`

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/

noncomputable theory
open_locale classical big_operators

open finset

variables {α β γ ι M M' N P G H R S : Type*}

namespace finsupp

/-!
### Additive monoid structure on `α →₀ M`
-/

section add_zero_class
variables [add_zero_class M]

instance : has_add (α →₀ M) := ⟨zip_with (+) (add_zero 0)⟩

instance : add_zero_class (α →₀ M) :=
{ zero      := 0,
  add       := (+),
  zero_add  := assume ⟨s, f, hf⟩, ext $ assume a, zero_add _,
  add_zero  := assume ⟨s, f, hf⟩, ext $ assume a, add_zero _ }

@[simp] lemma coe_add (f g : α →₀ M) : ⇑(f + g) = f + g := rfl
lemma add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ + g₂) a = g₁ a + g₂ a := rfl

lemma support_add [decidable_eq α] {g₁ g₂ : α →₀ M} : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
support_zip_with

lemma support_add_eq [decidable_eq α] {g₁ g₂ : α →₀ M} (h : disjoint g₁.support g₂.support) :
  (g₁ + g₂).support = g₁.support ∪ g₂.support :=
le_antisymm support_zip_with $ assume a ha,
(finset.mem_union.1 ha).elim
  (assume ha, have a ∉ g₂.support, from disjoint_left.1 h ha,
    by simp only [mem_support_iff, not_not] at *;
    simpa only [add_apply, this, add_zero])
  (assume ha, have a ∉ g₁.support, from disjoint_right.1 h ha,
    by simp only [mem_support_iff, not_not] at *;
    simpa only [add_apply, this, zero_add])

@[simp] lemma single_add {a : α} {b₁ b₂ : M} : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
ext $ assume a',
begin
  by_cases h : a = a',
  { rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same] },
  { rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_add] }
end

@[simp] lemma some_add (f g : option α →₀ M) : (f + g).some = f.some + g.some := by { ext, refl }

lemma filter_pos_add_filter_neg (f : α →₀ M) (p : α → Prop) :
  f.filter p + f.filter (λ a, ¬ p a) = f :=
coe_fn_injective $ set.indicator_self_add_compl {x | p x} f

/-- `finsupp.single` as an `add_monoid_hom`.

See `finsupp.lsingle` for the stronger version as a linear map.
-/
@[simps] def single_add_hom (a : α) : M →+ α →₀ M :=
⟨single a, single_zero, λ _ _, single_add⟩

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `finsupp.lapply` for the stronger version as a linear map. -/
@[simps apply]
def apply_add_hom (a : α) : (α →₀ M) →+ M := ⟨λ g, g a, zero_apply, λ _ _, add_apply _ _ _⟩

lemma update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) :
  f.update a b = single a b + f.erase a :=
begin
  ext j,
  rcases eq_or_ne a j with rfl|h,
  { simp },
  { simp [function.update_noteq h.symm, single_apply, h, erase_ne, h.symm] }
end

lemma update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) :
  f.update a b = f.erase a + single a b :=
begin
  ext j,
  rcases eq_or_ne a j with rfl|h,
  { simp },
  { simp [function.update_noteq h.symm, single_apply, h, erase_ne, h.symm] }
end

lemma single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.erase a = f :=
by rw [←update_eq_single_add_erase, update_self]

lemma erase_add_single (a : α) (f : α →₀ M) : f.erase a + single a (f a) = f :=
by rw [←update_eq_erase_add_single, update_self]

@[simp] lemma erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' :=
begin
  ext s, by_cases hs : s = a,
  { rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero] },
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply],
end

/-- `finsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def erase_add_hom (a : α) : (α →₀ M) →+ (α →₀ M) :=
{ to_fun := erase a, map_zero' := erase_zero a, map_add' := erase_add a }

@[elab_as_eliminator]
protected theorem induction {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (ha : ∀a b (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
  p f :=
suffices ∀s (f : α →₀ M), f.support = s → p f, from this _ _ rfl,
assume s, finset.induction_on s (λ f hf, by rwa [support_eq_empty.1 hf]) $
assume a s has ih f hf,
suffices p (single a (f a) + f.erase a), by rwa [single_add_erase] at this,
begin
  apply ha,
  { rw [support_erase, mem_erase], exact λ H, H.1 rfl },
  { rw [← mem_support_iff, hf], exact mem_insert_self _ _ },
  { apply ih _ _,
    rw [support_erase, hf, finset.erase_insert has] }
end

lemma induction₂ {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (ha : ∀a b (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (f + single a b)) :
  p f :=
suffices ∀s (f : α →₀ M), f.support = s → p f, from this _ _ rfl,
assume s, finset.induction_on s (λ f hf, by rwa [support_eq_empty.1 hf]) $
assume a s has ih f hf,
suffices p (f.erase a + single a (f a)), by rwa [erase_add_single] at this,
begin
  apply ha,
  { rw [support_erase, mem_erase], exact λ H, H.1 rfl },
  { rw [← mem_support_iff, hf], exact mem_insert_self _ _ },
  { apply ih _ _,
    rw [support_erase, hf, finset.erase_insert has] }
end

lemma induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M)
  (h0 : p 0) (hadd : ∀ f g : α →₀ M, p f → p g → p (f + g)) (hsingle : ∀ a b, p (single a b)) :
  p f :=
induction₂ f h0 (λ a b f _ _ w, hadd _ _ w (hsingle _ _))

@[simp] lemma add_closure_set_of_eq_single :
  add_submonoid.closure {f : α →₀ M | ∃ a b, f = single a b} = ⊤ :=
top_unique $ λ x hx, finsupp.induction x (add_submonoid.zero_mem _) $
  λ a b f ha hb hf, add_submonoid.add_mem _
    (add_submonoid.subset_closure $ ⟨a, b, rfl⟩) hf

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal. -/
lemma add_hom_ext [add_zero_class N] ⦃f g : (α →₀ M) →+ N⦄
  (H : ∀ x y, f (single x y) = g (single x y)) :
  f = g :=
begin
  refine add_monoid_hom.eq_of_eq_on_mdense add_closure_set_of_eq_single _,
  rintro _ ⟨x, y, rfl⟩,
  apply H
end

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal.

We formulate this using equality of `add_monoid_hom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext] lemma add_hom_ext' [add_zero_class N] ⦃f g : (α →₀ M) →+ N⦄
  (H : ∀ x, f.comp (single_add_hom x) = g.comp (single_add_hom x)) :
  f = g :=
add_hom_ext $ λ x, add_monoid_hom.congr_fun (H x)

lemma mul_hom_ext [mul_one_class N] ⦃f g : multiplicative (α →₀ M) →* N⦄
  (H : ∀ x y, f (multiplicative.of_add $ single x y) = g (multiplicative.of_add $ single x y)) :
  f = g :=
monoid_hom.ext $ add_monoid_hom.congr_fun $
  @add_hom_ext α M (additive N) _ _ f.to_additive'' g.to_additive'' H

@[ext] lemma mul_hom_ext' [mul_one_class N] {f g : multiplicative (α →₀ M) →* N}
  (H : ∀ x, f.comp (single_add_hom x).to_multiplicative =
    g.comp (single_add_hom x).to_multiplicative) :
  f = g :=
mul_hom_ext $ λ x, monoid_hom.congr_fun (H x)

lemma map_range_add [add_zero_class N]
  {f : M → N} {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : α →₀ M) :
  map_range f hf (v₁ + v₂) = map_range f hf v₁ + map_range f hf v₂ :=
ext $ λ a, by simp only [hf', add_apply, map_range_apply]

/-- Bundle `emb_domain f` as an additive map from `α →₀ M` to `β →₀ M`. -/
@[simps] def emb_domain.add_monoid_hom (f : α ↪ β) : (α →₀ M) →+ (β →₀ M) :=
{ to_fun := λ v, emb_domain f v,
  map_zero' := by simp,
  map_add' := λ v w,
  begin
    ext b,
    by_cases h : b ∈ set.range f,
    { rcases h with ⟨a, rfl⟩,
      simp, },
    { simp [emb_domain_notin_range, h], },
  end, }

@[simp] lemma emb_domain_add (f : α ↪ β) (v w : α →₀ M) :
  emb_domain f (v + w) = emb_domain f v + emb_domain f w :=
(emb_domain.add_monoid_hom f).map_add v w
variables [add_zero_class M] {p : α → Prop} {v v' : α →₀ M}

@[simp] lemma subtype_domain_add {v v' : α →₀ M} :
  (v + v').subtype_domain p = v.subtype_domain p + v'.subtype_domain p :=
ext $ λ _, rfl

/-- `subtype_domain` but as an `add_monoid_hom`. -/
def subtype_domain_add_monoid_hom : (α →₀ M) →+ subtype p →₀ M :=
{ to_fun := subtype_domain p,
  map_zero' := subtype_domain_zero,
  map_add' := λ _ _, subtype_domain_add }

/-- `finsupp.filter` as an `add_monoid_hom`. -/
def filter_add_hom (p : α → Prop) : (α →₀ M) →+ (α →₀ M) :=
{ to_fun := filter p,
  map_zero' := filter_zero p,
  map_add' := λ f g, coe_fn_injective $ set.indicator_add {x | p x} f g }

@[simp] lemma filter_add {v v' : α →₀ M} : (v + v').filter p = v.filter p + v'.filter p :=
(filter_add_hom p).map_add v v'

end add_zero_class

section add_monoid

variables [add_monoid M]

instance : add_monoid (α →₀ M) :=
{ add_monoid .
  zero      := 0,
  add       := (+),
  add_assoc := assume ⟨s, f, hf⟩ ⟨t, g, hg⟩ ⟨u, h, hh⟩, ext $ assume a, add_assoc _ _ _,
  nsmul := λ n v, v.map_range ((•) n) (nsmul_zero _),
  nsmul_zero' := λ v, by { ext i, simp },
  nsmul_succ' := λ n v, by { ext i, simp [nat.succ_eq_one_add, add_nsmul] },
  .. finsupp.add_zero_class }

end add_monoid

end finsupp

@[to_additive]
lemma mul_equiv.map_finsupp_prod [has_zero M] [comm_monoid N] [comm_monoid P]
  (h : N ≃* P) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
h.map_prod _ _

@[to_additive]
lemma monoid_hom.map_finsupp_prod [has_zero M] [comm_monoid N] [comm_monoid P]
  (h : N →* P) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
h.map_prod _ _

lemma ring_hom.map_finsupp_sum [has_zero M] [semiring R] [semiring S]
  (h : R →+* S) (f : α →₀ M) (g : α → M → R) : h (f.sum g) = f.sum (λ a b, h (g a b)) :=
h.map_sum _ _

lemma ring_hom.map_finsupp_prod [has_zero M] [comm_semiring R] [comm_semiring S]
  (h : R →+* S) (f : α →₀ M) (g : α → M → R) : h (f.prod g) = f.prod (λ a b, h (g a b)) :=
h.map_prod _ _

@[to_additive]
lemma monoid_hom.coe_finsupp_prod [has_zero β] [monoid N] [comm_monoid P]
  (f : α →₀ β) (g : α → β → N →* P) :
  ⇑(f.prod g) = f.prod (λ i fi, g i fi) :=
monoid_hom.coe_prod _ _

@[simp, to_additive]
lemma monoid_hom.finsupp_prod_apply [has_zero β] [monoid N] [comm_monoid P]
  (f : α →₀ β) (g : α → β → N →* P) (x : N) :
  f.prod g x = f.prod (λ i fi, g i fi x) :=
monoid_hom.finset_prod_apply _ _ _

namespace finsupp
section add_comm_monoid
variables [add_comm_monoid M] {p : α → Prop}

instance : add_comm_monoid (α →₀ M) :=
{ add_comm := assume ⟨s, f, _⟩ ⟨t, g, _⟩, ext $ assume a, add_comm _ _,
  .. finsupp.add_monoid }

lemma subtype_domain_sum {s : finset ι} {h : ι → α →₀ M} :
  (∑ c in s, h c).subtype_domain p = ∑ c in s, (h c).subtype_domain p :=
(subtype_domain_add_monoid_hom : _ →+ subtype p →₀ M).map_sum _ s

lemma subtype_domain_finsupp_sum [has_zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
  (s.sum h).subtype_domain p = s.sum (λc d, (h c d).subtype_domain p) :=
subtype_domain_sum

lemma filter_sum (s : finset ι) (f : ι → α →₀ M) :
  (∑ a in s, f a).filter p = ∑ a in s, filter p (f a) :=
(filter_add_hom p : (α →₀ M) →+ _).map_sum f s

lemma filter_eq_sum (p : α → Prop) [D : decidable_pred p] (f : α →₀ M) :
  f.filter p = ∑ i in f.support.filter p, single i (f i) :=
(f.filter p).sum_single.symm.trans $ finset.sum_congr (by rw subsingleton.elim D; refl) $
  λ x hx, by rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end add_comm_monoid

section group
variables [add_group G] {p : α → Prop} {v v' : α →₀ G}
instance [add_group G] : has_sub (α →₀ G) := ⟨zip_with has_sub.sub (sub_zero _)⟩

instance [add_group G] : add_group (α →₀ G) :=
{ neg            := map_range (has_neg.neg) neg_zero,
  sub            := has_sub.sub,
  sub_eq_add_neg := λ x y, ext (λ i, sub_eq_add_neg _ _),
  add_left_neg   := assume ⟨s, f, _⟩, ext $ assume x, add_left_neg _,
  zsmul := λ n v, v.map_range ((•) n) (zsmul_zero _),
  zsmul_zero' := λ v, by { ext i, simp },
  zsmul_succ' := λ n v, by { ext i, simp [nat.succ_eq_one_add, add_zsmul] },
  zsmul_neg' := λ n v, by { ext i, simp only [nat.succ_eq_add_one, map_range_apply,
    zsmul_neg_succ_of_nat, int.coe_nat_succ, neg_inj,
    add_zsmul, add_nsmul, one_zsmul, coe_nat_zsmul, one_nsmul] },
  .. finsupp.add_monoid }

@[simp] lemma subtype_domain_neg : (- v).subtype_domain p = - v.subtype_domain p :=
ext $ λ _, rfl

@[simp] lemma subtype_domain_sub :
  (v - v').subtype_domain p = v.subtype_domain p - v'.subtype_domain p :=
ext $ λ _, rfl

@[simp] lemma single_neg {a : α} {b : G} : single a (-b) = -single a b :=
(single_add_hom a : G →+ _).map_neg b

@[simp] lemma single_sub {a : α} {b₁ b₂ : G} : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
(single_add_hom a : G →+ _).map_sub b₁ b₂

@[simp] lemma erase_neg (a : α) (f : α →₀ G) : erase a (-f) = -erase a f :=
(erase_add_hom a : (_ →₀ G) →+ _).map_neg f

@[simp] lemma erase_sub (a : α) (f₁ f₂ : α →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
(erase_add_hom a : (_ →₀ G) →+ _).map_sub f₁ f₂

@[simp] lemma filter_neg (p : α → Prop) (f : α →₀ G) : filter p (-f) = -filter p f :=
(filter_add_hom p : (_ →₀ G) →+ _).map_neg f

@[simp] lemma filter_sub (p : α → Prop) (f₁ f₂ : α →₀ G) :
  filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
(filter_add_hom p : (_ →₀ G) →+ _).map_sub f₁ f₂

end group

instance [add_comm_group G] : add_comm_group (α →₀ G) :=
{ add_comm := add_comm, ..finsupp.add_group }

lemma single_multiset_sum [add_comm_monoid M] (s : multiset M) (a : α) :
  single a s.sum = (s.map (single a)).sum :=
multiset.induction_on s single_zero $ λ a s ih,
by rw [multiset.sum_cons, single_add, ih, multiset.map_cons, multiset.sum_cons]

lemma single_finset_sum [add_comm_monoid M] (s : finset ι) (f : ι → M) (a : α) :
  single a (∑ b in s, f b) = ∑ b in s, single a (f b) :=
begin
  transitivity,
  apply single_multiset_sum,
  rw [multiset.map_map],
  refl
end

lemma single_sum [has_zero M] [add_comm_monoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
  single a (s.sum f) = s.sum (λd c, single a (f d c)) :=
single_finset_sum _ _ _

@[to_additive]
lemma prod_neg_index [add_group G] [comm_monoid M] {g : α →₀ G} {h : α → G → M}
  (h0 : ∀a, h a 0 = 1) :
  (-g).prod h = g.prod (λa b, h a (- b)) :=
prod_map_range_index h0

@[simp] lemma coe_neg [add_group G] (g : α →₀ G) : ⇑(-g) = -g := rfl
lemma neg_apply [add_group G] (g : α →₀ G) (a : α) : (- g) a = - g a := rfl

@[simp] lemma coe_sub [add_group G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl
lemma sub_apply [add_group G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a := rfl

@[simp] lemma support_neg [add_group G] (f : α →₀ G) : support (-f) = support f :=
finset.subset.antisymm
  support_map_range
  (calc support f = support (- (- f)) : congr_arg support (neg_neg _).symm
     ... ⊆ support (- f) : support_map_range)

lemma support_sub [decidable_eq α] [add_group G] {f g : α →₀ G} :
  support (f - g) ⊆ support f ∪ support g :=
begin
  rw [sub_eq_add_neg, ←support_neg g],
  exact support_add,
end

lemma erase_eq_sub_single [add_group G] (f : α →₀ G) (a : α) :
  f.erase a = f - single a (f a) :=
begin
  ext a',
  rcases eq_or_ne a a' with rfl|h,
  { simp },
  { simp [erase_ne h.symm, single_eq_of_ne h] }
end

lemma update_eq_sub_add_single [add_group G] (f : α →₀ G) (a : α) (b : G) :
  f.update a b = f - single a (f a) + single a b :=
by rw [update_eq_erase_add_single, erase_eq_sub_single]

@[simp] lemma sum_apply [has_zero M] [add_comm_monoid N]
  {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
  (f.sum g) a₂ = f.sum (λa₁ b, g a₁ b a₂) :=
(apply_add_hom a₂ : (β →₀ N) →+ _).map_sum _ _

lemma support_sum [decidable_eq β] [has_zero M] [add_comm_monoid N]
  {f : α →₀ M} {g : α → M → (β →₀ N)} :
  (f.sum g).support ⊆ f.support.bUnion (λa, (g a (f a)).support) :=
have ∀ c, f.sum (λ a b, g a b c) ≠ 0 → (∃ a, f a ≠ 0 ∧ ¬ (g a (f a)) c = 0),
  from assume a₁ h,
  let ⟨a, ha, ne⟩ := finset.exists_ne_zero_of_sum_ne_zero h in
  ⟨a, mem_support_iff.mp ha, ne⟩,
by simpa only [finset.subset_iff, mem_support_iff, finset.mem_bUnion, sum_apply, exists_prop]

lemma support_finset_sum [decidable_eq β] [add_comm_monoid M] {s : finset α} {f : α → (β →₀ M)} :
  (finset.sum s f).support ⊆ s.bUnion (λ x, (f x).support) :=
begin
  rw ←finset.sup_eq_bUnion,
  induction s using finset.cons_induction_on with a s ha ih,
  { refl },
  { rw [finset.sum_cons, finset.sup_cons],
    exact support_add.trans (finset.union_subset_union (finset.subset.refl _) ih), },
end

@[simp] lemma sum_zero [has_zero M] [add_comm_monoid N] {f : α →₀ M} :
  f.sum (λa b, (0 : N)) = 0 :=
finset.sum_const_zero

@[simp, to_additive]
lemma prod_mul  [has_zero M] [comm_monoid N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
  f.prod (λa b, h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂ :=
finset.prod_mul_distrib

@[simp, to_additive]
lemma prod_inv [has_zero M] [comm_group G] {f : α →₀ M}
  {h : α → M → G} : f.prod (λa b, (h a b)⁻¹) = (f.prod h)⁻¹ :=
(((monoid_hom.id G)⁻¹).map_prod _ _).symm

@[simp] lemma sum_sub [has_zero M] [add_comm_group G] {f : α →₀ M}
  {h₁ h₂ : α → M → G} :
  f.sum (λa b, h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
finset.sum_sub_distrib

@[to_additive]
lemma prod_add_index [add_comm_monoid M] [comm_monoid N] {f g : α →₀ M}
  {h : α → M → N} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  (f + g).prod h = f.prod h * g.prod h :=
have hf : f.prod h = ∏ a in f.support ∪ g.support, h a (f a),
  from f.prod_of_support_subset (subset_union_left _ _) _ $ λ a ha, h_zero a,
have hg : g.prod h = ∏ a in f.support ∪ g.support, h a (g a),
  from g.prod_of_support_subset (subset_union_right _ _) _ $ λ a ha, h_zero a,
have hfg : (f + g).prod h = ∏ a in f.support ∪ g.support, h a ((f + g) a),
  from (f + g).prod_of_support_subset support_add _ $ λ a ha, h_zero a,
by simp only [*, add_apply, prod_mul_distrib]

@[simp]
lemma sum_add_index' [add_comm_monoid M] [add_comm_monoid N] {f g : α →₀ M} (h : α → M →+ N) :
  (f + g).sum (λ x, h x) = f.sum (λ x, h x) + g.sum (λ x, h x) :=
sum_add_index (λ a, (h a).map_zero) (λ a, (h a).map_add)

@[simp]
lemma prod_add_index' [add_comm_monoid M] [comm_monoid N] {f g : α →₀ M}
  (h : α → multiplicative M →* N) :
  (f + g).prod (λ a b, h a (multiplicative.of_add b)) =
    f.prod (λ a b, h a (multiplicative.of_add b)) * g.prod (λ a b, h a (multiplicative.of_add b)) :=
prod_add_index (λ a, (h a).map_one) (λ a, (h a).map_mul)

@[to_additive]
lemma prod_option_index [add_comm_monoid M] [comm_monoid N]
  (f : option α →₀ M) (b : option α → M → N) (h_zero : ∀ o, b o 0 = 1)
  (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
  f.prod b = b none (f none) * f.some.prod (λ a, b (option.some a)) :=
begin
  apply induction_linear f,
  { simp [h_zero], },
  { intros f₁ f₂ h₁ h₂,
    rw [finsupp.prod_add_index, h₁, h₂, some_add, finsupp.prod_add_index],
    simp only [h_add, pi.add_apply, finsupp.coe_add],
    rw mul_mul_mul_comm,
    all_goals { simp [h_zero, h_add], }, },
  { rintros (_|a) m; simp [h_zero, h_add], }
end

lemma sum_option_index_smul [semiring R] [add_comm_monoid M] [module R M]
  (f : option α →₀ R) (b : option α → M) :
  f.sum (λ o r, r • b o) =
    f none • b none + f.some.sum (λ a r, r • b (option.some a)) :=
f.sum_option_index _ (λ _, zero_smul _ _) (λ _ _ _, add_smul _ _ _)

/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
def lift_add_hom [add_comm_monoid M] [add_comm_monoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) :=
{ to_fun := λ F,
  { to_fun := λ f, f.sum (λ x, F x),
    map_zero' := finset.sum_empty,
    map_add' := λ _ _, sum_add_index (λ x, (F x).map_zero) (λ x, (F x).map_add) },
  inv_fun := λ F x, F.comp $ single_add_hom x,
  left_inv := λ F, by { ext, simp },
  right_inv := λ F, by { ext, simp },
  map_add' := λ F G, by { ext, simp } }

@[simp] lemma lift_add_hom_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : α → M →+ N) (f : α →₀ M) :
  lift_add_hom F f = f.sum (λ x, F x) :=
rfl

@[simp] lemma lift_add_hom_symm_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : (α →₀ M) →+ N) (x : α) :
  lift_add_hom.symm F x = F.comp (single_add_hom x) :=
rfl

lemma lift_add_hom_symm_apply_apply [add_comm_monoid M] [add_comm_monoid N]
  (F : (α →₀ M) →+ N) (x : α) (y : M) :
  lift_add_hom.symm F x y = F (single x y) :=
rfl

@[simp] lemma lift_add_hom_single_add_hom [add_comm_monoid M] :
  lift_add_hom (single_add_hom : α → M →+ α →₀ M) = add_monoid_hom.id _ :=
lift_add_hom.to_equiv.apply_eq_iff_eq_symm_apply.2 rfl

@[simp] lemma sum_single [add_comm_monoid M] (f : α →₀ M) :
  f.sum single = f :=
add_monoid_hom.congr_fun lift_add_hom_single_add_hom f

@[simp] lemma lift_add_hom_apply_single [add_comm_monoid M] [add_comm_monoid N]
  (f : α → M →+ N) (a : α) (b : M) :
  lift_add_hom f (single a b) = f a b :=
sum_single_index (f a).map_zero

@[simp] lemma lift_add_hom_comp_single [add_comm_monoid M] [add_comm_monoid N] (f : α → M →+ N)
  (a : α) :
  (lift_add_hom f).comp (single_add_hom a) = f a :=
add_monoid_hom.ext $ λ b, lift_add_hom_apply_single f a b

lemma comp_lift_add_hom [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
  (g : N →+ P) (f : α → M →+ N) :
  g.comp (lift_add_hom f) = lift_add_hom (λ a, g.comp (f a)) :=
lift_add_hom.symm_apply_eq.1 $ funext $ λ a,
  by rw [lift_add_hom_symm_apply, add_monoid_hom.comp_assoc, lift_add_hom_comp_single]

lemma sum_sub_index [add_comm_group β] [add_comm_group γ] {f g : α →₀ β}
  {h : α → β → γ} (h_sub : ∀a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) :
  (f - g).sum h = f.sum h - g.sum h :=
(lift_add_hom (λ a, add_monoid_hom.of_map_sub (h a) (h_sub a))).map_sub f g

@[to_additive]
lemma prod_emb_domain [has_zero M] [comm_monoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
  (v.emb_domain f).prod g = v.prod (λ a b, g (f a) b) :=
begin
  rw [prod, prod, support_emb_domain, finset.prod_map],
  simp_rw emb_domain_apply,
end

@[to_additive]
lemma prod_finset_sum_index [add_comm_monoid M] [comm_monoid N]
  {s : finset ι} {g : ι → α →₀ M}
  {h : α → M → N} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  ∏ i in s, (g i).prod h = (∑ i in s, g i).prod h :=
finset.induction_on s rfl $ λ a s has ih,
by rw [prod_insert has, ih, sum_insert has, prod_add_index h_zero h_add]

@[to_additive]
lemma prod_sum_index
  [add_comm_monoid M] [add_comm_monoid N] [comm_monoid P]
  {f : α →₀ M} {g : α → M → β →₀ N}
  {h : β → N → P} (h_zero : ∀a, h a 0 = 1) (h_add : ∀a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
  (f.sum g).prod h = f.prod (λa b, (g a b).prod h) :=
(prod_finset_sum_index h_zero h_add).symm

lemma multiset_sum_sum_index
  [add_comm_monoid M] [add_comm_monoid N]
  (f : multiset (α →₀ M)) (h : α → M → N)
  (h₀ : ∀a, h a 0 = 0) (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
  (f.sum.sum h) = (f.map $ λg:α →₀ M, g.sum h).sum :=
multiset.induction_on f rfl $ assume a s ih,
by rw [multiset.sum_cons, multiset.map_cons, multiset.sum_cons, sum_add_index h₀ h₁, ih]

lemma support_sum_eq_bUnion {α : Type*} {ι : Type*} {M : Type*} [add_comm_monoid M]
  {g : ι → α →₀ M} (s : finset ι) (h : ∀ i₁ i₂, i₁ ≠ i₂ → disjoint (g i₁).support (g i₂).support) :
  (∑ i in s, g i).support = s.bUnion (λ i, (g i).support) :=
begin
  apply finset.induction_on s,
  { simp },
  { intros i s hi,
    simp only [hi, sum_insert, not_false_iff, bUnion_insert],
    intro hs,
    rw [finsupp.support_add_eq, hs],
    rw [hs],
    intros x hx,
    simp only [mem_bUnion, exists_prop, inf_eq_inter, ne.def, mem_inter] at hx,
    obtain ⟨hxi, j, hj, hxj⟩ := hx,
    have hn : i ≠ j := λ H, hi (H.symm ▸ hj),
    apply h _ _ hn,
    simp [hxi, hxj] }
end

lemma multiset_map_sum [has_zero M] {f : α →₀ M} {m : β → γ} {h : α → M → multiset β} :
  multiset.map m (f.sum h) = f.sum (λa b, (h a b).map m) :=
(multiset.map_add_monoid_hom m).map_sum _ f.support

lemma multiset_sum_sum [has_zero M] [add_comm_monoid N] {f : α →₀ M} {h : α → M → multiset N} :
  multiset.sum (f.sum h) = f.sum (λa b, multiset.sum (h a b)) :=
(multiset.sum_add_monoid_hom : multiset N →+ N).map_sum _ f.support


/-- For disjoint `f1` and `f2`, and function `g`, the product of the products of `g`
over `f1` and `f2` equals the product of `g` over `f1 + f2` -/
lemma prod_add_index_of_disjoint [add_comm_monoid M] {f1 f2 : α →₀ M}
  (hd : disjoint f1.support f2.support) {β : Type*} [comm_monoid β] (g : α → M → β) :
  (f1 + f2).prod g = f1.prod g * f2.prod g :=
have ∀ {f1 f2 : α →₀ M}, disjoint f1.support f2.support →
  ∏ x in f1.support, g x (f1 x + f2 x) = f1.prod g :=
  λ f1 f2 hd, finset.prod_congr rfl (λ x hx,
    by simp only [not_mem_support_iff.mp (disjoint_left.mp hd hx), add_zero]),
by simp_rw [← this hd, ← this hd.symm,
  add_comm (f2 _), finsupp.prod, support_add_eq hd, prod_union hd, add_apply]

section map_range

section equiv
variables [has_zero M] [has_zero N] [has_zero P]

/-- `finsupp.map_range` as an equiv. -/
@[simps apply]
def map_range.equiv (f : M ≃ N) (hf : f 0 = 0) (hf' : f.symm 0 = 0) : (α →₀ M) ≃ (α →₀ N) :=
{ to_fun := (map_range f hf : (α →₀ M) → (α →₀ N)),
  inv_fun := (map_range f.symm hf' : (α →₀ N) → (α →₀ M)),
  left_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw equiv.symm_comp_self,
    { exact map_range_id _ },
    { refl },
  end,
  right_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw equiv.self_comp_symm,
    { exact map_range_id _ },
    { refl },
  end }

@[simp]
lemma map_range.equiv_refl :
  map_range.equiv (equiv.refl M) rfl rfl = equiv.refl (α →₀ M) :=
equiv.ext map_range_id

lemma map_range.equiv_trans
  (f : M ≃ N) (hf : f 0 = 0) (hf') (f₂ : N ≃ P) (hf₂ : f₂ 0 = 0) (hf₂') :
  (map_range.equiv (f.trans f₂) (by rw [equiv.trans_apply, hf, hf₂])
    (by rw [equiv.symm_trans_apply, hf₂', hf']) : (α →₀ _) ≃ _) =
    (map_range.equiv f hf hf').trans (map_range.equiv f₂ hf₂ hf₂') :=
equiv.ext $ map_range_comp _ _ _ _ _

@[simp] lemma map_range.equiv_symm (f : M ≃ N) (hf hf') :
  ((map_range.equiv f hf hf').symm : (α →₀ _) ≃ _) = map_range.equiv f.symm hf' hf :=
equiv.ext $ λ x, rfl

end equiv

section zero_hom
variables [has_zero M] [has_zero N] [has_zero P]

/-- Composition with a fixed zero-preserving homomorphism is itself an zero-preserving homomorphism
on functions. -/
@[simps]
def map_range.zero_hom (f : zero_hom M N) : zero_hom (α →₀ M) (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  map_zero' := map_range_zero }

@[simp]
lemma map_range.zero_hom_id :
  map_range.zero_hom (zero_hom.id M) = zero_hom.id (α →₀ M) := zero_hom.ext map_range_id

lemma map_range.zero_hom_comp (f : zero_hom N P) (f₂ : zero_hom M N) :
  (map_range.zero_hom (f.comp f₂) : zero_hom (α →₀ _) _) =
    (map_range.zero_hom f).comp (map_range.zero_hom f₂) :=
zero_hom.ext $ map_range_comp _ _ _ _ _

end zero_hom

section add_monoid_hom
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]

/--
Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
def map_range.add_monoid_hom (f : M →+ N) : (α →₀ M) →+ (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  map_zero' := map_range_zero,
  map_add' := λ a b, map_range_add f.map_add _ _ }

@[simp]
lemma map_range.add_monoid_hom_id :
  map_range.add_monoid_hom (add_monoid_hom.id M) = add_monoid_hom.id (α →₀ M) :=
add_monoid_hom.ext map_range_id

lemma map_range.add_monoid_hom_comp (f : N →+ P) (f₂ : M →+ N) :
  (map_range.add_monoid_hom (f.comp f₂) : (α →₀ _) →+ _) =
    (map_range.add_monoid_hom f).comp (map_range.add_monoid_hom f₂) :=
add_monoid_hom.ext $ map_range_comp _ _ _ _ _

@[simp]
lemma map_range.add_monoid_hom_to_zero_hom (f : M →+ N) :
  (map_range.add_monoid_hom f).to_zero_hom =
    (map_range.zero_hom f.to_zero_hom : zero_hom (α →₀ _) _) :=
zero_hom.ext $ λ _, rfl

lemma map_range_multiset_sum (f : M →+ N) (m : multiset (α →₀ M)) :
  map_range f f.map_zero m.sum = (m.map $ λx, map_range f f.map_zero x).sum :=
(map_range.add_monoid_hom f : (α →₀ _) →+ _).map_multiset_sum _

lemma map_range_finset_sum (f : M →+ N) (s : finset ι) (g : ι → (α →₀ M))  :
  map_range f f.map_zero (∑ x in s, g x) = ∑ x in s, map_range f f.map_zero (g x) :=
(map_range.add_monoid_hom f : (α →₀ _) →+ _).map_sum _ _


/-- `finsupp.map_range.add_monoid_hom` as an equiv. -/
@[simps apply]
def map_range.add_equiv (f : M ≃+ N) : (α →₀ M) ≃+ (α →₀ N) :=
{ to_fun := (map_range f f.map_zero : (α →₀ M) → (α →₀ N)),
  inv_fun := (map_range f.symm f.symm.map_zero : (α →₀ N) → (α →₀ M)),
  left_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw add_equiv.symm_comp_self,
    { exact map_range_id _ },
    { refl },
  end,
  right_inv := λ x, begin
    rw ←map_range_comp _ _ _ _; simp_rw add_equiv.self_comp_symm,
    { exact map_range_id _ },
    { refl },
  end,
  ..(map_range.add_monoid_hom f.to_add_monoid_hom) }

@[simp]
lemma map_range.add_equiv_refl :
  map_range.add_equiv (add_equiv.refl M) = add_equiv.refl (α →₀ M) :=
add_equiv.ext map_range_id

lemma map_range.add_equiv_trans (f : M ≃+ N) (f₂ : N ≃+ P) :
  (map_range.add_equiv (f.trans f₂) : (α →₀ _) ≃+ _) =
    (map_range.add_equiv f).trans (map_range.add_equiv f₂) :=
add_equiv.ext $ map_range_comp _ _ _ _ _

@[simp] lemma map_range.add_equiv_symm (f : M ≃+ N) :
  ((map_range.add_equiv f).symm : (α →₀ _) ≃+ _) = map_range.add_equiv f.symm :=
add_equiv.ext $ λ x, rfl

@[simp]
lemma map_range.add_equiv_to_add_monoid_hom (f : M ≃+ N) :
  (map_range.add_equiv f : (α →₀ _) ≃+ _).to_add_monoid_hom =
    (map_range.add_monoid_hom f.to_add_monoid_hom : (α →₀ _) →+ _) :=
add_monoid_hom.ext $ λ _, rfl

@[simp]
lemma map_range.add_equiv_to_equiv (f : M ≃+ N) :
  (map_range.add_equiv f).to_equiv =
    (map_range.equiv f.to_equiv f.map_zero f.symm.map_zero : (α →₀ _) ≃ _) :=
equiv.ext $ λ _, rfl

end add_monoid_hom
end map_range
end finsupp
