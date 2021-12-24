import algebra.big_operators.finsupp

/-! ### Declarations about `map_domain` -/

namespace finsupp
section map_domain
variables [add_comm_monoid M] {v v₁ v₂ : α →₀ M}

/-- Given `f : α → β` and `v : α →₀ M`, `map_domain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def map_domain (f : α → β) (v : α →₀ M) : β →₀ M :=
v.sum $ λa, single (f a)

lemma map_domain_apply {f : α → β} (hf : function.injective f) (x : α →₀ M) (a : α) :
  map_domain f x (f a) = x a :=
begin
  rw [map_domain, sum_apply, sum, finset.sum_eq_single a, single_eq_same],
  { assume b _ hba, exact single_eq_of_ne (hf.ne hba) },
  { assume h, rw [not_mem_support_iff.1 h, single_zero, zero_apply] }
end

lemma map_domain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ set.range f) :
  map_domain f x a = 0 :=
begin
  rw [map_domain, sum_apply, sum],
  exact finset.sum_eq_zero
    (assume a' h', single_eq_of_ne $ assume eq, h $ eq ▸ set.mem_range_self _)
end

@[simp]
lemma map_domain_id : map_domain id v = v :=
sum_single _

lemma map_domain_comp {f : α → β} {g : β → γ} :
  map_domain (g ∘ f) v = map_domain g (map_domain f v) :=
begin
  refine ((sum_sum_index _ _).trans _).symm,
  { intros, exact single_zero },
  { intros, exact single_add },
  refine sum_congr (λ _ _, sum_single_index _),
  { exact single_zero }
end

@[simp]
lemma map_domain_single {f : α → β} {a : α} {b : M} : map_domain f (single a b) = single (f a) b :=
sum_single_index single_zero

@[simp] lemma map_domain_zero {f : α → β} : map_domain f (0 : α →₀ M) = (0 : β →₀ M) :=
sum_zero_index

lemma map_domain_congr {f g : α → β} (h : ∀x∈v.support, f x = g x) :
  v.map_domain f = v.map_domain g :=
finset.sum_congr rfl $ λ _ H, by simp only [h _ H]

lemma map_domain_add {f : α → β} : map_domain f (v₁ + v₂) = map_domain f v₁ + map_domain f v₂ :=
sum_add_index (λ _, single_zero) (λ _ _ _, single_add)

@[simp] lemma map_domain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) :
  map_domain f x a = x (f.symm a) :=
begin
  conv_lhs { rw ←f.apply_symm_apply a },
  exact map_domain_apply f.injective _ _,
end

/-- `finsupp.map_domain` is an `add_monoid_hom`. -/
@[simps]
def map_domain.add_monoid_hom (f : α → β) : (α →₀ M) →+ (β →₀ M) :=
{ to_fun := map_domain f,
  map_zero' := map_domain_zero,
  map_add' := λ _ _, map_domain_add}

@[simp]
lemma map_domain.add_monoid_hom_id : map_domain.add_monoid_hom id = add_monoid_hom.id (α →₀ M) :=
add_monoid_hom.ext $ λ _, map_domain_id

lemma map_domain.add_monoid_hom_comp (f : β → γ) (g : α → β) :
  (map_domain.add_monoid_hom (f ∘ g) : (α →₀ M) →+ (γ →₀ M)) =
    (map_domain.add_monoid_hom f).comp (map_domain.add_monoid_hom g) :=
add_monoid_hom.ext $ λ _, map_domain_comp

lemma map_domain_finset_sum {f : α → β} {s : finset ι} {v : ι → α →₀ M} :
  map_domain f (∑ i in s, v i) = ∑ i in s, map_domain f (v i) :=
(map_domain.add_monoid_hom f : (α →₀ M) →+ β →₀ M).map_sum _ _

lemma map_domain_sum [has_zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
  map_domain f (s.sum v) = s.sum (λa b, map_domain f (v a b)) :=
(map_domain.add_monoid_hom f : (α →₀ M) →+ β →₀ M).map_finsupp_sum _ _

lemma map_domain_support [decidable_eq β] {f : α → β} {s : α →₀ M} :
  (s.map_domain f).support ⊆ s.support.image f :=
finset.subset.trans support_sum $
  finset.subset.trans (finset.bUnion_mono $ assume a ha, support_single_subset) $
  by rw [finset.bUnion_singleton]; exact subset.refl _

@[to_additive]
lemma prod_map_domain_index [comm_monoid N] {f : α → β} {s : α →₀ M}
  {h : β → M → N} (h_zero : ∀b, h b 0 = 1) (h_add : ∀b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
  (map_domain f s).prod h = s.prod (λa m, h (f a) m) :=
(prod_sum_index h_zero h_add).trans $ prod_congr $ λ _ _, prod_single_index (h_zero _)

/--
A version of `sum_map_domain_index` that takes a bundled `add_monoid_hom`,
rather than separate linearity hypotheses.
-/
-- Note that in `prod_map_domain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `monoid_hom`.
@[simp]
lemma sum_map_domain_index_add_monoid_hom [add_comm_monoid N] {f : α → β}
  {s : α →₀ M} (h : β → M →+ N) :
  (map_domain f s).sum (λ b m, h b m) = s.sum (λ a m, h (f a) m) :=
@sum_map_domain_index _ _ _ _ _ _ _ _
  (λ b m, h b m)
  (λ b, (h b).map_zero)
  (λ b m₁ m₂, (h b).map_add _ _)

lemma emb_domain_eq_map_domain (f : α ↪ β) (v : α →₀ M) :
  emb_domain f v = map_domain f v :=
begin
  ext a,
  by_cases a ∈ set.range f,
  { rcases h with ⟨a, rfl⟩,
    rw [map_domain_apply f.injective, emb_domain_apply] },
  { rw [map_domain_notin_range, emb_domain_notin_range]; assumption }
end

@[to_additive]
lemma prod_map_domain_index_inj [comm_monoid N] {f : α → β} {s : α →₀ M}
  {h : β → M → N} (hf : function.injective f) :
  (s.map_domain f).prod h = s.prod (λa b, h (f a) b) :=
by rw [←function.embedding.coe_fn_mk f hf, ←emb_domain_eq_map_domain, prod_emb_domain]

lemma map_domain_injective {f : α → β} (hf : function.injective f) :
  function.injective (map_domain f : (α →₀ M) → (β →₀ M)) :=
begin
  assume v₁ v₂ eq, ext a,
  have : map_domain f v₁ (f a) = map_domain f v₂ (f a), { rw eq },
  rwa [map_domain_apply hf, map_domain_apply hf] at this,
end

lemma map_domain.add_monoid_hom_comp_map_range [add_comm_monoid N] (f : α → β) (g : M →+ N) :
  (map_domain.add_monoid_hom f).comp (map_range.add_monoid_hom g) =
    (map_range.add_monoid_hom g).comp (map_domain.add_monoid_hom f) :=
by { ext, simp }

/-- When `g` preserves addition, `map_range` and `map_domain` commute. -/
lemma map_domain_map_range [add_comm_monoid N] (f : α → β) (v : α →₀ M) (g : M → N)
  (h0 : g 0 = 0) (hadd : ∀ x y, g (x + y) = g x + g y) :
  map_domain f (map_range g h0 v) = map_range g h0 (map_domain f v) :=
let g' : M →+ N := { to_fun := g, map_zero' := h0, map_add' := hadd} in
add_monoid_hom.congr_fun (map_domain.add_monoid_hom_comp_map_range f g') v

lemma map_domain_comap_domain [add_comm_monoid M] (f : α → β) (l : β →₀ M)
  (hf : function.injective f) (hl : ↑l.support ⊆ set.range f):
  map_domain f (comap_domain f l (hf.inj_on _)) = l :=
begin
  ext a,
  by_cases h_cases: a ∈ set.range f,
  { rcases set.mem_range.1 h_cases with ⟨b, hb⟩,
    rw [hb.symm, map_domain_apply hf, comap_domain_apply] },
  { rw map_domain_notin_range _ _ h_cases,
    by_contra h_contr,
    apply h_cases (hl $ finset.mem_coe.2 $ mem_support_iff.2 $ λ h, h_contr h.symm) }
end

lemma equiv_map_domain_eq_map_domain {M} [add_comm_monoid M] (f : α ≃ β) (l : α →₀ M) :
  equiv_map_domain f l = map_domain f l := by ext x; simp [map_domain_equiv_apply]

end map_domain
end finsupp
