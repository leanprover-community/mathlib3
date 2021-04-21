
import algebra.big_operators.finprod
import algebra.big_operators.order
import group_theory.group_action.defs

open function set

open_locale classical big_operators

variables {α β M M₀ A R G ι N : Type*}
[comm_monoid M] [monoid M₀] [add_comm_monoid A] [semiring R] [comm_group G] [ordered_comm_monoid N]

section main

variables {f g : α → M} {s t : set α} {x y : α}


/-- A set `s` has finite intersection with `mul_support f` if the product of `f` over `s`
   is not equal to one. -/
@[to_additive] lemma finite_mul_support_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) :
  (s ∩ mul_support f).finite :=
by_contra (λ hn, h (finprod_mem_eq_one_of_infinite hn))

/-- `mul_support f` is finite if the product of `f` over `s` is not equal to one. -/
@[to_additive] lemma finite_mul_support_of_finprod_ne_one (h : ∏ᶠ i, f i ≠ 1) :
  (mul_support f).finite :=
by {rw ← finprod_mem_univ at h, convert finite_mul_support_of_finprod_mem_ne_one h, simp}

/-- Given a function `g` that is involutive on `s` for which `(f a) * (f g a) = 1` and `f` is
one on every fixed point of `g`, the product of `f` on `s` is one. -/
@[to_additive] lemma finprod_mem_of_involution (f : α → M) (g : α → α)
(h_cancel : ∀ a ∈ s, (f a) * f (g a) = 1)
(h_mem : ∀ a ∈ s, g a ∈ s)
(h_inv : ∀ a ∈ s, g (g a) = a)
(h_ne : ∀ a ∈ s, g a = a → f a = 1):
  ∏ᶠ a ∈ s, f a = 1 :=
begin
  by_cases hs : (s ∩ mul_support f).finite, swap, rw finprod_mem_eq_one_of_infinite hs,
  rw [finprod_mem_eq_prod _ hs],
  refine finset.prod_involution (λ a _, g a) _ _ _ _,
  any_goals {simp_rw [finite.mem_to_finset, mem_inter_iff, mem_mul_support]},
  any_goals {tauto},
    exact λ a h hne hg, hne (h_ne a h.1 hg),
  refine λ a h, ⟨h_mem a h.1, (λ hg, _)⟩,
  specialize h_cancel a h.1,
  rw [hg, mul_one] at h_cancel,
  exact h.2 h_cancel,
end

end main

section distributivity

variables {f g : α → A} {s t : set α} {x y : α}

/-- A more general version of `finsum_mem_smul_distrib`, that requires `s ∩ support f` to be finite
instead of `s`. -/
lemma finsum_mem_smul_distrib' [distrib_mul_action M₀ A] (c : M₀)
  (hf : (s ∩ support f).finite) : c • (∑ᶠ i ∈ s, f i) = ∑ᶠ i ∈ s, (c • (f i)) :=
add_monoid_hom.map_finsum_mem' (const_smul_hom A c) hf

/-- scalar multiplication distributes over `finsum_mem` in a finite set `s` -/
lemma finsum_mem_smul_distrib [distrib_mul_action M₀ A] (c : M₀) (hs : s.finite) :
  c • (∑ᶠ i ∈ s, f i) = ∑ᶠ i ∈ s, (c • (f i)) :=
add_monoid_hom.map_finsum_mem _ (const_smul_hom A c) hs

def nsmul.monoid_hom (n : ℕ) : A →+ A :=
{ to_fun := nsmul n, map_zero' := nsmul_zero _, map_add' := λ _ _, nsmul_add _ _ _}


/-- Scalar multiplication distributes over `finsum_mem`, with the finiteness assumption replaced by
the assumption that the scalar multiplication has no zero divisors. Requires `semiring` and
`semimodule` instances. -/
lemma finsum_mem_smul_distrib'' [semimodule R A] [no_zero_smul_divisors R A] {f : α → A} (c : R) :
  c • (∑ᶠ i ∈ s, f i) = ∑ᶠ i ∈ s, (c • (f i)) :=
begin
  by_cases hs : (s ∩ support f).finite,
    apply finsum_mem_smul_distrib' c hs,
  rcases em (c = 0) with (rfl | hc),
    simp,
  rw [finsum_mem_eq_zero_of_infinite hs, finsum_mem_eq_zero_of_infinite],
    rw smul_zero,
  convert hs using 2,
  ext,
  simpa [mem_support, not_iff_not] using hc,
end

end distributivity

section group

variables {f g : α → G} {s t : set α} {x y : α}

@[to_additive] lemma finprod_mem_inv_distrib' (hs : (s ∩ mul_support f).finite):
  ∏ᶠ i ∈ s, (f i)⁻¹ = (∏ᶠ i ∈ s, f i)⁻¹ :=
(monoid_hom.map_finprod_mem' (monoid_hom.id G)⁻¹ hs).symm

@[to_additive] lemma finprod_mem_inv_distrib (hs : s.finite):
  ∏ᶠ i ∈ s, (f i)⁻¹ = (∏ᶠ i ∈ s, f i)⁻¹ :=
(monoid_hom.map_finprod_mem f (monoid_hom.id G)⁻¹ hs).symm

@[to_additive] lemma finprod_mem_div_distrib' (hf : (s ∩ (mul_support f)).finite)
  (hg : (s ∩ (mul_support g)).finite):
  ∏ᶠ i ∈ s, (f i)/(g i) = (∏ᶠ i ∈ s, f i) / (∏ᶠ i ∈ s, g i) :=
begin
  simp_rw [div_eq_mul_inv],
  rw [finprod_mem_mul_distrib' hf (by rwa mul_support_inv g), finprod_mem_inv_distrib' hg],
end

@[to_additive] lemma finprod_mem_div_distrib (hs : s.finite) :
  ∏ᶠ i ∈ s, (f i)/(g i) = (∏ᶠ i ∈ s, f i) / (∏ᶠ i ∈ s, g i) :=
finprod_mem_div_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

end group


section order

variables {f g : α → N} {s t : set α} {x y : α}

@[to_additive] lemma one_le_of_finprod_mem_one_le (hf : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ᶠ i ∈ s, f i :=
finprod_mem_induction _ (le_refl _) (λ _ _, one_le_mul) hf

@[to_additive] lemma one_le_of_finprod_one_le (hf : ∀ i, 1 ≤ f i) : 1 ≤ ∏ᶠ i, f i :=
by {rw ← finprod_mem_univ, exact one_le_of_finprod_mem_one_le (λ i _, hf i)}

@[to_additive finsum_mem_le_finsum_mem']
lemma finprod_mem_le_finprod_mem''' (hfg : ∀ x ∈ s, f x ≤ g x) (hf : (s ∩ mul_support f).finite)
  (hg : (s ∩ mul_support g).finite) : ∏ᶠ i ∈ s, f i ≤ ∏ᶠ i ∈ s, g i :=
begin
  convert @finset.prod_le_prod'' _ _ _  f g  ((hf.union hg).to_finset.filter s) (λ i, _),
  any_goals
  { refine finprod_mem_eq_prod_of_inter_mul_support_eq _ (ext_iff.mpr (λ _, _))},
  all_goals
  { simp only [finite.mem_to_finset, mem_sep_eq, finite.coe_to_finset, mem_inter_eq, ne.def,
    mem_union_eq, mem_mul_support, and.congr_left_iff, finset.coe_filter, finset.mem_filter],
    tauto },
end

@[to_additive finsum_mem_le_finsum_mem]
lemma finprod_mem_le_finprod_mem'' (hfg : ∀ x ∈ s, f x ≤ g x) (hs : s.finite) :
  ∏ᶠ i ∈ s, f i ≤ ∏ᶠ i ∈ s, g i :=
by {apply finprod_mem_le_finprod_mem''' hfg; apply hs.inter_of_left}

@[to_additive]
lemma finprod_mem_le_finprod_mem_of_one_lt (hfg : ∀ x ∈ s, f x ≤ g x) (h : 1 < ∏ᶠ i ∈ s, g i):
  ∏ᶠ i ∈ s, f i ≤ ∏ᶠ i ∈ s, g i :=
begin
  have hg : (s ∩ mul_support g).finite, from
    by_contra (λ hn, lt_irrefl _ (by {rwa finprod_mem_eq_one_of_infinite hn at h})),
  by_cases hf : (s ∩ mul_support f).finite,
    exact finprod_mem_le_finprod_mem''' hfg hf hg,
  exact (lt_of_le_of_lt (finprod_mem_eq_one_of_infinite hf).le h).le,
end

@[to_additive]
lemma finprod_mem_eq_one_iff_of_one_le (hs : (s ∩ mul_support f).finite) (hf : ∀ x ∈ s, 1 ≤ f x) :
  ∏ᶠ x ∈ s, f x = 1 ↔ ∀ x ∈ s, f x = 1 :=
begin
  convert @finset.prod_eq_one_iff_of_one_le' _ _ _ f hs.to_finset (λ i hi, hf _ _),
  { exact finprod_mem_eq_prod f hs},
  { simp},
  simp only [mem_inter_eq, finite.mem_to_finset] at hi,
  exact hi.1,
end

@[to_additive]
lemma finprod_mem_eq_one_iff_of_le_one (hs : (s ∩ mul_support f).finite) (hf : ∀ x ∈ s, 1 ≤ f x) :
  ∏ᶠ x ∈ s, f x = 1 ↔ ∀ x ∈ s, f x = 1 :=
begin
  sorry,
end

end order
