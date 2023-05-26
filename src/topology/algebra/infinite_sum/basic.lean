/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.nat.parity
import logic.encodable.lattice
import topology.algebra.uniform_group
import topology.algebra.star

/-!
# Infinite sum/product over a topological monoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

## Main declarations

* `has_prod`: Predicate for an infinite product to unconditionally converge to a given value.
* `has_sum`: Predicate for an infinite series to unconditionally converge to a given value.
* `prodable`: Predicate for an infinite product to unconditionally converge to some value.
* `summable`: Predicate for an infinite series to unconditionally converge to some value.
* `tprod`: The value an infinite product converges to, if such value exists. Else, defaults to `1`.
* `tsum`: The value an infinite series converges to, if such value exists. Else, defaults to `0`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

noncomputable theory
open classical filter finset function
open_locale big_operators classical topology

variables {α α' β γ δ G G' : Type*}

section has_prod
variables [comm_monoid α] [topological_space α]

/-- Infinite product on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we
take the product of bigger and bigger sets. This product operation is invariant under reordering. In
particular, the function `ℕ → ℝ` sending `n` to `e ^ ((-1)^n / (n + 1))` does not have a product for
this definition, but a series which is absolutely convergent will have the correct product.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant. -/
@[to_additive "Infinite sum on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant."]
def has_prod (f : β → α) (a : α) : Prop := tendsto (λ s, ∏ b in s, f b) at_top (𝓝 a)

/-- `prodable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
@[to_additive "`summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value."]
def prodable (f : β → α) : Prop := ∃ a, has_prod f a

/-- `∏' i, f i` is the product of `f` it exists, or `1` otherwise. -/
@[to_additive "`∑' i, f i` is the sum of `f` it exists, or `0` otherwise.", irreducible]
def tprod (f : β → α) := if h : prodable f then classical.some h else 1

-- see Note [operator precedence of big operators]
notation `∑'` binders `, ` r:(scoped:67 f, tsum f) := r
notation `∏'` binders `, ` r:(scoped:67 f, tprod f) := r

variables {f g : β → α} {a a' a₁ a₂ b : α} {s : finset β}

@[to_additive] lemma prodable.has_prod (ha : prodable f) : has_prod f (∏' b, f b) :=
by simp [ha, tprod]; exact some_spec ha

@[to_additive] protected lemma has_prod.prodable (h : has_prod f a) : prodable f := ⟨a, h⟩

/-- The constant one function has product `1`. -/
@[to_additive "The constant zero function has sum `0`."]
lemma has_prod_one : has_prod (λ b, 1 : β → α) 1 := by simp [has_prod, tendsto_const_nhds]

@[to_additive] lemma has_prod_empty [is_empty β] : has_prod f 1 := by convert has_prod_one

@[to_additive] lemma prodable_one : prodable (λ b, 1 : β → α) := has_prod_one.prodable

@[to_additive] lemma prodable_empty [is_empty β] : prodable f := has_prod_empty.prodable

@[to_additive] lemma tprod_eq_one_of_not_prodable (h : ¬ prodable f) : ∏' b, f b = 1 :=
by simp [tprod, h]

@[to_additive] lemma prodable_congr (hfg : ∀ b, f b = g b) : prodable f ↔ prodable g :=
iff_of_eq (congr_arg prodable $ funext hfg)

@[to_additive] lemma prodable.congr (hf : prodable f) (hfg : ∀ b, f b = g b) : prodable g :=
(prodable_congr hfg).mp hf

@[to_additive] lemma has_prod.has_prod_of_prod_eq {g : γ → α}
  (h_eq : ∀ u, ∃ v, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ ∏ x in u', g x = ∏ b in v', f b)
  (hf : has_prod g a) :
  has_prod f a :=
le_trans (map_at_top_finset_prod_le_of_prod_eq h_eq) hf

@[to_additive] lemma has_prod_iff_has_prod {g : γ → α}
  (h₁ : ∀ u, ∃ v, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ ∏ x in u', g x = ∏ b in v', f b)
  (h₂ : ∀ v, ∃ u, ∀ u', u ⊆ u' → ∃ v', v ⊆ v' ∧ ∏ b in v', f b = ∏ x in u', g x) :
  has_prod f a ↔ has_prod g a :=
⟨has_prod.has_prod_of_prod_eq h₂, has_prod.has_prod_of_prod_eq h₁⟩

@[to_additive] lemma function.injective.has_prod_iff {g : γ → β} (hg : injective g)
  (hf : ∀ x ∉ set.range g, f x = 1) :
  has_prod (f ∘ g) a ↔ has_prod f a :=
by simp only [has_prod, tendsto, hg.map_at_top_finset_prod_eq hf]

@[to_additive] lemma function.injective.prodable_iff {g : γ → β} (hg : injective g)
  (hf : ∀ x ∉ set.range g, f x = 1) :
  prodable (f ∘ g) ↔ prodable f :=
exists_congr $ λ _, hg.has_prod_iff hf

@[to_additive]
lemma has_prod_subtype_iff_of_mul_support_subset {s : set β} (hf : mul_support f ⊆ s) :
  has_prod (f ∘ coe : s → α) a ↔ has_prod f a :=
subtype.coe_injective.has_prod_iff $ by simpa using mul_support_subset_iff'.1 hf

@[to_additive] lemma has_prod_subtype_iff_mul_indicator {s : set β} :
  has_prod (f ∘ coe : s → α) a ↔ has_prod (s.mul_indicator f) a :=
by rw [← set.mul_indicator_range_comp, subtype.range_coe,
  has_prod_subtype_iff_of_mul_support_subset set.mul_support_mul_indicator_subset]

@[to_additive] lemma prodable_subtype_iff_mul_indicator {s : set β} :
  prodable (f ∘ coe : s → α) ↔ prodable (s.mul_indicator f) :=
exists_congr $ λ _, has_prod_subtype_iff_mul_indicator

@[simp, to_additive]
lemma has_prod_subtype_support : has_prod (f ∘ coe : mul_support f → α) a ↔ has_prod f a :=
has_prod_subtype_iff_of_mul_support_subset $ set.subset.refl _

@[to_additive] lemma has_prod_fintype [fintype β] (f : β → α) : has_prod f (∏ b, f b) :=
order_top.tendsto_at_top_nhds _

@[to_additive] protected lemma finset.has_prod (s : finset β) (f : β → α) :
  has_prod (f ∘ coe : (↑s : set β) → α) (∏ b in s, f b) :=
by { rw ← prod_attach, exact has_prod_fintype _ }

@[to_additive] protected lemma finset.prodable (s : finset β) (f : β → α) :
  prodable (f ∘ coe : (↑s : set β) → α) :=
(s.has_prod f).prodable

@[to_additive] protected lemma set.finite.prodable {s : set β} (hs : s.finite) (f : β → α) :
  prodable (f ∘ coe : s → α) :=
by convert hs.to_finset.prodable f; simp only [hs.coe_to_finset]

/-- If a function `f` vanishes outside of a finite set `s`, then it `has_prod` `∏ b in s, f b`. -/
@[to_additive
"If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`."]
lemma has_prod_prod_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) : has_prod f (∏ b in s, f b) :=
(has_prod_subtype_iff_of_mul_support_subset $ mul_support_subset_iff'.2 hf).1 $ s.has_prod f

@[to_additive] lemma prodable_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) : prodable f :=
(has_prod_prod_of_ne_finset_one hf).prodable

@[to_additive] lemma has_prod_single (b : β) (hf : ∀ b' ≠ b, f b' = 1) : has_prod f (f b) :=
suffices has_prod f (∏ b' in {b}, f b'),
  by simpa using this,
has_prod_prod_of_ne_finset_one $ by simpa [hf]

@[to_additive] lemma has_prod_ite_eq (b : β) [decidable_pred (= b)] (a : α) :
  has_prod (λ b', if b' = b then a else 1) a :=
begin
  convert has_prod_single b _,
  { exact (if_pos rfl).symm },
  { exact λ b' hb', if_neg hb' }
end

@[to_additive] lemma has_prod_pi_mul_single [decidable_eq β] (b : β) (a : α) :
  has_prod (pi.mul_single b a) a :=
show has_prod (λ x, pi.mul_single b a x) a,
  by simpa only [pi.mul_single_apply] using has_prod_ite_eq b a

@[to_additive] lemma equiv.has_prod_iff (e : γ ≃ β) : has_prod (f ∘ e) a ↔ has_prod f a :=
e.injective.has_prod_iff $ by simp

@[to_additive] lemma function.injective.has_prod_range_iff {g : γ → β} (hg : injective g) :
  has_prod (λ x : set.range g, f x) a ↔ has_prod (f ∘ g) a :=
(equiv.of_injective g hg).has_prod_iff.symm

@[to_additive] lemma equiv.prodable_iff (e : γ ≃ β) : prodable (f ∘ e) ↔ prodable f :=
exists_congr $ λ a, e.has_prod_iff

@[to_additive summable.prod_symm]
lemma prodable.prod_symm {f : β × γ → α} (hf : prodable f) : prodable (λ p : γ × β, f p.swap) :=
(equiv.prod_comm γ β).prodable_iff.2 hf

@[to_additive] lemma equiv.has_prod_iff_of_mul_support {g : γ → α}
  (e : mul_support f ≃ mul_support g) (he : ∀ x : mul_support f, g (e x) = f x) :
  has_prod f a ↔ has_prod g a :=
have (g ∘ coe) ∘ e = f ∘ coe, from funext he,
by rw [← has_prod_subtype_support, ← this, e.has_prod_iff, has_prod_subtype_support]

@[to_additive] lemma has_prod_iff_has_prod_of_ne_one_bij {g : γ → α} (i : mul_support g → β)
  (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
  (hf : mul_support f ⊆ set.range i) (hfg : ∀ x, f (i x) = g x) :
  has_prod f a ↔ has_prod g a :=
iff.symm $ equiv.has_prod_iff_of_mul_support
  (equiv.of_bijective (λ x, ⟨i x, λ hx, x.coe_prop $ hfg x ▸ hx⟩)
    ⟨λ x y h, subtype.ext $ hi $ subtype.ext_iff.1 h,
      λ y, (hf y.coe_prop).imp $ λ x hx, subtype.ext hx⟩)
  hfg

@[to_additive] lemma equiv.prodable_iff_of_mul_support {g : γ → α}
  (e : mul_support f ≃ mul_support g) (he : ∀ x : mul_support f, g (e x) = f x) :
  prodable f ↔ prodable g :=
exists_congr $ λ _, e.has_prod_iff_of_mul_support he

@[to_additive] protected lemma has_prod.map [comm_monoid γ] [topological_space γ]
  (hf : has_prod f a) [monoid_hom_class G α γ] (g : G) (hg : continuous g) :
  has_prod (g ∘ f) (g a) :=
have g ∘ (λ s, ∏ b in s, f b) = (λ s, ∏ b in s, g (f b)),
  from funext $ map_prod g _,
show tendsto (λ s, ∏ b in s, g (f b)) at_top (𝓝 (g a)),
  from this ▸ (hg.tendsto a).comp hf

@[to_additive] protected lemma prodable.map [comm_monoid γ] [topological_space γ]
  (hf : prodable f) [monoid_hom_class G α γ] (g : G) (hg : continuous g) :
  prodable (g ∘ f) :=
(hf.has_prod.map g hg).prodable

@[to_additive] protected lemma prodable.map_iff_of_left_inverse [comm_monoid γ]
  [topological_space γ] [monoid_hom_class G α γ] [monoid_hom_class G' γ α] (g : G) (g' : G')
  (hg : continuous g) (hg' : continuous g') (hinv : function.left_inverse g' g) :
  prodable (g ∘ f) ↔ prodable f :=
⟨λ h, by simpa only [←function.comp.assoc g', hinv.id] using h.map _ hg', λ h, h.map _ hg⟩

/-- A special case of `prodable.map_iff_of_left_inverse` for convenience -/
@[to_additive "A special case of `summable.map_iff_of_left_inverse` for convenience"]
protected lemma prodable.map_iff_of_equiv [comm_monoid γ] [topological_space γ]
  [mul_equiv_class G α γ] (g : G) (hg : continuous g)
  (hg' : continuous (mul_equiv_class.inv g : γ → α)) :
  prodable (g ∘ f) ↔ prodable f :=
prodable.map_iff_of_left_inverse g (g : α ≃* γ).symm hg hg' (mul_equiv_class.left_inv g)

/-- If `f : ℕ → α` has product `a`, then the partial prods `∏_{i=1}^{n-1} f i` converge to `a`. -/
@[to_additive
"If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=1}^{n-1} f i` converge to `a`."]
lemma has_prod.tendsto_prod_nat {f : ℕ → α} (h : has_prod f a) :
  tendsto (λ n, ∏ i in range n, f i) at_top (𝓝 a) :=
h.comp tendsto_finset_range

@[to_additive] lemma has_prod.unique [t2_space α] : has_prod f a₁ → has_prod f a₂ → a₁ = a₂ :=
tendsto_nhds_unique

@[to_additive] lemma prodable.has_prod_iff_tendsto_nat [t2_space α] {f : ℕ → α} (hf : prodable f) :
  has_prod f a ↔ tendsto (λ n, ∏ i in range n, f i) at_top (𝓝 a) :=
begin
  refine ⟨λ h, h.tendsto_prod_nat, λ h, _⟩,
  rw tendsto_nhds_unique h hf.has_prod.tendsto_prod_nat,
  exact hf.has_prod
end

@[to_additive] lemma function.surjective.prodable_iff_of_has_prod_iff [comm_monoid α']
  [topological_space α'] {e : α' → α} (hes : surjective e) {g : γ → α'}
  (he : ∀ {a}, has_prod f (e a) ↔ has_prod g a) :
  prodable f ↔ prodable g :=
hes.exists.trans $ exists_congr $ @he

variables [has_continuous_mul α]

@[to_additive] lemma has_prod.mul (hf : has_prod f a) (hg : has_prod g b) :
  has_prod (λ b, f b * g b) (a * b) :=
by simp only [has_prod, prod_mul_distrib]; exact hf.mul hg

@[to_additive] lemma prodable.mul (hf : prodable f) (hg : prodable g) :
  prodable (λ b, f b * g b) :=
(hf.has_prod.mul hg.has_prod).prodable

@[to_additive] lemma has_prod_prod {f : γ → β → α} {a : γ → α} {s : finset γ} :
  (∀ i ∈ s, has_prod (f i) (a i)) → has_prod (λ b, ∏ i in s, f i b) (∏ i in s, a i) :=
finset.induction_on s (by simp only [has_prod_one, prod_empty, forall_true_iff])
  (by simp only [has_prod.mul, prod_insert, mem_insert, forall_eq_or_imp,
        forall_2_true_iff, not_false_iff, forall_true_iff] {contextual := tt})

@[to_additive] lemma prodable_prod {f : γ → β → α} {s : finset γ} (hf : ∀ i ∈ s, prodable (f i)) :
  prodable (λ b, ∏ i in s, f i b) :=
(has_prod_prod $ assume i hi, (hf i hi).has_prod).prodable

@[to_additive] lemma has_prod.mul_disjoint {s t : set β} (hs : disjoint s t)
  (ha : has_prod (f ∘ coe : s → α) a) (hb : has_prod (f ∘ coe : t → α) b) :
  has_prod (f ∘ coe : s ∪ t → α) (a * b) :=
begin
  rw has_prod_subtype_iff_mul_indicator at *,
  rw set.mul_indicator_union_of_disjoint hs,
  exact ha.mul hb,
end

@[to_additive] lemma has_prod_prod_disjoint {ι} (s : finset ι) {t : ι → set β} {a : ι → α}
  (hs : (s : set ι).pairwise (disjoint on t))
  (hf : ∀ i ∈ s, has_prod (f ∘ coe : t i → α) (a i)) :
  has_prod (f ∘ coe : (⋃ i ∈ s, t i) → α) (∏ i in s, a i) :=
begin
  simp_rw has_prod_subtype_iff_mul_indicator at *,
  rw set.mul_indicator_finset_bUnion _ _ hs,
  exact has_prod_prod hf,
end

@[to_additive] lemma has_prod.mul_is_compl {s t : set β} (hs : is_compl s t)
  (ha : has_prod (f ∘ coe : s → α) a) (hb : has_prod (f ∘ coe : t → α) b) :
  has_prod f (a * b) :=
by simpa [← hs.compl_eq]
  using (has_prod_subtype_iff_mul_indicator.1 ha).mul (has_prod_subtype_iff_mul_indicator.1 hb)

@[to_additive] lemma has_prod.mul_compl {s : set β} (ha : has_prod (f ∘ coe : s → α) a)
  (hb : has_prod (f ∘ coe : sᶜ → α) b) :
  has_prod f (a * b) :=
ha.mul_is_compl is_compl_compl hb

@[to_additive] lemma prodable.mul_compl {s : set β} (hs : prodable (f ∘ coe : s → α))
  (hsc : prodable (f ∘ coe : sᶜ → α)) :
  prodable f :=
(hs.has_prod.mul_compl hsc.has_prod).prodable

@[to_additive] lemma has_prod.compl_mul {s : set β} (ha : has_prod (f ∘ coe : sᶜ → α) a)
  (hb : has_prod (f ∘ coe : s → α) b) :
  has_prod f (a * b) :=
ha.mul_is_compl is_compl_compl.symm hb

@[to_additive] lemma has_prod.even_mul_odd {f : ℕ → α} (he : has_prod (λ k, f (2 * k)) a)
  (ho : has_prod (λ k, f (2 * k + 1)) b) :
  has_prod f (a * b) :=
begin
  have := mul_right_injective₀ (two_ne_zero' ℕ),
  replace he := this.has_prod_range_iff.2 he,
  replace ho := ((add_left_injective 1).comp this).has_prod_range_iff.2 ho,
  refine he.mul_is_compl _ ho,
  simpa [(∘)] using nat.is_compl_even_odd
end

@[to_additive] lemma prodable.compl_mul {s : set β} (hs : prodable (f ∘ coe : sᶜ → α))
  (hsc : prodable (f ∘ coe : s → α)) : prodable f :=
(hs.has_prod.compl_mul hsc.has_prod).prodable

@[to_additive] lemma prodable.even_mul_odd {f : ℕ → α} (he : prodable (λ k, f (2 * k)))
  (ho : prodable (λ k, f (2 * k + 1))) : prodable f :=
(he.has_prod.even_mul_odd ho.has_prod).prodable

@[to_additive] protected lemma has_prod.sigma [regular_space α] {γ : β → Type*} {f : (Σ b, γ b) → α}
  {g : β → α} (ha : has_prod f a) (hf : ∀ b, has_prod (λ c, f ⟨b, c⟩) (g b)) : has_prod g a :=
begin
  refine (at_top_basis.tendsto_iff (closed_nhds_basis a)).mpr _,
  rintros s ⟨hs, hsc⟩,
  rcases mem_at_top_sets.mp (ha hs) with ⟨u, hu⟩,
  use [u.image sigma.fst, trivial],
  intros bs hbs,
  simp only [set.mem_preimage, ge_iff_le, finset.le_iff_subset] at hu,
  have : tendsto (λ t : finset (Σ b, γ b), ∏ p in t.filter (λ p, p.1 ∈ bs), f p)
    at_top (𝓝 $ ∏ b in bs, g b),
  { simp only [← sigma_preimage_mk, prod_sigma],
    refine tendsto_finset_prod _ (λ b hb, _),
    change tendsto (λ t, (λ t, ∏ s in t, f ⟨b, s⟩) (preimage t (sigma.mk b) _)) at_top (𝓝 (g b)),
    exact tendsto.comp (hf b) (tendsto_finset_preimage_at_top_at_top _) },
  refine hsc.mem_of_tendsto this (eventually_at_top.2 ⟨u, λ t ht, hu _ (λ x hx, _)⟩),
  exact mem_filter.2 ⟨ht hx, hbs $ mem_image_of_mem _ hx⟩
end

/-- If a series `f` on `β × γ` has product `a` and for each `b` the restriction of `f` to `{b} × γ`
has product `g b`, then the series `g` has product `a`. -/
@[to_additive has_sum.prod_fiberwise "If a series `f` on `β × γ` has sum `a` and for each `b` the
restriction of `f` to `{b} × γ` has sum `g b`, then the series `g` has sum `a`."]
lemma has_prod.prod_fiberwise [regular_space α] {f : β × γ → α} (ha : has_prod f a)
  (hf : ∀ b, has_prod (λ c, f (b, c)) (g b)) : has_prod g a :=
has_prod.sigma ((equiv.sigma_equiv_prod β γ).has_prod_iff.2 ha) hf

@[to_additive] lemma prodable.sigma' [regular_space α] {γ : β → Type*}
  {f : (Σ b, γ b) → α} (ha : prodable f) (hf : ∀ b, prodable (λ c, f ⟨b, c⟩)) :
  prodable (λ b, ∏' c, f ⟨b, c⟩) :=
(ha.has_prod.sigma $ λ b, (hf b).has_prod).prodable

@[to_additive] lemma has_prod.sigma_of_has_prod [t3_space α] {γ : β → Type*} {f : (Σ b, γ b) → α}
  (ha : has_prod g a) (hf : ∀ b, has_prod (λ c, f ⟨b, c⟩) (g b)) (hf' : prodable f) :
  has_prod f a :=
by simpa [(hf'.has_prod.sigma hf).unique ha] using hf'.has_prod

/-- Version of `has_prod.update` for `comm_monoid` rather than `comm_group`.
Rather than showing that `f.update` has a specific sum in terms of `has_prod`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/
@[to_additive "Version of `has_sum.update` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that `f.update` has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist."]
lemma has_prod.update' [t2_space α] {f : β → α} (hf : has_prod f a) (b : β) (x : α)
  (hf' : has_prod (f.update b x) a') : a * x = a' * f b :=
begin
  have : ∀ b', f b' * ite (b' = b) x 1 = f.update b x b' * ite (b' = b) (f b) 1,
  { intro b',
    split_ifs with hb',
    { simpa only [function.update_apply, hb', eq_self_iff_true] using mul_comm (f b) x },
    { simp only [function.update_apply, hb', if_false] } },
  have h := hf.mul ((has_prod_ite_eq b x)),
  simp_rw this at h,
  exact has_prod.unique h (hf'.mul $ has_prod_ite_eq b (f b)),
end

/-- Version of `has_prod_ite_div_has_prod` for `comm_monoid` rather than `comm_group`.
Rather than showing that the `ite` expression has a specific sum in terms of `has_prod`,
it gives a relationship between the sums of `f` and `ite (n = b) 1 (f n)` given that both exist. -/
@[to_additive
"Version of `has_sum_ite_sub_has_sum` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that the `ite` expression has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist."]
lemma eq_mul_of_has_prod_ite [t2_space α] (hf : has_prod f a) (b : β) (a' : α)
  (hf' : has_prod (λ n, ite (n = b) 1 (f n)) a') : a = a' * f b :=
begin
  refine (mul_one a).symm.trans (hf.update' b 1 _),
  convert hf',
  exact funext (f.update_apply b 1),
end

end has_prod

section tprod
variables [comm_monoid α] [topological_space α] {f g : β → α} {a a₁ a₂ : α}

@[to_additive] lemma tprod_congr_subtype (f : β → α) {s t : set β} (h : s = t) :
  ∏' x : s, f x = ∏' x : t, f x := by rw h

@[to_additive] lemma tprod_one' (hz : is_closed ({1} : set α)) : ∏' b : β, (1 : α) = 1 :=
begin
  classical,
  rw [tprod, dif_pos prodable_one],
  suffices : ∀ (x : α), has_prod (λ (b : β), (1 : α)) x → x = 1,
  { exact this _ (classical.some_spec _) },
  intros x hx,
  contrapose! hx,
  simp only [has_prod, tendsto_nhds, finset.prod_const_one, filter.mem_at_top_sets, ge_iff_le,
              finset.le_eq_subset, set.mem_preimage, not_forall, not_exists, exists_prop,
              exists_and_distrib_right],
  refine ⟨{1}ᶜ, ⟨is_open_compl_iff.mpr hz, _⟩, λ y, ⟨⟨y, subset_refl _⟩, _⟩⟩,
  { simpa using hx },
  { simp }
end

@[simp, to_additive] lemma tprod_one [t1_space α] : ∏' b : β, (1 : α) = 1 :=
tprod_one' is_closed_singleton

@[to_additive] lemma tprod_congr (hfg : ∀ b, f b = g b) : ∏' b, f b = ∏' b, g b :=
congr_arg tprod $ funext hfg

variables [t2_space α] {s : finset β}

@[to_additive] lemma has_prod.tprod_eq (ha : has_prod f a) : ∏' b, f b = a :=
(prodable.has_prod ⟨a, ha⟩).unique ha

@[to_additive] lemma prodable.has_prod_iff (h : prodable f) : has_prod f a ↔ ∏' b, f b = a :=
iff.intro has_prod.tprod_eq (assume eq, eq ▸ h.has_prod)

@[simp, to_additive] lemma tprod_empty [is_empty β] : ∏' b, f b = 1 := has_prod_empty.tprod_eq

@[to_additive] lemma tprod_eq_prod (hf : ∀ b ∉ s, f b = 1) : ∏' b, f b = ∏ b in s, f b :=
(has_prod_prod_of_ne_finset_one hf).tprod_eq

@[to_additive] lemma prod_eq_tprod_mul_indicator (f : β → α) (s : finset β) :
  ∏ x in s, f x = ∏' x, set.mul_indicator ↑s f x :=
have ∀ x ∉ s, set.mul_indicator ↑s f x = 1,
from λ x hx, set.mul_indicator_apply_eq_one.2 (λ hx', (hx $ finset.mem_coe.1 hx').elim),
(finset.prod_congr rfl (λ x hx, (set.mul_indicator_apply_eq_self.2 $
  λ hx', (hx' $ finset.mem_coe.2 hx).elim).symm)).trans (tprod_eq_prod this).symm

@[to_additive] lemma tprod_fintype [fintype β] (f : β → α) : ∏' b, f b = ∏ b, f b :=
(has_prod_fintype f).tprod_eq

@[to_additive] lemma tprod_bool (f : bool → α) : ∏' i : bool, f i = f false * f true :=
by rw [tprod_fintype, finset.prod_eq_mul]; simp

@[to_additive] lemma tprod_eq_single (b : β) (hf : ∀ b' ≠ b, f b' = 1) : ∏' b, f b = f b :=
(has_prod_single b hf).tprod_eq

@[to_additive] lemma tprod_tprod_eq_single (f : β → γ → α) (b : β) (c : γ)
  (hfb : ∀ b' ≠ b, f b' c = 1) (hfc : ∀ b' c', c' ≠ c → f b' c' = 1) :
  ∏' b' c', f b' c' = f b c :=
calc ∏' b' c', f b' c' = ∏' b', f b' c : tprod_congr $ λ b', tprod_eq_single _ (hfc b')
... = f b c : tprod_eq_single _ hfb

@[simp, to_additive] lemma tprod_ite_eq (b : β) [decidable_pred (= b)] (a : α) :
  ∏' b', (if b' = b then a else 1) = a :=
(has_prod_ite_eq b a).tprod_eq

@[simp, to_additive] lemma tprod_pi_mul_single [decidable_eq β] (b : β) (a : α) :
  ∏' b', pi.mul_single b a b' = a :=
(has_prod_pi_mul_single b a).tprod_eq

@[to_additive] lemma tprod_dite_right (P : Prop) [decidable P] (x : β → ¬ P → α) :
  ∏' b, (if h : P then (1 : α) else x b h) = if h : P then (1 : α) else ∏' b, x b h :=
by by_cases hP : P; simp [hP]

@[to_additive] lemma tprod_dite_left (P : Prop) [decidable P] (x : β → P → α) :
  ∏' b, (if h : P then x b h else 1) = if h : P then (∏' b, x b h) else 1 :=
by by_cases hP : P; simp [hP]

@[to_additive] lemma function.surjective.tprod_eq_tprod_of_has_prod_iff_has_prod [comm_monoid α']
  [topological_space α'] {e : α' → α} (hes : function.surjective e) (h1 : e 1 = 1) {g : γ → α'}
  (h : ∀ {a}, has_prod f (e a) ↔ has_prod g a) :
  ∏' b, f b = e (∏' c, g c) :=
by_cases
  (assume : prodable g, (h.mpr this.has_prod).tprod_eq)
  (assume hg : ¬ prodable g,
    have hf : ¬ prodable f, from mt (hes.prodable_iff_of_has_prod_iff @h).1 hg,
    by simp [tprod, hf, hg, h1])

@[to_additive]
lemma tprod_eq_tprod_of_has_prod_iff_has_prod {g : γ → α} (h : ∀ {a}, has_prod f a ↔ has_prod g a) :
  ∏' b, f b = ∏'c, g c :=
surjective_id.tprod_eq_tprod_of_has_prod_iff_has_prod rfl @h

@[to_additive] lemma equiv.tprod_eq (j : γ ≃ β) (f : β → α) : ∏'c, f (j c) = ∏' b, f b :=
tprod_eq_tprod_of_has_prod_iff_has_prod $ λ a, j.has_prod_iff

@[to_additive] lemma equiv.tprod_eq_tprod_of_mul_support {g : γ → α}
  (e : mul_support f ≃ mul_support g) (he : ∀ x, g (e x) = f x) :
  (∏' x, f x) = ∏' y, g y :=
tprod_eq_tprod_of_has_prod_iff_has_prod $ λ _, e.has_prod_iff_of_mul_support he

@[to_additive]
lemma tprod_eq_tprod_of_ne_one_bij {g : γ → α} (i : mul_support g → β)
  (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y) (hf : mul_support f ⊆ set.range i)
  (hfg : ∀ x, f (i x) = g x) :
  ∏' x, f x  = ∏' y, g y :=
tprod_eq_tprod_of_has_prod_iff_has_prod $ λ _, has_prod_iff_has_prod_of_ne_one_bij i hi hf hfg

/-! ### `tprod` on subsets -/

@[simp, to_additive] lemma finset.tprod_subtype (s : finset β) (f : β → α) :
  ∏' x : {x // x ∈ s}, f x = ∏ x in s, f x :=
(s.has_prod f).tprod_eq

@[simp, to_additive] lemma finset.tprod_subtype' (s : finset β) (f : β → α) :
  ∏' x : (s : set β), f x = ∏ x in s, f x :=
s.tprod_subtype f

@[to_additive] lemma tprod_subtype (s : set β) (f : β → α) :
  ∏' x : s, f x = ∏' x, s.mul_indicator f x :=
tprod_eq_tprod_of_has_prod_iff_has_prod $ λ _, has_prod_subtype_iff_mul_indicator

@[to_additive]
lemma tprod_subtype_eq_of_mul_support_subset {s : set β} (hs : mul_support f ⊆ s) :
  ∏' x : s, f x = ∏' x, f x :=
tprod_eq_tprod_of_has_prod_iff_has_prod $ λ x, has_prod_subtype_iff_of_mul_support_subset hs

@[simp, to_additive] lemma tprod_univ (f : β → α) :
  ∏' x : (set.univ : set β), f x = ∏' x, f x :=
tprod_subtype_eq_of_mul_support_subset $ set.subset_univ _

@[simp, to_additive] lemma tprod_singleton (b : β) (f : β → α) : ∏' x : ({b} : set β), f x = f b :=
begin
  rw [tprod_subtype, tprod_eq_single b],
  { simp },
  { intros b' hb',
    rw set.mul_indicator_of_not_mem,
    rwa set.mem_singleton_iff },
  { apply_instance }
end

@[to_additive] lemma tprod_image {g : γ → β} (f : β → α) {s : set γ} (hg : set.inj_on g s) :
  ∏' x : g '' s, f x = ∏' x : s, f (g x) :=
((equiv.set.image_of_inj_on _ _ hg).tprod_eq (λ x, f x)).symm

@[to_additive] lemma tprod_range {g : γ → β} (f : β → α) (hg : injective g) :
  ∏' x : set.range g, f x = ∏' x, f (g x) :=
by rw [← set.image_univ, tprod_image f (hg.inj_on _), tprod_univ (f ∘ g)]

section has_continuous_mul
variable [has_continuous_mul α]

@[to_additive] lemma tprod_mul (hf : prodable f) (hg : prodable g) :
  ∏' b, f b * g b = (∏' b, f b) * (∏' b, g b) :=
(hf.has_prod.mul hg.has_prod).tprod_eq

@[to_additive tsum_sum]
lemma tprod_prod'' {f : γ → β → α} {s : finset γ} (hf : ∀ i ∈ s, prodable (f i)) :
  ∏' b, ∏ i in s, f i b = ∏ i in s, ∏' b, f i b :=
(has_prod_prod $ λ i hi, (hf i hi).has_prod).tprod_eq

/-- Version of `tprod_eq_mul_tprod_ite` for `comm_monoid` rather than `comm_group`.
Requires a different convergence assumption involving `function.update`. -/
@[to_additive "Version of `tsum_eq_mul_tsum_ite` for `add_comm_monoid` rather
than `add_comm_group`. Requires a different convergence assumption involving `function.update`."]
lemma tprod_eq_mul_tprod_ite' (b : β) (hf : prodable (f.update b 1)) :
  ∏' x, f x = f b * ∏' x, ite (x = b) 1 (f x) :=
calc ∏' x, f x = ∏' x, ((ite (x = b) (f x) 1) * (f.update b 1 x)) :
    tprod_congr (λ n, by split_ifs; simp [function.update_apply, h])
  ... = (∏' x, ite (x = b) (f x) 1) * ∏' x, f.update b 1 x :
    tprod_mul ⟨ite (b = b) (f b) 1, has_prod_single b (λ b hb, if_neg hb)⟩ hf
  ... = ite (b = b) (f b) 1 * ∏' x, f.update b 1 x :
    by { congr, exact (tprod_eq_single b (λ b' hb', if_neg hb')) }
  ... = f b * ∏' x, ite (x = b) 1 (f x) :
    by simp only [function.update, eq_self_iff_true, if_true, eq_rec_constant, dite_eq_ite]

variables [comm_monoid δ] [topological_space δ] [t3_space δ] [has_continuous_mul δ]

@[to_additive]
lemma tprod_sigma' {γ : β → Type*} {f : (Σ b, γ b) → δ} (h₁ : ∀ b, prodable (λ c, f ⟨b, c⟩))
  (h₂ : prodable f) : ∏' p, f p = ∏' b c, f ⟨b, c⟩ :=
(h₂.has_prod.sigma $ λ b, (h₁ b).has_prod).tprod_eq.symm

@[to_additive tsum_prod']
lemma tprod_prod' {f : β × γ → δ} (h : prodable f) (h₁ : ∀ b, prodable (λ c, f (b, c))) :
  ∏' p, f p = ∏' b c, f (b, c) :=
(h.has_prod.prod_fiberwise $ λ b, (h₁ b).has_prod).tprod_eq.symm

@[to_additive]
lemma tprod_comm' {f : β → γ → δ} (h : prodable (uncurry f)) (h₁ : ∀ b, prodable (f b))
  (h₂ : ∀ c, prodable (λ b, f b c)) :
  ∏' c b, f b c = ∏' b c, f b c :=
begin
  erw [←tprod_prod' h h₁, ←tprod_prod' h.prod_symm h₂, ←(equiv.prod_comm γ β).tprod_eq (uncurry f)],
  refl
end

end has_continuous_mul

open encodable

section encodable
variable [encodable γ]

/-- You can compute a product over an encodable type by multiplying over the natural numbers and
taking a supremum. This is useful for outer measures. -/
@[to_additive "You can compute a sum over an encodable type by summing over the natural numbers and
taking a supremum. This is useful for outer measures."]
lemma tprod_supr_decode₂ [complete_lattice β] (m : β → α) (m1 : m ⊥ = 1) (s : γ → β) :
  ∏' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b) = ∏' b : γ, m (s b) :=
begin
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 1 → (decode₂ γ n).is_some,
  { intros n h,
    cases decode₂ γ n with b,
    { refine (h $ by simp [m1]).elim },
    { exact rfl } },
  symmetry, refine tprod_eq_tprod_of_ne_one_bij (λ a, option.get (H a.1 a.2)) _ _ _,
  { rintros ⟨m, hm⟩ ⟨n, hn⟩ e,
    have := mem_decode₂.1 (option.get_mem (H n hn)),
    rwa [← e, mem_decode₂.1 (option.get_mem (H m hm))] at this },
  { intros b h,
    refine ⟨⟨encode b, _⟩, _⟩,
    { simp only [mem_mul_support, encodek₂] at h ⊢, convert h, simp [set.ext_iff, encodek₂] },
    { exact option.get_of_mem _ (encodek₂ _) } },
  { rintros ⟨n, h⟩, dsimp only [subtype.coe_mk],
    transitivity, swap,
    rw [show decode₂ γ n = _, from option.get_mem (H n h)],
    congr, simp [ext_iff, -option.some_get] }
end

/-- `tprod_supr_decode₂` specialized to the complete lattice of sets. -/
@[to_additive "`tsum_supr_decode₂` specialized to the complete lattice of sets."]
lemma tprod_Union_decode₂ (m : set β → α) (m1 : m ∅ = 1) (s : γ → set β) :
  ∏' i, m (⋃ b ∈ decode₂ γ i, s b) = ∏' b, m (s b) :=
tprod_supr_decode₂ m m1 s

end encodable

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/

section countable
variables [countable γ]

/-- If a function is countably submultiplicative then it is submultiplicative on countable types. -/
@[to_additive
"If a function is countably subadditive then it is subadditive on countable types."]
lemma rel_supr_tprod [complete_lattice β] (m : β → α) (m1 : m ⊥ = 1) (R : α → α → Prop)
  (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) ∏' i, m (s i)) (s : γ → β) :
  R (m (⨆ b : γ, s b)) ∏' b : γ, m (s b) :=
by { casesI nonempty_encodable γ, rw [←supr_decode₂, ←tprod_supr_decode₂ _ m1 s], exact m_supr _ }

/-- If a function is countably submultiplicative then it is submultiplicative on finite sets. -/
@[to_additive "If a function is countably subadditive then it is subadditive on finite sets."]
lemma rel_supr_prod [complete_lattice β] (m : β → α) (m1 : m ⊥ = 1) (R : α → α → Prop)
  (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : δ → β) (t : finset δ) :
  R (m (⨆ d ∈ t, s d)) (∏ d in t, m (s d)) :=
by { rw [supr_subtype', ←finset.tprod_subtype], exact rel_supr_tprod m m1 R m_supr _ }

/-- If a function is countably submultiplicative then it is binary submultiplicative. -/
@[to_additive "If a function is countably subadditive then it is binary subadditive."]
lemma rel_sup_mul [complete_lattice β] (m : β → α) (m1 : m ⊥ = 1) (R : α → α → Prop)
  (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∏' i, m (s i))) (s₁ s₂ : β) :
  R (m (s₁ ⊔ s₂)) (m s₁ * m s₂) :=
begin
  convert rel_supr_tprod m m1 R m_supr (λ b, cond b s₁ s₂),
  { simp only [supr_bool_eq, cond] },
  { rw [tprod_fintype, fintype.prod_bool, cond, cond] }
end

end countable

variables [has_continuous_mul α]

@[to_additive] lemma tprod_mul_tprod_compl {s : set β} (hs : prodable (f ∘ coe : s → α))
  (hsc : prodable (f ∘ coe : sᶜ → α)) :
  (∏' x : s, f x) * (∏' x : sᶜ, f x) = ∏' x, f x :=
(hs.has_prod.mul_compl hsc.has_prod).tprod_eq.symm

@[to_additive] lemma tprod_union_disjoint {s t : set β} (hd : disjoint s t)
  (hs : prodable (f ∘ coe : s → α)) (ht : prodable (f ∘ coe : t → α)) :
  (∏' x : s ∪ t, f x) = (∏' x : s, f x) * (∏' x : t, f x) :=
(hs.has_prod.mul_disjoint hd ht.has_prod).tprod_eq

@[to_additive] lemma tprod_finset_bUnion_disjoint {ι} {s : finset ι} {t : ι → set β}
  (hd : (s : set ι).pairwise (disjoint on t))
  (hf : ∀ i ∈ s, prodable (f ∘ coe : t i → α)) :
  ∏' x : (⋃ i ∈ s, t i), f x = ∏ i in s, ∏' x : t i, f x :=
(has_prod_prod_disjoint _ hd (λ i hi, (hf i hi).has_prod)).tprod_eq

@[to_additive] lemma tprod_even_mul_odd {f : ℕ → α} (he : prodable (λ k, f (2 * k)))
  (ho : prodable (λ k, f (2 * k + 1))) :
  (∏' k, f (2 * k)) * (∏' k, f (2 * k + 1)) = ∏' k, f k :=
(he.has_prod.even_mul_odd ho.has_prod).tprod_eq.symm

end tprod

section topological_group
variables [comm_group α] [topological_space α] [topological_group α] {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
@[to_additive] lemma has_prod.inv (h : has_prod f a) : has_prod (λ b, (f b)⁻¹) a⁻¹ :=
by simpa only using h.map (monoid_hom.id α)⁻¹ continuous_inv

@[to_additive] lemma prodable.inv (hf : prodable f) : prodable (λ b, (f b)⁻¹) :=
hf.has_prod.inv.prodable

@[to_additive] lemma prodable.of_inv (hf : prodable (λ b, (f b)⁻¹)) : prodable f :=
by simpa only [inv_inv] using hf.inv

@[to_additive] lemma prodable_inv_iff : prodable (λ b, (f b)⁻¹) ↔ prodable f :=
⟨prodable.of_inv, prodable.inv⟩

@[to_additive] lemma has_prod.div (hf : has_prod f a₁) (hg : has_prod g a₂) :
  has_prod (λ b, f b / g b) (a₁ / a₂) :=
by { simp only [div_eq_mul_inv], exact hf.mul hg.inv }

@[to_additive] lemma prodable.div (hf : prodable f) (hg : prodable g) : prodable (λ b, f b / g b) :=
(hf.has_prod.div hg.has_prod).prodable

@[to_additive] lemma prodable.trans_div (hg : prodable g) (hfg : prodable (λ b, f b / g b)) :
  prodable f :=
by simpa only [div_mul_cancel'] using hfg.mul hg

@[to_additive] lemma prodable_iff_of_prodable_div (hfg : prodable (λ b, f b / g b)) :
  prodable f ↔ prodable g :=
⟨λ hf, hf.trans_div $ by simpa only [inv_div] using hfg.inv, λ hg, hg.trans_div hfg⟩

@[to_additive] lemma has_prod.update (hf : has_prod f a₁) (b : β) [decidable_eq β] (a : α) :
  has_prod (update f b a) (a / f b * a₁) :=
begin
  convert (has_prod_ite_eq b _).mul hf,
  ext b',
  split_ifs,
  { rw [h, update_same, div_mul_cancel'] },
  { rw [update_noteq h, one_mul] }
end

@[to_additive] lemma prodable.update (hf : prodable f) (b : β) [decidable_eq β] (a : α) :
  prodable (update f b a) :=
(hf.has_prod.update b a).prodable

@[to_additive] lemma has_prod.has_prod_compl_iff {s : set β} (hf : has_prod (f ∘ coe : s → α) a₁) :
  has_prod (f ∘ coe : sᶜ → α) a₂ ↔ has_prod f (a₁ * a₂) :=
begin
  refine ⟨λ h, hf.mul_compl h, λ h, _⟩,
  rw [has_prod_subtype_iff_mul_indicator] at hf ⊢,
  rw [set.mul_indicator_compl, ←div_eq_mul_inv],
  simpa only [mul_div_cancel'''] using h.div hf,
end

@[to_additive] lemma has_prod.has_prod_iff_compl {s : set β} (hf : has_prod (f ∘ coe : s → α) a₁) :
  has_prod f a₂ ↔ has_prod (f ∘ coe : sᶜ → α) (a₂ / a₁) :=
iff.symm $ hf.has_prod_compl_iff.trans $ by rw [mul_div_cancel'_right]

@[to_additive] lemma prodable.prodable_compl_iff {s : set β} (hf : prodable (f ∘ coe : s → α)) :
  prodable (f ∘ coe : sᶜ → α) ↔ prodable f :=
⟨λ ⟨a, ha⟩, (hf.has_prod.has_prod_compl_iff.1 ha).prodable,
  λ ⟨a, ha⟩, (hf.has_prod.has_prod_iff_compl.1 ha).prodable⟩

@[to_additive] protected lemma finset.has_prod_compl_iff (s : finset β) :
  has_prod (λ x : {x // x ∉ s}, f x) a ↔ has_prod f (a * ∏ i in s, f i) :=
(s.has_prod f).has_prod_compl_iff.trans $ by rw [mul_comm]

@[to_additive] protected lemma finset.has_prod_iff_compl (s : finset β) :
  has_prod f a ↔ has_prod (λ x : {x // x ∉ s}, f x) (a / ∏ i in s, f i) :=
(s.has_prod f).has_prod_iff_compl

@[to_additive] protected lemma finset.prodable_compl_iff (s : finset β) :
  prodable (λ x : {x // x ∉ s}, f x) ↔ prodable f :=
(s.prodable f).prodable_compl_iff

@[to_additive] lemma set.finite.prodable_compl_iff {s : set β} (hs : s.finite) :
  prodable (f ∘ coe : sᶜ → α) ↔ prodable f :=
(hs.prodable f).prodable_compl_iff

@[to_additive] lemma has_prod_ite_div_has_prod [decidable_eq β] (hf : has_prod f a) (b : β) :
  has_prod (λ n, ite (n = b) 1 (f n)) (a / f b) :=
begin
  convert hf.update b 1 using 1,
  { ext n,
    rw function.update_apply },
  { rw [div_mul_eq_mul_div, one_mul] }
end

section tsum
variables [t2_space α]

@[to_additive] lemma tprod_inv : ∏' b, (f b)⁻¹ = (∏' b, f b)⁻¹ :=
begin
  by_cases hf : prodable f,
  { exact hf.has_prod.inv.tprod_eq },
  { simp [tprod_eq_one_of_not_prodable hf, tprod_eq_one_of_not_prodable (mt prodable.of_inv hf)] },
end

@[to_additive] lemma tprod_div (hf : prodable f) (hg : prodable g) :
  ∏' b, (f b / g b) = (∏' b, f b) / ∏' b, g b :=
(hf.has_prod.div hg.has_prod).tprod_eq

@[to_additive] lemma prod_mul_tprod_compl {s : finset β} (hf : prodable f) :
  (∏ x in s, f x) * (∏' x : (↑s : set β)ᶜ, f x) = ∏' x, f x :=
((s.has_prod f).mul_compl (s.prodable_compl_iff.2 hf).has_prod).tprod_eq.symm

/-- Let `f : β → α` be a sequence with prodable series and let `b ∈ β` be an index. This lemma
writes `∏ f n` as the sum of `f b` plus the series of the remaining terms. -/
@[to_additive
"Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index. This lemma writes
`Σ f n` as the sum of `f b` plus the series of the remaining terms."]
lemma tprod_eq_mul_tprod_ite [decidable_eq β] (hf : prodable f) (b : β) :
  ∏' n, f n = f b * ∏' n, ite (n = b) 1 (f n) :=
begin
  rw (has_prod_ite_div_has_prod hf.has_prod b).tprod_eq,
  exact (mul_div_cancel'_right _ _).symm,
end

end tsum

/-!
### Sums on nat

We show the formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in
`sum_add_tsum_nat_add`, as well as several results relating sums on `ℕ` and `ℤ`.
-/
section nat

@[to_additive] lemma has_prod_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
  has_prod (λ n, f (n + k)) a ↔ has_prod f (a * ∏ i in range k, f i) :=
begin
  refine iff.trans _ (range k).has_prod_compl_iff,
  rw ←(not_mem_range_equiv k).symm.has_prod_iff,
  refl
end

@[to_additive] lemma prodable_nat_add_iff {f : ℕ → α} (k : ℕ) :
  prodable (λ n, f (n + k)) ↔ prodable f :=
iff.symm $ (equiv.mul_right (∏ i in range k, f i)).surjective.prodable_iff_of_has_prod_iff $
  λ a, (has_prod_nat_add_iff k).symm

@[to_additive] lemma has_prod_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
  has_prod (λ n, f (n + k)) (a / ∏ i in range k, f i) ↔ has_prod f a :=
by simp [has_prod_nat_add_iff]

@[to_additive] lemma prod_mul_tprod_nat_add [t2_space α] {f : ℕ → α} (k : ℕ) (h : prodable f) :
  (∏ i in range k, f i) * (∏' i, f (i + k)) = ∏' i, f i :=
by simpa only [mul_comm] using
  ((has_prod_nat_add_iff k).1 ((prodable_nat_add_iff k).2 h).has_prod).unique h.has_prod

@[to_additive] lemma tprod_eq_zero_mul [t2_space α] {f : ℕ → α} (hf : prodable f) :
  ∏' b, f b = f 0 * ∏' b, f (b + 1) :=
by simpa only [prod_range_one] using (prod_mul_tprod_nat_add 1 hf).symm

/-- For `f : ℕ → α`, then `∏' k, f (k + i)` tends to zero. This does not require a productability
assumption on `f`, as otherwise all products are zero. -/
@[to_additive "For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a
summability assumption on `f`, as otherwise all sums are zero."]
lemma tendsto_prod_nat_add [t2_space α] (f : ℕ → α) : tendsto (λ i, ∏' k, f (k + i)) at_top (𝓝 1) :=
begin
  by_cases hf : prodable f,
  { have h₀ : (λ i, (∏' i, f i) / ∏ j in range i, f j) = λ i, ∏' k, f (k + i),
    { ext1 i,
      rw [div_eq_iff_eq_mul, mul_comm, prod_mul_tprod_nat_add i hf] },
    have h₁ : tendsto (λ i : ℕ, ∏' i, f i) at_top (𝓝 (∏' i, f i)) := tendsto_const_nhds,
    simpa only [h₀, div_self'] using h₁.div' hf.has_prod.tendsto_prod_nat },
  { convert tendsto_const_nhds,
    ext1 i,
    rw ← prodable_nat_add_iff i at hf,
    { exact tprod_eq_one_of_not_prodable hf },
    { apply_instance } }
end

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both convergent series then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...`. -/
@[to_additive "If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both convergent series then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...`."]
lemma has_prod.int_rec {b : α} {f g : ℕ → α} (hf : has_prod f a) (hg : has_prod g b) :
  @has_prod α _ _ _ (@int.rec (λ _, α) f g : ℤ → α) (a * b) :=
begin
  -- note this proof works for any two-case inductive
  have h₁ : injective (coe : ℕ → ℤ) := @int.of_nat.inj,
  have h₂ : injective int.neg_succ_of_nat := @int.neg_succ_of_nat.inj,
  refine has_prod.mul_is_compl ⟨_, _⟩ (h₁.has_prod_range_iff.mpr hf) (h₂.has_prod_range_iff.mpr hg),
  { rw disjoint_iff_inf_le,
    rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩ },
  { rw codisjoint_iff_le_sup,
    rintro (i | j) h,
    exacts [or.inl ⟨_, rfl⟩, or.inr ⟨_, rfl⟩] }
end

@[to_additive] lemma has_prod.nonneg_mul_neg {b : α} {f : ℤ → α}
  (hnonneg : has_prod (λ n : ℕ, f n) a) (hneg : has_prod (λ n : ℕ, f (-n.succ)) b) :
  has_prod f (a * b) :=
begin
  simp_rw ← int.neg_succ_of_nat_coe at hneg,
  convert hnonneg.int_rec hneg using 1,
  ext (i | j); refl,
end

@[to_additive] lemma has_prod.pos_mul_zero_mul_neg {b : α} {f : ℤ → α}
  (hpos : has_prod (λ n : ℕ, f (n + 1)) a) (hneg : has_prod (λ n : ℕ, f (-n.succ)) b) :
  has_prod f (a * f 0 * b) :=
begin
  have : ∀ g : ℕ → α, has_prod (λ k, g (k + 1)) a → has_prod g (a * g 0),
  { intros g hg, simpa using (has_prod_nat_add_iff _).mp hg },
  exact (this (λ n, f n) hpos).nonneg_mul_neg hneg,
end

@[to_additive] lemma prodable_int_of_prodable_nat {f : ℤ → α}
  (hp : prodable (λ n : ℕ, f n)) (hn : prodable (λ n : ℕ, f (-n))) : prodable f :=
(has_prod.nonneg_mul_neg hp.has_prod $ prodable.has_prod $ (prodable_nat_add_iff 1).mpr hn).prodable

@[to_additive] lemma has_prod.prod_nat_of_prod_int {α : Type*} [comm_monoid α] [topological_space α]
  [has_continuous_mul α] {a : α} {f : ℤ → α} (hf : has_prod f a) :
  has_prod (λ n : ℕ, f n * f (-n)) (a * f 0) :=
begin
  apply (hf.mul (has_prod_ite_eq (0 : ℤ) (f 0))).has_prod_of_prod_eq (λ u, _),
  refine ⟨u.image int.nat_abs, λ v' hv', _⟩,
  let u1 := v'.image (λ (x : ℕ), (x : ℤ)),
  let u2 := v'.image (λ (x : ℕ), - (x : ℤ)),
  have A : u ⊆ u1 ∪ u2,
  { assume x hx,
    simp only [mem_union, mem_image, exists_prop],
    rcases le_total 0 x with h'x|h'x,
    { left,
      refine ⟨int.nat_abs x, hv' _, _⟩,
      { simp only [mem_image, exists_prop],
        exact ⟨x, hx, rfl⟩ },
      { simp only [h'x, int.coe_nat_abs, abs_eq_self] } },
    { right,
      refine ⟨int.nat_abs x, hv' _, _⟩,
      { simp only [mem_image, exists_prop],
        exact ⟨x, hx, rfl⟩ },
      { simp only [abs_of_nonpos h'x, int.coe_nat_abs, neg_neg] } } },
  refine ⟨u1 ∪ u2, A, _⟩,
  calc ∏ x in u1 ∪ u2, (f x * ite (x = 0) (f 0) 1)
      = (∏ x in u1 ∪ u2, f x) * ∏ x in u1 ∩ u2, f x :
    begin
      rw prod_mul_distrib,
      congr' 1,
      refine (prod_subset_one_on_sdiff inter_subset_union _ _).symm,
      { assume x hx,
        suffices : x ≠ 0, by simp only [this, if_false],
        rintros rfl,
        simpa only [mem_sdiff, mem_union, mem_image, neg_eq_zero, or_self, mem_inter, and_self,
          and_not_self] using hx },
      { assume x hx,
        simp only [mem_inter, mem_image, exists_prop] at hx,
        have : x = 0,
        { apply le_antisymm,
          { rcases hx.2 with ⟨a, ha, rfl⟩,
            simp only [right.neg_nonpos_iff, nat.cast_nonneg] },
          { rcases hx.1 with ⟨a, ha, rfl⟩,
            simp only [nat.cast_nonneg] } },
        simp only [this, eq_self_iff_true, if_true] }
    end
  ... = (∏ x in u1, f x) * ∏ x in u2, f x : prod_union_inter
  ... = (∏ b in v', f b) * ∏ b in v', f (-b) :
    by simp only [prod_image, nat.cast_inj, imp_self, implies_true_iff, neg_inj]
  ... = ∏ b in v', f b * f (-b) : prod_mul_distrib.symm
end

end nat

end topological_group

section uniform_group
variables [comm_group α] [uniform_space α]

/-- The **Cauchy criterion** for infinite products, also known as the **Cauchy convergence test** -/
@[to_additive
"The **Cauchy criterion** for infinite sums, also known as the **Cauchy convergence test**"]
lemma prodable_iff_cauchy_seq_finset [complete_space α] {f : β → α} :
  prodable f ↔ cauchy_seq (λ s, ∏ b in s, f b) :=
cauchy_map_iff_exists_tendsto.symm

variables [uniform_group α] {f g : β → α} {a a₁ a₂ : α}

@[to_additive] lemma cauchy_seq_finset_prod_iff_vanishing :
  cauchy_seq (λ s, ∏ b in s, f b) ↔
    ∀ e ∈ 𝓝 (1 : α), ∃ s, ∀ t, disjoint t s → ∏ b in t, f b ∈ e :=
begin
  simp only [cauchy_seq, cauchy_map_iff, and_iff_right at_top_ne_bot,
    prod_at_top_at_top_eq, uniformity_eq_comap_nhds_one α, tendsto_comap_iff, (∘)],
  rw [tendsto_at_top'],
  refine ⟨λ h e he, _, λ h e he, _⟩,
  { obtain ⟨⟨s₁, s₂⟩, h⟩ := h _ he,
    refine ⟨s₁ ∪ s₂, λ t ht, _⟩,
    specialize h (s₁ ∪ s₂, (s₁ ∪ s₂) ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩,
    simpa only [finset.prod_union ht.symm, mul_div_cancel'''] using h },
  { obtain ⟨d, hd, hde⟩ := exists_nhds_split_inv he,
    obtain ⟨s, h⟩ := h _ hd,
    use [(s, s)],
    rintros ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩,
    have : (∏ b in t₂, f b) / ∏ b in t₁, f b = (∏ b in t₂ \ s, f b) / ∏ b in t₁ \ s, f b,
    { simp only [←finset.prod_sdiff ht₁, ←finset.prod_sdiff ht₂, mul_div_mul_right_eq_div] },
    simp only [this],
    exact hde _ (h _ finset.sdiff_disjoint) _ (h _ finset.sdiff_disjoint) }
end

/-- The prod over the complement of a finset tends to `1` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all prods are one. -/
@[to_additive "The sum over the complement of a finset tends to `0`
when the finset grows to cover the whole space. This does not need a summability assumption, as
otherwise all sums are zero."]
lemma tendsto_tprod_compl_at_top_one (f : β → α) :
  tendsto (λ s : finset β, ∏' b : {x // x ∉ s}, f b) at_top (𝓝 1) :=
begin
  by_cases H : prodable f,
  { rintro e he,
    rcases exists_mem_nhds_is_closed_subset he with ⟨o, ho, o_closed, oe⟩,
    simp only [le_eq_subset, set.mem_preimage, mem_at_top_sets, filter.mem_map, ge_iff_le],
    obtain ⟨s, hs⟩ := cauchy_seq_finset_prod_iff_vanishing.1 H.has_prod.cauchy_seq o ho,
    refine ⟨s, λ a sa, oe _⟩,
    have A : prodable (λ b : {x // x ∉ a}, f b) := a.prodable_compl_iff.2 H,
    refine o_closed.mem_of_tendsto A.has_prod (eventually_of_forall $ λ b, _),
    rw ←prod_image (subtype.coe_injective.inj_on _),
    refine hs _ (disjoint_left.2 (λ i hi his, _)),
    apply_instance,
    obtain ⟨i', hi', rfl⟩ := mem_image.1 hi,
    exact i'.2 (sa his) },
  { convert tendsto_const_nhds,
    ext s,
    apply tprod_eq_one_of_not_prodable,
    rwa finset.prodable_compl_iff }
end

variable [complete_space α]

@[to_additive] lemma prodable_iff_vanishing :
  prodable f ↔ ∀ e ∈ 𝓝 (1 : α), ∃ s, ∀ t, disjoint t s → ∏ b in t, f b ∈ e :=
by rw [prodable_iff_cauchy_seq_finset, cauchy_seq_finset_prod_iff_vanishing]

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a * b) / b = a` -/
@[to_additive]
lemma prodable.prodable_of_eq_one_or_self (hf : prodable f) (h : ∀ b, g b = 1 ∨ g b = f b) :
  prodable g :=
prodable_iff_vanishing.2 $
  λ e he,
  let ⟨s, hs⟩ := prodable_iff_vanishing.1 hf e he in
  ⟨s, λ t ht,
    have eq : ∏ b in t.filter (λb, g b = f b), f b = ∏ b in t, g b :=
      calc ∏ b in t.filter (λb, g b = f b), f b = ∏ b in t.filter (λb, g b = f b), g b :
          finset.prod_congr rfl (λ b hb, (finset.mem_filter.1 hb).2.symm)
        ... = ∏ b in t, g b :
        begin
          refine finset.prod_subset (finset.filter_subset _ _) _,
          assume b hbt hb,
          simp only [(∉), finset.mem_filter, and_iff_right hbt] at hb,
          exact (h b).resolve_right hb
        end,
    eq ▸ hs _ $ finset.disjoint_of_subset_left (finset.filter_subset _ _) ht⟩

@[to_additive] protected lemma prodable.mul_indicator (hf : prodable f) (s : set β) :
  prodable (s.mul_indicator f) :=
hf.prodable_of_eq_one_or_self $ set.mul_indicator_eq_one_or_self _ _

@[to_additive] lemma prodable.comp_injective {i : γ → β} (hf : prodable f) (hi : injective i) :
  prodable (f ∘ i) :=
begin
  simpa only [set.mul_indicator_range_comp]
    using (hi.prodable_iff _).2 (hf.mul_indicator (set.range i)),
  exact λ x hx, set.mul_indicator_of_not_mem hx _
end

@[to_additive] protected lemma prodable.subtype (hf : prodable f) (s : set β) :
  prodable (f ∘ coe : s → α) :=
hf.comp_injective subtype.coe_injective

@[to_additive] lemma prodable_subtype_and_compl {s : set β} :
  prodable (λ x : s, f x) ∧ prodable (λ x : sᶜ, f x) ↔ prodable f :=
⟨and_imp.2 prodable.mul_compl, λ h, ⟨h.subtype s, h.subtype sᶜ⟩⟩

@[to_additive]
lemma prodable.sigma_factor {γ : β → Type*} {f : (Σ b, γ b) → α} (ha : prodable f) (b : β) :
  prodable (λ c, f ⟨b, c⟩) :=
ha.comp_injective sigma_mk_injective

@[to_additive]
protected lemma prodable.sigma {γ : β → Type*} {f : (Σ b, γ b) → α} (ha : prodable f) :
  prodable (λ b, ∏'c, f ⟨b, c⟩) :=
ha.sigma' (λ b, ha.sigma_factor b)

@[to_additive] lemma prodable.prod_factor {f : β × γ → α} (h : prodable f) (b : β) :
  prodable (λ c, f (b, c)) :=
h.comp_injective $ λ c₁ c₂ h, (prod.ext_iff.1 h).2

section loc_instances
-- enable inferring a T3-topological space from a topological group
local attribute [instance] topological_add_group.t3_space
-- disable getting a T0-space from a T3-space as this causes loops
local attribute [-instance] t3_space.to_t0_space

@[to_additive]
lemma tprod_sigma [t0_space α] {γ : β → Type*} {f : (Σ b, γ b) → α} (ha : prodable f) :
  ∏' p, f p = ∏' b c, f ⟨b, c⟩ :=
tprod_sigma' (λ b, ha.sigma_factor b) ha

@[to_additive tsum_prod] lemma tprod_prod [t0_space α] {f : β × γ → α} (h : prodable f) :
  ∏' p, f p = ∏' b c, f ⟨b, c⟩ :=
tprod_prod' h h.prod_factor

@[to_additive] lemma tprod_comm [t0_space α] {f : β → γ → α} (h : prodable (uncurry f)) :
  ∏' c b, f b c = ∏' b c, f b c :=
tprod_comm' h h.prod_factor h.prod_symm.prod_factor

end loc_instances

@[to_additive]
lemma tprod_subtype_mul_tprod_subtype_compl [t2_space α] (hf : prodable f) (s : set β) :
  (∏' x : s, f x) * ∏' x : sᶜ, f x = ∏' x, f x :=
((hf.subtype s).has_prod.mul_compl (hf.subtype {x | x ∉ s}).has_prod).unique hf.has_prod

@[to_additive]
lemma prod_mul_tprod_subtype_compl [t2_space α] (hf : prodable f) (s : finset β) :
  (∏ x in s, f x) * ∏' x : {x // x ∉ s}, f x = ∏' x, f x :=
by { rw [←tprod_subtype_mul_tprod_subtype_compl hf s, finset.tprod_subtype'], refl }

end uniform_group

section topological_group
variables [topological_space G] [comm_group G] [topological_group G] {f : α → G}

@[to_additive]
lemma prodable.vanishing (hf : prodable f) ⦃e : set G⦄ (he : e ∈ 𝓝 (1 : G)) :
  ∃ s : finset α, ∀ t, disjoint t s → ∏ k in t, f k ∈ e :=
begin
  letI : uniform_space G := topological_group.to_uniform_space G,
  letI : uniform_group G := topological_comm_group_is_uniform,
  rcases hf with ⟨y, hy⟩,
  exact cauchy_seq_finset_prod_iff_vanishing.1 hy.cauchy_seq e he,
end

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to one along
`cofinite`. -/
@[to_additive "Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`."]
lemma prodable.tendsto_cofinite_one (hf : prodable f) : tendsto f cofinite (𝓝 1) :=
begin
  intros e he,
  rw [filter.mem_map],
  rcases hf.vanishing he with ⟨s, hs⟩,
  refine s.eventually_cofinite_nmem.mono (λ x hx, _),
  by simpa using hs {x} (disjoint_singleton_left.2 hx)
end

@[to_additive] lemma prodable.tendsto_at_top_one {f : ℕ → G} (hf : prodable f) :
  tendsto f at_top (𝓝 1) :=
by { rw ←nat.cofinite_eq_at_top, exact hf.tendsto_cofinite_one }

end topological_group

section const_smul
variables [monoid γ] [topological_space α] [add_comm_monoid α] [distrib_mul_action γ α]
  [has_continuous_const_smul γ α] {f : β → α}

lemma has_sum.const_smul {a : α} (b : γ) (hf : has_sum f a) : has_sum (λ i, b • f i) (b • a) :=
hf.map (distrib_mul_action.to_add_monoid_hom α _) $ continuous_const_smul _

lemma summable.const_smul (b : γ) (hf : summable f) : summable (λ i, b • f i) :=
(hf.has_sum.const_smul _).summable

lemma tsum_const_smul [t2_space α] (b : γ) (hf : summable f) : ∑' i, b • f i = b • ∑' i, f i :=
(hf.has_sum.const_smul _).tsum_eq

end const_smul

/-! ### Product and pi types -/

section prod
variables [comm_monoid α] [topological_space α] [comm_monoid γ] [topological_space γ]

@[to_additive has_sum.prod_mk]
lemma has_prod.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ}
  (hf : has_prod f a) (hg : has_prod g b) :
  has_prod (λ x, (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ :=
by simp [has_prod, ← prod_mk_prod, hf.prod_mk_nhds hg]

end prod

section pi
variables {ι : Type*} {π : α → Type*} [∀ x, comm_monoid (π x)] [∀ x, topological_space (π x)]
  {f : ι → ∀ x, π x}

@[to_additive] lemma pi.has_prod {g : ∀ x, π x} : has_prod f g ↔ ∀ x, has_prod (λ i, f i x) (g x) :=
by simp only [has_prod, tendsto_pi_nhds, prod_apply]

@[to_additive] lemma pi.prodable : prodable f ↔ ∀ x, prodable (λ i, f i x) :=
by simp only [prodable, pi.has_prod, skolem]

@[to_additive] lemma tprod_apply [∀ x, t2_space (π x)] {x : α} (hf : prodable f) :
  (∏' i, f i) x = ∏' i, f i x :=
(pi.has_prod.1 hf.has_prod x).tprod_eq.symm

end pi

/-! ### Multiplicative/additive opposite -/

section mul_opposite
open mul_opposite
variables [add_comm_monoid α] [topological_space α] {f : β → α} {a : α}

lemma has_sum.op (hf : has_sum f a) : has_sum (λ a, op (f a)) (op a) :=
(hf.map (@op_add_equiv α _) continuous_op : _)

lemma summable.op (hf : summable f) : summable (op ∘ f) := hf.has_sum.op.summable

lemma has_sum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : has_sum f a) :
  has_sum (λ a, unop (f a)) (unop a) :=
(hf.map (@op_add_equiv α _).symm continuous_unop : _)

lemma summable.unop {f : β → αᵐᵒᵖ} (hf : summable f) : summable (unop ∘ f) :=
hf.has_sum.unop.summable

@[simp] lemma has_sum_op : has_sum (λ a, op (f a)) (op a) ↔ has_sum f a :=
⟨has_sum.unop, has_sum.op⟩

@[simp] lemma has_sum_unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} :
  has_sum (λ a, unop (f a)) (unop a) ↔ has_sum f a :=
⟨has_sum.op, has_sum.unop⟩

@[simp] lemma summable_op : summable (λ a, op (f a)) ↔ summable f := ⟨summable.unop, summable.op⟩

@[simp] lemma summable_unop {f : β → αᵐᵒᵖ} : summable (λ a, unop (f a)) ↔ summable f :=
⟨summable.op, summable.unop⟩

variables [t2_space α]

lemma tsum_op : ∑' x, mul_opposite.op (f x) = mul_opposite.op (∑' x, f x) :=
begin
  by_cases h : summable f,
  { exact h.has_sum.op.tsum_eq },
  { have ho := summable_op.not.mpr h,
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable ho, mul_opposite.op_zero] }
end

lemma tsum_unop {f : β → αᵐᵒᵖ} : ∑' x, mul_opposite.unop (f x) = mul_opposite.unop (∑' x, f x) :=
mul_opposite.op_injective tsum_op.symm

end mul_opposite

section add_opposite
open add_opposite
variables [comm_monoid α] [topological_space α] {f : β → α} {a : α}

lemma has_prod.op (hf : has_prod f a) : has_prod (λ a, op (f a)) (op a) :=
(hf.map (@op_mul_equiv α _) continuous_op : _)

lemma prodable.op (hf : prodable f) : prodable (op ∘ f) := hf.has_prod.op.prodable

lemma has_prod.unop {f : β → αᵃᵒᵖ} {a : αᵃᵒᵖ} (hf : has_prod f a) :
  has_prod (λ a, unop (f a)) (unop a) :=
(hf.map (@op_mul_equiv α _).symm continuous_unop : _)

lemma prodable.unop {f : β → αᵃᵒᵖ} (hf : prodable f) : prodable (unop ∘ f) :=
hf.has_prod.unop.prodable

@[simp] lemma has_prod_op : has_prod (λ a, op (f a)) (op a) ↔ has_prod f a :=
⟨has_prod.unop, has_prod.op⟩

@[simp] lemma has_prod_unop {f : β → αᵃᵒᵖ} {a : αᵃᵒᵖ} :
  has_prod (λ a, unop (f a)) (unop a) ↔ has_prod f a :=
⟨has_prod.op, has_prod.unop⟩

@[simp] lemma prodable_op : prodable (λ a, op (f a)) ↔ prodable f :=
⟨prodable.unop, prodable.op⟩

@[simp] lemma prodable_unop {f : β → αᵃᵒᵖ} : prodable (λ a, unop (f a)) ↔ prodable f :=
⟨prodable.op, prodable.unop⟩

variables [t2_space α]

lemma tprod_op : ∏' x, add_opposite.op (f x) = add_opposite.op (∏' x, f x) :=
begin
  by_cases h : prodable f,
  { exact h.has_prod.op.tprod_eq },
  { have ho := prodable_op.not.mpr h,
    rw [tprod_eq_one_of_not_prodable h, tprod_eq_one_of_not_prodable ho, add_opposite.op_one] }
end

lemma tprod_unop {f : β → αᵃᵒᵖ} : ∏' x, add_opposite.unop (f x) = add_opposite.unop (∏' x, f x) :=
add_opposite.op_injective tprod_op.symm

end add_opposite

/-! ### Interaction with the star -/

section has_continuous_star
variables [add_comm_monoid α] [topological_space α] [star_add_monoid α] [has_continuous_star α]
  {f : β → α} {a : α}

lemma has_sum.star (h : has_sum f a) : has_sum (λ b, star (f b)) (star a) :=
by simpa only using h.map (star_add_equiv : α ≃+ α) continuous_star

lemma summable.star (hf : summable f) : summable (λ b, star (f b)) :=
hf.has_sum.star.summable

lemma summable.of_star (hf : summable (λ b, star (f b))) : summable f :=
by simpa only [star_star] using hf.star

@[simp] lemma summable_star_iff : summable (λ b, star (f b)) ↔ summable f :=
⟨summable.of_star, summable.star⟩

@[simp] lemma summable_star_iff' : summable (star f) ↔ summable f := summable_star_iff

variables [t2_space α]

lemma tsum_star : star (∑' b, f b) = ∑' b, star (f b) :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.star.tsum_eq.symm, },
  { rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt summable.of_star hf),
        star_zero] },
end

end has_continuous_star
