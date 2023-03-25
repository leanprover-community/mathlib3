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
# Infinite sum over a topological monoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

noncomputable theory
open classical filter finset function
open_locale big_operators classical topology

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section has_sum
variables [add_comm_monoid α] [topological_space α]

/-- Infinite sum on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/
def has_sum (f : β → α) (a : α) : Prop := tendsto (λs:finset β, ∑ b in s, f b) at_top (𝓝 a)

/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def summable (f : β → α) : Prop := ∃a, has_sum f a

/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise -/
@[irreducible] def tsum {β} (f : β → α) := if h : summable f then classical.some h else 0

-- see Note [operator precedence of big operators]
notation `∑'` binders `, ` r:(scoped:67 f, tsum f) := r

variables {f g : β → α} {a b : α} {s : finset β}

lemma summable.has_sum (ha : summable f) : has_sum f (∑'b, f b) :=
by simp [ha, tsum]; exact some_spec ha

lemma has_sum.summable (h : has_sum f a) : summable f := ⟨a, h⟩

/-- Constant zero function has sum `0` -/
lemma has_sum_zero : has_sum (λb, 0 : β → α) 0 :=
by simp [has_sum, tendsto_const_nhds]

lemma has_sum_empty [is_empty β] : has_sum f 0 :=
by convert has_sum_zero

lemma summable_zero : summable (λb, 0 : β → α) := has_sum_zero.summable

lemma summable_empty [is_empty β] : summable f := has_sum_empty.summable

lemma tsum_eq_zero_of_not_summable (h : ¬ summable f) : ∑'b, f b = 0 :=
by simp [tsum, h]

lemma summable_congr (hfg : ∀b, f b = g b) :
  summable f ↔ summable g :=
iff_of_eq (congr_arg summable $ funext hfg)

lemma summable.congr (hf : summable f) (hfg : ∀b, f b = g b) :
  summable g :=
(summable_congr hfg).mp hf

lemma has_sum.has_sum_of_sum_eq {g : γ → α}
  (h_eq : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
  (hf : has_sum g a) :
  has_sum f a :=
le_trans (map_at_top_finset_sum_le_of_sum_eq h_eq) hf

lemma has_sum_iff_has_sum {g : γ → α}
  (h₁ : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
  (h₂ : ∀v:finset β, ∃u:finset γ, ∀u', u ⊆ u' → ∃v', v ⊆ v' ∧ ∑ b in v', f b = ∑ x in u', g x) :
  has_sum f a ↔ has_sum g a :=
⟨has_sum.has_sum_of_sum_eq h₂, has_sum.has_sum_of_sum_eq h₁⟩

lemma function.injective.has_sum_iff {g : γ → β} (hg : injective g)
  (hf : ∀ x ∉ set.range g, f x = 0) :
  has_sum (f ∘ g) a ↔ has_sum f a :=
by simp only [has_sum, tendsto, hg.map_at_top_finset_sum_eq hf]

lemma function.injective.summable_iff {g : γ → β} (hg : injective g)
  (hf : ∀ x ∉ set.range g, f x = 0) :
  summable (f ∘ g) ↔ summable f :=
exists_congr $ λ _, hg.has_sum_iff hf

lemma has_sum_subtype_iff_of_support_subset {s : set β} (hf : support f ⊆ s) :
  has_sum (f ∘ coe : s → α) a ↔ has_sum f a :=
subtype.coe_injective.has_sum_iff $ by simpa using support_subset_iff'.1 hf

lemma has_sum_subtype_iff_indicator {s : set β} :
  has_sum (f ∘ coe : s → α) a ↔ has_sum (s.indicator f) a :=
by rw [← set.indicator_range_comp, subtype.range_coe,
  has_sum_subtype_iff_of_support_subset set.support_indicator_subset]

lemma summable_subtype_iff_indicator {s : set β} :
  summable (f ∘ coe : s → α) ↔ summable (s.indicator f) :=
exists_congr (λ _, has_sum_subtype_iff_indicator)

@[simp] lemma has_sum_subtype_support : has_sum (f ∘ coe : support f → α) a ↔ has_sum f a :=
has_sum_subtype_iff_of_support_subset $ set.subset.refl _

lemma has_sum_fintype [fintype β] (f : β → α) : has_sum f (∑ b, f b) :=
order_top.tendsto_at_top_nhds _

protected lemma finset.has_sum (s : finset β) (f : β → α) :
  has_sum (f ∘ coe : (↑s : set β) → α) (∑ b in s, f b) :=
by { rw ← sum_attach, exact has_sum_fintype _ }

protected lemma finset.summable (s : finset β) (f : β → α) :
  summable (f ∘ coe : (↑s : set β) → α) :=
(s.has_sum f).summable

protected lemma set.finite.summable {s : set β} (hs : s.finite) (f : β → α) :
  summable (f ∘ coe : s → α) :=
by convert hs.to_finset.summable f; simp only [hs.coe_to_finset]

/-- If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`. -/
lemma has_sum_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : has_sum f (∑ b in s, f b) :=
(has_sum_subtype_iff_of_support_subset $ support_subset_iff'.2 hf).1 $ s.has_sum f

lemma summable_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : summable f :=
(has_sum_sum_of_ne_finset_zero hf).summable

lemma has_sum_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0) :
  has_sum f (f b) :=
suffices has_sum f (∑ b' in {b}, f b'),
  by simpa using this,
has_sum_sum_of_ne_finset_zero $ by simpa [hf]

lemma has_sum_ite_eq (b : β) [decidable_pred (= b)] (a : α) :
  has_sum (λb', if b' = b then a else 0) a :=
begin
  convert has_sum_single b _,
  { exact (if_pos rfl).symm },
  assume b' hb',
  exact if_neg hb'
end

lemma has_sum_pi_single [decidable_eq β] (b : β) (a : α) :
  has_sum (pi.single b a) a :=
show has_sum (λ x, pi.single b a x) a, by simpa only [pi.single_apply] using has_sum_ite_eq b a

lemma equiv.has_sum_iff (e : γ ≃ β) :
  has_sum (f ∘ e) a ↔ has_sum f a :=
e.injective.has_sum_iff $ by simp

lemma function.injective.has_sum_range_iff {g : γ → β} (hg : injective g) :
  has_sum (λ x : set.range g, f x) a ↔ has_sum (f ∘ g) a :=
(equiv.of_injective g hg).has_sum_iff.symm

lemma equiv.summable_iff (e : γ ≃ β) :
  summable (f ∘ e) ↔ summable f :=
exists_congr $ λ a, e.has_sum_iff

lemma summable.prod_symm {f : β × γ → α} (hf : summable f) : summable (λ p : γ × β, f p.swap) :=
(equiv.prod_comm γ β).summable_iff.2 hf

lemma equiv.has_sum_iff_of_support {g : γ → α} (e : support f ≃ support g)
  (he : ∀ x : support f, g (e x) = f x) :
  has_sum f a ↔ has_sum g a :=
have (g ∘ coe) ∘ e = f ∘ coe, from funext he,
by rw [← has_sum_subtype_support, ← this, e.has_sum_iff, has_sum_subtype_support]

lemma has_sum_iff_has_sum_of_ne_zero_bij {g : γ → α} (i : support g → β)
  (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
  (hf : support f ⊆ set.range i) (hfg : ∀ x, f (i x) = g x) :
  has_sum f a ↔ has_sum g a :=
iff.symm $ equiv.has_sum_iff_of_support
  (equiv.of_bijective (λ x, ⟨i x, λ hx, x.coe_prop $ hfg x ▸ hx⟩)
    ⟨λ x y h, subtype.ext $ hi $ subtype.ext_iff.1 h,
      λ y, (hf y.coe_prop).imp $ λ x hx, subtype.ext hx⟩)
  hfg

lemma equiv.summable_iff_of_support {g : γ → α} (e : support f ≃ support g)
  (he : ∀ x : support f, g (e x) = f x) :
  summable f ↔ summable g :=
exists_congr $ λ _, e.has_sum_iff_of_support he

protected lemma has_sum.map [add_comm_monoid γ] [topological_space γ] (hf : has_sum f a)
  {G} [add_monoid_hom_class G α γ] (g : G) (hg : continuous g) :
  has_sum (g ∘ f) (g a) :=
have g ∘ (λs:finset β, ∑ b in s, f b) = (λs:finset β, ∑ b in s, g (f b)),
  from funext $ map_sum g _,
show tendsto (λs:finset β, ∑ b in s, g (f b)) at_top (𝓝 (g a)),
  from this ▸ (hg.tendsto a).comp hf

protected lemma summable.map [add_comm_monoid γ] [topological_space γ] (hf : summable f)
  {G} [add_monoid_hom_class G α γ] (g : G) (hg : continuous g) :
  summable (g ∘ f) :=
(hf.has_sum.map g hg).summable

protected lemma summable.map_iff_of_left_inverse [add_comm_monoid γ] [topological_space γ]
  {G G'} [add_monoid_hom_class G α γ] [add_monoid_hom_class G' γ α] (g : G) (g' : G')
  (hg : continuous g) (hg' : continuous g') (hinv : function.left_inverse g' g) :
  summable (g ∘ f) ↔ summable f :=
⟨λ h, begin
  have := h.map _ hg',
  rwa [←function.comp.assoc, hinv.id] at this,
end, λ h, h.map _ hg⟩

/-- A special case of `summable.map_iff_of_left_inverse` for convenience -/
protected lemma summable.map_iff_of_equiv [add_comm_monoid γ] [topological_space γ]
  {G} [add_equiv_class G α γ] (g : G)
  (hg : continuous g) (hg' : continuous (add_equiv_class.inv g : γ → α)) :
  summable (g ∘ f) ↔ summable f :=
summable.map_iff_of_left_inverse g (g : α ≃+ γ).symm hg hg' (add_equiv_class.left_inv g)

/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
lemma has_sum.tendsto_sum_nat {f : ℕ → α} (h : has_sum f a) :
  tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
h.comp tendsto_finset_range

lemma has_sum.unique {a₁ a₂ : α} [t2_space α] : has_sum f a₁ → has_sum f a₂ → a₁ = a₂ :=
tendsto_nhds_unique

lemma summable.has_sum_iff_tendsto_nat [t2_space α] {f : ℕ → α} {a : α} (hf : summable f) :
  has_sum f a ↔ tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
begin
  refine ⟨λ h, h.tendsto_sum_nat, λ h, _⟩,
  rw tendsto_nhds_unique h hf.has_sum.tendsto_sum_nat,
  exact hf.has_sum
end

lemma function.surjective.summable_iff_of_has_sum_iff {α' : Type*} [add_comm_monoid α']
  [topological_space α'] {e : α' → α} (hes : function.surjective e) {f : β → α} {g : γ → α'}
  (he : ∀ {a}, has_sum f (e a) ↔ has_sum g a) :
  summable f ↔ summable g :=
hes.exists.trans $ exists_congr $ @he

variable [has_continuous_add α]

lemma has_sum.add (hf : has_sum f a) (hg : has_sum g b) : has_sum (λb, f b + g b) (a + b) :=
by simp only [has_sum, sum_add_distrib]; exact hf.add hg

lemma summable.add (hf : summable f) (hg : summable g) : summable (λb, f b + g b) :=
(hf.has_sum.add hg.has_sum).summable

lemma has_sum_sum {f : γ → β → α} {a : γ → α} {s : finset γ} :
  (∀i∈s, has_sum (f i) (a i)) → has_sum (λb, ∑ i in s, f i b) (∑ i in s, a i) :=
finset.induction_on s (by simp only [has_sum_zero, sum_empty, forall_true_iff])
  (by simp only [has_sum.add, sum_insert, mem_insert, forall_eq_or_imp,
        forall_2_true_iff, not_false_iff, forall_true_iff] {contextual := tt})

lemma summable_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, summable (f i)) :
  summable (λb, ∑ i in s, f i b) :=
(has_sum_sum $ assume i hi, (hf i hi).has_sum).summable

lemma has_sum.add_disjoint {s t : set β} (hs : disjoint s t)
  (ha : has_sum (f ∘ coe : s → α) a) (hb : has_sum (f ∘ coe : t → α) b) :
  has_sum (f ∘ coe : s ∪ t → α) (a + b) :=
begin
  rw has_sum_subtype_iff_indicator at *,
  rw set.indicator_union_of_disjoint hs,
  exact ha.add hb
end

lemma has_sum_sum_disjoint {ι} (s : finset ι) {t : ι → set β} {a : ι → α}
  (hs : (s : set ι).pairwise (disjoint on t))
  (hf : ∀ i ∈ s, has_sum (f ∘ coe : t i → α) (a i)) :
  has_sum (f ∘ coe : (⋃ i ∈ s, t i) → α) (∑ i in s, a i) :=
begin
  simp_rw has_sum_subtype_iff_indicator at *,
  rw set.indicator_finset_bUnion _ _ hs,
  exact has_sum_sum hf,
end

lemma has_sum.add_is_compl {s t : set β} (hs : is_compl s t)
  (ha : has_sum (f ∘ coe : s → α) a) (hb : has_sum (f ∘ coe : t → α) b) :
  has_sum f (a + b) :=
by simpa [← hs.compl_eq]
  using (has_sum_subtype_iff_indicator.1 ha).add (has_sum_subtype_iff_indicator.1 hb)

lemma has_sum.add_compl {s : set β} (ha : has_sum (f ∘ coe : s → α) a)
  (hb : has_sum (f ∘ coe : sᶜ → α) b) :
  has_sum f (a + b) :=
ha.add_is_compl is_compl_compl hb

lemma summable.add_compl {s : set β} (hs : summable (f ∘ coe : s → α))
  (hsc : summable (f ∘ coe : sᶜ → α)) :
  summable f :=
(hs.has_sum.add_compl hsc.has_sum).summable

lemma has_sum.compl_add {s : set β} (ha : has_sum (f ∘ coe : sᶜ → α) a)
  (hb : has_sum (f ∘ coe : s → α) b) :
  has_sum f (a + b) :=
ha.add_is_compl is_compl_compl.symm hb

lemma has_sum.even_add_odd {f : ℕ → α} (he : has_sum (λ k, f (2 * k)) a)
  (ho : has_sum (λ k, f (2 * k + 1)) b) :
  has_sum f (a + b) :=
begin
  have := mul_right_injective₀ (two_ne_zero' ℕ),
  replace he := this.has_sum_range_iff.2 he,
  replace ho := ((add_left_injective 1).comp this).has_sum_range_iff.2 ho,
  refine he.add_is_compl _ ho,
  simpa [(∘)] using nat.is_compl_even_odd
end

lemma summable.compl_add {s : set β} (hs : summable (f ∘ coe : sᶜ → α))
  (hsc : summable (f ∘ coe : s → α)) :
  summable f :=
(hs.has_sum.compl_add hsc.has_sum).summable

lemma summable.even_add_odd {f : ℕ → α} (he : summable (λ k, f (2 * k)))
  (ho : summable (λ k, f (2 * k + 1))) :
  summable f :=
(he.has_sum.even_add_odd ho.has_sum).summable

lemma has_sum.sigma [regular_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α} {a : α}
  (ha : has_sum f a) (hf : ∀b, has_sum (λc, f ⟨b, c⟩) (g b)) : has_sum g a :=
begin
  refine (at_top_basis.tendsto_iff (closed_nhds_basis a)).mpr _,
  rintros s ⟨hs, hsc⟩,
  rcases mem_at_top_sets.mp (ha hs) with ⟨u, hu⟩,
  use [u.image sigma.fst, trivial],
  intros bs hbs,
  simp only [set.mem_preimage, ge_iff_le, finset.le_iff_subset] at hu,
  have : tendsto (λ t : finset (Σ b, γ b), ∑ p in t.filter (λ p, p.1 ∈ bs), f p)
    at_top (𝓝 $ ∑ b in bs, g b),
  { simp only [← sigma_preimage_mk, sum_sigma],
    refine tendsto_finset_sum _ (λ b hb, _),
    change tendsto (λ t, (λ t, ∑ s in t, f ⟨b, s⟩) (preimage t (sigma.mk b) _)) at_top (𝓝 (g b)),
    exact tendsto.comp (hf b) (tendsto_finset_preimage_at_top_at_top _) },
  refine hsc.mem_of_tendsto this (eventually_at_top.2 ⟨u, λ t ht, hu _ (λ x hx, _)⟩),
  exact mem_filter.2 ⟨ht hx, hbs $ mem_image_of_mem _ hx⟩
end

/-- If a series `f` on `β × γ` has sum `a` and for each `b` the restriction of `f` to `{b} × γ`
has sum `g b`, then the series `g` has sum `a`. -/
lemma has_sum.prod_fiberwise [regular_space α] {f : β × γ → α} {g : β → α} {a : α}
  (ha : has_sum f a) (hf : ∀b, has_sum (λc, f (b, c)) (g b)) :
  has_sum g a :=
has_sum.sigma ((equiv.sigma_equiv_prod β γ).has_sum_iff.2 ha) hf

lemma summable.sigma' [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) (hf : ∀b, summable (λc, f ⟨b, c⟩)) :
  summable (λb, ∑'c, f ⟨b, c⟩) :=
(ha.has_sum.sigma (assume b, (hf b).has_sum)).summable

lemma has_sum.sigma_of_has_sum [t3_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α}
  {a : α} (ha : has_sum g a) (hf : ∀b, has_sum (λc, f ⟨b, c⟩) (g b)) (hf' : summable f) :
  has_sum f a :=
by simpa [(hf'.has_sum.sigma hf).unique ha] using hf'.has_sum

/-- Version of `has_sum.update` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that `f.update` has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/
lemma has_sum.update' {α β : Type*} [topological_space α] [add_comm_monoid α] [t2_space α]
  [has_continuous_add α] {f : β → α} {a a' : α} (hf : has_sum f a)
  (b : β) (x : α) (hf' : has_sum (f.update b x) a') : a + x = a' + f b :=
begin
  have : ∀ b', f b' + ite (b' = b) x 0 = f.update b x b' + ite (b' = b) (f b) 0,
  { intro b',
    split_ifs with hb',
    { simpa only [function.update_apply, hb', eq_self_iff_true] using add_comm (f b) x },
    { simp only [function.update_apply, hb', if_false] } },
  have h := hf.add ((has_sum_ite_eq b x)),
  simp_rw this at h,
  exact has_sum.unique h (hf'.add (has_sum_ite_eq b (f b)))
end

/-- Version of `has_sum_ite_sub_has_sum` for `add_comm_monoid` rather than `add_comm_group`.
Rather than showing that the `ite` expression has a specific sum in terms of `has_sum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
lemma eq_add_of_has_sum_ite {α β : Type*} [topological_space α] [add_comm_monoid α]
  [t2_space α] [has_continuous_add α] {f : β → α} {a : α} (hf : has_sum f a) (b : β) (a' : α)
  (hf' : has_sum (λ n, ite (n = b) 0 (f n)) a') : a = a' + f b :=
begin
  refine (add_zero a).symm.trans (hf.update' b 0 _),
  convert hf',
  exact funext (f.update_apply b 0),
end

end has_sum

section tsum
variables [add_comm_monoid α] [topological_space α]

lemma tsum_congr_subtype (f : β → α) {s t : set β} (h : s = t) :
  ∑' (x : s), f x = ∑' (x : t), f x :=
by rw h

lemma tsum_zero' (hz : is_closed ({0} : set α)) : ∑' b : β, (0 : α) = 0 :=
begin
  classical,
  rw [tsum, dif_pos summable_zero],
  suffices : ∀ (x : α), has_sum (λ (b : β), (0 : α)) x → x = 0,
  { exact this _ (classical.some_spec _) },
  intros x hx,
  contrapose! hx,
  simp only [has_sum, tendsto_nhds, finset.sum_const_zero, filter.mem_at_top_sets, ge_iff_le,
              finset.le_eq_subset, set.mem_preimage, not_forall, not_exists, exists_prop,
              exists_and_distrib_right],
  refine ⟨{0}ᶜ, ⟨is_open_compl_iff.mpr hz, _⟩, λ y, ⟨⟨y, subset_refl _⟩, _⟩⟩,
  { simpa using hx },
  { simp }
end

@[simp] lemma tsum_zero [t1_space α] : ∑' b : β, (0 : α) = 0 := tsum_zero' is_closed_singleton

variables [t2_space α] {f g : β → α} {a a₁ a₂ : α}

lemma has_sum.tsum_eq (ha : has_sum f a) : ∑'b, f b = a :=
(summable.has_sum ⟨a, ha⟩).unique ha

lemma summable.has_sum_iff (h : summable f) : has_sum f a ↔ ∑'b, f b = a :=
iff.intro has_sum.tsum_eq (assume eq, eq ▸ h.has_sum)

@[simp] lemma tsum_empty [is_empty β] : ∑'b, f b = 0 := has_sum_empty.tsum_eq

lemma tsum_eq_sum {f : β → α} {s : finset β} (hf : ∀b∉s, f b = 0)  :
  ∑' b, f b = ∑ b in s, f b :=
(has_sum_sum_of_ne_finset_zero hf).tsum_eq

lemma sum_eq_tsum_indicator (f : β → α) (s : finset β) :
  ∑ x in s, f x = ∑' x, set.indicator ↑s f x :=
have ∀ x ∉ s, set.indicator ↑s f x = 0,
from λ x hx, set.indicator_apply_eq_zero.2 (λ hx', (hx $ finset.mem_coe.1 hx').elim),
(finset.sum_congr rfl (λ x hx, (set.indicator_apply_eq_self.2 $
  λ hx', (hx' $ finset.mem_coe.2 hx).elim).symm)).trans (tsum_eq_sum this).symm

lemma tsum_congr {α β : Type*} [add_comm_monoid α] [topological_space α]
  {f g : β → α} (hfg : ∀ b, f b = g b) : ∑' b, f b = ∑' b, g b :=
congr_arg tsum (funext hfg)

lemma tsum_fintype [fintype β] (f : β → α) : ∑'b, f b = ∑ b, f b :=
(has_sum_fintype f).tsum_eq

lemma tsum_bool (f : bool → α) : ∑' i : bool, f i = f false + f true :=
by { rw [tsum_fintype, finset.sum_eq_add]; simp }

lemma tsum_eq_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0)  :
  ∑'b, f b = f b :=
(has_sum_single b hf).tsum_eq

lemma tsum_tsum_eq_single (f : β → γ → α) (b : β) (c : γ) (hfb : ∀ b' ≠ b, f b' c = 0)
  (hfc : ∀ (b' : β) (c' : γ), c' ≠ c → f b' c' = 0) :
  ∑' b' c', f b' c' = f b c :=
calc ∑' b' c', f b' c' = ∑' b', f b' c : tsum_congr $ λ b', tsum_eq_single _ (hfc b')
... = f b c : tsum_eq_single _ hfb

@[simp] lemma tsum_ite_eq (b : β) [decidable_pred (= b)] (a : α) :
  ∑' b', (if b' = b then a else 0) = a :=
(has_sum_ite_eq b a).tsum_eq

@[simp] lemma tsum_pi_single [decidable_eq β] (b : β) (a : α) :
  ∑' b', pi.single b a b' = a :=
(has_sum_pi_single b a).tsum_eq

lemma tsum_dite_right (P : Prop) [decidable P] (x : β → ¬ P → α) :
  ∑' (b : β), (if h : P then (0 : α) else x b h) = if h : P then (0 : α) else ∑' (b : β), x b h :=
by by_cases hP : P; simp [hP]

lemma tsum_dite_left (P : Prop) [decidable P] (x : β → P → α) :
  ∑' (b : β), (if h : P then x b h else 0) = if h : P then (∑' (b : β), x b h) else 0 :=
by by_cases hP : P; simp [hP]

lemma function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum {α' : Type*} [add_comm_monoid α']
  [topological_space α'] {e : α' → α} (hes : function.surjective e) (h0 : e 0 = 0)
  {f : β → α} {g : γ → α'}
  (h : ∀ {a}, has_sum f (e a) ↔ has_sum g a) :
  ∑' b, f b = e (∑' c, g c) :=
by_cases
  (assume : summable g, (h.mpr this.has_sum).tsum_eq)
  (assume hg : ¬ summable g,
    have hf : ¬ summable f, from mt (hes.summable_iff_of_has_sum_iff @h).1 hg,
    by simp [tsum, hf, hg, h0])

lemma tsum_eq_tsum_of_has_sum_iff_has_sum {f : β → α} {g : γ → α}
  (h : ∀{a}, has_sum f a ↔ has_sum g a) :
  ∑'b, f b = ∑'c, g c :=
surjective_id.tsum_eq_tsum_of_has_sum_iff_has_sum rfl @h

lemma equiv.tsum_eq (j : γ ≃ β) (f : β → α) : ∑'c, f (j c) = ∑'b, f b :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ a, j.has_sum_iff

lemma equiv.tsum_eq_tsum_of_support {f : β → α} {g : γ → α} (e : support f ≃ support g)
  (he : ∀ x, g (e x) = f x) :
  (∑' x, f x) = ∑' y, g y :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ _, e.has_sum_iff_of_support he

lemma tsum_eq_tsum_of_ne_zero_bij {g : γ → α} (i : support g → β)
  (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
  (hf : support f ⊆ set.range i) (hfg : ∀ x, f (i x) = g x) :
  ∑' x, f x  = ∑' y, g y :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ _, has_sum_iff_has_sum_of_ne_zero_bij i hi hf hfg

/-! ### `tsum` on subsets -/

@[simp] lemma finset.tsum_subtype (s : finset β) (f : β → α) :
  ∑' x : {x // x ∈ s}, f x = ∑ x in s, f x :=
(s.has_sum f).tsum_eq

@[simp] lemma finset.tsum_subtype' (s : finset β) (f : β → α) :
  ∑' x : (s : set β), f x = ∑ x in s, f x :=
s.tsum_subtype f

lemma tsum_subtype (s : set β) (f : β → α) :
  ∑' x : s, f x = ∑' x, s.indicator f x :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ _, has_sum_subtype_iff_indicator

lemma tsum_subtype_eq_of_support_subset {f : β → α} {s : set β} (hs : support f ⊆ s) :
  ∑' x : s, f x = ∑' x, f x :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ x, has_sum_subtype_iff_of_support_subset hs

@[simp] lemma tsum_univ (f : β → α) : ∑' x : (set.univ : set β), f x = ∑' x, f x :=
tsum_subtype_eq_of_support_subset $ set.subset_univ _

@[simp] lemma tsum_singleton (b : β) (f : β → α) :
  ∑' x : ({b} : set β), f x = f b :=
begin
  rw [tsum_subtype, tsum_eq_single b],
  { simp },
  { intros b' hb',
    rw set.indicator_of_not_mem,
    rwa set.mem_singleton_iff },
  { apply_instance }
end

lemma tsum_image {g : γ → β} (f : β → α) {s : set γ} (hg : set.inj_on g s) :
  ∑' x : g '' s, f x = ∑' x : s, f (g x) :=
((equiv.set.image_of_inj_on _ _ hg).tsum_eq (λ x, f x)).symm

lemma tsum_range {g : γ → β} (f : β → α) (hg : injective g) :
  ∑' x : set.range g, f x = ∑' x, f (g x) :=
by rw [← set.image_univ, tsum_image f (hg.inj_on _), tsum_univ (f ∘ g)]

section has_continuous_add
variable [has_continuous_add α]

lemma tsum_add (hf : summable f) (hg : summable g) : ∑'b, (f b + g b) = (∑'b, f b) + (∑'b, g b) :=
(hf.has_sum.add hg.has_sum).tsum_eq

lemma tsum_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, summable (f i)) :
  ∑'b, ∑ i in s, f i b = ∑ i in s, ∑'b, f i b :=
(has_sum_sum $ assume i hi, (hf i hi).has_sum).tsum_eq

/-- Version of `tsum_eq_add_tsum_ite` for `add_comm_monoid` rather than `add_comm_group`.
Requires a different convergence assumption involving `function.update`. -/
lemma tsum_eq_add_tsum_ite' {f : β → α} (b : β) (hf : summable (f.update b 0)) :
  ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
calc ∑' x, f x = ∑' x, ((ite (x = b) (f x) 0) + (f.update b 0 x)) :
    tsum_congr (λ n, by split_ifs; simp [function.update_apply, h])
  ... = ∑' x, ite (x = b) (f x) 0 + ∑' x, f.update b 0 x :
    tsum_add ⟨ite (b = b) (f b) 0, has_sum_single b (λ b hb, if_neg hb)⟩ (hf)
  ... = (ite (b = b) (f b) 0) + ∑' x, f.update b 0 x :
    by { congr, exact (tsum_eq_single b (λ b' hb', if_neg hb')) }
  ... = f b + ∑' x, ite (x = b) 0 (f x) :
    by simp only [function.update, eq_self_iff_true, if_true, eq_rec_constant, dite_eq_ite]

variables [add_comm_monoid δ] [topological_space δ] [t3_space δ] [has_continuous_add δ]

lemma tsum_sigma' {γ : β → Type*} {f : (Σb:β, γ b) → δ} (h₁ : ∀b, summable (λc, f ⟨b, c⟩))
  (h₂ : summable f) : ∑'p, f p = ∑'b c, f ⟨b, c⟩ :=
(h₂.has_sum.sigma (assume b, (h₁ b).has_sum)).tsum_eq.symm

lemma tsum_prod' {f : β × γ → δ} (h : summable f) (h₁ : ∀b, summable (λc, f (b, c))) :
  ∑'p, f p = ∑'b c, f (b, c) :=
(h.has_sum.prod_fiberwise (assume b, (h₁ b).has_sum)).tsum_eq.symm

lemma tsum_comm' {f : β → γ → δ} (h : summable (function.uncurry f)) (h₁ : ∀b, summable (f b))
  (h₂ : ∀ c, summable (λ b, f b c)) :
  ∑' c b, f b c = ∑' b c, f b c :=
begin
  erw [← tsum_prod' h h₁, ← tsum_prod' h.prod_symm h₂, ← (equiv.prod_comm γ β).tsum_eq (uncurry f)],
  refl
end

end has_continuous_add

open encodable

section encodable
variable [encodable γ]

/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_supr_decode₂ [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0)
  (s : γ → β) : ∑' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b) = ∑' b : γ, m (s b) :=
begin
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 0 → (decode₂ γ n).is_some,
  { intros n h,
    cases decode₂ γ n with b,
    { refine (h $ by simp [m0]).elim },
    { exact rfl } },
  symmetry, refine tsum_eq_tsum_of_ne_zero_bij (λ a, option.get (H a.1 a.2)) _ _ _,
  { rintros ⟨m, hm⟩ ⟨n, hn⟩ e,
    have := mem_decode₂.1 (option.get_mem (H n hn)),
    rwa [← e, mem_decode₂.1 (option.get_mem (H m hm))] at this },
  { intros b h,
    refine ⟨⟨encode b, _⟩, _⟩,
    { simp only [mem_support, encodek₂] at h ⊢, convert h, simp [set.ext_iff, encodek₂] },
    { exact option.get_of_mem _ (encodek₂ _) } },
  { rintros ⟨n, h⟩, dsimp only [subtype.coe_mk],
    transitivity, swap,
    rw [show decode₂ γ n = _, from option.get_mem (H n h)],
    congr, simp [ext_iff, -option.some_get] }
end

/-- `tsum_supr_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_Union_decode₂ (m : set β → α) (m0 : m ∅ = 0)
  (s : γ → set β) : ∑' i, m (⋃ b ∈ decode₂ γ i, s b) = ∑' b, m (s b) :=
tsum_supr_decode₂ m m0 s

end encodable

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/

section countable
variables [countable γ]

/-- If a function is countably sub-additive then it is sub-additive on countable types -/
theorem rel_supr_tsum [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0)
  (R : α → α → Prop) (m_supr : ∀(s : ℕ → β), R (m (⨆ i, s i)) ∑' i, m (s i))
  (s : γ → β) : R (m (⨆ b : γ, s b)) ∑' b : γ, m (s b) :=
by { casesI nonempty_encodable γ, rw [←supr_decode₂, ←tsum_supr_decode₂ _ m0 s], exact m_supr _ }

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_supr_sum [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0)
  (R : α → α → Prop) (m_supr : ∀(s : ℕ → β), R (m (⨆ i, s i)) (∑' i, m (s i)))
  (s : δ → β) (t : finset δ) :
  R (m (⨆ d ∈ t, s d)) (∑ d in t, m (s d)) :=
by { rw [supr_subtype', ←finset.tsum_subtype], exact rel_supr_tsum m m0 R m_supr _ }

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0)
  (R : α → α → Prop) (m_supr : ∀(s : ℕ → β), R (m (⨆ i, s i)) (∑' i, m (s i)))
  (s₁ s₂ : β) : R (m (s₁ ⊔ s₂)) (m s₁ + m s₂) :=
begin
  convert rel_supr_tsum m m0 R m_supr (λ b, cond b s₁ s₂),
  { simp only [supr_bool_eq, cond] },
  { rw [tsum_fintype, fintype.sum_bool, cond, cond] }
end

end countable

variables [has_continuous_add α]

lemma tsum_add_tsum_compl {s : set β} (hs : summable (f ∘ coe : s → α))
  (hsc : summable (f ∘ coe : sᶜ → α)) :
  (∑' x : s, f x) + (∑' x : sᶜ, f x) = ∑' x, f x :=
(hs.has_sum.add_compl hsc.has_sum).tsum_eq.symm

lemma tsum_union_disjoint {s t : set β} (hd : disjoint s t)
  (hs : summable (f ∘ coe : s → α)) (ht : summable (f ∘ coe : t → α)) :
  (∑' x : s ∪ t, f x) = (∑' x : s, f x) + (∑' x : t, f x) :=
(hs.has_sum.add_disjoint hd ht.has_sum).tsum_eq

lemma tsum_finset_bUnion_disjoint {ι} {s : finset ι} {t : ι → set β}
  (hd : (s : set ι).pairwise (disjoint on t))
  (hf : ∀ i ∈ s, summable (f ∘ coe : t i → α)) :
  (∑' x : (⋃ i ∈ s, t i), f x) = ∑ i in s, ∑' x : t i, f x :=
(has_sum_sum_disjoint _ hd (λ i hi, (hf i hi).has_sum)).tsum_eq

lemma tsum_even_add_odd {f : ℕ → α} (he : summable (λ k, f (2 * k)))
  (ho : summable (λ k, f (2 * k + 1))) :
  (∑' k, f (2 * k)) + (∑' k, f (2 * k + 1)) = ∑' k, f k :=
(he.has_sum.even_add_odd ho.has_sum).tsum_eq.symm

end tsum

section topological_group
variables [add_comm_group α] [topological_space α] [topological_add_group α]
variables {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
lemma has_sum.neg (h : has_sum f a) : has_sum (λb, - f b) (- a) :=
by simpa only using h.map (-add_monoid_hom.id α) continuous_neg

lemma summable.neg (hf : summable f) : summable (λb, - f b) :=
hf.has_sum.neg.summable

lemma summable.of_neg (hf : summable (λb, - f b)) : summable f :=
by simpa only [neg_neg] using hf.neg

lemma summable_neg_iff : summable (λ b, - f b) ↔ summable f :=
⟨summable.of_neg, summable.neg⟩

lemma has_sum.sub (hf : has_sum f a₁) (hg : has_sum g a₂) : has_sum (λb, f b - g b) (a₁ - a₂) :=
by { simp only [sub_eq_add_neg], exact hf.add hg.neg }

lemma summable.sub (hf : summable f) (hg : summable g) : summable (λb, f b - g b) :=
(hf.has_sum.sub hg.has_sum).summable

lemma summable.trans_sub (hg : summable g) (hfg : summable (λb, f b - g b)) :
  summable f :=
by simpa only [sub_add_cancel] using hfg.add hg

lemma summable_iff_of_summable_sub (hfg : summable (λb, f b - g b)) :
  summable f ↔ summable g :=
⟨λ hf, hf.trans_sub $ by simpa only [neg_sub] using hfg.neg, λ hg, hg.trans_sub hfg⟩

lemma has_sum.update (hf : has_sum f a₁) (b : β) [decidable_eq β] (a : α) :
  has_sum (update f b a) (a - f b + a₁) :=
begin
  convert ((has_sum_ite_eq b _).add hf),
  ext b',
  by_cases h : b' = b,
  { rw [h, update_same],
    simp only [eq_self_iff_true, if_true, sub_add_cancel] },
  simp only [h, update_noteq, if_false, ne.def, zero_add, not_false_iff],
end

lemma summable.update (hf : summable f) (b : β) [decidable_eq β] (a : α) :
  summable (update f b a) :=
(hf.has_sum.update b a).summable

lemma has_sum.has_sum_compl_iff {s : set β} (hf : has_sum (f ∘ coe : s → α) a₁) :
  has_sum (f ∘ coe : sᶜ → α) a₂ ↔ has_sum f (a₁ + a₂) :=
begin
  refine ⟨λ h, hf.add_compl h, λ h, _⟩,
  rw [has_sum_subtype_iff_indicator] at hf ⊢,
  rw [set.indicator_compl],
  simpa only [add_sub_cancel'] using h.sub hf
end

lemma has_sum.has_sum_iff_compl {s : set β} (hf : has_sum (f ∘ coe : s → α) a₁) :
  has_sum f a₂ ↔ has_sum (f ∘ coe : sᶜ → α) (a₂ - a₁) :=
iff.symm $ hf.has_sum_compl_iff.trans $ by rw [add_sub_cancel'_right]

lemma summable.summable_compl_iff {s : set β} (hf : summable (f ∘ coe : s → α)) :
  summable (f ∘ coe : sᶜ → α) ↔ summable f :=
⟨λ ⟨a, ha⟩, (hf.has_sum.has_sum_compl_iff.1 ha).summable,
  λ ⟨a, ha⟩, (hf.has_sum.has_sum_iff_compl.1 ha).summable⟩

protected lemma finset.has_sum_compl_iff (s : finset β) :
  has_sum (λ x : {x // x ∉ s}, f x) a ↔ has_sum f (a + ∑ i in s, f i) :=
(s.has_sum f).has_sum_compl_iff.trans $ by rw [add_comm]

protected lemma finset.has_sum_iff_compl (s : finset β) :
  has_sum f a ↔ has_sum (λ x : {x // x ∉ s}, f x) (a - ∑ i in s, f i) :=
(s.has_sum f).has_sum_iff_compl

protected lemma finset.summable_compl_iff (s : finset β) :
  summable (λ x : {x // x ∉ s}, f x) ↔ summable f :=
(s.summable f).summable_compl_iff

lemma set.finite.summable_compl_iff {s : set β} (hs : s.finite) :
  summable (f ∘ coe : sᶜ → α) ↔ summable f :=
(hs.summable f).summable_compl_iff

lemma has_sum_ite_sub_has_sum [decidable_eq β] (hf : has_sum f a) (b : β) :
  has_sum (λ n, ite (n = b) 0 (f n)) (a - f b) :=
begin
  convert hf.update b 0 using 1,
  { ext n, rw function.update_apply, },
  { rw [sub_add_eq_add_sub, zero_add], },
end

section tsum
variables [t2_space α]

lemma tsum_neg : ∑'b, - f b = - ∑'b, f b :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.neg.tsum_eq, },
  { simp [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt summable.of_neg hf)] },
end

lemma tsum_sub (hf : summable f) (hg : summable g) : ∑'b, (f b - g b) = ∑'b, f b - ∑'b, g b :=
(hf.has_sum.sub hg.has_sum).tsum_eq

lemma sum_add_tsum_compl {s : finset β} (hf : summable f) :
  (∑ x in s, f x) + (∑' x : (↑s : set β)ᶜ, f x) = ∑' x, f x :=
((s.has_sum f).add_compl (s.summable_compl_iff.2 hf).has_sum).tsum_eq.symm

/-- Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ f n` as the sum of `f b` plus the series of the
remaining terms. -/
lemma tsum_eq_add_tsum_ite [decidable_eq β] (hf : summable f) (b : β) :
  ∑' n, f n = f b + ∑' n, ite (n = b) 0 (f n) :=
begin
  rw (has_sum_ite_sub_has_sum hf.has_sum b).tsum_eq,
  exact (add_sub_cancel'_right _ _).symm,
end

end tsum

/-!
### Sums on nat

We show the formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in
`sum_add_tsum_nat_add`, as well as several results relating sums on `ℕ` and `ℤ`.
-/
section nat

lemma has_sum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
  has_sum (λ n, f (n + k)) a ↔ has_sum f (a + ∑ i in range k, f i) :=
begin
  refine iff.trans _ ((range k).has_sum_compl_iff),
  rw [← (not_mem_range_equiv k).symm.has_sum_iff],
  refl
end

lemma summable_nat_add_iff {f : ℕ → α} (k : ℕ) : summable (λ n, f (n + k)) ↔ summable f :=
iff.symm $ (equiv.add_right (∑ i in range k, f i)).surjective.summable_iff_of_has_sum_iff $
  λ a, (has_sum_nat_add_iff k).symm

lemma has_sum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
  has_sum (λ n, f (n + k)) (a - ∑ i in range k, f i) ↔ has_sum f a :=
by simp [has_sum_nat_add_iff]

lemma sum_add_tsum_nat_add [t2_space α] {f : ℕ → α} (k : ℕ) (h : summable f) :
  (∑ i in range k, f i) + (∑' i, f (i + k)) = ∑' i, f i :=
by simpa only [add_comm] using
  ((has_sum_nat_add_iff k).1 ((summable_nat_add_iff k).2 h).has_sum).unique h.has_sum

lemma tsum_eq_zero_add [t2_space α] {f : ℕ → α} (hf : summable f) :
  ∑'b, f b = f 0 + ∑'b, f (b + 1) :=
by simpa only [sum_range_one] using (sum_add_tsum_nat_add 1 hf).symm

/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
lemma tendsto_sum_nat_add [t2_space α] (f : ℕ → α) : tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0) :=
begin
  by_cases hf : summable f,
  { have h₀ : (λ i, (∑' i, f i) - ∑ j in range i, f j) = λ i, ∑' (k : ℕ), f (k + i),
    { ext1 i,
      rw [sub_eq_iff_eq_add, add_comm, sum_add_tsum_nat_add i hf] },
    have h₁ : tendsto (λ i : ℕ, ∑' i, f i) at_top (𝓝 (∑' i, f i)) := tendsto_const_nhds,
    simpa only [h₀, sub_self] using tendsto.sub h₁ hf.has_sum.tendsto_sum_nat },
  { convert tendsto_const_nhds,
    ext1 i,
    rw ← summable_nat_add_iff i at hf,
    { exact tsum_eq_zero_of_not_summable hf },
    { apply_instance } }
end

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both convergent then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...`. -/
lemma has_sum.int_rec {b : α} {f g : ℕ → α} (hf : has_sum f a) (hg : has_sum g b) :
  @has_sum α _ _ _ (@int.rec (λ _, α) f g : ℤ → α) (a + b) :=
begin
  -- note this proof works for any two-case inductive
  have h₁ : injective (coe : ℕ → ℤ) := @int.of_nat.inj,
  have h₂ : injective int.neg_succ_of_nat := @int.neg_succ_of_nat.inj,
  have : is_compl (set.range (coe : ℕ → ℤ)) (set.range int.neg_succ_of_nat),
  { split,
    { rw disjoint_iff_inf_le,
      rintros _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩ },
    { rw codisjoint_iff_le_sup,
      rintros (i | j) h,
      exacts [or.inl ⟨_, rfl⟩, or.inr ⟨_, rfl⟩] } },
  exact has_sum.add_is_compl this (h₁.has_sum_range_iff.mpr hf) (h₂.has_sum_range_iff.mpr hg),
end

lemma has_sum.nonneg_add_neg {b : α} {f : ℤ → α}
  (hnonneg : has_sum (λ n : ℕ, f n) a) (hneg : has_sum (λ (n : ℕ), f (-n.succ)) b) :
  has_sum f (a + b) :=
begin
  simp_rw ← int.neg_succ_of_nat_coe at hneg,
  convert hnonneg.int_rec hneg using 1,
  ext (i | j); refl,
end

lemma has_sum.pos_add_zero_add_neg {b : α} {f : ℤ → α}
  (hpos : has_sum (λ n:ℕ, f(n + 1)) a) (hneg : has_sum (λ (n : ℕ), f (-n.succ)) b) :
  has_sum f (a + f 0 + b) :=
begin
  have : ∀ g : ℕ → α, has_sum (λ k, g (k + 1)) a → has_sum g (a + g 0),
  { intros g hg, simpa using (has_sum_nat_add_iff _).mp hg },
  exact (this (λ n, f n) hpos).nonneg_add_neg hneg,
end

lemma summable_int_of_summable_nat {f : ℤ → α}
  (hp : summable (λ n:ℕ, f n)) (hn : summable (λ n:ℕ, f (-n))) : summable f :=
(has_sum.nonneg_add_neg hp.has_sum $ summable.has_sum $ (summable_nat_add_iff 1).mpr hn).summable

lemma has_sum.sum_nat_of_sum_int {α : Type*} [add_comm_monoid α] [topological_space α]
  [has_continuous_add α] {a : α} {f : ℤ → α} (hf : has_sum f a) :
  has_sum (λ n:ℕ, f n + f (-n)) (a + f 0) :=
begin
  apply (hf.add (has_sum_ite_eq (0 : ℤ) (f 0))).has_sum_of_sum_eq (λ u, _),
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
  calc ∑ x in u1 ∪ u2, (f x + ite (x = 0) (f 0) 0)
      = ∑ x in u1 ∪ u2, f x + ∑ x in u1 ∩ u2, f x :
    begin
      rw sum_add_distrib,
      congr' 1,
      refine (sum_subset_zero_on_sdiff inter_subset_union _ _).symm,
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
  ... = ∑ x in u1, f x + ∑ x in u2, f x : sum_union_inter
  ... = ∑ b in v', f b + ∑ b in v', f (-b) :
    by simp only [sum_image, nat.cast_inj, imp_self, implies_true_iff, neg_inj]
  ... = ∑ b in v', (f b + f (-b)) : sum_add_distrib.symm
end

end nat

end topological_group

section uniform_group

variables [add_comm_group α] [uniform_space α]

/-- The **Cauchy criterion** for infinite sums, also known as the **Cauchy convergence test** -/
lemma summable_iff_cauchy_seq_finset [complete_space α] {f : β → α} :
  summable f ↔ cauchy_seq (λ (s : finset β), ∑ b in s, f b) :=
cauchy_map_iff_exists_tendsto.symm

variables [uniform_add_group α] {f g : β → α} {a a₁ a₂ : α}

lemma cauchy_seq_finset_iff_vanishing :
  cauchy_seq (λ (s : finset β), ∑ b in s, f b)
  ↔ ∀ e ∈ 𝓝 (0:α), (∃s:finset β, ∀t, disjoint t s → ∑ b in t, f b ∈ e) :=
begin
  simp only [cauchy_seq, cauchy_map_iff, and_iff_right at_top_ne_bot,
    prod_at_top_at_top_eq, uniformity_eq_comap_nhds_zero α, tendsto_comap_iff, (∘)],
  rw [tendsto_at_top'],
  split,
  { assume h e he,
    rcases h e he with ⟨⟨s₁, s₂⟩, h⟩,
    use [s₁ ∪ s₂],
    assume t ht,
    specialize h (s₁ ∪ s₂, (s₁ ∪ s₂) ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩,
    simpa only [finset.sum_union ht.symm, add_sub_cancel'] using h },
  { assume h e he,
    rcases exists_nhds_half_neg he with ⟨d, hd, hde⟩,
    rcases h d hd with ⟨s, h⟩,
    use [(s, s)],
    rintros ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩,
    have : ∑ b in t₂, f b - ∑ b in t₁, f b = ∑ b in t₂ \ s, f b - ∑ b in t₁ \ s, f b,
    { simp only [(finset.sum_sdiff ht₁).symm, (finset.sum_sdiff ht₂).symm,
        add_sub_add_right_eq_sub] },
    simp only [this],
    exact hde _ (h _ finset.sdiff_disjoint) _ (h _ finset.sdiff_disjoint) }
end

local attribute [instance] topological_add_group.t3_space

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
lemma tendsto_tsum_compl_at_top_zero (f : β → α) :
  tendsto (λ (s : finset β), ∑' b : {x // x ∉ s}, f b) at_top (𝓝 0) :=
begin
  by_cases H : summable f,
  { assume e he,
    rcases exists_mem_nhds_is_closed_subset he with ⟨o, ho, o_closed, oe⟩,
    simp only [le_eq_subset, set.mem_preimage, mem_at_top_sets, filter.mem_map, ge_iff_le],
    obtain ⟨s, hs⟩ : ∃ (s : finset β), ∀ (t : finset β), disjoint t s → ∑ (b : β) in t, f b ∈ o :=
      cauchy_seq_finset_iff_vanishing.1 (tendsto.cauchy_seq H.has_sum) o ho,
    refine ⟨s, λ a sa, oe _⟩,
    have A : summable (λ b : {x // x ∉ a}, f b) := a.summable_compl_iff.2 H,
    apply is_closed.mem_of_tendsto o_closed A.has_sum (eventually_of_forall (λ b, _)),
    have : disjoint (finset.image (λ (i : {x // x ∉ a}), (i : β)) b) s,
    { apply disjoint_left.2 (λ i hi his, _),
      rcases mem_image.1 hi with ⟨i', hi', rfl⟩,
      exact i'.2 (sa his), },
    convert hs _ this using 1,
    rw sum_image,
    assume i hi j hj hij,
    exact subtype.ext hij },
  { convert tendsto_const_nhds,
    ext s,
    apply tsum_eq_zero_of_not_summable,
    rwa finset.summable_compl_iff }
end

variable [complete_space α]

lemma summable_iff_vanishing :
  summable f ↔ ∀ e ∈ 𝓝 (0:α), (∃s:finset β, ∀t, disjoint t s → ∑ b in t, f b ∈ e) :=
by rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing]

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a` -/
lemma summable.summable_of_eq_zero_or_self (hf : summable f) (h : ∀b, g b = 0 ∨ g b = f b) :
  summable g :=
summable_iff_vanishing.2 $
  assume e he,
  let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he in
  ⟨s, assume t ht,
    have eq : ∑ b in t.filter (λb, g b = f b), f b = ∑ b in t, g b :=
      calc ∑ b in t.filter (λb, g b = f b), f b = ∑ b in t.filter (λb, g b = f b), g b :
          finset.sum_congr rfl (assume b hb, (finset.mem_filter.1 hb).2.symm)
        ... = ∑ b in t, g b :
        begin
          refine finset.sum_subset (finset.filter_subset _ _) _,
          assume b hbt hb,
          simp only [(∉), finset.mem_filter, and_iff_right hbt] at hb,
          exact (h b).resolve_right hb
        end,
    eq ▸ hs _ $ finset.disjoint_of_subset_left (finset.filter_subset _ _) ht⟩

protected lemma summable.indicator (hf : summable f) (s : set β) :
  summable (s.indicator f) :=
hf.summable_of_eq_zero_or_self $ set.indicator_eq_zero_or_self _ _

lemma summable.comp_injective {i : γ → β} (hf : summable f) (hi : injective i) :
  summable (f ∘ i) :=
begin
  simpa only [set.indicator_range_comp]
    using (hi.summable_iff _).2 (hf.indicator (set.range i)),
  exact λ x hx, set.indicator_of_not_mem hx _
end

lemma summable.subtype (hf : summable f) (s : set β) : summable (f ∘ coe : s → α) :=
hf.comp_injective subtype.coe_injective

lemma summable_subtype_and_compl {s : set β} :
  summable (λ x : s, f x) ∧ summable (λ x : sᶜ, f x) ↔ summable f :=
⟨and_imp.2 summable.add_compl, λ h, ⟨h.subtype s, h.subtype sᶜ⟩⟩

lemma summable.sigma_factor {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) (b : β) : summable (λc, f ⟨b, c⟩) :=
ha.comp_injective sigma_mk_injective

lemma summable.sigma {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) : summable (λb, ∑'c, f ⟨b, c⟩) :=
ha.sigma' (λ b, ha.sigma_factor b)

lemma summable.prod_factor {f : β × γ → α} (h : summable f) (b : β) :
  summable (λ c, f (b, c)) :=
h.comp_injective $ λ c₁ c₂ h, (prod.ext_iff.1 h).2

lemma tsum_sigma [t1_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) : ∑'p, f p = ∑'b c, f ⟨b, c⟩ :=
tsum_sigma' (λ b, ha.sigma_factor b) ha

lemma tsum_prod [t1_space α] {f : β × γ → α} (h : summable f) :
  ∑'p, f p = ∑'b c, f ⟨b, c⟩ :=
tsum_prod' h h.prod_factor

lemma tsum_comm [t1_space α] {f : β → γ → α} (h : summable (function.uncurry f)) :
  ∑' c b, f b c = ∑' b c, f b c :=
tsum_comm' h h.prod_factor h.prod_symm.prod_factor

lemma tsum_subtype_add_tsum_subtype_compl [t2_space α] {f : β → α} (hf : summable f) (s : set β) :
  ∑' x : s, f x + ∑' x : sᶜ, f x = ∑' x, f x :=
((hf.subtype s).has_sum.add_compl (hf.subtype {x | x ∉ s}).has_sum).unique hf.has_sum

lemma sum_add_tsum_subtype_compl [t2_space α] {f : β → α} (hf : summable f) (s : finset β) :
  ∑ x in s, f x + ∑' x : {x // x ∉ s}, f x = ∑' x, f x :=
begin
  rw ← tsum_subtype_add_tsum_subtype_compl hf s,
  simp only [finset.tsum_subtype', add_right_inj],
  refl,
end

end uniform_group

section topological_group

variables {G : Type*} [topological_space G] [add_comm_group G] [topological_add_group G]
  {f : α → G}

lemma summable.vanishing (hf : summable f) ⦃e : set G⦄ (he : e ∈ 𝓝 (0 : G)) :
  ∃ s : finset α, ∀ t, disjoint t s → ∑ k in t, f k ∈ e :=
begin
  letI : uniform_space G := topological_add_group.to_uniform_space G,
  letI : uniform_add_group G := topological_add_comm_group_is_uniform,
  rcases hf with ⟨y, hy⟩,
  exact cauchy_seq_finset_iff_vanishing.1 hy.cauchy_seq e he
end

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
lemma summable.tendsto_cofinite_zero (hf : summable f) : tendsto f cofinite (𝓝 0) :=
begin
  intros e he,
  rw [filter.mem_map],
  rcases hf.vanishing he with ⟨s, hs⟩,
  refine s.eventually_cofinite_nmem.mono (λ x hx, _),
  by simpa using hs {x} (disjoint_singleton_left.2 hx)
end

lemma summable.tendsto_at_top_zero {f : ℕ → G} (hf : summable f) : tendsto f at_top (𝓝 0) :=
by { rw ←nat.cofinite_eq_at_top, exact hf.tendsto_cofinite_zero }

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
variables [add_comm_monoid α] [topological_space α] [add_comm_monoid γ] [topological_space γ]

lemma has_sum.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ}
  (hf : has_sum f a) (hg : has_sum g b) :
  has_sum (λ x, (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ :=
by simp [has_sum, ← prod_mk_sum, filter.tendsto.prod_mk_nhds hf hg]

end prod

section pi
variables {ι : Type*} {π : α → Type*} [∀ x, add_comm_monoid (π x)] [∀ x, topological_space (π x)]

lemma pi.has_sum {f : ι → ∀ x, π x} {g : ∀ x, π x} :
  has_sum f g ↔ ∀ x, has_sum (λ i, f i x) (g x) :=
by simp only [has_sum, tendsto_pi_nhds, sum_apply]

lemma pi.summable {f : ι → ∀ x, π x} : summable f ↔ ∀ x, summable (λ i, f i x) :=
by simp only [summable, pi.has_sum, skolem]

lemma tsum_apply [∀ x, t2_space (π x)] {f : ι → ∀ x, π x}{x : α} (hf : summable f) :
  (∑' i, f i) x = ∑' i, f i x :=
(pi.has_sum.mp hf.has_sum x).tsum_eq.symm

end pi

/-! ### Multiplicative opposite -/

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
