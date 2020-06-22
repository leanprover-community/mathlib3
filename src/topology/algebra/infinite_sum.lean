/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

Reference:
* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/
import topology.instances.real

noncomputable theory
open finset filter function classical
open_locale topological_space classical big_operators

variables {α : Type*} {β : Type*} {γ : Type*}

section has_sum
variables [add_comm_monoid α] [topological_space α]

/-- Infinite sum on a topological monoid
The `at_top` filter on `finset α` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is still invariant under reordering, and a absolute
sum operator.

This is based on Mario Carneiro's infinite sum in Metamath.

For the definition or many statements, α does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/
def has_sum (f : β → α) (a : α) : Prop := tendsto (λs:finset β, ∑ b in s, f b) at_top (𝓝 a)

/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def summable (f : β → α) : Prop := ∃a, has_sum f a

/-- `tsum f` is the sum of `f` it exists, or 0 otherwise -/
def tsum (f : β → α) := if h : summable f then classical.some h else 0

notation `∑'` binders `, ` r:(scoped f, tsum f) := r

variables {f g : β → α} {a b : α} {s : finset β}

lemma summable.has_sum (ha : summable f) : has_sum f (∑'b, f b) :=
by simp [ha, tsum]; exact some_spec ha

lemma has_sum.summable (h : has_sum f a) : summable f := ⟨a, h⟩

/-- Constant zero function has sum `0` -/
lemma has_sum_zero : has_sum (λb, 0 : β → α) 0 :=
by simp [has_sum, tendsto_const_nhds]

lemma summable_zero : summable (λb, 0 : β → α) := has_sum_zero.summable

lemma tsum_eq_zero_of_not_summable (h : ¬ summable f) : (∑'b, f b) = 0 :=
by simp [tsum, h]

/-- If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`. -/
lemma has_sum_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : has_sum f (∑ b in s, f b) :=
tendsto_infi' s $ tendsto.congr'
  (assume t (ht : s ⊆ t), show ∑ b in s, f b = ∑ b in t, f b, from sum_subset ht $ assume x _, hf _)
  tendsto_const_nhds

lemma has_sum_fintype [fintype β] (f : β → α) : has_sum f (∑ b, f b) :=
has_sum_sum_of_ne_finset_zero $ λ a h, h.elim (mem_univ _)

lemma summable_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : summable f :=
(has_sum_sum_of_ne_finset_zero hf).summable

lemma has_sum_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0) :
  has_sum f (f b) :=
suffices has_sum f (∑ b' in {b}, f b'),
  by simpa using this,
has_sum_sum_of_ne_finset_zero $ by simpa [hf]

lemma has_sum_ite_eq (b : β) (a : α) : has_sum (λb', if b' = b then a else 0) a :=
begin
  convert has_sum_single b _,
  { exact (if_pos rfl).symm },
  assume b' hb',
  exact if_neg hb'
end

lemma has_sum_of_iso {j : γ → β} {i : β → γ}
  (hf : has_sum f a) (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) : has_sum (f ∘ j) a :=
have ∀x y, j x = j y → x = y,
  from assume x y h,
  have i (j x) = i (j y), by rw [h],
  by rwa [h₁, h₁] at this,
have (λs:finset γ, ∑ x in s, f (j x)) = (λs:finset β, ∑ b in s, f b) ∘ (λs:finset γ, s.image j),
  from funext $ assume s, (sum_image $ assume x _ y _, this x y).symm,
show tendsto (λs:finset γ, ∑ x in s, f (j x)) at_top (𝓝 a),
   by rw [this]; apply hf.comp (tendsto_finset_image_at_top_at_top h₂)

lemma has_sum_iff_has_sum_of_iso {j : γ → β} (i : β → γ)
  (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) :
  has_sum (f ∘ j) a ↔ has_sum f a :=
iff.intro
  (assume hfj,
    have has_sum ((f ∘ j) ∘ i) a, from has_sum_of_iso hfj h₂ h₁,
    by simp [(∘), h₂] at this; assumption)
  (assume hf, has_sum_of_iso hf h₁ h₂)

lemma equiv.has_sum_iff (e : γ ≃ β) :
  has_sum (f ∘ e) a ↔ has_sum f a :=
has_sum_iff_has_sum_of_iso e.symm e.left_inv e.right_inv

lemma equiv.summable_iff (e : γ ≃ β) :
  summable (f ∘ e) ↔ summable f :=
⟨λ H, (e.has_sum_iff.1 H.has_sum).summable, λ H, (e.has_sum_iff.2 H.has_sum).summable⟩

lemma has_sum_hom (g : α → γ) [add_comm_monoid γ] [topological_space γ]
  [is_add_monoid_hom g] (h₃ : continuous g) (hf : has_sum f a) :
  has_sum (g ∘ f) (g a) :=
have (λs:finset β, ∑ b in s, g (f b)) = g ∘ (λs:finset β, ∑ b in s, f b),
  from funext $ assume s, s.sum_hom g,
show tendsto (λs:finset β, ∑ b in s, g (f b)) at_top (𝓝 (g a)),
  by rw [this]; exact tendsto.comp (continuous_iff_continuous_at.mp h₃ a) hf

/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
lemma has_sum.tendsto_sum_nat {f : ℕ → α} (h : has_sum f a) :
  tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
@tendsto.comp _ _ _ finset.range (λ s : finset ℕ, ∑ n in s, f n) _ _ _ h tendsto_finset_range

lemma has_sum_unique {a₁ a₂ : α} [t2_space α] : has_sum f a₁ → has_sum f a₂ → a₁ = a₂ :=
tendsto_nhds_unique at_top_ne_bot

lemma has_sum_iff_tendsto_nat_of_summable [t2_space α] {f : ℕ → α} {a : α} (hf : summable f) :
  has_sum f a ↔ tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
begin
  refine ⟨λ h, h.tendsto_sum_nat, λ h, _⟩,
  rw tendsto_nhds_unique at_top_ne_bot h hf.has_sum.tendsto_sum_nat,
  exact hf.has_sum
end

variable [topological_add_monoid α]

lemma has_sum.add (hf : has_sum f a) (hg : has_sum g b) : has_sum (λb, f b + g b) (a + b) :=
by simp [has_sum, sum_add_distrib]; exact hf.add hg

lemma summable.add (hf : summable f) (hg : summable g) : summable (λb, f b + g b) :=
(hf.has_sum.add hg.has_sum).summable

lemma has_sum_sum {f : γ → β → α} {a : γ → α} {s : finset γ} :
  (∀i∈s, has_sum (f i) (a i)) → has_sum (λb, ∑ i in s, f i b) (∑ i in s, a i) :=
finset.induction_on s (by simp [has_sum_zero]) (by simp [has_sum.add] {contextual := tt})

lemma summable_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, summable (f i)) :
  summable (λb, ∑ i in s, f i b) :=
(has_sum_sum $ assume i hi, (hf i hi).has_sum).summable

lemma has_sum.sigma [regular_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α} {a : α}
  (ha : has_sum f a) (hf : ∀b, has_sum (λc, f ⟨b, c⟩) (g b)) : has_sum g a :=
assume s' hs',
let
  ⟨s, hs, hss', hsc⟩ := nhds_is_closed hs',
  ⟨u, hu⟩ := mem_at_top_sets.mp $ ha hs,
  fsts := u.image sigma.fst,
  snds := λb, u.bind (λp, (if h : p.1 = b then {cast (congr_arg γ h) p.2} else ∅ : finset (γ b)))
in
have u_subset : u ⊆ fsts.sigma snds,
  from subset_iff.mpr $ assume ⟨b, c⟩ hu,
  have hb : b ∈ fsts, from finset.mem_image.mpr ⟨_, hu, rfl⟩,
  have hc : c ∈ snds b, from mem_bind.mpr ⟨_, hu, by simp; refl⟩,
  by simp [mem_sigma, hb, hc] ,
mem_at_top_sets.mpr $ exists.intro fsts $ assume bs (hbs : fsts ⊆ bs),
  have h : ∀cs : Π b ∈ bs, finset (γ b),
      ((⋂b (hb : b ∈ bs), (λp:Πb, finset (γ b), p b) ⁻¹' {cs' | cs b hb ⊆ cs' }) ∩
      (λp, ∑ b in bs, ∑ c in p b, f ⟨b, c⟩) ⁻¹' s).nonempty,
    from assume cs,
    let cs' := λb, (if h : b ∈ bs then cs b h else ∅) ∪ snds b in
    have sum_eq : ∑ b in bs, ∑ c in cs' b, f ⟨b, c⟩ = ∑ x in bs.sigma cs', f x,
      from sum_sigma.symm,
    have ∑ x in bs.sigma cs', f x ∈ s,
      from hu _ $ finset.subset.trans u_subset $ sigma_mono hbs $
        assume b, @finset.subset_union_right (γ b) _ _ _,
    exists.intro cs' $
    by simp [sum_eq, this]; { intros b hb, simp [cs', hb, finset.subset_union_left] },
  have tendsto (λp:(Πb:β, finset (γ b)), ∑ b in bs, ∑ c in p b, f ⟨b, c⟩)
      (⨅b (h : b ∈ bs), at_top.comap (λp, p b)) (𝓝 (∑ b in bs, g b)),
    from tendsto_finset_sum bs $
      assume c hc, tendsto_infi' c $ tendsto_infi' hc $ by apply tendsto.comp (hf c) tendsto_comap,
  have ∑ b in bs, g b ∈ s,
    from mem_of_closed_of_tendsto' this hsc $ forall_sets_nonempty_iff_ne_bot.mp $
      begin
        simp only [mem_inf_sets, exists_imp_distrib, forall_and_distrib, and_imp,
               filter.mem_infi_sets_finset, mem_comap_sets, mem_at_top_sets, and_comm,
               mem_principal_sets, set.preimage_subset_iff, exists_prop, skolem],
        intros s₁ s₂ s₃ hs₁ hs₃ p hs₂ p' hp cs hp',
        have : (⋂b (h : b ∈ bs), (λp:(Πb, finset (γ b)), p b) ⁻¹' {cs' | cs b h ⊆ cs' }) ≤ (⨅b∈bs, p b),
          from (infi_le_infi $ assume b, infi_le_infi $ assume hb,
            le_trans (set.preimage_mono $ hp' b hb) (hp b hb)),
        exact (h _).mono (set.subset.trans (set.inter_subset_inter (le_trans this hs₂) hs₃) hs₁)
      end,
  hss' this

lemma summable.sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) (hf : ∀b, summable (λc, f ⟨b, c⟩)) : summable (λb, ∑'c, f ⟨b, c⟩) :=
(ha.has_sum.sigma (assume b, (hf b).has_sum)).summable

lemma has_sum.sigma_of_has_sum [regular_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α} {a : α}
  (ha : has_sum g a) (hf : ∀b, has_sum (λc, f ⟨b, c⟩) (g b))  (hf' : summable f) : has_sum f a :=
by simpa [has_sum_unique (hf'.has_sum.sigma hf) ha] using hf'.has_sum

end has_sum

section has_sum_iff_has_sum_of_iso_ne_zero
variables [add_comm_monoid α] [topological_space α]
variables {f : β → α} {g : γ → α} {a : α}

lemma has_sum.has_sum_of_sum_eq
  (h_eq : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
  (hf : has_sum g a) : has_sum f a :=
suffices at_top.map (λs:finset β, ∑ b in s, f b) ≤ at_top.map (λs:finset γ, ∑ x in s, g x),
  from le_trans this hf,
by rw [map_at_top_eq, map_at_top_eq];
from (le_infi $ assume b, let ⟨v, hv⟩ := h_eq b in infi_le_of_le v $
  by simp [set.image_subset_iff]; exact hv)

lemma has_sum_iff_has_sum
  (h₁ : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
  (h₂ : ∀v:finset β, ∃u:finset γ, ∀u', u ⊆ u' → ∃v', v ⊆ v' ∧ ∑ b in v', f b = ∑ x in u', g x) :
  has_sum f a ↔ has_sum g a :=
⟨has_sum.has_sum_of_sum_eq h₂, has_sum.has_sum_of_sum_eq h₁⟩

variables
  (i : Π⦃c⦄, g c ≠ 0 → β) (hi : ∀⦃c⦄ (h : g c ≠ 0), f (i h) ≠ 0)
  (j : Π⦃b⦄, f b ≠ 0 → γ) (hj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) ≠ 0)
  (hji : ∀⦃c⦄ (h : g c ≠ 0), j (hi h) = c)
  (hij : ∀⦃b⦄ (h : f b ≠ 0), i (hj h) = b)
  (hgj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) = f b)
include hi hj hji hij hgj

-- FIXME this causes a deterministic timeout with `-T50000`
lemma has_sum.has_sum_ne_zero : has_sum g a → has_sum f a :=
have j_inj : ∀x y (hx : f x ≠ 0) (hy : f y ≠ 0), (j hx = j hy ↔ x = y),
  from assume x y hx hy,
  ⟨assume h,
    have i (hj hx) = i (hj hy), by simp [h],
    by rwa [hij, hij] at this; assumption,
  by simp {contextual := tt}⟩,
let ii : finset γ → finset β := λu, u.bind $ λc, if h : g c = 0 then ∅ else {i h} in
let jj : finset β → finset γ := λv, v.bind $ λb, if h : f b = 0 then ∅ else {j h} in
has_sum.has_sum_of_sum_eq $ assume u, exists.intro (ii u) $
  assume v hv, exists.intro (u ∪ jj v) $ and.intro (subset_union_left _ _) $
  have ∀c:γ, c ∈ u ∪ jj v → c ∉ jj v → g c = 0,
    from assume c hc hnc, classical.by_contradiction $ assume h : g c ≠ 0,
    have c ∈ u,
      from (finset.mem_union.1 hc).resolve_right hnc,
    have i h ∈ v,
      from hv $ by simp [mem_bind]; existsi c; simp [h, this],
    have j (hi h) ∈ jj v,
      by simp [mem_bind]; existsi i h; simp [h, hi, this],
    by rw [hji h] at this; exact hnc this,
  calc ∑ x in u ∪ jj v, g x = ∑ x in jj v, g x : (sum_subset (subset_union_right _ _) this).symm
    ... = ∑ x in v, _ : sum_bind $ by intros x _ y _ _; by_cases f x = 0; by_cases f y = 0; simp [*]; cc
    ... = ∑ x in v, f x : sum_congr rfl $ by intros x hx; by_cases f x = 0; simp [*]

lemma has_sum_iff_has_sum_of_ne_zero : has_sum f a ↔ has_sum g a :=
iff.intro
  (has_sum.has_sum_ne_zero j hj i hi hij hji $ assume b hb, by rw [←hgj (hi _), hji])
  (has_sum.has_sum_ne_zero i hi j hj hji hij hgj)

lemma summable_iff_summable_ne_zero : summable g ↔ summable f :=
exists_congr $
  assume a, has_sum_iff_has_sum_of_ne_zero j hj i hi hij hji $
    assume b hb, by rw [←hgj (hi _), hji]

end has_sum_iff_has_sum_of_iso_ne_zero

section has_sum_iff_has_sum_of_bij_ne_zero
variables [add_comm_monoid α] [topological_space α]
variables {f : β → α} {g : γ → α} {a : α}
  (i : Π⦃c⦄, g c ≠ 0 → β)
  (h₁ : ∀⦃c₁ c₂⦄ (h₁ : g c₁ ≠ 0) (h₂ : g c₂ ≠ 0), i h₁ = i h₂ → c₁ = c₂)
  (h₂ : ∀⦃b⦄, f b ≠ 0 → ∃c (h : g c ≠ 0), i h = b)
  (h₃ : ∀⦃c⦄ (h : g c ≠ 0), f (i h) = g c)
include i h₁ h₂ h₃

lemma has_sum_iff_has_sum_of_ne_zero_bij : has_sum f a ↔ has_sum g a :=
have hi : ∀⦃c⦄ (h : g c ≠ 0), f (i h) ≠ 0,
  from assume c h, by simp [h₃, h],
let j : Π⦃b⦄, f b ≠ 0 → γ := λb h, some $ h₂ h in
have hj : ∀⦃b⦄ (h : f b ≠ 0), ∃(h : g (j h) ≠ 0), i h = b,
  from assume b h, some_spec $ h₂ h,
have hj₁ : ∀⦃b⦄ (h : f b ≠ 0), g (j h) ≠ 0,
  from assume b h, let ⟨h₁, _⟩ := hj h in h₁,
have hj₂ : ∀⦃b⦄ (h : f b ≠ 0), i (hj₁ h) = b,
  from assume b h, let ⟨h₁, h₂⟩ := hj h in h₂,
has_sum_iff_has_sum_of_ne_zero i hi j hj₁
  (assume c h, h₁ (hj₁ _) h $ hj₂ _) hj₂ (assume b h, by rw [←h₃ (hj₁ _), hj₂])

lemma summable_iff_summable_ne_zero_bij : summable f ↔ summable g :=
exists_congr $
  assume a, has_sum_iff_has_sum_of_ne_zero_bij @i h₁ h₂ h₃

end has_sum_iff_has_sum_of_bij_ne_zero

section subtype
variables [add_comm_monoid α] [topological_space α] {s : finset β} {f : β → α} {a : α}

lemma has_sum_subtype_iff_of_eq_zero (h : ∀ x ∈ s, f x = 0) :
  has_sum (λ b : {b // b ∉ s}, f b) a ↔ has_sum f a :=
begin
  symmetry,
  apply has_sum_iff_has_sum_of_ne_zero_bij (λ (b : {b // b ∉ s}) hb, (b : β)),
  { exact λ c₁ c₂ h₁ h₂ H, subtype.eq H },
  { assume b hb,
    have : b ∉ s := λ H, hb (h b H),
    exact ⟨⟨b, this⟩, hb, rfl⟩ },
  { dsimp, simp }
end
end subtype

section tsum
variables [add_comm_monoid α] [topological_space α] [t2_space α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma tsum_eq_has_sum (ha : has_sum f a) : (∑'b, f b) = a :=
has_sum_unique (summable.has_sum ⟨a, ha⟩) ha

lemma summable.has_sum_iff (h : summable f) : has_sum f a ↔ (∑'b, f b) = a :=
iff.intro tsum_eq_has_sum (assume eq, eq ▸ h.has_sum)

@[simp] lemma tsum_zero : (∑'b:β, 0:α) = 0 := tsum_eq_has_sum has_sum_zero

lemma tsum_eq_sum {f : β → α} {s : finset β} (hf : ∀b∉s, f b = 0)  :
  (∑'b, f b) = ∑ b in s, f b :=
tsum_eq_has_sum $ has_sum_sum_of_ne_finset_zero hf

lemma tsum_fintype [fintype β] (f : β → α) : (∑'b, f b) = ∑ b, f b :=
tsum_eq_has_sum $ has_sum_fintype f

lemma tsum_eq_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0)  :
  (∑'b, f b) = f b :=
tsum_eq_has_sum $ has_sum_single b hf

@[simp] lemma tsum_ite_eq (b : β) (a : α) : (∑'b', if b' = b then a else 0) = a :=
tsum_eq_has_sum (has_sum_ite_eq b a)

lemma tsum_eq_tsum_of_has_sum_iff_has_sum {f : β → α} {g : γ → α}
  (h : ∀{a}, has_sum f a ↔ has_sum g a) : (∑'b, f b) = (∑'c, g c) :=
by_cases
  (assume : ∃a, has_sum f a,
    let ⟨a, hfa⟩ := this in
    have hga : has_sum g a, from h.mp hfa,
    by rw [tsum_eq_has_sum hfa, tsum_eq_has_sum hga])
  (assume hf : ¬ summable f,
    have hg : ¬ summable g, from assume ⟨a, hga⟩, hf ⟨a, h.mpr hga⟩,
    by simp [tsum, hf, hg])

lemma tsum_eq_tsum_of_ne_zero {f : β → α} {g : γ → α}
  (i : Π⦃c⦄, g c ≠ 0 → β) (hi : ∀⦃c⦄ (h : g c ≠ 0), f (i h) ≠ 0)
  (j : Π⦃b⦄, f b ≠ 0 → γ) (hj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) ≠ 0)
  (hji : ∀⦃c⦄ (h : g c ≠ 0), j (hi h) = c)
  (hij : ∀⦃b⦄ (h : f b ≠ 0), i (hj h) = b)
  (hgj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) = f b) :
  (∑'i, f i) = (∑'j, g j) :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ assume a, has_sum_iff_has_sum_of_ne_zero i hi j hj hji hij hgj

lemma tsum_eq_tsum_of_ne_zero_bij {f : β → α} {g : γ → α}
  (i : Π⦃c⦄, g c ≠ 0 → β)
  (h₁ : ∀⦃c₁ c₂⦄ (h₁ : g c₁ ≠ 0) (h₂ : g c₂ ≠ 0), i h₁ = i h₂ → c₁ = c₂)
  (h₂ : ∀⦃b⦄, f b ≠ 0 → ∃c (h : g c ≠ 0), i h = b)
  (h₃ : ∀⦃c⦄ (h : g c ≠ 0), f (i h) = g c) :
  (∑'i, f i) = (∑'j, g j) :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ assume a, has_sum_iff_has_sum_of_ne_zero_bij i h₁ h₂ h₃

lemma tsum_eq_tsum_of_iso (j : γ → β) (i : β → γ)
  (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) :
  (∑'c, f (j c)) = (∑'b, f b) :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ assume a, has_sum_iff_has_sum_of_iso i h₁ h₂

lemma tsum_equiv (j : γ ≃ β) : (∑'c, f (j c)) = (∑'b, f b) :=
tsum_eq_tsum_of_iso j j.symm (by simp) (by simp)

variable [topological_add_monoid α]

lemma tsum_add (hf : summable f) (hg : summable g) : (∑'b, f b + g b) = (∑'b, f b) + (∑'b, g b) :=
tsum_eq_has_sum $ hf.has_sum.add hg.has_sum

lemma tsum_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, summable (f i)) :
  (∑'b, ∑ i in s, f i b) = ∑ i in s, ∑'b, f i b :=
tsum_eq_has_sum $ has_sum_sum $ assume i hi, (hf i hi).has_sum

lemma tsum_sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (h₁ : ∀b, summable (λc, f ⟨b, c⟩)) (h₂ : summable f) : (∑'p, f p) = (∑'b c, f ⟨b, c⟩) :=
(tsum_eq_has_sum $ h₂.has_sum.sigma (assume b, (h₁ b).has_sum)).symm

end tsum

section topological_group
variables [add_comm_group α] [topological_space α] [topological_add_group α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum.neg : has_sum f a → has_sum (λb, - f b) (- a) :=
has_sum_hom has_neg.neg continuous_neg

lemma summable.neg (hf : summable f) : summable (λb, - f b) :=
hf.has_sum.neg.summable

lemma has_sum.sub (hf : has_sum f a₁) (hg : has_sum g a₂) : has_sum (λb, f b - g b) (a₁ - a₂) :=
by { simp [sub_eq_add_neg], exact hf.add hg.neg }

lemma summable.sub (hf : summable f) (hg : summable g) : summable (λb, f b - g b) :=
(hf.has_sum.sub hg.has_sum).summable

section tsum
variables [t2_space α]

lemma tsum_neg (hf : summable f) : (∑'b, - f b) = - (∑'b, f b) :=
tsum_eq_has_sum $ hf.has_sum.neg

lemma tsum_sub (hf : summable f) (hg : summable g) : (∑'b, f b - g b) = (∑'b, f b) - (∑'b, g b) :=
tsum_eq_has_sum $ hf.has_sum.sub hg.has_sum

lemma tsum_eq_zero_add {f : ℕ → α} (hf : summable f) : (∑'b, f b) = f 0 + (∑'b, f (b + 1)) :=
begin
  let f₁ : ℕ → α := λ n, nat.rec (f 0) (λ _ _, 0) n,
  let f₂ : ℕ → α := λ n, nat.rec 0 (λ k _, f (k+1)) n,
  have : f = λ n, f₁ n + f₂ n, { ext n, symmetry, cases n, apply add_zero, apply zero_add },
  have hf₁ : summable f₁,
  { fapply summable_sum_of_ne_finset_zero,
    { exact {0} },
    { rintros (_ | n) hn,
      { exfalso,
        apply hn,
        apply finset.mem_singleton_self },
      { refl } } },
  have hf₂ : summable f₂,
  { have : f₂ = λ n, f n - f₁ n, ext, rw [eq_sub_iff_add_eq', this],
    rw [this], apply hf.sub hf₁ },
  conv_lhs { rw [this] },
  rw [tsum_add hf₁ hf₂, tsum_eq_single 0],
  { congr' 1,
    fapply tsum_eq_tsum_of_ne_zero_bij (λ n _, n + 1),
    { intros _ _ _ _, exact nat.succ.inj },
    { rintros (_ | n) h,
      { contradiction },
      { exact ⟨n, h, rfl⟩ } },
    { intros, refl },
    { apply_instance } },
  { rintros (_ | n) hn,
    { contradiction },
    { refl } },
  { apply_instance }
end

end tsum

/-!
### Sums on subtypes

If `s` is a finset of `α`, we show that the summability of `f` in the whole space and on the subtype
`univ - s` are equivalent, and relate their sums. For a function defined on `ℕ`, we deduce the
formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in `sum_add_tsum_nat_add`.
-/
section subtype
variables {s : finset β}

lemma has_sum_subtype_iff :
  has_sum (λ b : {b // b ∉ s}, f b) a ↔ has_sum f (a + ∑ b in s, f b) :=
begin
  let gs := λ b, if b ∈ s then f b else 0,
  let g := λ b, if b ∉ s then f b else 0,
  have f_sum_iff : has_sum f (a + ∑ b in s, f b) = has_sum (λ b, g b + gs b) (a + ∑ b in s, f b),
  { congr,
    ext i,
    simp [gs, g],
    split_ifs;
    simp },
  have g_zero : ∀ b ∈ s, g b = 0,
  { assume b hb,
    dsimp [g],
    split_ifs,
    refl },
  have gs_sum : has_sum gs (∑ b in s, f b),
  { have : (∑ b in s, f b) = (∑ b in s, gs b),
    { apply sum_congr rfl (λ b hb, _),
      dsimp [gs],
      split_ifs,
      { refl },
      { exact false.elim (h hb) } },
    rw this,
    apply has_sum_sum_of_ne_finset_zero  (λ b hb, _),
    dsimp [gs],
    split_ifs,
    { exact false.elim (hb h) },
    { refl } },
  have : (λ b : {b // b ∉ s}, f b) = (λ b : {b // b ∉ s}, g b),
  { ext i,
    simp [g],
    split_ifs,
    { exact false.elim (i.2 h) },
    { refl } },
  rw [this, has_sum_subtype_iff_of_eq_zero g_zero, f_sum_iff],
  exact ⟨λ H, H.add gs_sum, λ H, by simpa using H.sub gs_sum⟩,
end

lemma has_sum_subtype_iff' :
  has_sum (λ b : {b // b ∉ s}, f b) (a - ∑ b in s, f b) ↔ has_sum f a :=
by simp [has_sum_subtype_iff]

lemma summable_subtype_iff (s : finset β):
  summable (λ b : {b // b ∉ s}, f b) ↔ summable f :=
⟨λ H, (has_sum_subtype_iff.1 H.has_sum).summable, λ H, (has_sum_subtype_iff'.2 H.has_sum).summable⟩

lemma sum_add_tsum_subtype [t2_space α] (s : finset β) (h : summable f) :
  (∑ b in s, f b) + (∑' (b : {b // b ∉ s}), f b) = (∑' b, f b) :=
by simpa [add_comm] using
  has_sum_unique (has_sum_subtype_iff.1 ((summable_subtype_iff s).2 h).has_sum) h.has_sum

lemma summable_nat_add_iff {f : ℕ → α} (k : ℕ) : summable (λ n, f (n + k)) ↔ summable f :=
begin
  refine iff.trans _ (summable_subtype_iff (range k)),
  rw [← (not_mem_range_equiv k).symm.summable_iff],
  refl
end

lemma has_sum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
  has_sum (λ n, f (n + k)) a ↔ has_sum f (a + ∑ i in range k, f i) :=
begin
  refine iff.trans _ has_sum_subtype_iff,
  rw [← (not_mem_range_equiv k).symm.has_sum_iff],
  refl
end

lemma has_sum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
  has_sum (λ n, f (n + k)) (a - ∑ i in range k, f i) ↔ has_sum f a :=
by simp [has_sum_nat_add_iff]

lemma sum_add_tsum_nat_add [t2_space α] {f : ℕ → α} (k : ℕ) (h : summable f) :
  (∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i) :=
by simpa [add_comm] using
  has_sum_unique ((has_sum_nat_add_iff k).1 ((summable_nat_add_iff k).2 h).has_sum) h.has_sum

end subtype

end topological_group

section topological_semiring
variables [semiring α] [topological_space α] [topological_semiring α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum.mul_left (a₂) : has_sum f a₁ → has_sum (λb, a₂ * f b) (a₂ * a₁) :=
has_sum_hom _ (continuous_const.mul continuous_id)

lemma has_sum.mul_right (a₂) (hf : has_sum f a₁) : has_sum (λb, f b * a₂) (a₁ * a₂) :=
@has_sum_hom _ _ _ _ _ f a₁ (λa, a * a₂) _ _ _
  (continuous_id.mul continuous_const) hf

lemma summable.mul_left (a) (hf : summable f) : summable (λb, a * f b) :=
(hf.has_sum.mul_left _).summable

lemma summable.mul_right (a) (hf : summable f) : summable (λb, f b * a) :=
(hf.has_sum.mul_right _).summable

section tsum
variables [t2_space α]

lemma tsum_mul_left (a) (hf : summable f) : (∑'b, a * f b) = a * (∑'b, f b) :=
tsum_eq_has_sum $ hf.has_sum.mul_left _

lemma tsum_mul_right (a) (hf : summable f) : (∑'b, f b * a) = (∑'b, f b) * a :=
tsum_eq_has_sum $ hf.has_sum.mul_right _

end tsum

end topological_semiring

section field

variables [field α] [topological_space α] [topological_semiring α]
{f g : β → α} {a a₁ a₂ : α}

lemma has_sum_mul_left_iff (h : a₂ ≠ 0) : has_sum f a₁ ↔ has_sum (λb, a₂ * f b) (a₂ * a₁) :=
⟨has_sum.mul_left _, λ H, by simpa [← mul_assoc, inv_mul_cancel h] using H.mul_left a₂⁻¹⟩

lemma has_sum_mul_right_iff (h : a₂ ≠ 0) : has_sum f a₁ ↔ has_sum (λb, f b * a₂) (a₁ * a₂) :=
by { simp only [mul_comm _ a₂], exact has_sum_mul_left_iff h }

lemma summable_mul_left_iff (h : a ≠ 0) : summable f ↔ summable (λb, a * f b) :=
⟨λ H, H.mul_left _, λ H, by simpa [← mul_assoc, inv_mul_cancel h] using H.mul_left a⁻¹⟩

lemma summable_mul_right_iff (h : a ≠ 0) : summable f ↔ summable (λb, f b * a) :=
by { simp only [mul_comm _ a], exact summable_mul_left_iff h }

end field

section order_topology
variables [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum_le (h : ∀b, f b ≤ g b) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
le_of_tendsto_of_tendsto' at_top_ne_bot hf hg $ assume s, sum_le_sum $ assume b _, h b

lemma has_sum_le_inj {g : γ → α} (i : β → γ) (hi : injective i) (hs : ∀c∉set.range i, 0 ≤ g c)
  (h : ∀b, f b ≤ g (i b)) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
have has_sum (λc, (partial_inv i c).cases_on' 0 f) a₁,
begin
  refine (has_sum_iff_has_sum_of_ne_zero_bij (λb _, i b) _ _ _).2 hf,
  { assume c₁ c₂ h₁ h₂ eq, exact hi eq },
  { assume c hc,
    cases eq : partial_inv i c with b; rw eq at hc,
    { contradiction },
    { rw [partial_inv_of_injective hi] at eq,
      exact ⟨b, hc, eq⟩ } },
  { assume c hc, rw [partial_inv_left hi, option.cases_on'] }
end,
begin
  refine has_sum_le (assume c, _) this hg,
  by_cases c ∈ set.range i,
  { rcases h with ⟨b, rfl⟩,
    rw [partial_inv_left hi, option.cases_on'],
    exact h _ },
  { have : partial_inv i c = none := dif_neg h,
    rw [this, option.cases_on'],
    exact hs _ h }
end

lemma tsum_le_tsum_of_inj {g : γ → α} (i : β → γ) (hi : injective i) (hs : ∀c∉set.range i, 0 ≤ g c)
  (h : ∀b, f b ≤ g (i b)) (hf : summable f) (hg : summable g) : tsum f ≤ tsum g :=
has_sum_le_inj i hi hs h hf.has_sum hg.has_sum

lemma sum_le_has_sum {f : β → α} (s : finset β) (hs : ∀ b∉s, 0 ≤ f b) (hf : has_sum f a) :
  ∑ b in s, f b ≤ a :=
ge_of_tendsto at_top_ne_bot hf (eventually_at_top.2 ⟨s, λ t hst,
  sum_le_sum_of_subset_of_nonneg hst $ λ b hbt hbs, hs b hbs⟩)

lemma sum_le_tsum {f : β → α} (s : finset β) (hs : ∀ b∉s, 0 ≤ f b) (hf : summable f) :
  ∑ b in s, f b ≤ tsum f :=
sum_le_has_sum s hs hf.has_sum

lemma tsum_le_tsum (h : ∀b, f b ≤ g b) (hf : summable f) (hg : summable g) : (∑'b, f b) ≤ (∑'b, g b) :=
has_sum_le h hf.has_sum hg.has_sum

lemma tsum_nonneg (h : ∀ b, 0 ≤ g b) : 0 ≤ (∑'b, g b) :=
begin
  by_cases hg : summable g,
  { simpa using tsum_le_tsum h summable_zero hg },
  { simp [tsum_eq_zero_of_not_summable hg] }
end

lemma tsum_nonpos (h : ∀ b, f b ≤ 0) : (∑'b, f b) ≤ 0 :=
begin
  by_cases hf : summable f,
  { simpa using tsum_le_tsum h hf summable_zero},
  { simp [tsum_eq_zero_of_not_summable hf] }
end

end order_topology

section uniform_group

variables [add_comm_group α] [uniform_space α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma summable_iff_cauchy_seq_finset [complete_space α] :
  summable f ↔ cauchy_seq (λ (s : finset β), ∑ b in s, f b) :=
(cauchy_map_iff_exists_tendsto at_top_ne_bot).symm

variable [uniform_add_group α]

lemma cauchy_seq_finset_iff_vanishing :
  cauchy_seq (λ (s : finset β), ∑ b in s, f b)
  ↔ ∀ e ∈ 𝓝 (0:α), (∃s:finset β, ∀t, disjoint t s → ∑ b in t, f b ∈ e) :=
begin
  simp only [cauchy_seq, cauchy_map_iff, and_iff_right at_top_ne_bot,
    prod_at_top_at_top_eq, uniformity_eq_comap_nhds_zero α, tendsto_comap_iff, (∘)],
  rw [tendsto_at_top' (_ : finset β × finset β → α)],
  split,
  { assume h e he,
    rcases h e he with ⟨⟨s₁, s₂⟩, h⟩,
    use [s₁ ∪ s₂],
    assume t ht,
    specialize h (s₁ ∪ s₂, (s₁ ∪ s₂) ∪ t) ⟨le_sup_left, le_sup_left_of_le le_sup_right⟩,
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
    exact hde _ _ (h _ finset.sdiff_disjoint) (h _ finset.sdiff_disjoint) }
end

variable [complete_space α]

lemma summable_iff_vanishing :
  summable f ↔ ∀ e ∈ 𝓝 (0:α), (∃s:finset β, ∀t, disjoint t s → ∑ b in t, f b ∈ e) :=
by rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing]

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a` -/
lemma summable.summable_of_eq_zero_or_self (hf : summable f) (h : ∀b, g b = 0 ∨ g b = f b) : summable g :=
summable_iff_vanishing.2 $
  assume e he,
  let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he in
  ⟨s, assume t ht,
    have eq : ∑ b in t.filter (λb, g b = f b), f b = ∑ b in t, g b :=
      calc ∑ b in t.filter (λb, g b = f b), f b = ∑ b in t.filter (λb, g b = f b), g b :
          finset.sum_congr rfl (assume b hb, (finset.mem_filter.1 hb).2.symm)
        ... = ∑ b in t, g b :
        begin
          refine finset.sum_subset (finset.filter_subset _) _,
          assume b hbt hb,
          simp only [(∉), finset.mem_filter, and_iff_right hbt] at hb,
          exact (h b).resolve_right hb
        end,
    eq ▸ hs _ $ finset.disjoint_of_subset_left (finset.filter_subset _) ht⟩

lemma summable.summable_comp_of_injective {i : γ → β} (hf : summable f) (hi : injective i) :
  summable (f ∘ i) :=
suffices summable (λb, if b ∈ set.range i then f b else 0),
begin
  refine (summable_iff_summable_ne_zero_bij (λc _, i c) _ _ _).1 this,
  { assume c₁ c₂ hc₁ hc₂ eq, exact hi eq },
  { assume b hb,
    split_ifs at hb,
    { rcases h with ⟨c, rfl⟩,
      exact ⟨c, hb, rfl⟩ },
    { contradiction } },
  { assume c hc, exact if_pos (set.mem_range_self _) }
end,
hf.summable_of_eq_zero_or_self $ assume b, by by_cases b ∈ set.range i; simp [h]

lemma summable.sigma_factor {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) (b : β) : summable (λc, f ⟨b, c⟩) :=
ha.summable_comp_of_injective (λ x y hxy, by simpa using hxy)

lemma summable.sigma' [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) : summable (λb, ∑'c, f ⟨b, c⟩) :=
ha.sigma (λ b, ha.sigma_factor b)

lemma tsum_sigma' [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) : (∑'p, f p) = (∑'b c, f ⟨b, c⟩) :=
tsum_sigma (λ b, ha.sigma_factor b) ha

end uniform_group

section cauchy_seq
open finset.Ico filter

/-- If the extended distance between consequent points of a sequence is estimated
by a summable series of `nnreal`s, then the original sequence is a Cauchy sequence. -/
lemma cauchy_seq_of_edist_le_of_summable [emetric_space α] {f : ℕ → α} (d : ℕ → nnreal)
  (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : summable d) : cauchy_seq f :=
begin
  refine emetric.cauchy_seq_iff_nnreal.2 (λ ε εpos, _),
  -- Actually we need partial sums of `d` to be a Cauchy sequence
  replace hd : cauchy_seq (λ (n : ℕ), ∑ x in range n, d x) :=
    let ⟨_, H⟩ := hd in cauchy_seq_of_tendsto_nhds _ H.tendsto_sum_nat,
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence
  refine (metric.cauchy_seq_iff'.1 hd ε (nnreal.coe_pos.2 εpos)).imp (λ N hN n hn, _),
  have hsum := hN n hn,
  -- We simplify the known inequality
  rw [dist_nndist, nnreal.nndist_eq, ← sum_range_add_sum_Ico _ hn, nnreal.add_sub_cancel'] at hsum,
  norm_cast at hsum,
  replace hsum := lt_of_le_of_lt (le_max_left _ _) hsum,
  rw edist_comm,

  -- Then use `hf` to simplify the goal to the same form
  apply lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn (λ k _ _, hf k)),
  assumption_mod_cast
end

/-- If the distance between consequent points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
lemma cauchy_seq_of_dist_le_of_summable [metric_space α] {f : ℕ → α} (d : ℕ → ℝ)
  (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : summable d) : cauchy_seq f :=
begin
  refine metric.cauchy_seq_iff'.2 (λε εpos, _),
  replace hd : cauchy_seq (λ (n : ℕ), ∑ x in range n, d x) :=
    let ⟨_, H⟩ := hd in cauchy_seq_of_tendsto_nhds _ H.tendsto_sum_nat,
  refine (metric.cauchy_seq_iff'.1 hd ε εpos).imp (λ N hN n hn, _),
  have hsum := hN n hn,
  rw [real.dist_eq, ← sum_Ico_eq_sub _ hn] at hsum,
  calc dist (f n) (f N) = dist (f N) (f n) : dist_comm _ _
  ... ≤ ∑ x in Ico N n, d x : dist_le_Ico_sum_of_dist_le hn (λ k _ _, hf k)
  ... ≤ abs (∑ x in Ico N n, d x) : le_abs_self _
  ... < ε : hsum
end

lemma cauchy_seq_of_summable_dist [metric_space α] {f : ℕ → α}
  (h : summable (λn, dist (f n) (f n.succ))) : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ (λ _, le_refl _) h

lemma dist_le_tsum_of_dist_le_of_tendsto [metric_space α] {f : ℕ → α} (d : ℕ → ℝ)
  (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : summable d) {a : α} (ha : tendsto f at_top (𝓝 a))
  (n : ℕ) :
  dist (f n) a ≤ ∑' m, d (n + m) :=
begin
  refine le_of_tendsto at_top_ne_bot (tendsto_const_nhds.dist ha)
    (eventually_at_top.2 ⟨n, λ m hnm, _⟩),
  refine le_trans (dist_le_Ico_sum_of_dist_le hnm (λ k _ _, hf k)) _,
  rw [sum_Ico_eq_sum_range],
  refine sum_le_tsum (range _) (λ _ _, le_trans dist_nonneg (hf _)) _,
  exact hd.summable_comp_of_injective (add_right_injective n)
end

lemma dist_le_tsum_of_dist_le_of_tendsto₀ [metric_space α] {f : ℕ → α} (d : ℕ → ℝ)
  (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : summable d) {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ tsum d :=
by simpa only [zero_add] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0

lemma dist_le_tsum_dist_of_tendsto [metric_space α] {f : ℕ → α}
  (h : summable (λn, dist (f n) (f n.succ))) {a : α} (ha : tendsto f at_top (𝓝 a)) (n) :
  dist (f n) a ≤ ∑' m, dist (f (n+m)) (f (n+m).succ) :=
show dist (f n) a ≤ ∑' m, (λx, dist (f x) (f x.succ)) (n + m), from
dist_le_tsum_of_dist_le_of_tendsto (λ n, dist (f n) (f n.succ)) (λ _, le_refl _) h ha n

lemma dist_le_tsum_dist_of_tendsto₀ [metric_space α] {f : ℕ → α}
  (h : summable (λn, dist (f n) (f n.succ))) {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ ∑' n, dist (f n) (f n.succ) :=
by simpa only [zero_add] using dist_le_tsum_dist_of_tendsto h ha 0

end cauchy_seq
