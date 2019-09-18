/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `tendsto_sum_nat_of_has_sum`.

Reference:
* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/
import logic.function algebra.big_operators data.set.lattice data.finset
       topology.metric_space.basic topology.algebra.uniform_group topology.algebra.ring
       topology.algebra.ordered topology.instances.real

noncomputable theory
open lattice finset filter function classical
local attribute [instance] classical.prop_decidable -- TODO: use "open_locale classical"

def option.cases_on' {α β} : option α → β → (α → β) → β
| none     n s := n
| (some a) n s := s a

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
def has_sum (f : β → α) (a : α) : Prop := tendsto (λs:finset β, s.sum f) at_top (nhds a)

/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def summable (f : β → α) : Prop := ∃a, has_sum f a

/-- `tsum f` is the sum of `f` it exists, or 0 otherwise -/
def tsum (f : β → α) := if h : summable f then classical.some h else 0

notation `∑` binders `, ` r:(scoped f, tsum f) := r

variables {f g : β → α} {a b : α} {s : finset β}

lemma has_sum_tsum (ha : summable f) : has_sum f (∑b, f b) :=
by simp [ha, tsum]; exact some_spec ha

lemma summable_spec (ha : has_sum f a) : summable f := ⟨a, ha⟩

lemma has_sum_zero : has_sum (λb, 0 : β → α) 0 :=
by simp [has_sum, tendsto_const_nhds]

lemma summable_zero : summable (λb, 0 : β → α) := summable_spec has_sum_zero

lemma has_sum_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : has_sum f (s.sum f) :=
tendsto_infi' s $ tendsto.congr'
  (assume t (ht : s ⊆ t), show s.sum f = t.sum f, from sum_subset ht $ assume x _, hf _)
  tendsto_const_nhds

lemma summable_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : summable f :=
summable_spec $ has_sum_sum_of_ne_finset_zero hf

lemma has_sum_ite_eq (b : β) (a : α) : has_sum (λb', if b' = b then a else 0) a :=
suffices
  has_sum (λb', if b' = b then a else 0) (({b} : finset β).sum (λb', if b' = b then a else 0)), from
  by simpa,
has_sum_sum_of_ne_finset_zero $ assume b' hb,
  have b' ≠ b, by simpa using hb,
  by rw [if_neg this]

lemma has_sum_of_iso {j : γ → β} {i : β → γ}
  (hf : has_sum f a) (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) : has_sum (f ∘ j) a :=
have ∀x y, j x = j y → x = y,
  from assume x y h,
  have i (j x) = i (j y), by rw [h],
  by rwa [h₁, h₁] at this,
have (λs:finset γ, s.sum (f ∘ j)) = (λs:finset β, s.sum f) ∘ (λs:finset γ, s.image j),
  from funext $ assume s, (sum_image $ assume x _ y _, this x y).symm,
show tendsto (λs:finset γ, s.sum (f ∘ j)) at_top (nhds a),
   by rw [this]; apply hf.comp (tendsto_finset_image_at_top_at_top h₂)

lemma has_sum_iff_has_sum_of_iso {j : γ → β} (i : β → γ)
  (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) :
  has_sum (f ∘ j) a ↔ has_sum f a :=
iff.intro
  (assume hfj,
    have has_sum ((f ∘ j) ∘ i) a, from has_sum_of_iso hfj h₂ h₁,
    by simp [(∘), h₂] at this; assumption)
  (assume hf, has_sum_of_iso hf h₁ h₂)

lemma has_sum_hom (g : α → γ) [add_comm_monoid γ] [topological_space γ]
  [is_add_monoid_hom g] (h₃ : continuous g) (hf : has_sum f a) :
  has_sum (g ∘ f) (g a) :=
have (λs:finset β, s.sum (g ∘ f)) = g ∘ (λs:finset β, s.sum f),
  from funext $ assume s, sum_hom g,
show tendsto (λs:finset β, s.sum (g ∘ f)) at_top (nhds (g a)),
  by rw [this]; exact tendsto.comp (continuous_iff_continuous_at.mp h₃ a) hf

lemma tendsto_sum_nat_of_has_sum {f : ℕ → α} (h : has_sum f a) :
  tendsto (λn:ℕ, (range n).sum f) at_top (nhds a) :=
suffices map (λ (n : ℕ), sum (range n) f) at_top ≤ map (λ (s : finset ℕ), sum s f) at_top,
  from le_trans this h,
assume s (hs : {t : finset ℕ | t.sum f ∈ s} ∈ at_top),
let ⟨t, ht⟩ := mem_at_top_sets.mp hs, ⟨n, hn⟩ := @exists_nat_subset_range t in
mem_at_top_sets.mpr ⟨n, assume n' hn', ht _ $ finset.subset.trans hn $ range_subset.mpr hn'⟩

variable [topological_add_monoid α]

lemma has_sum_add (hf : has_sum f a) (hg : has_sum g b) : has_sum (λb, f b + g b) (a + b) :=
by simp [has_sum, sum_add_distrib]; exact tendsto_add hf hg

lemma summable_add (hf : summable f) (hg : summable g) : summable (λb, f b + g b) :=
summable_spec $ has_sum_add (has_sum_tsum hf)(has_sum_tsum hg)

lemma has_sum_sum {f : γ → β → α} {a : γ → α} {s : finset γ} :
  (∀i∈s, has_sum (f i) (a i)) → has_sum (λb, s.sum $ λi, f i b) (s.sum a) :=
finset.induction_on s (by simp [has_sum_zero]) (by simp [has_sum_add] {contextual := tt})

lemma summable_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, summable (f i)) :
  summable (λb, s.sum $ λi, f i b) :=
summable_spec $ has_sum_sum $ assume i hi, has_sum_tsum $ hf i hi

lemma has_sum_sigma [regular_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α} {a : α}
  (hf : ∀b, has_sum (λc, f ⟨b, c⟩) (g b)) (ha : has_sum f a) : has_sum g a :=
assume s' hs',
let
  ⟨s, hs, hss', hsc⟩ := nhds_is_closed hs',
  ⟨u, hu⟩ := mem_at_top_sets.mp $ ha $ hs,
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
      (⋂b (hb : b ∈ bs), (λp:Πb, finset (γ b), p b) ⁻¹' {cs' | cs b hb ⊆ cs' }) ∩
      (λp, bs.sum (λb, (p b).sum (λc, f ⟨b, c⟩))) ⁻¹' s ≠ ∅,
    from assume cs,
    let cs' := λb, (if h : b ∈ bs then cs b h else ∅) ∪ snds b in
    have sum_eq : bs.sum (λb, (cs' b).sum (λc, f ⟨b, c⟩)) = (bs.sigma cs').sum f,
      from sum_sigma.symm,
    have (bs.sigma cs').sum f ∈ s,
      from hu _ $ finset.subset.trans u_subset $ sigma_mono hbs $
        assume b, @finset.subset_union_right (γ b) _ _ _,
    set.ne_empty_iff_exists_mem.mpr $ exists.intro cs' $
    by simp [sum_eq, this]; { intros b hb, simp [cs', hb, finset.subset_union_right] },
  have tendsto (λp:(Πb:β, finset (γ b)), bs.sum (λb, (p b).sum (λc, f ⟨b, c⟩)))
      (⨅b (h : b ∈ bs), at_top.comap (λp, p b)) (nhds (bs.sum g)),
    from tendsto_finset_sum bs $
      assume c hc, tendsto_infi' c $ tendsto_infi' hc $ by apply tendsto.comp (hf c) tendsto_comap,
  have bs.sum g ∈ s,
    from mem_of_closed_of_tendsto' this hsc $ forall_sets_neq_empty_iff_neq_bot.mp $
      by simp [mem_inf_sets, exists_imp_distrib, and_imp, forall_and_distrib,
               filter.mem_infi_sets_finset, mem_comap_sets, skolem, mem_at_top_sets,
               and_comm];
      from
        assume s₁ s₂ s₃ hs₁ hs₃ p hs₂ p' hp cs hp',
        have (⋂b (h : b ∈ bs), (λp:(Πb, finset (γ b)), p b) ⁻¹' {cs' | cs b h ⊆ cs' }) ≤ (⨅b∈bs, p b),
          from infi_le_infi $ assume b, infi_le_infi $ assume hb,
            le_trans (set.preimage_mono $ hp' b hb) (hp b hb),
        neq_bot_of_le_neq_bot (h _) (le_trans (set.inter_subset_inter (le_trans this hs₂) hs₃) hs₁),
  hss' this

lemma summable_sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (hf : ∀b, summable (λc, f ⟨b, c⟩)) (ha : summable f) : summable (λb, ∑c, f ⟨b, c⟩) :=
summable_spec $ has_sum_sigma (assume b, has_sum_tsum $ hf b) (has_sum_tsum ha)

end has_sum

section has_sum_iff_has_sum_of_iso_ne_zero
variables [add_comm_monoid α] [topological_space α]
variables {f : β → α} {g : γ → α} {a : α}

lemma has_sum_of_has_sum
  (h_eq : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ u'.sum g = v'.sum f)
  (hf : has_sum g a) : has_sum f a :=
suffices at_top.map (λs:finset β, s.sum f) ≤ at_top.map (λs:finset γ, s.sum g),
  from le_trans this hf,
by rw [map_at_top_eq, map_at_top_eq];
from (le_infi $ assume b, let ⟨v, hv⟩ := h_eq b in infi_le_of_le v $
  by simp [set.image_subset_iff]; exact hv)

lemma has_sum_iff_has_sum
  (h₁ : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ u'.sum g = v'.sum f)
  (h₂ : ∀v:finset β, ∃u:finset γ, ∀u', u ⊆ u' → ∃v', v ⊆ v' ∧ v'.sum f = u'.sum g) :
  has_sum f a ↔ has_sum g a :=
⟨has_sum_of_has_sum h₂, has_sum_of_has_sum h₁⟩

variables
  (i : Π⦃c⦄, g c ≠ 0 → β) (hi : ∀⦃c⦄ (h : g c ≠ 0), f (i h) ≠ 0)
  (j : Π⦃b⦄, f b ≠ 0 → γ) (hj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) ≠ 0)
  (hji : ∀⦃c⦄ (h : g c ≠ 0), j (hi h) = c)
  (hij : ∀⦃b⦄ (h : f b ≠ 0), i (hj h) = b)
  (hgj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) = f b)
include hi hj hji hij hgj

lemma has_sum_of_has_sum_ne_zero : has_sum g a → has_sum f a :=
have j_inj : ∀x y (hx : f x ≠ 0) (hy : f y ≠ 0), (j hx = j hy ↔ x = y),
  from assume x y hx hy,
  ⟨assume h,
    have i (hj hx) = i (hj hy), by simp [h],
    by rwa [hij, hij] at this; assumption,
  by simp {contextual := tt}⟩,
let ii : finset γ → finset β := λu, u.bind $ λc, if h : g c = 0 then ∅ else {i h} in
let jj : finset β → finset γ := λv, v.bind $ λb, if h : f b = 0 then ∅ else {j h} in
has_sum_of_has_sum $ assume u, exists.intro (ii u) $
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
  calc (u ∪ jj v).sum g = (jj v).sum g : (sum_subset (subset_union_right _ _) this).symm
    ... = v.sum _ : sum_bind $ by intros x _ y _ _; by_cases f x = 0; by_cases f y = 0; simp [*]; cc
    ... = v.sum f : sum_congr rfl $ by intros x hx; by_cases f x = 0; simp [*]

lemma has_sum_iff_has_sum_of_ne_zero : has_sum f a ↔ has_sum g a :=
iff.intro
  (has_sum_of_has_sum_ne_zero j hj i hi hij hji $ assume b hb, by rw [←hgj (hi _), hji])
  (has_sum_of_has_sum_ne_zero i hi j hj hji hij hgj)

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

section tsum
variables [add_comm_monoid α] [topological_space α] [t2_space α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum_unique : has_sum f a₁ → has_sum f a₂ → a₁ = a₂ := tendsto_nhds_unique at_top_ne_bot

lemma tsum_eq_has_sum (ha : has_sum f a) : (∑b, f b) = a := has_sum_unique (has_sum_tsum ⟨a, ha⟩) ha

lemma has_sum_iff_of_summable (h : summable f) : has_sum f a ↔ (∑b, f b) = a :=
iff.intro tsum_eq_has_sum (assume eq, eq ▸ has_sum_tsum h)

@[simp] lemma tsum_zero : (∑b:β, 0:α) = 0 := tsum_eq_has_sum has_sum_zero

lemma tsum_eq_sum {f : β → α} {s : finset β} (hf : ∀b∉s, f b = 0)  :
  (∑b, f b) = s.sum f :=
tsum_eq_has_sum $ has_sum_sum_of_ne_finset_zero hf

lemma tsum_fintype [fintype β] (f : β → α) : (∑b, f b) = finset.univ.sum f :=
tsum_eq_sum $ λ a h, h.elim (mem_univ _)

lemma tsum_eq_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0)  :
  (∑b, f b) = f b :=
calc (∑b, f b) = (finset.singleton b).sum f : tsum_eq_sum $ by simp [hf] {contextual := tt}
  ... = f b : by simp

@[simp] lemma tsum_ite_eq (b : β) (a : α) : (∑b', if b' = b then a else 0) = a :=
tsum_eq_has_sum (has_sum_ite_eq b a)

lemma tsum_eq_tsum_of_has_sum_iff_has_sum {f : β → α} {g : γ → α}
  (h : ∀{a}, has_sum f a ↔ has_sum g a) : (∑b, f b) = (∑c, g c) :=
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
  (∑i, f i) = (∑j, g j) :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ assume a, has_sum_iff_has_sum_of_ne_zero i hi j hj hji hij hgj

lemma tsum_eq_tsum_of_ne_zero_bij {f : β → α} {g : γ → α}
  (i : Π⦃c⦄, g c ≠ 0 → β)
  (h₁ : ∀⦃c₁ c₂⦄ (h₁ : g c₁ ≠ 0) (h₂ : g c₂ ≠ 0), i h₁ = i h₂ → c₁ = c₂)
  (h₂ : ∀⦃b⦄, f b ≠ 0 → ∃c (h : g c ≠ 0), i h = b)
  (h₃ : ∀⦃c⦄ (h : g c ≠ 0), f (i h) = g c) :
  (∑i, f i) = (∑j, g j) :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ assume a, has_sum_iff_has_sum_of_ne_zero_bij i h₁ h₂ h₃

lemma tsum_eq_tsum_of_iso (j : γ → β) (i : β → γ)
  (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) :
  (∑c, f (j c)) = (∑b, f b) :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ assume a, has_sum_iff_has_sum_of_iso i h₁ h₂

lemma tsum_equiv (j : γ ≃ β) : (∑c, f (j c)) = (∑b, f b) :=
tsum_eq_tsum_of_iso j j.symm (by simp) (by simp)

variable [topological_add_monoid α]

lemma tsum_add (hf : summable f) (hg : summable g) : (∑b, f b + g b) = (∑b, f b) + (∑b, g b) :=
tsum_eq_has_sum $ has_sum_add (has_sum_tsum hf) (has_sum_tsum hg)

lemma tsum_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, summable (f i)) :
  (∑b, s.sum (λi, f i b)) = s.sum (λi, ∑b, f i b) :=
tsum_eq_has_sum $ has_sum_sum $ assume i hi, has_sum_tsum $ hf i hi

lemma tsum_sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (h₁ : ∀b, summable (λc, f ⟨b, c⟩)) (h₂ : summable f) : (∑p, f p) = (∑b c, f ⟨b, c⟩) :=
(tsum_eq_has_sum $ has_sum_sigma (assume b, has_sum_tsum $ h₁ b) $ has_sum_tsum h₂).symm

end tsum

section topological_group
variables [add_comm_group α] [topological_space α] [topological_add_group α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum_neg : has_sum f a → has_sum (λb, - f b) (- a) :=
has_sum_hom has_neg.neg continuous_neg'

lemma summable_neg (hf : summable f) : summable (λb, - f b) :=
summable_spec $ has_sum_neg $ has_sum_tsum $ hf

lemma has_sum_sub (hf : has_sum f a₁) (hg : has_sum g a₂) : has_sum (λb, f b - g b) (a₁ - a₂) :=
by simp; exact has_sum_add hf (has_sum_neg hg)

lemma summable_sub (hf : summable f) (hg : summable g) : summable (λb, f b - g b) :=
summable_spec $ has_sum_sub (has_sum_tsum hf) (has_sum_tsum hg)

section tsum
variables [t2_space α]

lemma tsum_neg (hf : summable f) : (∑b, - f b) = - (∑b, f b) :=
tsum_eq_has_sum $ has_sum_neg $ has_sum_tsum $ hf

lemma tsum_sub (hf : summable f) (hg : summable g) : (∑b, f b - g b) = (∑b, f b) - (∑b, g b) :=
tsum_eq_has_sum $ has_sum_sub (has_sum_tsum hf) (has_sum_tsum hg)

lemma tsum_eq_zero_add {f : ℕ → α} (hf : summable f) : (∑b, f b) = f 0 + (∑b, f (b + 1)) :=
begin
  let f₁ : ℕ → α := λ n, nat.rec (f 0) (λ _ _, 0) n,
  let f₂ : ℕ → α := λ n, nat.rec 0 (λ k _, f (k+1)) n,
  have : f = λ n, f₁ n + f₂ n, { ext n, symmetry, cases n, apply add_zero, apply zero_add },
  have hf₁ : summable f₁,
  { fapply summable_sum_of_ne_finset_zero,
    { exact finset.singleton 0 },
    { rintros (_ | n) hn,
      { exfalso,
        apply hn,
        apply finset.mem_singleton_self },
      { refl } } },
  have hf₂ : summable f₂,
  { have : f₂ = λ n, f n - f₁ n, ext, rw [eq_sub_iff_add_eq', this],
    rw [this], apply summable_sub hf hf₁ },
  conv_lhs { rw [this] },
  rw [tsum_add hf₁ hf₂, tsum_eq_single 0],
  { congr' 1,
    fapply tsum_eq_tsum_of_ne_zero_bij (λ n _, n + 1),
    { intros _ _ _ _, exact nat.succ_inj },
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

end topological_group

section topological_semiring
variables [semiring α] [topological_space α] [topological_semiring α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum_mul_left (a₂) : has_sum f a₁ → has_sum (λb, a₂ * f b) (a₂ * a₁) :=
has_sum_hom _ (continuous_mul continuous_const continuous_id)

lemma has_sum_mul_right (a₂) (hf : has_sum f a₁) : has_sum (λb, f b * a₂) (a₁ * a₂) :=
@has_sum_hom _ _ _ _ _ f a₁ (λa, a * a₂) _ _ _
  (continuous_mul continuous_id continuous_const) hf

lemma summable_mul_left (a) (hf : summable f) : summable (λb, a * f b) :=
summable_spec $ has_sum_mul_left _ $ has_sum_tsum hf

lemma summable_mul_right (a) (hf : summable f) : summable (λb, f b * a) :=
summable_spec $ has_sum_mul_right _ $ has_sum_tsum hf

section tsum
variables [t2_space α]

lemma tsum_mul_left (a) (hf : summable f) : (∑b, a * f b) = a * (∑b, f b) :=
tsum_eq_has_sum $ has_sum_mul_left _ $ has_sum_tsum hf

lemma tsum_mul_right (a) (hf : summable f) : (∑b, f b * a) = (∑b, f b) * a :=
tsum_eq_has_sum $ has_sum_mul_right _ $ has_sum_tsum hf

end tsum

end topological_semiring

section order_topology
variables [ordered_comm_monoid α] [topological_space α] [ordered_topology α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum_le (h : ∀b, f b ≤ g b) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
le_of_tendsto_of_tendsto at_top_ne_bot hf hg $ univ_mem_sets' $
  assume s, sum_le_sum $ assume b _, h b

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

lemma tsum_le_tsum (h : ∀b, f b ≤ g b) (hf : summable f) (hg : summable g) : (∑b, f b) ≤ (∑b, g b) :=
has_sum_le h (has_sum_tsum hf) (has_sum_tsum hg)

end order_topology

section uniform_group

variables [add_comm_group α] [uniform_space α] [complete_space α]
variables (f g : β → α) {a a₁ a₂ : α}

lemma summable_iff_cauchy : summable f ↔ cauchy (map (λ (s : finset β), sum s f) at_top) :=
(cauchy_map_iff_exists_tendsto at_top_ne_bot).symm

variable [uniform_add_group α]

lemma summable_iff_vanishing :
  summable f ↔ ∀ e ∈ nhds (0:α), (∃s:finset β, ∀t, disjoint t s → t.sum f ∈ e) :=
begin
  simp only [summable_iff_cauchy, cauchy_map_iff, and_iff_right at_top_ne_bot,
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
    have : t₂.sum f - t₁.sum f = (t₂ \ s).sum f - (t₁ \ s).sum f,
    { simp only [(finset.sum_sdiff ht₁).symm, (finset.sum_sdiff ht₂).symm,
        add_sub_add_right_eq_sub] },
    simp only [this],
    exact hde _ _ (h _ finset.sdiff_disjoint) (h _ finset.sdiff_disjoint) }
end

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a` -/
lemma summable_of_summable_of_sub (hf : summable f) (h : ∀b, g b = 0 ∨ g b = f b) : summable g :=
(summable_iff_vanishing g).2 $
  assume e he,
  let ⟨s, hs⟩ := (summable_iff_vanishing f).1 hf e he in
  ⟨s, assume t ht,
    have eq : (t.filter (λb, g b = f b)).sum f = t.sum g :=
      calc (t.filter (λb, g b = f b)).sum f = (t.filter (λb, g b = f b)).sum g :
          finset.sum_congr rfl (assume b hb, (finset.mem_filter.1 hb).2.symm)
        ... = t.sum g :
        begin
          refine finset.sum_subset (finset.filter_subset _) _,
          assume b hbt hb,
          simp only [(∉), finset.mem_filter, and_iff_right hbt] at hb,
          exact (h b).resolve_right hb
        end,
    eq ▸ hs _ $ finset.disjoint_of_subset_left (finset.filter_subset _) ht⟩

lemma summable_comp_of_summable_of_injective {i : γ → β} (hf : summable f) (hi : injective i) :
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
summable_of_summable_of_sub _ _ hf $ assume b, by by_cases b ∈ set.range i; simp [h]

end uniform_group

section cauchy_seq
open finset.Ico filter

lemma cauchy_seq_of_summable_dist [metric_space α] {f : ℕ → α}
  (h : summable (λn, dist (f n) (f n.succ))) : cauchy_seq f :=
begin
  let d := λn, dist (f n) (f (n+1)),
  refine metric.cauchy_seq_iff'.2 (λε εpos, _),
  rcases (summable_iff_vanishing _).1 h {x : ℝ | x < ε} (gt_mem_nhds εpos) with ⟨s, hs⟩,
  have : ∃N:ℕ, ∀x ∈ s, x < N,
  { by_cases h : s = ∅,
    { use 0, simp [h]},
    { use s.max' h + 1,
      exact λx hx, lt_of_le_of_lt (s.le_max' h x hx) (nat.lt_succ_self _) }},
  rcases this with ⟨N, hN⟩,
  refine ⟨N, λn hn, _⟩,
  have : ∀n, n ≥ N → dist (f N) (f n) ≤ (Ico N n).sum d,
  { apply nat.le_induction,
    { simp },
    { assume n hn hrec,
      calc dist (f N) (f (n+1)) ≤ dist (f N) (f n) + d n : dist_triangle _ _ _
        ... ≤ (Ico N n).sum d + d n : add_le_add hrec (le_refl _)
        ... = (Ico N (n+1)).sum d : by rw [succ_top hn, sum_insert, add_comm]; simp }},
  calc dist (f n) (f N) ≤ (Ico N n).sum d : by rw dist_comm; apply this n hn
    ... < ε : hs _ (finset.disjoint_iff_ne.2
                     (λa ha b hb, ne_of_gt (lt_of_lt_of_le (hN _ hb) (mem.1 ha).1)))
end

end cauchy_seq
