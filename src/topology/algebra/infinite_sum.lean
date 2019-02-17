/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `tendsto_sum_nat_of_is_sum`.

Reference:
* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/
import logic.function algebra.big_operators data.set data.finset
       topology.metric_space.basic topology.algebra.topological_structures

noncomputable theory
open lattice finset filter function classical
local attribute [instance] prop_decidable

def option.cases_on' {α β} : option α → β → (α → β) → β
| none     n s := n
| (some a) n s := s a

variables {α : Type*} {β : Type*} {γ : Type*}

section is_sum
variables [add_comm_monoid α] [topological_space α] [topological_add_monoid α]

/-- Infinite sum on a topological monoid
The `at_top` filter on `finset α` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is still invariant under reordering, and a absolute
sum operator.

This is based on Mario Carneiro's infinite sum in Metamath.
-/
def is_sum (f : β → α) (a : α) : Prop := tendsto (λs:finset β, s.sum f) at_top (nhds a)

/-- `has_sum f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def has_sum (f : β → α) : Prop := ∃a, is_sum f a

/-- `tsum f` is the sum of `f` it exists, or 0 otherwise -/
def tsum (f : β → α) := if h : has_sum f then classical.some h else 0

notation `∑` binders `, ` r:(scoped f, tsum f) := r

variables {f g : β → α} {a b : α} {s : finset β}

lemma is_sum_tsum (ha : has_sum f) : is_sum f (∑b, f b) :=
by simp [ha, tsum]; exact some_spec ha

lemma has_sum_spec (ha : is_sum f a) : has_sum f := ⟨a, ha⟩

lemma is_sum_zero : is_sum (λb, 0 : β → α) 0 :=
by simp [is_sum, tendsto_const_nhds]

lemma has_sum_zero : has_sum (λb, 0 : β → α) := has_sum_spec is_sum_zero

lemma is_sum_add (hf : is_sum f a) (hg : is_sum g b) : is_sum (λb, f b + g b) (a + b) :=
by simp [is_sum, sum_add_distrib]; exact tendsto_add hf hg

lemma has_sum_add (hf : has_sum f) (hg : has_sum g) : has_sum (λb, f b + g b) :=
has_sum_spec $ is_sum_add (is_sum_tsum hf)(is_sum_tsum hg)

lemma is_sum_sum {f : γ → β → α} {a : γ → α} {s : finset γ} :
  (∀i∈s, is_sum (f i) (a i)) → is_sum (λb, s.sum $ λi, f i b) (s.sum a) :=
finset.induction_on s (by simp [is_sum_zero]) (by simp [is_sum_add] {contextual := tt})

lemma has_sum_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, has_sum (f i)) :
  has_sum (λb, s.sum $ λi, f i b) :=
has_sum_spec $ is_sum_sum $ assume i hi, is_sum_tsum $ hf i hi

lemma is_sum_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : is_sum f (s.sum f) :=
tendsto_infi' s $ tendsto_cong tendsto_const_nhds $
  assume t (ht : s ⊆ t), show s.sum f = t.sum f, from sum_subset ht $ assume x _, hf _

lemma has_sum_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : has_sum f :=
has_sum_spec $ is_sum_sum_of_ne_finset_zero hf

lemma is_sum_ite_eq (b : β) (a : α) : is_sum (λb', if b' = b then a else 0) a :=
suffices
  is_sum (λb', if b' = b then a else 0) (({b} : finset β).sum (λb', if b' = b then a else 0)), from
  by simpa,
is_sum_sum_of_ne_finset_zero $ assume b' hb,
  have b' ≠ b, by simpa using hb,
  by rw [if_neg this]

lemma is_sum_of_iso {j : γ → β} {i : β → γ}
  (hf : is_sum f a) (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) : is_sum (f ∘ j) a :=
have ∀x y, j x = j y → x = y,
  from assume x y h,
  have i (j x) = i (j y), by rw [h],
  by rwa [h₁, h₁] at this,
have (λs:finset γ, s.sum (f ∘ j)) = (λs:finset β, s.sum f) ∘ (λs:finset γ, s.image j),
  from funext $ assume s, (sum_image $ assume x _ y _, this x y).symm,
show tendsto (λs:finset γ, s.sum (f ∘ j)) at_top (nhds a),
   by rw [this]; apply (tendsto_finset_image_at_top_at_top h₂).comp hf

lemma is_sum_iff_is_sum_of_iso {j : γ → β} (i : β → γ)
  (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) :
  is_sum (f ∘ j) a ↔ is_sum f a :=
iff.intro
  (assume hfj,
    have is_sum ((f ∘ j) ∘ i) a, from is_sum_of_iso hfj h₂ h₁,
    by simp [(∘), h₂] at this; assumption)
  (assume hf, is_sum_of_iso hf h₁ h₂)

lemma is_sum_hom (g : α → γ) [add_comm_monoid γ] [topological_space γ] [topological_add_monoid γ]
  [is_add_monoid_hom g] (h₃ : continuous g) (hf : is_sum f a) :
  is_sum (g ∘ f) (g a) :=
have (λs:finset β, s.sum (g ∘ f)) = g ∘ (λs:finset β, s.sum f),
  from funext $ assume s, sum_hom g,
show tendsto (λs:finset β, s.sum (g ∘ f)) at_top (nhds (g a)),
  by rw [this]; exact hf.comp (continuous_iff_continuous_at.mp h₃ a)

lemma tendsto_sum_nat_of_is_sum {f : ℕ → α} (h : is_sum f a) :
  tendsto (λn:ℕ, (range n).sum f) at_top (nhds a) :=
suffices map (λ (n : ℕ), sum (range n) f) at_top ≤ map (λ (s : finset ℕ), sum s f) at_top,
  from le_trans this h,
assume s (hs : {t : finset ℕ | t.sum f ∈ s} ∈ at_top.sets),
let ⟨t, ht⟩ := mem_at_top_sets.mp hs, ⟨n, hn⟩ := @exists_nat_subset_range t in
mem_at_top_sets.mpr ⟨n, assume n' hn', ht _ $ finset.subset.trans hn $ range_subset.mpr hn'⟩

lemma is_sum_sigma [regular_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α} {a : α}
  (hf : ∀b, is_sum (λc, f ⟨b, c⟩) (g b)) (ha : is_sum f a) : is_sum g a :=
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
      assume c hc, tendsto_infi' c $ tendsto_infi' hc $ tendsto_comap.comp (hf c),
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

lemma has_sum_sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (hf : ∀b, has_sum (λc, f ⟨b, c⟩)) (ha : has_sum f) : has_sum (λb, ∑c, f ⟨b, c⟩):=
has_sum_spec $ is_sum_sigma (assume b, is_sum_tsum $ hf b) (is_sum_tsum ha)

end is_sum

section is_sum_iff_is_sum_of_iso_ne_zero
variables [add_comm_monoid α] [topological_space α] [topological_add_monoid α]
variables {f : β → α} {g : γ → α} {a : α}

lemma is_sum_of_is_sum
  (h_eq : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ u'.sum g = v'.sum f)
  (hf : is_sum g a) : is_sum f a :=
suffices at_top.map (λs:finset β, s.sum f) ≤ at_top.map (λs:finset γ, s.sum g),
  from le_trans this hf,
by rw [map_at_top_eq, map_at_top_eq];
from (le_infi $ assume b, let ⟨v, hv⟩ := h_eq b in infi_le_of_le v $
  by simp [set.image_subset_iff]; exact hv)

lemma is_sum_iff_is_sum
  (h₁ : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ u'.sum g = v'.sum f)
  (h₂ : ∀v:finset β, ∃u:finset γ, ∀u', u ⊆ u' → ∃v', v ⊆ v' ∧ v'.sum f = u'.sum g) :
  is_sum f a ↔ is_sum g a :=
⟨is_sum_of_is_sum h₂, is_sum_of_is_sum h₁⟩

variables
  (i : Π⦃c⦄, g c ≠ 0 → β) (hi : ∀⦃c⦄ (h : g c ≠ 0), f (i h) ≠ 0)
  (j : Π⦃b⦄, f b ≠ 0 → γ) (hj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) ≠ 0)
  (hji : ∀⦃c⦄ (h : g c ≠ 0), j (hi h) = c)
  (hij : ∀⦃b⦄ (h : f b ≠ 0), i (hj h) = b)
  (hgj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) = f b)
include hi hj hji hij hgj

lemma is_sum_of_is_sum_ne_zero : is_sum g a → is_sum f a :=
have j_inj : ∀x y (hx : f x ≠ 0) (hy : f y ≠ 0), (j hx = j hy ↔ x = y),
  from assume x y hx hy,
  ⟨assume h,
    have i (hj hx) = i (hj hy), by simp [h],
    by rwa [hij, hij] at this; assumption,
  by simp {contextual := tt}⟩,
let ii : finset γ → finset β := λu, u.bind $ λc, if h : g c = 0 then ∅ else {i h} in
let jj : finset β → finset γ := λv, v.bind $ λb, if h : f b = 0 then ∅ else {j h} in
is_sum_of_is_sum $ assume u, exists.intro (ii u) $
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
    ... = v.sum _ : sum_bind $ by intros x hx y hy hxy; by_cases f x = 0; by_cases f y = 0; simp [*]
    ... = v.sum f : sum_congr rfl $ by intros x hx; by_cases f x = 0; simp [*]

lemma is_sum_iff_is_sum_of_ne_zero : is_sum f a ↔ is_sum g a :=
iff.intro
  (is_sum_of_is_sum_ne_zero j hj i hi hij hji $ assume b hb, by rw [←hgj (hi _), hji])
  (is_sum_of_is_sum_ne_zero i hi j hj hji hij hgj)

lemma has_sum_iff_has_sum_ne_zero : has_sum g ↔ has_sum f :=
exists_congr $
  assume a, is_sum_iff_is_sum_of_ne_zero j hj i hi hij hji $
    assume b hb, by rw [←hgj (hi _), hji]

end is_sum_iff_is_sum_of_iso_ne_zero

section is_sum_iff_is_sum_of_bij_ne_zero
variables [add_comm_monoid α] [topological_space α] [topological_add_monoid α]
variables {f : β → α} {g : γ → α} {a : α}
  (i : Π⦃c⦄, g c ≠ 0 → β)
  (h₁ : ∀⦃c₁ c₂⦄ (h₁ : g c₁ ≠ 0) (h₂ : g c₂ ≠ 0), i h₁ = i h₂ → c₁ = c₂)
  (h₂ : ∀⦃b⦄, f b ≠ 0 → ∃c (h : g c ≠ 0), i h = b)
  (h₃ : ∀⦃c⦄ (h : g c ≠ 0), f (i h) = g c)
include i h₁ h₂ h₃

lemma is_sum_iff_is_sum_of_ne_zero_bij : is_sum f a ↔ is_sum g a :=
have hi : ∀⦃c⦄ (h : g c ≠ 0), f (i h) ≠ 0,
  from assume c h, by simp [h₃, h],
let j : Π⦃b⦄, f b ≠ 0 → γ := λb h, some $ h₂ h in
have hj : ∀⦃b⦄ (h : f b ≠ 0), ∃(h : g (j h) ≠ 0), i h = b,
  from assume b h, some_spec $ h₂ h,
have hj₁ : ∀⦃b⦄ (h : f b ≠ 0), g (j h) ≠ 0,
  from assume b h, let ⟨h₁, _⟩ := hj h in h₁,
have hj₂ : ∀⦃b⦄ (h : f b ≠ 0), i (hj₁ h) = b,
  from assume b h, let ⟨h₁, h₂⟩ := hj h in h₂,
is_sum_iff_is_sum_of_ne_zero i hi j hj₁
  (assume c h, h₁ (hj₁ _) h $ hj₂ _) hj₂ (assume b h, by rw [←h₃ (hj₁ _), hj₂])

lemma has_sum_iff_has_sum_ne_zero_bij : has_sum f ↔ has_sum g :=
exists_congr $
  assume a, is_sum_iff_is_sum_of_ne_zero_bij @i h₁ h₂ h₃

end is_sum_iff_is_sum_of_bij_ne_zero

section tsum
variables [add_comm_monoid α] [topological_space α] [topological_add_monoid α] [t2_space α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma is_sum_unique : is_sum f a₁ → is_sum f a₂ → a₁ = a₂ := tendsto_nhds_unique at_top_ne_bot

lemma tsum_eq_is_sum (ha : is_sum f a) : (∑b, f b) = a := is_sum_unique (is_sum_tsum ⟨a, ha⟩) ha

lemma is_sum_iff_of_has_sum (h : has_sum f) : is_sum f a ↔ (∑b, f b) = a :=
iff.intro tsum_eq_is_sum (assume eq, eq ▸ is_sum_tsum h)

@[simp] lemma tsum_zero : (∑b:β, 0:α) = 0 := tsum_eq_is_sum is_sum_zero

lemma tsum_add (hf : has_sum f) (hg : has_sum g) : (∑b, f b + g b) = (∑b, f b) + (∑b, g b) :=
tsum_eq_is_sum $ is_sum_add (is_sum_tsum hf) (is_sum_tsum hg)

lemma tsum_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, has_sum (f i)) :
  (∑b, s.sum (λi, f i b)) = s.sum (λi, ∑b, f i b) :=
tsum_eq_is_sum $ is_sum_sum $ assume i hi, is_sum_tsum $ hf i hi

lemma tsum_eq_sum {f : β → α} {s : finset β} (hf : ∀b∉s, f b = 0)  :
  (∑b, f b) = s.sum f :=
tsum_eq_is_sum $ is_sum_sum_of_ne_finset_zero hf

lemma tsum_fintype [fintype β] (f : β → α) : (∑b, f b) = finset.univ.sum f :=
tsum_eq_sum $ λ a h, h.elim (mem_univ _)

lemma tsum_eq_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0)  :
  (∑b, f b) = f b :=
calc (∑b, f b) = (finset.singleton b).sum f : tsum_eq_sum $ by simp [hf] {contextual := tt}
  ... = f b : by simp

lemma tsum_sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (h₁ : ∀b, has_sum (λc, f ⟨b, c⟩)) (h₂ : has_sum f) : (∑p, f p) = (∑b c, f ⟨b, c⟩):=
(tsum_eq_is_sum $ is_sum_sigma (assume b, is_sum_tsum $ h₁ b) $ is_sum_tsum h₂).symm

@[simp] lemma tsum_ite_eq (b : β) (a : α) : (∑b', if b' = b then a else 0) = a :=
tsum_eq_is_sum (is_sum_ite_eq b a)

lemma tsum_eq_tsum_of_is_sum_iff_is_sum {f : β → α} {g : γ → α}
  (h : ∀{a}, is_sum f a ↔ is_sum g a) : (∑b, f b) = (∑c, g c) :=
by_cases
  (assume : ∃a, is_sum f a,
    let ⟨a, hfa⟩ := this in
    have hga : is_sum g a, from h.mp hfa,
    by rw [tsum_eq_is_sum hfa, tsum_eq_is_sum hga])
  (assume hf : ¬ has_sum f,
    have hg : ¬ has_sum g, from assume ⟨a, hga⟩, hf ⟨a, h.mpr hga⟩,
    by simp [tsum, hf, hg])

lemma tsum_eq_tsum_of_ne_zero {f : β → α} {g : γ → α}
  (i : Π⦃c⦄, g c ≠ 0 → β) (hi : ∀⦃c⦄ (h : g c ≠ 0), f (i h) ≠ 0)
  (j : Π⦃b⦄, f b ≠ 0 → γ) (hj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) ≠ 0)
  (hji : ∀⦃c⦄ (h : g c ≠ 0), j (hi h) = c)
  (hij : ∀⦃b⦄ (h : f b ≠ 0), i (hj h) = b)
  (hgj : ∀⦃b⦄ (h : f b ≠ 0), g (j h) = f b) :
  (∑i, f i) = (∑j, g j) :=
tsum_eq_tsum_of_is_sum_iff_is_sum $ assume a, is_sum_iff_is_sum_of_ne_zero i hi j hj hji hij hgj

lemma tsum_eq_tsum_of_ne_zero_bij {f : β → α} {g : γ → α}
  (i : Π⦃c⦄, g c ≠ 0 → β)
  (h₁ : ∀⦃c₁ c₂⦄ (h₁ : g c₁ ≠ 0) (h₂ : g c₂ ≠ 0), i h₁ = i h₂ → c₁ = c₂)
  (h₂ : ∀⦃b⦄, f b ≠ 0 → ∃c (h : g c ≠ 0), i h = b)
  (h₃ : ∀⦃c⦄ (h : g c ≠ 0), f (i h) = g c) :
  (∑i, f i) = (∑j, g j) :=
tsum_eq_tsum_of_is_sum_iff_is_sum $ assume a, is_sum_iff_is_sum_of_ne_zero_bij i h₁ h₂ h₃

lemma tsum_eq_tsum_of_iso (j : γ → β) (i : β → γ)
  (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) :
  (∑c, f (j c)) = (∑b, f b) :=
tsum_eq_tsum_of_is_sum_iff_is_sum $ assume a, is_sum_iff_is_sum_of_iso i h₁ h₂

lemma tsum_equiv (j : γ ≃ β) : (∑c, f (j c)) = (∑b, f b) :=
tsum_eq_tsum_of_iso j j.symm (by simp) (by simp)

end tsum

section topological_group
variables [add_comm_group α] [topological_space α] [topological_add_group α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma is_sum_neg : is_sum f a → is_sum (λb, - f b) (- a) :=
is_sum_hom has_neg.neg continuous_neg'

lemma has_sum_neg (hf : has_sum f) : has_sum (λb, - f b) :=
has_sum_spec $ is_sum_neg $ is_sum_tsum $ hf

lemma is_sum_sub (hf : is_sum f a₁) (hg : is_sum g a₂) : is_sum (λb, f b - g b) (a₁ - a₂) :=
by simp; exact is_sum_add hf (is_sum_neg hg)

lemma has_sum_sub (hf : has_sum f) (hg : has_sum g) : has_sum (λb, f b - g b) :=
has_sum_spec $ is_sum_sub (is_sum_tsum hf) (is_sum_tsum hg)

section tsum
variables [t2_space α]

lemma tsum_neg (hf : has_sum f) : (∑b, - f b) = - (∑b, f b) :=
tsum_eq_is_sum $ is_sum_neg $ is_sum_tsum $ hf

lemma tsum_sub (hf : has_sum f) (hg : has_sum g) : (∑b, f b - g b) = (∑b, f b) - (∑b, g b) :=
tsum_eq_is_sum $ is_sum_sub (is_sum_tsum hf) (is_sum_tsum hg)

end tsum

end topological_group

section topological_semiring
variables [semiring α] [topological_space α] [topological_semiring α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma is_sum_mul_left (a₂) : is_sum f a₁ → is_sum (λb, a₂ * f b) (a₂ * a₁) :=
is_sum_hom _ (continuous_mul continuous_const continuous_id)

lemma is_sum_mul_right (a₂) (hf : is_sum f a₁) : is_sum (λb, f b * a₂) (a₁ * a₂) :=
@is_sum_hom _ _ _ _ _ _ f a₁ (λa, a * a₂) _ _ _ _
  (continuous_mul continuous_id continuous_const) hf

lemma has_sum_mul_left (a) (hf : has_sum f) : has_sum (λb, a * f b) :=
has_sum_spec $ is_sum_mul_left _ $ is_sum_tsum hf

lemma has_sum_mul_right (a) (hf : has_sum f) : has_sum (λb, f b * a) :=
has_sum_spec $ is_sum_mul_right _ $ is_sum_tsum hf

section tsum
variables [t2_space α]

lemma tsum_mul_left (a) (hf : has_sum f) : (∑b, a * f b) = a * (∑b, f b) :=
tsum_eq_is_sum $ is_sum_mul_left _ $ is_sum_tsum hf

lemma tsum_mul_right (a) (hf : has_sum f) : (∑b, f b * a) = (∑b, f b) * a :=
tsum_eq_is_sum $ is_sum_mul_right _ $ is_sum_tsum hf

end tsum

end topological_semiring

section order_topology
variables [ordered_comm_monoid α] [topological_space α] [ordered_topology α]
  [topological_add_monoid α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma is_sum_le (h : ∀b, f b ≤ g b) (hf : is_sum f a₁) (hg : is_sum g a₂) : a₁ ≤ a₂ :=
le_of_tendsto_of_tendsto at_top_ne_bot hf hg $ univ_mem_sets' $
  assume s, sum_le_sum' $ assume b _, h b

lemma is_sum_le_inj {g : γ → α} (i : β → γ) (hi : injective i) (hs : ∀c∉set.range i, 0 ≤ g c)
  (h : ∀b, f b ≤ g (i b)) (hf : is_sum f a₁) (hg : is_sum g a₂) : a₁ ≤ a₂ :=
have is_sum (λc, (partial_inv i c).cases_on' 0 f) a₁,
begin
  refine (is_sum_iff_is_sum_of_ne_zero_bij (λb _, i b) _ _ _).2 hf,
  { assume c₁ c₂ h₁ h₂ eq, exact hi eq },
  { assume c hc,
    cases eq : partial_inv i c with b; rw eq at hc,
    { contradiction },
    { rw [partial_inv_of_injective hi] at eq,
      exact ⟨b, hc, eq⟩ } },
  { assume c hc, rw [partial_inv_left hi, option.cases_on'] }
end,
begin
  refine is_sum_le (assume c, _) this hg,
  by_cases c ∈ set.range i,
  { rcases h with ⟨b, rfl⟩,
    rw [partial_inv_left hi, option.cases_on'],
    exact h _ },
  { have : partial_inv i c = none := dif_neg h,
    rw [this, option.cases_on'],
    exact hs _ h }
end

lemma tsum_le_tsum (h : ∀b, f b ≤ g b) (hf : has_sum f) (hg : has_sum g) : (∑b, f b) ≤ (∑b, g b) :=
is_sum_le h (is_sum_tsum hf) (is_sum_tsum hg)

end order_topology

section uniform_group
variables [add_comm_group α] [uniform_space α] [complete_space α] [uniform_add_group α]
variables (f g : β → α) {a a₁ a₂ : α}

lemma has_sum_iff_cauchy : has_sum f ↔ cauchy (map (λ (s : finset β), sum s f) at_top) :=
(cauchy_map_iff_exists_tendsto at_top_ne_bot).symm

lemma has_sum_iff_vanishing :
  has_sum f ↔ ∀e∈(nhds (0:α)).sets, (∃s:finset β, ∀t, disjoint t s → t.sum f ∈ e) :=
begin
  simp only [has_sum_iff_cauchy, cauchy_map_iff, and_iff_right at_top_ne_bot,
    prod_at_top_at_top_eq, uniformity_eq_comap_nhds_zero α, tendsto_comap_iff, (∘)],
  rw [tendsto_at_top' (_ : finset β × finset β → α)],
  split,
  { assume h e he,
    rcases h e he with ⟨⟨s₁, s₂⟩, h⟩,
    use [s₁ ∪ s₂],
    assume t ht,
    have : (s₁ ∪ s₂) ∩ t = ∅ := finset.disjoint_iff_inter_eq_empty.1 ht.symm,
    specialize h (s₁ ∪ s₂, (s₁ ∪ s₂) ∪ t) ⟨le_sup_left, le_sup_left_of_le le_sup_right⟩,
    simpa only [finset.sum_union this, add_sub_cancel'] using h },
  { assume h e he,
    rcases exists_nhds_half_neg he with ⟨d, hd, hde⟩,
    rcases h d hd with ⟨s, h⟩,
    use [(s, s)],
    rintros ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩,
    have : t₂.sum f - t₁.sum f = (t₂ \ s).sum f - (t₁ \ s).sum f,
    { simp only [(finset.sum_sdiff ht₁).symm, (finset.sum_sdiff ht₂).symm,
        add_sub_add_right_eq_sub] },
    simp only [this],
    exact hde _ _ (h _ finset.disjoint_sdiff) (h _ finset.disjoint_sdiff) }
end

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a` -/
lemma has_sum_of_has_sum_of_sub (hf : has_sum f) (h : ∀b, g b = 0 ∨ g b = f b) : has_sum g :=
(has_sum_iff_vanishing g).2 $
  assume e he,
  let ⟨s, hs⟩ := (has_sum_iff_vanishing f).1 hf e he in
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

lemma has_sum_comp_of_has_sum_of_injective {i : γ → β} (hf : has_sum f) (hi : injective i) :
  has_sum (f ∘ i) :=
suffices has_sum (λb, if b ∈ set.range i then f b else 0),
begin
  refine (has_sum_iff_has_sum_ne_zero_bij (λc _, i c) _ _ _).1 this,
  { assume c₁ c₂ hc₁ hc₂ eq, exact hi eq },
  { assume b hb,
    split_ifs at hb,
    { rcases h with ⟨c, rfl⟩,
      exact ⟨c, hb, rfl⟩ },
    { contradiction } },
  { assume c hc, exact if_pos (set.mem_range_self _) }
end,
has_sum_of_has_sum_of_sub _ _ hf $ assume b, by by_cases b ∈ set.range i; simp [h]

end uniform_group
