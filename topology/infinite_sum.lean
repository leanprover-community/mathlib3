/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.
-/
import data.set data.finset topology.topological_structures topology.metric_space algebra.big_operators
  logic.function_inverse
noncomputable theory
open set lattice finset filter function

variables {α : Type*} {β : Type*} {γ : Type*}

section logic

theorem forall_and_distrib' {α : Sort*} (p q : α → Prop) :
  (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h, ⟨(assume x, (h x).left), (assume x, (h x).right)⟩)
  (assume h x, ⟨h.left x, h.right x⟩)

end logic

lemma add_div {α : Type*} [division_ring α] {a b c : α} : (a + b) / c = a / c + b / c :=
by rw [div_eq_mul_one_div, add_mul, ←div_eq_mul_one_div, ←div_eq_mul_one_div]

open classical
local attribute [instance] decidable_inhabited prop_decidable

namespace filter

lemma mem_at_top [preorder α] (a : α) : {b : α | a ≤ b} ∈ (@at_top α _).sets :=
mem_infi_sets a $ subset.refl _

lemma mem_infi_sets_finset {s : finset α} {f : α → filter β} :
  ∀t, t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⋂a∈s, p a) ⊆ t) :=
show ∀t,  t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⨅a∈s, p a) ≤ t),
  from s.induction_on (by simp; exact assume t, iff.refl _) $
    by simp [infi_or, mem_inf_sets, infi_inf_eq] {contextual := tt};
    from assume a s has ih t, iff.intro
      (assume ⟨t₁, ht₁, t₂, ht, p, hp, ht₂⟩,
        ⟨λa', if a' = a then t₁ else p a',
          assume a' ha', by by_cases a' = a; simp * at *,
          have ∀a', (⨅ (h : a' ∈ s), ite (a' = a) t₁ (p a')) ≤ ⨅ (H : a' ∈ s), p a',
            from assume a', infi_le_infi $ assume has',
              have a' ≠ a, from assume h, has $ h ▸ has',
              le_of_eq $ by simp [this],
          le_trans (inf_le_inf (by simp; exact le_refl t₁) (le_trans (infi_le_infi this) ht₂)) ht⟩)
      (assume ⟨p, hp, ht⟩, ⟨p a, hp _ (by simp), ⨅ (x : α) (h : x ∈ s), p x, ht, p,
        assume a ha, hp _ (or.inr ha), le_refl _⟩)

end filter

open filter

section topological_space

variables [topological_space α]

lemma mem_closure_of_tendsto {f : β → α} {x : filter β} {a : α} {s : set α}
  (hf : tendsto f x (nhds a)) (hs : is_closed s) (h : x ⊓ principal (f ⁻¹' s) ≠ ⊥) : a ∈ s :=
is_closed_iff_nhds.mp hs _ $ neq_bot_of_le_neq_bot (@map_ne_bot _ _ _ f h) $
  le_inf (le_trans (map_mono $ inf_le_left) hf) $
    le_trans (map_mono $ inf_le_right_of_le $ by simp; exact subset.refl _) (@map_vmap_le _ _ _ f)

end topological_space

section uniform_space

lemma cauchy_iff [uniform_space α] {f : filter α} :
  cauchy f ↔ (f ≠ ⊥ ∧ (∀s∈(@uniformity α _).sets, ∃t∈f.sets, set.prod t t ⊆ s)) :=
and_congr (iff.refl _) $ forall_congr $ assume s, forall_congr $ assume hs, mem_prod_same_iff

end uniform_space

section at_top

@[simp] lemma at_top_ne_bot [inhabited α] [semilattice_sup α] : (at_top : filter α) ≠ ⊥ :=
infi_neq_bot_of_directed (by apply_instance)
  (assume a b, ⟨a ⊔ b, by simp {contextual := tt}⟩)
  (assume a, by simp [principal_eq_bot_iff]; exact ne_empty_of_mem (le_refl a))

lemma mem_at_top_iff [inhabited α] [semilattice_sup α] {s : set α} :
  s ∈ (at_top : filter α).sets ↔ (∃a:α, ∀b≥a, b ∈ s) :=
iff.intro
  (assume h, infi_sets_induct h ⟨default α, by simp⟩
    (assume a s₁ s₂ ha ⟨b, hb⟩, ⟨a ⊔ b,
      assume c hc, ⟨ha $ le_trans le_sup_left hc, hb _ $ le_trans le_sup_right hc⟩⟩)
    (assume s₁ s₂ h ⟨a, ha⟩, ⟨a, assume b hb, h $ ha _ hb⟩))
  (assume ⟨a, h⟩, mem_infi_sets a $ assume x, h x)

lemma map_at_top_eq [inhabited α] [semilattice_sup α] {f : α → β} :
  at_top.map f = (⨅a, principal $ f '' {a' | a ≤ a'}) :=
calc map f (⨅a, principal {a' | a ≤ a'}) = (⨅a, map f $ principal {a' | a ≤ a'}) :
    map_infi_eq (assume a b, ⟨a ⊔ b, by simp {contextual := tt}⟩) ⟨default α⟩
  ... = (⨅a, principal $ f '' {a' | a ≤ a'}) : by simp

lemma tendsto_finset_image_at_top_at_top {i : β → γ} {j : γ → β} (h : ∀x, j (i x) = x) :
  tendsto (λs:finset γ, s.image j) at_top at_top :=
tendsto_infi $ assume s, tendsto_infi' (s.image i) $ tendsto_principal_principal $
  assume t (ht : s.image i ⊆ t),
  calc s = (s.image i).image j : by simp [image_image, (∘), h]; exact finset.image_id.symm
    ... ⊆  t.image j : image_subset_image ht

end at_top

section is_sum
variables [add_comm_monoid α] [topological_space α] [topological_add_monoid α]

/-- Infinite sum on a topological monoid
The `at_top` filter on `finset α` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is still invariant under reordering, and a absolute
sum operator.

This is based on Mario Carneiro's infinite sum in Metamath.
-/
def is_sum (f : β → α) (a : α) : Prop := tendsto (λs:finset β, s.sum f) at_top (nhds a)

def has_sum (f : β → α) : Prop := ∃a, is_sum f a

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
s.induction_on (by simp [is_sum_zero]) (by simp [is_sum_add] {contextual := tt})

lemma has_sum_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, has_sum (f i)) :
  has_sum (λb, s.sum $ λi, f i b) :=
has_sum_spec $ is_sum_sum $ assume i hi, is_sum_tsum $ hf i hi

lemma is_sum_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : is_sum f (s.sum f) :=
tendsto_infi' s $ tendsto_cong tendsto_const_nhds $
  assume t (ht : s ⊆ t), show s.sum f = t.sum f, from sum_subset ht $ assume x _, hf _

lemma has_sum_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : has_sum f :=
has_sum_spec $ is_sum_sum_of_ne_finset_zero hf

lemma is_sum_of_iso {j : γ → β} {i : β → γ}
  (hf : is_sum f a) (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) : is_sum (f ∘ j) a :=
have ∀x y, j x = j y → x = y,
  from assume x y h,
  have i (j x) = i (j y), by rw [h],
  by rwa [h₁, h₁] at this,
have (λs:finset γ, s.sum (f ∘ j)) = (λs:finset β, s.sum f) ∘ (λs:finset γ, s.image j),
  from funext $ assume s, (sum_image $ assume x _ y _, this x y).symm,
show tendsto (λs:finset γ, s.sum (f ∘ j)) at_top (nhds a),
   by rw [this]; apply tendsto_compose (tendsto_finset_image_at_top_at_top h₂) hf

lemma is_sum_iff_is_sum_of_iso {j : γ → β} (i : β → γ)
  (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) :
  is_sum (f ∘ j) a ↔ is_sum f a :=
iff.intro
  (assume hfj,
    have is_sum ((f ∘ j) ∘ i) a, from is_sum_of_iso hfj h₂ h₁,
    by simp [(∘), h₂] at this; assumption)
  (assume hf, is_sum_of_iso hf h₁ h₂)

lemma is_sum_hom (g : α → γ) [add_comm_monoid γ] [topological_space γ] [topological_add_monoid γ]
  (h₁ : g 0 = 0) (h₂ : ∀x y, g (x + y) = g x + g y) (h₃ : continuous g) (hf : is_sum f a) :
  is_sum (g ∘ f) (g a) :=
have (λs:finset β, s.sum (g ∘ f)) = g ∘ (λs:finset β, s.sum f),
  from funext $ assume s, sum_hom g h₁ h₂,
show tendsto (λs:finset β, s.sum (g ∘ f)) at_top (nhds (g a)),
  by rw [this]; exact tendsto_compose hf (continuous_iff_tendsto.mp h₃ a)

lemma tendsto_sum_nat_of_is_sum {f : ℕ → α} (h : is_sum f a) :
  tendsto (λn:ℕ, (upto n).sum f) at_top (nhds a) :=
suffices map (λ (n : ℕ), sum (upto n) f) at_top ≤ map (λ (s : finset ℕ), sum s f) at_top,
  from le_trans this h,
assume s (hs : {t : finset ℕ | t.sum f ∈ s} ∈ at_top.sets),
let ⟨t, ht⟩ := mem_at_top_iff.mp hs, ⟨n, hn⟩ := @exists_nat_subset_upto t in
mem_at_top_iff.mpr ⟨n, assume n' hn', ht _ $ subset.trans hn $ upto_subset_upto_iff.mpr hn'⟩

lemma is_sum_sigma [regular_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α} {a : α}
  (hf : ∀b, is_sum (λc, f ⟨b, c⟩) (g b)) (ha : is_sum f a) : is_sum g a :=
assume s' hs',
let
  ⟨s, hs, hss', hsc⟩ := nhds_is_closed hs',
  ⟨u, hu⟩ := mem_at_top_iff.mp $ ha $ hs,
  fsts := u.image sigma.fst,
  snds := λb, u.bind (λp, (if h : p.1 = b then {cast (congr_arg γ h) p.2} else ∅ : finset (γ b)))
in
have u_subset : u ⊆ fsts.sigma snds,
  from subset_iff.mpr $ assume ⟨b, c⟩ hu,
  have hb : b ∈ fsts, from mem_image_iff.mpr ⟨_, hu, rfl⟩,
  have hc : c ∈ snds b, from mem_bind_iff.mpr ⟨_, hu, by simp; refl⟩,
  by simp [mem_sigma_iff, hb, hc] ,
mem_at_top_iff.mpr $ exists.intro fsts $ assume bs (hbs : fsts ⊆ bs),
  have h : ∀cs:(Πb, b ∈ bs → finset (γ b)),
      (⋂b (hb : b ∈ bs), (λp:Πb, finset (γ b), p b) ⁻¹' {cs' | cs b hb ⊆ cs' }) ∩
      (λp, bs.sum (λb, (p b).sum (λc, f ⟨b, c⟩))) ⁻¹' s ≠ ∅,
    from assume cs,
    let cs' := λb, (if h : b ∈ bs then cs b h else ∅) ∪ snds b in
    have sum_eq : bs.sum (λb, (cs' b).sum (λc, f ⟨b, c⟩)) = (bs.sigma cs').sum f,
      from sum_sigma.symm,
    have (bs.sigma cs').sum f ∈ s,
      from hu _ $ subset.trans u_subset $ sigma_mono hbs $
        assume b, @finset.subset_union_right (γ b) _ _ _,
    ne_empty_iff_exists_mem.mpr $ exists.intro cs' $
    by simp [sum_eq, this]; { intros b hb, simp [cs', hb, finset.subset_union_right] },
  have tendsto (λp:(Πb:β, finset (γ b)), bs.sum (λb, (p b).sum (λc, f ⟨b, c⟩)))
      (⨅b (h : b ∈ bs), at_top.vmap (λp, p b)) (nhds (bs.sum g)),
    from tendsto_sum $
      assume c hc, tendsto_infi' c $ tendsto_infi' hc $ tendsto_compose tendsto_vmap (hf c),
  have bs.sum g ∈ s,
    from mem_closure_of_tendsto this hsc $ forall_sets_neq_empty_iff_neq_bot.mp $
      by simp [mem_inf_sets, exists_imp_distrib, and_imp, forall_and_distrib',
               filter.mem_infi_sets_finset, mem_vmap, skolem, mem_at_top_iff];
      from
        assume s₁ s₂ s₃ hs₁ hs₃ p hs₂ p' hp cs hp',
        have (⋂b (h : b ∈ bs), (λp:(Πb, finset (γ b)), p b) ⁻¹' {cs' | cs b h ⊆ cs' }) ≤ (⨅b∈bs, p b),
          from infi_le_infi $ assume b, infi_le_infi $ assume hb,
            le_trans (preimage_mono $ hp' b hb) (hp b hb),
        neq_bot_of_le_neq_bot (h _) (le_trans (inter_subset_inter (le_trans this hs₂) hs₃) hs₁),
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
  by simp [image_subset_iff_subset_preimage]; exact hv)

lemma is_sum_iff_is_sum
  (h₁ : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ u'.sum g = v'.sum f)
  (h₂ : ∀v:finset β, ∃u:finset γ, ∀u', u ⊆ u' → ∃v', v ⊆ v' ∧ v'.sum f = u'.sum g) :
  is_sum f a ↔ is_sum g a :=
⟨is_sum_of_is_sum h₂, is_sum_of_is_sum h₁⟩

variables
  (i : Π{{c}}, g c ≠ 0 → β) (hi : ∀{{c}} (h : g c ≠ 0), f (i h) ≠ 0)
  (j : Π{{b}}, f b ≠ 0 → γ) (hj : ∀{{b}} (h : f b ≠ 0), g (j h) ≠ 0)
  (hji : ∀{{c}} (h : g c ≠ 0), j (hi h) = c)
  (hij : ∀{{b}} (h : f b ≠ 0), i (hj h) = b)
  (hgj : ∀{{b}} (h : f b ≠ 0), g (j h) = f b)
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
  assume v hv, exists.intro (u ∪ jj v) $ and.intro subset_union_left $
  have ∀c:γ, c ∈ u ∪ jj v → c ∉ jj v → g c = 0,
    from assume c hc hnc, classical.by_contradiction $ assume h : g c ≠ 0,
    have c ∈ u,
      from (mem_or_mem_of_mem_union hc).resolve_right hnc,
    have i h ∈ v,
      from mem_of_subset_of_mem hv $ by simp [mem_bind_iff]; existsi c; simp [h, this],
    have j (hi h) ∈ jj v,
      by simp [mem_bind_iff]; existsi i h; simp [h, hi, this],
    by rw [hji h] at this; exact hnc this,
  calc (u ∪ jj v).sum g = (jj v).sum g : (sum_subset subset_union_right this).symm
    ... = v.sum _ : sum_bind $ by intros x hx y hy hxy; by_cases f x = 0; by_cases f y = 0; simp [*]
    ... = v.sum f : sum_congr $ by intros x hx; by_cases f x = 0; simp [*]

lemma is_sum_iff_is_sum_of_ne_zero : is_sum f a ↔ is_sum g a :=
iff.intro
  (is_sum_of_is_sum_ne_zero j hj i hi hij hji $ assume b hb, by rw [←hgj (hi _), hji])
  (is_sum_of_is_sum_ne_zero i hi j hj hji hij hgj)

lemma has_sum_iff_has_sum_ne_zero : has_sum g ↔ has_sum f :=
exists_congr $
  assume a, is_sum_iff_is_sum_of_ne_zero j hj i hi hij hji $
    assume b hb, by rw [←hgj (hi _), hji]

end is_sum_iff_is_sum_of_iso_ne_zero

section tsum
variables [add_comm_monoid α] [topological_space α] [topological_add_monoid α] [t2_space α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma is_sum_unique : is_sum f a₁ → is_sum f a₂ → a₁ = a₂ := tendsto_nhds_unique at_top_ne_bot

lemma tsum_eq_is_sum (ha : is_sum f a) : (∑b, f b) = a := is_sum_unique (is_sum_tsum ⟨a, ha⟩) ha

@[simp] lemma tsum_zero : (∑b:β, 0:α) = 0 := tsum_eq_is_sum is_sum_zero

lemma tsum_add (hf : has_sum f) (hg : has_sum g) : (∑b, f b + g b) = (∑b, f b) + (∑b, g b) :=
tsum_eq_is_sum $ is_sum_add (is_sum_tsum hf) (is_sum_tsum hg)

lemma tsum_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, has_sum (f i)) :
  (∑b, s.sum (λi, f i b)) = s.sum (λi, ∑b, f i b) :=
tsum_eq_is_sum $ is_sum_sum $ assume i hi, is_sum_tsum $ hf i hi

lemma tsum_eq_sum {f : β → α} {s : finset β} (hf : ∀b∉s, f b = 0)  :
  (∑b, f b) = s.sum f :=
tsum_eq_is_sum $ is_sum_sum_of_ne_finset_zero hf

lemma tsum_eq_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0)  :
  (∑b, f b) = f b :=
calc (∑b, f b) = ({b} : finset β).sum f : tsum_eq_sum $ by simp [hf] {contextual := tt}
  ... = f b : by simp

lemma tsum_sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (h₁ : ∀b, has_sum (λc, f ⟨b, c⟩)) (h₂ : has_sum f) : (∑p, f p) = (∑b c, f ⟨b, c⟩):=
(tsum_eq_is_sum $ is_sum_sigma (assume b, is_sum_tsum $ h₁ b) $ is_sum_tsum h₂).symm

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
  (i : Π{{c}}, g c ≠ 0 → β) (hi : ∀{{c}} (h : g c ≠ 0), f (i h) ≠ 0)
  (j : Π{{b}}, f b ≠ 0 → γ) (hj : ∀{{b}} (h : f b ≠ 0), g (j h) ≠ 0)
  (hji : ∀{{c}} (h : g c ≠ 0), j (hi h) = c)
  (hij : ∀{{b}} (h : f b ≠ 0), i (hj h) = b)
  (hgj : ∀{{b}} (h : f b ≠ 0), g (j h) = f b) :
  (∑i, f i) = (∑j, g j) :=
tsum_eq_tsum_of_is_sum_iff_is_sum $ assume a, is_sum_iff_is_sum_of_ne_zero i hi j hj hji hij hgj

lemma tsum_eq_tsum_of_ne_zero_bij {f : β → α} {g : γ → α}
  (i : Π{{c}}, g c ≠ 0 → β)
  (h₁ : ∀{{c₁ c₂}} (h₁ : g c₁ ≠ 0) (h₂ : g c₂ ≠ 0), i h₁ = i h₂ → c₁ = c₂)
  (h₂ : ∀{{b}}, f b ≠ 0 → ∃c (h : g c ≠ 0), i h = b)
  (h₃ : ∀{{c}} (h : g c ≠ 0), f (i h) = g c) :
  (∑i, f i) = (∑j, g j) :=
have hi : ∀{{c}} (h : g c ≠ 0), f (i h) ≠ 0,
  from assume c h, by simp [h₃, h],
let j : Π{{b}}, f b ≠ 0 → γ := λb h, some $ h₂ h in
have hj : ∀{{b}} (h : f b ≠ 0), ∃(h : g (j h) ≠ 0), i h = b,
  from assume b h, some_spec $ h₂ h,
have hj₁ : ∀{{b}} (h : f b ≠ 0), g (j h) ≠ 0,
  from assume b h, let ⟨h₁, _⟩ := hj h in h₁,
have hj₂ : ∀{{b}} (h : f b ≠ 0), i (hj₁ h) = b,
  from assume b h, let ⟨h₁, h₂⟩ := hj h in h₂,
tsum_eq_tsum_of_ne_zero i hi j hj₁
  (assume c h, h₁ (hj₁ _) h $ hj₂ _) hj₂ (assume b h, by rw [←h₃ (hj₁ _), hj₂])

lemma tsum_eq_tsum_of_iso (j : γ → β) (i : β → γ)
  (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) :
  (∑c, f (j c)) = (∑b, f b) :=
tsum_eq_tsum_of_is_sum_iff_is_sum $ assume a, is_sum_iff_is_sum_of_iso i h₁ h₂

end tsum

section topological_group
variables [add_comm_group α] [topological_space α] [topological_add_group α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma is_sum_neg : is_sum f a → is_sum (λb, - f b) (- a) :=
is_sum_hom has_neg.neg (by simp) (by simp) continuous_neg'

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

lemma is_sum_mul_left : is_sum f a₁ → is_sum (λb, a₂ * f b) (a₂ * a₁) :=
is_sum_hom _ (by simp) (by simp [mul_add]) (continuous_mul continuous_const continuous_id)

lemma is_sum_mul_right (hf : is_sum f a₁) : is_sum (λb, f b * a₂) (a₁ * a₂) :=
@is_sum_hom _ _ _ _ _ _ f a₁ (λa, a * a₂) _ _ _
  (by simp) (by simp [add_mul]) (continuous_mul continuous_id continuous_const) hf

lemma has_sum_mul_left (hf : has_sum f) : has_sum (λb, a * f b) :=
has_sum_spec $ is_sum_mul_left $ is_sum_tsum hf

lemma has_sum_mul_right (hf : has_sum f) : has_sum (λb, f b * a) :=
has_sum_spec $ is_sum_mul_right $ is_sum_tsum hf

section tsum
variables [t2_space α]

lemma tsum_mul_left (hf : has_sum f) : (∑b, a * f b) = a * (∑b, f b) :=
tsum_eq_is_sum $ is_sum_mul_left $ is_sum_tsum hf

lemma tsum_mul_right (hf : has_sum f) : (∑b, f b * a) = (∑b, f b) * a :=
tsum_eq_is_sum $ is_sum_mul_right $ is_sum_tsum hf

end tsum

end topological_semiring

section order_topology
variables [ordered_comm_monoid α] [topological_space α] [ordered_topology α] [topological_add_monoid α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma is_sum_le (h : ∀b, f b ≤ g b) (hf : is_sum f a₁) (hg : is_sum g a₂) : a₁ ≤ a₂ :=
le_of_tendsto at_top_ne_bot hf hg $ univ_mem_sets' $ assume s, sum_le_sum' $ assume b _, h b

lemma tsum_le_tsum (h : ∀b, f b ≤ g b) (hf : has_sum f) (hg : has_sum g) : (∑b, f b) ≤ (∑b, g b) :=
is_sum_le h (is_sum_tsum hf) (is_sum_tsum hg)

end order_topology

section uniform_group
variables [add_comm_group α] [uniform_space α] [complete_space α] [uniform_add_group α]
variables {f g : β → α} {a a₁ a₂ : α}

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a` -/
lemma has_sum_of_has_sum_of_sub {f' : β → α} (hf : has_sum f) (h : ∀b, f' b = 0 ∨ f' b = f b) :
  has_sum f' :=
let ⟨a, hf⟩ := hf in
suffices cauchy (at_top.map (λs:finset β, s.sum f')),
  from complete_space.complete this,
⟨map_ne_bot at_top_ne_bot,
  assume s' hs',
  have ∃t∈(@uniformity α _).sets, ∀{a₁ a₂ a₃ a₄}, (a₁, a₂) ∈ t → (a₃, a₄) ∈ t → (a₁ - a₃, a₂ - a₄) ∈ s',
  begin
    have h : {p:(α×α)×(α×α)| (p.1.1 - p.1.2, p.2.1 - p.2.2) ∈ s'} ∈ (@uniformity (α × α) _).sets,
      from uniform_continuous_sub' hs',
    rw [uniformity_prod_eq_prod, mem_map, mem_prod_same_iff] at h,
    cases h with t ht, cases ht with ht h,
    exact ⟨t, ht, assume a₁ a₂ a₃ a₄ h₁ h₂, @h ((a₁, a₂), (a₃, a₄)) ⟨h₁, h₂⟩⟩
  end,
  let ⟨s, hs, hss'⟩ := this in
  have cauchy (at_top.map (λs:finset β, s.sum f)),
    from cauchy_downwards cauchy_nhds (map_ne_bot at_top_ne_bot) hf,
  have ∃t, ∀u₁ u₂:finset β, t ⊆ u₁ → t ⊆ u₂ → (u₁.sum f, u₂.sum f) ∈ s,
    by simp [cauchy_iff, mem_at_top_iff] at this;
    from let ⟨t, ht, u, hu⟩ := this s hs in
      ⟨u, assume u₁ u₂ h₁ h₂, ht $ prod_mk_mem_set_prod_eq.mpr ⟨hu _ h₁, hu _ h₂⟩⟩,
  let ⟨t, ht⟩ := this in
  let d := (t.filter (λb, f' b = 0)).sum f in
  have eq : ∀{u}, t ⊆ u → (t ∪ u.filter (λb, f' b ≠ 0)).sum f - d = u.sum f',
    from assume u hu,
    have t ∪ u.filter (λb, f' b ≠ 0) = t.filter (λb, f' b = 0) ∪ u.filter (λb, f' b ≠ 0),
      from ext $ assume b, by by_cases f' b = 0;
        simp [h, subset_iff.mp hu, iff_def, or_imp_distrib] {contextual := tt},
    calc (t ∪ u.filter (λb, f' b ≠ 0)).sum f - d =
        (t.filter (λb, f' b = 0) ∪ u.filter (λb, f' b ≠ 0)).sum f - d : by rw [this]
      ... = (d + (u.filter (λb, f' b ≠ 0)).sum f) - d :
        by rw [sum_union]; exact (ext $ assume b, by simp)
      ... = (u.filter (λb, f' b ≠ 0)).sum f :
        by simp
      ... = (u.filter (λb, f' b ≠ 0)).sum f' :
        sum_congr $ assume b, by have h := h b; cases h with h h; simp [*]
      ... = u.sum f' :
        by apply sum_subset; by simp [subset_iff, not_not] {contextual := tt},
  have ∀{u₁ u₂}, t ⊆ u₁ → t ⊆ u₂ → (u₁.sum f', u₂.sum f') ∈ s',
    from assume u₁ u₂ h₁ h₂,
    have ((t ∪ u₁.filter (λb, f' b ≠ 0)).sum f, (t ∪ u₂.filter (λb, f' b ≠ 0)).sum f) ∈ s,
      from ht _ _ subset_union_left subset_union_left,
    have ((t ∪ u₁.filter (λb, f' b ≠ 0)).sum f - d, (t ∪ u₂.filter (λb, f' b ≠ 0)).sum f - d) ∈ s',
      from hss' this $ refl_mem_uniformity hs,
    by rwa [eq h₁, eq h₂] at this,
  mem_prod_same_iff.mpr ⟨(λu:finset β, u.sum f') '' {u | t ⊆ u},
    image_mem_map $ mem_at_top t,
    assume ⟨a₁, a₂⟩ ⟨⟨t₁, h₁, eq₁⟩, ⟨t₂, h₂, eq₂⟩⟩, by simp at eq₁ eq₂; rw [←eq₁, ←eq₂]; exact this h₁ h₂⟩⟩

end uniform_group

section real

lemma has_sum_of_absolute_convergence {f : ℕ → ℝ}
  (hf : ∃r, tendsto (λn, (upto n).sum (λi, abs (f i))) at_top (nhds r)) : has_sum f :=
let f' := λs:finset ℕ, s.sum (λi, abs (f i)) in
suffices cauchy (map (λs:finset ℕ, s.sum f) at_top),
  from complete_space.complete this,
cauchy_iff.mpr $ and.intro (map_ne_bot at_top_ne_bot) $
assume s hs,
let ⟨ε, hε, hsε⟩ := mem_uniformity_dist.mp hs, ⟨r, hr⟩ := hf in
have hε' : {p : ℝ × ℝ | dist p.1 p.2 < ε / 2} ∈ (@uniformity ℝ _).sets,
  from mem_uniformity_dist.mpr ⟨ε / 2, div_pos_of_pos_of_pos hε two_pos, assume a b h, h⟩,
have cauchy (at_top.map $ λn, f' (upto n)),
  from cauchy_downwards cauchy_nhds (map_ne_bot at_top_ne_bot) hr,
have ∃n, ∀{n'}, n ≤ n' → dist (f' (upto n)) (f' (upto n')) < ε / 2,
  by simp [cauchy_iff, mem_at_top_iff] at this;
  from let ⟨t, ht, u, hu⟩ := this _ hε' in
    ⟨u, assume n' hn, ht $ prod_mk_mem_set_prod_eq.mpr ⟨hu _ (le_refl _), hu _ hn⟩⟩,
let ⟨n, hn⟩ := this in
have ∀{s}, upto n ⊆ s → abs ((s \ upto n).sum f) < ε / 2,
  from assume s hs,
  let ⟨n', hn'⟩ := @exists_nat_subset_upto s in
  have upto n ⊆ upto n', from subset.trans hs hn',
  have f'_nn : 0 ≤ f' (upto n' \ upto n), from zero_le_sum $ assume _ _, abs_nonneg _,
  calc abs ((s \ upto n).sum f) ≤ f' (s \ upto n) : abs_sum_le_sum_abs
    ... ≤ f' (upto n' \ upto n) : sum_le_sum_of_subset_of_nonneg
      (finset.sdiff_subset_sdiff hn' (finset.subset.refl _))
      (assume _ _ _, abs_nonneg _)
    ... = abs (f' (upto n' \ upto n)) : (abs_of_nonneg f'_nn).symm
    ... = abs (f' (upto n') - f' (upto n)) :
      by simp [f', (sum_sdiff ‹upto n ⊆ upto n'›).symm]
    ... = abs (f' (upto n) - f' (upto n')) : abs_sub _ _
    ... < ε / 2 : hn $ upto_subset_upto_iff.mp this,
have ∀{s t}, upto n ⊆ s → upto n ⊆ t → dist (s.sum f) (t.sum f) < ε,
  from assume s t hs ht,
  calc abs (s.sum f - t.sum f) = abs ((s \ upto n).sum f + - (t \ upto n).sum f) :
      by rw [←sum_sdiff hs, ←sum_sdiff ht]; simp
    ... ≤ abs ((s \ upto n).sum f) + abs ((t \ upto n).sum f) :
      le_trans (abs_add_le_abs_add_abs _ _) $ by rw [abs_neg]; exact le_refl _
    ... < ε / 2 + ε / 2 : add_lt_add (this hs) (this ht)
    ... = ε : by rw [←add_div, add_self_div_two],
⟨(λs:finset ℕ, s.sum f) '' {s | upto n ⊆ s}, image_mem_map $ mem_at_top (upto n),
  assume ⟨a, b⟩ ⟨⟨t, ht, ha⟩, ⟨s, hs, hb⟩⟩, by simp at ha hb; exact ha ▸ hb ▸ hsε _ _ (this ht hs)⟩

lemma is_sum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} {r : ℝ} (hf : ∀n, 0 ≤ f n) :
  is_sum f r ↔ tendsto (λn, (upto n).sum f) at_top (nhds r) :=
⟨tendsto_sum_nat_of_is_sum,
  assume hr,
  have tendsto (λn, (upto n).sum (λn, abs (f n))) at_top (nhds r),
    by simp [(λi, abs_of_nonneg (hf i)), hr],
  let ⟨p, h⟩ := has_sum_of_absolute_convergence ⟨r, this⟩ in
  have hp : tendsto (λn, (upto n).sum f) at_top (nhds p), from tendsto_sum_nat_of_is_sum h,
  have p = r, from tendsto_nhds_unique at_top_ne_bot hp hr,
  this ▸ h⟩

end real
