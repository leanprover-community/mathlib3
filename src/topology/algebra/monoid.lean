/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.continuous_on
import group_theory.submonoid.basic
import algebra.group.prod
import algebra.pointwise

/-!
# Theory of topological monoids

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in the definitions.
-/

open classical set filter topological_space
open_locale classical topological_space big_operators

variables {α : Type*} {β : Type*} {γ : Type*}

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_continuous_add α`. -/
class has_continuous_add (α : Type*) [topological_space α] [has_add α] : Prop :=
(continuous_add : continuous (λp:α×α, p.1 + p.2))

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `α`, for example, is obtained by requiring both the instances `monoid α`
and `has_continuous_mul α`. -/
@[to_additive]
class has_continuous_mul (α : Type*) [topological_space α] [has_mul α] : Prop :=
(continuous_mul : continuous (λp:α×α, p.1 * p.2))

section has_continuous_mul

variables [topological_space α] [has_mul α] [has_continuous_mul α]

@[to_additive]
lemma continuous_mul : continuous (λp:α×α, p.1 * p.2) :=
has_continuous_mul.continuous_mul

@[to_additive, continuity]
lemma continuous.mul [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
continuous_mul.comp (hf.prod_mk hg)

attribute [continuity] continuous.add

@[to_additive]
lemma continuous_mul_left (a : α) : continuous (λ b:α, a * b) :=
continuous_const.mul continuous_id

@[to_additive]
lemma continuous_mul_right (a : α) : continuous (λ b:α, b * a) :=
continuous_id.mul continuous_const

@[to_additive]
lemma continuous_on.mul [topological_space β] {f : β → α} {g : β → α} {s : set β}
  (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λx, f x * g x) s :=
(continuous_mul.comp_continuous_on (hf.prod hg) : _)

@[to_additive]
lemma tendsto_mul {a b : α} : tendsto (λp:α×α, p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
continuous_iff_continuous_at.mp has_continuous_mul.continuous_mul (a, b)

@[to_additive]
lemma filter.tendsto.mul {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, f x * g x) x (𝓝 (a * b)) :=
tendsto_mul.comp (hf.prod_mk_nhds hg)

@[to_additive]
lemma continuous_at.mul [topological_space β] {f : β → α} {g : β → α} {x : β}
  (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λx, f x * g x) x :=
hf.mul hg

@[to_additive]
lemma continuous_within_at.mul [topological_space β] {f : β → α} {g : β → α} {s : set β} {x : β}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (λx, f x * g x) s x :=
hf.mul hg

@[to_additive]
instance [topological_space β] [has_mul β] [has_continuous_mul β] : has_continuous_mul (α × β) :=
⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk
 ((continuous_snd.comp continuous_fst).mul (continuous_snd.comp continuous_snd))⟩

end has_continuous_mul

section has_continuous_mul

variables [topological_space α] [monoid α] [has_continuous_mul α]

@[to_additive exists_nhds_half]
lemma exists_nhds_split {s : set α} (hs : s ∈ 𝓝 (1 : α)) :
  ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧ ∀ (v ∈ V) (w ∈ V), v * w ∈ s :=
have ((λa:α×α, a.1 * a.2) ⁻¹' s) ∈ 𝓝 ((1, 1) : α × α),
  from tendsto_mul (by simpa only [one_mul] using hs),
by simpa only [prod_subset_iff] using exists_nhds_square this

@[to_additive exists_nhds_quarter]
lemma exists_nhds_split4 {u : set α} (hu : u ∈ 𝓝 (1 : α)) :
  ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧
    ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
begin
  rcases exists_nhds_split hu with ⟨W, W_open, W1, h⟩,
  rcases exists_nhds_split (mem_nhds_sets W_open W1) with ⟨V, V_open, V1, h'⟩,
  use [V, V_open, V1],
  intros v w s t v_in w_in s_in t_in,
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)
end

/-- Given a open neighborhood `U` of `1` there is a open neighborhood `V` of `1`
  such that `VV ⊆ U`. -/
@[to_additive "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`
  such that `V + V ⊆ U`."]
lemma exists_open_mem_mul_subset {U : set α} (hU : U ∈ 𝓝 (1 : α)) :
  ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧ V * V ⊆ U :=
begin
  rcases exists_nhds_split hU with ⟨V, Vo, V1, hV⟩,
  use [V, Vo, V1],
  rintros _ ⟨x, y, hx, hy, rfl⟩,
  exact hV _ hx _ hy
end

@[to_additive]
lemma tendsto_list_prod {f : γ → β → α} {x : filter β} {a : γ → α} :
  ∀l:list γ, (∀c∈l, tendsto (f c) x (𝓝 (a c))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (𝓝 ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp only [list.map_cons, list.prod_cons],
    exact (h f (list.mem_cons_self _ _)).mul
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

@[to_additive]
lemma continuous_list_prod [topological_space β] {f : γ → β → α} (l : list γ)
  (h : ∀c∈l, continuous (f c)) :
  continuous (λa, (l.map (λc, f c a)).prod) :=
continuous_iff_continuous_at.2 $ assume x, tendsto_list_prod l $ assume c hc,
  continuous_iff_continuous_at.1 (h c hc) x

-- @[to_additive continuous_smul]
@[continuity]
lemma continuous_pow : ∀ n : ℕ, continuous (λ a : α, a ^ n)
| 0 := by simpa using continuous_const
| (k+1) := show continuous (λ (a : α), a * a ^ k), from continuous_id.mul (continuous_pow _)

@[continuity]
lemma continuous.pow {f : β → α} [topological_space β] (h : continuous f) (n : ℕ) :
  continuous (λ b, (f b) ^ n) :=
continuous.comp (continuous_pow n) h

end has_continuous_mul

section

variables [topological_space α] [comm_monoid α]

@[to_additive]
lemma submonoid.mem_nhds_one (β : submonoid α) (oβ : is_open (β : set α)) :
  (β : set α) ∈ 𝓝 (1 : α) :=
mem_nhds_sets_iff.2 ⟨β, (by refl), oβ, β.one_mem⟩

variable [has_continuous_mul α]

@[to_additive]
lemma tendsto_multiset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : multiset γ) :
  (∀c∈s, tendsto (f c) x (𝓝 (a c))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (𝓝 ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simp, exact tendsto_list_prod l }

@[to_additive]
lemma tendsto_finset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : finset γ) :
  (∀c∈s, tendsto (f c) x (𝓝 (a c))) → tendsto (λb, ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
tendsto_multiset_prod _

@[to_additive, continuity]
lemma continuous_multiset_prod [topological_space β] {f : γ → β → α} (s : multiset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, (s.map (λc, f c a)).prod) :=
by { rcases s with ⟨l⟩, simp, exact continuous_list_prod l }

attribute [continuity] continuous_multiset_sum

@[to_additive, continuity]
lemma continuous_finset_prod [topological_space β] {f : γ → β → α} (s : finset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, ∏ c in s, f c a) :=
continuous_multiset_prod _

attribute [continuity] continuous_finset_sum

end
