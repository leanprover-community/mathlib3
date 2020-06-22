/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Theory of topological monoids.

TODO: generalize `topological_monoid` and `topological_add_monoid` to semigroups, or add a type class
`topological_operator α (*)`.
-/
import topology.continuous_on
import algebra.pi_instances

open classical set filter topological_space
open_locale classical topological_space big_operators

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section topological_monoid

/-- A topological monoid is a monoid in which the multiplication is continuous as a function
`α × α → α`. -/
class topological_monoid (α : Type u) [topological_space α] [monoid α] : Prop :=
(continuous_mul : continuous (λp:α×α, p.1 * p.2))

/-- A topological (additive) monoid is a monoid in which the addition is
  continuous as a function `α × α → α`. -/
class topological_add_monoid (α : Type u) [topological_space α] [add_monoid α] : Prop :=
(continuous_add : continuous (λp:α×α, p.1 + p.2))

attribute [to_additive topological_add_monoid] topological_monoid

section
variables [topological_space α] [monoid α] [topological_monoid α]

@[to_additive]
lemma continuous_mul : continuous (λp:α×α, p.1 * p.2) :=
topological_monoid.continuous_mul

@[to_additive]
lemma continuous.mul [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
continuous_mul.comp (hf.prod_mk hg)

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

-- @[to_additive continuous_smul]
lemma continuous_pow : ∀ n : ℕ, continuous (λ a : α, a ^ n)
| 0 := by simpa using continuous_const
| (k+1) := show continuous (λ (a : α), a * a ^ k), from continuous_id.mul (continuous_pow _)

@[to_additive]
lemma tendsto_mul {a b : α} : tendsto (λp:α×α, p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
continuous_iff_continuous_at.mp topological_monoid.continuous_mul (a, b)

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

@[to_additive topological_add_monoid]
instance [topological_space β] [monoid β] [topological_monoid β] : topological_monoid (α × β) :=
⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk
 ((continuous_snd.comp continuous_fst).mul (continuous_snd.comp continuous_snd))⟩

attribute [instance] prod.topological_add_monoid

end

section
variables [topological_space α] [comm_monoid α]

@[to_additive]
lemma is_submonoid.mem_nhds_one (β : set α) [is_submonoid β] (oβ : is_open β) :
  β ∈ 𝓝 (1 : α) :=
mem_nhds_sets_iff.2 ⟨β, (by refl), oβ, is_submonoid.one_mem⟩

variable [topological_monoid α]

@[to_additive]
lemma tendsto_multiset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : multiset γ) :
  (∀c∈s, tendsto (f c) x (𝓝 (a c))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (𝓝 ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simp, exact tendsto_list_prod l }

@[to_additive]
lemma tendsto_finset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : finset γ) :
  (∀c∈s, tendsto (f c) x (𝓝 (a c))) → tendsto (λb, ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
tendsto_multiset_prod _

@[to_additive]
lemma continuous_multiset_prod [topological_space β] {f : γ → β → α} (s : multiset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, (s.map (λc, f c a)).prod) :=
by { rcases s with ⟨l⟩, simp, exact continuous_list_prod l }

@[to_additive]
lemma continuous_finset_prod [topological_space β] {f : γ → β → α} (s : finset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, ∏ c in s, f c a) :=
continuous_multiset_prod _

end

end topological_monoid
