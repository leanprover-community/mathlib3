/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Theory of topological monoids.
-/
import topology.continuous_on
import group_theory.submonoid.basic
import algebra.group.prod

open classical set filter topological_space
open_locale classical topological_space big_operators

variables {α β M N : Type*}

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_continuous_add α`. -/
class has_continuous_add (M : Type*) [topological_space M] [has_add M] : Prop :=
(continuous_add : continuous (λ p : M × M, p.1 + p.2))

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `α`, for example, is obtained by requiring both the instances `monoid α`
and `has_continuous_mul α`. -/
@[to_additive]
class has_continuous_mul (M : Type*) [topological_space M] [has_mul M] : Prop :=
(continuous_mul : continuous (λ p : M × M, p.1 * p.2))

section has_continuous_mul

variables [topological_space M] [has_mul M] [has_continuous_mul M]

@[to_additive]
lemma continuous_mul : continuous (λp:M×M, p.1 * p.2) :=
has_continuous_mul.continuous_mul

@[to_additive, continuity]
lemma continuous.mul [topological_space α] {f : α → M} {g : α → M}
  (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
continuous_mul.comp (hf.prod_mk hg)

attribute [continuity] continuous.add

@[to_additive]
lemma continuous_mul_left (a : M) : continuous (λ b:M, a * b) :=
continuous_const.mul continuous_id

@[to_additive]
lemma continuous_mul_right (a : M) : continuous (λ b:M, b * a) :=
continuous_id.mul continuous_const

@[to_additive]
lemma continuous_on.mul [topological_space α] {f : α → M} {g : α → M} {s : set α}
  (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λx, f x * g x) s :=
(continuous_mul.comp_continuous_on (hf.prod hg) : _)

@[to_additive]
lemma tendsto_mul {a b : M} : tendsto (λp:M×M, p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
continuous_iff_continuous_at.mp has_continuous_mul.continuous_mul (a, b)

@[to_additive]
lemma filter.tendsto.mul {f : α → M} {g : α → M} {x : filter α} {a b : M}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, f x * g x) x (𝓝 (a * b)) :=
tendsto_mul.comp (hf.prod_mk_nhds hg)

@[to_additive]
lemma continuous_at.mul [topological_space α] {f : α → M} {g : α → M} {x : α}
  (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λx, f x * g x) x :=
hf.mul hg

@[to_additive]
lemma continuous_within_at.mul [topological_space α] {f : α → M} {g : α → M} {s : set α} {x : α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (λx, f x * g x) s x :=
hf.mul hg

@[to_additive]
instance [topological_space N] [has_mul N] [has_continuous_mul N] : has_continuous_mul (M × N) :=
⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk
 ((continuous_snd.comp continuous_fst).mul (continuous_snd.comp continuous_snd))⟩

end has_continuous_mul

section has_continuous_mul

variables [topological_space M] [monoid M] [has_continuous_mul M]

@[to_additive]
lemma tendsto_list_prod {f : β → α → M} {x : filter α} {a : β → M} :
  ∀l:list β, (∀c∈l, tendsto (f c) x (𝓝 (a c))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (𝓝 ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp only [list.map_cons, list.prod_cons],
    exact (h f (list.mem_cons_self _ _)).mul
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

@[to_additive]
lemma continuous_list_prod [topological_space α] {f : β → α → M} (l : list β)
  (h : ∀c∈l, continuous (f c)) :
  continuous (λa, (l.map (λc, f c a)).prod) :=
continuous_iff_continuous_at.2 $ assume x, tendsto_list_prod l $ assume c hc,
  continuous_iff_continuous_at.1 (h c hc) x

-- @[to_additive continuous_smul]
@[continuity]
lemma continuous_pow : ∀ n : ℕ, continuous (λ a : M, a ^ n)
| 0 := by simpa using continuous_const
| (k+1) := show continuous (λ (a : M), a * a ^ k), from continuous_id.mul (continuous_pow _)

@[continuity]
lemma continuous.pow {f : α → M} [topological_space α] (h : continuous f) (n : ℕ) :
  continuous (λ b, (f b) ^ n) :=
continuous.comp (continuous_pow n) h

end has_continuous_mul

section

variables [topological_space M] [comm_monoid M]

@[to_additive]
lemma submonoid.mem_nhds_one (S : submonoid M) (oS : is_open (S : set M)) :
  (S : set M) ∈ 𝓝 (1 : M) :=
mem_nhds_sets oS S.one_mem

variable [has_continuous_mul M]

@[to_additive]
lemma tendsto_multiset_prod {f : β → α → M} {x : filter α} {a : β → M} (s : multiset β) :
  (∀c∈s, tendsto (f c) x (𝓝 (a c))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (𝓝 ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simp, exact tendsto_list_prod l }

@[to_additive]
lemma tendsto_finset_prod {f : β → α → M} {x : filter α} {a : β → M} (s : finset β) :
  (∀c∈s, tendsto (f c) x (𝓝 (a c))) → tendsto (λb, ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
tendsto_multiset_prod _

@[to_additive, continuity]
lemma continuous_multiset_prod [topological_space α] {f : β → α → M} (s : multiset β) :
  (∀c∈s, continuous (f c)) → continuous (λa, (s.map (λc, f c a)).prod) :=
by { rcases s with ⟨l⟩, simp, exact continuous_list_prod l }

attribute [continuity] continuous_multiset_sum

@[to_additive, continuity]
lemma continuous_finset_prod [topological_space α] {f : β → α → M} (s : finset β) :
  (∀c∈s, continuous (f c)) → continuous (λa, ∏ c in s, f c a) :=
continuous_multiset_prod _

attribute [continuity] continuous_finset_sum

end
