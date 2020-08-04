/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Theory of topological monoids.
-/
import topology.continuous_on
import group_theory.submonoid.basic
import algebra.group.prod
import topology.homeomorph

open classical set filter topological_space opposite
open_locale classical topological_space big_operators

variables {α : Type*} {β : Type*} {γ : Type*}

instance [m : topological_space α] : topological_space αᵒᵖ := m.coinduced op

lemma opposite_eq_induced [m : topological_space α] : opposite.topological_space = m.induced unop :=
(induced_eq_coinduced equiv_to_opposite).symm

lemma continuous_op [topological_space α] : continuous (op : α → αᵒᵖ) := λ _ h, h
lemma continuous_unop [topological_space α] : continuous (unop : αᵒᵖ → α) := λ _ h, h

/-- The map `α ≃ αᵒᵖ` is a homeomorphism. -/
def homeomorphm_to_opposite [topological_space α] : α ≃ₜ αᵒᵖ :=
{ continuous_to_fun := continuous_op,
  continuous_inv_fun := continuous_unop,
  ..equiv_to_opposite }

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_continuous_add α`. -/
class has_continuous_add (α : Type*) [topological_space α] [has_add α] : Prop :=
(continuous_add : continuous (λp:α×α, p.1 + p.2))

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `α`, for example, is obtained by requiring both the instances `monoid α` and
`has_continuous_mul α`. -/
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
lemma filter.tendsto.mul {f : β → α} {g : β → α} {F : filter β} {a b : α}
  (hf : tendsto f F (𝓝 a)) (hg : tendsto g F (𝓝 b)) :
  tendsto (λx, f x * g x) F (𝓝 (a * b)) :=
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

instance : has_continuous_mul αᵒᵖ :=
{ continuous_mul := ((continuous_op.comp continuous_mul).comp continuous_swap).comp
  (continuous_unop.prod_map continuous_unop) }

end has_continuous_mul

section has_continuous_mul

variables [topological_space α] [monoid α] [has_continuous_mul α]

@[to_additive]
lemma tendsto_list_prod {f : γ → β → α} {F : filter β} {g : γ → α} :
  ∀l:list γ, (∀c∈l, tendsto (f c) F (𝓝 (g c))) →
    tendsto (λb, (l.map (λc, f c b)).prod) F (𝓝 ((l.map g).prod))
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
lemma tendsto_multiset_prod {f : γ → β → α} {F : filter β} {a : γ → α} (s : multiset γ) :
  (∀c∈s, tendsto (f c) F (𝓝 (a c))) →
    tendsto (λb, (s.map (λc, f c b)).prod) F (𝓝 ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simp, exact tendsto_list_prod l }

@[to_additive]
lemma tendsto_finset_prod {f : γ → β → α} {F : filter β} {a : γ → α} (s : finset γ) :
  (∀c∈s, tendsto (f c) F (𝓝 (a c))) → tendsto (λb, ∏ c in s, f c b) F (𝓝 (∏ c in s, a c)) :=
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
