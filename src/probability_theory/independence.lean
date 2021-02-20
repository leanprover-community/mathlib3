/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne
-/
import measure_theory.measure_space
import algebra.big_operators.intervals
import data.finset.intervals

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space α` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* TODO: `Indep_of_Indep_sets`: if π-systems are independent as sets of sets, then the
measurable space structures they generate are independent.
* `indep_of_indep_sets`: variant with two π-systems.

## Implementation notes

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set α)`.
Three other independence notions are defined using `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space α`,
* `Indep_set`: independence of a family of sets `s : ι → set α`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), α → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space α]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

open measure_theory measurable_space
open_locale big_operators classical

--- Move to measurable_space. ----
lemma supr_eq_generate_from {α} {β:Type*} {Mf:β → measurable_space α}:
  (supr Mf) = measurable_space.generate_from (⋃ (b:β), (Mf b).measurable_set') := begin
  apply le_antisymm,
  { apply @supr_le (measurable_space α) _ _,
    intros b, intros s h, 
    apply measurable_space.measurable_set_generate_from,
    simp,
    apply exists.intro b,
    apply h },
  { apply measurable_space.generate_from_le,
    intros s h_s,
    apply (@measurable_space.measurable_set_supr α β Mf s).2,
    apply measurable_space.generate_measurable.basic,
    simp, simp at h_s,  apply h_s  },
end

/- TODO: Move to pi_system.lean. Consider changing definition of is_pi_system, because
   it is difficult to keep saying that intersections don't count if they are
   disjoint -/
lemma is_pi_system.singleton {α} (S : set α) : is_pi_system ({S} : set (set α)) :=
begin
  intros s t h_s h_t h_ne,
  rw [set.mem_singleton_iff.1 h_s, set.mem_singleton_iff.1 h_t, set.inter_self,
      set.mem_singleton_iff],
end

lemma is_pi_system_finite_Inter {α} (g : set (set α)) (h_pi : is_pi_system g) 
  (m : ℕ) (f : fin m.succ → set α) (h_f : ∀ i, f i ∈ g) (h_nonempty : (⋂ i, f i).nonempty) :
  ((⋂ i, f i) ∈ g) := begin
  induction m,
  { have h_eq : set.Inter f = (f 0), 
    { ext a, simp, split; intros h_eq_1, 
      apply h_eq_1 0,
      intros i, cases i,
      cases i_val,
      apply h_eq_1,
      rw nat.succ_lt_succ_iff at i_property,
      apply false.elim (nat.not_lt_zero _ i_property) },
   rw h_eq,
   apply h_f },
 { have h_eq : (⋂ (i : fin m_n.succ.succ), f i) = f 0 ∩ (⋂ (i : fin m_n.succ), f (i.succ)),
   { ext a, split; intros h_eq_1; simp at h_eq_1; simp [h_eq_1],
     intros i,  cases (decidable.em (i = 0)),
     { subst i, apply h_eq_1.left },
     { have h_eq_2 := h_eq_1.right (i.pred h), simp at h_eq_2, apply h_eq_2 } },
   rw h_eq,
   apply h_pi,
   apply h_f,
   apply m_ih,
   { intros i, apply h_f },
   by_contradiction h_contra,
   apply h_nonempty.ne_empty,
   rw h_eq,
   rw set.not_nonempty_iff_eq_empty.1 h_contra,
   simp,
   rw ← h_eq,
   apply h_nonempty },
end

/-
inductive generate_pi_system' {α} (g : set (set α)) : (set α) → Prop
| base {s : set α} (h_s : s ∈ g) : generate_pi_system' s
| inter {s t : set α} (h_s : generate_pi_system' s)  (h_t : generate_pi_system' t) 
  (h_nonempty : (s ∩ t).nonempty) : generate_pi_system' (s ∩ t)

lemma is_pi_system_generate_pi_system' {α} (g : set (set α)) :
  is_pi_system (generate_pi_system' g) :=
  λ s t h_s h_t h_nonempty, generate_pi_system'.inter h_s h_t h_nonempty


lemma exists_fin_intro {α} {β:Type*} (g : set (set α)) [F:fintype β]
  [N:nonempty β] (f : β → set α) (h : ∀ b, f b ∈ g) 
: ∃ (m : ℕ) (f' : fin m.succ → set α), (∀ i, f' i ∈ g) ∧ ((⋂ i, f' i) = (⋂ i, f i)) := begin
  have h5 := classical.choice (nonempty_of_trunc (fintype.equiv_fin β)),
  apply exists.intro ((fintype.card β).pred),
  have h6 : (fintype.card β).pred.succ = (fintype.card β),
  { apply nat.succ_pred_eq_of_pos, rw ← fintype.card_pos_iff at N, apply N },
  rw [h6],
  apply exists.intro (f ∘ h5.inv_fun),
    split,
    { intros i, apply h, },
    { ext a, split; intros h7; simp at h7; simp [h7]; intros i,
      have h8 := h7 (h5.to_fun i),
      simp at h8, apply h8 },  
end

lemma generate_pi_system_elim {α} (g : set (set α)) (s : set α)
  (h : generate_pi_system' g s) : (s ∈ g ∧ s = ∅) ∨
  (s.nonempty ∧ ∃ (m : ℕ) (f : fin m.succ → set α), (∀ i, f i ∈ g) ∧ (s=(⋂ i, f i))) :=
begin
  induction h with s' h_s' s' t' h_gen_s' h_gen_t' h_nonempty h_s' h_t',
  cases (set.eq_empty_or_nonempty s') with h_empty h_nonempty,
  { left, apply and.intro h_s' h_empty },
  { right, apply and.intro h_nonempty,
    use [0, (λ _, s')], apply and.intro (λ _, h_s'),
    ext a, simp },
  right,
  apply and.intro h_nonempty, 
  cases h_s',
  { apply false.elim (h_nonempty.left.ne_empty h_s'.right), },
  cases h_t',
  { apply false.elim (h_nonempty.right.ne_empty h_t'.right), },
  rcases h_s' with ⟨h_s'_nonempty, ⟨m_s', ⟨f_s', h_s'⟩⟩⟩,
  rcases h_t' with ⟨h_t'_nonempty, ⟨m_t', ⟨f_t', h_t'⟩⟩⟩,
  let f : sum (fin m_s'.succ) (fin m_t'.succ) → set α :=
    (λ x, match x with
    | (sum.inl i) := f_s' i
    | (sum.inr i) := f_t' i
    end),
  begin
    have h_f'' := exists_fin_intro g f _,
    rcases h_f'' with ⟨m'', ⟨f'', h_f''⟩⟩,
    use [m'', f''],
    apply and.intro h_f''.left,
    rw h_f''.right,
    rw h_s'.right,
    rw h_t'.right,
    { ext a, simp },
    { intros b, cases b; simp [h_s'.left, h_t'.left] },
  end
end

lemma sub_generate_pi_system {α} (g : set (set α)) :
  g ⊆ generate_pi_system' g :=
begin
  rw set.subset_def,
  apply generate_pi_system'.base,
end 
-/

def generate_pi_system {α} (g : set (set α)) : set (set α) :=
  g ∪ {s|s.nonempty ∧ ∃ (m : ℕ) (f : fin m.succ → set α), (∀ i, f i ∈ g) ∧ (s=(⋂ i, f i)) }

lemma generate_pi_system_intro {α} {β : Type*} [fintype β] [N : nonempty β] 
  (g : set (set α)) (f : β → set α)
  (h_f_in : ∀ b, f b ∈ g) (h_nonempty : (set.Inter f).nonempty) :
  set.Inter f ∈ generate_pi_system g :=
begin
  classical,
  simp [generate_pi_system, h_nonempty],
  right,
  have h5 := classical.choice (nonempty_of_trunc (fintype.equiv_fin β)),
  apply exists.intro ((fintype.card β).pred),
  have h6 : (fintype.card β).pred.succ = (fintype.card β),
  { apply nat.succ_pred_eq_of_pos, rw ← fintype.card_pos_iff at N, apply N },
  rw [h6],
  apply exists.intro (f ∘ h5.inv_fun),
    split,
    { intros i, apply h_f_in, },
    { ext a, split; intros h7; simp at h7; simp [h7]; intros i,
      have h8 := h7 (h5.to_fun i),
      simp at h8, apply h8 },
end 

lemma sub_generate_pi_system {α} (g : set (set α)) :
  g ⊆ generate_pi_system g :=
begin
  unfold generate_pi_system,
  simp,
end 

lemma generate_pi_system_elim {α} (g : set (set α)) (s : set α)
  (h_gen : s ∈ generate_pi_system g) : (s ∈ g ∧ s = ∅) ∨
  (s.nonempty ∧ ∃ (m : ℕ) (f : fin m.succ → set α), (∀ i, f i ∈ g) ∧ (s=(⋂ i, f i))) :=
begin
  cases h_gen,
  cases (set.eq_empty_or_nonempty s) with h_empty h_nonempty,
  left,
  apply and.intro h_gen h_empty,
  right,
  apply and.intro h_nonempty,
  apply exists.intro 1,
  apply exists.intro (λ _, s),
  split,
  { intros i, simp, apply h_gen },
  ext a,
  { simp },
  simp at h_gen,
  right,
  simp [h_gen],
end

lemma is_pi_system_generate_pi_system {α} (g : set (set α)) :
  is_pi_system (generate_pi_system g) := begin
  unfold is_pi_system,
  intros s t h_s h_t h_nonempty,
  cases (generate_pi_system_elim _ _ h_s),
  { cases h, subst s,
    rw set.empty_inter,
    apply sub_generate_pi_system, apply h_left },
  cases (generate_pi_system_elim _ _ h_t),
  { cases h_1 with h_1 h_2, subst t,
    rw set.inter_empty,
    apply sub_generate_pi_system, apply h_1 },
  cases h with h_s_nonempty h_s_2,
  cases h_s_2 with m_s h_s_2,
  cases h_s_2 with f_s h_s_2,
  cases h_s_2 with h_f_s_in h_s_def,
  cases h_1 with h_t_nonempty h_t_2,
  cases h_t_2 with m_t h_t_2,
  cases h_t_2 with f_t h_t_2,
  cases h_t_2 with h_f_t_in h_t_def,
  have h2:s ∩ t = ⋂ (b:sum (fin m_s.succ) (fin m_t.succ)), @sum.cases_on _ _ (λ _, (set α)) b f_s f_t,
  { rw h_s_def, rw h_t_def,
    ext a, split; intros h2_1; simp at h2_1; simp [h2_1] },
  rw h2,
  apply generate_pi_system_intro, 
  { intros b, cases b,
    { simp [h_f_s_in] },
    { simp [h_f_t_in] } },
  { rw ← h2, apply h_nonempty },
end

lemma generate_pi_system_subset {α} {g t:set (set α)} (h_s:is_pi_system t)
  (h_sub:g ⊆ t):
  generate_pi_system g ⊆ t := begin
  rw set.subset_def,
  rw generate_pi_system,
  intros x h_x,
  simp at h_x,
  cases h_x,
  apply h_sub h_x,
  cases h_x with h_x_nonempty h_x,
  cases h_x with m h_x,
  cases h_x with f h_x,
  cases h_x with h_f h_x,
  subst x,
  apply is_pi_system_finite_Inter t h_s,
  { intros i, apply h_sub, apply h_f },
  { simp, apply h_x_nonempty },
end

lemma generate_pi_system_eq {α} {g:set (set α)} (h_pi:is_pi_system g)
  :
  generate_pi_system g = g := begin
  apply le_antisymm,
  apply generate_pi_system_subset,
  apply h_pi,
  apply set.subset.refl,
  apply sub_generate_pi_system,
end

lemma is_pi_system_intro {α} {β:Type*} [fintype β] [N:nonempty β] 
  {g:set (set α)} (h_pi:is_pi_system g) (f:β → set α)
  (h_f_in:∀ b, f b ∈ g) (h_nonempty:(set.Inter f).nonempty):
  set.Inter f ∈ g :=
begin
  rw ← generate_pi_system_eq h_pi,
  apply generate_pi_system_intro,
  apply h_f_in,
  apply h_nonempty,
end

lemma generate_pi_system_measurable_set {α} [M:measurable_space α] {g:set (set α)} 
  (h_meas_g:∀ s ∈ g, measurable_set s)
  (t:set α)
  (h_in_pi:generate_pi_system g t):measurable_set t :=
begin
  cases h_in_pi,
  { apply h_meas_g _ h_in_pi },
  { simp at h_in_pi, cases h_in_pi with h_t_nonempty h_t,
    cases h_t with m h_t,
    cases h_t with f h_t,
    cases h_t with h_f_in_g h_t_def,
    subst t,
    apply measurable_set.Inter,
    intros b, apply h_meas_g, 
    apply h_f_in_g },
end

lemma generate_from_measurable_set_of_generate_pi_system {α} {g:set (set α)} (t:set α):generate_pi_system g t →
  (measurable_space.generate_from g).measurable_set' t := begin
  apply generate_pi_system_measurable_set,
  intros s h_s_in_g,
  apply measurable_space.measurable_set_generate_from h_s_in_g,
end

lemma generate_from_generate_pi_system_eq {α} {g:set (set α)}:
  (measurable_space.generate_from (generate_pi_system g)) =
  (measurable_space.generate_from g) := begin
  apply le_antisymm;apply measurable_space.generate_from_le,
  { intros t h_t,
    apply generate_from_measurable_set_of_generate_pi_system,
    apply h_t },
  { intros t h_t, apply measurable_space.measurable_set_generate_from, 
    rw generate_pi_system,
    apply set.mem_union_left _ h_t },
end

lemma set.nonempty_of_nonempty_subset {α} (T V:set α)
  (h_nonempty_T:T.nonempty) (h_sub:T ⊆ V):V.nonempty := begin
  rw set.nonempty_def,
  rw set.nonempty_def at h_nonempty_T,
  cases h_nonempty_T with x h_nonempty_T,
  apply exists.intro x,
  apply h_sub,
  apply h_nonempty_T,
end

lemma is_pi_system_union {α} {β:Type*} {g:β → (set (set α))}
  (h_pi:∀ b:β, is_pi_system (g b))
  (h_nonempty:∀ b:β, (g b).nonempty)
  (t:set α)
  (h_t:t ∈ generate_pi_system (⋃ (b:β), g b)):
  (∃ (T:finset β) (f:β → set α), (t = ⋂ b ∈ T, f b) ∧ (∀ (b:β), f b ∈ (g b))) :=
begin
  classical,
  cases (generate_pi_system_elim _ _ h_t) with h_t_empty h_t_union,
  { cases h_t_empty with h_t_in h_t_empty,
    cases h_t_in with g' h_t_in,
    cases h_t_in with h_t_H h_t_in,
    cases h_t_H with b h_b_def,
    simp at h_b_def,
    subst g',
    apply exists.intro {b},
    have h_f:∀ b':β, ∃ (s:set α), (s ∈ g b') ∧ (b' = b → s = t),
    { intros b', cases classical.em (b' = b) with h_b'_eq_b h_b'_ne_b,
      { subst b', apply exists.intro t, simp [h_t_in] },
      { cases (set.nonempty_def.1 (h_nonempty b')) with s h_s,
        apply exists.intro s, simp [h_s, h_b'_ne_b] } },
    rw classical.skolem at h_f,
    cases h_f with f h_f,
    have h_f_b_eq_t:f b = t,
    { apply (h_f b).right, refl },
    apply exists.intro f,
    split,
    { ext a, split; intros h1,
      { simp [h1, h_f], intros b' h_b',
        rw @finset.mem_singleton β b b' at h_b',
        subst b', rw h_f_b_eq_t, apply h1 },
      simp at h1,  rw h_f_b_eq_t at h1, apply h1 },
    { intros b', apply (h_f b').left } },
  { cases h_t_union with h_t_nonempty h_t_union,
    cases h_t_union with m h_t_union,
    cases h_t_union with f h_t_union,
    cases h_t_union with h_f_def h_t_def,
    have h_f':∀ (i:fin m.succ), ∃ (b:β), f i ∈ g b,
    { intros i, cases (h_f_def i) with t' h_t',
      cases h_t' with h_t'_in h_f_i_in_t',
      cases h_t'_in with b h_t'_eq, 
      subst t',apply exists.intro b,
      apply h_f_i_in_t' },
    rw classical.skolem at h_f',
    cases h_f' with f' h_f',
    apply exists.intro (finset.image f' (finset.univ)),
    have h_f'':∀ (b:β), ∃ (s:set α), (s ∈ g b) ∧ (b ∈  (finset.image f' (finset.univ)) →
      s = ⋂ (i:fin m.succ) (H:f' i = b), f i),
    { intros b, cases classical.em (b ∈ finset.image f' (finset.univ)) with h_b_in h_b_notin,
      { apply exists.intro (⋂ (i:subtype (λ (i':fin m.succ), f' i' = b)), f i),
        split,
        have h_sub_non:nonempty (subtype (λ (i':fin m.succ), f' i' = b)),
        { simp at h_b_in, cases  h_b_in with i h_b_in,
          apply nonempty.intro (subtype.mk i h_b_in) },
        apply @is_pi_system_intro α _ _ h_sub_non,  
        apply h_pi,
        { intros i, cases i,
          have h_f'_2 := h_f' i_val,
          rw  i_property at h_f'_2,
          simp, apply h_f'_2 },
          have h_sub_t: t ⊆ (⋂ (i : {i' // f' i' = b}), f ↑i),
          { rw h_t_def, rw set.subset_def, intros x h_x, simp at h_x,
            simp, intros i h_i_eq, apply h_x },
        apply set.nonempty_of_nonempty_subset _ _ h_t_nonempty h_sub_t,
        intros h_2,
        { ext a, split; intros h_3; simp at h_3; simp [h_3];
          intros i h_4; apply h_3, apply h_4,
          simp, apply h_4, }, },
      { have h_6:= set.nonempty_def.1 (h_nonempty b),
        cases h_6 with s h_6,
        apply exists.intro s,
        apply and.intro h_6, intros h_7,
        apply absurd h_7 h_b_notin, }  },
    rw classical.skolem at h_f'',
    cases h_f'' with f'' h_f'',
    apply exists.intro f'',
    split,
    { rw h_t_def, ext a, split; intros h1; simp at h1; simp [h1]; intros i,
      { rw (h_f'' (f' i)).right _,
        intros s h_s,
        cases h_s with i' h_s,
        rw ← h_s,
        simp,
        intros h_i',
        apply h1, simp },
      { have h1_i := h1 i,
        rw (h_f'' (f' i)).right _ at h1_i,
        simp at h1_i,
        apply h1_i,
        refl, 
        simp } },
      intros b, apply (h_f'' b).left },
end

namespace probability_theory

section definitions

/-- A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def Indep_sets {α ι} [measurable_space α] (π : ι → set (set α)) (μ : measure α . volume_tac) :
  Prop :=
∀ (s : finset ι) {f : ι → set α} (H : ∀ i, i ∈ s → f i ∈ π i), μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep_sets {α} [measurable_space α] (s1 s2 : set (set α)) (μ : measure α . volume_tac) : Prop :=
∀ t1 t2 : set α, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space α` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep {α ι} (m : ι → measurable_space α) [measurable_space α] (μ : measure α . volume_tac) :
  Prop :=
Indep_sets (λ x, (m x).measurable_set') μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep {α} (m₁ m₂ : measurable_space α) [measurable_space α] (μ : measure α . volume_tac) :
  Prop :=
indep_sets (m₁.measurable_set') (m₂.measurable_set') μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def Indep_set {α ι} [measurable_space α] (s : ι → set α) (μ : measure α . volume_tac) : Prop :=
Indep_sets (λ i, {s i}) μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def indep_set {α} [measurable_space α] (s t : set α) (μ : measure α . volume_tac) : Prop :=
indep_sets {s} {t} μ

/-- A family of functions defined on the same space `α` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `α` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def Indep_fun {α ι} [measurable_space α] {β : ι → Type*} (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), α → β x) (μ : measure α . volume_tac) : Prop :=
Indep (λ x, measurable_space.comap (f x) (m x)) μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def indep_fun {α β γ} [measurable_space α] (mβ : measurable_space β) (mγ : measurable_space γ)
  (f : α → β) (g : α → γ) (μ : measure α . volume_tac) : Prop :=
indep (measurable_space.comap f mβ) (measurable_space.comap g mγ) μ

end definitions

section indep

lemma indep_sets.symm {α} {s₁ s₂ : set (set α)} [measurable_space α] {μ : measure α}
  (h : indep_sets s₁ s₂ μ) :
  indep_sets s₂ s₁ μ :=
by { intros t1 t2 ht1 ht2, rw [set.inter_comm, mul_comm], exact h t2 t1 ht2 ht1, }

lemma indep.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α}
  (h : indep m₁ m₂ μ) :
  indep m₂ m₁ μ :=
indep_sets.symm h

lemma indep_set.symm {α} [measurable_space α] (s t : set α) (μ : measure α . volume_tac) : 
indep_set s t μ → indep_set t s μ := begin
  intros h,
  apply indep_sets.symm,
  apply h,
end

lemma indep_sets_of_indep_sets_of_le_left {α} {s₁ s₂ s₃: set (set α)} [measurable_space α]
  {μ : measure α} (h_indep : indep_sets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
  indep_sets s₃ s₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma indep_sets_of_indep_sets_of_le_right {α} {s₁ s₂ s₃: set (set α)} [measurable_space α]
  {μ : measure α} (h_indep : indep_sets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
  indep_sets s₁ s₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma indep_of_indep_of_le_left {α} {m₁ m₂ m₃: measurable_space α} [measurable_space α]
  {μ : measure α} (h_indep : indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
  indep m₃ m₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma indep_of_indep_of_le_right {α} {m₁ m₂ m₃: measurable_space α} [measurable_space α]
  {μ : measure α} (h_indep : indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
  indep m₁ m₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma indep_sets.union {α} [measurable_space α] {s₁ s₂ s' : set (set α)} {μ : measure α}
  (h₁ : indep_sets s₁ s' μ) (h₂ : indep_sets s₂ s' μ) :
  indep_sets (s₁ ∪ s₂) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  cases (set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂,
  { exact h₁ t1 t2 ht1₁ ht2, },
  { exact h₂ t1 t2 ht1₂ ht2, },
end

@[simp] lemma indep_sets.union_iff {α} [measurable_space α] {s₁ s₂ s' : set (set α)}
  {μ : measure α} :
  indep_sets (s₁ ∪ s₂) s' μ ↔ indep_sets s₁ s' μ ∧ indep_sets s₂ s' μ :=
⟨λ h, ⟨indep_sets_of_indep_sets_of_le_left h (set.subset_union_left s₁ s₂),
    indep_sets_of_indep_sets_of_le_left h (set.subset_union_right s₁ s₂)⟩,
  λ h, indep_sets.union h.left h.right⟩

lemma indep_sets.Union {α ι} [measurable_space α] {s : ι → set (set α)} {s' : set (set α)}
  {μ : measure α} (hyp : ∀ n, indep_sets (s n) s' μ) :
  indep_sets (⋃ n, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_Union at ht1,
  cases ht1 with n ht1,
  exact hyp n t1 t2 ht1 ht2,
end

lemma indep_sets.inter {α} [measurable_space α] {s₁ s' : set (set α)} (s₂ : set (set α))
  {μ : measure α} (h₁ : indep_sets s₁ s' μ) :
  indep_sets (s₁ ∩ s₂) s' μ :=
λ t1 t2 ht1 ht2, h₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma indep_sets.Inter {α ι} [measurable_space α] {s : ι → set (set α)} {s' : set (set α)}
  {μ : measure α} (h : ∃ n, indep_sets (s n) s' μ) :
  indep_sets (⋂ n, s n) s' μ :=
by {intros t1 t2 ht1 ht2, cases h with n h, exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

end indep

/-! ### Deducing `indep` from `Indep` -/
section from_Indep_to_indep

lemma Indep_sets.indep_sets {α ι} {s : ι → set (set α)} [measurable_space α] {μ : measure α}
  (h_indep : Indep_sets s μ) {i j : ι} (hij : i ≠ j) :
  indep_sets (s i) (s j) μ :=
begin
  intros t₁ t₂ ht₁ ht₂,
  have hf_m : ∀ (x : ι), x ∈ {i, j} → (ite (x=i) t₁ t₂) ∈ s x,
  { intros x hx,
    cases finset.mem_insert.mp hx with hx hx,
    { simp [hx, ht₁], },
    { simp [finset.mem_singleton.mp hx, hij.symm, ht₂], }, },
  have h1 : t₁ = ite (i = i) t₁ t₂, by simp only [if_true, eq_self_iff_true],
  have h2 : t₂ = ite (j = i) t₁ t₂, by simp only [hij.symm, if_false],
  have h_inter : (⋂ (t : ι) (H : t ∈ ({i, j} : finset ι)), ite (t = i) t₁ t₂)
      = (ite (i = i) t₁ t₂) ∩ (ite (j = i) t₁ t₂),
    by simp only [finset.set_bInter_singleton, finset.set_bInter_insert],
  have h_prod : (∏ (t : ι) in ({i, j} : finset ι), μ (ite (t = i) t₁ t₂))
      = μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂),
    by simp only [hij, finset.prod_singleton, finset.prod_insert, not_false_iff,
      finset.mem_singleton],
  rw h1,
  nth_rewrite 1 h2,
  nth_rewrite 3 h2,
  rw [←h_inter, ←h_prod, h_indep {i, j} hf_m],
end

lemma Indep.indep {α ι} {m : ι → measurable_space α} [measurable_space α] {μ : measure α}
  (h_indep : Indep m μ) {i j : ι} (hij : i ≠ j) :
  indep (m i) (m j) μ :=
begin
  change indep_sets ((λ x, (m x).measurable_set') i) ((λ x, (m x).measurable_set') j) μ,
  exact Indep_sets.indep_sets h_indep hij,
end

end from_Indep_to_indep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets
/-! ### Independence of measurable space structures implies independence of generating π-systems -/

lemma Indep.Indep_sets {α ι} [measurable_space α] {μ : measure α} {m : ι → measurable_space α}
  {s : ι → set (set α)} (hms : ∀ n, m n = measurable_space.generate_from (s n))
  (h_indep : Indep m μ) :
  Indep_sets s μ :=
begin
  refine (λ S f hfs, h_indep S (λ x hxS, _)),
  simp_rw hms x,
  exact measurable_set_generate_from (hfs x hxS),
end

lemma indep.indep_sets {α} [measurable_space α] {μ : measure α} {s1 s2 : set (set α)}
  (h_indep : indep (generate_from s1) (generate_from s2) μ) :
  indep_sets s1 s2 μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces
/-! ### Independence of generating π-systems implies independence of measurable space structures -/

private lemma indep_sets.indep_aux {α} {m2 : measurable_space α}
  {m : measurable_space α} {μ : measure α} [probability_measure μ] {p1 p2 : set (set α)}
  (h2 : m2 ≤ m) (hp2 : is_pi_system p2) (hpm2 : m2 = generate_from p2)
  (hyp : indep_sets p1 p2 μ) {t1 t2 : set α} (ht1 : t1 ∈ p1) (ht2m : m2.measurable_set' t2) :
  μ (t1 ∩ t2) = μ t1 * μ t2 :=
begin
  let μ_inter := μ.restrict t1,
  let ν := (μ t1) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, measure_univ, mul_one],
  haveI : finite_measure μ_inter := @restrict.finite_measure α _ t1 μ (measure_lt_top μ t1),
  rw [set.inter_comm, ←@measure.restrict_apply α _ μ t1 t2 (h2 t2 ht2m)],
  refine ext_on_measurable_space_of_generate_finite m p2 (λ t ht, _) h2 hpm2 hp2 h_univ ht2m,
  have ht2 : m.measurable_set' t,
  { refine h2 _ _,
    rw hpm2,
    exact measurable_set_generate_from ht, },
  rw [measure.restrict_apply ht2, measure.smul_apply, set.inter_comm],
  exact hyp t1 t ht1 ht,
end

lemma indep_sets.indep {α} {m1 m2 : measurable_space α} {m : measurable_space α}
  {μ : measure α} [probability_measure μ] {p1 p2 : set (set α)} (h1 : m1 ≤ m) (h2 : m2 ≤ m)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = generate_from p1)
  (hpm2 : m2 = generate_from p2) (hyp : indep_sets p1 p2 μ) :
  indep m1 m2 μ :=
begin
  intros t1 t2 ht1 ht2,
  let μ_inter := μ.restrict t2,
  let ν := (μ t2) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, measure_univ, mul_one],
  haveI : finite_measure μ_inter := @restrict.finite_measure α _ t2 μ (measure_lt_top μ t2),
  rw [mul_comm, ←@measure.restrict_apply α _ μ t2 t1 (h1 t1 ht1)],
  refine ext_on_measurable_space_of_generate_finite m p1 (λ t ht, _) h1 hpm1 hp1 h_univ ht1,
  have ht1 : m.measurable_set' t,
  { refine h1 _ _,
    rw hpm1,
    exact measurable_set_generate_from ht, },
  rw [measure.restrict_apply ht1, measure.smul_apply, mul_comm],
  exact indep_sets.indep_aux h2 hp2 hpm2 hyp ht ht2,
end

--#check indep_set
lemma indep_set_iff {α} [m :measurable_space α] {μ : measure α} 
  {s t: set α} : indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t := begin
  unfold indep_set,
  unfold indep_sets,
  simp_rw set.mem_singleton_iff,
  split; intros h,
  apply h s t (eq.refl _) (eq.refl _),
  intros s1 t1 h_s1 h_t1,
  substs s1 t1,
  apply h,
end 

lemma indep_set.empty {α} [M:measurable_space α] (μ:measure α) (s:set α):
  indep_set s ∅ μ :=  begin
  rw indep_set_iff,
  simp
end

lemma independent_event_pair.compl {α} [M:measurable_space α] (μ:measure α) 
  [P:probability_measure μ] (s t:set α)
  (h_ind:indep_set s t μ) 
  (h_meas_s:measurable_set s)
  (h_meas_t:measurable_set t):
  indep_set s tᶜ μ := begin
  have h2:∀ t, μ t < ⊤,
  { intros t, 
    apply lt_of_le_of_lt (measure_theory.measure_mono (set.subset_univ _)),
    rw P.1, simp [P.1] },
  rw indep_set_iff,
  rw measure_theory.measure_compl h_meas_t (h2 t),
  rw P.1,
  rw ennreal.mul_sub,
  rw indep_set_iff at h_ind,
  rw ← h_ind, 
  rw mul_one,
  have h3:s ∩ tᶜ = s \ (s ∩ t),
  { ext a, split; intros h3_1; simp at h3_1; simp [h3_1] },
  rw h3,
  apply measure_theory.measure_diff (set.inter_subset_left _ _) h_meas_s,
  apply h_meas_s.inter h_meas_t,
  apply h2,
  { intros h3 h4, apply lt_top_iff_ne_top.1 (h2 _) },
end

-- Look up at the earlier theorems, may be a more general version.
lemma indep_set.nat_Union {α} [M:measurable_space α] (μ:measure α) 
  (s:set α) (f:ℕ → set α) 
  (h_meas_s:measurable_set s)
  (h_pair:pairwise (disjoint on f))
  (h_ind:∀ n, indep_set s (f n) μ) 
  (h_meas_t:∀ n, measurable_set (f n)):
  indep_set s (⋃ n, f n) μ := begin
  rw indep_set_iff,
  simp,
  
  have h1:s ∩ set.Union f = ⋃ n, (s ∩ (f n)),
  { rw set.inter_Union },
  rw h1,
  rw measure_theory.measure_Union,
  rw measure_theory.measure_Union,
  rw ← ennreal.tsum_mul_left,
  have h2:(λ n, μ s * μ (f n)) = (λ n, μ (s ∩ f n)),
  { ext1 n, rw indep_set_iff.1 (h_ind n), }, 
  rw h2,
  { apply h_pair },
  { apply h_meas_t },
  { intros i j h_ne, simp [function.on_fun, set.disjoint_left],
    intros a h_a_in_s h_a_in_f_i h_a_in_s h_a_in_f_j,
    have h_disj := h_pair i j h_ne,  
    rw [function.on_fun, set.disjoint_left] at h_disj, 
    apply h_disj h_a_in_f_i h_a_in_f_j },
  { intros i, apply h_meas_s.inter (h_meas_t i) },
end



/- This seems to be the theorem from above, but more fine-grained. -/
lemma generate_from_independent_space {α} [M:measurable_space α] (μ:measure α) 
  [probability_measure μ] (g:set (set α))
  (s:set α) (h_meas:measurable_set s) (h_meas_g:∀ t ∈ g, measurable_set t)
  (h_pi:is_pi_system g):
  (∀ t ∈ g, indep_set s t μ) → 
  (∀ t, (measurable_space.generate_from g).measurable_set' t → (indep_set s t μ)) :=
begin
  have h_meas_g':(∀ t, (measurable_space.generate_from g).measurable_set' t → measurable_set t),
  { intros t h_meas_t, apply measurable_space.generate_from_le h_meas_g, apply h_meas_t },
  intros h_ind,
  apply @measurable_space.induction_on_inter α (λ t, indep_set s t μ),
  { refl },
  { apply h_pi },
  { apply indep_set.empty },
  { apply h_ind },
  { intros t h_meas_t h_ind_t, apply independent_event_pair.compl,
    apply h_ind_t,
    apply h_meas,
    apply h_meas_g' _ h_meas_t, },
  { intros f h_disjoint h_meas_f h_ind_f,
    apply indep_set.nat_Union,
    apply h_meas,
    apply h_disjoint, apply h_ind_f,
    { intros n, apply h_meas_g', apply h_meas_f } },
end

-- Probably not unique.
lemma nonempty_measurable_set' {α} [M:measurable_space α]:
  set.nonempty (M.measurable_set') := begin
  rw set.nonempty_def,
  apply exists.intro ∅,
  apply M.measurable_set_empty,
end

lemma supr_independent_event_pair {α} {β:Type*} [M:measurable_space α] (μ:measure α) (s:set α)
  (h_meas_s:measurable_set s)
  [P:probability_measure μ] {Mf:β → measurable_space α}
  (h_meas_Mf:∀ b, Mf b ≤ M)
  (h_ind_pair:∀ (T:finset β) (f:β → set α), (∀ (b:β), (Mf b).measurable_set' (f b)) →
   indep_set s (⋂ b∈ T, f b) μ):
  (∀ (t:set α), (supr Mf).measurable_set' t → indep_set s t μ) := begin
  have h2:∀ t' ∈ (generate_pi_system (⋃ (b:β), (Mf b).measurable_set')),
    M.measurable_set' t',
  { have h2_1:(supr Mf) ≤ M,
    { apply @supr_le (measurable_space α) _ _,
      intros b, apply h_meas_Mf },
    intros t' h_t', apply h2_1, rw supr_eq_generate_from,
    apply generate_pi_system_measurable_set,
    apply measurable_space.measurable_set_generate_from,
    apply h_t' },
  intros t h_t,
  rw supr_eq_generate_from at h_t,
  rw ← generate_from_generate_pi_system_eq at h_t,
  apply generate_from_independent_space _ _ _ h_meas_s,
  apply h2,
  apply is_pi_system_generate_pi_system,
  intros t h_t,
  have h3 := is_pi_system_union _ _ t h_t,
  cases h3 with T h3,
  cases h3 with f h3,
  cases h3 with h_t_def h_meas_f,
  subst t,
  apply h_ind_pair,
  apply h_meas_f,
  { intros b, apply is_pi_system_measurable_set },
  apply (λ b, @nonempty_measurable_set' α (Mf b)),
  apply h_t,
  apply P,
end 

-- Used to be Sup_independent_event_pair
lemma Sup_indep_set {α} {β:Type*} [M:measurable_space α] (μ:measure α) (s:set α)
  (h_meas_s:measurable_set s)
  (S:set β)
  [P:probability_measure μ] {Mf:β → measurable_space α}
  (h_meas_Mf:∀ b, Mf b ≤ M)
  (h_ind_pair:∀ (T:finset β) (f:β → set α), (↑T ⊆ S) → (∀ (b:β), (Mf b).measurable_set' (f b)) →
   indep_set s (⋂ b∈ T, f b) μ) :
  (∀ (t:set α), (Sup (Mf '' S)).measurable_set' t → indep_set s t μ) := begin
  classical,
  intros t h_t,
  apply @supr_independent_event_pair α (subtype S) M μ s h_meas_s P
  (λ b, Mf b.val) (λ b, h_meas_Mf b.val) _ _,
  { unfold supr, have h1:Mf '' S = (set.range (λ (b:subtype S), Mf b.val)),
    { simp, ext1 M'; split; intros h2; simp at h2; simp [h2]; cases h2 with x h2;
      apply exists.intro x; simp [h2]; apply h2.left,
        }, rw ←  h1, apply h_t, },
  { intros T f h_sub, 
    have h3:(⋂ (b : subtype S) (H : b ∈ T), f b) = 
     (⋂ b ∈ (T.image subtype.val), if h: (b ∈ S) then (f (subtype.mk b h)) else ∅),
    { ext1 a, split; intros h3_1; simp at h3_1; simp [h3_1]; apply h3_1, },
    rw h3, apply h_ind_pair,
    { rw set.subset_def, intros x h_x_in_T, simp at h_x_in_T,
      cases h_x_in_T with h_x_in_S h_x_in_T, apply h_x_in_S },
    { intros b, cases (classical.em (b ∈ S)) with h_b_in_S h_b_notin_S,
      { rw dif_pos h_b_in_S, have h4 := h_sub ⟨b, h_b_in_S⟩, simp at h4, apply h4 },
      { rw dif_neg h_b_notin_S, apply measurable_set.empty } } }, 
end


lemma Inter_finset_congr {α} {β:Type*} {T:finset β} (f g:β → set α) 
  (h_congr:∀ (i ∈ T), f i = g i):(⋂ (i∈ T), f i) = (⋂ (i ∈ T), g i) := begin
  ext a, split; intros h1; simp at h1; simp; intros i h_i,
  rw  ← h_congr i h_i,
  apply h1 i h_i,
  rw h_congr i h_i,
  apply h1 i h_i
end



lemma indep_Sup_Sup {α} {β:Type*} [M:measurable_space α] (μ:measure α)
  [P:probability_measure μ] {Mf:β → measurable_space α}
  (h_meas_Mf:∀ b, Mf b ≤ M)
  (S1 S2:set β) (h_disj:disjoint S1 S2)
  (h_ind_pair:∀ (T1 T2:finset β) (f:β → set α), 
  ↑T1 ⊆ S1 → (↑T2 ⊆ S2) → (∀ (b:β), (Mf b).measurable_set' (f b)) →
   indep_set (⋂ b ∈ T1, f b) (⋂ b∈ T2, f b) μ):
   indep (Sup (Mf '' S1)) (Sup (Mf '' S2)) μ := begin
  classical,
  have h_measM:∀ s (S:set β), (Sup (Mf '' S)).measurable_set' s → M.measurable_set' s,
  { intros s S,
    have h1_1: (Sup (Mf '' S)) ≤ M,
    { apply @Sup_le (measurable_space α) _, intros M' h_M', cases  h_M' with b h_M',
      cases h_M' with h_b h_M', subst M', apply h_meas_Mf },
    apply h1_1 },
  intros s t h_s h_t,
  apply Sup_indep_set μ s _ S2,
  apply h_meas_Mf,
  { intros T2 f2 h_T2 h_meas_f2, 
    apply indep_set.symm,
    apply Sup_indep_set μ _ _ S1,
    apply h_meas_Mf,
    { intros T1 f1 h_T1 h_meas_f1,
      have h_disj_T1_T2:disjoint T1 T2,
      { rw finset.disjoint_left,
        rw set.disjoint_left at h_disj,
        intros b h_b h_b',
        apply @h_disj b _ _,
        apply h_T1, apply h_b,
        apply h_T2, apply h_b' }, 
      apply indep_set.symm,
      let f := (λ (b:β), if (b ∈ T1) then (f1 b) else (f2 b)),
      begin
        have h_f_def : ∀ b, f b = if (b ∈ T1) then (f1 b) else (f2 b),
        { intros b, refl },
        have hf_f1:(⋂ b ∈ T1, f b) = (⋂ b ∈ T1, f1 b),
        { apply Inter_finset_congr,
          intros i h_i, rw h_f_def i, rw if_pos h_i },
        have hf_f2:(⋂ b ∈ T2, f b) = (⋂ b ∈ T2, f2 b),
        { apply Inter_finset_congr,
          intros i h_i, rw h_f_def i,
          rw if_neg,
          apply finset.disjoint_right.1 h_disj_T1_T2 h_i },
        rw ← hf_f1,
        rw ← hf_f2,
        apply h_ind_pair T1 T2 f h_T1 h_T2 _,
        intros b, rw h_f_def, cases classical.em (b ∈ T1),
        { rw if_pos h, apply h_meas_f1 },
        { rw if_neg h, apply h_meas_f2 },
      end
       }, apply h_s, 
    { apply finset.measurable_set_bInter,
      intros b h_b,  apply h_meas_Mf b,
      apply h_meas_f2 } },
  apply h_t,
  repeat { apply set.mem_singleton },
  apply h_measM _ S1 h_s,
end

lemma indep_elim {α} {β} [M:measurable_space α] (μ:measure α) [probability_measure μ] (Mf:β → measurable_space α) (h_le:∀ b, Mf b ≤ M) (h_ind:Indep Mf μ) (S1 S2:set β) (h_disj:disjoint S1 S2)
  :(indep (Sup (Mf '' S1)) (Sup (Mf '' S2)) μ) :=
begin
  classical,
  apply indep_Sup_Sup,
  apply h_le,
  apply h_disj,
  intros T1 T2 f h_T1 h_T2 h_meas_f,
  rw indep_set_iff,
  unfold Indep at h_ind,
  unfold Indep_sets at h_ind,
  rw h_ind,
  rw h_ind,
  have h_eq:((⋂ (b ∈ T1), f b) ∩ ⋂ (b ∈ T2), f b) =
     ((⋂ (b ∈ (T1 ∪ T2)), f b)),
  { ext a, split; intros h_1,
    { simp at h_1,
      simp, intros i h_3,
      cases h_3 with h_3 h_3,
      apply h_1.left i h_3,
      apply h_1.right i h_3 },
    simp only [set.mem_inter_eq, set.mem_Inter],
    simp at h_1,
    split,
    { intros b h_b, apply h_1 b (or.inl h_b) },
    { intros b h_b, apply h_1 b (or.inr h_b) } },
  rw h_eq,
  rw h_ind,
  rw finset.prod_union,
  { rw finset.disjoint_left,
        rw set.disjoint_left at h_disj,
        intros b h_b h_b',
        apply @h_disj b _ _,
        apply h_T1, apply h_b,
        apply h_T2, apply h_b' }, 
  repeat {apply h_meas_f},
  repeat { intros b h_b, apply h_meas_f },
end

lemma indep_elim' {α} {β} [M:measurable_space α] (μ:measure α) [probability_measure μ] (Mf:β → measurable_space α) (h_le:∀ b, Mf b ≤ M) (h_ind:Indep Mf μ) (s:set β) (t:β) (h_t_notin_s:t ∉ s):(indep (Sup (Mf '' s)) (Mf t) μ) :=
begin
  have h1:Mf t = (Sup (Mf '' {t})),
  { simp },
  rw h1,
  apply indep_elim,
  apply h_le,
  apply h_ind,
  simp,
  apply h_t_notin_s,
end

end from_pi_systems_to_measurable_spaces

end probability_theory

