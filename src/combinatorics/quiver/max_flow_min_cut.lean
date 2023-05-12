/-
Copyright (c) 2023 Aleksandar Milchev, Leo Okawa Ericson, Viggo Laakshoharju. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Milchev, Leo Okawa Ericson, Viggo Laakshoharju
-/


import algebra.big_operators.order
import data.real.basic
import data.set.finite
import tactic.induction

/-!
# Max flow Min cut theorem

In this file we will prove the max-flow min-cut theorem,
stating that if a maximum flow exists in a flow network,
then its value is equal to the capacity of a minimum cut in the same network.

## Main results

- `weak_duality`        :
  The value of every flow is less than or equal to the capacity of every cut.

  direct consequences   :
  - The value of a max flow is always less than or equal to the capacity of a min cut.
  - `max_flow_criterion`:
    If a flow value is equal to a cut capacity in the same flow network, then the flow is maximum.
  - `min_cut_criterion` :
    If a capacity of a cut is equal to a flow value in the same network, then the cut is minimum.

- `no_augm_path`        :
  If the active flow gives a maximum flow, then there is no augmenting path in the residual network.
- `existence_of_a_cut`  :
  there exists a cut with a capacity equal to the value of the maximum flow.
- `max_flow_min_cut`    :
  If f is a max flow and c is a min cut in the same network, then their values are equal.

The `max_flow_min_cut` lemma is the statement of the max-flow min-cut theorem.

## Notation

- Type V is used for the set of all vertices in our graph. It is a finite type.

## References

- Some of the structure ideas and lemmas can be seen in https://github.com/Zetagon/maxflow-mincut.

-/

open finset

open_locale big_operators
open_locale classical

notation ` V' ` := univ -- The universe, containing all vertices.

/-!
  We now define our flow network. Our goal will be to prove weak_duality.
  As direct consequences, `max_flow_criterion` and `min_cut_criterion` will be proven.
-/

structure digraph (V : Type*) [inst : fintype V] :=
  (is_edge : V → V → Prop)
  (nonsymmetric : ∀ u v : V, ¬ ((is_edge u v) ∧ (is_edge v u)))

structure capacity (V : Type*) [inst : fintype V]
  extends digraph V :=
  (c : V -> V -> ℝ)
  (non_neg_capacity : ∀ u v : V, c u v ≥ 0)
  (vanishes : ∀ u v : V, ¬ (is_edge u v) → c u v = 0)

structure flow_network (V : Type*) [inst : fintype V]
  extends capacity V :=
  (source : V)
  (sink : V)

noncomputable
def mk_in {V : Type*} [inst : fintype V]
  (f : V -> V -> ℝ) (S : finset V) : ℝ := ∑ x in finset.univ \ S, ∑ y in S, f x y

noncomputable
def mk_out {V : Type*} [inst : fintype V]
  (f : V -> V -> ℝ) (S : finset V) : ℝ := ∑ x in S, ∑ y in finset.univ \ S, f x y

structure active_flow_network (V : Type*)  [fintype V] :=
  (network : flow_network V)
  (f : V -> V -> ℝ)
  (source_not_sink: network.source ≠ network.sink)
  (non_neg_flow : ∀ u v : V, f u v ≥ 0)
  (no_overflow : ∀ u v : V, f u v ≤ network.c u v)
  (no_edges_in_source : ∀ u : V, ¬ (network.is_edge u network.source))
  (no_edges_out_sink : ∀ u: V, ¬ (network.is_edge network.sink u))
  (conservation : ∀ v : V,
                  v ∈ (V' : finset V) \ {network.source, network.sink} →
                  mk_out f {v} = mk_in f {v})

noncomputable
def F_value {V : Type*}  [fintype V] :
                  active_flow_network V -> ℝ :=
λ N, mk_out N.f {N.network.source} - mk_in N.f {N.network.source}

structure cut (V : Type*)  [fintype V] :=
  (network : flow_network V)
  (S : finset V)
  (T : finset V)
  (sins : network.source ∈ S)
  (tint : network.sink ∈ T)
  (Tcomp : T = univ \ S)

noncomputable
def cut_cap {V : Type*}  [inst' : fintype V] -- stays for capacity of the cut
    (c : cut V) : ℝ := mk_out c.network.c c.S

lemma f_vanishes_outside_edge {V : Type*} [fintype V]
  (afn : active_flow_network V) (u : V) (v : V) (not_edge: ¬afn.network.is_edge u v) :
  afn.f u v = 0 :=
  begin
    have zeroCap: afn.network.c u v = 0 := afn.network.vanishes u v not_edge,
    have bar := afn.no_overflow u v,
    have foo := afn.non_neg_flow u v,
    linarith,
  end

lemma x_not_in_s {V : Type*} [fintype V]
  (c : cut V)  : ∀ x : V, x ∈ c.T -> x ∉ ({c.network.source} : finset V) :=
begin
  intros x xInS,
  cases c,
  simp only [mem_singleton] at *,
  rw c_Tcomp at xInS,
  have h: univ \ c_S ∩ c_S = ∅ := sdiff_inter_self c_S univ,
  have foo: disjoint (univ \ c_S)  c_S  := sdiff_disjoint,
  have bar: c_network.source ∈ c_S := c_sins,
  exact disjoint_iff_ne.mp foo x xInS c_network.source c_sins
end

lemma f_zero {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (x : V) : afn.f x x = 0 :=
begin
  have hnonsymm: _ := afn.network.nonsymmetric x x,
  have hvanish: _ := afn.network.vanishes x x,
  simp only [not_and, imp_not_self] at hnonsymm,
  have hnon_edge := hnonsymm, clear hnonsymm,
  have hcapacity_zero := hvanish hnon_edge,
  have hno_overflow := afn.no_overflow x x,
  rw hcapacity_zero at hno_overflow,
  have hnon_neg_flow := afn.non_neg_flow x x,
  linarith,
end


lemma mk_in_single_node {V : Type*}  [fintype V]
  (p : V) (afn : active_flow_network V) :
  mk_in (afn.f) {p} = ∑ v in finset.univ, (afn.f) v p :=
begin
  rw @sum_eq_sum_diff_singleton_add _ _ _ _ univ p (by simp only [mem_univ]) (λ x, afn.f x p),
  simp only [congr_fun],
  rw f_zero afn p,
  have foo: ∑ (x : V) in univ \ {p}, afn.f x p + 0 =
  (λ p', ∑ (x : V) in univ \ {p'}, afn.f x p') p := by simp only [add_zero],
  rw foo, clear foo,
  rw ← @finset.sum_singleton _ _ p (λp', ∑ (x : V) in univ \ {p'}, afn.f x p' ) _,
  simp only [mk_in, sum_singleton],
end

@[simp] lemma mk_in_single_node' {V : Type*}  [fintype V]
  (p : V) (afn : active_flow_network V) :
  ∑ v in finset.univ, (afn.f) v p = mk_in (afn.f) {p} := by rw mk_in_single_node

lemma mk_out_single_node {V : Type*}  [fintype V]
  (p : V) (afn : active_flow_network V) :
  mk_out afn.f {p} = ∑ v in finset.univ, (afn.f) p v :=
begin
  rw @sum_eq_sum_diff_singleton_add _ _ _ _ univ p (by simp only [mem_univ]) (λ x, afn.f p x),
  simp only [congr_fun],
  rw f_zero afn p,
  have foo: ∑ (x : V) in univ \ {p}, afn.f p x + 0 =
  (λ p', ∑ (x : V) in univ \ {p'}, afn.f p' x) p := by simp only [add_zero],
  rw foo, clear foo,
  rw ← @finset.sum_singleton _ _ p (λp', ∑ (x : V) in univ \ {p'}, afn.f p' x) _,
  simp only [mk_out, sum_singleton],
end

@[simp] lemma mk_out_single_node' {V : Type*}  [fintype V]
  (p : V) (afn : active_flow_network V) :
  ∑ v in finset.univ, (afn.f) p v = mk_out afn.f {p} := by rw mk_out_single_node

lemma break_out_neg (a b : ℝ) : (-a) + -(b) = -(a + b) := by ring

noncomputable
def edge_flow {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (x : V) : ℝ := (mk_out afn.f {x} - mk_in afn.f {x})

lemma edge_flow_conservation {V: Type*} [inst' : fintype V]
  (afn : active_flow_network V) (x : V) :
  x ∈ (V' : finset V) \ {afn.network.source, afn.network.sink} -> edge_flow afn x = 0 :=
begin
  intro hx,
  unfold edge_flow,
  rw afn.conservation x,
  { ring },
  { exact hx },
end

lemma foobar { a b : ℝ } : a + - b = a - b := rfl

lemma sub_comm_zero (a b : ℝ) : a - b = 0 → b - a = 0 := by {intro eq, linarith}

lemma set_flow_conservation {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V) :
S ⊆ finset.univ \ {afn.network.source, afn.network.sink} -> mk_in afn.f S = mk_out afn.f S :=
begin
  intro stNotInS,
  rw ← add_left_inj (- mk_out afn.f S),
  simp only [add_right_neg],
  rw ← add_zero (mk_in afn.f S),
  nth_rewrite 0 ← add_neg_self (∑ u in S, (∑ v in S, afn.f u v)),
  rw ← add_assoc,
  have foo: mk_in afn.f S + ∑ u in S, ∑ v in S, afn.f u v = ∑ u in S, ∑ v in V', afn.f v u :=
  begin
    unfold mk_in,
    have h: S ⊆ V' := finset.subset_univ S,
    have hyp:
    ∑ (x : V) in V' \ S, ∑ (y : V) in S, afn.f x y + ∑ (u : V) in S, ∑ (v : V) in S, afn.f u v
    = ∑ u in V', ∑ v in S, afn.f u v := finset.sum_sdiff h,
    have swap: ∑ u in V', ∑ v in S, afn.f u v = ∑ u in S, ∑ v in V', afn.f v u := finset.sum_comm,
    rw hyp,
    exact swap,
  end,
  have bar: mk_out afn.f S + (∑ u in S, ∑ v in S, afn.f u v) = ∑ u in S, ∑ v in V', afn.f u v :=
  begin
    unfold mk_out,
    rw finset.sum_comm,
    have h: S ⊆ V' := finset.subset_univ S,
    have baz:
    ∑ (y : V) in V' \ S, ∑ (x : V) in S, afn.f x y + ∑ (u : V) in S, ∑ (v : V) in S, afn.f v u =
    ∑ u in V', ∑ v in S, afn.f v u := finset.sum_sdiff h,
    have bark: ∑ (u : V) in S, ∑ (v : V) in S, afn.f v u =
    ∑ (u : V) in S, ∑ (v : V) in S, afn.f u v := finset.sum_comm,
    have swap: ∑ u in V', ∑ v in S, afn.f v u = ∑ u in S, ∑ v in V', afn.f u v := finset.sum_comm,
    rw bark at baz,
    rw baz,
    exact swap,
  end,
  rw foo,
  rw add_assoc,
  rw break_out_neg,
  nth_rewrite 1 add_comm,
  rw bar,
  clear foo bar,
  rw foobar,
  rw ← @sum_sub_distrib _ _ S _ _ _,
  simp only [mk_in_single_node', mk_out_single_node'],
  have h : ∀ (x : V), x ∈ S -> - edge_flow afn x = 0 :=
  begin
    intros x hx,
    unfold edge_flow,
    rw afn.conservation x,
    { ring },
    { exact finset.mem_of_subset stNotInS hx },
  end,
  have baz := finset.sum_congr rfl h,
  unfold edge_flow at baz,
  simp at baz,
  rw ← baz,
  simp,
end

lemma move_right (a b : ℝ) : b = a → a - b = 0 := by {intro eq, linarith}

lemma set_flow_conservation_eq {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (S : finset V) :
S ⊆ finset.univ \ {afn.network.source, afn.network.sink} -> mk_out afn.f S - mk_in afn.f S = 0 :=
begin
  intro hip,
  have h: mk_in afn.f S = mk_out afn.f S := set_flow_conservation afn S hip,
  linarith
end

lemma add_zero_middle (a b c: ℝ): c = 0 → a + c - b = a - b := by {intro eq, linarith}

lemma group_minus (a b c d : ℝ): a + b - c - d = a + b - (c + d) := by ring

lemma same_source_and_sink {V: Type*} [inst' : fintype V]
  (afn: active_flow_network V) (ct : cut V) (same_net : afn.network = ct.network):
  afn.network.source = ct.network.source ∧ afn.network.sink = ct.network.sink :=
begin
  rw same_net,
  split,
  {simp},
  simp
end

lemma sdiff_finset_sdiff_singleton_eq_sdiff_singleton {V : Type*}  [inst' : fintype V]
  (S : finset V) (s : V) : (s ∈ S) → V' \ (S \ {s}) \ {s} = V' \ S :=
begin
  intro sInS,
  have sSubsetS: {s} ⊆  S := (finset.singleton_subset_iff).2 sInS,
  ext x,
  have eq1: V' \ (S \ {s}) \ {s} = V' \ (S \ {s}) ∩ (V' \ {s}) :=
  finset.sdiff_sdiff_left' V' (S \ {s}) {s},
  rw eq1,
  have xIn: x ∈ V' := finset.mem_univ x,
  split,
  { intro hyp,
    have xIn1: x ∈ V' \ (S \ {s}) := (finset.mem_inter.1 hyp).1,
    have xIn2: x ∈ V' \ {s} := (finset.mem_inter.1 hyp).2,
    have xOut: x ∉ S :=
    begin
      have xOut1: x ∉ (S \ {s}) := (finset.mem_sdiff.1 xIn1).2,
      have xOut2: x ∉ {s} := (finset.mem_sdiff.1 xIn2).2,
      have xOutAnd: x ∉ (S \ {s}) ∧ x ∉ {s} := and.intro xOut1 xOut2,
      have eq2: S = (S \ {s}) ∪ {s} :=
      begin
        have inter: S ∩ {s} = {s} := finset.inter_singleton_of_mem sInS,
        have eq3: (S \ {s}) ∪ S ∩ {s} = S := by rw finset.sdiff_union_inter S {s},
        calc
          S
              = (S \ {s}) ∪ S ∩ {s} : eq_comm.1 eq3
          ... = (S \ {s}) ∪ {s} : by rw inter,
      end,
      rw eq2,
      exact finset.not_mem_union.2 xOutAnd,
    end,
    have concl: x ∈ V' ∧ x ∉ S := and.intro xIn xOut,
    exact finset.mem_sdiff.2 concl, },
  intro hyp,
  have xOutS: x ∉ S := (finset.mem_sdiff.1 hyp).2,
  have xOut: x ∉ S \ {s} :=
  begin
    by_contradiction h,
    have contr: x ∈ S := (finset.mem_sdiff.1 h).1,
    exact absurd contr xOutS,
  end,
  have sdiff: x ∈ V' ∧ x ∉ S \ {s} := and.intro xIn xOut,
  have xIn1: x ∈ V' \ (S \ {s}) := finset.mem_sdiff.2 sdiff,
  have xNotIns: x ∉ {s} :=
  begin
    by_contradiction h,
    have contr: x ∈ S := finset.mem_of_subset sSubsetS h,
    exact absurd contr xOutS,
  end,
  have concl: x ∈ V' ∧ x ∉ {s} := and.intro xIn xNotIns,
  have xIn2: x ∈ V' \ {s} := finset.mem_sdiff.2 concl,
  have member: x ∈ V' \ (S \ {s}) ∧ x ∈ V' \ {s} := and.intro xIn1 xIn2,
  exact finset.mem_inter.2 member,
end

lemma sdiff_finset_union_finset_eq_sdiff_singleton {V : Type*}  [inst' : fintype V]
  (S : finset V) (s : V) : (s ∈ S) → V' \ S ∪ S \ {s} = V' \ {s} :=
begin
  intro sInS,
  have sSubsetS: {s} ⊆  S := (finset.singleton_subset_iff).2 sInS,
  ext x,
  have xIn: x ∈ V' := finset.mem_univ x,
  split,
  { intro hyp,
    have foo: x ∈ V' \ S ∨ x ∈ S \ {s} := finset.mem_union.1 hyp,
    have bar: x ∈ V' \ S → x ∈ V' \ {s} :=
    begin
      intro hypo,
      have xOutS: x ∉ S := (finset.mem_sdiff.1 hypo).2,
      have xNotIns: x ∉ {s} :=
      begin
        by_contradiction h,
        have contr: x ∈ S := finset.mem_of_subset sSubsetS h,
        exact absurd contr xOutS,
      end,
      have concl: x ∈ V' ∧ x ∉ {s} := and.intro xIn xNotIns,
      exact finset.mem_sdiff.2 concl,
    end,
    have baz: x ∈ S \ {s} → x ∈ V' \ {s} :=
    begin
      intro hypo,
      have xNotIns: x ∉ {s} := (finset.mem_sdiff.1 hypo).2,
      have concl: x ∈ V' ∧ x ∉ {s} := and.intro xIn xNotIns,
      exact finset.mem_sdiff.2 concl,
    end,
    exact or.elim foo bar baz, },
  intro hyp,
  have xNotIns: x ∉ {s} := (finset.mem_sdiff.1 hyp).2,
  by_cases h' : x ∈ S,
  { have and: x ∈ S ∧ x ∉ {s} := and.intro h' xNotIns,
    have xInSs: x ∈ S \ {s} := finset.mem_sdiff.2 and,
    have conj: x ∈ V' \ S ∨ x ∈ S \ {s} := or.intro_right (x ∈ V' \ S) xInSs,
    exact finset.mem_union.2 conj, },
  { have and: x ∈ V' ∧ x ∉ S := and.intro xIn h',
    have xInVS: x ∈ V' \ S := finset.mem_sdiff.2 and,
    have conj: x ∈ V' \ S ∨ x ∈ S \ {s} := or.intro_left (x ∈ S \ {s}) xInVS,
    exact finset.mem_union.2 conj, },
end

lemma disjoint_sdiff_finset_sdiff_singleton {V : Type*}  [inst' : fintype V]
  (S : finset V) (s : V) : disjoint (V' \ S) (S \ {s}) :=
begin
  have foo: (V' \ S) ∩ (S \ {s}) = ∅ :=
  begin
    have noMembers: ∀ (v : V), v ∉ (V' \ S) ∩ (S \ {s}) :=
    begin
    intro v,
    by_contradiction h,
    have vInVmS: v ∈ (V' \ S) := (finset.mem_inter.1 h).1,
    have vNotInS: v ∉ S := (finset.mem_sdiff.1 vInVmS).2,
    have vInSms: v ∈ (S \ {s}) := (finset.mem_inter.1 h).2,
    have vInS: v ∈ S := (finset.mem_sdiff.1 vInSms).1,
    exact absurd vInS vNotInS,
    end,
    exact finset.eq_empty_of_forall_not_mem noMembers,
  end,
  have bar: ¬ ((V' \ S) ∩ (S \ {s})).nonempty :=
  begin
    by_contradiction h,
    have contr: (V' \ S) ∩ (S \ {s}) ≠ ∅ := finset.nonempty.ne_empty h,
    exact absurd foo contr,
  end,
  by_contradiction notDisjoint,
  have contr: ((V' \ S) ∩ (S \ {s})).nonempty :=
  finset.not_disjoint_iff_nonempty_inter.1 notDisjoint,
  exact absurd contr bar,
end

lemma sum_sdiff_singleton_sum_sdiff_finset_sdiff_singleton {V : Type*}  [inst' : fintype V]
  (f : V → V → ℝ) (S : finset V) (s : V) :
  (s ∈ S) →  ∑ (x : V) in (S \ {s}), ∑ (y : V) in V' \ (S \ {s}), f x y =
  ∑ (x : V) in (S \ {s}), f x s + ∑ (x : V) in (S \ {s}), ∑ (y : V) in V' \ S, f x y :=
begin
  intro sInS,
  have singleton: s ∈ {s} := finset.mem_singleton.2 rfl,
  have disjS: disjoint {s} (S \ {s}) :=
    begin
      have sOut: s ∉ (S \ {s}) := finset.not_mem_sdiff_of_mem_right singleton,
      exact finset.disjoint_singleton_left.2 sOut,
    end,
  have sInCompl: {s} ⊆ V' \ (S \ {s}) :=
  begin
    have sIn: {s} ⊆ V' := finset.subset_univ {s},
    have conj: {s} ⊆ V' ∧ disjoint {s} (S \ {s}) := and.intro sIn disjS,
    exact finset.subset_sdiff.2 conj,
  end,
  have foo: ∑ (x : V) in (S \ {s}), ∑ (y : V) in V' \ (S \ {s}), f x y =
  ∑ (y : V) in V' \ (S \ {s}), ∑ (x : V) in (S \ {s}), f x y := finset.sum_comm,
  have bar: ∑ (y : V) in V' \ (S \ {s}), ∑ (x : V) in (S \ {s}), f x y =
  ∑ (y : V) in V' \ S, ∑ (x : V) in (S \ {s}), f x y +
  ∑ (y : V) in {s}, ∑ (x : V) in (S \ {s}), f x y :=
  by {rw ← finset.sum_sdiff sInCompl, rw sdiff_finset_sdiff_singleton_eq_sdiff_singleton S s sInS},
  have baz: ∑ (y : V) in {s}, ∑ (x : V) in (S \ {s}), f x y = ∑ (x : V) in (S \ {s}), f x s :=
  by simp,
  have swap: ∑ (y : V) in V' \ S, ∑ (x : V) in S \ {s}, f x y =
  ∑ (x : V) in S \ {s}, ∑ (y : V) in V' \ S, f x y := finset.sum_comm,
  rw baz at bar,
  rw [foo, bar, add_comm, swap],
end

lemma in_expansion {V : Type*}  [inst' : fintype V]
  (f : V → V → ℝ) (S : finset V) (s : V) :
  (s ∈ S) → ∑ (x : V) in V' \ S, ∑ (y : V) in S, f x y =
  ∑ (x : V) in V' \ S, ∑ (y : V) in (S \ {s}), f x y +
  ∑ (x : V) in V' \ S, ∑ (y : V) in {s}, f x y :=
begin
  intro sInS,
  have sSubsetS: {s} ⊆  S := (finset.singleton_subset_iff).2 sInS,
  have foo: ∑ (x : V) in V' \ S, ∑ (y : V) in S, f x y =
  ∑ (y : V) in S, ∑ (x : V) in V' \ S, f x y := finset.sum_comm,
  have bar: ∑ (y : V) in S, ∑ (x : V) in V' \ S, f x y =
  ∑ (y : V) in (S \ {s}), ∑ (x : V) in V' \ S, f x y +
  ∑ (y : V) in {s}, ∑ (x : V) in V' \ S, f x y := by {rw finset.sum_sdiff sSubsetS},
  have swap:
  ∑ (y : V) in (S \ {s}), ∑ (x : V) in V' \ S, f x y +
  ∑ (y : V) in {s}, ∑ (x : V) in V' \ S, f x y =
  ∑ (x : V) in V' \ S, ∑ (y : V) in (S \ {s}), f x y +
  ∑ (x : V) in V' \ S, ∑ (y : V) in {s}, f x y :=
  begin
    have swap1: ∑ (y : V) in (S \ {s}), ∑ (x : V) in V' \ S, f x y =
    ∑ (x : V) in V' \ S, ∑ (y : V) in (S \ {s}), f x y := finset.sum_comm,
    have swap2: ∑ (y : V) in {s}, ∑ (x : V) in V' \ S, f x y =
    ∑ (x : V) in V' \ S, ∑ (y : V) in {s}, f x y := finset.sum_comm,
    linarith,
  end,
  linarith,
end

lemma sum_sdiff_finset_sdiff_singleton_sum_sdiff_singleton {V : Type*}  [inst' : fintype V]
  (f : V → V → ℝ) (S : finset V) (s : V) :
  (s ∈ S) → ∑ (x : V) in V' \ (S \ {s}), ∑ (y : V) in S \ {s}, f x y =
  ∑ (x : V) in V' \ S, ∑ (y : V) in S \ {s}, f x y + ∑ (u : V) in S \ {s}, f s u :=
begin
  intro sInS,
  have singleton: s ∈ {s} := finset.mem_singleton.2 rfl,
  have disjS: disjoint {s} (S \ {s}) :=
    begin
      have sOut: s ∉ (S \ {s}) := finset.not_mem_sdiff_of_mem_right singleton,
      exact finset.disjoint_singleton_left.2 sOut,
    end,
  have sInCompl: {s} ⊆ V' \ (S \ {s}) :=
  begin
    have sIn: {s} ⊆ V' := finset.subset_univ {s},
    have conj: {s} ⊆ V' ∧ disjoint {s} (S \ {s}) := and.intro sIn disjS,
    exact finset.subset_sdiff.2 conj,
  end,
  have foo: ∑ (x : V) in V' \ (S \ {s}), ∑ (y : V) in S \ {s}, f x y =
    ∑ (x : V) in V' \ S, ∑ (y : V) in S \ {s}, f x y +
    ∑ (x : V) in {s}, ∑ (y : V) in S \ {s}, f x y :=
  by {rw ← finset.sum_sdiff sInCompl, rw sdiff_finset_sdiff_singleton_eq_sdiff_singleton S s sInS},
  have bar: ∑ (x : V) in {s}, ∑ (y : V) in S \ {s}, f x y = ∑ (u : V) in S \ {s}, f s u :=
  by simp,
  linarith,
end

lemma flow_value_source_in_S {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V)
  (same_net : afn.network = ct.network) :
  mk_out afn.f {afn.network.source} - mk_in afn.f {afn.network.source} =
  mk_out afn.f ct.S - mk_in afn.f ct.S :=
begin
  set S := ct.S,
  set T := ct.T,
  set s := afn.network.source,
  set t := afn.network.sink,
  set f := afn.f,
  have singleton: s ∈ {s} := finset.mem_singleton.2 rfl,
  have sInS: s ∈ S :=
  begin
    have same_source: s = ct.network.source := (same_source_and_sink afn ct same_net).1,
    rw same_source,
    exact ct.sins,
  end,
  have sSubsetS: {s} ⊆  S := (finset.singleton_subset_iff).2 sInS,
  have disjS: disjoint {s} (S \ {s}) :=
    begin
      have sOut: s ∉ (S \ {s}) := finset.not_mem_sdiff_of_mem_right singleton,
      exact finset.disjoint_singleton_left.2 sOut,
    end,
  have sInCompl: {s} ⊆ V' \ (S \ {s}) :=
  begin
    have sIn: {s} ⊆ V' := finset.subset_univ {s},
    have conj: {s} ⊆ V' ∧ disjoint {s} (S \ {s}) := and.intro sIn disjS,
    exact finset.subset_sdiff.2 conj,
  end,
  have tNots: t ≠ s :=
  begin
    by_contradiction h,
    have contr: s = t := by rw ← h,
    exact absurd contr afn.source_not_sink,
  end,
  have tNotInS: t ∉ S :=
  begin
    have same_sink: t = ct.network.sink := (same_source_and_sink afn ct same_net).2,
    have tInT: t ∈ T := by {rw same_sink, exact ct.tint},
    have Tcomp : T = univ \ S := ct.Tcomp,
    have foo: S = univ \ (univ \ S) :=
    by {simp only [sdiff_sdiff_right_self, finset.inf_eq_inter, finset.univ_inter]},
    have Scomp : S = univ \ T := by {rw ← Tcomp at foo, exact foo},
    rw Scomp at *,
    exact finset.not_mem_sdiff_of_mem_right tInT,
  end,
  have seteq: V' \ (S \ {s}) \ {s} = V' \ S :=
  sdiff_finset_sdiff_singleton_eq_sdiff_singleton S s sInS,
  have union: V' \ S ∪ S \ {s} = V' \ {s} :=
  sdiff_finset_union_finset_eq_sdiff_singleton S s sInS,
  have disj: disjoint (V' \ S) (S \ {s}) := disjoint_sdiff_finset_sdiff_singleton S s,
  have disjTS: disjoint {t} {s} := finset.disjoint_singleton.2 (tNots),
  have expand: mk_out f {s} + (mk_out f (S \ {s}) - mk_in f (S \ {s})) - mk_in f {s}
  =  mk_out f {s} - mk_in f {s} :=
  begin
    have eq: mk_out f (S \ {s}) - mk_in f (S \ {s}) = 0 :=
    begin
      have h: (S \ {s}) ⊆ finset.univ \ {s,t} :=
      begin
        intros x xInSms,
        have xIn: x ∈ V' := finset.mem_univ x,
        have xInS: x ∈ S:= ((finset.mem_sdiff).1 xInSms).1,
        have xNotInT: x ∉ {t} :=
        begin
          by_contradiction h,
          have eq: x = t := finset.mem_singleton.1 h,
          rw eq at xInS,
          contradiction,
        end,
        have union: ({s}: finset V) ∪ {t} = {s,t} := by refl,
        have xNotInS: x ∉ {s} := ((finset.mem_sdiff).1 xInSms).2,
        have xOut: x ∉ {s,t} :=
        begin
          by_contradiction h,
          rw ← union at h,
          have inUnion: x ∈ {s} ∨ x ∈ {t} := finset.mem_union.1 h,
          have contr1: x ∈ {s} → false :=
          begin
            intro assumption,
            exact absurd assumption xNotInS,
          end,
          have contr2: x ∈ {t} → false :=
          begin
            intro assumption,
            exact absurd assumption xNotInT,
          end,
          exact or.elim inUnion contr1 contr2,
        end,
        have and: x ∈ V' ∧ x ∉ {s,t} := and.intro xIn xOut,
        exact finset.mem_sdiff.2 and,
      end,
      exact set_flow_conservation_eq afn (S \ {s}) h,
    end,
    exact add_zero_middle (mk_out f {s}) (mk_in f {s}) (mk_out f (S \ {s}) - mk_in f (S \ {s})) eq,
  end,
  have sum1: mk_out f {s} + mk_out f (S \ {s}) =
  mk_out f S + ∑ u in (S \ {s}), f s u + ∑ u in (S \ {s}), f u s :=
  begin
    unfold mk_out,
    have eq1: ∑ (x : V) in S, ∑ (y : V) in V' \ S, f x y =
    ∑ (x : V) in (S \ {s}) , ∑ (y : V) in V' \ S, f x y +
    ∑ (x : V) in {s}, ∑ (y : V) in V' \ S, f x y :=
    by {rw finset.sum_sdiff sSubsetS},
    have eq2: ∑ (x : V) in {s}, ∑ (y : V) in V' \ S, f x y = ∑ (y : V) in V' \ S, f s y := by simp,
    have eq3: ∑ (x : V) in (S \ {s}), ∑ (y : V) in V' \ (S \ {s}), f x y =
    ∑ (x : V) in (S \ {s}), f x s + ∑ (x : V) in (S \ {s}), ∑ (y : V) in V' \ S, f x y :=
    sum_sdiff_singleton_sum_sdiff_finset_sdiff_singleton f S s sInS,
    have eq4: ∑ (x : V) in {s}, ∑ (y : V) in V' \ {s}, f x y =
    ∑ (y : V) in V' \ S, f s y + ∑ (u : V) in S \ {s}, f s u :=
    begin
      have foo: ∑ (x : V) in {s}, ∑ (y : V) in V' \ {s}, f x y =
      ∑ (y : V) in V' \ {s}, f s y := by simp,
      rw foo,
      rw ← union,
      exact finset.sum_union disj,
    end,
    linarith
  end,
  have sum2: mk_in f (S \ {s}) + mk_in f {s} =
  mk_in f S + ∑ u in (S \ {s}), f s u + ∑ u in (S \ {s}), f u s :=
  begin
    unfold mk_in,
    have eq1: ∑ (x : V) in V' \ S, ∑ (y : V) in S, f x y =
    ∑ (x : V) in V' \ S, ∑ (y : V) in (S \ {s}), f x y +
    ∑ (x : V) in V' \ S, ∑ (y : V) in {s}, f x y :=
    in_expansion f S s sInS,
    have eq2: ∑ (x : V) in V' \ S, ∑ (y : V) in {s}, f x y = ∑ (u : V) in V' \ S, f u s :=
    by simp,
    have eq3: ∑ (x : V) in V' \ (S \ {s}), ∑ (y : V) in S \ {s}, f x y =
    ∑ (x : V) in V' \ S, ∑ (y : V) in S \ {s}, f x y + ∑ (u : V) in S \ {s}, f s u :=
    sum_sdiff_finset_sdiff_singleton_sum_sdiff_singleton f S s sInS,
    have eq4: ∑ (x : V) in V' \ {s}, ∑ (y : V) in {s}, f x y =
    ∑ (u : V) in V' \ S, f u s + ∑ (u : V) in S \ {s}, f u s :=
    begin
      have foo: ∑ (u : V) in V' \ S, f u s =
      ∑ (x : V) in V' \ S, ∑ (y : V) in {s}, f x y := by simp,
      have bar: ∑ (u : V) in S \ {s}, f u s =
      ∑ (x : V) in S \ {s}, ∑ (y : V) in {s}, f x y := by simp,
      rw ← union,
      rw [foo,bar],
      exact finset.sum_union disj,
    end,
    linarith,
  end,
  rw ← expand,
  rw add_sub,
  rw group_minus (mk_out f {s}) (mk_out f (S \ {s})) (mk_in f (S \ {s})) (mk_in f {s}),
  linarith
end

/-!
  Here is our first big lemma, weak duality.
  Every flow is less than or equal to the capacity of every cut in the same network.
-/

lemma weak_duality {V: Type*} [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V) (same_net : afn.network = ct.network):
  F_value afn ≤ cut_cap ct :=
begin
  set S := ct.S,
  set T:= ct.T,
  set s := afn.network.source,
  set t := afn.network.sink,
  unfold cut_cap,
  have lemma1: F_value afn = mk_out afn.f S - mk_in afn.f S :=
  by {unfold F_value, exact flow_value_source_in_S afn ct same_net},
  have lemma2: mk_out afn.f S ≤  mk_out ct.network.to_capacity.c S :=
  begin
    have no_overflow: mk_out afn.f S ≤ mk_out afn.network.to_capacity.c S :=
    begin
      unfold mk_out,
      have flowLEcut: ∀ (x y : V), (x ∈ S ∧ y ∈ V' \ S) →
      (afn.f x y ≤ afn.network.to_capacity.c x y) :=
      by {intros x y hyp, exact afn.no_overflow x y},
      exact finset.sum_le_sum (λ i hi, finset.sum_le_sum $ λ j hj, flowLEcut i j ⟨hi, hj⟩)
    end,
    unfold mk_out at no_overflow,
    rw same_net at no_overflow,
    exact no_overflow,
  end,
  have lemma3: F_value afn ≤ mk_out afn.f S :=
  begin
    rw lemma1,
    have obvs: mk_out afn.f S = mk_out afn.f S + 0 := by rw [add_zero],
    rw obvs,
    simp,
    unfold mk_in,
    have nonneg_flow: ∀ (u v : V), (u ∈ V' \ S ∧ v ∈ S) → afn.f u v ≥ 0 :=
    begin
      intros u v hyp,
      exact afn.non_neg_flow u v,
    end,
    exact finset.sum_nonneg (λ i hi, finset.sum_nonneg $ λ j hj, nonneg_flow i j ⟨hi, hj⟩),
  end,
  apply le_trans lemma3 lemma2,
end

def is_max_flow  {V : Type*}  [inst' : fintype V]
  (fn: active_flow_network V) : Prop :=
  ∀ fn' : active_flow_network V, fn.network = fn'.network → F_value fn' ≤ F_value fn

def is_min_cut {V : Type*}  [inst' : fintype V]
  (fn: cut V) : Prop := ∀ fn' : cut V, fn.network = fn'.network → cut_cap fn ≤ cut_cap fn'

lemma max_flow_criterion  {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V) (hsame_network : afn.network = ct.network):
  cut_cap ct = F_value afn -> is_max_flow afn :=
begin
  intros eq fn same_net,
  rw ← eq,
  have same_network: fn.network = ct.network := by {rw ← same_net, exact hsame_network},
  exact weak_duality (fn) (ct) (same_network),
end

lemma min_cut_criterion  {V : Type*}  [inst' : fintype V]
  (afn : active_flow_network V) (ct : cut V) (same_net: afn.network = ct.network) :
  cut_cap ct = F_value afn -> is_min_cut ct :=
begin
  intro eq,
  intros cut eq_net,
  rw eq,
  have h: afn.network = cut.network := by {rw same_net, exact eq_net,},
  exact weak_duality (afn) (cut) (h),
end

-- /-!
--   We now define our residual network. Our goal is to prove no_augm_path.
-- -/

-- noncomputable
-- def mk_rsf {V : Type*}  [inst' : fintype V] -- stays for residual flow
--   (afn : active_flow_network V)
--   (u v : V) : ℝ :=
--   if  afn.network.is_edge u v
--   then afn.network.c u v - afn.f u v
--   else if afn.network.is_edge v u
--         then afn.f v u
--         else 0

-- structure residual_network  (V : Type*)  [inst' : fintype V] :=
--   (afn : active_flow_network V)
--   (f' : V -> V -> ℝ)
--   (f_def : f' = mk_rsf afn)
--   (is_edge : V -> V -> Prop)
--   (is_edge_def : is_edge = λ u v, f' u v > 0)

-- noncomputable
-- def mk_rsn {V : Type*} [fintype V] -- stays for residual network
--   (afn : active_flow_network V) : residual_network V :=
--   ⟨afn, mk_rsf afn, rfl, λ u v, mk_rsf afn u v > 0 , rfl⟩

-- universe u

-- /-
--   We define a recursive structure returning the path between two vertices,
--   if such a path exists, given the edges in the graph.
-- -/
-- inductive path {V : Type u } (is_edge : V -> V -> Prop) (a : V) : V → Type (u + 1)
-- | nil  : path a
-- | cons : Π {b c : V}, path b → (is_edge b c) → path c

-- def no_augmenting_path {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V) : Prop :=
--   ∀ t : V, ∀ p : path rsn.is_edge rsn.afn.network.source t, ¬ (t = rsn.afn.network.sink)

-- /-
--   Given two vertices $u and $v, returns true if and only if (u,v) is an edge in a given path.
-- -/
-- def path.in {V : Type u}
--   {is_edge : V -> V -> Prop}
--   (u v : V)
--   {s : V} : ∀ {t : V}, path is_edge s t -> Prop
--   | t (@path.nil  _ is_edge' a)  := u = v
--   | t (@path.cons _ _ _ t' _ p _)  := (u = t' ∧ v = t) ∨ (@path.in t' p)

-- lemma residual_capacity_non_neg {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V) : ∀ u v : V,  0 ≤ rsn.f' u v :=
-- begin
--   intros u v,
--   cases rsn,
--   simp only,
--   rw rsn_f_def,
--   unfold mk_rsf,
--   have foo := classical.em (rsn_afn.network.to_capacity.to_digraph.is_edge u v),
--   cases foo,
--   { simp only [foo, if_true, sub_nonneg, rsn_afn.no_overflow], },
--   { simp only [foo, if_false], clear foo,
--     have bar := classical.em (rsn_afn.network.to_capacity.to_digraph.is_edge v u),
--     cases bar,
--     { have h := rsn_afn.non_neg_flow v u,
--       simp only [bar, h, if_true],
--       linarith, },
--     { simp only [bar, if_false] }, },
-- end

-- lemma positive_residual_flow {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V) (u v : V) : rsn.is_edge u v → rsn.f' u v > 0 :=
-- begin
--   intro edge,
--   rw rsn.is_edge_def at edge,
--   exact edge,
-- end

-- /-!
--   Here is our second big lemma, if the active flow is maximum,
--   then no augmenting path exists in the residual network.
-- -/

-- lemma no_augm_path {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V) : (is_max_flow rsn.afn) -> no_augmenting_path rsn :=
-- begin
--   intros max_flow x exists_path,
--   by_contradiction is_sink,
--   set s := rsn.afn.network.source,
--   set t := rsn.afn.network.sink,
--   have augm_path: path rsn.is_edge s t := by {rw is_sink at exists_path, exact exists_path},
--   have exists_augm_path: ¬no_augmenting_path rsn :=
--   begin
--     unfold no_augmenting_path,
--     push_neg,
--     use x,
--     by_contradiction h,
--     have contr: x ≠ t := h exists_path,
--     exact absurd is_sink contr,
--   end,
--   --all vertices in the augmenting path
--   set vertices := set.to_finset ({t} ∪ { x | (∃ y: V, exists_path.in x y) }),
--   -- set of all flow values in the augmenting path
--   set flows :=
--   set.to_finset (function.uncurry rsn.f' '' {e ∈ vertices ×ˢ vertices | exists_path.in e.1 e.2}),
--   have nonemp: flows.nonempty :=
--   begin
--     by_contradiction h,
--     have empty: flows = ∅ := finset.not_nonempty_iff_eq_empty.1 h,
--     have foo: ∀ v : V, exists_path.in v t → flows ≠ ∅ :=
--     begin
--       intros v hyp,
--       have t_in_vertices: t ∈ vertices := by simp,
--       have v_in_vertices: v ∈ vertices :=
--       begin
--         simp only [set.mem_to_finset, set.mem_set_of_eq],
--         have baz: exists_path.in v t := hyp,
--         have exist: ∃ (y : V), path.in v y exists_path := by {use t, exact hyp},
--         have mem: v ∈ {x_1 : V | ∃ (y : V), path.in x_1 y exists_path} :=
--         by {simp only [set.mem_set_of_eq], exact exist},
--         have or: v ∈ {t} ∨ v ∈ {x_1 : V | ∃ (y : V), path.in x_1 y exists_path} :=
--         or.intro_right (v ∈ {t}) mem,
--         exact (set.mem_union v {t} ({x_1 : V | ∃ (y : V), path.in x_1 y exists_path})).2 or,
--       end,
--       have contr: rsn.f' v t ∈ flows :=
--       begin
--         simp only [true_and, set.singleton_union, finset.mem_univ, set.to_finset_congr,
--           true_or, eq_self_iff_true, set.to_finset_set_of, finset.mem_insert,
--           set.to_finset_insert, finset.mem_filter, vertices] at v_in_vertices,
--         apply v_in_vertices.elim;
--         intro hypo,
--         {
--           simp only [hypo, set.mem_to_finset, set.coe_to_finset, set.singleton_union,
--             set.mem_image, set.mem_sep_iff, set.mem_prod, set.mem_insert_iff, set.mem_set_of_eq,
--             prod.exists, function.uncurry_apply_pair, set.to_finset_nonempty,
--             set.nonempty_image_iff, set.to_finset_eq_empty,
--             set.image_eq_empty,set.sep_eq_empty_iff_mem_false, and_imp, prod.forall,
--             eq_self_iff_true, true_or] at *,
--           use [t, t],
--           simpa,
--         },
--         {
--           simp only [set.singleton_union, set.mem_image, set.mem_to_finset,
--           set.coe_to_finset, prod.exists],
--           use [v, t],
--           simp [hypo, hyp]
--         },
--       end,
--       exact finset.ne_empty_of_mem contr,
--     end,
--     have bar: ∃ v : V, exists_path.in v t := -- exists augmenting path
--     begin
--       by_contradiction h,
--       push_neg at h,
--       have no_augm_path: no_augmenting_path rsn := by sorry,
--       exact absurd no_augm_path exists_augm_path,
--     end,
--     have contr: flows ≠ ∅ := exists.elim bar foo,
--     exact absurd empty contr,
--   end,
--   set d := flows.min' nonemp, -- the minimum flow in the augmenting path
--   have pos: 0 < d :=
--   begin
--     have mem: d ∈ flows := finset.min'_mem flows nonemp,
--     have pos: ∀ f : ℝ , f ∈ flows → f > 0 :=
--     begin
--       intros f hyp,
--       simp only [set.mem_to_finset, set.mem_set_of_eq, set.coe_to_finset, set.singleton_union,
--       set.mem_image, set.mem_sep_iff, set.mem_prod, set.mem_insert_iff, prod.exists,
--       function.uncurry_apply_pair] at hyp,
--       obtain ⟨a, b, hyp, hyp'⟩ := hyp,
--       rw [← hyp'],
--       apply positive_residual_flow,
--       sorry,
--     end,
--     exact pos d mem,
--   end,
--   set better_flow: active_flow_network V :=
--   ⟨rsn.afn.network,
--   (λ u v : V, if rsn.afn.network.is_edge u v then (if exists_path.in u v then rsn.afn.f u v + d
--               else (if exists_path.in v u then rsn.afn.f u v - d else rsn.afn.f u v)) else 0),
--   begin -- source ≠ sink
--     exact rsn.afn.source_not_sink,
--   end,
--   begin -- non_neg_flow
--     intros u v,
--     by_cases edge: rsn.afn.network.is_edge u v,
--     {
--       simp only [edge, if_true],
--       by_cases h: exists_path.in u v,
--       {
--         have nonneg: rsn.afn.f u v ≥ 0 := rsn.afn.non_neg_flow u v,
--         simp only [h, if_true],
--         linarith,
--       },
--       {
--         by_cases h': exists_path.in v u,
--         {
--           simp only [h, if_false, h', if_true],
--           have ine: d ≤ rsn.afn.f u v :=
--           begin
--             have minimality: d ≤ rsn.f' v u :=
--             begin
--               have min: ∀ f : ℝ , f ∈ flows → d ≤ f :=
--               by {intros f hf, exact finset.min'_le flows f hf},
--               have mem: rsn.f' v u ∈ flows :=
--               begin
--                 have foo: ∃ y : V, exists_path.in v y := by {use u, exact h'},
--                 simp only [set.mem_image, set.mem_to_finset, set.coe_to_finset, prod.exists],
--                   use [v, u],
--                   simp [foo, h'],
--                   sorry,
--               end,
--               exact min (rsn.f' v u) mem,
--             end,
--             have eq: rsn.f' v u = rsn.afn.f u v :=
--             begin
--               rw rsn.f_def,
--               unfold mk_rsf,
--               have notAnd := rsn.afn.network.nonsymmetric u v,
--               simp only [not_and] at notAnd,
--               have notEdge: ¬ rsn.afn.network.is_edge v u := notAnd edge,
--               simp only [notEdge, if_false, edge, if_true],
--             end,
--             rw ← eq,
--             exact minimality,
--           end,
--           linarith,
--         },
--         {
--           simp only [h, if_false, h', if_false],
--           exact rsn.afn.non_neg_flow u v,
--         },
--       },
--     },
--     {
--       simp only [edge, if_false],
--       linarith,
--     },
--   end,
--   begin -- no_overflow
--     intros u v,
--     by_cases edge: rsn.afn.network.is_edge u v,
--     {
--       simp only [edge, if_true],
--       by_cases h: exists_path.in u v,
--       {
--         have h1: rsn.afn.f u v + d ≤ rsn.afn.network.to_capacity.c u v :=
--         begin
--           have h2: rsn.afn.f u v + rsn.f' u v ≤ rsn.afn.network.to_capacity.c u v :=
--           begin
--               have eq: rsn.f' u v = rsn.afn.network.c u v - rsn.afn.f u v :=
--               by {rw rsn.f_def, unfold mk_rsf, simp only [edge, if_true, h, if_true]},
--               rw eq,
--               linarith,
--           end,
--           have h3: d ≤ rsn.f' u v :=
--           begin
--             have min: ∀ f : ℝ , f ∈ flows → d ≤ f :=
--             by {intros f hf, exact finset.min'_le flows f hf},
--             have mem: rsn.f' u v ∈ flows :=
--             begin
--               have foo: ∃ y : V, exists_path.in u y := by {use v, exact h},
--               simp only [set.mem_image, set.mem_to_finset, set.coe_to_finset, prod.exists],
--               use [u, v],
--               simp [foo, h],
--               sorry,
--             end,
--             exact min (rsn.f' u v) mem,
--           end,
--           have h4: rsn.afn.f u v + d ≤ rsn.afn.f u v + rsn.f' u v := by {linarith},
--           exact le_trans h4 h2
--         end,
--         simp only [h, if_true],
--         exact h1,
--       },
--       {
--         by_cases h': exists_path.in v u,
--           {
--             have h1: rsn.afn.f u v ≤ rsn.afn.network.to_capacity.c u v :=
--             rsn.afn.no_overflow u v,
--             simp only [h, if_false, h', if_true],
--             linarith,
--           },
--           {
--             simp only [h, if_false, h', if_false],
--             exact rsn.afn.no_overflow u v,
--           },
--       },
--     },
--     {
--       simp only [edge, if_false],
--       have cap: rsn.afn.network.c u v = 0 := rsn.afn.network.vanishes u v edge,
--       linarith,
--     },
--   end,
--   begin --no_edges_in_source
--     exact rsn.afn.no_edges_in_source,
--   end,
--   begin --no_edges_out_sink
--     exact rsn.afn.no_edges_out_sink,
--   end,
--   begin -- conservation
--     intros v vNotSinkSource,
--       have union: ({s}: finset V) ∪ ({t}: finset V) = {s,t} := by refl,
--     have vNotSource: v ≠ rsn.afn.network.source :=
--     begin
--       by_contradiction h,
--       have vIn: v ∈ ({s}: finset V) ∪ ({t}: finset V) :=
--       begin
--         have vSource: v ∈ {s} := finset.mem_singleton.2 h,
--         have vOR: v ∈ {s} ∨ v ∈ {t} := or.intro_left (v ∈ {t}) vSource,
--         exact finset.mem_union.2 vOR,
--       end,
--       rw union at vIn,
--       have vNotIn: v ∉ ({s}: finset V) ∪ ({t}: finset V) :=
--       by {rw union, exact (finset.mem_sdiff.1 vNotSinkSource).2},
--       exact absurd vIn vNotIn,
--     end,
--     have vNotSink: v ≠ rsn.afn.network.sink :=
--     begin
--       by_contradiction h,
--       have vIn: v ∈ ({s}: finset V) ∪ ({t}: finset V) :=
--       begin
--         have vSink: v ∈ {t} := finset.mem_singleton.2 h,
--         have vOR: v ∈ {s} ∨ v ∈ {t} := or.intro_right (v ∈ {s}) vSink,
--         exact finset.mem_union.2 vOR,
--       end,
--       rw union at vIn,
--       have vNotIn: v ∉ ({s}: finset V) ∪ ({t}: finset V) :=
--       by {rw union, exact (finset.mem_sdiff.1 vNotSinkSource).2},
--       exact absurd vIn vNotIn,
--     end,
--     set newf := (λ (u v : V), ite (rsn.afn.network.is_edge u v)
--     (ite (path.in u v exists_path) (rsn.afn.f u v + d)
--     (ite (path.in v u exists_path) (rsn.afn.f u v - d) (rsn.afn.f u v))) 0),
--     by_cases h: v ∈ vertices,
--     {
--       -- Issues: How are we looking into cases for the cardinality of predecessor and ancestor?
--       -- How do we procced after for picking these edges?
--       -- set predecessor := {u | exists_path.in u v},
--       -- set ancestor := {w | exists_path.in v w},
--       -- have h1: mk_out rsn.afn.f {v} = mk_in rsn.afn.f {v} :=
--       -- rsn.afn.conservation v vNotSinkSource,
--       -- rw [h2,h3,h1]
--       sorry,
--     },
--     {
--       have h1: ∀ u : V, ¬exists_path.in u v :=
--       begin
--         by_contradiction h',
--         push_neg at h',
--         have ancestor: ∃w : V, exists_path.in v w := by sorry, -- v ≠ t
--         have contr: v ∈ vertices :=
--         begin
--           simp only [set.mem_to_finset, set.mem_set_of_eq],
--           have mem: v ∈ {x_1 : V | ∃ (y : V), path.in x_1 y exists_path} :=
--           by {simp only [set.mem_set_of_eq], exact ancestor},
--           have or: v ∈ {t} ∨ v ∈ {x_1 : V | ∃ (y : V), path.in x_1 y exists_path} :=
--           or.intro_right (v ∈ {t}) mem,
--           exact (set.mem_union v {t} ({x_1 : V | ∃ (y : V), path.in x_1 y exists_path})).2 or,
--         end,
--         exact absurd contr h,
--       end,
--       have h2: ∀ w : V, ¬exists_path.in v w :=
--       begin
--         by_contradiction h',
--         push_neg at h',
--         have contr: v ∈ vertices :=
--         begin
--           simp only [set.mem_to_finset, set.mem_set_of_eq],
--           have mem: v ∈ {x_1 : V | ∃ (y : V), path.in x_1 y exists_path} :=
--           by {simp only [set.mem_set_of_eq], exact h'},
--           have or: v ∈ {t} ∨ v ∈ {x_1 : V | ∃ (y : V), path.in x_1 y exists_path} :=
--           or.intro_right (v ∈ {t}) mem,
--           exact (set.mem_union v {t} ({x_1 : V | ∃ (y : V), path.in x_1 y exists_path})).2 or,
--         end,
--         exact absurd contr h,
--       end,
--       have h3: ∀ u : V, newf u v = rsn.afn.f u v :=
--       begin
--         intro u,
--         by_cases edge: rsn.afn.network.is_edge u v,
--         {
--           have noEdge: ¬exists_path.in u v := h1 u,
--           have noReversedEdge: ¬exists_path.in v u := h2 u,
--           have simplify: newf u v = ite (rsn.afn.network.is_edge u v)
--           (ite (path.in u v exists_path) (rsn.afn.f u v + d)
--           (ite (path.in v u exists_path) (rsn.afn.f u v - d) (rsn.afn.f u v))) 0 := by simp,
--           rw simplify,
--           simp only [edge, if_true, noEdge, if_false, noReversedEdge, if_false],
--         },
--         {
--           have simplify: newf u v = ite (rsn.afn.network.is_edge u v)
--           (ite (path.in u v exists_path) (rsn.afn.f u v + d)
--           (ite (path.in v u exists_path) (rsn.afn.f u v - d) (rsn.afn.f u v))) 0 := by simp,
--           rw simplify,
--           simp only [edge, if_false],
--           have zeroFlow: rsn.afn.f u v = 0 := f_vanishes_outside_edge rsn.afn u v edge,
--           linarith,
--         },
--       end,
--       have h4: ∀ w : V, newf v w = rsn.afn.f v w :=
--       begin
--         intro w,
--         by_cases edge: rsn.afn.network.is_edge v w,
--         {
--           have noEdge: ¬exists_path.in w v := h1 w,
--           have noReversedEdge: ¬exists_path.in v w := h2 w,
--           have simplify: newf v w = ite (rsn.afn.network.is_edge v w)
--           (ite (path.in v w exists_path) (rsn.afn.f v w + d)
--           (ite (path.in w v exists_path) (rsn.afn.f v w - d) (rsn.afn.f v w))) 0 := by simp,
--           rw simplify,
--           simp only [edge, if_true, noReversedEdge, if_false, noEdge, if_false],
--       },
--       {
--         have simplify: newf v w = ite (rsn.afn.network.is_edge v w)
--         (ite (path.in v w exists_path) (rsn.afn.f v w + d)
--         (ite (path.in w v exists_path) (rsn.afn.f v w - d) (rsn.afn.f v w))) 0 := by simp,
--         rw simplify,
--         simp only [edge, if_false],
--         have zeroFlow: rsn.afn.f v w = 0 := f_vanishes_outside_edge rsn.afn v w edge,
--         linarith,
--       },
--       end,
--       have eqIn: mk_in newf {v} = mk_in rsn.afn.f {v} :=
--       begin
--         unfold mk_in,
--         have eq1:  ∑ (x : V) in V' \ {v}, ∑ (y : V) in {v}, newf x y =
--         ∑ (x : V) in V' \ {v}, newf x v := by simp,
--         have eq2: ∑ (x : V) in V' \ {v}, ∑ (y : V) in {v}, rsn.afn.f x y =
--         ∑ (x : V) in V' \ {v}, rsn.afn.f x v := by simp,
--         rw [eq1, eq2],
--         exact finset.sum_congr rfl (λ u h, h3 u),
--       end,
--       have eqOut: mk_out newf {v} = mk_out rsn.afn.f {v} :=
--       begin
--         unfold mk_out,
--         have eq1: ∑ (x : V) in {v}, ∑ (y : V) in V' \ {v}, newf x y =
--         ∑ (y : V) in V' \ {v}, newf v y := by simp,
--         have eq2: ∑ (x : V) in {v}, ∑ (y : V) in V' \ {v}, rsn.afn.f x y =
--         ∑ (y : V) in V' \ {v}, rsn.afn.f v y := by simp,
--         rw [eq1, eq2],
--         exact finset.sum_congr rfl (λ u h, h4 u),
--       end,
--       rw [eqIn,eqOut],
--       exact rsn.afn.conservation v vNotSinkSource,
--     },
--   end
--   ⟩,
--   have flow_value: F_value better_flow = F_value rsn.afn + d :=
--   begin
--     unfold F_value,
--     set source := better_flow.network.source,
--     have h1: mk_out better_flow.f {source} =
--     mk_out rsn.afn.f {source} + d :=
--     by sorry,
--     -- take the edge with the added flow
--     -- Issue: How do we prove that there is exactly one edge? How do we pick exactly that edge?
--     have h2: mk_in better_flow.f {source} =
--     mk_in rsn.afn.f {source} :=
--     begin
--       have h3: mk_in better_flow.f {source} = 0 :=
--       begin
--         unfold mk_in,
--         have eq: ∑ (x : V) in V' \ {source}, ∑ (y : V) in {source}, better_flow.f x y =
--         ∑ (x : V) in V' \ {source}, better_flow.f x source := by simp,
--         have zeroFlow: ∀ x : V, better_flow.f x source = 0 :=
--         begin
--           intro x,
--           have noEdge: ¬better_flow.network.is_edge x source :=
--           better_flow.no_edges_in_source x,
--           exact f_vanishes_outside_edge better_flow x source noEdge,
--         end,
--         rw eq,
--         exact finset.sum_eq_zero (λ x h, zeroFlow x),
--       end,
--       have h4: mk_in rsn.afn.f {source} = 0 :=
--       begin
--         unfold mk_in,
--         set s := rsn.afn.network.source,
--         have sameSource: s = source := by refl,
--         have eq: ∑ (x : V) in V' \ {s}, ∑ (y : V) in {s}, rsn.afn.f x y =
--         ∑ (x : V) in V' \ {s}, rsn.afn.f x s := by simp,
--         have zeroFlow: ∀ x : V, rsn.afn.f x s = 0 :=
--         begin
--           intro x,
--           have noEdge: ¬rsn.afn.network.is_edge x s :=
--           rsn.afn.no_edges_in_source x,
--           exact f_vanishes_outside_edge rsn.afn x s noEdge,
--         end,
--         rw eq,
--         exact finset.sum_eq_zero (λ x h, zeroFlow x),
--       end,
--       rw ← h4 at h3,
--       exact h3,
--     end,
--     rw [h1,h2],
--     linarith
--   end,
--   have le: F_value rsn.afn ≥ F_value better_flow :=
--   begin
--     have same_net: better_flow.network = rsn.afn.network := by simp,
--     unfold is_max_flow at max_flow,
--     exact max_flow better_flow same_net,
--   end,
--   have lt: F_value rsn.afn < F_value better_flow :=
--   begin
--     rw flow_value,
--     have h1: F_value rsn.afn - F_value rsn.afn < d := by linarith,
--     have h2: F_value rsn.afn < F_value rsn.afn + d := lt_add_of_sub_left_lt h1,
--     exact gt_iff_lt.2 h2,
--   end,
--   have nlt: ¬F_value rsn.afn < F_value better_flow := not_lt_of_ge le,
--   exact absurd lt nlt,
-- end

-- /-!
--   We will prove that there exists a cut with value equal to the max flow in the same network.
--   We will use a constructive proof, so we will construct our minimum cut.
-- -/

-- noncomputable
-- def mk_cut_set {V : Type u} [inst' : fintype V] -- The source set for the minimum cut
--   (rsn : residual_network V) : finset V :=
--   {x | (∃ p : path rsn.is_edge rsn.afn.network.source x, true)}.to_finset

-- noncomputable
-- def mk_cut_from_S {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V)
--   (hno_augmenting_path : no_augmenting_path rsn)
--   (S : finset V) (hS : S = mk_cut_set rsn) : cut V :=
-- ⟨rsn.afn.network, S, V' \ S,
--   begin
--     rw hS,
--     unfold mk_cut_set,
--     simp only [set.mem_to_finset, set.mem_set_of_eq],
--     exact exists.intro path.nil trivial,
--   end,
--   begin
--     rw hS,
--     unfold mk_cut_set,
--     simp only [mem_sdiff, mem_univ, set.mem_to_finset, set.mem_set_of_eq, true_and],
--     intro p,
--     unfold no_augmenting_path at hno_augmenting_path,
--     specialize hno_augmenting_path rsn.afn.network.sink,
--     simp only [eq_self_iff_true, not_true] at hno_augmenting_path,
--     apply exists.elim p,
--     intros p h,
--     specialize hno_augmenting_path p,
--     exact hno_augmenting_path,
--   end,
-- rfl⟩

-- lemma s_t_not_connected {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V)
--   (S : finset V) (hS : S = mk_cut_set rsn) :
--   ∀ u ∈ S, ∀ v ∈ (V' \ S), ¬ rsn.is_edge u v :=
-- begin
--   intros u uInS v vInT is_edge_u_v,
--   rw hS at *,
--   unfold mk_cut_set at *,
--   simp only [set.mem_to_finset, set.mem_set_of_eq, mem_sdiff, mem_univ, true_and] at *,
--   apply exists.elim uInS,
--   intros p _,
--   have tmp := path.cons p is_edge_u_v,
--   apply vInT,
--   exact exists.intro tmp trivial,
-- end

-- lemma residual_capacity_zero {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V)
--   (ct : cut V)
--   (h_eq_network : rsn.afn.network = ct.network)
--   (h: ∀ u ∈ ct.S, ∀ v ∈ ct.T, ¬ rsn.is_edge u v) :
--   ∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.f' u v = 0 :=
-- begin
--   intros u uInS v vInT,
--   specialize h u uInS v vInT,
--   rw rsn.is_edge_def at h,
--   simp only [not_lt] at h,
--   have hge := residual_capacity_non_neg rsn u v,
--   exact ge_antisymm hge h,
-- end

-- lemma min_max_cap_flow {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V)
--   (ct : cut V)
--   (h_eq_network : rsn.afn.network = ct.network)
--   (h: ∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.f' u v = 0 ) :
--   (∀ u ∈ ct.S, ∀ v ∈ ct.T, rsn.afn.f u v = rsn.afn.network.c u v) ∧
--   (∀ u ∈ ct.T, ∀ v ∈ ct.S, rsn.afn.f u v = 0) :=
-- begin
--   split,
--   {
--     intros u uInS v vInT,
--     specialize h u uInS v vInT,
--     rw rsn.f_def at h,
--     unfold mk_rsf at h,
--     have foo := classical.em (rsn.afn.network.to_capacity.to_digraph.is_edge u v),
--     cases foo,
--     {
--       simp only [foo, if_true] at h,
--       linarith,
--     },
--     {
--       simp only [foo, if_false, ite_eq_right_iff] at h,
--       have bar := rsn.afn.network.vanishes u v foo,
--       rw bar,
--       clear foo h,
--       have baz := rsn.afn.non_neg_flow u v,
--       have bark := rsn.afn.no_overflow u v,
--       linarith,
--     }
--   },
--   {
--     intros v vInT u uInS,
--     specialize h u uInS v vInT,
--     rw rsn.f_def at h,
--     unfold mk_rsf at h,
--     have foo := classical.em (rsn.afn.network.to_capacity.to_digraph.is_edge u v),
--     cases foo,
--     {
--       have bark := rsn.afn.network.nonsymmetric u v,
--       simp only [not_and] at bark,
--       specialize bark foo,
--       have bar := rsn.afn.non_neg_flow v u,
--       have baz := rsn.afn.no_overflow v u,
--       have blurg := rsn.afn.network.vanishes v u bark,
--       linarith,
--     },
--     {
--       simp only [foo, if_false, ite_eq_right_iff] at h,
--       clear foo,
--       have bar := classical.em (rsn.afn.network.to_capacity.to_digraph.is_edge v u),
--       cases bar,
--       {
--         exact h bar,
--       },
--       {
--         have blurg := rsn.afn.non_neg_flow v u,
--         have bark := rsn.afn.no_overflow v u,
--         have baz := rsn.afn.network.vanishes v u bar,
--         linarith,
--       },
--     },
--   }
-- end

-- lemma f_value_eq_out {V : Type*} [inst' : fintype V]
--     (ct : cut V)
--     (afn : active_flow_network V)
--     (h_eq_network : afn.network = ct.network)
--     (h : (∀ u ∈ ct.T, ∀ v ∈ ct.S, afn.f u v = 0)) :
--     F_value afn = mk_out afn.f ct.S :=
-- begin
--   dsimp [F_value],
--   rw flow_value_source_in_S afn ct h_eq_network,
--   dsimp [mk_in],
--   simp_rw [← ct.Tcomp],
--   simp only [sub_eq_self],
--   have sum_eq_sum_zero : ∑ (x : V) in ct.T, ∑ y in ct.S, (afn.f x y) =
--   ∑ x in ct.T, ∑ y in ct.S, 0 :=
--   begin
--     apply finset.sum_congr rfl,
--     intros x xInT,
--     apply finset.sum_congr rfl,
--     intros y yInS,
--     exact h x xInT y yInS,
--   end,
--   rw sum_eq_sum_zero,
--   simp only [sum_const_zero],
-- end

-- lemma cut_cap_eq_out {V : Type*} [inst' : fintype V]
--   (ct : cut V)
--   (afn : active_flow_network V)
--   (h_eq_network : afn.network = ct.network)
--   (h : (∀ u ∈ ct.S, ∀ v ∈ V' \ ct.S, afn.f u v = afn.network.c u v) ∧
--        (∀ u ∈ V' \ ct.S, ∀ v ∈ ct.S, afn.f u v = 0)) :
--       mk_out afn.f ct.S = cut_cap ct :=
-- begin
--   cases h with h_flow_eq_cap h_flow_zero,
--   dsimp [cut_cap, mk_out],
--   apply finset.sum_congr rfl,
--   intros x xInS,
--   rw ← ct.Tcomp at *,
--   apply finset.sum_congr rfl,
--   intros y yInT,
--   simp [h_eq_network, h_flow_eq_cap x xInS y yInT],
-- end

-- lemma eq_on_res_then_on_sum {V : Type*} [inst' : fintype V]
--   (A : finset V) (B : finset V) (f : V → V → ℝ) (g : V → V → ℝ)
--   (eq_on_res : ∀ u ∈ A, ∀ v ∈ B, f u v = g u v) :
--   ∑ (u : V) in A, ∑ (v : V) in B, f u v = ∑ (u : V) in A, ∑ (v : V) in B, g u v :=
-- begin
--   apply finset.sum_congr rfl,
--   intros a aInA,
--   apply finset.sum_congr rfl,
--   intros b bInB,
--   exact eq_on_res a aInA b bInB,
-- end

-- /-!
--   Here is our last big lemma, if there is no augmenting path in the resiual network, then
--   there exists a cut with a capacity equal to the value of the active flow in the same network.
-- -/

-- lemma existence_of_a_cut {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V)
--   (hno_augmenting_path : no_augmenting_path rsn) :
--   (∃c : cut V, rsn.afn.network = c.network ∧ cut_cap c = F_value rsn.afn) :=
-- begin
--   let S : finset V := mk_cut_set rsn,
--   let T := V' \ S,
--   let min_cut := mk_cut_from_S (rsn) (hno_augmenting_path) (S) rfl,
--   have same_net : rsn.afn.network = min_cut.network := by refl,
--   have subtract: ∀ x y : ℝ, (x=y) ↔ y-x=0 :=
--   by {intros x y, split, intro heq, linarith, intro heq, linarith},
--   have cf_vanishes_on_pipes: ∀ u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S, rsn.f' u v = 0 :=
--   begin
--     intros u uInS v vInNS,
--     by_contradiction h,
--     have edge: rsn.is_edge u v :=
--     begin
--       by_contradiction h',
--       have contr: rsn.f' u v = 0 :=
--       begin
--         rw rsn.is_edge_def at h',
--         simp only [not_lt] at h',
--         have hge := residual_capacity_non_neg rsn u v,
--         exact ge_antisymm hge h',
--       end,
--       contradiction
--     end,
--     have notEdge: ¬ rsn.is_edge u v := s_t_not_connected rsn S rfl u uInS v vInNS,
--     contradiction
--   end,
--   have cf_vanishes_on_pipes_spec: ∀ u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S,
--     (rsn.afn.network.is_edge u v) → (rsn.afn.network.c u v - rsn.afn.f u v = 0) :=
--   begin
--     intros u uInS v vInT is_edge,
--     have h1: mk_rsf rsn.afn u v = rsn.afn.network.c u v - rsn.afn.f u v :=
--     by {unfold mk_rsf, simp only [is_edge, if_true]},
--     rw ← h1,
--     have h2: mk_rsf rsn.afn u v = rsn.f' u v := by {rw rsn.f_def},
--     rw h2,
--     exact cf_vanishes_on_pipes u uInS v vInT,
--   end,
--   have eq_on_pipes: ∀ u ∈ min_cut.S, ∀ v ∈ V' \ min_cut.S, rsn.afn.f u v =
--   rsn.afn.network.c u v :=
--   begin
--     intros u uInS v vInT,
--     by_cases edge: rsn.afn.network.is_edge u v,
--     {
--       have h: rsn.afn.network.to_capacity.c u v - rsn.afn.f u v = 0 :=
--       cf_vanishes_on_pipes_spec u uInS v vInT edge,
--       linarith,
--     },
--     {
--       rw rsn.afn.network.vanishes u v edge,
--       exact f_vanishes_outside_edge (rsn.afn) (u) (v) (edge),
--     },
--   end,
--   have no_backflow: ∀ (u v : V), (u ∈ V' \ min_cut.S ∧ v ∈ min_cut.S) → rsn.afn.f u v = 0 :=
--   begin
--     intros u v hyp,
--     exact (min_max_cap_flow rsn min_cut same_net cf_vanishes_on_pipes).2 u hyp.1 v hyp.2,
--   end,
--   have cut_eq_flow: cut_cap min_cut = F_value rsn.afn :=
--   begin
--     rw F_value,
--     simp only,
--     rw flow_value_source_in_S rsn.afn min_cut same_net,
--     have no_input : mk_in rsn.afn.f min_cut.S = 0 :=
--     begin
--       rw mk_in,
--       exact finset.sum_eq_zero (λ i hi, finset.sum_eq_zero $ λ j hj, no_backflow i j ⟨hi, hj⟩),
--     end,
--     rw no_input,
--     simp only [sub_zero],
--     have flow_eq_cap_on_cut : mk_out rsn.afn.f min_cut.S = mk_out rsn.afn.network.c min_cut.S :=
--     begin
--       unfold mk_out,
--       rw eq_on_res_then_on_sum
--       (min_cut.S) (V' \ min_cut.S) (rsn.afn.f) (rsn.afn.network.to_capacity.c) (eq_on_pipes),
--     end,
--     rw flow_eq_cap_on_cut,
--     refl,
--   end,
--   use min_cut,
--   split,
--   {exact same_net},
--   exact cut_eq_flow
-- end

-- /-!
--   Finally, our biggest result, the max-flow min-cut theorem!
--   If a maximum flow exists, its value is equal to the capacity of the min-cut.
-- -/

-- theorem max_flow_min_cut {V : Type*} [inst' : fintype V]
--   (rsn : residual_network V) (c: cut V) (same_network: rsn.afn.network = c.network) :
--   (is_max_flow rsn.afn ∧ is_min_cut c) → (F_value rsn.afn = cut_cap c) :=
-- begin
--   rintros ⟨max_flow, min_cut⟩ ,
--   have noAugPath: no_augmenting_path rsn := no_augm_path rsn max_flow,
--   have existsCut: ∃cut : cut V, rsn.afn.network = cut.network ∧
--   cut_cap cut = F_value rsn.afn := existence_of_a_cut rsn noAugPath,
--   have max_flow_min_cut: ∀ cut : cut V,
--   (rsn.afn.network = cut.network ∧ cut_cap cut = F_value rsn.afn) →
--   (F_value rsn.afn = cut_cap c) :=
--   begin
--     rintros cut ⟨same_net, eq⟩,
--     have h1: is_min_cut cut := min_cut_criterion rsn.afn cut same_net eq,
--     have h2: is_min_cut c := min_cut,
--     have same_net1: cut.network = c.network := by {rw ← same_network, rw ← same_net},
--     have same_net2: c.network = cut.network := by rw ← same_net1,
--     have same_val: cut_cap cut = cut_cap c :=
--     begin
--       have le1: cut_cap cut ≤ cut_cap c :=
--       by {unfold is_min_cut at h1, exact h1 c same_net1},
--       have le2: cut_cap c ≤ cut_cap cut :=
--       by {unfold is_min_cut at h2, exact h2 cut same_net2},
--       exact le_antisymm le1 le2,
--     end,
--     rw ← eq,
--     exact same_val,
--   end,
--   exact exists.elim existsCut max_flow_min_cut,
-- end
