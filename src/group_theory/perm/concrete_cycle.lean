/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import group_theory.perm.list
import data.list.cycle
import group_theory.perm.cycle_type

/-!

# Properties of cyclic permutations constructed from lists/cycles

In the following, `{α : Type*} [fintype α] [decidable_eq α]`.

## Main definitions

* `cycle.form_perm`: the cyclic permutation created by looping over a `cycle α`
* `equiv.perm.to_list`: the list formed by iterating application of a permutation
* `equiv.perm.to_cycle`: the cycle formed by iterating application of a permutation
* `equiv.perm.iso_cycle`: the equivalence between cyclic permutations `f : perm α`
  and the terms of `cycle α` that correspond to them
* `equiv.perm.iso_cycle'`: the same equivalence as `equiv.perm.iso_cycle`
  but with evaluation via choosing over fintypes
* The notation `c[1, 2, 3]` to emulate notation of cyclic permutations `(1 2 3)`
* A `has_repr` instance for any `perm α`, by representing the `finset` of
  `cycle α` that correspond to the cycle factors.

## Main results

* `list.is_cycle_form_perm`: a nontrivial list without duplicates, when interpreted as
  a permutation, is cyclic
* `equiv.perm.is_cycle.exists_unique_cycle`: there is only one nontrivial `cycle α`
  corresponding to each cyclic `f : perm α`

## Implementation details

The forward direction of `equiv.perm.iso_cycle'` uses `fintype.choose` of the uniqueness
result, relying on the `fintype` instance of a `cycle.nodup` subtype.
It is unclear if this works faster than the `equiv.perm.to_cycle`, which relies
on recursion over `finset.univ`.
Running `#eval` on even a simple noncyclic permutation `c[(1 : fin 7), 2, 3] * c[0, 5]`
to show it takes a long time. TODO: is this because computing the cycle factors is slow?

-/

open equiv equiv.perm list

namespace list

variables {α : Type*} [decidable_eq α] {l l' : list α}

lemma form_perm_disjoint_iff (hl : nodup l) (hl' : nodup l')
  (hn : 2 ≤ l.length) (hn' : 2 ≤ l'.length) :
  perm.disjoint (form_perm l) (form_perm l') ↔ l.disjoint l' :=
begin
  rw [disjoint_iff_eq_or_eq, list.disjoint],
  split,
  { rintro h x hx hx',
    specialize h x,
    rw [form_perm_apply_mem_eq_self_iff _ hl _ hx,
        form_perm_apply_mem_eq_self_iff _ hl' _ hx'] at h,
    rcases h with hl | hl'; linarith },
  { intros h x,
    by_cases hx : x ∈ l; by_cases hx' : x ∈ l',
    { exact (h hx hx').elim },
    all_goals { have := form_perm_eq_self_of_not_mem _ _ ‹_›, tauto } }
end

lemma is_cycle_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  is_cycle (form_perm l) :=
begin
  cases l with x l,
  { norm_num at hn },
  induction l with y l IH generalizing x,
  { norm_num at hn },
  { use x,
    split,
    { rwa form_perm_apply_mem_ne_self_iff _ hl _ (mem_cons_self _ _) },
    { intros w hw,
      have : w ∈ (x :: y :: l) := mem_of_form_perm_ne_self _ _ hw,
      obtain ⟨k, hk, rfl⟩ := nth_le_of_mem this,
      use k,
      simp only [gpow_coe_nat, form_perm_pow_apply_head _ _ hl k, nat.mod_eq_of_lt hk] } }
end

lemma pairwise_same_cycle_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  pairwise (l.form_perm.same_cycle) l :=
pairwise.imp_mem.mpr (pairwise_of_forall (λ x y hx hy, (is_cycle_form_perm hl hn).same_cycle
  ((form_perm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
  ((form_perm_apply_mem_ne_self_iff _ hl _ hy).mpr hn)))

lemma cycle_of_form_perm (hl : nodup l) (hn : 2 ≤ l.length) (x) :
  cycle_of l.attach.form_perm x = l.attach.form_perm :=
have hn : 2 ≤ l.attach.length := by rwa ← length_attach at hn,
have hl : l.attach.nodup := by rwa ← nodup_attach at hl,
(is_cycle_form_perm hl hn).cycle_of_eq
  ((form_perm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)

lemma cycle_type_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  cycle_type l.attach.form_perm = {l.length} :=
begin
  rw ←length_attach at hn,
  rw ←nodup_attach at hl,
  rw cycle_type_eq [l.attach.form_perm],
  { simp only [map, function.comp_app],
    rw [support_form_perm_of_nodup _ hl, card_to_finset, erase_dup_eq_self.mpr hl],
    { simpa },
    { intros x h,
      simpa [h, nat.succ_le_succ_iff] using hn } },
  { simp },
  { simpa using is_cycle_form_perm hl hn },
  { simp }
end

lemma form_perm_apply_mem_eq_next (hl : nodup l) (x : α) (hx : x ∈ l) :
  form_perm l x = next l x hx :=
begin
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
  rw [next_nth_le _ hl, form_perm_apply_nth_le _ hl]
end

end list

namespace cycle

variables {α : Type*} [decidable_eq α] (s s' : cycle α)

/--
A cycle `s : cycle α` , given `nodup s` can be interpreted as a `equiv.perm α`
where each element in the list is permuted to the next one, defined as `form_perm`.
-/
def form_perm : Π (s : cycle α) (h : nodup s), equiv.perm α :=
λ s, quot.hrec_on s (λ l h, form_perm l)
  (λ l₁ l₂ (h : l₁ ~r l₂),
    begin
      ext,
      { exact h.nodup_iff },
      { intros h₁ h₂ _,
        exact heq_of_eq (form_perm_eq_of_is_rotated h₁ h) }
    end)

@[simp] lemma form_perm_coe (l : list α) (hl : l.nodup) :
  form_perm (l : cycle α) hl = l.form_perm := rfl

lemma form_perm_subsingleton (s : cycle α) (h : subsingleton s) :
  form_perm s h.nodup = 1 :=
begin
  induction s using quot.induction_on,
  simp only [form_perm_coe, mk_eq_coe],
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h,
  cases s with hd tl,
  { simp },
  { simp only [length_eq_zero, add_le_iff_nonpos_left, list.length, nonpos_iff_eq_zero] at h,
    simp [h] }
end

lemma is_cycle_form_perm (s : cycle α) (h : nodup s) (hn : nontrivial s) :
  is_cycle (form_perm s h) :=
begin
  induction s using quot.induction_on,
  exact list.is_cycle_form_perm h (length_nontrivial hn)
end

lemma support_form_perm [fintype α] (s : cycle α) (h : nodup s) (hn : nontrivial s) :
  support (form_perm s h) = s.to_finset :=
begin
  induction s using quot.induction_on,
  refine support_form_perm_of_nodup s h _,
  rintro _ rfl,
  simpa [nat.succ_le_succ_iff] using length_nontrivial hn
end

lemma form_perm_eq_self_of_not_mem (s : cycle α) (h : nodup s) (x : α) (hx : x ∉ s) :
  form_perm s h x = x :=
begin
  induction s using quot.induction_on,
  simpa using list.form_perm_eq_self_of_not_mem _ _ hx
end

lemma form_perm_apply_mem_eq_next (s : cycle α) (h : nodup s) (x : α) (hx : x ∈ s) :
  form_perm s h x = next s h x hx :=
begin
  induction s using quot.induction_on,
  simpa using list.form_perm_apply_mem_eq_next h _ _
end

lemma form_perm_reverse (s : cycle α) (h : nodup s) :
  form_perm s.reverse (nodup_reverse_iff.mpr h) = (form_perm s h)⁻¹ :=
begin
  induction s using quot.induction_on,
  simpa using form_perm_reverse _ h
end

lemma form_perm_eq_form_perm_iff {α : Type*} [decidable_eq α]
  {s s' : cycle α} {hs : s.nodup} {hs' : s'.nodup} :
  s.form_perm hs = s'.form_perm hs' ↔ s = s' ∨ s.subsingleton ∧ s'.subsingleton :=
begin
  rw [cycle.length_subsingleton_iff, cycle.length_subsingleton_iff],
  revert s s',
  intros s s',
  apply quotient.induction_on₂' s s',
  intros l l',
  simpa using form_perm_eq_form_perm_iff
end

end cycle
variables {α : Type*}

namespace equiv.perm

variables [fintype α] [decidable_eq α] (p : equiv.perm α) (x : α)

/--
`equiv.perm.to_list (f : perm α) (x : α)` generates the list `[x, f x, f (f x), ...]`
until looping. That means when `f x = x`, `to_list f x = []`.
-/
def to_list : list α :=
(list.range (cycle_of p x).support.card).map (λ k, (p ^ k) x)

@[simp] lemma to_list_one : to_list (1 : perm α) x = [] :=
by simp [to_list, cycle_of_one]

@[simp] lemma to_list_eq_nil_iff {p : perm α} {x} : to_list p x = [] ↔ x ∉ p.support :=
by simp [to_list]

@[simp] lemma length_to_list : length (to_list p x) = (cycle_of p x).support.card :=
by simp [to_list]

lemma to_list_ne_singleton (y : α) : to_list p x ≠ [y] :=
begin
  intro H,
  simpa [card_support_ne_one] using congr_arg length H
end

lemma two_le_length_to_list_iff_mem_support {p : perm α} {x : α} :
  2 ≤ length (to_list p x) ↔ x ∈ p.support :=
by simp

lemma length_to_list_pos_of_mem_support (h : x ∈ p.support) : 0 < length (to_list p x) :=
zero_lt_two.trans_le (two_le_length_to_list_iff_mem_support.mpr h)

lemma nth_le_to_list (n : ℕ) (hn : n < length (to_list p x)) :
  nth_le (to_list p x) n hn = (p ^ n) x :=
by simp [to_list]

lemma to_list_nth_le_zero (h : x ∈ p.support) :
  (to_list p x).nth_le 0 (length_to_list_pos_of_mem_support _ _ h) = x :=
by simp [to_list]

variables {p} {x}

lemma mem_to_list_iff {y : α} :
  y ∈ to_list p x ↔ same_cycle p x y ∧ x ∈ p.support :=
begin
  simp only [to_list, mem_range, mem_map],
  split,
  { rintro ⟨n, hx, rfl⟩,
    refine ⟨⟨n, rfl⟩, _⟩,
    contrapose! hx,
    rw ←support_cycle_of_eq_nil_iff at hx,
    simp [hx] },
  { rintro ⟨h, hx⟩,
    simpa using same_cycle.nat_of_mem_support _ h hx }
end

lemma nodup_to_list (p : perm α) (x : α) :
  nodup (to_list p x) :=
begin
  by_cases hx : p x = x,
  { rw [←not_mem_support, ←to_list_eq_nil_iff] at hx,
    simp [hx] },
  have hc : is_cycle (cycle_of p x) := is_cycle_cycle_of p hx,
  rw nodup_iff_nth_le_inj,
  rintros n m hn hm,
  rw [length_to_list, ←order_of_is_cycle hc] at hm hn,
  rw [←cycle_of_apply_self, ←ne.def, ←mem_support] at hx,
  rw [nth_le_to_list, nth_le_to_list,
      ←cycle_of_pow_apply_self p x n, ←cycle_of_pow_apply_self p x m],
  cases n; cases m,
  { simp },
  { rw [←hc.mem_support_pos_pow_iff_of_lt_order_of m.zero_lt_succ hm,
        mem_support, cycle_of_pow_apply_self] at hx,
    simp [hx.symm] },
  { rw [←hc.mem_support_pos_pow_iff_of_lt_order_of n.zero_lt_succ hn,
        mem_support, cycle_of_pow_apply_self] at hx,
    simp [hx] },
  intro h,
  have hn' : ¬ order_of (p.cycle_of x) ∣ n.succ := nat.not_dvd_of_pos_of_lt n.zero_lt_succ hn,
  have hm' : ¬ order_of (p.cycle_of x) ∣ m.succ := nat.not_dvd_of_pos_of_lt m.zero_lt_succ hm,
  rw ←hc.support_pow_eq_iff at hn' hm',
  rw [←nat.mod_eq_of_lt hn, ←nat.mod_eq_of_lt hm, ←pow_inj_mod],
  refine support_congr _ _,
  { rw [hm', hn'],
    exact finset.subset.refl _ },
  { rw hm',
    intros y hy,
    obtain ⟨k, rfl⟩ := hc.exists_pow_eq (mem_support.mp hx) (mem_support.mp hy),
    rw [←mul_apply, (commute.pow_pow_self _ _ _).eq, mul_apply, h, ←mul_apply, ←mul_apply,
        (commute.pow_pow_self _ _ _).eq] }
end

lemma next_to_list_eq_apply (p : perm α) (x y : α) (hy : y ∈ to_list p x) :
  next (to_list p x) y hy = p y :=
begin
  rw mem_to_list_iff at hy,
  obtain ⟨k, hk, hk'⟩ := hy.left.nat_of_mem_support _ hy.right,
  rw ←nth_le_to_list p x k (by simpa using hk) at hk',
  simp_rw ←hk',
  rw [next_nth_le _ (nodup_to_list _ _), nth_le_to_list, nth_le_to_list, ←mul_apply, ←pow_succ,
      length_to_list, pow_apply_eq_pow_mod_order_of_cycle_of_apply p (k + 1), order_of_is_cycle],
  exact is_cycle_cycle_of _ (mem_support.mp hy.right)
end

lemma to_list_pow_apply_eq_rotate (p : perm α) (x : α) (k : ℕ) :
  p.to_list ((p ^ k) x) = (p.to_list x).rotate k :=
begin
  apply ext_le,
  { simp },
  { intros n hn hn',
    rw [nth_le_to_list, nth_le_rotate, nth_le_to_list, length_to_list,
        pow_mod_card_support_cycle_of_self_apply, pow_add, mul_apply] }
end

lemma same_cycle.to_list_is_rotated {f : perm α} {x y : α} (h : same_cycle f x y) :
  to_list f x ~r to_list f y :=
begin
  by_cases hx : x ∈ f.support,
  { obtain ⟨_ | k, hk, hy⟩ := h.nat_of_mem_support _ hx,
    { simp only [coe_one, id.def, pow_zero] at hy,
      simp [hy] },
    use k.succ,
    rw [←to_list_pow_apply_eq_rotate, hy] },
  { rw [to_list_eq_nil_iff.mpr hx, is_rotated_nil_iff', eq_comm, to_list_eq_nil_iff],
    rwa ←h.mem_support_iff }
end

lemma pow_apply_mem_to_list_iff_mem_support {n : ℕ} :
  (p ^ n) x ∈ p.to_list x ↔ x ∈ p.support :=
begin
  rw [mem_to_list_iff, and_iff_right_iff_imp],
  refine λ _, same_cycle.symm _,
  rw same_cycle_pow_left_iff
end

lemma to_list_form_perm_nil (x : α) :
  to_list (form_perm ([] : list α)) x = [] :=
by simp

lemma to_list_form_perm_singleton (x y : α) :
  to_list (form_perm [x]) y = [] :=
by simp

lemma to_list_form_perm_nontrivial (l : list α) (hl : 2 ≤ l.length) (hn : nodup l) :
  to_list (form_perm l) (l.nth_le 0 (zero_lt_two.trans_le hl)) = l :=
begin
  have hc : l.form_perm.is_cycle := list.is_cycle_form_perm hn hl,
  have hs : l.form_perm.support = l.to_finset,
  { refine support_form_perm_of_nodup _ hn _,
    rintro _ rfl,
    simpa [nat.succ_le_succ_iff] using hl },
  rw [to_list, hc.cycle_of_eq (mem_support.mp _), hs, card_to_finset, erase_dup_eq_self.mpr hn],
  { refine list.ext_le (by simp) (λ k hk hk', _),
    simp [form_perm_pow_apply_nth_le _ hn, nat.mod_eq_of_lt hk'] },
  { simpa [hs] using nth_le_mem _ _ _ }
end

lemma to_list_form_perm_is_rotated_self (l : list α) (hl : 2 ≤ l.length) (hn : nodup l)
  (x : α) (hx : x ∈ l):
  to_list (form_perm l) x ~r l :=
begin
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
  have hr : l ~r l.rotate k := ⟨k, rfl⟩,
  rw form_perm_eq_of_is_rotated hn hr,
  rw ←nth_le_rotate' l k k,
  simp only [nat.mod_eq_of_lt hk, tsub_add_cancel_of_le hk.le, nat.mod_self],
  rw [to_list_form_perm_nontrivial],
  { simp },
  { simpa using hl },
  { simpa using hn }
end

lemma form_perm_to_list (f : perm α) (x : α) :
  form_perm (to_list f x) = f.cycle_of x :=
begin
  by_cases hx : f x = x,
  { rw [(cycle_of_eq_one_iff f).mpr hx, to_list_eq_nil_iff.mpr (not_mem_support.mpr hx),
        form_perm_nil] },
  ext y,
  by_cases hy : same_cycle f x y,
  { obtain ⟨k, hk, rfl⟩ := hy.nat_of_mem_support _ (mem_support.mpr hx),
    rw [cycle_of_apply_apply_pow_self, list.form_perm_apply_mem_eq_next (nodup_to_list f x),
        next_to_list_eq_apply, pow_succ, mul_apply],
    rw mem_to_list_iff,
    exact ⟨⟨k, rfl⟩, mem_support.mpr hx⟩ },
  { rw [cycle_of_apply_of_not_same_cycle hy, form_perm_apply_of_not_mem],
    simp [mem_to_list_iff, hy] }
end

lemma is_cycle.exists_unique_cycle {f : perm α} (hf : is_cycle f) :
  ∃! (s : cycle α), ∃ (h : s.nodup), s.form_perm h = f :=
begin
  obtain ⟨x, hx, hy⟩ := id hf,
  refine ⟨f.to_list x, ⟨nodup_to_list f x, _⟩, _⟩,
  { simp [form_perm_to_list, hf.cycle_of_eq hx] },
  { rintro ⟨l⟩ ⟨hn, rfl⟩,
    simp only [cycle.mk_eq_coe, cycle.coe_eq_coe, subtype.coe_mk, cycle.form_perm_coe],
    refine (to_list_form_perm_is_rotated_self _ _ hn _ _).symm,
    { contrapose! hx,
      suffices : form_perm l = 1,
      { simp [this] },
      rw form_perm_eq_one_iff _ hn,
      exact nat.le_of_lt_succ hx },
    { rw ←mem_to_finset,
      refine support_form_perm_le l _,
      simpa using hx } }
end

lemma is_cycle.exists_unique_cycle_subtype {f : perm α} (hf : is_cycle f) :
  ∃! (s : {s : cycle α // s.nodup}), (s : cycle α).form_perm s.prop = f :=
begin
  obtain ⟨s, ⟨hs, rfl⟩, hs'⟩ := hf.exists_unique_cycle,
  refine ⟨⟨s, hs⟩, rfl, _⟩,
  rintro ⟨t, ht⟩ ht',
  simpa using hs' _ ⟨ht, ht'⟩
end

lemma is_cycle.exists_unique_cycle_nontrivial_subtype {f : perm α} (hf : is_cycle f) :
  ∃! (s : {s : cycle α // s.nodup ∧ s.nontrivial}), (s : cycle α).form_perm s.prop.left = f :=
begin
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.exists_unique_cycle_subtype,
  refine ⟨⟨s, hn, _⟩, _, _⟩,
  { rw hn.nontrivial_iff,
    subst f,
    intro H,
    refine hf.ne_one _,
    simpa using cycle.form_perm_subsingleton _ H },
  { simpa using hs },
  { rintro ⟨t, ht, ht'⟩ ht'',
    simpa using hs' ⟨t, ht⟩ ht'' }
end

/--
Given a cyclic `f : perm α`, generate the `cycle α` in the order
of application of `f`. Implemented by finding an element `x : α`
in the support of `f` in `finset.univ`, and iterating on using
`equiv.perm.to_list f x`.
-/
def to_cycle (f : perm α) (hf : is_cycle f) : cycle α :=
multiset.rec_on (finset.univ : finset α).val
  (quot.mk _ [])
  (λ x s l, if f x = x then l else to_list f x)
  (by { intros x y m s,
    refine heq_of_eq _,
    split_ifs with hx hy hy; try { refl },
    { have hc : same_cycle f x y := is_cycle.same_cycle hf hx hy,
      exact quotient.sound' hc.to_list_is_rotated }})

lemma to_cycle_eq_to_list (f : perm α) (hf : is_cycle f) (x : α) (hx : f x ≠ x) :
  to_cycle f hf = to_list f x :=
begin
  have key : (finset.univ : finset α).val = x ::ₘ finset.univ.val.erase x,
  { simp },
  rw [to_cycle, key],
  simp [hx]
end

lemma nodup_to_cycle (f : perm α) (hf : is_cycle f) : (to_cycle f hf).nodup :=
begin
  obtain ⟨x, hx, -⟩ := id hf,
  simpa [to_cycle_eq_to_list f hf x hx] using nodup_to_list _ _
end

lemma nontrivial_to_cycle (f : perm α) (hf : is_cycle f) : (to_cycle f hf).nontrivial :=
begin
  obtain ⟨x, hx, -⟩ := id hf,
  simp [to_cycle_eq_to_list f hf x hx, hx, cycle.nontrivial_coe_nodup_iff (nodup_to_list _ _)]
end

/--
Any cyclic `f : perm α` is isomorphic to the nontrivial `cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by `equiv.perm.to_cycle`.
-/
def iso_cycle : {f : perm α // is_cycle f} ≃ {s : cycle α // s.nodup ∧ s.nontrivial} :=
{ to_fun := λ f, ⟨to_cycle (f : perm α) f.prop, nodup_to_cycle f f.prop,
    nontrivial_to_cycle _ f.prop⟩,
  inv_fun := λ s, ⟨(s : cycle α).form_perm s.prop.left,
    (s : cycle α).is_cycle_form_perm _ s.prop.right⟩,
  left_inv := λ f, by {
    obtain ⟨x, hx, -⟩ := id f.prop,
    simpa [to_cycle_eq_to_list (f : perm α) f.prop x hx, form_perm_to_list, subtype.ext_iff]
      using f.prop.cycle_of_eq hx },
  right_inv := λ s, by {
    rcases s with ⟨⟨s⟩, hn, ht⟩,
    obtain ⟨x, -, -, hx, -⟩ := id ht,
    have hl : 2 ≤ s.length := by simpa using cycle.length_nontrivial ht,
    simp only [cycle.mk_eq_coe, cycle.nodup_coe_iff, cycle.mem_coe_iff, subtype.coe_mk,
               cycle.form_perm_coe] at hn hx ⊢,
    rw to_cycle_eq_to_list _ _ x,
    { refine quotient.sound' _,
      exact to_list_form_perm_is_rotated_self _ hl hn _ hx },
    { rw [←mem_support, support_form_perm_of_nodup _ hn],
      { simpa using hx },
      { rintro _ rfl,
        simpa [nat.succ_le_succ_iff] using hl } } } }

/--
Any cyclic `f : perm α` is isomorphic to the nontrivial `cycle α`
that corresponds to repeated application of `f`.
The forward direction is implemented by finding this `cycle α` using `fintype.choose`.
-/
def iso_cycle' : {f : perm α // is_cycle f} ≃ {s : cycle α // s.nodup ∧ s.nontrivial} :=
{ to_fun := λ f, fintype.choose _ f.prop.exists_unique_cycle_nontrivial_subtype,
  inv_fun := λ s, ⟨(s : cycle α).form_perm s.prop.left,
    (s : cycle α).is_cycle_form_perm _ s.prop.right⟩,
  left_inv := λ f, by simpa [subtype.ext_iff]
    using fintype.choose_spec _ f.prop.exists_unique_cycle_nontrivial_subtype,
  right_inv := λ ⟨s, hs, ht⟩, by {
    simp [subtype.coe_mk],
    convert fintype.choose_subtype_eq (λ (s' : cycle α), s'.nodup ∧ s'.nontrivial) _,
    ext ⟨s', hs', ht'⟩,
    simp [cycle.form_perm_eq_form_perm_iff, (iff_not_comm.mp hs.nontrivial_iff),
          (iff_not_comm.mp hs'.nontrivial_iff), ht] } }

notation `c[` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) :=
  cycle.form_perm ↑l (cycle.nodup_coe_iff.mpr dec_trivial)

instance repr_perm [has_repr α] : has_repr (perm α) :=
⟨λ f, repr (multiset.pmap (λ (g : perm α) (hg : g.is_cycle),
  iso_cycle ⟨g, hg⟩) -- to_cycle is faster?
  (perm.cycle_factors_finset f).val
  (λ g hg, (mem_cycle_factors_finset_iff.mp (finset.mem_def.mpr hg)).left))⟩

end equiv.perm
