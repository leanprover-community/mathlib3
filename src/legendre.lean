import data.nat.prime
import number_theory.prime_counting
import liouville_data_fake
import tactic.slim_check

namespace nat

/-- The naturals `n` with `1 ≤ n ≤ x` which aren't divisible by anything from `ps`. -/
def phi_list (x : ℕ) (ps : list ℕ) : list ℕ :=
(list.range (x + 1)).filter (λ n, n ≠ 0 ∧ ∀ i ∈ ps, ¬ i ∣ n)

lemma zero_mem_phi_list {x ps} : 0 ∉ phi_list x ps :=
by simp [phi_list, list.all₂_iff_forall]

lemma list.range_one : list.range 1 = [0] := rfl

lemma phi_list_zero {ps : list ℕ} : phi_list 0 ps = [] := by { rw [phi_list, list.range_one], simp }
lemma phi_list_nil {x : ℕ} : phi_list x [] = (list.range (x + 1)).filter (λ n, n ≠ 0) :=
by { rw [phi_list], simp only [list.not_mem_nil, is_empty.forall_iff, forall_const, and_true] }

def phi (x : ℕ) (ps : list ℕ) : ℕ := (phi_list x ps).length

lemma phi_eq {x : ℕ} {ps : list ℕ} :
  phi x ps = ((finset.range (x + 1)).filter (λ n, n ≠ 0 ∧ ∀ i ∈ ps, ¬ i ∣ n)).card :=
rfl

lemma phi_eq' {x : ℕ} {ps : list ℕ} :
  phi x ps = ((finset.range x).filter (λ n, ∀ i ∈ ps, ¬ i ∣ (n + 1))).card :=
begin
  have : ((finset.range x).filter (λ n, ∀ i ∈ ps, ¬ i ∣ (n + 1))).card =
    (((finset.range x).map (add_right_embedding 1)).filter (λ n, ∀ i ∈ ps, ¬ i ∣ n)).card,
  { rw [finset.map_filter, finset.card_map],
    refl },
  rw [this, phi_eq],
  congr' 1,
  ext n,
  simp only [finset.mem_filter, finset.mem_map, ne.def, finset.mem_range, add_right_embedding_apply,
    exists_prop, ←and_assoc],
  apply and_congr_left',
  split,
  { rintro ⟨hn₁, hn₂⟩,
    have : 1 ≤ n,
    { rw [←ne.def, ←pos_iff_ne_zero] at hn₂,
      exact hn₂ },
    refine ⟨n - 1, _, _⟩,
    { rwa tsub_lt_iff_right this },
    rw [tsub_add_cancel_of_le this] },
  rintro ⟨n, hn, rfl⟩,
  simp [hn],
end

lemma phi_perm {x : ℕ} {ps qs : list ℕ} (h : ps ~ qs) :
  phi x ps = phi x qs :=
by { rw [phi_eq, phi_eq], simp only [h.mem_iff] }

lemma phi_reverse {x : ℕ} {ps : list ℕ} : phi x ps.reverse = phi x ps :=
phi_perm (list.reverse_perm _)

lemma finset.filter_sdiff {α : Type*} {s : finset α} (p q : α → Prop)
  [decidable_eq α] [decidable_pred p] [decidable_pred q] [decidable_pred (λ x, p x ∧ ¬ q x)]:
  s.filter p \ s.filter q = s.filter (λ x, p x ∧ ¬ q x) :=
begin
  ext x,
  simp only [finset.mem_sdiff, finset.mem_filter, not_and],
  tauto
end

lemma prime_iff_no_prime_dvd {p : ℕ} :
  prime p ↔ 2 ≤ p ∧ ∀ q, q ≤ sqrt p → prime q → ¬ q ∣ p :=
begin
  split,
  { intro hp,
    refine ⟨hp.two_le, λ q hq hq', _⟩,
    rw prime_dvd_prime_iff_eq hq' hp,
    rintro rfl,
    exact (nat.sqrt_lt_self hq'.one_lt).not_le hq },
  rintro ⟨hp, hq⟩,
  by_contra,
  have := nat.le_sqrt'.2 (min_fac_sq_le_self (by linarith) h),
  refine hq _ this (min_fac_prime _) (min_fac_dvd _),
  linarith,
end

lemma prime_counting_eq {x : ℕ} (hx : x ≠ 0) :
  prime_counting x + 1 = prime_counting (sqrt x) + phi x (nat.primes_le (sqrt x)) :=
begin
  have h₁ : finset.card (finset.filter (λ i, i = 1) (finset.range (x + 1))) = 1,
  { rw [finset.filter_eq', if_pos, finset.card_singleton],
    rw finset.mem_range_succ_iff,
    linarith [hx.bot_lt] },
  have h₂ : (finset.filter prime (finset.range (sqrt x + 1))) =
    finset.filter (λ p, prime p ∧ p ≤ sqrt x) (finset.range (x + 1)),
  { ext p,
    simp only [finset.mem_filter, finset.mem_range_succ_iff],
    have : p ≤ sqrt x → p ≤ x := le_trans' (nat.sqrt_le_self x),
    tauto },
  rw [←h₁, prime_counting, prime_counting, prime_counting', count_eq_card_filter_range,
    count_eq_card_filter_range, h₂, phi_eq, ←finset.card_disjoint_union,
    ←finset.card_disjoint_union, finset.filter_union_right, finset.filter_union_right],
  { congr' 1,
    ext n,
    simp only [finset.mem_filter, finset.mem_range_succ_iff, ne.def, and.congr_right_iff,
      mem_primes_le, and_imp],
    intro hn,
    split,
    { rintro (hp | rfl),
      { cases le_or_lt n (sqrt x),
        { exact or.inl ⟨hp, h⟩ },
        right,
        refine ⟨hp.ne_zero, λ i hi hi' hi'', _⟩,
        rcases hp.eq_one_or_self_of_dvd _ hi'' with rfl | rfl,
        { exact hi'.ne_one rfl },
        { exact hi.not_lt h } },
      right,
      refine ⟨by simp, _⟩,
      simp only [nat.dvd_one],
      rintro _ _ h rfl,
      exact h.ne_one rfl },
    rintro (⟨hn₁, hn₂⟩ | ⟨hn₁, hn₂⟩),
    { exact or.inl hn₁ },
    rw or_iff_not_imp_right,
    intro hn₃,
    rw prime_iff_no_prime_dvd,
    refine ⟨_, λ q hq hq', _⟩,
    { rcases n with (_ | _ | _),
      { cases hn₁ rfl },
      { cases hn₃ rfl },
      apply succ_le_succ,
      apply succ_le_succ,
      exact zero_le _ },
    exact hn₂ q (hq.trans (sqrt_le_sqrt hn)) hq' },
  { simp only [finset.disjoint_left, finset.mem_filter, true_and, finset.mem_range_succ_iff,
      mem_primes_le, and_imp, not_and, not_forall, not_not] {contextual := tt},
    intros p hp₁ hp₂ hp₃ hp₄,
    exact ⟨p, hp₃, hp₂, dvd_rfl⟩ },
  simp only [finset.disjoint_left, finset.mem_filter, finset.mem_range_succ_iff, true_and, and_imp,
    prime.ne_one, not_false_iff, implies_true_iff] {contextual := tt},
end

lemma phi_div_eq' (x p : ℕ) (hp : p ≠ 0) (ps : list ℕ) :
  phi (x / p) ps =
    (((finset.range ((x / p) + 1)).filter (λ n, n ≠ 0 ∧ ∀ i ∈ ps, ¬ i ∣ n)).image (*p)).card :=
begin
  rw [phi_eq, finset.card_image_of_injective],
  exact mul_left_injective₀ hp,
end

lemma phi_div_eq {x p : ℕ} {ps : list ℕ} (hp : p ≠ 0) (h : ∀ q ∈ ps, coprime p q) :
  phi (x / p) ps = ((finset.range (x + 1)).filter (λ n, n ≠ 0 ∧ p ∣ n ∧ ∀ i ∈ ps, ¬ i ∣ n)).card :=
begin
  rw phi_div_eq' _ _ hp,
  congr' 1,
  ext n,
  simp only [finset.mem_image, finset.mem_filter, finset.mem_range_succ_iff, exists_prop,
    and_assoc],
  split,
  { rintro ⟨k, hk, hk'', hk', rfl⟩,
    rw nat.le_div_iff_mul_le hp.bot_lt at hk,
    refine ⟨hk, mul_ne_zero hk'' hp, dvd_mul_left _ _, λ i hi hi', _⟩,
    exact hk' i hi (nat.coprime.dvd_of_dvd_mul_right (h _ hi).symm hi') },
  rintro ⟨hk, hk'', ⟨k, rfl⟩, hk'⟩,
  simp only [ne.def, nat.mul_eq_zero, not_or_distrib] at hk'',
  rw [mul_comm, ←nat.le_div_iff_mul_le hp.bot_lt] at hk,
  refine ⟨k, hk, hk''.2, λ i hi hi', _, mul_comm _ _⟩,
  exact hk' i hi (hi'.trans (dvd_mul_left _ _))
end

@[simp] lemma phi_nil {x : ℕ} : phi x [] = x :=
begin
  rw [phi_eq],
  simp only [list.not_mem_nil, is_empty.forall_iff, forall_const, and_true],
  rw [finset.filter_ne', finset.card_erase_of_mem, finset.card_range, nat.add_sub_cancel],
  simp
end

lemma phi_cons (x p : ℕ) (ps : list ℕ) (hp : p ≠ 0) (h : ∀ q ∈ ps, coprime p q) :
  phi x (p :: ps) + phi (x / p) ps = phi x ps :=
begin
  rw [phi_div_eq hp h, phi_eq, phi_eq],
  simp only [list.mem_cons_iff, forall_eq_or_imp],
  rw [←finset.card_disjoint_union, finset.filter_union_right],
  { congr' 2,
    ext n,
    tauto },
  rw finset.disjoint_left,
  simp only [finset.mem_filter],
  tauto
end.

lemma phi_add_mul_prod {x : ℕ} {ps : list ℕ} :
  phi (x + ps.prod) ps = phi x ps + phi ps.prod ps :=
begin
  rw [phi_eq', phi_eq', phi_eq', add_comm, finset.range_add, finset.filter_union,
    finset.card_disjoint_union, finset.map_filter, finset.card_map, add_comm],
  { congr' 3,
    ext n,
    simp only [function.comp_app, add_left_embedding_apply],
    refine forall₂_congr _,
    intros p hp,
    rw [not_iff_not, add_assoc],
    exact (nat.dvd_add_iff_right (list.dvd_prod hp)).symm },
  { apply finset.disjoint_filter_filter,
    apply finset.disjoint_range_add_left_embedding },
end

lemma phi_add_mul {x c : ℕ} (q : ℕ) {ps : list ℕ} (hc : c = list.prod ps) :
  phi (x + q * c) ps = phi x ps + q * phi c ps :=
begin
  subst c,
  induction q with q ih,
  { simp },
  rw [succ_mul, ←add_assoc, phi_add_mul_prod, ih, succ_mul, add_assoc],
end

lemma phi_mod {x c : ℕ} {ps : list ℕ} (hc : c = list.prod ps) :
  phi x ps = phi (x % c) ps + (x / c) * phi c ps :=
by rw [←phi_add_mul _ hc, mod_add_div']

def phi_helper (x l m) : Prop := (∃ n, l = (primes_le n).reverse) → phi x l = m

lemma primes_le_succ {p n : ℕ} {ps : list ℕ} :
  (p :: ps) = (primes_le n).reverse → ∃ m, ps = (primes_le m).reverse :=
begin
  intro h,
  refine ⟨p - 1, _⟩,
  have h₁ : list.sorted (>) (p - 1).primes_le.reverse := primes_le_reverse_sorted,
  have h₂ : list.sorted (>) n.primes_le.reverse := primes_le_reverse_sorted,
  have : ∀ i ∈ p :: ps, prime i,
  { simp only [h, list.mem_reverse],
    intros i,
    exact list.of_mem_filter },
  rw [←h, list.sorted_cons] at h₂,
  simp only [list.mem_cons_iff, forall_eq_or_imp] at this,
  apply list.eq_of_perm_of_sorted _ h₂.2 h₁,
  rw list.perm_ext h₂.2.nodup h₁.nodup,
  intro q,
  simp only [list.mem_reverse, mem_primes_le],
  split,
  { intro hq,
    rw [le_tsub_iff_right, add_one_le_iff],
    { exact ⟨h₂.1 _ hq, this.2 _ hq⟩ },
    exact this.1.pos },
  rintro ⟨hq, hq'⟩,
  have h₃ : p ≤ n ∧ prime p,
  { rw [←mem_primes_le, ←list.mem_reverse, ←h],
    simp },
  have : q ∈ p :: ps,
  { rw [h, list.mem_reverse, mem_primes_le],
    refine ⟨_, hq'⟩,
    apply hq.trans _,
    apply h₃.1.trans' _,
    simp },
  simp only [list.mem_cons_iff] at this,
  apply this.resolve_left,
  rintro rfl,
  exact hq.not_lt (nat.sub_lt (h₃.2.pos) zero_lt_one),
end

lemma coprime_of_prime_nodup {p : ℕ} {ps : list ℕ}
  (h₁ : ∀ i ∈ p :: ps, prime i) (h₂ : list.nodup (p :: ps)) :
  ∀ q ∈ ps, coprime p q :=
begin
  intros q hq,
  simp only [list.mem_cons_iff, forall_eq_or_imp] at h₁,
  rw nat.coprime_primes h₁.1 (h₁.2 _ hq),
  simp only [list.nodup_cons] at h₂,
  exact (ne_of_mem_of_not_mem hq h₂.1).symm,
end

lemma count_primes {x sx ll t llt m : ℕ} (l l' : list ℕ) (hsx : sqrt x = sx)
  (hl : primes_le sx = l) (hl' : l.reverse = l') (hll : l'.length = ll) (hphi : phi_helper x l' t)
  (hllt : ll + t = llt) (hm : llt - 1 = m) (hx : 0 < x) :
  prime_counting x = m :=
begin
  substs l l',
  specialize hphi ⟨sx, rfl⟩,
  substs sx ll t llt m,
  rw [list.length_reverse, primes_le_card, phi_reverse, ←prime_counting_eq hx.ne',
    nat.add_sub_cancel]
end

lemma phi_helper_cons (x p ps) (xp m₁ m₂ : ℕ) (m : ℕ)
  (hxp : x / p = xp) (hm₁ : phi_helper x ps m₁) (hm₂ : phi_helper xp ps m₂) (hm : m₁ - m₂ = m) :
  phi_helper x (p :: ps) m :=
begin
  subst xp,
  intros hl₁,
  obtain ⟨n, hl₁⟩ := hl₁,
  have hl₂ : ∀ q ∈ p :: ps, prime q,
  { simp only [hl₁, list.mem_reverse, mem_primes_le],
    simp },
  have hl₃ : (p :: ps).nodup,
  { rw [hl₁, list.nodup_reverse],
    exact primes_le_nodup },
  simp only [list.nodup_cons, list.mem_cons_iff, forall_eq_or_imp] at hl₂ hl₃,
  have : phi x ps - phi (x / p) ps = phi x (p :: ps),
  { rw [←phi_cons _ p _ hl₂.1.ne_zero, nat.add_sub_cancel],
    intros q hq,
    rw nat.coprime_primes hl₂.1 (hl₂.2 _ hq),
    exact (ne_of_mem_of_not_mem hq hl₃.1).symm },
  rwa [←this, hm₁ (primes_le_succ hl₁), hm₂ (primes_le_succ hl₁)],
end

lemma phi_helper_nil (x : ℕ) : phi_helper x [] x := λ _, phi_nil

lemma phi_helper_zero (ps : list ℕ) : phi_helper 0 ps 0 :=
by { intros h₁, rw [phi, phi_list_zero], refl }

lemma phi_helper_lt (x p : ℕ) (ps : list ℕ) (hx : 0 < x) (h : x ≤ p) : phi_helper x (p :: ps) 1 :=
begin
  rintro ⟨l, hl⟩,
  rw [phi_eq],
  have : ((finset.range (x + 1)).filter (λ n, n ≠ 0 ∧ ∀ (i : ℕ), i ∈ p :: ps → ¬i ∣ n)) = {1},
  { rw finset.eq_singleton_iff_unique_mem,
    simp only [finset.mem_filter, finset.mem_range, not_false_iff, and_assoc,
      true_and, nat.dvd_one, lt_add_iff_pos_left, hx, and_imp, hl, list.mem_reverse, mem_primes_le],
    refine ⟨one_ne_zero, λ q _ hq, hq.ne_one, _⟩,
    intros y hy hy' hy'',
    rw nat.lt_add_one_iff at hy,
    by_contra hy''',
    refine hy'' (nat.min_fac y) _ (nat.min_fac_prime hy''') (nat.min_fac_dvd _),
    refine ((nat.min_fac_le hy'.bot_lt).trans (hy.trans h)).trans _,
    have : p ≤ l ∧ p.prime,
    { rw [←mem_primes_le, ←list.mem_reverse, ←hl],
      simp },
    exact this.1 },
  rw [this],
  simp,
end

section data

lemma phi_helper_thirty_0 :  phi_helper 0  [5, 3, 2] 0 := λ _, rfl
lemma phi_helper_thirty_1 :  phi_helper 1  [5, 3, 2] 1 := λ _, rfl
lemma phi_helper_thirty_2 :  phi_helper 2  [5, 3, 2] 1 := λ _, rfl
lemma phi_helper_thirty_3 :  phi_helper 3  [5, 3, 2] 1 := λ _, rfl
lemma phi_helper_thirty_4 :  phi_helper 4  [5, 3, 2] 1 := λ _, rfl
lemma phi_helper_thirty_5 :  phi_helper 5  [5, 3, 2] 1 := λ _, rfl
lemma phi_helper_thirty_6 :  phi_helper 6  [5, 3, 2] 1 := λ _, rfl
lemma phi_helper_thirty_7 :  phi_helper 7  [5, 3, 2] 2 := λ _, rfl
lemma phi_helper_thirty_8 :  phi_helper 8  [5, 3, 2] 2 := λ _, rfl
lemma phi_helper_thirty_9 :  phi_helper 9  [5, 3, 2] 2 := λ _, rfl
lemma phi_helper_thirty_10 : phi_helper 10 [5, 3, 2] 2 := λ _, rfl
lemma phi_helper_thirty_11 : phi_helper 11 [5, 3, 2] 3 := λ _, rfl
lemma phi_helper_thirty_12 : phi_helper 12 [5, 3, 2] 3 := λ _, rfl
lemma phi_helper_thirty_13 : phi_helper 13 [5, 3, 2] 4 := λ _, rfl
lemma phi_helper_thirty_14 : phi_helper 14 [5, 3, 2] 4 := λ _, rfl
lemma phi_helper_thirty_15 : phi_helper 15 [5, 3, 2] 4 := λ _, rfl
lemma phi_helper_thirty_16 : phi_helper 16 [5, 3, 2] 4 := λ _, rfl
lemma phi_helper_thirty_17 : phi_helper 17 [5, 3, 2] 5 := λ _, rfl
lemma phi_helper_thirty_18 : phi_helper 18 [5, 3, 2] 5 := λ _, rfl
lemma phi_helper_thirty_19 : phi_helper 19 [5, 3, 2] 6 := λ _, rfl
lemma phi_helper_thirty_20 : phi_helper 20 [5, 3, 2] 6 := λ _, rfl
lemma phi_helper_thirty_21 : phi_helper 21 [5, 3, 2] 6 := λ _, rfl
lemma phi_helper_thirty_22 : phi_helper 22 [5, 3, 2] 6 := λ _, rfl
lemma phi_helper_thirty_23 : phi_helper 23 [5, 3, 2] 7 := λ _, rfl
lemma phi_helper_thirty_24 : phi_helper 24 [5, 3, 2] 7 := λ _, rfl
lemma phi_helper_thirty_25 : phi_helper 25 [5, 3, 2] 7 := λ _, rfl
lemma phi_helper_thirty_26 : phi_helper 26 [5, 3, 2] 7 := λ _, rfl
lemma phi_helper_thirty_27 : phi_helper 27 [5, 3, 2] 7 := λ _, rfl
lemma phi_helper_thirty_28 : phi_helper 28 [5, 3, 2] 7 := λ _, rfl
lemma phi_helper_thirty_29 : phi_helper 29 [5, 3, 2] 8 := λ _, rfl
lemma phi_helper_thirty_30 : phi_helper 30 [5, 3, 2] 8 := λ _, rfl

end data

end nat

lemma prove_reverse_core_cons {a : ℕ} {as bs cs : list ℕ} (h : list.reverse_core as (a::bs) = cs) :
  list.reverse_core (a::as) bs = cs := h

lemma prove_reverse_core_nil (as : list ℕ) :
  list.reverse_core [] as = as := rfl

lemma prove_reverse_lem {as bs : list ℕ} (h : list.reverse_core as [] = bs) :
  list.reverse as = bs := h

lemma prove_length_succ {α : Type*} (a : α) (as : list α) (m n : ℕ) (h : m + 1 = n)
  (h' : as.length = m) : (a :: as).length = n :=
by rwa [list.length_cons, h']

lemma prove_length_nil (α : Type*) : list.length (@list.nil α) = 0 := rfl

declare_trace phi_helper

namespace tactic

/- Given `as bs : list ℕ`, returns `(cs, ⊢ reverse_core as bs = cs)` -/
meta def prove_reverse_core : expr → expr → tactic (expr × expr)
| `(list.nil) bs := return (bs, `(prove_reverse_core_nil %%bs))
| `(list.cons %%a %%as) bs := do
    (cs, hcs) ← prove_reverse_core as `(@list.cons ℕ %%a %%bs),
    p ← mk_app `prove_reverse_core_cons [hcs],
    return (cs, p)
| _ _ := fail "match failed in prove_reverse_core"

/- Given `as : list ℕ`, returns `(bs, ⊢ reverse as = bs)` -/
meta def prove_reverse : expr → tactic (expr × expr)
| as := do
    (bs, hbs) ← prove_reverse_core as `(@list.nil ℕ),
    return (bs, `(@prove_reverse_lem %%as %%bs %%hbs))

/- Given `as : list α`, returns `(n, ⊢ length as = n)` -/
meta def prove_length (ic : instance_cache) : expr → tactic (expr × expr)
| `(@list.nil %%α) := do
    pf ← mk_app `prove_length_nil [α],
    return (`(0), pf)
| `(@list.cons %%α %%a %%as) := do
    (m, h') ← prove_length as,
    (_, n, hn) ← norm_num.prove_succ' ic m,
    pf ← mk_app `prove_length_succ [α, a, as, m, n, hn, h'],
    return (n, pf)
| _ := fail "match failed in prove_length"

/-- Given `x : ℕ`, `l : list ℕ`, returns `(m, ⊢ phi_helper x l m)`. -/
meta def prove_phi_helper :
  instance_cache → expr → expr → tactic (instance_cache × expr × expr)
| ic x `(list.nil) := do
    return (ic, x, `(nat.phi_helper_nil %%x))
| ic x z@`(list.cons %%p %%ps) := do
    nx ← x.to_nat,
    -- when_tracing `phi_helper (trace x),
    when_tracing `phi_helper (trace z),
    -- when_tracing `phi_helper (trace [x, z]),
    if nx = 0 then return (ic, x, `(nat.phi_helper_zero %%z)) else do
    (ic, xp, hxp) ← norm_num.prove_div_mod ic x p ff,
    (ic, m₁, hm₁) ← prove_phi_helper ic x ps,
    (ic, m₂, hm₂) ← prove_phi_helper ic xp ps,
    (m, hm) ← norm_num.prove_sub_nat ic m₁ m₂,
    return (ic, m, `(nat.phi_helper_cons %%x %%p %%ps %%xp %%m₁ %%m₂ %%m %%hxp %%hm₁ %%hm₂ %%hm))
| _ _ _ := fail "not list in prove_phi_helper"

namespace interactive
setup_tactic_parser

-- lemma count_primes {x sx ll t llt m : ℕ} (l l' : list ℕ) (hsx : sqrt x = sx)
--   (hl : primes_le sx = l) (hl' : l.reverse = l') (hll : l'.length = ll) (hphi : phi_helper x l' t)
--   (hllt : ll + t = llt) (hm : llt - 1 = m) (hx : 4 ≤ x) :
--   prime_counting x = m :=

meta def prove_phi_helper : command :=
do
  `(nat.phi_helper %%n %%l %%m) ← target,
  ic ← mk_instance_cache `(ℕ),
  (_, _, pf) ← tactic.prove_phi_helper ic n l,
  tactic.exact pf


meta def prove_prime_counting (h : parse texpr) : command :=
do
  `(nat.prime_counting %%x = %%m) ← target,
  ic ← mk_instance_cache `(ℕ),
  (ic, sx, hsx) ← norm_num.prove_sqrt ic x,
  hl ← to_expr h,
  `(_ = %%l) ← infer_type hl,
  (l', hl') ← prove_reverse l,
  (ll, hll) ← prove_length ic l',
  (ic, t, hphi) ← tactic.prove_phi_helper ic x l',
  (ic, llt, hllt) ← norm_num.prove_add_nat' ic ll t,
  (m, hm) ← norm_num.prove_sub_nat ic llt `(1),
  (ic, hx) ← norm_num.prove_pos_nat ic x,
  pf ← mk_app `nat.count_primes [l, l', hsx, hl, hl', hll, hphi, hllt, hm, hx],
  tactic.exact pf

-- meta def interactive.test' (h : parse texpr) : command :=
-- do
--   i ← to_expr h,
--   exact i

end interactive
end tactic

open nat

lemma primes_le_sqrt_1000 : primes_le 31 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] :=
begin
  simp only [primes_le, list.range_succ, list.filter_append, list.filter_singleton, list.range_zero,
    list.filter_nil],
  norm_num,
end

lemma primes_le_sqrt_10000 :
  primes_le 100 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97] :=
begin
  simp only [primes_le, list.range_succ, list.filter_append, list.filter_singleton, list.range_zero,
    list.filter_nil],
  norm_num,
end

lemma primes_le_sqrt_50000 :
  primes_le 223 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
    79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
    181, 191, 193, 197, 199, 211, 223] :=
begin
  simp only [primes_le, list.range_succ, list.filter_append, list.filter_singleton, list.range_zero,
    list.filter_nil],
  norm_num,
end

lemma primes_le_sqrt_100000 :
  primes_le 316 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
    79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
    181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293, 307, 311, 313] :=
begin
  simp only [primes_le, list.range_succ, list.filter_append, list.filter_singleton, list.range_zero,
    list.filter_nil],
  norm_num,
end

#eval ((primes_le 316).take 13).reverse

-- lemma phi_helper_100000_first :
--   phi_helper 100000 [313, 311, 307, 293, 283, 281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229,
--     227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127,
--     113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43] 66825 :=
-- begin
--   prove_phi_helper
-- end

-- set_option trace.phi_helper true

-- lemma phi_helper_100000_second :
--   phi_helper 100000 [277, 271, 269, 263, 257, 251, 241, 239, 233, 229,
--     227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139,
--     137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41,
--     37, 31, 29, 23, 19, 17, 13, 11, 7] 14540 :=
-- begin
--   prove_phi_helper,
-- end

set_option profiler true

lemma phi_helper_1000 :
  phi_helper 1000 [31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2] 158 :=
begin
  prove_phi_helper
end

lemma phi_helper_10000_first :
  phi_helper 10000 [97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13,
    11, 7, 5, 3, 2] 1205 :=
begin
  prove_phi_helper,
end

#eval 2 * 3 * 5 * 7 * 11

#eval sqrt 50000

lemma prime_counting_1000 : prime_counting 1000 = 168 :=
by prove_prime_counting primes_le_sqrt_1000

lemma prime_counting_10000 : prime_counting 10000 = 1229 :=
by prove_prime_counting primes_le_sqrt_10000

-- lemma prime_counting_50000 : prime_counting 50000 = 5133 :=
-- by prove_prime_counting primes_le_sqrt_50000

-- lemma prime_counting_100000 : prime_counting 100000 = 9592 :=
-- by prove_prime_counting primes_le_sqrt_100000
