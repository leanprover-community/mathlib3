import data.nat.prime
import number_theory.prime_counting
import liouville_data_fake
import tactic.slim_check

namespace nat

/-- The naturals `≤ x` which aren't divisible by anything from `ps`. -/
def phi_list (x : ℕ) (ps : list ℕ) : list ℕ :=
(list.range (x + 1)).filter (λ n, ps.all₂ (λ i, ¬ i ∣ n))

def phi (x : ℕ) (ps : list ℕ) : ℕ := (phi_list x ps).length

lemma phi_eq' {x : ℕ} {ps : list ℕ} :
  phi x ps = ((finset.range (x + 1)).filter (λ n, ps.all₂ (λ i, ¬ i ∣ n))).card :=
rfl

lemma phi_eq {x : ℕ} {ps : list ℕ} :
  phi x ps = ((finset.range (x + 1)).filter (λ n, ∀ i ∈ ps, ¬ i ∣ n)).card :=
by simp only [phi_eq', list.all₂_iff_forall]

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

lemma prime_counting_eq' {x : ℕ} (hx : 4 ≤ x) :
  prime_counting x - prime_counting (sqrt x) + 1 = phi x (nat.primes_le (sqrt x)) :=
begin
  have h₁ : finset.card (finset.filter (λ i, i = 1) (finset.range (x + 1))) = 1,
  { rw [finset.filter_eq', if_pos, finset.card_singleton],
    rw finset.mem_range_succ_iff,
    linarith },
  have h₂ : (finset.filter prime (finset.range (sqrt x + 1))) =
    finset.filter (λ p, prime p ∧ p ≤ sqrt x) (finset.range (x + 1)),
  { ext p,
    simp only [finset.mem_filter, finset.mem_range_succ_iff],
    have : p ≤ sqrt x → p ≤ x := le_trans' (nat.sqrt_le_self x),
    tauto },
  rw [←h₁, prime_counting, prime_counting, prime_counting', count_eq_card_filter_range,
    count_eq_card_filter_range, h₂, finset.filter_and, phi_eq, ←finset.card_sdiff,
    finset.sdiff_inter_self_left, finset.filter_sdiff, ←finset.card_disjoint_union,
    finset.filter_union_right],
  { congr' 1,
    ext p,
    simp only [not_le, finset.mem_filter, finset.mem_range_succ_iff, and.congr_right_iff,
      mem_primes_le, and_imp],
    intro hpx,
    split,
    { rintro (⟨hp₁, hp₂⟩ | rfl) q hq₁ hq₂,
      { rw prime_dvd_prime_iff_eq hq₂ hp₁,
        exact (hq₁.trans_lt hp₂).ne },
      simp only [nat.dvd_one],
      exact hq₂.ne_one },
    intro hp',
    rw or_iff_not_imp_right,
    intro hp'',
    suffices : prime p,
    { exact ⟨this, lt_of_not_le (λ hp''', hp' p hp''' this dvd_rfl)⟩ },
    have : p ≠ 0,
    { rintro rfl,
      simp only [dvd_zero, not_true] at hp',
      refine hp' 2 _ prime_two,
      rw nat.le_sqrt,
      norm_num1,
      exact hx },
    have : 2 ≤ p,
    { by_contra',
      interval_cases p,
      { exact ‹0 ≠ 0› rfl },
      { exact ‹1 ≠ 1› rfl } },
    rw prime_iff_no_prime_dvd,
    refine ⟨this, _⟩,
    intros q hq hq',
    refine hp' q _ hq',
    apply hq.trans _,
    apply sqrt_le_sqrt hpx },
  { rw finset.disjoint_right,
    simp [not_prime_one] {contextual := tt} },
  exact finset.inter_subset_left _ _,
end

lemma prime_counting_eq {x : ℕ} (hx : 4 ≤ x) :
  prime_counting x + 1 = prime_counting (sqrt x) + phi x (nat.primes_le (sqrt x)) :=
begin
  rw [←prime_counting_eq' hx, ←add_assoc, nat.add_sub_of_le],
  exact monotone_prime_counting (nat.sqrt_le_self _)
end

-- lemma prime_counting_eq'' {x : ℕ} (hx : 4 ≤ x) :
--   prime_counting x = prime_counting (sqrt x) + phi x (nat.primes_le (sqrt x)) - 1 :=
-- begin
--   rw [←prime_counting_eq],
-- end

lemma phi_div_eq' (x p : ℕ) (hp : p ≠ 0) (ps : list ℕ) :
  phi (x / p) ps =
    (((finset.range ((x / p) + 1)).filter (λ n, ∀ i ∈ ps, ¬ i ∣ n)).image (*p)).card :=
begin
  rw [phi_eq, finset.card_image_of_injective],
  exact mul_left_injective₀ hp,
end

lemma phi_div_eq {x p : ℕ} {ps : list ℕ} (hp : p ≠ 0) (h : ∀ q ∈ ps, coprime p q) :
  phi (x / p) ps = ((finset.range (x + 1)).filter (λ n, p ∣ n ∧ ∀ i ∈ ps, ¬ i ∣ n)).card :=
begin
  rw phi_div_eq' _ _ hp,
  congr' 1,
  ext n,
  simp only [finset.mem_image, finset.mem_filter, finset.mem_range_succ_iff, exists_prop,
    and_assoc],
  split,
  { rintro ⟨k, hk, hk', rfl⟩,
    rw nat.le_div_iff_mul_le hp.bot_lt at hk,
    refine ⟨hk, dvd_mul_left _ _, λ i hi hi', _⟩,
    exact hk' i hi (nat.coprime.dvd_of_dvd_mul_right (h _ hi).symm hi') },
  rintro ⟨hk, ⟨k, rfl⟩, hk'⟩,
  rw [mul_comm, ←nat.le_div_iff_mul_le hp.bot_lt] at hk,
  refine ⟨k, hk, λ i hi hi', _, mul_comm _ _⟩,
  exact hk' i hi (hi'.trans (dvd_mul_left _ _))
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

-- lemma phi_mod {x c : ℕ} {ps : list ℕ} (hc : c = list.prod ps) :
--   phi x ps = phi (x % c) ps + (x / c) * phi c ps :=
-- begin

-- end

def phi_helper (x l m) : Prop := (∀ i ∈ l, prime i) → list.nodup l → phi x l = m

lemma phi_helper_perm {x m : ℕ} (l l' : list ℕ) (h : l ~ l') :
  phi_helper x l m ↔ phi_helper x l' m :=
by simp only [phi_helper, h.mem_iff, h.nodup_iff, phi_perm h]

lemma phi_helper_reverse {x m : ℕ} (l : list ℕ) :
  phi_helper x l.reverse m ↔ phi_helper x l m :=
phi_helper_perm _ _ (list.reverse_perm _)

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
  (hllt : ll + t = llt) (hm : llt - 1 = m) (hx : 4 ≤ x) :
  prime_counting x = m :=
begin
  substs l l',
  rw phi_helper_reverse at hphi,
  rw list.length_reverse at hll,
  specialize hphi (λ i, list.of_mem_filter) primes_le_nodup,
  substs sx ll t llt m,
  rw [primes_le_card, ←prime_counting_eq hx, nat.add_sub_cancel],
end

lemma phi_helper_cons (x p ps) (xp m₁ m₂ : ℕ) (m : ℕ)
  (hxp : x / p = xp) (hm₁ : phi_helper x ps m₁) (hm₂ : phi_helper xp ps m₂) (hm : m₁ - m₂ = m) :
  phi_helper x (p :: ps) m :=
begin
  subst xp,
  intros hl₁ hl₂,
  have : phi x ps - phi (x / p) ps = phi x (p :: ps),
  { rw [←phi_cons _ p _ (hl₁ p (list.mem_cons_self _ _)).ne_zero, nat.add_sub_cancel],
    exact coprime_of_prime_nodup hl₁ hl₂ },
  rw [←this],
  simp only [list.nodup_cons] at hl₂,
  simp only [list.mem_cons_iff, forall_eq_or_imp] at hl₁,
  rwa [hm₁ hl₁.2 hl₂.2, hm₂ hl₁.2 hl₂.2],
end

lemma phi_helper_nil (x y : ℕ) (h : x + 1 = y) : phi_helper x [] y :=
begin
  intros h₁ h₂,
  rw [phi_eq, ←h],
  simp
end

lemma phi_helper_zero (p : ℕ) (ps : list ℕ) : phi_helper 0 (p :: ps) 0 :=
begin
  intros h₁ h₂,
  rw [phi_eq],
  simp [finset.filter_singleton],
end

-- lemma phi_helper_lt (x p : ℕ) (ps : list ℕ) : phi_helper x (p :: ps) 0 :=
-- begin
--   intros h₁ h₂,
--   rw [phi_eq],
--   simp [finset.filter_singleton],
-- end

section data

lemma phi_helper_thirty_0 :  phi_helper 0  [5, 3, 2] 0 := λ _ _, rfl
lemma phi_helper_thirty_1 :  phi_helper 1  [5, 3, 2] 1 := λ _ _, rfl
lemma phi_helper_thirty_2 :  phi_helper 2  [5, 3, 2] 1 := λ _ _, rfl
lemma phi_helper_thirty_3 :  phi_helper 3  [5, 3, 2] 1 := λ _ _, rfl
lemma phi_helper_thirty_4 :  phi_helper 4  [5, 3, 2] 1 := λ _ _, rfl
lemma phi_helper_thirty_5 :  phi_helper 5  [5, 3, 2] 1 := λ _ _, rfl
lemma phi_helper_thirty_6 :  phi_helper 6  [5, 3, 2] 1 := λ _ _, rfl
lemma phi_helper_thirty_7 :  phi_helper 7  [5, 3, 2] 2 := λ _ _, rfl
lemma phi_helper_thirty_8 :  phi_helper 8  [5, 3, 2] 2 := λ _ _, rfl
lemma phi_helper_thirty_9 :  phi_helper 9  [5, 3, 2] 2 := λ _ _, rfl
lemma phi_helper_thirty_10 : phi_helper 10 [5, 3, 2] 2 := λ _ _, rfl
lemma phi_helper_thirty_11 : phi_helper 11 [5, 3, 2] 3 := λ _ _, rfl
lemma phi_helper_thirty_12 : phi_helper 12 [5, 3, 2] 3 := λ _ _, rfl
lemma phi_helper_thirty_13 : phi_helper 13 [5, 3, 2] 4 := λ _ _, rfl
lemma phi_helper_thirty_14 : phi_helper 14 [5, 3, 2] 4 := λ _ _, rfl
lemma phi_helper_thirty_15 : phi_helper 15 [5, 3, 2] 4 := λ _ _, rfl
lemma phi_helper_thirty_16 : phi_helper 16 [5, 3, 2] 4 := λ _ _, rfl
lemma phi_helper_thirty_17 : phi_helper 17 [5, 3, 2] 5 := λ _ _, rfl
lemma phi_helper_thirty_18 : phi_helper 18 [5, 3, 2] 5 := λ _ _, rfl
lemma phi_helper_thirty_19 : phi_helper 19 [5, 3, 2] 6 := λ _ _, rfl
lemma phi_helper_thirty_20 : phi_helper 20 [5, 3, 2] 6 := λ _ _, rfl
lemma phi_helper_thirty_21 : phi_helper 21 [5, 3, 2] 6 := λ _ _, rfl
lemma phi_helper_thirty_22 : phi_helper 22 [5, 3, 2] 6 := λ _ _, rfl
lemma phi_helper_thirty_23 : phi_helper 23 [5, 3, 2] 7 := λ _ _, rfl
lemma phi_helper_thirty_24 : phi_helper 24 [5, 3, 2] 7 := λ _ _, rfl
lemma phi_helper_thirty_25 : phi_helper 25 [5, 3, 2] 7 := λ _ _, rfl
lemma phi_helper_thirty_26 : phi_helper 26 [5, 3, 2] 7 := λ _ _, rfl
lemma phi_helper_thirty_27 : phi_helper 27 [5, 3, 2] 7 := λ _ _, rfl
lemma phi_helper_thirty_28 : phi_helper 28 [5, 3, 2] 7 := λ _ _, rfl
lemma phi_helper_thirty_29 : phi_helper 29 [5, 3, 2] 8 := λ _ _, rfl
lemma phi_helper_thirty_30 : phi_helper 30 [5, 3, 2] 8 := λ _ _, rfl

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
    (ic, x1, hx1) ← norm_num.prove_succ' ic x,
    return (ic, x1, `(nat.phi_helper_nil %%x %%x1 %%hx1))
| ic x z@`(list.cons %%p %%ps) := do
    nx ← x.to_nat,
    -- when_tracing `phi_helper (trace x),
    when_tracing `phi_helper (trace z),
    -- when_tracing `phi_helper (trace [x, z]),
    if nx = 0 then return (ic, x, `(nat.phi_helper_zero %%p %%ps)) else do
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
  (ic, hx) ← norm_num.prove_le_nat ic `(4) x,
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
