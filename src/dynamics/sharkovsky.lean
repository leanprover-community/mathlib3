import data.nat.parity
import data.real.basic
import data.real.pointwise
import dynamics.periodic_pts
import topology.continuous_function.basic
import topology.instances.real
import data.nat.factorization.basic
import analysis.calculus.deriv
import analysis.calculus.mean_value
import order.upper_lower

--  0 <
--      3   <   5   <   7   <   9   < ...
--  < 2 * 3 < 2 * 5 < 2 * 7 < 2 * 9 < ...
--  < 4 * 3 < 4 * 5 < ...
--  < ...
--  < ... < 16 < 8 < 4 < 2 < 1

open nat

lemma weird_division_thing {n s k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) (hs : s ≠ 0) (hskn : s ∣ k * n)
  (h : (k * n / s) / (k * n / s).gcd n = k) :
  s ∣ n ∧ coprime s k :=
begin
  have h₁ := nat.eq_mul_of_div_eq_left hskn (nat.eq_mul_of_div_eq_left (nat.gcd_dvd_left _ _) h),
  rw [mul_assoc, nat.mul_right_inj hk.bot_lt] at h₁,
  have h₂ : s ∣ n,
  { rw dvd_iff_exists_eq_mul_left,
    exact ⟨_, h₁⟩ },
  rw [nat.mul_div_assoc _ h₂] at h h₁,
  have h₃ : (k * (n / s)).gcd n ∣ n / s,
  { rw [dvd_div_iff h₂, mul_comm, ←h₁] },
  rw [nat.mul_div_assoc _ h₃, mul_right_eq_self_iff hk.bot_lt] at h,
  refine ⟨h₂, _⟩,
  have h₄ : 0 < n / s := nat.div_pos (nat.le_of_dvd hn.bot_lt h₂) hs.bot_lt,
  rw [coprime_iff_gcd_eq_one, ←mul_right_eq_self_iff h₄, ←nat.gcd_mul_left, nat.div_mul_cancel h₂,
    mul_comm, nat.gcd_comm, eq_of_dvd_of_div_eq_one h₃ h],
end

def to_pair_aux : ℕ → ℕ → ℕ × ℕ
| 0       i := (i, 0)
| n@(k+1) i := if 2 ∣ n
    then have z : n / 2 < n := nat.div_lt_self k.succ_pos one_lt_two, to_pair_aux (n / 2) (i + 1)
    else (i, n)

lemma to_pair_aux_mul : ∀ n i, 2 ^ (to_pair_aux n i).1 * (to_pair_aux n i).2 = 2 ^ i * n
| 0 i := by simp [to_pair_aux]
| n@(k+1) i :=
  begin
    rw [to_pair_aux],
    split_ifs,
    { let z : (k + 1) / 2 < (k + 1) := nat.div_lt_self k.succ_pos one_lt_two,
      rw [to_pair_aux_mul ((k + 1) / 2) (i + 1), ←nat.mul_div_assoc _ h, pow_succ', mul_assoc,
        nat.mul_div_assoc _ (nat.dvd_mul_right _ _), nat.mul_div_cancel_left _ two_pos] },
    refl,
  end

lemma to_pair_aux_odd : ∀ n i, n ≠ 0 → ¬ 2 ∣ (to_pair_aux n i).2
| 0       i h := (h rfl).elim
| n@(k+1) i _ :=
  begin
    rw [to_pair_aux],
    split_ifs,
    { let z : (k + 1) / 2 < (k + 1) := nat.div_lt_self k.succ_pos one_lt_two,
      exact to_pair_aux_odd _ _ (nat.div_pos (nat.le_of_dvd k.succ_pos h) two_pos).ne' },
    exact h
  end

lemma odd_unique {a b c d : ℕ} (hb : odd b) (hd : odd d) (h : 2 ^ a * b = 2 ^ c * d) :
  a = c ∧ b = d :=
begin
  rw [nat.odd_iff_not_even, even_iff_two_dvd, ←prime_two.coprime_iff_not_dvd] at hb hd,
  have : a = c,
  { have h₁ : 2 ^ a ∣ 2 ^ c := (hd.pow_left _).dvd_of_dvd_mul_right ⟨_, h.symm⟩,
    have h₂ : 2 ^ c ∣ 2 ^ a := (hb.pow_left _).dvd_of_dvd_mul_right ⟨_, h⟩,
    exact pow_right_injective le_rfl (dvd_antisymm h₁ h₂) },
  subst c,
  exact ⟨rfl, mul_right_injective₀ (pow_ne_zero _ two_ne_zero) h⟩,
end

-- This calculates more efficiently than using nat.factors.count because it doesn't need to check
-- factors above 2, and avoids some multiplications
def to_pair (n : ℕ) := to_pair_aux n 0
def un_pair (i : ℕ × ℕ) := 2 ^ i.1 * i.2

lemma un_pair_inj_on {a b : ℕ × ℕ} (ha2 : odd a.2) (hb2 : odd b.2) (h : un_pair a = un_pair b) :
  a = b :=
begin
  rcases b with ⟨c, d⟩,
  rcases a with ⟨a, b⟩,
  simp only [un_pair] at *,
  rw [nat.odd_iff_not_even, even_iff_two_dvd, ←prime_two.coprime_iff_not_dvd] at ha2 hb2,
  have : a = c,
  { have h₁ : 2 ^ a ∣ 2 ^ c := (hb2.pow_left _).dvd_of_dvd_mul_right ⟨_, h.symm⟩,
    have h₂ : 2 ^ c ∣ 2 ^ a := (ha2.pow_left _).dvd_of_dvd_mul_right ⟨_, h⟩,
    exact pow_right_injective le_rfl (dvd_antisymm h₁ h₂) },
  subst c,
  ext1, { refl },
  exact mul_right_injective₀ (pow_ne_zero _ two_ne_zero) h,
end

lemma un_pair_to_pair (n : ℕ) : un_pair (to_pair n) = n :=
by rw [un_pair, to_pair, to_pair_aux_mul n 0, pow_zero, one_mul]

lemma un_pair_to_pair_left_inverse : function.left_inverse un_pair to_pair := un_pair_to_pair

lemma to_pair_injective : function.injective to_pair :=
un_pair_to_pair_left_inverse.injective

lemma odd_to_pair_snd_of_ne_zero {n : ℕ} (hn : n ≠ 0) : odd (to_pair n).2 :=
by { rw [odd_iff_not_even, even_iff_two_dvd], exact to_pair_aux_odd _ _ hn }

lemma to_pair_unique {k l n : ℕ} (hn : n ≠ 0) (hl : odd l) (h : 2 ^ k * l = n) :
  to_pair n = (k, l) :=
un_pair_inj_on (odd_to_pair_snd_of_ne_zero hn) hl (by rw [un_pair_to_pair, un_pair, ←h])

lemma to_pair_odd {n : ℕ} (hn : odd n) : to_pair n = (0, n) :=
to_pair_unique hn.pos.ne' hn (by simp)

lemma to_pair_bit1 {k : ℕ} : to_pair (bit1 k) = (0, bit1 k) := to_pair_odd (odd_bit1 _)

lemma to_pair_two_mul {n : ℕ} (hn : n ≠ 0) : to_pair (2 * n) = ((to_pair n).1 + 1, (to_pair n).2) :=
to_pair_unique (by simpa using hn) (odd_to_pair_snd_of_ne_zero hn) $
  by rw [pow_succ, mul_assoc, ←un_pair, un_pair_to_pair]

lemma to_pair_two_mul' {n : ℕ} (hn : n ≠ 0) : to_pair (2 * n) = to_pair n + (1, 0) :=
by { rw to_pair_two_mul hn, ext; refl }

lemma to_pair_bit0 {n : ℕ} (hn : n ≠ 0) : to_pair (bit0 n) = ((to_pair n).1 + 1, (to_pair n).2) :=
by { rw bit0_eq_two_mul, exact to_pair_two_mul hn }

lemma even_of_to_pair_fst_ne_zero {n : ℕ} (h : (to_pair n).1 ≠ 0) : even n :=
by { contrapose! h, rw ←odd_iff_not_even at h, rwa to_pair_odd }

lemma to_pair_fst_ne_zero_iff {n : ℕ} (hn : n ≠ 0) : (to_pair n).1 ≠ 0 ↔ even n :=
begin
  refine ⟨even_of_to_pair_fst_ne_zero, _⟩,
  rintro ⟨m, rfl⟩,
  simp only [ne.def, add_self_eq_zero] at hn,
  rw [←bit0, to_pair_bit0 hn],
  simp
end

lemma to_pair_fst_eq_zero_iff {n : ℕ} (hn : n ≠ 0) : (to_pair n).1 = 0 ↔ odd n :=
by rw [odd_iff_not_even, ←to_pair_fst_ne_zero_iff hn, not_not]

lemma to_pair_two_pow (k : ℕ) : to_pair (2 ^ k) = (k, 1) :=
to_pair_unique (pow_ne_zero _ two_ne_zero) odd_one (mul_one _)

lemma to_pair_snd_eq_zero_iff {n : ℕ} : (to_pair n).2 = 0 ↔ n = 0 :=
begin
  refine ⟨_, λ h, by simp [h, to_pair, to_pair_aux]⟩,
  intros h,
  by_contra' h',
  simpa [h] using odd_to_pair_snd_of_ne_zero h'
end

lemma to_pair_zero : to_pair 0 = (0, 0) := by rw [to_pair, to_pair_aux]
lemma to_pair_one : to_pair 1 = (0, 1) := to_pair_odd (by simp)
lemma to_pair_two : to_pair 2 = (1, 1) := to_pair_two_pow 1
lemma to_pair_three : to_pair 3 = (0, 3) := to_pair_bit1
lemma to_pair_four : to_pair 4 = (2, 1) := to_pair_two_pow 2
lemma to_pair_five : to_pair 5 = (0, 5) := to_pair_bit1
lemma to_pair_six : to_pair 6 = (1, 3) := by rw [to_pair_bit0 three_ne_zero, to_pair_three]

-- 2 ^ k * m ≤ 2 ^ l * n
inductive soa : ℕ × ℕ → ℕ × ℕ → Prop
| zero_le {k : ℕ} {l : ℕ × ℕ} : soa (k, 0) l
| powers {k l : ℕ} : l ≤ k → soa (k, 1) (l, 1)
| to_pow_two {k l m : ℕ} : soa (k, m + 2) (l, 1)
| same_level {k m n : ℕ} : m ≤ n → soa (k, m + 2) (k, n + 2)
| next_level {k l m n : ℕ} : k < l → soa (k, m + 2) (l, n + 2)

lemma soa_impl : ∀ {n₁ n₂ : ℕ × ℕ}, soa n₁ n₂ →
  n₁.2 = 0 ∨ (n₂.1 ≤ n₁.1 ∧ n₁.2 = 1 ∧ n₂.2 = 1) ∨ (2 ≤ n₁.2 ∧ n₂.2 = 1) ∨
  (n₁.1 = n₂.1 ∧ 2 ≤ n₁.2 ∧ 2 ≤ n₂.2 ∧ n₁.2 ≤ n₂.2) ∨ (2 ≤ n₁.2 ∧ 2 ≤ n₂.2 ∧ n₁.1 < n₂.1)
| _ _ soa.zero_le := or.inl rfl
| _ _ (soa.powers h) := or.inr (or.inl ⟨h, rfl, rfl⟩)
| _ _ soa.to_pow_two := or.inr $ or.inr $ or.inl ⟨le_add_self, rfl⟩
| _ _ (soa.same_level h) := by simpa
| _ _ (soa.next_level h) := or.inr $ or.inr $ or.inr $ or.inr $ by simpa

lemma soa_of : ∀ {n₁ n₂ : ℕ × ℕ},
  n₁.2 = 0 ∨ (n₂.1 ≤ n₁.1 ∧ n₁.2 = 1 ∧ n₂.2 = 1) ∨ (2 ≤ n₁.2 ∧ n₂.2 = 1) ∨
    (n₁.1 = n₂.1 ∧ 2 ≤ n₁.2 ∧ 2 ≤ n₂.2 ∧ n₁.2 ≤ n₂.2) ∨ (2 ≤ n₁.2 ∧ 2 ≤ n₂.2 ∧ n₁.1 < n₂.1) →
  soa n₁ n₂
| (_, 0) (_, _) _ := soa.zero_le
| (_, 1) (_, 1) (or.inr (or.inl h)) := soa.powers h.1
| (_, 1) (_, _) (or.inr (or.inr h)) := by norm_num at h
| (_, n+2) (_, 1) _ := soa.to_pow_two
| (k, n+2) (_, m+2) (or.inr (or.inr (or.inr (or.inl ⟨h, _, _, h'⟩)))) :=
    by { dsimp at h, rw h, exact soa.same_level (by simpa using h') }
| (_, n+2) (_, m+2) (or.inr (or.inr (or.inr (or.inr ⟨_, _, h⟩)))) := soa.next_level h

lemma soa_iff : ∀ {n₁ n₂ : ℕ × ℕ}, soa n₁ n₂ ↔
  n₁.2 = 0 ∨ (n₂.1 ≤ n₁.1 ∧ n₁.2 = 1 ∧ n₂.2 = 1) ∨ (2 ≤ n₁.2 ∧ n₂.2 = 1) ∨
    (n₁.1 = n₂.1 ∧ 2 ≤ n₁.2 ∧ 2 ≤ n₂.2 ∧ n₁.2 ≤ n₂.2) ∨ (2 ≤ n₁.2 ∧ 2 ≤ n₂.2 ∧ n₁.1 < n₂.1) :=
λ _ _, ⟨soa_impl, soa_of⟩

lemma soa_iff_powers {n₁ n₂ : ℕ × ℕ} (hn₁ : n₁.2 = 1) (hn₂ : n₂.2 = 1) : soa n₁ n₂ ↔ n₂.1 ≤ n₁.1 :=
by { rw soa_iff, simp only [hn₁, hn₂], norm_num }

instance decidable_soa : decidable_rel soa := λ n₁ n₂, decidable_of_iff' _ soa_iff

lemma soa_refl : ∀ (n : ℕ × ℕ), soa n n
| (_, 0)   := soa.zero_le
| (_, 1)   := soa.powers le_rfl
| (_, n+2) := soa.same_level le_rfl

lemma soa_trans : ∀ {n₁ n₂ n₃ : ℕ × ℕ}, soa n₁ n₂ → soa n₂ n₃ → soa n₁ n₃
| (_, _) (_, _) (_, _) soa.zero_le _ := soa.zero_le
| (_, _) (_, _) (_, _) (soa.powers h) (soa.powers h') := soa.powers (h'.trans h)
| (_, _) (_, _) (_, _) soa.to_pow_two (soa.powers _) := soa.to_pow_two
| (_, _) (_, _) (_, _) (soa.same_level _) soa.to_pow_two := soa.to_pow_two
| (_, _) (_, _) (_, _) (soa.same_level h) (soa.same_level h') := soa.same_level (h.trans h')
| (_, _) (_, _) (_, _) (soa.same_level h) (soa.next_level h') := soa.next_level h'
| (_, _) (_, _) (_, _) (soa.next_level _) soa.to_pow_two := soa.to_pow_two
| (_, _) (_, _) (_, _) (soa.next_level h') (soa.same_level _) := soa.next_level h'
| (_, _) (_, _) (_, _) (soa.next_level h) (soa.next_level h') := soa.next_level (h.trans h')

lemma soa_antisymm : ∀ {n₁ n₂ : ℕ × ℕ}, n₁.2 ≠ 0 → soa n₁ n₂ → soa n₂ n₁ → n₁ = n₂
| (_, _) (_, _) h soa.zero_le _ := (h rfl).elim
| (_, _) (_, _) _ (soa.powers h) (soa.powers h') := prod.ext (h'.antisymm h) rfl
| (_, _) (_, _) _ (soa.same_level h) (soa.same_level h') := prod.ext rfl (by rw h.antisymm h')
| (_, _) (_, _) _ (soa.same_level h) (soa.next_level h') := (lt_irrefl _ h').elim
| (_, _) (_, _) _ (soa.next_level h) (soa.same_level h') := (lt_irrefl _ h).elim
| (_, _) (_, _) _ (soa.next_level h) (soa.next_level h') := (lt_asymm h h').elim

lemma soa_total : ∀ {n₁ n₂ : ℕ × ℕ}, soa n₁ n₂ ∨ soa n₂ n₁
| (_, 0) (_, _) := or.inl soa.zero_le
| (_, _) (_, 0) := or.inr soa.zero_le
| (_, 1) (_, 1) := (le_total _ _).imp soa.powers soa.powers
| (_, 1) (_, m+2) := or.inr soa.to_pow_two
| (_, m+2) (_, 1) := or.inl soa.to_pow_two
| (k, m+2) (l, n+2) := (lt_trichotomy k l).elim3 (or.inl ∘ soa.next_level)
    (λ h, h ▸ (le_total m n).imp soa.same_level soa.same_level) (or.inr ∘ soa.next_level)

lemma soa_zero_left : ∀ {n₁ n₂ : ℕ × ℕ}, soa n₁ n₂ → n₂.2 = 0 → n₁.2 = 0
| _ ⟨_, _⟩ soa.zero_le rfl := rfl

lemma soa_has_min {s : set (ℕ × ℕ)} (hs : ∃ x ∈ s, prod.snd x ≠ 1) :
  ∃ y ∈ s, ∀ x ∈ s, soa y x :=
begin
  by_cases ∃ x ∈ s, prod.snd x = 0,
  { rcases h with ⟨⟨x, y⟩, hxy, rfl : y = 0⟩,
    exact ⟨_, hxy, λ y hy, soa.zero_le⟩ },
  push_neg at h,
  let s' := {x ∈ s | prod.snd x ≠ 1},
  have hs' : s'.nonempty,
  { obtain ⟨x, hx, hx'⟩ := hs,
    exact ⟨x, hx, hx'⟩ },
  let k : ℕ := Inf (prod.fst '' s'),
  let s'' := {x | (k, x) ∈ s'},
  have hk : k ∈ _ := nat.Inf_mem (hs'.image _),
  obtain ⟨⟨x, y⟩, hxy, hx : x = k⟩ := hk,
  subst x,
  have hs'' : s''.nonempty := ⟨y, hxy⟩,
  let l : ℕ := Inf s'',
  have hkl : (k, l) ∈ s ∧ l ≠ 1 := nat.Inf_mem hs'',
  refine ⟨(k, l), hkl.1, _⟩,
  rintro ⟨m, n⟩ hmn,
  have hl₂ : 2 ≤ l,
  { rw [←not_lt, nat.lt_succ_iff, le_iff_eq_or_lt, not_or_distrib, nat.lt_one_iff],
    exact ⟨hkl.2, h _ hkl.1⟩ },
  rcases eq_or_ne n 1 with rfl | hn,
  { exact soa_of (or.inr (or.inr (or.inl ⟨hl₂, rfl⟩))) },
  have : (m, n) ∈ s' := ⟨hmn, hn⟩,
  have hkm : k ≤ m := nat.Inf_le ⟨_, this, rfl⟩,
  rcases hkm.eq_or_lt with rfl | hkm,
  { have hln : l ≤ n := nat.Inf_le this,
    exact soa_of (or.inr (or.inr (or.inr (or.inl ⟨rfl, hl₂, hl₂.trans hln, hln⟩)))) },
  refine soa_of (or.inr (or.inr (or.inr (or.inr ⟨hl₂, _, hkm⟩)))),
  rw [←not_lt, nat.lt_succ_iff, le_iff_eq_or_lt, not_or_distrib, nat.lt_one_iff],
  exact ⟨hn, h _ hmn⟩,
end

lemma soa_partial_antisymm {k l : ℕ} :
  soa (to_pair k) (to_pair l) → soa (to_pair l) (to_pair k) → k = l :=
begin
  intros hkl hlk,
  by_cases (to_pair k).2 = 0,
  { rw to_pair_snd_eq_zero_iff at h,
    rw [h, to_pair_zero] at hlk,
    have : (to_pair l).2 = 0 := soa_zero_left hlk rfl,
    rw to_pair_snd_eq_zero_iff at this,
    rw [h, this] },
  exact to_pair_injective (soa_antisymm h hkl hlk),
end

lemma soa_one_right : ∀ (n : ℕ × ℕ), soa n (0, 1)
| (_, 0) := soa.zero_le
| (_, 1) := soa.powers (nat.zero_le _)
| (_, n+2) := soa.to_pow_two

lemma odd_le_iff_aux {n m₁ m₂ : ℕ} (hn : 2 ≤ n) :
  soa (0, n) (m₁, m₂) ↔ (m₂ = 1) ∨ (m₁ = 0 ∧ n ≤ m₂) ∨ (2 ≤ m₂ ∧ m₁ ≠ 0) :=
by { simp only [soa_iff, pos_iff_ne_zero], tauto {closer := `[linarith]} }

def sharkovsky := ℕ

namespace sharkovsky

def of_nat (n : ℕ) : sharkovsky := n
def to_nat (n : sharkovsky) : ℕ := n

@[simp] lemma to_nat_of_nat (n : ℕ) : to_nat (of_nat n) = n := rfl
@[simp] lemma of_nat_to_nat (n : sharkovsky) : of_nat (to_nat n) = n := rfl
@[simp] lemma to_nat_inj {n m : sharkovsky} : to_nat n = to_nat m ↔ n = m := iff.rfl
@[simp] lemma of_nat_inj {n m : ℕ} : of_nat n = of_nat m ↔ n = m := iff.rfl

@[simp] protected lemma «forall» {p : sharkovsky → Prop} : (∀ a, p a) ↔ ∀ a, p (of_nat a) := iff.rfl
@[simp] protected lemma «exists» {p : sharkovsky → Prop} : (∃ a, p a) ↔ ∃ a, p (of_nat a) := iff.rfl

@[elab_as_eliminator]
protected def rec {C : sharkovsky → Sort*} (h₂ : Π a : ℕ, C (of_nat a)) :
  Π a : sharkovsky, C a := h₂

instance : linear_order sharkovsky :=
{ le := λ n m, soa (to_pair n.to_nat) (to_pair m.to_nat),
  le_refl := λ _, soa_refl _,
  le_trans := λ _ _ _, soa_trans,
  le_total := λ _ _, soa_total,
  le_antisymm := λ _ _, soa_partial_antisymm,
  decidable_le := λ n m, decidable_soa (to_pair n) (to_pair m) }

end sharkovsky

local notation n ` ≼ `:50 m:50 := sharkovsky.of_nat n ≤ sharkovsky.of_nat m
local notation n ` ≺ `:50 m:50 := sharkovsky.of_nat n < sharkovsky.of_nat m

namespace sharkovsky

lemma of_nat_iff {n m : ℕ} : n ≼ m ↔ soa (to_pair n) (to_pair m) := iff.rfl

@[simp] lemma le_one (n : ℕ) : n ≼ 1 :=
by { rw [of_nat_iff, to_pair_one], exact soa_one_right (to_pair n) }

@[simp] lemma zero_le (n : ℕ) : 0 ≼ n :=
by { rw [of_nat_iff, to_pair_zero], exact soa.zero_le }

instance : bounded_order sharkovsky :=
{ top := of_nat 1,
  le_top := le_one,
  bot := of_nat 0,
  bot_le := zero_le }

@[simp] lemma to_nat_bot : to_nat ⊥ = 0 := rfl
@[simp] lemma to_nat_top : to_nat ⊤ = 1 := rfl
@[simp] lemma of_nat_zero : of_nat 0 = ⊥ := rfl
@[simp] lemma of_nat_one : of_nat 1 = ⊤ := rfl
@[simp] lemma of_nat_eq_top_iff {n : ℕ} : of_nat n = ⊤ ↔ n = 1 := iff.rfl
@[simp] lemma of_nat_eq_bot_iff {n : ℕ} : of_nat n = ⊥ ↔ n = 0 := iff.rfl

@[simp] lemma le_zero_iff (n : ℕ) : n ≼ 0 ↔ n = 0 := le_bot_iff

@[simp] lemma one_le_iff (n : ℕ) : 1 ≼ n ↔ n = 1 := top_le_iff

lemma eq_one_or_three_le_of_odd : ∀ {n : ℕ}, odd n → n = 1 ∨ 3 ≤ n
| _ ⟨0, rfl⟩ := or.inl rfl
| _ ⟨(n+1), rfl⟩ := or.inr (by linarith)

lemma three_le_of_odd_of_ne_one {n : ℕ} (hn : odd n) (hn' : n ≠ 1) : 3 ≤ n :=
(eq_one_or_three_le_of_odd hn).resolve_left hn'

lemma odd_le_iff {n m : ℕ} (hn : odd n) (hn' : n ≠ 1) (hm : m ≠ 0) :
  n ≼ m ↔ even m ∨ odd m ∧ (n ≤ m ∨ m = 1) :=
begin
  have : 3 ≤ n := three_le_of_odd_of_ne_one hn hn',
  have : (to_pair m).2 = 1 ∨ (to_pair m).1 = 0 ∧ n ≤ (to_pair m).2 ∨
    2 ≤ (to_pair m).2 ∧ ¬(to_pair m).1 = 0 ↔ ¬(to_pair m).1 = 0 ∨
    ((to_pair m).1 = 0 ∧ (n ≤ (to_pair m).2 ∨ (to_pair m).2 = 1)),
  { cases eq_one_or_three_le_of_odd (odd_to_pair_snd_of_ne_zero hm),
    { simp [h, em'] },
    have : 2 ≤ (to_pair m).2, by linarith only [h],
    tauto },
  rw [of_nat_iff, to_pair_odd hn, ←@prod.mk.eta _ _ (to_pair m),
    odd_le_iff_aux (show 2 ≤ n, by linarith), this, to_pair_fst_eq_zero_iff hm, ←even_iff_not_odd],
  refine or_congr_right' (and_congr_right (λ hm', _)),
  rw [to_pair_odd hm'],
end

lemma three_le_of_ne_zero {n : ℕ} (hn : n ≠ 0) : 3 ≼ n :=
begin
  rw odd_le_iff (odd_bit1 _) (show 3 ≠ 1, by linarith) hn,
  exact (nat.even_or_odd n).imp_right (λ h, ⟨h, (eq_one_or_three_le_of_odd h).symm⟩),
end

lemma ne_zero_of_ge_ne_zero {n m : ℕ} (hnm : n ≼ m) (hn : n ≠ 0) : m ≠ 0 :=
begin
  contrapose! hn,
  cases hn,
  simpa using hnm.antisymm (zero_le n),
end

lemma three_le_iff_ne_zero (n : ℕ) : 3 ≼ n ↔ n ≠ 0 :=
⟨λ h, ne_zero_of_ge_ne_zero h (by simp), three_le_of_ne_zero⟩

lemma odd_le_even_of_ne_one {n m : ℕ} (hn : odd n) (hn' : n ≠ 1) (hm : even m) (hm' : m ≠ 0) :
  n ≼ m :=
by simp [odd_le_iff hn hn' hm', hm]

lemma two_pow_le_two_pow_iff {k l : ℕ} : 2 ^ l ≼ 2 ^ k ↔ k ≤ l :=
by { rw [of_nat_iff, to_pair_two_pow, to_pair_two_pow, soa_iff_powers]; refl }

lemma not_two_pow_iff {n : ℕ} : (∀ l : ℕ, 2 ^ l ≠ n) ↔ (to_pair n).2 ≠ 1 :=
begin
  rcases eq_or_ne n 0 with rfl | hn',
  { simp only [to_pair_zero, ne.def, nat.zero_ne_one, not_false_iff, iff_true],
    exact λ l, pow_ne_zero l two_ne_zero },
  split,
  { intros hl hn,
    have : 2 ^ (to_pair n).1 * (to_pair n).2 = n := un_pair_to_pair _,
    rw [hn, mul_one] at this,
    exact hl _ this },
  rintro hn l rfl,
  rw to_pair_two_pow at hn,
  exact hn rfl
end

lemma le_two_pow_of_not_two_pow {n k : ℕ} (hn : ∀ l : ℕ, 2 ^ l ≠ n) : n ≼ 2 ^ k :=
begin
  rcases eq_or_ne n 0 with rfl | hn',
  { exact zero_le _ },
  rw not_two_pow_iff at hn,
  rw [of_nat_iff, to_pair_two_pow],
  refine soa_of (or.inr (or.inr (or.inl ⟨_, rfl⟩))),
  exact (nat.le_succ _).trans (three_le_of_odd_of_ne_one (odd_to_pair_snd_of_ne_zero hn') hn),
end

lemma le_two_mul_self_of_not_two_pow {n : ℕ} (hn : ∀ l : ℕ, 2 ^ l ≠ n) : n ≼ 2 * n :=
begin
  rcases eq_or_ne n 0 with rfl | hn',
  { exact zero_le _ },
  rw not_two_pow_iff at hn,
  rw [of_nat_iff],
  rw soa_iff,
  right, right, right, right,
  rw to_pair_two_mul hn',
  simp only [lt_add_iff_pos_right, lt_one_iff, eq_self_iff_true, and_true, and_self],
  linarith only [three_le_of_odd_of_ne_one (odd_to_pair_snd_of_ne_zero hn') hn],
end

-- If s contains a non-power-of-two, it has a minimum element
lemma exists_min {s : set ℕ} (hs : ∃ x ∈ s, ∀ l : ℕ, 2 ^ l ≠ x):
  ∃ x ∈ s, ∀ y ∈ s, x ≼ y :=
begin
  let s' := to_pair '' s,
  have : ∃ x ∈ s', prod.snd x ≠ 1,
  { obtain ⟨x, hx, hx'⟩ := hs,
    refine ⟨_, ⟨_, hx, rfl⟩, _⟩,
    rwa ←not_two_pow_iff },
  obtain ⟨_, ⟨x, hx, rfl⟩, hx'⟩ := soa_has_min this,
  refine ⟨x, hx, λ y hy, _⟩,
  exact hx' _ ⟨_, hy, rfl⟩,
end

lemma upper_set_two_pow {s : set ℕ} (hs : ∀ x y, x ≼ y → x ∈ s → y ∈ s) (hs' : ∃ n : ℕ, 2 ^ n ∉ s)
  (hs'' : 1 ∈ s) :
  ∃ n : ℕ, ∀ m, m ≤ n ↔ 2 ^ m ∈ s :=
begin
  let s' : set ℕ := {n : ℕ | 2 ^ n ∈ s},
  have h₁s' : bdd_above s',
  { obtain ⟨n, hn⟩ := hs',
    refine ⟨n, λ m (hm : 2 ^ m ∈ s), _⟩,
    by_contra',
    refine hn (hs _ _ _ hm),
    rw two_pow_le_two_pow_iff,
    exact this.le },
  have h₂s' : s'.nonempty := ⟨0, hs''⟩,
  refine ⟨Sup s', λ m, ⟨λ hm, _, le_cSup h₁s'⟩⟩,
  rw ←two_pow_le_two_pow_iff at hm,
  refine hs _ _ hm _,
  exact nat.Sup_mem h₂s' h₁s',
end

@[simp] lemma doubling_iff {n m : ℕ} : 2 * n ≼ 2 * m ↔ n ≼ m :=
begin
  rcases eq_or_ne n 0 with rfl | hn, { simp },
  rcases eq_or_ne m 0 with rfl | hm, { simp },
  rw [of_nat_iff, of_nat_iff, to_pair_two_mul hn, to_pair_two_mul hm, soa_iff, soa_iff],
  simp,
end

@[simp] lemma bit0_le_bit0_iff {n m : ℕ} : bit0 n ≼ bit0 m ↔ n ≼ m :=
by rw [bit0_eq_two_mul n, bit0_eq_two_mul m, doubling_iff]

@[simp] lemma bit1_le_bit1_iff {n m : ℕ} : bit1 n ≼ bit1 m ↔ (n ≠ 0 ∧ n ≤ m) ∨ m = 0 :=
by { rcases eq_or_ne n 0 with rfl | hn; simp [odd_le_iff, *] }

@[simp] lemma bit1_le_bit0_iff {n m : ℕ} : bit1 n ≼ bit0 m ↔ n ≠ 0 ∧ m ≠ 0 :=
begin
  rcases eq_or_ne n 0 with rfl | hn, { simp },
  rcases eq_or_ne m 0 with rfl | hm, { simp },
  simp only [hn, hm, ne.def, not_false_iff, and_self, iff_true],
  apply odd_le_even_of_ne_one; simp [*]
end

@[simp] lemma bit0_le_bit1_iff {n m : ℕ} : bit0 n ≼ bit1 m ↔ n = 0 ∨ m = 0 :=
by rw [←not_iff_not, not_or_distrib, ←bit1_le_bit0_iff, not_le, lt_iff_le_and_ne]; simp [and_comm]

-- an upper set of sharkovsky is empty, Ici, or powers of two
lemma upper_set_iff {s : set sharkovsky} :
  is_upper_set s ↔
    s = ∅ ∨ (∃ x, s = set.Ici x) ∨ s = set.range (λ n : ℕ, sharkovsky.of_nat (2 ^ n)) :=
begin
  symmetry,
  split,
  { rintro (rfl | ⟨x, rfl⟩ | rfl),
    { exact is_upper_set_empty },
    { exact is_upper_set_Ici _ },
    simp only [is_upper_set, set.mem_range, forall_exists_index],
    rintro _ y h x rfl,
    induction y using sharkovsky.rec,
    by_contra' hy',
    exact hy' x (h.antisymm (sharkovsky.le_two_pow_of_not_two_pow hy')) },
  intro h,
  rcases s.eq_empty_or_nonempty with rfl | hs,
  { exact or.inl rfl },
  right,
  rw or_iff_not_imp_left,
  intro h',
  push_neg at h',
  have h'' : ∀ ⦃a b : ℕ⦄, a ≼ b → of_nat a ∈ s → of_nat b ∈ s := h,
  rw sharkovsky.forall at h',
  rw ←h.top_mem at hs,
  have : s ⊆ set.range (λ n : ℕ, of_nat (2 ^ n)),
  { by_contra' t,
    simp only [set.subset_def, set.mem_range, sharkovsky.forall, of_nat_inj, not_forall,
      not_exists] at t,
    obtain ⟨x, hx, hx'⟩ := sharkovsky.exists_min t,
    exact h' x (set.subset.antisymm hx' (h.Ici_subset hx)) },
  refine set.subset.antisymm this _,
  by_contra' t,
  simp only [set.subset_def, not_forall, set.mem_range, exists_exists_eq_and, exists_prop] at t,
  obtain ⟨n, hn : ∀ (m : ℕ), m ≤ n ↔ of_nat (2 ^ m) ∈ s⟩ := upper_set_two_pow h'' t hs,
  apply h' (2 ^ n),
  ext m,
  induction m using sharkovsky.rec,
  split,
  { intro hm,
    obtain ⟨_, rfl : 2 ^ _ = m⟩ := this hm,
    rwa [set.mem_Ici, two_pow_le_two_pow_iff, hn] },
  intro h,
  simp only [set.mem_Ici] at h,
  exact h'' h ((hn _).1 le_rfl),
end

end sharkovsky

open function set

section proof

variables {f : ℝ → ℝ} {I : set ℝ} {P : finset ℝ}

lemma interval_eq_union {α : Type*} [linear_order α] {a b : α} :
  interval a b = Icc a b ∪ Icc b a := by rw [Icc_union_Icc', max_comm]; refl

lemma continuous_on.iterate (hf : continuous_on f I) (hf' : maps_to f I I) :
  ∀ n, continuous_on (f^[n]) I
| 0 := continuous_on_id
| (n+1) := by { rw iterate_succ, exact continuous_on.comp (continuous_on.iterate n) hf hf' }

lemma exists_fixed_point_Icc {a₁ a₂ : ℝ} (h : a₁ ≤ a₂)
  (hf : continuous_on f (Icc a₁ a₂)) (ha : a₁ ≤ f a₁ ∧ f a₂ ≤ a₂ ∨ f a₁ ≤ a₁ ∧ a₂ ≤ f a₂) :
  ∃ c ∈ Icc a₁ a₂, is_fixed_pt f c :=
begin
  rw ←interval_of_le h at *,
  have : (0 : ℝ) ∈ interval (f a₁ - a₁) (f a₂ - a₂),
  { simp only [interval_eq_union, mem_union, mem_Icc, sub_nonpos, sub_nonneg], tauto },
  obtain ⟨c, hc₁, hc₂⟩ := intermediate_value_interval (hf.sub continuous_on_id) this,
  exact ⟨c, hc₁, sub_eq_zero.1 hc₂⟩,
end

def finset.is_cycle {α : Type*} (P : finset α) (f : α → α) : Prop :=
  ∀ x ∈ P, f x ∈ P ∧ function.minimal_period f x = P.card

lemma finset.is_cycle.apply_mem_of_mem (hP : P.is_cycle f) {x : ℝ} (hx : x ∈ P) :
  f x ∈ P := (hP x hx).1

lemma finset.is_cycle.minimal_period (hP : P.is_cycle f) {x : ℝ} (hx : x ∈ P) :
  minimal_period f x = P.card := (hP x hx).2

lemma finset.is_cycle.iterate_apply_mem_of_mem (hP : P.is_cycle f)  :
  ∀ n {x}, x ∈ P → (f^[n] x ∈ P)
| 0 x hx := hx
| (n+1) x hx := finset.is_cycle.iterate_apply_mem_of_mem n (hP.apply_mem_of_mem hx)

lemma eq.is_periodic_pt {x : ℝ} {n : ℕ} (hx : minimal_period f x = n) : is_periodic_pt f n x :=
by { rw [←hx], exact is_periodic_pt_minimal_period _ _ }

lemma finset.is_cycle.iterate_card_apply (hP : P.is_cycle f) {x : ℝ} (hx : x ∈ P) :
  is_periodic_pt f P.card x :=
(hP.minimal_period hx).is_periodic_pt

lemma finset.is_cycle.iterate_ne (hP : P.is_cycle f) {x : ℝ} (hx : x ∈ P) {n : ℕ}
  (hn : n ≠ 0) (hn' : n < P.card) :
  f^[n] x ≠ x :=
begin
  rintro (h : is_periodic_pt f n x),
  apply hn'.not_le,
  rw ←hP.minimal_period hx,
  exact h.minimal_period_le hn.bot_lt,
end

lemma minimal_period_apply {n : ℕ} {x : ℝ} (hn : n ≠ 0) (hx : minimal_period f x = n) :
  minimal_period f (f x) = n :=
begin
  have : is_periodic_pt f n (f x) := hx.is_periodic_pt.apply,
  refine eq_of_le_of_not_lt (this.minimal_period_le hn.bot_lt) _,
  intro h,
  have := this.minimal_period_pos hn.bot_lt,
  have hn' : 1 ≤ n := hn.bot_lt,
  have := (is_periodic_pt_minimal_period f (f x)).apply_iterate (n - 1),
  rw [←iterate_succ_apply, succ_eq_add_one, nat.sub_add_cancel hn', ←hx,
    iterate_minimal_period] at this,
  have := this.minimal_period_le ‹_›,
  linarith
end

lemma minimal_period_apply_iterate {n : ℕ} (hn : n ≠ 0) :
  ∀ {x : ℝ} m, minimal_period f x = n → minimal_period f (f^[m] x) = n
| x 0 h := h
| x (m+1) h := minimal_period_apply_iterate m (minimal_period_apply hn h)

lemma exists_cycle_of_minimal_period {n : ℕ} {x : ℝ} (hf : maps_to f I I) (hx : x ∈ I) (hn : n ≠ 0)
  (hx' : minimal_period f x = n) :
  ∃ (P : finset ℝ), P.is_cycle f ∧ x ∈ P ∧ P.card = n ∧ ↑P ⊆ I :=
begin
  let P := (finset.range n).image (λ i, f^[i] x),
  have hx'' : (f^[n]) x = x, rw [←hx', iterate_minimal_period],
  have hx''' : x ∈ P, { rw [finset.mem_image], exact ⟨0, by simpa [pos_iff_ne_zero], rfl⟩ },
  have : P.card = n,
  { rw [finset.card_image_of_inj_on, finset.card_range],
    simp only [set.inj_on, finset.mem_coe, finset.mem_range],
    intros i hi j hj z,
    refine eq_of_lt_minimal_period_of_iterate_eq _ _ z;
    rwa hx' },
  have hPI : ↑P ⊆ I,
  { simp only [set.subset_def, finset.coe_image, mem_image, finset.mem_coe, finset.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
    rintro m hm,
    clear_dependent n,
    induction m generalizing x,
    exacts [hx, m_ih (hf hx)] },
  refine ⟨P, λ y hy, _, ‹_›, ‹_›, ‹_›⟩,
  simp only [finset.mem_image, finset.mem_range, exists_prop] at hy,
  obtain ⟨m, hm, rfl⟩ := hy,
  split,
  { rw ←iterate_succ_apply' f,
    cases lt_or_eq_of_le (succ_le_of_lt hm),
    { simp only [finset.mem_image, finset.mem_range],
      exact ⟨_, h, rfl⟩ },
    rwa [h, hx''] },
  { rw this, exact minimal_period_apply_iterate hn _ hx' },
end

lemma is_closed_sep_eq {α β : Type*} [topological_space α] [topological_space β] [t2_space α]
  {f g : β → α} {s : set β} (hs : is_closed s)
  (hf : continuous_on f s) (hg : continuous_on g s) : is_closed {x ∈ s | f x = g x} :=
begin
  have := is_closed_eq
    (continuous_on_iff_continuous_restrict.1 hf) (continuous_on_iff_continuous_restrict.1 hg),
  obtain ⟨u, hu, hu'⟩ := is_closed_induced_iff.1 this,
  have : s ∩ u = {x ∈ s | f x = g x},
  { ext i,
    apply and_congr_right,
    rw set.ext_iff at hu',
    simp only [mem_preimage, restrict_apply, mem_set_of_eq, set_coe.forall, subtype.coe_mk] at hu',
    exact hu' _ },
  rw ←this,
  apply is_closed.inter hs hu,
end

lemma period_two_of {y : ℝ} (hy₁ : f y ≠ y) (hy₂ : f^[2] y = y) :
  minimal_period f y = 2 :=
begin
  refine ((nat.dvd_prime prime_two).1 (is_periodic_pt.minimal_period_dvd hy₂)).resolve_left _,
  rwa is_fixed_point_iff_minimal_period_eq_one,
end

lemma part_a_first_aux (hP : P.is_cycle f) (hP₂ : 2 ≤ P.card) (hPI : ↑P ⊆ I)
  (hf : continuous_on f I) (hf' : maps_to f I I) [ord_connected I] :
  ∃ (h : P.nonempty) (z ∈ I),
    P.min' h ≤ z ∧ is_fixed_pt f z ∧ z ≤ (f^[P.card-1] (P.min' h)) ∧
    (3 ≤ P.card →
      ∃ v y ∈ I,
        f^[2] v = P.min' h ∧ minimal_period f y = 2 ∧
          P.min' h ≤ y ∧ y < v ∧ v ≤ z ∧ z ≤ f v ∧
            (∀ x ∈ Icc y v, z < f x) ∧ ∀ x ∈ Ioc y v, f^[2] x < x) :=
begin
  have hP₁ : 1 ≤ P.card := (nat.le_succ _).trans hP₂,
  have hPne : P.nonempty, { rwa ←finset.card_pos },
  let b := (f^[P.card-1]) (P.min' hPne),
  have hb₁ : b ∈ P := hP.iterate_apply_mem_of_mem _ (P.min'_mem _),
  have hb₂ : f b = P.min' hPne,
  { rw [←iterate_succ_apply' f, succ_eq_add_one, nat.sub_add_cancel hP₁,
      (hP.iterate_card_apply (finset.min'_mem _ _)).eq] },
  have hb₃ : P.min' hPne < b,
  { refine lt_of_le_of_ne (P.min'_le _ hb₁) _,
    simpa [←hb₂] using hP.iterate_ne hb₁ one_ne_zero hP₂ },
  have : ∃ a ∈ Icc (P.min' hPne) b, b ≤ f a,
  { by_contra' h,
    have : ∀ i, (f^[i] (P.min' hPne)) < b,
    { intro i,
      induction i with i ih,
      { exact hb₃ },
      rw function.iterate_succ_apply',
      exact h _ ⟨P.min'_le _ (hP.iterate_apply_mem_of_mem _ (P.min'_mem _)), ih.le⟩ },
    exact lt_irrefl _ (this (P.card - 1)) },
  obtain ⟨a, ⟨ha₁, ha₂⟩, ha₃⟩ := this,
  have hf₀ : Icc (P.min' hPne) b ⊆ I := set.Icc_subset _ (hPI (P.min'_mem _)) (hPI hb₁),
  have hf₁ : continuous_on f (Icc (P.min' hPne) b) := hf.mono hf₀,
  have hf₂ : continuous_on f (Icc a b) := hf₁.mono (Icc_subset_Icc_left ha₁),
  have : Icc a b ⊆ I :=
    (Icc_subset_Icc_left ha₁).trans (set.Icc_subset _ (hPI (P.min'_mem _)) (hPI hb₁)),
  obtain ⟨z, ⟨hz₁, hz₂⟩, hz₃⟩ := exists_fixed_point_Icc ha₂ hf₂
    (or.inl ⟨by linarith only [ha₂, ha₃], by linarith only [hb₂, hb₃]⟩),
  refine ⟨hPne, z, ‹Icc a b ⊆ I› ⟨hz₁, hz₂⟩, by linarith, hz₃, hz₂, _⟩,
  intro hP₃,
  obtain ⟨v, ⟨hv₁, hv₂⟩, hv₃⟩ := intermediate_value_Icc' hz₁ (hf₂.mono (Icc_subset_Icc_right hz₂))
    ⟨by rwa hz₃.eq, ha₃⟩,
  have hv₄ : (f^[2] v) = P.min' hPne,
  { rw [iterate_succ_apply, iterate_one, hv₃, hb₂] },
  have hPmin : P.min' hPne < (f^[2] (P.min' hPne)),
  { apply lt_of_le_of_ne (P.min'_le _ (hP.iterate_apply_mem_of_mem _ (P.min'_mem _))),
    exact (hP.iterate_ne (P.min'_mem _) two_ne_zero hP₃).symm },
  have hv₅ : (f^[2] v < v),
  { refine lt_of_le_of_ne _ _,
    { rw hv₄, exact ha₁.trans hv₁ },
    intro i,
    refine hP.iterate_ne hb₁ two_ne_zero hP₃ _,
    rw [←hv₃, ←iterate_succ_apply, iterate_succ_apply', i] },
  have hv₆ : P.min' hPne < v, { rwa ←hv₄ },
  have hv₇ : Icc (P.min' hPne) v ⊆ I,
  { exact (set.Icc_subset _ (hPI (P.min'_mem _)) (‹Icc a b ⊆ I› ⟨hv₁, hv₂.trans hz₂⟩)) },
  have hv₈ : continuous_on (f^[2]) (Icc (P.min' hPne) v),
  { rw [iterate_succ, iterate_one],
    exact hf.comp (hf.mono hv₇) (hf'.mono_left hv₇) },
  let Y := {x ∈ Icc (P.min' hPne) v | f^[2] x = x},
  have hY₁ : Y.nonempty,
  { obtain ⟨c, hc, hc'⟩ := exists_fixed_point_Icc hv₆.le hv₈ (or.inl ⟨hPmin.le, hv₅.le⟩),
    exact ⟨c, hc, hc'⟩ },
  have hY₂ : bdd_above Y := bdd_above.mono (set.sep_subset _ _) bdd_above_Icc,
  have hY₃ : is_closed Y := is_closed_sep_eq is_closed_Icc hv₈ continuous_on_id,
  let y := Sup Y,
  obtain ⟨⟨hy₁ : _ ≤ y, hy₂ : y ≤ _⟩, hy₃ : (f^[2] y) = y⟩ := hY₃.cSup_mem hY₁ hY₂,
  have hy₄ : y < v,
  { refine lt_of_le_of_ne ‹_› _,
    intro h,
    refine hv₅.ne' _,
    rwa [←h, hy₃] },
  have hy₅ : y < z := by linarith,
  have hy₆ : ∀ x ∈ Icc y v, z < f x,
  { rintro x ⟨hx₁, hx₂⟩,
    apply lt_of_not_le (λ hx₃, _),
    have : continuous_on f (Icc x v) := hf₁.mono (Icc_subset_Icc (by linarith) (by linarith)),
    obtain ⟨u, ⟨hu₁, hu₂⟩, hu₃⟩ := intermediate_value_Icc hx₂ this ⟨hx₃, by rwa hv₃⟩,
    have : Icc u v ⊆ (Icc (P.min' hPne) b) := Icc_subset_Icc (by linarith) (by linarith),
    have : continuous_on (f^[2]) (Icc u v),
    { rw [iterate_succ, iterate_one],
      exact (hf.comp hf₁ (hf'.mono_left hf₀)).mono this },
    have hyu : y < u,
    { refine lt_of_le_of_ne (hx₁.trans hu₁) _,
      rintro rfl,
      apply hy₅.ne,
      rw [←hy₃, iterate_succ_apply, iterate_one, hu₃, hz₃.eq] },
    have huz : u ≤ (f^[2] u),
    { rw [iterate_succ_apply, iterate_one, hu₃, hz₃.eq],
      linarith },
    obtain ⟨y', ⟨hy'₁, hy'₂⟩, hy'₃⟩ := exists_fixed_point_Icc hu₂ this (or.inl ⟨huz, hv₅.le⟩),
    have : y' ≤ y := le_cSup hY₂ ⟨⟨by linarith, hy'₂⟩, hy'₃⟩,
    linarith },
  have hy₇ : ∀ x ∈ Ioc y v, (f^[2] x) < x,
  { rintro x ⟨hx₁, hx₂⟩,
    by_contra' hx₃,
    have : continuous_on (f^[2]) (Icc x v),
    { rw [iterate_succ, iterate_one],
      exact (hf.comp hf₁ (hf'.mono_left hf₀)).mono (Icc_subset_Icc (by linarith) (by linarith)) },
    obtain ⟨y', ⟨hy'₁, hy'₂⟩, hy'₃⟩ := exists_fixed_point_Icc hx₂ this (or.inl ⟨hx₃, hv₅.le⟩),
    have : y' ≤ y := le_cSup hY₂ ⟨⟨by linarith, hy'₂⟩, hy'₃⟩,
    linarith },
  refine ⟨v, hf₀ ⟨hy₁.trans hy₂, by linarith⟩, y, hf₀ ⟨hy₁, by linarith⟩, hv₄,
    period_two_of (λ h, _) hy₃, hy₁, hy₄, hv₂, by rwa hv₃, hy₆, hy₇⟩,
  apply hy₅.not_lt,
  rw ←h,
  apply hy₆ y (left_mem_Icc.2 hy₂),
end

lemma part_a_one (hP : P.is_cycle f) (hP₂ : 2 ≤ P.card) (hPI : ↑P ⊆ I) (hf : continuous_on f I)
  (hf' : maps_to f I I) [ord_connected I] :
  (∃ c ∈ I, is_fixed_pt f c) :=
begin
  obtain ⟨_, z, hz, _, hz', _⟩ := part_a_first_aux hP hP₂ hPI hf hf',
  exact ⟨z, hz, hz'⟩,
end

lemma part_a_two (hP : P.is_cycle f) (hP₂ : 3 ≤ P.card) (hPI : ↑P ⊆ I) (hf : continuous_on f I)
  (hf' : maps_to f I I) [ord_connected I] :
  (∃ c ∈ I, minimal_period f c = 2) :=
begin
  obtain ⟨_, _, _, _, _, _, h⟩ := part_a_first_aux hP (by linarith) hPI hf hf',
  obtain ⟨_, _, y, hy, _, hy', _⟩ := h hP₂,
  exact ⟨y, hy, hy'⟩
end

lemma odd_of_dvd_odd {k n : ℕ} (hn : odd n) (hk : k ∣ n) : odd k :=
begin
  rcases hk with ⟨n, rfl⟩,
  exact odd.of_mul_left hn,
end

lemma part_b (hP : P.is_cycle f) (hP₂ : 3 ≤ P.card) (hP₃ : odd P.card) (hPI : ↑P ⊆ I)
  (hf : continuous_on f I) (hf' : maps_to f I I) [ord_connected I] :
  ∃ c ∈ I, minimal_period f c = P.card + 2 :=
begin
  obtain ⟨hPne, z, hz₁, hz₂, hz₃, hz₄, h⟩ := part_a_first_aux hP (by linarith) hPI hf hf',
  specialize h hP₂,
  obtain ⟨v, hv₁, y, hy₁, hv₂, hy₂, hy₃, hv₃, hv₄, hv₅, hy₄, hy₅⟩ := h,
  have hI₁ : Icc y z ⊆ I := I.Icc_subset hy₁ hz₁,
  have : z < f y := hy₄ _ (left_mem_Icc.2 hv₃.le),
  have hf₁ : ∀ n, continuous_on (f^[n]) I := λ _, hf.iterate hf' _,
  have hy₆ : ∀ m, odd m → (f^[m] y) = f y,
  { simp only [odd, forall_exists_index, forall_eq_apply_imp_iff', iterate_succ_apply'],
    intro a,
    rw (hy₂.is_periodic_pt.mul_const a).eq },
  have hy₇ : ∀ x ∈ Icc y v, f^[2] x ≤ x,
  { intros x hx,
    rcases eq_or_ne y x with rfl | hy,
    { rw hy₂.is_periodic_pt.eq },
    exact (hy₅ x ⟨lt_of_le_of_ne hx.1 hy, hx.2⟩).le },
  let X := {x ∈ Icc y v | f^[P.card+2] x = x},
  have hX₁ : X.nonempty,
  { obtain ⟨c, hc, hc'⟩ := exists_fixed_point_Icc hv₃.le
      ((hf₁ _).mono (I.Icc_subset hy₁ hv₁)) (or.inl ⟨_, _⟩),
    { exact ⟨c, hc, hc'⟩ },
    { rw hy₆,
      { linarith },
      simpa with parity_simps using hP₃ },
    rw [iterate_add_apply, hv₂, (hP.iterate_card_apply (P.min'_mem _)).eq],
    exact hy₃.trans hv₃.le },
  have hX₂ : bdd_below X := bdd_below.mono (set.sep_subset _ _) bdd_below_Icc,
  have hX₃ : is_closed X := is_closed_sep_eq is_closed_Icc
    ((hf₁ _).mono (I.Icc_subset hy₁ hv₁)) continuous_on_id,
  let p := Inf X,
  let k := minimal_period f p,
  obtain ⟨⟨hp₁ : _ ≤ p, hp₂ : p ≤ _⟩, hp₃ : (f^[P.card+2] p) = p⟩ := hX₃.cInf_mem hX₁ hX₂,
  have hk₁ : 0 < k := is_periodic_pt.minimal_period_pos (by simp) hp₃,
  have hp₄ : f p ≠ p := ((hp₂.trans hv₄).trans_lt (hy₄ p ⟨hp₁, hp₂⟩)).ne',
  have hk₂ : 2 ≤ k,
  { change 1 < k,
    exact lt_of_not_le (λ i, hp₄ (i.antisymm hk₁).is_periodic_pt) },
  have hk₃ : k ∣ P.card + 2 := is_periodic_pt.minimal_period_dvd hp₃,
  have hk₄ : odd k := odd_of_dvd_odd (by simpa with parity_simps using hP₃) hk₃,
  suffices : ¬ (k < P.card + 2),
  { refine ⟨p, _, eq_of_le_of_not_lt (nat.le_of_dvd (by simp) hk₃) this⟩,
    exact I.Icc_subset hy₁ hv₁ ⟨hp₁, hp₂⟩ },
  intro hk₅,
  have hyp : y < p,
  { refine lt_of_le_of_ne ‹_› _,
    intro hyp,
    suffices : odd 2, by simpa,
    rwa [←hy₂, hyp] },
  have ih : ∀ i, ∃ w ∈ Ico y p, f^[k + 2*(i+1)] w = w,
  { refine nat.rec _ _,
    { have : continuous_on (f^[k+2*(0+1)]) (Icc y p) :=
        (hf₁ _).mono ((Icc_subset_Icc_right (hp₂.trans hv₄)).trans hI₁),
      have h' : (f^[k+2] p) < p,
      { rw [add_comm, iterate_add_apply, iterate_minimal_period],
        exact hy₅ _ ⟨hyp, hp₂⟩ },
      have h'' : y ≤ (f^[k+2] y),
      { rw [hy₆], { linarith },
        simpa with parity_simps using hk₄ },
      obtain ⟨w, hw, hw'⟩ := exists_fixed_point_Icc hp₁ this
        (or.inl ⟨h'', h'.le⟩),
      refine ⟨w, ⟨hw.1, lt_of_le_of_ne hw.2 _⟩, hw'⟩,
      intro hwp,
      refine h'.ne' _,
      rw [←hwp],
      exact hw'.symm },
    rintro n ⟨w, ⟨hw₁, hw₂⟩, hw₃⟩,
    have : continuous_on (f^[k+2*(n+2)]) (Icc y w) :=
      (hf₁ _).mono ((Icc_subset_Icc_right (by linarith)).trans hI₁),
    have h' : (f^[k+2*(n+2)] w) ≤ w,
    { have : k+2*(n+2) = 2+(k+2*(n+1)), ring,
      rw [this, iterate_add_apply, hw₃],
      exact hy₇ _ ⟨hw₁, hw₂.le.trans hp₂⟩ },
    have h'' : y ≤ (f^[k+2*(n+2)] y),
    { rw [hy₆], { linarith },
      simpa with parity_simps using hk₄ },
    obtain ⟨c, hc, hc'⟩ := exists_fixed_point_Icc hw₁ this
      (or.inl ⟨h'', h'⟩),
    exact ⟨c, ⟨hc.1, hc.2.trans_lt hw₂⟩, hc'⟩ },
  have : even (P.card + 2 - k),
  { rw even_sub' hk₅.le,
    simpa [hk₄] with parity_simps using hP₃ },
  have : ∃ i, k + 2 * (i + 1) = P.card + 2,
  { refine ⟨(P.card + 2 - k) / 2 - 1, _⟩,
    rw even_iff_two_dvd at this,
    rw [nat.sub_add_cancel, nat.mul_div_cancel' this, nat.add_sub_of_le hk₅.le],
    rw [nat.le_div_iff_mul_le zero_lt_two],
    exact le_of_dvd (nat.sub_pos_of_lt hk₅) this },
  obtain ⟨i, hi⟩ := this,
  obtain ⟨p', ⟨hp'₁, hp'₂⟩, hp'₃⟩ := ih i,
  have : p' ∈ X := ⟨⟨hp'₁, hp'₂.le.trans hp₂⟩, by rwa ←hi⟩,
  exact hp'₂.not_le (cInf_le hX₂ this),
end

lemma part_c_aux (hP : P.is_cycle f) (hP₂ : 3 ≤ P.card) (hP₃ : odd P.card) (hPI : ↑P ⊆ I)
  (hf : continuous_on f I) (hf' : maps_to f I I) [ord_connected I] :
  ∃ d v z₀ z,
    d ∈ I ∧ v ∈ I ∧ z₀ ∈ I ∧ z ∈ I ∧
      d < v ∧ v < z₀ ∧ z₀ ≤ z ∧
        (f^[2] d) = z₀ ∧ is_periodic_pt f 2 z₀ ∧ is_fixed_pt f z ∧
          (f^[2] v) ≤ d ∧
            (∀ x ∈ Ioo d z₀, f^[2] x < z₀) ∧ (∀ x ∈ Ioo d z₀, z < f x) :=
begin
  obtain ⟨hPne, z, hz₁, -, hz₃, hz₄, h⟩ := part_a_first_aux hP
    ((nat.le_succ _).trans hP₂) hPI hf hf',
  specialize h hP₂,
  obtain ⟨v, hv₁, y, hy₁, hv₂, hy₂, hy₃, hv₃, hv₄, hv₅, hy₄, hy₅⟩ := h,
  have hI₁ : Icc (P.min' hPne) z ⊆ I := I.Icc_subset (hPI (P.min'_mem _)) hz₁,
  have hI₂ : Icc y z ⊆ I := (Icc_subset_Icc_left hy₃).trans hI₁,
  have : z < f y := hy₄ _ (left_mem_Icc.2 hv₃.le),
  have hf₁ : ∀ n, continuous_on (f^[n]) I := λ _, hf.iterate hf' _,
  have hv₆ : (f^[2] v) < v, { rw hv₂, exact hy₃.trans_lt hv₃ },
  let Z := {x ∈ Icc v z | f^[2] x = x},
  have hZ₁ : Z.nonempty,
  { obtain ⟨c, hc, hc'⟩ := exists_fixed_point_Icc hv₄
      ((hf₁ _).mono ((Icc_subset_Icc_left hv₃.le).trans hI₂)) (or.inr ⟨hv₆.le, (hz₃.iterate 2).ge⟩),
    exact ⟨c, hc, hc'⟩ },
  have hZ₂ : bdd_below Z := bdd_below.mono (set.sep_subset _ _) bdd_below_Icc,
  have hZ₃ : is_closed Z := is_closed_sep_eq is_closed_Icc
    ((hf₁ _).mono ((Icc_subset_Icc_left hv₃.le).trans hI₂)) continuous_on_id,
  let z₀ := Inf Z,
  obtain ⟨⟨hz₀₁ : _ ≤ z₀, hz₀₂ : z₀ ≤ _⟩, hz₀₃ : (f^[2] z₀) = z₀⟩ := hZ₃.cInf_mem hZ₁ hZ₂,
  replace hz₀₁ : v < z₀ := lt_of_le_of_ne hz₀₁ (λ i, hv₆.ne (by rwa i)),
  have hz₀₄ : ∀ x ∈ Ico v z₀, f^[2] x < x,
  { rintro x ⟨hx₁, hx₂⟩,
    by_contra' hx₃,
    obtain ⟨c, ⟨hc₁, hc₂⟩, hc₃⟩ := exists_fixed_point_Icc hx₁
      ((hf₁ 2).mono ((Icc_subset_Icc hv₃.le (hx₂.le.trans hz₀₂)).trans hI₂)) (or.inr ⟨hv₆.le, hx₃⟩),
    have : z₀ ≤ c := cInf_le hZ₂ ⟨⟨hc₁, by linarith⟩, hc₃⟩,
    exact hx₂.not_le (this.trans hc₂) },
  replace hz₀₄ : ∀ x ∈ Ioo y z₀, f^[2] x < x,
  { rw ←Ioc_union_Ico_eq_Ioo hv₃ hz₀₁,
    simp only [mem_union_eq, or_imp_distrib, forall_and_distrib],
    exact ⟨hy₅, hz₀₄⟩ },
  have hz₀₅ : ∀ x ∈ Ico v z₀, z < f x,
  { rintro x ⟨hx₁, hx₂⟩,
    by_contra' hx₃,
    obtain ⟨c, ⟨hc₁, hc₂⟩, hc₃⟩ := intermediate_value_Icc' hx₁
      (hf.mono ((Icc_subset_Icc hv₃.le (by linarith)).trans hI₂)) ⟨hx₃, hv₅⟩,
    have := hz₀₄ c ⟨hv₃.trans_le hc₁, hc₂.trans_lt hx₂⟩,
    rw [iterate_succ_apply, iterate_one, hc₃, hz₃.eq] at this,
    linarith },
  have hz₀₆ : ¬ ∀ x ∈ Ico (P.min' hPne) z₀, f^[2] x < z₀,
  { intro h,
    have : ∀ i, f^[2*i] (P.min' hPne) ∈ Ico (P.min' hPne) z₀,
    { refine nat.rec _ _,
      { exact ⟨by refl, by { simp only [mul_zero, iterate_zero_apply], linarith }⟩ },
      intros n hn,
      refine ⟨P.min'_le _ (hP.iterate_apply_mem_of_mem _ (P.min'_mem hPne)), _⟩,
      rw [mul_succ, add_comm, iterate_add_apply],
      exact h _ hn },
    refine (this ((P.card - 1) / 2)).2.not_le _,
    rw nat.mul_div_cancel',
    { exact hz₀₂.trans hz₄ },
    rw [←even_iff_two_dvd, even_sub'],
    { simpa using hP₃ },
    linarith },
  have hz₀₇ : ∃ x ∈ Icc (P.min' hPne) y, z₀ ≤ (f^[2] x),
  { push_neg at hz₀₆,
    obtain ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := hz₀₆,
    refine ⟨x, ⟨hx₁, _⟩, hx₃⟩,
    by_contra' hx₄,
    linarith [hz₀₄ x ⟨hx₄, hx₂⟩] },
  let D := {x ∈ Icc (P.min' hPne) y | f^[2] x = z₀},
  have hD₁ : D.nonempty,
  { obtain ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := hz₀₇,
    obtain ⟨c, ⟨hc₁, hc₂⟩, hc₃⟩ := intermediate_value_Icc' hx₂
      ((hf₁ 2).mono ((Icc_subset_Icc hx₁ (by linarith)).trans hI₁)) ⟨_, hx₃⟩,
    { exact ⟨c, ⟨by linarith, hc₂⟩, hc₃⟩ },
    rw hy₂.is_periodic_pt.eq,
    linarith },
  have hD₂ : bdd_above D := bdd_above.mono (set.sep_subset _ _) bdd_above_Icc,
  have hD₃ : is_closed D := is_closed_sep_eq is_closed_Icc
    ((hf₁ _).mono ((Icc_subset_Icc_right (by linarith)).trans hI₁)) continuous_on_const,
  let d := Sup D,
  obtain ⟨⟨hd₁ : _ ≤ d, hd₂ : d ≤ _⟩, hd₃ : (f^[2] d) = z₀⟩ := hD₃.cSup_mem hD₁ hD₂,
  have hd₄ : ∀ x ∈ Ioo d y, f^[2] x < z₀,
  { rintro x ⟨hx₁, hx₂⟩,
    by_contra',
    obtain ⟨c, ⟨hc₁, hc₂⟩, hc₃⟩ := intermediate_value_Icc' hx₂.le
      ((hf₁ 2).mono ((Icc_subset_Icc (hd₁.trans hx₁.le) (by linarith)).trans hI₁)) ⟨_, this⟩,
    { have : c ≤ d := le_cSup hD₂ ⟨⟨by linarith, hc₂⟩, hc₃⟩,
      linarith },
    rw hy₂.is_periodic_pt.eq,
    exact (hv₃.trans hz₀₁).le },
  replace hd₄ : ∀ x ∈ Ioo d z₀, f^[2] x < z₀,
  { rintro x ⟨hx₁, hx₂⟩,
    rcases lt_trichotomy x y with hx₃ | rfl | hx₃,
    { exact hd₄ _ ⟨hx₁, hx₃⟩ },
    { rwa hy₂.is_periodic_pt.eq },
    { exact (hz₀₄ x ⟨hx₃, hx₂⟩).trans hx₂ } },
  have hd₅ : ∀ x ∈ Ioo d v, z < f x,
  { rintro x ⟨hx₁, hx₂⟩,
    by_contra' hx₃,
    obtain ⟨c, hc, hc'⟩ := intermediate_value_Icc hx₂.le
      (hf.mono ((Icc_subset_Icc (hd₁.trans hx₁.le) (by linarith)).trans hI₁)) ⟨hx₃, hv₅⟩,
    have := hd₄ c ⟨hx₁.trans_le hc.1, hc.2.trans_lt hz₀₁⟩,
    rw [iterate_succ_apply, iterate_one, hc', hz₃.eq] at this,
    exact hz₀₂.not_lt this },
  replace hd₅ : ∀ x ∈ Ioo d z₀, z < f x,
  { rw ←Ioo_union_Ico_eq_Ioo (hd₂.trans_lt hv₃) hz₀₁.le,
    simp only [mem_union_eq, or_imp_distrib, forall_and_distrib],
    exact ⟨hd₅, hz₀₅⟩ },
  refine ⟨d, v, z₀, z, hI₁ ⟨hd₁, _⟩, hI₁ ⟨_, _⟩, hI₁ ⟨_, _⟩, hI₁ ⟨_, _⟩, _, hz₀₁, hz₀₂, hd₃, hz₀₃,
    hz₃, by rwa hv₂, hd₄, hd₅⟩;
  linarith
end

lemma part_c (hP : P.is_cycle f) (hP₂ : 3 ≤ P.card) (hP₃ : odd P.card) (hPI : ↑P ⊆ I)
  (hf : continuous_on f I) (hf' : maps_to f I I) [ord_connected I] :
  ∀ i : ℕ, ∃ c ∈ I, minimal_period f c = 2 * (i+1) :=
begin
  obtain ⟨d, v, z₀, z, hI₀, hI₁, hI₂, hI₃, hd₁, hv₁, hz₁, hd₂, hz₂, hz₃, hv₂, hd₃, hd₄⟩ :=
    part_c_aux hP hP₂ hP₃ hPI hf hf',
  have hd₅ : ∀ i, (f^[2*(i+1)] d) = z₀,
  { intros i,
    rw [mul_add_one, iterate_add_apply, hd₂, (hz₂.mul_const i).eq] },
  replace hd₅ : ∀ i, i ≠ 0 → even i → (f^[i] d) = z₀,
  { rintro i hj ⟨j, rfl⟩,
    rw [←hd₅ (j - 1), nat.sub_add_cancel, two_mul],
    rw [nat.succ_le_iff, pos_iff_ne_zero],
    simpa using hj },
  have hI₄ : Icc d z ⊆ I := I.Icc_subset ‹_› ‹_›,
  have hf₁ : ∀ n, continuous_on (f^[n]) I := λ _, hf.iterate hf' _,
  have hd' : d ≤ (f^[2] d), { rw hd₂, exact (hd₁.trans hv₁).le },
  suffices : ∀ i, ∃ u c, d < c ∧ c < u ∧ u ≤ v ∧ (f^[2*(i+1)] c = c) ∧ (f^[2*(i+1)] u = d) ∧
    (∀ x ∈ Ico d u, f^[2*(i+1)] x ≠ d) ∧ ∀ k, k ≠ 0 → k ≤ (i+1) →
    (∀ x ∈ Ioo d u, (f^[2*k] x) ∈ Ioo d z₀) ∧ ∃ u' ∈ Ioc c v, f^[2*k] u' = d,
  { intro n,
    specialize this n,
    obtain ⟨u, c, hdc, hcu, huv, hc, hu, hu', ih⟩ := this,
    refine ⟨c, I.Icc_subset hI₀ hI₁ ⟨hdc.le, hcu.le.trans huv⟩, _⟩,
    have t₁ : 0 < minimal_period f c := is_periodic_pt.minimal_period_pos (by simp) hc,
    refine eq_of_le_of_not_lt (is_periodic_pt.minimal_period_le (by simp) hc) (λ t₂, _),
    obtain ⟨k, hk⟩ := nat.even_or_odd' (minimal_period f c),
    rcases hk.symm with (hk | hk),
    { rcases eq_or_ne k 0 with rfl | hk',
      { have : f c = c := hk.is_periodic_pt.eq,
        linarith [hd₄ c ⟨hdc, by linarith⟩] },
      have := hd₄ _ ((ih _ hk' (by linarith only [t₂, hk])).1 c ⟨hdc, hcu⟩ ),
      rw [←iterate_succ_apply' f, succ_eq_add_one, ←hk, iterate_minimal_period] at this,
      linarith },
    have hk' : k ≠ 0, by linarith,
    have : k < n + 1,
    { have : 2 * k < 2 * (n + 1), by rwa ←hk,
      refine lt_of_mul_lt_mul_left' this },
    obtain ⟨u', hu'₁, hu'₂⟩ := (ih (n + 1 - k) (nat.sub_pos_of_lt ‹_›).ne' (nat.sub_le _ _)).2,
    have : u' ∈ Icc (f^[2 * k] c) (f^[2 * k] d),
    { rw [hd₅ (2 * k) (by simp [hk']) (by simp), hk.is_periodic_pt.eq],
      exact ⟨hu'₁.1.le, hu'₁.2.trans hv₁.le⟩ },
    obtain ⟨w, hw, hw'⟩ := intermediate_value_Icc' hdc.le
      ((hf₁ (2*k)).mono ((Icc_subset_Icc_right (by linarith)).trans hI₄)) this,
    refine hu' w ⟨hw.1, hw.2.trans_lt hcu⟩ _,
    rw [←hu'₂, ←hw', ←iterate_add_apply, ←mul_add, nat.sub_add_cancel ‹k < n + 1›.le] },
  refine nat.rec _ _,
  { let U := {x ∈ Icc d v | f^[2] x = d},
    have hU₁ : U.nonempty,
    { obtain ⟨c, hc, hc'⟩ := intermediate_value_Icc' ‹d < v›.le
        ((hf₁ 2).mono ((Icc_subset_Icc_right (by linarith)).trans hI₄)) ⟨hv₂, hd'⟩,
      exact ⟨c, hc, hc'⟩ },
    have hU₂ : bdd_below U := bdd_below.mono (set.sep_subset _ _) bdd_below_Icc,
    have hU₃ : is_closed U := is_closed_sep_eq is_closed_Icc
      ((hf₁ _).mono ((Icc_subset_Icc_right (hv₁.le.trans hz₁)).trans hI₄)) continuous_on_const,
    let u := Inf U,
    obtain ⟨⟨hu₁ : _ ≤ u, hu₂ : u ≤ _⟩, hu₃ : (f^[2] u) = d⟩ := hU₃.cInf_mem hU₁ hU₂,
    obtain ⟨c, ⟨hdc, hcu⟩, hc⟩ := exists_fixed_point_Icc hu₁
      ((hf₁ 2).mono ((Icc_subset_Icc_right (by linarith)).trans hI₄))
      (or.inl ⟨hd', by linarith⟩),
    replace hdc : d < c,
    { refine lt_of_le_of_ne hdc _,
      rintro rfl,
      linarith only [hc.eq, hd₂, hd₁, hv₁] },
    replace hcu : c < u,
    { refine lt_of_le_of_ne' hcu _,
      rintro rfl,
      linarith only [hdc, hc.eq, hu₃] },
    have hu₄ : ∀ x ∈ Ico d u, f^[2 * (0 + 1)] x ≠ d,
    { rintro x ⟨hx₁, hx₂⟩ i,
      exact hx₂.not_le (cInf_le hU₂ ⟨⟨hx₁, hx₂.le.trans hu₂⟩, i⟩) },
    refine ⟨u, c, hdc, hcu, hu₂, hc, hu₃, hu₄, _⟩,
    intros k hk₁ hk₂,
    have : k = 1 := hk₂.antisymm (hk₁.bot_lt),
    subst k,
    refine ⟨_, u, ⟨hcu, hu₂⟩, hu₃⟩,
    rintro x ⟨hx₁, hx₂⟩,
    refine ⟨_, hd₃ _ ⟨hx₁, by linarith⟩⟩,
    by_contra' hx₃,
    obtain ⟨w, ⟨hw₁, hw₂⟩, hw₃⟩ := intermediate_value_Icc' hx₁.le
      ((hf₁ 2).mono ((Icc_subset_Icc_right (by linarith)).trans hI₄)) ⟨hx₃, hd'⟩,
    exact hu₄ w ⟨hw₁, by linarith⟩ hw₃ },
  rintro n ⟨u, c, hdc, hcu, huv, hc, hu, hu', ih⟩,
  obtain ⟨u₁, ⟨h₁u₁, h₂u₁⟩, h₃u₁⟩ := (ih 1 (by simp) (by simp)).2,
  let U := {x ∈ Icc d c | f^[2 * (n + 2)] x = d},
  have hU₁ : U.nonempty,
  { have : u₁ ∈ Icc (f^[2 * (n + 1)] c) (f^[2 * (n + 1)] d),
    { rw [hc, hd₅ (2 * (n + 1)) (by simp) (by simp)],
      exact ⟨h₁u₁.le, h₂u₁.trans hv₁.le⟩ },
    obtain ⟨u₂, hu₂, h₃u₂⟩ := intermediate_value_Icc' hdc.le
      ((hf₁ (2*(n+1))).mono ((Icc_subset_Icc_right (by linarith)).trans hI₄)) this,
    refine ⟨u₂, hu₂, _⟩,
    simp only [←h₃u₁, ←h₃u₂, ←iterate_add_apply],
    ring_nf },
  have hU₂ : bdd_below U := bdd_below.mono (set.sep_subset _ _) bdd_below_Icc,
  have hU₃ : is_closed U := is_closed_sep_eq is_closed_Icc
    ((hf₁ _).mono ((Icc_subset_Icc_right (by linarith)).trans hI₄)) continuous_on_const,
  let u' := Inf U,
  obtain ⟨⟨hu'₁ : _ ≤ u', hu'₂ : u' ≤ _⟩, hu'₃ : (f^[_] u') = d⟩ := hU₃.cInf_mem hU₁ hU₂,
  have : d ≤ (f^[2 * (n + 2)] d) ∧ (f^[2 * (n + 2)] u') ≤ u',
  { rw [hu'₃, hd₅ (2 * (n + 2)) (by simp) (by simp)],
    split; linarith },
  obtain ⟨c', ⟨hdc', hc'u'⟩, hc'⟩ := exists_fixed_point_Icc hu'₁
    ((hf₁ (2*(n+2))).mono ((Icc_subset_Icc_right (by linarith)).trans hI₄)) (or.inl this),
  replace hdc' : d < c',
  { refine lt_of_le_of_ne hdc' _,
    rintro rfl,
    linarith only [hc'.eq, hd₅ (2 * (n + 2)) (by simp) (by simp), hd₁, hv₁] },
  replace hc'u' : c' < u',
  { refine lt_of_le_of_ne' hc'u' _,
    rintro rfl,
    linarith only [hdc', hc'.eq, hu'₃] },
  have hu'₄ : ∀ x ∈ Ico d u', f^[2 * (n + 2)] x ≠ d,
  { rintro x ⟨hx₁, hx₂⟩ i,
    exact hx₂.not_le (cInf_le hU₂ ⟨⟨hx₁, hx₂.le.trans hu'₂⟩, i⟩) },
  refine ⟨u', c', hdc', hc'u', by linarith, hc', hu'₃, hu'₄, _⟩,
  intros k hk₁ hk₂,
  have hk₃ : k ≤ n + 1 ∨ k = n + 2,
  { cases hk₂.lt_or_eq,
    { rw nat.lt_succ_iff at h,
      exact or.inl h },
    exact or.inr h },
  rcases hk₃ with hk₃ | rfl,
  { obtain ⟨hk₄, u'', ⟨hu'', h'u''⟩, h''u''⟩ := ih k hk₁ hk₃,
    refine ⟨λ x hx, hk₄ x ⟨hx.1, by linarith only [hx.2, hu'₂, hcu]⟩, u'', ⟨_, h'u''⟩, h''u''⟩,
    linarith },
  refine ⟨_, u', ⟨hc'u', by linarith⟩, hu'₃⟩,
  rintro x ⟨hx₁, hx₂⟩,
  have : (f^[2 * (n + 2)] x) < z₀,
  { rw [nat.mul_succ, add_comm, iterate_add_apply],
    exact hd₃ _ ((ih _ (by simp) le_rfl).1 _ ⟨hx₁, by linarith⟩), },
  refine ⟨lt_of_not_le (λ hx₃, _), this⟩,
  have hd₀ : d ≤ (f^[2 * (n + 2)] d),
  { linarith [hd₅ (2 * (n + 2)) (by simp) (by simp)] },
  obtain ⟨w, ⟨hw₁, hw₂⟩, hw₃⟩ := intermediate_value_Icc' hx₁.le
    ((hf₁ (2*(n+2))).mono ((Icc_subset_Icc_right (by linarith)).trans hI₄)) ⟨hx₃, hd₀⟩,
  exact hu'₄ w ⟨hw₁, hw₂.trans_lt hx₂⟩ hw₃,
end.

lemma three_two {x : ℝ} {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) (h : minimal_period (f^[n]) x = k) :
  ∃ s : ℕ, minimal_period f x = k * n / s ∧ s ∣ n ∧ coprime s k :=
begin
  have : is_periodic_pt f (k * n) x,
  { have := h.is_periodic_pt,
    rwa [is_periodic_pt, ←iterate_mul, mul_comm] at this },
  obtain ⟨s, hs⟩ := this.minimal_period_dvd,
  have hs' : s ≠ 0, { rintro rfl, simpa [hn, hk] using hs },
  have hs'' : minimal_period f x = k * n / s,
  { rw [hs, nat.mul_div_cancel],
    rwa pos_iff_ne_zero },
  refine ⟨s, hs'', _⟩,
  have : minimal_period (f^[n]) x = _ := minimal_period_iterate_eq_div_gcd hn,
  rw [h, hs''] at this,
  refine weird_division_thing hn hk hs' _ this.symm,
  rw hs,
  apply dvd_mul_left,
end

lemma eq_one_of_dvd_two_pow_of_coprime_two {s k : ℕ} (hs : s ∣ 2 ^ k) (hs' : s.coprime 2) : s = 1 :=
begin
  obtain ⟨(_ | _), ht, rfl⟩ := (nat.dvd_prime_pow prime_two).1 hs,
  { refl },
  rw coprime_pow_left_iff succ_pos' at hs',
  simpa using hs'
end

variables [ord_connected I] (hf : continuous_on f I) (hf' : maps_to f I I)
include hf hf'

lemma one_of_two_le {m : ℕ} {c : ℝ} (hm : 2 ≤ m) (hc : c ∈ I) (hc' : minimal_period f c = m) :
  ∃ d ∈ I, minimal_period f d = 1 :=
begin
  obtain ⟨P, hP₁, hP₂, rfl, hP₄⟩ := exists_cycle_of_minimal_period hf' hc (by linarith) hc',
  obtain ⟨d, hd, hd'⟩ := part_a_one hP₁ hm hP₄ hf hf',
  exact ⟨d, hd, by rwa is_fixed_point_iff_minimal_period_eq_one⟩,
end

lemma two_of_three_le {m : ℕ} {c : ℝ} (hm : 3 ≤ m) (hc : c ∈ I) (hc' : minimal_period f c = m) :
  ∃ d ∈ I, minimal_period f d = 2 :=
begin
  obtain ⟨P, hP₁, hP₂, rfl, hP₄⟩ := exists_cycle_of_minimal_period hf' hc (by linarith) hc',
  exact part_a_two hP₁ hm hP₄ hf hf',
end

lemma add_two_of_three_le_of_odd {m : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m) (hc : c ∈ I)
  (hc' : minimal_period f c = m) :
  ∃ d ∈ I, minimal_period f d = m + 2 :=
begin
  obtain ⟨P, hP₁, hP₂, rfl, hP₄⟩ := exists_cycle_of_minimal_period hf' hc (by linarith) hc',
  exact part_b hP₁ hm hm' hP₄ hf hf',
end

lemma odd_of_ge_of_ge_three {m : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m) (hc : c ∈ I)
  (hc' : minimal_period f c = m) {n : ℕ} (hn : odd n) (hn' : m ≤ n) :
  ∃ d ∈ I, minimal_period f d = n :=
begin
  have : ∀ i, ∃ d ∈ I, minimal_period f d = m + 2 * i,
  { refine nat.rec _ _,
    { exact ⟨_, hc, hc'⟩ },
    rintro n ⟨d, hd, hd'⟩,
    refine add_two_of_three_le_of_odd hf hf' (le_add_right hm) _ hd hd',
    exact hm'.add_even (even_two_mul _) },
  obtain ⟨d, hd, hd'⟩ := this ((n - m) / 2),
  refine ⟨d, hd, _⟩,
  rw [hd', nat.mul_div_cancel', add_tsub_cancel_of_le hn'],
  rw [←even_iff_two_dvd],
  exact nat.odd.sub_odd hn hm',
end

lemma even_of_odd {m : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m) (hc : c ∈ I)
  (hc' : minimal_period f c = m) {n : ℕ} (hn : even n) (hn' : n ≠ 0) :
  ∃ d ∈ I, minimal_period f d = n :=
begin
  rw even_iff_two_dvd at hn,
  obtain ⟨n, rfl⟩ := hn,
  simp only [ne.def, nat.mul_eq_zero, bit0_eq_zero, nat.one_ne_zero, false_or] at hn',
  obtain ⟨P, hP₁, hP₂, rfl, hP₄⟩ := exists_cycle_of_minimal_period hf' hc (by linarith) hc',
  obtain ⟨d, hd, hd'⟩ := part_c hP₁ hm hm' hP₄ hf hf' (n - 1),
  refine ⟨d, hd, _⟩,
  rw [hd', nat.sub_add_cancel],
  rwa [nat.succ_le_iff, pos_iff_ne_zero],
end

lemma six_of_three_le_of_odd {m : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m) (hc : c ∈ I)
  (hc' : minimal_period f c = m) : ∃ d ∈ I, minimal_period f d = 6 :=
even_of_odd hf hf' hm hm' hc hc' (by simp) (by simp)

lemma two_mul_of_three_le_of_odd {m : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m) (hc : c ∈ I)
  (hc' : minimal_period f c = m) : ∃ d ∈ I, minimal_period f d = 2 * m :=
even_of_odd hf hf' hm hm' hc hc' (by simp) (by linarith)


lemma two_mul_odd_of_two_mul_odd_ge {m : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m) (hc : c ∈ I)
  (hc' : minimal_period f c = 2 * m) {n : ℕ} (hn : odd n) (hn' : m ≤ n) :
  ∃ d ∈ I, minimal_period f d = 2 * n :=
begin
  have hf2 : minimal_period (f^[2]) c = _ := minimal_period_iterate_eq_div_gcd two_ne_zero,
  rw [hc', gcd_mul_right_left, nat.mul_div_cancel_left _ zero_lt_two] at hf2,
  obtain ⟨x, hx, hx'⟩ :=
    odd_of_ge_of_ge_three (hf.iterate hf' _) (hf'.iterate _) hm hm' hc hf2 hn hn',
  obtain ⟨s, hs, hs', hs''⟩ := three_two two_ne_zero hn.pos.ne' hx',
  rw nat.dvd_prime prime_two at hs',
  rcases hs' with (rfl | rfl),
  { exact ⟨x, hx, by rw [hs, nat.div_one, mul_comm]⟩ },
  rw nat.mul_div_cancel _ zero_lt_two at hs,
  exact two_mul_of_three_le_of_odd hf hf' (by linarith) hn hx hs
end

lemma two_mul_even_of_two_mul_odd {m : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m) (hc : c ∈ I)
  (hc' : minimal_period f c = 2 * m) {n : ℕ} (hn : even n) (hn' : n ≠ 0) :
    ∃ d ∈ I, minimal_period f d = 2 * n :=
begin
  have hf2 : minimal_period (f^[2]) c = _ := minimal_period_iterate_eq_div_gcd two_ne_zero,
  rw [hc', gcd_mul_right_left, nat.mul_div_cancel_left _ zero_lt_two] at hf2,
  obtain ⟨x, hx, hx'⟩ := even_of_odd (hf.iterate hf' _) (hf'.iterate _) hm hm' hc hf2 hn hn',
  obtain ⟨s, hs, hs', hs''⟩ := three_two two_ne_zero hn' hx',
  rw nat.dvd_prime prime_two at hs',
  have : s ≠ 2,
  { rintro rfl,
    rw [prime_two.coprime_iff_not_dvd, ←even_iff_two_dvd] at hs'',
    exact hs'' hn },
  cases hs'.resolve_right this,
  rw [mul_comm, nat.div_one] at hs,
  exact ⟨x, hx, hs⟩,
end

lemma two_pow_mul_odd_of_two_pow_mul_odd_ge {m k : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m)
  (hc : c ∈ I) (hc' : minimal_period f c = 2 ^ k * m) {n : ℕ} (hn : odd n) (hn' : m ≤ n) :
  ∃ d ∈ I, minimal_period f d = 2 ^ k * n :=
begin
  cases k,
  { rw [pow_zero, one_mul] at hc' ⊢,
    exact odd_of_ge_of_ge_three hf hf' hm hm' hc hc' hn hn' },
  have hf2 : minimal_period (f^[2^k]) c = _ :=
    minimal_period_iterate_eq_div_gcd (pow_ne_zero _ two_ne_zero),
  rw [hc', pow_succ', mul_assoc, gcd_mul_right_left,
    nat.mul_div_cancel_left _ (pow_pos two_pos _)] at hf2,
  obtain ⟨d, hd, hd'⟩ :=
    two_mul_odd_of_two_mul_odd_ge (hf.iterate hf' _) (hf'.iterate _) hm hm' hc hf2 hn hn',
  obtain ⟨s, hs, hs', hs''⟩ := three_two (pow_ne_zero _ two_ne_zero) (by linarith) hd',
  cases eq_one_of_dvd_two_pow_of_coprime_two hs' hs''.coprime_mul_right_right,
  refine ⟨d, hd, _⟩,
  rw [hs, nat.div_one, mul_right_comm, pow_succ],
end

lemma two_pow_mul_even_of_two_pow_mul_odd {m k : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m)
  (hc : c ∈ I) (hc' : minimal_period f c = 2 ^ k * m) {n : ℕ} (hn : even n) (hn' : n ≠ 0) :
  ∃ d ∈ I, minimal_period f d = 2 ^ k * n :=
begin
  cases k,
  { rw [pow_zero, one_mul] at hc' ⊢,
    exact even_of_odd hf hf' hm hm' hc hc' hn hn' },
  have hf2 : minimal_period (f^[2^k]) c = _ :=
    minimal_period_iterate_eq_div_gcd (pow_ne_zero _ two_ne_zero),
  rw [hc', pow_succ', mul_assoc, gcd_mul_right_left,
    nat.mul_div_cancel_left _ (pow_pos two_pos _)] at hf2,
  obtain ⟨d, hd, hd'⟩ :=
    two_mul_even_of_two_mul_odd (hf.iterate hf' _) (hf'.iterate _) hm hm' hc hf2 hn hn',
  obtain ⟨s, hs, hs', hs''⟩ := three_two (pow_ne_zero _ two_ne_zero) (by simpa using hn') hd',
  cases eq_one_of_dvd_two_pow_of_coprime_two hs' hs''.coprime_mul_right_right,
  refine ⟨d, hd, _⟩,
  rw [hs, nat.div_one, mul_right_comm, pow_succ],
end

lemma two_pow_of_two_pow_succ {k : ℕ} {c : ℝ} (hc : c ∈ I)
  (hc' : minimal_period f c = 2 ^ (k + 1)) :
  ∃ d ∈ I, minimal_period f d = 2 ^ k :=
begin
  cases k,
  { exact one_of_two_le hf hf' le_rfl hc hc' },
  have hf2 : minimal_period (f^[2^k]) c = _ :=
    minimal_period_iterate_eq_div_gcd (pow_ne_zero _ two_ne_zero),
  rw [hc', pow_add _ _ 2, gcd_mul_right_left, nat.mul_div_cancel_left _ (pow_pos two_pos _),
    sq] at hf2,
  obtain ⟨d, hd, hd'⟩ := two_of_three_le (hf.iterate hf' _) (hf'.iterate _) (nat.le_succ _) hc hf2,
  obtain ⟨s, hs, hs', hs''⟩ := three_two (pow_ne_zero _ two_ne_zero) two_ne_zero hd',
  cases eq_one_of_dvd_two_pow_of_coprime_two hs' hs'',
  refine ⟨d, hd, _⟩,
  rw [hs, nat.div_one, pow_succ]
end

lemma two_pow_of_two_pow {k l : ℕ} {c : ℝ} (hc : c ∈ I) (hc' : minimal_period f c = 2 ^ l)
  (hlk : k ≤ l) : ∃ d ∈ I, minimal_period f d = 2 ^ k :=
begin
  refine nat.decreasing_induction _ hlk ⟨_, hc, hc'⟩,
  rintro n ⟨d, hd, hd'⟩,
  exact two_pow_of_two_pow_succ hf hf' hd hd',
end

lemma two_pow_of_two_pow_mul_odd_aux {m i : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m)
  (hc : c ∈ I) (hc' : minimal_period f c = 2 ^ i * m) {l : ℕ} (hl : i ≤ l) :
  ∃ d ∈ I, minimal_period f d = 2 ^ (l + 1) :=
begin
  have hf2 : minimal_period (f^[2^i]) c = _ :=
    minimal_period_iterate_eq_div_gcd (pow_ne_zero _ two_ne_zero),
  rw [hc', gcd_mul_right_left, nat.mul_div_cancel_left _ (pow_pos two_pos _)] at hf2,
  have hf3 : minimal_period (f^[2^i]^[2^(l-i)]) c = _ :=
    minimal_period_iterate_eq_div_gcd (pow_ne_zero _ two_ne_zero),
  have : coprime m (2^(l-i)),
  { cases lt_or_eq_of_le hl,
    { rwa [nat.coprime_pow_right_iff (nat.sub_pos_of_lt h), coprime_comm,
        prime_two.coprime_iff_not_dvd, ←even_iff_two_dvd, ←odd_iff_not_even] },
    rw [h, nat.sub_self, pow_zero],
    exact coprime_one_right m },
  rw [hf2, this.gcd_eq_one, nat.div_one, ←iterate_mul, ←pow_add, nat.add_sub_of_le hl] at hf3,
  obtain ⟨d, hd, hd'⟩ := two_of_three_le (hf.iterate hf' _) (hf'.iterate _) hm hc hf3,
  obtain ⟨s, hs, hs', hs''⟩ := three_two (pow_ne_zero _ two_ne_zero) two_ne_zero hd',
  cases eq_one_of_dvd_two_pow_of_coprime_two hs' hs'',
  refine ⟨d, hd, _⟩,
  rw [hs, nat.div_one, pow_succ],
end

lemma two_pow_of_two_pow_mul_odd {m i : ℕ} {c : ℝ} (hm : 3 ≤ m) (hm' : odd m)
  (hc : c ∈ I) (hc' : minimal_period f c = 2 ^ i * m) {l : ℕ} :
  ∃ d ∈ I, minimal_period f d = 2 ^ l :=
begin
  cases le_or_lt i l,
  { obtain ⟨d, hd, hd'⟩ := two_pow_of_two_pow_mul_odd_aux hf hf' hm hm' hc hc' h,
    exact two_pow_of_two_pow_succ hf hf' hd hd' },
  { obtain ⟨d, hd, hd'⟩ := two_pow_of_two_pow_mul_odd_aux hf hf' hm hm' hc hc' le_rfl,
    exact two_pow_of_two_pow hf hf' hd hd' (by linarith) }
end

theorem sharkovsky_forcing {f : ℝ → ℝ} {I : set ℝ} [I.ord_connected]
  (hf : continuous_on f I) (hf' : maps_to f I I) {n m : ℕ} (h : n ≼ m) (hn : n ≠ 0)
  (hx : ∃ x ∈ I, minimal_period f x = n) : ∃ x ∈ I, minimal_period f x = m :=
begin
  obtain ⟨x, hx, hx'⟩ := hx,
  have hm : m ≠ 0 := sharkovsky.ne_zero_of_ge_ne_zero h hn,
  rw [sharkovsky.of_nat_iff, soa_iff] at h,
  set a := (to_pair n).1,
  set b := (to_pair n).2,
  set c := (to_pair m).1,
  set d := (to_pair m).2,
  have hab : 2 ^ a * b = _ := un_pair_to_pair n,
  have hb : odd b := odd_to_pair_snd_of_ne_zero hn,
  have hcd : 2 ^ c * d = _ := un_pair_to_pair m,
  have hd : odd d := odd_to_pair_snd_of_ne_zero hm,
  clear_value a b c d,
  substs hab hcd,
  simp only [ne.def, nat.mul_eq_zero, not_or_distrib, pow_ne_zero, ne.def, bit0_eq_zero,
    nat.one_ne_zero, not_false_iff, true_and] at hn hm,
  have : 2 ≤ b → 3 ≤ b,
  { intro i,
    exact (sharkovsky.eq_one_or_three_le_of_odd hb).resolve_left (by linarith) },
  rcases h with (_ | ⟨h, rfl, rfl⟩ | ⟨hb', rfl⟩ | ⟨rfl, hb', hd', hbd⟩ | ⟨hb', hd', hac⟩),
  { cases hn h },
  { rw mul_one at hx' ⊢,
    exact two_pow_of_two_pow hf hf' hx hx' h },
  { rw mul_one,
    exact two_pow_of_two_pow_mul_odd hf hf' (this hb') hb hx hx' },
  { exact two_pow_mul_odd_of_two_pow_mul_odd_ge hf hf' (this hb') hb hx hx' hd hbd },
  { have h₁ : 2 ^ a * (2 ^ (c - a) * d) = 2 ^ c * d,
    { rw [←mul_assoc, ←pow_add, add_tsub_cancel_of_le hac.le] },
    have h₂ : even (2 ^ (c - a) * d) :=
      (even_two.pow_of_ne_zero (nat.sub_pos_of_lt hac).ne').mul_right _,
    have h₃ : 2 ^ (c - a) * d ≠ 0,
    { simp [pow_ne_zero, hm] },
    obtain ⟨y, hy, hy'⟩ := two_pow_mul_even_of_two_pow_mul_odd hf hf' (this hb') hb hx hx' h₂ h₃,
    refine ⟨y, hy, _⟩,
    rwa ←h₁ },
end

end proof

lemma is_periodic_pt.minimal_period_eq {α : Type*} {f : α → α} {n : ℕ} {x : α} (hn : n ≠ 0)
  (hx : is_periodic_pt f n x) (hn' : ∀ i < n, i ≠ 0 → ¬ is_periodic_pt f i x) :
  minimal_period f x = n :=
begin
  refine eq_of_le_of_not_lt (hx.minimal_period_le hn.bot_lt) _,
  intro hk,
  exact hn' _ hk (hx.minimal_period_pos hn.bot_lt).ne' (is_periodic_pt_minimal_period _ _),
end

variables {a b h k x : ℝ}

noncomputable def tent_map (h x : ℝ) : ℝ := min h (1 - |2 * x - 1|)

lemma tent_map_continuous : continuous (tent_map h) := by continuity

lemma tent_map_eq_min_ite :
  tent_map h x = min h (if x ≤ 1 / 2 then 2 * x else 2 - 2 * x) :=
begin
  rw [tent_map],
  congr' 1,
  split_ifs,
  { rw [abs_of_nonpos]; linarith },
  { rw [abs_of_nonneg]; linarith },
end

lemma tent_map_one_eq : tent_map 1 x = 1 - |2 * x - 1| :=
by { rw [tent_map, min_eq_right_iff, sub_le_self_iff], exact abs_nonneg _ }

lemma tent_map_one_eq_ite :
  tent_map 1 x = if x ≤ 1 / 2 then 2 * x else 2 - 2 * x :=
begin
  rw [tent_map_one_eq],
  split_ifs,
  { rw [abs_of_nonpos]; linarith },
  { rw [abs_of_nonneg]; linarith },
end

lemma tent_map_one_of_le_half (hx : x ≤ 1 / 2) : tent_map 1 x = 2 * x :=
by rw [tent_map_one_eq, abs_of_nonpos]; linarith

lemma tent_map_one_of_half_le (hx : (1 : ℝ) / 2 ≤ x) : tent_map 1 x = 2 - 2 * x :=
by rw [tent_map_one_eq, abs_of_nonneg]; linarith

lemma tent_map_flip : tent_map h (1 - x) = tent_map h x :=
by { rw [tent_map, tent_map, abs_sub_comm, mul_one_sub, ←sub_add, add_comm], congr' 3, ring }

lemma tent_map_maps_to (h₀ : 0 ≤ h) : maps_to (tent_map h) (Icc 0 1) (Icc 0 h) :=
begin
  rintro x ⟨hx₀, hx₁⟩,
  rw tent_map_eq_min_ite,
  refine ⟨le_min h₀ _, min_le_left _ _⟩,
  split_ifs;
  linarith,
end

lemma tent_map_zero_eq (hx : x ∈ Icc (0 : ℝ) 1) : tent_map 0 x = 0 :=
by simpa using tent_map_maps_to le_rfl hx

lemma tent_map_maps_to' (h₀ : 0 ≤ h) (h₁ : h ≤ 1) :
  maps_to (tent_map h) (Icc 0 1) (Icc 0 1) :=
(tent_map_maps_to h₀).mono_right (Icc_subset_Icc_right h₁)

lemma tent_map_zero_periodic_pt {n : ℕ} (hn : n ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
  is_periodic_pt (tent_map 0) n x → x = 0 :=
begin
  cases n,
  { cases hn rfl },
  rw [is_periodic_pt, is_fixed_pt, iterate_succ_apply'],
  have : ((tent_map 0)^[n] x) ∈ Icc (0 : ℝ) 1 :=
    (tent_map_maps_to' le_rfl zero_le_one).iterate _ hx,
  rw [tent_map_zero_eq this],
  exact eq.symm,
end

lemma tent_map_right_zero (h₀ : 0 ≤ h) : tent_map h 0 = 0 :=
by norm_num [tent_map, h₀]

lemma minimal_period_zero_tent_map (h₀ : 0 ≤ h) : minimal_period (tent_map h) 0 = 1 :=
by { rw is_fixed_point_iff_minimal_period_eq_one, exact tent_map_right_zero h₀ }

lemma tent_map_right_one (h₀ : 0 ≤ h) : tent_map h 1 = 0 :=
by norm_num [tent_map, h₀]

lemma tent_map_lt_of_neg_right (h₀ : x < 0) : tent_map h x < x :=
begin
  rw [tent_map_eq_min_ite, if_pos],
  refine (min_le_right _ _).trans_lt (by linarith),
  linarith
end

lemma tent_map_lt_of_neg_left (h₀ : h < 0) : tent_map h x < x :=
begin
  cases le_or_lt 0 x with h₁ h₁,
  { exact (min_le_left _ _).trans_lt (h₀.trans_le h₁) },
  apply tent_map_lt_of_neg_right h₁,
end

lemma parameter_nonneg_of_cycle {O : finset ℝ} (hO : O.is_cycle (tent_map h)) (hO' : O.nonempty) :
  0 ≤ h :=
begin
  by_contra',
  refine (O.min'_le _ (hO _ (O.min'_mem hO')).1).not_lt _,
  apply tent_map_lt_of_neg_left this,
end

lemma tent_map_cycle_subset {O : finset ℝ} (hO : O.is_cycle (tent_map h)) : ↑O ⊆ Ico (0 : ℝ) 1 :=
begin
  rcases O.eq_empty_or_nonempty with rfl | hO',
  { simp },
  have h₀ := parameter_nonneg_of_cycle hO hO',
  have : (1 : ℝ) ∉ O,
  { intro h₁,
    have h₀' : (0 : ℝ) ∈ O,
    { rw ←tent_map_right_one h₀,
      exact (hO _ h₁).1 },
    have := (hO _ h₀').2,
    rw minimal_period_zero_tent_map h₀ at this,
    apply this.not_lt,
    rw [finset.one_lt_card_iff],
    exact ⟨_, _, h₀', h₁, by simp⟩ },
  suffices : ↑O ⊆ Ici (0 : ℝ),
  { intros x hx,
    have hx' : tent_map h ((tent_map h)^[O.card - 1] x) = x,
    { rw [←iterate_succ_apply' (tent_map h), succ_eq_add_one, nat.sub_add_cancel,
        (hO.iterate_card_apply hx).eq],
      rwa [nat.succ_le_iff, finset.card_pos] },
    refine ⟨this hx, lt_of_le_of_ne _ (ne_of_mem_of_not_mem hx ‹1 ∉ O›)⟩,
    rw [←hx', tent_map],
    apply (min_le_right _ _).trans _,
    simp [abs_nonneg] },
  by_contra',
  simp only [set.subset_def, finset.mem_coe, mem_Ici, not_forall, not_le, exists_prop] at this,
  obtain ⟨x, hx, hx'⟩ := this,
  have : O.min' hO' < 0 := (O.min'_le _ hx).trans_lt hx',
  exact (tent_map_lt_of_neg_right this).not_le (O.min'_le _ (hO _ (O.min'_mem _)).1),
end

lemma tent_map_cycle_subset' {O : finset ℝ} (hO : O.is_cycle (tent_map h)) : ↑O ⊆ Icc (0 : ℝ) h :=
begin
  intros x hx,
  have : (tent_map h^[O.card - 1] x) ∈ Icc (0 : ℝ) 1,
  { exact Ico_subset_Icc_self (tent_map_cycle_subset hO (hO.iterate_apply_mem_of_mem _ hx)), },
  have One : O.nonempty := ⟨_, hx⟩,
  convert tent_map_maps_to (parameter_nonneg_of_cycle hO One) this,
  have : 1 ≤ O.card, { rwa [nat.succ_le_iff, finset.card_pos] },
  rwa [←iterate_succ_apply' (tent_map h), succ_eq_add_one, nat.sub_add_cancel this,
    (hO.iterate_card_apply _).eq],
end

lemma minimal_period.mem_Icc {m : ℕ} (hm : m ≠ 0) {x : ℝ} (hx : minimal_period (tent_map h) x = m) :
  x ∈ Ico (0 : ℝ) 1 :=
begin
  obtain ⟨O, hO, hO', hO'', hO'''⟩ :=
    exists_cycle_of_minimal_period (maps_to_univ (tent_map h) set.univ) (mem_univ _) hm hx,
  exact tent_map_cycle_subset hO hO',
end

lemma tent_map_one_three : minimal_period (tent_map 1) (2 / 7) = 3 :=
begin
  refine is_periodic_pt.minimal_period_eq (by norm_num) _ _,
  { rw [is_periodic_pt, is_fixed_pt],
    norm_num [tent_map_one_eq_ite] },
  intros i hi hi',
  have : 1 ≤ i := hi'.bot_lt,
  rw [is_periodic_pt, is_fixed_pt],
  interval_cases i;
  norm_num [tent_map_one_eq_ite],
end

lemma tent_map_one_minimal_period {n : ℕ} (hn : n ≠ 0) :
  ∃ x ∈ Icc (0 : ℝ) 1, minimal_period (tent_map 1) x = n :=
sharkovsky_forcing tent_map_continuous.continuous_on (tent_map_maps_to' zero_le_one le_rfl)
  (sharkovsky.three_le_of_ne_zero hn) three_ne_zero ⟨2 / 7, by split; linarith, tent_map_one_three⟩

-- lemma tent_map_one_iterate' {n : ℕ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
--   (tent_map 1)^[n + 1] x = tent_map 1 (int.fract (x * 2 ^ n)) :=

lemma tent_map_one_flip (f : ℝ → ℝ) {x : ℝ}
  (hf : ∀ y ∈ Icc (0 : ℝ) 1, f (1 - y) = f y) (hx : x ∈ Icc (0 : ℝ) 1) :
  f (tent_map 1 x) = f (ite (x ≤ 1 / 2) (2 * x) (2 * x - 1)) :=
begin
  rw [tent_map_one_eq_ite],
  split_ifs,
  { refl },
  rw [←hf],
  { ring_nf },
  cases hx,
  split;
  linarith,
end

lemma tent_map_one_iterate {n : ℕ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
  (tent_map 1)^[n + 1] x = tent_map 1 (int.fract (x * 2 ^ n)) :=
begin
  induction n with n ih generalizing x,
  { simp only [iterate_one, pow_zero, mul_one],
    rcases eq_or_ne x 1 with rfl | hx₁,
    { rw [int.fract, int.floor_one, int.cast_one, sub_self, tent_map_right_zero zero_le_one,
        tent_map_right_one zero_le_one] },
    rw int.fract_eq_self.2 ⟨hx.1, lt_of_le_of_ne hx.2 hx₁⟩ },
  rw [iterate_succ_apply, tent_map_one_flip (tent_map 1^[n+1]) _ hx, ih],
  { congr' 1,
    split_ifs,
    { ring_nf },
    rw [sub_one_mul, ←int.cast_two, ←int.cast_pow, int.fract_sub_int],
    simp,
    ring_nf },
  { cases hx, split_ifs; split; linarith },
  intros y hy,
  rw [iterate_succ_apply, tent_map_flip, ←iterate_succ_apply],
end

lemma tent_map_one_dyadic_zero {n k : ℕ} (hk : k ≤ 2 ^ n) :
  (tent_map 1)^[n + 1] (k / 2 ^ n) = 0 :=
begin
  rw [tent_map_one_iterate, div_mul_cancel, int.fract_nat_cast, tent_map_right_zero],
  { exact zero_le_one },
  { exact pow_ne_zero _ two_ne_zero },
  split,
  { exact div_nonneg (by simp) (by simp) },
  rw div_le_one,
  { exact_mod_cast hk },
  exact pow_pos two_pos _,
end

lemma tent_map_one_dyadic_one {n k : ℕ} (hk : k < 2 ^ n) :
  (tent_map 1)^[n + 1] ((2 * k + 1) / 2 ^ (n + 1)) = 1 :=
begin
  rw [tent_map_one_iterate, div_mul_comm, pow_succ, mul_comm (2 : ℝ), ←div_div, div_self,
    mul_add_one, ←mul_assoc, one_div_mul_cancel, one_mul, ←int.cast_coe_nat, add_comm,
    int.fract_add_int, int.fract_eq_self.2, tent_map_eq_min_ite],
  { norm_num },
  { norm_num },
  { norm_num1 },
  { exact pow_ne_zero _ two_ne_zero },
  split,
  { exact div_nonneg (by exact_mod_cast (nat.zero_le _)) (pow_nonneg zero_le_two _) },
  rw [div_le_one],
  { norm_cast,
    rw [nat.add_one_le_iff, pow_succ],
    exact mul_lt_mul_of_pos_left hk two_pos },
  exact pow_pos two_pos _
end

lemma not_one_is_periodic_pt (n : ℕ) : ¬ is_periodic_pt (tent_map 1) (n + 1) 1 :=
begin
  have := tent_map_one_dyadic_zero (le_refl (2 ^ n)),
  rw [is_periodic_pt, is_fixed_pt],
  simp only [cast_pow, cast_two, div_self_of_invertible] at this,
  simp [this],
end

open_locale filter topological_space
open filter

lemma tent_map_one_on {n k : ℕ} (hk : k < 2 ^ (n + 1)) :
  ∀ x ∈ Icc ((k : ℝ) / 2 ^ (n + 1)) ((k + 1) / 2 ^ (n + 1)),
    (tent_map 1^[n + 1]) x =
      (if even k then (-k) else (k + 1)) + 2 ^ (n + 1) * (if even k then 1 else -1) * x :=
begin
  have h₂ : (0 : ℝ) < 2 ^ (n + 1) := pow_pos two_pos _,
  have hk₀ : 0 ≤ (k : ℝ) / 2 ^ (n + 1) := div_nonneg (nat.cast_nonneg _) h₂.le,
  have hk₁ : (k + 1 : ℝ) / 2 ^ (n + 1) ≤ 1,
  { rw div_le_one h₂,
    norm_cast,
    rwa add_one_le_iff },
  intros x hx,
  rw [tent_map_one_iterate (Icc_subset_Icc hk₀ hk₁ hx)],
  have : 0 ≤ x * 2 ^ n - k / 2 ∧ x * 2 ^ n - k / 2 ≤ 1 / 2,
  { rw [mem_Icc, div_le_iff h₂, le_div_iff h₂] at hx,
    rwa [sub_div' (_ : ℝ) _ _ two_ne_zero, mul_assoc, ←pow_succ', le_div_iff, zero_mul,
      div_le_div_right, sub_le_iff_le_add', sub_nonneg],
    { exact two_pos },
    { exact two_pos } },
  split_ifs,
  { simp only [even, ←two_mul] at h,
    rcases h with ⟨i, rfl⟩,
    rw [nat.cast_mul, nat.cast_two, mul_div_cancel_left (_ : ℝ) two_ne_zero] at this,
    have hi : int.floor (x * 2 ^ n) = i,
    { rw [int.floor_eq_iff, int.cast_coe_nat],
      split;
      linarith only [this.1, this.2] },
    rw [int.fract, hi, int.cast_coe_nat, tent_map_one_of_le_half this.2, pow_succ, nat.cast_mul,
      nat.cast_two],
    ring },
  rw [←odd_iff_not_even, odd] at h,
  rcases h with ⟨i, rfl⟩,
  rw [nat.cast_add_one, nat.cast_mul, nat.cast_two] at this ⊢,
  rw [_root_.add_div, mul_div_cancel_left (_ : ℝ) two_ne_zero] at this,
  cases this.2.eq_or_lt,
  { rw [sub_eq_iff_eq_add] at h,
    rw [mul_neg, mul_one, neg_mul, mul_comm _ x, pow_succ', ←mul_assoc, h],
    ring_nf,
    rw [←nat.cast_add_one, int.fract_nat_cast, tent_map_right_zero zero_le_one] },
  have hi : int.floor (x * 2 ^ n) = i,
  { rw [int.floor_eq_iff, int.cast_coe_nat],
    split,
    { linarith only [this.1] },
    { linarith only [h] } },
  rw [int.fract, hi, int.cast_coe_nat, tent_map_one_of_half_le, pow_succ],
  { ring_nf },
  linarith only [this.1],
end

lemma tent_map_one_on' {n : ℕ} (hx : x ∈ Icc (0 : ℝ) 1) :
  let k : ℕ := ⌊x * 2 ^ n⌋₊ in
  tent_map 1^[n] x = (if even k then (-k) else (k + 1)) + 2 ^ n * (if even k then 1 else -1) * x :=
begin
  cases n,
  { rcases hx.2.eq_or_lt with rfl | hx',
    { simp },
    simp [nat.floor_eq_zero.2 hx'] },
  have h : (0 : ℝ) < 2 ^ (n + 1) := pow_pos two_pos _,
  intro k,
  rcases hx.2.eq_or_lt with rfl | hx',
  { have h₁ : ((tent_map 1)^[n + 1] _) = _ := tent_map_one_dyadic_zero le_rfl,
    rw [nat.cast_pow, nat.cast_two, div_self_of_invertible] at h₁,
    have h₂ : k = 2 ^ (n + 1),
    { simp only [k, one_mul],
      rw [←nat.cast_two, ←nat.cast_pow, nat.floor_coe] },
    have h₃: even k,
    { rw [h₂, pow_succ],
      exact even_two_mul _ },
    rw [h₁, if_pos h₃, if_pos h₃, h₂],
    simp },
  apply tent_map_one_on,
  { rwa [nat.floor_lt, nat.cast_pow, nat.cast_two, mul_lt_iff_lt_one_left h],
    simpa using hx.1 },
  rw [mem_Icc, div_le_iff h, le_div_iff h],
  exact ⟨nat.floor_le (mul_nonneg hx.1 h.le), (lt_floor_add_one _).le⟩,
end

lemma tent_map_periodic_pt_in {n k : ℕ} (hk : k < 2 ^ (n + 1)) :
  ∀ x ∈ Icc ((k : ℝ) / 2 ^ (n + 1)) ((k + 1) / 2 ^ (n + 1)),
    is_periodic_pt (tent_map 1) (n + 1) x ↔
      x = if even k then k / (2 ^ (n + 1) - 1) else (k + 1) / (2 ^ (n + 1) + 1) :=
begin
  intros x hx,
  rw [is_periodic_pt, is_fixed_pt, tent_map_one_on hk x hx, ←sub_eq_zero, add_sub_assoc,
    ←sub_one_mul, add_eq_zero_iff_neg_eq, eq_comm, mul_comm, ←div_eq_iff_mul_eq,
    apply_ite has_neg.neg, neg_neg],
  { split_ifs,
    { simp [eq_comm] },
    rw [neg_div, ←div_neg_eq_neg_div, mul_neg, neg_sub, mul_one, sub_neg_eq_add, eq_comm,
      add_comm (1 : ℝ)] },
  split_ifs,
  { rw [mul_one, sub_ne_zero],
    have : (2 : ℝ) ≤ 2 ^ (n + 1) := le_self_pow one_le_two (by simp),
    linarith only [this] },
  rw [mul_neg, mul_one, ←neg_add', neg_ne_zero],
  norm_cast,
  simp,
end

lemma tent_map_periodic_pt {n k : ℕ} (hk : k < 2 ^ (n + 1)) :
  is_periodic_pt (tent_map 1) (n + 1) x ∧ x ∈ Ico ((k : ℝ) / 2 ^ (n + 1)) ((k + 1) / 2 ^ (n + 1)) ↔
    x = if even k then k / (2 ^ (n + 1) - 1) else (k + 1) / (2 ^ (n + 1) + 1) :=
begin
  have h₂ : (2 : ℝ) ≤ 2 ^ (n + 1) := le_self_pow one_le_two (by simp),
  split,
  { rintro ⟨hx₁, hx₂⟩,
    rwa ←tent_map_periodic_pt_in hk _ (Ico_subset_Icc_self hx₂) },
  intro h,
  have h' : x ∈ Ico ((k : ℝ) / 2 ^ (n + 1)) ((↑k + 1) / 2 ^ (n + 1)),
  { rw h,
    split_ifs with h',
    { split,
      { refine div_le_div_of_le_left (nat.cast_nonneg _) _ (by simp),
        linarith only [h₂] },
      rw [div_lt_div_iff, add_one_mul, mul_sub_one, sub_add, lt_sub, sub_self, sub_neg,
        lt_sub_iff_add_lt],
      { norm_cast,
        rw ←nat.add_one_le_iff at hk,
        apply lt_of_le_of_ne hk,
        intro i,
        have : even (k + 1), { simp [i, even_pow] },
        simp only [even_add, not_even_one, iff_false] at this,
        apply this h' },
      { linarith only [h₂] },
      { linarith only [h₂] } },
    split,
    { rw [div_le_div_iff, mul_add_one, add_one_mul, add_le_add_iff_left],
      { exact_mod_cast hk.le },
      { linarith only [h₂] },
      { linarith only [h₂] } },
    exact div_lt_div_of_lt_left (nat.cast_add_one_pos _) (by linarith only [h₂]) (by simp) },
  refine ⟨_, h'⟩,
  rw [tent_map_periodic_pt_in hk _ (Ico_subset_Icc_self h'), h],
end

def tent_map_periodic_pts_rat (n : ℕ) : finset ℚ :=
(finset.range (2 ^ n)).image (λ k, if even k then k / (2 ^ n - 1) else (k + 1) / (2 ^ n + 1))

lemma mem_tent_map_periodic_pts_rat_iff {n : ℕ} {x : ℚ} :
  x ∈ tent_map_periodic_pts_rat (n + 1) ↔
    is_periodic_pt (tent_map 1) (n + 1) x ∧
      ∃ k : ℕ, k < 2 ^ (n + 1) ∧ ↑x ∈ Ico ((k : ℝ) / 2 ^ (n + 1)) ((k + 1) / 2 ^ (n + 1)) :=
begin
  simp only [tent_map_periodic_pts_rat, finset.mem_image, finset.mem_range, exists_prop],
  split,
  { rintro ⟨k, hk, h⟩,
    have z := (tent_map_periodic_pt hk).2 _,
    { refine ⟨z.1, k, hk, z.2⟩ },
    rw ←h,
    rw apply_ite coe,
    simp },
  rintro ⟨hx, k, hk, hx'⟩,
  refine ⟨k, hk, _⟩,
  have := (tent_map_periodic_pt hk).1 ⟨hx, hx'⟩,
  rw [←@rat.cast_inj ℝ, this, apply_ite coe],
  simp
end

lemma tent_map_periodic_pts_rat_subset {n : ℕ} : ↑(tent_map_periodic_pts_rat n) ⊆ Icc (0 : ℚ) 1 :=
begin
  cases n,
  { simp only [tent_map_periodic_pts_rat, if_pos, finset.range_one, finset.image_singleton,
      even_zero, pow_zero, sub_self, div_zero, finset.coe_singleton, singleton_subset_iff,
      left_mem_Icc, zero_le_one] },
  have h₂ : (0 : ℝ) < 2 ^ (n + 1) := pow_pos two_pos _,
  intros x hx,
  simp only [finset.mem_coe, mem_tent_map_periodic_pts_rat_iff] at hx,
  obtain ⟨h, k, hk, hk'⟩ := hx,
  rw [mem_Icc, ←@rat.cast_le ℝ, ←@rat.cast_le ℝ, rat.cast_zero, rat.cast_one, ←mem_Icc],
  refine Ico_subset_Icc_self.trans (Icc_subset_Icc _ _) hk',
  { exact div_nonneg (nat.cast_nonneg _) h₂.le },
  rwa [div_le_one h₂, ←nat.cast_two, ←nat.cast_pow, ←nat.cast_add_one, nat.cast_le, add_one_le_iff],
end

lemma one_not_mem_tent_map_periodic_pts_rat {n : ℕ} :
  ¬(1 : ℚ) ∈ tent_map_periodic_pts_rat (n + 1) :=
by { rw [mem_tent_map_periodic_pts_rat_iff, rat.cast_one], simp [not_one_is_periodic_pt n] }

lemma tent_map_periodic_pt_iff {n : ℕ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1):
  is_periodic_pt (tent_map 1) (n + 1) x ↔ ∃ q ∈ tent_map_periodic_pts_rat (n + 1), x = ↑q :=
begin
  rcases hx.2.eq_or_lt with rfl | hx',
  { simp only [not_one_is_periodic_pt n, false_iff, not_exists],
    intros q hq hq',
    rw [eq_comm, ←rat.cast_one, rat.cast_inj] at hq',
    subst hq',
    apply one_not_mem_tent_map_periodic_pts_rat hq },
  have h₂ : (2 : ℝ) ≤ 2 ^ (n + 1) := le_self_pow one_le_two (by simp),
  split,
  { let k : ℕ := ⌊x * 2 ^ (n + 1)⌋₊,
    simp only [tent_map_periodic_pts_rat, finset.mem_image, finset.mem_range, exists_prop,
      exists_exists_and_eq_and],
    have hk : k < 2 ^ (n + 1),
    { rw ←@nat.cast_lt ℝ,
      refine (nat.floor_le (mul_nonneg hx.1 (by simp))).trans_lt _,
      simp only [cast_pow, cast_bit0, cast_one],
      rwa mul_lt_iff_lt_one_left,
      linarith only [h₂] },
    have : x ∈ Ico ((k : ℝ) / 2 ^ (n + 1)) ((k + 1) / 2 ^ (n + 1)),
    { split,
      { rw div_le_iff,
        { exact nat.floor_le (mul_nonneg hx.1 (by simp)) },
        exact pow_pos two_pos _ },
      rw lt_div_iff,
      { exact nat.lt_floor_add_one _ },
      { exact pow_pos two_pos _ } },
    intro hx,
    refine ⟨k, hk, _⟩,
    rw [(tent_map_periodic_pt hk).1 ⟨hx, this⟩, apply_ite coe],
    simp },
  rintro ⟨q, hq, rfl⟩,
  rw mem_tent_map_periodic_pts_rat_iff at hq,
  exact hq.1
end

def tent_map_periodic_pts (n : ℕ) : finset ℝ :=
(tent_map_periodic_pts_rat n).map ⟨(coe : ℚ → ℝ), rat.cast_injective⟩

lemma tent_map_periodic_pts_subset {n : ℕ} : ↑(tent_map_periodic_pts n) ⊆ Icc (0 : ℝ) 1 :=
begin
  simp only [set.subset_def, finset.mem_coe, tent_map_periodic_pts, finset.mem_map,
    embedding.coe_fn_mk, forall_exists_index, forall_apply_eq_imp_iff₂, rat.cast_nonneg],
  intros x hx,
  have := tent_map_periodic_pts_rat_subset hx,
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩,
end

lemma tent_map_periodic_pt_iff' {n : ℕ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1):
  is_periodic_pt (tent_map 1) (n + 1) x ↔ x ∈ tent_map_periodic_pts (n + 1) :=
by simp only [tent_map_periodic_pts, tent_map_periodic_pt_iff hx, exists_prop, finset.mem_map,
    embedding.coe_fn_mk, eq_comm]

lemma tent_map_periodic_pts_rat_card {n : ℕ} :
  (tent_map_periodic_pts_rat (n + 1)).card = 2 ^ (n + 1) :=
begin
  have h₂ : (0 : ℝ) ≤ 2 ^ (n + 1),
  { simp only [pow_nonneg, zero_le_bit0, zero_le_one] },
  rw [tent_map_periodic_pts_rat, finset.card_image_of_inj_on, finset.card_range],
  simp only [set.inj_on, finset.mem_coe, finset.mem_range],
  intros k₁ hk₁ k₂ hk₂ h,
  rw [←@rat.cast_inj ℝ, apply_ite coe, apply_ite coe] at h,
  simp only [rat.cast_div, rat.cast_coe_nat, rat.cast_sub, rat.cast_pow, rat.cast_one,
    rat.cast_bit0, rat.cast_add] at h,
  by_contra h',
  wlog : k₁ < k₂ := ne.lt_or_lt h' using k₁ k₂,
  have : disjoint (Ico ((k₁ : ℝ) / 2 ^ (n + 1)) ((k₁ + 1) / 2 ^ (n + 1)))
    (Ico ((k₂ : ℝ) / 2 ^ (n + 1)) ((k₂ + 1) / 2 ^ (n + 1))),
  { rw [Ico_disjoint_Ico, min_eq_left, max_eq_right],
    { apply div_le_div_of_le h₂,
      rwa [←nat.cast_add_one, nat.cast_le, nat.add_one_le_iff] },
    apply div_le_div_of_le h₂ (nat.cast_le.2 case.le),
    apply div_le_div_of_le h₂ _,
    simpa using case.le },
  exact this.ne_of_mem ((tent_map_periodic_pt hk₁).2 rfl).2 ((tent_map_periodic_pt hk₂).2 h).2 rfl
end

lemma tent_map_periodic_pts_card {n : ℕ} :
  (tent_map_periodic_pts (n + 1)).card = 2 ^ (n + 1) :=
by rw [tent_map_periodic_pts, finset.card_map, tent_map_periodic_pts_rat_card]

lemma finitely_many_periodic_pts {n : ℕ} :
  set.finite {x ∈ Icc (0 : ℝ) 1 | is_periodic_pt (tent_map 1) (n + 1) x} :=
(finite_mem_finset (tent_map_periodic_pts (n + 1))).subset
  (by { rintro x ⟨hx₁, hx₂⟩, rwa [mem_set_of_eq, ←tent_map_periodic_pt_iff' hx₁] })

lemma minimal_period_congr {f g : ℝ → ℝ} (hf : ∀ i, f^[i] x = (g^[i] x)) :
  minimal_period f x = minimal_period g x :=
begin
  rw minimal_period_eq_minimal_period_iff,
  intros n,
  rw [is_periodic_pt, is_periodic_pt, is_fixed_pt, is_fixed_pt, hf],
end

-- lemma minimal_period_congr' {f g : ℝ → ℝ} (hf : ∀ i < minimal_period f x, f^[i] x = (g^[i] x)) :
--   minimal_period f x = minimal_period g x :=
-- begin
--   apply minimal_period_congr,
--   intros i,
--   have := is_periodic_pt.minimal_period_pos,
--   have := hf (i % minimal_period f x) (mod_lt _ _),
-- end

lemma cycle_up {O : finset ℝ} (hO : O.is_cycle (tent_map h)) (hO' : ↑O ⊆ Ico 0 h) (hk : h ≤ k) :
  O.is_cycle (tent_map k) :=
begin
  intros x hx,
  have : ∀ n, tent_map h^[n] x = (tent_map k^[n] x),
  { refine nat.rec _ (λ n ih, _),
    { refl },
    have : (tent_map h^[n+1] x) < h := (hO' (hO.iterate_apply_mem_of_mem _ hx)).2,
    simp only [iterate_succ_apply', tent_map] at this ⊢,
    have := (lt_of_not_le (mt min_eq_left_iff.2 this.ne)).le,
    rw [min_eq_right this, ←ih, min_eq_right (this.trans hk)] },
  refine ⟨_, _⟩,
  { specialize this 1,
    simp only [iterate_one] at this,
    rw [←this],
    apply (hO _ hx).1 },
  rw ←minimal_period_congr this,
  exact (hO _ hx).2
end

lemma cycle_down {O : finset ℝ} (hO : O.is_cycle (tent_map k)) (hO' : ↑O ⊆ Icc 0 h) (hk : h ≤ k) :
  O.is_cycle (tent_map h) :=
begin
  intros x hx,
  have : ∀ n, tent_map h^[n] x = (tent_map k^[n] x),
  { refine nat.rec _ (λ n ih, _),
    { refl },
    have : (tent_map k^[n+1] x) ≤ h := (hO' (hO.iterate_apply_mem_of_mem _ hx)).2,
    simp only [iterate_succ_apply', tent_map] at this ⊢,
    refine le_antisymm _ _,
    { refine min_le_min hk _,
      rw ih },
    rw le_min_iff,
    refine ⟨this, _⟩,
    rw ih,
    exact min_le_right _ _ },
  refine ⟨_, _⟩,
  { specialize this 1,
    simp only [iterate_one] at this,
    rw [this],
    apply (hO _ hx).1 },
  rw minimal_period_congr this,
  exact (hO _ hx).2
end


noncomputable def cycles_of_period (m : ℕ) : finset (finset ℝ) :=
by classical; exactI
((tent_map_periodic_pts m).powerset_len m).filter (λ O : finset ℝ, O.is_cycle (tent_map 1))

lemma cycles_of_period_subset {m : ℕ} {O : finset ℝ} (hO : O ∈ cycles_of_period m) :
  (O : set ℝ) ⊆ Icc (0 : ℝ) 1 :=
begin
  rw [cycles_of_period, finset.mem_filter, finset.mem_powerset_len] at hO,
  exact (finset.coe_subset.2 hO.1.1).trans tent_map_periodic_pts_subset,
end

lemma is_m_cycle_iff_aux {m : ℕ} {O : finset ℝ} (hO : ↑O ⊆ Icc (0 : ℝ) 1):
  O ∈ cycles_of_period m ↔ O.is_cycle (tent_map 1) ∧ O.card = m :=
begin
  rw [cycles_of_period, finset.mem_filter, finset.mem_powerset_len],
  suffices : O.is_cycle (tent_map 1) → O.card = m → O ⊆ tent_map_periodic_pts m,
  { tauto },
  cases m,
  { simp {contextual := tt} },
  rintro hO' hm x hx,
  rw ←tent_map_periodic_pt_iff' (hO hx),
  exact ((hO' x hx).2.trans hm).is_periodic_pt,
end

lemma is_m_cycle_iff {m : ℕ} {O : finset ℝ} :
  O ∈ cycles_of_period m ↔ O.is_cycle (tent_map 1) ∧ O.card = m ∧ ↑O ⊆ Icc (0 : ℝ) 1 :=
begin
  split,
  { intro hO',
    rw [←and_assoc],
    refine ⟨_, cycles_of_period_subset hO'⟩,
    rwa ←is_m_cycle_iff_aux (cycles_of_period_subset hO') },
  rintro ⟨hO, hO', hO''⟩,
  rw is_m_cycle_iff_aux hO'',
  exact ⟨hO, hO'⟩
end

lemma cycles_of_period_nonempty (n : ℕ) : (cycles_of_period (n + 1)).nonempty :=
begin
  obtain ⟨x, hx, hx'⟩ := tent_map_one_minimal_period n.add_one_ne_zero,
  obtain ⟨O, hO, hO', hO'', hO'''⟩ := exists_cycle_of_minimal_period (tent_map_maps_to zero_le_one)
    hx n.add_one_ne_zero hx',
  refine ⟨O, _⟩,
  rw is_m_cycle_iff_aux hO''',
  exact ⟨hO, hO''⟩
end

noncomputable def optimal_parameter : ℕ → ℝ
| 0 := 1
| (m + 1) := ((cycles_of_period (m + 1)).attach.image _).min' $
    ((finset.attach_nonempty_iff _).2 (cycles_of_period_nonempty _)).image $
      λ O, O.1.max' $ by { rw [←finset.card_pos, (is_m_cycle_iff.1 O.2).2.1], exact succ_pos' }

lemma has_cycle_iff {l : ℕ} (hl : l ≠ 0) (h₁ : h ≤ 1) :
  optimal_parameter l < h ↔ ∃ O : finset ℝ, O.is_cycle (tent_map h) ∧ O.card = l ∧ ↑O ⊆ Ico 0 h :=
begin
  cases l,
  { cases hl rfl },
  rw [optimal_parameter, ←not_le, finset.le_min'_iff],
  simp only [subtype.val_eq_coe, subtype.coe_mk, finset.mem_image, finset.mem_attach,
    exists_true_left, subtype.exists, bex_imp_distrib, not_forall, not_le, exists_prop,
    exists_and_distrib_right, true_and],
  split,
  { rintro ⟨_, ⟨O, hO, rfl⟩, hO'⟩,
    rw is_m_cycle_iff at hO,
    have : ↑O ⊆ Ico 0 h,
    { intros x hx,
      exact ⟨(hO.2.2 hx).1, (finset.le_max' _ _ hx).trans_lt hO'⟩ },
    exact ⟨O, cycle_down hO.1 (this.trans Ico_subset_Icc_self) h₁, hO.2.1, this⟩ },
  rintro ⟨O, hO, hO', hO''⟩,
  exact ⟨_, ⟨_, is_m_cycle_iff.2 ⟨cycle_up hO hO'' h₁, hO', hO''.trans
    (Ico_subset_Icc_self.trans (Icc_subset_Icc_right h₁))⟩, rfl⟩, (hO'' (O.max'_mem _)).2⟩,
end

lemma optimal_parameter_succ_mem (m : ℕ) : optimal_parameter (m + 1) ∈ Ico (0 : ℝ) 1 :=
begin
  have : optimal_parameter (m + 1) ∈ _ := finset.min'_mem _ _,
  simp only [nat_zero_eq_zero, add_def, add_zero, subtype.val_eq_coe, subtype.coe_mk,
    finset.mem_image, finset.mem_attach, exists_true_left, subtype.exists] at this,
  obtain ⟨O, hO, hO'⟩ := this,
  rw is_m_cycle_iff at hO,
  rw ←hO',
  exact tent_map_cycle_subset hO.1 (O.max'_mem _)
end

lemma optimal_parameter_mem (m : ℕ) : optimal_parameter m ∈ Icc (0 : ℝ) 1 :=
begin
  cases m,
  { rw [optimal_parameter],
    simp only [right_mem_Icc, zero_le_one] },
  exact Ico_subset_Icc_self (optimal_parameter_succ_mem _),
end

lemma has_cycle_at {m : ℕ} (hm : m ≠ 0) :
  minimal_period (tent_map (optimal_parameter m)) (optimal_parameter m) = m :=
begin
  cases m, { cases hm rfl },
  have : optimal_parameter (m + 1) ∈ _ := finset.min'_mem _ _,
  simp only [nat_zero_eq_zero, add_def, add_zero, subtype.val_eq_coe, subtype.coe_mk,
    finset.mem_image, finset.mem_attach, exists_true_left, subtype.exists] at this,
  obtain ⟨O, hO, hO'⟩ := this,
  rw is_m_cycle_iff at hO,
  have : ↑O ⊆ Icc 0 (optimal_parameter (m + 1)),
  { intros x hx,
    refine ⟨(hO.2.2 hx).1, _⟩,
    rw ←hO',
    exact finset.le_max' _ _ hx },
  convert (cycle_down hO.1 this (optimal_parameter_mem _).2 _ (finset.max'_mem _ _)).2,
  { exact hO'.symm },
  { exact hO.2.1.symm },
end

lemma has_other_cycle {m : ℕ} (O : finset ℝ)
  (hO : O.is_cycle (tent_map (optimal_parameter m))) (hO' : optimal_parameter m ∉ O) :
  ↑O ⊆ Ico 0 (optimal_parameter m) :=
begin
  have hO'' := (tent_map_cycle_subset hO).trans Ico_subset_Icc_self,
  suffices : ∀ x ∈ O, x ≤ optimal_parameter m,
  { intros x hx,
    exact ⟨(hO'' hx).1, (this _ hx).lt_of_ne (ne_of_mem_of_not_mem hx hO')⟩ },
  intros x hx,
  exact (tent_map_cycle_subset' hO hx).2,
end

lemma has_later_cycle {l m : ℕ} (hm : m ≠ 0) (hlm : m ≼ l) :
  ∃ x ∈ Icc (0 : ℝ) 1, minimal_period (tent_map (optimal_parameter m)) x = l :=
begin
  refine sharkovsky_forcing _ _ hlm hm ⟨_, optimal_parameter_mem _, has_cycle_at hm⟩,
  { exact tent_map_continuous.continuous_on },
  { exact tent_map_maps_to' (optimal_parameter_mem _).1 (optimal_parameter_mem _).2 }
end

lemma optimal_parameter_lt {l m : ℕ} (hlm : m ≺ l) :
  optimal_parameter l < optimal_parameter m :=
begin
  have : m ≠ l := hlm.ne,
  rcases eq_or_ne m 0 with rfl | hm,
  { rw [optimal_parameter],
    cases l, { cases this rfl },
    exact (optimal_parameter_succ_mem _).2 },
  obtain ⟨x, hx, hx'⟩ := has_later_cycle hm hlm.le,
  have hl := sharkovsky.ne_zero_of_ge_ne_zero hlm.le hm,
  rw has_cycle_iff hl (optimal_parameter_mem _).2,
  obtain ⟨O, hO, hO', hO'', hO'''⟩ := exists_cycle_of_minimal_period
    (tent_map_maps_to' (optimal_parameter_mem _).1 (optimal_parameter_mem _).2) hx hl hx',
  refine ⟨O, hO, hO'', has_other_cycle O hO _⟩,
  intro h,
  apply this,
  rw [←hO'', ←(hO _ h).2, has_cycle_at hm],
end

lemma optimal_parameter_strict_anti : strict_anti (optimal_parameter ∘ sharkovsky.to_nat) :=
λ l m, optimal_parameter_lt

lemma optimal_parameter_lt_iff {l m : ℕ} : optimal_parameter l < optimal_parameter m ↔ m ≺ l :=
optimal_parameter_strict_anti.lt_iff_lt

lemma optimal_parameter_le_iff {l m : ℕ} : optimal_parameter l ≤ optimal_parameter m ↔ m ≼ l :=
optimal_parameter_strict_anti.le_iff_le

noncomputable def optimal_parameter_infty : ℝ := supr (λ i : ℕ, optimal_parameter (2 ^ i))

lemma optimal_parameter_infty_gt (i : ℕ) : optimal_parameter (2 ^ i) < optimal_parameter_infty :=
begin
  have : optimal_parameter (2 ^ i) < optimal_parameter (2 ^ (i + 1)),
  { rw [optimal_parameter_lt_iff, lt_iff_lt_of_le_iff_le sharkovsky.two_pow_le_two_pow_iff,
      lt_add_iff_pos_right, lt_one_iff] },
  refine lt_of_lt_of_le _ (le_csupr _ (i + 1)),
  { exact this },
  rw [bdd_above_def],
  refine ⟨1, _⟩,
  simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff'],
  intros n,
  exact (optimal_parameter_mem _).2,
end

lemma optimal_parameter_infty_mem_Icc : optimal_parameter_infty ∈ Icc (0 : ℝ) 1 :=
begin
  refine ⟨(optimal_parameter_mem _).1.trans (optimal_parameter_infty_gt 0).le, _⟩,
  apply csupr_le,
  intro x,
  exact (optimal_parameter_mem _).2
end

lemma optimal_parameter_infty' {m : ℕ} (hm : ∀ i : ℕ, 2 ^ i ≠ m) (hm₀ : m ≠ 0) :
  ∀ x, minimal_period (tent_map optimal_parameter_infty) x ≠ m :=
begin
  intros x hx,
  have := sharkovsky.le_two_mul_self_of_not_two_pow hm,
  have hx' := minimal_period.mem_Icc hm₀ hx,
  have h := tent_map_maps_to' optimal_parameter_infty_mem_Icc.1 optimal_parameter_infty_mem_Icc.2,
  obtain ⟨y, hy', hy⟩ := sharkovsky_forcing tent_map_continuous.continuous_on h this hm₀
    ⟨_, Ico_subset_Icc_self hx', hx⟩,
  obtain ⟨O, hO, hO₂, hO₃, hO₄⟩ :=
    exists_cycle_of_minimal_period h (Ico_subset_Icc_self hx') hm₀ hx,
  obtain ⟨P, hP, hP₂, hP₃, hP₄⟩ := exists_cycle_of_minimal_period h hy' (by simpa using hm₀) hy,
  have hO₅ := tent_map_cycle_subset' hO,
  have hP₅ := tent_map_cycle_subset' hP,
  suffices : optimal_parameter (2 * m) < optimal_parameter_infty,
  { obtain ⟨k, hk : _ < optimal_parameter _⟩ := exists_lt_of_lt_csupr this,
    rw optimal_parameter_lt_iff at hk,
    refine (sharkovsky.le_two_pow_of_not_two_pow _).not_lt hk,
    intros l hl,
    cases l,
    { simp only [pow_zero] at hl,
      apply @two_mul_ne_two_mul_add_one m 0,
      rw [←hl, mul_zero] },
    rw [pow_succ, mul_right_inj'] at hl,
    { apply hm l hl },
    exact two_ne_zero },
  have or : ↑O ⊆ Ico 0 optimal_parameter_infty ∨ ↑P ⊆ Ico 0 optimal_parameter_infty,
  { by_contra',
    have hO₆ : optimal_parameter_infty ∈ O,
    { by_contra,
      refine this.1 (λ x hx, ⟨(hO₅ hx).1, lt_of_le_of_ne (hO₅ hx).2 _⟩),
      exact ne_of_mem_of_not_mem hx h },
    have hP₆ : optimal_parameter_infty ∈ P,
    { by_contra,
      refine this.2 (λ x hx, ⟨(hP₅ hx).1, lt_of_le_of_ne (hP₅ hx).2 _⟩),
      exact ne_of_mem_of_not_mem hx h },
    refine (lt_two_mul_self hm₀.bot_lt).ne' _,
    rwa [←hP₃, ←(hP _ hP₆).2, (hO _ hO₆).2] },
  cases or with h' h',
  { refine (optimal_parameter_le_iff.2 this).trans_lt _,
    exact (has_cycle_iff hm₀ optimal_parameter_infty_mem_Icc.2).2 ⟨_, hO, hO₃, h'⟩ },
  exact (has_cycle_iff (by simpa using hm₀) optimal_parameter_infty_mem_Icc.2).2 ⟨_, hP, hP₃, h'⟩
end

def minimal_periods_on {α : Type*} (f : α → α) (s : set α) : set ℕ :=
{n | 0 < n ∧ ∃ x ∈ s, minimal_period f x = n}

lemma mem_minimal_periods_on {α : Type*} {f : α → α} {s : set α} (n : ℕ) :
  n ∈ minimal_periods_on f s ↔ 0 < n ∧ ∃ x ∈ s, minimal_period f x = n :=
iff.rfl

lemma minimal_periods_eq {α : Type*} {f : α → α} {s : set α} :
  minimal_periods_on f s = minimal_period f '' (periodic_pts f ∩ s) :=
begin
  ext n,
  simp only [mem_minimal_periods_on, mem_periodic_pts, exists_prop, mem_set_of_eq, mem_image,
    mem_inter_eq, gt_iff_lt, and_assoc, ←exists_and_distrib_right, ←exists_and_distrib_left],
  split,
  { rintro ⟨x, hn, hx, rfl⟩,
    exact ⟨x, _, hn, is_periodic_pt_minimal_period f x, hx, rfl⟩ },
  { rintro ⟨x, k, hk, hk', hx, rfl⟩,
    exact ⟨_, hk'.minimal_period_pos hk, hx, rfl⟩ }
end


-- def minimal_periods_on {α : Type*} (f : α → α) (s : set α) : set ℕ :=
-- {n | 0 < n ∧ ∃ x ∈ s, minimal_period f x = n}

theorem sharkovsky_compact_unit {s : set sharkovsky} (hs : ⊥ ∉ s) :
  (∃ f : ℝ → ℝ, continuous_on f (Icc 0 1) ∧ maps_to f (Icc 0 1) (Icc 0 1)
    ∧ s = sharkovsky.of_nat '' minimal_periods_on f (Icc 0 1)) ↔
  is_upper_set s ∧ s.nonempty :=
begin
  split,
  { rintro ⟨f, hf₁, hf₂, rfl⟩,
    refine ⟨_, _⟩,
    { rintro _ m h ⟨n, ⟨hn, x, hx, hx'⟩, rfl⟩,
      induction m using sharkovsky.rec,
      obtain ⟨y, hy, hy'⟩ := sharkovsky_forcing hf₁ hf₂ h hn.ne' ⟨x, hx, hx'⟩,
      exact ⟨_, ⟨(sharkovsky.ne_zero_of_ge_ne_zero h hn.ne').bot_lt, y, hy, hy'⟩, rfl⟩ },
    refine ⟨⊤, _⟩,
    simp only [mem_minimal_periods_on, mem_image, lt_one_iff, eq_self_iff_true, true_and,
      sharkovsky.of_nat_eq_top_iff, exists_eq_right, is_fixed_point_iff_minimal_period_eq_one],
    refine exists_fixed_point_Icc zero_le_one hf₁ (or.inl ⟨_, _⟩),
    { exact (hf₂ (left_mem_Icc.2 zero_le_one)).1 },
    { exact (hf₂ (right_mem_Icc.2 zero_le_one)).2 } },
  rintro ⟨hs₁, hs₂⟩,
  rcases (sharkovsky.upper_set_iff.1 hs₁) with (rfl | ⟨n, rfl⟩ | rfl),
  { simpa using hs₂ },
  { refine ⟨tent_map (optimal_parameter n.to_nat), tent_map_continuous.continuous_on, _, _⟩,
    { exact tent_map_maps_to' (optimal_parameter_mem _).1 (optimal_parameter_mem _).2 },
    induction n using sharkovsky.rec,
    ext m,
    induction m using sharkovsky.rec,
    simp only [mem_Ici, le_bot_iff, sharkovsky.of_nat_eq_bot_iff] at hs,
    simp only [mem_Ici, sharkovsky.to_nat_of_nat, mem_image, sharkovsky.of_nat_inj,
      exists_eq_right, mem_minimal_periods_on],



  }
end

theorem sharkovsky_compact {s : set sharkovsky} (hs : sharkovsky.of_nat 0 ∉ s)
  {I : set ℝ} [I.ord_connected] (hI : is_compact I) :
  ∃ f : ℝ → ℝ, continuous_on f I ∧ maps_to f I I ∧ s = minimal_periods_on f I ↔
    is_upper_set s ∧ s.nonempty :=
begin
  sorry
end

theorem sharkovsky_non_compact {s : set sharkovsky} (hs : sharkovsky.of_nat 0 ∉ s)
  {I : set ℝ} [I.ord_connected] (hI : ¬is_compact I) :
  ∃ f : ℝ → ℝ, continuous_on f I ∧ maps_to f I I ∧ s = minimal_periods_on f I ↔
    is_upper_set s :=
begin
  sorry
end

#exit

section computable

def rational_tent_map (h x : ℚ) : ℚ := min h (1 - |2 * x - 1|)

lemma rational_tent_map_one_eq {h x : ℚ} : (rational_tent_map h x : ℝ) = tent_map h x :=
by { rw [rational_tent_map, tent_map], simp }

def tent_map_minimal_period_pts_rat (n : ℕ) : finset ℚ :=
(tent_map_periodic_pts_rat n).filter (λ x, ∀ i < n, i ∣ n → (rational_tent_map 1^[i] x ≠ x))

def max_of_period (n : ℕ) : finset ℚ :=
(tent_map_periodic_pts_rat n).filter (λ x, ∀ i < n, i ≠ 0 → (rational_tent_map 1^[i] x < x))

def computable_cycles_of_period (n : ℕ) : finset (finset ℚ) :=
(max_of_period n).image (λ q, (finset.range n).image (λ i, rational_tent_map 1^[i] q))

def computable_optimal_parameter (n : ℕ) : ℚ := (max_of_period n).min.get_or_else 0

-- #eval computable_optimal_parameter 5

end computable

-- n        periodic pts         pts of min period
-- 1             2                       2            0; 2/3
-- 2             4                       2            2/5, 4/5
-- 3             8                       6            2/9, 4/9, 8/9;
--                                                    2/7, 4/7, 6/7
-- 4            16                      12            2/15, 4/15, 8/15, 14/15;
--                                                    2/17, 4/17, 8/17, 16/17;
--                                                    6/17, 10/17, 12/17, 14/17
-- 5            32                      30
-- 6            64                      54
-- 7           128
-- 8           256
-- 9           512
-- 10         1024
-- 11         2048
-- 12         4096
