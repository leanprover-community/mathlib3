
#exit
lemma eq_C_of_trailing_degree_le_zero (h : trailing_degree p ≤ 0) : p = C (coeff p 0) :=
begin
  sorry,
/-
  refine ext (λ n, _),
  cases n,
  { simp },
  { have : trailing_degree p < ↑(nat.succ n) := lt_of_le_of_lt h (with_top.some_lt_some.2 (nat.succ_pos _)),
    rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_trailing_degree_lt this] }
-/
end

lemma eq_C_of_trailing_degree_eq_zero (h : trailing_degree p = 0) : p = C (coeff p 0) :=
eq_C_of_trailing_degree_le_zero (h ▸ le_refl _)

lemma trailing_degree_le_zero_iff : trailing_degree p ≤ 0 ↔ p = C (coeff p 0) :=
begin
  sorry,
end
/-
⟨eq_C_of_trailing_degree_le_zero, λ h, h.symm ▸ trailing_degree_C_le⟩
-/


lemma trailing_degree_add_le (p q : polynomial R) : min (trailing_degree p) (trailing_degree q) ≤ trailing_degree (p + q) :=
begin
  sorry,
--calc trailing_degree (p + q) = ((p + q).support).inf some : rfl
--  ... ≤ (p.support ∪ q.support).inf some : by convert sup_mono support_add
--  ... = p.support.inf some ⊔ q.support.inf some : by convert sup_union
--  ... = _ : with_top.sup_eq_max _ _
end


@[simp] lemma trailing_coeff_zero : trailing_coeff (0 : polynomial R) = 0 := rfl

@[simp] lemma trailing_coeff_eq_zero : trailing_coeff p = 0 ↔ p = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_min (trailing_degree_eq_nat_trailing_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma trailing_coeff_eq_zero_iff_deg_eq_top : trailing_coeff p = 0 ↔ trailing_degree p = ⊤ :=
by rw [trailing_coeff_eq_zero, trailing_degree_eq_top]

/-  these next three lemmas and their proofs were written entirely by me: they may already exist with better proofs in mathlib -/
lemma non_zero_of_nonempty_support {R : Type u} [semiring R] {f : polynomial R} : f.1.nonempty → f ≠ 0 :=
begin
    intro,
    cases a with N Nhip,
    intro,
    have zero : coeff f N = 0,
        rw a,
        exact coeff_zero N,
    have nonzero : f.2 N ≠ 0,
        exact (f.3 N).mp Nhip,
    apply nonzero,
    exact zero,
end

lemma nonempty_support_of_non_zero {R : Type u} [semiring R] {f : polynomial R} : f ≠ 0 → f.1.nonempty :=
begin
    intro fne,
    let a : R := leading_coeff f,
    have lcnz : f.to_fun (nat_degree f) ≠ 0,
        intro az,
        apply fne,
        apply leading_coeff_eq_zero.mp,
        assumption,
    have dinsupp : nat_degree f ∈ f.1,
        apply (f.3 (nat_degree f)).mpr,
        assumption,
    apply set.nonempty_of_mem,
    assumption,
end

lemma non_zero_iff {R : Type u} [semiring R] {f : polynomial R} : f.1.nonempty ↔ f ≠ 0 :=
begin
    split,
        {
            exact non_zero_of_nonempty_support,
        },
        {
            exact nonempty_support_of_non_zero,
        },
end
/- up to here.  Now back to the library -/

lemma nat_trailing_degree_add_eq_of_nat_trailing_degree_lt (h : trailing_degree p < trailing_degree q) : nat_trailing_degree (p + q) = nat_trailing_degree p :=
begin
  sorry,
/-
  le_antisymm (min_eq_right_of_lt h ▸ trailing_degree_add_le _ _) $ trailing_degree_le_trailing_degree $
  begin
    rw [coeff_add, coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt h, zero_add],
    exact mt leading_coeff_eq_zero.1 (ne_zero_of_trailing_degree_gt h)
  end
-/
end

lemma trailing_degree_add_eq_of_trailing_degree_lt (h : trailing_degree p < trailing_degree q) : trailing_degree (p + q) = trailing_degree p :=
begin
  sorry,
end

lemma trailing_degree_add_C (hp : trailing_degree p < n) : trailing_degree (p + (C a)*X^n) = trailing_degree p :=
begin
  sorry,
end
--add_comm (C a) p ▸ trailing_degree_add_eq_of_trailing_degree_lt $ lt_of_le_of_lt trailing_degree_C_le hp

lemma trailing_degree_add_eq_of_leading_coeff_add_ne_zero (h : trailing_coeff p + trailing_coeff q ≠ 0) :
  trailing_degree (p + q) = min p.trailing_degree q.trailing_degree :=
begin
  sorry,
end
/-
le_antisymm (trailing_degree_add_le _ _) $
  match lt_trichotomy (trailing_degree p) (trailing_degree q) with
  | or.inl hlt :=
    by rw [trailing_degree_add_eq_of_trailing_degree_lt hlt, max_eq_right_of_lt hlt]; exact le_refl _
  | or.inr (or.inl heq) :=
    le_of_not_gt $
      assume hlt : max (trailing_degree p) (trailing_degree q) > trailing_degree (p + q),
      h $ show leading_coeff p + leading_coeff q = 0,
      begin
        rw [heq, max_self] at hlt,
        rw [leading_coeff, leading_coeff, nat_trailing_degree_eq_of_trailing_degree_eq heq, ← coeff_add],
        exact coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt hlt
      end
  | or.inr (or.inr hlt) :=
    by rw [add_comm, trailing_degree_add_eq_of_trailing_degree_lt hlt, max_eq_left_of_lt hlt]; exact le_refl _
  end
-/

lemma trailing_degree_le_erase (p : polynomial R) (n : ℕ) : trailing_degree p ≤ trailing_degree (p.erase n) :=
by convert inf_mono (erase_subset _ _)

lemma trailing_degree_lt_erase (hp : p ≠ 0) : trailing_degree p < trailing_degree (p.erase (nat_trailing_degree p)) :=
begin
  sorry,
end
/-
lt_of_le_of_ne (trailing_degree_erase_le _ _) $
  (trailing_degree_eq_nat_trailing_degree hp).symm ▸ (by convert λ h, not_mem_erase _ _ (mem_of_max h))
-/

lemma trailing_degree_le_sum (s : finset ι) (f : ι → polynomial R) :
  s.inf (λ b, trailing_degree (f b)) ≤ trailing_degree (∑ i in s, f i) :=
begin
  sorry,
end
/-
finset.induction_on s (by simp only [sum_empty, sup_empty, trailing_degree_zero, le_refl]) $
  assume a s has ih,
  calc trailing_degree (∑ i in insert a s, f i) ≤ max (trailing_degree (f a)) (trailing_degree (∑ i in s, f i)) :
    by rw sum_insert has; exact trailing_degree_add_le _ _
  ... ≤ _ : by rw [sup_insert, with_top.sup_eq_max]; exact max_le_max (le_refl _) ih
-/

lemma trailing_degree_le_mul (p q : polynomial R) : trailing_degree p + trailing_degree q ≤ trailing_degree (p * q) :=
begin
  sorry,
end
/-
calc trailing_degree (p * q) ≤ (p.support).sup (λi, trailing_degree (sum q (λj a, C (coeff p i * a) * X ^ (i + j)))) :
    by simp only [single_eq_C_mul_X.symm]; exact trailing_degree_sum_le _ _
  ... ≤ p.support.sup (λi, q.support.sup (λj, trailing_degree (C (coeff p i * coeff q j) * X ^ (i + j)))) :
    finset.sup_mono_fun (assume i hi,  trailing_degree_sum_le _ _)
  ... ≤ trailing_degree p + trailing_degree q :
    begin
      refine finset.sup_le (λ a ha, finset.sup_le (λ b hb, le_trans (trailing_degree_monomial_le _ _) _)),
      rw [with_top.coe_add],
      rw mem_support_iff at ha hb,
      exact add_le_add (le_trailing_degree_of_ne_zero ha) (le_trailing_degree_of_ne_zero hb)
    end
-/

/- I added the := at the end of the line, since it was not there.  I am not sure how this really works... -/
lemma trailing_degree_le_pow (p : polynomial R) : ∀ n, n •ℕ (trailing_degree p) ≤ trailing_degree (p ^ n) :=
begin
  sorry,
end
/-
| 0     := by rw [pow_zero, zero_nsmul]; exact trailing_degree_one_le
| (n+1) := calc trailing_degree (p ^ (n + 1)) ≤ trailing_degree p + trailing_degree (p ^ n) :
    by rw pow_succ; exact trailing_degree_mul_le _ _
  ... ≤ _ : by rw succ_nsmul; exact add_le_add (le_refl _) (trailing_degree_pow_le _)
-/

@[simp] lemma trailing_coeff_monomial (a : R) (n : ℕ) : trailing_coeff (C a * X ^ n) = a :=
begin
  by_cases ha : a = 0,
  { simp only [ha, C_0, zero_mul, trailing_coeff_zero] },
  { rw [trailing_coeff, nat_trailing_degree, trailing_degree_monomial _ ha, ← single_eq_C_mul_X],
    exact @finsupp.single_eq_same _ _ _ n a }
end

@[simp] lemma trailing_coeff_C (a : R) : trailing_coeff (C a) = a :=
suffices trailing_coeff (C a * X^0) = a, by rwa [pow_zero, mul_one] at this,
trailing_coeff_monomial a 0

@[simp] lemma trailing_coeff_X : trailing_coeff (X : polynomial R) = 1 :=
suffices trailing_coeff (C (1:R) * X^1) = 1, by rwa [C_1, pow_one, one_mul] at this,
trailing_coeff_monomial 1 1

@[simp] lemma trailing_monic_X : trailing_monic (X : polynomial R) := trailing_coeff_X

@[simp] lemma trailing_coeff_one : trailing_coeff (1 : polynomial R) = 1 :=
suffices trailing_coeff (C (1:R) * X^0) = 1, by rwa [C_1, pow_zero, mul_one] at this,
trailing_coeff_monomial 1 0


@[simp] lemma trailing_monic_one : trailing_monic (1 : polynomial R) := trailing_coeff_C _

lemma trailing_monic.ne_zero_of_zero_ne_one (h : (0:R) ≠ 1) {p : polynomial R} (hp : p.trailing_monic) :
  p ≠ 0 :=
by { contrapose! h, rwa [h] at hp }

lemma trailing_monic.ne_zero {R : Type*} [semiring R] [nontrivial R] {p : polynomial R} (hp : p.trailing_monic) :
  p ≠ 0 :=
hp.ne_zero_of_zero_ne_one zero_ne_one

lemma trailing_coeff_add_of_trailing_degree_lt (h : trailing_degree p < trailing_degree q) :
  leading_coeff (p + q) = leading_coeff p :=
begin
  sorry,
end
/-
have coeff p (nat_trailing_degree q) = 0, from coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt h,
by simp only [leading_coeff, nat_trailing_degree_eq_of_trailing_degree_eq (trailing_degree_add_eq_of_trailing_degree_lt h),
  this, coeff_add, zero_add]
-/

lemma trailing_coeff_add_of_trailing_degree_eq (h : trailing_degree p = trailing_degree q)
  (hlc : trailing_coeff p + trailing_coeff q ≠ 0) :
  trailing_coeff (p + q) = trailing_coeff p + trailing_coeff q :=
begin
  sorry,
end
/-
have nat_trailing_degree (p + q) = nat_trailing_degree p,
  by apply nat_trailing_degree_eq_of_trailing_degree_eq;
    rw [trailing_degree_add_eq_of_trailing_coeff_add_ne_zero hlc, h, max_self],
by simp only [trailing_coeff, this, nat_trailing_degree_eq_of_trailing_degree_eq h, coeff_add]
-/

@[simp] lemma coeff_mul_trailing_degree_add_trailing_degree (p q : polynomial R) :
  coeff (p * q) (nat_trailing_degree p + nat_trailing_degree q) = trailing_coeff p * trailing_coeff q :=
begin
  sorry,
end
/-
calc coeff (p * q) (nat_trailing_degree p + nat_trailing_degree q) =
    ∑ x in nat.antidiagonal (nat_trailing_degree p + nat_trailing_degree q),
    coeff p x.1 * coeff q x.2 : coeff_mul _ _ _
... = coeff p (nat_trailing_degree p) * coeff q (nat_trailing_degree q) :
  begin
    refine finset.sum_eq_single (nat_trailing_degree p, nat_trailing_degree q) _ _,
    { rintro ⟨i,j⟩ h₁ h₂, rw nat.mem_antidiagonal at h₁,
      by_cases H : nat_trailing_degree p < i,
      { rw [coeff_eq_zero_of_trailing_degree_lt
          (lt_of_le_of_lt nat_trailing_degree_le_trailing_degree (with_top.coe_lt_coe.2 H)), zero_mul] },
      { rw not_lt_iff_eq_or_lt at H, cases H,
        { subst H, rw add_left_cancel_iff at h₁, dsimp at h₁, subst h₁, exfalso, exact h₂ rfl },
        { suffices : nat_trailing_degree q < j,
          { rw [coeff_eq_zero_of_trailing_degree_lt
              (lt_of_le_of_lt trailing_degree_le_nat_trailing_degree (with_top.coe_lt_coe.2 this)), mul_zero] },
          { by_contra H', rw not_lt at H',
            exact ne_of_lt (nat.lt_of_lt_of_le
              (nat.add_lt_add_right H j) (nat.add_le_add_left H' _)) h₁ } } } },
    { intro H, exfalso, apply H, rw nat.mem_antidiagonal }
  end
-/

lemma trailing_degree_mul' (h : trailing_coeff p * trailing_coeff q ≠ 0) :
  trailing_degree (p * q) = trailing_degree p + trailing_degree q :=
begin
  sorry,
end
/-
have hp : p ≠ 0 := by refine mt _ h; exact λ hp, by rw [hp, trailing_coeff_zero, zero_mul],
have hq : q ≠ 0 := by refine mt _ h; exact λ hq, by rw [hq, trailing_coeff_zero, mul_zero],
le_antisymm (trailing_degree_le_mul _ _)
begin
  rw [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq],
  refine le_trailing_degree_of_ne_zero _,
  rwa coeff_mul_trailing_degree_add_trailing_degree
end
-/

lemma nat_trailing_degree_mul' (h : trailing_coeff p * trailing_coeff q ≠ 0) :
  nat_trailing_degree (p * q) = nat_trailing_degree p + nat_trailing_degree q :=
begin
  sorry,
end
/-
have hp : p ≠ 0 := mt trailing_coeff_eq_zero.2 (λ h₁, h $ by rw [h₁, zero_mul]),
have hq : q ≠ 0 := mt trailing_coeff_eq_zero.2 (λ h₁, h $ by rw [h₁, mul_zero]),
have hpq : p * q ≠ 0 := λ hpq, by rw [← coeff_mul_trailing_degree_add_trailing_degree, hpq, coeff_zero] at h;
  exact h rfl,
option.some_inj.1 (show (nat_trailing_degree (p * q) : with_top ℕ) = nat_trailing_degree p + nat_trailing_degree q,
  by rw [← trailing_degree_eq_nat_trailing_degree hpq, trailing_degree_mul' h, trailing_degree_eq_nat_trailing_degree hp,
    trailing_degree_eq_nat_trailing_degree hq])
-/

lemma trailing_coeff_mul' (h : trailing_coeff p * trailing_coeff q ≠ 0) :
  trailing_coeff (p * q) = trailing_coeff p * trailing_coeff q :=
begin
  unfold trailing_coeff,
  rw [nat_trailing_degree_mul' h, coeff_mul_trailing_degree_add_trailing_degree],
  refl
end

lemma trailing_coeff_pow' : trailing_coeff p ^ n ≠ 0 →
  trailing_coeff (p ^ n) = trailing_coeff p ^ n :=
nat.rec_on n (by simp) $
λ n ih h,
have h₁ : trailing_coeff p ^ n ≠ 0 :=
  λ h₁, h $ by rw [pow_succ, h₁, mul_zero],
have h₂ : trailing_coeff p * trailing_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← ih h₁] at h,
by rw [pow_succ, pow_succ, trailing_coeff_mul' h₂, ih h₁]

lemma trailing_degree_pow' : ∀ {n}, trailing_coeff p ^ n ≠ 0 →
  trailing_degree (p ^ n) = n •ℕ (trailing_degree p)
| 0     := λ h, by rw [pow_zero, ← C_1] at *;
  rw [trailing_degree_C h, zero_nsmul]
| (n+1) := λ h,
have h₁ : trailing_coeff p ^ n ≠ 0 := λ h₁, h $
  by rw [pow_succ, h₁, mul_zero],
have h₂ : trailing_coeff p * trailing_coeff (p ^ n) ≠ 0 :=
  by rwa [pow_succ, ← trailing_coeff_pow' h₁] at h,
by rw [pow_succ, trailing_degree_mul' h₂, succ_nsmul, trailing_degree_pow' h₁]

lemma nat_trailing_degree_pow' {n : ℕ} (h : trailing_coeff p ^ n ≠ 0) :
  nat_trailing_degree (p ^ n) = n * nat_trailing_degree p :=
begin
  sorry,
end
/-
if hp0 : p = 0 then
  if hn0 : n = 0 then by simp *
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else
have hpn : p ^ n ≠ 0, from λ hpn0,  have h1 : _ := h,
  by rw [← trailing_coeff_pow' h1, hpn0, trailing_coeff_zero] at h;
  exact h rfl,
option.some_inj.1 $ show (nat_trailing_degree (p ^ n) : with_top ℕ) = (n * nat_trailing_degree p : ℕ),
  by rw [← trailing_degree_eq_nat_trailing_degree hpn, trailing_degree_pow' h, trailing_degree_eq_nat_trailing_degree hp0,
    ← with_top.coe_nsmul]; simp
-/

@[simp] lemma trailing_coeff_X_pow : ∀ n : ℕ, trailing_coeff ((X : polynomial R) ^ n) = 1
| 0 := by simp
| (n+1) :=
if h10 : (1 : R) = 0
then by rw [pow_succ, ← one_mul X, ← C_1, h10]; simp
else
have h : trailing_coeff (X : polynomial R) * trailing_coeff (X ^ n) ≠ 0,
  by rw [trailing_coeff_X, trailing_coeff_X_pow n, one_mul];
    exact h10,
by rw [pow_succ, trailing_coeff_mul' h, trailing_coeff_X, trailing_coeff_X_pow, one_mul]


theorem trailing_coeff_mul_X_pow {p : polynomial R} {n : ℕ} :
  trailing_coeff (p * X ^ n) = trailing_coeff p :=
decidable.by_cases
  (λ H : trailing_coeff p = 0, by rw [H, trailing_coeff_eq_zero.1 H, zero_mul, trailing_coeff_zero])
  (λ H : trailing_coeff p ≠ 0,
    by rw [trailing_coeff_mul', trailing_coeff_X_pow, mul_one];
      rwa [trailing_coeff_X_pow, mul_one])

lemma nat_trailing_degree_mul_le {p q : polynomial R} : nat_trailing_degree p + nat_trailing_degree q ≤ nat_trailing_degree (p * q) :=
begin
  sorry,
/-
  apply trailing_degree_le_of_nat_trailing_degree_le,
  apply le_trans (trailing_degree_mul_le p q),
  rw with_top.coe_add,
  refine add_le_add _ _; apply trailing_degree_le_nat_trailing_degree,
-/
end

lemma subsingleton_of_trailing_monic_zero (h : trailing_monic (0 : polynomial R)) :
  (∀ p q : polynomial R, p = q) ∧ (∀ a b : R, a = b) :=
by rw [trailing_monic.def, trailing_coeff_zero] at h;
  exact ⟨λ p q, by rw [← mul_one p, ← mul_one q, ← C_1, ← h, C_0, mul_zero, mul_zero],
    λ a b, by rw [← mul_one a, ← mul_one b, ← h, mul_zero, mul_zero]⟩


lemma zero_le_trailing_degree_iff {p : polynomial R} : trailing_degree p < ⊤ ↔ p ≠ 0 :=
by rw [ne.def, ← trailing_degree_eq_top];
  cases trailing_degree p; exact dec_trivial

/- I am not sure how this lemma is different from the one above, but it was in the file -/
lemma trailing_degree_nonneg_iff_ne_zero : trailing_degree p < ⊤ ↔ p ≠ 0 :=
begin
  sorry,
end
/-
⟨λ h0p hp0, absurd h0p (by rw [hp0, trailing_degree_zero]; exact dec_trivial),
  λ hp0, le_of_not_gt (λ h, by simp [gt, trailing_degree_eq_top, *] at *)⟩
-/

lemma nat_trailing_degree_eq_zero_iff_trailing_degree_le_zero : p.nat_trailing_degree = 0 ↔ p.trailing_degree = (0 : with_top ℕ) ∨ p.trailing_degree = (⊤ : with_top ℕ) :=
begin
  sorry,
end
/-
if hp0 : p = 0 then by simp [hp0]
else by rw [trailing_degree_eq_nat_trailing_degree hp0, ← with_top.coe_zero, with_top.coe_le_coe,
  nat.le_zero_iff]
-/

theorem trailing_degree_ge_iff_coeff_zero (f : polynomial R) (n : with_top ℕ) :
  n ≤ trailing_degree f ↔ ∀ m : ℕ, (m : with_top ℕ) < n → coeff f m = 0 :=
begin
  sorry,
end
/-
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_top ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_top ℕ) ≤ n)) Hm,
  H1 $ (finsupp.mem_support_to_fun f m).2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  (finsupp.mem_support_to_fun f b).1 Hb $ H b $ lt_of_not_ge Hn⟩
-/


lemma trailing_degree_lt_trailing_degree_mul_X (hp : p ≠ 0) : p.trailing_degree < (p * X).trailing_degree :=
by haveI := nonzero.of_polynomial_ne hp; exact
have trailing_coeff p * trailing_coeff X ≠ 0, by simpa,
by erw [trailing_degree_mul' this, trailing_degree_eq_nat_trailing_degree hp,
    trailing_degree_X, ← with_top.coe_one, ← with_top.coe_add, with_top.coe_lt_coe];
  exact nat.lt_succ_self _


lemma eq_C_of_nat_trailing_degree_le_zero {p : polynomial R} (h : nat_trailing_degree p ≤ 0) : p = C (coeff p 0) :=
begin
  sorry,
/-
  refine polynomial.ext (λ n, _),
  cases n,
  { simp },
  { have : nat_trailing_degree p < nat.succ n := lt_of_le_of_lt h (nat.succ_pos _),
    rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_lt_nat_trailing_degree this] }
-/
end

lemma nat_trailing_degree_pos_iff_trailing_degree_pos {p : polynomial R} :
  0 < nat_trailing_degree p ↔ 0 < trailing_degree p ∧ trailing_degree p < ⊤ :=
begin
  sorry,
end
/-
⟨ λ h, ((trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos h).mpr rfl).symm ▸ (with_top.some_lt_some.mpr h),
  by { unfold nat_trailing_degree,
       cases trailing_degree p,
       { rintros ⟨_, ⟨⟩, _⟩ },
       { exact with_top.some_lt_some.mp } } ⟩
-/

end semiring


section nonzero_semiring
variables [semiring R] [nontrivial R] {p q : polynomial R}

@[simp] lemma trailing_degree_X_pow : ∀ (n : ℕ), trailing_degree ((X : polynomial R) ^ n) = n
| 0 := by simp only [pow_zero, trailing_degree_one]; refl
| (n+1) :=
have h : trailing_coeff (X : polynomial R) * trailing_coeff (X ^ n) ≠ 0,
  by rw [trailing_coeff_X, trailing_coeff_X_pow n, one_mul];
    exact zero_ne_one.symm,
by rw [pow_succ, trailing_degree_mul' h, trailing_degree_X, trailing_degree_X_pow, add_comm]; refl

end nonzero_semiring

section ring
variables [ring R] {p q : polynomial R}


lemma trailing_degree_sub_le (p q : polynomial R) : min (trailing_degree p) (trailing_degree q) ≤ trailing_degree (p - q) :=
trailing_degree_neg q ▸ trailing_degree_add_le p (-q)

lemma trailing_degree_sub_lt (hd : trailing_degree p = trailing_degree q)
  (hp0 : p ≠ 0) (hlc : trailing_coeff p = trailing_coeff q) :
  trailing_degree (p - q) < trailing_degree p :=
begin
  sorry,
end
/-
have hp : single (nat_trailing_degree p) (leading_coeff p) + p.erase (nat_trailing_degree p) = p :=
  finsupp.single_add_erase,
have hq : single (nat_trailing_degree q) (leading_coeff q) + q.erase (nat_trailing_degree q) = q :=
  finsupp.single_add_erase,
have hd' : nat_trailing_degree p = nat_trailing_degree q := by unfold nat_trailing_degree; rw hd,
have hq0 : q ≠ 0 := mt trailing_degree_eq_top.2 (hd ▸ mt trailing_degree_eq_top.1 hp0),
calc trailing_degree (p - q) = trailing_degree (erase (nat_trailing_degree q) p + -erase (nat_trailing_degree q) q) :
  by conv {to_lhs, rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]}
... ≤ max (trailing_degree (erase (nat_trailing_degree q) p)) (trailing_degree (erase (nat_trailing_degree q) q))
  : trailing_degree_neg (erase (nat_trailing_degree q) q) ▸ trailing_degree_add_le _ _
... < trailing_degree p : max_lt_iff.2 ⟨hd' ▸ trailing_degree_lt_erase hp0, hd.symm ▸ trailing_degree_lt_erase hq0⟩
-/

lemma nat_trailing_degree_X_sub_C_le {r : R} : (X - C r).nat_trailing_degree ≤ 1 :=
begin
  sorry,
end
/-
nat_trailing_degree_le_of_trailing_degree_le $ le_trans (trailing_degree_sub_le _ _) $ max_le trailing_degree_X_le $
le_trans trailing_degree_C_le $ with_top.coe_le_coe.2 zero_le_one
-/

end ring

section nonzero_ring
variables [nontrivial R] [ring R]

@[simp] lemma trailing_degree_X_sub_C (a : R) : trailing_degree (X - C a) = 1 :=
begin
  sorry,
/-
  rw [sub_eq_add_neg, add_comm, ← @trailing_degree_X R],
  by_cases ha : a = 0,
  { simp only [ha, C_0, neg_zero, zero_add] },
  exact trailing_degree_add_eq_of_trailing_degree_lt (by rw [trailing_degree_X, trailing_degree_neg, trailing_degree_C ha]; exact dec_trivial)
-/
end

@[simp] lemma nat_trailing_degree_X_sub_C (x : R) : (X - C x).nat_trailing_degree = 1 :=
nat_trailing_degree_eq_of_trailing_degree_eq_some $ trailing_degree_X_sub_C x


/-not sure what this lemma is doing
@[simp]
lemma next_coeff_X_sub_C (c : R) : next_coeff (X - C c) = - c :=
by simp [next_coeff_of_pos_nat_trailing_degree]
-/

lemma trailing_degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  trailing_degree ((X : polynomial R) ^ n - C a) = n :=
begin
  sorry,
end
/-
have trailing_degree (-C a) < trailing_degree ((X : polynomial R) ^ n),
  from calc trailing_degree (-C a) ≤ 0 : by rw trailing_degree_neg; exact le_trailing_degree_C
  ... < trailing_degree ((X : polynomial R) ^ n) : by rwa [trailing_degree_X_pow];
    exact with_top.coe_lt_coe.2 hn,
by rw [sub_eq_add_neg, add_comm, trailing_degree_add_eq_of_trailing_degree_lt this, trailing_degree_X_pow]
-/

lemma nat_trailing_degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} :
  (X ^ n - C r).nat_trailing_degree = n :=
begin
  sorry,
end
--by { apply nat_trailing_degree_eq_of_trailing_degree_eq_some, simp [trailing_degree_X_pow_sub_C hn], }

end nonzero_ring

section integral_domain
variables [integral_domain R] {p q : polynomial R}

@[simp] lemma trailing_degree_mul : trailing_degree (p * q) = trailing_degree p + trailing_degree q :=
if hp0 : p = 0 then by simp only [hp0, trailing_degree_zero, zero_mul, with_top.top_add]
else if hq0 : q = 0 then  by simp only [hq0, trailing_degree_zero, mul_zero, with_top.add_top]
else trailing_degree_mul' $ mul_ne_zero (mt trailing_coeff_eq_zero.1 hp0)
    (mt trailing_coeff_eq_zero.1 hq0)

@[simp] lemma trailing_degree_pow (p : polynomial R) (n : ℕ) :
  trailing_degree (p ^ n) = n •ℕ (trailing_degree p) :=
by induction n; [simp only [pow_zero, trailing_degree_one, zero_nsmul],
simp only [*, pow_succ, succ_nsmul, trailing_degree_mul]]

@[simp] lemma trailing_coeff_mul (p q : polynomial R) : trailing_coeff (p * q) =
  trailing_coeff p * trailing_coeff q :=
begin
  by_cases hp : p = 0,
  { simp only [hp, zero_mul, trailing_coeff_zero] },
  { by_cases hq : q = 0,
    { simp only [hq, mul_zero, trailing_coeff_zero] },
    { rw [trailing_coeff_mul'],
      exact mul_ne_zero (mt trailing_coeff_eq_zero.1 hp) (mt trailing_coeff_eq_zero.1 hq) } }
end

@[simp] lemma trailing_coeff_X_add_C (a b : R) (ha : a ≠ 0):
  leading_coeff (C a * X + C b) = b :=
begin
  sorry,
/-
  rw [add_comm, trailing_coeff_add_of_trailing_degree_lt],
  { simp },
  { simpa [trailing_degree_C ha] using lt_of_le_of_lt le_trailing_degree_C (with_top.coe_lt_coe.2 zero_lt_one)}
-/
end

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` is an `integral_domain`, and thus
  `leading_coeff` is multiplicative -/
def trailing_coeff_hom : polynomial R →* R :=
{ to_fun := trailing_coeff,
  map_one' := by simp,
  map_mul' := trailing_coeff_mul }

@[simp] lemma trailing_coeff_hom_apply (p : polynomial R) :
  trailing_coeff_hom p = trailing_coeff p := rfl

@[simp] lemma trailing_coeff_pow (p : polynomial R) (n : ℕ) :
  trailing_coeff (p ^ n) = trailing_coeff p ^ n :=
trailing_coeff_hom.map_pow p n
end integral_domain

lemma trailprod {R : Type*} [field R] {f g : polynomial R} : trailing_coeff (f*g) = trailing_coeff f * trailing_coeff g :=
begin
  exact trailing_coeff_mul f g,
end
