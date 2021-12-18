/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import data.sym.sym2

/-!
# Stars and bars

In this file, we prove the case `n = 2` of stars and bars.

## Informal statement

If we have `n` objects to put in `k` boxes, we can do so in exactly `(n + k - 1).choose k` ways.

## Formal statement

We can identify the `k` boxes with the elements of a fintype `α` of card `k`. Then placing `n`
elements in those boxes corresponds to choosing how many of each element of `α` appear in a multiset
of card `n`. `sym α n` being the subtype of `multiset α` of multisets of card `n`, writing stars
and bars using types gives
```lean
lemma stars_and_bars {α : Type*} [fintype α] (n : ℕ) :
  card (sym α n) = (card α + n - 1).choose n := sorry
```

## TODO

Prove the general case of stars and bars.

## Tags

stars and bars
-/

def multichoose1 (n k : ℕ) := fintype.card (sym (fin n) k)

def multichoose2 (n k : ℕ) := (n + k - 1).choose k

instance sym.has_zero {α : Type*} : has_zero (sym α 0) := ⟨⟨0, rfl⟩⟩
instance sym.has_emptyc {α : Type*} : has_emptyc (sym α 0) := ⟨0⟩

instance sym.subsingleton {α : Type*} {n : ℕ} [g : subsingleton α] : subsingleton (sym α n) :=
⟨begin
  unfreezingI { cases g },
  intros,
  rcases a with ⟨c, d⟩,
  rcases b with ⟨a, b⟩,
  simp only [subtype.mk.inj_eq],
  induction a using multiset.case_strong_induction_on with k hk wa generalizing n c,
  { rw b.symm at d,
    norm_num at d,
    assumption },
  { cases n,
    { norm_num at b },
    { classical,
      exact if s : c = 0 then begin
        rw s at d,
        norm_num at d,
      end else begin
        have re := multiset.exists_mem_of_ne_zero s,
        rcases re with ⟨re, we⟩,
        cases multiset.exists_cons_of_mem we,
        rw h,
        have ob := @wa hk (by norm_num) n w begin
          rw h at d,
          norm_num at d,
          refine nat.succ.inj d,
        end begin
          norm_num at b,
          refine nat.succ.inj b,
        end,
        rw [ob, g re k],
      end } },
end⟩

instance sym2.subsingleton {α : Type*} [g : subsingleton α] : subsingleton (sym2 α) := ⟨begin
  have k := @sym.subsingleton α 2 g,
  unfreezingI { cases g },
  intros,
  have z := equiv.injective (sym2.equiv_sym α),
  rw function.injective at z,
  exact @z a b begin
    generalize_hyp c : sym2.equiv_sym α = o,
    cases o,
    rw equiv.coe_fn_mk,
    unfreezingI { cases k },
    apply k,
  end,
end⟩

instance sym2.unique {α : Type*} [g : unique α] : unique (sym2 α) := unique.mk' _
instance sym.unique {α : Type*} {n : ℕ} [g : unique α] : unique (sym α n) := unique.mk' _

instance sym.is_empty {α : Type*} {n : ℕ} [g : is_empty α] : is_empty (sym α n.succ) := ⟨begin
  intro h,
  rw sym at h,
  have w := @multiset.exists_mem_of_ne_zero _ h.val begin
    intro y,
    have z := h.property,
    rw y at z,
    norm_num at z,
  end,
  rcases w with ⟨w, q⟩,
  unfreezingI {
    cases g,
    tauto,
  },
end⟩

instance sym2.is_empty {α : Type*} [g : is_empty α] : is_empty (sym2 α) := ⟨begin
  intro x,
  have h := (@sym2.equiv_sym α).to_fun x,
  rw sym at h,
  have := @sym.is_empty α 1 g,
  cases this,
  tauto,
end⟩

instance sym2.nontrivial {α : Type*} [g : nontrivial α] : nontrivial (sym2 α) := ⟨begin
  unfreezingI { rcases g with ⟨w, ⟨m, g⟩⟩ },
  use [sym2.diag w, sym2.diag m],
  intro h,
  exact g (sym2.diag_injective h),
end⟩

instance sym.nontrivial {α : Type*} {n : ℕ} [g : nontrivial α] : nontrivial (sym α (n + 1)) :=
⟨begin
  unfreezingI { rcases g with ⟨w, ⟨m, g⟩⟩ },
  induction n with n h,
  { use [w::sym.nil, m::sym.nil],
    norm_num,
    assumption },
  { rcases h with ⟨t, ⟨q, h⟩⟩,
    use [w::t, m::t],
    norm_num,
    assumption }
end⟩

def sym.map {α β : Type*} {n : ℕ} (f : α → β) (x : sym α n) : sym β n :=
  ⟨x.val.map f, by simpa [multiset.card_map] using x.property⟩

@[simp] lemma sym.mem_map {α β : Type*} {n : ℕ} {f : α → β} {b : β} {l : sym α n} :
  b ∈ sym.map f l ↔ ∃ a, a ∈ l ∧ f a = b := multiset.mem_map

@[simp] lemma sym.map_id {α : Type*} {n : ℕ} (s : sym α n) : sym.map id s = s :=
  by simp [sym.map, subtype.mk.inj_eq]

@[simp] lemma sym.map_map {α β γ : Type*} {n : ℕ} (g : β → γ) (f : α → β) (s : sym α n) :
  sym.map g (sym.map f s) = sym.map (g ∘ f) s :=
  by simp [sym.map, subtype.mk.inj_eq]

@[simp] lemma sym.map_zero {α β : Type*} (f : α → β) :
  sym.map f (0 : sym α 0) = (0 : sym β 0) :=
  begin
    rw sym.has_zero,
    simp only [sym.map, multiset.map_zero],
    rw sym.has_zero,
    norm_num,
  end

@[simp] lemma sym.map_cons {α β : Type*} {n : ℕ} (f : α → β) (a : α) (s : sym α n) : sym.map f (a::s) = (f a)::sym.map f s :=
  begin
    simp only [sym.map, subtype.mk.inj_eq, sym.cons],
    convert multiset.map_cons f a s.val,
    cases s,
    rw sym.cons,
  end

def encode (n k : ℕ) (x : sym (fin n.succ) k.succ) : sym (fin n) k.succ ⊕ sym (fin n.succ) k :=
if h : fin.last n ∈ x then
  sum.inr ⟨x.val.erase (fin.last n), by { rw [multiset.card_erase_of_mem h, x.property], refl }⟩
else begin
  refine sum.inl ⟨x.val.map (λ a, ⟨if (a : ℕ) = n then 0 else a, _⟩), _⟩,
  { split_ifs,
    { rw pos_iff_ne_zero,
      rintro rfl,
      obtain ⟨w, r⟩ := @multiset.exists_mem_of_ne_zero _ x.val (λ h, by simpa [h] using x.property),
      simpa [subsingleton.elim w 0] using r, },
    { cases lt_or_eq_of_le (nat.le_of_lt_succ a.property); solve_by_elim } },
  { rw [multiset.card_map, x.property] }
end

def decode (n k : ℕ) : sym (fin n) k.succ ⊕ sym (fin n.succ) k → sym (fin n.succ) k.succ
| (sum.inl x) := ⟨x.val.map (λ a, ⟨a.val, a.property.step⟩),
                  by simpa [multiset.card_map] using x.property⟩
| (sum.inr x) := (fin.last n)::x

lemma equivalent (n k : ℕ) : sym (fin n.succ) k.succ ≃ sym (fin n) k.succ ⊕ sym (fin n.succ) k :=
{ to_fun := encode n k,
  inv_fun := decode n k,
  left_inv := begin
    rintro ⟨x, hx⟩,
    rw encode,
    split_ifs,
    { rw decode,
      simp [sym.cons, multiset.cons_erase h], },
    { simp only [decode, multiset.map_map, subtype.mk.inj_eq, function.comp],
      convert multiset.map_congr _,
      { rw multiset.map_id, },
      rintros ⟨g, hg⟩ h',
      split_ifs with h'',
      { simp only [fin.coe_mk] at h'',
        subst g,
        exact false.elim (h h'), },
      { refl } },
  end,
  right_inv := begin
    rintro (x|x),
    { cases x with x hx,
      rw [decode, encode],
      split_ifs,
      { obtain ⟨y, v, b⟩ := multiset.mem_map.mp h,
        rw [fin.last, subtype.mk_eq_mk] at b,
        have := y.property,
        rw b at this,
        exact nat.lt_asymm this this, },
      { simp only [multiset.map_map, function.comp],
        simp only [fin.val_eq_coe, subtype.mk_eq_mk, multiset.map_map, fin.coe_mk],
        convert multiset.map_congr _,
        { rw multiset.map_id, },
        rintros ⟨g, hg⟩ h',
        split_ifs with h'',
        { simp only [fin.coe_mk] at h'',
          subst g,
          exact (nat.lt_asymm hg hg).elim, },
        { refl } } },
    { rw [decode, encode],
      split_ifs,
      { cases x, simp [sym.cons] },
      { apply h,
        cases x,
        simp only [sym.cons],
        apply multiset.mem_cons_self } }
  end }

lemma multichoose1_rec (n k : ℕ) :
  multichoose1 n.succ k.succ = multichoose1 n k.succ + multichoose1 n.succ k :=
begin
  simp only [multichoose1, fintype.card_sum.symm],
  exact fintype.card_congr (equivalent n k),
end

lemma multichoose2_rec (n k : ℕ) :
  multichoose2 n.succ k.succ = multichoose2 n k.succ + multichoose2 n.succ k :=
begin
  simp only [multichoose2, nat.add_succ, tsub_zero, nat.succ_sub_succ_eq_sub, nat.succ_add_sub_one,
    nat.succ_add, nat.choose_succ_succ, nat.add_comm],
end

lemma multichoose1_eq_multichoose2 : ∀ (n k : ℕ), multichoose1 n k = multichoose2 n k
| 0 0 := begin
  simp only [multichoose1, multichoose2],
  norm_num,
end
| 0 (k + 1) := begin
  simp only [multichoose1, multichoose2],
  norm_num,
  have no_inhabitants : sym (fin 0) k.succ → false := begin
    intro h,
    rw sym at h,
    have w := @multiset.exists_mem_of_ne_zero _ h.val begin
      intro y,
      have z := h.property,
      rw y at z,
      norm_num at z,
    end,
    rcases w with ⟨⟨v, w⟩, q⟩,
    norm_num at w,
  end,
  exact (@fintype.card_eq_zero_iff (sym (fin 0) k.succ) _).mpr ⟨no_inhabitants⟩,
end
| (n + 1) 0 := begin
  simp only [multichoose1, multichoose2],
  norm_num,
  dec_trivial,
end
| (n + 1) (k + 1) := begin
  simp only [multichoose1_rec, multichoose2_rec, multichoose1_eq_multichoose2 n k.succ,
    multichoose1_eq_multichoose2 n.succ k],
end

open finset fintype

namespace sym2

lemma stars_and_bars {α : Type*} [decidable_eq α] [fintype α] (n : ℕ) :
  fintype.card (sym α n) = (fintype.card α + n - 1).choose n :=
begin
  have start := multichoose1_eq_multichoose2 (fintype.card α) n,
  simp only [multichoose1, multichoose2] at start,
  rw start.symm,
  have bundle := (@fintype.equiv_fin_of_card_eq α _ (fintype.card α) rfl),
  apply fintype.card_congr,
  refine ⟨_, _, _, _⟩,
  { intro x,
    refine ⟨_, _⟩,
    { exact x.val.map (bundle.to_fun) },
    { rw [multiset.card_map, x.property] } },
  { intro x,
    refine ⟨_, _⟩,
    { exact x.val.map (bundle.inv_fun) },
    { rw [multiset.card_map, x.property] } },
  { rw function.left_inverse,
    intro x,
    simp_rw [multiset.map_map, function.comp],
    have temp := bundle.left_inv,
    rw function.left_inverse at temp,
    have unpack : x = ⟨x.val, x.property⟩ := begin
      norm_num,
    end,
    conv begin
      to_rhs,
      rw unpack,
    end,
    rw subtype.mk.inj_eq,
    conv begin
      to_rhs,
      rw (@multiset.map_id _ x.val).symm,
    end,
    apply multiset.map_congr,
    intros b u,
    rw [id, temp] },
  { rw [function.right_inverse, function.left_inverse],
    intro x,
    simp_rw [multiset.map_map, function.comp],
    have temp := bundle.right_inv,
    rw function.right_inverse at temp,
    have unpack : x = ⟨x.val, x.property⟩ := begin
      norm_num,
    end,
    conv begin
      to_rhs,
      rw unpack,
    end,
    rw subtype.mk.inj_eq,
    conv begin
      to_rhs,
      rw (@multiset.map_id _ x.val).symm,
    end,
    apply multiset.map_congr,
    intros b u,
    rw [id, temp] },
end

variables {α : Type*} [decidable_eq α]

/-- The `diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.card`. -/
lemma card_image_diag (s : finset α) :
  (s.diag.image quotient.mk).card = s.card :=
begin
  rw [card_image_of_inj_on, diag_card],
  rintro ⟨x₀, x₁⟩ hx _ _ h,
  cases quotient.eq.1 h,
  { refl },
  { simp only [mem_coe, mem_diag] at hx,
    rw hx.2 }
end

lemma two_mul_card_image_off_diag (s : finset α) :
  2 * (s.off_diag.image quotient.mk).card = s.off_diag.card :=
begin
  rw [card_eq_sum_card_fiberwise
    (λ x, mem_image_of_mem _ : ∀ x ∈ s.off_diag, quotient.mk x ∈ s.off_diag.image quotient.mk),
    sum_const_nat (quotient.ind _), mul_comm],
  rintro ⟨x, y⟩ hxy,
  simp_rw [mem_image, exists_prop, mem_off_diag, quotient.eq] at hxy,
  obtain ⟨a, ⟨ha₁, ha₂, ha⟩, h⟩ := hxy,
  obtain ⟨hx, hy, hxy⟩ : x ∈ s ∧ y ∈ s ∧ x ≠ y,
  { cases h; have := ha.symm; exact ⟨‹_›, ‹_›, ‹_›⟩ },
  have hxy' : y ≠ x := hxy.symm,
  have : s.off_diag.filter (λ z, ⟦z⟧ = ⟦(x, y)⟧) = ({(x, y), (y, x)} : finset _),
  { ext ⟨x₁, y₁⟩,
    rw [mem_filter, mem_insert, mem_singleton, sym2.eq_iff, prod.mk.inj_iff, prod.mk.inj_iff,
      and_iff_right_iff_imp],
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); rw mem_off_diag; exact ⟨‹_›, ‹_›, ‹_›⟩ }, -- hxy' is used here
  rw [this, card_insert_of_not_mem, card_singleton],
  simp only [not_and, prod.mk.inj_iff, mem_singleton],
  exact λ _, hxy',
end

/-- The `off_diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.off_diag.card / 2`.
This is because every element `⟦(x, y)⟧` of `sym2 α` not on the diagonal comes from exactly two
pairs: `(x, y)` and `(y, x)`. -/
lemma card_image_off_diag (s : finset α) :
  (s.off_diag.image quotient.mk).card = s.card.choose 2 :=
by rw [nat.choose_two_right, mul_tsub, mul_one, ←off_diag_card,
  nat.div_eq_of_eq_mul_right zero_lt_two (two_mul_card_image_off_diag s).symm]

lemma card_subtype_diag [fintype α] :
  card {a : sym2 α // a.is_diag} = card α :=
begin
  convert card_image_diag (univ : finset α),
  rw [fintype.card_of_subtype, ←filter_image_quotient_mk_is_diag],
  rintro x,
  rw [mem_filter, univ_product_univ, mem_image],
  obtain ⟨a, ha⟩ := quotient.exists_rep x,
  exact and_iff_right ⟨a, mem_univ _, ha⟩,
end

lemma card_subtype_not_diag [fintype α] :
  card {a : sym2 α // ¬a.is_diag} = (card α).choose 2 :=
begin
  convert card_image_off_diag (univ : finset α),
  rw [fintype.card_of_subtype, ←filter_image_quotient_mk_not_is_diag],
  rintro x,
  rw [mem_filter, univ_product_univ, mem_image],
  obtain ⟨a, ha⟩ := quotient.exists_rep x,
  exact and_iff_right ⟨a, mem_univ _, ha⟩,
end

protected lemma card [fintype α] :
  card (sym2 α) = card α * (card α + 1) / 2 :=
by rw [←fintype.card_congr (@equiv.sum_compl _ is_diag (sym2.is_diag.decidable_pred α)),
  fintype.card_sum, card_subtype_diag, card_subtype_not_diag, nat.choose_two_right, add_comm,
  ←nat.triangle_succ, nat.succ_sub_one, mul_comm]

end sym2
