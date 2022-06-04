import data.nary_fraction.basic
import data.set.intervals.nontrivial
import data.fin.tuple.monotone
import order.conditionally_complete_lattice

/-!
-/

variables {α : Type*}

open set

namespace nary_fraction

structure encoding (N : ℕ) (α : Type*) [preorder α] :=
(next : nontrivial_interval α → fin N → nontrivial_interval α)
(right_le_left' : ∀ I ⦃i j : fin N⦄, (i + 1 : ℕ) = j → (next I i).right ≤ (next I j).left)
(le_left' : ∀ (I : nontrivial_interval α) (i : fin N), (i : ℕ) = 0 → I.left ≤ (next I i).left)
(right_le' : ∀ I (i : fin N), (i + 1 : ℕ) = N → (next I i).right ≤ I.right)

namespace encoding

section preorder

variables [preorder α] {N : ℕ} (e : encoding N α) {i j : fin N} {I : nontrivial_interval α}
  {x y : nary_fraction N}

lemma right_le_left (I : nontrivial_interval α) (h : i < j) :
  (e.next I i).right ≤ (e.next I j).left :=
begin
  cases j with j hj,
  change (i + 1 : ℕ) ≤ j at h,
  revert hj,
  refine nat.le_induction _ _ _ h,
  { exact λ hj, e.right_le_left' I rfl },
  { clear h j, intros j hij ihj hjN,
    calc (e.next I i).right ≤ (e.next I ⟨j, j.lt_succ_self.trans hjN⟩).left : ihj _
    ... ≤ (e.next I ⟨j, j.lt_succ_self.trans hjN⟩).right : (nontrivial_interval.left_lt_right _).le
    ... ≤ (e.next I ⟨j + 1, hjN⟩).left : e.right_le_left' _ rfl }
end

lemma strict_mono_left (I : nontrivial_interval α) : strict_mono (λ i, (e.next I i).left) :=
λ i j h, (e.next I i).left_lt_right.trans_le $ e.right_le_left I h

lemma left_lt_left (I : nontrivial_interval α) :
  (e.next I i).left < (e.next I j).left ↔ i < j :=
(e.strict_mono_left I).lt_iff_lt

lemma left_le_left (I : nontrivial_interval α) :
  (e.next I i).left ≤ (e.next I j).left ↔ i ≤ j :=
(e.strict_mono_left I).le_iff_le

lemma strict_mono_right (I : nontrivial_interval α) : strict_mono (λ i, (e.next I i).right) :=
λ i j h, (e.right_le_left I h).trans_lt (e.next I j).left_lt_right

lemma right_lt_right (I : nontrivial_interval α) :
  (e.next I i).right < (e.next I j).right ↔ i < j :=
(e.strict_mono_right I).lt_iff_lt

lemma right_le_right (I : nontrivial_interval α) :
  (e.next I i).right ≤ (e.next I j).right ↔ i ≤ j :=
(e.strict_mono_right I).le_iff_le

lemma right_lt_left (I : nontrivial_interval α) (h : (i + 1 : ℕ) < j) :
  (e.next I i).right < (e.next I j).left :=
calc (e.next I i).right ≤ (e.next I ⟨i + 1, h.trans j.is_lt⟩).left :
  e.right_le_left _ (nat.lt_succ_self _)
... < (e.next I j).left : (e.left_lt_left I).2 h

lemma next_le (I : nontrivial_interval α) (i : fin N) : e.next I i ≤ I :=
begin
  rcases le_iff_exists_add'.1 (nat.succ_le_iff.2 $ fin.pos_iff_nonempty.2 ⟨i⟩) with ⟨N, rfl⟩,
  exact ⟨(e.le_left' I 0 rfl).trans $ (e.left_le_left _).2 (fin.zero_le i),
    ((e.right_le_right _).2 (fin.le_last i)).trans $ e.right_le' I _ rfl⟩
end

lemma right_lt (I : nontrivial_interval α) (hi : (i + 1 : ℕ) ≠ N) :
  (e.next I i).right < I.right :=
calc (e.next I i).right < (e.next I ⟨i + 1, lt_of_le_of_ne (nat.succ_le_iff.2 i.is_lt) hi⟩).right :
  (e.right_lt_right _).2 (nat.lt_succ_self i)
... ≤ I.right : (e.next_le I _).2

lemma lt_left (I : nontrivial_interval α) (hi : (i : ℕ) ≠ 0) :
  I.left < (e.next I i).left :=
calc I.left ≤ (e.next I ⟨i - 1, (nat.sub_le _ _).trans_lt i.is_lt⟩).left : (e.next_le I _).1
... < (e.next I i).left : (e.left_lt_left _).2 (nat.pred_lt hi)

def of_seq' (f : nontrivial_interval α → fin (N + 1) ↪o α)
  (hle₀ : ∀ I : nontrivial_interval α, I.left ≤ f I 0) (hle : ∀ I, f I (fin.last _) ≤ I.right) :
  encoding N α :=
{ next := λ I i, ⟨f I i.cast_succ, f I i.succ, (f I).strict_mono i.cast_succ_lt_succ⟩,
  right_le_left' := λ I i j h, le_of_eq $ congr_arg (f I) $ by { ext, simpa },
  le_left' := λ I i hi,
    have H : i.cast_succ = 0, from fin.ext hi,
    by simpa only [H] using hle₀ I,
  right_le' := λ I i hi,
    have H : i.succ = fin.last N, by { ext, simpa },
    by simpa only [H] using hle I }

def of_seq (f : Π I : nontrivial_interval α, fin (N + 1) ↪o I.Icc) :
  encoding N α :=
of_seq' (λ I, (f I).trans (order_embedding.subtype _)) (λ I, (f I 0).2.1) (λ I, (f I _).2.2)

instance [densely_ordered α] : nonempty (encoding N α) :=
begin
  choose f hf using λ I : nontrivial_interval α, nat.exists_strict_mono I.Ioo,
  refine ⟨of_seq $ λ I, (fin.coe_embedding _).trans _⟩,
  exact order_embedding.of_strict_mono (λ i, inclusion Ioo_subset_Icc_self (f I i)) (hf I)
end

def nth (I : nontrivial_interval α) (x : nary_fraction N) : ℕ → nontrivial_interval α
| 0 := I
| (n + 1) := e.next (nth n) (x n)

@[simp] lemma nth_zero (I : nontrivial_interval α) (x : nary_fraction N) : e.nth I x 0 = I := rfl

lemma nth_succ (I : nontrivial_interval α) (x : nary_fraction N) (n : ℕ) :
  e.nth I x (n + 1) = e.next (e.nth I x n) (x n) :=
rfl

lemma nth_succ' (I : nontrivial_interval α) (x : nary_fraction N) (n : ℕ) :
  e.nth I x (n + 1) = e.nth (e.next I (x 0)) x.tail n :=
begin
  induction n with n ihn,
  { refl },
  { rw [nth_succ, ihn, nth_succ, tail_apply] }
end

lemma antitone_nth : antitone (e.nth I x) :=
antitone_nat_of_succ_le $ λ n, e.next_le _ _

lemma nth_congr {n} (h : ∀ k < n, x k = y k) : e.nth I x n = e.nth I y n :=
begin
  induction n with n ihn, { refl },
  rw [nth_succ, nth_succ, ihn, h],
  exacts [n.lt_succ_self, λ k hk, h k $ hk.trans n.lt_succ_self]
end

lemma exists_nth_right_le_nth_left (I : nontrivial_interval α) (h : x < y) :
  ∃ n, (e.nth I x n).right ≤ (e.nth I y n).left :=
begin
  rcases h with ⟨n, hn_eq, hn⟩,
  use n + 1,
  rw [nth_succ, nth_succ, e.nth_congr hn_eq],
  exact e.right_le_left _ hn
end

lemma exists_nth_right_lt_nth_left (I : nontrivial_interval α) (h : ⟦x⟧ < ⟦y⟧) :
  ∃ n, (e.nth I x n).right < (e.nth I y n).left :=
begin
  rw [mkq_lt_mkq'] at h,
  rcases h with ⟨⟨n, hn_eq, hn⟩, ht⟩,
  rw [fin.lt_iff_coe_lt_coe, nat.lt_iff_add_one_le, le_iff_eq_or_lt] at hn,
  cases hn,
  { obtain ⟨m, hnm, hxym⟩ : ∃ m > n, (x m + 1 : ℕ) ≠ N ∨ (y m : ℕ) ≠ 0,
    { contrapose! ht,
      exact ⟨n, hn_eq, hn, λ m hm, (ht m hm).1, λ m hm, (ht m hm).2⟩ },
    use m + 1,
    have : (e.nth I x m).right ≤ (e.nth I y m).left,
    calc (e.nth I x m).right ≤ (e.nth I x (n + 1)).right : (e.antitone_nth hnm).2
    ... ≤ (e.nth I y (n + 1)).left :
      begin
        rw [nth_succ, nth_succ, e.nth_congr hn_eq],
        apply e.right_le_left,
        rw [fin.lt_iff_coe_lt_coe, ← hn],
        exact nat.lt_succ_self _
      end
    ... ≤ (e.nth I y m).left : (e.antitone_nth hnm).1,
    cases hxym with hxm hym,
    { calc (e.nth I x (m + 1)).right < (e.nth I x m).right : e.right_lt _ hxm
      ... ≤ (e.nth I y m).left : this
      ... ≤ (e.nth I y (m + 1)).left : (e.next_le _ _).1 },
    { calc (e.nth I x (m + 1)).right ≤ (e.nth I x m).right : (e.next_le _ _).2
      ... ≤ (e.nth I y m).left : this
      ... < (e.nth I y (m + 1)).left : e.lt_left _ hym } },
  { refine ⟨n + 1, _⟩,
    rw [nth_succ, nth_succ, e.nth_congr hn_eq],
    exact e.right_lt_left _ hn }
end

def cantor (I : nontrivial_interval α) : set α := ⋃ x, ⋂ n, (e.nth I x n).Icc

lemma cantor_rec (I : nontrivial_interval α) : e.cantor I = ⋃ i, e.cantor (e.next I i) :=
calc (⋃ x, ⋂ n, (e.nth I x n).Icc)
    = ⋃ x : fin N × nary_fraction N, ⋂ n, (e.nth I (cons x.1 x.2) n).Icc :
  (Union_congr_of_surjective cons_equiv cons_equiv.surjective (λ x, rfl)).symm
... = ⋃ i x, ⋂ n, (e.nth I (cons i x) n).Icc : supr_prod
... = ⋃ i x, ⋂ n, (e.nth I (cons i x) (n + 1)).Icc :
  Union₂_congr $ λ i x, eq.symm $
    (nontrivial_interval.Icc.monotone.comp_antitone e.antitone_nth).Inter_nat_add 1
... = ⋃ i x, ⋂ n, (e.nth (e.next I i) x n).Icc :
  Union₂_congr $ λ i x, by simp only [nth_succ', cons_apply_zero, tail_cons]

lemma cantor_eq_Inter (I : nontrivial_interval α) :
  e.cantor I = ⋂ n, ⋃ x, (e.nth I x n).Icc :=
begin
  refine subset.antisymm Union_Inter_subset _,
  have : ∀ I, (⋂ n, ⋃ x, (e.nth I x n).Icc) = ⋃ i, ⋂ n, ⋃ x, (e.nth (e.next I i) x n).Icc,
  { intro I,
    have : ∀ {I}, antitone (λ n, ⋃ x, (e.nth I x n).Icc),
      from λ I m n h, Union_mono (λ x, nontrivial_interval.Icc.mono $ e.antitone_nth h),
    calc (⋂ n, ⋃ x, (e.nth I x n).Icc) = ⋂ n, ⋃ x, (e.nth I x (n + 1)).Icc :
      (this.Inter_nat_add 1).symm
    ... = ⋂ n, ⋃ x : fin N × nary_fraction N, (e.nth I (cons x.1 x.2) (n + 1)).Icc :
      Inter_congr $ λ n,
        (Union_congr_of_surjective cons_equiv cons_equiv.surjective (λ _, rfl)).symm
    ... = ⋂ n, ⋃ i x, (e.nth I (cons i x) (n + 1)).Icc : Inter_congr $ λ n, supr_prod
    ... = ⋂ n, ⋃ i x, (e.nth (e.next I i) x n).Icc :
      by simp only [nth_succ', cons_apply_zero, tail_cons]
    ... = ⋃ i, ⋂ n, ⋃ x, (e.nth (e.next I i) x n).Icc :
      Inter_Union_of_antitone (λ i, this) },
  
end

end preorder

section conditionally_complete_lattice

variables [conditionally_complete_lattice α] {N : ℕ} (e : encoding N α) {i j : fin N}
  {I : nontrivial_interval α} {x y : nary_fraction N}

def decode (I : nontrivial_interval α) (x : nary_fraction N) : α :=
⨆ n, (e.nth I x n).left

lemma decode_mem_Inter_Icc (I : nontrivial_interval α) (x : nary_fraction N) :
  e.decode I x ∈ ⋂ n, (e.nth I x n).Icc :=
csupr_mem_Inter_Icc_of_antitone_nontrivial_interval e.antitone_nth

lemma decode_mem_Icc (I : nontrivial_interval α) (x : nary_fraction N) (n : ℕ) :
  e.decode I x ∈ (e.nth I x n).Icc :=
by convert mem_Inter.1 (e.decode_mem_Inter_Icc I x) n

lemma decode_mono : monotone (e.decode I) :=
begin
  refine monotone_iff_forall_lt.2 (λ x y hxy, _),
  rcases e.exists_nth_right_le_nth_left I hxy with ⟨n, hn⟩,
  calc e.decode I x ≤ (e.nth I x n).right : (e.decode_mem_Icc I x n).2
  ... ≤ (e.nth I y n).left : hn
  ... ≤ e.decode I y : (e.decode_mem_Icc I y n).1
end

lemma decode_lt_of_mkq_lt_mkq (h : ⟦x⟧ < ⟦y⟧) : e.decode I x < e.decode I y :=
begin
  rcases e.exists_nth_right_lt_nth_left I h with ⟨n, hn⟩,
  calc e.decode I x ≤ (e.nth I x n).right : (e.decode_mem_Icc I x n).2
  ... < (e.nth I y n).left : hn
  ... ≤ e.decode I y : (e.decode_mem_Icc I y n).1
end

lemma strict_mono_decode_out :
  strict_mono (λ x : quotient nary_fraction.setoid, e.decode I x.out) :=
λ x y h, e.decode_lt_of_mkq_lt_mkq $ by rwa [x.out_eq, y.out_eq]

end conditionally_complete_lattice

section linear_order


variables [linear_order α] {N : ℕ} (e : encoding N α) {i j : fin N} {I : nontrivial_interval α}
  {x y : nary_fraction N}

end linear_order

end encoding

variable (choice : Π I : nontrivial_interval α, I.Ioo)

/-- Given a choice function `choice : Π I : nontrivial_interval α, I.Ioo`, a boolean value `b`, and
a nontrivial interval `I`, returns either `[I.left, choice I]` (if `b = ff`), or
`[choice I, I.right]` (if `b = tt`). -/
def next_interval (b : bool) (I : nontrivial_interval α) : nontrivial_interval α :=
cond b ⟨choice I, I.right, (choice I).2.2⟩ ⟨I.left, choice I, (choice I).2.1⟩

lemma next_interval_lt (I : nontrivial_interval α) :
  ∀ b, next_interval choice b I < I
| ff := ⟨⟨le_rfl, (choice I).2.2.le⟩, λ h, h.2.not_lt (choice I).2.2⟩
| tt := ⟨⟨(choice I).2.1.le, le_rfl⟩, λ h, h.1.not_lt (choice I).2.1⟩

/-- Given a choice function `choice : Π I : nontrivial_interval α, I.Ioo`, a binary fraction `x`
and an initial interval `I`, returns the strictly antitone sequence of nontrivial intervals given by
`nth_interval choice x I 0 = I` and
`nth_interval choice x I (n + 1) = next_interval choice (x n) (nth_interval choice x I n)`. -/
def nth_interval (x : binary_fraction) (I : nontrivial_interval α) : ℕ → nontrivial_interval α
| 0 := I
| (n + 1) := next_interval choice (x n) (nth_interval n)

@[simp] lemma nth_interval_zero (x : binary_fraction) (I : nontrivial_interval α) :
  nth_interval choice x I 0 = I := rfl

lemma nth_interval_succ (x : binary_fraction) (I : nontrivial_interval α) (n : ℕ) :
  nth_interval choice x I (n + 1) = next_interval choice (x n) (nth_interval choice x I n) :=
rfl

lemma nth_interval_succ' (x : binary_fraction) (I : nontrivial_interval α) (n : ℕ) :
  nth_interval choice x I (n + 1) =
    nth_interval choice (λ n, x (n + 1)) (next_interval choice (x 0) I) n :=
begin
  induction n with n ihn generalizing I, { refl },
  rw [nth_interval_succ, nat.succ_eq_add_one, ihn, nth_interval_succ]
end

@[simp] lemma nth_interval_bot_left (I : nontrivial_interval α) (n : ℕ) :
  (nth_interval choice ⊥ I n).left = I.left :=
by induction n generalizing I; simp [nth_interval, next_interval, *]

lemma strict_anti_nth_interval (x : binary_fraction) (I : nontrivial_interval α) :
  strict_anti (x.nth_interval choice I) :=
strict_anti_nat_of_succ_lt $ λ n, next_interval_lt _ _ _

lemma antitone_nth_interval (x : binary_fraction) (I : nontrivial_interval α) :
  antitone (x.nth_interval choice I) :=
(strict_anti_nth_interval choice x I).antitone

lemma nth_interval_congr (n : ℕ) (h : ∀ k < n, x k = y k) (I : nontrivial_interval α) :
  x.nth_interval choice I n = y.nth_interval choice I n :=
begin
  induction n with n ihn, { refl },
  rw [nth_interval, nth_interval, ihn, h n n.lt_succ_self],
  exact λ k hk, h k (hk.trans n.lt_succ_self)
end

end preorder

section conditionally_complete_lattice

variables [conditionally_complete_lattice α] (choice : Π I : nontrivial_interval α, I.Ioo)

/-- “Decode” an element of a conditionally complete lattice `α` encoded by `x : binary_fraction`
given a choice function and an initial interval. In the case of real numbers,
`I = ⟨0, 1, zero_lt_one⟩`, and `(choice J : ℝ) = (J.left + J.right) / 2`, this corresponds to the
classical binary representation of a real number. -/
def decode (I : nontrivial_interval α) (x : binary_fraction) : α :=
⨆ n, (x.nth_interval choice I n).left

@[simp] lemma decode_bot (I : nontrivial_interval α) :
  decode choice I ⊥ = I.left :=
by simp [decode]

lemma decode_mem_Inter_Icc (I : nontrivial_interval α) (x : binary_fraction) :
  x.decode choice I ∈ ⋂ n, (x.nth_interval choice I n).Icc :=
csupr_mem_Inter_Icc_of_antitone_nontrivial_interval (x.antitone_nth_interval choice I)

lemma decode_mem_Icc (I : nontrivial_interval α) (x : binary_fraction) (n : ℕ) :
  x.decode choice I ∈ (x.nth_interval choice I n).Icc :=
by convert mem_Inter.1 (x.decode_mem_Inter_Icc choice I) n

lemma decode_lt_of_lt_not_eqv (I : nontrivial_interval α) (h₁ : x < y) (h₂ : ¬ x ≈ y) :
  x.decode choice I < y.decode choice I :=
begin
  rcases h₁ with ⟨N, lt_N, xy_N⟩,
  rw bool.lt_iff at xy_N,
  rcases em (∃ n > N, x n = ff) with ⟨n, hNn, hxn⟩|Hx,
  { calc x.decode choice I ≤ (x.nth_interval choice I (n + 1)).right :
      (x.decode_mem_Icc choice I _).2
    ... < (x.nth_interval choice I n).right :
      by { rw [nth_interval, hxn], exact (choice _).2.2 }
    ... ≤ (x.nth_interval choice I (N + 1)).right :
      nontrivial_interval.monotone_right $ antitone_nth_interval _ _ _ hNn
    ... = (y.nth_interval choice I (N + 1)).left :
      by { rw [nth_interval, nth_interval, xy_N.1, xy_N.2, nth_interval_congr _ _ lt_N], refl }
    ... ≤ y.decode choice I : (y.decode_mem_Icc choice I _).1 },
  { rcases em (∃ n > N, y n = tt) with ⟨n, hNn, hyn⟩|Hy,
    { calc x.decode choice I ≤ (x.nth_interval choice I (N + 1)).right :
        (x.decode_mem_Icc choice I _).2
      ... = (y.nth_interval choice I (N + 1)).left :
        by { rw [nth_interval, nth_interval, xy_N.1, xy_N.2, nth_interval_congr _ _ lt_N], refl }
      ... ≤ (y.nth_interval choice I n).left :
        nontrivial_interval.antitone_left $ antitone_nth_interval _ _ _ hNn
      ... < (y.nth_interval choice I (n + 1)).left :
        by { rw [nth_interval, hyn], exact (choice _).2.1 }
      ... ≤ y.decode choice I : (y.decode_mem_Icc choice I _).1 },
    suffices : tail_rel x y, from (h₂ this.eqv).elim,
    push_neg at Hx Hy,
    exact ⟨N, lt_N, xy_N.1, xy_N.2, λ i hi, eq_tt_of_ne_ff (Hx i hi),
      λ i hi, eq_ff_of_ne_tt (Hy i hi)⟩ }
end

lemma strict_mono_decode_out (I : nontrivial_interval α) :
  strict_mono (λ x : quotient binary_fraction.setoid, x.out.decode choice I) :=
λ x y h, decode_lt_of_lt_not_eqv _ _ h $ λ H, h.ne $ quotient.out_eqv_out.1 H

lemma left_lt_decode (I : nontrivial_interval α) {x : binary_fraction} (hx : x ≠ ⊥) :
  I.left < decode choice I x :=
decode_bot choice I ▸ decode_lt_of_lt_not_eqv _ _ hx.bot_lt _

end conditionally_complete_lattice

section linear_order

variables [linear_order α] (choice : Π I : nontrivial_interval α, I.Ioo)

def encode : Π I : nontrivial_interval α, I.Ioc → binary_fraction
| I x 0 := (choice I : α) < x
| I x (n + 1) :=
  if h : (choice I : α) < x
  then encode (next_interval choice tt I) ⟨x, h, x.2.2⟩ n
  else encode (next_interval choice ff I) ⟨x, x.2.1, not_lt.1 h⟩ n

lemma mem_nth_interval_encode (I : nontrivial_interval α) (x : I.Ioc) (n : ℕ) :
  (x : α) ∈ (nth_interval choice (encode choice I x) I n).Ioc :=
begin
  induction n with n ihn generalizing I x,
  { exact x.2 },
  { cases lt_or_le (choice I : α) x with hlt hle,
    { simp only [nth_interval_succ', encode, hlt, to_bool_true_eq_tt, dif_pos],
      exact ihn _ _ },
    { simp only [nth_interval_succ', encode, hle.not_lt, to_bool_false_eq_ff, dif_neg,
        not_false_iff],
      exact ihn _ _ } }
end

end linear_order

section conditionally_complete_linear_order

variables [conditionally_complete_linear_order α] (choice : Π I : nontrivial_interval α, I.Ioo)

lemma decode_encode_le (I : nontrivial_interval α) (x : I.Ioc) :
  decode choice I (encode choice I x) ≤ x :=
csupr_le $ λ n, (mem_nth_interval_encode choice I x n).1.le

lemma 

end conditionally_complete_linear_order
