/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.basic

/-!
# The powerset of a multiset
-/

namespace multiset
open list

variables {α : Type*}

/-! ### powerset -/

/-- A helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists_aux`), as multisets. -/
def powerset_aux (l : list α) : list (multiset α) :=
0 :: sublists_aux l (λ x y, x :: y)

theorem powerset_aux_eq_map_coe {l : list α} :
  powerset_aux l = (sublists l).map coe :=
by simp [powerset_aux, sublists];
   rw [← show @sublists_aux₁ α (multiset α) l (λ x, [↑x]) =
              sublists_aux l (λ x, list.cons ↑x),
         from sublists_aux₁_eq_sublists_aux _ _,
       sublists_aux_cons_eq_sublists_aux₁,
       ← bind_ret_eq_map, sublists_aux₁_bind]; refl

@[simp] theorem mem_powerset_aux {l : list α} {s} :
  s ∈ powerset_aux l ↔ s ≤ ↑l :=
quotient.induction_on s $
by simp [powerset_aux_eq_map_coe, subperm, and.comm]

/-- Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets. -/
def powerset_aux' (l : list α) : list (multiset α) := (sublists' l).map coe

theorem powerset_aux_perm_powerset_aux' {l : list α} :
  powerset_aux l ~ powerset_aux' l :=
by rw powerset_aux_eq_map_coe; exact (sublists_perm_sublists' _).map _

@[simp] theorem powerset_aux'_nil : powerset_aux' (@nil α) = [0] := rfl

@[simp] theorem powerset_aux'_cons (a : α) (l : list α) :
  powerset_aux' (a::l) = powerset_aux' l ++ list.map (cons a) (powerset_aux' l) :=
by simp [powerset_aux']; refl

theorem powerset_aux'_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  powerset_aux' l₁ ~ powerset_aux' l₂ :=
begin
  induction p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂, {simp},
  { simp, exact IH.append (IH.map _) },
  { simp, apply perm.append_left,
    rw [← append_assoc, ← append_assoc,
        (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)],
    exact perm_append_comm.append_right _ },
  { exact IH₁.trans IH₂ }
end

theorem powerset_aux_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  powerset_aux l₁ ~ powerset_aux l₂ :=
powerset_aux_perm_powerset_aux'.trans $
(powerset_aux'_perm p).trans powerset_aux_perm_powerset_aux'.symm

/-- The power set of a multiset. -/
def powerset (s : multiset α) : multiset (multiset α) :=
quot.lift_on s
  (λ l, (powerset_aux l : multiset (multiset α)))
  (λ l₁ l₂ h, quot.sound (powerset_aux_perm h))

theorem powerset_coe (l : list α) :
  @powerset α l = ((sublists l).map coe : list (multiset α)) :=
congr_arg coe powerset_aux_eq_map_coe

@[simp] theorem powerset_coe' (l : list α) :
  @powerset α l = ((sublists' l).map coe : list (multiset α)) :=
quot.sound powerset_aux_perm_powerset_aux'

@[simp] theorem powerset_zero : @powerset α 0 = {0} := rfl

@[simp] theorem powerset_cons (a : α) (s) :
  powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s) :=
quotient.induction_on s $ λ l, by simp; refl

@[simp] theorem mem_powerset {s t : multiset α} :
  s ∈ powerset t ↔ s ≤ t :=
quotient.induction_on₂ s t $ by simp [subperm, and.comm]

theorem map_single_le_powerset (s : multiset α) :
  s.map singleton ≤ powerset s :=
quotient.induction_on s $ λ l, begin
  simp only [powerset_coe, quot_mk_to_coe, coe_le, coe_map],
  show l.map (coe ∘ list.ret) <+~ (sublists l).map coe,
  rw ← list.map_map,
  exact ((map_ret_sublist_sublists _).map _).subperm
end

@[simp] theorem card_powerset (s : multiset α) :
  card (powerset s) = 2 ^ card s :=
quotient.induction_on s $ by simp

theorem revzip_powerset_aux {l : list α} ⦃x⦄
  (h : x ∈ revzip (powerset_aux l)) : x.1 + x.2 = ↑l :=
begin
  rw [revzip, powerset_aux_eq_map_coe, ← map_reverse, zip_map, ← revzip] at h,
  simp at h, rcases h with ⟨l₁, l₂, h, rfl, rfl⟩,
  exact quot.sound (revzip_sublists _ _ _ h)
end

theorem revzip_powerset_aux' {l : list α} ⦃x⦄
  (h : x ∈ revzip (powerset_aux' l)) : x.1 + x.2 = ↑l :=
begin
  rw [revzip, powerset_aux', ← map_reverse, zip_map, ← revzip] at h,
  simp at h, rcases h with ⟨l₁, l₂, h, rfl, rfl⟩,
  exact quot.sound (revzip_sublists' _ _ _ h)
end

theorem revzip_powerset_aux_lemma [decidable_eq α] (l : list α)
  {l' : list (multiset α)} (H : ∀ ⦃x : _ × _⦄, x ∈ revzip l' → x.1 + x.2 = ↑l) :
  revzip l' = l'.map (λ x, (x, ↑l - x)) :=
begin
  have : forall₂ (λ (p : multiset α × multiset α) (s : multiset α), p = (s, ↑l - s))
    (revzip l') ((revzip l').map prod.fst),
  { rw forall₂_map_right_iff,
    apply forall₂_same, rintro ⟨s, t⟩ h,
    dsimp, rw [← H h, add_sub_cancel_left] },
  rw [← forall₂_eq_eq_eq, forall₂_map_right_iff], simpa
end

theorem revzip_powerset_aux_perm_aux' {l : list α} :
  revzip (powerset_aux l) ~ revzip (powerset_aux' l) :=
begin
  haveI := classical.dec_eq α,
  rw [revzip_powerset_aux_lemma l revzip_powerset_aux,
      revzip_powerset_aux_lemma l revzip_powerset_aux'],
  exact powerset_aux_perm_powerset_aux'.map _
end

theorem revzip_powerset_aux_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  revzip (powerset_aux l₁) ~ revzip (powerset_aux l₂) :=
begin
  haveI := classical.dec_eq α,
  simp [λ l:list α, revzip_powerset_aux_lemma l revzip_powerset_aux, coe_eq_coe.2 p],
  exact (powerset_aux_perm p).map _
end

/-! ### powerset_len -/

/-- Helper function for `powerset_len`. Given a list `l`, `powerset_len_aux n l` is the list
of sublists of length `n`, as multisets. -/
def powerset_len_aux (n : ℕ) (l : list α) : list (multiset α) :=
sublists_len_aux n l coe []

theorem powerset_len_aux_eq_map_coe {n} {l : list α} :
  powerset_len_aux n l = (sublists_len n l).map coe :=
by rw [powerset_len_aux, sublists_len_aux_eq, append_nil]

@[simp] theorem mem_powerset_len_aux {n} {l : list α} {s} :
  s ∈ powerset_len_aux n l ↔ s ≤ ↑l ∧ card s = n :=
quotient.induction_on s $
by simp [powerset_len_aux_eq_map_coe, subperm]; exact
  λ l₁, ⟨λ ⟨l₂, ⟨s, e⟩, p⟩, ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
    λ ⟨⟨l₂, p, s⟩, e⟩, ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩

@[simp] theorem powerset_len_aux_zero (l : list α) :
  powerset_len_aux 0 l = [0] :=
by simp [powerset_len_aux_eq_map_coe]

@[simp] theorem powerset_len_aux_nil (n : ℕ) :
  powerset_len_aux (n+1) (@nil α) = [] := rfl

@[simp] theorem powerset_len_aux_cons (n : ℕ) (a : α) (l : list α) :
  powerset_len_aux (n+1) (a::l) =
  powerset_len_aux (n+1) l ++ list.map (cons a) (powerset_len_aux n l) :=
by simp [powerset_len_aux_eq_map_coe]; refl

theorem powerset_len_aux_perm {n} {l₁ l₂ : list α} (p : l₁ ~ l₂) :
  powerset_len_aux n l₁ ~ powerset_len_aux n l₂ :=
begin
  induction n with n IHn generalizing l₁ l₂, {simp},
  induction p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂, {refl},
  { simp, exact IH.append ((IHn p).map _) },
  { simp, apply perm.append_left,
    cases n, {simp, apply perm.swap},
    simp,
    rw [← append_assoc, ← append_assoc,
        (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)],
    exact perm_append_comm.append_right _ },
  { exact IH₁.trans IH₂ }
end

/-- `powerset_len n s` is the multiset of all submultisets of `s` of length `n`. -/
def powerset_len (n : ℕ) (s : multiset α) : multiset (multiset α) :=
quot.lift_on s
  (λ l, (powerset_len_aux n l : multiset (multiset α)))
  (λ l₁ l₂ h, quot.sound (powerset_len_aux_perm h))

theorem powerset_len_coe' (n) (l : list α) :
  @powerset_len α n l = powerset_len_aux n l := rfl

theorem powerset_len_coe (n) (l : list α) :
  @powerset_len α n l = ((sublists_len n l).map coe : list (multiset α)) :=
congr_arg coe powerset_len_aux_eq_map_coe

@[simp] theorem powerset_len_zero_left (s : multiset α) :
  powerset_len 0 s = {0} :=
quotient.induction_on s $ λ l, by simp [powerset_len_coe']; refl

@[simp] theorem powerset_len_zero_right (n : ℕ) :
  @powerset_len α (n + 1) 0 = 0 := rfl

@[simp] theorem powerset_len_cons (n : ℕ) (a : α) (s) :
  powerset_len (n + 1) (a ::ₘ s) =
  powerset_len (n + 1) s + map (cons a) (powerset_len n s) :=
quotient.induction_on s $ λ l, by simp [powerset_len_coe']; refl

@[simp] theorem mem_powerset_len {n : ℕ} {s t : multiset α} :
  s ∈ powerset_len n t ↔ s ≤ t ∧ card s = n :=
quotient.induction_on t $ λ l, by simp [powerset_len_coe']

@[simp] theorem card_powerset_len (n : ℕ) (s : multiset α) :
  card (powerset_len n s) = nat.choose (card s) n :=
quotient.induction_on s $ by simp [powerset_len_coe]

theorem powerset_len_le_powerset (n : ℕ) (s : multiset α) :
  powerset_len n s ≤ powerset s :=
quotient.induction_on s $ λ l, by simp [powerset_len_coe]; exact
  ((sublists_len_sublist_sublists' _ _).map _).subperm

theorem powerset_len_mono (n : ℕ) {s t : multiset α} (h : s ≤ t) :
  powerset_len n s ≤ powerset_len n t :=
le_induction_on h $ λ l₁ l₂ h, by simp [powerset_len_coe]; exact
  ((sublists_len_sublist_of_sublist _ h).map _).subperm

end multiset
