open fin nat

lemma lt_succ_of_lt {a b : nat} (h : a < b) : a < b + 1 := lt_add_of_lt_of_pos h one_pos

def raise_fin {n : ℕ} (k : fin n) : fin (n + 1) := ⟨val k, lt_succ_of_lt (is_lt k)⟩

lemma eq_of_lt_succ_of_not_lt {a b : ℕ} (h1 : a < b + 1) (h2 : ¬ a < b) : a = b :=
have h3 : a ≤ b, from le_of_lt_succ h1,
or.elim (eq_or_lt_of_not_lt h2) (λ h, h) (λ h, absurd h (not_lt_of_ge h3))


section
set_option eqn_compiler.zeta true
instance fin_dec : Π (n : ℕ) (P : fin n → Prop) [hd : decidable_pred P], decidable (∀ k : fin n, P k)
| 0 P hd := decidable.is_true (λ k, absurd (fin.is_lt k) (not_lt_zero _))
| (k+1) P hd :=
  match hd (fin.mk k (lt_succ_self _)) with
  | decidable.is_false h := decidable.is_false (λ h1, h (h1 _))
  | decidable.is_true h :=
    let lP := (λ l : fin k, P (raise_fin l)) in
    have lPd : decidable_pred lP, from
      assume l, decidable.rec_on (hd (raise_fin l)) decidable.is_false decidable.is_true,
    match @fin_dec k lP lPd with
    | decidable.is_false h1 := decidable.is_false (λ h2, h1 (λ l, h2 _))
    | decidable.is_true h1 := decidable.is_true (λ l, fin.rec_on l
       (λ val is_lt, if hval : val < k then
         suffices lP (fin.mk val hval), from this,
         h1 _
       else
         have hvk : val = k, from eq_of_lt_succ_of_not_lt is_lt hval,
         begin revert is_lt, rw hvk, intro, apply h end))
    end
  end
end

instance fin_to_nat (n : ℕ) : has_coe (fin n) nat := ⟨fin.val⟩
instance fin_to_int (n : ℕ) : has_coe (fin n) int := ⟨λ k, ↑(fin.val k)⟩
