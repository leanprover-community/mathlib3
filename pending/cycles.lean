import group_theory.perm group_theory.order_of_element data.zmod
#exit
variables {α : Type*} [decidable_eq α]
open equiv finset
namespace equiv.perm

instance [fintype α] : fintype (perm α) := sorry

def disjoint (f g : perm α) := ∀ x : α, f x = x ∨ g x = x

def is_cycle (f : perm α) := f ≠ 1 ∧ ∃ x, ∀ y, ∃ n : ℕ, (f ^ n) x = y

def cycle_of_aux (f : perm α) : Π (n : ℕ) (y : α), list α
| 0     y := []
| (n+1) y := y :: (cycle_of_aux n (f y))

lemma length_cycle_of_aux (f : perm α) (n : ℕ) : ∀ y : α, (cycle_of_aux f n y).length = n :=
by induction n; simp [cycle_of_aux, *]

@[simp] lemma nth_cycle_of_aux [fintype α] (f : perm α) : ∀ {n m : ℕ} (y : α)
  (hn : nat.succ m < (cycle_of_aux f n y).length),
  list.nth_le (cycle_of_aux f n y) (nat.succ m) hn =
  f (list.nth_le (cycle_of_aux f n y) m (nat.lt_of_succ_lt hn))
| 0     m     y hn := (nat.not_lt_zero _ hn).elim
| 1     0     y hn := (lt_irrefl _ hn).elim
| (n+2) 0     y hn := rfl
| (n+1) (m+1) y hn :=
  begin
    unfold cycle_of_aux list.nth_le,
    rw nth_cycle_of_aux,
    refl,
  end

@[simp] lemma nth_cycle_of_aux_eq_pow [fintype α] (f : perm α) : ∀ {n m : ℕ} (x : α)
  (hm : m < (cycle_of_aux f n x).length), (cycle_of_aux f n x).nth_le m hm = (f ^ m) x
| 0     m     := λ _ hm, absurd hm dec_trivial
| (n+1) 0     := λ _ _, rfl
| (n+1) (m+1) := λ x hm,
  by unfold cycle_of_aux list.nth_le; rw [nth_cycle_of_aux_eq_pow, pow_succ', mul_apply]

lemma exists_pow_apply_eq_self [fintype α] (f : perm α) (x : α) : ∃ n, n >0 ∧ (f ^ n) x = x :=
⟨order_of f, order_of_pos _, by rw pow_order_of_eq_one; refl⟩

def cycle_of_list [fintype α] (f : perm α) (x : α) : list α :=
cycle_of_aux f (nat.find (exists_pow_apply_eq_self f x)) x

lemma cycle_of_list_eq_cons [fintype α] (f : perm α) (x : α) : cycle_of_list f x =
  x :: cycle_of_aux f (nat.find (exists_pow_apply_eq_self f x) - 1) (f x) :=
begin
  unfold cycle_of_list,
  cases h : nat.find (exists_pow_apply_eq_self f x),
  { exact absurd h (nat.pos_iff_ne_zero.1 $ (nat.find_spec (exists_pow_apply_eq_self f x)).1) },
  { simp [cycle_of_aux] }
end

def cycle_length [fintype α] (f : perm α) (x : α) : ℕ := (cycle_of_list f x).length

lemma cycle_length_pos [fintype α] (f : perm α) (x : α) : cycle_length f x > 0 :=
by rw [cycle_length, cycle_of_list, length_cycle_of_aux];
  exact (nat.find_spec (exists_pow_apply_eq_self f x)).1

@[simp] lemma pow_cycle_length_apply [fintype α] (f : perm α) (x : α) : (f ^ cycle_length f x) x = x :=
by rw [cycle_length, cycle_of_list, length_cycle_of_aux];
  exact (nat.find_spec (exists_pow_apply_eq_self f x)).2

@[simp] lemma length_cycle_of_list [fintype α] (f : perm α) (x : α) :
  (cycle_of_list f x).length = cycle_length f x := rfl

@[simp] lemma nth_cycle_of_list_eq_pow [fintype α] (f : perm α) (x : α) {n : ℕ} (hn : n < cycle_length f x) :
  (cycle_of_list f x).nth_le n hn = (f ^ n) x := nth_cycle_of_aux_eq_pow _ _ hn

open list

def cycle_list_factors [fintype α] (f : perm α) : Π l : list α, list (list α)
| []       := []
| (x :: l) := let m := cycle_of_list f x in
  have wf : ((x :: l : list α).diff (cycle_of_list f x)).length < (x :: l : list α).length :=
  calc ((x :: l : list α).diff (cycle_of_list f x)).length =
    list.length (list.diff l (cycle_of_aux f (nat.find _ - 1) (f x))) :
    by rw [cycle_of_list_eq_cons, list.diff_cons, list.erase_cons_head]
  ... ≤ l.length : list.length_le_of_sublist (diff_sublist _ _)
   ... < (x :: l : list α).length : nat.lt_succ_self _,
  if f x = x then cycle_list_factors ((x :: l : list α).diff m)
  else m :: cycle_list_factors ((x :: l : list α).diff m)
using_well_founded {dec_tac := tactic.assumption,
  rel_tac := λ _ _ , `[exact ⟨_, measure_wf list.length⟩]}

meta instance [fintype α] [has_repr α] : has_repr (perm α) :=
⟨λ f, repr (cycle_list_factors f (quot.unquot (@univ α _).1))⟩

instance zmod_has_repr (n : ℕ+) : has_repr (zmod n) := fin.has_repr n

-- instance (n : ℕ+) : has_coe ℕ (zmod n) := by apply_instance

#eval (let p := 11 in let q := 3 in
       ({ to_fun := λ x : zmod ⟨p * q, dec_trivial⟩,
         (↑((x.1 % p * q) % (p * q) + x.1 / p : ℕ) : zmod ⟨p * q, dec_trivial⟩),
         inv_fun := sorry,
         left_inv := sorry,
         right_inv := sorry } : perm (zmod ⟨p * q, dec_trivial⟩)))

def list_to_perm : Π (l : list α), perm α
| []        := 1
| [x]       := 1
| (x::y::l) := swap x y * list_to_perm (y :: l)

@[simp] lemma list_to_perm_eq_swap (x y : α) : list_to_perm [x,y] = swap x y := rfl

lemma list_to_perm_pow {l : list α} {x : α} (h : (x :: l : list α).nodup) {n : ℕ}
  (hn : n < (x::l : list α).length) :
  (list_to_perm (x :: l) ^ n) x = (x :: l : list α).nth_le n hn :=
begin
  induction l with y l ih,
  { have hn : n = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ hn),
    subst hn,
    rw [list_to_perm, one_pow]; refl },
  rw [list_to_perm],


end

def cycle_of [fintype α] (f : perm α) (x : α) : perm α := list_to_perm (cycle_of_list f x)

@[simp] lemma cycle_of_apply_self [fintype α] (f : perm α) (x : α) : cycle_of f x x = f x :=
begin
  rw cycle_of,


end

lemma cycle_of_is_cycle [fintype α] (f : perm α) (x : α) (h : f x ≠ x) : is_cycle (cycle_of f x) :=
⟨begin end, begin end⟩

#eval list_to_perm ([1,2,3,4,3] : list (fin 5))

def list_to_cycle_append : Π (l₁ l₂ : list α), list_to_cycle_aux (l₁ ++ l₂) =
  list_to_cycle_aux l₁ ∘ list_to_cycle_aux l₂
| []      l₂ := rfl
| [a] l₂ := begin


end

lemma list_to_cycle_reverse : ∀ (l : list α) (x y w z : α), z ≠ x → z ≠ y → z ≠ w →
 list_to_cycle_aux (x :: l ++ [y]) (list_to_cycle_aux (x :: l ++ [w] : list α).reverse z) = z
| []     x y w z := λ hzx hzy, by simp [list_to_cycle_aux]; split_ifs; cc
| (a::l) x y w z := λ hzx hzy hzw,
list.reverse_rec_on l (by simp [list_to_cycle_aux]; split_ifs; cc)
(λ l b _, begin
  simp only [reverse_cons, reverse_append, nil_append, reverse_nil, cons_append],
  unfold list_to_cycle_aux,
  split_ifs,
  cc <|> simp [*, list_to_cycle_aux],
end)

-- def list_to_cycle' (l : list α) : l.nodup → perm α :=
-- list.reverse_rec_on l (λ _, 1) (λ l, list.cases_on l (λ _ _ _, 1)
-- $ λ x l y _ h,
-- have hx : (x::l : list α).nodup := (list.nodup_of_nodup_append_left h),
-- have hy : (l ++ [y]).nodup := by rw list.cons_append at h;
--   exact list.nodup_of_nodup_cons h,
-- let f := list_to_cycle_aux (x :: l ++ [y]) in
-- let g := list_to_cycle_aux (x :: l ++ [y]).reverse in
-- { to_fun := λ n, if n = y then x else f n,
--   inv_fun := λ n, if n = x then y else g n,
--   left_inv := λ n, begin dsimp, split_ifs, cc, end,
--   right_inv := sorry })

-- #eval ((list_to_cycle' ([1,2,3] : list (fin 6)) sorry) * list_to_cycle' [2,3,0,4] sorry) * swap 0 5
-- def list_to_cycle2 : Π l : list α, l.nodup → perm α
-- | []     := λ h, 1
-- | (x::l) := λ h,
-- { to_fun := λ x, list.nth_le (x::l) (((list.index_of x l : ℕ) : zmod l.length.succ) + 1).val
--     (((list.index_of x l : ℕ) : zmod l.length.succ) + 1).2,
--   inv_fun := λ x, list.nth_le (x::l) ((list.index_of x l : zmod l.length.succ) - 1).val
--     ((list.index_of x l : zmod l.length.succ) - 1).2,
--   left_inv := λ x, begin dsimp, rw index_of_nth_le  end,
--   right_inv := sorry }

-- def list_to_cycle (l : list α) (hl : l.nodup) : perm α :=
-- { to_fun := λ x, if h : x ∈ l then begin
--     have := list.index_of x l,
--     have := list.ind
--   end else x,
--   inv_fun := λ x, if h : x ∈ l then begin end else x,
--   left_inv := sorry,
--   right_inv := sorry }

def list_to_cycle (l : list α) : l.nodup → perm α :=
list.cases_on l (λ _, 1) (λ x l, list.reverse_rec_on l (λ _ , 1)
(λ m y,
list.reverse_rec_on m (λ _ _, swap x y)
(λ n z f h ih,
have hyx : y ≠ x := sorry,
let f := h sorry in
have hfax : ∀ a : α, f a = x ↔ a = z := sorry,
{ to_fun := λ a, if a = z then y else if a = y then x else f a,
  inv_fun := λ a, if a = x then y else if a = y then z else f⁻¹ a,
  left_inv := λ a, begin simp, split_ifs, end,
  right_inv := sorry })))

end equiv.perm