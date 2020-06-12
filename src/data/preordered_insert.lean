import data.list.sort


instance is_total_not_lt {α : Type*} [preorder α] : is_total α (λ x y, ¬(x < y)) :=
{ total := λ x y,
  begin
    classical, by_contradiction,
    rw not_or_distrib at a,
    simp at a,
    exact lt_irrefl x (lt_trans a.1 a.2),
  end }


namespace list

lemma sorted_append {α : Type*} {r : α → α → Prop} {l₁ l₂ : list α} : sorted r (l₁++l₂) ↔
  sorted r l₁ ∧ sorted r l₂ ∧ ∀ x ∈ l₁, ∀ y ∈ l₂, r x y :=
pairwise_append

lemma mem_take_while {α : Type*} {p : α → Prop} [decidable_pred p] {L : list α} {a : α}
   (h : a ∈ L.take_while p) : p a := sorry

section sort

/-!
Before setting up `insertion_sort`, which requires a transitive and total relation `≤`
and produces a list which is `sorted (≤)`,
we define `preorder_sort`, which given a transitive and irreflexive relation `<`
(e.g. coming from any preorder, with no requirement it is total),
produces a list which is `sorted (λ x y, ¬ y < x)`.

If the order relations come from a `decidable_linear_order`,
then in fact `preorder_sort` and `insertion_sort` agree.

It is useful to have `preorder_sort` when working with partial ordered data.
-/

section preorder_sort

parameters {α : Type*} (r : α → α → Prop) [decidable_rel r]
local infix ` ≺ ` : 50 := r

/--
`preordered_insert (≺) a l` inserts `a` into `l` so that `a` appears before any smaller elements.
-/
def preordered_insert (a : α) (L : list α) : list α :=
L.take_while (λ x, ¬ x ≺ a) ++ [a] ++ L.drop_while (λ x, ¬ x ≺ a)

@[simp] def preorder_sort' : list α → list α
| []       := []
| (b :: l) := preordered_insert b (preorder_sort' l)

/--
When `≺` is a transitive and irreflexive relation (e.g. `<` in any preorder)
`preorder_sort (≺) l` returns a list which is `sorted (λ x y, ¬(y ≺ x))`,
that is, no strictly larger element comes before a smaller element.
-/
@[simp] def preorder_sort (L : list α) : list α :=
(preorder_sort' L).reverse

@[simp] lemma preordered_insert_nil (a : α) : [].preordered_insert r a = [a] := rfl

theorem preordered_insert_length (L : list α) (a : α) :
  (L.preordered_insert r a).length = L.length + 1 :=
begin
  dsimp [preordered_insert],
  simp only [cons_append, length, append_assoc, nil_append, length_append],
  rw [←add_assoc, ←length_append, take_while_append_drop],
end

section correctness
open perm

theorem perm_preordered_insert (a) (L : list α) : preordered_insert a L ~ a :: L :=
begin
  dsimp [preordered_insert],
  calc take_while (λ (x : α), ¬r x a) L ++ [a] ++ drop_while (λ (x : α), ¬r x a) L
        ~ [a] ++ take_while (λ (x : α), ¬r x a) L ++ drop_while (λ (x : α), ¬r x a) L :
            (perm_append_right_iff _).2 perm_append_comm
    ... ~ [a] ++ L : by rw [append_assoc, take_while_append_drop]
    ... ~ a :: L : by simp,
end

theorem preordered_insert_count [decidable_eq α] (L : list α) (a b : α) :
  count a (L.preordered_insert r b) = count a L + if (a = b) then 1 else 0 :=
begin
  rw [(L.perm_preordered_insert r b).count_eq, count_cons],
  split_ifs; simp only [nat.succ_eq_add_one, add_zero],
end

theorem perm_preorder_sort (L : list α) : preorder_sort L ~ L :=
begin
  dsimp [preorder_sort],
  calc _ ~ preorder_sort' (≺) L : reverse_perm _
     ... ~ L : _,
  induction L with hd tl ih,
  { simp, },
  { simp [list.preordered_insert], sorry, }
end

section asymm_and_trans
variables [is_asymm α r] [is_trans α r]

theorem sorted_preordered_insert (a : α) :
  ∀ l, sorted (λ x y, ¬(x ≺ y)) l → sorted (λ x y, ¬(x ≺ y)) (preordered_insert a l)
| []       h := sorted_singleton a
| (b :: l) h :=
  begin
    simp only [preordered_insert],
    apply sorted_append.2,
    refine ⟨_,_,_⟩,
    { apply sorted_append.2,
      refine ⟨_,_,_⟩,
      { sorry, },
      { simp, },
      { rintros x m y ⟨w|w'⟩, apply mem_take_while m, rcases H, }, },
    { sorry, },
    { intros x mx y my, sorry, },
  end

theorem sorted_preorder_sort : ∀ l, sorted (λ x y, ¬(y ≺ x)) (preorder_sort l)
| []       := sorted_nil
| (a :: l) := sorted_preordered_insert a _ (sorted_preorder_sort l)

end asymm_and_trans
end correctness
end preorder_sort

variables {α : Type*} [decidable_linear_order α]

lemma preorder_sort_eq_insertion_sort (L : list α) : preorder_sort (<) L = insertion_sort (≤) L :=
eq_of_sorted_of_perm ((perm_preorder_sort (<) L).trans (perm_insertion_sort (≤) L).symm)
  (by simpa using sorted_preorder_sort (<) L)
  (sorted_insertion_sort (≤) L)

end sort

end list
