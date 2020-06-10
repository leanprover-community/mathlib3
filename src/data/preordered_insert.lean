import data.list.sort

namespace list

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
local infix ` ≺  ` : 50 := r

/--
`preordered_insert (≺) a l` inserts `a` into `l` so that `a` appears after any smaller elements.
-/
@[simp] def preordered_insert (a : α) : list α → list α
| []       := [a]
| (b :: l) := if ∃ m ∈ b :: l, m ≺ a then b :: preordered_insert l else a :: b :: l

/--
When `≺` is a transitive and irreflexive relation (e.g. `<` in any preorder)
`preorder_sort (≺) l` returns a list which is `sorted (λ x y, ¬(y ≺ x)`,
that is, no strictly larger element comes before a smaller element.
-/
@[simp] def preorder_sort : list α → list α
| []       := []
| (b :: l) := preordered_insert b (preorder_sort l)

@[simp] lemma preordered_insert_nil (a : α) : [].preordered_insert r a = [a] := rfl

theorem preordered_insert_length :
  Π (L : list α) (a : α), (L.preordered_insert r a).length = L.length + 1
| [] a := rfl
| (hd :: tl) a := by { dsimp [preordered_insert], split_ifs; simp [preordered_insert_length], }

section correctness
open perm

theorem perm_preordered_insert (a) : ∀ l : list α, preordered_insert a l ~ a :: l
| []       := perm.refl _
| (b :: l) :=
  begin
    simp only [preordered_insert],
    split_ifs,
    { transitivity,
      { apply perm.cons,
        apply perm_preordered_insert, },
      { apply perm.swap, }, },
    { refl, },
  end

theorem preordered_insert_count [decidable_eq α] (L : list α) (a b : α) :
  count a (L.preordered_insert r b) = count a L + if (a = b) then 1 else 0 :=
begin
  rw [(L.perm_preordered_insert r b).count_eq, count_cons],
  split_ifs; simp only [nat.succ_eq_add_one, add_zero],
end

theorem perm_preorder_sort : ∀ l : list α, preorder_sort l ~ l
| []       := perm.nil
| (b :: l) := by simpa [preorder_sort] using
  (perm_preordered_insert _ _ _).trans ((perm_preorder_sort l).cons b)

section asymm_and_trans
variables [is_asymm α r] [is_trans α r]

theorem sorted_preordered_insert (a : α) :
  ∀ l, sorted (λ x y, ¬(y ≺ x)) l → sorted (λ x y, ¬(y ≺ x)) (preordered_insert a l)
| []       h := sorted_singleton a
| (b :: l) h :=
  begin
    simp only [preordered_insert],
    split_ifs with w,
    { apply sorted_cons.2,
      split,
      { intros c h',
        rw perm.mem_iff (perm_preordered_insert _ _ _) at h',
        rcases h' with ⟨rfl|h'⟩,
        { obtain ⟨c, m, w⟩ := w,
          rcases m with ⟨rfl|m⟩,
          { exact asymm w, },
          { exact λ w', rel_of_sorted_cons h c m (trans w w') }, },
        { apply rel_of_sorted_cons h _ h', }, },
      { exact sorted_preordered_insert _ (sorted_of_sorted_cons h), }, },
    { simp at w,
      apply sorted_cons.2,
      split,
      { intros c h',
        rcases h' with ⟨rfl|h'⟩,
        { exact w.1, },
        { exact w.2 _ h', }, },
      { exact h, }, },
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
