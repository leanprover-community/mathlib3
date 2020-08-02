import data.list.basic
import data.list.defs
import data.list.range
import data.list.zip
import logic.basic

universes u v

open function

namespace list

variables {α : Type u} {β : Type v}


section foldr_with_index

def foldr_with_index_aux_spec (f : ℕ → α → β → β) (start : ℕ) (b : β)
  (as : list α) : β :=
foldr (uncurry f) b $ zip (range' start as.length) as

lemma foldr_with_index_aux_spec_cons (f : ℕ → α → β → β) (start b a as)
  : foldr_with_index_aux_spec f start b (a :: as)
  = f start a (foldr_with_index_aux_spec f (start + 1) b as) := rfl

lemma foldr_with_index_aux_correct (f : ℕ → α → β → β) (start b as)
  : foldr_with_index_aux f start b as = foldr_with_index_aux_spec f start b as :=
by induction as generalizing start;
  [ refl, simp only [foldr_with_index_aux, foldr_with_index_aux_spec_cons, *] ]

lemma foldr_with_index_correct' (f : ℕ → α → β → β) (b : β) (as : list α)
  : foldr_with_index f b as = foldr (uncurry f) b (zip (range as.length) as) :=
by simp only
    [ foldr_with_index, foldr_with_index_aux_spec, foldr_with_index_aux_correct
    , ←range_eq_range' ]

end foldr_with_index


theorem indexes_correct (as : list α) : indexes as = range as.length :=
begin
  suffices h : foldr (cons ∘ prod.fst) nil ((range as.length).zip as) = range as.length,
  { simp [indexes, foldr_with_index_correct'], exact h },
  rw ←foldr_map,
  simp [map_fst_zip]
end

theorem indexed_correct (as : list α) : indexed as = zip (indexes as) as :=
by simp [indexed, foldr_with_index_correct', indexes_correct, uncurry]

theorem foldr_with_index_correct (f : ℕ → α → β → β) (b : β) (as : list α)
  : foldr_with_index f b as = foldr (uncurry f) b (indexed as) :=
by rw [indexed_correct, indexes_correct, foldr_with_index_correct']

theorem indexes_values_correct (p : α → Prop) [decidable_pred p] (as : list α)
  : indexes_values p as = filter (p ∘ prod.snd) (indexed as) :=
by simp
    [ indexes_values, foldr_with_index_correct, indexes_correct, uncurry
    , filter_eq_foldr ]

theorem find_indexes_correct (p : α → Prop) [decidable_pred p] (as : list α)
  : find_indexes p as = map prod.fst (indexes_values p as) :=
begin
  rw [indexes_values_correct, map_filter_eq_foldr],
  simp only [find_indexes, foldr_with_index_correct, uncurry]
end


section foldl_with_index

def foldl_with_index_aux_spec (f : ℕ → α → β → α) (start : ℕ) (a : α)
  (bs : list β) : α :=
foldl (λ a (p : ℕ × β), f p.fst a p.snd) a $ zip (range' start bs.length) bs

@[simp] lemma foldl_with_index_aux_spec_cons (f : ℕ → α → β → α) (start a b bs)
  : foldl_with_index_aux_spec f start a (b :: bs)
  = foldl_with_index_aux_spec f (start + 1) (f start a b) bs := rfl

lemma foldl_with_index_aux_correct (f : ℕ → α → β → α) (start a bs)
  : foldl_with_index_aux f start a bs = foldl_with_index_aux_spec f start a bs :=
by induction bs generalizing start a; [ refl, simp [foldl_with_index_aux, *] ]

lemma foldl_with_index_correct (f : ℕ → α → β → α) (a : α) (bs : list β)
  : foldl_with_index f a bs
  = foldl (λ a (p : ℕ × β), f p.fst a p.snd) a (indexed bs) :=
by simp only
    [ foldl_with_index, foldl_with_index_aux_spec, foldl_with_index_aux_correct
    , indexed_correct, indexes_correct, ←range_eq_range' ]

end foldl_with_index

end list
