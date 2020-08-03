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

theorem foldr_with_index_aux_spec_cons (f : ℕ → α → β → β) (start b a as)
  : foldr_with_index_aux_spec f start b (a :: as)
  = f start a (foldr_with_index_aux_spec f (start + 1) b as) := rfl

theorem foldr_with_index_aux_correct (f : ℕ → α → β → β) (start b as)
  : foldr_with_index_aux f start b as = foldr_with_index_aux_spec f start b as :=
by induction as generalizing start;
    [refl, simp only [foldr_with_index_aux, foldr_with_index_aux_spec_cons, *]]

theorem foldr_with_index_correct' (f : ℕ → α → β → β) (b : β) (as : list α)
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
by simp only
    [ indexes_values_correct, map_filter_eq_foldr, find_indexes
    , foldr_with_index_correct, uncurry ]


section foldl_with_index

def foldl_with_index_aux_spec (f : ℕ → α → β → α) (start : ℕ) (a : α)
  (bs : list β) : α :=
foldl (λ a (p : ℕ × β), f p.fst a p.snd) a $ zip (range' start bs.length) bs

@[simp] theorem foldl_with_index_aux_spec_cons (f : ℕ → α → β → α) (start a b bs)
  : foldl_with_index_aux_spec f start a (b :: bs)
  = foldl_with_index_aux_spec f (start + 1) (f start a b) bs := rfl

theorem foldl_with_index_aux_correct (f : ℕ → α → β → α) (start a bs)
  : foldl_with_index_aux f start a bs = foldl_with_index_aux_spec f start a bs :=
by induction bs generalizing start a; [ refl, simp [foldl_with_index_aux, *] ]

theorem foldl_with_index_correct (f : ℕ → α → β → α) (a : α) (bs : list β)
  : foldl_with_index f a bs
  = foldl (λ a (p : ℕ × β), f p.fst a p.snd) a (indexed bs) :=
by simp only
    [ foldl_with_index, foldl_with_index_aux_spec, foldl_with_index_aux_correct
    , indexed_correct, indexes_correct, ←range_eq_range' ]

end foldl_with_index


section mfold_with_index

variables {m : Type u → Type v} [monad m]

theorem mfoldr_with_index_correct {α β} (f : ℕ → α → β → m β) (b : β) (as : list α)
  : mfoldr_with_index f b as = mfoldr (uncurry f) b (indexed as) :=
by simp only
    [mfoldr_with_index, mfoldr_eq_foldr, foldr_with_index_correct, uncurry]

theorem mfoldl_with_index_correct [is_lawful_monad m] {α β} (f : ℕ → β → α → m β)
  (b : β) (as : list α)
  : mfoldl_with_index f b as
  = mfoldl (λ b (p : ℕ × α), f p.fst b p.snd) b (indexed as) :=
by rw [mfoldl_with_index, mfoldl_eq_foldl, foldl_with_index_correct]

end mfold_with_index


section mmap_with_index

variables {m : Type u → Type v} [monad m]

def mmap_with_index_aux_spec {α β} (f : ℕ → α → m β) (start : ℕ) (as : list α)
  : m (list β) :=
mmap (uncurry f) $ zip (range' start as.length) as

@[simp] theorem mmap_with_index_aux_spec_cons {α β} (f : ℕ → α → m β) (start : ℕ)
  (a : α) (as : list α)
  : mmap_with_index_aux_spec f start (a :: as)
  = do {
      b ← f start a,
      bs ← mmap_with_index_aux_spec f (start + 1) as,
      pure $ b :: bs
    } :=
rfl

variables [is_lawful_monad m]

theorem mmap_with_index_aux_correct {α β} (f : ℕ → α → m β) (start : ℕ) (as : list α)
  : mmap_with_index_aux f start as = mmap_with_index_aux_spec f start as :=
by induction as generalizing start;
    [ refl, simp [mmap_with_index_aux, *] with monad_norm ]

theorem mmap_with_index_correct {α β} (f : ℕ → α → m β) (as : list α)
  : mmap_with_index f as = mmap (uncurry f) (indexed as) :=
by simp only
    [ mmap_with_index, mmap_with_index_aux_spec, mmap_with_index_aux_correct
    , indexed_correct, indexes_correct, range_eq_range' ]

end mmap_with_index


section mmap_with_index'

variables {m : Type u → Type v} [applicative m] [is_lawful_applicative m]

theorem mmap_with_index'_aux_eq_mmap_with_index_aux {α} (f : ℕ → α → m punit)
  (start : ℕ) (as : list α)
  : mmap_with_index'_aux f start as
  = mmap_with_index_aux f start as *> pure punit.star :=
by induction as generalizing start;
    simp [mmap_with_index'_aux, mmap_with_index_aux, *, seq_right_eq, const]
      with functor_norm

theorem mmap_with_index'_eq_mmap_with_index {α} (f : ℕ → α → m punit) (as : list α)
  : mmap_with_index' f as = mmap_with_index f as *> pure punit.star :=
by apply mmap_with_index'_aux_eq_mmap_with_index_aux

end mmap_with_index'

end list
