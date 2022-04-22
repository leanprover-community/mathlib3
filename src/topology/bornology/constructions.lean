import topology.bornology.basic

/-!
-/

open set filter bornology function
open_locale filter

variables {α β ι : Type*} {π : ι → Type*} [fintype ι] [bornology α] [bornology β]
  [Π i, bornology (π i)]

instance : bornology (α × β) :=
{ cobounded := (cobounded α).coprod (cobounded β),
  le_cofinite := @coprod_cofinite α β ▸ coprod_mono ‹bornology α›.le_cofinite
    ‹bornology β›.le_cofinite }

instance : bornology (Π i, π i) :=
{ cobounded := filter.Coprod (λ i, cobounded (π i)),
  le_cofinite := @Coprod_cofinite ι π _ ▸ (filter.Coprod_mono $ λ i, bornology.le_cofinite _) }

namespace bornology

lemma cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) := rfl

lemma prod_is_bounded {s : set (α × β)} :
  is_bounded s ↔ is_bounded (prod.fst '' s) ∧ is_bounded (prod.snd '' s) :=
compl_mem_coprod

lemma pi_is_bounded {s : set (Π i, π i)} : is_bounded s ↔ ∀ i, is_bounded (eval i '' s) :=
compl_mem_Coprod

variables {s : set α} {t : set β} {S : Π i, set (π i)}

lemma is_bounded.fst_of_prod (h : is_bounded (s ×ˢ t)) (ht : t.nonempty) :
  is_bounded s :=
fst_image_prod s ht ▸ (prod_is_bounded.1 h).1

lemma is_bounded.snd_of_prod (h : is_bounded (s ×ˢ t)) (hs : s.nonempty) :
  is_bounded t :=
snd_image_prod hs t ▸ (prod_is_bounded.1 h).2

lemma is_bounded.prod (hs : is_bounded s) (ht : is_bounded t) : is_bounded (s ×ˢ t) :=
prod_is_bounded.2 ⟨hs.subset $ fst_image_prod_subset _ _, ht.subset $ snd_image_prod_subset _ _⟩

lemma is_bounded_prod_of_nonempty (hne : set.nonempty (s ×ˢ t)) :
  is_bounded (s ×ˢ t) ↔ is_bounded s ∧ is_bounded t :=
⟨λ h, ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, λ h, h.1.prod h.2⟩

lemma is_bounded_prod : is_bounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ is_bounded s ∧ is_bounded t :=
begin
  rcases s.eq_empty_or_nonempty with rfl|hs, { simp },
  rcases t.eq_empty_or_nonempty with rfl|ht, { simp },
  simp only [hs.ne_empty, ht.ne_empty, is_bounded_prod_of_nonempty (hs.prod ht), false_or]
end

lemma is_bounded_prod_self : is_bounded (s ×ˢ s) ↔ is_bounded s :=
begin
  rcases s.eq_empty_or_nonempty with rfl|hs, { simp },
  exact (is_bounded_prod_of_nonempty (hs.prod hs)).trans (and_self _)
end

lemma is_bounded.pi (h : ∀ i, is_bounded (S i)) : is_bounded (pi univ S) :=
pi_is_bounded.2 $ λ i, (h i).subset eval_image_univ_pi_subset

lemma is_bounded_pi_of_nonempty (hne : (pi univ S).nonempty) :
  is_bounded (pi univ S) ↔ ∀ i, is_bounded (S i) :=
⟨λ H i, @eval_image_univ_pi _ _ _ i hne ▸ pi_is_bounded.1 H i, is_bounded.pi⟩

lemma is_bounded_pi : is_bounded (pi univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, is_bounded (S i) :=
begin
  by_cases hne : ∃ i, S i = ∅,
  { simp [hne, univ_pi_eq_empty_iff.2 hne] },
  { simp only [hne, false_or],
    simp only [not_exists, ← ne.def, ne_empty_iff_nonempty, ← univ_pi_nonempty_iff] at hne,
    exact is_bounded_pi_of_nonempty hne }
end

end bornology
