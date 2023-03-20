import data.fintype.basic
import order.atoms

variables {α : Type*}


namespace multiset
variables {s t : multiset α} {a : α}

@[simp] lemma cons_zero (a : α) : a ::ₘ 0 = {a} := rfl

@[simp] lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

lemma le_singleton_iff : s ≤ {a} ↔ s = 0 ∨ s = {a} :=
quot.induction_on s $ λ l, by simp only [singleton_eq_cons, singleton_coe, quot_mk_to_coe'', coe_le,
  coe_eq_zero, coe_eq_coe, list.perm_singleton, list.subperm_singleton_iff']

lemma lt_singleton_iff : s < {a} ↔ s = 0 :=
begin
  rw [lt_iff_le_and_ne, le_singleton_iff, or_and_distrib_right, or_iff_left (and_not_self _).1,
    and_iff_left_of_imp],
  rintro rfl,
  rw singleton_eq_cons,
  exact zero_ne_cons,
end

lemma covby_cons (m : multiset α) (a : α) : m ⋖ a ::ₘ m :=
⟨lt_cons_self _ _, begin
  simp_rw lt_iff_cons_le,
  rintros m' ⟨b, hbm'⟩ ⟨c, hcm'⟩,
  apply @irrefl _ (<) _ m,
  have h := lt_of_le_of_lt hbm' (lt_cons_self _ c),
  replace h := lt_of_lt_of_le h hcm',
  clear hbm' hcm',
  induction m using multiset.induction with d m hm,
  { rw [cons_zero a, lt_singleton_iff] at h,
    exact (cons_ne_zero h).elim },
  { simp_rw cons_swap _ d at h,
    rw cons_lt_cons_iff at h ⊢,
    exact hm h }
end⟩

lemma _root_.covby.exists_cons_multiset (h : s ⋖ t) : ∃ a, t = a ::ₘ s :=
(lt_iff_cons_le.1 h.lt).imp $ λ a ha, ha.eq_of_not_gt $ h.2 $ lt_cons_self _ _

lemma covby_iff : s ⋖ t ↔ ∃ a, t = a ::ₘ s :=
⟨covby.exists_cons_multiset, by { rintro ⟨a, rfl⟩, exact covby_cons _ _ }⟩

lemma _root_.covby.card_multiset (h : s ⋖ t) : s.card ⋖ t.card :=
by { obtain ⟨a, rfl⟩ := h.exists_cons_multiset, rw card_cons, exact covby_succ _ }

lemma card_strict_mono : strict_mono (card : multiset α → ℕ) := λ _ _, card_lt_of_lt

end multiset

namespace finset
variables {s t : finset α}

-- golf using `image_covby_iff`
@[simp] lemma val_covby_iff : s.1 ⋖ t.1 ↔ s ⋖ t :=
begin
  split;
  rintro ⟨hlt, no_intermediate⟩;
  split;
  simp at *;
  rwa [←val_lt_iff] at *;
  intros c hsc hct;
  simp at *;
  rw [←val_lt_iff] at *,
  { apply @no_intermediate c.val; assumption },
  { apply @no_intermediate ⟨c, multiset.nodup_of_le hct.1 t.nodup⟩;
    rw ←val_lt_iff;
    assumption }
end

alias val_covby_iff ↔ _ covby.finset_val

lemma _root_.covby.card_finset (h : s ⋖ t) : s.card ⋖ t.card := (val_covby_iff.2 h).card_multiset

lemma _root_.is_min.eq_empty : is_min s → s = ∅ := is_min.eq_bot

lemma val_strict_mono : strict_mono (val : finset α → multiset α) := λ _ _, val_lt_iff.2

lemma card_strict_mono : strict_mono (card : finset α → ℕ) := λ _ _, card_lt_card

end finset

namespace finset
variables {s : finset α}

lemma exists_eq_singleton_iff_nonempty_subsingleton :
  (∃ a : α, s = {a}) ↔ s.nonempty ∧ ∀ a b ∈ s, a = b :=
begin
  refine ⟨_, λ h, _⟩,
  { rintro ⟨a, rfl⟩,
    exact ⟨singleton_nonempty a, λ b hb c hc,
      (eq_of_mem_singleton hb).trans (eq_of_mem_singleton hc).symm⟩ },
  { obtain ⟨a, ha⟩ := h.1,
    exact ⟨a, eq_singleton_iff_unique_mem.mpr ⟨ha, λ b hb, (h.2 _ hb _ ha)⟩⟩ }
end

lemma is_atom_singleton (a : α) : is_atom ({a} : finset α) :=
⟨singleton_ne_empty a, λ s, eq_empty_of_ssubset_singleton⟩

lemma is_coatom_compl_singleton [fintype α] [decidable_eq α] (a : α) :
  is_coatom ({a}ᶜ : finset α) :=
(is_atom_singleton a).compl

lemma is_atom_iff : is_atom s ↔ ∃ a, s = {a} :=
begin
  refine ⟨λ hs, exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨nonempty_of_ne_empty hs.1,
    λ a ha b hb, _⟩, _⟩,
  { rw [←singleton_subset_iff] at ha hb,
    exact singleton_injective (((hs.le_iff_eq $ singleton_ne_empty _).1 ha).trans $
      ((hs.le_iff_eq $ singleton_ne_empty _).1 hb).symm) },
  { rintro ⟨a, rfl⟩,
    exact is_atom_singleton _ }
end

lemma is_coatom_iff [fintype α] [decidable_eq α] : is_coatom s ↔ ∃ a, s = {a}ᶜ :=
by simp_rw [←is_atom_compl, is_atom_iff, compl_eq_iff_is_compl, eq_compl_iff_is_compl]

end finset

namespace multiset
variables {m : multiset α}

lemma le_singleton_iff_eq {m : multiset α} {x : α} : m ≤ {x} ↔ m = 0 ∨ m = {x} :=
begin
  obtain rfl | hm := eq_or_ne m 0,
  refine ⟨λ _, or.inl rfl, λ _, zero_le _⟩,
  simp [eq_singleton_iff_nonempty_unique_mem, hs, ne_empty_iff_nonempty.2 hs],
end

@[simp] lemma lt_singleton_iff {m : multiset α} {a : α} :  m < {a} ↔ m = 0 :=
begin
  rw [lt_iff_le_and_ne, le_singleton_iff_eq, or_and_distrib_right, and_not_self, or_false,
    and_iff_left_iff_imp],
  rintro rfl,
  exact (singleton_ne_zero _).symm,
end

lemma eq_zero_of_ssubset_singleton {s : multiset α} {x : α} (hs : s ⊂ {x}) : s = 0 :=
ssubset_singleton_iff.1 hs

lemma is_atom_singleton (a : α) : is_atom ({a} : multiset α) :=
⟨singleton_ne_zero a, λ s, eq_zero_of_lt_singleton⟩

lemma is_atom_iff : is_atom m ↔ ∃ a, m = {a} :=
begin
  refine ⟨λ hs, exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨nonempty_of_ne_empty hs.1,
    λ a ha b hb, _⟩, _⟩,
  { rw [←singleton_subset_iff] at ha hb,
    exact singleton_injective (((hs.le_iff_eq $ singleton_ne_empty _).1 ha).trans $
      ((hs.le_iff_eq $ singleton_ne_empty _).1 hb).symm) },
  { rintro ⟨a, rfl⟩,
    exact is_atom_singleton _ }
end

end multiset
