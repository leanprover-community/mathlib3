import data.fintype.card
import order.atoms
import data.nat.succ_pred

variables {α : Type*}

open order

namespace list
variables {l l₁ l₂ : list α} {a : α}

lemma subperm_iff : l₁ <+~ l₂ ↔ ∃ l ~ l₂, l₁ <+ l :=
begin
  refine ⟨_, λ ⟨l, h₁, h₂⟩, h₂.subperm.trans h₁.subperm⟩,
  rintro ⟨l, h₁, h₂⟩,
  obtain ⟨l', h₂⟩ := h₂.exists_perm_append,
  exact ⟨l₁ ++ l', (h₂.trans (h₁.append_right _)).symm, (prefix_append _ _).sublist⟩,
end

@[simp] lemma sublist_singleton : l <+ [a] ↔ l = [] ∨ l = [a] :=
by split; rintro (_ | _); simp [*] at *

@[simp] lemma subperm_singleton_iff' : l <+~ [a] ↔ l = [] ∨ l = [a] :=
begin
  split,
  { rw subperm_iff,
    rintro ⟨s, hla, h⟩,
    rwa [perm_singleton.mp hla, sublist_singleton] at h },
  { rintro (rfl | rfl),
    exacts [nil_subperm, subperm.refl _] }
end

end list

namespace multiset
variables {s t : multiset α} {a : α}

instance : is_nonstrict_strict_order (multiset α) (⊆) (⊂) := ⟨λ _ _, iff.rfl⟩

@[simp] lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

@[simp] lemma le_singleton : s ≤ {a} ↔ s = 0 ∨ s = {a} :=
quot.induction_on s $ λ l, by simp only [cons_zero, ←coe_singleton, quot_mk_to_coe'', coe_le,
  coe_eq_zero, coe_eq_coe, list.perm_singleton, list.subperm_singleton_iff']

@[simp] lemma lt_singleton : s < {a} ↔ s = 0 :=
begin
  simp only [lt_iff_le_and_ne, le_singleton, or_and_distrib_right, ne.def, and_not_self, or_false,
    and_iff_left_iff_imp],
  rintro rfl,
  exact (singleton_ne_zero _).symm,
end

lemma covby_cons (m : multiset α) (a : α) : m ⋖ a ::ₘ m :=
⟨lt_cons_self _ _, begin
  simp_rw lt_iff_cons_le,
  rintro m' ⟨b, hbm'⟩ ⟨c, hcm'⟩,
  apply @irrefl _ (<) _ m,
  have h := lt_of_le_of_lt hbm' (lt_cons_self _ c),
  replace h := lt_of_lt_of_le h hcm',
  clear hbm' hcm',
  induction m using multiset.induction with d m hm,
  { rw [cons_zero a, lt_singleton] at h,
    exact (cons_ne_zero h).elim },
  { simp_rw cons_swap _ d at h,
    rw cons_lt_cons_iff at h ⊢,
    exact hm h }
end⟩

attribute [simp] subset_zero

@[simp] lemma zero_ssubset : 0 ⊂ s ↔ s ≠ 0 := by simp [ssubset_iff_subset_not_subset]

@[simp] lemma singleton_subset : {a} ⊆ s ↔ a ∈ s := by simp [subset_iff]

@[simp] lemma ssubset_singleton_iff : s ⊂ {a} ↔ s = 0 :=
begin
  refine ⟨λ hs, eq_zero_of_subset_zero $ λ b hb, hs.2 _, _⟩,
  { obtain rfl := mem_singleton.1 (hs.1 hb),
    rwa singleton_subset },
  { rintro rfl,
    simp }
end

lemma _root_.covby.exists_cons_multiset (h : s ⋖ t) : ∃ a, t = a ::ₘ s :=
(lt_iff_cons_le.1 h.lt).imp $ λ a ha, ha.eq_of_not_gt $ h.2 $ lt_cons_self _ _

lemma covby_iff : s ⋖ t ↔ ∃ a, t = a ::ₘ s :=
⟨covby.exists_cons_multiset, by { rintro ⟨a, rfl⟩, exact covby_cons _ _ }⟩

lemma _root_.covby.card_multiset (h : s ⋖ t) : s.card ⋖ t.card :=
by { obtain ⟨a, rfl⟩ := h.exists_cons_multiset, rw card_cons, exact covby_succ _ }

lemma card_strict_mono : strict_mono (card : multiset α → ℕ) := λ _ _, card_lt_of_lt

lemma is_atom_iff : is_atom s ↔ ∃ a, s = {a} := bot_covby_iff.symm.trans covby_iff

@[simp] lemma is_atom_singleton (a : α) : is_atom ({a} : multiset α) := is_atom_iff.2 ⟨_, rfl⟩

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
