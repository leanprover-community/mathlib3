import data.fintype.basic
import data.set.finite
import tactic

open fintype
open function

universes u v

section general_lemmas

lemma card_ne_eq {α : Type*} [fintype α] [decidable_eq α] (a : α) :
  card {x : α | x ≠ a} = card α - 1 :=
begin
  rw [←set.to_finset_card],
  convert_to (finset.univ.erase a).card = _,
  { congr,
    ext,
    rw [set.mem_to_finset, finset.mem_erase, set.mem_set_of_eq],
    simp only [finset.mem_univ, and_true], },
  { rw [finset.card_erase_of_mem (finset.mem_univ _), finset.card_univ],
    refl, },
end

lemma le_pred_if_lt {a b : ℕ} (h : a < b) : a ≤ b.pred :=
begin
  cases b, omega, simp only [nat.pred_succ], exact nat.lt_succ_iff.mp h,
end

@[simp]
lemma finset.nonempty.image_iff {α β: Type*} [decidable_eq β]
  (f : α → β) (s : finset α) :
  (s.image f).nonempty ↔ s.nonempty :=
begin
  split,
  { rintro ⟨y, hy⟩,
    rw finset.mem_image at hy,
    rcases hy with ⟨x, hx, rfl⟩,
    exact ⟨x, hx⟩, },
  { intro h,
    exact finset.nonempty.image h f, },
end

lemma finset.bind_erase {α β : Type*} [decidable_eq β] (f : α → finset β) (s : finset α) (b : β) :
  s.bind (λ x, (f x).erase b) = (s.bind f).erase b :=
begin
  ext y,
  simp only [exists_prop, finset.mem_bind, ne.def, finset.mem_erase],
  tauto,
end

lemma finset.card_eq_iff_eq_univ {α : Type*} [fintype α] (s : finset α) :
  s.card = card α ↔ s = finset.univ :=
begin
  split,
  { intro h,
    exact finset.eq_univ_of_card _ h, },
  { rintro rfl,
    exact finset.card_univ, },
end

lemma finset.card_lt_of_ne_univ {α : Type*} [fintype α]
  (s : finset α) (hnu : s ≠ finset.univ) : s.card < card α :=
begin
  by_contra h,
  apply hnu,
  rw ←finset.card_eq_iff_eq_univ,
  have h' : s.card ≤ card α := finset.card_le_univ s,
  push_neg at h,
  exact nat.le_antisymm h' h,
end

lemma finset.card_compl_lt_of_nonempty {α : Type*} [fintype α] [decidable_eq α]
  (s : finset α) (hne : s.nonempty) :
  sᶜ.card < card α :=
begin
  apply finset.card_lt_of_ne_univ,
  cases hne with x hx,
  intro h,
  have h' := finset.mem_univ x,
  rw ←h at h',
  simpa [hx] using h',
end

lemma finset.bind_union {α β : Type*} [decidable_eq α] [decidable_eq β]
  (s t : finset α) (f : α → finset β) :
  (s ∪ t).bind f = s.bind f ∪ t.bind f :=
begin
  ext y,
  simp [or_and_distrib_right],
  split,
  { rintro ⟨x, (h|h)⟩,
    { left, exact ⟨x, h⟩, },
    { right, exact ⟨x, h⟩, }, },
  { rintro (⟨x, h⟩|⟨x, h⟩),
    { exact ⟨x, or.inl h⟩, },
    { exact ⟨x, or.inr h⟩, }, },
end

lemma finset.compl_inter_self {α : Type*} [decidable_eq α] [fintype α] (s : finset α) :
  sᶜ ∩ s = ∅ :=
begin
  ext x, simp,
end

/- -- unused
lemma finset.bind_of_subset {α β : Type*} [decidable_eq β] {s : finset α} (f f' : α → finset β)
  (h : ∀ x, f x ⊆ f' x) :
  s.bind f ⊆ s.bind f' :=
begin
  intro y,
  simp only [and_imp, exists_prop, finset.mem_bind, exists_imp_distrib],
  tauto,
end

-- note: follows inter, which is opposite convention from set version...
lemma finset.union_subset_union_right {x y s : finset α} (h : x ⊆ y) : x ∪ s ⊆ y ∪ s :=
finset.union_subset_union h (finset.subset.refl _)

lemma finset.union_subset_union_left {x y s : finset α} (h : x ⊆ y) : s ∪ x ⊆ s ∪ y :=
finset.union_subset_union (finset.subset.refl _) h
-/

end general_lemmas

/-- An indexed family of finite sets is given by an `ι : α → finset β`, and a product of such a
family is a function `f : α → β` such that `f x ∈ ι x` for all `x : α`.  A *matching* is an
injective product of an indexed family of sets.

A `matching` can be used as a function. -/
@[ext]
structure matching {α β : Type*} (ι : α → finset β) :=
(f : α → β)
(mem_prod' : ∀ (a : α), f a ∈ ι a)
(injective' : injective f)

namespace matching
variables {α : Type u} {β : Type v} {ι : α → finset β}

instance : has_coe_to_fun (matching ι) := ⟨_, matching.f⟩

@[simp] lemma mem_prod (f : matching ι) (a : α) : f a ∈ ι a := f.mem_prod' a
@[simp] lemma injective (f : matching ι) : injective f := f.injective'
@[simp] lemma eq_coe (f : matching ι) (a : α) : f.f a = f a := rfl

lemma card_le_card_bind [decidable_eq β] (f : matching ι) (s : finset α) :
  s.card ≤ (s.bind ι).card :=
begin
  rw ←finset.card_image_of_injective s f.injective,
  apply finset.card_le_of_subset,
  intros b,
  rw [finset.mem_image, finset.mem_bind],
  rintros ⟨a, ha, rfl⟩,
  exact ⟨a, ha, f.mem_prod a⟩,
end

end matching

variables {α : Type u} {β : Type v} [decidable_eq α] [decidable_eq β]
variables (ι : α → finset β)

theorem hall_hard_inductive_zero [fintype α] (hn : card α = 0) :
  nonempty (matching ι) :=
begin
  rw fintype.card_eq_zero_iff at hn,
  exact ⟨{ f := λ a, false.elim (hn a),
           mem_prod' := by tauto,
           injective' := by tauto }⟩,
end

theorem hall_hard_inductive_one [fintype α] (hn : card α = 1)
  (hr : ∀ (s : finset α), s.card ≤ (s.bind ι).card) :
  nonempty (matching ι) :=
begin
  rcases fintype.card_eq_one_iff.mp hn with ⟨a, ha⟩,
  have hr' : 0 < (ι a).card,
  { refine lt_of_lt_of_le nat.one_pos _,
    convert hr {a},
    simp, },
  rcases classical.indefinite_description _ (finset.card_pos.mp hr') with ⟨b, hb⟩,
  exact ⟨{ f := λ _, b,
           mem_prod' := λ a', by rwa ha a',
           injective' := λ a1 a2, by { rw [ha a1, ha a2], tauto, } }⟩,
end

section A_step

/-- Given an indexed family of finite sets, gives he indexed family from dropping `a₀` from the
domain and `b₀` from the codomain. -/
def ι_remove (a₀ : α) (b₀ : β) : {x : α | x ≠ a₀} → finset β := λ x, (ι x).erase b₀

lemma ι_remove.subset (a₀ : α) (b₀ : β) (x) : ι_remove ι a₀ b₀ x ⊆ ι x :=
begin
  rcases x with ⟨x, hx⟩,
  intro y,
  simp only [ι_remove, and_imp, imp_self, finset.mem_erase, forall_true_iff],
end

/-- Giving a matching for `ι_remove`, extend it into a matching for the original indexed family. -/
def matching_of_ι_remove (a₀ : α) (b₀ : β) (hb₀ : b₀ ∈ ι a₀)
  (f' : matching (ι_remove ι a₀ b₀)) : matching ι :=
{ f := λ a, if ha : a = a₀ then b₀ else f' ⟨a, ha⟩,
  mem_prod' := λ a, begin
    split_ifs with ha,
    { rwa [ha], },
    exact ι_remove.subset ι a₀ b₀ ⟨a, ha⟩ (f'.mem_prod ⟨a, ha⟩),
  end,
  injective' := begin
    intros a a',
    have hb : ∀ {x}, b₀ ≠ f' x,
    { intro x,
      have mem_prod' := f'.mem_prod x,
      intro h,
      rw ←h at mem_prod',
      simpa [ι_remove] using mem_prod', },
    by_cases h : a = a₀; by_cases h' : a' = a₀; simp [h, h', f'.injective, hb, hb.symm],
  end }

lemma card_le_bind_ι_remove (a₀ : α) (b₀ : β) (hb₀ : b₀ ∈ ι a₀)
  (s' : finset {x | x ≠ a₀})
  (h : s'.card < (s'.bind (λ x, ι x)).card) :
  s'.card ≤ (s'.bind (ι_remove ι a₀ b₀)).card :=
begin
  dunfold ι_remove,
  rw finset.bind_erase,
  by_cases hb : b₀ ∈ s'.bind (λ x, ι x),
  { rw finset.card_erase_of_mem hb,
    exact le_pred_if_lt h, },
  { rw finset.erase_eq_of_not_mem hb,
    exact nat.le_of_lt h, },
end

lemma nonempty_of_card_le
  (hr : ∀ (s : finset α), s.card ≤ (s.bind ι).card)
  (a : α) :
  (ι a).nonempty :=
begin
  rw ←finset.card_pos,
  apply nat.lt_of_lt_of_le (nat.one_pos),
  convert hr {a},
  rw finset.singleton_bind,
end

lemma hall_hard_inductive_A [fintype α] [nonempty α] (n : ℕ) (hn : card α = n.succ.succ)
  (hr : ∀ (s : finset α), s.card ≤ (s.bind ι).card)
  (ih : ∀ (m : ℕ), m < n.succ.succ →
          ∀ {α' : Type u} {β' : Type v} [decidable_eq α'] [decidable_eq β']
          (ι' : α' → finset β') [fintype α'],
          by exactI (card α' = m) →
          (∀ (s : finset α'), s.card ≤ (s.bind ι').card) → nonempty (matching ι'))
  (hc : ∀ (s : finset α), s.nonempty → s ≠ finset.univ → s.card < (s.bind ι).card) :
  nonempty (matching ι) :=
begin
  let a₀ : α := classical.choice (by apply_instance),
  rcases classical.indefinite_description _ (nonempty_of_card_le ι hr a₀) with ⟨b₀, hb₀⟩,
  have ih' := ih n.succ (lt_add_one _) (ι_remove ι a₀ b₀) (by { rw [card_ne_eq, hn], refl }) _,
  { cases ih' with f',
    exact ⟨matching_of_ι_remove ι a₀ b₀ hb₀ f'⟩, },
  { intro s',
    specialize hc (s'.image coe),
    simp only [ne.def, finset.nonempty.image_iff] at hc,
    rw finset.card_image_of_injective s' subtype.coe_injective at hc,
    by_cases he : s'.nonempty,
    { specialize hc he (λ h, by { have h' := finset.mem_univ a₀, rw [←h] at h', simpa using h' }),
      apply card_le_bind_ι_remove ι a₀ b₀ hb₀ s',
      convert hc using 2,
      ext y,
      simp only [exists_prop, set_coe.exists, exists_and_distrib_right, finset.mem_bind,
                 exists_eq_right, finset.mem_image, subtype.coe_mk], },
    { rw [finset.nonempty_iff_ne_empty, not_not] at he, subst s', simp, }, },
end

end A_step

section B_step

/-- Given an indexed family of finite sets, restrict the domain to a finite set `s`. -/
@[reducible] def ι_restrict (s : finset α) : (s : set α) → finset β :=
λ x, ι x

/-- Given an indexed family of finite sets, restrict the domain to the complement of a finite set
`s` and the codomain to the complement of `s.bind ι`. -/
@[reducible] def ι_compl [fintype α] (s : finset α) : (↑(sᶜ) : set α) → finset β :=
λ x, ι x \ s.bind ι

lemma ι_restrict.card (s : finset α)
  (hr : ∀ (s : finset α), s.card ≤ (s.bind ι).card)
  (A : finset (s : set α)) :
  A.card ≤ (A.bind (ι_restrict ι s)).card :=
begin
  convert hr (A.image coe) using 1,
  { rw finset.card_image_of_injective _ subtype.coe_injective, },
  { apply congr_arg,
    ext y,
    simp [ι_restrict], },
end

lemma ι_compl.subset [fintype α] (s : finset α) (x) :
  ι_compl ι s x ⊆ ι x :=
begin
  intro y,
  simp only [finset.mem_sdiff],
  rintro ⟨h, _⟩,
  exact h,
end

lemma ι_compl_card₀ [fintype α] (s : finset α)
  (hc : s.card = (s.bind ι).card)
  (hr : ∀ (s : finset α), s.card ≤ (s.bind ι).card)
  (A : finset ((↑(sᶜ) : set α) : Type u))
  (hA : (A.bind (ι_compl ι s)).card < A.card) :
  false :=
begin
  have hAc : (A.image coe).card = A.card,
  { rw finset.card_image_of_injective A subtype.coe_injective, },
  have key : (A.image coe ∪ s).bind ι ⊆ A.bind (ι_compl ι s) ∪ s.bind ι,
  { intro y,
    rw [finset.mem_union],
    by_cases hy : y ∈ s.bind ι,
    { intro, right, exact hy, },
    { rw [finset.bind_union, finset.mem_union],
      simp only [hy, or_false],
      simp only [not_exists, exists_prop, not_and, finset.mem_bind] at hy,
      simp only [finset.mem_bind, exists_imp_distrib, finset.mem_image, finset.mem_sdiff],
      rintro _ ⟨x, hx⟩ ha rfl hyx,
      use [⟨x, hx⟩, ha, hyx],
      push_neg,
      exact hy, }, },
  have key' := le_trans (finset.card_le_of_subset key) (finset.card_union_le _ _),
  rw ←hc at key',
  have Bcard : (A.image coe ∪ s).card = (A.image coe).card + s.card,
  { have hAsub : A.image coe ⊆ sᶜ,
    { intro x,
      rw finset.mem_image,
      rintro ⟨⟨x', hx⟩, hx', rfl⟩,
      exact hx, },
    have disj : disjoint (A.image coe) s,
    { rw finset.disjoint_iff_inter_eq_empty,
      rw [←finset.subset_empty, ←finset.compl_inter_self s],
      exact finset.inter_subset_inter_right hAsub, },
    exact finset.card_disjoint_union disj, },
  have hr' := hr (A.image coe ∪ s),
  rw [Bcard, hAc] at hr',
  linarith,
end

lemma ι_compl.card [fintype α] (s : finset α)
  (hc : s.card = (s.bind ι).card)
  (hr : ∀ (s : finset α), s.card ≤ (s.bind ι).card)
  (A : finset ((↑(sᶜ) : set α) : Type u)) :
  A.card ≤ (A.bind (ι_compl ι s)).card :=
begin
  revert A,
  by_contra h,
  push_neg at h,
  rcases h with ⟨A, hA⟩,
  apply ι_compl_card₀ ι s hc hr A hA,
end

lemma ι_restrict.compl_matching_disj [fintype α] (s : finset α)
  (f : matching (ι_restrict ι s))
  (f' : matching (ι_compl ι s))
  {a b : α} {ha : a ∈ s} {hb : ¬ b ∈ s} :
  f ⟨a, ha⟩ ≠ f' ⟨b, by simp [hb]⟩ :=
begin
  intro h,
  have hf : f ⟨a, ha⟩ ∈ s.bind ι,
  { rw finset.mem_bind,
    exact ⟨a, ha, f.mem_prod _⟩, },
  have hf' : ¬ f' ⟨b, by simp [hb]⟩ ∈ s.bind ι,
  { have k := f'.mem_prod ⟨b, by simp [hb]⟩,
    rw finset.mem_sdiff at k,
    exact k.2, },
  rw h at hf,
  exact hf' hf,
end

/-- Given a matching on the restriction and the complement, combine them into a matching for the
original indexed family. -/
def combine_matchings [fintype α]
  (s : finset α)
  (f' : matching (ι_restrict ι s))
  (f'' : matching (ι_compl ι s)) :
  matching ι :=
{ f := λ x, if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, by simp [h]⟩,
  mem_prod' := λ x, begin
    split_ifs with h,
    { apply f'.mem_prod },
    { exact ι_compl.subset ι s _ (f''.mem_prod ⟨x, by simp [h]⟩), },
  end,
  injective' := λ x1 x2, begin
    dsimp,
    split_ifs with h1 h2,
    { intro h,
      have h' := f'.injective h,
      simpa using h', },
    { intro h,
      exfalso,
      exact ι_restrict.compl_matching_disj ι s f' f'' h, },
    { intro h,
      exfalso,
      exact ι_restrict.compl_matching_disj ι s f' f'' h.symm, },
    { intro h,
      have h' := f''.injective h,
      simpa using h', },
  end }

lemma hall_hard_inductive_B [fintype α] (n : ℕ) (hn : card α = n.succ.succ)
  (hr : ∀ (s : finset α), s.card ≤ (s.bind ι).card)
  (ih : ∀ (m : ℕ), m < n.succ.succ →
          ∀ {α' : Type u} {β' : Type v} [decidable_eq α'] [decidable_eq β']
          (ι' : α' → finset β') [fintype α'],
          by exactI (card α' = m) →
          (∀ (s : finset α'), s.card ≤ (s.bind ι').card) →
          nonempty (matching ι'))
  (s : finset α) (hne : s.nonempty) (hnu : s ≠ finset.univ)
  (hc : s.card = (s.bind ι).card) :
  nonempty (matching ι) :=
begin
  let ι' := ι_restrict ι s,
  let ι'' := ι_compl ι s,
  have ih' := ih (card (s : set α))
    (by { rw ←hn, convert finset.card_lt_of_ne_univ _ hnu, convert fintype.card_coe _ })
    ι' rfl
    (λ A, by convert ι_restrict.card ι s hr A),
  have ih'' := ih (card ((sᶜ : finset α) : set α))
    (by { rw ←hn, convert finset.card_compl_lt_of_nonempty _ hne, convert fintype.card_coe _ })
    ι'' rfl
    (λ A, by convert ι_compl.card ι s hc hr A),
  cases ih' with f',
  cases ih'' with f'',
  exact ⟨combine_matchings ι s f' f''⟩,
end

end B_step

lemma hall_hard_inductive [fintype α] (k : ℕ) (hn : fintype.card α = k)
  (hr : ∀ (s : finset α), s.card ≤ (s.bind ι).card) :
  nonempty (matching ι) :=
begin
  tactic.unfreeze_local_instances,
  revert α β,
  refine nat.strong_induction_on k (λ n ih, _),
  intros,
  rcases n with (_|_|_),
  { apply hall_hard_inductive_zero ι hn, },
  { apply hall_hard_inductive_one ι hn hr, },
  { have hn' : 1 < card α,
    { rw hn,
      exact nat.succ_lt_succ (nat.succ_pos _), },
    haveI hα : nontrivial α := one_lt_card_iff_nontrivial.mp hn',
    by_cases hc : ∀ (s : finset α), s.nonempty → s ≠ finset.univ → s.card < (s.bind ι).card,
    { exact hall_hard_inductive_A ι n hn hr ih hc, },
    { push_neg at hc,
      rcases hc with ⟨s, hne, hnu, hc'⟩,
      have hc := nat.le_antisymm (hr _) hc',
      exact hall_hard_inductive_B ι n hn hr ih s hne hnu hc, }, },
end

theorem hall [fintype α] :
  (∀ (s : finset α), s.card ≤ (s.bind ι).card) ↔ nonempty (matching ι) :=
begin
  split,
  { intro hr,
    exact hall_hard_inductive ι (card α) rfl hr, },
  { rintros ⟨f⟩,
    exact f.card_le_card_bind, },
end
