/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Martin Zinkevich
-/
import measure_theory.measure_space
import tactic.fin_cases

--import algebra.big_operators.intervals
--import data.finset.intervals

/-!
# Lemmas regarding is_pi_system.

is_pi_system is similar, but not identical to, the classic π-system encountered in measure
theory. In particular, it is not required to be nonempty, and it isn't closed under disjoint
intersection (thus neither more nor less general than a typical π-system).

## Main statements

* generate_pi_system. generate_pi_system g gives the minimal pi system containing g. This can
  be considered a Galois insertion into both measurable spaces and sets.

* is_pi_system_finite_Inter nonempty intersection of a finite number of elements of
  π-system is in a π-system.
* is_pi_system_union. any element of the "supremum" of a set of pi systems can be represented
  as the intersection of representative elements from a finite number of pi systems.

## Implementation details

* is_pi_system is a predicate, not a type. Thus, we don't explicitly define the galois
  insertion, nor do we define a complete lattice. In theory, we could define a complete
  lattice and galois insertion on the is_pi_system.

-/

open measure_theory measurable_space
open_locale classical

lemma is_pi_system.singleton {α} (S : set α) : is_pi_system ({S} : set (set α)) :=
begin
  intros s t h_s h_t h_ne,
  rw [set.mem_singleton_iff.1 h_s, set.mem_singleton_iff.1 h_t, set.inter_self,
      set.mem_singleton_iff],
end

lemma is_pi_system_finite_Inter {α} (g : set (set α)) (h_pi : is_pi_system g) 
  (m : ℕ) (f : fin m.succ → set α) (h_f : ∀ i, f i ∈ g) (h_nonempty : (⋂ i, f i).nonempty) :
  ((⋂ i, f i) ∈ g) := begin
  induction m,
  { have h_eq : set.Inter f = (f 0), 
    { ext a, simp, split; intros h_eq_1, 
      apply h_eq_1 0,
      intros i, cases i,
      cases i_val,
      apply h_eq_1,
      rw nat.succ_lt_succ_iff at i_property,
      apply false.elim (nat.not_lt_zero _ i_property) },
   rw h_eq,
   apply h_f },
 { have h_eq : (⋂ (i : fin m_n.succ.succ), f i) = f 0 ∩ (⋂ (i : fin m_n.succ), f (i.succ)),
   { ext a, split; intros h_eq_1; simp at h_eq_1; simp [h_eq_1],
     intros i,  cases (decidable.em (i = 0)),
     { subst i, apply h_eq_1.left },
     { have h_eq_2 := h_eq_1.right (i.pred h), simp at h_eq_2, apply h_eq_2 } },
   rw h_eq,
   apply h_pi,
   apply h_f,
   apply m_ih,
   { intros i, apply h_f },
   by_contradiction h_contra,
   apply h_nonempty.ne_empty,
   rw h_eq,
   rw set.not_nonempty_iff_eq_empty.1 h_contra,
   simp,
   rw ← h_eq,
   apply h_nonempty },
end

lemma exists_fin_intro {α} {β : Type*} (g : set (set α)) [F : fintype β]
  [N : nonempty β] (f : β → set α) (h : ∀ b, f b ∈ g) 
: ∃ (m : ℕ) (f' : fin m.succ → set α), (∀ i, f' i ∈ g) ∧ ((⋂ i, f' i) = (⋂ i, f i)) := begin
  have h5 := classical.choice (nonempty_of_trunc (fintype.equiv_fin β)),
  apply exists.intro ((fintype.card β).pred),
  have h6 : (fintype.card β).pred.succ = (fintype.card β),
  { apply nat.succ_pred_eq_of_pos, rw ← fintype.card_pos_iff at N, apply N },
  rw [h6],
  apply exists.intro (f ∘ h5.inv_fun),
    split,
    { intros i, apply h, },
    { ext a, split; intros h7; simp at h7; simp [h7]; intros i,
      have h8 := h7 (h5.to_fun i),
      simp at h8, apply h8 },  
end

lemma is_pi_system_intro {α} {β : Type*} [fintype β] [N : nonempty β] 
  {g : set (set α)} (h_pi : is_pi_system g) (f : β → set α)
  (h_f_in : ∀ b, f b ∈ g) (h_nonempty : (set.Inter f).nonempty) :
  set.Inter f ∈ g :=
begin
  have h_exists := exists_fin_intro g f h_f_in,
  rcases h_exists with ⟨m, ⟨f', h_f'⟩⟩,
  rw ← h_f'.right,
  apply is_pi_system_finite_Inter g h_pi _ _ h_f'.left,
  rw h_f'.right,
  apply h_nonempty,
end

inductive generate_pi_system {α} (g : set (set α)) : set (set α)
| base {s : set α} (h_s : s ∈ g) : generate_pi_system s
| inter {s t : set α} (h_s : generate_pi_system s)  (h_t : generate_pi_system t) 
  (h_nonempty : (s ∩ t).nonempty) : generate_pi_system (s ∩ t)

lemma is_pi_system_generate_pi_system {α} (g : set (set α)) :
  is_pi_system (generate_pi_system g) :=
  λ s t h_s h_t h_nonempty, generate_pi_system.inter h_s h_t h_nonempty



lemma sub_generate_pi_system {α} (g : set (set α)) :
  g ⊆ generate_pi_system g :=
begin
  rw set.subset_def,
  apply generate_pi_system.base,
end

lemma generate_pi_system_intro {α} {β : Type*} [fintype β] [N : nonempty β] 
  (g : set (set α)) (f : β → set α)
  (h_f_in : ∀ b, f b ∈ g) (h_nonempty : (set.Inter f).nonempty) :
  set.Inter f ∈ generate_pi_system g :=
begin
  classical,
  apply is_pi_system_intro,
  apply is_pi_system_generate_pi_system,
  intros b,
  apply generate_pi_system.base,
  apply h_f_in,
  apply h_nonempty,
end 

lemma generate_pi_system_subset {α} {g t : set (set α)} (h_t : is_pi_system t)
  (h_sub : g ⊆ t) : (generate_pi_system g : (set (set α))) ⊆ t := begin
  rw set.subset_def,
  intros x h,
  induction h with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  apply h_sub h_s,
  apply h_t _ _ h_s h_u h_nonempty
end

lemma generate_pi_system_eq {α} {g : set (set α)} (h_pi : is_pi_system g) :
  generate_pi_system g = g := begin
  apply le_antisymm,
  apply generate_pi_system_subset,
  apply h_pi,
  apply set.subset.refl,
  apply sub_generate_pi_system,
end

lemma generate_pi_system_measurable_set {α} [M : measurable_space α] {g : set (set α)} 
  (h_meas_g : ∀ s ∈ g, measurable_set s) (t : set α)
  (h_in_pi : generate_pi_system g t) : measurable_set t :=
begin
  induction h_in_pi with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  apply h_meas_g _ h_s,
  apply measurable_set.inter h_s h_u,
end

lemma generate_from_measurable_set_of_generate_pi_system {α} {g : set (set α)} (t : set α) : generate_pi_system g t →
  (measurable_space.generate_from g).measurable_set' t := begin
  apply generate_pi_system_measurable_set,
  intros s h_s_in_g,
  apply measurable_space.measurable_set_generate_from h_s_in_g,
end

lemma generate_from_generate_pi_system_eq {α} {g : set (set α)} : 
  (measurable_space.generate_from (generate_pi_system g)) =
  (measurable_space.generate_from g) := begin
  apply le_antisymm;apply measurable_space.generate_from_le,
  { intros t h_t,
    apply generate_from_measurable_set_of_generate_pi_system,
    apply h_t },
  { intros t h_t, apply measurable_space.measurable_set_generate_from, 
    apply generate_pi_system.base h_t },
end

lemma set.nonempty_of_nonempty_subset {α} (T V : set α)
  (h_nonempty_T : T.nonempty) (h_sub : T ⊆ V) : V.nonempty := begin
  rw set.nonempty_def,
  rw set.nonempty_def at h_nonempty_T,
  cases h_nonempty_T with x h_nonempty_T,
  use x,
  apply h_sub h_nonempty_T,
end



lemma generate_pi_system_elim {α} (g : set (set α)) (s : set α)
  (h : generate_pi_system g s) : (s ∈ g ∧ s = ∅) ∨
  (s.nonempty ∧ ∃ (m : ℕ) (f : fin m.succ → set α), (∀ i, f i ∈ g) ∧ (s=(⋂ i, f i))) :=
begin
  induction h with s' h_s' s' t' h_gen_s' h_gen_t' h_nonempty h_s' h_t',
  cases (set.eq_empty_or_nonempty s') with h_empty h_nonempty,
  { left, apply and.intro h_s' h_empty },
  { right, apply and.intro h_nonempty,
    use [0, (λ _, s')], apply and.intro (λ _, h_s'),
    ext a, simp },
  right,
  apply and.intro h_nonempty, 
  cases h_s',
  { apply false.elim (h_nonempty.left.ne_empty h_s'.right), },
  cases h_t',
  { apply false.elim (h_nonempty.right.ne_empty h_t'.right), },
  rcases h_s' with ⟨h_s'_nonempty, ⟨m_s', ⟨f_s', h_s'⟩⟩⟩,
  rcases h_t' with ⟨h_t'_nonempty, ⟨m_t', ⟨f_t', h_t'⟩⟩⟩,
  have h_f'' := exists_fin_intro g (λ x : sum (fin m_s'.succ) (fin m_t'.succ), match x with
  | (sum.inl i) := f_s' i
  | (sum.inr i) := f_t' i
  end) _,
  rcases h_f'' with ⟨m'', ⟨f'', h_f''⟩⟩,
  use [m'', f''],
  apply and.intro h_f''.left,
  rw [h_f''.right, h_s'.right, h_t'.right],
  { ext a, simp },
  { intros b, cases b; simp [h_s'.left, h_t'.left] },
end

lemma set.nonempty_of_subset {α} {s t:set α} (h : s ⊆ t) (h_nonempty : set.nonempty s) :
  set.nonempty t := begin
  rw set.nonempty_def,
  use (h_nonempty.some),
  apply (h h_nonempty.some_mem),
end

/- This theorem shows that every element of the pi system generated by the union of the
   pi systems can be represented by a finite union of elements from the pi systems. -/
lemma is_pi_system_union' {α} {β : Type*} {g : β → (set (set α))}
  (h_pi : ∀ b : β, is_pi_system (g b))
  (t : set α)
  (h_t : t ∈ generate_pi_system (⋃ (b : β), g b)) : 
  (∃ (T : finset β) (f : β → set α), (t = ⋂ b ∈ T, f b) ∧ (∀ b ∈ T, f b ∈ (g b))) :=
begin
  induction h_t with s h_s s t' h_gen_s h_gen_t' h_nonempty h_s h_t',
  { rcases h_s with ⟨t', ⟨⟨b, rfl⟩, h_s_in_t'⟩⟩,
    apply exists.intro {b},
    use (λ b', s),
    split,
    { ext a, split; intros h1, simp, apply (λ _ _, h1),
      simp at h1, apply h1 b (finset.mem_singleton_self _) },
    { intros b' h_b', rw finset.mem_singleton at h_b',
      rw h_b', apply h_s_in_t' } }, 
  { rcases h_t' with ⟨T_t', ⟨f_t', ⟨rfl, h_t'⟩⟩⟩,
    rcases h_s with ⟨T_s, ⟨f_s, ⟨rfl, h_s⟩ ⟩ ⟩,
    use [(T_s ∪ T_t'), (λ (b:β),
      if (b ∈ T_s) then (
        if (b ∈ T_t') then (f_s b ∩ (f_t' b)) 
        else (f_s b)) 
      else (
        if (b ∈ T_t') then (f_t' b)
        else (∅:set α)))],
    split,
    { ext a,
      split; intros h1; simp at h1; simp [h1],
      { intros b h_b_in, split_ifs,
        apply set.mem_inter (h1.left b h) (h1.right b h_1),
        apply h1.left b h,
        apply h1.right b h_1,
        apply false.elim (h_b_in.elim h h_1) },
      split,
      { intros b h_b_in, 
        have h2 := h1 b (or.inl h_b_in),
        rw if_pos h_b_in at h2,
        split_ifs at h2,
        apply h2.left,
        apply h2 },
      { intros b h_b_in,
        have h2 := h1 b (or.inr h_b_in),
        rw if_pos h_b_in at h2,
        split_ifs at h2,
        apply h2.right,
        apply h2 } },
    intros b h_b,
    split_ifs,
    apply h_pi b,
    apply h_s b h,
    apply h_t' b h_1,
    apply set.nonempty_of_subset _ h_nonempty,
    apply set.inter_subset_inter,
    { apply set.subset.trans, apply set.Inter_subset, apply b, apply set.Inter_subset, apply h },
    { apply set.subset.trans, apply set.Inter_subset, apply b, apply set.Inter_subset, apply h_1 },
    apply h_s _ h,
    apply h_t' _ h_1,
    rw finset.mem_union at h_b,
    apply false.elim (h_b.elim h h_1) },
end

lemma is_pi_system_union {α} {β : Type*} {g : β → (set (set α))}
  (h_pi : ∀ b : β, is_pi_system (g b))
  (h_nonempty : ∀ b : β, (g b).nonempty)
  (t : set α)
  (h_t : t ∈ generate_pi_system (⋃ (b : β), g b)) : 
  (∃ (T : finset β) (f : β → set α), (t = ⋂ b ∈ T, f b) ∧ (∀ (b : β), f b ∈ (g b))) :=
begin
  classical,
  cases (generate_pi_system_elim _ _ h_t) with h_t_empty h_t_union,
  { rcases h_t_empty with ⟨⟨g', ⟨⟨b, rfl⟩, h_t_in⟩⟩, rfl⟩,
    apply exists.intro {b},
    use (λ b', ite (b' = b) ∅ (h_nonempty b').some),
    split,
    { ext a, simp only [exists_prop, set.mem_empty_eq, false_iff, set.mem_Inter, not_forall],
      use b, simp only [set.mem_empty_eq, and_true, if_true, eq_self_iff_true, not_false_iff],
      rw finset.mem_singleton },    
    { intros b', split_ifs, rw h, apply h_t_in, apply set.nonempty.some_mem } },
  { rcases h_t_union with ⟨h_t_nonempty,⟨m, ⟨f, ⟨h_f_def, h_t_def⟩⟩⟩⟩,
    have h_f' : ∀ (i : fin m.succ), ∃ (b : β), f i ∈ g b,
    { intros i, rcases (h_f_def i) with ⟨t',⟨⟨b, h_t'_eq⟩, h_f_i_in_t'⟩⟩,
      subst t',apply exists.intro b,
      apply h_f_i_in_t' },
    rw classical.skolem at h_f',
    cases h_f' with f' h_f',
    apply exists.intro (finset.image f' (finset.univ)),
    have h_f'' : ∀ (b : β), ∃ (s : set α), (s ∈ g b) ∧ (b ∈  (finset.image f' (finset.univ)) →
      s = ⋂ (i : fin m.succ) (H : f' i = b), f i),
    { intros b, cases classical.em (b ∈ finset.image f' (finset.univ)) with h_b_in h_b_notin,
      { apply exists.intro (⋂ (i : subtype (λ (i' : fin m.succ), f' i' = b)), f i),
        split,
        have h_sub_non : nonempty (subtype (λ (i' : fin m.succ), f' i' = b)),
        { simp at h_b_in, cases  h_b_in with i h_b_in,
          apply nonempty.intro (subtype.mk i h_b_in) },
        apply @is_pi_system_intro α _ _ h_sub_non,  
        apply h_pi,
        { intros i, cases i,
          have h_f'_2  := h_f' i_val,
          rw  i_property at h_f'_2,
          simp, apply h_f'_2 },
          have h_sub_t :  t ⊆ (⋂ (i : {i' // f' i' = b}), f ↑i),
          { rw h_t_def, rw set.subset_def, intros x h_x, simp at h_x,
            simp, intros i h_i_eq, apply h_x },
        apply set.nonempty_of_nonempty_subset _ _ h_t_nonempty h_sub_t,
        intros h_2,
        { ext a, split; intros h_3; simp at h_3; simp [h_3];
          intros i h_4; apply h_3, apply h_4,
          simp, apply h_4, }, },
      { cases (set.nonempty_def.1 (h_nonempty b)) with s h_6,
        use s,
        apply and.intro h_6, intros h_7,
        apply absurd h_7 h_b_notin } },
    rw classical.skolem at h_f'',
    cases h_f'' with f'' h_f'',
    apply exists.intro f'',
    split,
    { rw h_t_def, ext a, split; intros h1; simp at h1; simp [h1]; intros i,
      { rw (h_f'' (f' i)).right _,
        intros s h_s,
        cases h_s with i' h_s,
        rw ← h_s,
        simp,
        intros h_i',
        apply h1, simp },
      { have h1_i := h1 i,
        rw (h_f'' (f' i)).right _ at h1_i,
        simp at h1_i,
        apply h1_i,
        refl, 
        simp } },
      intros b, apply (h_f'' b).left },
end


lemma is_pi_system_union {α} {β : Type*} {g : β → (set (set α))}
  (h_pi : ∀ b : β, is_pi_system (g b))
  (h_nonempty : ∀ b : β, (g b).nonempty)
  (t : set α)
  (h_t : t ∈ generate_pi_system (⋃ (b : β), g b)) : 
  (∃ (T : finset β) (f : β → set α), (t = ⋂ b ∈ T, f b) ∧ (∀ (b : β), f b ∈ (g b))) :=
begin
  classical,
  cases (generate_pi_system_elim _ _ h_t) with h_t_empty h_t_union,
  { rcases h_t_empty with ⟨⟨g', ⟨⟨b, rfl⟩, h_t_in⟩⟩, rfl⟩,
    apply exists.intro {b},
    have h_f : ∀ b' : β, ∃ (s : set α), (s ∈ g b') ∧ (b' = b → s = ∅),
    { intros b', cases classical.em (b' = b) with h_b'_eq_b h_b'_ne_b,
      { subst b', apply exists.intro (∅ : set α), simp [h_t_in] },
      { cases (set.nonempty_def.1 (h_nonempty b')) with s h_s,
        apply exists.intro s, simp [h_s, h_b'_ne_b] } },
    rw classical.skolem at h_f,
    cases h_f with f h_f,
    have h_f_b_eq_t : f b = ∅,
    { apply (h_f b).right, refl },
    apply exists.intro f,
    split,
    { ext a, split; intros h1,
      { simp [h1, h_f], intros b' h_b',
        rw @finset.mem_singleton β b b' at h_b',
        subst b', rw h_f_b_eq_t, apply h1 },
      simp at h1,  rw h_f_b_eq_t at h1, apply h1 },
    { intros b', apply (h_f b').left } },
  { rcases h_t_union with ⟨h_t_nonempty,⟨m, ⟨f, ⟨h_f_def, h_t_def⟩⟩⟩⟩,
    have h_f' : ∀ (i : fin m.succ), ∃ (b : β), f i ∈ g b,
    { intros i, rcases (h_f_def i) with ⟨t',⟨⟨b, h_t'_eq⟩, h_f_i_in_t'⟩⟩,
      subst t',apply exists.intro b,
      apply h_f_i_in_t' },
    rw classical.skolem at h_f',
    cases h_f' with f' h_f',
    apply exists.intro (finset.image f' (finset.univ)),
    have h_f'' : ∀ (b : β), ∃ (s : set α), (s ∈ g b) ∧ (b ∈  (finset.image f' (finset.univ)) →
      s = ⋂ (i : fin m.succ) (H : f' i = b), f i),
    { intros b, cases classical.em (b ∈ finset.image f' (finset.univ)) with h_b_in h_b_notin,
      { apply exists.intro (⋂ (i : subtype (λ (i' : fin m.succ), f' i' = b)), f i),
        split,
        have h_sub_non : nonempty (subtype (λ (i' : fin m.succ), f' i' = b)),
        { simp at h_b_in, cases  h_b_in with i h_b_in,
          apply nonempty.intro (subtype.mk i h_b_in) },
        apply @is_pi_system_intro α _ _ h_sub_non,  
        apply h_pi,
        { intros i, cases i,
          have h_f'_2  := h_f' i_val,
          rw  i_property at h_f'_2,
          simp, apply h_f'_2 },
          have h_sub_t :  t ⊆ (⋂ (i : {i' // f' i' = b}), f ↑i),
          { rw h_t_def, rw set.subset_def, intros x h_x, simp at h_x,
            simp, intros i h_i_eq, apply h_x },
        apply set.nonempty_of_nonempty_subset _ _ h_t_nonempty h_sub_t,
        intros h_2,
        { ext a, split; intros h_3; simp at h_3; simp [h_3];
          intros i h_4; apply h_3, apply h_4,
          simp, apply h_4, }, },
      { cases (set.nonempty_def.1 (h_nonempty b)) with s h_6,
        use s,
        apply and.intro h_6, intros h_7,
        apply absurd h_7 h_b_notin } },
    rw classical.skolem at h_f'',
    cases h_f'' with f'' h_f'',
    apply exists.intro f'',
    split,
    { rw h_t_def, ext a, split; intros h1; simp at h1; simp [h1]; intros i,
      { rw (h_f'' (f' i)).right _,
        intros s h_s,
        cases h_s with i' h_s,
        rw ← h_s,
        simp,
        intros h_i',
        apply h1, simp },
      { have h1_i := h1 i,
        rw (h_f'' (f' i)).right _ at h1_i,
        simp at h1_i,
        apply h1_i,
        refl, 
        simp } },
      intros b, apply (h_f'' b).left },
end


