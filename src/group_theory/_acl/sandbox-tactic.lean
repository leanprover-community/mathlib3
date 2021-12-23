import tactic

import data.finset.basic

/- Pour prouver une appartenance a ∈ s -/

example : 8 ∈ ({1, 3, 9, 12, 18, 23, 8 } : finset ℕ) :=
begin
  iterate {
    rw finset.mem_insert,
     exact or.intro_left _ rfl <|> apply or.intro_right _, } ,
  rw finset.mem_singleton,
end


example : 8 ∈ ({1, 3, 9, 12, 18, 23, 8 } : finset ℕ) :=
begin
  simp only [finset.mem_insert, or.intro_left, or.intro_right, finset.mem_singleton],
end

/- Pour prouver une inclusion s ⊆ t entre deux finset explicites -/

example : ({ 12, 8, 2, 3} : finset ℕ) ⊆ {1, 2,9, 12, 8, 3} :=
begin
  iterate { rw finset.insert_subset, apply and.intro _},
  refine finset.singleton_subset_iff.mpr _,
  all_goals {
    iterate {
      rw finset.mem_insert,
      exact or.intro_left _ rfl <|> apply or.intro_right _, } ,
      try { exact finset.mem_singleton.mpr rfl, },
  }
end

example : ({ 12, 8, 2, 3} : finset ℕ) ⊆ {1, 2,9, 12, 8, 3} :=
begin
    simp only [finset.insert_subset, and.intro _, finset.singleton_subset_iff,
      finset.mem_insert, or.intro_left, or.intro_right, finset.mem_singleton, and_true],
end
