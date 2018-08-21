
import data.coinductive.basic .tactic

universes u₀ u₁ u₂

namespace coinduction
variables {ι : Type u₁}
variables {α : ι → Type u₀}
variables {β : Π i, α i → Type u₂}
variables {γ : Π i (a : α i), β i a → ι}
variables {i : ι}

open coinduction.approx

namespace subtree
open nat
inductive select' : ∀ {j : ι} {n : ℕ}, cofix_a γ j n → path @β → α i → Prop
| nil {n : ℕ} (x : α i) (z : cofix_a γ i (succ n)) :
  x = head' z →
  select' z [] x
| cons {n : ℕ} {j} (a : α j) (x : β j a) (y : α i)
       (ch : Π b, cofix_a γ (γ j a b) n)
       (z : cofix_a γ j (succ n)) (ps : path @β) :
  z = cofix_a.intro a ch →
  select' (ch x) ps y →
  select' z (⟨_,a,x⟩ :: ps) y
variables {n : ℕ}

inductive subtree' : ∀ {j : ι} {m : ℕ} (ps : path @β) (x : cofix_a γ j m), cofix_a γ i n → Prop
| nil (x y : cofix_a γ i n) :
  x = y →
  subtree' [] x y
| cons {m : ℕ} {j} (a : α j) (x : β j a) (y : cofix_a γ i n )
       (ch : Π b, cofix_a γ (γ j a b) n) (ps : path @β) :
  subtree' ps (ch x) y →
  subtree' (⟨_,a,x⟩ :: ps) (cofix_a.intro a ch) y

-- def subtree' : ∀ {i : ι} {n : ℕ} (ps : path @β) (x : cofix_a γ i (n + ps.length)), roption (Σ i, cofix_a γ i n)
--  | i n [] t := return ⟨_,t⟩
--  | i' n (⟨i, y, j⟩ :: ys) (cofix_a.intro y' ch) :=
-- assert (i' = i ∧ y == y') $ λ h,
-- subtree' ys (ch $ ♯ j)

#check cofix_a.intro

end subtree
open subtree

-- def subtree {j : ι} (x : cofix γ j) (ps : path @β) (y : cofix γ i) : Prop :=
-- ∀ n, subtree' ps (x.approx $ n + ps.length) (y.approx n)

inductive subtree : ∀ {j : ι} (ps : path @β) (x : cofix γ j), cofix γ i → Prop
| nil (x y : cofix γ i) :
  x = y →
  subtree [] x y
| cons {j} (a : α j) (x : β j a)
       (r : cofix γ j) (y : cofix γ i )
       (ch : Π b, cofix γ (γ j a b)) (ps : path @β) :
  r = cofix.mk a ch →
  subtree ps (ch x) y →
  subtree (⟨_,a,x⟩ :: ps) r y

open cofix

inductive select : ∀ {j : ι} (ps : path @β) (x : cofix γ j), α i → Prop
| nil (x : cofix γ i) (a : α i) :
  head x = a →
  select [] x a
| cons {j} (a : α j) (x : β j a)
       (r : cofix γ j) (y : α i )
       (ch : Π b, cofix γ (γ j a b)) (ps : path @β) :
  r = cofix.mk a ch →
  select ps (ch x) y →
  select (⟨_,a,x⟩ :: ps) r y

-- def select {j : ι} (x : cofix γ j) (ps : path @β) : α i → Prop :=
-- select' (x.approx ps.length.succ) ps
open nat

@[simp]
lemma select_nil' {j : ι} {n : ℕ} (x : cofix_a γ j (succ n)) (a : α i) :
  select' x [] a ↔ i = j ∧ a == head' x :=
begin
  split; intro h,
  { cases h, simp * },
  { cases h, subst i, subst h_right,
    constructor, refl }
end

@[simp]
lemma select_nil {j : ι} (x : cofix γ j) (a : α i) :
  select [] x a ↔ i = j ∧ a == head x :=
begin
  split; intro h,
  { cases h, simp * },
  { cases h, subst i, subst h_right,
    constructor, refl }
end
notation x ` ∧. `:35 y:34 := ∃ _ : x, y
#print notation ∧

run_cmd mk_simp_attr `cast

local prefix `♯`:0 := cast (by casesm* _ ∧ _ ; simp [*] with cast <|> cc <|> solve_by_elim)

@[simp]
lemma select_cons' {n} {j k : ι} (x : cofix_a γ k (succ n)) (z : α i) {y : α j} (a : β j y) (ps : path @β) :
  select' x (⟨_,_,a⟩ :: ps) z ↔ j = k ∧. y == head' x ∧. select' (children' x $ ♯ a) ps z :=
sorry

@[simp]
lemma select_cons {j k : ι} (x : cofix γ k) (z : α i) {y : α j} (a : β j y) (ps : path @β) :
  select (⟨_,_,a⟩ :: ps) x z ↔ j = k ∧. y == head x ∧. select ps (children x $ ♯ a) z :=
sorry

@[cast]
lemma head'_approx {j : ι} (n : ℕ) (x : cofix γ j) :
  head' (x.approx (succ n)) = head x :=
by simp [head,head_approx_succ' _ n]

lemma children'_approx {j : ι} (n : ℕ) (x : cofix γ j)
  (i : β j (head' (x.approx (succ n))))
  (j : β j (head x))
  (h : i == j) :
  children' (x.approx (succ n)) i == (children x j).approx n :=
by { cases x, revert i, dsimp [children], simp, intros,
     congr, symmetry, apply cast_eq_of_heq, symmetry, assumption }

lemma select_eq_select {j : ι} (x : cofix γ j) (ps : path @β) (a : α i) :
  select ps x a ↔ select' (x.approx ps.length.succ) ps a :=
begin
  induction ps generalizing x j,
  { simp [head'_approx] },
  { rcases ps_hd with ⟨_,_,_⟩, simp *,
    apply exists_congr, intro,
    subst j,
    apply exists_prop_congr, intro,
    { -- cases x, dsimp [children,add_one],
      apply eq.to_iff, congr' 1,
      { dsimp [head], congr' 1; simp with cast },
      symmetry,
      h_generalize! _ : _ == k,
      -- h_generalize! _ : _ == k',
      rw [list.length,add_one],
      intros, apply children'_approx, cc,
      simp with cast },  }

      -- h_generalize _ : _ == k,
      -- transitivity,
      -- -- h_generalize! _ : _ == k',
      -- apply children'_approx, dsimp [add_one],
      -- admit, admit, } },
  -- split; rintro ⟨ h, b ⟩,
  -- { constructor, subst a, refl },
  -- { constructor, subst a, refl },
  -- { dsimp, cases x, constructor, rw a_1_a_1, refl,
  --   rw a_1_a_1 at *, },
end

-- lemma select_head {j : ι} (x : cofix γ j) (ps : path @β) (y : cofix γ i)
--   (h : subtree ps x y) :
--   select x ps (head y) :=
-- begin
--   induction ps generalizing x,
--   { dsimp [select,head],
--     cases h, constructor, subst h_x },
--   { cases h, dsimp [select],
--     constructor,
--     co_cases x,
--     -- apply cofix.cases,
--  }
-- end

lemma exists_subtree {j : ι} (x : cofix γ j) (ps : path @β) (a : α i)
  (h : select ps x a) :
  ∃ ch, subtree ps x (cofix.mk a ch) :=
begin
  induction ps generalizing i j x a,
  { cases h with x,
    revert a,
    co_cases x, intros,
    simp at h_a_1, subst h_a_1,
    existsi c, constructor, refl, },
  { cases h, revert ps_ih h h_a h_x,
    co_cases x, intros,
    cases ps_ih _ _ h_a_2 with ch' h_ch',
    existsi ch', constructor; try { assumption } }
end

#check cofix.cases_on _ _


-- variables {C : Π {j : ι}, path @β → cofix γ j → cofix γ i → Prop}
-- variables (h₀ : ∀ x y : cofix γ i, x = y → C [] x y)
-- variables (h₁ : ∀ {j : ι} (a : α j) (x : β j a) (y : cofix γ i)
--                   (ch : Π (b : β j a), cofix γ (γ j a b)) (ps : path β),
--                   subtree (ch x) ps y →
--                   C ps (ch x) y →
--                   C (⟨j, ⟨a, x⟩⟩ :: ps) (cofix.mk a ch) y)

-- def subtree.rec  {j : ι} (ps : path @β) {x : cofix γ j} (a : cofix γ i) : subtree x ps a → C ps x a

#check @subtree'.rec

end coinduction
