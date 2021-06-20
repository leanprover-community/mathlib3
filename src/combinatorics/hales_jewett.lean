/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import data.fintype.basic
import data.pnat.basic
import algebra.big_operators.basic

noncomputable theory
open_locale classical
open_locale big_operators

@[simp] lemma option.map_get_or_else {α β} (f : α → β) (a : α) (x : option α) :
  (x.map f).get_or_else (f a) = f (x.get_or_else a) :=
by { cases x; refl }

def option_fin_equiv_fin_succ (n : ℕ) : option (fin n) ≃ fin (n+1) :=
{ to_fun := λ o, o.elim 0 fin.succ,
  inv_fun := λ i, fin.cases none some i,
  left_inv := by { rintro (_ | _), refl, dsimp, rw fin.cases_succ, },
  right_inv := by { apply fin.cases; simp, }, }

def hygienic_fintype_induction {P : Type* → Prop}
  (hygienic : ∀ A B, A ≃ B → P A → P B)
  (h_unit : P unit)
  (h_option : ∀ (A) [fintype A] [nonempty A], P A → P (option A))
  (A) [fintype A] [nonempty A] : P A :=
begin
  suffices : ∀ n : pnat, P (fin n),
  { let n : pnat := ⟨fintype.card A, fintype.card_pos_iff.mpr infer_instance⟩,
    exact hygienic (fin n) _ (fintype.equiv_fin A).symm (this n), },
  intro n, apply n.rec_on,
  { refine hygienic _ _ _ h_unit, dsimp, exact equiv_of_unique_of_unique },
  { introsI n' ih,
    refine hygienic _ _ _ (h_option _ _),
    { exact fin n' },
    { dsimp, apply option_fin_equiv_fin_succ, },
    { apply_instance, },
    { use 0, exact pnat.pos n', },
    { apply ih, }, },
end

variables (m m' k n n' : Type)

structure combinatorial_line : Type :=
(foo : n → option m)
(proper : ∃ i, foo i = none)

instance : has_coe_to_fun (combinatorial_line m n) :=
⟨λ _, (m → n → m), λ l x i, (l.foo i).get_or_else x⟩

def diagonal [nonempty n] : combinatorial_line m n :=
{ foo := λ _, none,
  proper := ⟨classical.arbitrary n, rfl⟩ }

variables {m m' k n n'}

def is_mono (c : (n → m) → k) (l : combinatorial_line m n) : Prop :=
∃ a, ∀ x, c (l x) = a

structure almost_mono (c : (n → option m) → k) : Type :=
(line : combinatorial_line (option m) n)
(colour : k)
(has_colour : ∀ x : m, c (line (some x)) = colour)

structure colour_focused_lines (c : (n → option m) → k) : Type :=
(lines : multiset (almost_mono c))
(focus : n → option m)
(is_focused : ∀ p : almost_mono c, p ∈ lines → p.line none = focus)
(nodup : (lines.map almost_mono.colour).nodup)

@[simps]
def combinatorial_line.map (f : m → m') (l : combinatorial_line m n) : combinatorial_line m' n :=
{ foo    := λ i, (l.foo i).map f,
  proper := ⟨l.proper.some, by rw [l.proper.some_spec, option.map_none'] ⟩ }

@[simp] lemma combinatorial_line.apply (l : combinatorial_line m n) (x : m) (i : n) :
  l x i = (l.foo i).get_or_else x := rfl

@[simp]
lemma combinatorial_line.map_apply (f : m → m') (l : combinatorial_line m n) (x : m) (i : n) :
  l.map f (f x) i = f (l x i) :=
by rw [combinatorial_line.apply, combinatorial_line.map_foo, option.map_get_or_else,
  combinatorial_line.apply]

theorem hales_jewett : ∀ m [fintype m] [nonempty m] k [fintype k],
  ∃ n [fintype n], ∀ c : (n → m) → k, ∃ l, is_mono c l :=
begin
  refine hygienic_fintype_induction _ _ _,
  { introsI A B e hA k _,
    obtain ⟨n, hn, bar⟩ := @hA k infer_instance,
    refine ⟨n, hn, _⟩,
    intro c,
    obtain ⟨l, C, lC⟩ := bar (λ v, c (e ∘ v)),
    refine ⟨l.map e, C, e.forall_congr_left.mp _⟩,
    intro a,
    rw ←lC a,
    congr,
    funext,
    apply combinatorial_line.map_apply, },
  { intros, exact ⟨unit, infer_instance, λ c, ⟨diagonal _ _, c (λ _, unit.star), λ ⟨⟩, rfl⟩⟩ },
  { introsI m _ _ ihm k _,
    suffices claim : ∀ r : ℕ, ∃ (n : Type) [fintype n], ∀ c : (n → (option m)) → k,
      (∃ s : colour_focused_lines c, s.lines.card = r) ∨ (∃ l, is_mono c l),
    { obtain ⟨n, nn, hn⟩ := claim (fintype.card k + 1),
      refine ⟨n, nn, _⟩,
      intro c,
      apply (hn c).resolve_left,
      rintro ⟨s, sr⟩,
      apply nat.not_succ_le_self (fintype.card k),
      let cs : finset k := ⟨_, s.nodup⟩,
      convert finset.card_le_univ cs,
      rw [finset.card_mk, multiset.card_map, sr], },
    intro r,
    induction r with r ihr,
    { refine ⟨empty, infer_instance, _⟩,
      intro c,
      left,
      refine ⟨⟨0, empty.elim, _, _⟩, multiset.card_zero⟩,
      { tauto },
      { simp only [multiset.nodup_zero, multiset.map_zero] }, },
    obtain ⟨n, nn, hn⟩ := ihr,
    resetI,
    obtain ⟨n', nn', hn'⟩ := @ihm ((n → option m) → k) infer_instance,
    resetI,
    refine ⟨n ⊕ n', infer_instance, _⟩,
    intro c,
    obtain ⟨l', C', l'C'⟩ := hn' (λ v' v, c (sum.elim v (λ i, some (v' i)))),
    have claim : (∃ l, is_mono C' l) → (∃ l, is_mono c l),
    { rintro ⟨l, C, lC⟩,
      refine ⟨⟨sum.elim l.foo (λ i, some (some $ l' (classical.arbitrary m) i)),
        sum.inl l.proper.some, l.proper.some_spec⟩, C, _⟩,
      intro x,
      rw [←lC x, ←l'C' (classical.arbitrary m)],
      congr, funext i, cases i; refl, },
    rcases hn C' with ⟨s, cr⟩ | foo,
    { by_cases h : ∃ p ∈ s.lines, C' s.focus = almost_mono.colour p,
      { right,
        apply claim,
        obtain ⟨p, p_mem, hp⟩ := h,
        refine ⟨p.line, p.colour, _⟩,
        rintro (_ | _),
        { rw [←hp, s.is_focused p p_mem], },
        { apply p.has_colour, }, },
      { left,
        refine ⟨⟨(s.lines.map _).cons _, sum.elim s.focus (l'.map some none), _, _⟩, _⟩,
        { refine ⟨⟨sum.elim (λ i, some (s.focus i)) (λ i, (l'.foo i).map some),
            sum.inr l'.proper.some, _⟩, C' s.focus, _⟩,
          { dsimp, rw [l'.proper.some_spec, option.map_none'], },
          intro x,
          rw ←congr_fun (l'C' x),
          dsimp, congr, funext, cases i, refl, apply option.map_get_or_else, },
        { intro p,
          refine ⟨⟨sum.elim p.line.foo (λ i, (l'.foo i).map some),
            sum.inl p.line.proper.some, p.line.proper.some_spec⟩, p.colour, _⟩,
          intro x,
          rw [←p.has_colour x, ←congr_fun (l'C' x)],
          dsimp, congr, funext, cases i, refl, apply option.map_get_or_else, },
        { intros p hp,
          rw [multiset.mem_cons, multiset.mem_map] at hp,
          rcases hp with rfl | ⟨q, hq, rfl⟩,
          { funext, cases i; refl },
          { funext, cases i, { rw ←s.is_focused q hq, refl, }, { refl, }, }, },
        { rw [multiset.map_cons, multiset.map_map, multiset.nodup_cons],
          split,
          { intro mem,
            obtain ⟨q, hq, he⟩ := multiset.mem_map.mp mem,
            exact h ⟨q, hq, he.symm⟩, },
          { exact s.nodup, }, },
        { rw [multiset.card_cons, multiset.card_map, cr], }, }, },
    { right, apply claim, exact foo, }, },
end

theorem gallai (M) (k S : Type) [add_comm_monoid M] [fintype k] [fintype S] (f : S → M)
  (c : M → k) : ∃ (a : pnat) (b : M) (C : k), ∀ s, c ((a : ℕ) • (f s) + b) = C :=
begin
  by_cases h : nonempty S,
  { resetI,
    obtain ⟨n, inst, hn⟩ := hales_jewett S k,
    resetI,
    obtain ⟨l, C, lC⟩ := hn (λ v, c $ ∑ i, f (v i)),
    set s : finset n := { i ∈ finset.univ | l.foo i = none } with hs,
    refine ⟨⟨s.card, finset.card_pos.mpr ⟨l.proper.some, _⟩⟩,
      ∑ i in sᶜ, f (l (classical.arbitrary S) i), C, _⟩,
    { rw [hs, finset.sep_def, finset.mem_filter], exact ⟨finset.mem_univ _, l.proper.some_spec⟩, },
    intro x,
    rw ←lC x,
    dsimp, congr,
    rw ←finset.sum_add_sum_compl s,
    congr' 1,
    { rw ←finset.sum_const,
      apply finset.sum_congr rfl,
      intros i hi,
      rw [hs, finset.sep_def, finset.mem_filter] at hi,
      rw hi.right, refl, },
    { apply finset.sum_congr rfl,
      intros i hi, congr' 1,
      rw [hs, finset.sep_def, finset.compl_filter, finset.mem_filter] at hi,
      obtain ⟨y, hy⟩ := option.ne_none_iff_exists.mp hi.right,
      rw ←hy, refl, }, },
  { refine ⟨1, 0, (c 0), _⟩, intro s, exfalso, apply h, use s, },
end
