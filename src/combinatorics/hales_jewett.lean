/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import data.fintype.basic
import algebra.big_operators.basic

/-!
# The Hales-Jewett theorem
-/

noncomputable theory
open_locale classical
open_locale big_operators

def option_fin_equiv_fin_succ (n : ℕ) : option (fin n) ≃ fin (n+1) :=
{ to_fun := λ o, o.elim 0 fin.succ,
  inv_fun := λ i, fin.cases none some i,
  left_inv := by { rintro (_ | _), refl, apply fin.cases_succ, },
  right_inv := by { apply fin.cases; simp, }, }

def hygienic_fintype_induction {P : Type → Sort*} (hygienic : ∀ {α β}, α ≃ β → P α → P β)
  (h_unit : P unit) (h_option : ∀ {α} [fintype α] [nonempty α], P α → P (option α))
  (α) [fintype α] [nonempty α] : P α :=
begin
  suffices : ∀ n, P (fin (n+1)),
  { refine hygienic (fintype.equiv_fin α).symm _,
    have card_pos : 0 < fintype.card α := finset.card_pos.mpr finset.univ_nonempty,
    cases fintype.card α, exfalso, exact lt_irrefl _ card_pos, apply this, },
  intro n, induction n with n ih,
  exact hygienic equiv_of_unique_of_unique h_unit,
  exact hygienic (option_fin_equiv_fin_succ _) (h_option ih),
end

structure combinatorial_line (m n : Type) :=
(idx_fun : n → option m)
(proper : ∃ i, idx_fun i = none)

instance (m n) : has_coe_to_fun (combinatorial_line m n) :=
⟨λ _, m → n → m, λ l x i, (l.idx_fun i).get_or_else x⟩

def diagonal (m n) [nonempty n] : combinatorial_line m n :=
{ idx_fun    := λ _, none,
  proper := ⟨classical.arbitrary n, rfl⟩ }

def is_mono {m n k : Type} (C : (n → m) → k) (l : combinatorial_line m n) : Prop :=
∃ c, ∀ x, C (l x) = c

structure almost_mono {m n k : Type} (C : (n → option m) → k) :=
(line : combinatorial_line (option m) n)
(color : k)
(has_color : ∀ x : m, C (line (some x)) = color)

structure color_focused_lines {m n k} (C : (n → option m) → k) :=
(lines : multiset (almost_mono C))
(focus : n → option m)
(is_focused : ∀ p : almost_mono C, p ∈ lines → p.line none = focus)
(nodup : (lines.map almost_mono.color).nodup)

def combinatorial_line.map {m m' n} (f : m → m') (l : combinatorial_line m n) :
  combinatorial_line m' n :=
{ idx_fun    := λ i, (l.idx_fun i).map f,
  proper := ⟨l.proper.some, by rw [l.proper.some_spec, option.map_none'] ⟩ }

lemma combinatorial_line.apply {m n} (l : combinatorial_line m n) (x : m) :
  l x = λ i, (l.idx_fun i).get_or_else x := rfl

@[simp] lemma combinatorial_line.apply_none {m n} (l : combinatorial_line m n) (x : m) (i : n)
  (h : l.idx_fun i = none) : l x i = x :=
by simp only [option.none_get_or_else, h, combinatorial_line.apply]

@[simp] lemma combinatorial_line.apply_some {m n} (l : combinatorial_line m n) (x y : m) (i : n)
  (h : l.idx_fun i = some y) : l x i = y :=
by simp only [option.some_get_or_else, h, combinatorial_line.apply]

@[simp] lemma combinatorial_line.map_apply {m m' n} (f : m → m') (l : combinatorial_line m n)
  (x : m) : l.map f (f x) = f ∘ l x :=
by simp only [combinatorial_line.apply, combinatorial_line.map, option.map_get_or_else]

def combinatorial_line.vertical {m n n'} (v : n → m) (l : combinatorial_line m n') :
  combinatorial_line m (n ⊕ n') :=
{ idx_fun := sum.elim (some ∘ v) l.idx_fun,
  proper := ⟨sum.inr l.proper.some, l.proper.some_spec⟩ }

def combinatorial_line.horizontal {m n n'} (l : combinatorial_line m n) (v : n' → m):
  combinatorial_line m (n ⊕ n') :=
{ idx_fun := sum.elim l.idx_fun (some ∘ v),
  proper := ⟨sum.inl l.proper.some, l.proper.some_spec⟩ }

def combinatorial_line.product {m n n'}
  (l : combinatorial_line m n) (l' : combinatorial_line m n') : combinatorial_line m (n ⊕ n') :=
{ idx_fun := sum.elim l.idx_fun l'.idx_fun,
  proper := ⟨sum.inl l.proper.some, l.proper.some_spec⟩ }

@[simp] lemma vertical_apply {m n n'} (v : n → m) (l : combinatorial_line m n') (x : m) :
  l.vertical v x = sum.elim v (l x) :=
by { funext i, cases i; refl }

@[simp] lemma horizontal_apply {m n n'} (l : combinatorial_line m n) (v : n' → m) (x : m) :
  l.horizontal v x = sum.elim (l x) v :=
by { funext i, cases i; refl }

@[simp] lemma product_apply {m n n'} (l : combinatorial_line m n) (l' : combinatorial_line m n')
  (x : m) : l.product l' x = sum.elim (l x) (l' x) :=
by { funext i, cases i; refl }

theorem hales_jewett : ∀ m [fintype m] [nonempty m] k [fintype k],
  ∃ n [fintype n], ∀ C : (n → m) → k, ∃ l, is_mono C l :=
hygienic_fintype_induction
(λ A B e, forall_imp $ λ k, forall_imp $ λ _, Exists.imp $ λ n, Exists.imp $ λ _ hA C,
  let ⟨l, c, lc⟩ := hA (λ v, C (e ∘ v)) in
  ⟨l.map e, c, e.forall_congr_left.mp $ λ a, by rw [←lc a, combinatorial_line.map_apply]⟩)
(λ k _, ⟨unit, infer_instance, λ C, ⟨diagonal _ _, C (λ _, unit.star), λ ⟨⟩, rfl⟩⟩)
begin
  introsI m _ _ ihm k _,
  suffices claim : ∀ r : ℕ, ∃ (n : Type) [fintype n], ∀ C : (n → (option m)) → k,
    (∃ s : color_focused_lines C, s.lines.card = r) ∨ (∃ l, is_mono C l),
  { obtain ⟨n, nn, hn⟩ := claim (fintype.card k + 1),
    refine ⟨n, nn, λ C, (hn C).resolve_left _⟩,
    rintro ⟨s, sr⟩,
    apply nat.not_succ_le_self (fintype.card k),
    rw [←nat.add_one, ←sr, ←multiset.card_map, ←finset.card_mk],
    exact finset.card_le_univ ⟨_, s.nodup⟩ },
  intro r,
  induction r with r ihr,
  { exact ⟨empty, infer_instance, λ C, or.inl
      ⟨⟨0, empty.elim, λ _, false.elim, multiset.nodup_zero⟩, multiset.card_zero⟩⟩, },
  obtain ⟨n, _inst, hn⟩ := ihr,
  resetI,
  specialize ihm ((n → option m) → k),
  obtain ⟨n', _inst, hn'⟩ := ihm,
  resetI,
  refine ⟨n ⊕ n', infer_instance, _⟩,
  intro C,
  specialize hn' (λ v' v, C (sum.elim v (some ∘ v'))),
  obtain ⟨l', C', hl'⟩ := hn',
  have claim : (∃ l, is_mono C' l) → (∃ l, is_mono C l),
  { rintro ⟨l, c, hl⟩,
    refine ⟨l.horizontal (some ∘ l' (classical.arbitrary m)), c, λ x, _⟩,
    rw [horizontal_apply, ←hl, ←hl'], },
  specialize hn C',
  rcases hn with ⟨s, sr⟩ | _,
  work_on_goal 1 { exact or.inr (claim hn) },
  by_cases h : ∃ p ∈ s.lines, (p : almost_mono _).color = C' s.focus,
  { obtain ⟨p, p_mem, hp⟩ := h,
    refine or.inr (claim ⟨p.line, p.color, _⟩),
    rintro (_ | _),
    { rw [hp, s.is_focused p p_mem], },
    { apply p.has_color, }, },
  refine or.inl ⟨⟨(s.lines.map _).cons ⟨(l'.map some).vertical s.focus, C' s.focus, λ x, _⟩,
    sum.elim s.focus (l'.map some none), _, _⟩, _⟩,
  { rw [vertical_apply, ←congr_fun (hl' x), combinatorial_line.map_apply], },
  { refine λ p, ⟨p.line.product (l'.map some), p.color, λ x, _⟩,
    rw [product_apply, combinatorial_line.map_apply, ←p.has_color, ←congr_fun (hl' x)], },
  { simp_rw [multiset.mem_cons, multiset.mem_map],
    rintros _ (rfl | ⟨q, hq, rfl⟩),
    { rw vertical_apply, },
    { rw [product_apply, s.is_focused q hq], }, },
  { rw [multiset.map_cons, multiset.map_map, multiset.nodup_cons, multiset.mem_map],
    exact ⟨λ ⟨q, hq, he⟩, h ⟨q, hq, he⟩, s.nodup⟩, },
  { rw [multiset.card_cons, multiset.card_map, sr], },
end

theorem gallai (M) (k S : Type) [add_comm_monoid M] [fintype k] [fintype S] (f : S → M)
  (C : M → k) : ∃ (a : pnat) (b : M) (c : k), ∀ s, C ((a : ℕ) • (f s) + b) = c :=
begin
  by_cases hS : nonempty S,
  work_on_goal 1 { exact ⟨1, 0, (C 0), λ s, (hS ⟨s⟩).elim⟩, },
  resetI,
  obtain ⟨n, _inst, hn⟩ := hales_jewett S k,
  resetI,
  specialize hn (λ v, C $ ∑ i, f (v i)),
  obtain ⟨l, c, hl⟩ := hn,
  set s : finset n := { i ∈ finset.univ | l.idx_fun i = none } with hs,
  refine ⟨⟨s.card, finset.card_pos.mpr ⟨l.proper.some, _⟩⟩,
    ∑ i in sᶜ, f (l (classical.arbitrary S) i), c, _⟩,
  { rw [hs, finset.sep_def, finset.mem_filter], exact ⟨finset.mem_univ _, l.proper.some_spec⟩, },
  intro x,
  rw ←hl x,
  clear hl, dsimp, congr,
  rw ←finset.sum_add_sum_compl s,
  congr' 1,
  { rw ←finset.sum_const,
    apply finset.sum_congr rfl,
    intros i hi,
    rw [hs, finset.sep_def, finset.mem_filter] at hi,
    rw l.apply_none _ _ hi.right, },
  { apply finset.sum_congr rfl,
    intros i hi,
    rw [hs, finset.sep_def, finset.compl_filter, finset.mem_filter] at hi,
    obtain ⟨y, hy⟩ := option.ne_none_iff_exists.mp hi.right,
    simp only [l.apply_some _ _ _ hy.symm], },
end
#lint
