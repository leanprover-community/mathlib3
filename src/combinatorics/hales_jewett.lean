import data.fintype.basic
import data.pnat.basic
import algebra.big_operators.basic

noncomputable theory
open_locale classical
open_locale big_operators

def option_fin (n : ℕ) : fin (n+1) ≃ option (fin n) :=
begin
  symmetry,
  convert fintype.equiv_fin _,
  swap,
  apply_instance,
  simp,
end

def hygienic_fintype_induction {P : Type → Prop}
  (hygienic : ∀ A B : Type, A ≃ B → P A → P B)
  (h_unit : P unit)
  (h_option : ∀ (A) [fintype A] [nonempty A], P A → P (option A))
  (A : Type) [fintype A] [nonempty A] : P A :=
begin
  suffices : ∀ n : pnat, P (fin n),
  { let n : pnat := ⟨fintype.card A, fintype.card_pos_iff.mpr infer_instance⟩,
    exact hygienic (fin n) _ (fintype.equiv_fin A).symm (this n), },
  intro n, apply n.rec_on,
  { refine hygienic _ _ _ h_unit, dsimp, exact equiv_of_unique_of_unique },
  { introsI n' ih,
    refine hygienic _ _ _ (h_option _ _),
    { exact fin n' },
    { dsimp, symmetry, apply option_fin, },
    { apply_instance, },
    { use 0, exact pnat.pos n', },
    { apply ih, }, },
end

variables (m m' k n n' : Type)

def line : Type :=
{ f : m → (n → m) // ∀ i, (∀ x, f x i = x) ∨ (∃ y, ∀ x, f x i = y) }

def diagonal : line m n :=
⟨λ x i, x, λ i, or.inl (λ _, rfl)⟩

variables {m m' k n n'}

def line.map (f : m → m') (l : line m n) : line m' n :=
⟨λ y i, if h : ∀ x, l.val x i = x
        then y
        else f $ ((l.property i).resolve_left h).some,
  by { intro i, split_ifs, { tauto }, { right, exact ⟨_, λ _, rfl⟩, } }⟩

def is_proper (l : line m n) : Prop :=
∃ i, ∀ x, l.val x i = x

lemma map_proper (f : m → m') (l : line m n) (h : is_proper l) : is_proper (l.map f) :=
by { cases h with i hi, use i, intro, delta line.map, dsimp, rw dif_pos, exact hi }

lemma map_spec (f : m → m') (l : line m n) (x : m) : (l.map f).val (f x) = f ∘ (l.val x) :=
begin
  delta line.map, dsimp, funext i, split_ifs,
  { dsimp, rw h, },
  { congr, symmetry, exact ((l.property i).resolve_left h).some_spec _, },
end

lemma diagonal_proper [nonempty n] : is_proper (diagonal m n) :=
⟨classical.arbitrary n, λ _, rfl⟩

def is_mono (c : (n → m) → k) (l : line m n) : Prop :=
∃ a, ∀ x, c (l.val x) = a

def good_line (c : (n → option m) → k) : Type :=
{ p : line (option m) n × k // is_proper p.fst ∧ ∀ x : m, c (p.fst.val (some x)) = p.snd }

def colour_focused (c : (n → option m) → k) (s : multiset (good_line c)) : Prop :=
  (∃ focus, ∀ p ∈ s, (prod.fst (subtype.val p) : line _ _).val none = focus)
∧ (s.map (prod.snd ∘ subtype.val)).nodup

def trivial_line (y : n → m) : line m n :=
⟨λ x, y, λ i, or.inr ⟨y i, λ _, rfl⟩⟩

def product_line (l : line m n) (l' : line m n') : line m (n ⊕ n') :=
⟨λ x, sum.elim (l.val x) (l'.val x),
  by { intro i, cases i, { dsimp, apply l.property, }, { dsimp, apply l'.property, } }⟩

lemma product_proper (l : line m n) (l' : line m n') (h : is_proper l ∨ is_proper l') :
  is_proper (product_line l l') :=
begin
  cases h,
  { obtain ⟨i, hi⟩ := h,
    use sum.inl i,
    dsimp, exact hi, },
  { obtain ⟨i, hi⟩ := h,
    use sum.inr i,
    dsimp, exact hi, },
end

variables (m k)

theorem hales_jewett [fintype m] [nonempty m] : ∀ [fintype k], ∃ n [fintype n], ∀ c : (n → m) → k,
  ∃ l : line m n, is_proper l ∧ is_mono c l :=
begin
  revert k,
  refine hygienic_fintype_induction _ _ _ m,
  { introsI A B e hA k _, -- can equiv_rw do this?
    specialize @hA k,
    rcases hA with ⟨n, hn, hA⟩,
    use n,
    use hn,
    intro c,
    specialize hA (λ v, c (e ∘ v)),
    rcases hA with ⟨l, lp, lm⟩,
    refine ⟨⟨λ b, e ∘ l.val (e.symm b), _⟩, _, _⟩,
    { intro i,
      obtain foo := l.property i,
      cases foo,
      { left,
        intro b,
        specialize foo (e.symm b),
        rw equiv.eq_symm_apply at foo,
        exact foo, },
      { right,
        cases foo with a foo,
        use e a,
        intro b,
        specialize foo (e.symm b),
        apply congr_arg e foo, }, },
    { cases lp with i hi,
      use i,
      intro b,
      specialize hi (e.symm b),
      rw equiv.eq_symm_apply at hi,
      exact hi, },
    cases lm with C hC,
    use C,
    intro b,
    specialize hC (e.symm b),
    exact hC, },
  { intros k _,
    use unit,
    use infer_instance,
    intro c,
    refine ⟨diagonal _ _, diagonal_proper, c (λ _, unit.star), _⟩,
    rintro ⟨⟩, refl, },
  { clear _inst_2 _inst_1 m,
    introsI m _ _ ihm k _,
    suffices claim : ∀ r : ℕ, ∃ (n : Type) [fintype n], ∀ c : (n → (option m)) → k,
      (∃ s, colour_focused c s ∧ s.card = r) ∨ (∃ l, is_proper l ∧ is_mono c l),
    { obtain ⟨n, nn, hn⟩ := claim (fintype.card k + 1),
      use n,
      use nn,
      intro c,
      apply (hn c).resolve_left,
      rintro ⟨s, cf, cr⟩,
      apply nat.not_succ_le_self (fintype.card k),
      let cs : finset k := ⟨_, cf.2⟩,
      convert finset.card_le_univ cs,
      rw [finset.card_mk, multiset.card_map, cr], },
    intro r,
    induction r with r ihr,
    { use empty,
      use infer_instance,
      intro c,
      use ∅,
      refine ⟨⟨_, _⟩, _⟩,
      { use classical.arbitrary _, tauto, },
      { simp only [multiset.nodup_zero, multiset.map_zero, multiset.empty_eq_zero], },
      { simp only [multiset.card_zero, multiset.empty_eq_zero], }, },
    obtain ⟨n, nn, hn⟩ := ihr,
    resetI,
    specialize @ihm ((n → option m) → k),
    specialize @ihm infer_instance,
    obtain ⟨n', nn', hn'⟩ := ihm,
    resetI,
    use n ⊕ n',
    use infer_instance,
    intro c,
    specialize hn' (λ v' v, c (sum.elim v (some ∘ v'))),
    obtain ⟨l', l'p, C', l'C⟩ := hn',
    specialize hn C',
    have claim : (∃ l, is_proper l ∧ is_mono C' l) → ∃ l, is_proper l ∧ is_mono c l,
    { rintro ⟨l, lp, C, lC⟩,
      refine ⟨product_line l (trivial_line (some ∘ l'.val (classical.arbitrary m))), _, _⟩,
      { apply product_proper, left, assumption, },
      use C,
      intro x,
      rw ←lC x,
      specialize l'C (classical.arbitrary m),
      rw ←l'C,
      refl, },
    rcases hn with ⟨s, ⟨⟨v, hv⟩, sndp⟩, cr⟩ | foo,
    { by_cases h : ∃ p ∈ s, C' v = prod.snd (subtype.val p),
      { right,
        apply claim,
        obtain ⟨p, p_mem, hp⟩ := h,
        use p.val.fst,
        refine ⟨p.property.left, _⟩,
        use p.val.snd,
        rintro (x | _),
        { rw ←hp, congr, apply hv, exact p_mem, },
        { apply p.property.right, }, },
      { left,
        refine ⟨(s.map _).cons _, ⟨_, _⟩, _⟩,
        { refine ⟨⟨product_line (trivial_line v) (l'.map some), C' v⟩, _, _⟩,
          { apply product_proper, right, apply map_proper, exact l'p, },
          intro x, dsimp [product_line],
          rw ←l'C x,
          dsimp, congr, exact map_spec some l' x, },
        { intro p,
          refine ⟨⟨product_line p.val.fst (l'.map some), p.val.snd⟩, _, _⟩,
          { apply product_proper, left, exact p.property.left, },
          intro x,
          dsimp [product_line],
          erw ←p.property.right x,
          specialize l'C x,
          rw function.funext_iff at l'C,
          rw ←l'C,
          dsimp,
          congr,
          exact map_spec some l' x, },
        { use sum.elim v ((l'.map some).val none),
          intros p hp,
          rw [multiset.mem_cons, multiset.mem_map] at hp,
          rcases hp with rfl | ⟨q, hq, rfl⟩,
          { refl, },
          { delta product_line, dsimp, congr,
            apply hv, exact hq, } },
        { rw [multiset.map_cons, multiset.map_map, multiset.nodup_cons],
          split,
          { intro mem, rw multiset.mem_map at mem, rcases mem with ⟨q, hq, he⟩,
            apply h, use q, refine ⟨hq, _⟩,
            dsimp at he, exact he.symm, },
          { rw function.comp, simp_rw function.comp_app, exact sndp, } },
        { simp only [multiset.card_map, multiset.card_cons, cr], } }, },
    { right, apply claim, exact foo, }, },
end

theorem gallai (M) (k S : Type) [add_comm_monoid M] [fintype k] [fintype S] (f : S → M)
  (c : M → k) : ∃ (a : pnat) (b : M) (C : k), ∀ s, c ((a : ℕ) • (f s) + b) = C :=
begin
  by_cases h : nonempty S,
  { resetI,
    obtain ⟨n, inst, hn⟩ := hales_jewett S k,
    resetI,
    specialize hn (λ v, c $ ∑ i : n, f (v i)),
    obtain ⟨l, lp, C, lC⟩ := hn,
    set s : finset n := { i ∈ finset.univ | ∀ x, l.val x i = x } with hs,
    use s.card,
    { refine finset.card_pos.mpr _, obtain ⟨i, hi⟩ := lp, use i,
      rw [hs, finset.sep_def, finset.mem_filter],
      exact ⟨finset.mem_univ i, hi⟩, },
    use ∑ i in sᶜ, f (l.val (classical.arbitrary S) i),
    use C,
    intro x,
    specialize lC x,
    rw ←lC,
    dsimp,
    congr,
    rw ←finset.sum_add_sum_compl s,
    congr' 1,
    { rw ←finset.sum_const,
      apply finset.sum_congr rfl,
      intros i hi,
      rw [hs, finset.sep_def, finset.mem_filter] at hi,
      congr,
      exact (hi.right x).symm, },
    { apply finset.sum_congr rfl,
      intros i hi, congr' 1,
      obtain ⟨y, hy⟩ := (l.property i).resolve_left _,
      { change l.val _ i = l.val _ i, rw [hy, hy], },
      rw [hs, finset.sep_def, finset.compl_filter, finset.mem_filter] at hi,
      exact hi.right, } },
  refine ⟨1, 0, (c 0), _⟩,
  intro s, exfalso, apply h, use s,
end
