import data.set.intervals
import data.finset
import data.matrix.notation
import logic.equiv.basic
import data.vector.basic
import data.real.basic
import measure_theory.measure.lebesgue

variables {n : ℕ}
open list
open_locale pointwise big_operators

abbreviation brick (n : ℕ) := vector ℕ n

def brick.is_harmonic (b : brick n) : Prop := ∃ l, l ~ b.1 ∧ l.pairwise (∣)

lemma is_harmonic_iff {b : brick n} (hb : ∀ i ∈ b.1, i ≠ 0) :
  b.is_harmonic ↔ (b.1.merge_sort (≤)).pairwise (∣) :=
begin
  rw [brick.is_harmonic],
  split,
  { rintro ⟨l, hl₁, hl₂⟩,
    convert hl₂,
    refine list.eq_of_perm_of_sorted _ (list.sorted_merge_sort _ _) _,
    { exact (list.perm_merge_sort _ _).trans hl₁.symm },
    { apply hl₂.imp_of_mem _,
      intros x₁ x₂ hx₁ hx₂ h,
      exact nat.le_of_dvd (hb _ (hl₁.mem_iff.1 hx₂)).bot_lt h } },
  intro h,
  exact ⟨_, list.perm_merge_sort _ _, h⟩,
end

def brick.space (b : brick n) : finset (fin n → ℕ) :=
fintype.pi_finset (λ i, finset.range (b.nth i))

lemma space_nil : brick.space vector.nil = finset.univ :=
by { ext x, simp [brick.space] }

lemma mem_space {b : brick n} {x : fin n → ℕ} : x ∈ b.space ↔ ∀ i, x i ∈ finset.range (b.nth i) :=
by simp [brick.space]

lemma mem_space' {b : brick n} {x : fin n → ℕ} : x ∈ b.space ↔ ∀ i, x i < b.nth i :=
by simp [brick.space]

def brick.trivially_fills (b : brick n) (B : finset (fin n → ℕ)) : Prop :=
∃ p : finset (fin n → ℕ),
  set.pairwise_disjoint (p : set (fin n → ℕ)) (λ i, i +ᵥ b.space) ∧
    (p.bUnion $ λ i, i +ᵥ b.space) = B


def restrict_zero (s : finset (fin n.succ → ℕ)) : finset ℕ :=
(s.filter (λ i, matrix.vec_tail i = 0)).image matrix.vec_head

lemma mem_restrict_zero_iff {k : ℕ} {s : finset (fin n.succ → ℕ)} :
  k ∈ restrict_zero s ↔ matrix.vec_cons k 0 ∈ s :=
begin
  simp only [restrict_zero, finset.mem_image, finset.mem_filter, exists_prop, and_assoc],
  split,
  { rintro ⟨m, hm₁, hm₂, hm⟩,
    simpa only [←hm₂, ←hm, matrix.cons_head_tail] },
  intro hs,
  exact ⟨_, hs, by simp⟩,
end

lemma restrict_zero_bUnion {α : Type*} {s : finset α} {f : α → finset (fin n.succ → ℕ)} :
  s.bUnion (λ x, restrict_zero (f x)) = restrict_zero (s.bUnion f) :=
begin
  ext x,
  simp only [mem_restrict_zero_iff, finset.mem_bUnion],
end

lemma restrict_zero_space {b : brick n.succ} (hb : ∀ i : fin n, b.nth i.succ ≠ 0) :
  restrict_zero b.space = finset.range (b.nth 0) :=
begin
  ext x,
  simp only [mem_restrict_zero_iff, set.mem_set_of_eq, mem_space],
  rw fin.forall_fin_succ,
  simp [hb, pos_iff_ne_zero],
end

lemma vec_eq_iff {u v : fin n.succ → ℕ} :
  u = v ↔ matrix.vec_head u = matrix.vec_head v ∧ matrix.vec_tail u = matrix.vec_tail v :=
by simpa only [function.funext_iff, fin.forall_fin_succ]

lemma restrict_zero_vadd (u : fin n.succ → ℕ) (s : finset (fin n.succ → ℕ)) :
  restrict_zero (u +ᵥ s) =
    if matrix.vec_tail u = 0 then matrix.vec_head u +ᵥ restrict_zero s else ∅ :=
begin
  ext x,
  simp only [mem_restrict_zero_iff, finset.mem_vadd_finset, vadd_eq_add, vec_eq_iff,
    matrix.head_add, matrix.head_cons, matrix.tail_add, matrix.tail_cons, add_eq_zero_iff],
  split_ifs,
  { simp only [finset.mem_vadd_finset, mem_restrict_zero_iff, vadd_eq_add],
    split,
    { rintro ⟨v, hv₁, rfl, hv₂, hv₃⟩,
      exact ⟨matrix.vec_head v, by rwa [←hv₃, matrix.cons_head_tail], rfl⟩ },
    { rintro ⟨y, hy, rfl⟩,
      exact ⟨_, hy, by simp [h]⟩ } },
  simp [h]
end


def restrict_succ (s : finset (fin n.succ → ℕ)) : finset (fin n → ℕ) :=
(s.filter (λ i, matrix.vec_head i = 0)).image matrix.vec_tail

lemma mem_restrict_succ_iff {k : fin n → ℕ} {s : finset (fin n.succ → ℕ)} :
  k ∈ restrict_succ s ↔ matrix.vec_cons 0 k ∈ s :=
begin
  simp only [restrict_succ, finset.mem_image, finset.mem_filter, exists_prop, and_assoc],
  split,
  { rintro ⟨m, hm₁, hm₂, hm⟩,
    simpa only [←hm₂, ←hm, matrix.cons_head_tail] },
  intro hs,
  exact ⟨_, hs, by simp⟩,
end

lemma restrict_succ_bUnion {α : Type*} {s : finset α} {f : α → finset (fin n.succ → ℕ)} :
  s.bUnion (λ x, restrict_succ (f x)) = restrict_succ (s.bUnion f) :=
begin
  ext x,
  simp only [mem_restrict_succ_iff, finset.mem_bUnion],
end

lemma restrict_succ_space {b : brick n.succ} (hb : b.head ≠ 0) :
  restrict_succ b.space = brick.space b.tail :=
begin
  ext x,
  simp only [mem_restrict_succ_iff, set.mem_set_of_eq, mem_space],
  rw fin.forall_fin_succ,
  simp [hb, pos_iff_ne_zero],
end


lemma vadd_card {s : finset ℕ} {n : ℕ} : (n +ᵥ s).card = s.card :=
finset.card_image_of_injective _ (λ _, by simp)


def restrict_at (s : finset (fin n → ℕ)) (i : fin n) : finset ℕ :=
(s.filter (λ x : fin n → ℕ, ∀ j, i ≠ j → x j = 0)).image ($ i)

lemma mem_restrict_at_iff {s : finset (fin n → ℕ)} {i : fin n} {k : ℕ} :
  k ∈ restrict_at s i ↔ (finsupp.single i k : fin n → ℕ) ∈ s :=
begin
  simp only [restrict_at, finset.mem_image, finset.mem_filter, exists_prop, and_assoc],
  split,
  { rintro ⟨m, hm₁, hm₂, hm⟩,
    convert hm₁,
    ext j,
    rw [finsupp.single_apply],
    split_ifs,
    { rw [←h, hm] },
    { rwa hm₂ } },
  { intro h,
    exact ⟨_, h, by simp {contextual := tt}⟩ },
end

lemma restrict_at_bUnion {α : Type*} {s : finset α} {f : α → finset (fin n → ℕ)} {i : fin n} :
  s.bUnion (λ x, restrict_at (f x) i) = restrict_at (s.bUnion f) i :=
begin
  ext x,
  simp only [mem_restrict_at_iff, finset.mem_bUnion],
end

lemma restrict_at_space {b : brick n} {i : fin n} (hb : ∀ j : fin n, i ≠ j → b.nth j ≠ 0)  :
  restrict_at b.space i = finset.range (b.nth i) :=
begin
  ext x,
  simp only [mem_restrict_at_iff, set.mem_set_of_eq, mem_space, finsupp.single_apply],
  split,
  { intro j, simpa using j i },
  intros hx j,
  split_ifs,
  { rwa [←h] },
  simp only [nat.Ico_zero_eq_range, finset.mem_range],
  exact (hb _ h).bot_lt,
end

lemma restrict_at_vadd (u : fin n → ℕ) (s : finset (fin n → ℕ)) {i : fin n} :
  restrict_at (u +ᵥ s) i = if ∀ j, i ≠ j → u j = 0 then u i +ᵥ restrict_at s i else ∅ :=
begin
  ext x,
  simp only [mem_restrict_at_iff, finset.mem_vadd_finset, vadd_eq_add, function.funext_iff,
    pi.add_apply, ne.def, finsupp.single_apply],
  split_ifs,
  { simp only [finset.mem_vadd_finset, mem_restrict_at_iff, vadd_eq_add],
    split,
    { rintro ⟨y, hy, hy'⟩,
      refine ⟨y i, _, by simpa using hy' i⟩,
      convert hy,
      ext j,
      rw finsupp.single_apply,
      split_ifs,
      { rw h_1 },
      suffices : u j = 0 ∧ y j = 0, exact this.right.symm,
      simpa [h_1] using hy' j },
    rintro ⟨y, hy, rfl⟩,
    refine ⟨_, hy, λ j, _⟩,
    rw finsupp.single_apply,
    split_ifs,
    { subst i },
    rw h _ h_1 },
  simp only [finset.not_mem_empty, iff_false, not_exists, not_and, not_forall],
  simp only [not_forall, exists_prop] at h,
  obtain ⟨j, hj₁, hj₂⟩ := h,
  rintro y hy,
  exact ⟨j, by simp [hj₁, hj₂]⟩,
end

lemma pairwise_disjoint_restrict_at {α : Type*} {s : set α} {f : α → finset (fin n → ℕ)}
  {i : fin n} (h : s.pairwise_disjoint f) :
  s.pairwise_disjoint (λ k, restrict_at (f k) i) :=
begin
  simp only [set.pairwise_disjoint, function.on_fun, set.pairwise, finset.disjoint_iff_ne,
    mem_restrict_at_iff] at h ⊢,
  rintro x hx y hy t a ha b hb rfl,
  exact h hx hy t _ ha _ hb rfl,
end

lemma brick.trivially_fills_box_iff {b B : brick n}
  (hb : ∀ i, b.nth i ≠ 0) (hB : ∀ i, B.nth i ≠ 0) :
  b.trivially_fills B.space ↔ ∀ i, b.nth i ∣ B.nth i :=
begin
  split,
  { rintro ⟨p, hp₁, hp₂⟩,
    intro i,
    have : (restrict_at B.space i).card = B.nth i,
    { rw [restrict_at_space (λ k _, hB k), finset.card_range] },
    rw [←this, ←hp₂, ←restrict_at_bUnion, finset.card_bUnion (pairwise_disjoint_restrict_at hp₁)],
    simp only [restrict_at_vadd, apply_ite finset.card, finset.card_empty, ←finset.sum_filter,
      vadd_card, restrict_at_space (λ k _, hb k), finset.card_range, finset.sum_const,
      smul_eq_mul, dvd_mul_left] },
  intro k,
  choose f hf using k,
  refine ⟨fintype.pi_finset (λ i, (finset.range (f i)).image (* vector.nth b i)), _, _⟩,
  {
    simp only [set.pairwise_disjoint, set.pairwise, function.on_fun, finset.mem_coe,
      fintype.mem_pi_finset, finset.mem_image, finset.mem_range, exists_prop,
      finset.disjoint_iff_ne, finset.mem_vadd_finset, vadd_eq_add, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, mem_space'],
    rintro x hx y hy hxy p hp q hq k,
    apply hxy _,
    ext i,
    simp only [function.funext_iff, pi.add_apply] at k,
    obtain ⟨kx, h₁kx, h₂kx⟩ := hx i,
    obtain ⟨ky, h₁ky, h₂ky⟩ := hy i,
    have : (x i + p i) / b.nth i = (y i + q i) / b.nth i,
    { rw k },
    rw [←h₂kx, ←h₂ky] at *,
    rw [add_comm, mul_comm, nat.add_mul_div_left _ _ (hb _).bot_lt, nat.div_eq_zero (hp _),
      zero_add, add_comm, mul_comm, nat.add_mul_div_left _ _ (hb _).bot_lt, nat.div_eq_zero (hq _),
      zero_add] at this,
    rw this,
    -- rw [nat.add_mod, nat.mod_eq_zero_of_lt] at this,

    -- congr' 1,
    -- apply_fun (/ vector.nth b i) at this,
    -- simp at this,
    -- rw nat.add_mul_div_left,
    -- rintro x hx y hy hxy p hp q hq rfl,
    -- refine hxy _,

    -- simp only [finset.mem_image, finset.mem_range, exists_prop, ne.def],
  },
  ext x,
  simp only [finset.mem_bUnion, fintype.mem_pi_finset, finset.mem_image, finset.mem_range,
    exists_prop, finset.mem_vadd_finset, vadd_eq_add, mem_space],
  split,
  {

  },

  -- induction n with n ih,
  -- { simp only [is_empty.forall_iff, iff_true],
  --   refine ⟨{fin.elim0}, by simp, _⟩,
  --   ext,
  --   simp [space_nil, subsingleton.elim b vector.nil, subsingleton.elim B vector.nil] },
  -- obtain ⟨b0, b, rfl⟩ := b.exists_eq_cons,
  -- obtain ⟨B0, B, rfl⟩ := B.exists_eq_cons,
  -- simp only [fin.forall_fin_succ, vector.nth_cons_zero, vector.nth_cons_succ] at hb hB ⊢,
  -- rw ←ih hb.2 hB.2,

  -- -- split,
  -- -- { rintro ⟨p, hp₁, hp₂⟩,
  -- --   refine ⟨_, p.image matrix.vec_tail, _, _⟩,
  -- --   { apply_fun restrict_zero at hp₂,
  -- --     apply_fun finset.card at hp₂,
  -- --     rw [restrict_zero_space, ←restrict_zero_bUnion, vector.nth_cons_zero, nat.Ico_zero_eq_range,
  -- --       finset.card_range, finset.card_bUnion] at hp₂,
  -- --     { simp only [restrict_zero_vadd, apply_ite finset.card, finset.card_empty,
  -- --         ←finset.sum_filter, vadd_card, smul_eq_mul, finset.sum_const] at hp₂,
  -- --       rw [restrict_zero_space, nat.card_Ico, tsub_zero, vector.nth_cons_zero] at hp₂,
  -- --       { rw ←hp₂,
  -- --         apply dvd_mul_left },
  -- --       simpa only [vector.nth_cons_succ] using hb.2 },
  -- --     { intros x hx y hy hxy,
  -- --       simp only [finset.disjoint_iff_ne, mem_restrict_zero_iff],
  -- --       rintro p hp q hq rfl,
  -- --       exact finset.disjoint_iff_ne.1 (hp₁ hx hy hxy) _ hp _ hq rfl },
  -- --     { simpa only [vector.nth_cons_succ] using hB.2 } },
  -- --   {
  -- --     -- simp only [set.pairwise_disjoint, set.pairwise, finset.disjoint_iff_ne, function.on_fun,
  -- --     --   finset.coe_image, set.mem_image, finset.mem_coe, ne.def, forall_exists_index, and_imp,
  -- --     --   forall_apply_eq_imp_iff₂, finset.mem_vadd_finset, vadd_eq_add] at hp₁ ⊢,
  -- --     -- intros x hx y hy ht i hi j hj,
  -- --     -- have := hp₁ hx hy _,
  -- --     -- intros x hx y hy ht,

  -- --   },
  -- -- },
end
