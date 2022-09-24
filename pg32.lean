import data.finset.card
import data.fintype.basic
import data.zmod.basic
import data.matrix.notation
import algebra.char_p.two
import algebra.char_p.pi

def pg32.point := {x : fin 4 → zmod 2 // x ≠ 0}

def pg32.point.vec : pg32.point → fin 4 → zmod 2 := subtype.val

def pg32.line := {s : finset pg32.point // s.card = 3 ∧ s.sum subtype.val = 0}

open pg32

@[simp] lemma coe_eq_vec (p : pg32.point) : p.val = p.vec := rfl

lemma add_eq_iff (x y : fin 4 → zmod 2) : x + y = 0 ↔ x = y :=
by rw [←char_two.sub_eq_add, sub_eq_zero]

def line_of_distinct3 (a b c : point) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (h : a.1 + b.1 + c.1 = 0) : line :=
⟨⟨[a, b, c], by simp [*]⟩, by simpa [add_assoc] using h⟩

def line_of_distinct3' (a b c : point) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (h : a.1 + b.1 = c.1) : line :=
line_of_distinct3 _ _ _ hab hac hbc $ by rwa add_eq_iff

instance : has_mem point line := ⟨λ p l, p ∈ l.1⟩

@[simp] lemma mem1 {a b c : point} {hab hac hbc h} :
  a ∈ line_of_distinct3' a b c hab hac hbc h :=
or.inl rfl

@[simp] lemma mem2 {a b c : point} {hab hac hbc h} :
  b ∈ line_of_distinct3' a b c hab hac hbc h :=
or.inr (or.inl rfl)

@[simp] lemma mem3 {a b c : point} {hab hac hbc h} :
  c ∈ line_of_distinct3' a b c hab hac hbc h :=
or.inr (or.inr (or.inl rfl))

instance : fintype point := subtype.fintype _
instance : fintype line :=
fintype.subtype ((finset.univ.powerset_len 3).filter (λ i, i.sum subtype.val = 0))
(by simp [finset.mem_powerset_len_univ_iff])

@[simp] lemma card_point : fintype.card point = 15 := rfl
@[simp] lemma card_line : fintype.card line = 35 := rfl.

instance : nontrivial point := fintype.one_lt_card_iff_nontrivial.1 (by norm_num)
instance : nontrivial line := fintype.one_lt_card_iff_nontrivial.1 (by norm_num)

lemma get_third_line (a b : point) (h : a ≠ b) :
  ∃ c (l : line), c ≠ a ∧ c ≠ b ∧ a ∈ l ∧ b ∈ l ∧ c ∈ l :=
begin
  cases a with a ha,
  cases b with b hb,
  simp only [ne.def, subtype.mk_eq_mk] at h,
  let c : point := ⟨a + b, by rwa [ne.def, add_eq_iff]⟩,
  refine ⟨c, line_of_distinct3' ⟨a, ha⟩ ⟨b, hb⟩ c _ _ _ rfl, _⟩;
  simp [*]
end

lemma get_third (a b : point) : ∃ c, c ≠ a ∧ c ≠ b :=
begin
  suffices : ({a, b} : finset point)ᶜ.nonempty,
  { simpa [finset.nonempty] using this },
  rcases eq_or_ne a b with rfl | hab;
  simp [*, ←finset.card_pos, finset.card_compl],
end

lemma a1_exists (a b : point) : ∃ l : line, a ∈ l ∧ b ∈ l :=
begin
  rcases eq_or_ne a b with rfl | hab,
  { obtain ⟨b, hb⟩ := exists_ne a,
    obtain ⟨c, l, hca, hcb, hal, hbl, hcl⟩ := get_third_line a b hb.symm,
    exact ⟨l, hal, hal⟩ },
  have := get_third_line a b hab,
  tauto
end

lemma add_mem {a b : point} (h : a ≠ b) {l : line} (hal : a ∈ l) (hbl : b ∈ l) :
  a + b ∈ l :=
begin
end

def uniqueness :
  ∀ {a b : point} {l₁ l₂ : line}, a ∈ l₁ → b ∈ l₁ → a ∈ l₂ → b ∈ l₂ → a = b ∨ l₁ = l₂ :=
begin
  -- rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨l₁, hl₁, h'l₁⟩ ⟨l₂, hl₂, h'l₂⟩,
  -- have := finset.card_eq_three.1 hl₁,

end
