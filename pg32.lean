import data.finset.card
import data.fintype.basic
import data.zmod.basic
import data.matrix.notation
import algebra.char_p.two
import algebra.char_p.pi

variables {α : Type*} [decidable_eq α]

@[derive (λ t, has_coe t (fin 4 → zmod 2))]
def pg32.point := {x : fin 4 → zmod 2 // x ≠ 0}

@[derive (λ t, has_coe t (finset pg32.point))]
def pg32.line : Type := {s : finset pg32.point // s.card = 3 ∧ s.sum (coe : _ → fin 4 → zmod 2) = 0}

open pg32

meta def go_away : command := `[dec_trivial]
meta def pls : command :=
  tactic.assumption <|>
  (tactic.symmetry >> tactic.assumption) <|>
  tactic.fail "pls"

def mk_point (x : fin 4 → zmod 2) (h : ∃ i, x i ≠ 0 . go_away) : pg32.point :=
{ val := x, property := by { rwa function.ne_iff } }

@[simp] lemma mk_point_coe {x h} : (mk_point x h : fin 4 → zmod 2) = x := rfl

lemma mk_point_iff (x y : fin 4 → zmod 2) (hx : ∃ i, x i ≠ 0) (hy : ∃ i, y i ≠ 0) :
  mk_point x hx = mk_point y hy ↔ x = y :=
subtype.ext_iff

lemma vecs_eq_iff {n : ℕ} (x y : fin (n + 1) → zmod 2) :
  x = y ↔ matrix.vec_head x = matrix.vec_head y ∧ matrix.vec_tail x = matrix.vec_tail y :=
begin
  split,
  { rintro rfl,
    simp },
  intro h,
  ext i : 1,
  refine fin.cases _ _ i,
  { exact h.1 },
  rw function.funext_iff at h,
  exact h.2
end

lemma add_eq_iff (x y : fin 4 → zmod 2) : x + y = 0 ↔ x = y :=
by rw [←char_two.sub_eq_add, sub_eq_zero]

lemma add_ne_iff (x y : fin 4 → zmod 2) : x + y ≠ 0 ↔ x ≠ y :=
by rw [ne.def, add_eq_iff]

@[simp] lemma point.ne_zero (x : point) : (x : fin 4 → zmod 2) ≠ 0 := x.prop

def add (x y : point) :=
if h : x = y then x else ⟨x + y, (add_ne_iff _ _).2 (by simpa [subtype.ext_iff] using h)⟩

instance : has_add point := ⟨add⟩

@[simp] lemma add_self {x : point} : x + x = x := dif_pos rfl
@[simp] lemma add_val_ne {x y : point} (h : x ≠ y . pls) : (↑(x + y) : fin 4 → zmod 2) = x + y :=
congr_arg _ (dif_neg h)

lemma add_ne_left {x y : point} (h : x ≠ y . pls) : x + y ≠ x :=
by { rw [←subtype.coe_injective.ne_iff, add_val_ne], simp }

lemma add_ne_right {x y : point} (h : x ≠ y . pls) : x + y ≠ y :=
by { rw [←subtype.coe_injective.ne_iff, add_val_ne], simp }

lemma point.add_comm (x y : point) : x + y = y + x :=
begin
  rcases eq_or_ne x y with rfl | hxy, { refl },
  rw [subtype.ext_iff, add_val_ne, add_val_ne, add_comm]
end

lemma add_eq_comm' (x y z : point) (h : x ≠ y . pls) : x + y = z → x + z = y :=
begin
  rintro rfl,
  rw [subtype.ext_iff, add_val_ne, add_val_ne, ←add_assoc, char_two.add_self_eq_zero, zero_add],
  exact add_ne_left.symm,
end

lemma add_eq_comm (x y z : point) (h : x ≠ y . pls) : x + y = z ↔ x + z = y :=
begin
  refine ⟨add_eq_comm' _ _ _, _⟩,
  rintro rfl,
  have : x ≠ z,
  { rintro rfl,
    simp only [ne.def, auto_param_eq] at h,
    change ¬ (x = dite (x = x) _ _) at h,
    rw dif_pos rfl at h,
    exact h rfl },
  apply add_eq_comm' _ _ _ this rfl,
end

lemma point.add_assoc {x y z : point} (hxy : x ≠ y . pls) (hxz : x ≠ z . pls) (hyz : y ≠ z . pls)
  (h : x + y ≠ z . pls) :
  x + y + z = x + (y + z) :=
begin
  have : y + z ≠ x,
  { rwa [ne.def, add_eq_comm, point.add_comm] },
  rw [subtype.ext_iff, add_val_ne, add_val_ne, add_val_ne, add_val_ne, add_assoc],
end

lemma point.add_assoc' {x y z : point} (hxy : x ≠ y . pls) (hxz : x ≠ z . pls) (hyz : y ≠ z . pls)
  (h : y + z ≠ x . pls) :
  x + y + z = x + (y + z) :=
begin
  have : x + y ≠ z,
  { rwa [ne.def, point.add_comm, add_eq_comm] },
  rw point.add_assoc,
end

@[simp] lemma add_cancel_left {x y : point} (hxy : x ≠ y . pls) : x + (x + y) = y :=
by rw ←add_eq_comm

@[simp] lemma add_cancel_right {x y : point} (hxy : x ≠ y . pls) : x + (y + x) = y :=
by rw [←add_eq_comm, point.add_comm]

lemma add_cancellative_left' {x y z : point} (hxz : x ≠ z . pls) (hyz : y ≠ z . pls) :
  x + z = y + z ↔ x = y :=
by { rw [subtype.ext_iff, subtype.ext_iff, add_val_ne, add_val_ne], simp }

lemma add_cancellative_left {x y z : point} : x + z = y + z ↔ x = y :=
begin
  split,
  { intro h,
    rcases eq_or_ne x z with rfl | hxz,
    { by_contra h',
      rw add_self at h,
      revert h,
      exact add_ne_right.symm },
    rcases eq_or_ne y z with rfl | hyz,
    { rw add_self at h,
      cases add_ne_right hxz h },
    rwa add_cancellative_left' at h },
  rintro rfl,
  simp
end

lemma add_cancellative_right {x y z : point} : z + x = z + y ↔ x = y :=
by rw [point.add_comm, point.add_comm z, add_cancellative_left]

def line_of_distinct3 (a b c : point) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (h : (a : fin 4 → zmod 2) + b + c = 0) : line :=
⟨⟨[a, b, c], by simp [*]⟩, by simpa [add_assoc] using h⟩

lemma line_of_distinct3_eq {a b c : point} (h : (a : fin 4 → zmod 2) + b + c = 0)
  (hab : a ≠ b . pls) (hac : a ≠ c . pls) (hbc : b ≠ c . pls) :
  ((line_of_distinct3 a b c hab hac hbc h) : finset pg32.point) = {a, b, c} :=
by { rw [line_of_distinct3, subtype.coe_mk], ext i, simp }

def line_of_distinct3' (a b c : point) (h : a + b = c)
  (hab : a ≠ b . pls) (hac : a ≠ c . pls) (hbc : b ≠ c . pls) : line :=
line_of_distinct3 _ _ _ hab hac hbc $ by rwa [add_eq_iff, ←add_val_ne, h]

lemma line_of_distinct3'_eq {a b c : point} (h : a + b = c)
  (hab : a ≠ b . pls) (hac : a ≠ c . pls) (hbc : b ≠ c . pls) :
  ((line_of_distinct3' a b c h) : finset pg32.point) = {a, b, c} :=
begin
  rw [line_of_distinct3', line_of_distinct3, subtype.coe_mk],
  ext i,
  simp,
end

meta def do_the_thing : command := `[simp [mk_point_iff, vecs_eq_iff]]

def mk_line_of_distinct3' (a b c : fin 4 → zmod 2)
  (ha : ∃ i, a i ≠ 0 . go_away) (hb : ∃ i, b i ≠ 0 . go_away) (hc : ∃ i, c i ≠ 0 . go_away)
  (hab : a ≠ b . do_the_thing) (hac : a ≠ c . do_the_thing)
  (hbc : b ≠ c . do_the_thing) (h : (a : fin 4 → zmod 2) + b = c . do_the_thing) :
  line :=
line_of_distinct3 (mk_point a ha) (mk_point b hb) (mk_point c hc) (subtype.ne_of_val_ne hab)
  (subtype.ne_of_val_ne hac) (subtype.ne_of_val_ne hbc) (by rwa add_eq_iff)

instance : has_mem point line := ⟨λ p l, p ∈ (l : finset pg32.point)⟩

lemma mem_line_iff {p : point} {l : line} : p ∈ l ↔ p ∈ (l : finset pg32.point) := iff.rfl

@[simp] lemma mem1 {a b c : point} {hab hac hbc h} :
  a ∈ line_of_distinct3' a b c h :=
or.inl rfl

@[simp] lemma mem2 {a b c : point} {hab hac hbc h} :
  b ∈ line_of_distinct3' a b c h :=
or.inr (or.inl rfl)

@[simp] lemma mem3 {a b c : point} {hab hac hbc h} :
  c ∈ line_of_distinct3' a b c h :=
or.inr (or.inr (or.inl rfl))

instance : fintype point := subtype.fintype _
instance : fintype line :=
fintype.subtype ((finset.univ.powerset_len 3).filter (λ i, i.sum subtype.val = 0))
(by simp [finset.mem_powerset_len_univ_iff])

@[simp] lemma card_point : fintype.card point = 15 := rfl
@[simp] lemma card_line : fintype.card line = 35 := rfl.

instance : nontrivial point := fintype.one_lt_card_iff_nontrivial.1 (by norm_num)
instance : nontrivial line := fintype.one_lt_card_iff_nontrivial.1 (by norm_num)


lemma get_third_on_line (a b : point) (h : a ≠ b . pls) :
  ∃ c (l : line), c ≠ a ∧ c ≠ b ∧ a ∈ l ∧ b ∈ l ∧ c ∈ l :=
⟨a + b, line_of_distinct3' a b (a + b) rfl h add_ne_left.symm add_ne_right.symm,
    add_ne_left, add_ne_right, by simp⟩

lemma get_second_third_point (l : line) {a : point} (ha : a ∈ l . pls) :
  ∃ b c, b ≠ c ∧ (l : finset pg32.point) = {a, b, c} :=
begin
  suffices : ∃ b c, b ≠ c ∧ (l : finset pg32.point).erase a = {b, c},
  { obtain ⟨b, c, hbc, hl⟩ := this,
    refine ⟨b, c, hbc, _⟩,
    rw [←hl, finset.insert_erase ha] },
  rwa [←finset.card_eq_two, finset.card_erase_of_mem, l.prop.1],
end

lemma get_third_point (l : line) (a b : point) (hab : a ≠ b . pls) (ha : a ∈ l . pls)
  (hb : b ∈ l . pls) :
  ∃ c, a ≠ c ∧ b ≠ c ∧ (l : finset pg32.point) = {a, b, c} :=
begin
  suffices : ∃ c, a ≠ c ∧ b ≠ c ∧ ((l : finset pg32.point).erase a).erase b = {c},
  { obtain ⟨c, ac, bc, hl⟩ := this,
    refine ⟨c, ac, bc, _⟩,
    rwa [←hl, finset.insert_erase, finset.insert_erase],
    simpa [hab.symm] },
  suffices : ∃ c, ((l : finset pg32.point).erase a).erase b = {c},
  { obtain ⟨c, hc⟩ := this,
    have bc : b ∉ {c},
    { rw [←hc],
      apply finset.not_mem_erase },
    have ac : a ∉ {c},
    { rw [←hc, finset.erase_right_comm],
      apply finset.not_mem_erase },
    exact ⟨c, by simpa using ac, by simpa using bc, hc⟩ },
  rwa [←finset.card_eq_one, finset.card_erase_of_mem, finset.card_erase_of_mem, l.prop.1],
  simpa [hab.symm],
end

lemma line_eq_of_mems (a b c : point) (l : line) (ha : a ∈ l . pls) (hb : b ∈ l . pls)
  (hc : c ∈ l . pls) (ab : a ≠ b . pls) (ac : a ≠ c . pls) (bc : b ≠ c . pls) :
  (l : finset pg32.point) = {a, b, c} :=
begin
  apply (finset.eq_of_subset_of_card_le _ _).symm,
  { simp only [finset.insert_subset, finset.singleton_subset_iff, ←mem_line_iff,
      ha, hb, hc, and_self] },
  rw l.prop.1,
  exact ge_of_eq (finset.card_eq_three.2 ⟨a, b, c, ab, ac, bc, rfl⟩),
end

lemma diff_of_card_eq_two {a b : α} {s : finset α} (hs : s.card = 2)
  (h : s = {a, b}) : a ≠ b :=
begin
  subst h,
  rintro rfl,
  simpa using hs
end

lemma diff_of_card_eq_three {a b c : α} {s : finset α} (hs : s.card = 3)
  (h : s = {a, b, c}) : a ≠ b ∧ a ≠ c ∧ b ≠ c :=
begin
  subst h,
  rw [finset.card_insert_eq_ite] at hs,
  have : finset.card {b, c} ≠ 3,
  { apply ne_of_lt,
    rw nat.lt_add_one_iff,
    refine (finset.card_insert_le _ {c}).trans _,
    simp },
  simp only [ite_eq_iff, this, and_false, false_or, finset.mem_insert, finset.mem_singleton,
    not_or_distrib, ←ne.def, nat.succ_inj'] at hs,
  exact ⟨hs.1.1, hs.1.2, diff_of_card_eq_two hs.2 rfl⟩,
end

lemma sum_of_eq {a b c : point} {l : line} (hl : (l : finset pg32.point) = {a, b, c}) :
  (a : fin 4 → zmod 2) + b + c = 0 :=
begin
  have := diff_of_card_eq_three l.prop.1 hl,
  rw [←l.prop.2, hl, finset.sum_insert, finset.sum_pair this.2.2, add_assoc],
  simp [this.1, this.2.1],
end

lemma third_point_eq (a b c : point) (l : line) (ha : a ∈ l . pls) (hb : b ∈ l . pls)
  (hab : a ≠ b . pls) (hac : a ≠ c . pls) (hbc : b ≠ c . pls) (hc : c ∈ l . pls) :
  a + b = c :=
by { apply subtype.ext, rw ←add_eq_iff, rw add_val_ne, exact sum_of_eq (line_eq_of_mems a b c l) }

lemma add_mem_line (a b : point) (l : line) (ha : a ∈ l . pls) (hb : b ∈ l . pls) :
  a + b ∈ l :=
begin
  rcases eq_or_ne a b with rfl | h,
  { simpa },
  obtain ⟨c, ac, bc, h⟩ := get_third_point l a b,
  rw [mem_line_iff, h],
  apply finset.mem_insert_of_mem,
  apply finset.mem_insert_of_mem,
  rw finset.mem_singleton,
  have : c ∈ l,
  { rw [mem_line_iff, h],
    simp },
  exact third_point_eq a b c l,
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
    obtain ⟨c, l, hca, hcb, hal, hbl, hcl⟩ := get_third_on_line a b,
    exact ⟨l, hal, hal⟩ },
  have := get_third_on_line a b,
  tauto
end

lemma uniqueness (a b : point) (l₁ l₂ : line) (ha₁ : a ∈ l₁ . pls) (hb₁ : b ∈ l₁ . pls)
  (ha₂ : a ∈ l₂ . pls) (hb₂ : b ∈ l₂ . pls) : a = b ∨ l₁ = l₂ :=
begin
  simp only [or_iff_not_imp_left],
  intros h,
  obtain ⟨c₁, hac₁, hbc₁, hl₁⟩ := get_third_point l₁ a b,
  obtain ⟨c₂, hac₂, hbc₂, hl₂⟩ := get_third_point l₂ a b,
  ext : 1,
  rw [hl₁, hl₂],
  congr' 3,
  ext : 1,
  rw ←(add_eq_iff _ _).1 (sum_of_eq hl₁),
  exact (add_eq_iff _ _).1 (sum_of_eq hl₂),
end

lemma a3_1 (l : line) : ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∈ l ∧ b ∈ l ∧ c ∈ l :=
begin
  obtain ⟨a, b, c, ab, ac, bc, hl⟩ := finset.card_eq_three.1 l.prop.1,
  refine ⟨a, b, c, ab, ac, bc, _⟩,
  rw [mem_line_iff, mem_line_iff, mem_line_iff, hl],
  simp
end

-- we can remove a lot of assumptions from the coq version
lemma a2 {a b c d i : point} {lAB lCD lAC lBD : line} (hac : a ≠ c) (hbd : b ≠ d)
  (haAB : a ∈ lAB) (hbAB : b ∈ lAB)
  (hcCD : c ∈ lCD) (hdCD : d ∈ lCD)
  (haAC : a ∈ lAC) (hcAC : c ∈ lAC)
  (hbBD : b ∈ lBD) (hdBD : d ∈ lBD)
  (hiAB : i ∈ lAB) (hiCD : i ∈ lCD) :
  ∃ j, j ∈ lAC ∧ j ∈ lBD :=
begin
  rcases eq_or_ne a b with rfl | hab, { exact ⟨a, haAC, hbBD⟩ },
  rcases eq_or_ne c d with rfl | hcd, { exact ⟨c, hcAC, hdBD⟩ },
  rcases eq_or_ne lAC lCD with rfl | hC,
  { exact ⟨d, hdCD, hdBD⟩ },
  rcases eq_or_ne lBD lCD with rfl | hD,
  { exact ⟨c, ‹_›, ‹_›⟩ },
  rcases eq_or_ne lAB lAC with rfl | hA,
  { exact ⟨b, ‹_›, ‹_›⟩ },
  rcases eq_or_ne lAB lBD with rfl | hB,
  { exact ⟨a, ‹_›, ‹_›⟩ },
  rcases eq_or_ne a i with rfl | hai,
  { cases hac ((uniqueness a c lAC lCD).resolve_right hC) },
  rcases eq_or_ne b i with rfl | hbi,
  { cases hbd ((uniqueness b d lBD lCD).resolve_right hD) },
  rcases eq_or_ne c i with rfl | hci,
  { cases hac ((uniqueness a c lAB lAC).resolve_right hA) },
  rcases eq_or_ne d i with rfl | hdi,
  { cases hbd ((uniqueness b d lAB lBD).resolve_right hB) },
  have h₁ := third_point_eq a b i lAB,
  have h₂ := third_point_eq c d i lCD,
  refine ⟨_, add_mem_line a c lAC, _⟩,
  have : a + c = b + d,
  { simp only [subtype.ext_iff, add_val_ne] at h₁ h₂ ⊢,
    rw [←add_eq_iff, add_add_add_comm, h₁, h₂, char_two.add_self_eq_zero] },
  simp only [this],
  exact add_mem_line _ _ _ hbBD hdBD,
end

lemma a3_2 : ∃ (l₁ l₂ : line), ∀ p, ¬ (p ∈ l₁ ∧ p ∈ l₂) :=
begin
  simp only [not_and],
  refine ⟨mk_line_of_distinct3' ![0, 0, 0, 1] ![0, 0, 1, 0] ![0, 0, 1, 1],
          mk_line_of_distinct3' ![0, 1, 0, 0] ![1, 0, 0, 0] ![1, 1, 0, 0],
    _⟩,
  simp [mk_line_of_distinct3', mem_line_iff, line_of_distinct3_eq, mk_point_iff, vecs_eq_iff],
end.

section
open_locale pointwise

lemma a3_3 (l₁ l₂ l₃ : line) :
  ∃ (l₄ : line) p₁ p₂ p₃, p₁ ∈ l₁ ∧ p₁ ∈ l₄ ∧ p₂ ∈ l₂ ∧ p₂ ∈ l₄ ∧ p₃ ∈ l₃ ∧ p₃ ∈ l₄ :=
begin
  simp only [mem_line_iff],
  by_cases h₁₂ : ∃ x, x ∈ (l₁ : finset point) ∧ x ∈ (l₂ : finset point),
  { obtain ⟨x, hx₁, hx₂⟩ := h₁₂,
    obtain ⟨g, h, i, -, -, -, hl₃⟩ := finset.card_eq_three.1 l₃.prop.1,
    obtain ⟨l₄, hx, hg⟩ := a1_exists x g,
    refine ⟨l₄, x, x, g, _, _, _, _, (by simp [hl₃]), _⟩,
    assumption' },
  push_neg at h₁₂,
  by_cases h₁₃ : ∃ x, x ∈ (l₁ : finset point) ∧ x ∈ (l₃ : finset point),
  { obtain ⟨x, hx₁, hx₃⟩ := h₁₃,
    obtain ⟨g, h, i, -, -, -, hl₂⟩ := finset.card_eq_three.1 l₂.prop.1,
    obtain ⟨l₄, hx, hg⟩ := a1_exists x g,
    refine ⟨l₄, x, g, x, _, _, (by simp [hl₂]), _, _, _⟩,
    assumption' },
  push_neg at h₁₃,
  by_cases h₂₃ : ∃ x, x ∈ (l₂ : finset point) ∧ x ∈ (l₃ : finset point),
  { obtain ⟨x, hx₂, hx₃⟩ := h₂₃,
    obtain ⟨g, h, i, -, -, -, hl₁⟩ := finset.card_eq_three.1 l₁.prop.1,
    obtain ⟨l₄, hx, hg⟩ := a1_exists x g,
    refine ⟨l₄, g, x, x, (by simp [hl₁]), _, _, _, _, _⟩,
    assumption' },
  push_neg at h₂₃,
  let adds := (l₁ : finset point) + l₂,
  have hl₁ : disjoint adds l₁,
  { simp only [finset.disjoint_left, finset.mem_add],
    rintro _ ⟨x₁, x₂, hx₁, hx₂, rfl⟩ h,
    apply h₁₂ (x₁ + (x₁ + x₂)) (add_mem_line _ _ _),
    have : x₁ ≠ x₂,
    { exact (hx₂.ne_of_not_mem (h₁₂ _ hx₁)).symm },
    rwa add_cancel_left },
  have hl₂ : disjoint adds l₂,
  { simp only [finset.disjoint_left, finset.mem_add],
    rintro _ ⟨x₁, x₂, hx₁, hx₂, rfl⟩ h,
    apply h₁₂ (x₂ + (x₁ + x₂)) _ (add_mem_line _ _ l₂),
    have : x₁ ≠ x₂,
    { exact (hx₂.ne_of_not_mem (h₁₂ _ hx₁)).symm },
    rwa add_cancel_right },
  have : adds.card = 9,
  { rw [finset.card_add_iff.2, l₁.prop.1, l₂.prop.1],
    { norm_num1 },
    rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩ h,
    simp only [finset.mem_coe] at hx₁ hx₂ hy₁ hy₂,
    dsimp at h,
    have : x₁ ≠ x₂ := (ne_of_mem_of_not_mem hx₂ (h₁₂ x₁ hx₁)).symm,
    have : y₁ ≠ y₂ := (ne_of_mem_of_not_mem hy₂ (h₁₂ y₁ hy₁)).symm,
    have : x₁ ≠ y₂ := (ne_of_mem_of_not_mem hy₂ (h₁₂ x₁ hx₁)).symm,
    have : x₂ ≠ y₁ := (ne_of_mem_of_not_mem hx₂ (h₁₂ y₁ hy₁)),
    rcases eq_or_ne x₁ y₁ with rfl | _, { rw add_cancellative_right at h, simp [h] },
    rcases eq_or_ne x₂ y₂ with rfl | _, { rw add_cancellative_left at h, cases h_1 h },
    have : x₁ + y₁ ≠ y₂ := (ne_of_mem_of_not_mem hy₂ (h₁₂ _ (add_mem_line x₁ _ _))).symm,
    rw [add_eq_comm, ←point.add_assoc, point.add_comm, add_eq_comm] at h,
    cases ne_of_mem_of_not_mem (add_mem_line y₂ x₂ l₂) (h₁₂ _ (add_mem_line x₁ y₁ l₁)) h },
  have : (l₁ : finset point) ∪ l₂ ∪ adds = finset.univ,
  { apply finset.eq_univ_of_card,
    rw [finset.card_disjoint_union, this, finset.card_disjoint_union, l₁.prop.1, l₂.prop.1,
      card_point],
    { rwa finset.disjoint_left },
    rw [disjoint.comm, finset.disjoint_union_right],
    exact ⟨hl₁, hl₂⟩ },
  have : (l₃ : finset point) ⊆ adds,
  { intros x hx,
    by_contra' t,
    have : x ∉ (finset.univ : finset point),
    { rw [←this],
      simp [finset.union_assoc, finset.mem_union, t,
        mt (h₂₃ x) (λ i, i hx), mt (h₁₃ x) (λ i, i hx)] },
    simpa using this, },
  obtain ⟨c, -, -, _, _, _, hc, _, _⟩ := a3_1 l₃,
  obtain ⟨a, b, ha, hb, rfl⟩ := finset.mem_add.1 (this hc),
  obtain ⟨l₄, ha₄, hb₄⟩ := a1_exists a b,
  exact ⟨l₄, a, b, a + b, ha, ha₄, hb, hb₄, hc, add_mem_line _ _ l₄⟩,
end

end
