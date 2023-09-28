/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import combinatorics.simple_graph.ramsey

/-!
# Constructions to prove lower bounds on some small Ramsey numbers
-/

namespace simple_graph

open fintype (card)
open finset

section paley

variables {F : Type*} [field F] [fintype F]

lemma symmetric_is_square (hF : card F % 4 ≠ 3) :
  symmetric (λ x y : F, is_square (x - y)) :=
λ _ _ h, by simpa using h.mul (finite_field.is_square_neg_one_iff.2 hF)

/--
If `F` is a finite field with `|F| = 3 mod 4`, the Paley graph on `F` has an edge `x ~ y` if
`x - y` is a (non-zero) quadratic residue.
The definition should only be used if `card F % 4 ≠ 3`. If this condition fails, the graph is `⊤`,
but it is still defined for convenience.
-/
def {u} paley_graph (F : Type*) [field F] [fintype F] : simple_graph F :=
{ adj := λ x y, x ≠ y ∧ (is_square (x - y) ∨ card F % 4 = 3),
  symm :=
  begin
    rintro x y ⟨h₁, h₂⟩,
    refine ⟨h₁.symm, _⟩,
    rw or_iff_not_imp_right,
    intro h,
    exact symmetric_is_square h (h₂.resolve_right h),
  end,
  loopless := λ _ h, h.1 rfl }

lemma paley_graph_adj' {x y : F} :
  (paley_graph F).adj x y ↔ x ≠ y ∧ (is_square (x - y) ∨ card F % 4 = 3) :=
iff.rfl

instance paley_decidable [decidable_eq F] :
  decidable_rel (paley_graph F).adj :=
λ x y, decidable_of_iff' _ paley_graph_adj'

lemma paley_graph_adj (hF : card F % 4 ≠ 3) {x y : F} :
  (paley_graph F).adj x y ↔ x ≠ y ∧ is_square (x - y) :=
and_congr_right' (or_iff_left hF)

lemma is_square_sub_of_paley_graph_adj (hF : card F % 4 ≠ 3) {x y : F}
  (h : (paley_graph F).adj x y) : is_square (x - y) :=
((paley_graph_adj hF).1 h).2

/-- Addition of `x` is a graph isomorphism of the Paley graph. -/
@[simps] def rotate (x : F) : paley_graph F ≃g paley_graph F :=
{ to_equiv := equiv.add_left x,
  map_rel_iff' := λ a b, by simp only [paley_graph_adj', equiv.coe_add_left, ne.def, add_right_inj,
    add_sub_add_left_eq_sub] }

/-- The graph automorphism rescaling the Paley graph by a non-zero square. -/
@[simps]
def rescale (x : F) (hx : is_square x) (hx' : x ≠ 0) :
  paley_graph F ≃g paley_graph F :=
{ to_equiv := (units.mk0 x hx').mul_left,
  map_rel_iff' :=
  begin
    intros a b,
    simp only [paley_graph],
    simp only [hx', units.mul_left_apply, units.coe_mk0, ne.def, mul_eq_mul_left_iff, or_false,
      not_and, and.congr_right_iff, not_false_iff, forall_true_left] {contextual := tt},
    intro h,
    have : a - b ≠ 0, { rwa sub_ne_zero },
    refine or_congr_left' _,
    haveI : decidable_eq F := classical.dec_eq F,
    rw ←quadratic_char_one_iff_is_square hx' at hx,
    rw [←not_iff_not, ←mul_sub, ←quadratic_char_neg_one_iff_not_is_square, map_mul, hx, one_mul,
      quadratic_char_neg_one_iff_not_is_square],
  end }

/--
The graph isomorphism witnessing that the Paley graph is self complementary: rescalingby a
non-square.
-/
@[simps]
def self_compl (hF : card F % 4 ≠ 3)
  (x : F) (hx : ¬ is_square x) : (paley_graph F)ᶜ ≃g paley_graph F :=
have hx' : x ≠ 0, from λ h, hx (h.symm ▸ is_square_zero F),
{ to_equiv := (units.mk0 x hx').mul_left,
  map_rel_iff' :=
  begin
    intros a b,
    rw [paley_graph_adj hF, compl_adj, paley_graph_adj hF],
    simp only [hx', units.mul_left_apply, units.coe_mk0, ne.def, mul_eq_mul_left_iff, or_false,
      not_and, and.congr_right_iff, not_false_iff, forall_true_left] {contextual := tt},
    intro h,
    have : a - b ≠ 0,
    { rwa sub_ne_zero },
    classical,
    rw ←quadratic_char_neg_one_iff_not_is_square at hx,
    rw [iff_not_comm, ←mul_sub, ←quadratic_char_neg_one_iff_not_is_square, map_mul, hx,
      ←quadratic_char_one_iff_is_square this, neg_mul, one_mul, neg_inj],
  end }

/-- The Paley graph on a finite field `F` viewed as a labelling of edges. -/
def paley_labelling (F : Type*) [field F] [fintype F] [decidable_eq F] :
  top_edge_labelling F (fin 2) := to_edge_labelling (paley_graph F)

-- smaller `k` don't need the paley construction
lemma no_paley_mono_set [decidable_eq F] {k : ℕ} (hF : card F % 4 = 1)
  (h : ∃ (m : finset F) c, (paley_labelling F).monochromatic_of m c ∧ k + 2 = m.card) :
  ∃ (m : finset F), m.card = k ∧ (0 : F) ∉ m ∧ (1 : F) ∉ m ∧
    (∀ x ∈ m, is_square x) ∧ (∀ x ∈ m, is_square (x - 1 : F)) ∧
      (m : set F).pairwise (λ x y, is_square (y - x)) :=
begin
  have card_not_three_mod_four : card F % 4 ≠ 3,
  { rw hF, simp only [ne.def, nat.one_eq_bit1, nat.one_ne_zero, not_false_iff]},
  have card_one_mod_two : card F % 2 = 1,
  { rw [←nat.mod_mod_of_dvd (card F) (show 2 ∣ 4, by norm_num), hF, nat.one_mod] },
  have : ∃ x : F, ¬ is_square x,
  { apply finite_field.exists_nonsquare,
    rwa [ne.def, finite_field.even_card_iff_char_two, nat.mod_two_ne_zero] },
  rw [exists_comm] at h,
  simp only [is_ramsey_valid_iff_embedding_aux] at h,
  rw [fin.exists_fin_two, paley_labelling, to_edge_labelling_label_graph,
    to_edge_labelling_label_graph_compl] at h,
  have : nonempty ((⊤ : simple_graph (fin (k + 2))) ↪g paley_graph F),
  { rcases h with ⟨⟨h⟩⟩ | h,
    { obtain ⟨x, hx⟩ := this,
      exact ⟨h.trans (self_compl card_not_three_mod_four x hx).to_rel_embedding⟩ },
    exact h },
  have : ∃ f : (⊤ : simple_graph (fin (k + 2))) ↪g paley_graph F, f 0 = 0,
  { obtain ⟨f⟩ := this,
    exact ⟨f.trans (rotate (- f 0)).to_rel_embedding, by simp⟩ },
  have : ∃ f : (⊤ : simple_graph (fin (k + 2))) ↪g paley_graph F, f 0 = 0 ∧ f 1 = 1,
  { obtain ⟨f, hf⟩ := this,
    have hf1 : is_square (f 1),
    { suffices : (paley_graph F).adj (f 1) (f 0),
      { rw [paley_graph_adj card_not_three_mod_four, hf, sub_zero] at this,
        exact this.2 },
      rw f.map_rel_iff,
      simp only [top_adj, ne.def, fin.one_eq_zero_iff, nat.succ_succ_ne_one, not_false_iff] },
    have hf2 : f 1 ≠ 0,
    { rw [←hf, ne.def, rel_embedding.inj],
      simp only [fin.one_eq_zero_iff, nat.succ_succ_ne_one, not_false_iff] },
    refine ⟨f.trans (rescale (f 1) hf1 hf2).symm.to_rel_embedding, _⟩,
    simp only [hf2, hf, rel_iso.to_rel_embedding_eq_coe, embedding.coe_comp, rel_iso.coe_coe_fn,
      function.comp_app, rescale_symm_apply, units.coe_inv, units.coe_mk0, mul_zero,
      eq_self_iff_true, inv_mul_cancel, ne.def, not_false_iff, and_self] },
  have hss : symmetric (λ x y : F, is_square (y - x)),
  { intros x y h,
    exact symmetric_is_square card_not_three_mod_four h },
  suffices : ∃ m : finset F, k = m.card ∧ (0 : F) ∉ m ∧ (1 : F) ∉ m ∧
    (insert (0 : F) (insert (1 : F) (m : set F))).pairwise (λ x y, is_square (y - x)),
  { obtain ⟨m, hm_card, hm₀, hm₁, hm₂⟩ := this,
    rw [set.pairwise_insert_of_symmetric_of_not_mem hss,
      set.pairwise_insert_of_symmetric_of_not_mem hss] at hm₂,
    simp only [mem_coe, set.mem_insert_iff, sub_zero, forall_eq_or_imp, is_square_one,
      true_and] at hm₂,
    { exact ⟨m, hm_card.symm, hm₀, hm₁, hm₂.2, hm₂.1.2, hm₂.1.1⟩ },
    { exact hm₁ },
    simp only [hm₀, set.mem_insert_iff, zero_ne_one, mem_coe, or_self, not_false_iff] },
  simp only [←coe_insert],
  obtain ⟨f, hf₀, hf₁⟩ := this,
  have : ({0, 1} : finset F) ⊆ finset.map f.to_embedding univ,
  { rw [insert_subset, singleton_subset_iff, ←hf₀, ←hf₁],
    exact ⟨mem_map_of_mem _ (by simp), mem_map_of_mem _ (by simp)⟩ },
  refine ⟨(univ : finset (fin (k + 2))).map f.to_embedding \ {0, 1}, _, _, _, _⟩,
  { rw [card_sdiff, card_map, card_doubleton, card_fin, nat.add_sub_cancel],
    { simp only [ne.def, zero_ne_one, not_false_iff] },
    exact this },
  { simp only [mem_sdiff, mem_insert, eq_self_iff_true, mem_singleton, zero_ne_one, or_false,
      not_true, and_false, not_false_iff] },
  { simp only [mem_sdiff, mem_insert, one_ne_zero, mem_singleton, eq_self_iff_true, false_or,
      not_true, and_false, not_false_iff]},
  rw [insert_eq, insert_eq, ←union_assoc, ←insert_eq, union_comm, sdiff_union_of_subset this],
  simp only [set.pairwise, mem_coe, mem_map, exists_prop, mem_univ, true_and, forall_exists_index,
    ne.def, rel_embedding.coe_fn_to_embedding, forall_apply_eq_imp_iff', rel_embedding.inj],
  intros x y h,
  exact is_square_sub_of_paley_graph_adj card_not_three_mod_four (f.map_rel_iff.2 (ne.symm h)),
end

-- #lint

lemma card_non_zero_square_non_square {F : Type*} [fintype F] [field F] [decidable_eq F]
  (hF : ring_char F ≠ 2) :
  (univ.filter (λ x : F, x ≠ 0 ∧ is_square x)).card = card F / 2 ∧
  (univ.filter (λ x : F, ¬ is_square x)).card = card F / 2 :=
begin
  have : (univ.filter (λ x : F, ¬ is_square x)) = (univ.filter (λ x : F, x ≠ 0 ∧ ¬ is_square x)),
  { refine filter_congr _,
    simp [not_imp_not] {contextual := tt} },
  rw this,
  have cf := quadratic_char_sum_zero hF,
  simp only [quadratic_char_apply, quadratic_char_fun] at cf,
  rw [sum_ite, sum_const_zero, zero_add, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    mul_neg, mul_one, mul_one, add_neg_eq_zero, nat.cast_inj, filter_filter, filter_filter] at cf,
  rw [←cf, and_self],
  have : (univ.filter (λ x : F, x ≠ 0 ∧ is_square x)) ∪
    (univ.filter (λ x : F, x ≠ 0 ∧ ¬ is_square x)) ∪ {0} = univ,
  { simp only [←filter_or, ←and_or_distrib_left, em, and_true, filter_ne'],
    rw [union_comm, ←insert_eq, insert_erase],
    exact mem_univ _ },
  have h' := congr_arg finset.card this,
  rw [card_disjoint_union, card_disjoint_union, card_singleton, card_univ, ←cf, ←two_mul,
    ←bit0_eq_two_mul, ←bit1] at h',
  { rw [←h', nat.bit1_div_two] },
  { rw finset.disjoint_left,
    simp {contextual := tt} },
  { simp },
end

lemma card_square (F : Type*) [fintype F] [field F] (hF : ring_char F ≠ 2) :
  ((univ : finset F).filter is_square).card = card F / 2 + 1 :=
begin
  rw [←(card_non_zero_square_non_square hF).1],
  simp only [and_comm, ←filter_filter, filter_ne'],
  rw card_erase_add_one,
  simp
end

lemma paley_five_bound : ¬ is_ramsey_valid (zmod 5) ![3, 3] :=
begin
  haveI : fact (nat.prime 5) := ⟨by norm_num⟩,
  classical,
  rw is_ramsey_valid_iff_eq,
  intro h,
  specialize h (paley_labelling (zmod 5)),
  have : ∃ (m : finset (zmod 5)) (c : fin 2),
    (paley_labelling (zmod 5)).monochromatic_of m c ∧ 3 = m.card,
  { simpa only [fin.exists_fin_two] using h },
  have := no_paley_mono_set (by norm_num) this,
  simp only [card_eq_one, ←exists_and_distrib_right, @exists_comm (finset (zmod 5)), exists_eq_left,
    mem_singleton, forall_eq, coe_singleton, set.pairwise_singleton, and_true] at this,
  revert this,
  dec_trivial,
end

lemma paley_seventeen_helper :
  ∀ (a : zmod 17), a ≠ 0 → a ≠ 1 → is_square a → is_square (a - 1) → a = 2 ∨ a = 9 ∨ a = 16 :=
by dec_trivial

lemma paley_seventeen_bound : ¬ is_ramsey_valid (zmod 17) ![4, 4] :=
begin
  haveI : fact (nat.prime 17) := ⟨by norm_num⟩,
  classical,
  rw is_ramsey_valid_iff_eq,
  intro h,
  specialize h (paley_labelling (zmod 17)),
  have : ∃ (m : finset (zmod 17)) (c : fin 2),
    (paley_labelling (zmod 17)).monochromatic_of m c ∧ 4 = m.card,
  { simpa only [fin.exists_fin_two] using h },
  have := no_paley_mono_set (by norm_num) this,
  simp only [card_eq_two, ←exists_and_distrib_right, and_assoc, ne.def, exists_eq_left, mem_insert,
    @exists_comm (finset (zmod 17)), exists_and_distrib_left, mem_singleton, forall_eq_or_imp,
    forall_eq, coe_pair, not_or_distrib, @eq_comm (zmod 17) 0, @eq_comm (zmod 17) 1] at this,
  obtain ⟨a, b, hab, ha₀, hb₀, ha₁, hb₁, ha, hb, ha₁', hb₁', h⟩ := this,
  rw set.pairwise_insert_of_symmetric_of_not_mem at h,
  rotate,
  { intros x y h,
    exact symmetric_is_square (by norm_num) h },
  { exact hab },
  simp only [set.pairwise_singleton, set.mem_singleton_iff, forall_eq, true_and] at h,
  have : a = 2 ∨ a = 9 ∨ a = 16 := paley_seventeen_helper a ha₀ ha₁ ha ha₁',
  have : b = 2 ∨ b = 9 ∨ b = 16 := paley_seventeen_helper b hb₀ hb₁ hb hb₁',
  clear ha₀ ha₁ ha ha₁' hb₀ hb₁ hb hb₁',
  revert h hab,
  revert a b,
  dec_trivial,
end

end paley

lemma diagonal_ramsey_three : diagonal_ramsey 3 = 6 :=
begin
  refine le_antisymm _ _,
  { exact (ramsey_number_two_colour_bound 3 3 (by norm_num)).trans_eq (by simp) },
  rw [←not_lt, nat.lt_succ_iff, ←zmod.card 5, diagonal_ramsey.def, ramsey_number_le_iff],
  exact paley_five_bound
end

lemma ramsey_number_three_four_upper : ramsey_number ![3, 4] ≤ 9 :=
begin
  refine (ramsey_number_two_colour_bound_even 4 6 _ _ _ _ _ _).trans_eq _,
  { norm_num },
  { norm_num },
  { norm_num },
  { rw [nat.succ_sub_succ_eq_sub, tsub_zero, ←diagonal_ramsey, diagonal_ramsey_three] },
  { norm_num },
  { norm_num },
  { norm_num },
end

lemma diagonal_ramsey_four : diagonal_ramsey 4 = 18 :=
begin
  refine le_antisymm _ _,
  { refine (ramsey_number_two_colour_bound 4 4 (by norm_num)).trans _,
    simp only [nat.succ_sub_succ_eq_sub, tsub_zero],
    rw ramsey_number_pair_swap 4,
    linarith [ramsey_number_three_four_upper] },
  rw [←not_lt, nat.lt_succ_iff, ←zmod.card 17, diagonal_ramsey.def, ramsey_number_le_iff],
  exact paley_seventeen_bound
end

lemma ramsey_number_three_four : ramsey_number ![3, 4] = 9 :=
begin
  refine eq_of_le_of_not_lt ramsey_number_three_four_upper _,
  intro h,
  have : diagonal_ramsey 4 ≤ 16,
  { refine (ramsey_number_two_colour_bound 4 4 (by norm_num)).trans _,
    simp only [nat.succ_sub_succ_eq_sub, tsub_zero],
    rw ramsey_number_pair_swap 4,
    linarith only [h] },
  rw diagonal_ramsey_four at this,
  norm_num at this,
end

section

def parts : fin 3 → finset (fin 4 → zmod 2) :=
![{(![1, 1, 0, 0]), (![0, 0, 1, 1]), (![1, 0, 0, 1]), (![1, 1, 1, 0]), (![1, 0, 0, 0])},
  {(![1, 0, 1, 0]), (![0, 1, 0, 1]), (![0, 1, 1, 0]), (![1, 1, 0, 1]), (![0, 1, 0, 0])},
  {(![0, 0, 0, 1]), (![0, 0, 1, 0]), (![0, 1, 1, 1]), (![1, 0, 1, 1]), (![1, 1, 1, 1])}]

lemma parts_property : ∀ i : fin 3, ∀ x y ∈ parts i, x + y ∉ parts i := by dec_trivial.
lemma parts_cover : ∀ i : fin 4 → zmod 2, i ≠ 0 → ∃ j, i ∈ parts j := by dec_trivial.
lemma parts_disjoint :
  ∀ (i : fin 4 → zmod 2) (j : fin 3), i ∈ parts j → ∀ k : fin 3, i ∈ parts k → j = k :=
dec_trivial

lemma parts_get_aux : ∀ i : fin 4 → zmod 2, i ≠ 0 →
  ∃! j, j ∈ (univ : finset (fin 3)) ∧ i ∈ parts j :=
begin
  intros i hi,
  obtain ⟨j, hj⟩ := parts_cover i hi,
  exact ⟨j, ⟨mem_univ _, hj⟩, λ k hk, parts_disjoint _ _ hk.2 _ hj⟩,
end

lemma parts_pair_get_aux : ∀ i j : fin 4 → zmod 2, i ≠ j →
  ∃! k, k ∈ (univ : finset (fin 3)) ∧ i - j ∈ parts k :=
λ i j hij, parts_get_aux _ (sub_ne_zero_of_ne hij)

def parts_pair_get (i j : fin 4 → zmod 2) (hij : i ≠ j) : fin 3 :=
finset.choose _ _ (parts_pair_get_aux i j hij)

lemma parts_pair_get_spec {i j : fin 4 → zmod 2} (hij : i ≠ j) :
  i - j ∈ parts (parts_pair_get i j hij) :=
finset.choose_property _ _ (parts_pair_get_aux i j hij)

lemma parts_pair_get_spec' {i j : fin 4 → zmod 2} {c : fin 3} {hij : i ≠ j}
  (h : parts_pair_get i j hij = c) : i + j ∈ parts c :=
by { rw [←h, ←char_two.sub_eq_add], exact parts_pair_get_spec _ }

lemma parts_pair_get_symm (i j : fin 4 → zmod 2) (hij : i ≠ j) :
  parts_pair_get j i hij.symm = parts_pair_get i j hij :=
begin
  have : i - j = j - i,
  { rw [char_two.sub_eq_add, char_two.sub_eq_add, add_comm] },
  refine parts_disjoint (j - i) _ (parts_pair_get_spec hij.symm) _ _,
  rw ←this,
  exact parts_pair_get_spec hij
end

open top_edge_labelling

def clebsch_colouring : top_edge_labelling (fin 4 → zmod 2) (fin 3) :=
top_edge_labelling.mk parts_pair_get parts_pair_get_symm

lemma clebsch_bound : ¬ is_ramsey_valid (fin 4 → zmod 2) ![3, 3, 3] :=
begin
  rw is_ramsey_valid_iff_eq,
  push_neg,
  refine ⟨clebsch_colouring, _⟩,
  rintro m c hm hc,
  have : m.card = 3,
  { clear hm,
    revert c,
    simp only [fin.forall_fin_succ, fin.forall_fin_two, matrix.cons_val_zero, fin.succ_zero_eq_one',
      matrix.cons_val_one, matrix.head_cons, fin.succ_one_eq_two', and_self, eq_comm, imp_self,
      matrix.cons_vec_bit0_eq_alt0, matrix.cons_vec_append, matrix.empty_vec_append,
      matrix.cons_vec_alt0] },
  clear hc,
  rw card_eq_three at this,
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := this,
  have hxyz : x ∉ ({y, z} : set (fin 4 → zmod 2)), { simp [hxy, hxz] },
  have hyz' : y ∉ ({z} : set (fin 4 → zmod 2)), { simp [hyz] },
  simp only [coe_insert, coe_pair, monochromatic_of_insert hxyz, monochromatic_of_insert hyz',
    set.mem_singleton_iff, set.mem_insert_iff, monochromatic_of_singleton, true_and,
    clebsch_colouring, mk_get] at hm,
  have hyz'' := parts_pair_get_spec' (hm.1 _ rfl),
  have hxy'' := parts_pair_get_spec' (hm.2 _ (or.inl rfl)),
  have hxz'' := parts_pair_get_spec' (hm.2 _ (or.inr rfl)),
  apply parts_property _ _ hxz'' _ hyz'',
  rwa [←char_two.sub_eq_add, add_sub_add_right_eq_sub, char_two.sub_eq_add],
end

end

lemma ramsey_number_three_three_three : ramsey_number ![3, 3, 3] = 17 :=
begin
  refine le_antisymm _ _,
  { refine (ramsey_number_three_colour_bound (nat.le_succ _) (nat.le_succ _)
      (nat.le_succ _)).trans _,
    rw [nat.succ_sub_succ_eq_sub, tsub_zero, ramsey_number_first_swap 3],
    have : ramsey_number ![3, 3, 2] = ramsey_number ![2, 3, 3],
    { have : ![2, 3, 3] ∘ ⇑(fin_rotate 3) = ![3, 3, 2],
      { dec_trivial },
      rw [←this, ramsey_number_equiv] },
    rw [this, ramsey_number_cons_two, ←diagonal_ramsey, diagonal_ramsey_three] },
  rw [←not_lt, nat.lt_succ_iff],
  have := clebsch_bound,
  rw [←ramsey_number_le_iff, fintype.card_fun, zmod.card, fintype.card_fin] at this,
  exact this
end

end simple_graph
