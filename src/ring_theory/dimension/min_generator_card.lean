import ring_theory.noetherian

variables {R M : Type*} [semiring R] [add_comm_monoid M] [module R M]

namespace submodule

noncomputable
def min_generator_card (p : submodule R M) : ℕ :=
⨅ s : { s : set M // s.finite ∧ span R s = p}, s.2.1.to_finset.card

noncomputable
def size (p : submodule R M) : with_top ℕ :=
⨅ s : { s : set M // s.finite ∧ span R s = p}, s.2.1.to_finset.card

lemma size_ne_top_iff {p : submodule R M} :
  p.size ≠ ⊤ ↔ p.fg :=
begin
  simp [size, submodule.fg_def],
end

lemma fg_iff_card_finset_nonempty {p : submodule R M} :
  p.fg ↔ set.nonempty (finset.card '' { s : finset M | span R (s : set M) = p }) :=
set.nonempty_image_iff.symm

lemma fg_iff_size_eq {p : submodule R M} :
  p.fg ↔ p.size = p.min_generator_card :=
begin
  split,
  { intro h,
    haveI : nonempty {s : set M // s.finite ∧ span R s = p},
    { rwa [nonempty_subtype, ← fg_def] },
    exact (with_top.coe_infi _).symm },
  { intro e, rw [← size_ne_top_iff, e], exact with_top.coe_ne_top }
end

alias fg_iff_size_eq ↔ fg.size_eq _

lemma fg.exists_generator_eq_min_generator_card {p : submodule R M} (h : p.fg) :
  ∃ f : fin p.min_generator_card → M, span R (set.range f) = p :=
begin
  obtain ⟨⟨s, h₁, h₂⟩, h₃ : h₁.to_finset.card = _⟩ : p.min_generator_card ∈ _ := nat.Inf_mem _,
  { rw ← h₃,
    refine ⟨subtype.val ∘ h₁.to_finset.equiv_fin.symm, _⟩,
    rw [set.range_comp, set.range_iff_surjective.mpr (equiv.surjective _), set.image_univ,
      subtype.range_val, ← h₂],
    congr' 1,
    ext, exact h₁.mem_to_finset },
  { rwa [set.range_nonempty_iff_nonempty, nonempty_subtype, ← submodule.fg_def] }
end

lemma fg.min_generator_card_le_iff_exists {p : submodule R M} {n : ℕ} :
  p.size ≤ n ↔ ∃ f : fin n → M, span R (set.range f) = p :=
begin
  classical,
  split,
  { intro e,
    have h := size_ne_top_iff.mp (e.trans_lt (with_top.coe_lt_top n)).ne,
    rw [h.size_eq, with_top.coe_le_coe] at e,
    obtain ⟨f, hf⟩ := h.exists_generator_eq_min_generator_card,
    let f' : fin n → M := λ i, if h : i.1 < p.min_generator_card then f (fin.cast_lt i h) else 0,
    use f',
    rw ← hf,
    apply le_antisymm; rw submodule.span_le; rintros _ ⟨x, rfl⟩,
    { dsimp only [f'],
      split_ifs,
      { apply submodule.subset_span, exact set.mem_range_self _ },
      { exact (span R (set.range f)).zero_mem } },
    { apply submodule.subset_span, use fin.cast_le e x, dsimp [f'], rw dif_pos x.is_lt, congr' 1,
      ext, refl } },
  { rintros ⟨f, hf⟩,
    let s : { s : set M // s.finite ∧ span R s = p} :=
      ⟨set.range f, set.finite.intro infer_instance, hf⟩,
    calc p.size
        ≤ s.2.1.to_finset.card : cInf_le (order_bot.bdd_below _) (set.mem_range_self _)
    ... = (finset.univ.image f).card : by { congr' 2, ext, simp }
    ... ≤ n : by { rw with_top.coe_le_coe, convert finset.card_image_le,
                    rw [finset.card_univ, fintype.card_fin] } }
end

noncomputable
def fg.min_generator {p : submodule R M} (h : p.fg) : fin p.min_generator_card → M :=
h.exists_generator_eq_min_generator_card.some

lemma fg.span_min_generator_range {p : submodule R M} (h : p.fg) :
  span R (set.range h.min_generator) = p :=
h.exists_generator_eq_min_generator_card.some_spec

lemma fg.min_generator_mem {p : submodule R M} (h : p.fg) (i) : h.min_generator i ∈ p :=
by { conv_rhs { rw ← h.span_min_generator_range }, exact subset_span (set.mem_range_self i) }

end submodule
