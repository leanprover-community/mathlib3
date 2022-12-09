import order.monotone.union
import order.conditionally_complete_lattice.basic

open set

variables {α β : Type*} [linear_order α] [conditionally_complete_linear_order β]
  {f : α → β} {s : set α} {a b : α}

/-- If a function is monotone on a set `s`, then it admits a monotone extension to the whole space
provided `s` has a least element `a` and a greatest element `b`. -/
lemma monotone_on.exists_monotone_extension (h : monotone_on f s) (ha : is_least s a)
  (hb : is_greatest s b) :
  ∃ g : α → β, monotone g ∧ eq_on f g s :=
begin
  /- The extension is defined by `f x = f a` for `x ≤ a`, and `f x` is the supremum of the values
  of `f`  to the left of `x` for `x ≥ a`. -/
  have aleb : a ≤ b := hb.2 ha.1,
  have H : ∀ x ∈ s, f x = Sup (f '' (Icc a x ∩ s)),
  { assume x xs,
    have xmem : x ∈ Icc a x ∩ s := ⟨⟨ha.2 xs, le_rfl⟩, xs⟩,
    have H : ∀ z, z ∈ f '' (Icc a x ∩ s) → z ≤ f x,
    { rintros _ ⟨z, ⟨⟨az, zx⟩, zs⟩, rfl⟩,
      exact h zs xs zx },
    apply le_antisymm,
    { exact le_cSup ⟨f x, H⟩ (mem_image_of_mem _ xmem) },
    { exact cSup_le (nonempty_image_iff.2 ⟨x, xmem⟩) H } },
  let g := λ x, if x ≤ a then f a else Sup (f '' (Icc a x ∩ s)),
  have hfg : eq_on f g s,
  { assume x xs,
    dsimp only [g],
    by_cases hxa : x ≤ a,
    { have : x = a, from le_antisymm hxa (ha.2 xs),
      simp only [if_true, this, le_refl] },
    rw [if_neg hxa],
    exact H x xs },
  have M1 : monotone_on g (Iic a),
  { rintros x (hx : x ≤ a) y (hy : y ≤ a) hxy,
    dsimp only [g],
    simp only [hx, hy, if_true] },
  have g_eq : ∀ x ∈ Ici a, g x = Sup (f '' (Icc a x ∩ s)),
  { rintros x ax,
    dsimp only [g],
    by_cases hxa : x ≤ a,
    { have : x = a := le_antisymm hxa ax,
      simp_rw [hxa, if_true, H a ha.1, this] },
    simp only [hxa, if_false], },
  have M2 : monotone_on g (Ici a),
  { rintros x ax y ay hxy,
    rw [g_eq x ax, g_eq y ay],
    apply cSup_le_cSup,
    { refine ⟨f b, _⟩,
      rintros _ ⟨z, ⟨⟨az, zy⟩, zs⟩, rfl⟩,
      exact h zs hb.1 (hb.2 zs) },
    { exact ⟨f a, mem_image_of_mem _ ⟨⟨le_rfl, ax⟩, ha.1⟩⟩ },
    { apply image_subset,
      apply inter_subset_inter_left,
      exact Icc_subset_Icc le_rfl hxy } },
  exact ⟨g, M1.Iic_union_Ici M2, hfg⟩,
end

/-- If a function is antitone on a set `s`, then it admits an antitone extension to the whole space
provided `s` has a least element `a` and a greatest element `b`. -/
lemma antitone_on.exists_antitone_extension (h : antitone_on f s) (ha : is_least s a)
  (hb : is_greatest s b) :
  ∃ g : α → β, antitone g ∧ eq_on f g s :=
h.dual_right.exists_monotone_extension ha hb
