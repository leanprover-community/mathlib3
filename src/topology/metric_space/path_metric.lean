import topology.metric_space.emetric_space
import analysis.bounded_variation
import topology.metric_space.lipschitz

noncomputable theory

open_locale nnreal ennreal big_operators

section real_line_map

variables (a b : ℝ)

lemma continuous_line_map : continuous (λ x, a + (b-a)*x) := sorry
lemma surj_on_unit_interval_line_map_of_le (h : a ≤ b) :
  set.surj_on (λ x, a + (b-a)*x) unit_interval (set.Icc a b) := sorry
lemma maps_to_unit_interval_line_map_of_le (h : a ≤ b) :
  set.maps_to (λ x, a + (b-a)*x) unit_interval (set.Icc a b) := sorry
lemma monotone_line_map_of_le (h : a ≤ b) :
  monotone (λ x, a + (b-a)*x) := sorry

lemma surj_on_unit_interval_line_map_of_ge (h : b ≤ a) :
  set.surj_on (λ x, a + (b-a)*x) unit_interval (set.Icc b a) := sorry
lemma maps_to_unit_interval_line_map_of_ge (h : b ≤ a) :
  set.maps_to (λ x, a + (b-a)*x) unit_interval (set.Icc b a) := sorry
lemma antitone_line_map_of_ge (h : b ≤ a) :
  antitone (λ x, a + (b-a)*x) := sorry

end real_line_map

namespace evariation_on

lemma sum_on_Icc_le {α E : Type*} [linear_order α] [pseudo_emetric_space E]
  (f : α → E) {s : set α} (n : ℕ) {u : ℕ → α} (hu : monotone u) (us : ∀ i, i ≤ n → u i ∈ s) :
  ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ) ∩ s) ≤ evariation_on f s :=
begin
  revert s,
  induction n,
  { rintro s us, simp only [finset.range_zero, finset.sum_empty, zero_le'], },
  { rintro s us,
    specialize @n_ih {x | x ∈ s ∧ x ≤ u n_n} (λ i hi,  ⟨us i (hi.trans (nat.le_succ _)), hu hi⟩),
    rw finset.sum_range_succ,
    have : ∑ (i : ℕ) in finset.range n_n, evariation_on f (set.Icc (u i) (u i.succ) ∩
                                                           {x : α | x ∈ s ∧ x ≤ u n_n})
         = ∑ (i : ℕ) in finset.range n_n, evariation_on f (set.Icc (u i) (u i.succ) ∩ s), by
    { refine finset.sum_congr rfl (λ i hi, _),
      congr' 1 with x : 1,
      refine ⟨λ h, ⟨h.1,h.2.1⟩, λ h, ⟨h.1, ⟨h.2, h.1.2.trans (hu (nat.succ_le_of_lt _))⟩⟩⟩,
      rw finset.mem_range at hi,
      exact hi, },
    rw this at n_ih,
    refine (add_le_add_right n_ih _).trans ((add_le_union f _).trans (mono f _)),
    { rintros x ⟨_,hx⟩ y ⟨⟨hy,_⟩,_⟩, exact hx.trans hy, },
    { rintros x (⟨h,_⟩|⟨_,h⟩); exact h, }, },
end

end evariation_on

section path_emetric

universe u

private abbreviation 𝕀 := unit_interval

def path_emetric (E : Type u) [pseudo_emetric_space E] : Type u := E

variables {E : Type u} [pseudo_emetric_space E]

def to_path_emetric : E → path_emetric E := id
def from_path_emetric : path_emetric E → E := id
abbreviation of : E → path_emetric E := to_path_emetric
abbreviation fo : path_emetric E → E := from_path_emetric

lemma from_to_path_emetric (x : E) : from_path_emetric (to_path_emetric x) = x := rfl
lemma to_from_path_emetric (x : path_emetric E) : to_path_emetric (from_path_emetric x) = x := rfl

def path_emetric.edist (x y : E) : ℝ≥0∞ :=
  ⨅ (p : ℝ → E) (h : p 0 = x ∧ p 1 = y ∧ continuous_on p 𝕀), evariation_on p 𝕀

instance : pseudo_emetric_space (path_emetric E) :=
{ edist := λ x y, path_emetric.edist (from_path_emetric x) (from_path_emetric y),
  edist_self := λ x, by
  { dsimp [path_emetric.edist],
    refine le_antisymm _ zero_le',
    transitivity' (evariation_on (λ (t : ℝ), fo x) 𝕀),
    { refine infi₂_le (λ t : ℝ, fo x) ⟨rfl,rfl, continuous_on_const⟩,  },
    { refine eq.le (evariation_on.constant_on _),
      simp only [set.nonempty.image_const, set.nonempty_Icc, zero_le_one, set.subsingleton_singleton], }, },
  edist_comm := λ x y, by
  { apply le_antisymm;
    { dsimp [path_emetric.edist],
      apply le_infi₂ _,
      rintro p ⟨px,py,pc⟩,
      rw ←evariation_on.comp_eq_of_antitone_on p (λ u, 1 + (0-1)*u),
      apply infi₂_le _ _,
      split,
      { simp only [zero_sub, neg_mul, one_mul, function.comp_app, neg_zero, add_zero, py], },
      split,
      { simp only [px, zero_sub, neg_mul, one_mul, function.comp_app, eq_self_iff_true, true_and,
                   ←sub_eq_add_neg, sub_self], },
      apply pc.comp (continuous_line_map 1 0).continuous_on,
      exact maps_to_unit_interval_line_map_of_ge 1 0 (zero_le_one),
      exact (antitone_line_map_of_ge 1 0 (zero_le_one)).antitone_on _,
      exact maps_to_unit_interval_line_map_of_ge 1 0 (zero_le_one),
      exact surj_on_unit_interval_line_map_of_ge 1 0 (zero_le_one), }, },
  edist_triangle := λ x y z, by
  { dsimp only [path_emetric.edist],
    simp_rw [ennreal.infi_add, ennreal.add_infi],
    refine le_infi (λ p, le_infi (λ hp, le_infi (λ q, le_infi (λ hq, _)))),
    obtain ⟨px,py,pc⟩ := hp,
    obtain ⟨qy,qz,qc⟩ := hq,
    have : evariation_on p 𝕀 + evariation_on q 𝕀 =
           evariation_on (λ t, if t ≤ 1/2 then p (2 * t) else q (2 * t - 1)) 𝕀, by
    { sorry, },
    rw this, clear this,
    refine infi₂_le _ _,
    have : ¬ 1 ≤ 1/2, by sorry,
    simp only [one_div, inv_nonneg, zero_le_bit0, zero_le_one, mul_zero, if_true, mul_one],
    refine ⟨px,_,_⟩, sorry, sorry,
  } }

lemma path_emetric.edist_le {x y : E} {p : ℝ → E} {s t : ℝ} (st : s ≤ t)
  (ps : p s = x) (pt : p t = y) (pc : continuous_on p (set.Icc s t)) :
  edist (of x) (of y) ≤ evariation_on p (set.Icc s t) :=
begin
  have : evariation_on p (set.Icc s t) = (evariation_on (p ∘ (λ u, s + (t-s)*u)) 𝕀), by
  { symmetry, apply evariation_on.comp_eq_of_monotone_on,
    exact (monotone_line_map_of_le _ _ st).monotone_on _,
    exact (maps_to_unit_interval_line_map_of_le _ _ st),
    exact (surj_on_unit_interval_line_map_of_le _ _ st), },
  rw this,
  apply infi₂_le _ _,
  simp only [function.comp_app, mul_zero, add_zero, mul_one, add_sub_cancel'_right],
  exact ⟨ps, pt, pc.comp (continuous_line_map s t).continuous_on
                         (maps_to_unit_interval_line_map_of_le s t st)⟩,
end

lemma from_path_emetric_nonexpanding :
  lipschitz_with 1 (from_path_emetric : path_emetric E → E) :=
begin
  rintro x y,
  dsimp only [edist, path_emetric.edist],
  simp only [ennreal.coe_one, one_mul, le_infi₂_iff],
  rintro p ⟨px, py, pc⟩,
  rw [←px, ←py],
  exact evariation_on.edist_le p unit_interval.zero_mem unit_interval.one_mem,
end

lemma continuous_for_path_metric_of_bounded_variation_of_continuous {f : ℝ → E}
  (fc : continuous_on f 𝕀) (fb : has_bounded_variation_on f 𝕀) :
  continuous_on (of ∘ f) 𝕀 := sorry

lemma sum_for_path_metric_le_evariation_on_of_bounded_variation
  --{α : Type*} [linear_order α]
{f : ℝ → E} --{s : set ℝ}
  (fb : has_bounded_variation_on f 𝕀) (fc : continuous_on f 𝕀)
  (n : ℕ) {u : ℕ → ℝ} (us : ∀ i, u i ∈ 𝕀) (um : monotone u) :
  ∑ i in finset.range n, edist ((of ∘ f) (u (i + 1))) ((of ∘ f) (u i)) ≤ evariation_on f 𝕀 :=
begin
  calc ∑ i in finset.range n, edist ((of ∘ f) (u (i + 1))) ((of ∘ f) (u i))
     ≤ ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ)) : by
  begin
    refine finset.sum_le_sum (λ i hi, _),
    rw edist_comm,
    apply path_emetric.edist_le (um (i.le_succ)) rfl rfl
            (continuous_on.mono fc (set.Icc_subset_Icc (us i).left (us i.succ).right)),
  end
  ...= ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ) ∩ 𝕀) : by
  { congr' 1 with i : 1, congr, symmetry,
    apply set.inter_eq_self_of_subset_left,
    apply set.Icc_subset_Icc (us i).left (us i.succ).right, }
  ...≤ evariation_on f 𝕀 : evariation_on.sum_on_Icc_le f n um (λ i hi, us i)
end

lemma evariation_on_for_path_metric_le_evariation_on_of_bounded_variation {f : ℝ → E}
  (fb : has_bounded_variation_on f 𝕀)  (fc : continuous_on f 𝕀) :
  evariation_on (of ∘ f) 𝕀 ≤ evariation_on f 𝕀 :=
begin
  dsimp only [evariation_on],
  refine supr_le _,
  rintro ⟨n, ⟨u, um, us⟩⟩,
  apply sum_for_path_metric_le_evariation_on_of_bounded_variation fb fc n us um,
end

lemma path_metric_idempotent : isometry (of : path_emetric E → path_emetric (path_emetric E)) :=
begin
  rintro x y,
  dsimp only [edist, from_path_emetric, path_emetric.edist],
  apply le_antisymm; simp only [le_infi_iff],
  { rintro f ⟨fx, fy, fc⟩,
    by_cases h : evariation_on f 𝕀 ≠ ∞,
    { refine le_trans _ (evariation_on_for_path_metric_le_evariation_on_of_bounded_variation h fc),
      refine infi₂_le (of ∘ f) ⟨congr_arg of fx, congr_arg of fy, _⟩,
      exact continuous_for_path_metric_of_bounded_variation_of_continuous fc h, },
    { rw not_not.mp h, exact le_top, }, },
  { rintro f' ⟨f'x, f'y, f'c⟩,
    have : evariation_on f' 𝕀 = (1 : ennreal) * (evariation_on f' 𝕀), by rw [one_mul], rw this,
    refine le_trans _ (((from_path_emetric_nonexpanding).lipschitz_on_with set.univ).comp_evariation_on_le (set.maps_to_univ _ _)),
    refine infi₂_le (fo ∘ f') ⟨congr_arg fo f'x, congr_arg fo f'y, _⟩,
    exact from_path_emetric_nonexpanding.continuous.continuous_on.comp f'c (set.maps_to_univ _ 𝕀), }
end


end path_emetric
