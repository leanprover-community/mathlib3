import topology.metric_space.emetric_space
import analysis.bounded_variation
import topology.metric_space.lipschitz
import analysis.bounded_variation
import topology.metric_space.emetric_space
import topology.path_connected
import data.real.ennreal

noncomputable theory

open_locale nnreal ennreal big_operators

set_option profiler true

theorem half_nonneg {α : Type*} [linear_ordered_semifield α] {a : α} (h : 0 ≤ a) :
  0 ≤ a / 2 :=
begin
  sorry
end

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

namespace unit_interval

/-- The midpoint of the unit interval -/
abbreviation half : unit_interval := ⟨1/2, div_mem zero_le_one zero_le_two one_le_two ⟩

@[simp] lemma symm_half : symm half = half :=
subtype.ext $ sub_half 1

@[simp] lemma symm_inv : symm.involutive := symm_symm
@[simp] lemma symm_inj : symm.injective := symm_inv.injective
@[simp] lemma symm_surj : symm.surjective := symm_inv.surjective
@[simp] lemma symm_anti : antitone symm := λ x y h, (sub_le_sub_iff_left 1).mpr h

@[simp] lemma Icc_zero_one : set.Icc (0 : unit_interval) (1 : unit_interval) = set.univ :=
by { simp only [set.Icc, le_one', nonneg', and_self, set.set_of_true,
                set.univ_inter], }

def expand_bot_half : unit_interval → unit_interval :=
λ t, if h : t ≤ half then ⟨2*t, (mul_pos_mem_iff zero_lt_two).mpr ⟨nonneg',h⟩⟩ else 1

lemma expand_bot_half_monotone : monotone expand_bot_half := λ ⟨x,xl,xr⟩ ⟨y,yl,yr⟩ h,
begin
  dsimp only [expand_bot_half],
  split_ifs with h_1 h_2,
  { simpa only [subtype.mk_le_mk, mul_le_mul_left, zero_lt_bit0, zero_lt_one] using h, },
  { exact le_one' },
  { exfalso, exact h_1 (h.trans h_2), },
  { refl, },
end

lemma expand_bot_half_maps_to : (set.Icc 0 half).maps_to expand_bot_half (set.Icc 0 1) :=
by { simp only [Icc_zero_one], apply set.maps_to_univ, }

lemma expand_bot_half_surj_on : (set.Icc 0 half).surj_on expand_bot_half (set.Icc 0 1) :=
begin
  rintros ⟨x,xl,xr⟩ _,
  dsimp only [expand_bot_half],
  simp only [set.mem_Icc, subtype.mk_le_mk, subtype.coe_mk, set.mem_image, set_coe.exists],
  use x/2,
  refine ⟨⟨half_nonneg xl, (half_le_self xl).trans xr⟩,_⟩,
  sorry

end

def expand_top_half : unit_interval → unit_interval :=
λ t, if h : t ≤ half then 0 else
  ⟨2*↑t - 1, two_mul_sub_one_mem_iff.mpr ⟨le_of_lt (not_le.mp h),t.prop.right⟩⟩

lemma expand_top_half_monotone : monotone expand_top_half := λ ⟨x,xl,xr⟩ ⟨y,yl,yr⟩ h,
begin
  dsimp only [expand_top_half],
  split_ifs,
  { refl, },
  { exact nonneg', },
  { exfalso, exact h_1 (h.trans h_2), },
  { simp only [subtype.coe_mk, subtype.mk_le_mk, sub_le_sub_iff_right, mul_le_mul_left,
               zero_lt_bit0, zero_lt_one], exact h, },
end
lemma expand_top_half_maps_to : (set.Icc half 1).maps_to expand_top_half (set.Icc 0 1) :=
by { simp only [Icc_zero_one], apply set.maps_to_univ, }

lemma expand_top_half_surj_on : (set.Icc half 1).surj_on expand_top_half (set.Icc 0 1) :=
begin sorry end

end unit_interval

namespace path

lemma trans_eq_on_bot_half
  {X : Type*} [topological_space X] {x y z : X} (γ : path x y) (γ' : path y z):
  (set.Icc 0 unit_interval.half).eq_on (γ.trans γ') (γ ∘ unit_interval.expand_bot_half) :=
begin
  rintro ⟨t,_,_⟩ ⟨tl,tr⟩,
  dsimp only [unit_interval.expand_bot_half, path.trans],
  simp only [subtype.mk_le_mk, subtype.coe_mk, coe_mk, function.comp_app] at tl tr ⊢,
  split_ifs with h;
  { rw extend_extends, },
end

lemma trans_eq_on_top_half
  {X : Type*} [topological_space X] {x y z : X} (γ : path x y) (γ' : path y z):
  (set.Icc unit_interval.half 1).eq_on (γ.trans γ') (γ' ∘ unit_interval.expand_top_half) :=
begin
  rintro ⟨t,_,_⟩ ⟨tl,tr⟩,
  dsimp only [unit_interval.expand_top_half, path.trans],
  simp only [subtype.mk_le_mk, one_div, subtype.coe_mk, coe_mk, function.comp_app] at tl tr ⊢,
  split_ifs with h,
  { simp only [le_antisymm h tl, path.source, coe_mk, function.comp_app, subtype.coe_mk, le_refl,
               set.right_mem_Icc, zero_le_one, mul_inv_cancel_of_invertible, extend_extends,
               set.Icc.mk_one, path.target, if_true], },
  { rw extend_extends, },
end

end path

namespace path
variables {E : Type*} [pseudo_emetric_space E]

def length {x y : E} (p : path x y) : ennreal := evariation_on p set.univ

lemma length_eq_evariation_on_extend  {x y : E} (p : path x y) :
  p.length = evariation_on (p.extend) unit_interval :=
begin
  sorry,
end

lemma length_ge (x y : E) (p : path x y) : edist x y ≤ p.length :=
begin
  dsimp only [path.length],
  simp_rw  [←p.source', ←p.target'],
  apply evariation_on.edist_le; trivial,
end

lemma length_refl (x : E) : (path.refl x).length = 0 :=
begin
  apply evariation_on.constant_on,
  simp only [set.image_univ, continuous_map.to_fun_eq_coe, coe_to_continuous_map, refl_range,
             set.subsingleton_singleton],
end

lemma length_symm {x y : E} (p : path x y) : p.symm.length = p.length :=
begin
  apply evariation_on.comp_eq_of_antitone_on,
  { exact unit_interval.symm_anti.antitone_on _, },
  { simp only [set.maps_univ_to, set.mem_univ, forall_const], },
  { rw ←set.surjective_iff_surj_on_univ,
    exact unit_interval.symm_surj, }
end


lemma length_trans {x y z : E} (p : path x y) (q : path y z) :
  (p.trans q).length = p.length + q.length :=
begin
  change
    evariation_on ⇑(p.trans q) set.univ = evariation_on ⇑p set.univ + evariation_on ⇑q set.univ,
  have : set.univ = set.univ ∩ set.Icc (0 : unit_interval) (1 : unit_interval), by
  { simp only [unit_interval.Icc_zero_one, set.univ_inter], },
  rw this, clear this,
  rw ←evariation_on.Icc_add_Icc _ (unit_interval.nonneg' : 0 ≤ unit_interval.half)
                                  (unit_interval.le_one' : unit_interval.half ≤ 1) (set.mem_univ _),
  simp only [set.univ_inter],
  congr' 1,
  { rw ←evariation_on.comp_eq_of_monotone_on (⇑p) (unit_interval.expand_bot_half)
          (unit_interval.expand_bot_half_monotone.monotone_on _)
          (unit_interval.expand_bot_half_maps_to)
          (unit_interval.expand_bot_half_surj_on),
    apply evariation_on.eq_of_eq_on,
    apply path.trans_eq_on_bot_half, },
  { rw ←evariation_on.comp_eq_of_monotone_on (⇑q) (unit_interval.expand_top_half)
          (unit_interval.expand_top_half_monotone.monotone_on _)
          (unit_interval.expand_top_half_maps_to)
          (unit_interval.expand_top_half_surj_on),
    apply evariation_on.eq_of_eq_on,
    apply path.trans_eq_on_top_half, },
end

end path

def path_emetric (E : Type*) [pseudo_emetric_space E] := E

namespace path_emetric

private abbreviation 𝕀 := unit_interval

variables {E : Type*} [pseudo_emetric_space E]

def to_path_emetric : E → path_emetric E := id
def from_path_emetric : path_emetric E → E := id

lemma from_to_path_emetric (x : E) : from_path_emetric (to_path_emetric x) = x := rfl
lemma to_from_path_emetric (x : path_emetric E) : to_path_emetric (from_path_emetric x) = x := rfl

@[protected]
abbreviation of : E → path_emetric E := to_path_emetric
@[protected]
abbreviation fo : path_emetric E → E := from_path_emetric

instance : pseudo_emetric_space (path_emetric E) :=
{ edist := λ x y, infi (λ (p : path (fo x) (fo y)), p.length),
  edist_self := λ x, by
  { refine le_antisymm _ zero_le',
    rw ←(path.length_refl $ fo x),
    refine infi_le _ _, },
  edist_comm := λ x y, by
  { apply le_antisymm;
    { refine le_infi (λ p, _),
      rw ←path.length_symm,
      refine infi_le _ _, }, },
  edist_triangle := λ x y z, by
  { simp_rw [ennreal.infi_add, ennreal.add_infi],
    apply le_infi₂ (λ p q, _),
    rw ←path.length_trans p q,
    exact infi_le _ (p.trans q), } }

lemma from_length_emetric_nonexpanding :
  lipschitz_with 1 (from_path_emetric : path_emetric E → E) :=
begin
  rintro x y,
  simp only [edist, ennreal.coe_one, one_mul, le_infi_iff],
  apply path.length_ge,
end

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
  /-
  apply infi₂_le _ _,
  simp only [function.comp_app, mul_zero, add_zero, mul_one, add_sub_cancel'_right],
  exact ⟨ps, pt, pc.comp (continuous_line_map s t)⟩,
  -/
  sorry,
end

lemma continuous_for_path_metric_of_bounded_variation_of_continuous {f : ℝ → E}
  (fc : continuous_on f 𝕀) (fb : has_bounded_variation_on f 𝕀) :
  continuous_on (of ∘ f) 𝕀 := sorry

lemma sum_for_path_metric_le_evariation_on_of_bounded_variation {f : ℝ → E}
  {s : set ℝ} (hs : ∀ (x z ∈ s) (y : ℝ), x ≤ y → y ≤ z → y ∈ s)
  (fb : has_locally_bounded_variation_on f s) (fc : continuous f)
  (n : ℕ) {u : ℕ → ℝ} (us : ∀ i, u i ∈ s) (um : monotone u) :
  ∑ i in finset.range n, edist ((of ∘ f) (u (i + 1))) ((of ∘ f) (u i)) ≤ evariation_on f s :=
begin
  calc ∑ i in finset.range n, edist ((of ∘ f) (u (i + 1))) ((of ∘ f) (u i))
     ≤ ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ)) : by
  begin
    refine finset.sum_le_sum (λ i hi, _),
    rw edist_comm,
    refine path_emetric.edist_le (um (i.le_succ)) rfl rfl fc,
  end
  ...= ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ) ∩ s) : by
  { congr' 1 with i : 1, congr, symmetry,
    apply set.inter_eq_self_of_subset_left,
    exact λ t ht, hs (u i) (us i) (u i.succ) (us i.succ) t ht.left ht.right, }
  ...≤ evariation_on f s : evariation_on.sum_on_Icc_le f n um (λ i hi, us i)
end

lemma evariation_on_for_path_metric_le_evariation_on_of_bounded_variation {f : ℝ → E}
  {s : set ℝ} (hs : ∀ (x z ∈ s) (y : ℝ), x ≤ y → y ≤ z → y ∈ s)
  (fb : has_locally_bounded_variation_on f s)  (fc : continuous f) :
  evariation_on (of ∘ f) s ≤ evariation_on f s :=
begin
  dsimp only [evariation_on],
  refine supr_le _,
  rintro ⟨n, ⟨u, um, us⟩⟩,
  apply sum_for_path_metric_le_evariation_on_of_bounded_variation hs fb fc n us um,
end

lemma path_metric_idempotent : isometry (of : path_emetric E → path_emetric (path_emetric E)) :=
begin
  rintro x y,
  dsimp only [edist, from_path_emetric, path_emetric.edist],
  apply le_antisymm; simp only [le_infi_iff],
  { rintro f ⟨fx, fy, fc⟩,
    by_cases h : evariation_on f 𝕀 ≠ ⊤,
    { refine le_trans _ (evariation_on_for_path_metric_le_evariation_on_of_bounded_variation (λ x ⟨zx,xo⟩ y ⟨zy,yo⟩ u xu uy, ⟨zx.trans xu, uy.trans yo⟩ ) (has_bounded_variation_on.has_locally_bounded_variation_on h) fc),
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
