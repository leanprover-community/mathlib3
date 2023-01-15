import topology.metric_space.emetric_space
import analysis.bounded_variation
import topology.path_connected

noncomputable theory

open_locale nnreal ennreal big_operators

private abbreviation 𝕀 := unit_interval

lemma half_nonneg {α : Type*} [linear_ordered_semifield α] {a : α} (h : 0 ≤ a) :
  0 ≤ a / 2 := sorry

lemma emetric.tendsto_within_nhds_ennreal_zero
  {α : Type*} [pseudo_emetric_space α] {s : set α} {f : α → ℝ≥0∞} {a : α} :
  filter.tendsto f (nhds_within a s) (nhds 0) ↔
    ∀ (ε : ennreal), ε > 0 →
      (∃ (δ : ennreal) (H : δ > 0), ∀ {x : α}, x ∈ s → has_edist.edist x a < δ → f x < ε) :=
begin
  rw ennreal.tendsto_nhds_zero,
  dsimp only [filter.eventually],
  simp_rw [emetric.mem_nhds_within_iff, set.inter_comm],
  split,
  { rintro h ε hε,
    obtain ⟨ε',ε'pos,ε'ε⟩ := exists_between hε,
    obtain ⟨δ,hδ,h⟩ := h ε' ε'pos,
    exact ⟨δ,hδ,λ x xs dxa, lt_of_le_of_lt (h ⟨xs,dxa⟩) ε'ε⟩, },
  { rintro h ε hε,
    obtain ⟨δ,hδ,h⟩ := h ε hε,
    exact ⟨δ,hδ, λ x hx, (h hx.1 hx.2).le⟩, }
end

lemma emetric.continuous_within_at_iff
  {α β : Type*} [pseudo_emetric_space α] [pseudo_emetric_space β] {f : α → β} {a : α} {s : set α} :
  continuous_within_at f s a ↔
  ∀ ε > 0, ∃ δ > 0, ∀{x:α}, x ∈ s → edist x a < δ → edist (f x) (f a) < ε :=
by rw [continuous_within_at, emetric.tendsto_nhds_within_nhds]

lemma emetric.continuous_on_iff
  {α β : Type*} [pseudo_emetric_space α] [pseudo_emetric_space β] {f : α → β} {s : set α} :
  continuous_on f s ↔
  ∀ (b ∈ s) (ε > 0), ∃ δ > 0, ∀a ∈ s, edist a b < δ → edist (f a) (f b) < ε :=
by simp [continuous_on, emetric.continuous_within_at_iff]

section real_line_map

variables (a b : ℝ)

lemma continuous_line_map : continuous (λ x, a + (b-a)*x) := sorry

variables {a b} {c d : ℝ}

lemma surj_on_Icc_line_map_of_le (h : a ≤ b) (h' : c ≤ d) :
  set.surj_on (λ x, a + (b-a)*x) (set.Icc c d) (set.Icc (a + (b-a)*c) (a + (b-a)*d)) :=
begin
  rintro x ⟨xl,xr⟩,
  by_cases ab : a = b,
  { cases ab,
    simp only [sub_self, zero_mul, add_zero, set.mem_image, set.mem_Icc, exists_and_distrib_right,
               le_refl, eq_self_iff_true] at *,
    cases le_antisymm xl xr,
    exact ⟨⟨c,le_rfl,h'⟩,rfl⟩, },
  { have := lt_iff_le_and_ne.mpr ⟨h,ab⟩,
    rw ←sub_pos at this,
    replace ab := sub_ne_zero.mpr (ne.symm ab),
    use (x-a)/(b-a),
    simp only [set.mem_Icc],
    rw [le_div_iff, div_le_iff, add_comm, le_sub_iff_add_le, sub_le_iff_le_add, mul_comm (b-a),
        div_mul_cancel, sub_add, sub_self, sub_zero, mul_comm c, add_comm _ a, add_comm _ a,
        mul_comm d _],
    exact ⟨⟨xl,xr⟩,rfl⟩, assumption, assumption, assumption, },
end
lemma maps_to_Icc_line_map_of_le (h : a ≤ b) (h' : c ≤ d) :
  set.maps_to (λ x, a + (b-a)*x) (set.Icc c d) (set.Icc (a + (b-a)*c) (a + (b-a)*d)) :=
begin
  rintro x ⟨xl,xr⟩,
  simp only [set.mem_Icc, add_le_add_iff_left],
  exact ⟨mul_le_mul_of_nonneg_left xl (sub_nonneg.mpr h),
         mul_le_mul_of_nonneg_left xr (sub_nonneg.mpr h)⟩,
end

lemma monotone_line_map_of_le (h : a ≤ b) :
  monotone (λ x, a + (b-a)*x) := λ x y xy,
by { simp only [add_le_add_iff_left], exact mul_le_mul_of_nonneg_left xy (sub_nonneg.mpr h), }

lemma surj_on_unit_interval_line_map_of_le (h : a ≤ b) :
  set.surj_on (λ x, a + (b-a)*x) unit_interval (set.Icc a b) :=
begin
  convert surj_on_Icc_line_map_of_le h (zero_le_one);
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel'_right],
end
lemma maps_to_unit_interval_line_map_of_le (h : a ≤ b) :
  set.maps_to (λ x, a + (b-a)*x) unit_interval (set.Icc a b) :=
begin
  convert maps_to_Icc_line_map_of_le h (zero_le_one);
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel'_right],
end

lemma surj_on_unit_interval_line_map_of_ge (h : b ≤ a) (h' : c ≤ d):
  set.surj_on (λ x, a + (b-a)*x) (set.Icc c d) (set.Icc (a + (b-a)*d) (a + (b-a)*c)) := sorry
lemma maps_to_unit_interval_line_map_of_ge (h : b ≤ a) (h' : c ≤ d):
  set.maps_to (λ x, a + (b-a)*x) (set.Icc c d) (set.Icc (a + (b-a)*d) (a + (b-a)*c)) := sorry
lemma antitone_line_map_of_ge (h : b ≤ a) :
  antitone (λ x, a + (b-a)*x) := sorry

end real_line_map

namespace unit_interval

lemma half_mem : (1:ℝ) / 2 ∈ unit_interval := div_mem zero_le_one zero_le_two one_le_two

/-- The midpoint of the unit interval -/
abbreviation half : unit_interval := ⟨_, half_mem⟩

end unit_interval

namespace path

lemma extend_symm
  {X : Type*} [topological_space X] {x y : X} (γ : path x y) :
  γ.symm.extend = γ.extend ∘ (λ x, 1 - x) :=
begin
  ext t,
  by_cases ht : t ≤ 0,
  { have : 1 ≤ 1 - t, by { simp only [ht, le_sub_self_iff], },
    simp [path.extend_of_le_zero (γ.symm) ht, function.comp_app, path.extend_of_one_le γ this], },
  { by_cases ht' : 1 ≤ t,
    { have : 1 - t ≤ 0, by { simp only [ht', sub_nonpos], },
      simp [path.extend_of_one_le (γ.symm) ht', function.comp_app, path.extend_of_le_zero γ this], },
    { simp only [not_le] at ht ht',
      simp only [path.extend_extends γ.symm ⟨ht.le,ht'.le⟩, symm_apply, function.comp_app,
                 unit_interval.symm, subtype.coe_mk,
                 path.extend_extends γ (unit_interval.mem_iff_one_sub_mem.mp ⟨ht.le,ht'.le⟩)], }, },
end

lemma extend_trans_on_bot_half
  {X : Type*} [topological_space X] {x y z : X} (γ : path x y) (γ' : path y z) :
  (set.Icc (0:ℝ) ((1:ℝ)/2)).eq_on (γ.trans γ').extend (γ.extend ∘ (λ t, 2*t)) := sorry

lemma extend_trans_on_top_half
  {X : Type*} [topological_space X] {x y z : X} (γ : path x y) (γ' : path y z) :
  (set.Icc ((1:ℝ)/2) 1).eq_on (γ.trans γ').extend (γ'.extend ∘ (λ t, 2*t - 1)) := sorry

/- This is surely somewhere since it's needed for functoriality of the fundamental group -/
def comp
  {X : Type*} [topological_space X] {x y : X} (γ : path x y)
  {Y : Type*} [topological_space Y] (φ : X → Y) (φc : continuous φ ) : path (φ x) (φ y) := sorry

lemma extend_comp
  {X : Type*} [topological_space X] {x y : X} (γ : path x y)
  {Y : Type*} [topological_space Y] (φ : X → Y) (φc : continuous φ ) :
  (γ.comp φ φc).extend = φ ∘ γ.extend := sorry

-- Maybe the scaling+translating should be done separately?
lemma of_continuous_on
  {X : Type*} [topological_space X] {x y : X} {s t : ℝ} (st : s ≤ t) {f : ℝ → X}
  (fsx : f s = x) (fty : f t = y)(fc : continuous_on f (set.Icc s t)) : path x y :=
{ to_fun := f ∘ (λ (u : ℝ), s + (t-s)*u) ∘ (coe : 𝕀 → ℝ),
  continuous_to_fun := sorry,
  source' := sorry,
  target' := sorry }

lemma eq_on_extend_of_continuous_on_self
  {X : Type*} [topological_space X] {x y : X} {s t : ℝ} (st : s ≤ t) {f : ℝ → X}
  (fsx : f s = x) (fty : f t = y) (fc : continuous_on f (set.Icc s t)) :
  𝕀.eq_on (path.of_continuous_on st fsx fty fc).extend (f ∘ (λ (u : ℝ), s + (t-s)*u)) := sorry

end path

namespace path
variables {E : Type*} [pseudo_emetric_space E]

@[reducible]
def length {x y : E} (p : path x y) : ennreal := evariation_on p.extend 𝕀

lemma length_ge (x y : E) (p : path x y) : edist x y ≤ p.length :=
begin
  dsimp only [path.length],
  simp_rw  [←p.extend_one, ←p.extend_zero],
  apply evariation_on.edist_le _ unit_interval.zero_mem unit_interval.one_mem,
end

lemma length_refl (x : E) : (path.refl x).length = 0 :=
begin
  apply evariation_on.constant_on,
  simp only [refl_extend, set.nonempty.image_const, set.nonempty_Icc, zero_le_one,
             set.subsingleton_singleton],
end

lemma length_symm {x y : E} (p : path x y) : p.symm.length = p.length :=
begin
  dsimp [path.length],
  rw path.extend_symm,
  apply evariation_on.comp_eq_of_antitone_on,
  { rintro s hs t ht st, simp only [st, sub_le_sub_iff_left], },
  { rintro s hs, rw ←unit_interval.mem_iff_one_sub_mem, exact hs, },
  { rintro s hs, refine ⟨1-s,_,_⟩, rw ←unit_interval.mem_iff_one_sub_mem, exact hs, simp, },
end

lemma length_trans {x y z : E} (p : path x y) (q : path y z) :
  (p.trans q).length = p.length + q.length :=
begin
  dsimp only [path.length],
  nth_rewrite_lhs 0 ←set.inter_self 𝕀,
  rw ←evariation_on.Icc_add_Icc (p.trans q).extend
    unit_interval.half_mem.left unit_interval.half_mem.right unit_interval.half_mem,
  congr' 1,
  { rw set.inter_eq_self_of_subset_right (set.Icc_subset_Icc_right (unit_interval.half_mem.right)),
    rw ←evariation_on.comp_eq_of_monotone_on (p.extend) (λ (t : ℝ), 0 + (2 - 0)*t),
    { apply evariation_on.eq_of_eq_on,
      simp only [tsub_zero, zero_add, path.extend_trans_on_bot_half], },
    { exact (monotone_line_map_of_le zero_le_two).monotone_on _, },
    { convert maps_to_Icc_line_map_of_le zero_le_two (half_nonneg zero_le_one),
      simp only [tsub_zero, mul_zero, one_div, mul_inv_cancel_of_invertible, zero_add], },
    { convert surj_on_Icc_line_map_of_le zero_le_two (half_nonneg zero_le_one),
      simp only [tsub_zero, mul_zero, one_div, mul_inv_cancel_of_invertible, zero_add], }, },
  { rw set.inter_eq_self_of_subset_right (set.Icc_subset_Icc_left (unit_interval.half_mem.left)),
    rw ←evariation_on.comp_eq_of_monotone_on (q.extend) (λ (t : ℝ), -1 + (1 -(-1))*t),
    { apply evariation_on.eq_of_eq_on,
      simp only [one_add_one_eq_two, sub_neg_eq_add, add_comm (-(1:ℝ))],
      apply path.extend_trans_on_top_half, },
    { exact (monotone_line_map_of_le $ by simp only [neg_le_self_iff, zero_le_one]).monotone_on _, },
    { convert maps_to_Icc_line_map_of_le (by simp only [neg_le_self_iff, zero_le_one] : -(1:ℝ) ≤ 1) (half_le_self zero_le_one),
      simp only [sub_neg_eq_add, mul_one, ←one_add_one_eq_two, ←sub_eq_neg_add, one_div,
                 mul_inv_cancel, ne.def, add_self_eq_zero, one_ne_zero, not_false_iff, sub_self,
                 add_tsub_cancel_left], },
    { convert surj_on_Icc_line_map_of_le (by simp only [neg_le_self_iff, zero_le_one] : -(1:ℝ) ≤ 1) (half_le_self zero_le_one),
      simp only [sub_neg_eq_add, mul_one, ←one_add_one_eq_two, ←sub_eq_neg_add, one_div,
                 mul_inv_cancel, ne.def, add_self_eq_zero, one_ne_zero, not_false_iff, sub_self,
                 add_tsub_cancel_left], }, },
end

end path
/-
def path_emetric (E : Type*) [pseudo_emetric_space E] := E

namespace path_emetric

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

lemma edist_le {x y : E} {p : ℝ → E} {s t : ℝ} (st : s ≤ t)
  (ps : p s = x) (pt : p t = y) (pc : continuous_on p (set.Icc s t)) :
  edist (of x) (of y) ≤ evariation_on p (set.Icc s t) :=
begin
  have : evariation_on p (set.Icc s t) = (evariation_on (p ∘ (λ u, s + (t-s)*u)) 𝕀), by
  { symmetry, apply evariation_on.comp_eq_of_monotone_on,
    exacts [(monotone_line_map_of_le st).monotone_on _,
            maps_to_unit_interval_line_map_of_le st,
            surj_on_unit_interval_line_map_of_le st], },
  rw [this, ←evariation_on.eq_of_eq_on (path.eq_on_extend_of_continuous_on_self st ps pt pc)],
  exact infi_le (λ p, evariation_on p.extend 𝕀) (path.of_continuous_on st ps pt pc),
end

theorem continuous_right_self_evariation' {f : ℝ → E} {a b : ℝ} (ab : a < b)
  (fb : has_locally_bounded_variation_on f (set.Ico a b))
  (hcont : continuous_within_at f (set.Ico a b) a) /- f is right continuous at a -/ :
  filter.tendsto (λ (x : ℝ), evariation_on f (set.Icc a x))
    (nhds_within a (set.Ici a)) (nhds 0) :=
begin
  sorry,
end

theorem continuous_right_self_evariation {f : ℝ → E}
  {s : set ℝ} (hs : ∀ ⦃x⦄ (xs : x∈s) ⦃z⦄ (zs : z∈s), set.Icc x z ⊆ s)
  (fb : has_locally_bounded_variation_on f s) {a : ℝ} (as : a ∈ s)
  (hcont : continuous_within_at f (s ∩ set.Ici a) a) /- f is right continuous at a -/ :
  filter.tendsto (λ (b : ℝ), evariation_on f (set.Icc a b))
    (nhds_within a (s ∩ set.Ici a)) (nhds 0) :=
begin
  rw emetric.tendsto_within_nhds_ennreal_zero,
  by_cases h : ∃ b, b ∈ s ∧ b > a,
  { obtain ⟨b,bs,ab⟩ := h,
    let := continuous_right_self_evariation' ab
      (fb.mono (set.Ico_subset_Icc_self.trans (hs as bs)))
      (hcont.mono (set.subset_inter (set.Ico_subset_Icc_self.trans (hs as bs))
                                    (set.Ico_subset_Ici_self))),
    rw emetric.tendsto_within_nhds_ennreal_zero at this,
    rintro ε hε,
    obtain ⟨δ,hδ,h⟩ := this ε hε,
    exact ⟨δ,hδ,λ x hx dxa, h hx.2 dxa⟩, },
  { push_neg at h,
    rintro ε hε,
    refine ⟨1,zero_lt_one, λ x hx dxa, _⟩,
    obtain ⟨xs,xa⟩ := hx,
    cases le_antisymm (h x xs) xa,
    rw evariation_on.subsingleton _
      (by simp only [set.Icc_self, set.subsingleton_singleton] : (set.Icc a a).subsingleton),
    exact hε, },
end

theorem continuous_left_self_evariation' {f : ℝ → E} {a b : ℝ}  (ba : b < a)
  (fb : has_locally_bounded_variation_on f (set.Ioc b a))
  (hcont : continuous_within_at f (set.Ioc b a) a) /- f is left continuous at a -/ :
  filter.tendsto (λ (x : ℝ), evariation_on f (set.Icc x a))
    (nhds_within a (set.Iic a)) (nhds 0) := sorry

theorem continuous_left_self_evariation {f : ℝ → E}
  {s : set ℝ} (hs : ∀ ⦃x⦄ (xs : x∈s) ⦃z⦄ (zs : z∈s), set.Icc x z ⊆ s)
  (fb : has_locally_bounded_variation_on f s) {a : ℝ} (as : a ∈ s)
  (hcont : continuous_within_at f (s ∩ set.Iic a) a) /- f is left continuous at a -/ :
  filter.tendsto (λ (b : ℝ), evariation_on f (set.Icc b a))
    (nhds_within a (s ∩ set.Iic a)) (nhds 0) := sorry

lemma continuous_for_path_metric_of_bounded_variation_of_continuous {f : ℝ → E}
  {s : set ℝ} (hs : ∀ ⦃x⦄ (xs : x∈s) ⦃z⦄ (zs : z∈s), set.Icc x z ⊆ s)
  (fc : continuous_on f s) (fb : has_locally_bounded_variation_on f s) :
  continuous_on (of ∘ f) s :=
begin
  rw emetric.continuous_on_iff,
  rintros b bs ε hε,
  let hleft := continuous_right_self_evariation hs fb bs
                 ((fc.continuous_within_at bs).mono (set.inter_subset_left _ _)),
  rw emetric.tendsto_within_nhds_ennreal_zero at hleft,
  obtain ⟨δl,hδl,hl⟩ := hleft ε hε,
  let hright := continuous_left_self_evariation hs fb bs
                 ((fc.continuous_within_at bs).mono (set.inter_subset_left _ _)),
  rw emetric.tendsto_within_nhds_ennreal_zero at hright,
  obtain ⟨δr,hδr,hr⟩ := hright ε hε,
  refine ⟨δl ⊓ δr, lt_inf_iff.mpr ⟨hδl.lt,hδr.lt⟩, λ a as hab, _⟩,
  simp only [function.comp_app],
  rcases lt_trichotomy a b with (ab|rfl|ba),
  { apply lt_of_le_of_lt,
    apply edist_le ab.le rfl rfl (fc.mono (hs as bs)),
    apply hr ⟨as,ab.le⟩ (lt_of_lt_of_le hab inf_le_right), },
  { simp only [edist_self], exact hε, },
  { rw edist_comm,
    apply lt_of_le_of_lt,
    apply edist_le ba.le rfl rfl (fc.mono (hs bs as)),
    refine hl ⟨as,ba.le⟩ (lt_of_lt_of_le hab inf_le_left), },
end

lemma sum_for_path_metric_le_evariation_on_of_bounded_variation {f : ℝ → E}
  {s : set ℝ} (hs : ∀ ⦃x⦄ (xs : x∈s) ⦃z⦄ (zs : z∈s), set.Icc x z ⊆ s)
  (fb : has_locally_bounded_variation_on f s) (fc : continuous_on f s)
  (n : ℕ) {u : ℕ → ℝ} (us : ∀ i, u i ∈ s) (um : monotone u) :
  ∑ i in finset.range n, edist ((of ∘ f) (u (i + 1))) ((of ∘ f) (u i)) ≤ evariation_on f s :=
begin
  calc ∑ i in finset.range n, edist ((of ∘ f) (u (i + 1))) ((of ∘ f) (u i))
     ≤ ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ)) : by
  begin
    refine finset.sum_le_sum (λ i hi, _),
    rw edist_comm,
    refine edist_le (um (i.le_succ)) rfl rfl (fc.mono $ hs (us i) (us i.succ)),
  end
  ...= ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ) ∩ s) : by
  { congr' 1 with i : 1, congr, symmetry,
    apply set.inter_eq_self_of_subset_left (hs (us i) (us i.succ)), }
  ...≤ evariation_on f s : evariation_on.sum_on_Icc_le f n um (λ i hi, us i)
end

lemma evariation_on_for_path_metric_le_evariation_on_of_bounded_variation {f : ℝ → E}
  {s : set ℝ} (hs : ∀ ⦃x⦄ (xs : x∈s) ⦃z⦄ (zs : z∈s), set.Icc x z ⊆ s)
  (fb : has_locally_bounded_variation_on f s)  (fc : continuous_on f s) :
  evariation_on (of ∘ f) s ≤ evariation_on f s :=
begin
  refine supr_le _,
  rintro ⟨n, ⟨u, um, us⟩⟩,
  apply sum_for_path_metric_le_evariation_on_of_bounded_variation hs fb fc n us um,
end

lemma path_metric_idempotent : isometry (of : path_emetric E → path_emetric (path_emetric E)) :=
begin
  rintro x y,
  dsimp only [edist, from_path_emetric, path.length],
  apply le_antisymm; simp only [le_infi_iff],
  { rintro p,
    by_cases h : evariation_on p.extend 𝕀 ≠ ⊤,
    { have ofpx : (of ∘ p.extend) 0 = of x.fo, by
        simp only [function.comp_app, set.left_mem_Icc, zero_le_one,
                   path.extend_extends, set.Icc.mk_zero, path.source],
      have ofpy : (of ∘ p.extend) 1 = of y.fo, by
        simp only [function.comp_app, set.right_mem_Icc, zero_le_one,
                   path.extend_extends, set.Icc.mk_one, path.target],
      have ofpc : continuous_on (of ∘ p.extend) 𝕀, by
      { apply continuous_for_path_metric_of_bounded_variation_of_continuous,
        exacts [λ x hx z hz y ⟨yl,yr⟩, ⟨hx.left.trans yl, yr.trans hz.right⟩,
                (p.continuous_extend).continuous_on,
                has_bounded_variation_on.has_locally_bounded_variation_on h], },
      calc infi path.length
         ≤ evariation_on (path.of_continuous_on zero_le_one ofpx ofpy ofpc).extend 𝕀 : infi_le _ _
      ...= evariation_on (path_emetric.of ∘ p.extend) 𝕀 : by
      begin
        refine evariation_on.eq_of_eq_on (λ u hu,_),
        simp only [function.comp_app, path.eq_on_extend_of_continuous_on_self _ _ _ _ hu,
                   tsub_zero, one_mul, zero_add],
      end
      ...≤ p.length : by
      begin
        apply evariation_on_for_path_metric_le_evariation_on_of_bounded_variation,
        exacts [λ x ⟨zx,xo⟩ y ⟨zy,yo⟩ u ⟨xu,uy⟩, ⟨zx.trans xu, uy.trans yo⟩,
                has_bounded_variation_on.has_locally_bounded_variation_on h,
                p.continuous_extend.continuous_on],
      end },
    { simp only [not_not] at h,
      simp only [path.length, h, le_top], }, },
  { rintro p',
    calc infi path.length
       ≤ evariation_on (p'.comp fo from_length_emetric_nonexpanding.continuous).extend 𝕀 :
    infi_le _ _
    ...= evariation_on (fo ∘ p'.extend) 𝕀 : by
    begin
      refine evariation_on.eq_of_eq_on (λ u hu,_),
      rw path.extend_comp,
    end
    ...≤ (1 : ℝ≥0∞) * (evariation_on p'.extend 𝕀) : by
    begin
      apply (from_length_emetric_nonexpanding.lipschitz_on_with set.univ).comp_evariation_on_le,
      exact (set.maps_to_univ _ _),
    end
    ...= evariation_on p'.extend 𝕀 : by simp only [one_mul] },
end

end path_emetric
-/
