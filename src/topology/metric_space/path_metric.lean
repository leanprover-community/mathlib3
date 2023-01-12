import topology.metric_space.emetric_space
import analysis.bounded_variation
import topology.path_connected

noncomputable theory

open_locale nnreal ennreal big_operators

private abbreviation 𝕀 := unit_interval

set_option profiler true

lemma half_nonneg {α : Type*} [linear_ordered_semifield α] {a : α} (h : 0 ≤ a) :
  0 ≤ a / 2 := sorry

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

lemma half_mem : (1:ℝ) / 2 ∈ unit_interval := div_mem zero_le_one zero_le_two one_le_two

/-- The midpoint of the unit interval -/
abbreviation half : unit_interval := ⟨_, half_mem⟩

end unit_interval

namespace path

lemma extend_symm
  {X : Type*} [topological_space X] {x y : X} (γ : path x y) :
  γ.symm.extend = γ.extend ∘ (λ x, 1 - x) := sorry

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
    sorry, sorry, sorry,
  },
  { rw set.inter_eq_self_of_subset_right (set.Icc_subset_Icc_left (unit_interval.half_mem.left)),
    rw ←evariation_on.comp_eq_of_monotone_on (q.extend) (λ (t : ℝ), -1 + (3-1)*t),
    { apply evariation_on.eq_of_eq_on,
      simp_rw [neg_add_eq_sub, (sorry : (3:ℝ)-1 = 2)],
      apply path.extend_trans_on_top_half, },
    sorry, sorry, sorry, },
end

end path

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
    exact (monotone_line_map_of_le _ _ st).monotone_on _,
    exact (maps_to_unit_interval_line_map_of_le _ _ st),
    exact (surj_on_unit_interval_line_map_of_le _ _ st), },
  rw [this, ←evariation_on.eq_of_eq_on (path.eq_on_extend_of_continuous_on_self st ps pt pc)],
  exact infi_le (λ p, evariation_on p.extend 𝕀) (path.of_continuous_on st ps pt pc),
end

lemma continuous_for_path_metric_of_bounded_variation_of_continuous {f : ℝ → E}
  {s : set ℝ} (hs : ∀ (x z ∈ s) (y : ℝ), x ≤ y → y ≤ z → y ∈ s)
  (fc : continuous_on f s) (fb : has_locally_bounded_variation_on f s) :
  continuous_on (of ∘ f) s := sorry

lemma sum_for_path_metric_le_evariation_on_of_bounded_variation {f : ℝ → E}
  {s : set ℝ} (hs : ∀ (x z ∈ s) (y : ℝ), x ≤ y → y ≤ z → y ∈ s)
  (fb : has_locally_bounded_variation_on f s) (fc : continuous_on f s)
  (n : ℕ) {u : ℕ → ℝ} (us : ∀ i, u i ∈ s) (um : monotone u) :
  ∑ i in finset.range n, edist ((of ∘ f) (u (i + 1))) ((of ∘ f) (u i)) ≤ evariation_on f s :=
begin
  calc ∑ i in finset.range n, edist ((of ∘ f) (u (i + 1))) ((of ∘ f) (u i))
     ≤ ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ)) : by
  begin
    refine finset.sum_le_sum (λ i hi, _),
    rw edist_comm,
    refine edist_le (um (i.le_succ)) rfl rfl (fc.mono $ λ x ⟨xl,xr⟩, hs _ (us i) _ (us i.succ) x xl xr ),
  end
  ...= ∑ i in finset.range n, evariation_on f (set.Icc (u i) (u i.succ) ∩ s) : by
  { congr' 1 with i : 1, congr, symmetry,
    apply set.inter_eq_self_of_subset_left,
    exact λ t ht, hs (u i) (us i) (u i.succ) (us i.succ) t ht.left ht.right, }
  ...≤ evariation_on f s : evariation_on.sum_on_Icc_le f n um (λ i hi, us i)
end

lemma evariation_on_for_path_metric_le_evariation_on_of_bounded_variation {f : ℝ → E}
  {s : set ℝ} (hs : ∀ (x z ∈ s) (y : ℝ), x ≤ y → y ≤ z → y ∈ s)
  (fb : has_locally_bounded_variation_on f s)  (fc : continuous_on f s) :
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
  dsimp only [edist, from_path_emetric, path.length],
  apply le_antisymm; simp only [le_infi_iff],
  { rintro p,
    by_cases h : evariation_on p.extend 𝕀 ≠ ⊤,
    { have ofpx : (of ∘ p.extend) 0 = of x.fo, by
        simp only [function.comp_app, set.left_mem_Icc, zero_le_one, path.extend_extends, set.Icc.mk_zero, path.source],
      have ofpy : (of ∘ p.extend) 1 = of y.fo, by
        simp only [function.comp_app, set.right_mem_Icc, zero_le_one, path.extend_extends, set.Icc.mk_one, path.target],
      have ofpc : continuous_on (of ∘ p.extend) 𝕀, by
      { apply continuous_for_path_metric_of_bounded_variation_of_continuous,
        exacts [λ x hx z hz y yl yr, ⟨hx.left.trans yl, yr.trans hz.right⟩,
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
        exacts [λ x ⟨zx,xo⟩ y ⟨zy,yo⟩ u xu uy, ⟨zx.trans xu, uy.trans yo⟩,
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
