import analysis.convex.basic

open set
open_locale classical

namespace submodule

theorem mem_sup_span_singleton {R E : Type*} {_ : division_ring R} {_ : add_comm_group E}
  {_ : module R E} {p : submodule R E} {x y : E} :
  y ∈ p ⊔ span R {x} ↔ y ∈ p ∨ ∃ (c : R) (c0 : c ≠ 0) (z : p), y = c • ((z:E) + x) :=
begin
  split,
  { simp only [mem_sup, exists_prop, mem_span_singleton],
    rintros ⟨z, hzp, _, ⟨c, rfl⟩, rfl⟩,
    by_cases hc : c = 0,
    { left, rwa [hc, zero_smul, add_zero] },
    { refine or.inr ⟨c, hc, c⁻¹ • ⟨z, hzp⟩, _⟩,
      rw [smul_add, coe_smul, smul_smul, mul_inv_cancel hc, one_smul, coe_mk] } },
  { rintros (hy|⟨c, hc0, ⟨z, hz⟩, rfl⟩),
    { exact le_def.1 lattice.le_sup_left hy },
    { exact smul_mem _ c (add_mem _ (le_def.1 lattice.le_sup_left hz)
        (le_def.1 lattice.le_sup_right $ subset_span $ mem_singleton x)),  } }
end

end submodule

variables {E : Type*} [add_comm_group E] [vector_space ℝ E]

structure convex_cone (s : set E) : Prop :=
(smul_mem : ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ s → c • x ∈ s)
(add_mem : ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x + y ∈ s)

variables {s t : set E}

lemma convex_cone.convex (hs : convex_cone s) : convex s :=
convex_iff_forall_pos.2 $ λ x y hx hy a b ha hb hab,
hs.add_mem (hs.smul_mem ha hx) (hs.smul_mem hb hy)

lemma convex_cone.smul_mem_iff (hs : convex_cone s) {c : ℝ} (hc : 0 < c) {x : E} :
  c • x ∈ s ↔ x ∈ s :=
⟨λ h, by simpa only [smul_smul, inv_mul_cancel (ne_of_gt hc), one_smul]
  using hs.smul_mem (inv_pos hc) h, λ h, hs.smul_mem hc h⟩

lemma convex_cone_sInter {S : set (set E)} (hS : ∀ s ∈ S, convex_cone s) :
  convex_cone (⋂₀ S) :=
{ smul_mem := λ c hc x hx s hs, (hS s hs).smul_mem hc (hx s hs),
  add_mem := λ x hx y hy s hs, (hS s hs).add_mem (hx s hs) (hy s hs) }

lemma convex_cone_Inter {ι : Sort*} {s : ι → set E} (hS : ∀ i, convex_cone (s i)) :
  convex_cone (⋂ i, s i) :=
convex_cone_sInter $ forall_range_iff.2 hS

lemma convex_cone.inter (hs : convex_cone s) (ht : convex_cone t) : convex_cone (s ∩ t) :=
{ smul_mem := λ c hc x ⟨hxs, hxt⟩, ⟨hs.smul_mem hc hxs, ht.smul_mem hc hxt⟩,
  add_mem := λ x ⟨hxs, hxt⟩ y ⟨hys, hyt⟩, ⟨hs.add_mem hxs hys, ht.add_mem hxt hyt⟩ }

/-- Cone over a `convex` set is a `convex_cone`. -/
lemma convex.cone (hs : convex s) :
  convex_cone {x : E | ∃ (c : ℝ) (hC : 0 < c), c • x ∈ s} :=
convex_cone.mk
begin
  rintros c c_pos x ⟨c', c'_pos, hc'⟩,
  refine ⟨c' / c, div_pos c'_pos c_pos, _⟩,
  rwa [smul_smul, div_mul_cancel _ (ne_of_gt c_pos)]
end
begin
  rintros x ⟨cx, cx_pos, hcx⟩ y ⟨cy, cy_pos, hcy⟩,
  refine ⟨cx * cy / (cy + cx), div_pos (mul_pos cx_pos cy_pos) (add_pos cy_pos cx_pos), _⟩,
  rw [smul_add, ← mul_div_assoc', mul_comm, mul_smul, div_mul_comm, mul_smul],
  exact convex_iff_div.1 hs hcx hcy (le_of_lt cy_pos) (le_of_lt cx_pos) (add_pos cy_pos cx_pos)
end

open submodule

theorem riesz_extension_step (hs : convex_cone s) (p : submodule ℝ E) {f : p →ₗ[ℝ] ℝ}
  (hps : ∀ y : E, ∃ x : p, y - x ∈ s) (hf : ∀ x : p, ↑x ∈ s → 0 ≤ f x) (hp : p < ⊤) :
  ∃ (p' : submodule ℝ E) (hp' : p < p') (g : p' →ₗ[ℝ] ℝ),
    (g.comp (of_le (le_of_lt hp')) = f) ∧ ∀ x : p', (x:E) ∈ s → 0 ≤ g x :=
begin
  rcases exists_of_lt hp with ⟨y, hy', hyp⟩, clear hy',
  set p' := p ⊔ span ℝ {y},
  have hyp' : y ∈ p', from (lattice.le_sup_right : _ ≤ p') (subset_span $ mem_singleton y),
  have hp' : p < p', from lt_iff_le_and_exists.2 ⟨lattice.le_sup_left, y, hyp', hyp⟩,
  use [p', hp'],
  set S := {x : p | y - x ∈ s},
  have fSle : ∀ (x : p), -y - x ∈ s → ∀ z ∈ S, f z ≤ f (-x),
  { intros x hx z hz,
    have : (-x - z : E) ∈ s, by { convert hs.add_mem hx hz, abel },
    norm_cast at this,
    have := hf _ this,
    rwa [← sub_nonneg, ← f.map_sub] },
  set r := lattice.Sup (f '' S),
  obtain ⟨g, hgf, hgy⟩ : ∃ g : p' →ₗ[ℝ] ℝ, (g.comp (of_le (le_of_lt hp')) = f) ∧ g ⟨y, hyp'⟩ = r,
    from sorry,
  use [g, hgf],
  rintros ⟨x, hxp'⟩ hxs,
  rcases mem_sup_span_singleton.1 hxp' with hxp|⟨c, hc0, ⟨z, hz⟩, rfl⟩,
  { convert hf ⟨x, hxp⟩ hxs,
    rw [← hgf, g.comp_apply, of_le_apply],
    exact congr_arg g rfl },
  convert_to 0 ≤ g (c • ((of_le (le_of_lt hp') ⟨z, hz⟩) + ⟨y, hyp'⟩)),
  rw [g.map_smul c, g.map_add, ← g.comp_apply, hgf, hgy, smul_eq_mul],
  change c • (z + y) ∈ s at hxs,
  clear hxp',
  cases lt_or_gt_of_ne hc0 with hc0 hc0,
  { apply mul_nonneg_of_nonpos_of_nonpos (le_of_lt hc0),
    rw [add_comm, ← le_neg_iff_add_nonpos, ← f.map_neg],
    apply lattice.cSup_le (nonempty.image f (hps y)),
    rintros _ ⟨w, hw, rfl⟩,
    rw [← neg_neg c, neg_smul, ← smul_neg, hs.smul_mem_iff (neg_pos.2 hc0), neg_add_rev] at hxs,
    apply fSle,
    exacts [hxs, hw] },
  { refine mul_nonneg (le_of_lt hc0) (neg_le_iff_add_nonneg.1 _),
    rw [← f.map_neg],
    refine lattice.le_cSup _ (mem_image_of_mem _ _),
    rcases hps (-y) with ⟨x₀, hx₀⟩,
    exact ⟨f (-x₀), ball_image_iff.2 (fSle x₀ hx₀)⟩,
    change _ ∈ s,
    rwa [coe_neg, coe_mk, sub_neg_eq_add, add_comm, ← hs.smul_mem_iff hc0] }
end
