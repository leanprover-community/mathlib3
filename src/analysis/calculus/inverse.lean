import analysis.calculus.deriv
import topology.local_homeomorph
import topology.metric_space.contracting

open function set filter
open_locale topological_space classical

namespace is_open_map

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β] {f : α → β}
  (h : is_open_map f)

include h

theorem is_open_range : is_open (range f) := by { rw ← image_univ, exact h _ is_open_univ }

theorem continuous_on_range_of_left_inverse {finv : β → α} (hleft : left_inverse finv f) :
  continuous_on finv (range f) :=
begin
  rintros _ ⟨x, rfl⟩ t ht,
  rw [hleft x] at ht,
  replace h : nhds (f x) ≤ map f (nhds x), from (is_open_map_iff_nhds_le _).1 h x,
  apply mem_nhds_within_of_mem_nhds,
  apply h,
  apply mem_sets_of_superset ht,
  rw [← preimage_comp, function.comp, funext hleft, preimage, set_of_mem_eq]
end

omit h

theorem continuous_on_image_of_left_inv_on {s : set α}
  (h : is_open_map (λ x : s, f x)) {finv : β → α} (hleft : left_inv_on finv f s) :
  continuous_on finv (f '' s) :=
begin
  rintros _ ⟨x, xs, rfl⟩ t ht,
  rw [hleft x xs] at ht,
  replace h := (is_open_map_iff_nhds_le _).1 h ⟨x, xs⟩,
  apply mem_nhds_within_of_mem_nhds,
  apply h,
  erw [map_compose.symm, comp, mem_map, ← nhds_within_eq_map_subtype_val],
  apply mem_sets_of_superset (inter_mem_nhds_within _ ht),
  assume y hy,
  rw [mem_set_of_eq, mem_preimage, hleft _ hy.1],
  exact hy.2
end

end is_open_map

lemma is_complete.complete_space {α : Type*} [uniform_space α] [complete_space α]
  {s : set α} (hs : is_complete s) :
  complete_space s :=
begin
  split,
  assume f hf,
  set f' := f.map subtype.val,
  have hf' : cauchy f' := cauchy_map uniform_continuous_subtype_val hf,
  have : s ∈ f', from mem_map.2 (univ_mem_sets' subtype.property),
  rcases hs f' hf' (le_principal_iff.2 this) with ⟨a, amem, ha⟩,
  use ⟨a, amem⟩,
  rw [map_le_iff_le_comap] at ha,
  rwa [nhds_subtype_eq_comap]
end

namespace metric

variables {α : Type*} {β : Type*} [metric_space α] [metric_space β] {f : α → β}

theorem is_open_map_iff :
  is_open_map f ↔ ∀ a : α, ∀ ε > 0, ∃ δ > 0, ball (f a) δ ⊆ f '' (ball a ε) :=
begin
  refine (is_open_map_iff_nhds_le f).trans (forall_congr $ λ a, _),
  split,
  { assume H ε ε0,
    exact mem_nhds_iff.1 (H (image_mem_map (ball_mem_nhds a ε0))) },
  { assume H s hs,
    rcases mem_nhds_iff.1 hs with ⟨ε, ε0, hε⟩,
    rcases H ε ε0 with ⟨δ, δ0, hδ⟩,
    exact mem_nhds_iff.2 ⟨δ, δ0, subset.trans hδ (image_subset_iff.2 hε)⟩ }
end

theorem mem_nhds_iff_closed_ball {s : set α} {x : α} :
  s ∈ 𝓝 x ↔ ∃ ε (H : 0 < ε), closed_ball x ε ⊆ s :=
begin
  rw mem_nhds_iff,
  refine ⟨_, λ ⟨ε, ε0, hε⟩, ⟨ε, ε0, subset.trans ball_subset_closed_ball hε⟩⟩,
  rintros ⟨ε, ε0, hε⟩,
  use [ε / 2, half_pos ε0],
  assume y hy,
  simp only [mem_ball, mem_closed_ball] at hε hy,
  exact hε (lt_of_le_of_lt hy $ half_lt_self ε0)
end

theorem closed_ball_subset_ball {ε₁ ε₂ : ℝ} {x : α} (h : ε₁ < ε₂) :
  closed_ball x ε₁ ⊆ ball x ε₂ :=
assume y (yx : _ ≤ ε₁), lt_of_le_of_lt yx h

theorem is_open_iff_closed_ball {s : set α} :
  is_open s ↔ ∀ x ∈ s, ∃ ε (H : 0 < ε), closed_ball x ε ⊆ s :=
by simp only [is_open_iff_nhds, mem_nhds_iff_closed_ball, le_principal_iff]

theorem is_open_map_on_iff_of_is_open {s : set α} (h : is_open s) :
  is_open_map (λ x : s, f x) ↔
    ∀ a ∈ s, ∀ ε > 0, closed_ball a ε ⊆ s → ∃ δ > 0, ball (f a) δ ⊆ f '' (closed_ball a ε) :=
begin
  split,
  { assume H a ha ε ε0 hε,
    rcases is_open_map_iff.1 H ⟨a, ha⟩ ε ε0 with ⟨δ, δ0, hδ⟩,
    refine ⟨δ, δ0, subset.trans hδ _⟩,
    rintros _ ⟨⟨x, xs⟩, hx, rfl⟩,
    simp only [subtype.coe_mk],
    apply mem_image_of_mem,
    exact (ball_subset_closed_ball hx) },
  { rw is_open_map_iff_nhds_le,
    rintros H ⟨a, ha⟩ t ht,
    erw [← filter.map_map, mem_map, ← nhds_within_eq_map_subtype_val, nhds_within_eq_of_open ha h,
      mem_nhds_iff] at ht,
    rcases ht with ⟨ε', ε0', hε'⟩,
    replace h := is_open_iff_nhds.1 h a ha,
    rw [le_principal_iff, mem_nhds_iff_closed_ball] at h,
    rcases h with ⟨ε, ε0, hε⟩,
    rcases H a ha (min ε (ε' / 2)) (lt_min ε0 (half_pos ε0'))
      (subset.trans (closed_ball_subset_closed_ball $ min_le_left _ _) hε) with ⟨δ, δ0, hδ⟩,
    rw [mem_nhds_iff],
    refine ⟨δ, δ0, subset.trans hδ (image_subset_iff.2 $ subset.trans _ hε')⟩,
    exact closed_ball_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self ε0')) }
end


end metric

theorem continuous_at_comp_subtype_val_iff_continuous_within_at {α β : Type*} [topological_space α]
  [topological_space β] {f : α → β} {s : set α} {a : α} {ha : a ∈ s} :
  continuous_at (λ x : s, f x) ⟨a, ha⟩ ↔ continuous_within_at f s a :=
by rw [continuous_at, continuous_within_at, tendsto, tendsto, nhds_within_eq_map_subtype_val ha,
  filter.map_map]; refl

theorem continuous_comp_subtype_val_iff_continuous_on {α β : Type*} [topological_space α]
  [topological_space β] {f : α → β} {s : set α} :
  continuous (λ x : s, f x) ↔ continuous_on f s :=
continuous_iff_continuous_at.trans $ subtype.forall.trans $
  forall_congr $ λ a, forall_congr $ λ ha, continuous_at_comp_subtype_val_iff_continuous_within_at

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space 𝕜 G]

open asymptotics filter metric set
open continuous_linear_map (id)

/-- Function `f` has derivative `f'` at `a` in the sense of *strict differentiability*,
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. Any `C^1` function is strictly differentiable
but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
def has_strict_fderiv_at (f : E → F) (f' : E →L[𝕜] F) (a : E) :=
is_o (λ p : E × E, f p.1 - f p.2 - f' (p.1 - p.2)) (λ p : E × E, p.1 - p.2) ((𝓝 a).prod (𝓝 a))

theorem continuous_linear_map.has_strict_fderiv_at (f : E →L[𝕜] F) (a : E) :
  has_strict_fderiv_at f f a :=
(is_o_zero _ _).congr_left $ λ x, by simp only [f.map_sub, sub_self]

theorem continuous_linear_equiv.has_strict_fderiv_at (f : E ≃L[𝕜] F) (a : E) :
  has_strict_fderiv_at f (f : E →L[𝕜] F) a :=
f.to_continuous_linear_map.has_strict_fderiv_at a

theorem exists_local_homeo_of_id_approx [complete_space E]
  {f : E → E} {c : ℝ} (hc : c ∈ Ioo (0:ℝ) 1) {s : set E}
  (hs : is_open s) (hf : ∀ x y ∈ s, ∥f x - f y - (x - y)∥ ≤ c * ∥x - y∥) :
  ∃ e : local_homeomorph E E, e.to_fun = f ∧ e.source = s :=
begin
  have dist_le_of_image : ∀ x y ∈ s,  dist x y ≤ dist (f x) (f y) / (1 - c),
  { assume x y hx hy,
    rw [le_div_iff' (sub_pos.2 hc.2), sub_mul, one_mul, dist_eq_norm, dist_eq_norm, sub_le],
    apply le_trans (norm_sub_norm_le _ _),
    rw [← norm_neg],
    convert hf x y hx hy,
    abel },
  have f_inj : inj_on f s,
  { assume x y hx hy hxy,
    have := dist_le_of_image x y hx hy,
    rwa [dist_eq_zero.2 hxy, zero_div, dist_le_zero] at this },
  have f_lip : lipschitz_with (1 + ⟨c, le_of_lt hc.1⟩) (λ x : s, f x),
  { assume x y,
    simp only [dist_eq_norm, subtype.dist_eq, nnreal.coe_add, nnreal.coe_one,
      add_mul, one_mul, sub_le_iff_le_add'.symm],
    apply le_trans (norm_sub_norm_le _ _),
    exact hf x y x.2 y.2 },
  have f_cont : continuous_on f s,
    from continuous_comp_subtype_val_iff_continuous_on.1 f_lip.to_continuous,
  -- Main part of the proof: application of the Banach fixed-point theorem
  have f_open : is_open_map (λ x : s, f x),
  { rw is_open_map_on_iff_of_is_open hs,
    intros b hb ε ε0 hε,
    set δ := (1 - c) * ε,
    have δ0 : 0 < δ, from mul_pos (sub_pos.2 hc.2) ε0,
    refine ⟨δ, δ0, λ y hy, _⟩,
    set g : E → E := λ x, x + y - f x,
    have g_sub : ∀ x x', g x - g x' = -(f x - f x' - (x - x')),
    { assume x x', simp only [g], abel },
    have g_contracts : ∀ x x' ∈ s, dist (g x) (g x') ≤ c * dist x x',
    { assume x x' hx hx',
      rw [dist_eq_norm, dist_eq_norm, g_sub, norm_neg],
      exact hf x x' hx hx' },
    have dist_g : ∀ x, dist x (g x) = dist (f x) y,
      by { intro x, simp only [g, dist_eq_norm], apply congr_arg, abel },
    have fixed_iff : ∀ {x}, g x = x ↔ f x = y,
    { assume x, rw [← dist_eq_zero, dist_comm, dist_g, dist_eq_zero]},
    have g_maps_to : maps_to g (closed_ball b ε) (closed_ball b ε),
    { assume x hx,
      simp only [mem_closed_ball, mem_ball, mem_preimage] at hx hy ⊢,
      rw [dist_comm] at hy,
      calc dist (g x) b ≤ dist (g x) (g b) + dist b (g b) : dist_triangle_right _ _ _
      ... ≤ c * dist x b + dist (f b) y :
        add_le_add (g_contracts _ _ (hε hx) hb) (le_of_eq $ dist_g b)
      ... ≤ c * ε + (1 - c) * ε :
        add_le_add ((mul_le_mul_left hc.1).2 hx) (le_of_lt hy)
      ... = ε : by rw [sub_mul, one_mul, add_sub_cancel'_right] },
    let g' : (closed_ball b ε) → (closed_ball b ε) := λ x, ⟨g x, g_maps_to x.2⟩,
    have hg' : contracting_with ⟨c, le_of_lt hc.1⟩ g',
      from ⟨hc.2, λ x x', g_contracts x x' (hε x.2) (hε x'.2)⟩,
    haveI : complete_space (closed_ball b ε) :=
      (is_complete_of_is_closed is_closed_ball).complete_space,
    haveI : nonempty (closed_ball b ε) := ⟨⟨b, mem_closed_ball_self (le_of_lt ε0)⟩⟩,
    rcases hg'.exists_fixed_point with ⟨⟨x, xmem⟩, hx⟩,
    have : f x = y, from fixed_iff.1 (subtype.ext.1 hx),
    exact ⟨x, xmem, this⟩ },
  -- Now we pack the results are required by the theorem
  letI : inhabited E := ⟨0⟩,
  set e : local_equiv E E := f_inj.to_local_equiv f s,
  refine ⟨⟨e, hs, _, f_cont, _⟩, rfl, rfl⟩,
  { change is_open (f '' s),
    rw [image_eq_range],
    apply f_open.is_open_range },
  { apply f_open.continuous_on_image_of_left_inv_on,
    exact e.left_inv }
end

namespace has_strict_fderiv_at

lemma has_fderiv_at {f : E → F} {f' : E →L[𝕜] F} {a : E}
  (hf : has_strict_fderiv_at f f' a) :
  has_fderiv_at f f' a :=
λ c hc, (tendsto_id.prod_mk tendsto_const_nhds) (hf c hc)

lemma comp {g : F → G} {f : E → F} {g' : F →L[𝕜] G} {f' : E →L[𝕜] F} {a : E}
  (hg : has_strict_fderiv_at g g' (f a)) (hf : has_strict_fderiv_at f f' a) :
  has_strict_fderiv_at (λ x, g (f x)) (g'.comp f') a :=
sorry


lemma exists_local_homeo [complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∃ e : local_homeomorph E F, e.to_fun = f ∧ e.source ∈ 𝓝 a :=
begin
  have hg := (f'.symm.has_strict_fderiv_at (f a)).comp hf,
  set g : E → E := λ x, f'.symm (f x),
  rw [f'.coe_symm_comp_coe] at hg,
  rcases mem_prod_same_iff.1 (hg _ one_half_pos) with ⟨s', smem', hs'⟩,
  rcases mem_nhds_sets_iff.1 smem' with ⟨s, hss', hs, has⟩,
  have hle : ∀ x y ∈ s, ∥g x - g y - (x - y)∥ ≤ (1 / 2) * ∥x - y∥,
  { intros x y hx hy,
    exact hs' (⟨hss' hx, hss' hy⟩ : (x, y) ∈ s'.prod s') },
  rcases exists_local_homeo_of_id_approx ⟨one_half_pos, one_half_lt_one⟩ hs hle
    with ⟨e, heg, hes⟩,
  let e' : local_homeomorph E F := e.trans f'.to_homeomorph.to_local_homeomorph,
  have H1 : e'.to_fun = f, by sorry,
  have H2 : e'.source = s, from sorry,
  exact ⟨e', H1, H2.symm ▸ mem_nhds_sets hs has⟩
end
end has_strict_fderiv_at

