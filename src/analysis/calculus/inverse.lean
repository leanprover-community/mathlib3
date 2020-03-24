import analysis.calculus.deriv
import topology.local_homeomorph
import topology.metric_space.contracting

open function set filter metric
open_locale topological_space classical nnreal

section

variables {α : Type*} {β : Type*} [emetric_space α] [emetric_space β]
  {g : β → α} {f : α → β} {t : set β}

lemma antilipschitz_with.to_right_inv_on {K : ℝ≥0} (hf : antilipschitz_with K f)
  (h : right_inv_on g f t) :
  lipschitz_with K (t.restrict g) :=
λ x y, by simpa only [restrict_apply, h x.mem, h y.mem] using hf (g x) (g y)

lemma antilipschitz_with.to_right_inv_on' {K : ℝ≥0} {s : set α}
  (hf : antilipschitz_with K (s.restrict f)) (g_maps : maps_to g t s)
  (g_inv : right_inv_on g f t) :
  lipschitz_with K (t.restrict g) :=
λ x y, by simpa only [restrict_apply, g_inv x.mem, g_inv y.mem, subtype.edist_eq, subtype.coe_mk,
    subtype.val_eq_coe] using hf ⟨g x, g_maps x.mem⟩ ⟨g y, g_maps y.mem⟩

lemma antilipschitz_with.cod_restrict {K : ℝ≥0} (hf : antilipschitz_with K f)
  {s : set β} (hs : ∀ x, f x ∈ s) :
  antilipschitz_with K (s.cod_restrict f hs) :=
λ x y, hf x y

lemma subsingleton.antilipschitz_with [subsingleton α] {K : ℝ≥0} : antilipschitz_with K f :=
λ x y, by simp only [subsingleton.elim x y, edist_self, zero_le]

lemma set.subsingleton_univ {α : Type*} [subsingleton α] : (univ : set α).subsingleton :=
λ x hx y hy, subsingleton.elim x y

lemma subsingleton.empty_or_univ {α : Type*} [subsingleton α] (s : set α) :
  s = ∅ ∨ s = univ :=
s.eq_empty_or_nonempty.imp id (λ ⟨x, hx⟩, eq_univ_of_forall $ λ y, subsingleton.elim x y ▸ hx)

lemma subsingleton.is_open {α : Type*} [topological_space α] [subsingleton α] (s : set α) :
  is_open s :=
(subsingleton.empty_or_univ s).elim (λ h, h.symm ▸ is_open_empty) (λ h, h.symm ▸ is_open_univ)

lemma subsingleton.is_closed {α : Type*} [topological_space α] [subsingleton α] (s : set α) :
  is_closed s :=
(subsingleton.empty_or_univ s).elim (λ h, h.symm ▸ is_closed_empty) (λ h, h.symm ▸ is_closed_univ)

end


section
variables {α : Type*} {β : Type*} [metric_space α] [metric_space β] {f : α → β}

theorem is_open_iff_closed_ball {s : set α} :
  is_open s ↔ ∀ x ∈ s, ∃ ε (H : 0 < ε), closed_ball x ε ⊆ s :=
by simp only [is_open_iff_nhds, le_principal_iff, nhds_basis_closed_ball.mem_iff]
end

namespace local_homeomorph

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

lemma eventually_left_inverse (e : local_homeomorph α β) {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 x, e.inv_fun (e.to_fun y) = y :=
eventually.mono (mem_nhds_sets e.open_source hx) e.left_inv

lemma eventually_right_inverse (e : local_homeomorph α β) {x} (hx : x ∈ e.target) :
  ∀ᶠ y in 𝓝 x, e.to_fun (e.inv_fun y) = y :=
eventually.mono (mem_nhds_sets e.open_target hx) e.right_inv

lemma eventually_right_inverse' (e : local_homeomorph α β) {x} (hx : x ∈ e.source) :
  ∀ᶠ y in 𝓝 (e.to_fun x), e.to_fun (e.inv_fun y) = y :=
e.eventually_right_inverse (e.map_source hx)

variables {E : Type*} [has_norm E] {F : Type*} [has_norm F]

open asymptotics

/-- Transfer `is_O_with` over a `local_homeomorph`. -/
lemma is_O_with_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target)
  {f : β → E} {g : β → F} {C : ℝ} :
  is_O_with C f g (𝓝 b) ↔ is_O_with C (f ∘ e.to_fun) (g ∘ e.to_fun) (𝓝 (e.inv_fun b)) :=
⟨λ h, h.comp_tendsto $
  by { convert e.continuous_at_to_fun (e.map_target hb), exact (e.right_inv hb).symm },
  λ h, (h.comp_tendsto (e.continuous_at_inv_fun hb)).congr' rfl
    ((e.eventually_right_inverse hb).mono $ λ x hx, congr_arg f hx)
    ((e.eventually_right_inverse hb).mono $ λ x hx, congr_arg g hx)⟩

/-- Transfer `is_O` over a `local_homeomorph`. -/
lemma is_O_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
  is_O f g (𝓝 b) ↔ is_O (f ∘ e.to_fun) (g ∘ e.to_fun) (𝓝 (e.inv_fun b)) :=
exists_congr $ λ C, e.is_O_with_congr hb

/-- Transfer `is_o` over a `local_homeomorph`. -/
lemma is_o_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
  is_o f g (𝓝 b) ↔ is_o (f ∘ e.to_fun) (g ∘ e.to_fun) (𝓝 (e.inv_fun b)) :=
forall_congr $ λ c, forall_congr $ λ hc, e.is_O_with_congr hb

end local_homeomorph

lemma continuous_at.prod_map {α β γ δ : Type*} [topological_space α] [topological_space β]
  [topological_space γ] [topological_space δ] {f : α → γ} {g : β → δ} {x : α} {y : β}
  (hf : continuous_at f x) (hg : continuous_at g y) :
  continuous_at (λ p : α × β, (f p.1, g p.2)) (x, y) :=
have hf : continuous_at f (x, y).fst, from hf,
have hg : continuous_at g (x, y).snd, from hg,
(hf.comp continuous_fst.continuous_at).prod (hg.comp continuous_snd.continuous_at)

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space 𝕜 G]

open asymptotics filter metric set
open continuous_linear_map (id)

/-- Function `f` has derivative `f'` at `a` in the sense of *strict differentiability*,
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. Any `C^1` function on a vector space
over `ℝ` is strictly differentiable but this definition works, e.g., for vector spaces
over `p`-adic numbers. -/
def has_strict_fderiv_at (f : E → F) (f' : E →L[𝕜] F) (a : E) :=
is_o (λ p : E × E, f p.1 - f p.2 - f' (p.1 - p.2)) (λ p : E × E, p.1 - p.2) (𝓝 (a, a))

theorem continuous_linear_map.has_strict_fderiv_at (f : E →L[𝕜] F) (a : E) :
  has_strict_fderiv_at f f a :=
(is_o_zero _ _).congr_left $ λ x, by simp only [f.map_sub, sub_self]

theorem continuous_linear_equiv.has_strict_fderiv_at (f : E ≃L[𝕜] F) (a : E) :
  has_strict_fderiv_at f (f : E →L[𝕜] F) a :=
(f : E →L[𝕜] F).has_strict_fderiv_at a

/-- We say that `f` approximates continuous linear map `f'` on `s` with constant `c`,
if `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` whenever `x, y ∈ s`.

TODO : find a better name or move into a namespace.

This predicate is defined to faciliate splitting of the inverse function theorem into small lemmas.
Some of these lemmas can be useful, e.g., to prove that the inverse function is defined
on a specific set. -/
def approximates_linear_on (f : E → F) (f' : E →L[𝕜] F) (s : set E) (c : ℝ≥0) : Prop :=
∀ (x ∈ s) (y ∈ s), ∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥

/-- If `f` has derivative `f'` at `a` in strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
lemma has_strict_fderiv_at.approximates_linear_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E}
  (hf : has_strict_fderiv_at f f' a) {c : ℝ≥0} (hc : 0 < c) :
  ∃ s ∈ 𝓝 a, approximates_linear_on f f' s c :=
begin
  have := hf hc,
  rw [nhds_prod_eq, is_O_with, filter.eventually, mem_prod_same_iff] at this,
  rcases this with ⟨s, has, hs⟩,
  exact ⟨s, has, λ x hx y hy, hs (mk_mem_prod hx hy)⟩
end

namespace approximates_linear_on

variables [cs : complete_space E] {f : E → F}

section

variables {f' : E →L[𝕜] F} {s : set E} {c c' : ℝ≥0}

protected theorem mono (hf : approximates_linear_on f f' s c) (hc : c ≤ c') :
  approximates_linear_on f f' s c' :=
λ x hx y hy, le_trans (hf x hx y hy) (mul_le_mul_of_nonneg_right hc $ norm_nonneg _)

lemma lipschitz_sub (hf : approximates_linear_on f f' s c) :
  lipschitz_with c (λ x : s, f x - f' x) :=
begin
  refine lipschitz_with.of_dist_le_mul (λ x y, _),
  rw [dist_eq_norm, subtype.dist_eq, dist_eq_norm],
  convert hf x x.2 y y.2 using 2,
  rw [f'.map_sub], abel
end

protected lemma lipschitz (hf : approximates_linear_on f f' s c) :
  lipschitz_with (nnnorm f' + c) (s.restrict f) :=
by simpa only [restrict_apply, add_sub_cancel'_right]
  using (f'.lipschitz.restrict s).add hf.lipschitz_sub

protected lemma continuous (hf : approximates_linear_on f f' s c) :
  continuous (s.restrict f) :=
hf.lipschitz.continuous

protected lemma continuous_on (hf : approximates_linear_on f f' s c) :
  continuous_on f s :=
continuous_on_iff_continuous_restrict.2 hf.continuous

end

variables {f' : E ≃L[𝕜] F} {s : set E} {c : ℝ≥0}
  (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)

include hf

local notation `N` := nnnorm (f'.symm : F →L[𝕜] E)

variable (hc : subsingleton E ∨ c < N⁻¹)

include hc

protected lemma antilipschitz : antilipschitz_with (N⁻¹ - c)⁻¹ (s.restrict f) :=
begin
  cases hc with hE hc,
  { haveI : subsingleton s := ⟨λ x y, subtype.eq $ @subsingleton.elim _ hE _ _⟩,
    exact subsingleton.antilipschitz_with },
  convert (f'.antilipschitz.restrict s).add_lipschitz_with hf.lipschitz_sub hc,
  simp [restrict]
end

protected lemma injective : injective (s.restrict f) :=
(hf.antilipschitz hc).injective

protected lemma inj_on : inj_on f s :=
inj_on_iff_injective.2 $ hf.injective hc

/-- A map approximating a linear equivalence defines a local equivalence. Should not
be used outside of this file, because it is superseeded by `to_local_homeomorph` below.

This is a first step towards the inverse function. -/
noncomputable def to_local_equiv : local_equiv E F :=
by haveI : nonempty E := ⟨0⟩; exact (hf.inj_on hc).to_local_equiv _ _

/-- Inverse function is continuous on `f '' s`. Use properties of `local_homeomorph` instead. -/
lemma inverse_continuous_on : continuous_on (hf.to_local_equiv hc).inv_fun (f '' s) :=
continuous_on_iff_continuous_restrict.2 $
  ((hf.antilipschitz hc).to_right_inv_on' (hf.to_local_equiv hc).map_target
    (hf.to_local_equiv hc).right_inv).continuous

omit hf hc

section

variables (f f')

/-- Iterations of this map converge to `f⁻¹ y`. -/
def inverse_approx_map (y : F) (x : E) : E := x + f'.symm (y - f x)

end

section inverse_approx_map

variables (y : F) {x x' : E} {ε : ℝ}

local notation `g` := inverse_approx_map f f' y

lemma inverse_approx_map_sub (x x' : E) : g x - g x' = (x - x') - f'.symm (f x - f x') :=
by { simp only [inverse_approx_map, f'.symm.map_sub], abel }

lemma inverse_approx_map_dist_self (x : E) :
  dist (g x) x = dist (f'.symm $ f x) (f'.symm y) :=
by simp only [inverse_approx_map, dist_eq_norm, f'.symm.map_sub, add_sub_cancel', norm_sub_rev]

lemma inverse_approx_map_dist_self_le (x : E) :
  dist (g x) x ≤ N * dist (f x) y :=
by { rw inverse_approx_map_dist_self, exact f'.symm.lipschitz.dist_le_mul (f x) y }

lemma inverse_approx_map_fixed_iff {x : E} :
  g x = x ↔ f x = y :=
by rw [← dist_eq_zero, inverse_approx_map_dist_self, dist_eq_zero, f'.symm.injective.eq_iff]

include hf hc

lemma inverse_approx_map_contracts_on {x x'} (hx : x ∈ s) (hx' : x' ∈ s) :
  dist (g x) (g x') ≤ N * c * dist x x' :=
begin
  rw [dist_eq_norm, dist_eq_norm, inverse_approx_map_sub, norm_sub_rev],
  suffices : ∥f'.symm (f x - f x' - f' (x - x'))∥ ≤ N * (c * ∥x - x'∥),
    by simpa only [f'.symm.map_sub, f'.symm_apply_apply, mul_assoc] using this,
  exact (f'.symm : F →L[𝕜] E).le_op_norm_of_le (hf x hx x' hx')
end

variable {y}

lemma inverse_approx_map_maps_to {b : E} (hb : b ∈ s) (hε : closed_ball b ε ⊆ s)
  (hy : y ∈ closed_ball (f b) ((N⁻¹ - c) * ε)) :
  maps_to g (closed_ball b ε) (closed_ball b ε) :=
begin
  cases hc with hE hc,
  { exactI λ x hx, mem_preimage.2 (subsingleton.elim x (g x) ▸ hx) },
  assume x hx,
  simp only [subset_def, mem_closed_ball, mem_preimage] at hx hy ⊢,
  rw [dist_comm] at hy,
  calc dist (inverse_approx_map f f' y x) b ≤
    dist (inverse_approx_map f f' y x) (inverse_approx_map f f' y b) +
      dist (inverse_approx_map f f' y b) b : dist_triangle _ _ _
  ... ≤ N * c * dist x b + N * dist (f b) y :
    add_le_add (hf.inverse_approx_map_contracts_on (or.inr hc) y (hε hx) hb)
      (inverse_approx_map_dist_self_le _ _)
  ... ≤ N * c * ε + N * ((N⁻¹ - c) * ε) :
    add_le_add (mul_le_mul_of_nonneg_left hx (mul_nonneg (nnreal.coe_nonneg _) c.coe_nonneg))
      (mul_le_mul_of_nonneg_left hy (nnreal.coe_nonneg _))
  ... = N * (c + (N⁻¹ - c)) * ε : by simp only [mul_add, add_mul, mul_assoc]
  ... = ε : by { rw [add_sub_cancel'_right, mul_inv_cancel, one_mul],
    exact ne_of_gt (inv_pos.1 $ lt_of_le_of_lt c.coe_nonneg hc) }
end

end inverse_approx_map

include hf cs hc

variable {ε : ℝ}

theorem surj_on_closed_ball {b : E} (ε0 : 0 ≤ ε) (hε : closed_ball b ε ⊆ s) :
  surj_on f (closed_ball b ε) (closed_ball (f b) ((N⁻¹ - c) * ε)) :=
begin
  cases hc with hE hc,
  { resetI,
    haveI hF : subsingleton F := f'.symm.to_linear_equiv.to_equiv.subsingleton,
    intros y hy,
    exact ⟨b, mem_closed_ball_self ε0, subsingleton.elim _ _⟩ },
  intros y hy,
  have : contracting_with (N * c) ((hf.inverse_approx_map_maps_to (or.inr hc)
    (hε $ mem_closed_ball_self ε0) hε hy).restrict _ _ _),
  { split,
    { rwa [mul_comm, ← nnreal.lt_inv_iff_mul_lt],
      exact ne_of_gt (inv_pos.1 $ lt_of_le_of_lt c.coe_nonneg hc) },
    { exact lipschitz_with.of_dist_le_mul (λ x x', hf.inverse_approx_map_contracts_on
        (or.inr hc) y (hε x.mem) (hε x'.mem)) } },
  refine ⟨this.efixed_point' _ _ _ b (mem_closed_ball_self ε0) (edist_lt_top _ _), _, _⟩,
  { exact is_complete_of_is_closed is_closed_ball },
  { apply contracting_with.efixed_point_mem' },
  { exact (inverse_approx_map_fixed_iff y).1 (this.efixed_point_is_fixed' _ _ _ _) }
end

section

variables (f s)

/-- Given a function `f` that approximates a linear equivalence on an open set `s`,
returns a local homeomorph with `to_fun = f` and `source = s`. -/
noncomputable def to_local_homeomorph (hs : is_open s) : local_homeomorph E F :=
{ to_local_equiv := hf.to_local_equiv hc,
    open_source := hs,
    open_target :=
      begin
        cases hc with hE hc,
        { resetI,
          haveI hF : subsingleton F := f'.to_linear_equiv.to_equiv.symm.subsingleton,
          exact subsingleton.is_open _ },
        change is_open (f '' s),
        simp only [is_open_iff_mem_nhds, nhds_basis_closed_ball.mem_iff, ball_image_iff] at hs ⊢,
        intros x hx,
        rcases hs x hx with ⟨ε, ε0, hε⟩,
        refine ⟨(N⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, _⟩,
        exact (hf.surj_on_closed_ball (or.inr hc) (le_of_lt ε0) hε).mono hε (subset.refl _)
      end,
    continuous_to_fun := hf.continuous_on,
    continuous_inv_fun := hf.inverse_continuous_on hc }

end

@[simp] lemma to_local_homeomorph_to_fun (hs : is_open s) :
  (hf.to_local_homeomorph f s hc hs).to_fun = f := rfl

@[simp] lemma to_local_homeomorph_source (hs : is_open s) :
  (hf.to_local_homeomorph f s hc hs).source = s := rfl

@[simp] lemma to_local_homeomorph_target (hs : is_open s) :
  (hf.to_local_homeomorph f s hc hs).target = f '' s := rfl

end approximates_linear_on

namespace has_strict_fderiv_at

section
variables {f : E → F} {f' : E →L[𝕜] F} {a : E}

protected lemma is_O (hf : has_strict_fderiv_at f f' a) :
  is_O (λ p : E × E, f p.1 - f p.2) (λ p : E × E, p.1 - p.2) (𝓝 (a, a)) :=
(hf.is_O.add $ f'.is_O_comp _ _).congr_left (λ p, sub_add_cancel _ _)

lemma has_fderiv_at (hf : has_strict_fderiv_at f f' a) :
  has_fderiv_at f f' a :=
λ c hc, tendsto_id.prod_mk_nhds tendsto_const_nhds (hf hc)

lemma differentiable_at (hf : has_strict_fderiv_at f f' a) :
  differentiable_at 𝕜 f a :=
hf.has_fderiv_at.differentiable_at

lemma continuous_at (hf : has_strict_fderiv_at f f' a) :
  continuous_at f a :=
hf.has_fderiv_at.continuous_at

lemma comp {g : F → G} {g' : F →L[𝕜] G} (hg : has_strict_fderiv_at g g' (f a))
  (hf : has_strict_fderiv_at f f' a) :
  has_strict_fderiv_at (λ x, g (f x)) (g'.comp f') a :=
((hg.comp_tendsto (hf.continuous_at.prod_map hf.continuous_at)).trans_is_O hf.is_O).triangle $
  by simpa only [g'.map_sub, f'.coe_comp']
    using (g'.is_O_comp _ _).trans_is_o hf

lemma approximates_deriv_on_open_nhds' (hf : has_strict_fderiv_at f f' a) {c : ℝ≥0}
  (hc : subsingleton E ∨ 0 < c) :
  ∃ s : set E, a ∈ s ∧ is_open s ∧ approximates_linear_on f f' s c :=
begin
  cases hc with hE hc,
  { refine ⟨univ, trivial, is_open_univ, λ x hx y hy, _⟩,
    simp [@subsingleton.elim E hE x y] },
  simp only [has_strict_fderiv_at, nhds_prod_eq] at hf,
  rcases mem_prod_same_iff.1 (hf hc) with ⟨s', smem', hs'⟩,
  rcases mem_nhds_sets_iff.1 smem' with ⟨s, hss', hs, has⟩,
  exact ⟨s, has, hs, λ x hx y hy, hs' (mk_mem_prod (hss' hx) (hss' hy))⟩
end

end

variables [cs : complete_space E] {f : E → F} (f' : E ≃L[𝕜] F) {a : E}
  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a)

-- TODO move
lemma subsingleton_or_norm_symm_pos :
  subsingleton E ∨ 0 < ∥(f'.symm : F →L[𝕜] E)∥ :=
(subsingleton_or_exists_ne (0 : E)).imp id (λ hE, f'.norm_symm_pos hE)

lemma subsingleton_or_nnnorm_symm_pos :
  subsingleton E ∨ 0 < (nnnorm $ (f'.symm : F →L[𝕜] E)) :=
subsingleton_or_norm_symm_pos f'

variable {f'}

lemma approximates_deriv_on_open_nhds :
  ∃ s : set E, a ∈ s ∧ is_open s ∧
    approximates_linear_on f (f' : E →L[𝕜] F) s ((nnnorm (f'.symm : F →L[𝕜] E))⁻¹ / 2) :=
hf.approximates_deriv_on_open_nhds' $ (subsingleton_or_exists_ne (0 : E)).imp id $
  λ hE, nnreal.half_pos $ nnreal.inv_pos.2 $ f'.norm_symm_pos hE

include cs hf

variable (f)

/-- Given a function with a bijective strict derivative at `a`, returns a `local_homeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `local_homeomorph.inv_fun_has_strict_fderiv_at`  -/
noncomputable def to_local_homeomorph : local_homeomorph E F :=
approximates_linear_on.to_local_homeomorph f
  (classical.some hf.approximates_deriv_on_open_nhds)
  (classical.some_spec hf.approximates_deriv_on_open_nhds).2.2
  ((subsingleton_or_exists_ne (0:E)).imp id $ λ hE, nnreal.half_lt_self $ ne_of_gt $
    nnreal.inv_pos.2 $ f'.norm_symm_pos hE)
  (classical.some_spec hf.approximates_deriv_on_open_nhds).2.1

variable {f}

@[simp] lemma to_local_homeomorph_to_fun : (hf.to_local_homeomorph f).to_fun = f := rfl

lemma mem_to_local_homeomorph_source : a ∈ (hf.to_local_homeomorph f).source :=
  (classical.some_spec hf.approximates_deriv_on_open_nhds).1

end has_strict_fderiv_at

/-- If `f` is a `local_homeomorph` between two normed vector spaces and `f`
has an invertible strict derivative `f'` at `a ∈ f.source`, then the inverse
function has strict derivative `f'.symm`. -/
theorem local_homeomorph.inv_fun_has_strict_fderiv_at (f : local_homeomorph E F)
  {a : E} (ha : a ∈ f.source) {f' : E ≃L[𝕜] F}
  (hf : has_strict_fderiv_at f.to_fun (f' : E →L[𝕜] F) a) :
  has_strict_fderiv_at f.inv_fun (f'.symm : F →L[𝕜] E) (f.to_fun a) :=
begin
  rw [has_strict_fderiv_at, (f.prod f).is_o_congr
    (mk_mem_prod (f.map_source ha) (f.map_source ha))],
  simp only [local_homeomorph.prod_to_local_equiv, continuous_linear_equiv.coe_apply,
    local_equiv.prod_inv_fun, local_equiv.prod_to_fun, f.left_inv ha, (∘)],
  suffices : is_o (λ (p : E × E), f'.symm (f' (p.fst - p.snd) - (f.to_fun p.fst - f.to_fun p.snd)))
    (λ (p : E × E), f.to_fun p.fst - f.to_fun p.snd) (𝓝 (a, a)),
  { refine this.congr' _ (eventually_of_forall _ $ λ _, rfl),
    filter_upwards [continuous_fst.tendsto (a, a) (f.eventually_left_inverse ha),
      continuous_snd.tendsto (a, a) (f.eventually_left_inverse ha)],
    simp only [mem_set_of_eq, mem_preimage],
    intros,
    simp only [*, continuous_linear_equiv.map_sub, f'.symm_apply_apply] },
  suffices : is_o (λ (p : E × E), (f' (p.fst - p.snd) - (f.to_fun p.fst - f.to_fun p.snd)))
    (λ (p : E × E), f.to_fun p.fst - f.to_fun p.snd) (𝓝 (a, a)),
  from (f'.symm.to_continuous_linear_map.is_O_comp _ _).trans_is_o this,
  refine (hf.trans_is_O _).symm,
  rcases hf.approximates_deriv_on_open_nhds with ⟨s, has, hs, H⟩,
  have := H.antilipschitz ((subsingleton_or_exists_ne (0:E)).imp id $
    λ hE, nnreal.half_lt_self $ ne_of_gt $ nnreal.inv_pos.2 $ f'.norm_symm_pos hE),
  exact ⟨_, eventually.mono (mem_nhds_sets (is_open_prod hs hs) (mk_mem_prod has has)) $
    λ p hp, by { simp only [← dist_eq_norm], exact this.le_mul_dist ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩ }⟩
end

theorem has_strict_fderiv_at.inv_fun_has_strict_fderiv_at [complete_space E] {f : E → F}
  {f' : E ≃L[𝕜] F} {a : E} (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  has_strict_fderiv_at (hf.to_local_homeomorph f).inv_fun (f'.symm : F →L[𝕜] E) (f a) :=
(hf.to_local_homeomorph f).inv_fun_has_strict_fderiv_at hf.mem_to_local_homeomorph_source hf
