/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov.
-/
import analysis.calculus.deriv
import topology.local_homeomorph
import topology.metric_space.contracting

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `x`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `has_strict_deriv_at.to_local_homeomorph` that repacks a function `f`
with a `hf : has_strict_deriv_at f f' x`, `f' : E ≃L[𝕜] F`, into a `local_homeomorph`.
The `to_fun` of this `local_homeomorph` is `defeq` to `f`, so one can apply theorems
about `local_homeomorph` to `hf.to_local_homeomorph f`, and get statements about `f`.

We also prove that for `f : local_homeomorph E F` that has a strict derivative `f' : E ≃L[𝕜] F`
at a point `a ∈ f.source`, then its `f.inv_fun` has strict derivative `f'.symm`, then apply
it to `hf.to_local_homeomorph f` to get a similar statement about `hf.to_local_homeomorph f`.

Finally, we prove Implicit function theorem.
-/

open function set filter metric
open_locale topological_space classical nnreal

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_group G'] [normed_space 𝕜 G']

open asymptotics filter metric set
open continuous_linear_map (id)

/-- We say that `f` approximates continuous linear map `f'` on `s` with constant `c`,
if `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` whenever `x, y ∈ s`.

This predicate is defined to faciliate splitting of the inverse function theorem into small lemmas.
Some of these lemmas can be useful, e.g., to prove that the inverse function is defined
on a specific set. -/
def approximates_linear_on (f : E → F) (f' : E →L[𝕜] F) (s : set E) (c : ℝ≥0) : Prop :=
∀ (x ∈ s) (y ∈ s), ∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥

namespace approximates_linear_on

variables [cs : complete_space E] {f : E → F}

section

variables {f' : E →L[𝕜] F} {s t : set E} {c c' : ℝ≥0}

theorem mono_num (hc : c ≤ c') (hf : approximates_linear_on f f' s c) :
  approximates_linear_on f f' s c' :=
λ x hx y hy, le_trans (hf x hx y hy) (mul_le_mul_of_nonneg_right hc $ norm_nonneg _)

theorem mono_set (hst : s ⊆ t) (hf : approximates_linear_on f f' t c) :
  approximates_linear_on f f' s c :=
λ x hx y hy, hf x (hst hx) y (hst hy)

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
    exact antilipschitz_with.of_subsingleton },
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
def to_local_equiv : local_equiv E F :=
by haveI : nonempty E := ⟨0⟩; exact (hf.inj_on hc).to_local_equiv _ _

/-- Inverse function is continuous on `f '' s`. Use properties of `local_homeomorph` instead. -/
lemma inverse_continuous_on : continuous_on (hf.to_local_equiv hc).inv_fun (f '' s) :=
continuous_on_iff_continuous_restrict.2 $
  ((hf.antilipschitz hc).to_right_inv_on' (hf.to_local_equiv hc).map_target
    (hf.to_local_equiv hc).right_inv).continuous

omit hf hc

section

variables (f f')

/-- Iterations of this map converge to `f⁻¹ y`. The formula is very similar to the one
used in Newton's method but we use the same `f'.symm` for all `y` instead of evaluating
the derivative at each point along the orbit. -/
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

include hf

lemma inverse_approx_map_contracts_on {x x'} (hx : x ∈ s) (hx' : x' ∈ s) :
  dist (g x) (g x') ≤ N * c * dist x x' :=
begin
  rw [dist_eq_norm, dist_eq_norm, inverse_approx_map_sub, norm_sub_rev],
  suffices : ∥f'.symm (f x - f x' - f' (x - x'))∥ ≤ N * (c * ∥x - x'∥),
    by simpa only [f'.symm.map_sub, f'.symm_apply_apply, mul_assoc] using this,
  exact (f'.symm : F →L[𝕜] E).le_op_norm_of_le (hf x hx x' hx')
end

include hc

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
    add_le_add (hf.inverse_approx_map_contracts_on y (hε hx) hb)
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
        y (hε x.mem) (hε x'.mem)) } },
  refine ⟨this.efixed_point' _ _ _ b (mem_closed_ball_self ε0) (edist_lt_top _ _), _, _⟩,
  { exact is_complete_of_is_closed is_closed_ball },
  { apply contracting_with.efixed_point_mem' },
  { exact (inverse_approx_map_fixed_iff y).1 (this.efixed_point_is_fixed' _ _ _ _) }
end

section

variables (f s)

/-- Given a function `f` that approximates a linear equivalence on an open set `s`,
returns a local homeomorph with `to_fun = f` and `source = s`. -/
def to_local_homeomorph (hs : is_open s) : local_homeomorph E F :=
{ to_local_equiv := hf.to_local_equiv hc,
    open_source := hs,
    open_target :=
      begin
        cases hc with hE hc,
        { resetI,
          haveI hF : subsingleton F := f'.to_linear_equiv.to_equiv.symm.subsingleton,
          apply is_open_discrete },
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

lemma closed_ball_subset_target (hs : is_open s) {b : E} (ε0 : 0 ≤ ε) (hε : closed_ball b ε ⊆ s) :
  closed_ball (f b) ((N⁻¹ - c) * ε) ⊆ (hf.to_local_homeomorph f s hc hs).target :=
(hf.surj_on_closed_ball hc ε0 hε).mono hε (subset.refl _)

end approximates_linear_on

namespace has_strict_fderiv_at

section
variables {f : E → F} {f' : E →L[𝕜] F} {a : E}

/-- If `f` has derivative `f'` at `a` in strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
lemma approximates_deriv_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E}
  (hf : has_strict_fderiv_at f f' a) {c : ℝ≥0} (hc : subsingleton E ∨ 0 < c) :
  ∃ s ∈ 𝓝 a, approximates_linear_on f f' s c :=
begin
  cases hc with hE hc,
  { refine ⟨univ, mem_nhds_sets is_open_univ trivial, λ x hx y hy, _⟩,
    simp [@subsingleton.elim E hE x y] },
  have := hf.def hc,
  rw [nhds_prod_eq, filter.eventually, mem_prod_same_iff] at this,
  rcases this with ⟨s, has, hs⟩,
  exact ⟨s, has, λ x hx y hy, hs (mk_mem_prod hx hy)⟩
end

end

variables [cs : complete_space E] {f : E → F} (f' : E ≃L[𝕜] F) {a : E}
  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a)

variable {f'}
include hf

lemma approximates_deriv_on_open_nhds :
  ∃ (s : set E) (hs :  a ∈ s ∧ is_open s),
    approximates_linear_on f (f' : E →L[𝕜] F) s ((nnnorm (f'.symm : F →L[𝕜] E))⁻¹ / 2) :=
begin
  refine ((nhds_basis_opens a).exists_iff _).1 _,
  exact (λ s t, approximates_linear_on.mono_set),
  exact (hf.approximates_deriv_on_nhds $ f'.subsingleton_or_nnnorm_symm_pos.imp id $
    λ hf', nnreal.half_pos $ nnreal.inv_pos.2 $ hf')
end

include cs

variable (f)

/-- Given a function with a bijective strict derivative at `a`, returns a `local_homeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `local_homeomorph.inv_fun_has_strict_fderiv_at` states that the inverse function
of this `local_homeomorph` has derivative `f'.symm`. -/
def to_local_homeomorph : local_homeomorph E F :=
approximates_linear_on.to_local_homeomorph f
  (classical.some hf.approximates_deriv_on_open_nhds)
  (classical.some_spec hf.approximates_deriv_on_open_nhds).snd
  (f'.subsingleton_or_nnnorm_symm_pos.imp id $ λ hf', nnreal.half_lt_self $ ne_of_gt $
    nnreal.inv_pos.2 $ hf')
  (classical.some_spec hf.approximates_deriv_on_open_nhds).fst.2

variable {f}

@[simp] lemma to_local_homeomorph_to_fun : (hf.to_local_homeomorph f).to_fun = f := rfl

lemma mem_to_local_homeomorph_source : a ∈ (hf.to_local_homeomorph f).source :=
  (classical.some_spec hf.approximates_deriv_on_open_nhds).fst.1

variables (f f' a)

/-- Given a function `f` with an invertible derivative, returns a function that is locally inverse
to `f`. -/
def local_inverse : F → E := (hf.to_local_homeomorph f).inv_fun

variables {f f' a}

lemma eventually_left_inverse : ∀ᶠ x in 𝓝 a, hf.local_inverse f f' a (f x) = x :=
(hf.to_local_homeomorph f).eventually_left_inverse hf.mem_to_local_homeomorph_source

lemma eventually_right_inverse : ∀ᶠ y in 𝓝 (f a), f (hf.local_inverse f f' a y) = y :=
(hf.to_local_homeomorph f).eventually_right_inverse' hf.mem_to_local_homeomorph_source

/-- If `f` has an invertible derivative `f'` at `a` in the sense of strict differentiability `(hf)`,
then the inverse function `hf.local_inverse f` has derivative `f'.symm` at `f a`. -/
theorem to_local_inverse :
  has_strict_fderiv_at (hf.local_inverse f f' a) (f'.symm : F →L[𝕜] E) (f a) :=
begin
  dunfold local_inverse,
  set e := hf.to_local_homeomorph f,
  have ha := hf.mem_to_local_homeomorph_source,
  refine ((e.prod e).is_o_congr (mk_mem_prod (e.map_source ha) (e.map_source ha))).2 _,
  simp only [local_homeomorph.prod_to_local_equiv, continuous_linear_equiv.coe_apply,
    local_equiv.prod_inv_fun, local_equiv.prod_to_fun, e.left_inv ha, (∘)],
  suffices : is_o (λ (p : E × E), f'.symm (f' (p.fst - p.snd) - (e.to_fun p.fst - e.to_fun p.snd)))
    (λ (p : E × E), e.to_fun p.fst - e.to_fun p.snd) (𝓝 (a, a)),
  { refine this.congr' _ (eventually_of_forall _ $ λ _, rfl),
    filter_upwards [continuous_fst.tendsto (a, a) (e.eventually_left_inverse ha),
      continuous_snd.tendsto (a, a) (e.eventually_left_inverse ha)],
    simp only [mem_set_of_eq, mem_preimage],
    intros,
    simp only [*, continuous_linear_equiv.map_sub, f'.symm_apply_apply] },
  suffices : is_o (λ (p : E × E), (f' (p.fst - p.snd) - (f p.fst - f p.snd)))
    (λ (p : E × E), f p.fst - f p.snd) (𝓝 (a, a)),
  from (f'.symm.to_continuous_linear_map.is_O_comp _ _).trans_is_o this,
  refine (hf.trans_is_O _).symm,
  rcases hf.approximates_deriv_on_open_nhds with ⟨s, ⟨has, hs⟩, H⟩,
  have := H.antilipschitz (f'.subsingleton_or_nnnorm_symm_pos.imp id $
    λ hf', nnreal.half_lt_self $ ne_of_gt $ nnreal.inv_pos.2 $ hf'),
  exact is_O.of_bound this.K
    (eventually.mono (mem_nhds_sets (is_open_prod hs hs) (mk_mem_prod has has)) $
      λ p hp, by { simp only [← dist_eq_norm], exact this.le_mul_dist ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩ })
end

/-- If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict differentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at `f a`. -/
theorem to_local_inverse' {g : F → E} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
  has_strict_fderiv_at g (f'.symm : F →L[𝕜] E) (f a) :=
begin
  apply hf.to_local_inverse.congr_of_mem_sets,
  have := ((hf.to_local_homeomorph f).inv_fun_tendsto
    hf.mem_to_local_homeomorph_source).eventually hg,
  refine this.mp (hf.eventually_right_inverse.mono $ λ y hy hy', _),
  exact hy'.symm.trans (congr_arg g hy)
end

end has_strict_fderiv_at

open continuous_linear_map (fst snd subtype_val smul_right)

namespace has_strict_fderiv_at

variables [cs : complete_space E] {f : E → F} {f' : E →L[𝕜] F} {f'inv : F →L[𝕜] E}
  {a : E} (hf : has_strict_fderiv_at f f' a) (hf' : right_inverse f'inv f')

include hf hf'

lemma implicit_aux_has_fderiv :
  has_strict_fderiv_at
    (λ x, (f x, continuous_linear_map.proj_ker_of_right_inverse f' f'inv hf' (x - a)))
    (continuous_linear_equiv.equiv_of_right_inverse f' f'inv hf' : E →L[𝕜] (F × f'.ker)) a :=
hf.prod $ (continuous_linear_map.has_strict_fderiv_at _).comp a
  ((has_strict_fderiv_at_id a).sub_const a)

include cs

section defs

variables (f f' f'inv)

/-- A local homeomorphism between E` and `f'.ker × F` sending level surfaces of `f`
to horizontal subspaces. -/
def implicit_to_local_homeomorph : local_homeomorph E (F × f'.ker) :=
(hf.implicit_aux_has_fderiv hf').to_local_homeomorph _

/-- Implicit function `g` defined by `f (g y x) = y`. -/
def implicit_function : F → f'.ker → E :=
function.curry $ (hf.implicit_aux_has_fderiv hf').local_inverse _ _ _

end defs

@[simp] lemma implicit_to_local_homeomorph_fst (x : E) :
  ((hf.implicit_to_local_homeomorph f f' f'inv  hf').to_fun x).fst = f x :=
rfl

@[simp] lemma implicit_to_local_homeomorph_ker_snd (x : f'.ker) :
  ((hf.implicit_to_local_homeomorph f f' f'inv hf').to_fun (x + a)).snd = x :=
by simpa only [implicit_to_local_homeomorph, to_local_homeomorph_to_fun, add_sub_cancel]
  using (continuous_linear_map.proj_ker_of_right_inverse_apply_idem _ _ hf' x)

@[simp] lemma implicit_to_local_homeomorph_self :
  (hf.implicit_to_local_homeomorph f f' f'inv hf').to_fun a = (f a, 0) :=
prod.ext rfl $ by simpa using hf.implicit_to_local_homeomorph_ker_snd hf' 0

lemma mem_implicit_to_local_homeomorph_source :
  a ∈ (hf.implicit_to_local_homeomorph f f' f'inv hf').source :=
mem_to_local_homeomorph_source _

lemma mem_implicit_to_local_homeomorph_target :
  (f a, (0 : f'.ker)) ∈ (hf.implicit_to_local_homeomorph f f' f'inv hf').target :=
by simpa only [implicit_to_local_homeomorph_self] using
  ((hf.implicit_to_local_homeomorph f f' f'inv hf').map_source $
    (hf.mem_implicit_to_local_homeomorph_source hf'))

/-- `implicit_function` sends `(z, y)` to a point in `f ⁻¹' z`. -/
lemma map_implicit_function_eq :
  ∀ᶠ p in 𝓝 (f a, (0 : f'.ker)),
    f (hf.implicit_function f f' f'inv hf' (p : F × f'.ker).1 p.2) = p.1 :=
((hf.implicit_to_local_homeomorph f f' f'inv hf').eventually_right_inverse $
  hf.mem_implicit_to_local_homeomorph_target hf').mono $ λ ⟨z, y⟩ h,
    congr_arg prod.fst h

/-- Any point in some neighborhood of `a` can be represented as `implicit_function`
of some point. -/
lemma eq_implicit_function :
  ∀ᶠ x in 𝓝 a, hf.implicit_function f f' f'inv hf' (f x)
    ((hf.implicit_to_local_homeomorph f f' f'inv hf').to_fun x).snd = x :=
(hf.implicit_aux_has_fderiv hf').eventually_left_inverse

/-- Derivative of the inverse function used to prove the implicit function theorem. -/
lemma to_implicit_function_aux :
  has_strict_fderiv_at (hf.implicit_to_local_homeomorph f f' f'inv hf').inv_fun
    (f'inv.coprod $ subtype_val f'.ker) (f a, 0) :=
hf.implicit_to_local_homeomorph_self hf' ▸
  (hf.implicit_aux_has_fderiv hf').to_local_inverse

lemma to_implicit_function :
  has_strict_fderiv_at (hf.implicit_function f f' f'inv hf' (f a)) (subtype_val f'.ker) 0 :=
begin
  have := (hf.to_implicit_function_aux hf').comp 0
    ((has_strict_fderiv_at_const (f a) 0).prod $ has_strict_fderiv_at_id 0),
  convert this,
  ext x,
  simp
end

end has_strict_fderiv_at

namespace has_strict_fderiv_at

variables [cs : complete_space (E × F)] {f : E × F → G} (f' : E × F →L[𝕜] G) (f'inv : G →L[𝕜] F)
  {p : E × F} (hf : has_strict_fderiv_at f f' p)
  (hf'l : ∀ y : F, f'inv (f' (0, y)) = y) (hf'r : ∀ z : G, f' (0, f'inv z) = z)

/-- Formula for the derivative of an implicit function. -/
def prod_implicit_function_fderiv : (E × G) →L[𝕜] F :=
(f'inv.comp $ continuous_linear_map.snd 𝕜 E G -
      f'.comp ((continuous_linear_map.id 𝕜 E).prod_map 0))

variables {f' f'inv}

@[simp] lemma prod_implicit_function_fderiv_apply (x) :
  prod_implicit_function_fderiv f' f'inv x = f'inv (x.2 - f' (x.1, 0)) := rfl

include hf'r

lemma prod_implicit_fderiv_right_inverse (x : E) (z : G) :
  f' (x, f'inv z) = f' (x, 0) + z :=
by { conv_rhs { rw [← hf'r z] }, simp [← f'.map_add] }

include hf'l

variables (f' f'inv)

/-- Derivative of an auxiliary function used in the proof of the implicit function theorem. -/
def prod_implicit_function_aux_fderiv : (E × F) ≃L[𝕜] (E × G) :=
continuous_linear_equiv.equiv_of_inverse
  ((continuous_linear_map.fst 𝕜 E F).prod f')
  ((continuous_linear_map.fst 𝕜 E G).prod $ prod_implicit_function_fderiv f' f'inv)
  (λ ⟨x, y⟩, by simp [← continuous_linear_map.map_sub, hf'l])
  (λ ⟨x, z⟩, by simp [-continuous_linear_map.map_sub, prod_implicit_fderiv_right_inverse hf'r])

variables {f' f'inv}

include hf

lemma prod_implicit_function_aux_deriv :
  has_strict_fderiv_at (λ x : E × F, (x.1, f x))
    (prod_implicit_function_aux_fderiv f' f'inv hf'l hf'r : (E × F) →L[𝕜] E × G) p :=
has_strict_fderiv_at_fst.prod hf

include cs
variable (f)

/-- Implicit function `g` defined by an equation `f (x, g(x, y)) = z`. -/
def prod_implicit_function (x : E × G) : F :=
((hf.prod_implicit_function_aux_deriv hf'l hf'r).local_inverse _ _ _ x).2

lemma prod_implicit_function_def (x : E × G) :
  hf.prod_implicit_function f hf'l hf'r x =
    ((hf.prod_implicit_function_aux_deriv hf'l hf'r).local_inverse _ _ _ x).2 :=
rfl

lemma to_prod_implicit_function :
  has_strict_fderiv_at (hf.prod_implicit_function f hf'l hf'r)
    (prod_implicit_function_fderiv f' f'inv) (p.1, f p) :=
((hf.prod_implicit_function_aux_deriv hf'l hf'r).to_local_inverse).snd

lemma eventually_apply_fst_prod_implicit_function_eq :
  ∀ᶠ x in 𝓝 (p.1, f p), f ((x : E × G).1, hf.prod_implicit_function f hf'l hf'r x) = x.2 :=
(hf.prod_implicit_function_aux_deriv hf'l hf'r).eventually_right_inverse.mono $
  λ x hx, by { convert congr_arg prod.snd hx, convert prod.mk.eta,
    exact (congr_arg prod.fst hx).symm }

lemma eventually_prod_implicit_function_eq :
  ∀ᶠ x in 𝓝 p, hf.prod_implicit_function f hf'l hf'r ((x : E × F).1, f x) = x.2 :=
(hf.prod_implicit_function_aux_deriv hf'l hf'r).eventually_left_inverse.mono $
  λ x hx, congr_arg prod.snd hx

end has_strict_fderiv_at

namespace has_strict_deriv_at

variables [cs : complete_space 𝕜] {f : 𝕜 → 𝕜} {f' a : 𝕜} (hf : has_strict_deriv_at f f' a)
  (hf' : f' ≠ 0)

lemma has_strict_fderiv_at' :
  has_strict_fderiv_at f
    (continuous_linear_equiv.units_equiv_aut 𝕜 (units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) a :=
hf

include cs

variables (f f' a)

/-- A function that is inverse to `f` near `a`. -/
@[reducible] def local_inverse : 𝕜 → 𝕜 := (hf.has_strict_fderiv_at' hf').local_inverse _ _ _

variables {f f' a}

theorem to_local_inverse : has_strict_deriv_at (hf.local_inverse f f' a hf') f'⁻¹ (f a) :=
(hf.has_strict_fderiv_at' hf').to_local_inverse

theorem to_local_inverse' {g : 𝕜 → 𝕜} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
  has_strict_deriv_at g f'⁻¹ (f a) :=
(hf.has_strict_fderiv_at' hf').to_local_inverse' hg

end has_strict_deriv_at
