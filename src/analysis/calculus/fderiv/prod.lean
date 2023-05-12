/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.fderiv.linear
import analysis.calculus.fderiv.comp

open filter asymptotics continuous_linear_map set metric
open_locale topology classical nnreal filter asymptotics ennreal

noncomputable theory


section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']

variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}

section cartesian_product
/-! ### Derivative of the cartesian product of two functions -/

section prod
variables {f₂ : E → G} {f₂' : E →L[𝕜] G}

protected lemma has_strict_fderiv_at.prod
  (hf₁ : has_strict_fderiv_at f₁ f₁' x) (hf₂ : has_strict_fderiv_at f₂ f₂' x) :
  has_strict_fderiv_at (λx, (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
hf₁.prod_left hf₂

lemma has_fderiv_at_filter.prod
  (hf₁ : has_fderiv_at_filter f₁ f₁' x L) (hf₂ : has_fderiv_at_filter f₂ f₂' x L) :
  has_fderiv_at_filter (λx, (f₁ x, f₂ x)) (f₁'.prod f₂') x L :=
hf₁.prod_left hf₂

lemma has_fderiv_within_at.prod
  (hf₁ : has_fderiv_within_at f₁ f₁' s x) (hf₂ : has_fderiv_within_at f₂ f₂' s x) :
  has_fderiv_within_at (λx, (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
hf₁.prod hf₂

lemma has_fderiv_at.prod (hf₁ : has_fderiv_at f₁ f₁' x) (hf₂ : has_fderiv_at f₂ f₂' x) :
  has_fderiv_at (λx, (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
hf₁.prod hf₂

lemma has_fderiv_at_prod_mk_left (e₀ : E) (f₀ : F) :
  has_fderiv_at (λ e : E, (e, f₀)) (inl 𝕜 E F) e₀ :=
(has_fderiv_at_id e₀).prod (has_fderiv_at_const f₀ e₀)

lemma has_fderiv_at_prod_mk_right (e₀ : E) (f₀ : F) :
  has_fderiv_at (λ f : F, (e₀, f)) (inr 𝕜 E F) f₀ :=
(has_fderiv_at_const e₀ f₀).prod (has_fderiv_at_id f₀)

lemma differentiable_within_at.prod
  (hf₁ : differentiable_within_at 𝕜 f₁ s x) (hf₂ : differentiable_within_at 𝕜 f₂ s x) :
  differentiable_within_at 𝕜 (λx:E, (f₁ x, f₂ x)) s x :=
(hf₁.has_fderiv_within_at.prod hf₂.has_fderiv_within_at).differentiable_within_at

@[simp]
lemma differentiable_at.prod (hf₁ : differentiable_at 𝕜 f₁ x) (hf₂ : differentiable_at 𝕜 f₂ x) :
  differentiable_at 𝕜 (λx:E, (f₁ x, f₂ x)) x :=
(hf₁.has_fderiv_at.prod hf₂.has_fderiv_at).differentiable_at

lemma differentiable_on.prod (hf₁ : differentiable_on 𝕜 f₁ s) (hf₂ : differentiable_on 𝕜 f₂ s) :
  differentiable_on 𝕜 (λx:E, (f₁ x, f₂ x)) s :=
λx hx, differentiable_within_at.prod (hf₁ x hx) (hf₂ x hx)

@[simp]
lemma differentiable.prod (hf₁ : differentiable 𝕜 f₁) (hf₂ : differentiable 𝕜 f₂) :
  differentiable 𝕜 (λx:E, (f₁ x, f₂ x)) :=
λ x, differentiable_at.prod (hf₁ x) (hf₂ x)

lemma differentiable_at.fderiv_prod
  (hf₁ : differentiable_at 𝕜 f₁ x) (hf₂ : differentiable_at 𝕜 f₂ x) :
  fderiv 𝕜 (λx:E, (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).prod (fderiv 𝕜 f₂ x) :=
(hf₁.has_fderiv_at.prod hf₂.has_fderiv_at).fderiv

lemma differentiable_at.fderiv_within_prod
  (hf₁ : differentiable_within_at 𝕜 f₁ s x) (hf₂ : differentiable_within_at 𝕜 f₂ s x)
  (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx:E, (f₁ x, f₂ x)) s x =
    (fderiv_within 𝕜 f₁ s x).prod (fderiv_within 𝕜 f₂ s x) :=
(hf₁.has_fderiv_within_at.prod hf₂.has_fderiv_within_at).fderiv_within hxs

end prod

section fst

variables {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

lemma has_strict_fderiv_at_fst : has_strict_fderiv_at (@prod.fst E F) (fst 𝕜 E F) p :=
(fst 𝕜 E F).has_strict_fderiv_at

protected lemma has_strict_fderiv_at.fst (h : has_strict_fderiv_at f₂ f₂' x) :
  has_strict_fderiv_at (λ x, (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
has_strict_fderiv_at_fst.comp x h

lemma has_fderiv_at_filter_fst {L : filter (E × F)} :
  has_fderiv_at_filter (@prod.fst E F) (fst 𝕜 E F) p L :=
(fst 𝕜 E F).has_fderiv_at_filter

protected lemma has_fderiv_at_filter.fst (h : has_fderiv_at_filter f₂ f₂' x L) :
  has_fderiv_at_filter (λ x, (f₂ x).1) ((fst 𝕜 F G).comp f₂') x L :=
has_fderiv_at_filter_fst.comp x h tendsto_map

lemma has_fderiv_at_fst : has_fderiv_at (@prod.fst E F) (fst 𝕜 E F) p :=
has_fderiv_at_filter_fst

protected lemma has_fderiv_at.fst (h : has_fderiv_at f₂ f₂' x) :
  has_fderiv_at (λ x, (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
h.fst

lemma has_fderiv_within_at_fst {s : set (E × F)} :
  has_fderiv_within_at (@prod.fst E F) (fst 𝕜 E F) s p :=
has_fderiv_at_filter_fst

protected lemma has_fderiv_within_at.fst (h : has_fderiv_within_at f₂ f₂' s x) :
  has_fderiv_within_at (λ x, (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
h.fst

lemma differentiable_at_fst : differentiable_at 𝕜 prod.fst p :=
has_fderiv_at_fst.differentiable_at

@[simp] protected lemma differentiable_at.fst (h : differentiable_at 𝕜 f₂ x) :
  differentiable_at 𝕜 (λ x, (f₂ x).1) x :=
differentiable_at_fst.comp x h

lemma differentiable_fst : differentiable 𝕜 (prod.fst : E × F → E) :=
λ x, differentiable_at_fst

@[simp] protected lemma differentiable.fst (h : differentiable 𝕜 f₂) :
  differentiable 𝕜 (λ x, (f₂ x).1) :=
differentiable_fst.comp h

lemma differentiable_within_at_fst {s : set (E × F)} : differentiable_within_at 𝕜 prod.fst s p :=
differentiable_at_fst.differentiable_within_at

protected lemma differentiable_within_at.fst (h : differentiable_within_at 𝕜 f₂ s x) :
  differentiable_within_at 𝕜 (λ x, (f₂ x).1) s x :=
differentiable_at_fst.comp_differentiable_within_at x h

lemma differentiable_on_fst {s : set (E × F)} : differentiable_on 𝕜 prod.fst s :=
differentiable_fst.differentiable_on

protected lemma differentiable_on.fst (h : differentiable_on 𝕜 f₂ s) :
  differentiable_on 𝕜 (λ x, (f₂ x).1) s :=
differentiable_fst.comp_differentiable_on h

lemma fderiv_fst : fderiv 𝕜 prod.fst p = fst 𝕜 E F := has_fderiv_at_fst.fderiv

lemma fderiv.fst (h : differentiable_at 𝕜 f₂ x) :
  fderiv 𝕜 (λ x, (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
h.has_fderiv_at.fst.fderiv

lemma fderiv_within_fst {s : set (E × F)} (hs : unique_diff_within_at 𝕜 s p) :
  fderiv_within 𝕜 prod.fst s p = fst 𝕜 E F :=
has_fderiv_within_at_fst.fderiv_within hs

lemma fderiv_within.fst (hs : unique_diff_within_at 𝕜 s x) (h : differentiable_within_at 𝕜 f₂ s x) :
  fderiv_within 𝕜 (λ x, (f₂ x).1) s x = (fst 𝕜 F G).comp (fderiv_within 𝕜 f₂ s x) :=
h.has_fderiv_within_at.fst.fderiv_within hs

end fst

section snd

variables {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

lemma has_strict_fderiv_at_snd : has_strict_fderiv_at (@prod.snd E F) (snd 𝕜 E F) p :=
(snd 𝕜 E F).has_strict_fderiv_at

protected lemma has_strict_fderiv_at.snd (h : has_strict_fderiv_at f₂ f₂' x) :
  has_strict_fderiv_at (λ x, (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
has_strict_fderiv_at_snd.comp x h

lemma has_fderiv_at_filter_snd {L : filter (E × F)} :
  has_fderiv_at_filter (@prod.snd E F) (snd 𝕜 E F) p L :=
(snd 𝕜 E F).has_fderiv_at_filter

protected lemma has_fderiv_at_filter.snd (h : has_fderiv_at_filter f₂ f₂' x L) :
  has_fderiv_at_filter (λ x, (f₂ x).2) ((snd 𝕜 F G).comp f₂') x L :=
has_fderiv_at_filter_snd.comp x h tendsto_map

lemma has_fderiv_at_snd : has_fderiv_at (@prod.snd E F) (snd 𝕜 E F) p :=
has_fderiv_at_filter_snd

protected lemma has_fderiv_at.snd (h : has_fderiv_at f₂ f₂' x) :
  has_fderiv_at (λ x, (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
h.snd

lemma has_fderiv_within_at_snd {s : set (E × F)} :
  has_fderiv_within_at (@prod.snd E F) (snd 𝕜 E F) s p :=
has_fderiv_at_filter_snd

protected lemma has_fderiv_within_at.snd (h : has_fderiv_within_at f₂ f₂' s x) :
  has_fderiv_within_at (λ x, (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
h.snd

lemma differentiable_at_snd : differentiable_at 𝕜 prod.snd p :=
has_fderiv_at_snd.differentiable_at

@[simp] protected lemma differentiable_at.snd (h : differentiable_at 𝕜 f₂ x) :
  differentiable_at 𝕜 (λ x, (f₂ x).2) x :=
differentiable_at_snd.comp x h

lemma differentiable_snd : differentiable 𝕜 (prod.snd : E × F → F) :=
λ x, differentiable_at_snd

@[simp] protected lemma differentiable.snd (h : differentiable 𝕜 f₂) :
  differentiable 𝕜 (λ x, (f₂ x).2) :=
differentiable_snd.comp h

lemma differentiable_within_at_snd {s : set (E × F)} : differentiable_within_at 𝕜 prod.snd s p :=
differentiable_at_snd.differentiable_within_at

protected lemma differentiable_within_at.snd (h : differentiable_within_at 𝕜 f₂ s x) :
  differentiable_within_at 𝕜 (λ x, (f₂ x).2) s x :=
differentiable_at_snd.comp_differentiable_within_at x h

lemma differentiable_on_snd {s : set (E × F)} : differentiable_on 𝕜 prod.snd s :=
differentiable_snd.differentiable_on

protected lemma differentiable_on.snd (h : differentiable_on 𝕜 f₂ s) :
  differentiable_on 𝕜 (λ x, (f₂ x).2) s :=
differentiable_snd.comp_differentiable_on h

lemma fderiv_snd : fderiv 𝕜 prod.snd p = snd 𝕜 E F := has_fderiv_at_snd.fderiv

lemma fderiv.snd (h : differentiable_at 𝕜 f₂ x) :
  fderiv 𝕜 (λ x, (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
h.has_fderiv_at.snd.fderiv

lemma fderiv_within_snd {s : set (E × F)} (hs : unique_diff_within_at 𝕜 s p) :
  fderiv_within 𝕜 prod.snd s p = snd 𝕜 E F :=
has_fderiv_within_at_snd.fderiv_within hs

lemma fderiv_within.snd (hs : unique_diff_within_at 𝕜 s x) (h : differentiable_within_at 𝕜 f₂ s x) :
  fderiv_within 𝕜 (λ x, (f₂ x).2) s x = (snd 𝕜 F G).comp (fderiv_within 𝕜 f₂ s x) :=
h.has_fderiv_within_at.snd.fderiv_within hs

end snd

section prod_map

variables {f₂ : G → G'} {f₂' : G →L[𝕜] G'} {y : G} (p : E × G)

protected theorem has_strict_fderiv_at.prod_map (hf : has_strict_fderiv_at f f' p.1)
  (hf₂ : has_strict_fderiv_at f₂ f₂' p.2) :
  has_strict_fderiv_at (prod.map f f₂) (f'.prod_map f₂') p :=
(hf.comp p has_strict_fderiv_at_fst).prod (hf₂.comp p has_strict_fderiv_at_snd)

protected theorem has_fderiv_at.prod_map (hf : has_fderiv_at f f' p.1)
  (hf₂ : has_fderiv_at f₂ f₂' p.2) :
  has_fderiv_at (prod.map f f₂) (f'.prod_map f₂') p :=
(hf.comp p has_fderiv_at_fst).prod (hf₂.comp p has_fderiv_at_snd)

@[simp] protected theorem differentiable_at.prod_map (hf : differentiable_at 𝕜 f p.1)
  (hf₂ : differentiable_at 𝕜 f₂ p.2) :
  differentiable_at 𝕜 (λ p : E × G, (f p.1, f₂ p.2)) p :=
(hf.comp p differentiable_at_fst).prod (hf₂.comp p differentiable_at_snd)

end prod_map

section pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has_*fderiv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `λ x i, φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `λ x, Φ x i` from
  differentiability of `Φ`.
-/

variables {ι : Type*} [fintype ι] {F' : ι → Type*} [Π i, normed_add_comm_group (F' i)]
  [Π i, normed_space 𝕜 (F' i)] {φ : Π i, E → F' i} {φ' : Π i, E →L[𝕜] F' i}
  {Φ : E → Π i, F' i} {Φ' : E →L[𝕜] Π i, F' i}

@[simp] lemma has_strict_fderiv_at_pi' :
  has_strict_fderiv_at Φ Φ' x ↔
    ∀ i, has_strict_fderiv_at (λ x, Φ x i) ((proj i).comp Φ') x :=
begin
  simp only [has_strict_fderiv_at, continuous_linear_map.coe_pi],
  exact is_o_pi
end

@[simp] lemma has_strict_fderiv_at_pi :
  has_strict_fderiv_at (λ x i, φ i x) (continuous_linear_map.pi φ') x ↔
    ∀ i, has_strict_fderiv_at (φ i) (φ' i) x :=
has_strict_fderiv_at_pi'

@[simp] lemma has_fderiv_at_filter_pi' :
  has_fderiv_at_filter Φ Φ' x L ↔
    ∀ i, has_fderiv_at_filter (λ x, Φ x i) ((proj i).comp Φ') x L :=
begin
  simp only [has_fderiv_at_filter, continuous_linear_map.coe_pi],
  exact is_o_pi
end

lemma has_fderiv_at_filter_pi :
  has_fderiv_at_filter (λ x i, φ i x) (continuous_linear_map.pi φ') x L ↔
    ∀ i, has_fderiv_at_filter (φ i) (φ' i) x L :=
has_fderiv_at_filter_pi'

@[simp] lemma has_fderiv_at_pi' :
  has_fderiv_at Φ Φ' x ↔
    ∀ i, has_fderiv_at (λ x, Φ x i) ((proj i).comp Φ') x :=
has_fderiv_at_filter_pi'

lemma has_fderiv_at_pi :
  has_fderiv_at (λ x i, φ i x) (continuous_linear_map.pi φ') x ↔
    ∀ i, has_fderiv_at (φ i) (φ' i) x :=
has_fderiv_at_filter_pi

@[simp] lemma has_fderiv_within_at_pi' :
  has_fderiv_within_at Φ Φ' s x ↔
    ∀ i, has_fderiv_within_at (λ x, Φ x i) ((proj i).comp Φ') s x :=
has_fderiv_at_filter_pi'

lemma has_fderiv_within_at_pi :
  has_fderiv_within_at (λ x i, φ i x) (continuous_linear_map.pi φ') s x ↔
    ∀ i, has_fderiv_within_at (φ i) (φ' i) s x :=
has_fderiv_at_filter_pi

@[simp] lemma differentiable_within_at_pi :
  differentiable_within_at 𝕜 Φ s x ↔
   ∀ i, differentiable_within_at 𝕜 (λ x, Φ x i) s x :=
⟨λ h i, (has_fderiv_within_at_pi'.1 h.has_fderiv_within_at i).differentiable_within_at,
  λ h, (has_fderiv_within_at_pi.2 (λ i, (h i).has_fderiv_within_at)).differentiable_within_at⟩

@[simp] lemma differentiable_at_pi :
  differentiable_at 𝕜 Φ x ↔ ∀ i, differentiable_at 𝕜 (λ x, Φ x i) x :=
⟨λ h i, (has_fderiv_at_pi'.1 h.has_fderiv_at i).differentiable_at,
  λ h, (has_fderiv_at_pi.2 (λ i, (h i).has_fderiv_at)).differentiable_at⟩

lemma differentiable_on_pi :
  differentiable_on 𝕜 Φ s ↔ ∀ i, differentiable_on 𝕜 (λ x, Φ x i) s :=
⟨λ h i x hx, differentiable_within_at_pi.1 (h x hx) i,
  λ h x hx, differentiable_within_at_pi.2 (λ i, h i x hx)⟩

lemma differentiable_pi :
  differentiable 𝕜 Φ ↔ ∀ i, differentiable 𝕜 (λ x, Φ x i) :=
⟨λ h i x, differentiable_at_pi.1 (h x) i, λ h x, differentiable_at_pi.2 (λ i, h i x)⟩

-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
lemma fderiv_within_pi (h : ∀ i, differentiable_within_at 𝕜 (φ i) s x)
  (hs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λ x i, φ i x) s x = pi (λ i, fderiv_within 𝕜 (φ i) s x) :=
(has_fderiv_within_at_pi.2 (λ i, (h i).has_fderiv_within_at)).fderiv_within hs

lemma fderiv_pi (h : ∀ i, differentiable_at 𝕜 (φ i) x) :
  fderiv 𝕜 (λ x i, φ i x) x = pi (λ i, fderiv 𝕜 (φ i) x) :=
(has_fderiv_at_pi.2 (λ i, (h i).has_fderiv_at)).fderiv

end pi

end cartesian_product

end
