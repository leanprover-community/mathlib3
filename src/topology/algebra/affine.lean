/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import linear_algebra.affine_space.affine_equiv
import linear_algebra.affine_space.midpoint
import topology.algebra.group
import topology.algebra.mul_action

/-!
# Topological properties of affine spaces and maps

For now, this contains only a few facts regarding the continuity of affine maps in the special
case when the point space and vector space are the same.

TODO: Deal with the case where the point spaces are different from the vector spaces. Note that
we do have some results in this direction under the assumption that the topologies are induced by
(semi)norms.
-/

open filter affine_map
open_locale topological_space

variables {α X : Type*} [topological_space X]

class topological_add_torsor (E : out_param Type*) [out_param (topological_space E)]
  [out_param (add_group E)] (P : Type*) [topological_space P]
  extends add_torsor E P,  has_continuous_vadd E P :=
(continuous_vsub : continuous (λ p : P × P, p.1 -ᵥ p.2))

@[priority 200]
instance topological_add_group.to_topological_add_torsor {G : Type*} [add_group G]
  [topological_space G] [topological_add_group G] : topological_add_torsor G G :=
⟨continuous_sub⟩

section add_torsor

variables {E P : Type*} [topological_space E] [add_group E] [topological_space P]
  [topological_add_torsor E P]

include E

lemma filter.tendsto.vsub {f g : α → P} {l : filter α} {x y : P} (hf : tendsto f l (𝓝 x))
  (hg : tendsto g l (𝓝 y)) : tendsto (λ x, f x -ᵥ g x) l (𝓝 (x -ᵥ y)) :=
(topological_add_torsor.continuous_vsub.tendsto (x, y)).comp (hf.prod_mk_nhds hg)

variables {f g : X → P} {s : set X} {a : X}

lemma continuous_at.vsub (hf : continuous_at f a) (hg : continuous_at g a) :
  continuous_at (λ x, f x -ᵥ g x) a :=
hf.vsub hg

lemma continuous_within_at.vsub (hf : continuous_within_at f s a)
  (hg : continuous_within_at g s a) : continuous_within_at (λ x, f x -ᵥ g x) s a :=
hf.vsub hg

lemma continuous_on.vsub (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ x, f x -ᵥ g x) s :=
λ a ha, (hf a ha).vsub (hg a ha)

@[continuity] lemma continuous.vsub (hf : continuous f) (hg : continuous g) :
  continuous (λ x, f x -ᵥ g x) :=
continuous.comp ‹topological_add_torsor E P›.continuous_vsub (hf.prod_mk hg)

section

variables (E P)
include P

lemma topological_add_torsor.to_topological_add_group : topological_add_group E :=
begin
  inhabit P,
  refine topological_add_group_iff_has_continuous_sub.2 ⟨_⟩,
  simpa only [← vadd_vsub_vadd_cancel_right _ _ (default : P)]
    using (continuous_fst.vadd continuous_const).vsub (continuous_snd.vadd continuous_const)
end

end

namespace homeomorph

/-- `equiv.vadd_const` as a homeomorphism. -/
@[simps {fully_applied := ff}] def vadd_const (p : P) : E ≃ₜ P :=
{ to_equiv := equiv.vadd_const p,
  continuous_to_fun := continuous_id.vadd continuous_const,
  continuous_inv_fun := continuous_id.vsub continuous_const }

/-- `equiv.const_vsub` as a homeomorphism. -/
@[simps {fully_applied := ff}] def const_vsub (p : P) : P ≃ₜ E :=
{ to_equiv := equiv.const_vsub p,
  continuous_to_fun := continuous_const.vsub continuous_id,
  continuous_inv_fun :=
    begin
      haveI := topological_add_torsor.to_topological_add_group E P,
      exact continuous_neg.vadd continuous_const
    end }

/-- `equiv.point_reflection` as a homeomorphism. -/
@[simps apply {fully_applied := ff}] def point_reflection (x : P) : P ≃ₜ P :=
(const_vsub x).trans (vadd_const x)

@[simp] lemma point_reflection_symm (x : P) : (point_reflection x).symm = point_reflection x :=
by { ext y, simp [point_reflection] }

variable (P)

/-- `equiv.const_vadd` as a homeomorphism. -/
@[simps {fully_applied := ff}] def const_vadd (v : E) : P ≃ₜ P :=
{ to_equiv := equiv.const_vadd P v,
  continuous_to_fun := continuous_const.vadd continuous_id,
  continuous_inv_fun := continuous_const.vadd continuous_id }

end homeomorph

end add_torsor

variables {R E PE F PF : Type*}
variables [add_comm_group E] [topological_space E] [topological_space PE]
  [topological_add_torsor E PE]
variables [add_comm_group F] [topological_space F] [topological_space PF]
  [topological_add_torsor F PF]

section ring

variables [ring R] [module R E] [module R F]
include E F

/-- The linear part of an affine map is continuous iff the affine map is continuous. -/
lemma affine_map.continuous_linear_iff (f : PE →ᵃ[R] PF) : continuous f.linear ↔ continuous f :=
begin
  inhabit PE,
  have : ⇑f.linear = (homeomorph.vadd_const (f default)).symm ∘ f ∘ (homeomorph.vadd_const default),
    from f.coe_linear default,
  rw [this, homeomorph.comp_continuous_iff, homeomorph.comp_continuous_iff']
end

variables [topological_space R] [has_continuous_smul R E]
omit F

lemma filter.tendsto.line_map {f₁ f₂ : α → PE} {g : α → R} {p₁ p₂ : PE} {c : R} {l : filter α}
  (h₁ : tendsto f₁ l (𝓝 p₁)) (h₂ : tendsto f₂ l (𝓝 p₂)) (hg : tendsto g l (𝓝 c)) :
  tendsto (λ x, line_map (f₁ x) (f₂ x) (g x)) l (𝓝 $ line_map p₁ p₂ c) :=
(hg.smul (h₂.vsub h₁)).vadd h₁

lemma continuous_at.line_map {f₁ f₂ : X → PE} {g : X → R} {a : X}
  (h₁ : continuous_at f₁ a) (h₂ : continuous_at f₂ a) (hg : continuous_at g a) :
  continuous_at (λ x, line_map (f₁ x) (f₂ x) (g x)) a :=
h₁.line_map h₂ hg

lemma continuous_within_at.line_map {f₁ f₂ : X → PE} {g : X → R} {s : set X} {a : X}
  (h₁ : continuous_within_at f₁ s a) (h₂ : continuous_within_at f₂ s a)
  (hg : continuous_within_at g s a) :
  continuous_within_at (λ x, line_map (f₁ x) (f₂ x) (g x)) s a :=
h₁.line_map h₂ hg

lemma continuous_on.line_map {f₁ f₂ : X → PE} {g : X → R} {s : set X}
  (h₁ : continuous_on f₁ s) (h₂ : continuous_on f₂ s) (hg : continuous_on g s) :
  continuous_on (λ x, line_map (f₁ x) (f₂ x) (g x)) s :=
λ a ha, (h₁ a ha).line_map (h₂ a ha) (hg a ha)

@[continuity] lemma continuous.line_map {f₁ f₂ : X → PE} {g : X → R} (h₁ : continuous f₁)
  (h₂ : continuous f₂) (hg : continuous g) :
  continuous (λ x, line_map (f₁ x) (f₂ x) (g x)) :=
(hg.smul (h₂.vsub h₁)).vadd h₁

end ring

section midpoint

variables [ring R] [invertible (2 : R)] [module R E] [has_continuous_const_smul R E]
include E

lemma filter.tendsto.midpoint {f g : α → PE} {l : filter α} {a b : PE} (hf : tendsto f l (𝓝 a))
  (hg : tendsto g l (𝓝 b)) :
  tendsto (λ x, midpoint R (f x) (g x)) l (𝓝 (midpoint R a b)) :=
((hg.vsub hf).const_smul _).vadd hf

variables {f g : X → PE} {s : set X} {a : X}

lemma continuous_at.midpoint (hf : continuous_at f a) (hg : continuous_at g a) :
  continuous_at (λ x, midpoint R (f x) (g x)) a :=
hf.midpoint hg

lemma continuous_within_at.midpoint (hf : continuous_within_at f s a)
  (hg : continuous_within_at g s a) :
  continuous_within_at (λ x, midpoint R (f x) (g x)) s a :=
hf.midpoint hg

lemma continuous_on.midpoint (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ x, midpoint R (f x) (g x)) s :=
λ a ha, (hf a ha).midpoint (hg a ha)

lemma continuous.midpoint (hf : continuous f) (hg : continuous g) :
  continuous (λ x, midpoint R (f x) (g x)) :=
continuous_iff_continuous_at.2 $ λ x, hf.continuous_at.midpoint hg.continuous_at

end midpoint

section midpoint

variables [ring R] [invertible (2 : R)] [module R E] [has_continuous_const_smul R E]
  [has_continuous_add E]
include E

lemma filter.tendsto.midpoint' {f g : α → E} {l : filter α} {a b : E} (hf : tendsto f l (𝓝 a))
  (hg : tendsto g l (𝓝 b)) :
  tendsto (λ x, midpoint R (f x) (g x)) l (𝓝 (midpoint R a b)) :=
by simpa only [midpoint_eq_smul_add] using (hf.add hg).const_smul _

variables {f g : X → E} {s : set X} {a : X}

lemma continuous_at.midpoint' (hf : continuous_at f a) (hg : continuous_at g a) :
  continuous_at (λ x, midpoint R (f x) (g x)) a :=
hf.midpoint' hg

lemma continuous_within_at.midpoint' (hf : continuous_within_at f s a)
  (hg : continuous_within_at g s a) :
  continuous_within_at (λ x, midpoint R (f x) (g x)) s a :=
hf.midpoint' hg

lemma continuous_on.midpoint' (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ x, midpoint R (f x) (g x)) s :=
λ a ha, (hf a ha).midpoint' (hg a ha)

lemma continuous.midpoint' (hf : continuous f) (hg : continuous g) :
  continuous (λ x, midpoint R (f x) (g x)) :=
continuous_iff_continuous_at.2 $ λ x, hf.continuous_at.midpoint' hg.continuous_at

end midpoint

section homothety

variables [topological_space R] [comm_ring R] [module R E] [has_continuous_smul R E]
include E

lemma filter.tendsto.homothety {f₁ f₂ : α → PE} {g : α → R} {p₁ p₂ : PE} {c : R} {l : filter α}
  (h₁ : tendsto f₁ l (𝓝 p₁)) (hg : tendsto g l (𝓝 c)) (h₂ : tendsto f₂ l (𝓝 p₂)) :
  tendsto (λ x, homothety (f₁ x) (g x) (f₂ x)) l (𝓝 $ homothety p₁ c p₂) :=
h₁.line_map h₂ hg

lemma continuous_at.homothety {f₁ f₂ : X → PE} {g : X → R} {a : X}
  (h₁ : continuous_at f₁ a) (hg : continuous_at g a) (h₂ : continuous_at f₂ a) :
  continuous_at (λ x, homothety (f₁ x) (g x) (f₂ x)) a :=
h₁.homothety hg h₂

lemma continuous_within_at.homothety {f₁ f₂ : X → PE} {g : X → R} {s : set X} {a : X}
  (h₁ : continuous_within_at f₁ s a) (hg : continuous_within_at g s a)
  (h₂ : continuous_within_at f₂ s a) :
  continuous_within_at (λ x, homothety (f₁ x) (g x) (f₂ x)) s a :=
h₁.homothety hg h₂

lemma continuous_on.homothety {f₁ f₂ : X → PE} {g : X → R} {s : set X}
  (h₁ : continuous_on f₁ s) (hg : continuous_on g s) (h₂ : continuous_on f₂ s) :
  continuous_on (λ x, homothety (f₁ x) (g x) (f₂ x)) s :=
h₁.line_map h₂ hg

@[continuity] lemma continuous.homothety {f₁ f₂ : X → PE} {g : X → R} (h₁ : continuous f₁)
  (hg : continuous g) (h₂ : continuous f₂) :
  continuous (λ x, homothety (f₁ x) (g x) (f₂ x)) :=
h₁.line_map h₂ hg

end homothety

section const_smul

variables [comm_ring R] [module R E] [has_continuous_const_smul R E]
include E

@[continuity] lemma continuous_homothety {c : PE} {t : R} : continuous (homothety c t) :=
show continuous (λ x, t • (x -ᵥ c) +ᵥ c),
from ((continuous_id.vsub continuous_const).const_smul _).vadd continuous_const

/-- Homothety about `c` with scale factor `t : Rˣ` as a homeomorphism. -/
@[simps apply {fully_applied := ff}] def homeomorph.homothety (c : PE) (t : Rˣ) : PE ≃ₜ PE :=
{ to_equiv := affine_equiv.homothety_units_mul_hom c t,
  continuous_to_fun := continuous_homothety,
  continuous_inv_fun := continuous_homothety }

@[simp] lemma homeomorph.homothety_symm (c : PE) (t : Rˣ) :
  (homeomorph.homothety c t).symm = homeomorph.homothety c t⁻¹ :=
rfl

lemma is_unit.is_open_map_homothety {t : R} (ht : is_unit t) (c : PE) :
  is_open_map (homothety c t) :=
(homeomorph.homothety c ht.unit).is_open_map

lemma is_open_map_homothety {k : Type*} [field k] [module k E] [has_continuous_const_smul k E]
  (c : PE) (t : k) (ht : t ≠ 0) : is_open_map (homothety c t) :=
(is_unit.mk0 t ht).is_open_map_homothety c

end const_smul
