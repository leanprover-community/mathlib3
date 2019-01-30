/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel
We define emetric isometries, i.e., maps between emetric spaces that preserve
the edistance, and metric isometries, i.e., maps between metric spaces that
preserve the distance. We prove their basic properties.
-/

import topology.metric_space.basic topology.instances.real

noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function set metric

namespace emetric
section isometry

variables [emetric_space α] [emetric_space β] [emetric_space γ]
variables {f : α → β} {x y z : α}  {s : set α}

/-- An isometry is a map preserving the edistance -/
def isometry_on (f : α → β) (s : set α) : Prop :=
∀⦃x1 x2 : α⦄, x1 ∈ s → x2 ∈ s → edist (f x1) (f x2) = edist x1 x2

/-- An isometry is injective -/
lemma isometry_on.inj_on (h : isometry_on f s) : inj_on f s :=
λx y hx hy hxy, edist_eq_zero.1 $
calc edist x y = edist (f x) (f y) : (h hx hy).symm
         ...   = 0 : by rw [hxy]; simp

/-- Any map on the empty set is an isometry -/
theorem isometry_on_empty : isometry_on f ∅ :=
λx y hx hy, false.elim hx

/-- Any map on a singleton is an isometry -/
theorem isometry_on_singleton {a : α} : isometry_on f {a} :=
assume x y hx hy,
have A : x = y := by simp at hx; simp at hy; simp [hx, hy],
by simp [A]

/-- The composition of isometries is an isometry -/
theorem isometry_on_comp {g : β → γ} {f : α → β} {a : set α} {b : set β}
  (h₁ : maps_to f a b) (h₂ : isometry_on g b) (h₃: isometry_on f a) :
  isometry_on (g ∘ f) a :=
assume x y hx hy, calc
  edist ((g ∘ f) x) ((g ∘ f) y) = edist (f x) (f y) : h₂ (h₁ hx) (h₁ hy)
                            ... = edist x y : h₃ hx hy

open function

/-- The inverse of an isometry is an isometry -/
theorem isometry_on.inv_fun_on [inhabited α] (I : isometry_on f s) :
  isometry_on (inv_fun_on f s) (f '' s) :=
begin
  rintros x y ⟨x', ⟨x's, hx'⟩⟩ ⟨y', ⟨y's, hy'⟩⟩,
  have Ax : inv_fun_on f s (f x') = x' := inv_fun_on_eq' I.inj_on x's,
  have Ay : inv_fun_on f s (f y') = y' := inv_fun_on_eq' I.inj_on y's,
  simp [hx'.symm, hy'.symm, Ax, Ay, I x's y's]
end

/-- An isometry is an embedding -/
theorem isometry_on.uniform_embedding {f : α → β}
  (hf : isometry_on f univ) : uniform_embedding f :=
begin
  have hf' : ∀x y, edist (f x) (f y) = edist x y := λx y, hf (mem_univ x) (mem_univ y),
  refine uniform_embedding_iff.2 ⟨_, _, _⟩,
  { assume x y hxy,
    have : edist (f x) (f y) = 0 := by simp [hxy],
    have : edist x y = 0 :=
      begin have A := hf' x y, rwa this at A, exact eq.symm A end,
    by simpa using this },
  { refine uniform_continuous_iff.2 (λε εpos, _),
    existsi [ε, εpos],
    simp [hf'] },
  { assume δ δpos,
    existsi [δ, δpos],
    simp [hf'] }
end

/-- An isometry is continuous -/
lemma isometry_on.continuous {f : α → β}
  (hf : isometry_on f univ) : continuous f :=
hf.uniform_embedding.embedding.continuous

/-- Isometries preserve the diameter -/
lemma diam_image_of_isometry [emetric_space β] {f : α → β} (hf : isometry_on f s) :
  diam (f '' s) = diam s :=
begin
  refine le_antisymm _ _,
  { apply lattice.Sup_le _,
    simp only [and_imp, set.mem_image, set.mem_prod, exists_imp_distrib, prod.exists],
    assume b x x' z zs xz z' z's x'z' hb,
    rw [← hb, ← xz, ← x'z', hf zs z's],
    exact edist_le_diam_of_mem zs z's },
  { apply lattice.Sup_le _,
    simp only [and_imp, set.mem_image, set.mem_prod, exists_imp_distrib, prod.exists],
    assume b x x' xs x's hb,
    rw [← hb, ← hf xs x's],
    exact edist_le_diam_of_mem (mem_image_of_mem _ xs) (mem_image_of_mem _ x's) }
end

end isometry
end emetric

namespace metric
section isometry

variables [metric_space α] [metric_space β] [metric_space γ]
variables {f : α → β} {x y z : α} {s : set α}

def isometry_on (f : α → β) (s : set α) : Prop :=
∀⦃x1 x2 : α⦄, x1 ∈ s → x2 ∈ s → dist (f x1) (f x2) = dist x1 x2

lemma emetric_isometry_on_iff_isometry_on : emetric.isometry_on f s ↔ isometry_on f s :=
⟨assume H x y hx hy, by simp [dist_edist, H hx hy],
assume H x y hx hy, by simp [edist_dist, H hx hy]⟩

/-- An isometry is injective -/
lemma isometry_on.inj_on (h : isometry_on f s) : inj_on f s :=
(emetric_isometry_on_iff_isometry_on.2 h).inj_on

/-- Any map on the empty set is an isometry -/
theorem isometry_on_empty : isometry_on f ∅ :=
assume x y hx hy, false.elim hx

/-- Any map on a singleton is an isometry -/
theorem isometry_on_singleton {a : α} : isometry_on f {a} :=
assume x y hx hy,
have A : x = y := by simp at hx; simp at hy; simp [hx, hy],
by simp [A]

/-- The composition of isometries is an isometry -/
theorem isometry_on_comp {g : β → γ} {f : α → β} {a : set α} {b : set β}
  (h₁ : maps_to f a b) (h₂ : isometry_on g b) (h₃: isometry_on f a) :
  isometry_on (g ∘ f) a :=
assume x y hx hy, calc
  dist ((g ∘ f) x) ((g ∘ f) y) = dist (f x) (f y) : h₂ (h₁ hx) (h₁ hy)
                           ... = dist x y : h₃ hx hy

open function
/-- The inverse of an isometry is an isometry -/
theorem isometry_on.inv_fun_on [inhabited α] (I : isometry_on f s) :
  isometry_on (inv_fun_on f s) (f '' s) :=
begin
  rintros x y ⟨x', ⟨x's, hx'⟩⟩ ⟨y', ⟨y's, hy'⟩⟩,
  have Ax : inv_fun_on f s (f x') = x' := inv_fun_on_eq' I.inj_on x's,
  have Ay : inv_fun_on f s (f y') = y' := inv_fun_on_eq' I.inj_on y's,
  simp [hx'.symm, hy'.symm, Ax, Ay, I x's y's]
end

/-- An isometry is a uniform embedding -/
theorem isometry_on.uniform_embedding (h : isometry_on f univ) : uniform_embedding f :=
(emetric_isometry_on_iff_isometry_on.2 h).uniform_embedding

/-- An isometry is continuous -/
lemma isometry_on.continuous
  (hf : isometry_on f univ) : continuous f :=
hf.uniform_embedding.embedding.continuous

/-- The injection from a subtype is an isometry -/
lemma isometry_on_subtype.val {s : set α} : isometry_on (subtype.val : s → α) univ :=
λx y hx hy, rfl

/-- An isometry preserves the diameter -/
lemma diam_image_of_isometry [metric_space β] {f : α → β} (hf : isometry_on f s) :
  diam (f '' s) = diam s :=
by rw [diam, diam, emetric.diam_image_of_isometry (emetric_isometry_on_iff_isometry_on.2 hf)]

end isometry --section
end metric --namespace
