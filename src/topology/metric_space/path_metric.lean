import topology.metric_space.emetric_space
import analysis.bounded_variation
import topology.metric_space.lipschitz

noncomputable theory

open_locale nnreal ennreal



section path_emetric

universe u

def path_emetric (E : Type u) [pseudo_emetric_space E] : Type u := E


variables {E : Type u} [pseudo_emetric_space E]

def to_path_emetric : E → path_emetric E := id
def from_path_emetric : path_emetric E → E := id
abbreviation of : E → path_emetric E := to_path_emetric
abbreviation fo : path_emetric E → E := from_path_emetric


lemma from_to_path_emetric (x : E) : from_path_emetric (to_path_emetric x) = x := rfl
lemma to_from_path_emetric (x : path_emetric E) : to_path_emetric (from_path_emetric x) = x := rfl

def is_l_path_from_to (x y : E) (l : ℝ≥0) (p : ℝ → E) :=
  (p 0 = x ∧ p l = y) ∧ continuous_on p (set.Icc 0 l)

structure path_btw (x y : E) :=
(l : ℝ≥0)
(path : ℝ → E)
(map_source : ∀ ⦃t⦄, t ≤ 0 → path t = x)
(map_target : ∀ ⦃t⦄, l ≤ t → path t = y)
(continuous : continuous_on path (set.Icc 0 l))

def path_btw.refl (x : E) : path_btw x x :=
{ l := 0,
  path := λ _, x,
  map_source := by simp,
  map_target := by simp,
  continuous := by {simp, apply continuous_on_singleton, } }

def path_btw.trans {x y z : E} (p : path_btw x y) (p' : path_btw y z) : path_btw x z :=
{ l := p.l + p'.l,
  path := λ t, if t ≤ p.l then p.path t else p'.path (p.l + t),
  map_source := sorry,
  map_target := sorry,
  continuous := sorry }

def path_btw.symm {x y : E} (p : path_btw x y) : path_btw y x :=
{ l := p.l,
  path := λ t, p.path (p.l-t),
  map_source := sorry,
  map_target := sorry,
  continuous := sorry }

def path_emetric.edist (x y : E) : ℝ≥0∞ := ⨅ (p : ℝ → E) (l : ℝ≥0) (h : is_l_path_from_to x y l p),
  evariation_on p (set.Icc 0 l)

def path_emetric.edist' (x y : E) : ℝ≥0∞ :=
  ⨅ (p : ℝ → E) (l : ℝ≥0) (h : p 0 = x ∧ p l = y ∧ continuous_on p (set.Icc 0 l)),
    evariation_on p (set.Icc 0 l)

instance : pseudo_emetric_space (path_emetric E) :=
{ edist := λ x y, path_emetric.edist (from_path_emetric x) (from_path_emetric y),
  edist_self := sorry,
  edist_comm := sorry,
  edist_triangle := sorry }

lemma from_path_emetric_nonexpanding :
  lipschitz_with 1 (from_path_emetric : path_emetric E → E) := sorry





end path_emetric
