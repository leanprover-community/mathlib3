/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.polish
import measure_theory.constructions.borel_space

/-!
# Analytic sets
-/


namespace measure_theory

variables {α : Type*} [topological_space α]

/-- An analytic set is a set which is the continuous image of some Polish space. There are several
equivalent characterizations of this definition. For the definition, we pick one that avoids
universe issues: a set is analytic if and only if it is a continuous image of `ℕ → ℕ` (or if it
is empty). The above more usual characterization is given
in `analytic_set_iff_exists_polish_space_range`.

Warning: these are analytic sets in the context of descriptive set theory (which is why they are
registered in the namespace `measure_theory`). They have nothing to do with analytic sets in the
context of complex analysis. -/
@[irreducible] def analytic_set (s : set α) : Prop :=
s = ∅ ∨ ∃ (f : (ℕ → ℕ) → α), continuous f ∧ range f = s

lemma analytic_set_empty :
  analytic_set (∅ : set α) :=
by { rw analytic_set, exact or.inl rfl }

lemma analytic_set_of_polish_space_range
  {β : Type*} [topological_space β] [polish_space β] (f : β → α) {s : set α}
  (f_cont : continuous f) (hf : range f = s) :
  analytic_set s :=
begin
  casesI is_empty_or_nonempty β,
  { have : s = ∅, by rw [← hf, range_eq_empty],
    rw [this, analytic_set],
    exact or.inl rfl },
  { rw analytic_set,
    obtain ⟨g, g_cont, hg⟩ : ∃ (g : (ℕ → ℕ) → β), continuous g ∧ surjective g :=
      exists_nat_nat_continuous_surjective_of_polish_space β,
    right,
    refine ⟨f ∘ g, f_cont.comp g_cont, _⟩,
    rwa hg.range_comp }
end

/-- A set is analytic if and only if it is the continuous image of some Polish space. -/
theorem analytic_set_iff_exists_polish_space_range {s : set α} :
  analytic_set s ↔ ∃ (β : Type) (h : topological_space β) (h' : @polish_space β h) (f : β → α),
    @continuous _ _ h _ f ∧ range f = s :=
begin
  split,
  { assume h,
    rw analytic_set at h,
    cases h,
    { refine ⟨empty, by apply_instance, by apply_instance, empty.elim, continuous_bot, _⟩,
      rw h,
      exact range_eq_empty _ },
    { exact ⟨ℕ → ℕ, by apply_instance, by apply_instance, h⟩ } },
  { rintros ⟨β, h, h', f, f_cont, f_range⟩,
    resetI,
    exact analytic_set_of_polish_space_range f f_cont f_range }
end

/-- A countable intersection of analytic sets is analytic. -/
theorem analytic_set.Inter [t2_space α] {s : ℕ → set α} (hs : ∀ n, analytic_set (s n)) :
  analytic_set (⋂ n, s n) :=
begin
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
  Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
  `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, and the
  range of `x ↦ f 0 (x 0)` on `t` is exactly `⋂ n, s n`, so this set is analytic. -/
  choose β hβ h'β f f_cont f_range using λ n, analytic_set_iff_exists_polish_space_range.1 (hs n),
  resetI,
  let γ := Π n, β n,
  let t : set γ := ⋂ n, {x | f n (x n) = f 0 (x 0)},
  have t_closed : is_closed t,
  { apply is_closed_Inter,
    assume n,
    exact is_closed_eq ((f_cont n).comp (continuous_apply n))
      ((f_cont 0).comp (continuous_apply 0)) },
  haveI : polish_space t := t_closed.polish_space,
  let F : t → α := λ x, f 0 ((x : γ) 0),
  have F_cont : continuous F := (f_cont 0).comp ((continuous_apply 0).comp continuous_subtype_coe),
  have F_range : range F = ⋂ (n : ℕ), s n,
  { apply subset.antisymm,
    { rintros y ⟨x, rfl⟩,
      apply mem_Inter.2 (λ n, _),
      have : f n ((x : γ) n) = F x := (mem_Inter.1 x.2 n : _),
      rw [← this, ← f_range n],
      exact mem_range_self _ },
    { assume y hy,
      have A : ∀ n, ∃ (x : β n), f n x = y,
      { assume n,
        rw [← mem_range, f_range n],
        exact mem_Inter.1 hy n },
      choose x hx using A,
      have xt : x ∈ t,
      { apply mem_Inter.2 (λ n, _),
        simp [hx] },
        refine ⟨⟨x, xt⟩, _⟩,
        exact hx 0 } },
  exact analytic_set_of_polish_space_range F F_cont F_range,
end

/-- A countable union of analytic sets is analytic. -/
theorem analytic_set.Union {s : ℕ → set α} (hs : ∀ n, analytic_set (s n)) :
  analytic_set (⋃ n, s n) :=
begin
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
  Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
  coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using λ n, analytic_set_iff_exists_polish_space_range.1 (hs n),
  resetI,
  let γ := Σ n, β n,
  let F : γ → α := by { rintros ⟨n, x⟩, exact f n x },
  have F_cont : continuous F := continuous_sigma f_cont,
  have F_range : range F = ⋃ n, s n,
  { rw [range_sigma_eq_Union_range],
    congr,
    ext1 n,
    rw ← f_range n },
  exact analytic_set_of_polish_space_range F F_cont F_range,
end

end measure_theory
