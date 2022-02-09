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

open set function polish_space

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
      exists_nat_nat_continuous_surjective β,
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

def borel_separable [measurable_space α] (s t : set α) : Prop :=
  ∃ u, s ⊆ u ∧ disjoint t u ∧ measurable_set u

lemma borel_separable.Union [measurable_space α] (s t : ℕ → set α)
  (h : ∀ m n, borel_separable (s m) (t n)) :
  borel_separable (⋃ n, s n) (⋃ m, t m) :=
begin
  choose u hsu htu hu using h,
  refine ⟨⋃ m, (⋂ n, u m n), _, _, _⟩,
  { refine Union_subset (λ m, subset_Union_of_subset m _),
    exact subset_Inter (λ n, hsu m n) },
  { simp_rw [disjoint_Union_left, disjoint_Union_right],
    assume n m,
    apply disjoint.mono_right _ (htu m n),
    apply Inter_subset },
  { refine measurable_set.Union (λ m, _),
    exact measurable_set.Inter (λ n, hu m n) }
end

open pi_nat

open_locale topological_space

lemma Union_cylinder_update {E : ℕ → Type*} (x : Π n, E n) (n : ℕ) :
  (⋃ k, cylinder (update x n k) (n+1)) = cylinder x n :=
begin
  ext y,
  simp only [mem_cylinder_iff, mem_Union],
  split,
  { rintros ⟨k, hk⟩ i hi,
    simpa [hi.ne] using hk i (nat.lt_succ_of_lt hi) },
  { assume H,
    refine ⟨y n, λ i hi, _⟩,
    rcases nat.lt_succ_iff_lt_or_eq.1 hi with h'i|rfl,
    { simp [H i h'i, h'i.ne] },
    { simp } },
end

lemma update_mem_cylinder {E : ℕ → Type*} (x : Π n, E n) (n : ℕ) (y : E n) :
  update x n y ∈ cylinder x n :=
mem_cylinder_iff.2 (λ i hi, by simp [hi.ne])

lemma zoug [measurable_space α] [t2_space α] (f g : (ℕ → ℕ) → α)
  (hf : continuous f) (hg : continuous g) (h : disjoint (range f) (range g)) :
  borel_separable (range f) (range g) :=
begin
  by_contra hfg,
  have I : ∀ n x y, (¬(borel_separable (f '' (cylinder x n)) (g '' (cylinder y n))))
    → ∃ x' y', x' ∈ cylinder x n ∧ y' ∈ cylinder y n ∧
                ¬(borel_separable (f '' (cylinder x' (n+1))) (g '' (cylinder y' (n+1)))),
  { assume n x y,
    contrapose!,
    assume H,
    rw [← Union_cylinder_update x n, ← Union_cylinder_update y n, image_Union, image_Union],
    apply borel_separable.Union _ _ (λ i j, _),
    exact H _ _ (update_mem_cylinder _ _ _) (update_mem_cylinder _ _ _) },
  let A := {p // ¬(borel_separable (f '' (cylinder (p : ℕ × (ℕ → ℕ) × (ℕ → ℕ)).2.1 p.1))
                                   (g '' (cylinder p.2.2 p.1)))},
  have : ∀ (p : A), ∃ (q : A), q.1.1 = p.1.1 + 1 ∧ q.1.2.1 ∈ cylinder p.1.2.1 p.1.1
    ∧ q.1.2.2 ∈ cylinder p.1.2.2 p.1.1,
  { rintros ⟨⟨n, x, y⟩, hp⟩,
    rcases I n x y hp with ⟨x', y', hx', hy', h'⟩,
    exact ⟨⟨⟨n+1, x', y'⟩, h'⟩, rfl, hx', hy'⟩ },
  choose F hFn hFx hFy using this,
  let p0 : A := ⟨⟨0, λ n, 0, λ n, 0⟩, by simp [hfg]⟩,
  let p : ℕ → A := λ n, F^[n] p0,
  have prec : ∀ n, p (n+1) = F (p n) := λ n, by simp only [p, iterate_succ'],
  have pn_fst : ∀ n, (p n).1.1 = n,
  { assume n,
    induction n with n IH,
    { refl },
    { simp only [prec, hFn, IH] } },
  have Ix : ∀ m n, m + 1 ≤ n → (p n).1.2.1 m = (p (m+1)).1.2.1 m,
  { assume m,
    apply nat.le_induction,
    { refl },
    assume n hmn IH,
    have I : (F (p n)).val.snd.fst m = (p n).val.snd.fst m,
    { apply hFx (p n) m,
      rw pn_fst,
      exact hmn },
    rw [prec, I, IH] },
  have Iy : ∀ m n, m + 1 ≤ n → (p n).1.2.2 m = (p (m+1)).1.2.2 m,
  { assume m,
    apply nat.le_induction,
    { refl },
    assume n hmn IH,
    have I : (F (p n)).val.snd.snd m = (p n).val.snd.snd m,
    { apply hFy (p n) m,
      rw pn_fst,
      exact hmn },
    rw [prec, I, IH] },
  set x : ℕ → ℕ := λ n, (p (n+1)).1.2.1 n with hx,
  set y : ℕ → ℕ := λ n, (p (n+1)).1.2.2 n with hy,
  have : ∀ n, ¬(borel_separable (f '' (cylinder x n)) (g '' (cylinder y n))),
  { assume n,
    convert (p n).2 using 3,
    { rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff],
      assume i hi,
      rw hx,
      exact (Ix i n hi).symm },
    { rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff],
      assume i hi,
      rw hy,
      exact (Iy i n hi).symm } },
  obtain ⟨u, v, u_open, v_open, xu, yv, huv⟩ :
    ∃ u v : set α, is_open u ∧ is_open v ∧ f x ∈ u ∧ g y ∈ v ∧ u ∩ v = ∅,
  { apply t2_separation,
    exact disjoint_iff_forall_ne.1 h _ (mem_range_self _) _ (mem_range_self _) },
  have : f ⁻¹' u ∈ 𝓝 x,
  { apply hf.continuous_at.preimage_mem_nhds,

  }


end

end measure_theory
