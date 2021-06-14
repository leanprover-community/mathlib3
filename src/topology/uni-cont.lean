import topology.continuous_function.bounded

def clopen_sets (H : Type*) [topological_space H] := {s : set H // is_clopen s}

open_locale big_operators

--variables {R : Type*} [ring R] [topological_space R]
--variables {R : Type*} [ring R] [topological_space R] [topological_ring R]
variables (X : Type*) [topological_space X] [compact_space X] [t2_space X] [totally_disconnected_space X]

lemma bdd_above_compact_range_norm {R : Type*} [normed_group R]
  (f : C(X, R)) : bdd_above (set.range (λ (x : X), ∥f x∥)) :=
begin
{  set g := λ (x : X), ∥(f x)∥ with hg,
  have cont : continuous g, { rw hg, refine continuous.norm _, show continuous f, apply f.2, },
  set bdd_cont := bounded_continuous_function.mk_of_compact ⟨g,cont⟩ with hb,
  have bdd := @bounded_continuous_function.bounded_range _ _ _ _ bdd_cont,
  rw real.bounded_iff_bdd_below_bdd_above at bdd,
  suffices : bdd_above (set.range bdd_cont), convert this, exact bdd.2, },
end

noncomputable instance {R : Type*} [normed_group R] : has_norm C(X,R) :=
{ norm := λ f, (⨆ x : X, ∥f x∥) }

lemma norm_def {R : Type*} [normed_group R] (f : C(X,R)) : ∥f∥ = ⨆ x : X, ∥f x∥ := rfl

lemma met {R : Type*} [normed_group R] [nonempty X] : normed_group.core C(X,R) :=
{
  norm_eq_zero_iff := begin
    rintros f, split,
    { rintros h, rw le_antisymm_iff at h, cases h with h1 h2,
      suffices : ∀ x : X, ∥f x∥ ≤ 0,
      {  ext, specialize this x, rw [norm_le_zero_iff] at this, simp [this], },
      rintros x, refine (cSup_le_iff  _ _).1 _ (∥f x∥) _,
      exact set.range (λ x, ∥f x∥), apply bdd_above_compact_range_norm,
      { rw set.range_nonempty_iff_nonempty, assumption, },
      { change Sup (set.range (λ x, ∥f x∥)) ≤ 0 at h1, assumption,}, exact ⟨x, rfl⟩, },
    { rintros h, rw h,-- conv_lhs { congr, funext, rw zero',},
      have : ∀ x : X, ∥(0 : C(X, R)) x∥ = 0, { rintros x, rw norm_eq_zero, refl, },
      unfold has_norm.norm, conv_lhs { congr, funext, rw this x, },
      { refine csupr_const, }, },
  end,
  triangle := begin
              rintros x y, refine csupr_le (λ z, _),
              transitivity (∥x z∥ + ∥y z∥), {  exact norm_add_le (x z) (y z), },
              { apply add_le_add,
                { apply le_cSup, { apply bdd_above_compact_range_norm, },
                  exact ⟨z, rfl⟩ },
                { apply le_cSup, { apply bdd_above_compact_range_norm, }, exact ⟨z, rfl⟩ },
              },
              end,
  norm_neg := begin
                rintros f, unfold has_norm.norm, congr, ext, refine norm_neg (f x),
              end,
}

noncomputable instance {R : Type*} [normed_group R] [h : nonempty X] : normed_group C(X,R) :=
  normed_group.of_core _ (met X)

noncomputable instance uniform {R : Type*} [normed_group R] [h : nonempty X] : uniform_space C(X, R) :=
begin
  have : metric_space C(X,R), { refine normed_group.to_metric_space, },
  apply metric_space.to_uniform_space',
end
