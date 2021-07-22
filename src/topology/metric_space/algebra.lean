/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import topology.metric_space.lipschitz

/-!
# Compatibility of algebraic operations with metric space structures

In this file we define mixin typeclasses `has_lipschitz_mul`, `has_lipschitz_add`,
`has_lipschitz_smul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure.  The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `has_continuous_mul` instance from `has_lipschitz_mul`, etc.  In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`uniform_group`) is structured differently.

-/

open_locale nnreal

noncomputable theory

variables (β : Type*) [pseudo_metric_space β]

section has_lipschitz_mul

/-- Class `has_lipschitz_add M` says that the addition `(+) : X × X → X` is Lipschitz jointly in
the two arguments. -/
class has_lipschitz_add [add_monoid β] : Prop :=
( lipschitz_add : ∃ C, lipschitz_with C (λ p : β × β, p.1 + p.2) )

/-- Class `has_lipschitz_mul M` says that the multiplication `(*) : X × X → X` is Lipschitz jointly
in the two arguments. -/
@[to_additive] class has_lipschitz_mul [monoid β] : Prop :=
( lipschitz_mul : ∃ C, lipschitz_with C (λ p : β × β, p.1 * p.2) )

variables [monoid β]

@[to_additive] def has_lipschitz_mul.C [_i : has_lipschitz_mul β] : ℝ≥0 :=
classical.some _i.lipschitz_mul

variables {β}

@[to_additive] lemma lipschitz_with_lipschitz_const_mul_edist [_i : has_lipschitz_mul β] :
  lipschitz_with (has_lipschitz_mul.C β) (λ p : β × β, p.1 * p.2) :=
classical.some_spec _i.lipschitz_mul

variables [has_lipschitz_mul β]

@[to_additive] lemma lipschitz_with_lipschitz_const_mul :
  ∀ p q : β × β, dist (p.1 * p.2) (q.1 * q.2) ≤ (has_lipschitz_mul.C β) * dist p q :=
begin
  rw ← lipschitz_with_iff_dist_le_mul,
  exact lipschitz_with_lipschitz_const_mul_edist,
end

@[to_additive] instance has_lipschitz_mul.has_continuous_mul : has_continuous_mul β :=
⟨ lipschitz_with_lipschitz_const_mul_edist.continuous ⟩

@[to_additive] instance submonoid.has_lipschitz_mul (s : submonoid β) : has_lipschitz_mul s :=
{ lipschitz_mul := ⟨has_lipschitz_mul.C β, begin
    rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    convert lipschitz_with_lipschitz_const_mul_edist ⟨(x₁:β), x₂⟩ ⟨y₁, y₂⟩ using 1
  end⟩ }

-- this instance could be deduced from `normed_group.has_lipschitz_add`, but we prove it separately
-- here so that it is available earlier in the hierarchy
instance real.has_lipschitz_add : has_lipschitz_add ℝ :=
{ lipschitz_add := ⟨2, begin
    rw lipschitz_with_iff_dist_le_mul,
    intros p q,
    simp only [real.dist_eq, prod.dist_eq, prod.fst_sub, prod.snd_sub, nnreal.coe_one,
      nnreal.coe_bit0],
    convert le_trans (abs_add (p.1 - q.1) (p.2 - q.2)) _ using 2,
    { abel },
    have := le_max_left (abs (p.1 - q.1)) (abs (p.2 - q.2)),
    have := le_max_right (abs (p.1 - q.1)) (abs (p.2 - q.2)),
    linarith,
  end⟩ }

-- this instance has the same proof as `add_submonoid.has_lipschitz_add`, but the former can't
-- directly be applied here since `ℝ≥0` is a subtype of `ℝ`, not an additive submonoid.
instance nnreal.has_lipschitz_add : has_lipschitz_add ℝ≥0 :=
{ lipschitz_add := ⟨has_lipschitz_add.C ℝ, begin
    rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    convert lipschitz_with_lipschitz_const_add_edist ⟨(x₁:ℝ), x₂⟩ ⟨y₁, y₂⟩ using 1
  end⟩ }

end has_lipschitz_mul
