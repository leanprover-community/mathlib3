/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import ring_theory.ideal.operations
import topology.algebra.nonarchimedean.bases
import topology.algebra.uniform_ring
/-!
# Adic topology

Given a commutative ring `R` and an ideal `I` in `R`, this file constructs the unique
topology on `R` which is compatible with the ring structure and such that a set is a neighborhood
of zero if and only if it contains a power of `I`. This topology is non-archimedean: every
neighborhood of zero contains an open subgroup, namely a power of `I`.

It also studies the predicate `is_adic` which states that a given topological ring structure is
adic, proving a characterization and showing that raising an ideal to a positive power does not
change the associated topology.

Finally, it defines `with_ideal`, a class registering an ideal in a ring and providing the
corresponding adic topology to the type class inference system.


## Main definitions and results

* `ideal.adic_basis`: the basis of submodules given by powers of an ideal.
* `ideal.adic_topology`: the adic topology associated to an ideal. It has the above basis
  for neighborhoods of zero.
* `ideal.nonarchimedean`: the adic topology is non-archimedean
* `is_ideal_adic_iff`: A topological ring is `J`-adic if and only if it admits the powers of `J` as
  a basis of open neighborhoods of zero.
* `with_ideal`: a class registering an ideal in a ring.

## Implementation notes

The `I`-adic topology on a ring `R` has a contrived definition using `I^n • ⊤` instead of `I`
to make sure it is definitionally equal to the `I`-topology on `R` seen as a `R`-module.

-/

variables {R : Type*} [comm_ring R]

open set topological_add_group submodule filter
open_locale topological_space pointwise

namespace ideal

lemma adic_basis (I : ideal R) : submodules_ring_basis (λ n : ℕ, (I^n • ⊤ : ideal R)) :=
{ inter := begin
    suffices : ∀ i j : ℕ, ∃ k, I ^ k ≤ I ^ i ∧ I ^ k ≤ I ^ j, by simpa,
    intros i j,
    exact ⟨max i j, pow_le_pow (le_max_left i j), pow_le_pow (le_max_right i j)⟩
  end,
  left_mul := begin
    suffices : ∀ (a : R) (i : ℕ), ∃ j : ℕ, a • I ^ j ≤ I ^ i,  by simpa,
    intros r n,
    use n,
    rintro a ⟨x, hx, rfl⟩,
    exact (I ^ n).smul_mem r hx
  end,
  mul := begin
    suffices : ∀ (i : ℕ), ∃ (j : ℕ), ↑(I ^ j) * ↑(I ^ j) ⊆ ↑(I ^ i), by simpa,
    intro n,
    use n,
    rintro a ⟨x, b, hx, hb, rfl⟩,
    exact (I^n).smul_mem x hb
  end }

/-- The adic ring filter basis associated to an ideal `I` is made of powers of `I`. -/
def ring_filter_basis (I : ideal R) := I.adic_basis.to_ring_subgroups_basis.to_ring_filter_basis

/-- The adic topology associated to an ideal `I`. This topology admits powers of `I` as a basis of
neighborhoods of zero. It is compatible with the ring structure and is non-archimedean. -/
def adic_topology (I : ideal R) : topological_space R :=
(adic_basis I).topology

lemma nonarchimedean (I : ideal R) : @nonarchimedean_ring R _ I.adic_topology :=
I.adic_basis.to_ring_subgroups_basis.nonarchimedean

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
lemma has_basis_nhds_zero_adic (I : ideal R) :
  has_basis (@nhds R I.adic_topology (0 : R)) (λ n : ℕ, true) (λ n, ((I^n : ideal R) : set R)) :=
⟨begin
  intros U,
  rw I.ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff,
  split,
  { rintros ⟨-, ⟨i, rfl⟩, h⟩,
    replace h : ↑(I ^ i) ⊆ U := by simpa using h,
    use [i, trivial, h] },
  { rintros ⟨i, -, h⟩,
    exact ⟨(I^i : ideal R), ⟨i, by simp⟩, h⟩ }
end⟩

lemma has_basis_nhds_adic (I : ideal R) (x : R) :
  has_basis (@nhds R I.adic_topology x) (λ n : ℕ, true) (λ n, (λ y, x + y) '' (I^n : ideal R)) :=
begin
  letI := I.adic_topology,
  have := I.has_basis_nhds_zero_adic.map (λ y, x + y),
  rwa map_add_left_nhds_zero x at this
end

variables (I : ideal R) (M : Type*) [add_comm_group M] [module R M]

lemma adic_module_basis  :
  I.ring_filter_basis.submodules_basis (λ n : ℕ, (I^n) • (⊤ : submodule R M)) :=
{ inter := λ i j, ⟨max i j, le_inf_iff.mpr ⟨smul_mono_left $ pow_le_pow (le_max_left i j),
                                            smul_mono_left $ pow_le_pow (le_max_right i j)⟩⟩,
  smul := λ m i, ⟨(I^i • ⊤ : ideal R), ⟨i, rfl⟩,
                  λ a a_in, by { replace a_in : a ∈ I^i := by simpa [(I^i).mul_top] using a_in,
                                 exact smul_mem_smul a_in mem_top }⟩ }

/-- The topology on a `R`-module `M` associated to an ideal `M`. Submodules $I^n M$,
written `I^n • ⊤` form a basis of neighborhoods of zero. -/
def adic_module_topology : topological_space M :=
  @module_filter_basis.topology R M _ I.adic_basis.topology _ _
  (I.ring_filter_basis.module_filter_basis (I.adic_module_basis M))

/-- The elements of the basis of neighborhoods of zero for the `I`-adic topology
on a `R`-module `M`, seen as open additive subgroups of `M`. -/
def open_add_subgroup (n : ℕ) : @open_add_subgroup R _ I.adic_topology :=
{ is_open' := begin
    letI := I.adic_topology,
    convert (I.adic_basis.to_ring_subgroups_basis.open_add_subgroup n).is_open,
    simp
  end,
  ..(I^n).to_add_subgroup}

end ideal

section is_adic

/-- Given a topology on a ring `R` and an ideal `J`, `is_adic J` means the topology is the
`J`-adic one. -/
def is_adic [H : topological_space R] (J : ideal R) : Prop :=
H = J.adic_topology

/-- A topological ring is `J`-adic if and only if it admits the powers of `J` as a basis of
open neighborhoods of zero. -/
lemma is_adic_iff [top : topological_space R] [topological_ring R] {J : ideal R} :
  is_adic J ↔ (∀ n : ℕ, is_open ((J^n : ideal R) : set R)) ∧
              (∀ s ∈ 𝓝 (0 : R), ∃ n : ℕ, ((J^n : ideal R) : set R) ⊆ s) :=
begin
  split,
  { intro H,
    change _ = _ at H,
    rw H,
    letI := J.adic_topology,
    split,
    { intro n,
      exact (J.open_add_subgroup n).is_open' },
    { intros s hs,
      simpa using J.has_basis_nhds_zero_adic.mem_iff.mp hs } },
  { rintro ⟨H₁, H₂⟩,
    apply topological_add_group.ext,
    { apply @topological_ring.to_topological_add_group },
    { apply (ring_subgroups_basis.to_ring_filter_basis _).to_add_group_filter_basis
             .is_topological_add_group },
    { ext s,
      letI := ideal.adic_basis J,
      rw J.has_basis_nhds_zero_adic.mem_iff,
      split; intro H,
      { rcases H₂ s H with ⟨n, h⟩,
        use [n, trivial, h] },
      { rcases H with ⟨n, -, hn⟩,
        rw mem_nhds_iff,
        refine ⟨_, hn, H₁ n, (J^n).zero_mem⟩ } } }
end

variables [topological_space R] [topological_ring R]

lemma is_ideal_adic_pow {J : ideal R} (h : is_adic J) {n : ℕ} (hn : 0 < n) :
  is_adic (J^n) :=
begin
  rw is_adic_iff at h ⊢,
  split,
  { intro m, rw ← pow_mul, apply h.left },
  { intros V hV,
    cases h.right V hV with m hm,
    use m,
    refine set.subset.trans _ hm,
    cases n, { exfalso, exact nat.not_succ_le_zero 0 hn },
    rw [← pow_mul, nat.succ_mul],
    apply ideal.pow_le_pow,
    apply nat.le_add_left }
end

lemma is_bot_adic_iff {A : Type*} [comm_ring A] [topological_space A] [topological_ring A] :
is_adic (⊥ : ideal A) ↔ discrete_topology A :=
begin
  rw is_adic_iff,
  split,
  { rintro ⟨h, h'⟩,
    rw discrete_topology_iff_open_singleton_zero,
    simpa using h 1 },
  { introsI,
    split,
    { simp, },
    { intros U U_nhds,
      use 1,
      simp [mem_of_mem_nhds U_nhds] } },
end

end is_adic

/-- The ring `R` is equipped with a preferred ideal. -/
class with_ideal (R : Type*) [comm_ring R] :=
(I : ideal R)

namespace with_ideal

variables (R) [with_ideal R]

@[priority 100] instance : topological_space R := I.adic_topology

@[priority 100] instance : nonarchimedean_ring R := ring_subgroups_basis.nonarchimedean _
@[priority 100] instance : uniform_space R :=
topological_add_group.to_uniform_space R

@[priority 100] instance : uniform_add_group R :=
topological_add_group_is_uniform

/-- The adic topology on a `R` module coming from the ideal `with_ideal.I`.
This cannot be an instance because `R` cannot be inferred from `M`. -/
def topological_space_module (M : Type*) [add_comm_group M] [module R M] :
  topological_space M := (I : ideal R).adic_module_topology M

/-
The next examples are kept to make sure potential future refactors won't break the instance
chaining.
-/

example : nonarchimedean_ring R :=
by apply_instance

example : topological_ring (uniform_space.completion R) :=
by apply_instance

example (M : Type*) [add_comm_group M] [module R M] :
  @topological_add_group M (with_ideal.topological_space_module R M) _:=
by apply_instance

example (M : Type*) [add_comm_group M] [module R M] :
  @has_continuous_smul R M _ _ (with_ideal.topological_space_module R M) :=
by apply_instance

example (M : Type*) [add_comm_group M] [module R M] :
  @nonarchimedean_add_group M _ (with_ideal.topological_space_module R M) :=
submodules_basis.nonarchimedean _

end with_ideal
