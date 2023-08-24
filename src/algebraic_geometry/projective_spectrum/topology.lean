/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Johan Commelin
-/

import ring_theory.graded_algebra.homogeneous_ideal
import topology.category.Top.basic
import topology.sets.opens

/-!
# Projective spectrum of a graded ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The projective spectrum of a graded commutative ring is the subtype of all homogenous ideals that
are prime and do not contain the irrelevant ideal.
It is naturally endowed with a topology: the Zariski topology.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → submodule R A` is the grading of `A`;

## Main definitions

* `projective_spectrum 𝒜`: The projective spectrum of a graded ring `A`, or equivalently, the set of
  all homogeneous ideals of `A` that is both prime and relevant i.e. not containing irrelevant
  ideal. Henceforth, we call elements of projective spectrum *relevant homogeneous prime ideals*.
* `projective_spectrum.zero_locus 𝒜 s`: The zero locus of a subset `s` of `A`
  is the subset of `projective_spectrum 𝒜` consisting of all relevant homogeneous prime ideals that
  contain `s`.
* `projective_spectrum.vanishing_ideal t`: The vanishing ideal of a subset `t` of
  `projective_spectrum 𝒜` is the intersection of points in `t` (viewed as relevant homogeneous prime
  ideals).
* `projective_spectrum.Top`: the topological space of `projective_spectrum 𝒜` endowed with the
  Zariski topology.
-/

noncomputable theory
open_locale direct_sum big_operators pointwise
open direct_sum set_like Top topological_space category_theory opposite

variables {R A: Type*}
variables [comm_semiring R] [comm_ring A] [algebra R A]
variables (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]

/-- The projective spectrum of a graded commutative ring is the subtype of all homogenous ideals
that are prime and do not contain the irrelevant ideal. -/
@[ext, nolint has_nonempty_instance] structure projective_spectrum :=
(as_homogeneous_ideal : homogeneous_ideal 𝒜)
(is_prime : as_homogeneous_ideal.to_ideal.is_prime)
(not_irrelevant_le : ¬(homogeneous_ideal.irrelevant 𝒜 ≤ as_homogeneous_ideal))

attribute [instance] projective_spectrum.is_prime

namespace projective_spectrum

/-- The zero locus of a set `s` of elements of a commutative ring `A` is the set of all relevant
homogeneous prime ideals of the ring that contain the set `s`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal) the function (i.e., element) `f` takes values in the
quotient ring `A` modulo the prime ideal `x`. In this manner, `zero_locus s` is exactly the subset
of `projective_spectrum 𝒜` where all "functions" in `s` vanish simultaneously. -/
def zero_locus (s : set A) : set (projective_spectrum 𝒜) :=
{x | s ⊆ x.as_homogeneous_ideal}

@[simp] lemma mem_zero_locus (x : projective_spectrum 𝒜) (s : set A) :
  x ∈ zero_locus 𝒜 s ↔ s ⊆ x.as_homogeneous_ideal := iff.rfl

@[simp] lemma zero_locus_span (s : set A) :
  zero_locus 𝒜 (ideal.span s) = zero_locus 𝒜 s :=
by { ext x, exact (submodule.gi _ _).gc s x.as_homogeneous_ideal.to_ideal }

variable {𝒜}
/-- The vanishing ideal of a set `t` of points of the projective spectrum of a commutative ring `R`
is the intersection of all the relevant homogeneous prime ideals in the set `t`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal) the function (i.e., element) `f` takes values in the
quotient ring `A` modulo the prime ideal `x`. In this manner, `vanishing_ideal t` is exactly the
ideal of `A` consisting of all "functions" that vanish on all of `t`. -/
def vanishing_ideal (t : set (projective_spectrum 𝒜)) : homogeneous_ideal 𝒜 :=
⨅ (x : projective_spectrum 𝒜) (h : x ∈ t), x.as_homogeneous_ideal

lemma coe_vanishing_ideal (t : set (projective_spectrum 𝒜)) :
  (vanishing_ideal t : set A) =
  {f | ∀ x : projective_spectrum 𝒜, x ∈ t → f ∈ x.as_homogeneous_ideal} :=
begin
  ext f,
  rw [vanishing_ideal, set_like.mem_coe, ← homogeneous_ideal.mem_iff,
    homogeneous_ideal.to_ideal_infi, submodule.mem_infi],
  apply forall_congr (λ x, _),
  rw [homogeneous_ideal.to_ideal_infi, submodule.mem_infi, homogeneous_ideal.mem_iff],
end

lemma mem_vanishing_ideal (t : set (projective_spectrum 𝒜)) (f : A) :
  f ∈ vanishing_ideal t ↔
  ∀ x : projective_spectrum 𝒜, x ∈ t → f ∈ x.as_homogeneous_ideal :=
by rw [← set_like.mem_coe, coe_vanishing_ideal, set.mem_set_of_eq]

@[simp] lemma vanishing_ideal_singleton (x : projective_spectrum 𝒜) :
  vanishing_ideal ({x} : set (projective_spectrum 𝒜)) = x.as_homogeneous_ideal :=
by simp [vanishing_ideal]

lemma subset_zero_locus_iff_le_vanishing_ideal (t : set (projective_spectrum 𝒜))
  (I : ideal A) :
  t ⊆ zero_locus 𝒜 I ↔ I ≤ (vanishing_ideal t).to_ideal :=
⟨λ h f k, (mem_vanishing_ideal _ _).mpr (λ x j, (mem_zero_locus _ _ _).mpr (h j) k), λ h,
  λ x j, (mem_zero_locus _ _ _).mpr (le_trans h (λ f h, ((mem_vanishing_ideal _ _).mp h) x j))⟩

variable (𝒜)
/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
lemma gc_ideal : @galois_connection
  (ideal A) (set (projective_spectrum 𝒜))ᵒᵈ _ _
  (λ I, zero_locus 𝒜 I) (λ t, (vanishing_ideal t).to_ideal) :=
λ I t, subset_zero_locus_iff_le_vanishing_ideal t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
lemma gc_set : @galois_connection
  (set A) (set (projective_spectrum 𝒜))ᵒᵈ _ _
  (λ s, zero_locus 𝒜 s) (λ t, vanishing_ideal t) :=
have ideal_gc : galois_connection (ideal.span) coe := (submodule.gi A _).gc,
by simpa [zero_locus_span, function.comp] using galois_connection.compose ideal_gc (gc_ideal 𝒜)

lemma gc_homogeneous_ideal : @galois_connection
  (homogeneous_ideal 𝒜) (set (projective_spectrum 𝒜))ᵒᵈ _ _
  (λ I, zero_locus 𝒜 I) (λ t, (vanishing_ideal t)) :=
λ I t, by simpa [show I.to_ideal ≤ (vanishing_ideal t).to_ideal ↔ I ≤ (vanishing_ideal t),
  from iff.rfl] using subset_zero_locus_iff_le_vanishing_ideal t I.to_ideal

lemma subset_zero_locus_iff_subset_vanishing_ideal (t : set (projective_spectrum 𝒜))
  (s : set A) :
  t ⊆ zero_locus 𝒜 s ↔ s ⊆ vanishing_ideal t :=
(gc_set _) s t

lemma subset_vanishing_ideal_zero_locus (s : set A) :
  s ⊆ vanishing_ideal (zero_locus 𝒜 s) :=
(gc_set _).le_u_l s

lemma ideal_le_vanishing_ideal_zero_locus (I : ideal A) :
  I ≤ (vanishing_ideal (zero_locus 𝒜 I)).to_ideal :=
(gc_ideal _).le_u_l I

lemma homogeneous_ideal_le_vanishing_ideal_zero_locus (I : homogeneous_ideal 𝒜) :
  I ≤ vanishing_ideal (zero_locus 𝒜 I) :=
(gc_homogeneous_ideal _).le_u_l I

lemma subset_zero_locus_vanishing_ideal (t : set (projective_spectrum 𝒜)) :
  t ⊆ zero_locus 𝒜 (vanishing_ideal t) :=
(gc_ideal _).l_u_le t

lemma zero_locus_anti_mono {s t : set A} (h : s ⊆ t) : zero_locus 𝒜 t ⊆ zero_locus 𝒜 s :=
(gc_set _).monotone_l h

lemma zero_locus_anti_mono_ideal {s t : ideal A} (h : s ≤ t) :
  zero_locus 𝒜 (t : set A) ⊆ zero_locus 𝒜 (s : set A) :=
(gc_ideal _).monotone_l h

lemma zero_locus_anti_mono_homogeneous_ideal {s t : homogeneous_ideal 𝒜} (h : s ≤ t) :
  zero_locus 𝒜 (t : set A) ⊆ zero_locus 𝒜 (s : set A) :=
(gc_homogeneous_ideal _).monotone_l h

lemma vanishing_ideal_anti_mono {s t : set (projective_spectrum 𝒜)} (h : s ⊆ t) :
  vanishing_ideal t ≤ vanishing_ideal s :=
(gc_ideal _).monotone_u h

lemma zero_locus_bot :
  zero_locus 𝒜 ((⊥ : ideal A) : set A) = set.univ :=
(gc_ideal 𝒜).l_bot

@[simp] lemma zero_locus_singleton_zero :
  zero_locus 𝒜 ({0} : set A) = set.univ :=
zero_locus_bot _

@[simp] lemma zero_locus_empty :
  zero_locus 𝒜 (∅ : set A) = set.univ :=
(gc_set 𝒜).l_bot

@[simp] lemma vanishing_ideal_univ :
  vanishing_ideal (∅ : set (projective_spectrum 𝒜)) = ⊤ :=
by simpa using (gc_ideal _).u_top

lemma zero_locus_empty_of_one_mem {s : set A} (h : (1:A) ∈ s) :
  zero_locus 𝒜 s = ∅ :=
set.eq_empty_iff_forall_not_mem.mpr $ λ x hx,
  (infer_instance : x.as_homogeneous_ideal.to_ideal.is_prime).ne_top $
  x.as_homogeneous_ideal.to_ideal.eq_top_iff_one.mpr $ hx h

@[simp] lemma zero_locus_singleton_one :
  zero_locus 𝒜 ({1} : set A) = ∅ :=
zero_locus_empty_of_one_mem 𝒜 (set.mem_singleton (1 : A))

@[simp] lemma zero_locus_univ :
  zero_locus 𝒜 (set.univ : set A) = ∅ :=
zero_locus_empty_of_one_mem _ (set.mem_univ 1)

lemma zero_locus_sup_ideal (I J : ideal A) :
  zero_locus 𝒜 ((I ⊔ J : ideal A) : set A) = zero_locus _ I ∩ zero_locus _ J :=
(gc_ideal 𝒜).l_sup

lemma zero_locus_sup_homogeneous_ideal (I J : homogeneous_ideal 𝒜) :
  zero_locus 𝒜 ((I ⊔ J : homogeneous_ideal 𝒜) : set A) = zero_locus _ I ∩ zero_locus _ J :=
(gc_homogeneous_ideal 𝒜).l_sup

lemma zero_locus_union (s s' : set A) :
  zero_locus 𝒜 (s ∪ s') = zero_locus _ s ∩ zero_locus _ s' :=
(gc_set 𝒜).l_sup

lemma vanishing_ideal_union (t t' : set (projective_spectrum 𝒜)) :
  vanishing_ideal (t ∪ t') = vanishing_ideal t ⊓ vanishing_ideal t' :=
by ext1; convert (gc_ideal 𝒜).u_inf

lemma zero_locus_supr_ideal {γ : Sort*} (I : γ → ideal A) :
  zero_locus _ ((⨆ i, I i : ideal A) : set A) = (⋂ i, zero_locus 𝒜 (I i)) :=
(gc_ideal 𝒜).l_supr

lemma zero_locus_supr_homogeneous_ideal {γ : Sort*} (I : γ → homogeneous_ideal 𝒜) :
  zero_locus _ ((⨆ i, I i : homogeneous_ideal 𝒜) : set A) = (⋂ i, zero_locus 𝒜 (I i)) :=
(gc_homogeneous_ideal 𝒜).l_supr

lemma zero_locus_Union {γ : Sort*} (s : γ → set A) :
  zero_locus 𝒜 (⋃ i, s i) = (⋂ i, zero_locus 𝒜 (s i)) :=
(gc_set 𝒜).l_supr

lemma zero_locus_bUnion (s : set (set A)) :
  zero_locus 𝒜 (⋃ s' ∈ s, s' : set A) = ⋂ s' ∈ s, zero_locus 𝒜 s' :=
by simp only [zero_locus_Union]

lemma vanishing_ideal_Union {γ : Sort*} (t : γ → set (projective_spectrum 𝒜)) :
  vanishing_ideal (⋃ i, t i) = (⨅ i, vanishing_ideal (t i)) :=
homogeneous_ideal.to_ideal_injective $
by convert (gc_ideal 𝒜).u_infi; exact homogeneous_ideal.to_ideal_infi _

lemma zero_locus_inf (I J : ideal A) :
  zero_locus 𝒜 ((I ⊓ J : ideal A) : set A) = zero_locus 𝒜 I ∪ zero_locus 𝒜 J :=
set.ext $ λ x, x.is_prime.inf_le

lemma union_zero_locus (s s' : set A) :
  zero_locus 𝒜 s ∪ zero_locus 𝒜 s' = zero_locus 𝒜 ((ideal.span s) ⊓ (ideal.span s'): ideal A) :=
by { rw zero_locus_inf, simp }

lemma zero_locus_mul_ideal (I J : ideal A) :
  zero_locus 𝒜 ((I * J : ideal A) : set A) = zero_locus 𝒜 I ∪ zero_locus 𝒜 J :=
set.ext $ λ x, x.is_prime.mul_le

lemma zero_locus_mul_homogeneous_ideal (I J : homogeneous_ideal 𝒜) :
  zero_locus 𝒜 ((I * J : homogeneous_ideal 𝒜) : set A) = zero_locus 𝒜 I ∪ zero_locus 𝒜 J :=
set.ext $ λ x, x.is_prime.mul_le

lemma zero_locus_singleton_mul (f g : A) :
  zero_locus 𝒜 ({f * g} : set A) = zero_locus 𝒜 {f} ∪ zero_locus 𝒜 {g} :=
set.ext $ λ x, by simpa using x.is_prime.mul_mem_iff_mem_or_mem

@[simp] lemma zero_locus_singleton_pow (f : A) (n : ℕ) (hn : 0 < n) :
  zero_locus 𝒜 ({f ^ n} : set A) = zero_locus 𝒜 {f} :=
set.ext $ λ x, by simpa using x.is_prime.pow_mem_iff_mem n hn

lemma sup_vanishing_ideal_le (t t' : set (projective_spectrum 𝒜)) :
  vanishing_ideal t ⊔ vanishing_ideal t' ≤ vanishing_ideal (t ∩ t') :=
begin
  intros r,
  rw [← homogeneous_ideal.mem_iff, homogeneous_ideal.to_ideal_sup, mem_vanishing_ideal,
    submodule.mem_sup],
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩,
  erw mem_vanishing_ideal at hf hg,
  apply submodule.add_mem; solve_by_elim
end

lemma mem_compl_zero_locus_iff_not_mem {f : A} {I : projective_spectrum 𝒜} :
  I ∈ (zero_locus 𝒜 {f} : set (projective_spectrum 𝒜))ᶜ ↔ f ∉ I.as_homogeneous_ideal :=
by rw [set.mem_compl_iff, mem_zero_locus, set.singleton_subset_iff]; refl

/-- The Zariski topology on the prime spectrum of a commutative ring is defined via the closed sets
of the topology: they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariski_topology : topological_space (projective_spectrum 𝒜) :=
topological_space.of_closed (set.range (projective_spectrum.zero_locus 𝒜))
  (⟨set.univ, by simp⟩)
  begin
    intros Zs h,
    rw set.sInter_eq_Inter,
    let f : Zs → set _ := λ i, classical.some (h i.2),
    have hf : ∀ i : Zs, ↑i = zero_locus 𝒜 (f i) := λ i, (classical.some_spec (h i.2)).symm,
    simp only [hf],
    exact ⟨_, zero_locus_Union 𝒜 _⟩
  end
  (by { rintros _ ⟨s, rfl⟩ _ ⟨t, rfl⟩, exact ⟨_, (union_zero_locus 𝒜 s t).symm⟩ })

/-- The underlying topology of `Proj` is the projective spectrum of graded ring `A`. -/
def Top : Top := Top.of (projective_spectrum 𝒜)

lemma is_open_iff (U : set (projective_spectrum 𝒜)) :
  is_open U ↔ ∃ s, Uᶜ = zero_locus 𝒜 s :=
by simp only [@eq_comm _ Uᶜ]; refl

lemma is_closed_iff_zero_locus (Z : set (projective_spectrum 𝒜)) :
  is_closed Z ↔ ∃ s, Z = zero_locus 𝒜 s :=
by rw [← is_open_compl_iff, is_open_iff, compl_compl]

lemma is_closed_zero_locus (s : set A) :
  is_closed (zero_locus 𝒜 s) :=
by { rw [is_closed_iff_zero_locus], exact ⟨s, rfl⟩ }

lemma zero_locus_vanishing_ideal_eq_closure (t : set (projective_spectrum 𝒜)) :
  zero_locus 𝒜 (vanishing_ideal t : set A) = closure t :=
begin
  apply set.subset.antisymm,
  { rintro x hx t' ⟨ht', ht⟩,
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zero_locus 𝒜 s,
    by rwa [is_closed_iff_zero_locus] at ht',
    rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht,
    exact set.subset.trans ht hx },
  { rw (is_closed_zero_locus _ _).closure_subset_iff,
    exact subset_zero_locus_vanishing_ideal 𝒜 t }
end

lemma vanishing_ideal_closure (t : set (projective_spectrum 𝒜)) :
  vanishing_ideal (closure t) = vanishing_ideal t :=
begin
  have := (gc_ideal 𝒜).u_l_u_eq_u t,
  dsimp only at this,
  ext1,
  erw zero_locus_vanishing_ideal_eq_closure 𝒜 t at this,
  exact this,
end

section basic_open

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basic_open (r : A) : topological_space.opens (projective_spectrum 𝒜) :=
{ carrier := { x | r ∉ x.as_homogeneous_ideal },
  is_open' := ⟨{r}, set.ext $ λ x, set.singleton_subset_iff.trans $ not_not.symm⟩ }

@[simp] lemma mem_basic_open (f : A) (x : projective_spectrum 𝒜) :
  x ∈ basic_open 𝒜 f ↔ f ∉ x.as_homogeneous_ideal := iff.rfl

lemma mem_coe_basic_open (f : A) (x : projective_spectrum 𝒜) :
  x ∈ (↑(basic_open 𝒜 f): set (projective_spectrum 𝒜)) ↔ f ∉ x.as_homogeneous_ideal := iff.rfl

lemma is_open_basic_open {a : A} : is_open ((basic_open 𝒜 a) :
  set (projective_spectrum 𝒜)) :=
(basic_open 𝒜 a).is_open

@[simp] lemma basic_open_eq_zero_locus_compl (r : A) :
  (basic_open 𝒜 r : set (projective_spectrum 𝒜)) = (zero_locus 𝒜 {r})ᶜ :=
set.ext $ λ x, by simpa only [set.mem_compl_iff, mem_zero_locus, set.singleton_subset_iff]

@[simp] lemma basic_open_one : basic_open 𝒜 (1 : A) = ⊤ :=
topological_space.opens.ext $ by simp

@[simp] lemma basic_open_zero : basic_open 𝒜 (0 : A) = ⊥ :=
topological_space.opens.ext $ by simp

lemma basic_open_mul (f g : A) : basic_open 𝒜 (f * g) = basic_open 𝒜 f ⊓ basic_open 𝒜 g :=
topological_space.opens.ext $ by {simp [zero_locus_singleton_mul]}

lemma basic_open_mul_le_left (f g : A) : basic_open 𝒜 (f * g) ≤ basic_open 𝒜 f :=
by { rw basic_open_mul 𝒜 f g, exact inf_le_left }

lemma basic_open_mul_le_right (f g : A) : basic_open 𝒜 (f * g) ≤ basic_open 𝒜 g :=
by { rw basic_open_mul 𝒜 f g, exact inf_le_right }

@[simp] lemma basic_open_pow (f : A) (n : ℕ) (hn : 0 < n) :
  basic_open 𝒜 (f ^ n) = basic_open 𝒜 f :=
topological_space.opens.ext $ by simpa using zero_locus_singleton_pow 𝒜 f n hn

lemma basic_open_eq_union_of_projection (f : A) :
  basic_open 𝒜 f = ⨆ (i : ℕ), basic_open 𝒜 (graded_algebra.proj 𝒜 i f) :=
topological_space.opens.ext $ set.ext $ λ z, begin
  erw [mem_coe_basic_open, topological_space.opens.mem_Sup],
  split; intros hz,
  { rcases show ∃ i, graded_algebra.proj 𝒜 i f ∉ z.as_homogeneous_ideal, begin
      contrapose! hz with H,
      classical,
      rw ←direct_sum.sum_support_decompose 𝒜 f,
      apply ideal.sum_mem _ (λ i hi, H i)
    end with ⟨i, hi⟩,
    exact ⟨basic_open 𝒜 (graded_algebra.proj 𝒜 i f), ⟨i, rfl⟩, by rwa mem_basic_open⟩ },
  { obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz,
    exact λ rid, hz (z.1.2 i rid) },
end

lemma is_topological_basis_basic_opens : topological_space.is_topological_basis
  (set.range (λ (r : A), (basic_open 𝒜 r : set (projective_spectrum 𝒜)))) :=
begin
  apply topological_space.is_topological_basis_of_open_of_nhds,
  { rintros _ ⟨r, rfl⟩,
    exact is_open_basic_open 𝒜 },
  { rintros p U hp ⟨s, hs⟩,
    rw [← compl_compl U, set.mem_compl_iff, ← hs, mem_zero_locus, set.not_subset] at hp,
    obtain ⟨f, hfs, hfp⟩ := hp,
    refine ⟨basic_open 𝒜 f, ⟨f, rfl⟩, hfp, _⟩,
    rw [← set.compl_subset_compl, ← hs, basic_open_eq_zero_locus_compl, compl_compl],
    exact zero_locus_anti_mono 𝒜 (set.singleton_subset_iff.mpr hfs) }
end

end basic_open

section order

/-!
## The specialization order

We endow `projective_spectrum 𝒜` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.
-/

instance : partial_order (projective_spectrum 𝒜) :=
partial_order.lift as_homogeneous_ideal $ λ ⟨_, _, _⟩ ⟨_, _, _⟩, mk.inj_eq.mpr

@[simp] lemma as_ideal_le_as_ideal (x y : projective_spectrum 𝒜) :
  x.as_homogeneous_ideal ≤ y.as_homogeneous_ideal ↔ x ≤ y :=
iff.rfl

@[simp] lemma as_ideal_lt_as_ideal (x y : projective_spectrum 𝒜) :
  x.as_homogeneous_ideal < y.as_homogeneous_ideal ↔ x < y :=
iff.rfl

lemma le_iff_mem_closure (x y : projective_spectrum 𝒜) :
  x ≤ y ↔ y ∈ closure ({x} : set (projective_spectrum 𝒜)) :=
begin
  rw [← as_ideal_le_as_ideal, ← zero_locus_vanishing_ideal_eq_closure,
    mem_zero_locus, vanishing_ideal_singleton],
  simp only [coe_subset_coe, subtype.coe_le_coe, coe_coe],
end

end order

end projective_spectrum
