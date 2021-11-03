/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import topology.opens
import ring_theory.ideal.prod
import ring_theory.ideal.over
import linear_algebra.finsupp
import algebra.punit_instances

/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `algebraic_geometry.structure_sheaf`.)

## Main definitions

* `prime_spectrum R`: The prime spectrum of a commutative ring `R`,
  i.e., the set of all prime ideals of `R`.
* `zero_locus s`: The zero locus of a subset `s` of `R`
  is the subset of `prime_spectrum R` consisting of all prime ideals that contain `s`.
* `vanishing_ideal t`: The vanishing ideal of a subset `t` of `prime_spectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from
<https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

-/

noncomputable theory
open_locale classical

universes u v

variables (R : Type u) [comm_ring R]

/-- The prime spectrum of a commutative ring `R`
is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `algebraic_geometry.structure_sheaf`).
It is a fundamental building block in algebraic geometry. -/
@[nolint has_inhabited_instance]
def prime_spectrum := {I : ideal R // I.is_prime}

variable {R}

namespace prime_spectrum

/-- A method to view a point in the prime spectrum of a commutative ring
as an ideal of that ring. -/
abbreviation as_ideal (x : prime_spectrum R) : ideal R := x.val

instance is_prime (x : prime_spectrum R) :
  x.as_ideal.is_prime := x.2

/--
The prime spectrum of the zero ring is empty.
-/
lemma punit (x : prime_spectrum punit) : false :=
x.1.ne_top_iff_one.1 x.2.1 $ subsingleton.elim (0 : punit) 1 ▸ x.1.zero_mem

section
variables (R) (S : Type v) [comm_ring S]

/-- The prime spectrum of `R × S` is in bijection with the disjoint unions of the prime spectrum of
    `R` and the prime spectrum of `S`. -/
noncomputable def prime_spectrum_prod :
  prime_spectrum (R × S) ≃ prime_spectrum R ⊕ prime_spectrum S :=
ideal.prime_ideals_equiv R S

variables {R S}

@[simp] lemma prime_spectrum_prod_symm_inl_as_ideal (x : prime_spectrum R) :
  ((prime_spectrum_prod R S).symm (sum.inl x)).as_ideal = ideal.prod x.as_ideal ⊤ :=
by { cases x, refl }
@[simp] lemma prime_spectrum_prod_symm_inr_as_ideal (x : prime_spectrum S) :
  ((prime_spectrum_prod R S).symm (sum.inr x)).as_ideal = ideal.prod ⊤ x.as_ideal :=
by { cases x, refl }

end

@[ext] lemma ext {x y : prime_spectrum R} :
  x = y ↔ x.as_ideal = y.as_ideal :=
subtype.ext_iff_val

/-- The zero locus of a set `s` of elements of a commutative ring `R`
is the set of all prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `prime_spectrum R`
where all "functions" in `s` vanish simultaneously.
-/
def zero_locus (s : set R) : set (prime_spectrum R) :=
{x | s ⊆ x.as_ideal}

@[simp] lemma mem_zero_locus (x : prime_spectrum R) (s : set R) :
  x ∈ zero_locus s ↔ s ⊆ x.as_ideal := iff.rfl

@[simp] lemma zero_locus_span (s : set R) :
  zero_locus (ideal.span s : set R) = zero_locus s :=
by { ext x, exact (submodule.gi R R).gc s x.as_ideal }

/-- The vanishing ideal of a set `t` of points
of the prime spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishing_ideal (t : set (prime_spectrum R)) : ideal R :=
⨅ (x : prime_spectrum R) (h : x ∈ t), x.as_ideal

lemma coe_vanishing_ideal (t : set (prime_spectrum R)) :
  (vanishing_ideal t : set R) = {f : R | ∀ x : prime_spectrum R, x ∈ t → f ∈ x.as_ideal} :=
begin
  ext f,
  rw [vanishing_ideal, set_like.mem_coe, submodule.mem_infi],
  apply forall_congr, intro x,
  rw [submodule.mem_infi],
end

lemma mem_vanishing_ideal (t : set (prime_spectrum R)) (f : R) :
  f ∈ vanishing_ideal t ↔ ∀ x : prime_spectrum R, x ∈ t → f ∈ x.as_ideal :=
by rw [← set_like.mem_coe, coe_vanishing_ideal, set.mem_set_of_eq]

@[simp] lemma vanishing_ideal_singleton (x : prime_spectrum R) :
  vanishing_ideal ({x} : set (prime_spectrum R)) = x.as_ideal :=
by simp [vanishing_ideal]

lemma subset_zero_locus_iff_le_vanishing_ideal (t : set (prime_spectrum R)) (I : ideal R) :
  t ⊆ zero_locus I ↔ I ≤ vanishing_ideal t :=
⟨λ h f k, (mem_vanishing_ideal _ _).mpr (λ x j, (mem_zero_locus _ _).mpr (h j) k), λ h,
  λ x j, (mem_zero_locus _ _).mpr (le_trans h (λ f h, ((mem_vanishing_ideal _ _).mp h) x j))⟩

section gc
variable (R)

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
lemma gc : @galois_connection
  (ideal R) (order_dual (set (prime_spectrum R))) _ _
  (λ I, zero_locus I) (λ t, vanishing_ideal t) :=
λ I t, subset_zero_locus_iff_le_vanishing_ideal t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
lemma gc_set : @galois_connection
  (set R) (order_dual (set (prime_spectrum R))) _ _
  (λ s, zero_locus s) (λ t, vanishing_ideal t) :=
have ideal_gc : galois_connection (ideal.span) coe := (submodule.gi R R).gc,
by simpa [zero_locus_span, function.comp] using ideal_gc.compose (gc R)

lemma subset_zero_locus_iff_subset_vanishing_ideal (t : set (prime_spectrum R)) (s : set R) :
  t ⊆ zero_locus s ↔ s ⊆ vanishing_ideal t :=
(gc_set R) s t

end gc

lemma subset_vanishing_ideal_zero_locus (s : set R) :
  s ⊆ vanishing_ideal (zero_locus s) :=
(gc_set R).le_u_l s

lemma le_vanishing_ideal_zero_locus (I : ideal R) :
  I ≤ vanishing_ideal (zero_locus I) :=
(gc R).le_u_l I

@[simp] lemma vanishing_ideal_zero_locus_eq_radical (I : ideal R) :
  vanishing_ideal (zero_locus (I : set R)) = I.radical := ideal.ext $ λ f,
begin
  rw [mem_vanishing_ideal, ideal.radical_eq_Inf, submodule.mem_Inf],
  exact ⟨(λ h x hx, h ⟨x, hx.2⟩ hx.1), (λ h x hx, h x.1 ⟨hx, x.2⟩)⟩
end

@[simp] lemma zero_locus_radical (I : ideal R) : zero_locus (I.radical : set R) = zero_locus I :=
vanishing_ideal_zero_locus_eq_radical I ▸ (gc R).l_u_l_eq_l I

lemma subset_zero_locus_vanishing_ideal (t : set (prime_spectrum R)) :
  t ⊆ zero_locus (vanishing_ideal t) :=
(gc R).l_u_le t

lemma zero_locus_anti_mono {s t : set R} (h : s ⊆ t) : zero_locus t ⊆ zero_locus s :=
(gc_set R).monotone_l h

lemma zero_locus_anti_mono_ideal {s t : ideal R} (h : s ≤ t) :
  zero_locus (t : set R) ⊆ zero_locus (s : set R) :=
(gc R).monotone_l h

lemma vanishing_ideal_anti_mono {s t : set (prime_spectrum R)} (h : s ⊆ t) :
  vanishing_ideal t ≤ vanishing_ideal s :=
(gc R).monotone_u h

lemma zero_locus_subset_zero_locus_iff (I J : ideal R) :
  zero_locus (I : set R) ⊆ zero_locus (J : set R) ↔ J ≤ I.radical :=
⟨λ h, ideal.radical_le_radical_iff.mp (vanishing_ideal_zero_locus_eq_radical I ▸
  vanishing_ideal_zero_locus_eq_radical J ▸ vanishing_ideal_anti_mono h),
λ h, zero_locus_radical I ▸ zero_locus_anti_mono_ideal h⟩

lemma zero_locus_subset_zero_locus_singleton_iff (f g : R) :
  zero_locus ({f} : set R) ⊆ zero_locus {g} ↔ g ∈ (ideal.span ({f} : set R)).radical :=
by rw [← zero_locus_span {f}, ← zero_locus_span {g}, zero_locus_subset_zero_locus_iff,
    ideal.span_le, set.singleton_subset_iff, set_like.mem_coe]

lemma zero_locus_bot :
  zero_locus ((⊥ : ideal R) : set R) = set.univ :=
(gc R).l_bot

@[simp] lemma zero_locus_singleton_zero :
  zero_locus ({0} : set R) = set.univ :=
zero_locus_bot

@[simp] lemma zero_locus_empty :
  zero_locus (∅ : set R) = set.univ :=
(gc_set R).l_bot

@[simp] lemma vanishing_ideal_univ :
  vanishing_ideal (∅ : set (prime_spectrum R)) = ⊤ :=
by simpa using (gc R).u_top

lemma zero_locus_empty_of_one_mem {s : set R} (h : (1:R) ∈ s) :
  zero_locus s = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros x hx,
  rw mem_zero_locus at hx,
  have x_prime : x.as_ideal.is_prime := by apply_instance,
  have eq_top : x.as_ideal = ⊤, { rw ideal.eq_top_iff_one, exact hx h },
  apply x_prime.ne_top eq_top,
end

@[simp] lemma zero_locus_singleton_one :
  zero_locus ({1} : set R) = ∅ :=
zero_locus_empty_of_one_mem (set.mem_singleton (1 : R))

lemma zero_locus_empty_iff_eq_top {I : ideal R} :
  zero_locus (I : set R) = ∅ ↔ I = ⊤ :=
begin
  split,
  { contrapose!,
    intro h,
    apply set.ne_empty_iff_nonempty.mpr,
    rcases ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩,
    exact ⟨⟨M, hM.is_prime⟩, hIM⟩ },
  { rintro rfl, apply zero_locus_empty_of_one_mem, trivial }
end

@[simp] lemma zero_locus_univ :
  zero_locus (set.univ : set R) = ∅ :=
zero_locus_empty_of_one_mem (set.mem_univ 1)

lemma zero_locus_sup (I J : ideal R) :
  zero_locus ((I ⊔ J : ideal R) : set R) = zero_locus I ∩ zero_locus J :=
(gc R).l_sup

lemma zero_locus_union (s s' : set R) :
  zero_locus (s ∪ s') = zero_locus s ∩ zero_locus s' :=
(gc_set R).l_sup

lemma vanishing_ideal_union (t t' : set (prime_spectrum R)) :
  vanishing_ideal (t ∪ t') = vanishing_ideal t ⊓ vanishing_ideal t' :=
(gc R).u_inf

lemma zero_locus_supr {ι : Sort*} (I : ι → ideal R) :
  zero_locus ((⨆ i, I i : ideal R) : set R) = (⋂ i, zero_locus (I i)) :=
(gc R).l_supr

lemma zero_locus_Union {ι : Sort*} (s : ι → set R) :
  zero_locus (⋃ i, s i) = (⋂ i, zero_locus (s i)) :=
(gc_set R).l_supr

lemma zero_locus_bUnion (s : set (set R)) :
  zero_locus (⋃ s' ∈ s, s' : set R) = ⋂ s' ∈ s, zero_locus s' :=
by simp only [zero_locus_Union]

lemma vanishing_ideal_Union {ι : Sort*} (t : ι → set (prime_spectrum R)) :
  vanishing_ideal (⋃ i, t i) = (⨅ i, vanishing_ideal (t i)) :=
(gc R).u_infi

lemma zero_locus_inf (I J : ideal R) :
  zero_locus ((I ⊓ J : ideal R) : set R) = zero_locus I ∪ zero_locus J :=
set.ext $ λ x, by simpa using x.2.inf_le

lemma union_zero_locus (s s' : set R) :
  zero_locus s ∪ zero_locus s' = zero_locus ((ideal.span s) ⊓ (ideal.span s') : ideal R) :=
by { rw zero_locus_inf, simp }

lemma zero_locus_mul (I J : ideal R) :
  zero_locus ((I * J : ideal R) : set R) = zero_locus I ∪ zero_locus J :=
set.ext $ λ x, by simpa using x.2.mul_le

lemma zero_locus_singleton_mul (f g : R) :
  zero_locus ({f * g} : set R) = zero_locus {f} ∪ zero_locus {g} :=
set.ext $ λ x, by simpa using x.2.mul_mem_iff_mem_or_mem

@[simp] lemma zero_locus_pow (I : ideal R) {n : ℕ} (hn : 0 < n) :
  zero_locus ((I ^ n : ideal R) : set R) = zero_locus I :=
zero_locus_radical (I ^ n) ▸ (I.radical_pow n hn).symm ▸ zero_locus_radical I

@[simp] lemma zero_locus_singleton_pow (f : R) (n : ℕ) (hn : 0 < n) :
  zero_locus ({f ^ n} : set R) = zero_locus {f} :=
set.ext $ λ x, by simpa using x.2.pow_mem_iff_mem n hn

lemma sup_vanishing_ideal_le (t t' : set (prime_spectrum R)) :
  vanishing_ideal t ⊔ vanishing_ideal t' ≤ vanishing_ideal (t ∩ t') :=
begin
  intros r,
  rw [submodule.mem_sup, mem_vanishing_ideal],
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩,
  rw mem_vanishing_ideal at hf hg,
  apply submodule.add_mem; solve_by_elim
end

lemma mem_compl_zero_locus_iff_not_mem {f : R} {I : prime_spectrum R} :
  I ∈ (zero_locus {f} : set (prime_spectrum R))ᶜ ↔ f ∉ I.as_ideal :=
by rw [set.mem_compl_eq, mem_zero_locus, set.singleton_subset_iff]; refl

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariski_topology : topological_space (prime_spectrum R) :=
topological_space.of_closed (set.range prime_spectrum.zero_locus)
  (⟨set.univ, by simp⟩)
  begin
    intros Zs h,
    rw set.sInter_eq_Inter,
    let f : Zs → set R := λ i, classical.some (h i.2),
    have hf : ∀ i : Zs, ↑i = zero_locus (f i) := λ i, (classical.some_spec (h i.2)).symm,
    simp only [hf],
    exact ⟨_, zero_locus_Union _⟩
  end
  (by { rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩, exact ⟨_, (union_zero_locus s t).symm⟩ })

lemma is_open_iff (U : set (prime_spectrum R)) :
  is_open U ↔ ∃ s, Uᶜ = zero_locus s :=
by simp only [@eq_comm _ Uᶜ]; refl

lemma is_closed_iff_zero_locus (Z : set (prime_spectrum R)) :
  is_closed Z ↔ ∃ s, Z = zero_locus s :=
by rw [← is_open_compl_iff, is_open_iff, compl_compl]

lemma is_closed_zero_locus (s : set R) :
  is_closed (zero_locus s) :=
by { rw [is_closed_iff_zero_locus], exact ⟨s, rfl⟩ }

lemma is_closed_singleton_iff_is_maximal (x : prime_spectrum R) :
  is_closed ({x} : set (prime_spectrum R)) ↔ x.as_ideal.is_maximal :=
begin
  refine (is_closed_iff_zero_locus _).trans ⟨λ h, _, λ h, _⟩,
  { obtain ⟨s, hs⟩ := h,
    rw [eq_comm, set.eq_singleton_iff_unique_mem] at hs,
    refine ⟨⟨x.2.1, λ I hI, not_not.1 (mt (ideal.exists_le_maximal I) $
      not_exists.2 (λ J, not_and.2 $ λ hJ hIJ,_))⟩⟩,
    exact ne_of_lt (lt_of_lt_of_le hI hIJ) (symm $ congr_arg prime_spectrum.as_ideal
      (hs.2 ⟨J, hJ.is_prime⟩ (λ r hr, hIJ (le_of_lt hI $ hs.1 hr)))) },
  { refine ⟨x.as_ideal.1, _⟩,
    rw [eq_comm, set.eq_singleton_iff_unique_mem],
    refine ⟨λ _ h, h, λ y hy, prime_spectrum.ext.2 (h.eq_of_le y.2.ne_top hy).symm⟩ }
end

lemma zero_locus_vanishing_ideal_eq_closure (t : set (prime_spectrum R)) :
  zero_locus (vanishing_ideal t : set R) = closure t :=
begin
  apply set.subset.antisymm,
  { rintro x hx t' ⟨ht', ht⟩,
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zero_locus s,
    by rwa [is_closed_iff_zero_locus] at ht',
    rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht,
    exact set.subset.trans ht hx },
  { rw (is_closed_zero_locus _).closure_subset_iff,
    exact subset_zero_locus_vanishing_ideal t }
end

lemma vanishing_ideal_closure (t : set (prime_spectrum R)) :
  vanishing_ideal (closure t) = vanishing_ideal t :=
zero_locus_vanishing_ideal_eq_closure t ▸ (gc R).u_l_u_eq_u t

lemma t1_space_iff_is_field [is_domain R] :
  t1_space (prime_spectrum R) ↔ is_field R :=
begin
  refine ⟨_, λ h, _⟩,
  { introI h,
    have hbot : ideal.is_prime (⊥ : ideal R) := ideal.bot_prime,
    exact not_not.1 (mt (ring.ne_bot_of_is_maximal_of_not_is_field $
      (is_closed_singleton_iff_is_maximal _).1 (t1_space.t1 ⟨⊥, hbot⟩)) (not_not.2 rfl)) },
  { refine ⟨λ x, (is_closed_singleton_iff_is_maximal x).2 _⟩,
    by_cases hx : x.as_ideal = ⊥,
    { exact hx.symm ▸ @ideal.bot_is_maximal R (@field.to_division_ring _ $ is_field.to_field R h) },
    { exact absurd h (ring.not_is_field_iff_exists_prime.2 ⟨x.as_ideal, ⟨hx, x.2⟩⟩) } }
end

section comap
variables {S : Type v} [comm_ring S] {S' : Type*} [comm_ring S']

/-- The function between prime spectra of commutative rings induced by a ring homomorphism.
This function is continuous. -/
def comap (f : R →+* S) : prime_spectrum S → prime_spectrum R :=
λ y, ⟨ideal.comap f y.as_ideal, infer_instance⟩

variables (f : R →+* S)

@[simp] lemma comap_as_ideal (y : prime_spectrum S) :
  (comap f y).as_ideal = ideal.comap f y.as_ideal :=
rfl

@[simp] lemma comap_id : comap (ring_hom.id R) = id :=
funext $ λ _, subtype.ext $ ideal.ext $ λ _, iff.rfl

@[simp] lemma comap_comp (f : R →+* S) (g : S →+* S') :
  comap (g.comp f) = comap f ∘ comap g :=
funext $ λ _, subtype.ext $ ideal.ext $ λ _, iff.rfl

@[simp] lemma preimage_comap_zero_locus (s : set R) :
  (comap f) ⁻¹' (zero_locus s) = zero_locus (f '' s) :=
begin
  ext x,
  simp only [mem_zero_locus, set.mem_preimage, comap_as_ideal, set.image_subset_iff],
  refl
end

lemma comap_injective_of_surjective (f : R →+* S) (hf : function.surjective f) :
  function.injective (comap f) :=
λ x y h, prime_spectrum.ext.2 (ideal.comap_injective_of_surjective f hf
  (congr_arg prime_spectrum.as_ideal h : (comap f x).as_ideal = (comap f y).as_ideal))

lemma comap_continuous (f : R →+* S) : continuous (comap f) :=
begin
  rw continuous_iff_is_closed,
  simp only [is_closed_iff_zero_locus],
  rintro _ ⟨s, rfl⟩,
  exact ⟨_, preimage_comap_zero_locus f s⟩
end

lemma comap_singleton_is_closed_of_surjective (f : R →+* S) (hf : function.surjective f)
  (x : prime_spectrum S) (hx : is_closed ({x} : set (prime_spectrum S))) :
  is_closed ({comap f x} : set (prime_spectrum R)) :=
begin
  haveI : x.as_ideal.is_maximal := (is_closed_singleton_iff_is_maximal x).1 hx,
  exact (is_closed_singleton_iff_is_maximal _).2 (ideal.comap_is_maximal_of_surjective f hf)
end

lemma comap_singleton_is_closed_of_is_integral (f : R →+* S) (hf : f.is_integral)
  (x : prime_spectrum S) (hx : is_closed ({x} : set (prime_spectrum S))) :
  is_closed ({comap f x} : set (prime_spectrum R)) :=
(is_closed_singleton_iff_is_maximal _).2 (ideal.is_maximal_comap_of_is_integral_of_is_maximal'
  f hf x.as_ideal $ (is_closed_singleton_iff_is_maximal x).1 hx)

end comap

section basic_open

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basic_open (r : R) : topological_space.opens (prime_spectrum R) :=
{ val := { x | r ∉ x.as_ideal },
  property := ⟨{r}, set.ext $ λ x, set.singleton_subset_iff.trans $ not_not.symm⟩ }

@[simp] lemma mem_basic_open (f : R) (x : prime_spectrum R) :
  x ∈ basic_open f ↔ f ∉ x.as_ideal := iff.rfl

lemma is_open_basic_open {a : R} : is_open ((basic_open a) : set (prime_spectrum R)) :=
(basic_open a).property

@[simp] lemma basic_open_eq_zero_locus_compl (r : R) :
  (basic_open r : set (prime_spectrum R)) = (zero_locus {r})ᶜ :=
set.ext $ λ x, by simpa only [set.mem_compl_eq, mem_zero_locus, set.singleton_subset_iff]

@[simp] lemma basic_open_one : basic_open (1 : R) = ⊤ :=
topological_space.opens.ext $ by {simp, refl}

@[simp] lemma basic_open_zero : basic_open (0 : R) = ⊥ :=
topological_space.opens.ext $ by {simp, refl}

lemma basic_open_le_basic_open_iff (f g : R) :
  basic_open f ≤ basic_open g ↔ f ∈ (ideal.span ({g} : set R)).radical :=
by rw [topological_space.opens.le_def, basic_open_eq_zero_locus_compl,
    basic_open_eq_zero_locus_compl, set.le_eq_subset, set.compl_subset_compl,
    zero_locus_subset_zero_locus_singleton_iff]

lemma basic_open_mul (f g : R) : basic_open (f * g) = basic_open f ⊓ basic_open g :=
topological_space.opens.ext $ by {simp [zero_locus_singleton_mul]}

lemma basic_open_mul_le_left (f g : R) : basic_open (f * g) ≤ basic_open f :=
by { rw basic_open_mul f g, exact inf_le_left }

lemma basic_open_mul_le_right (f g : R) : basic_open (f * g) ≤ basic_open g :=
by { rw basic_open_mul f g, exact inf_le_right }

@[simp] lemma basic_open_pow (f : R) (n : ℕ) (hn : 0 < n) : basic_open (f ^ n) = basic_open f :=
topological_space.opens.ext $ by simpa using zero_locus_singleton_pow f n hn

lemma is_topological_basis_basic_opens : topological_space.is_topological_basis
  (set.range (λ (r : R), (basic_open r : set (prime_spectrum R)))) :=
begin
  apply topological_space.is_topological_basis_of_open_of_nhds,
  { rintros _ ⟨r, rfl⟩,
    exact is_open_basic_open },
  { rintros p U hp ⟨s, hs⟩,
    rw [← compl_compl U, set.mem_compl_eq, ← hs, mem_zero_locus, set.not_subset] at hp,
    obtain ⟨f, hfs, hfp⟩ := hp,
    refine ⟨basic_open f, ⟨f, rfl⟩, hfp, _⟩,
    rw [← set.compl_subset_compl, ← hs, basic_open_eq_zero_locus_compl, compl_compl],
    exact zero_locus_anti_mono (set.singleton_subset_iff.mpr hfs) }
end

lemma is_compact_basic_open (f : R) : is_compact (basic_open f : set (prime_spectrum R)) :=
is_compact_of_finite_subfamily_closed $ λ ι Z hZc hZ,
begin
  let I : ι → ideal R := λ i, vanishing_ideal (Z i),
  have hI : ∀ i, Z i = zero_locus (I i) := λ i,
    by simpa only [zero_locus_vanishing_ideal_eq_closure] using (hZc i).closure_eq.symm,
  rw [basic_open_eq_zero_locus_compl f, set.inter_comm, ← set.diff_eq,
      set.diff_eq_empty, funext hI, ← zero_locus_supr] at hZ,
  obtain ⟨n, hn⟩ : f ∈ (⨆ (i : ι), I i).radical,
  { rw ← vanishing_ideal_zero_locus_eq_radical,
    apply vanishing_ideal_anti_mono hZ,
    exact (subset_vanishing_ideal_zero_locus {f} (set.mem_singleton f)) },
  rcases submodule.exists_finset_of_mem_supr I hn with ⟨s, hs⟩,
  use s,
  -- Using simp_rw here, because `hI` and `zero_locus_supr` need to be applied underneath binders
  simp_rw [basic_open_eq_zero_locus_compl f, set.inter_comm, ← set.diff_eq,
           set.diff_eq_empty, hI, ← zero_locus_supr],
  rw ← zero_locus_radical, -- this one can't be in `simp_rw` because it would loop
  apply zero_locus_anti_mono,
  rw set.singleton_subset_iff,
  exact ⟨n, hs⟩
end

end basic_open

/-- The prime spectrum of a commutative ring is a compact topological space. -/
instance : compact_space (prime_spectrum R) :=
{ compact_univ := by { convert is_compact_basic_open (1 : R), rw basic_open_one, refl } }

section order

/-!
## The specialization order

We endow `prime_spectrum R` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.

TODO: maybe define sober topological spaces, and generalise this instance to those
-/

instance : partial_order (prime_spectrum R) :=
subtype.partial_order _

@[simp] lemma as_ideal_le_as_ideal (x y : prime_spectrum R) :
  x.as_ideal ≤ y.as_ideal ↔ x ≤ y :=
subtype.coe_le_coe

@[simp] lemma as_ideal_lt_as_ideal (x y : prime_spectrum R) :
  x.as_ideal < y.as_ideal ↔ x < y :=
subtype.coe_lt_coe

lemma le_iff_mem_closure (x y : prime_spectrum R) :
  x ≤ y ↔ y ∈ closure ({x} : set (prime_spectrum R)) :=
by rw [← as_ideal_le_as_ideal, ← zero_locus_vanishing_ideal_eq_closure,
    mem_zero_locus, vanishing_ideal_singleton, set_like.coe_subset_coe]

end order

end prime_spectrum
