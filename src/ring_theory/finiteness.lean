/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.noetherian
import ring_theory.ideal.operations
import ring_theory.algebra_tower

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `module.finite`, `algebra.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `algebra.finite_type`, `ring_hom.finite_type`, `alg_hom.finite_type`
  all of these express that some object is finitely generated *as algebra* over some base ring.

-/

open function (surjective)
open_locale big_operators

namespace module

variables (R M N : Type*) [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

/-- A module over a commutative ring is `finite` if it is finitely generated as a module. -/
def finite : Prop := (⊤ : submodule R M).fg

namespace finite

variables {R M N}

lemma of_surjective (hM : finite R M) (f : M →ₗ[R] N) (hf : surjective f) :
  finite R N :=
begin
  rw [← linear_map.range_eq_top, ← submodule.map_top] at hf,
  rw [finite, ← hf],
  exact submodule.fg_map hM
end

variables (R)

lemma self : finite R R :=
⟨{1}, by simpa only [finset.coe_singleton] using ideal.span_singleton_one⟩

variables {R}

lemma prod (hM : finite R M) (hN : finite R N) : finite R (M × N) :=
begin
  rw [finite, ← submodule.prod_top],
  exact submodule.fg_prod hM hN
end

lemma equiv (hM : finite R M) (e : M ≃ₗ[R] N) : finite R N :=
hM.of_surjective e e.surjective

end finite

end module

namespace algebra
variables (R A B : Type*) [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]

/-- An algebra over a commutative ring is `finite`
if it is finitely generated as module over the base ring. -/
def finite : Prop := module.finite R A

/-- An algebra over a commutative ring is of `finite_type` if it is finitely generated
over the base ring as algebra. -/
def finite_type : Prop := (⊤ : subalgebra R A).fg

namespace finite

variables {R A B}

lemma of_surjective (hM : finite R A) (f : A →ₐ[R] B) (hf : surjective f) :
  finite R B :=
hM.of_surjective f.to_linear_map hf

variables (R)

lemma self : finite R R := module.finite.self R

variables {R}

-- move this
instance : algebra R (A × B) :=
{ commutes' := by { rintro r ⟨a, b⟩, dsimp, rw [commutes r a, commutes r b] },
  smul_def' := by { rintro r ⟨a, b⟩, dsimp, rw [smul_def r a, smul_def r b] },
  .. (show module R (A × B), by apply_instance),
  .. ring_hom.prod (algebra_map R A) (algebra_map R B) }

lemma prod (hRA : finite R A) (hRB : finite R B) : finite R (A × B) :=
module.finite.prod hRA hRB

lemma equiv (hRA : finite R A) (e : A ≃ₐ[R] B) : finite R B :=
hRA.of_surjective e e.surjective

lemma trans [algebra A B] [is_scalar_tower R A B] (hRA : finite R A) (hAB : finite A B) :
  finite R B :=
begin
  classical,
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := ⟨hRA, hAB⟩,
  refine ⟨s.bind (λ a, t.bind (λ b, {a • b})), _⟩,
  rw submodule.eq_top_iff',
  intro b,
  obtain ⟨f, rfl⟩ : ∃ (f : B → A), ∑ i in t, f i • i = b,
  { rw [← mem_span_finset, ht], trivial },
  refine submodule.sum_mem _ _,
  intros b hb,
  obtain ⟨g, hg⟩ : ∃ g : A → R, ∑ i in s, g i • i = f b,
  { rw [← mem_span_finset, hs], trivial },
  rw [← hg, finset.sum_smul],
  refine submodule.sum_mem _ _,
  intros a ha,
  rw smul_assoc,
  apply submodule.smul_mem _ _ _,
  apply submodule.subset_span,
  simp only [finset.bUnion_coe, exists_prop, set.mem_Union, finset.coe_bind,
    set.mem_singleton_iff, finset.coe_singleton],
  exact ⟨a, ha, b, hb, rfl⟩
end

lemma finite_type (hRA : finite R A) : finite_type R A :=
subalgebra.fg_of_submodule_fg hRA

end finite

namespace finite_type

lemma self : finite_type R R := ⟨{1}, subsingleton.elim _ _⟩

variables {R A B}

lemma of_surjective (hRA : finite_type R A) (f : A →ₐ[R] B) (hf : surjective f) :
  finite_type R B :=
begin
  rw [finite_type] at hRA ⊢,
  convert subalgebra.fg_map _ f hRA,
  simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, alg_hom.mem_range] using hf
end

lemma equiv (hRA : finite_type R A) (e : A ≃ₐ[R] B) : finite_type R B :=
hRA.of_surjective e e.surjective

lemma trans [algebra A B] [is_scalar_tower R A B] (hRA : finite_type R A) (hAB : finite_type A B) :
  finite_type R B :=
fg_trans' hRA hAB

end finite_type

end algebra

namespace ring_hom
variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C]

/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def finite (f : A →+* B) : Prop := @algebra.finite A B _ _ f.to_algebra

/-- A ring morphism `A →+* B` is of `finite_type` if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →+* B) : Prop := @algebra.finite_type A B _ _ f.to_algebra

namespace finite

variables (A)

lemma id : finite (ring_hom.id A) := algebra.finite.self A

variables {A}

lemma comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite) (hg : surjective g) :
  (g.comp f).finite :=
@algebra.finite.of_surjective A B C _ _ f.to_algebra _ (g.comp f).to_algebra hf
{ to_fun := g, commutes' := λ a, rfl, .. g } hg

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite :=
by { rw ← f.comp_id, exact (id A).comp_surjective hf }

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
@algebra.finite.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

lemma finite_type {f : A →+* B} (hf : f.finite) : finite_type f :=
@algebra.finite.finite_type _ _ _ _ f.to_algebra hf

end finite

namespace finite_type

variables (A)

lemma id : finite_type (ring_hom.id A) := algebra.finite_type.self A

variables {A}

lemma comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.finite_type) (hg : surjective g) :
  (g.comp f).finite_type :=
@algebra.finite_type.of_surjective A B C _ _ f.to_algebra _ (g.comp f).to_algebra hf
{ to_fun := g, commutes' := λ a, rfl, .. g } hg

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite_type :=
by { rw ← f.comp_id, exact (id A).comp_surjective hf }

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite_type) (hf : f.finite_type) :
  (g.comp f).finite_type :=
@algebra.finite_type.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

end finite_type

end ring_hom

namespace alg_hom

variables {R A B C : Type*} [comm_ring R]
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra R A] [algebra R B] [algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def finite (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite

/-- An algebra morphism `A →ₐ[R] B` is of `finite_type` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def finite_type (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite_type

namespace finite

variables (R A)

lemma id : finite (alg_hom.id R A) := ring_hom.finite.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
ring_hom.finite.comp hg hf

lemma comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite) (hg : surjective g) :
  (g.comp f).finite :=
ring_hom.finite.comp_surjective hf hg

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite :=
ring_hom.finite.of_surjective f hf

lemma finite_type {f : A →ₐ[R] B} (hf : f.finite) : finite_type f :=
ring_hom.finite.finite_type hf

end finite

namespace finite_type

variables (R A)

lemma id : finite_type (alg_hom.id R A) := ring_hom.finite_type.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite_type) (hf : f.finite_type) :
  (g.comp f).finite_type :=
ring_hom.finite_type.comp hg hf

lemma comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.finite_type) (hg : surjective g) :
  (g.comp f).finite_type :=
ring_hom.finite_type.comp_surjective hf hg

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite_type :=
ring_hom.finite_type.of_surjective f hf

end finite_type

end alg_hom
