import ring_theory.ideal.basic
import category_theory.preadditive.injective
import algebra.category.Module.abelian
import algebra.module.injective

universes u v

noncomputable theory

variables (R : Type u) [ring R] (Q : Type (max u v)) [add_comm_group Q] [module R Q]

variables {R} {M N : Type (max u v)} [add_comm_group M] [add_comm_group N]
variables [module R M] [module R N] {i : M →ₗ[R] N} (hi : function.injective i) (f : M →ₗ[R] Q)
variable {Q}

theorem criterion' (h : module.injective R Q) :
  module.Baer R Q :=
λ I g, begin
  replace h := h.out,
  replace h := @h (ulift I) (ulift R) _ _ _ _,
  set f' : ulift I →ₗ[R] ulift R :=
  { to_fun := λ x, ⟨x.down.1⟩,
    map_add' := λ x y, rfl,
    map_smul' := λ x y, rfl, },
  have f'_inj : function.injective f',
  { intros a b eq1,
    change ulift.up a.down.1 = ulift.up b.down.1 at eq1,
    rw ulift.ext_iff at eq1,
    dsimp only at eq1,
    rw [ulift.ext_iff, subtype.ext_iff_val, eq1], },
  set g' : ulift I →ₗ[R] Q :=
  { to_fun := λ x, g x.down,
    map_add' := λ x y, by { change g (x.down + y.down) = _, rw [map_add] },
    map_smul' := λ x y, by { change g (x • y.down) = _, rw [map_smul, ring_hom.id_apply], } },
  replace h := h f' f'_inj g',
  rcases h with ⟨h, eq1⟩,
  set h' : R →ₗ[R] Q :=
  { to_fun := λ x, h ⟨x⟩,
    map_add' := λ x y, by { change h (⟨x⟩ + ⟨y⟩) = _, rw map_add },
    map_smul' := λ x y, by { change h (x • ⟨y⟩) = _, rw [map_smul, ring_hom.id_apply] } },
  use h',
  intros x hx,
  change h ⟨x⟩ = _,
  specialize eq1 ⟨⟨x, hx⟩⟩,
  convert eq1,
end
