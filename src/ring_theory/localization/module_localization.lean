/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.tensor_product
import ring_theory.localization.basic

/-!
# The localization of R-algebras

Let `R` be a commutative ring, `S` be a submonoid of `R`, and `M, M'` be `R`-modules.
Following `is_localization`, we define `M'` is the localization of `M` via a map `f : M →ₗ[R] M'`
(`is_module_localization S f`) if
- (`map_units`) : `x ↦ r • x` is bijective for `r : S`, `x : M'`.
- (`surj`) : Every `x : M'` can be expressed as some `f m / r` with some `m : M`, `r : S`.
- (`exists_of_eq_zero`) : If `f m = 0`, then there exists some `r : S` that annihilates `m`.

## Main declaration

- `is_module_localization`: A typeclass asserting that an `R`-linear map is a localization map.

-/
universe u

variables {R : Type*} [comm_ring R] (S : submonoid R)
variables {M M' M'' N : Type*}
variables [add_comm_group M] [add_comm_group M'] [add_comm_group M''] [add_comm_group N]
variables [module R M] [module R M'] [module R M''] [module R N]
variables (f : M →ₗ[R] M') (f' : M →ₗ[R] M'') (g : M →ₗ[R] N)

/-- The typeclass `is_module_localization (S : submonoid R) (f : M →ₗ[R] M')`
expresses that `M'` is the localization of `M` at `S`. -/
class is_module_localization : Prop :=
(map_units [] : ∀ (x : S), is_unit (algebra_map R (module.End R M') x))
(surj [] : ∀ y : M', ∃ (x : M × S), x.2 • y = f x.1)
(exists_of_eq_zero [] : ∀ {x}, f x = 0 → ∃ c : S, c • x = 0)

lemma module.End_is_unit_iff {f : module.End R M} :
  is_unit f ↔ function.bijective f :=
begin
  split,
  { rintro ⟨⟨f, g, fg : f.comp g = linear_map.id, gf : g.comp f = linear_map.id⟩, rfl⟩,
    refine equiv.bijective { inv_fun := g, left_inv := _, right_inv := _, ..f },
    { intro x, change g.comp f x = linear_map.id x, rw gf },
    { intro x, change f.comp g x = linear_map.id x, rw fg } },
  { intro H,
    let e : M ≃ₗ[R] M := { ..f, ..(equiv.of_bijective f H) },
    exact ⟨⟨_, e.symm, linear_map.ext e.right_inv, linear_map.ext e.left_inv⟩, rfl⟩ }
end

lemma smul_is_unit_inv_smul (r : R) (h : is_unit (algebra_map R (module.End R M) r)) (x : M) :
  r • (h.unit⁻¹ x) = x :=
begin
  change (algebra_map R (module.End R M) r * (h.unit⁻¹ : _)) x = x,
  rw h.mul_coe_inv, refl
end

lemma is_unit_center (R : Type*) [ring R] (x : subring.center R)  :
  is_unit x ↔ is_unit (x : R) :=
begin
  split,
  { intro h, exact (subring.center R).subtype.is_unit_map h },
  { rintro ⟨⟨x, y, xy, yx⟩, (rfl : x = _)⟩,
    refine ⟨⟨x, ⟨y, _⟩, subtype.coe_inj.mp xy, subtype.coe_inj.mp yx⟩, rfl⟩,
    intro z,
    calc z * y = (y * x) * z * y : by rw [yx, one_mul]
           ... = y * (x * z) * y : by simp_rw mul_assoc
           ... = (y * z) * (x * y) : by { rw ← x.prop, simp_rw mul_assoc }
           ... = y * z : by rw [xy, mul_one] }
end

/-- A `ring_hom` version of `linear_map.to_add_monoid_hom`.s -/
@[simps]
def module.End.to_add_monoid_End (R M : Type*) [semiring R] [add_comm_monoid M] [module R M] :
  module.End R M →+* add_monoid.End M :=
{ to_fun := linear_map.to_add_monoid_hom,
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

namespace is_unit_End

/-- An abbreviation for `f ⁻¹ x` for some `R`-automorphism `f` of an `R`-module. -/
noncomputable def mk (x : M) (f : module.End R M) (hf : is_unit f) : M :=
hf.unit.inv x

lemma apply_mk {x : M} {f : module.End R M} (hf : is_unit f) :
  f (mk x f hf) = x :=
congr_arg (λ f : module.End R M, f x) hf.mul_coe_inv

lemma mk_apply {x : M} {f : module.End R M} (hf : is_unit f) :
  mk (f x) f hf = x :=
congr_arg (λ f : module.End R M, f x) hf.coe_inv_mul

lemma eq_mk_iff_map_eq {x z : M} {f : module.End R M} (hf : is_unit f) :
  z = mk x f hf ↔ f z = x :=
by rw [← (module.End_is_unit_iff.mp hf).injective.eq_iff, apply_mk]

lemma mk_eq_iff_eq_map {x z : M} {f : module.End R M} (hf : is_unit f) :
  mk x f hf = z ↔ x = f z :=
by rw [← (module.End_is_unit_iff.mp hf).injective.eq_iff, apply_mk]

lemma mk_add_mk (x x' : M) {f f' : module.End R M} (hf : is_unit f) (hf' : is_unit f')
  (h : commute f f') :
  mk x f hf + mk x' f' hf' = mk (f' x + f x') (f * f') (hf.mul hf') :=
by rw [eq_mk_iff_map_eq, map_add, h.eq, linear_map.mul_apply, apply_mk, ← h.eq,
    linear_map.mul_apply, apply_mk]

lemma mk_smul (r : R) (x : M) {f : module.End R M} (hf : is_unit f) :
   mk (r • x) f hf = r • mk x f hf :=
linear_map.map_smul _ _ _

lemma mk_apply_of_commute {x : M} {f f' : module.End R M} {hf' : is_unit f'} (h : commute f f') :
  mk (f x) f' hf' = f (mk x f' hf') :=
by rw [mk_eq_iff_eq_map, ← linear_map.mul_apply, ← h.eq, linear_map.mul_apply, apply_mk]

lemma mk_mul {x : M} {f f' : module.End R M} (hf : is_unit f) {hf' : is_unit f'} :
  mk x (f * f') (hf.mul hf') = mk (mk x f hf) f' hf' :=
by rw [mk_eq_iff_eq_map, linear_map.mul_apply, apply_mk, apply_mk]

lemma mk_eq_mk_iff (x x' : M) {f f' : module.End R M} (hf : is_unit f) (hf' : is_unit f')
  (h : commute f f') :
  mk x f hf = mk x' f' hf' ↔ f' x = f x' :=
by { rw [mk_eq_iff_eq_map, ← mk_apply_of_commute, eq_mk_iff_map_eq], exact h }

lemma mk_add (x x' : M) {f : module.End R M} (hf : is_unit f) :
  mk (x + x') f hf = mk x f hf + mk x' f hf :=
by { rw [mk_add_mk, mk_mul, ← map_add, mk_apply], exact commute.refl _ }

lemma mk_zero {f : module.End R M} (hf : is_unit f) :
  mk 0 f hf = 0 :=
by { dsimp [is_unit_End.mk], rw [map_zero] }

variable (S)

lemma mk_one (x : M) : mk x (1 : module.End R M) is_unit_one = x :=
apply_mk is_unit_one

variables {S}


end is_unit_End

namespace is_module_localization

variables [is_module_localization S f]

include f

lemma eq_iff_exists {x₁ x₂} : f x₁ = f x₂ ↔ ∃ c : S, c • x₁ = c • x₂ :=
begin
  split,
  { intros e,
    rw [← sub_eq_zero, ← map_sub] at e,
    obtain ⟨c, e'⟩ := is_module_localization.exists_of_eq_zero S e,
    exact ⟨c, by rwa [← sub_eq_zero, ← smul_sub]⟩ },
  { rintro ⟨c, e⟩,
    apply_fun f at e,
    rw [submonoid.smul_def, submonoid.smul_def, f.map_smul, f.map_smul] at e,
    exact (module.End_is_unit_iff.mp $ is_module_localization.map_units f c).1 e },
end

variable {S}

/-- `is_localization.mk' S` is the surjection sending `(x, y) : M × S` to
`f x / s`. -/
noncomputable def mk' (x : M) (y : S) : M' :=
is_unit_End.mk (f x) (algebra_map R _ y) (map_units f y)

variables {f}

lemma eq_mk'_iff_smul_eq {x : M} {y : S} {z : M'} :
  z = mk' f x y ↔ y • z = f x :=
is_unit_End.eq_mk_iff_map_eq _

lemma mk'_eq_iff_eq_smul {x : M} {y : S} {z : M'} :
  mk' f x y = z ↔ f x = y • z :=
by rw [eq_comm, eq_mk'_iff_smul_eq, eq_comm]

lemma self_smul_mk' {x : M} {y : S} :
  y • (mk' f x y) = f x :=
is_unit_End.apply_mk (map_units f y)

lemma mk'_self_smul {x : M} {y : S} :
  mk' f (y • x) y = f x :=
by { refine eq.trans _ (is_unit_End.mk_apply (map_units f y)), delta mk', erw f.map_smul, refl }

lemma mk'_add_mk' {x x' : M} {y y' : S} :
 mk' f x y + mk' f x' y' = mk' f (y' • x + y • x') (y * y') :=
begin
  refine (is_unit_End.mk_add_mk _ _ _ _ _).trans _,
  { exact (commute.all y.1 y'.1).map _ },
  delta mk',
  rw [map_add, submonoid.smul_def, submonoid.smul_def, f.map_smul, f.map_smul],
  congr,
  exact (map_mul _ _ _).symm
end

lemma mk'_smul {r : R} {x : M} {y : S} :
   mk' f (r • x) y = r • mk' f x y :=
by { refine eq.trans _ (linear_map.map_smul _ _ _), delta mk', rw f.map_smul, refl }

lemma smul_mk'_cancel {x : M} {y y' : S} :
  y • mk' f x (y * y') = mk' f x y' :=
by rw [eq_mk'_iff_smul_eq, ← mul_smul, mul_comm, self_smul_mk']

lemma mk'_eq_mk'_iff (x x' : M) (y y' : S) :
  mk' f x y = mk' f x' y' ↔ y' • f x = y • f x' :=
is_unit_End.mk_eq_mk_iff _ _ _ _ ((commute.all y.1 y'.1).map _)

lemma mk'_eq_mk'_iff_exists {x x' : M} {y y' : S} :
  mk' f x y = mk' f x' y' ↔ ∃ c : S, c • y' • x = c • y • x' :=
begin
  refine (is_unit_End.mk_eq_mk_iff _ _ _ _ ((commute.all y.1 y'.1).map _)).trans _,
  dsimp,
  rw [← f.map_smul, ← f.map_smul, eq_iff_exists S f],
  refl
end

lemma mk_add {x x' : M} {y : S} :
  mk' f (x + x') y = mk' f x y + mk' f x' y :=
by { delta mk', rw map_add, exact is_unit_End.mk_add (f x) (f x') (map_units f y) }

lemma mk'_zero (y : S) :
  mk' f 0 y = 0 :=
by { dsimp [mk', is_unit_End.mk], rw [map_zero, map_zero] }

variable (S)

lemma mk'_one (x : M) : mk' f x (1 : S) = f x :=
by rw [← one_smul S (mk' f x (1 : S)), self_smul_mk']

variables {S}

variables (S f)

lemma mk'_surj (x : M') : ∃ (y : M) (s : S), mk' f y s = x :=
⟨_, _, mk'_eq_iff_eq_smul.mpr (surj S f x).some_spec.symm⟩

/-- Given a localization map `f : M →ₗ[R] N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x / y = z`. -/
noncomputable def sec (x : M') : M × S :=
classical.some (surj S f x)

lemma sec_spec (x : M') : (sec S f x).2 • x = f (sec S f x).1 :=
classical.some_spec (surj S f x)

lemma mk'_sec (x : M') : mk' f (sec S f x).1 (sec S f x).2 = x :=
by rw [mk'_eq_iff_eq_smul, sec_spec]

omit f

/-- The associated `R`-module structure on `M` given a map `R →+* add_monoid.End M`. -/
@[simps]
def ring_hom.module_of_to_End {R M : Type*} [semiring R] [add_comm_monoid M]
  (f : R →+* add_monoid.End M) : module R M :=
{ smul := λ r m, f r m,
  one_smul := λ m, by { change f 1 m = m, rw map_one, refl },
  mul_smul := λ x y m, by { change f (x * y) m = f x (f y m), rw map_mul, refl },
  smul_add := λ r, (f r).map_add,
  smul_zero := λ r, (f r).map_zero,
  add_smul := λ r s m, by { change f (r + s) m = f r m + f s m, rw map_add, refl },
  zero_smul := λ m, by { change f 0 m = 0, rw map_zero, refl } }

/-- The associated `R`-module structure on `M` given a map `R →+* add_monoid.End M`. -/
@[simps]
def module.to_add_monoid_End (R M : Type*) [semiring R] [add_comm_monoid M] [module R M] :
  R →+* add_monoid.End M :=
{ to_fun := λ r, ⟨has_scalar.smul r, smul_zero r, smul_add r⟩,
  map_one' := add_monoid_hom.ext (one_smul R),
  map_mul' := λ r s, add_monoid_hom.ext (mul_smul r s),
  map_zero' := add_monoid_hom.ext (zero_smul R),
  map_add' := λ r s, add_monoid_hom.ext (add_smul r s) }

/-- Giving a `R`-module structure on a `add_comm_monoid` is equivalent to giving a
`R →+* add_monoid.End M`. -/
def module_equiv_to_End {R M : Type*} [semiring R] [add_comm_monoid M] :
  (R →+* add_monoid.End M) ≃ module R M :=
{ to_fun := ring_hom.module_of_to_End,
  inv_fun := λ _, by exactI module.to_add_monoid_End R M,
  left_inv := λ f, ring_hom.ext $ λ r, add_monoid_hom.ext $ λ m, rfl,
  right_inv := λ _, by { ext, refl } }

/-- Let `M` be an `R`-module, `S` be a submonoid of `R`, and `R'` be a localization of `R` wrt `S`.
Suppose each `s : S` acts invertibly on `M`. Then we may induce an action of `R'` on `M`. -/
noncomputable
def module_of_is_localization (R' : Type*) [comm_ring R'] [algebra R R'] [is_localization S R']
  (h : ∀ (x : S), is_unit (algebra_map R (module.End R M) x)) :
  module R' M :=
begin
  apply ring_hom.module_of_to_End,
  let : R →+* subring.center (module.End R M) := (algebra_map R (module.End R M)).cod_restrict' _
    (by { intros x y, ext z, exact y.map_smul _ _ }),
  let := @is_localization.lift R _ S R' _ _ _ _ _ this (λ x, (is_unit_center _ _).mpr (h x)),
  exact ((module.End.to_add_monoid_End R M).comp (subring.subtype _)).comp this,
end

lemma module_is_scalar_tower_of_is_localization (R' : Type*) [comm_ring R'] [algebra R R']
  [is_localization S R'] (h : ∀ (x : S), is_unit (algebra_map R (module.End R M) x)) :
  @@is_scalar_tower R R' M _
    (module_of_is_localization S R' h).to_distrib_mul_action.to_has_scalar _ :=
begin
  constructor,
  intros x y z,
  delta module_of_is_localization ring_hom.module_of_to_End,
  dsimp,
  rw [algebra.smul_def, map_mul, is_localization.lift_eq],
  refl
end

lemma exists_localization_smul_of_is_localization (R' : Type*) [comm_ring R'] [algebra R R']
  [is_localization S R'] (x : M') : ∃ (r : S) (m : M), x = @@has_scalar.smul
    (module_of_is_localization S R' (map_units f)).to_distrib_mul_action.to_has_scalar
    (is_localization.mk' R' (1 : R) r) (f m) :=
begin
  letI := module_is_scalar_tower_of_is_localization S R' (map_units f),
  obtain ⟨y, s, rfl⟩ := mk'_surj S f x,
  refine ⟨s, y, _⟩,
  rw [mk'_eq_iff_eq_smul, ← smul_assoc, submonoid.smul_def, algebra.smul_def,
    is_localization.mk'_spec', map_one, one_smul],
end

include S f

lemma linear_map_ext (h : ∀ (x : S), is_unit (algebra_map R (module.End R N) x))
  (g g' : M' →ₗ[R] N) : g.comp f = g'.comp f ↔ g = g' :=
begin
  split,
  { intro e, ext x,
    obtain ⟨y, s, rfl⟩ := mk'_surj S f x,
    transitivity is_unit_End.mk (g.comp f y) _ (h s),
    { rw is_unit_End.eq_mk_iff_map_eq,
      dsimp,
      rw [← g.map_smul, ← submonoid.smul_def, self_smul_mk'] },
    { rw [e, is_unit_End.mk_eq_iff_eq_map],
      dsimp,
      rw [← g'.map_smul, ← submonoid.smul_def, self_smul_mk'] } },
  { rintro rfl, exact rfl }
end

lemma mk_map_eq (h : ∀ (x : S), is_unit (algebra_map R (module.End R N) x)) (x x' : M) (y y' : S)
  (h' : mk' f x y = mk' f x' y') : is_unit_End.mk (g x) _ (h y) = is_unit_End.mk (g x') _ (h y') :=
begin
  obtain ⟨c, e⟩ := mk'_eq_mk'_iff_exists.mp h',
  rw [is_unit_End.mk_eq_mk_iff, ← (module.End_is_unit_iff.mp (h c)).injective.eq_iff],
  dsimp,
  simp_rw ← g.map_smul,
  exacts [congr_arg g e, (commute.all _ _).map _],
end

include g

/-- The lift of a linear map `M →ₗ[R] N` along a localization map `M →ₗ[R] M'` provided that
`S` acts invertibly on `N`. -/
noncomputable
def lift (h : ∀ (x : S), is_unit (algebra_map R (module.End R N) x)) :
  M' →ₗ[R] N :=
{ to_fun := λ x, is_unit_End.mk (g (sec S f x).1) _ (h (sec S f x).2),
  map_add' := λ x y, by begin
    rw is_unit_End.mk_add_mk _ _ _ _ ((commute.all _ _).map _),
    dsimp,
    simp_rw [← linear_map.map_smul, ← map_add, ← map_mul,
      ← submonoid.coe_mul, ← submonoid.smul_def],
    apply mk_map_eq S f g h,
    rw [← mk'_add_mk', mk'_sec, mk'_sec, mk'_sec],
  end,
  map_smul' := λ r x, begin
    rw [← is_unit_End.mk_smul, ← g.map_smul],
    apply mk_map_eq S f g h,
    rw [mk'_smul, mk'_sec, mk'_sec],
    refl
  end }

lemma lift_mk' (h : ∀ (x : S), is_unit (algebra_map R (module.End R N) x)) (x : M) (s : S) :
  lift S f g h (mk' f x s) = is_unit_End.mk (g x) _ (h s) :=
begin
  convert mk_map_eq S f g h _ x _ s _,
  rw [mk'_sec],
end

lemma lift_eq (h : ∀ (x : S), is_unit (algebra_map R (module.End R N) x)) (x : M) :
  lift S f g h (f x) = g x :=
begin
  rw [← mk'_one S x, lift_mk'],
  convert is_unit_End.mk_one (g x),
  rw [submonoid.coe_one, map_one]
end

lemma lift_comp (h : ∀ (x : S), is_unit (algebra_map R (module.End R N) x)) :
  (lift S f g h).comp f = g :=
begin
  ext, exact (lift_eq S f g h x : _),
end

/-- The linear eqivalence between two localizations of `M` wrt `S`. -/
noncomputable
def linear_equiv [is_module_localization S g] : M' ≃ₗ[R] N :=
{ inv_fun := lift S g f (map_units f),
  left_inv := λ x, congr_arg (λ f : module.End R M', f x) ((linear_map_ext S f (map_units f)
    ((lift S g f (map_units f)).comp $ lift S f g (map_units g)) linear_map.id).mp
    (by { rw [linear_map.comp_assoc, lift_comp, lift_comp], ext, refl })),
  right_inv := λ x, congr_arg (λ f : module.End R N, f x) ((linear_map_ext S g (map_units g)
    ((lift S f g (map_units g)).comp $ lift S g f (map_units f)) linear_map.id).mp
    (by { rw [linear_map.comp_assoc, lift_comp, lift_comp], ext, refl })),
  ..(lift S f g (map_units g)) }

omit f g

variables (R M)

/-- `linear_map.restrict_scalars_map` as a `ring_hom`. --/
@[simps]
def _root_.module.End.restrict_scalars (S : Type*) [comm_ring S] [algebra R S] [module S M]
  [is_scalar_tower R S M] :
  module.End S M →+* module.End R M :=
{ map_one' := rfl,
  map_mul' := λ f g, rfl,
  map_zero' := rfl,
  ..(linear_map.restrict_scalars_map R S M) }

variables {R M}

open_locale tensor_product

lemma module.End.algebra_map_factors (R S M : Type*) [comm_ring R] [comm_ring S] [add_comm_group M]
  [algebra R S] [module R M] [module S M] [is_scalar_tower R S M] :
  algebra_map R (module.End R M) = (module.End.restrict_scalars R M S).comp
    ((algebra_map S (module.End S M)).comp $ algebra_map R S) :=
by { ext r x, exact (algebra_map_smul S r x).symm }

include f

/-- The canonical equivalence `S⁻¹M ≃ₗ[R] S⁻¹R ⊗[R] M`. -/
noncomputable
def equiv_tensor_product (R' : Type*) [comm_ring R'] [algebra R R'] [is_localization S R']
  [module R' M'] [is_scalar_tower R R' M'] : M' ≃ₗ[R] R' ⊗[R] M :=
{ inv_fun := tensor_product.lift
    (((algebra_alg_hom R' $ module.End R' (M →ₗ[R] M')).to_linear_map.flip f).restrict_scalars R),
  left_inv := λ x, by begin
    obtain ⟨y, s, rfl⟩ := mk'_surj S f x,
    rw [linear_map.to_fun_eq_coe, lift_mk', eq_mk'_iff_smul_eq, submonoid.smul_def,
      ← linear_map.map_smul],
    convert tensor_product.lift.tmul (1 : R') y using 1,
    { congr' 1,
      generalize_proofs _ h,
      exact is_unit_End.apply_mk h },
    { exact (one_smul _ _).symm }
  end,
  right_inv := λ x, begin
    rw [linear_map.to_fun_eq_coe],
    refine (linear_map.comp_apply _ _ _).symm.trans (eq.trans _ (linear_map.id_apply _)),
    swap 4,
    congr' 2,
    apply tensor_product.ext',
    intros r m,
    rw [linear_map.comp_apply, linear_map.id_apply, tensor_product.lift.tmul],
    change lift S f (tensor_product.mk R R' M 1) _ (r • f m) = _,
    obtain ⟨y, s, rfl⟩ := is_localization.mk'_surjective S r,
    convert lift_mk' S f (tensor_product.mk R R' M 1) _ (y • m) s,
    { rw [eq_mk'_iff_smul_eq, submonoid.smul_def, ← smul_assoc, algebra.smul_def,
        is_localization.mk'_spec', algebra_map_smul, f.map_smul] },
    { rw [is_unit_End.eq_mk_iff_map_eq],
      change ((s : R) • is_localization.mk' R' y s) ⊗ₜ[R] m = 1 ⊗ₜ (y • m),
      rw [algebra.smul_def, is_localization.mk'_spec', ← tensor_product.smul_tmul,
        algebra.smul_def, mul_one] }
  end,
  ..(lift S f (tensor_product.mk R R' M 1) (λ x, begin
    rw [module.End.algebra_map_factors R R', ← ring_hom.comp_assoc, ring_hom.comp_apply],
    exact ring_hom.is_unit_map _ (is_localization.map_units R' x)
  end)) }
.
/-- Localization of a module is the base change along the localization ring map. -/
protected
lemma is_base_change (R' : Type*) [comm_ring R'] [algebra R R']
  [is_localization S R'] [module R' M'] [is_scalar_tower R R' M'] : is_base_change R' f :=
(equiv_tensor_product S f R').symm.bijective

lemma linear_equiv_comp (e : M' ≃ₗ[R] M'') [is_module_localization S f] :
  is_module_localization S (e.to_linear_map.comp f) :=
begin
  constructor,
  { intro r,
    have := is_module_localization.map_units f r,
    rw module.End_is_unit_iff at this ⊢,
    convert (e.bijective.comp this).comp e.symm.bijective,
    ext, dsimp, rw [e.map_smul, e.apply_symm_apply] },
  { intro x,
    obtain ⟨⟨y, s⟩, e'⟩ := is_module_localization.surj S f (e.symm x),
    rw [submonoid.smul_def, ← e.symm.map_smul, e.symm_apply_eq] at e',
    exact ⟨⟨y, s⟩, e'⟩ },
  { rintro x hx,
    exact is_module_localization.exists_of_eq_zero S (e.injective (hx.trans e.map_zero.symm)) }
end

end is_module_localization

variable (M)

/-- The set of fractions of the form `m / s`, on which we will take quotient and construct the
localization. -/
def module_localization.set := M × S

instance : add_comm_monoid (module_localization.set S M) :=
{ add := λ x₁ x₂, ⟨x₂.2 • x₁.1 + x₁.2 • x₂.1, x₁.2 * x₂.2⟩,
  add_assoc := λ x₁ x₂ x₃, begin
    dsimp,
    simp_rw [smul_add, add_assoc, mul_assoc, smul_smul],
    congr' 3; rw mul_comm
  end,
  zero := (0, 1),
  zero_add := λ a, by { dsimp, simp },
  add_zero := λ a, by { dsimp, simp },
  add_comm := λ x₁ x₂, begin
    change (⟨_, _⟩ : M × S) = ⟨_, _⟩,
    rw [add_comm, mul_comm]
  end }

instance : distrib_mul_action R (module_localization.set S M) :=
{ smul := λ r x, ⟨r • x.1, x.2⟩,
  one_smul := λ ⟨_, _⟩, by { dsimp, rw one_smul, },
  mul_smul := λ _ _ ⟨_, _⟩, by { dsimp, rw mul_smul },
  smul_add := λ _ ⟨_, _⟩ ⟨_, _⟩, by { ext, refine (smul_add _ _ _).trans _,
    congr' 1; rw [smul_comm], refl },
  smul_zero := λ _, by { dsimp, erw smul_zero, refl } }

/-- The relation on `module_localization.set` whose quotient is the localization. -/
def module_localization.r : add_con (module_localization.set S M) :=
{ r := λ x y, ∃ c : S, c • y.2 • x.1 = c • x.2 • y.1,
  iseqv := begin
    refine ⟨_, _, _⟩,
    { rintro ⟨m, s⟩, use 1 },
    { rintros ⟨m₁, s₁⟩ ⟨m₂, s₂⟩ ⟨c, e⟩, exact ⟨c, e.symm⟩ },
    { rintros ⟨m₁, s₁⟩ ⟨m₂, s₂⟩ ⟨m₃, s₃⟩ ⟨c₁, e₁⟩ ⟨c₂, e₂⟩,
      use c₁ * c₂ * s₂,
      apply_fun (λ m : M, (c₂ * s₃) • m) at e₁,
      apply_fun (λ m : M, (c₁ * s₁) • m) at e₂,
      simp only [smul_smul, ← mul_assoc] at ⊢ e₁ e₂,
      convert e₁.trans ((congr_arg (λ s : S, s • m₂) _).trans e₂) using 2,
      all_goals { ext1, simp only [submonoid.coe_mul], ring } }
  end,
  add' := begin
    rintros ⟨m₁, s₁⟩ ⟨m₂, s₂⟩ ⟨m₃, s₃⟩ ⟨m₄, s₄⟩ ⟨c₁, e₁⟩ ⟨c₂, e₂⟩,
    use c₁ * c₂,
    change (c₁ * c₂) • (s₂ * s₄) • (s₃ • m₁ + s₁ • m₃) = (c₁ * c₂) • (s₁ * s₃) • (_ + _),
    dsimp at e₁ e₂,
    apply_fun (λ m : M, (c₂ * s₃ * s₄) • m) at e₁,
    apply_fun (λ m : M, (c₁ * s₁ * s₂) • m) at e₂,
    simp only [smul_smul, ← mul_assoc, smul_add] at ⊢ e₁ e₂,
    have : (c₂ * s₃ * s₄ * c₁ * s₂) • m₁ + (c₁ * s₁ * s₂ * c₂ * s₄) • m₃ =
      (c₂ * s₃ * s₄ * c₁ * s₁) • m₂ + (c₁ * s₁ * s₂ * c₂ * s₃) • m₄ := by rw [e₁, e₂],
    convert this using 3,
    all_goals { ext1, simp only [submonoid.coe_mul], ring }
  end }
.
/-- A construction of the localization of a module. -/
def module_localization : Type* := (module_localization.r S M).quotient

instance : add_comm_monoid (module_localization S M) :=
by { delta module_localization, apply_instance }

instance : add_comm_group (module_localization S M) :=
{ neg := begin
    fapply quotient.lift,
    exact λ x, (module_localization.r S M).mk' (-x.1, x.2),
    rintros ⟨x₁, s₁⟩ ⟨x₂, s₂⟩ ⟨c, e⟩,
    dsimp,
    rw add_con.eq,
    use c,
    simp only [smul_neg, e],
  end,
  add_left_neg := begin
    intro b,
    change quotient.lift _ _ _ + b = 0,
    induction b using add_con.induction_on,
    erw quotient.lift_mk,
    change ↑(_ + b) = ↑(0 : module_localization.set S M),
    rw add_con.eq,
    use 1,
    change (1 : S) • (1 : S) • (_ + _) = (1 : S) • _ • (0 : M),
    simp,
  end,
  ..(show add_comm_monoid (module_localization S M), by apply_instance) }

instance : module R (module_localization S M) :=
{ smul := λ r, (module_localization.r S M).lift ((module_localization.r S M).mk'.comp
    (distrib_mul_action.to_add_monoid_hom (module_localization.set S M) r)) (begin
      rintro ⟨x₁, s₁⟩ ⟨x₂, s₂⟩ ⟨c, e⟩,
      rw [add_con.ker_rel, add_monoid_hom.comp_apply, add_monoid_hom.comp_apply, ← add_con.ker_rel,
        add_con.mk'_ker],
      use c,
      show c • s₂ • r • x₁ = c • s₁ • r • x₂, by simp only [e, smul_comm _ r]
    end),
  one_smul := λ b, by { induction b using add_con.induction_on,
    change ↑((1 : R) • b) = ↑b, rw one_smul },
  mul_smul := λ x y b, by { induction b using add_con.induction_on,
    change ↑((x * y) • b) = ↑(x • y • b), rw mul_smul },
  smul_add := λ x a b, by { induction a using add_con.induction_on,
    induction b using add_con.induction_on, change ↑(x • (a + b)) = ↑(x • a + x • b), rw smul_add },
  smul_zero := λ r, by { change ↑(r • 0 : module_localization.set S M) = _, rw smul_zero, refl },
  add_smul := λ r s b, begin
    induction b using add_con.induction_on,
    change ↑((r + s) • b) = ↑(r • b + s • b),
    rw add_con.eq,
    use 1,
    cases b with x y,
    rw [one_smul, one_smul],
    change (y * y) • (r + s) • x = y • (y • r • x + y • s • x),
    rw [mul_smul, add_smul, smul_add],
  end,
  zero_smul := λ b, begin
    induction b using add_con.induction_on,
    change ↑((0 : R) • b) = ↑(0 : module_localization.set S M),
    rw add_con.eq,
    use 1,
    cases b with x y,
    change (1 : S) • (1 : S) • (0 : R) • x = (1 : S) • y • (0 : M),
    simp only [zero_smul, smul_zero]
  end }

/-- A construction of the localization map of a module. -/
def module_localization_map : M →ₗ[R] module_localization S M :=
{ to_fun := λ m, (module_localization.r S M).mk' (m, 1),
  map_add' := λ x y, by { rw ← (module_localization.r S M).mk'.map_add, congr' 2; dsimp; simp },
  map_smul' := λ r x, by refl }

instance module_localization.is_module_localization :
  is_module_localization S (module_localization_map S M) :=
begin
  constructor,
  { intro r,
    rw module.End_is_unit_iff,
    split,
    { intros x y e,
      induction x using add_con.induction_on,
      induction y using add_con.induction_on,
      obtain ⟨c, e' : c • y.2 • r • x.1 = c • x.2 • r • y.1⟩ := (add_con.eq _).mp e,
      rw add_con.eq,
      use r * c,
      simpa only [mul_smul, smul_comm _ r] using e' },
    { intros x,
      induction x using add_con.induction_on,
      use (module_localization.r S M).mk' ⟨x.1, x.2 * r⟩,
      refine (add_con.eq _).mpr _,
      use 1,
      rw [one_smul, one_smul],
      exact smul_smul _ _ _ } },
  { intro y,
    induction y using add_con.induction_on,
    use y,
    refine (add_con.eq _).mpr _,
    exact ⟨1, by simpa⟩ },
  { intros x e,
    obtain ⟨c, e' : c • (1 : S) • x = c • (1 : S) • (0 : M)⟩ := (add_con.eq _).mp e,
    use c,
    simpa using e' }
end

noncomputable
instance module_localization.localization_module (R' : Type*) [comm_ring R'] [algebra R R']
  [is_localization S R'] : module R' (module_localization S M) :=
is_module_localization.module_of_is_localization S R'
  (is_module_localization.map_units (module_localization_map S M))

instance (R' : Type*) [comm_ring R'] [algebra R R']
  [is_localization S R'] : is_scalar_tower R R' (module_localization S M) :=
is_module_localization.module_is_scalar_tower_of_is_localization S R'
  (is_module_localization.map_units (module_localization_map S M))

lemma module_localization.is_base_change (R' : Type*) [comm_ring R'] [algebra R R']
  [is_localization S R'] : is_base_change R' (module_localization_map S M) :=
is_module_localization.is_base_change S _ R'

lemma is_module_localization.of_is_base_change {R' M' : Type*} [add_comm_group M']
  [comm_ring R'] [algebra R R']
  [is_localization S R'] [module R M'] [module R' M'] [is_scalar_tower R R' M']
  {f : M →ₗ[R] M'} (h : is_base_change R' f) : is_module_localization S f :=
begin
  convert is_module_localization.linear_equiv_comp S (module_localization_map S M)
    ((is_module_localization.equiv_tensor_product S
      (module_localization_map S M) R').trans h.equiv),
  ext x,
  dsimp [is_module_localization.equiv_tensor_product],
  rw is_module_localization.lift_eq,
  erw is_base_change.equiv_tmul,
  rw one_smul
end

lemma is_module_localization.iff_is_base_change {M' : Type*} [add_comm_group M'] [module R M']
  (f : M →ₗ[R] M') (R' : Type*) [comm_ring R'] [algebra R R']
  [is_localization S R'] [module R' M'] [is_scalar_tower R R' M'] :
    is_module_localization S f ↔ is_base_change R' f :=
⟨λ x, by exactI is_module_localization.is_base_change S f R',
  is_module_localization.of_is_base_change S M⟩
