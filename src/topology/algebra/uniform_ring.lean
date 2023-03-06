/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import algebra.algebra.basic
import topology.algebra.group_completion
import topology.algebra.ring.ideal

/-!
# Completion of topological rings:

This files endows the completion of a topological ring with a ring structure.
More precisely the instance `uniform_space.completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`uniform_add_group`. There is also a commutative version when the original ring is commutative.
Moreover, if a topological ring is an algebra over a commutative semiring, then so is its
`uniform_space.completion`.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `uniform_space.completion.extension_hom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `completion R`.
* `uniform_space.completion.map_ring_hom` : promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `completion R` to `completion S`.

TODO: Generalise the results here from the concrete `completion` to any `abstract_completion`.
-/
open classical set filter topological_space add_comm_group
open_locale classical
noncomputable theory
universes u

namespace uniform_space.completion
open dense_inducing uniform_space function
variables (α : Type*) [ring α] [uniform_space α]

instance : has_one (completion α) := ⟨(1:α)⟩

instance : has_mul (completion α) :=
⟨curry $ (dense_inducing_coe.prod dense_inducing_coe).extend (coe ∘ uncurry (*))⟩

@[norm_cast] lemma coe_one : ((1 : α) : completion α) = 1 := rfl

variables {α} [topological_ring α]

@[norm_cast]
lemma coe_mul (a b : α) : ((a * b : α) : completion α) = a * b :=
((dense_inducing_coe.prod dense_inducing_coe).extend_eq
  ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm

variables [uniform_add_group α]

lemma continuous_mul : continuous (λ p : completion α × completion α, p.1 * p.2) :=
begin
  let m := (add_monoid_hom.mul : α →+ α →+ α).compr₂ to_compl,
  have : continuous (λ p : α × α, m p.1 p.2),
  from (continuous_coe α).comp continuous_mul,
  have di : dense_inducing (to_compl : α → completion α),
  from dense_inducing_coe,
  convert di.extend_Z_bilin di this,
  ext ⟨x, y⟩,
  refl
end

lemma continuous.mul {β : Type*} [topological_space β] {f g : β → completion α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, f b * g b) :=
continuous_mul.comp (hf.prod_mk hg : _)

instance : ring (completion α) :=
{ one_mul       := assume a, completion.induction_on a
    (is_closed_eq (continuous.mul continuous_const continuous_id) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, one_mul]),
  mul_one       := assume a, completion.induction_on a
    (is_closed_eq (continuous.mul continuous_id continuous_const) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, mul_one]),
  mul_assoc     := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous.mul (continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd))
      (continuous.mul continuous_fst
        (continuous.mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]),
  left_distrib  := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous.mul continuous_fst (continuous.add
        (continuous_fst.comp continuous_snd)
        (continuous_snd.comp continuous_snd)))
      (continuous.add
        (continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
        (continuous.mul continuous_fst (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, mul_add]),
  right_distrib := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous.mul (continuous.add continuous_fst
        (continuous_fst.comp continuous_snd)) (continuous_snd.comp continuous_snd))
      (continuous.add
        (continuous.mul continuous_fst (continuous_snd.comp continuous_snd))
        (continuous.mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, add_mul]),
  .. add_monoid_with_one.unary,
  ..completion.add_comm_group, ..completion.has_mul α, ..completion.has_one α }

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
def coe_ring_hom : α →+* completion α :=
⟨coe, coe_one α, assume a b, coe_mul a b, coe_zero, assume a b, coe_add a b⟩

lemma continuous_coe_ring_hom : continuous (coe_ring_hom : α → completion α) :=
continuous_coe α

variables {β : Type u} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β]
          (f : α →+* β) (hf : continuous f)

/-- The completion extension as a ring morphism. -/
def extension_hom [complete_space β] [separated_space β] :
  completion α →+* β :=
have hf' : continuous (f : α →+ β), from hf, -- helping the elaborator
have hf : uniform_continuous f, from uniform_continuous_add_monoid_hom_of_continuous hf',
{ to_fun := completion.extension f,
  map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero],
  map_add' := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      (continuous_extension.comp continuous_add)
      ((continuous_extension.comp continuous_fst).add
                      (continuous_extension.comp continuous_snd)))
    (assume a b,
      by rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf,
             f.map_add]),
  map_one' := by rw [← coe_one, extension_coe hf, f.map_one],
  map_mul' := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      (continuous_extension.comp continuous_mul)
      ((continuous_extension.comp continuous_fst).mul (continuous_extension.comp continuous_snd)))
    (assume a b,
      by rw [← coe_mul, extension_coe hf, extension_coe hf, extension_coe hf, f.map_mul]) }

instance top_ring_compl : topological_ring (completion α) :=
{ continuous_add := continuous_add,
  continuous_mul := continuous_mul }

/-- The completion map as a ring morphism. -/
def map_ring_hom (hf : continuous f) : completion α →+* completion β :=
extension_hom (coe_ring_hom.comp f) (continuous_coe_ring_hom.comp  hf)

section algebra
variables (A : Type*) [ring A] [uniform_space A] [uniform_add_group A] [topological_ring A]
  (R : Type*) [comm_semiring R] [algebra R A] [has_uniform_continuous_const_smul R A]

@[simp] lemma map_smul_eq_mul_coe (r : R) :
  completion.map ((•) r) = (*) (algebra_map R A r : completion A) :=
begin
  ext x,
  refine completion.induction_on x _ (λ a, _),
  { exact is_closed_eq (completion.continuous_map) (continuous_mul_left _) },
  { rw [map_coe (uniform_continuous_const_smul r) a, algebra.smul_def, coe_mul] },
end

instance : algebra R (completion A) :=
{ commutes' := λ r x, completion.induction_on x
    (is_closed_eq (continuous_mul_left _) (continuous_mul_right _)) $ λ a,
      by simpa only [coe_mul] using congr_arg (coe : A → completion A) (algebra.commutes r a),
  smul_def' := λ r x, congr_fun (map_smul_eq_mul_coe A R r) x,
  ..((uniform_space.completion.coe_ring_hom : A →+* completion A).comp (algebra_map R A)) }

lemma algebra_map_def (r : R) :
  algebra_map R (completion A) r = (algebra_map R A r : completion A) :=
rfl

end algebra

section comm_ring
variables (R : Type*) [comm_ring R] [uniform_space R] [uniform_add_group R] [topological_ring R]

instance : comm_ring (completion R) :=
{ mul_comm := assume a b, completion.induction_on₂ a b
      (is_closed_eq (continuous_fst.mul continuous_snd)
                    (continuous_snd.mul continuous_fst))
      (assume a b, by rw [← coe_mul, ← coe_mul, mul_comm]),
 ..completion.ring }

 /-- A shortcut instance for the common case -/
instance algebra' : algebra R (completion R) :=
by apply_instance

end comm_ring

end uniform_space.completion

namespace uniform_space
variables {α : Type*}
lemma ring_sep_rel (α) [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  separation_setoid α = submodule.quotient_rel (ideal.closure ⊥) :=
setoid.ext $ λ x y, (add_group_separation_rel x y).trans $
  iff.trans (by refl) (submodule.quotient_rel_r_def _).symm

lemma ring_sep_quot
  (α : Type u) [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  quotient (separation_setoid α) = (α ⧸ (⊥ : ideal α).closure) :=
by rw [@ring_sep_rel α r]; refl

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sep_quot_equiv_ring_quot (α)
  [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  quotient (separation_setoid α) ≃ (α ⧸ (⊥ : ideal α).closure) :=
quotient.congr_right $ λ x y, (add_group_separation_rel x y).trans $
  iff.trans (by refl) (submodule.quotient_rel_r_def _).symm

/- TODO: use a form of transport a.k.a. lift definition a.k.a. transfer -/
instance comm_ring [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  comm_ring (quotient (separation_setoid α)) :=
by rw ring_sep_quot α; apply_instance

instance topological_ring
  [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  topological_ring (quotient (separation_setoid α)) :=
begin
  convert topological_ring_quotient (⊥ : ideal α).closure; try {apply ring_sep_rel},
  simp [uniform_space.comm_ring]
end

end uniform_space

section uniform_extension

variables {α : Type*} [uniform_space α] [semiring α]
variables {β : Type*} [uniform_space β] [semiring β] [topological_semiring β]
variables {γ : Type*} [uniform_space γ] [semiring γ] [topological_semiring γ]
variables [t2_space γ] [complete_space γ]

/-- The dense inducing extension as a ring homomorphism. -/
noncomputable def dense_inducing.extend_ring_hom {i : α →+* β} {f : α →+* γ}
  (ue : uniform_inducing i) (dr : dense_range i) (hf : uniform_continuous f):
  β →+* γ :=
  { to_fun := (ue.dense_inducing dr).extend f,
    map_one' := by { convert dense_inducing.extend_eq (ue.dense_inducing dr) hf.continuous 1,
      exacts [i.map_one.symm, f.map_one.symm], },
    map_zero' := by { convert dense_inducing.extend_eq (ue.dense_inducing dr) hf.continuous 0,
      exacts [i.map_zero.symm, f.map_zero.symm], },
    map_add' :=
    begin
      have h := (uniform_continuous_uniformly_extend ue dr hf).continuous,
      refine λ x y, dense_range.induction_on₂ dr _ (λ a b, _) x y,
      { exact is_closed_eq (continuous.comp h continuous_add)
        ((h.comp continuous_fst).add (h.comp continuous_snd)), },
      { simp_rw [← i.map_add, dense_inducing.extend_eq (ue.dense_inducing dr) hf.continuous _,
          ← f.map_add], },
    end,
    map_mul' :=
    begin
      have h := (uniform_continuous_uniformly_extend ue dr hf).continuous,
      refine λ x y, dense_range.induction_on₂ dr _ (λ a b, _) x y,
      { exact is_closed_eq (continuous.comp h continuous_mul)
        ((h.comp continuous_fst).mul (h.comp continuous_snd)), },
      { simp_rw [← i.map_mul, dense_inducing.extend_eq (ue.dense_inducing dr) hf.continuous _,
          ← f.map_mul], },
    end, }

end uniform_extension
