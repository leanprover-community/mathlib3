/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import algebra.group.hom_instances
import topology.uniform_space.completion
import topology.algebra.uniform_group

/-!
# Completion of topological groups:

This files endows the completion of a uniform group with a group structure.  More precisely the
instance `uniform_space.completion.group` builds a group structure on the completion of a group
endowed with a compatible uniform structure.  Then the instance
`uniform_space.completion.uniform_group` proves this group structure is compatible with the
completed uniform structure. The compatibility condition is `uniform_group`.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked), the main
constructions deal with continuous group morphisms.

* `monoid_hom.extension`: extends a continuous group morphism from `G`
  to a complete separated group `H` to `completion G`.
* `monoid_hom.completion`: promotes a continuous group morphism
  from `G` to `H` into a continuous group morphism
  from `completion G` to `completion H`.
-/

noncomputable theory

universes u v

section group
open uniform_space Cauchy filter set
variables {G : Type u} [uniform_space G]

@[to_additive] instance [has_one G] : has_one (completion G) := ⟨(1 : G)⟩
@[to_additive] instance [has_inv G] : has_inv (completion G) := ⟨completion.map (λ a, a⁻¹)⟩
@[to_additive] instance [has_mul G] : has_mul (completion G) := ⟨completion.map₂ (*)⟩
@[to_additive] instance [has_div G] : has_div (completion G) := ⟨completion.map₂ (/)⟩

@[norm_cast, to_additive]
lemma uniform_space.completion.coe_one [has_one G] : ((1 : G) : completion G) = 1 := rfl

end group

namespace uniform_space
namespace completion

variables {G : Type*} [uniform_space G] [group G] [uniform_group G]

@[norm_cast, to_additive]
lemma coe_inv (a : G) : ((a⁻¹ : G) : completion G) = a⁻¹ :=
(map_coe uniform_continuous_inv a).symm

@[norm_cast, to_additive]
lemma coe_div (a b : G) : ((a / b : G) : completion G) = a / b :=
(map₂_coe_coe a b has_div.div uniform_continuous_div).symm

@[norm_cast, to_additive]
lemma coe_mul (a b : G) : ((a * b : G) : completion G) = a * b :=
(map₂_coe_coe a b (*) uniform_continuous_mul).symm

@[to_additive] instance : monoid (completion G) :=
{ one_mul := λ a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_const continuous_id) continuous_id)
    (λ a, by rw [← coe_one, ← coe_mul, one_mul]),
  mul_one := λ a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_id continuous_const) continuous_id)
    (λ a, by rw [← coe_one, ← coe_mul, mul_one]),
  mul_assoc := λ a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_map₂ (continuous_map₂ continuous_fst continuous_snd.fst) continuous_snd.snd)
      (continuous_map₂ continuous_fst (continuous_map₂ continuous_snd.fst continuous_snd.snd)))
    (λ a b c, by simp only [← coe_mul, mul_assoc]),
  .. completion.has_one, .. completion.has_mul }

@[to_additive] instance : div_inv_monoid (completion G) :=
{ div_eq_mul_inv := λ a b, completion.induction_on₂ a b
    (is_closed_eq (continuous_map₂ continuous_fst continuous_snd)
      (continuous_map₂ continuous_fst (completion.continuous_map.comp continuous_snd)))
   (λ a b, by exact_mod_cast congr_arg coe (div_eq_mul_inv a b)),
  .. completion.monoid, .. completion.has_inv, .. completion.has_div }

@[to_additive] instance : group (completion G) :=
{ mul_left_inv := λ a, completion.induction_on a
    (is_closed_eq (continuous_map₂ completion.continuous_map continuous_id) continuous_const)
    (λ a, by rw [← coe_inv, ← coe_mul, mul_left_inv, coe_one]),
  .. completion.div_inv_monoid }

@[to_additive] instance : uniform_group (completion G) :=
⟨uniform_continuous_map₂ has_div.div⟩

/-- The map from a group to its completion as a group homomorphism. -/
@[to_additive "The map from an additive group to its completion as a group homomorphism",
  simps {fully_applied := ff}]
def coe_monoid_hom : G →* completion G :=
{ to_fun := coe,
  map_mul' := coe_mul,
  map_one' := coe_one }

@[to_additive] instance {G : Type u} [uniform_space G] [comm_group G] [uniform_group G] :
  comm_group (completion G) :=
{ mul_comm  := assume a b, completion.induction_on₂ a b
    (is_closed_eq (continuous_map₂ continuous_fst continuous_snd)
      (continuous_map₂ continuous_snd continuous_fst))
    (assume x y, by rw [← coe_mul, ← coe_mul, mul_comm]),
  .. completion.group }

end completion
end uniform_space

namespace monoid_hom
variables {G : Type u} [uniform_space G] [group G] [uniform_group G]
          {H : Type v} [uniform_space H] [group H] [uniform_group H]

open uniform_space uniform_space.completion

section extension

variables [complete_space H] [separated_space H]

/-- Extension to the completion of a continuous group homomorphism. -/
@[to_additive "Extension to the completion of a continuous group homomorphism."]
def extension (f : G →* H) (hf : continuous f) : completion G →* H :=
have hf : uniform_continuous f, from uniform_continuous_monoid_hom_of_continuous hf,
{ to_fun := completion.extension f,
  map_one' := by rw [← coe_one, extension_coe hf, map_one],
  map_mul' := assume a b, completion.induction_on₂ a b
  (is_closed_eq
    (continuous_extension.comp continuous_mul)
    ((continuous_extension.comp continuous_fst).mul (continuous_extension.comp continuous_snd)))
  (λ a b, by rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, map_mul]) }

@[to_additive] lemma extension_coe (f : G →* H) (hf : continuous f) (a : G) :
  f.extension hf a = f a :=
extension_coe (uniform_continuous_monoid_hom_of_continuous hf) a

@[continuity]
lemma continuous_extension (f : G →* H) (hf : continuous f) : continuous (f.extension hf) :=
continuous_extension

end extension

/-- Completion of a continuous group hom, as a group hom. -/
@[to_additive "Completion of a continuous group hom, as a group hom."]
protected def completion (f : G →* H) (hf : continuous f) : completion G →* completion H :=
(coe_monoid_hom.comp f).extension ((continuous_coe _).comp hf)

@[continuity, to_additive]
lemma continuous_completion (f : G →* H) (hf : continuous f) :
  continuous (f.completion hf : completion G → completion H) :=
continuous_map

@[simp, to_additive] lemma completion_coe (f : G →* H) (hf : continuous f) (a : G) :
  f.completion hf a = f a :=
map_coe (uniform_continuous_monoid_hom_of_continuous hf) a

@[simp, to_additive] lemma completion_one : (1 : G →* H).completion continuous_const = 1 :=
begin
  ext x,
  apply completion.induction_on x,
  { apply is_closed_eq ((1 : G →* H).continuous_completion continuous_const),
    simp [continuous_const] },
  { intro a,
    simp [(1 : G →* H).completion_coe continuous_const, coe_one] }
end

@[to_additive] lemma completion_mul {H : Type*} [comm_group H] [uniform_space H]
  [uniform_group H] (f g : G →* H) (hf : continuous f) (hg : continuous g) :
  (f * g).completion (hf.mul hg) = f.completion hf * g.completion hg :=
begin
  have hfg := hf.mul hg,
  ext x,
  apply completion.induction_on x,
  { exact is_closed_eq ((f * g).continuous_completion hfg)
    ((f.continuous_completion hf).mul (g.continuous_completion hg)) },
  { intro a,
    simp [(f * g).completion_coe hfg, coe_mul, f.completion_coe hf, g.completion_coe hg] }
end

end monoid_hom
