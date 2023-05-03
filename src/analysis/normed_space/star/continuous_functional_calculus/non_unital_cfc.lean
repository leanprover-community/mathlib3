import algebra.algebra.unitization
import algebra.algebra.spectrum
import topology.algebra.ring.basic
import topology.algebra.star
import topology.continuous_function.polynomial
import topology.continuous_function.zero_at_infty
import topology.alexandroff
import topology.continuous_function.ideals
import ring_theory.non_unital_subsemiring.basic
import ring_theory.non_unital_subring.basic
import analysis.normed_space.star.continuous_functional_calculus.basic

.

example (α β γ : Prop) (h : ¬ γ) : ¬ β :=
begin
  refine h ∘ _,
  sorry
end

#exit

section

variables {α β : Type*} [topological_space α] [has_zero β] [topological_space β]

lemma open_embedding_inclusion_diff_closed (s t : set α) (ht : is_closed t) :
  open_embedding (set.inclusion $ set.diff_subset s t) :=
{ induced := topological_space.subset_trans (set.diff_subset _ _),
  inj := set.inclusion_injective (set.diff_subset _ _),
  open_range :=
  begin
    rw set.range_inclusion (set.diff_subset _ _),
    convert is_open_induced (@is_closed.is_open_compl _ _ _ ht),
    ext x,
    exact ⟨set.not_mem_of_mem_diff, set.mem_diff_of_mem x.prop⟩,
  end }

instance (s t : set α) [locally_compact_space s] [is_closed t] :
  locally_compact_space (s \ t : set α) :=
(open_embedding_inclusion_diff_closed s t ‹_›).locally_compact_space

instance has_sdiff.sdiff.locally_compact_space_singleton (s : set α) [locally_compact_space s]
  [t1_space α] (x : α) : locally_compact_space (s \ {x} : set α) :=
@has_sdiff.sdiff.locally_compact_space α _ s _ _ is_closed_singleton

/-
noncomputable def alexandroff_one_point (s : set α) [decidable_eq α] [compact_space s]
  [t2_space α] (x : s) : s ≃ₜ alexandroff (s \ {x} : set α) :=
{ to_fun := λ y, if hy : y = x then ∞ else
    ↑(⟨y, set.mem_diff_singleton.mpr ⟨y.prop, (not_iff_not.mpr subtype.ext_iff).mp hy⟩⟩ : (s \ {x} : set α)),
  inv_fun := alexandroff.rec (λ _, s) x (set.inclusion $ set.diff_subset _ _),
  left_inv :=
  begin
    intros y,
    lift x to s using hx,
    by_cases hy : (y : α) = x,
    subst hy,
    ext,
    have : hx = y.prop := rfl,
    subst this,
    simp only [subtype.coe_eta],
  end,
  right_inv := _,
  continuous_to_fun := _,
  continuous_inv_fun := _ }
-/

end section

namespace continuous_map

open polynomial
open_locale polynomial zero_at_infty

variables {R : Type*} [comm_semiring R] [metric_space R] [topological_semiring R]

/-
def subset_to_ideal {s t : set R} (hst : t ⊆ s) : ideal C(s, R) :=
{ carrier := {f : C(s, R) | ∀ x : s, (x : R) ∈ t → f x = 0},
  add_mem' := λ f₁ f₂ hf₁ hf₂ x hx,
    by simp only [continuous_map.add_apply, hf₁ x hx, hf₂ x hx, add_zero],
  zero_mem' := λ _ _, rfl,
  smul_mem' := λ f₁ f hf x hx,
    by simp only [continuous_map.mul_apply, algebra.id.smul_eq_mul, hf x hx, mul_zero] }
-/

instance {R : Type*} [has_zero R] (s : set R) : has_zero (s ∪ {0} : set R) :=
  ⟨⟨0, set.mem_union_right _ $ set.mem_singleton 0⟩⟩

lemma set.union_coe_zero {s : set R} : ((0 : s ∪ {0}) : R) = 0 := rfl


/-
def mk_foo (f : R → R) (hf : continuous_on f s) (hf₀ : f 0 = 0) :
  C₀((s \ {0} : set R), R) :=
{ to_fun := λ x, f x,
  continuous_to_fun := _,
  zero_at_infty' := _ }

def mk_foo (f : C(s, R)) (hf₀ : ∀ x : s, (x : R) = 0 → f x = 0) :
  C₀((s \ {0} : set R), R) :=
{ to_fun := λ x, f (set.inclusion (set.diff_subset _ _) x),
  continuous_to_fun := _,
  zero_at_infty' := _ }
  -/

end continuous_map

section spectrumₙ
universes u v w
variables {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [comm_ring S] [non_unital_ring A]
variables [module S A] [is_scalar_tower S A A] [smul_comm_class S A A]
variables [algebra R S] [distrib_mul_action R A] [is_scalar_tower R S A]

variables (R S)

/-- The spectrum of an element in a non-unital `R`-algebra `A` relative to a the minimal unitization
of `A` over an intermediate algebra `S`.

This is important because it allows us to talk about, for example, the `ℝ≥0` spectrum of an element
of a C⋆-algebra. -/
def spectrumₙ (a : A) : set R := spectrum R (a : unitization S A)

end spectrumₙ


/-
example (a : A) : has_compl (set ((spectrumₙ R S a) ∪ {0} : set R)) := infer_instance

example (a : A) : set ((spectrumₙ R S a) ∪ {0} : set R) := {0}ᶜ

variables [star_ring R] [metric_space R] [topological_semiring R] [has_continuous_star R]

@[reducible]
def continuous_map.ideal_zero_at_zero_set (s : set R) : ideal C((s ∪ {0} : set R), R) :=
continuous_map.ideal_of_set R {0}ᶜ
-/

/-- the ideal of continuous functions on a topological semiring which are zero at zero. -/
def continuous_map.ideal_zero_at_zero (R : Type*) [comm_semiring R] [topological_space R]
  [topological_semiring R] : ideal C(R, R) :=
continuous_map.ideal_of_set R ({0}ᶜ : set R)

namespace continuous_map
namespace ideal_zero_at_zero

variables {R : Type*} [comm_semiring R] [topological_space R] [topological_semiring R]
notation `C(` R `, ` R `)₀` := continuous_map.ideal_zero_at_zero R

instance _root_.ideal.non_unital_subsemiring_class {R : Type*} [comm_semiring R] :
  non_unital_subsemiring_class (ideal R) R :=
{   mul_mem := λ I a b ha hb, I.mul_mem_left a hb,
  .. submodule.add_submonoid_class }

instance _root_.ideal.non_unital_subring_class {R : Type*} [comm_ring R] :
  non_unital_subring_class (ideal R) R :=
{ .. ideal.non_unital_subsemiring_class }

instance _root_.ideal.topological_semiring (I : ideal R) :
  topological_semiring I :=
{ .. inducing.has_continuous_add (⟨coe, λ _ _, rfl⟩ : add_hom I R) ⟨rfl⟩,
  .. inducing.has_continuous_mul (⟨coe, λ _ _, rfl⟩ : mul_hom I R) ⟨rfl⟩ }

instance _root_.ideal.topological_ring {R : Type*} [comm_ring R] [topological_space R]
  [topological_ring R] (I : ideal R) :
  topological_ring I :=
{ .. I.topological_semiring }

lemma mem_iff {R : Type*} [comm_semiring R] [topological_space R]
  [topological_semiring R] (f : C(R, R)) : f ∈ C(R, R)₀ ↔ f 0 = 0 :=
continuous_map.mem_ideal_of_set_compl_singleton 0 f

alias mem_iff ↔ map_zero_of_mem mem_of_map_zero

@[simp]
lemma coe_coe (f : C(R, R)₀) : ⇑(f : C(R, R)) = f := rfl

@[simp]
lemma coe_add (f g : C(R, R)₀) : (↑(f + g) : C(R, R)) = f + g := rfl

@[simp]
lemma coe_mul (f g : C(R, R)₀) : (↑(f * g) : C(R, R)) = f * g := rfl

-- smul version?

@[simp]
lemma coe_zero : ((0 : C(R, R)₀) : C(R, R)) = 0 := rfl

@[simp]
lemma coe_mk (f : C(R, R)) (h) : ⇑(⟨f, h⟩ : C(R, R)₀) = f := rfl

instance zero_hom_class : zero_hom_class C(R, R)₀ R R :=
{ coe := λ f, f,
  coe_injective' := λ f g h,
  begin
    simp only [←coe_coe] at h,
    exact subtype.ext (fun_like.coe_injective h),
  end,
  map_zero := λ f, map_zero_of_mem _ f.prop }

@[ext]
lemma ext (f g : C(R, R)₀) (h : ∀ x : R, f x = g x) : f = g :=
fun_like.ext _ _ h

lemma ext_iff {f g : C(R, R)₀} : f = g ↔ ∀ x : R, f x = g x :=
fun_like.ext_iff

instance has_star [star_ring R] [has_continuous_star R] :
  has_star C(R, R)₀ :=
{ star := λ f, ⟨star f,
  begin
    simp only [mem_iff, continuous_map.star_apply, coe_coe, star_eq_zero],
    exact map_zero_of_mem f f.prop,
  end⟩ }

instance star_ring [star_ring R] [has_continuous_star R] :
  star_ring C(R, R)₀ :=
{ star := star,
  star_involutive := λ f, subtype.ext $ continuous_map.ext $ λ x, star_star (f x),
  star_mul := λ f g, subtype.ext $ continuous_map.ext $ λ x, star_mul (f x) (g x),
  star_add := λ f g, subtype.ext $ continuous_map.ext $ λ x, star_add (f x) (g x) }

@[simp]
lemma coe_star [star_ring R] [has_continuous_star R] (f : C(R, R)₀) :
  (↑(star f) : C(R, R)) = star f := rfl
.

variable (R)

protected def id : C(R, R)₀ :=
⟨continuous_map.id R, mem_of_map_zero _ rfl⟩

variable {R}

@[simp]
lemma coe_id : ⇑(continuous_map.ideal_zero_at_zero.id R) = continuous_map.id R :=
rfl

/- I think we don't want this because then we get *two* coercions to `continuous_map`, and we likely
prefer the subtype coercion.
instance continuous_map.ideal_zero_at_zero.continuous_map_class {R : Type*} [comm_semiring R]
  [topological_space R] [topological_semiring R] : continuous_map_class C(R, R)₀ R R :=
{ coe := λ f, f,
  coe_injective' := fun_like.coe_injective,
  map_continuous := λ f, map_continuous (f : C(R, R)) }
  -/

def comp (g f : C(R, R)₀) : C(R, R)₀ :=
{ val := (g : C(R, R)).comp f,
  property := mem_of_map_zero _
    (by simp only [continuous_map.comp_apply, coe_coe, map_zero f,
      map_zero g]) }

@[simp]
lemma coe_comp (g f : C(R, R)₀) : ⇑(comp g f) = g ∘ f := rfl

@[simp]
lemma comp_apply (g f : C(R, R)₀) (x : R) : comp g f x = g (f x) := rfl

@[simp]
lemma comp_id (g : C(R, R)₀) : comp g (continuous_map.ideal_zero_at_zero.id R) = g :=
by {ext, refl}

@[simp]
lemma id_comp (g : C(R, R)₀) : comp (continuous_map.ideal_zero_at_zero.id R) g = g :=
by {ext, refl}

open_locale nnreal

def _root_.unitization.of_prod {R : Type*} {A : Type*} (x : R × A) : unitization R A := x

@[simp]
lemma _root_.unitization.of_prod_snd {R : Type*} {A : Type*} (r : R) (a : A) :
  (unitization.of_prod (r, a)).snd = a := rfl

@[simp]
lemma _root_.unitization.of_prod_fst {R : Type*} {A : Type*} (r : R) (a : A) :
  (unitization.of_prod (r, a)).fst = r := rfl

instance _root_.continuous_map.module'' {α : Type*} [topological_space α]
  (R : Type*) [semiring R] [topological_space R] [topological_semiring R]
  (M : Type*) [topological_space M] [add_comm_monoid M] [has_continuous_add M]
  [module R M] [has_continuous_smul R M] :
  module C(α, R) C(α, M) :=
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x),
  zero_smul := λ f, by ext x; exact zero_smul _ _,
  smul_zero := λ r, by ext x; exact smul_zero _, }

instance : is_scalar_tower R C(R, R)₀ C(R, R)₀ :=
{ smul_assoc := λ r f₁ f₂, subtype.ext $ smul_assoc r (f₁ : C(R, R)) (f₂ : C(R, R)) }

instance : smul_comm_class R C(R, R)₀ C(R, R)₀ :=
{ smul_comm := λ r f₁ f₂, subtype.ext $ smul_comm r (f₁ : C(R, R)) (f₂ : C(R, R)) }

@[protected]
def unitization_star_alg_hom [star_ring R] [has_continuous_star R] :
  unitization R C(R, R)₀ →⋆ₐ[R] C(R, R) :=
{ to_fun := λ f, f.snd + algebra_map R C(R, R) f.fst,
  map_mul' := λ f₁ f₂,
  begin
    simp only [unitization.snd_mul, submodule.coe_smul_of_tower,
      continuous_map.ideal_zero_at_zero.coe_add, map_mul, unitization.fst_mul,
      continuous_map.ideal_zero_at_zero.coe_mul, mul_add, add_mul, algebra.algebra_map_eq_smul_one,
      smul_mul_assoc, one_mul],
    rw [mul_smul_comm, mul_one, smul_add, smul_smul],
    ring,
  end,
  map_add' := λ f₁ f₁,
    by simp only [unitization.fst_add, unitization.snd_add, coe_add, map_add, add_add_add_comm],
  map_star' := λ f,
  begin
    simp only [star_add_monoid.star_add, add_left_inj, unitization.snd_star, algebra_map_star_comm,
      unitization.fst_star, coe_star],
  end,
  map_zero' := by simp only [add_zero, eq_self_iff_true, continuous_map.ideal_zero_at_zero.coe_zero,
    unitization.snd_zero, map_zero, unitization.fst_zero],
  map_one' :=
  begin
    ext x,
    rw [unitization.snd_one, unitization.fst_one, coe_zero, zero_add],
    refl,
  end,
  commutes' := λ r, by simp only [unitization.fst_inl, unitization.snd_inl, eq_self_iff_true,
    zero_add, coe_zero, unitization.algebra_map_eq_inl] }

.

end ideal_zero_at_zero
end continuous_map

namespace unitization

instance {R A : Type*} [topological_space R] [topological_space A] :
  topological_space (unitization R A) := prod.topological_space

/-- The coercion from a non-unital `R`-algebra `A` to its unitization `unitization R A`
realized as a non-unital star algebra homomorphism. -/
@[simps]
def coe_non_unital_star_alg_hom (R A : Type*) [comm_semiring R] [non_unital_semiring A] [module R A]
  [star_add_monoid R] [has_star A] :
  A →⋆ₙₐ[R] unitization R A :=
{ to_fun := coe,
  map_smul' := coe_smul R,
  map_zero' := coe_zero R,
  map_add' := coe_add R,
  map_mul' := coe_mul R,
  map_star' := coe_star }

end unitization

#exit



lemma mem_range_coe_non_unital_star_alg_hom (R A : Type*) [comm_semiring R] [non_unital_semiring A]
  [module R A] [star_add_monoid R] [has_star A] (x : unitization R A) :
  x ∈ star_alg_hom.range (coe_non_unital_star_alg_hom R A) ↔  :=
{ to_fun := coe,
  map_smul' := coe_smul R,
  map_zero' := coe_zero R,
  map_add' := coe_add R,
  map_mul' := coe_mul R,
  map_star' := coe_star }

#check star_alg_hom.cod_restrict
#check non_unital_star_alg_hom.range

end unitization


#where

universes u v w
variables {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [comm_ring S] [non_unital_ring A]
variables [star_ring R] [topological_space R] [topological_semiring R] [has_continuous_star R]
variables [star_ring S] [topological_space S] [star_ring A] [topological_space A]
variables [module S A] [is_scalar_tower S A A] [smul_comm_class S A A] [star_module S A]
variables [algebra R S] [distrib_mul_action R A] [is_scalar_tower R S A]
variables (a : A) [cfc_core_class R (a : unitization S A)]

def cfcₙ_part : unitization R C(R, R)₀ →⋆ₐ[R] unitization S A :=
(cfc₂ a : C(R, R) →⋆ₐ[R] unitization S A).comp continuous_map.ideal_zero_at_zero.unitization_star_alg_hom

#exit

@[protected]
def unitization {R : Type*} [comm_ring R] [star_ring R] [topological_space R]
  [topological_ring R] [has_continuous_star R] :
  unitization R C(R, R)₀ ≃⋆ₐ[R] C(R, R) :=
{ to_fun := λ f, f.snd + algebra_map R C(R, R) f.fst,
  inv_fun := λ f, unitization.of_prod (f 0, ⟨(f : C(R, R)) - algebra_map R C(R, R) (f 0),
  begin
    refine mem_of_map_zero (f - algebra_map R C(R, R) (f 0)) _,
    simp only [sub_apply, algebra_map_apply, algebra.id.smul_eq_mul, mul_one, sub_self],
  end⟩),
  left_inv := λ f, sorry,
  /- begin
    have : ((f.snd : C(R, R)) + algebra_map R C(R, R) f.fst) 0 = f.fst,
    sorry { show f.snd 0 + algebra_map R C(R, R) f.fst 0 = f.fst,
      rw [map_zero f.snd, zero_add],
      refl },
    refine unitization.ext sorry _,
    ext1 x,
    simp only [mul_one, algebra.id.smul_eq_mul, algebra_map_apply, continuous_map.add_apply,
      zero_add, map_zero, continuous_map.ideal_zero_at_zero.coe_coe, unitization.of_prod_snd,
      coe_mk, continuous_map.sub_apply, add_sub_cancel],
  end, -/
  right_inv := λ f, sorry,
  /- begin
    ext1 x,
    simp only [unitization.of_prod_snd, mul_one, algebra.id.smul_eq_mul, unitization.of_prod_fst,
      algebra_map_apply, continuous_map.sub_apply, continuous_map.add_apply, submodule.coe_mk,
      sub_add_cancel],
  end,-/
  map_mul' := λ f₁ f₂,
  begin
    simp only [unitization.snd_mul, submodule.coe_smul_of_tower,
      continuous_map.ideal_zero_at_zero.coe_add, map_mul, unitization.fst_mul,
      continuous_map.ideal_zero_at_zero.coe_mul, mul_add, add_mul, algebra.algebra_map_eq_smul_one,
      smul_mul_assoc, one_mul],
    rw [mul_smul_comm, mul_one, smul_add, smul_smul],
    ring,
  end,
  map_add' := λ f₁ f₁,
    by simp only [unitization.fst_add, unitization.snd_add, coe_add, map_add, add_add_add_comm],
  map_star' := λ f,
  begin
    simp only [star_add_monoid.star_add, add_left_inj, unitization.snd_star, algebra_map_star_comm,
      unitization.fst_star, coe_star],
  end,
  map_smul' := λ r f,
  begin
    simp only [smul_add, submodule.coe_smul_of_tower, unitization.fst_smul,
      add_right_inj, map_mul, unitization.snd_smul],
    ext x,
    refl,
  end }

end ideal_zero_at_zero
end continuous_map


.

/-
class cfcₙ_core_class [star_ring R] [metric_space R] [topological_semiring R]
  [has_continuous_star R] [star_ring A] [topological_space A] (a : A) :=
(to_non_unital_star_alg_hom : C(R, R)₀ →⋆ₙₐ[R] A)
(hom_continuous : continuous to_non_unital_star_alg_hom)
(hom_map_id : to_non_unital_star_alg_hom (continuous_map.ideal_zero_at_zero.id R) = a)
(hom_eq_of_eq_on : ∀ f g : C(R, R)₀, (spectrumₙ R S a).eq_on f g →
  to_non_unital_star_alg_hom f = to_non_unital_star_alg_hom g)
(hom_map_spectrum : ∀ f : C(R, R)₀,
  spectrumₙ R S (to_non_unital_star_alg_hom f) = f '' (spectrumₙ R S a))
-/

end

#exit

So, what is the idea?

unitization R C(R, R)₀ ≃ C(R, R) →⋆ₐ[R] unitization S A

Using unitization.lift we get a C(R, R)₀ →⋆ₐ[R] unitization S A.

unitization R C(R, R)₀ ≃⋆ₐ[R] C(R, R)

We claim that the range of this map does not contain any scalars. And indeed, since
