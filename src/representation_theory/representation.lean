import algebra.algebra.basic
import linear_algebra.direct_sum_module
import linear_algebra.dfinsupp

/-
TODO:
* From A V module to representation
* equiv between representation and representation.to_module
* Define the opposite representation ᵒᵖ according to the definition below Def 2.3.1
* Arrow notation for Hom_k,A V V₂ ?
* Decomposable implies reducible
* Schur's lemma
-/


/-
k: commutative semiring (e.g. field)
A: semiring
algebra k A: e.g. algebra A over k
A representation ρ of a k-module A on a k-module V is an algebra homomorphism from A to the algebra of endomorphisms of the k-module V.
-/
def representation
  (k : Type _) [comm_semiring k]
  (A : Type _) [semiring A] [algebra k A]
  (V : Type _) [add_comm_monoid V] [module k V] := A →ₐ[k] V →ₗ[k] V

namespace representation

variables
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]

instance has_coe_to_fun : has_coe_to_fun (representation k A V) :=
⟨λ ρ : representation k A V, A → V →ₗ[k] V, λ ρ : representation k A V, ρ.to_fun⟩

variable (ρ : representation k A V)

lemma to_fun_eq_coe : ρ.to_fun = ⇑ρ := rfl

-- lemma coe_apply (a : A) : ρ a = ρ.to_fun a := rfl

lemma one_smul (v : V) : ρ 1 v = v :=
begin
  rw alg_hom.map_one ρ,
  simp
end

lemma mul_smul (a b : A) (v : V) : ρ (a * b) v = ρ a (ρ b v) :=
begin
  rw [←linear_map.comp_apply, ←alg_hom.to_fun_eq_coe, alg_hom.map_mul' ρ],
  refl
end

lemma smul_add (a : A) (u v : V) : ρ a (u + v) = ρ a u + ρ a v := by {apply linear_map.map_add}

lemma smul_zero (a : A) : ρ a 0 = 0 := by {apply linear_map.map_zero}

lemma add_smul (a b : A) (v : V) : ρ (a + b) v = ρ a v + ρ b v := by {simp}

lemma zero_smul (v : V) : ρ 0 v = 0 := by {simp}

def to_mul_action : mul_action A V :=
{mul_action .
to_has_scalar := ⟨λ (a : A) (v : V), ρ a v⟩,
one_smul := one_smul ρ,
mul_smul := mul_smul ρ}

def to_distrib_mul_action : distrib_mul_action A V :=
{distrib_mul_action .
to_mul_action := to_mul_action ρ,
smul_add := smul_add ρ,
smul_zero := smul_zero ρ}

/-
A representation ρ : A →ₐ[k] V →ₗ[k] V can be viewed as a module V over A with scalar multiplication a • v := ρ a v.
-/
def to_module : module A V :=
{module .
to_distrib_mul_action := to_distrib_mul_action ρ,
add_smul := add_smul ρ,
zero_smul := zero_smul ρ}

end representation

/-
A member of subrepresentation k A V is a submodule k V that is invariant under action by ρ a.
-/
structure subrepresentation
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  (ρ : representation k A V) extends submodule k V :=
(invar : ∀ (a : A) (v : V), v ∈ to_submodule → ρ a v ∈ to_submodule)

namespace subrepresentation

variables
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  {ρ : representation k A V}

instance has_top : has_top (subrepresentation ρ) :=
begin
  split,
  split,
  show submodule k V,
  exact ⊤,
  intros,
  apply submodule.mem_top
end

instance has_bot : has_bot (subrepresentation ρ) :=
begin
  split,
  split,
  show submodule k V,
  exact ⊥,
  intros,
  rw submodule.mem_bot at ᾰ,
  rw ᾰ,
  rw linear_map.map_zero (ρ a),
  rw submodule.mem_bot
end

lemma has_top_to_submodule : (⊤ : subrepresentation ρ).to_submodule = (⊤ : submodule k V) := rfl

lemma has_bot_to_submodule : (⊥ : subrepresentation ρ).to_submodule = (⊥ : submodule k V) := rfl

def map_restrict (ρ' : subrepresentation ρ) (a : A) : ρ'.to_submodule →ₗ[k] ρ'.to_submodule :=
linear_map.restrict (ρ a) (ρ'.invar a)

namespace map_restrict

variables (ρ' : subrepresentation ρ)

-- lemma coe_apply (a : A) (v : ρ'.to_submodule) : ↑(ρ'.map_restrict a v) = ρ a ↑v := rfl

lemma map_one : ρ'.map_restrict 1 = 1 :=
begin
  apply linear_map.ext,
  intro v,
  unfold map_restrict,
  rw linear_map.restrict_apply,
  simp
end

lemma map_mul (a b : A) : ρ'.map_restrict (a * b) = ρ'.map_restrict a * ρ'.map_restrict b :=
begin
  apply linear_map.ext,
  intro v,
  unfold map_restrict,
  rw linear_map.restrict_apply,
  simp,
  rw linear_map.restrict_apply,
  rw linear_map.restrict_apply,
  simp
end

lemma map_zero : ρ'.map_restrict 0 = 0 :=
begin
  apply linear_map.ext,
  intro v,
  unfold map_restrict,
  rw linear_map.restrict_apply,
  simp
end

lemma map_add (a b : A) : ρ'.map_restrict (a + b) = ρ'.map_restrict a + ρ'.map_restrict b :=
begin
  apply linear_map.ext,
  intro v,
  unfold map_restrict,
  rw linear_map.restrict_apply,
  apply subtype.ext,
  simp,
  rw linear_map.restrict_apply,
  rw linear_map.restrict_apply,
  simp
end

lemma commutes (r : k) : ρ'.map_restrict (algebra_map k A r) = algebra_map k (↥(ρ'.to_submodule) →ₗ[k] ↥(ρ'.to_submodule)) r :=
begin
  rw algebra.algebra_map_eq_smul_one,
  rw algebra.algebra_map_eq_smul_one,
  unfold map_restrict,
  apply linear_map.ext,
  intro v,
  rw linear_map.restrict_apply,
  apply subtype.ext,
  simp
end

end map_restrict

def representation (ρ' : subrepresentation ρ) : representation k A ρ'.to_submodule :=
begin
  split,
  show A → (↥(ρ'.to_submodule) →ₗ[k] ↥(ρ'.to_submodule)),
  exact map_restrict ρ',

  apply map_restrict.map_one,
  apply map_restrict.map_mul,
  apply map_restrict.map_zero,
  apply map_restrict.map_add,
  apply map_restrict.commutes
end

-- lemma coe_apply (ρ' : subrepresentation ρ) (a : A) : ρ'.representation a = map_restrict ρ' a := rfl

end subrepresentation

/-
Predicate for irreducible representation V: 0 and V are the only subrepresentations
-/
def is_irreducible
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  (ρ : representation k A V) : Prop :=
∀ ρ' : subrepresentation ρ, ρ' = ⊤ ∨ ρ' = ⊥

/-
A homomorphism of representations is a linear map between the target vector spaces that commutes with the action of A on V.
-/
structure repr_hom
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  {V₂ : Type _} [add_comm_monoid V₂] [module k V₂]
  (ρ : representation k A V) (ρ₂ : representation k A V₂) extends V →ₗ[k] V₂ :=
(commutes : ∀ (a : A) (v : V), to_fun (ρ a v) = ρ₂ a (to_fun v))

namespace repr_hom

variables
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  {V₂ : Type _} [add_comm_monoid V₂] [module k V₂]
  {ρ : representation k A V} {ρ₂ : representation k A V₂}

/-
The kernal of a repr_hom as subrepresentation of the source representation
-/
def ker (φ : repr_hom ρ ρ₂) : subrepresentation ρ :=
begin
  split,
  show submodule k V,
  {exact φ.to_linear_map.ker},
  {intros a v,
  simp,
  rw ←linear_map.to_fun_eq_coe,
  rw φ.commutes,
  intro h,
  rw h,
  simp}
end

/-
The range of a repr_hom as a subrepresentation of the target representation
-/
def range (φ : repr_hom ρ ρ₂) : subrepresentation ρ₂ :=
begin
  split,
  show submodule k V₂,
  {exact φ.to_linear_map.range},
  {intros a v,
  rw linear_map.mem_range,
  rw linear_map.mem_range,
  rw ←linear_map.to_fun_eq_coe,
  intro h,
  cases h with u hu,
  use ρ a u,
  rw φ.commutes,
  rw hu}
end

lemma repr_ker_is_linear_map_ker (φ : repr_hom ρ ρ₂) : (ker φ).to_submodule = φ.to_linear_map.ker := by unfold ker

lemma repr_range_is_linear_map_range (φ : repr_hom ρ ρ₂) : (range φ).to_submodule = φ.to_linear_map.range := by unfold range

end repr_hom

/-
An isomorphism of representations is a linear equiv ...
-/
structure repr_iso
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  {V₂ : Type _} [add_comm_monoid V₂] [module k V₂]
  (ρ : representation k A V) (ρ₂ : representation k A V₂) extends V ≃ₗ[k] V₂ :=
(commutes : ∀ (a : A) (v : V), to_fun (ρ a v) = ρ₂ a (to_fun v))

namespace representation

/-
Embedding of a subrepresentation into the larger representation, as a homomorphism of representations.
-/
def subtype
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  {ρ : representation k A V} (ρ' : subrepresentation ρ) : repr_hom ρ'.representation ρ :=
begin
  split,
  show ↥(ρ'.to_submodule) →ₗ[k] V,
  apply submodule.subtype,

  simp,
  intros a v,
  refl
end

end representation


namespace repr_iso

variables
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  {V₂ : Type _} [add_comm_monoid V₂] [module k V₂]
  {ρ : representation k A V} {ρ₂ : representation k A V₂}

def to_repr_hom (φ : repr_iso ρ ρ₂) : repr_hom ρ ρ₂ :=
⟨φ.to_linear_equiv.to_linear_map, φ.commutes⟩

def symm (φ : repr_iso ρ ρ₂) : repr_iso ρ₂ ρ :=
begin
  split,
    show V₂ ≃ₗ[k] V,
    exact φ.to_linear_equiv.symm,
  intros,
  have : ρ₂ a v = ρ₂ a v, from rfl,
  nth_rewrite 0 ←linear_equiv.apply_symm_apply φ.to_linear_equiv (ρ₂ a v) at this,
  nth_rewrite 1 ←linear_equiv.apply_symm_apply φ.to_linear_equiv v at this,
  rw ←linear_equiv.to_fun_eq_coe at this,
  rw ←φ.commutes a (φ.to_linear_equiv.symm v) at this,
  apply_fun φ.to_linear_equiv.symm at this,
  rw linear_equiv.to_fun_eq_coe at this,
  rw linear_equiv.symm_apply_apply φ.to_linear_equiv at this,
  rw linear_equiv.symm_apply_apply φ.to_linear_equiv at this,
  exact this
end

def trans
  {V₃ : Type _} [add_comm_monoid V₃] [module k V₃]
  {ρ₃ : representation k A V₃}
  (φ : repr_iso ρ ρ₂) (ψ : repr_iso ρ₂ ρ₃) : repr_iso ρ ρ₃ :=
begin
  sorry
end

end repr_iso

namespace direct_sum_repr

variables
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {ι : Type _} {V : ι → Type _}
  [Π (i : ι), add_comm_monoid (V i)] [Π (i : ι), module k (V i)]
  (ρ : Π (i : ι), representation k A (V i))

def to_fun (a : A) : direct_sum ι V →ₗ[k] direct_sum ι V :=
dfinsupp.map_range.linear_map (λ i : ι, ρ i a)

lemma map_one : to_fun ρ 1 = 1 :=
begin
  unfold to_fun,
  have : (λ (i : ι), ρ i 1) = λ (i : ι), linear_map.id,
    apply funext,
    intro i,
    apply (ρ i).map_one',
  rw this,
  apply dfinsupp.map_range.linear_map_id
end

lemma map_mul (a b : A) : to_fun ρ (a * b) = to_fun ρ a * to_fun ρ b :=
begin
  unfold to_fun,
  have : (λ i : ι, ρ i (a * b)) = λ i : ι, (ρ i a).comp (ρ i b),
    apply funext,
    intro i,
    apply (ρ i).map_mul,
  rw this,
  apply dfinsupp.map_range.linear_map_comp
end

lemma map_zero : to_fun ρ 0 = 0 :=
begin
  unfold to_fun,
  have : (λ (i : ι), ρ i 0) = λ (i : ι), 0,
    apply funext,
    intro i,
    apply (ρ i).map_zero',
  rw this,
  apply linear_map.ext,
  intro vv,
  rw dfinsupp.map_range.linear_map_apply,
  apply dfinsupp.ext,
  simp
end

lemma map_add (a b : A) : to_fun ρ (a + b) = to_fun ρ a + to_fun ρ b :=
begin
  unfold to_fun,
  have : (λ (i : ι), ρ i (a + b)) = λ (i : ι), ρ i a + ρ i b,
    apply funext,
    intro i,
    apply (ρ i).map_add',
  rw this,
  apply linear_map.ext,
  intro vv,
  rw linear_map.add_apply,
  rw dfinsupp.map_range.linear_map_apply,
  rw dfinsupp.map_range.linear_map_apply,
  rw dfinsupp.map_range.linear_map_apply,
  apply dfinsupp.ext,
  simp,
end

lemma commutes (r : k) : to_fun ρ ((algebra_map k A) r) = (algebra_map k (direct_sum ι V →ₗ[k] direct_sum ι V)) r :=
begin
  unfold to_fun,
  rw algebra.algebra_map_eq_smul_one,
  rw algebra.algebra_map_eq_smul_one,
  have : (λ (i : ι), ρ i (r • 1)) = λ (i : ι), r • 1,
    apply funext,
    intro i,
    rw ←algebra.algebra_map_eq_smul_one,
    apply (ρ i).commutes',
  rw this,
  apply linear_map.ext,
  intro vv,
  rw dfinsupp.map_range.linear_map_apply,
  apply dfinsupp.ext,
  simp
end

end direct_sum_repr

/-
Given representations ρ indexed by ι, build the direct sum representation.
-/
def direct_sum_repr
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  (ι : Type _) {V : ι → Type _}
  [Π (i : ι), add_comm_monoid (V i)] [Π (i : ι), module k (V i)]
  (ρ : Π (i : ι), representation k A (V i)) : representation k A (direct_sum ι V) :=
begin
  split,
  show A → (direct_sum ι V →ₗ[k] direct_sum ι V),
  exact direct_sum_repr.to_fun ρ,
  all_goals {simp},
  {apply direct_sum_repr.map_one},
  {apply direct_sum_repr.map_mul},
  {apply direct_sum_repr.map_zero},
  {apply direct_sum_repr.map_add},
  {apply direct_sum_repr.commutes}
end

lemma to_module_map_range
  {k : Type _} [comm_semiring k]
  {ι : Type _} [decidable_eq ι] {V : ι → Type _}
  [Π (i : ι), add_comm_monoid (V i)] [Π (i : ι), module k (V i)]
  {W : Type _} [add_comm_monoid W] [module k W]
  (ρ : Π i : ι, V i →ₗ[k] V i)
  (φ : Π i : ι, V i →ₗ[k] W) :
∀ (v : direct_sum ι V), (direct_sum.to_module k ι W φ) (dfinsupp.map_range.linear_map ρ v) = direct_sum.to_module k ι W (λ i : ι, (φ i).comp (ρ i)) v :=
begin
  intro vv,
  rw ←linear_map.comp_apply,
  apply direct_sum.to_module.ext,
  intro i,
  change λ (i : ι), V i with V,
  apply linear_map.ext,
  intro v,
  rw linear_map.comp_apply,
  rw linear_map.comp_apply,
  rw linear_map.comp_apply,
  rw direct_sum.to_module_lof,
  simp,
  rw ←direct_sum.single_eq_lof,
  unfold direct_sum.to_module dfinsupp.lsum,
  simp
end

namespace direct_sum_repr

variables
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  (ι : Type _) {V : ι → Type _}
  [Π (i : ι), add_comm_monoid (V i)] [Π (i : ι), module k (V i)]
  (ρ : Π (i : ι), representation k A (V i))

@[simp]
lemma to_fun_eq_def (a : A) :
direct_sum_repr ι ρ a = dfinsupp.map_range.linear_map (λ i : ι, ρ i a) := rfl

lemma apply (a : A) (vv : direct_sum ι V) (i : ι) :
  direct_sum_repr ι ρ a vv i = ρ i a (vv i) :=
begin
  rw ←representation.to_fun_eq_coe,
  simp
end

/-
Projection of direct sum representation onto the i-th component, as a homomorphism of representations.
-/
def component (i : ι) : repr_hom (direct_sum_repr ι ρ) (ρ i) :=
begin
  split,
  show direct_sum ι (λ (i : ι), V i) →ₗ[k] V i,
  apply direct_sum.component,

  change (λ (i : ι), V i) with V,
  change (λ (i : ι), V i) with V,
  intros a vv,
  simp,
  rw ←direct_sum.apply_eq_component,
  rw ←direct_sum.apply_eq_component,
  apply apply
end

/-
From a collection of individual repr_hom to the same representation, build a repr_hom from the direct sum of starting representations to the target representation.

Arguments: index set ι, collection of source representations ρ, target representation ρ₂, collection of repr_hom from each ρ i to ρ₂.
-/
def hom_to_representation
  {V₂ : Type _} [add_comm_monoid V₂] [module k V₂]
  (ρ₂ : representation k A V₂) [decidable_eq ι]
  (φ : Π i : ι, repr_hom (ρ i) ρ₂) : repr_hom (direct_sum_repr ι ρ) ρ₂ :=
begin
  split,
  show direct_sum ι (λ (i : ι), V i) →ₗ[k] V₂,
  exact direct_sum.to_module k ι V₂ (λ i : ι, (φ i).to_linear_map),

  simp [-dfinsupp.map_range.linear_map_apply],
  change (λ (i : ι), V i) with V,
  intros a vv,
  rw to_module_map_range,
  unfold direct_sum.to_module dfinsupp.lsum,
  simp,
  have : ⇑(ρ₂ a) = (ρ₂ a).to_add_monoid_hom,
    refl,
  rw this,
  rw ←add_monoid_hom.comp_apply,
  rw dfinsupp.comp_sum_add_hom,
  have : (λ (i : ι), ((φ i).to_linear_map.comp (ρ i a)).to_add_monoid_hom) = λ (i : ι), (ρ₂ a).to_add_monoid_hom.comp (φ i).to_linear_map.to_add_monoid_hom,
    apply funext,
    intro i,
    apply add_monoid_hom.ext,
    intro v,
    simp,
    rw ←linear_map.to_fun_eq_coe,
    rw (φ i).commutes,
  rw this
end

end direct_sum_repr

namespace direct_sum_repr

variables
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V]
  {ρ : representation k A V} {ι : Type _} [decidable_eq ι]
  (ρ' : ι → subrepresentation ρ)

/-
The direct sum of a collection of subrepresentations is said to be internal if the canonical map from the direct sum representaation to the parent representation is bijective. TODO: there is a repr_iso between the parent representation and the direct sum of subrepresentations.
-/
def is_internal : Prop :=
function.bijective (direct_sum_repr.hom_to_representation ι (λ i : ι, (ρ' i).representation) ρ (λ i: ι, representation.subtype (ρ' i))).to_fun

end direct_sum_repr

/-
Nontrivial decomposition: a collection of nontrivial subrepresentations whose direct_sum is internal.
-/
structure decomposition
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V] [nontrivial V]
  (ρ : representation k A V) :=
{ι : Type _}
[nontriv_ι : nontrivial ι]
[dec_ι : decidable_eq ι]
(subreps : ι → subrepresentation ρ)
(nontriv_subreps : Π i : ι, subreps i ≠ ⊥)
(internal : direct_sum_repr.is_internal subreps)

/-
Predicate of decomposition
-/
def is_decomposable
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V] [nontrivial V]
  (ρ : representation k A V) :=
nonempty (decomposition ρ)

structure decomposition2
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V] [nontrivial V]
  (ρ : representation k A V) :=
{ι : Type _}
[nontriv_ι : nontrivial ι]
[dec_ι : decidable_eq ι]
(subreps : ι → subrepresentation ρ)
(nontriv_subreps : Π i : ι, subreps i ≠ ⊥)
(iso : repr_iso (direct_sum_repr ι (λ i : ι, (subreps i).representation)) ρ)

def is_decomposable2
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V] [nontrivial V]
  (ρ : representation k A V) :=
nonempty (decomposition2 ρ)

lemma reducible_of_decomposable
  {k : Type _} [comm_semiring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_monoid V] [module k V] [nontrivial V]
  {ρ : representation k A V} : is_decomposable ρ → ¬is_irreducible ρ :=
begin
  sorry
end

namespace schur

variables
  {k : Type _} [comm_ring k]
  {A : Type _} [semiring A] [algebra k A]
  {V : Type _} [add_comm_group V] [module k V]
  {V₂ : Type _} [add_comm_group V₂] [module k V₂]
  {ρ : representation k A V} {ρ₂ : representation k A V₂}

lemma injective_of_irreducible
  (φ : repr_hom ρ ρ₂) (h : φ.to_linear_map ≠ 0) : is_irreducible ρ → φ.to_linear_map.ker = ⊥ :=
begin
  intro hh,
  have := hh (repr_hom.ker φ),
  cases this,
  {apply_fun subrepresentation.to_submodule at this,
  rw repr_hom.repr_ker_is_linear_map_ker at this,
  rw subrepresentation.has_top_to_submodule at this,
  have := linear_map.ker_eq_top.mp this,
  exact absurd this h},
  {apply_fun subrepresentation.to_submodule at this,
  rw repr_hom.repr_ker_is_linear_map_ker at this,
  rw subrepresentation.has_bot_to_submodule at this,
  exact this}
end

lemma surjective_of_irreducible
  (φ : repr_hom ρ ρ₂) (h : φ.to_linear_map ≠ 0) : is_irreducible ρ₂ → φ.to_linear_map.range = ⊤ :=
begin
  intro hh,
  have := hh (repr_hom.range φ),
  cases this,
  {apply_fun subrepresentation.to_submodule at this,
  rw repr_hom.repr_range_is_linear_map_range at this,
  rw subrepresentation.has_top_to_submodule at this,
  exact this},
  {apply_fun subrepresentation.to_submodule at this,
  rw repr_hom.repr_range_is_linear_map_range at this,
  rw subrepresentation.has_bot_to_submodule at this,
  have := linear_map.range_eq_bot.mp this,
  exact absurd this h}
end

noncomputable def linear_equiv_of_irreducible
  (φ : repr_hom ρ ρ₂) (h : φ.to_linear_map ≠ 0) : is_irreducible ρ → is_irreducible ρ₂ → V ≃ₗ[k] V₂ :=
begin
  intros h1 h2,
  apply linear_equiv.of_bijective,
  show V →ₗ[k] V₂,
  {exact φ.to_linear_map},
  {exact injective_of_irreducible φ h h1},
  {exact surjective_of_irreducible φ h h2}
end

noncomputable lemma main
  (φ : repr_hom ρ ρ₂) (h : φ.to_linear_map ≠ 0) : is_irreducible ρ → is_irreducible ρ₂ → repr_iso ρ ρ₂ :=
begin
  intros h1 h2,
  split,
  show V ≃ₗ[k] V₂,
  {exact linear_equiv_of_irreducible φ h h1 h2},
  {intros a v,
  simp,
  unfold linear_equiv_of_irreducible linear_equiv.of_bijective,
  repeat {rw [linear_equiv.trans_apply, linear_equiv.of_top_apply, linear_equiv.of_injective_apply]},
  apply φ.commutes}
end

end schur