import category_theory.full_subcategory
import topology.is_locally_homeomorph
import topology.homotopy.fundamental_groupoid

variables {E X : Type*} [topological_space E] [topological_space X]

section evenly_covered

variables (f : E → X) (U : set X) (I : Type*) [topological_space I]
  {x y : X} (hx : x ∈ U) (hy : y ∈ U)

structure evenly_covered :=
(to_homeomorph : I × U ≃ₜ f ⁻¹' U)
(commutes' : ∀ p, f (to_homeomorph p) = p.2)

variables {U I}

structure evenly_covered_point :=
(to_homeomorph : f ⁻¹' {x} × U ≃ₜ f ⁻¹' U)
(commutes' : ∀ p, f (to_homeomorph p) = p.2)
(compatible' : ∀ p, to_homeomorph ⟨p, x, hx⟩ = ⟨p, (congr_arg (∈ U) p.2).mpr hx⟩)

variables {f hx}

namespace evenly_covered

instance : has_coe_to_fun (evenly_covered f U I) (λ ι, I × U → f ⁻¹' U) :=
⟨λ ι, ι.to_homeomorph⟩

variables (ι : evenly_covered f U I)

def commutes (p : I × U) : f (ι p) = p.2 :=
ι.commutes' p

def symm : f ⁻¹' U ≃ₜ I × U :=
ι.to_homeomorph.symm

def apply_symm_apply (p : f ⁻¹' U) : ι (ι.symm p) = p :=
ι.to_homeomorph.apply_symm_apply p

def symm_apply_apply (p : I × U) : ι.symm (ι p) = p :=
ι.to_homeomorph.symm_apply_apply p

def fiber_homeomorph : f ⁻¹' {y} ≃ₜ I :=
{ to_fun := λ p, (ι.symm ⟨p, (congr_arg (∈ U) p.2).mpr hy⟩).1,
  inv_fun := λ p, ⟨ι ⟨p, y, hy⟩, ι.commutes ⟨p, y, hy⟩⟩,
  left_inv := λ p, subtype.ext (by
  { have key := ι.commutes (ι.symm ⟨p, (congr_arg (∈ U) p.2).mpr hy⟩),
    rw [ι.apply_symm_apply, subtype.coe_mk, show f p = y, from p.2] at key,
    rw [subtype.coe_mk, show (⟨y, hy⟩ : U) = _, from subtype.ext key,
        prod.mk.eta, ι.apply_symm_apply, subtype.coe_mk] }),
  right_inv := λ p, by simp_rw [subtype.coe_mk, subtype.coe_eta, ι.symm_apply_apply],
  continuous_to_fun := by continuity,
  continuous_inv_fun := by continuity! }

def to_evenly_covered_point : evenly_covered_point f hy :=
{ to_homeomorph := ((ι.fiber_homeomorph hy).prod_congr (homeomorph.refl U)).trans ι.to_homeomorph,
  commutes' := λ p, ι.commutes' _,
  compatible' := λ p, subtype.ext (by
  { have this := subtype.ext_iff.mp ((ι.fiber_homeomorph hy).symm_apply_apply p),
    exact this }) }

end evenly_covered

namespace evenly_covered_point

instance : has_coe_to_fun (evenly_covered_point f hx) (λ ι, f ⁻¹' {x} × U → f ⁻¹' U) :=
⟨λ ι, ι.to_homeomorph⟩

variables (ι : evenly_covered_point f hx)

def commutes (p : f ⁻¹' {x} × U) : f (ι p) = p.2 :=
ι.commutes' p

def compatible (p : f ⁻¹' {x}) : ι ⟨p, x, hx⟩ = ⟨p, (congr_arg (∈ U) p.2).mpr hx⟩ :=
ι.compatible' p

def symm : f ⁻¹' U ≃ₜ f ⁻¹' {x} × U :=
ι.to_homeomorph.symm

def apply_symm_apply (p : f ⁻¹' U) : ι (ι.symm p) = p :=
ι.to_homeomorph.apply_symm_apply p

def symm_apply_apply (p : f ⁻¹' {x} × U) : ι.symm (ι p) = p :=
ι.to_homeomorph.symm_apply_apply p

def to_evenly_covered : evenly_covered f U (f ⁻¹' {x}) :=
{ .. ι }

def to_evenly_covered_point : evenly_covered_point f hy :=
ι.to_evenly_covered.to_evenly_covered_point hy

def fiber_homeomorph : f ⁻¹' {y} ≃ₜ f ⁻¹' {x} :=
ι.to_evenly_covered.fiber_homeomorph hy

end evenly_covered_point

end evenly_covered

variables (E X)

structure covering_map extends continuous_map E X :=
(surjective : function.surjective to_fun)
(discrete_fibers : ∀ x : X, discrete_topology (to_fun ⁻¹' {x}))
(evenly_covered : ∀ x : X, ∃ U : set X, is_open U ∧
  ∃ hx : x ∈ U, nonempty (evenly_covered_point to_fun hx))

variables {E X}

def fundamental_group (x : X) :=
let y : fundamental_groupoid X := x in y ⟶ y

noncomputable instance (x : X) : group (fundamental_group x) :=
{ mul := category_theory.category_struct.comp,
  mul_assoc := category_theory.category.assoc,
  one := category_theory.category_struct.id _,
  one_mul := category_theory.category.id_comp,
  mul_one := category_theory.category.comp_id,
  inv := category_theory.groupoid.inv,
  mul_left_inv := category_theory.groupoid.inv_comp }

namespace covering_map

infixr ` ↠ `:25 := covering_map -- shortcut: type `\rr-` or just type `\rr `

instance : has_coe_to_fun (E ↠ X) (λ _, E → X) := ⟨λ q, q.to_fun⟩

@[continuity] lemma continuous (q : E ↠ X) : continuous q := q.continuous_to_fun

lemma is_locally_homeomorph (q : E ↠ X) : is_locally_homeomorph q :=
begin
  intro x,
  obtain ⟨U, h_open, ⟨h_mem, ⟨h_covered⟩⟩⟩ := q.evenly_covered (q x),
  sorry,
end

lemma is_open_map (q : E ↠ X) : is_open_map q :=
q.is_locally_homeomorph.is_open_map

lemma covering_map_quotient_map (q : E ↠ X) : quotient_map q :=
q.is_open_map.to_quotient_map q.continuous q.surjective

end covering_map
