import topology.is_locally_homeomorph

variables {E X : Type*} [topological_space E] [topological_space X] (f : E → X)
  (I : Type*) [topological_space I] {x y : X} (U V : set X)

structure evenly_covered_set extends homeomorph (I × U) (f ⁻¹' U) :=
(commutes' : ∀ p, f (to_fun p) = p.2)

variables {f I U V}

namespace evenly_covered_set

variables (ϕ : evenly_covered_set f I U)

instance : has_coe_to_fun (evenly_covered_set f I U) (λ ι, I × U → f ⁻¹' U) :=
⟨λ ϕ, ϕ.to_fun⟩

def symm : f ⁻¹' U ≃ₜ I × U :=
ϕ.to_homeomorph.symm

@[simp] def apply_symm_apply (p : f ⁻¹' U) : ϕ (ϕ.symm p) = p :=
ϕ.to_equiv.apply_symm_apply p

@[simp] def symm_apply_apply (p : I × U) : ϕ.symm (ϕ p) = p :=
ϕ.to_equiv.symm_apply_apply p

lemma commutes (p : I × U) : f (ϕ p) = p.2 :=
ϕ.commutes' p

lemma commutes_inv (p : f ⁻¹' U) : f p = (ϕ.symm p).2 :=
by rw [←ϕ.apply_symm_apply p, ϕ.commutes, ϕ.apply_symm_apply]

def mono (h : V ⊆ U) : evenly_covered_set f I V :=
{ to_fun := λ p, ⟨ϕ ⟨p.1, p.2, h p.2.2⟩, by rw [set.mem_preimage, ϕ.commutes]; exact p.2.2⟩,
  inv_fun := λ p, ⟨(ϕ.symm ⟨p, h p.2⟩).1,
    ⟨(ϕ.symm ⟨p, h p.2⟩).2, by rw [←ϕ.commutes, apply_symm_apply]; exact p.2⟩⟩,
  left_inv := λ p, by simp only [subtype.coe_mk, subtype.coe_eta, prod.mk.eta, symm_apply_apply],
  right_inv := λ p, by simp only [subtype.coe_mk, subtype.coe_eta, prod.mk.eta, apply_symm_apply],
  commutes' := λ p, ϕ.commutes ⟨p.1, p.2, h p.2.2⟩,
  continuous_to_fun := by continuity! }

def fiber_homeomorph (hx : x ∈ U) : f ⁻¹' {x} ≃ₜ I :=
{ to_fun := λ p, (ϕ.symm ⟨p, (congr_arg (∈ U) p.2).mpr hx⟩).1,
  inv_fun := λ p, ⟨ϕ ⟨p, x, hx⟩, ϕ.commutes ⟨p, x, hx⟩⟩,
  left_inv := λ p, subtype.ext (by
  { obtain ⟨p, rfl : f p = x⟩ := p,
    have := ϕ.commutes_inv ⟨p, _⟩,
    rw subtype.coe_mk at this,
    simp only [this, subtype.coe_mk, subtype.coe_eta, prod.mk.eta, apply_symm_apply],
    exact hx }),
  right_inv := λ p, by simp only [subtype.coe_mk, subtype.coe_eta, symm_apply_apply],
  continuous_inv_fun := by continuity! }

def translate (hx : x ∈ U) : evenly_covered_set f (f ⁻¹' {x}) U :=
{ to_homeomorph := ((ϕ.fiber_homeomorph hx).prod_congr (homeomorph.refl U)).trans ϕ.to_homeomorph,
  commutes' := λ p, ϕ.commutes ⟨ϕ.fiber_homeomorph hx p.1, p.2⟩ }

end evenly_covered_set

variables (f)

structure evenly_covered_pt (hx : x ∈ U) extends evenly_covered_set f (f ⁻¹' {x}) U :=
(rigid' : ∀ p : f ⁻¹' {x}, to_fun ⟨p, x, hx⟩ = ⟨p, (congr_arg (∈ U) p.2).mpr hx⟩)

variables {f}

namespace evenly_covered_pt

variables {hx : x ∈ U} (ϕ : evenly_covered_pt f hx)

instance : has_coe_to_fun (evenly_covered_pt f hx) (λ ι, f ⁻¹' {x} × U → f ⁻¹' U) :=
⟨λ ϕ, ϕ.to_fun⟩

def symm : f ⁻¹' U ≃ₜ f ⁻¹' {x} × U :=
ϕ.to_evenly_covered_set.symm

@[simp] def apply_symm_apply (p : f ⁻¹' U) : ϕ (ϕ.symm p) = p :=
ϕ.to_evenly_covered_set.apply_symm_apply p

@[simp] def symm_apply_apply (p : f ⁻¹' {x} × U) : ϕ.symm (ϕ p) = p :=
ϕ.to_evenly_covered_set.symm_apply_apply p

lemma commutes (p : f ⁻¹' {x} × U) : f (ϕ p) = p.2 :=
ϕ.to_evenly_covered_set.commutes p

lemma commutes_inv (p : f ⁻¹' U) : f p = (ϕ.symm p).2 :=
ϕ.to_evenly_covered_set.commutes_inv p

lemma rigid (p : f ⁻¹' {x}) : ϕ ⟨p, x, hx⟩ = ⟨p, (congr_arg (∈ U) p.2).mpr hx⟩ :=
ϕ.rigid' p

def mono {hx' : x ∈ V} (h : V ⊆ U) : evenly_covered_pt f hx' :=
{ rigid' := λ p, subtype.ext (show _, from subtype.ext_iff.mp (ϕ.rigid p)),
  .. ϕ.to_evenly_covered_set.mono h }

def translate (hy : y ∈ U) : evenly_covered_pt f hy :=
{ rigid' := λ p, sorry,
  .. ϕ.to_evenly_covered_set.translate hy }

end evenly_covered_pt

variables (f)

def evenly_covered (hx : x ∈ U) : Prop :=
nonempty (evenly_covered_pt f hx)

variables {f}

namespace evenly_covered

lemma mono {hx : x ∈ V} {hy : x ∈ U} (hf : evenly_covered f hy) (h : V ⊆ U) :
  evenly_covered f hx :=
hf.elim (λ g, ⟨g.mono h⟩)

lemma translate {hx : x ∈ U} (hf : evenly_covered f hx) (hy : y ∈ U) : evenly_covered f hy :=
hf.elim (λ g, ⟨g.translate hy⟩)

end evenly_covered

lemma evenly_covered_translate_iff (hx : x ∈ U) (hy : y ∈ U) :
  evenly_covered f hx ↔ evenly_covered f hy :=
⟨λ hf, hf.translate hy, λ hf, hf.translate hx⟩

variables (E X)

structure covering_map extends continuous_map E X :=
(surjective : function.surjective to_fun)
(discrete_fibers : ∀ x, discrete_topology (to_fun ⁻¹' {x}))
(evenly_covered : ∀ x, ∃ U, is_open U ∧ ∃ hU : x ∈ U, evenly_covered to_fun hU)

variables {E X}

namespace covering_map

infixr ` ↠ `:25 := covering_map -- shortcut: type `\rr-` or just type `\rr `

instance : has_coe_to_fun (E ↠ X) (λ _, E → X) := ⟨λ q, q.to_fun⟩

lemma continuous (q : E ↠ X) : continuous q := q.continuous_to_fun

lemma is_locally_homeomorph (q : E ↠ X) : is_locally_homeomorph q :=
begin
  classical,
  intro x,
  obtain ⟨U, hU, hx, ⟨ϕ⟩⟩ := q.evenly_covered (q x),
  let ψ : U → E := λ p, ϕ ⟨⟨x, rfl⟩, p⟩,
  have hψ : ∀ p : U, q (ψ p) = p := λ p, ϕ.commutes ⟨⟨x, rfl⟩, p⟩,
  refine ⟨{ to_fun := q,
  inv_fun := λ p, if hp : p ∈ U then ψ ⟨p, hp⟩ else x,
  source := set.range ψ,
  target := U,
  open_source := sorry,
  open_target := hU,
  map_source' := λ _ ⟨⟨p, _⟩, hp⟩, by rwa [←hp, hψ],
  map_target' := λ p hp, ⟨⟨p, hp⟩, by rw [dif_pos hp]⟩,
  left_inv' := λ _ ⟨p, hp⟩, by rw [←hp, hψ, dif_pos p.prop, subtype.coe_eta],
  right_inv' := λ p hp, by rw [dif_pos hp, hψ, subtype.coe_mk],
  continuous_to_fun := q.continuous.continuous_on,
  continuous_inv_fun := sorry }, ⟨⟨q x, hx⟩, subtype.ext_iff.mp (ϕ.rigid ⟨x, rfl⟩)⟩, rfl⟩,
end

lemma is_open_map (q : E ↠ X) : is_open_map q :=
q.is_locally_homeomorph.is_open_map

lemma covering_map_quotient_map (q : E ↠ X) : quotient_map q :=
q.is_open_map.to_quotient_map q.continuous q.surjective

end covering_map

-- *** FUNDAMENTAL GROUP *** --

-- def fundamental_group (x : X) :=
-- let y : fundamental_groupoid X := x in y ⟶ y

-- noncomputable instance (x : X) : group (fundamental_group x) :=
-- { mul := category_theory.category_struct.comp,
--   mul_assoc := category_theory.category.assoc,
--   one := category_theory.category_struct.id _,
--   one_mul := category_theory.category.id_comp,
--   mul_one := category_theory.category.comp_id,
--   inv := category_theory.groupoid.inv,
--   mul_left_inv := category_theory.groupoid.inv_comp }
