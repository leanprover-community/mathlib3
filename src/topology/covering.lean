import topology.is_locally_homeomorph

variables {E X : Type*} [topological_space E] [topological_space X] (f : E → X) {x y : X}
  (U V : set X) (I : Type*) [topological_space I]

structure even_covering extends homeomorph (U × I) (f ⁻¹' U) :=
(commutes' : ∀ p, f (to_fun p) = p.1)

variables {f U V I} (ϕ : even_covering f U I)

namespace even_covering

instance : has_coe_to_fun (even_covering f U I) (λ ι, U × I → f ⁻¹' U) :=
⟨λ ϕ, ϕ.to_fun⟩

def symm : f ⁻¹' U ≃ₜ U × I :=
ϕ.to_homeomorph.symm

@[simp] def apply_symm_apply (p : f ⁻¹' U) : ϕ (ϕ.symm p) = p :=
ϕ.to_equiv.apply_symm_apply p

@[simp] def symm_apply_apply (p : U × I) : ϕ.symm (ϕ p) = p :=
ϕ.to_equiv.symm_apply_apply p

lemma commutes (p : U × I) : f (ϕ p) = p.1 :=
ϕ.commutes' p

lemma commutes_inv (p : f ⁻¹' U) : f p = (ϕ.symm p).1 :=
by rw [←ϕ.apply_symm_apply p, ϕ.commutes, ϕ.apply_symm_apply]

def mono (h : V ⊆ U) : even_covering f V I :=
{ to_fun := λ p, ⟨ϕ ⟨⟨p.1, h p.1.2⟩, p.2⟩, by rw [set.mem_preimage, ϕ.commutes]; exact p.1.2⟩,
  inv_fun := λ p, ⟨⟨(ϕ.symm ⟨p, h p.2⟩).1, by rw [←ϕ.commutes, apply_symm_apply]; exact p.2⟩,
    (ϕ.symm ⟨p, h p.2⟩).2⟩,
  left_inv := λ p, by simp only [subtype.coe_mk, subtype.coe_eta, prod.mk.eta, symm_apply_apply],
  right_inv := λ p, by simp only [subtype.coe_mk, subtype.coe_eta, prod.mk.eta, apply_symm_apply],
  commutes' := λ p, ϕ.commutes ⟨⟨p.1, h p.1.2⟩, p.2⟩,
  continuous_to_fun := by continuity! }

def fiber_homeomorph (hx : x ∈ U) : f ⁻¹' {x} ≃ₜ I :=
{ to_fun := λ p, (ϕ.symm ⟨p, (congr_arg (∈ U) p.2).mpr hx⟩).2,
  inv_fun := λ p, ⟨ϕ ⟨⟨x, hx⟩, p⟩, ϕ.commutes ⟨⟨x, hx⟩, p⟩⟩,
  left_inv := λ p, subtype.ext (by
  { obtain ⟨p, rfl : f p = x⟩ := p,
    have := ϕ.commutes_inv ⟨p, _⟩,
    rw subtype.coe_mk at this,
    simp only [this, subtype.coe_mk, subtype.coe_eta, prod.mk.eta, apply_symm_apply],
    exact hx }),
  right_inv := λ p, by simp only [subtype.coe_mk, subtype.coe_eta, symm_apply_apply],
  continuous_inv_fun := by continuity! }

def translate (ϕ : even_covering f U I) (hx : x ∈ U) : even_covering f U (f ⁻¹' {x}) :=
{ to_homeomorph := ((homeomorph.refl U).prod_congr (ϕ.fiber_homeomorph hx)).trans ϕ.to_homeomorph,
  commutes' := λ p, ϕ.commutes ⟨p.1, ϕ.fiber_homeomorph hx p.2⟩ }

end even_covering

variables (f)

def evenly_covered (hx : x ∈ U) : Prop :=
nonempty (even_covering f U (f ⁻¹' {x}))

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
(discrete_fibers : ∀ x : X, discrete_topology (to_fun ⁻¹' {x}))
(evenly_covered : ∀ x : X, ∃ (U : set X) (hU : U ∈ nhds x),
  evenly_covered to_fun (mem_of_mem_nhds hU))

variables {E X}

namespace covering_map

infixr ` ↠ `:25 := covering_map -- shortcut: type `\rr-` or just type `\rr `

instance : has_coe_to_fun (E ↠ X) (λ _, E → X) := ⟨λ q, q.to_fun⟩

@[continuity] lemma continuous (q : E ↠ X) : continuous q := q.continuous_to_fun

lemma is_locally_homeomorph (q : E ↠ X) : is_locally_homeomorph q :=
begin
  apply is_locally_homeomorph.mk,
  intro x,
  obtain ⟨U, hU, ⟨ϕ⟩⟩ := q.evenly_covered (q x),
  sorry,
end

lemma is_open_map (q : E ↠ X) : is_open_map q :=
q.is_locally_homeomorph.is_open_map

lemma covering_map_quotient_map (q : E ↠ X) : quotient_map q :=
q.is_open_map.to_quotient_map q.continuous q.surjective

end covering_map

/-- *** FUNDAMENTAL GROUP *** -/

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
