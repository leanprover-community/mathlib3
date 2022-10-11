import data.zmod.basic
import group_theory.perm.sign
import tactic.derive_fintype

-- move this
instance fintype.decidable_exists_unique_fintype {α : Type*} {p : α → Prop}
  [decidable_eq α] [decidable_pred p] [fintype α] :
  decidable (∃! a, p a) :=
fintype.decidable_exists_fintype

-- move this
/-- `fintype.equiv_of_bij` is the computable equiv of a bijection `f` of fintypes. This acts
  as a computable alternative to `equiv.of_bijective.`. -/
def fintype.equiv_of_bij {α β : Type*} [fintype α] [decidable_eq β] (f : α → β)
  (f_bij : function.bijective f) : α ≃ β :=
{ to_fun := f,
  inv_fun := fintype.bij_inv f_bij,
  left_inv := fintype.left_inverse_bij_inv f_bij,
  right_inv := fintype.right_inverse_bij_inv f_bij, }

namespace icosahedron

/-- The 12 vertices of the icosahedron. -/
@[derive [fintype, decidable_eq]]
structure vert :=
(a : zmod 3)
(e₁ : zmod 2)
(eₚ : zmod 2)

/-- The 30 edges of the icosahedron. -/
@[derive [fintype, decidable_eq]]
inductive edge : Type
| a : zmod 3 → zmod 2 → edge -- 3 . 2 = 6
| b : zmod 3 → zmod 2 → edge -- 3 . 2 = 6
| c : zmod 3 → zmod 2 → edge -- 3 . 2 = 6
| d : zmod 3 → zmod 2 → edge -- 3 . 2 = 6
| e : zmod 3 → zmod 2 → edge -- 3 . 2 = 6

/-- The 20 faces of the icosahedron. -/
@[derive [fintype, decidable_eq]]
inductive face : Type
| w : zmod 2 → face -- 2
| x : zmod 3 → zmod 2 → face -- 3 . 2 = 6
| y : zmod 3 → zmod 2 → face -- 3 . 2 = 6
| z : zmod 3 → zmod 2 → face -- 3 . 2 = 6

/-- The two vertices bounding each edge of the icosahedron. -/
def edge.to_vert : edge → finset vert
| (edge.a i u) := {⟨i, 0, u⟩, ⟨i, 1, u⟩}
| (edge.d i u) := {⟨i, u, u⟩, ⟨i + 1, u, u⟩}
| (edge.b i u) := {⟨i, u, u⟩, ⟨i + 1, u, 1 + u⟩}
| (edge.c i u) := {⟨i, 1 + u, u⟩, ⟨i + 1, u, u⟩}
| (edge.e i u) := {⟨i, u, 1 + u⟩, ⟨i + 1, 1 + u, u⟩}

/-- The three edges bounding each face of the icosahedron. -/
def face.to_edge : face → finset edge
| (face.w u) := {edge.d 0 u, edge.d 1 u, edge.d 2 u}
| (face.x i u) := {edge.b i u, edge.c (i + 2) u, edge.e (i + 1) u}
| (face.y i u) := {edge.d (i + 2) u, edge.a (i + 2) u, edge.c (i + 2) u}
| (face.z i u) := {edge.a i u, edge.b i u, edge.e i (1 + u)}

-- /- Every vertex touches five edges. -/
-- example {v : vert} : finset.card (finset.filter (λ e : edge, v ∈ e.to_vert) finset.univ) = 5 :=
-- -- sorry
-- by dec_trivial!

-- /- Every edge touches two faces. -/
-- example {e : edge} : finset.card (finset.filter (λ f : face, e ∈ f.to_edge) finset.univ) = 2 :=
-- -- sorry
-- by dec_trivial!

-- /- For each (vertex, face) pair, either they don't touch, or there are exactly two edges which bound
-- the face and which are bounded by the vertex. -/
-- example {v : vert} {f : face} :
--   finset.card (finset.filter (λ e : edge, v ∈ e.to_vert ∧ e ∈ f.to_edge) finset.univ)
--   ∈ ({0, 2} : finset ℕ) :=
-- -- sorry
-- by dec_trivial!

section

meta def tactic.dec_trivial : tactic unit := `[dec_trivial!]

def mk_edges (p : equiv.perm vert)
  (h₁ : ∀ e : edge, ∃! e' : edge, e'.to_vert = e.to_vert.image p . tactic.dec_trivial)
  (h₂ : function.bijective (λ e, fintype.choose _ (h₁ e)) . tactic.dec_trivial) :
  equiv.perm edge :=
fintype.equiv_of_bij _ h₂

lemma mk_edges_apply (p : equiv.perm vert)
  (h₁ : ∀ e : edge, ∃! e' : edge, e'.to_vert = e.to_vert.image p)
  (h₂ : function.bijective (λ e, fintype.choose _ (h₁ e)))
  (e : edge) :
  (mk_edges p h₁ h₂ e).to_vert = finset.image p e.to_vert :=
fintype.choose_spec (λ e' : edge, e'.to_vert = e.to_vert.image p) _

def mk_faces (p : equiv.perm edge)
  (h₁ : ∀ f : face, ∃! f' : face, f'.to_edge = f.to_edge.image p . tactic.dec_trivial)
  (h₂ : function.bijective (λ f, fintype.choose _ (h₁ f)) . tactic.dec_trivial) :
  equiv.perm face :=
fintype.equiv_of_bij _ h₂

def mk_faces_apply (p : equiv.perm edge)
  (h₁ : ∀ f : face, ∃! f' : face, f'.to_edge = f.to_edge.image p . tactic.dec_trivial)
  (h₂ : function.bijective (λ f, fintype.choose _ (h₁ f)) . tactic.dec_trivial)
  (f : face) :
  (mk_faces p h₁ h₂ f).to_edge = finset.image p f.to_edge :=
fintype.choose_spec (λ f' : face, f'.to_edge = f.to_edge.image p) _

end

section P

def P_vert : equiv.perm vert :=
fintype.equiv_of_bij (λ ⟨i, u, u'⟩, ⟨i + 1, u, u'⟩) (by dec_trivial!)

example : P_vert ^ 3 = 1 := by dec_trivial

def P_edge : equiv.perm edge := mk_edges P_vert

@[simp] lemma P_edge_to_vert (e : edge) :
  (P_edge e).to_vert = finset.image P_vert e.to_vert :=
mk_edges_apply _ _ _ _

def P_face : equiv.perm face := mk_faces P_edge

@[simp] lemma P_face_to_edge (f : face) :
  (P_face f).to_edge = finset.image P_edge f.to_edge :=
mk_faces_apply _ _ _ _

def P : equiv.perm vert × equiv.perm edge × equiv.perm face := ⟨P_vert, P_edge, P_face⟩

end P

section Q

/-- A period-5 bijection, composed of two disjoint 5-cycles
⟨2, 1, 0⟩ → ⟨0, 0, 1⟩ → ⟨1, 1, 0⟩ → ⟨1, 0, 0⟩ → ⟨0, 0, 0⟩ →
⟨2, 0, 1⟩ → ⟨0, 1, 0⟩ → ⟨1, 0, 1⟩ → ⟨1, 1, 1⟩ → ⟨0, 1, 1⟩ →
and fixing ⟨2, 0, 0⟩ and ⟨2, 1, 1⟩.
-/
def Q_vert_aux : zmod 3 → zmod 2 → zmod 2 → vert :=
![![![⟨2, 1, 0⟩, ⟨1, 1, 0⟩],  -- images of ⟨0, 0, 0⟩, ⟨0, 0, 1⟩
    ![⟨1, 0, 1⟩, ⟨2, 0, 1⟩]], -- images of ⟨0, 1, 0⟩, ⟨0, 1, 1⟩
  ![![⟨0, 0, 0⟩, ⟨1, 1, 1⟩],  -- images of ⟨1, 0, 0⟩, ⟨1, 0, 1⟩
    ![⟨1, 0, 0⟩, ⟨0, 1, 1⟩]], -- images of ⟨1, 1, 0⟩, ⟨1, 1, 1⟩
  ![![⟨2, 0, 0⟩, ⟨0, 1, 0⟩],  -- images of ⟨2, 0, 0⟩, ⟨2, 0, 1⟩
    ![⟨0, 0, 1⟩, ⟨2, 1, 1⟩]]] -- images of ⟨2, 1, 0⟩, ⟨2, 1, 1⟩

def Q_vert : equiv.perm vert :=
fintype.equiv_of_bij (λ ⟨i, u, u'⟩, Q_vert_aux i u u') (by dec_trivial!)

example : Q_vert ^ 5 = 1 := by dec_trivial!

def Q_edge : equiv.perm edge := mk_edges Q_vert

@[simp] lemma Q_edge_to_vert (e : edge) :
  (Q_edge e).to_vert = finset.image Q_vert e.to_vert :=
mk_edges_apply _ _ _ _

def Q_face : equiv.perm face := mk_faces Q_edge

@[simp] lemma Q_face_to_edge (f : face) :
  (Q_face f).to_edge = finset.image Q_edge f.to_edge :=
mk_faces_apply _ _ _ _

/-- A period-5 automorphism of the icosahedron, acting on the vertex set in two disjoint 5-cycles
⟨2, 1, 0⟩ → ⟨0, 0, 1⟩ → ⟨1, 1, 0⟩ → ⟨1, 0, 0⟩ → ⟨0, 0, 0⟩ →
⟨2, 0, 1⟩ → ⟨0, 1, 0⟩ → ⟨1, 0, 1⟩ → ⟨1, 1, 1⟩ → ⟨0, 1, 1⟩ →
and fixing ⟨2, 0, 0⟩ and ⟨2, 1, 1⟩. -/
def Q : equiv.perm vert × equiv.perm edge × equiv.perm face := ⟨Q_vert, Q_edge, Q_face⟩

end Q

section R

/-- A period-5 bijection, composed of two disjoint 5-cycles
⟨0, 1, 0⟩ → ⟨1, 0, 1⟩ → ⟨2, 1, 0⟩ → ⟨2, 0, 0⟩ → ⟨1, 0, 0⟩ →
⟨0, 0, 1⟩ → ⟨1, 1, 0⟩ → ⟨2, 0, 1⟩ → ⟨2, 1, 1⟩ → ⟨1, 1, 1⟩ →
and fixing ⟨0, 0, 0⟩ and ⟨0, 1, 1⟩.
-/
def R_vert_aux : zmod 3 → zmod 2 → zmod 2 → vert :=
![![![⟨0, 0, 0⟩, ⟨1, 1, 0⟩],  -- images of ⟨0, 0, 0⟩, ⟨0, 0, 1⟩
    ![⟨1, 0, 1⟩, ⟨0, 1, 1⟩]], -- images of ⟨0, 1, 0⟩, ⟨0, 1, 1⟩
  ![![⟨0, 1, 0⟩, ⟨2, 1, 0⟩],  -- images of ⟨1, 0, 0⟩, ⟨1, 0, 1⟩
    ![⟨2, 0, 1⟩, ⟨0, 0, 1⟩]], -- images of ⟨1, 1, 0⟩, ⟨1, 1, 1⟩
  ![![⟨1, 0, 0⟩, ⟨2, 1, 1⟩],  -- images of ⟨2, 0, 0⟩, ⟨2, 0, 1⟩
    ![⟨2, 0, 0⟩, ⟨1, 1, 1⟩]]] -- images of ⟨2, 1, 0⟩, ⟨2, 1, 1⟩

def R_vert : equiv.perm vert :=
fintype.equiv_of_bij (λ ⟨i, u, u'⟩, R_vert_aux i u u') (by dec_trivial!)

example : R_vert ^ 5 = 1 := by dec_trivial!

example : R_vert * Q_vert * P_vert = 1 := by dec_trivial!

def R_edge : equiv.perm edge := mk_edges R_vert

@[simp] lemma R_edge_to_vert (e : edge) :
  (R_edge e).to_vert = finset.image R_vert e.to_vert :=
mk_edges_apply _ _ _ _

def R_face : equiv.perm face := mk_faces R_edge

@[simp] lemma R_face_to_edge (f : face) :
  (R_face f).to_edge = finset.image R_edge f.to_edge :=
mk_faces_apply _ _ _ _

/-- A period-5 automorphism of the icosahedron, acting on the vertex set in two disjoint 5-cycles
⟨0, 1, 0⟩ → ⟨1, 0, 1⟩ → ⟨2, 1, 0⟩ → ⟨2, 0, 0⟩ → ⟨1, 0, 0⟩
⟨0, 0, 1⟩ → ⟨1, 1, 0⟩ → ⟨2, 0, 1⟩ → ⟨2, 1, 1⟩ → ⟨1, 1, 1⟩
and fixing ⟨0, 0, 0⟩ and ⟨0, 1, 1⟩. -/
def R : equiv.perm vert × equiv.perm edge × equiv.perm face := ⟨R_vert, R_edge, R_face⟩

end R

section aut

def aut_aux1 : subgroup (equiv.perm vert × equiv.perm edge × equiv.perm face) :=
{ carrier := λ p, ∀ e, (p.2.1 e).to_vert = e.to_vert.image p.1,
  mul_mem' := λ p p' hp hp' e, begin
    calc _ = _ : hp (p'.2.1 e)
    ... = _ : by rw hp' e
    ... = _ : finset.image_image,
  end,
  one_mem' := λ e, finset.image_id.symm,
  inv_mem' := λ p hp e, begin
    let q₀ : equiv.perm vert := p.1⁻¹,
    let q₁ : equiv.perm edge := p.2.1⁻¹,
    calc (q₁ e).to_vert
        = (q₁ e).to_vert.image id : finset.image_id.symm
    ... = (q₁ e).to_vert.image (q₀ ∘ p.1) : by congr; exact p.1.symm_comp_self.symm
    ... = ((q₁ e).to_vert.image p.1).image q₀ : by rw finset.image_image
    ... = (p.2.1 (q₁ e)).to_vert.image q₀ : by rw hp (q₁ e)
    ... = e.to_vert.image q₀ : by congr; exact p.2.1.right_inv e,
  end }

def aut_aux2 : subgroup (equiv.perm vert × equiv.perm edge × equiv.perm face) :=
{ carrier := λ p, ∀ f, (p.2.2 f).to_edge = f.to_edge.image p.2.1,
  mul_mem' := λ p p' hp hp' f, begin
    calc _ = _ : hp (p'.2.2 f)
    ... = _ : by rw hp' f
    ... = _ : finset.image_image,
  end,
  one_mem' := λ f, finset.image_id.symm,
  inv_mem' := λ p hp f, begin
    let q₁ : equiv.perm edge := p.2.1⁻¹,
    let q₂ : equiv.perm face := p.2.2⁻¹,
    -- have : ((q₂ f).to_edge.image p.2.1).image q₁ = (p.2.2 (q₂ f)).to_edge.image q₁ := by rw hp (q₂ f),
    -- simp [q₁, q₂, finset.image_image] at this ⊢,
    -- have : (q₂ f).to_edge.image ⇑(q₁ * p.2.1) = (q₂ f).to_edge,
    -- simp_rw equiv.perm.coe_mul at this,
    -- simp [q₁, q₂] at this,
    -- have := p.2.2.inv_apply_self,
    calc (q₂ f).to_edge
        = (q₂ f).to_edge.image id : finset.image_id.symm
    ... = (q₂ f).to_edge.image (q₁ ∘ p.2.1) : by congr; exact p.2.1.symm_comp_self.symm
    ... = ((q₂ f).to_edge.image p.2.1).image q₁ : by rw finset.image_image
    ... = (p.2.2 (q₂ f)).to_edge.image q₁ : by rw hp (q₂ f)
    ... = f.to_edge.image q₁ : by congr; exact p.2.2.right_inv f,
  end }

def aut_aux3 : subgroup (equiv.perm vert × equiv.perm edge × equiv.perm face) :=
monoid_hom.ker $ (equiv.perm.sign.comp (monoid_hom.fst _ _))

instance foo (x : equiv.perm vert × equiv.perm edge × equiv.perm face) :
  decidable (x ∈ aut_aux3.to_submonoid) :=
begin
  change decidable (equiv.perm.sign x.1 = 1),
  apply_instance,
end

def aut : subgroup (equiv.perm vert × equiv.perm edge × equiv.perm face) :=
aut_aux1 ⊓ aut_aux2 ⊓ aut_aux3

-- lemma P_image : P ∈ aut := ⟨⟨P_edge_to_vert, P_face_to_edge⟩, by dec_trivial!⟩

-- #check foo
-- example : fintype aut := fintype.of_finite ↥aut
def aut_finset : finset (equiv.perm vert × equiv.perm edge × equiv.perm face) :=
begin
  haveI : decidable_pred (∈ aut),
  { intros g,
    change decidable (((∀ e, (g.2.1 e).to_vert = _) ∧ (∀ f : face, (g.2.2 f).to_edge = _))
      ∧ equiv.perm.sign g.1 = 1),
    apply_instance },
  exact finset.filter (λ g, g ∈ aut) finset.univ,
end

-- example : finset.card aut_finset = 60 := by dec_trivial!

end aut

end icosahedron

-- /-- The three vertices touching each face of the icosahedron. -/
-- def face.to_vert : face → finset vert
-- | (face.w u) := {⟨0, u, u⟩, ⟨1, u, u⟩, ⟨2, u, u⟩}
-- | (face.x i u) := {⟨i, u, u⟩, ⟨i + 1, u, m * u⟩, ⟨i + 2, m * u, u⟩}
-- | (face.y i u) := {⟨i, u, u⟩, ⟨i + 2, u, u⟩, ⟨i + 2, m * u, u⟩}
-- | (face.z i u) := {⟨i, u, u⟩, ⟨i, m * u, u⟩, ⟨i + 1, u, m * u⟩}

-- /-- The two faces which each edge of the icosahedron bounds. -/
-- def edge.to_face : edge → finset face
-- | (edge.a i u) := {face.y (i + 1) u, face.z i u}
-- | (edge.d i u) := {face.w u, face.y (i + 1) u}
-- | (edge.b i u) := {face.x i u, face.z i u}
-- | (edge.c i u) := {face.x (i + 1) u, face.y (i + 1) u}
-- | (edge.e i u) := {face.x (i + 2) u, face.z i (m * u)}
-- /- Every vertex touches five faces. -/
-- example {v : vert} :
--   finset.card (finset.filter (λ f : face, ∃ e : edge, v ∈ e.to_vert ∧ e ∈ f.to_edge) finset.univ) = 5 :=
-- sorry

-- /- Every vertex touches five faces. -/
-- example {v : vert} : finset.card (finset.filter (λ f : face, v ∈ f.to_vert) finset.univ) = 5 :=
-- sorry
-- --by dec_trivial!

-- /- Every vertex touching a face bounds exactly two edges which bound that face. -/
-- example {v : vert} {f : face} (h : v ∈ f.to_vert) :
--   finset.card (finset.filter (λ e : edge, v ∈ e.to_vert ∧ e ∈ f.to_edge) finset.univ) = 2 :=
-- -- sorry
-- by dec_trivial!


-- /- The specified edge-to-face and face-to-edge pairings indeed give the same definition. -/
-- example {f : face} {e : edge} : f ∈ e.to_face ↔ e ∈ f.to_edge :=
-- sorry
--by dec_trivial!

-- example {f : face} {v : vert} : v ∈ f.to_vert ↔ ∃ e : edge, e ∈ f.to_edge ∧ v ∈ e.to_vert :=
-- by dec_trivial!
