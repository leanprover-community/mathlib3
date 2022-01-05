/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.additive
import tactic.abel

/-!
# Chain homotopies

We define chain homotopies, and prove that homotopic chain maps induce the same map on homology.
-/

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

section 

/-- The subset of ι × ι consisting of those (i,j) such that c.rel j i) -/
def homotopy.set_of_cs (c : complex_shape ι) : set (ι × ι) := λ (x : ι × ι), c.rel x.2 x.1

/-- A prehomotopy C D consists of morphisms C.X i ⟶ C.X j when c.rel j i -/
abbreviation prehomotopy (C D : homological_complex V c) :=
Π (ij : homotopy.set_of_cs c), C.X ij.val.1 ⟶ D.X ij.val.2

namespace homotopy

/-- The composition of `C.d i i' ≫ f ⟨⟨i',i⟩,_⟩` if there is some `i'` coming after `i`,
and `0` otherwise. -/
def d_next (i : ι) : prehomotopy C D →+ (C.X i ⟶ D.X i) :=
add_monoid_hom.mk' (λ f, match c.next i with
| none := 0
| some ⟨i',w⟩ := C.d i i' ≫ f ⟨⟨i',i⟩,w⟩
end)
begin
  intros f g,
  rcases c.next i with _|⟨i',w⟩,
  exact (zero_add _).symm,
  exact preadditive.comp_add _ _ _ _ _ _,
end

/-- `f ⟨⟨i',i⟩,_⟩` if `i'` comes after `i`, and 0 if there's no such `i'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def from_next [has_zero_object V] (i : ι) : prehomotopy C D →+ (C.X_next i ⟶ D.X i) :=
add_monoid_hom.mk' (λ f, match c.next i with
| none := 0
| some ⟨i',w⟩ := (C.X_next_iso w).hom ≫ f ⟨⟨i',i⟩,w⟩
end)
begin
  intros f g,
  rcases c.next i with _|⟨i',w⟩,
  exact (zero_add _).symm,
  exact preadditive.comp_add _ _ _ _ _ _,
end

lemma d_next_eq_d_from_from_next [has_zero_object V] (f : prehomotopy C D) (i : ι) :
  d_next i f = C.d_from i ≫ from_next i f :=
begin
  dsimp [d_next, from_next],
  rcases c.next i with ⟨⟩|⟨⟨i', w⟩⟩;
  { dsimp [d_next, from_next], simp },
end

lemma d_next_eq (f : prehomotopy C D) {i i' : ι} (w : c.rel i i') :
  d_next i f = C.d i i' ≫ f ⟨⟨i',i⟩,w⟩ :=
begin
  dsimp [d_next],
  rw c.next_eq_some w,
  refl,
end

@[simp] lemma d_next_comp_left (f : C ⟶ D) (g : prehomotopy D E) (i : ι) :
  d_next i (λ ij, f.f ij.val.1 ≫ g ij) = f.f i ≫ d_next i g :=
begin
  dsimp [d_next],
  rcases c.next i with _|⟨i',w⟩,
  { exact comp_zero.symm, },
  { dsimp [d_next],
    simp, },
end

@[simp] lemma d_next_comp_right (f : prehomotopy C D) (g : D ⟶ E) (i : ι) :
  d_next i (λ ij, f ij ≫ g.f ij.val.2) = d_next i f ≫ g.f i :=
begin
  dsimp [d_next],
  rcases c.next i with _|⟨i',w⟩,
  { exact zero_comp.symm, },
  { dsimp [d_next],
    simp, },
end

/-- The composition of `f ⟨⟨j,j'⟩,_⟩ ≫ D.d j' j` if there is some `j'` coming before `j`,
and `0` otherwise. -/
def prev_d (j : ι) : prehomotopy C D →+ (C.X j ⟶ D.X j) :=
add_monoid_hom.mk' (λ f, match c.prev j with
| none := 0
| some ⟨j',w⟩ := f ⟨⟨j,j'⟩,w⟩ ≫ D.d j' j
end)
begin
  intros f g,
  rcases c.prev j with _|⟨j',w⟩,
  exact (zero_add _).symm,
  exact preadditive.add_comp _ _ _ _ _ _,
end

/-- `f ⟨⟨j,j⟩,_⟩'` if `j'` comes after `j`, and 0 if there's no such `j'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def to_prev [has_zero_object V] (j : ι) : prehomotopy C D →+ (C.X j ⟶ D.X_prev j) :=
add_monoid_hom.mk' (λ f, match c.prev j with
| none := 0
| some ⟨j',w⟩ := f ⟨⟨j,j'⟩,w⟩ ≫ (D.X_prev_iso w).inv
end)
begin
  intros f g,
  rcases c.prev j with _|⟨j',w⟩,
  exact (zero_add _).symm,
  exact preadditive.add_comp _ _ _ _ _ _,
end

lemma prev_d_eq_to_prev_d_to [has_zero_object V] (f : prehomotopy C D) (j : ι) :
  prev_d j f = to_prev j f ≫ D.d_to j :=
begin
  dsimp [prev_d, to_prev],
  rcases c.prev j with ⟨⟩|⟨⟨j', w⟩⟩;
  { dsimp [prev_d, to_prev], simp },
end

lemma prev_d_eq (f : prehomotopy C D) {j j' : ι} (w : c.rel j' j) :
  prev_d j f = f ⟨⟨j,j'⟩,w⟩ ≫ D.d j' j :=
begin
  dsimp [prev_d],
  rw c.prev_eq_some w,
  refl,
end

@[simp] lemma prev_d_comp_left (f : C ⟶ D) (g : prehomotopy D E) (j : ι) :
  prev_d j (λ ij, f.f ij.val.1 ≫ g ij) = f.f j ≫ prev_d j g :=
begin
  dsimp [prev_d],
  rcases c.prev j with _|⟨j',w⟩,
  { exact comp_zero.symm, },
  { dsimp [prev_d, hom.prev],
    simp, },
end

@[simp] lemma to_prev'_comp_right (f : prehomotopy C D) (g : D ⟶ E) (j : ι) :
  prev_d j (λ ij, f ij ≫ g.f ij.val.2) = prev_d j f ≫ g.f j :=
begin
  dsimp [prev_d],
  rcases c.prev j with _|⟨j',w⟩,
  { exact zero_comp.symm, },
  { dsimp [prev_d],
    simp, },
end

/-!
Null homotopic maps can be constructed using the formula `hd+dh`. We provide some
convenient simplification lemmas that give a degreewise description of `hd+dh`,
depending on whether we have two differentials going to and from a certain degree,
only one, or none.
-/

/-- The null homotopic map associated to a family `hom` of morphisms `C_i ⟶ D_j`
when `c.rel j i`. This is the same datum as for the field `hom` in the structure
`homotopy`. -/
def null_homotopic_map (hom : prehomotopy C D) : C ⟶ D :=
{ f      := λ i, d_next i hom + prev_d i hom,
  comm'  := λ i j hij,
  begin
    have eq1 : prev_d i hom ≫ D.d i j = 0,
    { rcases h : c.prev i with _|⟨i',w⟩,
      { dsimp [prev_d], rw h, erw zero_comp, },
      { rw [prev_d_eq hom w, category.assoc, D.d_comp_d' i' i j w hij, comp_zero], }, },
    have eq2 : C.d i j ≫ d_next j hom = 0,
    { rcases h : c.next j with _|⟨j',w⟩,
      { dsimp [d_next], rw h, erw comp_zero, },
      { rw [d_next_eq hom w, ← category.assoc, C.d_comp_d' i j j' hij w, zero_comp], }, },
    rw [d_next_eq hom hij, prev_d_eq hom hij, preadditive.comp_add, preadditive.add_comp,
      eq1, eq2, add_zero, zero_add, category.assoc], 
  end }

/-- make `null_homotopic_map` into an additive map of monoids -/
def add_monoid_hom_null_homotopic_map : prehomotopy C D →+ (C ⟶ D) :=
add_monoid_hom.mk' null_homotopic_map
begin
  intros hom₁ hom₂,
  unfold null_homotopic_map,
  ext,
  dsimp,
  simp only [map_add, add_f_apply],
  abel, 
end

/-- Use this lemma when you need the additivity of `null_homotopic_map` -/
lemma additive_null_homotopic_map (hom : prehomotopy C D) :
   null_homotopic_map hom = add_monoid_hom_null_homotopic_map hom :=
by { dsimp [add_monoid_hom_null_homotopic_map], refl, }

/-- null homotopies can be postcomposed with a morphism of complexes,
and the corresponding null homotopic maps are computed by `null_homotopic_map_comp` -/
@[simp]
def prehomotopy_comp (hom : prehomotopy C D) (g : D ⟶ E) : prehomotopy C E :=
λ ij, hom ij ≫ g.f ij.val.2 

/-- null homotopies can be precomposed with a morphism of complexes,
and the corresponding null homotopic maps are computed by `comp_null_homotopic_map` -/
@[simp]
def comp_prehomotopy (g : C ⟶ D) (hom : prehomotopy D E) : prehomotopy C E :=
λ ij, g.f ij.val.1 ≫ hom ij

@[simp]
lemma null_homotopic_map_comp (hom : prehomotopy C D) (g : D ⟶ E) :
  null_homotopic_map hom ≫ g = null_homotopic_map (prehomotopy_comp hom g) :=
begin
  ext,
  simp only [null_homotopic_map, prehomotopy_comp, d_next_comp_right, preadditive.add_comp,
    to_prev'_comp_right, comp_f],
end

@[simp]
lemma comp_null_homotopic_map (g : C ⟶ D) (hom : prehomotopy D E)  :
   g ≫ null_homotopic_map hom = null_homotopic_map (comp_prehomotopy g hom) :=
begin
  ext,
  simp only [null_homotopic_map, d_next_comp_left, prev_d_comp_left, preadditive.comp_add,
    comp_prehomotopy, comp_f],
end

/-! This lemma and the following ones can be used in order to compute
the degreewise morphisms induced by the null homotopic maps constructed
with `null_homotopic_map` -/
@[simp]
lemma null_homotopic_map_f {k₂ k₁ k₀ : ι} (r₂₁ : c.rel k₂ k₁) (r₁₀ : c.rel k₁ k₀)
  (hom : prehomotopy C D) :
  (null_homotopic_map hom).f k₁ = C.d k₁ k₀ ≫ hom ⟨⟨k₀,k₁⟩,r₁₀⟩ + hom ⟨⟨k₁,k₂⟩,r₂₁⟩ ≫ D.d k₂ k₁ :=
by { dsimp [null_homotopic_map], rw [d_next_eq hom r₁₀, prev_d_eq hom r₂₁], }

@[simp]
lemma null_homotopic_map_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l) (hom : prehomotopy C D) :
  (null_homotopic_map hom).f k₀ = hom ⟨⟨k₀,k₁⟩,r₁₀⟩ ≫ D.d k₁ k₀ :=
begin
  dsimp [null_homotopic_map],
  rw prev_d_eq hom r₁₀,
  rcases h : c.next k₀ with _|⟨l,w⟩, swap, exfalso, exact hk₀ l w,
  dsimp [d_next], rw h, erw zero_add,
end

@[simp]
lemma null_homotopic_map_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₁ : ∀ l : ι, ¬c.rel l k₁)
  (hom : prehomotopy C D) :
  (null_homotopic_map hom).f k₁ = C.d k₁ k₀ ≫ hom ⟨⟨k₀,k₁⟩,r₁₀⟩ :=
begin
  dsimp [null_homotopic_map],
  rw d_next_eq hom r₁₀,
  rcases h : c.prev k₁ with _|⟨l,w⟩, swap, exfalso, exact hk₁ l w,
  dsimp [prev_d], rw h, erw add_zero,
end

@[simp]
lemma null_homotopic_map_f_eq_zero {k₀ : ι} 
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l) (hk₀' : ∀ l : ι, ¬c.rel l k₀)
  (hom : prehomotopy C D) :
  (null_homotopic_map hom).f k₀ = 0 :=
begin
  dsimp [null_homotopic_map],
  rcases h1 : c.next k₀ with _|⟨l,w⟩, swap, exfalso, exact hk₀ l w,
  rcases h2 : c.prev k₀ with _|⟨l,w⟩, swap, exfalso, exact hk₀' l w,
  dsimp [d_next, prev_d],
  rw [h1, h2],
  erw zero_add,
  refl,
end

end homotopy

/--
A homotopy `h` between chain maps `f` and `g` consists of a prehomotopy `hom`
such the difference between `f` and `g` is the `null_homotopic_map`
attached to hom. -/
@[ext, nolint has_inhabited_instance]
structure homotopy (f g : C ⟶ D) :=
(hom : prehomotopy C D)
(comm : f = homotopy.null_homotopic_map hom + g)

variables {f g}
namespace homotopy

lemma comm_ext (e : homotopy f g) (i : ι) :
  f.f i = (null_homotopic_map e.hom).f i + g.f i :=
begin
  have H := congr_arg (λ φ, φ.f i : (C ⟶ D) → (C.X i ⟶ D.X i)) e.comm,
  simp only [add_f_apply] at H,
  exact H,
end

/-- Tautological construction of the `homotopy` to zero for maps constructed by
`null_homotopic_map` -/
@[simps]
def null_homotopy (hom : prehomotopy C D) :
  homotopy (null_homotopic_map hom) 0 :=
{ hom := hom,
  comm := by simp only [add_zero], }

/--
`f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equiv_sub_zero : homotopy f g ≃ homotopy (f - g) 0 :=
{ to_fun := λ h,
  { hom := h.hom,
    comm := by { simpa only [add_zero] using sub_eq_of_eq_add h.comm, }, },
  inv_fun := λ h,
  { hom := h.hom,
    comm := by { simpa only [add_zero] using eq_add_of_sub_eq h.comm, }, },
  left_inv  := by { intro, dsimp, ext, refl, },
  right_inv := by { intro, dsimp, ext, refl, }, }

/-- Equal chain maps are homotopic. -/
@[simps]
def of_eq (h : f = g) : homotopy f g :=
{ hom := 0,
  comm := by { simpa only [additive_null_homotopic_map, zero_add, map_zero], }, }

/-- Every chain map is homotopic to itself. -/
@[simps, refl]
def refl (f : C ⟶ D) : homotopy f f :=
of_eq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps, symm]
def symm {f g : C ⟶ D} (h : homotopy f g) : homotopy g f :=
{ hom := -h.hom,
  comm :=
  begin
    have H := h.comm,
    simp only [additive_null_homotopic_map, map_neg] at H ⊢,
    exact eq_neg_add_of_add_eq (eq.symm H),
  end }

/-- homotopy is a transitive relation. -/
@[simps, trans]
def trans {e f g : C ⟶ D} (h : homotopy e f) (k : homotopy f g) : homotopy e g :=
{ hom := h.hom + k.hom,
  comm :=
  begin
    have H := eq.trans h.comm (congr_arg (has_add.add _) k.comm),
    simpa only [additive_null_homotopic_map, map_add, add_assoc] using H,
  end }

/-- the sum of two homotopies is a homotopy between the sum of the respective morphisms. -/
@[simps]
def add {f₁ g₁ f₂ g₂: C ⟶ D}
  (h₁ : homotopy f₁ g₁) (h₂ : homotopy f₂ g₂) : homotopy (f₁+f₂) (g₁+g₂) :=
{ hom := h₁.hom + h₂.hom,
  comm := 
  begin
    have H1 := h₁.comm,
    have H2 := h₂.comm,
    simp only [additive_null_homotopic_map, map_add] at H1 H2 ⊢,
    simp only [congr (congr_arg has_add.add H1) H2],
    abel,
  end }

/-- the difference of two homotopies is a homotopy between the differences
of the respective morphisms. -/
@[simps]
def sub {f₁ g₁ f₂ g₂: C ⟶ D}
  (h₁ : homotopy f₁ g₁) (h₂ : homotopy f₂ g₂) : homotopy (f₁-f₂) (g₁-g₂) :=
{ hom := h₁.hom - h₂.hom,
  comm := 
  begin
    have H1 := h₁.comm,
    have H2 := h₂.comm,
    simp only [additive_null_homotopic_map, map_sub] at H1 H2 ⊢,
    simp only [congr (congr_arg has_sub.sub H1) H2],
    abel,
  end }

/-- homotopy is closed under composition (on the right) -/
@[simps]
def comp_right {e f : C ⟶ D} (h : homotopy e f) (g : D ⟶ E) : homotopy (e ≫ g) (f ≫ g) :=
{ hom := prehomotopy_comp h.hom g,
  comm :=
  begin
    simp only [← null_homotopic_map_comp, ← preadditive.add_comp],
    congr',
    exact h.comm,
  end}

/-- homotopy is closed under composition (on the left) -/
@[simps]
def comp_left {f g : D ⟶ E} (h : homotopy f g) (e : C ⟶ D) : homotopy (e ≫ f) (e ≫ g) :=
{ hom := comp_prehomotopy e h.hom,
  comm :=
  begin
    simp only [← comp_null_homotopic_map, ← preadditive.comp_add],
    congr',
    exact h.comm,
  end}

/-- homotopy is closed under composition -/
@[simps]
def comp {C₁ C₂ C₃ : homological_complex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
  (h₁ : homotopy f₁ g₁) (h₂ : homotopy f₂ g₂) : homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
(h₁.comp_right _).trans (h₂.comp_left _)

/-- a variant of `homotopy.comp_right` useful for dealing with homotopy equivalences. -/
@[simps]
def comp_right_id {f : C ⟶ C} (h : homotopy f (𝟙 C)) (g : C ⟶ D) : homotopy (f ≫ g) g :=
(h.comp_right g).trans (of_eq $ category.id_comp _)

/-- a variant of `homotopy.comp_left` useful for dealing with homotopy equivalences. -/
@[simps]
def comp_left_id {f : D ⟶ D} (h : homotopy f (𝟙 D)) (g : C ⟶ D) : homotopy (g ≫ f) g :=
(h.comp_left g).trans (of_eq $ category.comp_id _)

/-!
`homotopy.mk_inductive` allows us to build a homotopy inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.

To simplify the situation, we only construct homotopies of the form `homotopy e 0`.
`homotopy.equiv_sub_zero` can provide the general case.

Notice however, that this construction does not have particularly good definitional properties:
we have to insert `eq_to_hom` in several places.
Hopefully this is okay in most applications, where we only need to have the existence of some
homotopy.
-/
section mk_inductive

variables {P Q : chain_complex V ℕ}

lemma cs_down_succ (j : ℕ) : (complex_shape.down ℕ).rel (j+1) j :=
by { have eq : j+1 = j+1 := rfl, assumption, }

lemma cs_down_0_not_rel_left (j : ℕ) : ¬(complex_shape.down ℕ).rel 0 j :=
begin
  intro h,
  dsimp at h,
  apply nat.not_succ_le_zero j,
  rw [show j.succ=j+1, by refl, h],
end

@[simp] lemma prev_d_chain_complex (f : prehomotopy P Q) (j : ℕ) :
  prev_d j f = f ⟨⟨j,j+1⟩,cs_down_succ j⟩ ≫ Q.d _ _ :=
begin
  dsimp [prev_d],
  simp only [chain_complex.prev],
  refl,
end

@[simp] lemma d_next_succ_chain_complex (f : prehomotopy P Q) (i : ℕ) :
  d_next (i+1) f = P.d _ _ ≫ f ⟨⟨i,i+1⟩,cs_down_succ i⟩ :=
begin
  dsimp [d_next],
  simp only [chain_complex.next_nat_succ],
  refl,
end

@[simp] lemma d_next_zero_chain_complex (f : prehomotopy P Q) :
  d_next 0 f = 0 :=
begin
  dsimp [d_next],
  simp only [chain_complex.next_nat_zero],
  refl,
end

variables (e : P ⟶ Q)
  (zero : P.X 0 ⟶ Q.X 1)
  (comm_zero : e.f 0 = zero ≫ Q.d 1 0)
  (one : P.X 1 ⟶ Q.X 2)
  (comm_one : e.f 1 = P.d 1 0 ≫ zero + one ≫ Q.d 2 1)
  (succ : ∀ (n : ℕ)
    (p : Σ' (f : P.X n ⟶ Q.X (n+1)) (f' : P.X (n+1) ⟶ Q.X (n+2)),
      e.f (n+1) = P.d (n+1) n ≫ f + f' ≫ Q.d (n+2) (n+1)),
    Σ' f'' : P.X (n+2) ⟶ Q.X (n+3), e.f (n+2) = P.d (n+2) (n+1) ≫ p.2.1 + f'' ≫ Q.d (n+3) (n+2))

include comm_one comm_zero

/--
An auxiliary construction for `mk_inductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
in `mk_inductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `X_next` and `X_prev`,
which we do in `mk_inductive_aux₂`.
-/
@[simp, nolint unused_arguments]
def mk_inductive_aux₁ :
  Π n, Σ' (f : P.X n ⟶ Q.X (n+1)) (f' : P.X (n+1) ⟶ Q.X (n+2)),
    e.f (n+1) = P.d (n+1) n ≫ f + f' ≫ Q.d (n+2) (n+1)
| 0 := ⟨zero, one, comm_one⟩
| 1 := ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
| (n+2) :=
  ⟨(mk_inductive_aux₁ (n+1)).2.1,
    (succ (n+1) (mk_inductive_aux₁ (n+1))).1,
    (succ (n+1) (mk_inductive_aux₁ (n+1))).2⟩

section

variable [has_zero_object V]
/--
An auxiliary construction for `mk_inductive`.
-/
@[simp]
def mk_inductive_aux₂ :
  Π n, Σ' (f : P.X_next n ⟶ Q.X n) (f' : P.X n ⟶ Q.X_prev n), e.f n = P.d_from n ≫ f + f' ≫ Q.d_to n
| 0 := ⟨0, zero ≫ (Q.X_prev_iso rfl).inv, by simpa using comm_zero⟩
| (n+1) := let I := mk_inductive_aux₁ e zero comm_zero one comm_one succ n in
  ⟨(P.X_next_iso rfl).hom ≫ I.1, I.2.1 ≫ (Q.X_prev_iso rfl).inv, by simpa using I.2.2⟩

lemma mk_inductive_aux₃ (i : ℕ) :
  (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.X_prev_iso rfl).hom
    = (P.X_next_iso rfl).inv ≫ (mk_inductive_aux₂ e zero comm_zero one comm_one succ (i+1)).1 :=
by rcases i with (_|_|i); { dsimp, simp, }

/--
A constructor for a `homotopy e 0`, for `e` a chain map between `ℕ`-indexed chain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
def mk_inductive : homotopy e 0 :=
{ hom := λ ij, (mk_inductive_aux₂ e zero comm_zero one comm_one succ ij.val.1).2.1 ≫
    (Q.X_prev_iso ij.property).hom,
  comm := begin
    ext i,
    dsimp, simp only [add_zero],
    convert (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.2,
    { rcases i with (_|_|_|i),
      { simp only [null_homotopic_map_f_of_not_rel_left
          (cs_down_succ 0) cs_down_0_not_rel_left],
        dsimp,
        simp only [zero_add, comp_zero],
        slice_rhs 2 3 { erw X_prev_iso_comp_d_to, },
        slice_lhs 2 3 { erw iso.inv_hom_id, },
        simp only [category.id_comp], },
      simp only [null_homotopic_map_f (cs_down_succ 1) (cs_down_succ 0)], rotate,
      simp only [null_homotopic_map_f (cs_down_succ 2) (cs_down_succ 1)], rotate,
      simp only [null_homotopic_map_f (cs_down_succ (i.succ.succ.succ))
        (cs_down_succ (i.succ.succ))],
      all_goals
      { dsimp,
        simp only [d_from_comp_X_next_iso_assoc, category.assoc],
        erw iso.inv_hom_id,
        simp only [X_prev_iso_comp_d_to, category.comp_id],
        simp only [add_right_inj],
        slice_lhs 2 3 { erw iso.inv_hom_id, },
        simp only [category.id_comp], }, },
  end }
end

end mk_inductive

end homotopy

/--
A homotopy equivalence between two chain complexes consists of a chain map each way,
and homotopies from the compositions to the identity chain maps.

Note that this contains data;
arguably it might be more useful for many applications if we truncated it to a Prop.
-/
structure homotopy_equiv (C D : homological_complex V c) :=
(hom : C ⟶ D)
(inv : D ⟶ C)
(homotopy_hom_inv_id : homotopy (hom ≫ inv) (𝟙 C))
(homotopy_inv_hom_id : homotopy (inv ≫ hom) (𝟙 D))

namespace homotopy_equiv

/-- Any complex is homotopy equivalent to itself. -/
@[refl] def refl (C : homological_complex V c) : homotopy_equiv C C :=
{ hom := 𝟙 C,
  inv := 𝟙 C,
  homotopy_hom_inv_id := by simp,
  homotopy_inv_hom_id := by simp, }

instance : inhabited (homotopy_equiv C C) := ⟨refl C⟩

/-- Being homotopy equivalent is a symmetric relation. -/
@[symm] def symm
  {C D : homological_complex V c} (f : homotopy_equiv C D) :
  homotopy_equiv D C :=
{ hom := f.inv,
  inv := f.hom,
  homotopy_hom_inv_id := f.homotopy_inv_hom_id,
  homotopy_inv_hom_id := f.homotopy_hom_inv_id, }

/-- Homotopy equivalence is a transitive relation. -/
@[trans] def trans
  {C D E : homological_complex V c} (f : homotopy_equiv C D) (g : homotopy_equiv D E) :
  homotopy_equiv C E :=
{ hom := f.hom ≫ g.hom,
  inv := g.inv ≫ f.inv,
  homotopy_hom_inv_id := by simpa using
    ((g.homotopy_hom_inv_id.comp_right_id f.inv).comp_left f.hom).trans f.homotopy_hom_inv_id,
  homotopy_inv_hom_id := by simpa using
    ((f.homotopy_inv_hom_id.comp_right_id g.hom).comp_left g.inv).trans g.homotopy_inv_hom_id, }

end homotopy_equiv

variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

variable [has_zero_object V]

/--
Null homotopic maps induce the zero map on homology.
-/
theorem homology_map_eq_zero (hom : prehomotopy C D) (i : ι) :
  (homology_functor V c i).map (homotopy.null_homotopic_map hom) = 0 :=
begin
  dsimp [homology_functor, kernel_subobject_map, homotopy.null_homotopic_map],
  ext,
  simp only [homology.π_map, comp_zero],
  dsimp [kernel_subobject_map],
  simp only [preadditive.comp_add, homotopy.d_next_eq_d_from_from_next,
    kernel_subobject_arrow_comp_assoc, zero_comp,zero_add],
  erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)],
  { simp only [comp_zero, image_to_kernel_as_boundaries_to_cycles,
    homology.condition, category.assoc], },
  { rw [homotopy.prev_d_eq_to_prev_d_to, ← category.assoc],
    apply image_subobject_factors_comp_self, },
end

/--
Homotopic maps induce the same map on homology.
-/
theorem homology_map_eq_of_homotopy (h : homotopy f g) (i : ι) :
  (homology_functor V c i).map f = (homology_functor V c i).map g :=
begin
  rw h.comm,
  simp only [add_left_eq_self, functor.map_add],
  exact homology_map_eq_zero h.hom i,
end

/-- Homotopy equivalent complexes have isomorphic homologies. -/
def homology_obj_iso_of_homotopy_equiv (f : homotopy_equiv C D) (i : ι) :
  (homology_functor V c i).obj C ≅ (homology_functor V c i).obj D :=
{ hom := (homology_functor V c i).map f.hom,
  inv := (homology_functor V c i).map f.inv,
  hom_inv_id' := begin
    rw [←functor.map_comp, homology_map_eq_of_homotopy f.homotopy_hom_inv_id,
      category_theory.functor.map_id],
  end,
  inv_hom_id' := begin
    rw [←functor.map_comp, homology_map_eq_of_homotopy f.homotopy_inv_hom_id,
      category_theory.functor.map_id],
  end, }

end

namespace category_theory

variables {W : Type*} [category W] [preadditive W]

/-- An additive functor takes homotopies to homotopies. -/
@[simps]
def functor.map_homotopy (F : V ⥤ W) [F.additive] {f g : C ⟶ D} (h : homotopy f g) :
  homotopy ((F.map_homological_complex c).map f) ((F.map_homological_complex c).map g) :=
{ hom := λ ij, F.map (h.hom ij),
  comm := begin
    ext i,
    have := homotopy.comm_ext h i,
    dsimp [homotopy.null_homotopic_map, homotopy.d_next, homotopy.prev_d] at *,
    rcases c.next i with _|⟨inext,wn⟩;
    rcases c.prev i with _|⟨iprev,wp⟩;
    dsimp [homotopy.d_next, homotopy.prev_d] at *;
    { intro h, simp only [h, functor.map_add, zero_add, functor.map_comp, functor.map_zero], },
  end, }

/-- An additive functor preserves homotopy equivalences. -/
@[simps]
def functor.map_homotopy_equiv (F : V ⥤ W) [F.additive] (h : homotopy_equiv C D) :
  homotopy_equiv ((F.map_homological_complex c).obj C) ((F.map_homological_complex c).obj D) :=
{ hom := (F.map_homological_complex c).map h.hom,
  inv := (F.map_homological_complex c).map h.inv,
  homotopy_hom_inv_id := begin
    rw [←(F.map_homological_complex c).map_comp, ←(F.map_homological_complex c).map_id],
    exact F.map_homotopy h.homotopy_hom_inv_id,
  end,
  homotopy_inv_hom_id := begin
    rw [←(F.map_homological_complex c).map_comp, ←(F.map_homological_complex c).map_id],
    exact F.map_homotopy h.homotopy_inv_hom_id,
  end }

end category_theory
