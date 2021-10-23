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

/-- The composition of `C.d i i' ≫ f i' i` if there is some `i'` coming after `i`,
and `0` otherwise. -/
def d_next (i : ι) : (Π i j, C.X i ⟶ D.X j) →+ (C.X i ⟶ D.X i) :=
add_monoid_hom.mk' (λ f, match c.next i with
| none := 0
| some ⟨i',w⟩ := C.d i i' ≫ f i' i
end)
begin
  intros f g,
  rcases c.next i with _|⟨i',w⟩,
  exact (zero_add _).symm,
  exact preadditive.comp_add _ _ _ _ _ _,
end

/-- `f i' i` if `i'` comes after `i`, and 0 if there's no such `i'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def from_next [has_zero_object V] (i : ι) : (Π i j, C.X i ⟶ D.X j) →+ (C.X_next i ⟶ D.X i) :=
add_monoid_hom.mk' (λ f, match c.next i with
| none := 0
| some ⟨i',w⟩ := (C.X_next_iso w).hom ≫ f i' i
end)
begin
  intros f g,
  rcases c.next i with _|⟨i',w⟩,
  exact (zero_add _).symm,
  exact preadditive.comp_add _ _ _ _ _ _,
end

lemma d_next_eq_d_from_from_next [has_zero_object V] (f : Π i j, C.X i ⟶ D.X j) (i : ι) :
  d_next i f = C.d_from i ≫ from_next i f :=
begin
  dsimp [d_next, from_next],
  rcases c.next i with ⟨⟩|⟨⟨i', w⟩⟩;
  { dsimp [d_next, from_next], simp },
end

lemma d_next_eq (f : Π i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.rel i i') :
  d_next i f = C.d i i' ≫ f i' i :=
begin
  dsimp [d_next],
  rw c.next_eq_some w,
  refl,
end

@[simp] lemma d_next_comp_left (f : C ⟶ D) (g : Π i j, D.X i ⟶ E.X j) (i : ι) :
  d_next i (λ i j, f.f i ≫ g i j) = f.f i ≫ d_next i g :=
begin
  dsimp [d_next],
  rcases c.next i with _|⟨i',w⟩,
  { exact comp_zero.symm, },
  { dsimp [d_next],
    simp, },
end

@[simp] lemma d_next_comp_right (f : Π i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι) :
  d_next i (λ i j, f i j ≫ g.f j) = d_next i f ≫ g.f i :=
begin
  dsimp [d_next],
  rcases c.next i with _|⟨i',w⟩,
  { exact zero_comp.symm, },
  { dsimp [d_next],
    simp, },
end

/-- The composition of `f j j' ≫ D.d j' j` if there is some `j'` coming before `j`,
and `0` otherwise. -/
def prev_d (j : ι) : (Π i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X j) :=
add_monoid_hom.mk' (λ f, match c.prev j with
| none := 0
| some ⟨j',w⟩ := f j j' ≫ D.d j' j
end)
begin
  intros f g,
  rcases c.prev j with _|⟨j',w⟩,
  exact (zero_add _).symm,
  exact preadditive.add_comp _ _ _ _ _ _,
end

/-- `f j j'` if `j'` comes after `j`, and 0 if there's no such `j'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def to_prev [has_zero_object V] (j : ι) : (Π i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X_prev j) :=
add_monoid_hom.mk' (λ f, match c.prev j with
| none := 0
| some ⟨j',w⟩ := f j j' ≫ (D.X_prev_iso w).inv
end)
begin
  intros f g,
  rcases c.prev j with _|⟨j',w⟩,
  exact (zero_add _).symm,
  exact preadditive.add_comp _ _ _ _ _ _,
end

lemma prev_d_eq_to_prev_d_to [has_zero_object V] (f : Π i j, C.X i ⟶ D.X j) (j : ι) :
  prev_d j f = to_prev j f ≫ D.d_to j :=
begin
  dsimp [prev_d, to_prev],
  rcases c.prev j with ⟨⟩|⟨⟨j', w⟩⟩;
  { dsimp [prev_d, to_prev], simp },
end

lemma prev_d_eq (f : Π i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.rel j' j) :
  prev_d j f = f j j' ≫ D.d j' j :=
begin
  dsimp [prev_d],
  rw c.prev_eq_some w,
  refl,
end

@[simp] lemma prev_d_comp_left (f : C ⟶ D) (g : Π i j, D.X i ⟶ E.X j) (j : ι) :
  prev_d j (λ i j, f.f i ≫ g i j) = f.f j ≫ prev_d j g :=
begin
  dsimp [prev_d],
  rcases c.prev j with _|⟨j',w⟩,
  { exact comp_zero.symm, },
  { dsimp [prev_d, hom.prev],
    simp, },
end

@[simp] lemma to_prev'_comp_right (f : Π i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι) :
  prev_d j (λ i j, f i j ≫ g.f j) = prev_d j f ≫ g.f j :=
begin
  dsimp [prev_d],
  rcases c.prev j with _|⟨j',w⟩,
  { exact zero_comp.symm, },
  { dsimp [prev_d],
    simp, },
end

lemma d_next_nat (C D : chain_complex V ℕ) (i : ℕ) (f : Π i j, C.X i ⟶ D.X j) :
  d_next i f = C.d i (i-1) ≫ f (i-1) i :=
begin
  cases i,
  { dsimp [d_next],
    rcases (complex_shape.down ℕ).next 0 with _|⟨j,hj⟩;
    dsimp [d_next],
    { rw [C.shape, zero_comp], dsimp, dec_trivial },
    { dsimp at hj, exact (nat.succ_ne_zero _ hj).elim } },
  rw d_next_eq, dsimp, refl
end

lemma prev_d_nat (C D : cochain_complex V ℕ) (i : ℕ) (f : Π i j, C.X i ⟶ D.X j) :
  prev_d i f = f i (i-1) ≫ D.d (i-1) i :=
begin
  cases i,
  { dsimp [prev_d],
    rcases (complex_shape.up ℕ).prev 0 with _|⟨j,hj⟩;
    dsimp [prev_d],
    { rw [D.shape, comp_zero], dsimp, dec_trivial },
    { dsimp at hj, exact (nat.succ_ne_zero _ hj).elim } },
  rw prev_d_eq, dsimp, refl
end

/--
A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X j`
which are zero unless `c.rel j i`, satisfying the homotopy condition.
-/
@[ext, nolint has_inhabited_instance]
structure homotopy (f g : C ⟶ D) :=
(hom : Π i j, C.X i ⟶ D.X j)
(zero' : ∀ i j, ¬ c.rel j i → hom i j = 0 . obviously)
(comm : ∀ i, f.f i = d_next i hom + prev_d i hom + g.f i . obviously')

variables {f g}
namespace homotopy

restate_axiom homotopy.zero'

/--
`f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equiv_sub_zero : homotopy f g ≃ homotopy (f - g) 0 :=
{ to_fun := λ h,
  { hom := λ i j, h.hom i j,
    zero' := λ i j w, h.zero _ _ w,
    comm := λ i, by simp [h.comm] },
  inv_fun := λ h,
  { hom := λ i j, h.hom i j,
    zero' := λ i j w, h.zero _ _ w,
    comm := λ i, by simpa [sub_eq_iff_eq_add] using h.comm i },
  left_inv := by tidy,
  right_inv := by tidy, }

/-- Equal chain maps are homotopic. -/
@[simps]
def of_eq (h : f = g) : homotopy f g :=
{ hom := 0,
  zero' := λ _ _ _, rfl,
  comm := λ _, by simp only [add_monoid_hom.map_zero, zero_add, h] }

/-- Every chain map is homotopic to itself. -/
@[simps, refl]
def refl (f : C ⟶ D) : homotopy f f :=
of_eq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps, symm]
def symm {f g : C ⟶ D} (h : homotopy f g) : homotopy g f :=
{ hom := -h.hom,
  zero' := λ i j w, by rw [pi.neg_apply, pi.neg_apply, h.zero i j w, neg_zero],
  comm := λ i, by rw [add_monoid_hom.map_neg, add_monoid_hom.map_neg, h.comm, ← neg_add,
      ← add_assoc, neg_add_self, zero_add] }

/-- homotopy is a transitive relation. -/
@[simps, trans]
def trans {e f g : C ⟶ D} (h : homotopy e f) (k : homotopy f g) : homotopy e g :=
{ hom := h.hom + k.hom,
  zero' := λ i j w, by rw [pi.add_apply, pi.add_apply, h.zero i j w, k.zero i j w, zero_add],
  comm := λ i, by { rw [add_monoid_hom.map_add, add_monoid_hom.map_add, h.comm, k.comm], abel }, }

/-- homotopy is closed under composition (on the right) -/
@[simps]
def comp_right {e f : C ⟶ D} (h : homotopy e f) (g : D ⟶ E) : homotopy (e ≫ g) (f ≫ g) :=
{ hom := λ i j, h.hom i j ≫ g.f j,
  zero' := λ i j w, by rw [h.zero i j w, zero_comp],
  comm := λ i, by simp only [h.comm i, d_next_comp_right, preadditive.add_comp,
    to_prev'_comp_right, comp_f], }

/-- homotopy is closed under composition (on the left) -/
@[simps]
def comp_left {f g : D ⟶ E} (h : homotopy f g) (e : C ⟶ D) : homotopy (e ≫ f) (e ≫ g) :=
{ hom := λ i j, e.f i ≫ h.hom i j,
  zero' := λ i j w, by rw [h.zero i j w, comp_zero],
  comm := λ i, by simp only [h.comm i, d_next_comp_left, preadditive.comp_add,
    prev_d_comp_left, comp_f], }

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

@[simp] lemma prev_d_chain_complex (f : Π i j, P.X i ⟶ Q.X j) (j : ℕ) :
  prev_d j f = f j (j+1) ≫ Q.d _ _ :=
begin
  dsimp [prev_d],
  simp only [chain_complex.prev],
  refl,
end

@[simp] lemma d_next_succ_chain_complex (f : Π i j, P.X i ⟶ Q.X j) (i : ℕ) :
  d_next (i+1) f = P.d _ _ ≫ f i (i+1) :=
begin
  dsimp [d_next],
  simp only [chain_complex.next_nat_succ],
  refl,
end

@[simp] lemma d_next_zero_chain_complex (f : Π i j, P.X i ⟶ Q.X j) :
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
{ hom := λ i j, if h : i + 1 = j then
    (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.X_prev_iso h).hom
  else
    0,
  zero' := λ i j w, by rwa dif_neg,
  comm := λ i, begin
    dsimp, simp only [add_zero],
    convert (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.2,
    { rcases i with (_|_|_|i),
      { dsimp,
        simp only [d_next_zero_chain_complex, d_from_eq_zero, limits.comp_zero], },
      all_goals
      { simp only [d_next_succ_chain_complex],
        dsimp,
        simp only [category.comp_id, category.assoc, iso.inv_hom_id, d_from_comp_X_next_iso_assoc,
          dite_eq_ite, if_true, eq_self_iff_true]}, },
    { cases i,
      all_goals
      { simp only [prev_d_chain_complex],
        dsimp,
        simp only [category.comp_id, category.assoc, iso.inv_hom_id, X_prev_iso_comp_d_to,
          dite_eq_ite, if_true, eq_self_iff_true], }, },
  end, }

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
Homotopic maps induce the same map on homology.
-/
theorem homology_map_eq_of_homotopy (h : homotopy f g) (i : ι) :
  (homology_functor V c i).map f = (homology_functor V c i).map g :=
begin
  dsimp [homology_functor],
  apply eq_of_sub_eq_zero,
  ext,
  simp only [homology.π_map, comp_zero, preadditive.comp_sub],
  dsimp [kernel_subobject_map],
  simp_rw [h.comm i],
  simp only [zero_add, zero_comp, d_next_eq_d_from_from_next, kernel_subobject_arrow_comp_assoc,
    preadditive.comp_add],
  rw [←preadditive.sub_comp],
  simp only [category_theory.subobject.factor_thru_add_sub_factor_thru_right],
  erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)],
  { simp, },
  { rw [prev_d_eq_to_prev_d_to, ←category.assoc],
    apply image_subobject_factors_comp_self, },
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
{ hom := λ i j, F.map (h.hom i j),
  zero' := λ i j w, by { rw [h.zero i j w, F.map_zero], },
  comm := λ i, begin
    have := h.comm i,
    dsimp [d_next, prev_d] at *,
    rcases c.next i with _|⟨inext,wn⟩;
    rcases c.prev i with _|⟨iprev,wp⟩;
    dsimp [d_next, prev_d] at *;
    { intro h,
      simp [h] },
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
