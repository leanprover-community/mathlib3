/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard
-/

import algebra.pi_instances data.finsupp data.equiv.algebra order.order_iso

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps. If `p` and `q` are submodules of a module, `p ≤ q`
means that `p ⊆ q`.

Many of the relevant definitions, including `module`, `submodule`, and `linear_map`, are found in
`src/algebra/module.lean`.

## Main definitions

* Many constructors for linear maps, including `pair` and `copair`
* `submodule.span s` is defined to be the smallest submodule containing the set `s`.
* If `p` is a submodule of `M`, `submodule.quotient p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.
* The kernel `ker` and range `range` of a linear map are submodules of the domain and codomain
  respectively.
* `lin_equiv M M₂`, the type of linear equivalences between `M` and `M₂`, is a structure that extends
  `linear_map` and `equiv`.
* The general linear group is defined to be the group of invertible linear maps from `M` to itself.

## Main statements

* The first and second isomorphism laws for modules are proved as `quot_ker_equiv_range` and
  `sup_quotient_equiv_quotient_inf`.

## Notations

* We continue to use the notation `M →ₗ[R] M₂` for the type of linear maps from `M` to `M₂` over the
  ring `R`.
* We introduce the notations `M ≃ₗ M₂` and `M ≃ₗ[R] M₂` for `lin_equiv M M₂`. In the first, the ring
  `R` is implicit.

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`pair`, `copair`, arithmetic operations like `+`) instead of defining a function and proving
it is linear.

## Tags
linear algebra, vector space, module

-/

open function lattice

reserve infix ` ≃ₗ `:25

universes u v w x y z u' v' w' y'
variables {R : Type u} {𝕜 : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variables {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}

namespace finset

lemma smul_sum {α : Type u} {M : Type v} {R : Type w}
  [ring R] [add_comm_group M] [module R M]
  {s : finset α} {a : R} {f : α → M} :
  a • (s.sum f) = s.sum (λc, a • f c) :=
(finset.sum_hom ((•) a)).symm

end finset

namespace finsupp

lemma smul_sum {α : Type u} {β : Type v} {R : Type w} {M : Type y}
  [has_zero β] [ring R] [add_comm_group M] [module R M]
  {v : α →₀ β} {c : R} {h : α → β → M} :
  c • (v.sum h) = v.sum (λa b, c • h a b) :=
finset.smul_sum

end finsupp

namespace linear_map
section
variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [add_comm_group M₄]
variables [module R M] [module R M₂] [module R M₃] [module R M₄]
variables (f g : M →ₗ[R] M₂)
include R

@[simp] theorem comp_id : f.comp id = f :=
linear_map.ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
linear_map.ext $ λ x, rfl

theorem comp_assoc (g : M₂ →ₗ[R] M₃) (h : M₃ →ₗ[R] M₄) : (h.comp g).comp f = h.comp (g.comp f) :=
rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (h : ∀c, f c ∈ p) : M₂ →ₗ[R] p :=
by refine {to_fun := λc, ⟨f c, h c⟩, ..}; intros; apply set_coe.ext; simp

@[simp] theorem cod_restrict_apply (p : submodule R M) (f : M₂ →ₗ[R] M) {h} (x : M₂) :
  (cod_restrict p f h x : M) = f x := rfl

@[simp] lemma comp_cod_restrict (p : submodule R M₂) (h : ∀b, f b ∈ p) (g : M₃ →ₗ[R] M) :
  (cod_restrict p f h).comp g = cod_restrict p (f.comp g) (assume b, h _) :=
ext $ assume b, rfl

@[simp] lemma subtype_comp_cod_restrict (p : submodule R M₂) (h : ∀b, f b ∈ p) :
  p.subtype.comp (cod_restrict p f h) = f :=
ext $ assume b, rfl

/-- If a function `g` is a left and right inverse of a linear map `f`, then `g` is linear itself. -/
def inverse (g : M₂ → M) (h₁ : left_inverse g f) (h₂ : right_inverse g f) : M₂ →ₗ[R] M :=
by dsimp [left_inverse, function.right_inverse] at h₁ h₂; exact
⟨g, λ x y, by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂],
    λ a b, by rw [← h₁ (g (a • b)), ← h₁ (a • g b)]; simp [h₂]⟩

/-- The constant 0 map is linear. -/
instance : has_zero (M →ₗ[R] M₂) := ⟨⟨λ _, 0, by simp, by simp⟩⟩

@[simp] lemma zero_apply (x : M) : (0 : M →ₗ[R] M₂) x = 0 := rfl

/-- The negation of a linear map is linear. -/
instance : has_neg (M →ₗ[R] M₂) := ⟨λ f, ⟨λ b, - f b, by simp, by simp⟩⟩

@[simp] lemma neg_apply (x : M) : (- f) x = - f x := rfl

/-- The sum of two linear maps is linear. -/
instance : has_add (M →ₗ[R] M₂) := ⟨λ f g, ⟨λ b, f b + g b, by simp, by simp [smul_add]⟩⟩

@[simp] lemma add_apply (x : M) : (f + g) x = f x + g x := rfl

/-- The type of linear maps is an additive group. -/
instance : add_comm_group (M →ₗ[R] M₂) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp

instance linear_map.is_add_group_hom : is_add_group_hom f :=
{ map_add := f.add }

instance linear_map_apply_is_add_group_hom (a : M) :
  is_add_group_hom (λ f : M →ₗ[R] M₂, f a) :=
{ map_add := λ f g, linear_map.add_apply f g a }

lemma sum_apply [decidable_eq M₃] (t : finset M₃) (f : M₃ → M →ₗ[R] M₂) (b : M) :
  t.sum f b = t.sum (λd, f d b) :=
(@finset.sum_hom _ _ _ t f _ _ (λ g : M →ₗ[R] M₂, g b) _).symm

@[simp] lemma sub_apply (x : M) : (f - g) x = f x - g x := rfl

/-- `λb, f b • x` is a linear map. -/
def smul_right (f : M₂ →ₗ[R] R) (x : M) : M₂ →ₗ[R] M :=
⟨λb, f b • x, by simp [add_smul], by simp [smul_smul]⟩.

@[simp] theorem smul_right_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
  (smul_right f x : M₂ → M) c = f c • x := rfl

instance : has_one (M →ₗ[R] M) := ⟨linear_map.id⟩
instance : has_mul (M →ₗ[R] M) := ⟨linear_map.comp⟩

@[simp] lemma one_app (x : M) : (1 : M →ₗ[R] M) x = x := rfl
@[simp] lemma mul_app (A B : M →ₗ[R] M) (x : M) : (A * B) x = A (B x) := rfl

@[simp] theorem comp_zero : f.comp (0 : M₃ →ₗ[R] M) = 0 :=
ext $ assume c, by rw [comp_apply, zero_apply, zero_apply, f.map_zero]

@[simp] theorem zero_comp : (0 : M₂ →ₗ[R] M₃).comp f = 0 :=
rfl

section
variables (R M)
include M

instance endomorphism_ring : ring (M →ₗ[R] M) :=
by refine {mul := (*), one := 1, ..linear_map.add_comm_group, ..};
  { intros, apply linear_map.ext, simp }

end

section
variables (R M M₂)

/-- The first projection of a product is a linear map. -/
def fst : M × M₂ →ₗ[R] M := ⟨prod.fst, λ x y, rfl, λ x y, rfl⟩

/-- The second projection of a product is a linear map. -/
def snd : M × M₂ →ₗ[R] M₂ := ⟨prod.snd, λ x y, rfl, λ x y, rfl⟩
end

@[simp] theorem fst_apply (x : M × M₂) : fst R M M₂ x = x.1 := rfl
@[simp] theorem snd_apply (x : M × M₂) : snd R M M₂ x = x.2 := rfl

/-- The pair of two linear maps is a linear map. -/
def pair (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : M →ₗ[R] M₂ × M₃ :=
⟨λ x, (f x, g x), λ x y, by simp, λ x y, by simp⟩

@[simp] theorem pair_apply (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) (x : M) :
  pair f g x = (f x, g x) := rfl

@[simp] theorem fst_pair (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  (fst R M₂ M₃).comp (pair f g) = f := by ext; refl

@[simp] theorem snd_pair (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  (snd R M₂ M₃).comp (pair f g) = g := by ext; refl

@[simp] theorem pair_fst_snd : pair (fst R M M₂) (snd R M M₂) = linear_map.id :=
by ext; refl

section
variables (R M M₂)

/-- The left injection into a product is a linear map. -/
def inl : M →ₗ[R] M × M₂ := by refine ⟨prod.inl, _, _⟩; intros; simp [prod.inl]

/-- The right injection into a product is a linear map. -/
def inr : M₂ →ₗ[R] M × M₂ := by refine ⟨prod.inr, _, _⟩; intros; simp [prod.inr]

end

@[simp] theorem inl_apply (x : M) : inl R M M₂ x = (x, 0) := rfl
@[simp] theorem inr_apply (x : M₂) : inr R M M₂ x = (0, x) := rfl

/-- The copair function `λ x : M × M₂, f x.1 + g x.2` is a linear map. -/
def copair (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : M × M₂ →ₗ[R] M₃ :=
⟨λ x, f x.1 + g x.2, λ x y, by simp, λ x y, by simp [smul_add]⟩

@[simp] theorem copair_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (x : M) (y : M₂) :
  copair f g (x, y) = f x + g y := rfl

@[simp] theorem copair_inl (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
  (copair f g).comp (inl R M M₂) = f := by ext; simp

@[simp] theorem copair_inr (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
  (copair f g).comp (inr R M M₂) = g := by ext; simp

@[simp] theorem copair_inl_inr : copair (inl R M M₂) (inr R M M₂) = linear_map.id :=
by ext ⟨x, y⟩; simp

theorem fst_eq_copair : fst R M M₂ = copair linear_map.id 0 := by ext ⟨x, y⟩; simp

theorem snd_eq_copair : snd R M M₂ = copair 0 linear_map.id := by ext ⟨x, y⟩; simp

theorem inl_eq_pair : inl R M M₂ = pair linear_map.id 0 := rfl

theorem inr_eq_pair : inr R M M₂ = pair 0 linear_map.id := rfl

end

section comm_ring
variables [comm_ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
variables (f g : M →ₗ[R] M₂)
include R

instance : has_scalar R (M →ₗ[R] M₂) := ⟨λ a f,
  ⟨λ b, a • f b, by simp [smul_add], by simp [smul_smul, mul_comm]⟩⟩

@[simp] lemma smul_apply (a : R) (x : M) : (a • f) x = a • f x := rfl

instance : module R (M →ₗ[R] M₂) :=
module.of_core $ by refine { smul := (•), ..};
  intros; ext; simp [smul_add, add_smul, smul_smul]

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂` to the space of
linear maps `M₂ → M₃`. -/
def congr_right (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] (M →ₗ[R] M₃) :=
⟨linear_map.comp f,
λ _ _, linear_map.ext $ λ _, f.2 _ _,
λ _ _, linear_map.ext $ λ _, f.3 _ _⟩

theorem smul_comp (g : M₂ →ₗ[R] M₃) (a : R) : (a • g).comp f = a • (g.comp f) :=
rfl

theorem comp_smul (g : M₂ →ₗ[R] M₃) (a : R) : g.comp (a • f) = a • (g.comp f) :=
ext $ assume b, by rw [comp_apply, smul_apply, g.map_smul]; refl

end comm_ring
end linear_map

namespace submodule
variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
variables (p p' : submodule R M) (q q' : submodule R M₂)
variables {r : R} {x y : M}
open set lattice

instance : partial_order (submodule R M) :=
partial_order.lift (coe : submodule R M → set M) (λ a b, ext') (by apply_instance)

lemma le_def {p p' : submodule R M} : p ≤ p' ↔ (p : set M) ⊆ p' := iff.rfl

lemma le_def' {p p' : submodule R M} : p ≤ p' ↔ ∀ x ∈ p, x ∈ p' := iff.rfl

def of_le {p p' : submodule R M} (h : p ≤ p') : p →ₗ[R] p' :=
linear_map.cod_restrict _ p.subtype $ λ ⟨x, hx⟩, h hx

@[simp] theorem of_le_apply {p p' : submodule R M} (h : p ≤ p')
  (x : p) : (of_le h x : M) = x := rfl

lemma subtype_comp_of_le (p q : submodule R M) (h : p ≤ q) :
  (submodule.subtype q).comp (of_le h) = submodule.subtype p :=
by ext ⟨b, hb⟩; simp

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : has_bot (submodule R M) :=
⟨by split; try {exact {0}}; simp {contextual := tt}⟩

@[simp] lemma bot_coe : ((⊥ : submodule R M) : set M) = {0} := rfl

section
variables (R)
@[simp] lemma mem_bot : x ∈ (⊥ : submodule R M) ↔ x = 0 := mem_singleton_iff
end

instance : order_bot (submodule R M) :=
{ bot := ⊥,
  bot_le := λ p x, by simp {contextual := tt},
  ..submodule.partial_order }

/-- The universal set is the top element of the lattice of submodules. -/
instance : has_top (submodule R M) :=
⟨by split; try {exact set.univ}; simp⟩

@[simp] lemma top_coe : ((⊤ : submodule R M) : set M) = univ := rfl

@[simp] lemma mem_top : x ∈ (⊤ : submodule R M) := trivial

lemma eq_bot_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : p = ⊥ :=
by ext x; simp [semimodule.eq_zero_of_zero_eq_one _ x zero_eq_one]

instance : order_top (submodule R M) :=
{ top := ⊤,
  le_top := λ p x _, trivial,
  ..submodule.partial_order }

instance : has_Inf (submodule R M) :=
⟨λ S, {
  carrier := ⋂ s ∈ S, ↑s,
  zero := by simp,
  add  := by simp [add_mem] {contextual := tt},
  smul := by simp [smul_mem] {contextual := tt} }⟩

private lemma Inf_le' {S : set (submodule R M)} {p} : p ∈ S → Inf S ≤ p :=
bInter_subset_of_mem

private lemma le_Inf' {S : set (submodule R M)} {p} : (∀p' ∈ S, p ≤ p') → p ≤ Inf S :=
subset_bInter

instance : has_inf (submodule R M) :=
⟨λ p p', {
  carrier := p ∩ p',
  zero := by simp,
  add  := by simp [add_mem] {contextual := tt},
  smul := by simp [smul_mem] {contextual := tt} }⟩

instance : complete_lattice (submodule R M) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c, subset_inter,
  inf_le_left  := λ a b, inter_subset_left _ _,
  inf_le_right := λ a b, inter_subset_right _ _,
  Sup          := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ p' hp', hp' _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..submodule.lattice.order_top,
  ..submodule.lattice.order_bot }

instance : add_comm_monoid (submodule R M) :=
{ add := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero := ⊥,
  zero_add := λ _, bot_sup_eq,
  add_zero := λ _, sup_bot_eq,
  add_comm := λ _ _, sup_comm }

@[simp] lemma add_eq_sup (p q : submodule R M) : p + q = p ⊔ q := rfl
@[simp] lemma zero_eq_bot : (0 : submodule R M) = ⊥ := rfl

lemma eq_top_iff' {p : submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, @h x trivial, λ h x _, h x⟩

@[simp] theorem inf_coe : (p ⊓ p' : set M) = p ∩ p' := rfl

@[simp] theorem mem_inf {p p' : submodule R M} :
  x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

@[simp] theorem Inf_coe (P : set (submodule R M)) : (↑(Inf P) : set M) = ⋂ p ∈ P, ↑p := rfl

@[simp] theorem infi_coe {ι} (p : ι → submodule R M) :
  (↑⨅ i, p i : set M) = ⋂ i, ↑(p i) :=
by rw [infi, Inf_coe]; ext a; simp; exact
⟨λ h i, h _ i rfl, λ h i x e, e ▸ h _⟩

@[simp] theorem mem_infi {ι} (p : ι → submodule R M) :
  x ∈ (⨅ i, p i) ↔ ∀ i, x ∈ p i :=
by rw [← mem_coe, infi_coe, mem_Inter]; refl

theorem disjoint_def {p p' : submodule R M} :
  disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0:M) :=
show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : set M)) ↔ _, by simp

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ₗ[R] M₂) (p : submodule R M) : submodule R M₂ :=
{ carrier := f '' p,
  zero  := ⟨0, p.zero_mem, f.map_zero⟩,
  add   := by rintro _ _ ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩;
              exact ⟨_, p.add_mem hb₁ hb₂, f.map_add _ _⟩,
  smul  := by rintro a _ ⟨b, hb, rfl⟩;
              exact ⟨_, p.smul_mem _ hb, f.map_smul _ _⟩ }

lemma map_coe (f : M →ₗ[R] M₂) (p : submodule R M) :
  (map f p : set M₂) = f '' p := rfl

@[simp] lemma mem_map {f : M →ₗ[R] M₂} {p : submodule R M} {x : M₂} :
  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x := iff.rfl

theorem mem_map_of_mem {f : M →ₗ[R] M₂} {p : submodule R M} {r} (h : r ∈ p) : f r ∈ map f p :=
set.mem_image_of_mem _ h

lemma map_id : map linear_map.id p = p :=
submodule.ext $ λ a, by simp

lemma map_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (p : submodule R M) :
  map (g.comp f) p = map g (map f p) :=
submodule.ext' $ by simp [map_coe]; rw ← image_comp

lemma map_mono {f : M →ₗ[R] M₂} {p p' : submodule R M} : p ≤ p' → map f p ≤ map f p' :=
image_subset _

@[simp] lemma map_zero : map (0 : M →ₗ[R] M₂) p = ⊥ :=
have ∃ (x : M), x ∈ p := ⟨0, p.zero_mem⟩,
ext $ by simp [this, eq_comm]

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : M →ₗ[R] M₂) (p : submodule R M₂) : submodule R M :=
{ carrier := f ⁻¹' p,
  zero  := by simp,
  add   := λ x y h₁ h₂, by simp [p.add_mem h₁ h₂],
  smul  := λ a x h, by simp [p.smul_mem _ h] }

@[simp] lemma comap_coe (f : M →ₗ[R] M₂) (p : submodule R M₂) :
  (comap f p : set M) = f ⁻¹' p := rfl

@[simp] lemma mem_comap {f : M →ₗ[R] M₂} {p : submodule R M₂} :
  x ∈ comap f p ↔ f x ∈ p := iff.rfl

lemma comap_id : comap linear_map.id p = p :=
submodule.ext' rfl

lemma comap_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (p : submodule R M₃) :
  comap (g.comp f) p = comap f (comap g p) := rfl

lemma comap_mono {f : M →ₗ[R] M₂} {q q' : submodule R M₂} : q ≤ q' → comap f q ≤ comap f q' :=
preimage_mono

lemma map_le_iff_le_comap {f : M →ₗ[R] M₂} {p : submodule R M} {q : submodule R M₂} :
  map f p ≤ q ↔ p ≤ comap f q := image_subset_iff

lemma gc_map_comap (f : M →ₗ[R] M₂) : galois_connection (map f) (comap f)
| p q := map_le_iff_le_comap

@[simp] lemma map_bot (f : M →ₗ[R] M₂) : map f ⊥ = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma map_sup (f : M →ₗ[R] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
(gc_map_comap f).l_sup

@[simp] lemma map_supr {ι : Sort*} (f : M →ₗ[R] M₂) (p : ι → submodule R M) :
  map f (⨆i, p i) = (⨆i, map f (p i)) :=
(gc_map_comap f).l_supr

@[simp] lemma comap_top (f : M →ₗ[R] M₂) : comap f ⊤ = ⊤ := rfl

@[simp] lemma comap_inf (f : M →ₗ[R] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' := rfl

@[simp] lemma comap_infi {ι : Sort*} (f : M →ₗ[R] M₂) (p : ι → submodule R M₂) :
  comap f (⨅i, p i) = (⨅i, comap f (p i)) :=
(gc_map_comap f).u_infi

@[simp] lemma comap_zero : comap (0 : M →ₗ[R] M₂) q = ⊤ :=
ext $ by simp

lemma map_comap_le (f : M →ₗ[R] M₂) (q : submodule R M₂) : map f (comap f q) ≤ q :=
(gc_map_comap f).l_u_le _

lemma le_comap_map (f : M →ₗ[R] M₂) (p : submodule R M) : p ≤ comap f (map f p) :=
(gc_map_comap f).le_u_l _

--TODO(Mario): is there a way to prove this from order properties?
lemma map_inf_eq_map_inf_comap {f : M →ₗ[R] M₂}
  {p : submodule R M} {p' : submodule R M₂} :
  map f p ⊓ p' = map f (p ⊓ comap f p') :=
le_antisymm
  (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
  (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))

lemma map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
ext $ λ x, ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

lemma eq_zero_of_bot_submodule : ∀(b : (⊥ : submodule R M)), b = 0
| ⟨b', hb⟩ := subtype.eq $ show b' = 0, from (mem_bot R).1 hb

section
variables (R)

/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : set M) : submodule R M := Inf {p | s ⊆ p}
end

variables {s t : set M}
lemma mem_span : x ∈ span R s ↔ ∀ p : submodule R M, s ⊆ p → x ∈ p :=
mem_bInter_iff

lemma subset_span : s ⊆ span R s :=
λ x h, mem_span.2 $ λ p hp, hp h

lemma span_le {p} : span R s ≤ p ↔ s ⊆ p :=
⟨subset.trans subset_span, λ ss x h, mem_span.1 h _ ss⟩

lemma span_mono (h : s ⊆ t) : span R s ≤ span R t :=
span_le.2 $ subset.trans h subset_span

lemma span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span R s) : span R s = p :=
le_antisymm (span_le.2 h₁) h₂

@[simp] lemma span_eq : span R (p : set M) = p :=
span_eq_of_le _ (subset.refl _) subset_span

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition and scalar multiplication, then `p` holds for all elements of the span of
`s`. -/
@[elab_as_eliminator] lemma span_induction {p : M → Prop} (h : x ∈ span R s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ (a:R) x, p x → p (a • x)) : p x :=
(@span_le _ _ _ _ _ _ ⟨p, H0, H1, H2⟩).2 Hs h

section
variables (R M)

/-- `span` forms a Galois insertion with the coercion from submodule to set. -/
protected def gi : galois_insertion (@span R M _ _ _) coe :=
{ choice := λ s _, span R s,
  gc := λ s t, span_le,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, rfl }

end

@[simp] lemma span_empty : span R (∅ : set M) = ⊥ :=
(submodule.gi R M).gc.l_bot

@[simp] lemma span_univ : span R (univ : set M) = ⊤ :=
eq_top_iff.2 $ le_def.2 $ subset_span

lemma span_union (s t : set M) : span R (s ∪ t) = span R s ⊔ span R t :=
(submodule.gi R M).gc.l_sup

lemma span_Union {ι} (s : ι → set M) : span R (⋃ i, s i) = ⨆ i, span R (s i) :=
(submodule.gi R M).gc.l_supr

@[simp] theorem Union_coe_of_directed {ι} (hι : nonempty ι)
  (S : ι → submodule R M)
  (H : ∀ i j, ∃ k, S i ≤ S k ∧ S j ≤ S k) :
  ((supr S : submodule R M) : set M) = ⋃ i, S i :=
begin
  refine subset.antisymm _ (Union_subset $ le_supr S),
  rw [show supr S = ⨆ i, span R (S i), by simp, ← span_Union],
  unfreezeI,
  refine λ x hx, span_induction hx (λ _, id) _ _ _,
  { cases hι with i, exact mem_Union.2 ⟨i, by simp⟩ },
  { simp, intros x y i hi j hj,
    rcases H i j with ⟨k, ik, jk⟩,
    exact ⟨k, add_mem _ (ik hi) (jk hj)⟩ },
  { simp [-mem_coe]; exact λ a x i hi, ⟨i, smul_mem _ a hi⟩ },
end

lemma mem_supr_of_mem {ι : Sort*} {b : M} (p : ι → submodule R M) (i : ι) (h : b ∈ p i) :
  b ∈ (⨆i, p i) :=
have p i ≤ (⨆i, p i) := le_supr p i,
@this b h

@[simp] theorem mem_supr_of_directed {ι} (hι : nonempty ι)
  (S : ι → submodule R M)
  (H : ∀ i j, ∃ k, S i ≤ S k ∧ S j ≤ S k) {x} :
  x ∈ supr S ↔ ∃ i, x ∈ S i :=
by rw [← mem_coe, Union_coe_of_directed hι S H, mem_Union]; refl

theorem mem_Sup_of_directed {s : set (submodule R M)}
  {z} (hzs : z ∈ Sup s) (x ∈ s)
  (hdir : ∀ i ∈ s, ∀ j ∈ s, ∃ k ∈ s, i ≤ k ∧ j ≤ k) :
  ∃ y ∈ s, z ∈ y :=
begin
  haveI := classical.dec, rw Sup_eq_supr at hzs,
  have : ∃ (i : submodule R M), z ∈ ⨆ (H : i ∈ s), i,
  { refine (mem_supr_of_directed ⟨⊥⟩ _ (λ i j, _)).1 hzs,
    by_cases his : i ∈ s; by_cases hjs : j ∈ s,
    { rcases hdir i his j hjs with ⟨k, hks, hik, hjk⟩,
        exact ⟨k, le_supr_of_le hks (supr_le $ λ _, hik),
          le_supr_of_le hks (supr_le $ λ _, hjk)⟩ },
    { exact ⟨i, le_refl _, supr_le $ hjs.elim⟩ },
    { exact ⟨j, supr_le $ his.elim, le_refl _⟩ },
    { exact ⟨⊥, supr_le $ his.elim, supr_le $ hjs.elim⟩ } },
  cases this with N hzn, by_cases hns : N ∈ s,
  { have : (⨆ (H : N ∈ s), N) ≤ N := supr_le (λ _, le_refl _),
    exact ⟨N, hns, this hzn⟩ },
  { have : (⨆ (H : N ∈ s), N) ≤ ⊥ := supr_le hns.elim,
    cases (mem_bot R).1 (this hzn), exact ⟨x, H, x.zero_mem⟩ }
end

section
variables {p p'}
lemma mem_sup : x ∈ p ⊔ p' ↔ ∃ (y ∈ p) (z ∈ p'), y + z = x :=
⟨λ h, begin
  rw [← span_eq p, ← span_eq p', ← span_union] at h,
  apply span_induction h,
  { rintro y (h | h),
    { exact ⟨y, h, 0, by simp, by simp⟩ },
    { exact ⟨0, by simp, y, h, by simp⟩ } },
  { exact ⟨0, by simp, 0, by simp⟩ },
  { rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩,
    exact ⟨_, add_mem _ hy₁ hy₂, _, add_mem _ hz₁ hz₂, by simp⟩ },
  { rintro a _ ⟨y, hy, z, hz, rfl⟩,
    exact ⟨_, smul_mem _ a hy, _, smul_mem _ a hz, by simp [smul_add]⟩ }
end,
by rintro ⟨y, hy, z, hz, rfl⟩; exact add_mem _
  ((le_sup_left : p ≤ p ⊔ p') hy)
  ((le_sup_right : p' ≤ p ⊔ p') hz)⟩
end

lemma mem_span_singleton {y : M} : x ∈ span R ({y} : set M) ↔ ∃ a:R, a • y = x :=
⟨λ h, begin
  apply span_induction h,
  { rintro y (rfl|⟨⟨⟩⟩), exact ⟨1, by simp⟩ },
  { exact ⟨0, by simp⟩ },
  { rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩,
    exact ⟨a + b, by simp [add_smul]⟩ },
  { rintro a _ ⟨b, rfl⟩,
    exact ⟨a * b, by simp [smul_smul]⟩ }
end,
by rintro ⟨a, y, rfl⟩; exact
  smul_mem _ _ (subset_span $ by simp)⟩

lemma span_singleton_eq_range (y : M) : (span R ({y} : set M) : set M) = range ((• y) : R → M) :=
set.ext $ λ x, mem_span_singleton

lemma mem_span_insert {y} : x ∈ span R (insert y s) ↔ ∃ (a:R) (z ∈ span R s), x = a • y + z :=
begin
  rw [← union_singleton, span_union, mem_sup],
  simp [mem_span_singleton], split,
  { rintro ⟨z, hz, _, ⟨a, rfl⟩, rfl⟩, exact ⟨a, z, hz, rfl⟩ },
  { rintro ⟨a, z, hz, rfl⟩, exact ⟨z, hz, _, ⟨a, rfl⟩, rfl⟩ }
end

lemma mem_span_insert' {y} : x ∈ span R (insert y s) ↔ ∃(a:R), x + a • y ∈ span R s :=
begin
  rw mem_span_insert, split,
  { rintro ⟨a, z, hz, rfl⟩, exact ⟨-a, by simp [hz]⟩ },
  { rintro ⟨a, h⟩, exact ⟨-a, _, h, by simp⟩ }
end

lemma span_insert_eq_span (h : x ∈ span R s) : span R (insert x s) = span R s :=
span_eq_of_le _ (set.insert_subset.mpr ⟨h, subset_span⟩) (span_mono $ subset_insert _ _)

lemma span_span : span R (span R s : set M) = span R s := span_eq _

lemma span_eq_bot : span R (s : set M) = ⊥ ↔ ∀ x ∈ s, (x:M) = 0 :=
eq_bot_iff.trans ⟨
  λ H x h, (mem_bot R).1 $ H $ subset_span h,
  λ H, span_le.2 (λ x h, (mem_bot R).2 $ H x h)⟩

lemma span_singleton_eq_bot : span R ({x} : set M) = ⊥ ↔ x = 0 :=
span_eq_bot.trans $ by simp

@[simp] lemma span_image (f : M →ₗ[R] M₂) : span R (f '' s) = map f (span R s) :=
span_eq_of_le _ (image_subset _ subset_span) $ map_le_iff_le_comap.2 $
span_le.2 $ image_subset_iff.1 subset_span

lemma linear_eq_on (s : set M) {f g : M →ₗ[R] M₂} (H : ∀x∈s, f x = g x) {x} (h : x ∈ span R s) :
  f x = g x :=
by apply span_induction h H; simp {contextual := tt}

/-- The product of two submodules is a submodule. -/
def prod : submodule R (M × M₂) :=
{ carrier := set.prod p q,
  zero := ⟨zero_mem _, zero_mem _⟩,
  add  := by rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨hx₁, hy₁⟩ ⟨hx₂, hy₂⟩;
             exact ⟨add_mem _ hx₁ hx₂, add_mem _ hy₁ hy₂⟩,
  smul := by rintro a ⟨x, y⟩ ⟨hx, hy⟩;
             exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }

@[simp] lemma prod_coe :
  (prod p q : set (M × M₂)) = set.prod p q := rfl

@[simp] lemma mem_prod {p : submodule R M} {q : submodule R M₂} {x : M × M₂} :
  x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q := set.mem_prod

lemma span_prod_le (s : set M) (t : set M₂) :
  span R (set.prod s t) ≤ prod (span R s) (span R t) :=
span_le.2 $ set.prod_mono subset_span subset_span

@[simp] lemma prod_top : (prod ⊤ ⊤ : submodule R (M × M₂)) = ⊤ :=
by ext; simp

@[simp] lemma prod_bot : (prod ⊥ ⊥ : submodule R (M × M₂)) = ⊥ :=
by ext ⟨x, y⟩; simp [prod.zero_eq_mk]

lemma prod_mono {p p' : submodule R M} {q q' : submodule R M₂} :
  p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' := prod_mono

@[simp] lemma prod_inf_prod : prod p q ⊓ prod p' q' = prod (p ⊓ p') (q ⊓ q') :=
ext' set.prod_inter_prod

@[simp] lemma prod_sup_prod : prod p q ⊔ prod p' q' = prod (p ⊔ p') (q ⊔ q') :=
begin
  refine le_antisymm (sup_le
    (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right)) _,
  simp [le_def'], intros xx yy hxx hyy,
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩,
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩,
  refine mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩
end

-- TODO(Mario): Factor through add_subgroup
def quotient_rel : setoid M :=
⟨λ x y, x - y ∈ p, λ x, by simp,
 λ x y h, by simpa using neg_mem _ h,
 λ x y z h₁ h₂, by simpa using add_mem _ h₁ h₂⟩

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
def quotient : Type* := quotient (quotient_rel p)

namespace quotient

def mk {p : submodule R M} : M → quotient p := quotient.mk'

@[simp] theorem mk_eq_mk {p : submodule R M} (x : M) : (quotient.mk x : quotient p) = mk x := rfl
@[simp] theorem mk'_eq_mk {p : submodule R M} (x : M) : (quotient.mk' x : quotient p) = mk x := rfl
@[simp] theorem quot_mk_eq_mk {p : submodule R M} (x : M) : (quot.mk _ x : quotient p) = mk x := rfl

protected theorem eq {x y : M} : (mk x : quotient p) = mk y ↔ x - y ∈ p := quotient.eq'

instance : has_zero (quotient p) := ⟨mk 0⟩

@[simp] theorem mk_zero : mk 0 = (0 : quotient p) := rfl

@[simp] theorem mk_eq_zero : (mk x : quotient p) = 0 ↔ x ∈ p :=
by simpa using (quotient.eq p : mk x = 0 ↔ _)

instance : has_add (quotient p) :=
⟨λ a b, quotient.lift_on₂' a b (λ a b, mk (a + b)) $
 λ a₁ a₂ b₁ b₂ h₁ h₂, (quotient.eq p).2 $ by simpa using add_mem p h₁ h₂⟩

@[simp] theorem mk_add : (mk (x + y) : quotient p) = mk x + mk y := rfl

instance : has_neg (quotient p) :=
⟨λ a, quotient.lift_on' a (λ a, mk (-a)) $
 λ a b h, (quotient.eq p).2 $ by simpa using neg_mem p h⟩

@[simp] theorem mk_neg : (mk (-x) : quotient p) = -mk x := rfl

instance : add_comm_group (quotient p) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   repeat {rintro ⟨⟩};
   simp [-mk_zero, (mk_zero p).symm, -mk_add, (mk_add p).symm, -mk_neg, (mk_neg p).symm]

instance : has_scalar R (quotient p) :=
⟨λ a x, quotient.lift_on' x (λ x, mk (a • x)) $
 λ x y h, (quotient.eq p).2 $ by simpa [smul_add] using smul_mem p a h⟩

@[simp] theorem mk_smul : (mk (r • x) : quotient p) = r • mk x := rfl

instance : module R (quotient p) :=
module.of_core $ by refine {smul := (•), ..};
  repeat {rintro ⟨⟩ <|> intro}; simp [smul_add, add_smul, smul_smul,
    -mk_add, (mk_add p).symm, -mk_smul, (mk_smul p).symm]

instance {𝕜 M} {R:discrete_field 𝕜} [add_comm_group M] [vector_space 𝕜 M]
  (p : submodule 𝕜 M) : vector_space 𝕜 (quotient p) := {}

end quotient

end submodule

namespace submodule
variables [discrete_field 𝕜]
variables [add_comm_group V] [vector_space 𝕜 V]
variables [add_comm_group V₂] [vector_space 𝕜 V₂]

lemma comap_smul (f : V →ₗ[𝕜] V₂) (p : submodule 𝕜 V₂) (a : 𝕜) (h : a ≠ 0) :
  p.comap (a • f) = p.comap f :=
by ext b; simp only [submodule.mem_comap, p.smul_mem_iff h, linear_map.smul_apply]

lemma map_smul (f : V →ₗ[𝕜] V₂) (p : submodule 𝕜 V) (a : 𝕜) (h : a ≠ 0) :
  p.map (a • f) = p.map f :=
le_antisymm
  begin rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap], exact le_refl _ end
  begin rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap], exact le_refl _ end

set_option class.instance_max_depth 40

lemma comap_smul' (f : V →ₗ[𝕜] V₂) (p : submodule 𝕜 V₂) (a : 𝕜) :
  p.comap (a • f) = (⨅ h : a ≠ 0, p.comap f) :=
by by_cases a = 0; simp [h, comap_smul]

lemma map_smul' (f : V →ₗ[𝕜] V₂) (p : submodule 𝕜 V) (a : 𝕜) :
  p.map (a • f) = (⨆ h : a ≠ 0, p.map f) :=
by by_cases a = 0; simp [h, map_smul]

end submodule

namespace linear_map
variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
include R
open submodule

@[simp] lemma finsupp_sum {R M M₂ γ} [ring R] [add_comm_group M] [module R M]
   [add_comm_group M₂] [module R M₂] [has_zero γ]
  (f : M →ₗ[R] M₂) {t : ι →₀ γ} {g : ι → γ → M} :
  f (t.sum g) = t.sum (λi d, f (g i d)) := f.map_sum

theorem map_cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (h p') :
  submodule.map (cod_restrict p f h) p' = comap p.subtype (p'.map f) :=
submodule.ext $ λ ⟨x, hx⟩, by simp [subtype.coe_ext]

theorem comap_cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (hf p') :
  submodule.comap (cod_restrict p f hf) p' = submodule.comap f (map p.subtype p') :=
submodule.ext $ λ x, ⟨λ h, ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`. -/
def range (f : M →ₗ[R] M₂) : submodule R M₂ := map f ⊤

theorem range_coe (f : M →ₗ[R] M₂) : (range f : set M₂) = set.range f := set.image_univ

@[simp] theorem mem_range {f : M →ₗ[R] M₂} : ∀ {x}, x ∈ range f ↔ ∃ y, f y = x :=
(set.ext_iff _ _).1 (range_coe f).

@[simp] theorem range_id : range (linear_map.id : M →ₗ[R] M) = ⊤ := map_id _

theorem range_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : range (g.comp f) = map g (range f) :=
map_comp _ _ _

theorem range_comp_le_range (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : range (g.comp f) ≤ range g :=
by rw range_comp; exact map_mono le_top

theorem range_eq_top {f : M →ₗ[R] M₂} : range f = ⊤ ↔ surjective f :=
by rw [← submodule.ext'_iff, range_coe, top_coe, set.range_iff_surjective]

lemma range_le_iff_comap {f : M →ₗ[R] M₂} {p : submodule R M₂} : range f ≤ p ↔ comap f p = ⊤ :=
by rw [range, map_le_iff_le_comap, eq_top_iff]

lemma map_le_range {f : M →ₗ[R] M₂} {p : submodule R M} : map f p ≤ range f :=
map_mono le_top

lemma sup_range_inl_inr :
  (inl R M M₂).range ⊔ (inr R M M₂).range = ⊤ :=
begin
  refine eq_top_iff'.2 (λ x, mem_sup.2 _),
  rcases x with ⟨x₁, x₂⟩ ,
  have h₁ : prod.mk x₁ (0 : M₂) ∈ (inl R M M₂).range,
    by simp,
  have h₂ : prod.mk (0 : M) x₂ ∈ (inr R M M₂).range,
    by simp,
  use [⟨x₁, 0⟩, h₁, ⟨0, x₂⟩, h₂],
  simp
end

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : M →ₗ[R] M₂) : submodule R M := comap f ⊥

@[simp] theorem mem_ker {f : M →ₗ[R] M₂} {y} : y ∈ ker f ↔ f y = 0 := mem_bot R

@[simp] theorem ker_id : ker (linear_map.id : M →ₗ[R] M) = ⊥ := rfl

theorem ker_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : ker (g.comp f) = comap f (ker g) := rfl

theorem ker_le_ker_comp (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : ker f ≤ ker (g.comp f) :=
by rw ker_comp; exact comap_mono bot_le

theorem sub_mem_ker_iff {f : M →ₗ[R] M₂} {x y} : x - y ∈ f.ker ↔ f x = f y :=
by rw [mem_ker, map_sub, sub_eq_zero]

theorem disjoint_ker {f : M →ₗ[R] M₂} {p : submodule R M} :
  disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 :=
by simp [disjoint_def]

theorem disjoint_ker' {f : M →ₗ[R] M₂} {p : submodule R M} :
  disjoint p (ker f) ↔ ∀ x y ∈ p, f x = f y → x = y :=
disjoint_ker.trans
⟨λ H x y hx hy h, eq_of_sub_eq_zero $ H _ (sub_mem _ hx hy) (by simp [h]),
 λ H x h₁ h₂, H x 0 h₁ (zero_mem _) (by simpa using h₂)⟩

theorem inj_of_disjoint_ker {f : M →ₗ[R] M₂} {p : submodule R M}
  {s : set M} (h : s ⊆ p) (hd : disjoint p (ker f)) :
  ∀ x y ∈ s, f x = f y → x = y :=
λ x y hx hy, disjoint_ker'.1 hd _ _ (h hx) (h hy)

lemma disjoint_inl_inr : disjoint (inl R M M₂).range (inr R M M₂).range :=
by simp [disjoint_def, @eq_comm M 0, @eq_comm M₂ 0] {contextual := tt}; intros; refl

theorem ker_eq_bot {f : M →ₗ[R] M₂} : ker f = ⊥ ↔ injective f :=
by simpa [disjoint] using @disjoint_ker' _ _ _ _ _ _ _ _ f ⊤

theorem ker_eq_bot' {f : M →ₗ[R] M₂} :
  ker f = ⊥ ↔ (∀ m, f m = 0 → m = 0) :=
have h : (∀ m ∈ (⊤ : submodule R M), f m = 0 → m = 0) ↔ (∀ m, f m = 0 → m = 0),
  from ⟨λ h m, h m mem_top, λ h m _, h m⟩,
by simpa [h, disjoint] using @disjoint_ker _ _ _ _ _ _ _ _ f ⊤

lemma le_ker_iff_map {f : M →ₗ[R] M₂} {p : submodule R M} : p ≤ ker f ↔ map f p = ⊥ :=
by rw [ker, eq_bot_iff, map_le_iff_le_comap]

lemma ker_cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (hf) :
  ker (cod_restrict p f hf) = ker f :=
by rw [ker, comap_cod_restrict, map_bot]; refl

lemma range_cod_restrict (p : submodule R M) (f : M₂ →ₗ[R] M) (hf) :
  range (cod_restrict p f hf) = comap p.subtype f.range :=
map_cod_restrict _ _ _ _

lemma map_comap_eq (f : M →ₗ[R] M₂) (q : submodule R M₂) :
  map f (comap f q) = range f ⊓ q :=
le_antisymm (le_inf (map_mono le_top) (map_comap_le _ _)) $
by rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

lemma map_comap_eq_self {f : M →ₗ[R] M₂} {q : submodule R M₂} (h : q ≤ range f) :
  map f (comap f q) = q :=
by rw [map_comap_eq, inf_of_le_right h]

lemma comap_map_eq (f : M →ₗ[R] M₂) (p : submodule R M) :
  comap f (map f p) = p ⊔ ker f :=
begin
  refine le_antisymm _ (sup_le (le_comap_map _ _) (comap_mono bot_le)),
  rintro x ⟨y, hy, e⟩,
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩
end

lemma comap_map_eq_self {f : M →ₗ[R] M₂} {p : submodule R M} (h : ker f ≤ p) :
  comap f (map f p) = p :=
by rw [comap_map_eq, sup_of_le_left h]

@[simp] theorem ker_zero : ker (0 : M →ₗ[R] M₂) = ⊤ :=
eq_top_iff'.2 $ λ x, by simp

@[simp] theorem range_zero : range (0 : M →ₗ[R] M₂) = ⊥ :=
submodule.map_zero _

theorem ker_eq_top {f : M →ₗ[R] M₂} : ker f = ⊤ ↔ f = 0 :=
⟨λ h, ext $ λ x, mem_ker.1 $ h.symm ▸ trivial, λ h, h.symm ▸ ker_zero⟩

lemma range_le_bot_iff (f : M →ₗ[R] M₂) : range f ≤ ⊥ ↔ f = 0 :=
by rw [range_le_iff_comap]; exact ker_eq_top

theorem map_le_map_iff {f : M →ₗ[R] M₂} (hf : ker f = ⊥) {p p'} : map f p ≤ map f p' ↔ p ≤ p' :=
⟨λ H x hx, let ⟨y, hy, e⟩ := H ⟨x, hx, rfl⟩ in ker_eq_bot.1 hf e ▸ hy, map_mono⟩

theorem map_injective {f : M →ₗ[R] M₂} (hf : ker f = ⊥) : injective (map f) :=
λ p p' h, le_antisymm ((map_le_map_iff hf).1 (le_of_eq h)) ((map_le_map_iff hf).1 (ge_of_eq h))

theorem comap_le_comap_iff {f : M →ₗ[R] M₂} (hf : range f = ⊤) {p p'} : comap f p ≤ comap f p' ↔ p ≤ p' :=
⟨λ H x hx, by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, comap_mono⟩

theorem comap_injective {f : M →ₗ[R] M₂} (hf : range f = ⊤) : injective (comap f) :=
λ p p' h, le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))

theorem map_copair_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (p : submodule R M) (q : submodule R M₂) :
  map (copair f g) (p.prod q) = map f p ⊔ map g q :=
begin
  refine le_antisymm _ (sup_le (map_le_iff_le_comap.2 _) (map_le_iff_le_comap.2 _)),
  { rw le_def', rintro _ ⟨x, ⟨h₁, h₂⟩, rfl⟩,
    exact mem_sup.2 ⟨_, ⟨_, h₁, rfl⟩, _, ⟨_, h₂, rfl⟩, rfl⟩ },
  { exact λ x hx, ⟨(x, 0), by simp [hx]⟩ },
  { exact λ x hx, ⟨(0, x), by simp [hx]⟩ }
end

theorem comap_pair_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) (p : submodule R M₂) (q : submodule R M₃) :
  comap (pair f g) (p.prod q) = comap f p ⊓ comap g q :=
submodule.ext $ λ x, iff.rfl

theorem prod_eq_inf_comap (p : submodule R M) (q : submodule R M₂) :
  p.prod q = p.comap (linear_map.fst R M M₂) ⊓ q.comap (linear_map.snd R M M₂) :=
submodule.ext $ λ x, iff.rfl

theorem prod_eq_sup_map (p : submodule R M) (q : submodule R M₂) :
  p.prod q = p.map (linear_map.inl R M M₂) ⊔ q.map (linear_map.inr R M M₂) :=
by rw [← map_copair_prod, copair_inl_inr, map_id]

lemma span_inl_union_inr {s : set M} {t : set M₂} :
  span R (prod.inl '' s ∪ prod.inr '' t) = (span R s).prod (span R t) :=
by rw [span_union, prod_eq_sup_map, ← span_image, ← span_image]; refl

lemma ker_pair (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
  ker (pair f g) = ker f ⊓ ker g :=
by rw [ker, ← prod_bot, comap_pair_prod]; refl

end linear_map

namespace linear_map
variables [discrete_field 𝕜]
variables [add_comm_group V] [vector_space 𝕜 V]
variables [add_comm_group V₂] [vector_space 𝕜 V₂]

lemma ker_smul (f : V →ₗ[𝕜] V₂) (a : 𝕜) (h : a ≠ 0) : ker (a • f) = ker f :=
submodule.comap_smul f _ a h

lemma ker_smul' (f : V →ₗ[𝕜] V₂) (a : 𝕜) : ker (a • f) = ⨅(h : a ≠ 0), ker f :=
submodule.comap_smul' f _ a

lemma range_smul (f : V →ₗ[𝕜] V₂) (a : 𝕜) (h : a ≠ 0) : range (a • f) = range f :=
submodule.map_smul f _ a h

lemma range_smul' (f : V →ₗ[𝕜] V₂) (a : 𝕜) : range (a • f) = ⨆(h : a ≠ 0), range f :=
submodule.map_smul' f _ a

end linear_map

namespace is_linear_map

lemma is_linear_map_add {R M : Type*} [ring R] [add_comm_group M] [module R M]:
  is_linear_map R (λ (x : M × M), x.1 + x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp },
  { intros x y,
    simp [smul_add] }
end

lemma is_linear_map_sub {R M : Type*} [ring R] [add_comm_group M] [module R M]:
  is_linear_map R (λ (x : M × M), x.1 - x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp },
  { intros x y,
    simp [smul_add] }
end

end is_linear_map

namespace submodule
variables {T : ring R} [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
variables (p p' : submodule R M) (q : submodule R M₂)
include T
open linear_map

@[simp] theorem map_top (f : M →ₗ[R] M₂) : map f ⊤ = range f := rfl

@[simp] theorem comap_bot (f : M →ₗ[R] M₂) : comap f ⊥ = ker f := rfl

@[simp] theorem ker_subtype : p.subtype.ker = ⊥ :=
ker_eq_bot.2 $ λ x y, subtype.eq'

@[simp] theorem range_subtype : p.subtype.range = p :=
by simpa using map_comap_subtype p ⊤

lemma map_subtype_le (p' : submodule R p) : map p.subtype p' ≤ p :=
by simpa using (map_mono le_top : map p.subtype p' ≤ p.subtype.range)

@[simp] theorem ker_of_le (p p' : submodule R M) (h : p ≤ p') : (of_le h).ker = ⊥ :=
by rw [of_le, ker_cod_restrict, ker_subtype]

lemma range_of_le (p q : submodule R M) (h : p ≤ q) : (of_le h).range = comap q.subtype p :=
by rw [← map_top, of_le, linear_map.map_cod_restrict, map_top, range_subtype]

lemma disjoint_iff_comap_eq_bot (p q : submodule R M) :
  disjoint p q ↔ comap p.subtype q = ⊥ :=
by rw [eq_bot_iff, ← map_le_map_iff p.ker_subtype, map_bot, map_comap_subtype]; refl

/-- If N ⊆ M then submodules of N are the same as submodules of M contained in N -/
def map_subtype.order_iso :
  ((≤) : submodule R p → submodule R p → Prop) ≃o
  ((≤) : {p' : submodule R M // p' ≤ p} → {p' : submodule R M // p' ≤ p} → Prop) :=
{ to_fun    := λ p', ⟨map p.subtype p', map_subtype_le p _⟩,
  inv_fun   := λ q, comap p.subtype q,
  left_inv  := λ p', comap_map_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.eq' $ by simp [map_comap_subtype p, inf_of_le_right hq],
  ord       := λ p₁ p₂, (map_le_map_iff $ ker_subtype _).symm }

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of M. -/
def map_subtype.le_order_embedding :
  ((≤) : submodule R p → submodule R p → Prop) ≼o ((≤) : submodule R M → submodule R M → Prop) :=
(order_iso.to_order_embedding $ map_subtype.order_iso p).trans (subtype.order_embedding _ _)

@[simp] lemma map_subtype_embedding_eq (p' : submodule R p) :
  map_subtype.le_order_embedding p p' = map p.subtype p' := rfl

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of M. -/
def map_subtype.lt_order_embedding :
  ((<) : submodule R p → submodule R p → Prop) ≼o ((<) : submodule R M → submodule R M → Prop) :=
(map_subtype.le_order_embedding p).lt_embedding_of_le_embedding

@[simp] theorem map_inl : p.map (inl R M M₂) = prod p ⊥ :=
by ext ⟨x, y⟩; simp [and.left_comm, eq_comm]

@[simp] theorem map_inr : q.map (inr R M M₂) = prod ⊥ q :=
by ext ⟨x, y⟩; simp [and.left_comm, eq_comm]

@[simp] theorem comap_fst : p.comap (fst R M M₂) = prod p ⊤ :=
by ext ⟨x, y⟩; simp

@[simp] theorem comap_snd : q.comap (snd R M M₂) = prod ⊤ q :=
by ext ⟨x, y⟩; simp

@[simp] theorem prod_comap_inl : (prod p q).comap (inl R M M₂) = p := by ext; simp

@[simp] theorem prod_comap_inr : (prod p q).comap (inr R M M₂) = q := by ext; simp

@[simp] theorem prod_map_fst : (prod p q).map (fst R M M₂) = p :=
by ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ q)]

@[simp] theorem prod_map_snd : (prod p q).map (snd R M M₂) = q :=
by ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ p)]

@[simp] theorem ker_inl : (inl R M M₂).ker = ⊥ :=
by rw [ker, ← prod_bot, prod_comap_inl]

@[simp] theorem ker_inr : (inr R M M₂).ker = ⊥ :=
by rw [ker, ← prod_bot, prod_comap_inr]

@[simp] theorem range_fst : (fst R M M₂).range = ⊤ :=
by rw [range, ← prod_top, prod_map_fst]

@[simp] theorem range_snd : (snd R M M₂).range = ⊤ :=
by rw [range, ← prod_top, prod_map_snd]

/-- The map from a module `M` to the quotient of `M` by a submodule `p` is a linear map. -/
def mkq : M →ₗ[R] p.quotient := ⟨quotient.mk, by simp, by simp⟩

@[simp] theorem mkq_apply (x : M) : p.mkq x = quotient.mk x := rfl

/-- The map from the quotient of `M` by a submodule `p` to `M₂` along `f : M → M₂` is linear. -/
def liftq (f : M →ₗ[R] M₂) (h : p ≤ f.ker) : p.quotient →ₗ[R] M₂ :=
⟨λ x, _root_.quotient.lift_on' x f $
   λ a b (ab : a - b ∈ p), eq_of_sub_eq_zero $ by simpa using h ab,
 by rintro ⟨x⟩ ⟨y⟩; exact f.map_add x y,
 by rintro a ⟨x⟩; exact f.map_smul a x⟩

@[simp] theorem liftq_apply (f : M →ₗ[R] M₂) {h} (x : M) :
  p.liftq f h (quotient.mk x) = f x := rfl

@[simp] theorem liftq_mkq (f : M →ₗ[R] M₂) (h) : (p.liftq f h).comp p.mkq = f :=
by ext; refl

@[simp] theorem range_mkq : p.mkq.range = ⊤ :=
eq_top_iff'.2 $ by rintro ⟨x⟩; exact ⟨x, trivial, rfl⟩

@[simp] theorem ker_mkq : p.mkq.ker = p :=
by ext; simp

lemma le_comap_mkq (p' : submodule R p.quotient) : p ≤ comap p.mkq p' :=
by simpa using (comap_mono bot_le : p.mkq.ker ≤ comap p.mkq p')

@[simp] theorem mkq_map_self : map p.mkq p = ⊥ :=
by rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkq]; exact le_refl _

@[simp] theorem comap_map_mkq : comap p.mkq (map p.mkq p') = p ⊔ p' :=
by simp [comap_map_eq, sup_comm]

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapq (f : M →ₗ[R] M₂) (h : p ≤ comap f q) : p.quotient →ₗ[R] q.quotient :=
p.liftq (q.mkq.comp f) $ by simpa [ker_comp] using h

@[simp] theorem mapq_apply (f : M →ₗ[R] M₂) {h} (x : M) :
  mapq p q f h (quotient.mk x) = quotient.mk (f x) := rfl

theorem mapq_mkq (f : M →ₗ[R] M₂) {h} : (mapq p q f h).comp p.mkq = q.mkq.comp f :=
by ext x; refl

theorem comap_liftq (f : M →ₗ[R] M₂) (h) :
  q.comap (p.liftq f h) = (q.comap f).map (mkq p) :=
le_antisymm
  (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
  (by rw [map_le_iff_le_comap, ← comap_comp, liftq_mkq]; exact le_refl _)

theorem map_liftq (f : M →ₗ[R] M₂) (h) (q : submodule R (quotient p)) :
  q.map (p.liftq f h) = (q.comap p.mkq).map f :=
le_antisymm
  (by rintro _ ⟨⟨x⟩, hxq, rfl⟩; exact ⟨x, hxq, rfl⟩)
  (by rintro _ ⟨x, hxq, rfl⟩; exact ⟨quotient.mk x, hxq, rfl⟩)

theorem ker_liftq (f : M →ₗ[R] M₂) (h) :
  ker (p.liftq f h) = (ker f).map (mkq p) := comap_liftq _ _ _ _

theorem range_liftq (f : M →ₗ[R] M₂) (h) :
  range (p.liftq f h) = range f := map_liftq _ _ _ _

theorem ker_liftq_eq_bot (f : M →ₗ[R] M₂) (h) (h' : ker f ≤ p) : ker (p.liftq f h) = ⊥ :=
by rw [ker_liftq, le_antisymm h h', mkq_map_self]

/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
def comap_mkq.order_iso :
  ((≤) : submodule R p.quotient → submodule R p.quotient → Prop) ≃o
  ((≤) : {p' : submodule R M // p ≤ p'} → {p' : submodule R M // p ≤ p'} → Prop) :=
{ to_fun    := λ p', ⟨comap p.mkq p', le_comap_mkq p _⟩,
  inv_fun   := λ q, map p.mkq q,
  left_inv  := λ p', map_comap_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.eq' $ by simp [comap_map_mkq p, sup_of_le_right hq],
  ord       := λ p₁ p₂, (comap_le_comap_iff $ range_mkq _).symm }

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def comap_mkq.le_order_embedding :
  ((≤) : submodule R p.quotient → submodule R p.quotient → Prop) ≼o ((≤) : submodule R M → submodule R M → Prop) :=
(order_iso.to_order_embedding $ comap_mkq.order_iso p).trans (subtype.order_embedding _ _)

@[simp] lemma comap_mkq_embedding_eq (p' : submodule R p.quotient) :
  comap_mkq.le_order_embedding p p' = comap p.mkq p' := rfl

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def comap_mkq.lt_order_embedding :
  ((<) : submodule R p.quotient → submodule R p.quotient → Prop) ≼o ((<) : submodule R M → submodule R M → Prop) :=
(comap_mkq.le_order_embedding p).lt_embedding_of_le_embedding

end submodule

section
set_option old_structure_cmd true

/-- A linear equivalence is an invertible linear map. -/
structure linear_equiv (R : Type u) (M : Type v) (M₂ : Type w)
  [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
  extends M →ₗ[R] M₂, M ≃ M₂
end

infix ` ≃ₗ ` := linear_equiv _
notation M ` ≃ₗ[`:50 R `] ` M₂ := linear_equiv R M M₂

namespace linear_equiv
section ring
variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
include R

instance : has_coe (M ≃ₗ[R] M₂) (M →ₗ[R] M₂) := ⟨to_linear_map⟩

@[simp] theorem coe_apply (e : M ≃ₗ[R] M₂) (b : M) : (e : M →ₗ[R] M₂) b = e b := rfl

lemma to_equiv_injective : function.injective (to_equiv : (M ≃ₗ[R] M₂) → M ≃ M₂) :=
λ ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ h, linear_equiv.mk.inj_eq.mpr (equiv.mk.inj h)

@[extensionality] lemma ext {f g : M ≃ₗ[R] M₂} (h : (f : M → M₂) = g) : f = g :=
to_equiv_injective (equiv.eq_of_to_fun_eq h)

section
variable (M)

/-- The identity map is a linear equivalence. -/
def refl : M ≃ₗ[R] M := { .. linear_map.id, .. equiv.refl M }
end

/-- Linear equivalences are symmetric. -/
def symm (e : M ≃ₗ[R] M₂) : M₂ ≃ₗ[R] M :=
{ .. e.to_linear_map.inverse e.inv_fun e.left_inv e.right_inv,
  .. e.to_equiv.symm }

/-- Linear equivalences are transitive. -/
def trans (e₁ : M ≃ₗ[R] M₂) (e₂ : M₂ ≃ₗ[R] M₃) : M ≃ₗ[R] M₃ :=
{ .. e₂.to_linear_map.comp e₁.to_linear_map,
  .. e₁.to_equiv.trans e₂.to_equiv }

@[simp] theorem apply_symm_apply (e : M ≃ₗ[R] M₂) (c : M₂) : e (e.symm c) = c := e.6 c
@[simp] theorem symm_apply_apply (e : M ≃ₗ[R] M₂) (b : M) : e.symm (e b) = b := e.5 b

/-- A bijective linear map is a linear equivalence. Here, bijectivity is described by saying that
the kernel of `f` is `{0}` and the range is the universal set. -/
noncomputable def of_bijective
  (f : M →ₗ[R] M₂) (hf₁ : f.ker = ⊥) (hf₂ : f.range = ⊤) : M ≃ₗ[R] M₂ :=
{ ..f, ..@equiv.of_bijective _ _ f
  ⟨linear_map.ker_eq_bot.1 hf₁, linear_map.range_eq_top.1 hf₂⟩ }

@[simp] theorem of_bijective_apply (f : M →ₗ[R] M₂) {hf₁ hf₂} (x : M) :
  of_bijective f hf₁ hf₂ x = f x := rfl

/-- If a linear map has an inverse, it is a linear equivalence. -/
def of_linear (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M)
  (h₁ : f.comp g = linear_map.id) (h₂ : g.comp f = linear_map.id) : M ≃ₗ[R] M₂ :=
{ inv_fun   := g,
  left_inv  := linear_map.ext_iff.1 h₂,
  right_inv := linear_map.ext_iff.1 h₁,
  ..f }

@[simp] theorem of_linear_apply (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M) {h₁ h₂}
  (x : M) : of_linear f g h₁ h₂ x = f x := rfl

@[simp] theorem of_linear_symm_apply (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M) {h₁ h₂}
  (x : M₂) : (of_linear f g h₁ h₂).symm x = g x := rfl

@[simp] protected theorem ker (f : M ≃ₗ[R] M₂) : (f : M →ₗ[R] M₂).ker = ⊥ :=
linear_map.ker_eq_bot.2 f.to_equiv.injective

@[simp] protected theorem range (f : M ≃ₗ[R] M₂) : (f : M →ₗ[R] M₂).range = ⊤ :=
linear_map.range_eq_top.2 f.to_equiv.surjective

/-- The top submodule of `M` is linearly equivalent to `M`. -/
def of_top (p : submodule R M) (h : p = ⊤) : p ≃ₗ[R] M :=
{ inv_fun   := λ x, ⟨x, h.symm ▸ trivial⟩,
  left_inv  := λ ⟨x, h⟩, rfl,
  right_inv := λ x, rfl,
  .. p.subtype }

@[simp] theorem of_top_apply (p : submodule R M) {h} (x : p) :
  of_top p h x = x := rfl

@[simp] theorem of_top_symm_apply (p : submodule R M) {h} (x : M) :
  ↑((of_top p h).symm x) = x := rfl

lemma eq_bot_of_equiv (p : submodule R M) (e : p ≃ₗ[R] (⊥ : submodule R M₂)) :
  p = ⊥ :=
begin
  refine bot_unique (submodule.le_def'.2 $ assume b hb, (submodule.mem_bot R).2 _),
  have := e.symm_apply_apply ⟨b, hb⟩,
  rw [← e.coe_apply, submodule.eq_zero_of_bot_submodule ((e : p →ₗ[R] (⊥ : submodule R M₂)) ⟨b, hb⟩),
    ← e.symm.coe_apply, linear_map.map_zero] at this,
  exact congr_arg (coe : p → M) this.symm
end

end ring

section comm_ring
variables [comm_ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
include R
open linear_map

set_option class.instance_max_depth 39

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smul_of_unit (a : units R) : M ≃ₗ[R] M :=
of_linear ((a:R) • 1 : M →ₗ M) (((a⁻¹ : units R) : R) • 1 : M →ₗ M)
  (by rw [smul_comp, comp_smul, smul_smul, units.mul_inv, one_smul]; refl)
  (by rw [smul_comp, comp_smul, smul_smul, units.inv_mul, one_smul]; refl)

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrow_congr {R M₁ M₂ M₂₁ M₂₂ : Sort*} [comm_ring R]
  [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₂₁] [add_comm_group M₂₂]
  [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) :
  (M₁ →ₗ[R] M₂₁) ≃ₗ[R] (M₂ →ₗ[R] M₂₂) :=
{ to_fun := λ f, e₂.to_linear_map.comp $ f.comp e₁.symm.to_linear_map,
  inv_fun := λ f, e₂.symm.to_linear_map.comp $ f.comp e₁.to_linear_map,
  left_inv := λ f, by { ext x, unfold_coes,
    change e₂.inv_fun (e₂.to_fun $ f.to_fun $ e₁.inv_fun $ e₁.to_fun x) = _,
    rw [e₁.left_inv, e₂.left_inv] },
  right_inv := λ f, by { ext x, unfold_coes,
    change e₂.to_fun (e₂.inv_fun $ f.to_fun $ e₁.to_fun $ e₁.inv_fun x) = _,
    rw [e₁.right_inv, e₂.right_inv] },
  add := λ f g, by { ext x, change e₂.to_fun ((f + g) (e₁.inv_fun x)) = _,
    rw [linear_map.add_apply, e₂.add], refl },
  smul := λ c f, by { ext x, change e₂.to_fun ((c • f) (e₁.inv_fun x)) = _,
    rw [linear_map.smul_apply, e₂.smul], refl } }

/-- If M₂ and M₃ are linearly isomorphic then the two spaces of linear maps from M into M₂ and
M into M₃ are linearly isomorphic. -/
def congr_right (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ (M →ₗ M₃) := arrow_congr (linear_equiv.refl M) f

/-- If M and M₂ are linearly isomorphic then the two spaces of linear maps from M and M₂ to themselves
are linearly isomorphic. -/
def conj (e : M ≃ₗ[R] M₂) : (M →ₗ[R] M) ≃ₗ[R] (M₂ →ₗ[R] M₂) := arrow_congr e e

end comm_ring

section field
variables [field 𝕜] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module 𝕜 M] [module 𝕜 M₂] [module 𝕜 M₃]
variable (M)
open linear_map

/-- Multiplying by a nonzero element `a` of the field `𝕜` is a linear equivalence. -/
def smul_of_ne_zero (a : 𝕜) (ha : a ≠ 0) : M ≃ₗ[𝕜] M :=
smul_of_unit $ units.mk0 a ha

end field

end linear_equiv

namespace equiv
variables [ring R] [add_comm_group M] [module R M] [add_comm_group M₂] [module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def to_linear_equiv (e : M ≃ M₂) (h : is_linear_map R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
{ add := h.add, smul := h.smul, .. e}

end equiv

namespace linear_map
variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
variables (f : M →ₗ[R] M₂)

/-- The first isomorphism law for modules. The quotient of `M` by the kernel of `f` is linearly
equivalent to the range of `f`.  -/
noncomputable def quot_ker_equiv_range : f.ker.quotient ≃ₗ[R] f.range :=
have hr : ∀ x : f.range, ∃ y, f y = ↑x := λ x, x.2.imp $ λ _, and.right,
let F : f.ker.quotient →ₗ[R] f.range :=
  f.ker.liftq (cod_restrict f.range f $ λ x, ⟨x, trivial, rfl⟩)
    (λ x hx, by simp; apply subtype.coe_ext.2; simpa using hx) in
{ inv_fun    := λx, submodule.quotient.mk (classical.some (hr x)),
  left_inv   := by rintro ⟨x⟩; exact
    (submodule.quotient.eq _).2 (sub_mem_ker_iff.2 $
      classical.some_spec $ hr $ F $ submodule.quotient.mk x),
  right_inv  := λ x : range f, subtype.eq $ classical.some_spec (hr x),
  .. F }

open submodule

def sup_quotient_to_quotient_inf (p p' : submodule R M) :
  (comap p.subtype (p ⊓ p')).quotient →ₗ[R] (comap (p ⊔ p').subtype p').quotient :=
(comap p.subtype (p ⊓ p')).liftq
  ((comap (p ⊔ p').subtype p').mkq.comp (of_le le_sup_left)) begin
rw [ker_comp, of_le, comap_cod_restrict, ker_mkq, map_comap_subtype],
exact comap_mono (inf_le_inf le_sup_left (le_refl _)) end

set_option class.instance_max_depth 41

/-- Second Isomorphism Law -/
noncomputable def sup_quotient_equiv_quotient_inf (p p' : submodule R M) :
  (comap p.subtype (p ⊓ p')).quotient ≃ₗ[R] (comap (p ⊔ p').subtype p').quotient :=
{ .. sup_quotient_to_quotient_inf p p',
  .. show (comap p.subtype (p ⊓ p')).quotient ≃ (comap (p ⊔ p').subtype p').quotient, from
    @equiv.of_bijective _ _ (sup_quotient_to_quotient_inf p p') begin
      constructor,
      { rw [← ker_eq_bot, sup_quotient_to_quotient_inf, ker_liftq_eq_bot],
        rw [ker_comp, ker_mkq],
        rintros ⟨x, hx1⟩ hx2, exact ⟨hx1, hx2⟩ },
      rw [← range_eq_top, sup_quotient_to_quotient_inf, range_liftq, eq_top_iff'],
      rintros ⟨x, hx⟩, rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩,
      use [⟨y, hy⟩, trivial], apply (submodule.quotient.eq _).2,
      change y - (y + z) ∈ p', rwa [sub_add_eq_sub_sub, sub_self, zero_sub, neg_mem_iff]
    end }

section prod

/-- The product of two linear maps is a linear map. -/
def prod {R M M₂ M₃ : Type*} [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
  [module R M] [module R M₂] [module R M₃]
  (f₁ : M →ₗ[R] M₂) (f₂ : M →ₗ[R] M₃) : M →ₗ[R] (M₂ × M₃) :=
{ to_fun := λx, (f₁ x, f₂ x),
  add := λx y, begin
    change (f₁ (x + y), f₂ (x+y)) = (f₁ x, f₂ x) + (f₁ y, f₂ y),
    simp only [linear_map.map_add],
    refl
  end,
  smul := λc x, by simp only [linear_map.map_smul] }

lemma is_linear_map_prod_iso {R M M₂ M₃ : Type*} [comm_ring R] [add_comm_group M] [add_comm_group M₂]
  [add_comm_group M₃] [module R M] [module R M₂] [module R M₃] :
  is_linear_map R (λ(p : (M →ₗ[R] M₂) × (M →ₗ[R] M₃)), (linear_map.prod p.1 p.2 : (M →ₗ[R] (M₂ × M₃)))) :=
⟨λu v, rfl, λc u, rfl⟩

/-- The product by a linear map into the scalar ring is a linear map. -/
def scalar_prod_space_iso {R M M₂ : Type*} [comm_ring R] [add_comm_group M] [add_comm_group M₂]
  [module R M] [module R M₂] (c : M →ₗ[R] R) (f : M₂) : M →ₗ[R] M₂ :=
{ to_fun := λx, (c x) • f,
  add := λx y, begin
    change c (x + y) • f = (c x) • f + (c y) • f,
    simp [add_smul],
  end,
  smul := λa x, by simp [smul_smul] }

end prod

section pi
universe i
variables {φ : ι → Type i}
variables [∀i, add_comm_group (φ i)] [∀i, module R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : Πi, M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (Πi, φ i) :=
⟨λc i, f i c,
  assume c d, funext $ assume i, (f i).add _ _, assume c d, funext $ assume i, (f i).smul _ _⟩

@[simp] lemma pi_apply (f : Πi, M₂ →ₗ[R] φ i) (c : M₂) (i : ι) :
  pi f c i = f i c := rfl

lemma ker_pi (f : Πi, M₂ →ₗ[R] φ i) : ker (pi f) = (⨅i:ι, ker (f i)) :=
by ext c; simp [funext_iff]; refl

lemma pi_eq_zero (f : Πi, M₂ →ₗ[R] φ i) : pi f = 0 ↔ (∀i, f i = 0) :=
by simp only [linear_map.ext_iff, pi_apply, funext_iff]; exact ⟨λh a b, h b a, λh a b, h b a⟩

lemma pi_zero : pi (λi, 0 : Πi, M₂ →ₗ[R] φ i) = 0 :=
by ext; refl

lemma pi_comp (f : Πi, M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) : (pi f).comp g = pi (λi, (f i).comp g) :=
rfl

/-- The projections from a family of modules are linear maps. -/
def proj (i : ι) : (Πi, φ i) →ₗ[R] φ i :=
⟨ λa, a i, assume f g, rfl, assume c f, rfl ⟩

@[simp] lemma proj_apply (i : ι) (b : Πi, φ i) : (proj i : (Πi, φ i) →ₗ[R] φ i) b = b i := rfl

lemma proj_pi (f : Πi, M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
ext $ assume c, rfl

lemma infi_ker_proj : (⨅i, ker (proj i) : submodule R (Πi, φ i)) = ⊥ :=
bot_unique $ submodule.le_def'.2 $ assume a h,
begin
  simp only [mem_infi, mem_ker, proj_apply] at h,
  exact (mem_bot _).2 (funext $ assume i, h i)
end

section
variables (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def infi_ker_proj_equiv {I J : set ι} [decidable_pred (λi, i ∈ I)]
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) :
  (⨅i ∈ J, ker (proj i) : submodule R (Πi, φ i)) ≃ₗ[R] (Πi:I, φ i) :=
begin
  refine linear_equiv.of_linear
    (pi $ λi, (proj (i:ι)).comp (submodule.subtype _))
    (cod_restrict _ (pi $ λi, if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) _) _ _,
  { assume b,
    simp only [mem_infi, mem_ker, funext_iff, proj_apply, pi_apply],
    assume j hjJ,
    have : j ∉ I := assume hjI, hd ⟨hjI, hjJ⟩,
    rw [dif_neg this, zero_apply] },
  { simp only [pi_comp, comp_assoc, subtype_comp_cod_restrict, proj_pi, dif_pos, subtype.val_prop'],
    ext b ⟨j, hj⟩, refl },
  { ext ⟨b, hb⟩,
    apply subtype.coe_ext.2,
    ext j,
    have hb : ∀i ∈ J, b i = 0,
    { simpa only [mem_infi, mem_ker, proj_apply] using (mem_infi _).1 hb },
    simp only [comp_apply, pi_apply, id_apply, proj_apply, subtype_apply, cod_restrict_apply],
    split_ifs,
    { rw [dif_pos h], refl },
    { rw [dif_neg h],
      exact (hb _ $ (hu trivial).resolve_left h).symm } }
end
end

section
variable [decidable_eq ι]

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
@function.update ι (λj, φ i →ₗ[R] φ j) _ 0 i id j

lemma update_apply (f : Πi, M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
  (update f i b j) c = update (λi, f i c) i (b c) j :=
begin
  by_cases j = i,
  { rw [h, update_same, update_same] },
  { rw [update_noteq h, update_noteq h] }
end

end

section
variable [decidable_eq ι]
variables (R φ)

/-- The standard basis of the product of `φ`. -/
def std_basis (i : ι) : φ i →ₗ[R] (Πi, φ i) := pi (diag i)

lemma std_basis_apply (i : ι) (b : φ i) : std_basis R φ i b = update 0 i b :=
by ext j; rw [std_basis, pi_apply, diag, update_apply]; refl

@[simp] lemma std_basis_same (i : ι) (b : φ i) : std_basis R φ i b i = b :=
by rw [std_basis_apply, update_same]

lemma std_basis_ne (i j : ι) (h : j ≠ i) (b : φ i) : std_basis R φ i b j = 0 :=
by rw [std_basis_apply, update_noteq h]; refl

lemma ker_std_basis (i : ι) : ker (std_basis R φ i) = ⊥ :=
ker_eq_bot.2 $ assume f g hfg,
  have std_basis R φ i f i = std_basis R φ i g i := hfg ▸ rfl,
  by simpa only [std_basis_same]

lemma proj_comp_std_basis (i j : ι) : (proj i).comp (std_basis R φ j) = diag j i :=
by rw [std_basis, proj_pi]

lemma proj_std_basis_same (i : ι) : (proj i).comp (std_basis R φ i) = id :=
by ext b; simp

lemma proj_std_basis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (std_basis R φ j) = 0 :=
by ext b; simp [std_basis_ne R φ _ _ h]

lemma supr_range_std_basis_le_infi_ker_proj (I J : set ι) (h : disjoint I J) :
  (⨆i∈I, range (std_basis R φ i)) ≤ (⨅i∈J, ker (proj i)) :=
begin
  refine (supr_le $ assume i, supr_le $ assume hi, range_le_iff_comap.2 _),
  simp only [(ker_comp _ _).symm, eq_top_iff, le_def', mem_ker, comap_infi, mem_infi],
  assume b hb j hj,
  have : i ≠ j := assume eq, h ⟨hi, eq.symm ▸ hj⟩,
  rw [proj_std_basis_ne R φ j i this.symm, zero_apply]
end

lemma infi_ker_proj_le_supr_range_std_basis {I : finset ι} {J : set ι} (hu : set.univ ⊆ ↑I ∪ J) :
  (⨅ i∈J, ker (proj i)) ≤ (⨆i∈I, range (std_basis R φ i)) :=
submodule.le_def'.2
begin
  assume b hb,
  simp only [mem_infi, mem_ker, proj_apply] at hb,
  rw ← show I.sum (λi, std_basis R φ i (b i)) = b,
  { ext i,
    rw [pi.finset_sum_apply, ← std_basis_same R φ i (b i)],
    refine finset.sum_eq_single i (assume j hjI ne, std_basis_ne _ _ _ _ ne.symm _) _,
    assume hiI,
    rw [std_basis_same],
    exact hb _ ((hu trivial).resolve_left hiI) },
  exact sum_mem _ (assume i hiI, mem_supr_of_mem _ i $ mem_supr_of_mem _ hiI $
    linear_map.mem_range.2 ⟨_, rfl⟩)
end

lemma supr_range_std_basis_eq_infi_ker_proj {I J : set ι}
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) (hI : set.finite I) :
  (⨆i∈I, range (std_basis R φ i)) = (⨅i∈J, ker (proj i)) :=
begin
  refine le_antisymm (supr_range_std_basis_le_infi_ker_proj _ _ _ _ hd) _,
  have : set.univ ⊆ ↑hI.to_finset ∪ J, { rwa [finset.coe_to_finset] },
  refine le_trans (infi_ker_proj_le_supr_range_std_basis R φ this) (supr_le_supr $ assume i, _),
  rw [← finset.mem_coe, finset.coe_to_finset],
  exact le_refl _
end

lemma supr_range_std_basis [fintype ι] : (⨆i:ι, range (std_basis R φ i)) = ⊤ :=
have (set.univ : set ι) ⊆ ↑(finset.univ : finset ι) ∪ ∅ := by rw [finset.coe_univ, set.union_empty],
begin
  apply top_unique,
  convert (infi_ker_proj_le_supr_range_std_basis R φ this),
  exact infi_emptyset.symm,
  exact (funext $ λi, (@supr_pos _ _ _ (λh, range (std_basis R φ i)) $ finset.mem_univ i).symm)
end

lemma disjoint_std_basis_std_basis (I J : set ι) (h : disjoint I J) :
  disjoint (⨆i∈I, range (std_basis R φ i)) (⨆i∈J, range (std_basis R φ i)) :=
begin
  refine disjoint_mono
    (supr_range_std_basis_le_infi_ker_proj _ _ _ _ $ set.disjoint_compl I)
    (supr_range_std_basis_le_infi_ker_proj _ _ _ _ $ set.disjoint_compl J) _,
  simp only [disjoint, submodule.le_def', mem_infi, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff],
  rintros b ⟨hI, hJ⟩ i,
  classical,
  by_cases hiI : i ∈ I,
  { by_cases hiJ : i ∈ J,
    { exact (h ⟨hiI, hiJ⟩).elim },
    { exact hJ i hiJ } },
  { exact hI i hiI }
end

lemma std_basis_eq_single {a : R} :
  (λ (i : ι), (std_basis R (λ _ : ι, R) i) a) = λ (i : ι), (finsupp.single i a) :=
begin
  ext i j,
  rw [std_basis_apply, finsupp.single_apply],
  split_ifs,
  { rw [h, function.update_same] },
  { rw [function.update_noteq (ne.symm h)], refl },
end

end

end pi

variables (R M)

instance automorphism_group : group (M ≃ₗ[R] M) :=
{ mul := λ f g, g.trans f,
  one := linear_equiv.refl M,
  inv := λ f, f.symm,
  mul_assoc := λ f g h, by {ext, refl},
  mul_one := λ f, by {ext, refl},
  one_mul := λ f, by {ext, refl},
  mul_left_inv := λ f, by {ext, exact f.left_inv x} }

instance automorphism_group.to_linear_map_is_monoid_hom :
  is_monoid_hom (linear_equiv.to_linear_map : (M ≃ₗ[R] M) → (M →ₗ[R] M)) :=
{ map_one := rfl,
  map_mul := λ f g, rfl }

/-- The group of invertible linear maps from `M` to itself -/
def general_linear_group := units (M →ₗ[R] M)

namespace general_linear_group
variables {R M}

instance : group (general_linear_group R M) := by delta general_linear_group; apply_instance

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
def to_linear_equiv (f : general_linear_group R M) : (M ≃ₗ[R] M) :=
{ inv_fun := f.inv.to_fun,
  left_inv := λ m, show (f.inv * f.val) m = m,
    by erw f.inv_val; simp,
  right_inv := λ m, show (f.val * f.inv) m = m,
    by erw f.val_inv; simp,
  ..f.val }

/-- An equivalence from `M` to itself determines an invertible linear map. -/
def of_linear_equiv (f : (M ≃ₗ[R] M)) : general_linear_group R M :=
{ val := f,
  inv := f.symm,
  val_inv := linear_map.ext $ λ _, f.apply_symm_apply _,
  inv_val := linear_map.ext $ λ _, f.symm_apply_apply _ }

variables (R M)

/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
def general_linear_equiv : general_linear_group R M ≃* (M ≃ₗ[R] M) :=
{ to_fun := to_linear_equiv,
  inv_fun := of_linear_equiv,
  left_inv := λ f,
  begin
    delta to_linear_equiv of_linear_equiv,
    cases f with f f_inv, cases f, cases f_inv,
    congr
  end,
  right_inv := λ f,
  begin
    delta to_linear_equiv of_linear_equiv,
    cases f,
    congr
  end,
  map_mul' := λ x y, by {ext, refl} }

@[simp] lemma general_linear_equiv_to_linear_map (f : general_linear_group R M) :
  ((general_linear_equiv R M).to_equiv f).to_linear_map = f.val :=
by {ext, refl}

end general_linear_group

end linear_map
