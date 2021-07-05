/-
Copyright (c) 2021 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.subrepre
import linear_algebra.basic

/-!
Closely follows linear_algebra.basic
-/

open function
open_locale big_operators

namespace repre_hom

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]
  [add_comm_monoid M₃] [module k M₃] [repre k G M₃]
  (f g : M →ᵣ[k;G] M₂)
include k

/-- The restriction of a repre_hom `f : M → M₂` to a subrepre `p ⊆ M` gives a repre_hom `p → M₂`. -/
def dom_restrict (f : M →ᵣ[k;G] M₂) (p : subrepre k G M) : p →ᵣ[k;G] M₂ := f.comp p.subtype

@[simp] lemma dom_restrict_apply (f : M →ᵣ[k;G] M₂) (p : subrepre k G M) (x : p) :
  f.dom_restrict p x = f x := rfl

/-- A repre_hom `f : M₂ → M` whose values lie in a subrepre `p ⊆ M` can be restricted to a repre_hom M₂ → p. -/
def cod_restrict (p : subrepre k G M) (f : M₂ →ᵣ[k;G] M) (h : ∀c, f c ∈ p) : M₂ →ᵣ[k;G] p :=
begin
  refine {..linear_map.cod_restrict p.to_submodule f.to_linear_map h, ..},
  intros,
  ext,
  rw subrepre.coe_smul2,
  simp
end

@[simp] theorem cod_restrict_apply (p : subrepre k G M) (f : M₂ →ᵣ[k;G] M) {h} (x : M₂) :
  (cod_restrict p f h x : M) = f x := rfl

@[simp] lemma comp_cod_restrict (p : subrepre k G M₂) (h : ∀b, f b ∈ p) (g : M₃ →ᵣ[k;G] M) :
  (cod_restrict p f h).comp g = cod_restrict p (f.comp g) (assume b, h _) :=
ext $ assume b, rfl

@[simp] lemma subtype_comp_cod_restrict (p : subrepre k G M₂) (h : ∀b, f b ∈ p) :
  p.subtype.comp (cod_restrict p f h) = f :=
ext $ assume b, rfl

/-- Restrict domain and codomain of an endomorphism. -/
def restrict (f : M →ᵣ[k;G] M) {p : subrepre k G M} (hf : ∀ x ∈ p, f x ∈ p) : p →ᵣ[k;G] p :=
(f.dom_restrict p).cod_restrict p $ set_like.forall.2 hf

lemma restrict_apply
  {f : M →ᵣ[k;G] M} {p : subrepre k G M} (hf : ∀ x ∈ p, f x ∈ p) (x : p) :
  f.restrict hf x = ⟨f x, hf x.1 x.2⟩ := rfl

lemma subtype_comp_restrict {f : M →ᵣ[k;G] M} {p : subrepre k G M} (hf : ∀ x ∈ p, f x ∈ p) :
  p.subtype.comp (f.restrict hf) = f.dom_restrict p := rfl

lemma restrict_eq_cod_restrict_dom_restrict
  {f : M →ᵣ[k;G] M} {p : subrepre k G M} (hf : ∀ x ∈ p, f x ∈ p) :
  f.restrict hf = (f.dom_restrict p).cod_restrict p (λ x, hf x.1 x.2) := rfl

lemma restrict_eq_dom_restrict_cod_restrict
  {f : M →ᵣ[k;G] M} {p : subrepre k G M} (hf : ∀ x, f x ∈ p) :
  f.restrict (λ x _, hf x) = (f.cod_restrict p hf).dom_restrict p := rfl

end repre_hom












namespace subrepre

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]
  [add_comm_monoid M₃] [module k M₃] [repre k G M₃]
  (p p' : subrepre k G M) (q q' : subrepre k G M₂)
  {r : k} {g : G} {x y : M}

open set

variables {p p'}

/-- If two subrepresentations `p` and `p'` satisfy `p ⊆ p'`, then `of_le p p'` is the repre_hom version of
this inclusion. -/
def of_le (h : p ≤ p') : p →ᵣ[k;G] p' :=
p.subtype.cod_restrict p' $ λ ⟨x, hx⟩, h hx

@[simp] theorem coe_of_le (h : p ≤ p') (x : p) :
  (of_le h x : M) = x := rfl

theorem of_le_apply (h : p ≤ p') (x : p) : of_le h x = ⟨x, h x.2⟩ := rfl

variables (p p')

lemma subtype_comp_of_le (p q : subrepre k G M) (h : p ≤ q) :
  q.subtype.comp (of_le h) = p.subtype :=
by { ext ⟨b, hb⟩, refl }

instance lattice_add_comm_monoid : add_comm_monoid (subrepre k G M) :=
{ add := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero := ⊥,
  zero_add := λ _, bot_sup_eq,
  add_zero := λ _, sup_bot_eq,
  add_comm := λ _ _, sup_comm }

@[simp] lemma add_eq_sup (p q : subrepre k G M) : p + q = p ⊔ q := rfl
@[simp] lemma zero_eq_bot : (0 : subrepre k G M) = ⊥ := rfl

variable (k)

lemma subsingleton_iff : subsingleton M ↔ subsingleton (subrepre k G M) :=
add_submonoid.subsingleton_iff.trans $ begin
  rw [←subsingleton_iff_bot_eq_top, ←subsingleton_iff_bot_eq_top],
  convert to_add_submonoid_eq, refl, refl
end

lemma nontrivial_iff : nontrivial M ↔ nontrivial (subrepre k G M) :=
not_iff_not.mp (
  (not_nontrivial_iff_subsingleton.trans $ subsingleton_iff k).trans
  not_nontrivial_iff_subsingleton.symm)

variable {k}

instance [subsingleton M] : unique (subrepre k G M) :=
⟨⟨⊥⟩, λ a, @subsingleton.elim _ ((subsingleton_iff k).mp ‹_›) a _⟩

instance unique' [subsingleton k] : unique (subrepre k G M) :=
by {haveI := repre.subsingleton k G M, apply_instance}

instance [nontrivial M] : nontrivial (subrepre k G M) := (nontrivial_iff k).mp ‹_›

theorem disjoint_def {p p' : subrepre k G M} :
  disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0:M) :=
show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : set M)) ↔ _, by simp

theorem disjoint_def' {p p' : subrepre k G M} :
  disjoint p p' ↔ ∀ (x ∈ p) (y ∈ p'), x = y → x = (0:M) :=
disjoint_def.trans ⟨λ h x hx y hy hxy, h x hx $ hxy.symm ▸ hy,
  λ h x hx hx', h _ hx x hx' rfl⟩

theorem mem_right_iff_eq_zero_of_disjoint {p p' : subrepre k G M} (h : disjoint p p') {x : p} :
  (x:M) ∈ p' ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x x.2 hx, λ h, h.symm ▸ p'.zero_mem⟩

theorem mem_left_iff_eq_zero_of_disjoint {p p' : subrepre k G M} (h : disjoint p p') {x : p'} :
  (x:M) ∈ p ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x hx x.2, λ h, h.symm ▸ p.zero_mem⟩

/-- The pushforward of a subrepresentation `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ᵣ[k;G] M₂) (p : subrepre k G M) : subrepre k G M₂ :=
{ smul_mem2' :=
  begin
    intros g x₂,
    simp,
    intros x h1 h2,
    existsi g • x,
    split,
    { apply p.smul_mem2',
      simp,
      exact h1 },
    { simp,
      rw h2 }
  end,
  .. p.to_submodule.map f.to_linear_map }

@[simp] lemma map_coe (f : M →ᵣ[k;G] M₂) (p : subrepre k G M) :
  (map f p : set M₂) = f '' p := rfl

@[simp] lemma mem_map {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} {x : M₂} :
  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x := iff.rfl

theorem mem_map_of_mem {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} {r} (h : r ∈ p) : f r ∈ map f p :=
set.mem_image_of_mem _ h

lemma apply_coe_mem_map (f : M →ᵣ[k;G] M₂) {p : subrepre k G M} (r : p) : f r ∈ map f p :=
mem_map_of_mem r.prop

@[simp] lemma map_id (p : subrepre k G M) : map repre_hom.id p = p :=
subrepre.ext $ λ a, by simp

lemma map_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) (p : subrepre k G M) :
  map (g.comp f) p = map g (map f p) :=
set_like.coe_injective $ by simp [map_coe]; rw ← set.image_comp

lemma map_mono {f : M →ᵣ[k;G] M₂} {p p' : subrepre k G M} : p ≤ p' → map f p ≤ map f p' :=
set.image_subset _

@[simp] lemma map_zero_eq_bot (p : subrepre k G M) : map (0 : M →ᵣ[k;G] M₂) p = ⊥ :=
begin
  have : ∃ (x : M), x ∈ p,
  { existsi (0 : M), simp },
  ext,
  simp [this, eq_comm]
end

/- range_map_nonempty skipped -/

/-- An injective repre_hom gives a repre_iso between the domain and the range. -/
@[simps]
noncomputable def equiv_map_of_injective (f : M →ᵣ[k;G] M₂) (i : function.injective f) (p : subrepre k G M) :
  p ≃ᵣ[k;G] p.map f :=
{ map_add' := by { intros, simp, refl },
  map_smul' := by { intros, simp [subrepre.coe_smul], refl },
  map_smul2' := by { intros, simp [subrepre.coe_smul2], refl },
  ..(equiv.set.image f p i) }

/-- The pullback of a subrepresentation `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : M →ᵣ[k;G] M₂) (p : subrepre k G M₂) : subrepre k G M :=
{ carrier   := f ⁻¹' p,
  smul_mem2' := by
  { intros g x,
    simp,
    apply smul_mem2' },
  .. p.to_submodule.comap f.to_linear_map }

@[simp] lemma comap_coe (f : M →ᵣ[k;G] M₂) (p : subrepre k G M₂) :
  (comap f p : set M) = f ⁻¹' p := rfl

@[simp] lemma mem_comap {f : M →ᵣ[k;G] M₂} {p : subrepre k G M₂} :
  ∀ x, x ∈ comap f p ↔ f x ∈ p := λ x, iff.rfl

lemma comap_id (p : subrepre k G M) : comap repre_hom.id p = p :=
set_like.coe_injective rfl

lemma comap_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) (p : subrepre k G M₃) :
  comap (g.comp f) p = comap f (comap g p) := rfl

lemma comap_mono {f : M →ᵣ[k;G] M₂} {q q' : subrepre k G M₂} : q ≤ q' → comap f q ≤ comap f q' :=
set.preimage_mono

lemma map_le_iff_le_comap {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} {q : subrepre k G M₂} :
  map f p ≤ q ↔ p ≤ comap f q := set.image_subset_iff

lemma gc_map_comap (f : M →ᵣ[k;G] M₂) : galois_connection (map f) (comap f)
| p q := map_le_iff_le_comap

@[simp] lemma map_bot (f : M →ᵣ[k;G] M₂) : map f ⊥ = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma map_sup (p p' : subrepre k G M) (f : M →ᵣ[k;G] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
(gc_map_comap f).l_sup

@[simp] lemma map_supr {ι : Sort*} (f : M →ᵣ[k;G] M₂) (p : ι → subrepre k G M) :
  map f (⨆i, p i) = (⨆i, map f (p i)) :=
(gc_map_comap f).l_supr

@[simp] lemma comap_top (f : M →ᵣ[k;G] M₂) : comap f ⊤ = ⊤ := rfl

@[simp] lemma comap_inf (q q' : subrepre k G M₂) (f : M →ᵣ[k;G] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' := rfl

@[simp] lemma comap_infi {ι : Sort*} (f : M →ᵣ[k;G] M₂) (p : ι → subrepre k G M₂) :
  comap f (⨅i, p i) = (⨅i, comap f (p i)) :=
(gc_map_comap f).u_infi

@[simp] lemma comap_zero (q : subrepre k G M₂) : comap (0 : M →ᵣ[k;G] M₂) q = ⊤ :=
ext $ by simp

lemma map_comap_le (f : M →ᵣ[k;G] M₂) (q : subrepre k G M₂) : map f (comap f q) ≤ q :=
(gc_map_comap f).l_u_le _

lemma le_comap_map (f : M →ᵣ[k;G] M₂) (p : subrepre k G M) : p ≤ comap f (map f p) :=
(gc_map_comap f).le_u_l _

end subrepre

namespace repre_hom

section add_comm_monoid

open subrepre

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]
  [add_comm_monoid M₃] [module k M₃] [repre k G M₃]
  (p p' : subrepre k G M) (q q' : subrepre k G M₂)
  {r : k} {g : G} {x y : M}

theorem map_cod_restrict (p : subrepre k G M) (f : M₂ →ᵣ[k;G] M) (h p') :
  subrepre.map (cod_restrict p f h) p' = comap p.subtype (p'.map f) :=
subrepre.ext $ λ ⟨x, hx⟩, by simp [subtype.ext_iff_val]

theorem comap_cod_restrict (p : subrepre k G M) (f : M₂ →ᵣ[k;G] M) (hf p') :
  subrepre.comap (cod_restrict p f hf) p' = subrepre.comap f (map p.subtype p') :=
subrepre.ext $ λ x, ⟨λ h, ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

/-- The range of a repre_hom `f : M → M₂` is a subrepresentation of `M₂`. -/
def range (f : M →ᵣ[k;G] M₂) : subrepre k G M₂ :=
(subrepre.map f ⊤).copy (set.range f) set.image_univ.symm

theorem range_coe (f : M →ᵣ[k;G] M₂) : (range f : set M₂) = set.range f := rfl

@[simp] theorem mem_range {f : M →ᵣ[k;G] M₂} {x} : x ∈ range f ↔ ∃ y, f y = x :=
iff.rfl

lemma range_eq_map (f : M →ᵣ[k;G] M₂) : range f = subrepre.map f ⊤ :=
by { ext, simp }

theorem mem_range_self (f : M →ᵣ[k;G] M₂) (x : M) : f x ∈ range f := ⟨x, rfl⟩

@[simp] theorem range_id : range (repre_hom.id : M →ᵣ[k;G] M) = ⊤ :=
set_like.coe_injective set.range_id

theorem range_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) : range (g.comp f) = subrepre.map g (range f) :=
set_like.coe_injective (set.range_comp g f)

theorem range_comp_le_range (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) : range (g.comp f) ≤ range g :=
set_like.coe_mono (set.range_comp_subset_range f g)

theorem range_eq_top {f : M →ᵣ[k;G] M₂} : range f = ⊤ ↔ function.surjective f :=
by rw [set_like.ext'_iff, range_coe, subrepre.top_coe, set.range_iff_surjective]

lemma range_le_iff_comap {f : M →ᵣ[k;G] M₂} {p : subrepre k G M₂} : range f ≤ p ↔ subrepre.comap f p = ⊤ :=
by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

lemma map_le_range {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} : subrepre.map f p ≤ range f :=
set_like.coe_mono (set.image_subset_range f p)

@[reducible] def range_restrict (f : M →ᵣ[k;G] M₂) : M →ᵣ[k;G] f.range :=
f.cod_restrict f.range f.mem_range_self

/-- The kernel of a repre_hom `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the set of `x : M` such that `f x = 0`. The kernel is a subrepresentation of `M`. -/
def ker (f : M →ᵣ[k;G] M₂) : subrepre k G M := subrepre.comap f ⊥

@[simp] theorem mem_ker {f : M →ᵣ[k;G] M₂} {y} : y ∈ ker f ↔ f y = 0 := by apply subrepre.mem_comap

@[simp] theorem ker_id : ker (repre_hom.id : M →ᵣ[k;G] M) = ⊥ := rfl

@[simp] theorem map_coe_ker (f : M →ᵣ[k;G] M₂) (x : ker f) : f x = 0 := mem_ker.1 x.2

lemma comp_ker_subtype (f : M →ᵣ[k;G] M₂) : f.comp f.ker.subtype = 0 :=
repre_hom.ext $ λ x, suffices f x = 0, by simp [this], mem_ker.1 x.2

theorem ker_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) : ker (g.comp f) = subrepre.comap f (ker g) := rfl

theorem ker_le_ker_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) : ker f ≤ ker (g.comp f) := by {rw ker_comp, exact subrepre.comap_mono bot_le}

theorem disjoint_ker {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} :
  disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 :=
by simp [disjoint_def]

theorem ker_eq_bot' {f : M →ᵣ[k;G] M₂} :
  ker f = ⊥ ↔ (∀ m, f m = 0 → m = 0) :=
by simpa [disjoint] using @disjoint_ker _ _ _ _ _ _ _ _ _ _ _ _ f ⊤

theorem ker_eq_bot_of_inverse {f : M →ᵣ[k;G] M₂} {g : M₂ →ᵣ[k;G] M} (h : g.comp f = id) :
  ker f = ⊥ :=
ker_eq_bot'.2 $ λ m hm, by rw [← id_apply m, ← h, comp_apply, hm, g.map_zero]

lemma le_ker_iff_map {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} : p ≤ ker f ↔ subrepre.map f p = ⊥ :=
by rw [ker, eq_bot_iff, subrepre.map_le_iff_le_comap]

lemma ker_cod_restrict (p : subrepre k G M) (f : M₂ →ᵣ[k;G] M) (hf) :
  ker (cod_restrict p f hf) = ker f :=
by rw [ker, comap_cod_restrict, map_bot]; refl

lemma range_cod_restrict (p : subrepre k G M) (f : M₂ →ᵣ[k;G] M) (hf) :
  range (cod_restrict p f hf) = comap p.subtype f.range :=
by simpa only [range_eq_map] using map_cod_restrict _ _ _ _

lemma ker_restrict {p : subrepre k G M} {f : M →ᵣ[k;G] M} (hf : ∀ x : M, x ∈ p → f x ∈ p) :
  ker (f.restrict hf) = (f.dom_restrict p).ker :=
by rw [restrict_eq_cod_restrict_dom_restrict, ker_cod_restrict]

lemma map_comap_eq (f : M →ᵣ[k;G] M₂) (q : subrepre k G M₂) :
  subrepre.map f (subrepre.comap f q) = range f ⊓ q :=
le_antisymm (le_inf map_le_range (subrepre.map_comap_le _ _)) $
by rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

lemma map_comap_eq_self {f : M →ᵣ[k;G] M₂} {q : subrepre k G M₂} (h : q ≤ range f) :
  subrepre.map f (subrepre.comap f q) = q :=
by rwa [map_comap_eq, inf_eq_right]

@[simp] theorem ker_zero : ker (0 : M →ᵣ[k;G] M₂) = ⊤ :=
subrepre.eq_top_iff'.2 $ λ x, by simp

@[simp] theorem range_zero : range (0 : M →ᵣ[k;G] M₂) = ⊥ :=
by simp [range_eq_map]

theorem ker_eq_top {f : M →ᵣ[k;G] M₂} : ker f = ⊤ ↔ f = 0 :=
⟨λ h, ext $ λ x, mem_ker.1 $ h.symm ▸ trivial, λ h, h.symm ▸ ker_zero⟩

lemma range_le_bot_iff (f : M →ᵣ[k;G] M₂) : range f ≤ ⊥ ↔ f = 0 :=
by rw [range_le_iff_comap]; exact ker_eq_top

theorem range_eq_bot {f : M →ᵣ[k;G] M₂} : range f = ⊥ ↔ f = 0 :=
by rw [← range_le_bot_iff, le_bot_iff]

lemma range_le_ker_iff {f : M →ᵣ[k;G] M₂} {g : M₂ →ᵣ[k;G] M₃} : range f ≤ ker g ↔ g.comp f = 0 :=
⟨λ h, ker_eq_top.1 $ eq_top_iff'.2 $ λ x, h $ ⟨_, rfl⟩,
 λ h x hx, mem_ker.2 $ exists.elim hx $ λ y hy, by rw [←hy, ←comp_apply, h, zero_apply]⟩

theorem comap_le_comap_iff {f : M →ᵣ[k;G] M₂} (hf : range f = ⊤) {p p'} :
  subrepre.comap f p ≤ subrepre.comap f p' ↔ p ≤ p' :=
⟨λ H x hx, by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, subrepre.comap_mono⟩

theorem comap_injective {f : M →ᵣ[k;G] M₂} (hf : range f = ⊤) : function.injective (subrepre.comap f) :=
λ p p' h, le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h))
  ((comap_le_comap_iff hf).1 (ge_of_eq h))

theorem ker_eq_bot_of_injective {f : M →ᵣ[k;G] M₂} (hf : function.injective f) : ker f = ⊥ :=
begin
  have : disjoint ⊤ f.ker, by { rw [disjoint_ker, ← map_zero f], exact λ x hx H, hf H },
  simpa [disjoint]
end

end add_comm_monoid

section add_comm_group

open subrepre

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
  [semiring k] [monoid G]
  [add_comm_group M] [module k M] [repre k G M]
  [add_comm_group M₂] [module k M₂] [repre k G M₂]
  [add_comm_group M₃] [module k M₃] [repre k G M₃]





end add_comm_group

section ring

open subrepre

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
  [ring k] [monoid G]
  [add_comm_group M] [module k M] [repre k G M]
  [add_comm_group M₂] [module k M₂] [repre k G M₂]
  [add_comm_group M₃] [module k M₃] [repre k G M₃]
  {f : M →ᵣ[k;G] M₂}

theorem sub_mem_ker_iff {x y} : x - y ∈ f.ker ↔ f x = f y :=
by rw [mem_ker, map_sub, sub_eq_zero]

theorem disjoint_ker' {p : subrepre k G M} :
  disjoint p (ker f) ↔ ∀ x y ∈ p, f x = f y → x = y :=
disjoint_ker.trans
⟨λ H x y hx hy h, eq_of_sub_eq_zero $ H _ (sub_mem _ hx hy) (by simp [h]),
 λ H x h₁ h₂, H x 0 h₁ (zero_mem _) (by simpa using h₂)⟩

theorem inj_of_disjoint_ker {p : subrepre k G M}
  {s : set M} (h : s ⊆ p) (hd : disjoint p (ker f)) :
  ∀ x y ∈ s, f x = f y → x = y :=
λ x y hx hy, disjoint_ker'.1 hd _ _ (h hx) (h hy)

theorem ker_eq_bot : ker f = ⊥ ↔ injective f :=
by simpa [disjoint] using @disjoint_ker' _ _ _ _ _ _ _ _ _ _ _ _ f ⊤

lemma ker_le_iff {p : subrepre k G M} : ker f ≤ p ↔ ∃ (y ∈ range f), f ⁻¹' {y} ⊆ p :=
begin
  split,
  { intros h, use 0, rw [← set_like.mem_coe, f.range_coe], exact ⟨⟨0, map_zero f⟩, h⟩, },
  { rintros ⟨y, h₁, h₂⟩,
    rw set_like.le_def, intros z hz, simp only [mem_ker, set_like.mem_coe] at hz,
    rw [← set_like.mem_coe, f.range_coe, set.mem_range] at h₁, obtain ⟨x, hx⟩ := h₁,
    have hx' : x ∈ p, { exact h₂ hx, },
    have hxz : z + x ∈ p, { apply h₂, simp [hx, hz], },
    suffices : z + x - x ∈ p, { simpa only [this, add_sub_cancel],  },
    exact p.sub_mem hxz hx', },
end

end ring

end repre_hom

namespace repre_iso

section add_comm_monoid

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]
  [add_comm_monoid M₃] [module k M₃] [repre k G M₃]

section

variables (e e' : M ≃ᵣ[k;G] M₂)

lemma map_eq_comap {p : subrepre k G M} : (p.map e : subrepre k G M₂) = p.comap e.symm :=
set_like.coe_injective $ by simp [e.image_eq_preimage]

def of_subrepre (p : subrepre k G M) : p ≃ᵣ[k;G] ↥(p.map ↑e : subrepre k G M₂) :=
{ inv_fun   := λ y, ⟨e.symm y, by {
    rcases y with ⟨y', hy⟩, rw subrepre.mem_map at hy, rcases hy with ⟨x, hx, hxy⟩, subst hxy,
    simp only [symm_apply_apply, submodule.coe_mk, coe_coe, hx], }⟩,
  left_inv  := λ x, by simp,
  right_inv := λ y, by { apply set_coe.ext, simp, },
  ..((e : M →ᵣ[k;G] M₂).dom_restrict p).cod_restrict (p.map ↑e) (λ x, ⟨x, by simp⟩) }

@[simp] lemma of_subrepre_apply (p : subrepre k G M) (x : p) :
  ↑(e.of_subrepre p x) = e x := rfl

@[simp] lemma of_subrepre_symm_apply (p : subrepre k G M) (x : (p.map ↑e : subrepre k G M₂)) :
  ↑((e.of_subrepre p).symm x) = e.symm x := rfl

end

section

variables (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M) (e : M ≃ᵣ[k;G] M₂) (h : M₂ →ᵣ[k;G] M₃) (l : M₃ →ᵣ[k;G] M) (p q : subrepre k G M)

/-- Linear equivalence between two equal submodules. -/
def of_eq (h : p = q) : p ≃ᵣ[k;G] q :=
{ map_smul' := λ _ _, rfl, map_smul2' := λ _ _, rfl, map_add' := λ _ _, rfl, .. equiv.set.of_eq (congr_arg _ h) }

variables {p q}

@[simp] lemma coe_of_eq_apply (h : p = q) (x : p) : (of_eq p q h x : M) = x := rfl

@[simp] lemma of_eq_symm (h : p = q) : (of_eq p q h).symm = of_eq q p h.symm := rfl

/-- A linear equivalence which maps a submodule of one module onto another, restricts to a linear
equivalence of the two submodules. -/
def of_subrepres (p : subrepre k G M) (q : subrepre k G M₂) (h : p.map ↑e = q) : p ≃ᵣ[k;G] q :=
(e.of_subrepre p).trans (repre_iso.of_eq _ _ h)

@[simp] lemma of_subrepres_apply {p : subrepre k G M} {q : subrepre k G M₂}
  (h : p.map ↑e = q) (x : p) : ↑(e.of_subrepres p q h x) = e x := rfl

@[simp] lemma of_subrepres_symm_apply {p : subrepre k G M} {q : subrepre k G M₂}
  (h : p.map ↑e = q) (x : q) : ↑((e.of_subrepres p q h).symm x) = e.symm x := rfl

/-- A linear equivalence of two modules restricts to a linear equivalence from the preimage of any
submodule to that submodule.
This is `linear_equiv.of_submodule` but with `comap` on the left instead of `map` on the right. -/
def of_subrepre' [repre k G M] [repre k G M₂] (f : M ≃ᵣ[k;G] M₂) (U : subrepre k G M₂) :
  U.comap (f : M →ᵣ[k;G] M₂) ≃ᵣ[k;G] U :=
(f.symm.of_subrepres _ _ f.symm.map_eq_comap).symm

lemma of_subrepre'_to_repre_hom [repre k G M] [repre k G M₂]
  (f : M ≃ᵣ[k;G] M₂) (U : subrepre k G M₂) :
  (f.of_subrepre' U).to_repre_hom =
  (f.to_repre_hom.dom_restrict _).cod_restrict _ subtype.prop :=
by { ext, refl }

@[simp]
lemma of_subrepre'_apply [repre k G M] [repre k G M₂]
  (f : M ≃ᵣ[k;G] M₂) (U : subrepre k G M₂) (x : U.comap (f : M →ᵣ[k;G] M₂)) :
(f.of_subrepre' U x : M₂) = f (x : M) := rfl

@[simp]
lemma of_submodule'_symm_apply [repre k G M] [repre k G M₂]
  (f : M ≃ᵣ[k;G] M₂) (U : subrepre k G M₂) (x : U) :
((f.of_subrepre' U).symm x : M) = f.symm (x : M₂) := rfl

variable (p)

/-- The top submodule of `M` is linearly equivalent to `M`. -/
def of_top (h : p = ⊤) : p ≃ᵣ[k;G] M :=
{ inv_fun   := λ x, ⟨x, h.symm ▸ trivial⟩,
  left_inv  := λ ⟨x, h⟩, rfl,
  right_inv := λ x, rfl,
  .. p.subtype }

@[simp] theorem of_top_apply {h} (x : p) : of_top p h x = x := rfl

@[simp] theorem coe_of_top_symm_apply {h} (x : M) : ((of_top p h).symm x : M) = x := rfl

theorem of_top_symm_apply {h} (x : M) : (of_top p h).symm x = ⟨x, h.symm ▸ trivial⟩ := rfl

/-- If a linear map has an inverse, it is a linear equivalence. -/
def of_repre_hom (h₁ : f.comp g = repre_hom.id) (h₂ : g.comp f = repre_hom.id) : M ≃ᵣ[k;G] M₂ :=
{ inv_fun   := g,
  left_inv  := repre_hom.ext_iff.1 h₂,
  right_inv := repre_hom.ext_iff.1 h₁,
  ..f }

@[simp] theorem of_repre_hom_apply {h₁ h₂} (x : M) : of_repre_hom f g h₁ h₂ x = f x := rfl

@[simp] theorem of_repre_hom_symm_apply {h₁ h₂} (x : M₂) : (of_repre_hom f g h₁ h₂).symm x = g x := rfl

@[simp] protected theorem range : (e : M →ᵣ[k;G] M₂).range = ⊤ :=
repre_hom.range_eq_top.2 e.to_equiv.surjective

lemma eq_bot_of_equiv [repre k G M₂] (e : p ≃ᵣ[k;G] (⊥ : subrepre k G M₂)) : p = ⊥ :=
begin
  refine bot_unique (set_like.le_def.2 $ assume b hb, (submodule.mem_bot k).2 _),
  rw [← p.mk_eq_zero hb, ← e.map_eq_zero_iff],
  apply submodule.eq_zero_of_bot_submodule
end

@[simp] protected theorem ker : (e : M →ᵣ[k;G] M₂).ker = ⊥ :=
repre_hom.ker_eq_bot_of_injective e.to_equiv.injective

-- @[simp] theorem range_comp : (h.comp (e : M →ᵣ[k;G] M₂)).range = h.range :=
-- repre_hom.range_comp_of_range_eq_top _ e.range

-- @[simp] theorem ker_comp : ((e : M →ᵣ[k;G] M₂).comp l).ker = l.ker :=
-- repre_hom.ker_comp_of_ker_eq_bot _ e.ker

variables {f g}

/-- An linear map `f : M →ₗ[R] M₂` with a left-inverse `g : M₂ →ₗ[R] M` defines a linear equivalence
between `M` and `f.range`.
This is a computable alternative to `linear_equiv.of_injective`, and a bidirectional version of
`linear_map.range_restrict`. -/
def of_left_inverse {g : M₂ → M} (h : function.left_inverse g f) : M ≃ᵣ[k;G] f.range :=
{ to_fun := f.range_restrict,
  inv_fun := g ∘ f.range.subtype,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := repre_hom.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  .. f.range_restrict }

@[simp] lemma of_left_inverse_apply
  (h : function.left_inverse g f) (x : M) :
  ↑(of_left_inverse h x) = f x := rfl

@[simp] lemma of_left_inverse_symm_apply
  (h : function.left_inverse g f) (x : f.range) :
  (of_left_inverse h).symm x = g x := rfl

end

end add_comm_monoid

section add_comm_group




end add_comm_group

section ring

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
  [ring k] [monoid G]
  [add_comm_group M] [module k M] [repre k G M]
  [add_comm_group M₂] [module k M₂] [repre k G M₂]
  (f : M →ᵣ[k;G] M₂) (e : M ≃ᵣ[k;G] M₂)

/-- An `injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. See also `linear_map.of_left_inverse`. -/
noncomputable def of_injective (h : f.ker = ⊥) : M ≃ᵣ[k;G] f.range :=
of_left_inverse $ classical.some_spec (repre_hom.ker_eq_bot.1 h).has_left_inverse

@[simp] theorem of_injective_apply {h : f.ker = ⊥} (x : M) :
  ↑(of_injective f h x) = f x := rfl

/-- A bijective linear map is a linear equivalence. Here, bijectivity is described by saying that
the kernel of `f` is `{0}` and the range is the universal set. -/
noncomputable def of_bijective (hf₁ : f.ker = ⊥) (hf₂ : f.range = ⊤) : M ≃ᵣ[k;G] M₂ :=
(of_injective f hf₁).trans (of_top _ hf₂)

@[simp] theorem of_bijective_apply {hf₁ hf₂} (x : M) :
  of_bijective f hf₁ hf₂ x = f x := rfl

end ring

end repre_iso

/- Schur! -/

namespace schur

open repre_hom

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
  [ring k] [monoid G]
  [add_comm_group M] [module k M] [nontrivial M] [repre k G M]
  [add_comm_group M₂] [module k M₂] [nontrivial M₂] [repre k G M₂]
  (φ : M →ᵣ[k;G] M₂)

lemma injective (h : φ ≠ 0) : is_irreducible k G M → φ.ker = ⊥ :=
begin
  have hneq : φ.ker ≠ ⊤,
  { simp [ker_eq_top, h] },
  intro irr,
  have heq_bot := irr φ.ker,
  simp [hneq] at heq_bot,
  assumption
end

lemma surjective (h : φ ≠ 0) : is_irreducible k G M₂ → φ.range = ⊤ :=
begin
  have hneq : φ.range ≠ ⊥,
  { simp [range_eq_bot], exact h },
  intro irr,
  have heq_top := irr φ.range,
  simp [hneq] at heq_top,
  assumption
end

end schur

/-- A non-zero repre_hom between irreducible representations is a repre_iso. -/
noncomputable lemma schur
  {k : Type*} [ring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_group M] [module k M] [nontrivial M]
  [repre k G M]
  {M₂ : Type*} [add_comm_group M₂] [module k M₂] [nontrivial M₂]
  [repre k G M₂] (φ : M →ᵣ[k;G] M₂) (h : φ ≠ 0) :
  is_irreducible k G M → is_irreducible k G M₂ → M ≃ᵣ[k;G] M₂ :=
begin
  intros irr irr₂,
  apply repre_iso.of_bijective φ,
  exact schur.injective φ h irr,
  exact schur.surjective φ h irr₂
end