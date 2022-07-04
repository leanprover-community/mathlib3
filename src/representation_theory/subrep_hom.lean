/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.subrep_lattice

-- Follows linear_algebra.basic

open function
open_locale big_operators pointwise

namespace rep_hom

section add_comm_monoid

variables
  {k G V V₂ V₃ V₄ ι : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] {ρ : representation k G V}
  [add_comm_monoid V₂] [module k V₂] {ρ₂ : representation k G V₂}
  [add_comm_monoid V₃] [module k V₃] {ρ₃ : representation k G V₃}
  [add_comm_monoid V₄] [module k V₄] {ρ₄ : representation k G V₄}
  (f : ρ →ᵣ ρ₂) (f₂ : ρ₂ →ᵣ ρ₃)

def dom_restrict (f : ρ →ᵣ ρ₂) (p : subrep ρ) : p.representation' →ᵣ ρ₂ := f.comp p.subtype

@[simp] lemma dom_restrict_apply (f : ρ →ᵣ ρ₂) (p : subrep ρ) (x : p) :
  f.dom_restrict p x = f x := rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def cod_restrict (p : subrep ρ₂) (f : ρ →ᵣ ρ₂) (h : ∀c, f c ∈ p) :ρ →ᵣ p.representation' :=
by refine {to_fun := λc, ⟨f c, h c⟩, ..}; intros; apply set_coe.ext; simp [map_smulG]

@[simp] theorem cod_restrict_apply (p : subrep ρ₂) (f : ρ →ᵣ ρ₂) {h} (x : V) :
  (cod_restrict p f h x : V₂) = f x := rfl

@[simp] lemma comp_cod_restrict (p : subrep ρ₃) (h : ∀b, f₂ b ∈ p) :
  ((cod_restrict p f₂ h).comp f : ρ →ᵣ p.representation')
  = cod_restrict p (f₂.comp f) (assume b, h _) :=
ext $ assume b, rfl

@[simp] lemma subtype_comp_cod_restrict (p : subrep ρ₂) (h : ∀b, f b ∈ p) :
  p.subtype.comp (cod_restrict p f h) = f :=
ext $ assume b, rfl

/-- Restrict domain and codomain of an endomorphism. -/
def restrict (f : ρ →ᵣ ρ) {p : subrep ρ} (hf : ∀ x ∈ p, f x ∈ p) :
p.representation' →ᵣ p.representation' :=
(f.dom_restrict p).cod_restrict p $ set_like.forall.2 hf

lemma restrict_apply
  {f : ρ →ᵣ ρ} {p : subrep ρ} (hf : ∀ x ∈ p, f x ∈ p) (x : p) :
  f.restrict hf x = ⟨f x, hf x.1 x.2⟩ := rfl

lemma subtype_comp_restrict {f : ρ →ᵣ ρ} {p : subrep ρ} (hf : ∀ x ∈ p, f x ∈ p) :
  p.subtype.comp (f.restrict hf) = f.dom_restrict p := rfl

lemma restrict_eq_cod_restrict_dom_restrict
  {f : ρ →ᵣ ρ} {p : subrep ρ} (hf : ∀ x ∈ p, f x ∈ p) :
  f.restrict hf = (f.dom_restrict p).cod_restrict p (λ x, hf x.1 x.2) := rfl

lemma restrict_eq_dom_restrict_cod_restrict
  {f : ρ →ᵣ ρ} {p : subrep ρ} (hf : ∀ x, f x ∈ p) :
  f.restrict (λ x _, hf x) = (f.cod_restrict p hf).dom_restrict p := rfl

instance unique_of_left [subsingleton V] : unique (ρ →ᵣ ρ₂) :=
{ uniq := λ f, ext $ λ x, by rw [subsingleton.elim x 0, map_zero, map_zero],
  .. rep_hom.inhabited }

instance unique_of_right [subsingleton V₂] : unique (ρ →ᵣ ρ₂) :=
coe_injective.unique

-- eval_add_monoid_hom

/-- Projection from `rep_hom` to `linear_map` (`rep_hom.to_linear_map`) as a linear map -/
def to_linear_map' : (ρ →ᵣ ρ₂) →ₗ[k] (V →ₗ[k] V₂) :=
{ to_fun := to_linear_map,
  map_add' := by intros; ext; refl,
  map_smul' := by intros; ext; refl }

-- smul_right

instance [nontrivial V] : nontrivial (representation.End ρ) :=
begin
  obtain ⟨m, ne⟩ := (nontrivial_iff_exists_ne (0 : V)).mp infer_instance,
  exact nontrivial_of_ne 1 0 (λ p, ne (rep_hom.congr_fun p m))
end

@[simp, norm_cast] lemma coe_fn_sum {ι : Type*} (t : finset ι) (f : ι → ρ →ᵣ ρ₂) :
  ⇑(∑ i in t, f i) = ∑ i in t, (f i : V → V₂) :=
add_monoid_hom.map_sum ⟨@to_fun k G V V₂ _ _ _ _ _ _ ρ ρ₂, rfl, λ x y, rfl⟩ _ _

lemma sum_apply (t : finset ι) (f : ι → ρ →ᵣ ρ₂) (b : V) :
  (∑ d in t, f d) b = ∑ d in t, f d b :=
begin
  convert linear_map.sum_apply t (λ i, (f i).to_linear_map) b,
  simp
end

@[simp] lemma pow_apply (f : ρ →ᵣ ρ) (n : ℕ) (m : V) :
  (f^n) m = (f^[n] m) :=
begin
  induction n with n ih,
  { refl, },
  { simp only [function.comp_app, function.iterate_succ, rep_hom.mul_apply, pow_succ, ih, mul_apply],
    exact (function.commute.iterate_self _ _ m).symm, }
end

-- pow...

-- iterate, pow

-- pi_apply_eq_sum_univ

end add_comm_monoid

-- module (representation?)

end rep_hom

namespace subrep

section add_comm_monoid

variables
  {k G V V₂ V₃ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] {ρ : representation k G V}
  [add_comm_monoid V₂] [module k V₂] {ρ₂ : representation k G V₂}
  [add_comm_monoid V₃] [module k V₃] {ρ₃ : representation k G V₃}
  (p p' : subrep ρ) (q q' : subrep ρ₂)
  {c : k} {g : G} {x y : V}
open set

variables {p p'}

/-- If two subreps `p` and `p'` satisfy `p ⊆ p'`, then `of_le p p'` is the linear map version of
this inclusion. -/
def of_le (h : p ≤ p') : p.representation' →ᵣ p'.representation' :=
p.subtype.cod_restrict p' $ λ ⟨x, hx⟩, h hx

@[simp] theorem coe_of_le (h : p ≤ p') (x : p) :
  (of_le h x : V) = x := rfl

theorem of_le_apply (h : p ≤ p') (x : p) : of_le h x = ⟨x, h x.2⟩ := rfl

theorem of_le_injective (h : p ≤ p') : function.injective (of_le h) :=
λ x y h, subtype.val_injective (subtype.mk.inj h)

variables (p p')

lemma subtype_comp_of_le (p q : subrep ρ) (h : p ≤ q) :
  q.subtype.comp (of_le h) = p.subtype :=
by { ext ⟨b, hb⟩, refl }

@[simp] lemma subsingleton_iff : subsingleton (subrep ρ) ↔ subsingleton V :=
have h : subsingleton (subrep ρ) ↔ subsingleton (add_submonoid V),
{ rw [←subsingleton_iff_bot_eq_top, ←subsingleton_iff_bot_eq_top, to_submodule_eq.symm],
  convert submodule.to_add_submonoid_eq.symm; refl },
h.trans add_submonoid.subsingleton_iff

@[simp] lemma nontrivial_iff : nontrivial (subrep ρ) ↔ nontrivial V :=
not_iff_not.mp (
  (not_nontrivial_iff_subsingleton.trans $ subsingleton_iff).trans
  not_nontrivial_iff_subsingleton.symm)

instance [subsingleton V] : unique (subrep ρ) :=
⟨⟨⊥⟩, λ a, @subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

instance unique' [subsingleton k] : unique (subrep ρ) :=
by haveI := module.subsingleton k V; apply_instance

instance [nontrivial V] : nontrivial (subrep ρ) := nontrivial_iff.mpr ‹_›

theorem mem_right_iff_eq_zero_of_disjoint {p p' : subrep ρ} (h : disjoint p p') {x : p} :
  (x : V) ∈ p' ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x x.2 hx, λ h, h.symm ▸ p'.zero_mem⟩

theorem mem_left_iff_eq_zero_of_disjoint {p p' : subrep ρ} (h : disjoint p p') {x : p'} :
  (x : V) ∈ p ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x hx x.2, λ h, h.symm ▸ p.zero_mem⟩

/-- The pushforward of a subrep `p ⊆ M` by `f : M → M₂` -/
def map (f : ρ →ᵣ ρ₂) (p : subrep ρ) : subrep ρ₂ :=
{ carrier   := f '' p,
  smulG_mem' :=
  begin
    rintro g x ⟨y, hy, rfl⟩,
    exact ⟨ρ g y, smulG_mem p g hy, map_smulG f g _⟩
  end,
  .. p.to_submodule.map f.to_linear_map }

@[simp] lemma map_coe (f : ρ →ᵣ ρ₂) (p : subrep ρ) :
  (map f p : set V₂) = f '' p := rfl

lemma map_to_submodule (f : ρ →ᵣ ρ₂) (p : subrep ρ) :
  (p.map f).to_submodule = p.to_submodule.map f.to_linear_map :=
set_like.coe_injective rfl

@[simp] lemma mem_map {f : ρ →ᵣ ρ₂} {p : subrep ρ} {x : V₂} :
  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x := iff.rfl

theorem mem_map_of_mem {f : ρ →ᵣ ρ₂} {p : subrep ρ} {r} (h : r ∈ p) :
  f r ∈ map f p := set.mem_image_of_mem _ h

lemma apply_coe_mem_map (f : ρ →ᵣ ρ₂) {p : subrep ρ} (r : p) :
  f r ∈ map f p := mem_map_of_mem r.prop

@[simp] lemma map_id : map (rep_hom.id : ρ →ᵣ ρ) p = p :=
subrep.ext $ λ a, by simp

lemma map_comp
  (f : ρ →ᵣ ρ₂) (g : ρ₂ →ᵣ ρ₃) (p : subrep ρ) :
  map (g.comp f : ρ →ᵣ ρ₃) p = map g (map f p) :=
set_like.coe_injective $ by simp [map_coe]; rw ← image_comp

lemma map_mono {f : ρ →ᵣ ρ₂} {p p' : subrep ρ} :
  p ≤ p' → map f p ≤ map f p' := image_subset _

@[simp] lemma map_zero : map (0 : ρ →ᵣ ρ₂) p = ⊥ :=
have ∃ (x : V), x ∈ p := ⟨0, p.zero_mem⟩,
ext $ by simp [this, eq_comm]

lemma map_add_le (f g : ρ →ᵣ ρ₂) : map (f + g) p ≤ map f p ⊔ map g p :=
begin
  rintros x ⟨m, hm, rfl⟩,
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm),
end

lemma range_map_nonempty (N : subrep ρ) :
  (set.range (λ ϕ, subrep.map ϕ N : (ρ →ᵣ ρ₂) → subrep ρ₂)).nonempty :=
⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩

/-- The pushforward of a subrep by an injective rep_hom is
equivalent to the original subrep. -/
noncomputable def equiv_map_of_injective (f : ρ →ᵣ ρ₂) (i : injective f)
  (p : subrep ρ) : p.representation' ≃ᵣ (p.map f).representation' :=
{ map_add' := by { intros, simp only [equiv.to_fun_as_coe, equiv.set.image_apply,
                  map_add, subrep.coe_add], refl },
  map_smul' := by { intros, simp only [equiv.to_fun_as_coe, equiv.set.image_apply,
                  subrep.coe_smul_of_tower, smul_hom_class.map_smul], refl },
  map_smulG' := by { intros, simp only [equiv.to_fun_as_coe, equiv.set.image_apply,
                  subrep.representation_apply], congr, apply map_smulG },
  ..(equiv.set.image f p i) }

@[simp] lemma coe_equiv_map_of_injective_apply (f : ρ →ᵣ ρ₂) (i : injective f)
  (p : subrep ρ) (x : p) :
  (equiv_map_of_injective f i p x : V₂) = f x := rfl

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : ρ →ᵣ ρ₂) (p : subrep ρ₂) : subrep ρ :=
{ carrier   := f ⁻¹' p,
  smulG_mem' := λ a x h, by {simp only [set.mem_preimage, set_like.mem_coe,
                            map_smulG, smulG_mem p a h] at * },
  .. p.to_submodule.comap f.to_linear_map }

@[simp] lemma comap_coe (f : ρ →ᵣ ρ₂) (p : subrep ρ₂) :
  (comap f p : set V) = f ⁻¹' p := rfl

@[simp] lemma mem_comap {f : ρ →ᵣ ρ₂} {p : subrep ρ₂} :
  x ∈ comap f p ↔ f x ∈ p := iff.rfl

@[simp] lemma comap_id : comap rep_hom.id p = p :=
set_like.coe_injective rfl

lemma comap_comp (f : ρ →ᵣ ρ₂) (g : ρ₂ →ᵣ ρ₃)
  (p : subrep ρ₃) : comap (g.comp f : ρ →ᵣ ρ₃) p = comap f (comap g p) :=
rfl

lemma comap_mono {f : ρ →ᵣ ρ₂} {q q' : subrep ρ₂} :
  q ≤ q' → comap f q ≤ comap f q' := preimage_mono

-- le_comap_pow_of_le_comap

lemma map_le_iff_le_comap {f : ρ →ᵣ ρ₂} {p : subrep ρ} {q : subrep ρ₂} :
  map f p ≤ q ↔ p ≤ comap f q := image_subset_iff

lemma gc_map_comap (f : ρ →ᵣ ρ₂) : galois_connection (map f) (comap f)
| p q := map_le_iff_le_comap

@[simp] lemma map_bot (f : ρ →ᵣ ρ₂) : map f ⊥ = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma map_sup (f : ρ →ᵣ ρ₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
(gc_map_comap f).l_sup

@[simp] lemma map_supr {ι : Sort*} (f : ρ →ᵣ ρ₂) (p : ι → subrep ρ) :
  map f (⨆i, p i) = (⨆i, map f (p i)) :=
(gc_map_comap f).l_supr

@[simp] lemma comap_top (f : ρ →ᵣ ρ₂) : comap f ⊤ = ⊤ := rfl

@[simp] lemma comap_inf (f : ρ →ᵣ ρ₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' := rfl

@[simp] lemma comap_infi {ι : Sort*} (f : ρ →ᵣ ρ₂)
  (p : ι → subrep ρ₂) :
  comap f (⨅i, p i) = (⨅i, comap f (p i)) :=
(gc_map_comap f).u_infi

@[simp] lemma comap_zero : comap (0 : ρ →ᵣ ρ₂) q = ⊤ :=
ext $ by simp

lemma map_comap_le (f : ρ →ᵣ ρ₂) (q : subrep ρ₂) :
  map f (comap f q) ≤ q :=
(gc_map_comap f).l_u_le _

lemma le_comap_map (f : ρ →ᵣ ρ₂) (p : subrep ρ) :
  p ≤ comap f (map f p) :=
(gc_map_comap f).le_u_l _

-- galois insertion

-- galois coinsertion

lemma map_inf_eq_map_inf_comap {f : ρ →ᵣ ρ₂}
  {p : subrep ρ} {p' : subrep ρ₂} :
  map f p ⊓ p' = map f (p ⊓ comap f p') :=
le_antisymm
  (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
  (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))

lemma map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
ext $ λ x, ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

lemma eq_zero_of_bot_submodule : ∀(b : (⊥ : subrep ρ)), b = 0
| ⟨b', hb⟩ := subtype.eq $ show b' = 0, from mem_bot.1 hb

/-- The infimum of a family of invariant subrep of an endomorphism is also an invariant
subrep. -/
lemma _root_.rep_hom.infi_invariant {ι : Sort*}
  (f : ρ →ᵣ ρ) {p : ι → subrep ρ} (hf : ∀ i, ∀ v ∈ (p i), f v ∈ p i) :
  ∀ v ∈ infi p, f v ∈ infi p :=
begin
  have : ∀ i, (p i).map f ≤ p i,
  { rintros i - ⟨v, hv, rfl⟩,
    exact hf i v hv },
  suffices : (infi p).map f ≤ infi p,
  { exact λ v hv, this ⟨v, hv, rfl⟩, },
  exact le_infi (λ i, (subrep.map_mono (infi_le p i)).trans (this i)),
end

end add_comm_monoid

section add_comm_group

variables
  {k G V V₂ : Type*} [comm_ring k] [monoid G]
  [add_comm_group V] [module k V] {ρ : representation k G V}
  [add_comm_group V₂] [module k V₂] {ρ₂ : representation k G V₂}
  (p : subrep ρ)

@[simp] lemma neg_coe : -(p : set V) = p := set.ext $ λ x, p.neg_mem_iff

@[simp] protected lemma map_neg (f : ρ →ᵣ ρ₂) : map (-f) p = map f p :=
ext $ λ y, ⟨λ ⟨x, hx, hy⟩, hy ▸ ⟨-x, show -x ∈ p, from neg_mem hx, map_neg f x⟩,
  λ ⟨x, hx, hy⟩, hy ▸ ⟨-x, show -x ∈ p, from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩

end add_comm_group

section field

variables
  {k G V V₂ : Type*} [field k] [monoid G]
  [add_comm_group V] [module k V] {ρ : representation k G V}
  [add_comm_group V₂] [module k V₂] {ρ₂ : representation k G V₂}

lemma comap_smul (f : ρ →ᵣ ρ₂) (p : subrep ρ₂) (a : k) (h : a ≠ 0) :
  p.comap (a • f) = p.comap f :=
by ext b; simp only [subrep.mem_comap, p.smul_mem_iff h, rep_hom.smul_apply]

lemma map_smul (f : ρ →ᵣ ρ₂) (p : subrep ρ) (a : k) (h : a ≠ 0) :
  p.map (a • f) = p.map f :=
le_antisymm
  begin rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap], exact le_rfl end
  begin rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap], exact le_rfl end

lemma comap_smul' (f : ρ →ᵣ ρ₂) (p : subrep ρ₂) (a : k) :
  p.comap (a • f) = (⨅ h : a ≠ 0, p.comap f) :=
by classical; by_cases a = 0; simp [h, comap_smul]

lemma map_smul' (f : ρ →ᵣ ρ₂) (p : subrep ρ) (a : k) :
  p.map (a • f) = (⨆ h : a ≠ 0, p.map f) :=
by classical; by_cases a = 0; simp [h, map_smul]

end field

end subrep

namespace rep_hom

section add_comm_monoid

variables
  {k G V V₂ V₃ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] {ρ : representation k G V}
  [add_comm_monoid V₂] [module k V₂] {ρ₂ : representation k G V₂}
  [add_comm_monoid V₃] [module k V₃] {ρ₃ : representation k G V₃}
open subrep

-- dfinsupp

theorem map_cod_restrict (p : subrep ρ) (f : ρ₂ →ᵣ ρ) (h p') :
  subrep.map (cod_restrict p f h) p' = comap p.subtype (p'.map f) :=
subrep.ext $ λ ⟨x, hx⟩, by simp [subtype.ext_iff_val]

theorem comap_cod_restrict (p : subrep ρ) (f : ρ₂ →ᵣ ρ) (hf p') :
  subrep.comap (cod_restrict p f hf) p' = subrep.comap f (map p.subtype p') :=
subrep.ext $ λ x, ⟨λ h, ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern]. -/
def range (f : ρ →ᵣ ρ₂) : subrep ρ₂ :=
(map f ⊤).copy (set.range f) set.image_univ.symm

theorem range_coe (f : ρ →ᵣ ρ₂) :
  (range f : set V₂) = set.range f := rfl

lemma range_to_submodule (f : ρ →ᵣ ρ₂) :
  f.range.to_submodule = f.to_linear_map.range := rfl

@[simp] theorem mem_range   {f : ρ →ᵣ ρ₂} {x} : x ∈ range f ↔ ∃ y, f y = x :=
iff.rfl

lemma range_eq_map   (f : ρ →ᵣ ρ₂) : f.range = map f ⊤ :=
by { ext, simp }

theorem mem_range_self   (f : ρ →ᵣ ρ₂) (x : V) : f x ∈ f.range := ⟨x, rfl⟩

@[simp] theorem range_id : range (rep_hom.id : ρ →ᵣ ρ) = ⊤ :=
set_like.coe_injective set.range_id

theorem range_comp   (f : ρ →ᵣ ρ₂) (g : ρ₂ →ᵣ ρ₃) :
  range (g.comp f : ρ →ᵣ ρ₃) = map g (range f) :=
set_like.coe_injective (set.range_comp g f)

theorem range_comp_le_range   (f : ρ →ᵣ ρ₂) (g : ρ₂ →ᵣ ρ₃) :
  range (g.comp f : ρ →ᵣ ρ₃) ≤ range g :=
set_like.coe_mono (set.range_comp_subset_range f g)

theorem range_eq_top {f : ρ →ᵣ ρ₂} :
  range f = ⊤ ↔ surjective f :=
by rw [set_like.ext'_iff, range_coe, top_coe, set.range_iff_surjective]

lemma range_le_iff_comap {f : ρ →ᵣ ρ₂} {p : subrep ρ₂} :
  range f ≤ p ↔ comap f p = ⊤ :=
by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

lemma map_le_range {f : ρ →ᵣ ρ₂} {p : subrep ρ} :
  map f p ≤ range f :=
set_like.coe_mono (set.image_subset_range f p)

@[simp] lemma range_neg {k G V V₂ : Type*} [comm_ring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_group V₂] [module k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂} (f : ρ →ᵣ ρ₂) :
  (-f).range = f.range :=
begin
  change ((-rep_hom.id : ρ₂ →ᵣ ρ₂).comp f).range = _,
  rw [range_comp, subrep.map_neg, subrep.map_id]
end

-- iterate_range

/-- Restrict the codomain of a rep_hom `f` to `f.range`.
This is the bundled version of `set.range_factorization`. -/
@[reducible] def range_restrict (f : ρ →ᵣ ρ₂) :
  ρ →ᵣ f.range.representation' := f.cod_restrict f.range f.mem_range_self

/-- The range of a rep_hom is finite if the domain is finite.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype M₂`. -/
instance fintype_range [fintype V] [decidable_eq V₂]
  (f : ρ →ᵣ ρ₂) : fintype (range f) :=
set.fintype_range f

/-- The kernel of a rep_hom `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : ρ →ᵣ ρ₂) : subrep ρ := comap f ⊥

@[simp] theorem mem_ker {f : ρ →ᵣ ρ₂} {y} : y ∈ ker f ↔ f y = 0 :=
by { rw ←@mem_bot k G V₂ _ _ _ _ ρ₂ (f y), refl }

@[simp] theorem ker_id : ker (rep_hom.id : ρ →ᵣ ρ) = ⊥ := rfl

@[simp] theorem map_coe_ker (f : ρ →ᵣ ρ₂) (x : ker f) : f x = 0 := mem_ker.1 x.2

lemma ker_to_submodule (f : ρ →ᵣ ρ₂) :
  f.ker.to_submodule = f.to_linear_map.ker := rfl

lemma comp_ker_subtype (f : ρ →ᵣ ρ₂) : f.comp f.ker.subtype = 0 :=
rep_hom.ext $ λ x, suffices f x = 0, by simp [this], mem_ker.1 x.2

theorem ker_comp (f : ρ →ᵣ ρ₂) (g : ρ₂ →ᵣ ρ₃) :
  ker (g.comp f : ρ →ᵣ ρ₃) = comap f (ker g) := rfl

theorem ker_le_ker_comp (f : ρ →ᵣ ρ₂) (g : ρ₂ →ᵣ ρ₃) :
  ker f ≤ ker (g.comp f : ρ →ᵣ ρ₃) :=
by rw ker_comp; exact comap_mono bot_le

theorem disjoint_ker {f : ρ →ᵣ ρ₂} {p : subrep ρ} :
  disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 :=
by simp [disjoint_def]

theorem ker_eq_bot' {f : ρ →ᵣ ρ₂} :
  ker f = ⊥ ↔ (∀ m, f m = 0 → m = 0) :=
by simpa [disjoint] using @disjoint_ker _ _ _ _ _ _ _ _ _ _ _ _ f ⊤

theorem ker_eq_bot_of_inverse
  {f : ρ →ᵣ ρ₂} {g : ρ₂ →ᵣ ρ} (h : (g.comp f : ρ →ᵣ ρ) = id) :
  ker f = ⊥ :=
ker_eq_bot'.2 $ λ m hm, by rw [← id_apply m, ← h, comp_apply, hm, g.map_zero]

lemma le_ker_iff_map {f : ρ →ᵣ ρ₂} {p : subrep ρ} :
  p ≤ ker f ↔ map f p = ⊥ :=
by rw [ker, eq_bot_iff, map_le_iff_le_comap]

lemma ker_cod_restrict (p : subrep ρ) (f : ρ₂ →ᵣ ρ) (hf) :
  ker (cod_restrict p f hf) = ker f :=
by rw [ker, comap_cod_restrict, map_bot]; refl

lemma range_cod_restrict (p : subrep ρ) (f : ρ₂ →ᵣ ρ) (hf) :
  range (cod_restrict p f hf) = comap p.subtype f.range :=
by simpa only [range_eq_map] using map_cod_restrict _ _ _ _

lemma ker_restrict {p : subrep ρ} {f : ρ →ᵣ ρ} (hf : ∀ x : V, x ∈ p → f x ∈ p) :
  ker (f.restrict hf) = (f.dom_restrict p).ker :=
by rw [restrict_eq_cod_restrict_dom_restrict, ker_cod_restrict]

lemma _root_.subrep.map_comap_eq
  (f : ρ →ᵣ ρ₂) (q : subrep ρ₂) : map f (comap f q) = range f ⊓ q :=
le_antisymm (le_inf map_le_range (map_comap_le _ _)) $
by rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

lemma _root_.subrep.map_comap_eq_self
  {f : ρ →ᵣ ρ₂} {q : subrep ρ₂} (h : q ≤ range f) : map f (comap f q) = q :=
by rwa [subrep.map_comap_eq, inf_eq_right]

@[simp] theorem ker_zero : ker (0 : ρ →ᵣ ρ₂) = ⊤ :=
eq_top_iff'.2 $ λ x, by simp

@[simp] theorem range_zero : range (0 : ρ →ᵣ ρ₂) = ⊥ :=
by simpa only [range_eq_map] using subrep.map_zero _

theorem ker_eq_top {f : ρ →ᵣ ρ₂} : ker f = ⊤ ↔ f = 0 :=
⟨λ h, ext $ λ x, mem_ker.1 $ h.symm ▸ trivial, λ h, h.symm ▸ ker_zero⟩

lemma range_le_bot_iff (f : ρ →ᵣ ρ₂) : range f ≤ ⊥ ↔ f = 0 :=
by rw [range_le_iff_comap]; exact ker_eq_top

theorem range_eq_bot {f : ρ →ᵣ ρ₂} : range f = ⊥ ↔ f = 0 :=
by rw [← range_le_bot_iff, le_bot_iff]

lemma range_le_ker_iff {f : ρ →ᵣ ρ₂} {g : ρ₂ →ᵣ ρ₃} :
  range f ≤ ker g ↔ (g.comp f : ρ →ᵣ ρ₃) = 0 :=
⟨λ h, ker_eq_top.1 $ eq_top_iff'.2 $ λ x, h $ ⟨_, rfl⟩,
 λ h x hx, mem_ker.2 $ exists.elim hx $ λ y hy, by rw [←hy, ←comp_apply, h, zero_apply]⟩

theorem comap_le_comap_iff {f : ρ →ᵣ ρ₂} (hf : range f = ⊤) {p p'} :
  comap f p ≤ comap f p' ↔ p ≤ p' :=
⟨λ H x hx, by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, comap_mono⟩

theorem comap_injective {f : ρ →ᵣ ρ₂} (hf : range f = ⊤) : injective (comap f) :=
λ p p' h, le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h))
  ((comap_le_comap_iff hf).1 (ge_of_eq h))

theorem ker_eq_bot_of_injective {f : ρ →ᵣ ρ₂} (hf : injective f) : ker f = ⊥ :=
begin
  have : disjoint ⊤ f.ker, by { rw [disjoint_ker, ← map_zero f], exact λ x hx H, hf H },
  simpa [disjoint]
end

-- iterate ker

end add_comm_monoid

section add_comm_group

variables
  {k G V V₂ : Type*} [comm_ring k] [monoid G]
  [add_comm_group V] [module k V] {ρ : representation k G V}
  [add_comm_group V₂] [module k V₂] {ρ₂ : representation k G V₂}
  {f : ρ →ᵣ ρ₂}
open subrep

theorem sub_mem_ker_iff {x y} : x - y ∈ f.ker ↔ f x = f y :=
by rw [mem_ker, map_sub, sub_eq_zero]

theorem disjoint_ker' {p : subrep ρ} :
  disjoint p (ker f) ↔ ∀ x y ∈ p, f x = f y → x = y :=
disjoint_ker.trans
⟨λ H x hx y hy h, eq_of_sub_eq_zero $ H _ (sub_mem hx hy) (by simp [h]),
 λ H x h₁ h₂, H x h₁ 0 (zero_mem _) (by simpa using h₂)⟩

theorem inj_of_disjoint_ker {p : subrep ρ}
  {s : set V} (h : s ⊆ p) (hd : disjoint p (ker f)) :
  ∀ x y ∈ s, f x = f y → x = y :=
λ x hx y hy, disjoint_ker'.1 hd _ (h hx) _ (h hy)

theorem ker_eq_bot : ker f = ⊥ ↔ injective f :=
by simpa [disjoint] using @disjoint_ker' _ _ _ _ _ _ _ _ _ _ _ _ f ⊤

lemma ker_le_iff {p : subrep ρ} :
  ker f ≤ p ↔ ∃ (y ∈ range f), f ⁻¹' {y} ⊆ p :=
begin
  split,
  { intros h, use 0, rw [← set_like.mem_coe, f.range_coe], exact ⟨⟨0, map_zero f⟩, h⟩, },
  { rintros ⟨y, h₁, h₂⟩,
    rw set_like.le_def, intros z hz, simp only [mem_ker, set_like.mem_coe] at hz,
    rw [← set_like.mem_coe, f.range_coe, set.mem_range] at h₁, obtain ⟨x, hx⟩ := h₁,
    have hx' : x ∈ p, { exact h₂ hx, },
    have hxz : z + x ∈ p, { apply h₂, simp [hx, hz], },
    suffices : z + x - x ∈ p, { simpa only [this, add_sub_cancel], },
    exact p.sub_mem hxz hx', },
end

end add_comm_group

section field

variables
  {k G V V₂ : Type*} [field k] [monoid G]
  [add_comm_group V] [module k V] {ρ : representation k G V}
  [add_comm_group V₂] [module k V₂] {ρ₂ : representation k G V₂}

lemma ker_smul (f : ρ →ᵣ ρ₂) (a : k) (h : a ≠ 0) : ker (a • f) = ker f :=
subrep.comap_smul f _ a h

lemma ker_smul' (f : ρ →ᵣ ρ₂) (a : k) : ker (a • f) = ⨅(h : a ≠ 0), ker f :=
subrep.comap_smul' f _ a

lemma range_smul (f : ρ →ᵣ ρ₂) (a : k) (h : a ≠ 0) : range (a • f) = range f :=
by simpa only [range_eq_map] using subrep.map_smul f _ a h

lemma range_smul' (f : ρ →ᵣ ρ₂) (a : k) : range (a • f) = ⨆(h : a ≠ 0), range f :=
by simpa only [range_eq_map] using subrep.map_smul' f _ a

end field

end rep_hom
