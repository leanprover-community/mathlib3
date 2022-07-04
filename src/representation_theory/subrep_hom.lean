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
  { simp only [function.comp_app, function.iterate_succ, linear_map.mul_apply, pow_succ, ih, mul_apply],
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
set_option trace.simplify.rewrite true
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

end subrep
