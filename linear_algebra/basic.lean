/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard

Basics of linear algebra. This sets up the "categorical/lattice structure" of
modules, submodules, and linear maps.
-/

import algebra.pi_instances order.zorn data.set.finite data.finsupp order.order_iso

open function lattice

reserve infix `≃ₗ` : 50

universes u v w x y
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type y} {ι : Type x}

@[elab_as_eliminator]
lemma classical.some_spec3 {α : Type*} {p : α → Prop} {h : ∃a, p a}
  (q : α → Prop) (hpq : ∀a, p a → q a) : q (classical.some h) :=
hpq _ $ classical.some_spec _

namespace finset

lemma smul_sum [ring γ] [add_comm_group β] [module γ β]
  {s : finset α} {a : γ} {f : α → β} :
  a • (s.sum f) = s.sum (λc, a • f c) :=
(finset.sum_hom ((•) a) (@smul_zero γ β _ _ _ a) (assume _ _, smul_add _ _ _)).symm

end finset

namespace finsupp

lemma smul_sum [has_zero β] [ring γ] [add_comm_group δ] [module γ δ]
  {v : α →₀ β} {c : γ} {h : α → β → δ} :
  c • (v.sum h) = v.sum (λa b, c • h a b) :=
finset.smul_sum

end finsupp

namespace linear_map
section
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables (f g : β →ₗ γ)
include α

theorem comp_id (f : β →ₗ γ) : f.comp id = f :=
linear_map.ext $ λ x, rfl

theorem id_comp (f : β →ₗ γ) : id.comp f = f :=
linear_map.ext $ λ x, rfl

def cod_restrict (p : submodule α β) (f : γ →ₗ β) (h : ∀c, f c ∈ p) : γ →ₗ p :=
by refine {to_fun := λc, ⟨f c, h c⟩, ..}; intros; apply set_coe.ext; simp

@[simp] theorem cod_restrict_apply (p : submodule α β) (f : γ →ₗ β) {h} (x : γ) :
  (cod_restrict p f h x : β) = f x := rfl

def inverse (g : γ → β) (h₁ : left_inverse g f) (h₂ : right_inverse g f) : γ →ₗ β :=
by dsimp [left_inverse, function.right_inverse] at h₁ h₂; exact
⟨g, λ x y, by rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]; simp [h₂],
    λ a b, by rw [← h₁ (g (a • b)), ← h₁ (a • g b)]; simp [h₂]⟩

instance : has_zero (β →ₗ γ) := ⟨⟨λ _, 0, by simp, by simp⟩⟩

@[simp] lemma zero_apply (x : β) : (0 : β →ₗ γ) x = 0 := rfl

instance : has_neg (β →ₗ γ) := ⟨λ f, ⟨λ b, - f b, by simp, by simp⟩⟩

@[simp] lemma neg_apply (x : β) : (- f) x = - f x := rfl

instance : has_add (β →ₗ γ) := ⟨λ f g, ⟨λ b, f b + g b, by simp, by simp [smul_add]⟩⟩

@[simp] lemma add_apply (x : β) : (f + g) x = f x + g x := rfl

instance : add_comm_group (β →ₗ γ) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp

lemma sum_apply [decidable_eq δ] (t : finset δ) (f : δ → β →ₗ γ) (b : β) :
  t.sum f b = t.sum (λd, f d b) :=
(@finset.sum_hom _ _ _ t f _ _ (λ g : β →ₗ γ, g b) (by simp) (by simp)).symm

@[simp] lemma sub_apply (x : β) : (f - g) x = f x - g x := rfl

def smul_right (f : γ →ₗ α) (x : β) : γ →ₗ β :=
⟨λb, f b • x, by simp [add_smul], by simp [smul_smul]⟩.

@[simp] theorem smul_right_apply (f : γ →ₗ α) (x : β) (c : γ) :
  (smul_right f x : γ → β) c = f c • x := rfl

instance : has_one (β →ₗ β) := ⟨linear_map.id⟩
instance : has_mul (β →ₗ β) := ⟨linear_map.comp⟩

@[simp] lemma one_app (x : β) : (1 : β →ₗ β) x = x := rfl
@[simp] lemma mul_app (A B : β →ₗ β) (x : β) : (A * B) x = A (B x) := rfl

section
variables (α β)
include β

-- declaring this an instance breaks `real.lean` with reaching max. instance resolution depth
def endomorphism_ring : ring (β →ₗ β) :=
by refine {mul := (*), one := 1, ..linear_map.add_comm_group, ..};
  { intros, apply linear_map.ext, simp }

/-- The group of invertible linear maps from `β` to itself -/
def general_linear_group :=
by haveI := endomorphism_ring α β; exact units (β →ₗ β)
end

section
variables (β γ)
def fst : β × γ →ₗ β := ⟨prod.fst, λ x y, rfl, λ x y, rfl⟩
def snd : β × γ →ₗ γ := ⟨prod.snd, λ x y, rfl, λ x y, rfl⟩
end

@[simp] theorem fst_apply (x : β × γ) : fst β γ x = x.1 := rfl
@[simp] theorem snd_apply (x : β × γ) : snd β γ x = x.2 := rfl

def pair (f : β →ₗ γ) (g : β →ₗ δ) : β →ₗ γ × δ :=
⟨λ x, (f x, g x), λ x y, by simp, λ x y, by simp⟩

@[simp] theorem pair_apply (f : β →ₗ γ) (g : β →ₗ δ) (x : β) :
  pair f g x = (f x, g x) := rfl

@[simp] theorem fst_pair (f : β →ₗ γ) (g : β →ₗ δ) :
  (fst γ δ).comp (pair f g) = f := by ext; refl

@[simp] theorem snd_pair (f : β →ₗ γ) (g : β →ₗ δ) :
  (snd γ δ).comp (pair f g) = g := by ext; refl

@[simp] theorem pair_fst_snd : pair (fst β γ) (snd β γ) = linear_map.id :=
by ext; refl

section
variables (β γ)
def inl : β →ₗ β × γ := by refine ⟨prod.inl, _, _⟩; intros; simp [prod.inl]
def inr : γ →ₗ β × γ := by refine ⟨prod.inr, _, _⟩; intros; simp [prod.inr]
end

@[simp] theorem inl_apply (x : β) : inl β γ x = (x, 0) := rfl
@[simp] theorem inr_apply (x : γ) : inr β γ x = (0, x) := rfl

def copair (f : β →ₗ δ) (g : γ →ₗ δ) : β × γ →ₗ δ :=
⟨λ x, f x.1 + g x.2, λ x y, by simp, λ x y, by simp [smul_add]⟩

@[simp] theorem copair_apply (f : β →ₗ δ) (g : γ →ₗ δ) (x : β) (y : γ) :
  copair f g (x, y) = f x + g y := rfl

@[simp] theorem copair_inl (f : β →ₗ δ) (g : γ →ₗ δ) :
  (copair f g).comp (inl β γ) = f := by ext; simp

@[simp] theorem copair_inr (f : β →ₗ δ) (g : γ →ₗ δ) :
  (copair f g).comp (inr β γ) = g := by ext; simp

@[simp] theorem copair_inl_inr : copair (inl β γ) (inr β γ) = linear_map.id :=
by ext ⟨x, y⟩; simp

theorem fst_eq_copair : fst β γ = copair linear_map.id 0 := by ext ⟨x, y⟩; simp

theorem snd_eq_copair : snd β γ = copair 0 linear_map.id := by ext ⟨x, y⟩; simp

theorem inl_eq_pair : inl β γ = pair linear_map.id 0 := rfl

theorem inr_eq_pair : inr β γ = pair 0 linear_map.id := rfl

end

section comm_ring
variables [comm_ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables (f g : β →ₗ γ)
include α

instance : has_scalar α (β →ₗ γ) := ⟨λ a f,
  ⟨λ b, a • f b, by simp [smul_add], by simp [smul_smul, mul_comm]⟩⟩

@[simp] lemma smul_apply (a : α) (x : β) : (a • f) x = a • f x := rfl

instance : module α (β →ₗ γ) :=
module.of_core $ by refine { smul := (•), ..};
  intros; ext; simp [smul_add, add_smul, smul_smul]

def congr_right (f : γ →ₗ δ) : (β →ₗ γ) →ₗ (β →ₗ δ) :=
⟨linear_map.comp f,
λ _ _, linear_map.ext $ λ _, f.2 _ _,
λ _ _, linear_map.ext $ λ _, f.3 _ _⟩

end comm_ring
end linear_map

namespace submodule
variables {R:ring α} [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables (p p' : submodule α β) (q q' : submodule α γ)
variables {r : α} {x y : β}
include R
open set lattice

instance : partial_order (submodule α β) :=
partial_order.lift (coe : submodule α β → set β) $ λ a b, ext'

lemma le_def {p p' : submodule α β} : p ≤ p' ↔ (p : set β) ⊆ p' := iff.rfl

lemma le_def' {p p' : submodule α β} : p ≤ p' ↔ ∀ x ∈ p, x ∈ p' := iff.rfl

def of_le {p p' : submodule α β} (h : p ≤ p') : p →ₗ p' :=
linear_map.cod_restrict _ p.subtype $ λ ⟨x, hx⟩, h hx

@[simp] theorem of_le_apply {p p' : submodule α β} (h : p ≤ p')
  (x : p) : (of_le h x : β) = x := rfl

instance : has_bot (submodule α β) :=
⟨by split; try {exact {0}}; simp {contextual := tt}⟩

@[simp] lemma bot_coe : ((⊥ : submodule α β) : set β) = {0} := rfl

@[simp] lemma mem_bot : x ∈ (⊥ : submodule α β) ↔ x = 0 := mem_singleton_iff

instance : order_bot (submodule α β) :=
{ bot := ⊥,
  bot_le := λ p x, by simp {contextual := tt},
  ..submodule.partial_order }

instance : has_top (submodule α β) :=
⟨by split; try {exact set.univ}; simp⟩

@[simp] lemma top_coe : ((⊤ : submodule α β) : set β) = univ := rfl

@[simp] lemma mem_top : x ∈ (⊤ : submodule α β) := trivial

instance : order_top (submodule α β) :=
{ top := ⊤,
  le_top := λ p x _, trivial,
  ..submodule.partial_order }

instance : has_Inf (submodule α β) :=
⟨λ S, {
  carrier := ⋂ s ∈ S, ↑s,
  zero := by simp,
  add  := by simp [add_mem] {contextual := tt},
  smul := by simp [smul_mem] {contextual := tt} }⟩

private lemma Inf_le' {S : set (submodule α β)} {p} : p ∈ S → Inf S ≤ p :=
bInter_subset_of_mem

private lemma le_Inf' {S : set (submodule α β)} {p} : (∀p' ∈ S, p ≤ p') → p ≤ Inf S :=
subset_bInter

instance : has_inf (submodule α β) :=
⟨λ p p', {
  carrier := p ∩ p',
  zero := by simp,
  add  := by simp [add_mem] {contextual := tt},
  smul := by simp [smul_mem] {contextual := tt} }⟩

instance : complete_lattice (submodule α β) :=
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

lemma eq_top_iff' {p : submodule α β} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, @h x trivial, λ h x _, h x⟩

@[simp] theorem inf_coe : (p ⊓ p' : set β) = p ∩ p' := rfl

@[simp] theorem mem_inf {p p' : submodule α β} :
  x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

@[simp] theorem Inf_coe (P : set (submodule α β)) : (↑(Inf P) : set β) = ⋂ p ∈ P, ↑p := rfl

@[simp] theorem infi_coe {ι} (p : ι → submodule α β) :
  (↑⨅ i, p i : set β) = ⋂ i, ↑(p i) :=
by rw [infi, Inf_coe]; ext a; simp; exact
⟨λ h i, h _ i rfl, λ h i x e, e.symm ▸ h _⟩

@[simp] theorem mem_infi {ι} (p : ι → submodule α β) :
  x ∈ (⨅ i, p i) ↔ ∀ i, x ∈ p i :=
by rw [← mem_coe, infi_coe, mem_Inter]; refl

theorem disjoint_def {p p' : submodule α β} :
  disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0:β) :=
show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : set β)) ↔ _, by simp

/-- The pushforward -/
def map (f : β →ₗ γ) (p : submodule α β) : submodule α γ :=
{ carrier := f '' p,
  zero  := ⟨0, p.zero_mem, f.map_zero⟩,
  add   := by rintro _ _ ⟨b₁, hb₁, rfl⟩ ⟨b₂, hb₂, rfl⟩;
              exact ⟨_, p.add_mem hb₁ hb₂, f.map_add _ _⟩,
  smul  := by rintro a _ ⟨b, hb, rfl⟩;
              exact ⟨_, p.smul_mem _ hb, f.map_smul _ _⟩ }

lemma map_coe (f : β →ₗ γ) (p : submodule α β) :
  (map f p : set γ) = f '' p := rfl

@[simp] lemma mem_map {f : β →ₗ γ} {p : submodule α β} {x : γ} :
  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x := iff.rfl

lemma map_id : map linear_map.id p = p :=
submodule.ext $ λ a, by simp

lemma map_comp (f : β →ₗ γ) (g : γ →ₗ δ) (p : submodule α β) :
  map (g.comp f) p = map g (map f p) :=
submodule.ext' $ by simp [map_coe]; rw ← image_comp

lemma map_mono {f : β →ₗ γ} {p p' : submodule α β} : p ≤ p' → map f p ≤ map f p' :=
image_subset _

/-- The pullback -/
def comap (f : β →ₗ γ) (p : submodule α γ) : submodule α β :=
{ carrier := f ⁻¹' p,
  zero  := by simp,
  add   := λ x y h₁ h₂, by simp [p.add_mem h₁ h₂],
  smul  := λ a x h, by simp [p.smul_mem _ h] }

@[simp] lemma comap_coe (f : β →ₗ γ) (p : submodule α γ) :
  (comap f p : set β) = f ⁻¹' p := rfl

@[simp] lemma mem_comap {f : β →ₗ γ} {p : submodule α γ} :
  x ∈ comap f p ↔ f x ∈ p := iff.rfl

lemma comap_id : comap linear_map.id p = p :=
submodule.ext' rfl

lemma comap_comp (f : β →ₗ γ) (g : γ →ₗ δ) (p : submodule α δ) :
  comap (g.comp f) p = comap f (comap g p) := rfl

lemma comap_mono {f : β →ₗ γ} {q q' : submodule α γ} : q ≤ q' → comap f q ≤ comap f q' :=
preimage_mono

@[simp] lemma comap_top (f : β →ₗ γ) : comap f ⊤ = ⊤ := rfl

lemma map_le_iff_le_comap {f : β →ₗ γ} {p : submodule α β} {q : submodule α γ} :
  map f p ≤ q ↔ p ≤ comap f q := image_subset_iff

lemma map_comap_le (f : β →ₗ γ) (q : submodule α γ) : map f (comap f q) ≤ q :=
map_le_iff_le_comap.2 $ le_refl _

lemma le_comap_map (f : β →ₗ γ) (p : submodule α β) : p ≤ comap f (map f p) :=
map_le_iff_le_comap.1 $ le_refl _

@[simp] lemma map_bot (f : β →ₗ γ) : map f ⊥ = ⊥ :=
eq_bot_iff.2 $ map_le_iff_le_comap.2 bot_le

--TODO(Mario): is there a way to prove this from order properties?
lemma map_inf_eq_map_inf_comap {f : β →ₗ γ}
  {p : submodule α β} {p' : submodule α γ} :
  map f p ⊓ p' = map f (p ⊓ comap f p') :=
le_antisymm
  (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
  (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))

lemma map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
ext $ λ x, ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

def span (s : set β) : submodule α β := Inf {p | s ⊆ p}

variables {s t : set β}
lemma mem_span : x ∈ span s ↔ ∀ p : submodule α β, s ⊆ p → x ∈ p :=
mem_bInter_iff

lemma subset_span : s ⊆ span s :=
λ x h, mem_span.2 $ λ p hp, hp h

lemma span_le {p} : span s ≤ p ↔ s ⊆ p :=
⟨subset.trans subset_span, λ ss x h, mem_span.1 h _ ss⟩

lemma span_mono (h : s ⊆ t) : span s ≤ span t :=
span_le.2 $ subset.trans h subset_span

lemma span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span s) : span s = p :=
le_antisymm (span_le.2 h₁) h₂

@[simp] lemma span_eq : span (p : set β) = p :=
span_eq_of_le _ (subset.refl _) subset_span

@[elab_as_eliminator] lemma span_induction {p : β → Prop} (h : x ∈ span s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ a x, p x → p (a • x)) : p x :=
(@span_le _ _ _ _ _ _ ⟨p, H0, H1, H2⟩).2 Hs h

variables (β)
protected def gi : galois_insertion (@span α β _ _ _) coe :=
{ choice := λ s _, span s,
  gc := λ s t, span_le,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, rfl }
variables {β}

@[simp] lemma span_empty : span (∅ : set β) = ⊥ :=
(submodule.gi β).gc.l_bot

lemma span_union (s t : set β) : span (s ∪ t) = span s ⊔ span t :=
(submodule.gi β).gc.l_sup

lemma span_Union {ι} (s : ι → set β) : span (⋃ i, s i) = ⨆ i, span (s i) :=
(submodule.gi β).gc.l_supr

@[simp] theorem Union_coe_of_directed {ι} (hι : nonempty ι)
  (S : ι → submodule α β)
  (H : ∀ i j, ∃ k, S i ≤ S k ∧ S j ≤ S k) :
  ((supr S : submodule α β) : set β) = ⋃ i, S i :=
begin
  refine subset.antisymm _ (Union_subset $ le_supr S),
  rw [show supr S = ⨆ i, span (S i), by simp, ← span_Union],
  unfreezeI,
  refine λ x hx, span_induction hx (λ _, id) _ _ _,
  { cases hι with i, exact mem_Union.2 ⟨i, by simp⟩ },
  { simp, intros x y i hi j hj,
    rcases H i j with ⟨k, ik, jk⟩,
    exact ⟨k, add_mem _ (ik hi) (jk hj)⟩ },
  { simp [-mem_coe]; exact λ a x i hi, ⟨i, smul_mem _ a hi⟩ },
end

@[simp] theorem mem_supr_of_directed {ι} (hι : nonempty ι)
  (S : ι → submodule α β)
  (H : ∀ i j, ∃ k, S i ≤ S k ∧ S j ≤ S k) {x} :
  x ∈ supr S ↔ ∃ i, x ∈ S i :=
by rw [← mem_coe, Union_coe_of_directed hι S H, mem_Union]; refl

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
variables (p p')

lemma mem_span_singleton {y : β} : x ∈ span ({y} : set β) ↔ ∃ a, a • y = x :=
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

lemma span_singleton_eq_range (y : β) : (span ({y} : set β) : set β) = range (• y) :=
set.ext $ λ x, mem_span_singleton

lemma mem_span_insert {y} : x ∈ span (insert y s) ↔ ∃ a (z ∈ span s), x = a • y + z :=
begin
  rw [← union_singleton, span_union, mem_sup],
  simp [mem_span_singleton], split,
  { rintro ⟨z, hz, _, ⟨a, rfl⟩, rfl⟩, exact ⟨a, z, hz, rfl⟩ },
  { rintro ⟨a, z, hz, rfl⟩, exact ⟨z, hz, _, ⟨a, rfl⟩, rfl⟩ }
end

lemma mem_span_insert' {y} : x ∈ span (insert y s) ↔ ∃a, x + a • y ∈ span s :=
begin
  rw mem_span_insert, split,
  { rintro ⟨a, z, hz, rfl⟩, exact ⟨-a, by simp [hz]⟩ },
  { rintro ⟨a, h⟩, exact ⟨-a, _, h, by simp⟩ }
end

lemma span_insert_eq_span (h : x ∈ span s) : span (insert x s) = span s :=
span_eq_of_le _ (set.insert_subset.mpr ⟨h, subset_span⟩) (span_mono $ subset_insert _ _)

lemma span_span : span (span s : set β) = span s := span_eq _

lemma span_eq_bot : span (s : set β) = ⊥ ↔ ∀ x ∈ s, (x:β) = 0 :=
eq_bot_iff.trans ⟨
  λ H x h, mem_bot.1 $ H $ subset_span h,
  λ H, span_le.2 (λ x h, mem_bot.2 (H x h))⟩

lemma span_singleton_eq_bot : span ({x} : set β) = ⊥ ↔ x = 0 :=
span_eq_bot.trans $ by simp

@[simp] lemma span_image (f : β →ₗ γ) : span (f '' s) = map f (span s) :=
span_eq_of_le _ (image_subset _ subset_span) $ map_le_iff_le_comap.2 $
span_le.2 $ image_subset_iff.1 subset_span

def prod : submodule α (β × γ) :=
{ carrier := set.prod p q,
  zero := ⟨zero_mem _, zero_mem _⟩,
  add  := by rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨hx₁, hy₁⟩ ⟨hx₂, hy₂⟩;
             exact ⟨add_mem _ hx₁ hx₂, add_mem _ hy₁ hy₂⟩,
  smul := by rintro a ⟨x, y⟩ ⟨hx, hy⟩;
             exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }

@[simp] lemma prod_coe :
  (prod p q : set (β × γ)) = set.prod p q := rfl

@[simp] lemma mem_prod {p : submodule α β} {q : submodule α γ} {x : β × γ} :
  x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q := set.mem_prod

lemma span_prod_le (s : set β) (t : set γ) :
  span (set.prod s t) ≤ prod (span s) (span t) :=
span_le.2 $ set.prod_mono subset_span subset_span

@[simp] lemma prod_top : (prod ⊤ ⊤ : submodule α (β × γ)) = ⊤ :=
by ext; simp

@[simp] lemma prod_bot : (prod ⊥ ⊥ : submodule α (β × γ)) = ⊥ :=
by ext ⟨x, y⟩; simp [prod.zero_eq_mk]

lemma prod_mono {p p' : submodule α β} {q q' : submodule α γ} :
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
def quotient_rel : setoid β :=
⟨λ x y, x - y ∈ p, λ x, by simp,
 λ x y h, by simpa using neg_mem _ h,
 λ x y z h₁ h₂, by simpa using add_mem _ h₁ h₂⟩

def quotient : Type* := quotient (quotient_rel p)

namespace quotient

def mk {p : submodule α β} : β → quotient p := quotient.mk'

@[simp] theorem mk_eq_mk {p : submodule α β} (x : β) : (quotient.mk x : quotient p) = mk x := rfl
@[simp] theorem mk'_eq_mk {p : submodule α β} (x : β) : (quotient.mk' x : quotient p) = mk x := rfl
@[simp] theorem quot_mk_eq_mk {p : submodule α β} (x : β) : (quot.mk _ x : quotient p) = mk x := rfl

protected theorem eq {x y : β} : (mk x : quotient p) = mk y ↔ x - y ∈ p := quotient.eq'

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

instance : has_scalar α (quotient p) :=
⟨λ a x, quotient.lift_on' x (λ x, mk (a • x)) $
 λ x y h, (quotient.eq p).2 $ by simpa [smul_add] using smul_mem p a h⟩

@[simp] theorem mk_smul : (mk (r • x) : quotient p) = r • mk x := rfl

instance : module α (quotient p) :=
module.of_core $ by refine {smul := (•), ..};
  repeat {rintro ⟨⟩ <|> intro}; simp [smul_add, add_smul, smul_smul,
    -mk_add, (mk_add p).symm, -mk_smul, (mk_smul p).symm]

instance {α β} {R:discrete_field α} [add_comm_group β] [vector_space α β]
  (p : submodule α β) : vector_space α (quotient p) := {}

end quotient

end submodule

namespace linear_map
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
include α
open submodule

@[simp] lemma finsupp_sum {α β γ δ} [ring α] [add_comm_group β] [module α β]
   [add_comm_group γ] [module α γ] [has_zero δ]
  (f : β →ₗ γ) {t : ι →₀ δ} {g : ι → δ → β} :
  f (t.sum g) = t.sum (λi d, f (g i d)) := f.map_sum

theorem map_cod_restrict (p : submodule α β) (f : γ →ₗ β) (h p') :
  submodule.map (cod_restrict p f h) p' = comap p.subtype (p'.map f) :=
submodule.ext $ λ ⟨x, hx⟩, by simp [subtype.coe_ext]

theorem comap_cod_restrict (p : submodule α β) (f : γ →ₗ β) (hf p') :
  submodule.comap (cod_restrict p f hf) p' = submodule.comap f (map p.subtype p') :=
submodule.ext $ λ x, ⟨λ h, ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

def range (f : β →ₗ γ) : submodule α γ := map f ⊤

theorem range_coe (f : β →ₗ γ) : (range f : set γ) = set.range f := set.image_univ

@[simp] theorem mem_range {f : β →ₗ γ} : ∀ {x}, x ∈ range f ↔ ∃ y, f y = x :=
(set.ext_iff _ _).1 (range_coe f).

@[simp] theorem range_id : range (linear_map.id : β →ₗ β) = ⊤ := map_id _

theorem range_comp (f : β →ₗ γ) (g : γ →ₗ δ) : range (g.comp f) = map g (range f) :=
map_comp _ _ _

theorem range_comp_le_range (f : β →ₗ γ) (g : γ →ₗ δ) : range (g.comp f) ≤ range g :=
by rw range_comp; exact map_mono le_top

theorem range_eq_top {f : β →ₗ γ} : range f = ⊤ ↔ surjective f :=
by rw [← submodule.ext'_iff, range_coe, top_coe, set.range_iff_surjective]

lemma range_le_iff_comap {f : β →ₗ γ} {p : submodule α γ} : range f ≤ p ↔ comap f p = ⊤ :=
by rw [range, map_le_iff_le_comap, eq_top_iff]

def ker (f : β →ₗ γ) : submodule α β := comap f ⊥

@[simp] theorem mem_ker {f : β →ₗ γ} {y} : y ∈ ker f ↔ f y = 0 := mem_bot

@[simp] theorem ker_id : ker (linear_map.id : β →ₗ β) = ⊥ := rfl

theorem ker_comp (f : β →ₗ γ) (g : γ →ₗ δ) : ker (g.comp f) = comap f (ker g) := rfl

theorem ker_le_ker_comp (f : β →ₗ γ) (g : γ →ₗ δ) : ker f ≤ ker (g.comp f) :=
by rw ker_comp; exact comap_mono bot_le

theorem sub_mem_ker_iff {f : β →ₗ γ} {x y} : x - y ∈ f.ker ↔ f x = f y :=
by rw [mem_ker, map_sub, sub_eq_zero]

theorem disjoint_ker {f : β →ₗ γ} {p : submodule α β} :
  disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 :=
by simp [disjoint_def]

theorem disjoint_ker' {f : β →ₗ γ} {p : submodule α β} :
  disjoint p (ker f) ↔ ∀ x y ∈ p, f x = f y → x = y :=
disjoint_ker.trans
⟨λ H x y hx hy h, eq_of_sub_eq_zero $ H _ (sub_mem _ hx hy) (by simp [h]),
 λ H x h₁ h₂, H x 0 h₁ (zero_mem _) (by simpa using h₂)⟩

theorem inj_of_disjoint_ker {f : β →ₗ γ} {p : submodule α β}
  {s : set β} (h : s ⊆ p) (hd : disjoint p (ker f)) :
  ∀ x y ∈ s, f x = f y → x = y :=
λ x y hx hy, disjoint_ker'.1 hd _ _ (h hx) (h hy)

theorem ker_eq_bot {f : β →ₗ γ} : ker f = ⊥ ↔ injective f :=
by simpa [disjoint] using @disjoint_ker' _ _ _ _ _ _ _ _ f ⊤

lemma le_ker_iff_map {f : β →ₗ γ} {p : submodule α β} : p ≤ ker f ↔ map f p = ⊥ :=
by rw [ker, eq_bot_iff, map_le_iff_le_comap]

lemma map_comap_eq (f : β →ₗ γ) (q : submodule α γ) :
  map f (comap f q) = range f ⊓ q :=
le_antisymm (le_inf (map_mono le_top) (map_comap_le _ _)) $
by rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

lemma map_comap_eq_self {f : β →ₗ γ} {q : submodule α γ} (h : q ≤ range f) :
  map f (comap f q) = q :=
by rw [map_comap_eq, inf_of_le_right h]

lemma comap_map_eq (f : β →ₗ γ) (p : submodule α β) :
  comap f (map f p) = p ⊔ ker f :=
begin
  refine le_antisymm _ (sup_le (le_comap_map _ _) (comap_mono bot_le)),
  rintro x ⟨y, hy, e⟩,
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩
end

lemma comap_map_eq_self {f : β →ₗ γ} {p : submodule α β} (h : ker f ≤ p) :
  comap f (map f p) = p :=
by rw [comap_map_eq, sup_of_le_left h]

@[simp] theorem ker_zero : ker (0 : β →ₗ γ) = ⊤ :=
eq_top_iff'.2 $ λ x, by simp

theorem ker_eq_top {f : β →ₗ γ} : ker f = ⊤ ↔ f = 0 :=
⟨λ h, ext $ λ x, mem_ker.1 $ h.symm ▸ trivial, λ h, h.symm ▸ ker_zero⟩

theorem map_le_map_iff {f : β →ₗ γ} (hf : ker f = ⊥) {p p'} : map f p ≤ map f p' ↔ p ≤ p' :=
⟨λ H x hx, let ⟨y, hy, e⟩ := H ⟨x, hx, rfl⟩ in ker_eq_bot.1 hf e ▸ hy, map_mono⟩

theorem map_injective {f : β →ₗ γ} (hf : ker f = ⊥) : injective (map f) :=
λ p p' h, le_antisymm ((map_le_map_iff hf).1 (le_of_eq h)) ((map_le_map_iff hf).1 (ge_of_eq h))

theorem comap_le_comap_iff {f : β →ₗ γ} (hf : range f = ⊤) {p p'} : comap f p ≤ comap f p' ↔ p ≤ p' :=
⟨λ H x hx, by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, comap_mono⟩

theorem comap_injective {f : β →ₗ γ} (hf : range f = ⊤) : injective (comap f) :=
λ p p' h, le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))

theorem map_copair_prod (f : β →ₗ δ) (g : γ →ₗ δ) (p : submodule α β) (q : submodule α γ) :
  map (copair f g) (p.prod q) = map f p ⊔ map g q :=
begin
  refine le_antisymm _ (sup_le (map_le_iff_le_comap.2 _) (map_le_iff_le_comap.2 _)),
  { rw le_def', rintro _ ⟨x, ⟨h₁, h₂⟩, rfl⟩,
    exact mem_sup.2 ⟨_, ⟨_, h₁, rfl⟩, _, ⟨_, h₂, rfl⟩, rfl⟩ },
  { exact λ x hx, ⟨(x, 0), by simp [hx]⟩ },
  { exact λ x hx, ⟨(0, x), by simp [hx]⟩ }
end

theorem comap_pair_prod (f : β →ₗ γ) (g : β →ₗ δ) (p : submodule α γ) (q : submodule α δ) :
  comap (pair f g) (p.prod q) = comap f p ⊓ comap g q :=
submodule.ext $ λ x, iff.rfl

theorem prod_eq_inf_comap (p : submodule α β) (q : submodule α γ) :
  p.prod q = p.comap (linear_map.fst β γ) ⊓ q.comap (linear_map.snd β γ) :=
submodule.ext $ λ x, iff.rfl

theorem prod_eq_sup_map (p : submodule α β) (q : submodule α γ) :
  p.prod q = p.map (linear_map.inl β γ) ⊔ q.map (linear_map.inr β γ) :=
by rw [← map_copair_prod, copair_inl_inr, map_id]

lemma span_inl_union_inr {s : set β} {t : set γ} :
  span (prod.inl '' s ∪ prod.inr '' t) = (span s).prod (span t) :=
by rw [span_union, prod_eq_sup_map, ← span_image, ← span_image]; refl

end linear_map

namespace submodule
variables {R:ring α} [add_comm_group β] [add_comm_group γ] [module α β] [module α γ]
variables (p p' : submodule α β) (q : submodule α γ)
include R
open linear_map

@[simp] theorem map_top (f : β →ₗ γ) : map f ⊤ = range f := rfl

@[simp] theorem comap_bot (f : β →ₗ γ) : comap f ⊥ = ker f := rfl

@[simp] theorem ker_subtype : p.subtype.ker = ⊥ :=
ker_eq_bot.2 $ λ x y, subtype.eq'

@[simp] theorem range_subtype : p.subtype.range = p :=
by simpa using map_comap_subtype p ⊤

lemma map_subtype_le (p' : submodule α p) : map p.subtype p' ≤ p :=
by simpa using (map_mono le_top : map p.subtype p' ≤ p.subtype.range)

/-- If N ⊆ M then submodules of N are the same as submodules of M contained in N -/
def map_subtype.order_iso :
  ((≤) : submodule α p → submodule α p → Prop) ≃o
  ((≤) : {p' : submodule α β // p' ≤ p} → {p' : submodule α β // p' ≤ p} → Prop) :=
{ to_fun    := λ p', ⟨map p.subtype p', map_subtype_le p _⟩,
  inv_fun   := λ q, comap p.subtype q,
  left_inv  := λ p', comap_map_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.eq' $ by simp [map_comap_subtype p, inf_of_le_right hq],
  ord       := λ p₁ p₂, (map_le_map_iff $ ker_subtype _).symm }

def map_subtype.le_order_embedding :
  ((≤) : submodule α p → submodule α p → Prop) ≼o ((≤) : submodule α β → submodule α β → Prop) :=
(order_iso.to_order_embedding $ map_subtype.order_iso p).trans (subtype.order_embedding _ _)

@[simp] lemma map_subtype_embedding_eq (p' : submodule α p) :
  map_subtype.le_order_embedding p p' = map p.subtype p' := rfl

def map_subtype.lt_order_embedding :
  ((<) : submodule α p → submodule α p → Prop) ≼o ((<) : submodule α β → submodule α β → Prop) :=
(map_subtype.le_order_embedding p).lt_embedding_of_le_embedding

@[simp] theorem map_inl : p.map (inl β γ) = prod p ⊥ :=
by ext ⟨x, y⟩; simp [and.left_comm, eq_comm]

@[simp] theorem map_inr : q.map (inr β γ) = prod ⊥ q :=
by ext ⟨x, y⟩; simp [and.left_comm, eq_comm]

@[simp] theorem comap_fst : p.comap (fst β γ) = prod p ⊤ :=
by ext ⟨x, y⟩; simp

@[simp] theorem comap_snd : q.comap (snd β γ) = prod ⊤ q :=
by ext ⟨x, y⟩; simp

@[simp] theorem prod_comap_inl : (prod p q).comap (inl β γ) = p := by ext; simp

@[simp] theorem prod_comap_inr : (prod p q).comap (inr β γ) = q := by ext; simp

@[simp] theorem prod_map_fst : (prod p q).map (fst β γ) = p :=
by ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ q)]

@[simp] theorem prod_map_snd : (prod p q).map (snd β γ) = q :=
by ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ p)]

@[simp] theorem ker_inl : (inl β γ).ker = ⊥ :=
by rw [ker, ← prod_bot, prod_comap_inl]

@[simp] theorem ker_inr : (inr β γ).ker = ⊥ :=
by rw [ker, ← prod_bot, prod_comap_inr]

@[simp] theorem range_fst : (fst β γ).range = ⊤ :=
by rw [range, ← prod_top, prod_map_fst]

@[simp] theorem range_snd : (snd β γ).range = ⊤ :=
by rw [range, ← prod_top, prod_map_snd]

def mkq : β →ₗ p.quotient := ⟨quotient.mk, by simp, by simp⟩

@[simp] theorem mkq_apply (x : β) : p.mkq x = quotient.mk x := rfl

def liftq (f : β →ₗ γ) (h : p ≤ f.ker) : p.quotient →ₗ γ :=
⟨λ x, _root_.quotient.lift_on' x f $
   λ a b (ab : a - b ∈ p), eq_of_sub_eq_zero $ by simpa using h ab,
 by rintro ⟨x⟩ ⟨y⟩; exact map_add f x y,
 by rintro a ⟨x⟩; exact map_smul f a x⟩

@[simp] theorem liftq_apply (f : β →ₗ γ) {h} (x : β) :
  p.liftq f h (quotient.mk x) = f x := rfl

@[simp] theorem liftq_mkq (f : β →ₗ γ) (h) : (p.liftq f h).comp p.mkq = f :=
by ext; refl

@[simp] theorem range_mkq : p.mkq.range = ⊤ :=
eq_top_iff'.2 $ by rintro ⟨x⟩; exact ⟨x, trivial, rfl⟩

@[simp] theorem ker_mkq : p.mkq.ker = p :=
by ext; simp

lemma le_comap_mkq (p' : submodule α p.quotient) : p ≤ comap p.mkq p' :=
by simpa using (comap_mono bot_le : p.mkq.ker ≤ comap p.mkq p')

@[simp] theorem mkq_map_self : map p.mkq p = ⊥ :=
by rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkq]; exact le_refl _

@[simp] theorem comap_map_mkq : comap p.mkq (map p.mkq p') = p ⊔ p' :=
by simp [comap_map_eq, sup_comm]

def mapq (f : β →ₗ γ) (h : p ≤ comap f q) : p.quotient →ₗ q.quotient :=
p.liftq (q.mkq.comp f) $ by simpa [ker_comp] using h

@[simp] theorem mapq_apply (f : β →ₗ γ) {h} (x : β) :
  mapq p q f h (quotient.mk x) = quotient.mk (f x) := rfl

theorem mapq_mkq (f : β →ₗ γ) {h} : (mapq p q f h).comp p.mkq = q.mkq.comp f :=
by ext x; refl

theorem comap_liftq (f : β →ₗ γ) (h) :
  q.comap (p.liftq f h) = (q.comap f).map (mkq p) :=
le_antisymm
  (by rintro ⟨x⟩ hx; exact ⟨_, hx, rfl⟩)
  (by rw [map_le_iff_le_comap, ← comap_comp, liftq_mkq]; exact le_refl _)

theorem ker_liftq (f : β →ₗ γ) (h) :
  ker (p.liftq f h) = (ker f).map (mkq p) := comap_liftq _ _ _ _

theorem ker_liftq_eq_bot (f : β →ₗ γ) (h) (h' : ker f = p) : ker (p.liftq f h) = ⊥ :=
by rw [ker_liftq, h', mkq_map_self]

/-- Correspondence Theorem -/
def comap_mkq.order_iso :
  ((≤) : submodule α p.quotient → submodule α p.quotient → Prop) ≃o
  ((≤) : {p' : submodule α β // p ≤ p'} → {p' : submodule α β // p ≤ p'} → Prop) :=
{ to_fun    := λ p', ⟨comap p.mkq p', le_comap_mkq p _⟩,
  inv_fun   := λ q, map p.mkq q,
  left_inv  := λ p', map_comap_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.eq' $ by simp [comap_map_mkq p, sup_of_le_right hq],
  ord       := λ p₁ p₂, (comap_le_comap_iff $ range_mkq _).symm }

def comap_mkq.le_order_embedding :
  ((≤) : submodule α p.quotient → submodule α p.quotient → Prop) ≼o ((≤) : submodule α β → submodule α β → Prop) :=
(order_iso.to_order_embedding $ comap_mkq.order_iso p).trans (subtype.order_embedding _ _)

@[simp] lemma comap_mkq_embedding_eq (p' : submodule α p.quotient) :
  comap_mkq.le_order_embedding p p' = comap p.mkq p' := rfl

def comap_mkq.lt_order_embedding :
  ((<) : submodule α p.quotient → submodule α p.quotient → Prop) ≼o ((<) : submodule α β → submodule α β → Prop) :=
(comap_mkq.le_order_embedding p).lt_embedding_of_le_embedding

end submodule

section
set_option old_structure_cmd true
structure linear_equiv {α : Type u} (β : Type v) (γ : Type w)
  [ring α] [add_comm_group β] [add_comm_group γ] [module α β] [module α γ]
  extends β →ₗ γ, β ≃ γ
end

infix ` ≃ₗ ` := linear_equiv

namespace linear_equiv
section ring
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
include α

section
variable (β)
def refl : β ≃ₗ β := { .. linear_map.id, .. equiv.refl β }
end

def symm (e : β ≃ₗ γ) : γ ≃ₗ β :=
{ .. e.to_linear_map.inverse e.inv_fun e.left_inv e.right_inv,
  .. e.to_equiv.symm }

def trans (e₁ : β ≃ₗ γ) (e₂ : γ ≃ₗ δ) : β ≃ₗ δ :=
{ .. e₂.to_linear_map.comp e₁.to_linear_map,
  .. e₁.to_equiv.trans e₂.to_equiv }

instance : has_coe (β ≃ₗ γ) (β →ₗ γ) := ⟨to_linear_map⟩

@[simp] theorem apply_symm_apply (e : β ≃ₗ γ) (c : γ) : e (e.symm c) = c := e.6 c
@[simp] theorem symm_apply_apply (e : β ≃ₗ γ) (b : β) : e.symm (e b) = b := e.5 b

@[simp] theorem coe_apply (e : β ≃ₗ γ) (b : β) : (e : β →ₗ γ) b = e b := rfl

noncomputable def of_bijective
  (f : β →ₗ γ) (hf₁ : f.ker = ⊥) (hf₂ : f.range = ⊤) : β ≃ₗ γ :=
{ ..f, ..@equiv.of_bijective _ _ f
  ⟨linear_map.ker_eq_bot.1 hf₁, linear_map.range_eq_top.1 hf₂⟩ }

@[simp] theorem of_bijective_apply (f : β →ₗ γ) {hf₁ hf₂} (x : β) :
  of_bijective f hf₁ hf₂ x = f x := rfl

def of_linear (f : β →ₗ γ) (g : γ →ₗ β)
  (h₁ : f.comp g = linear_map.id) (h₂ : g.comp f = linear_map.id) : β ≃ₗ γ :=
{ inv_fun   := g,
  left_inv  := linear_map.ext_iff.1 h₂,
  right_inv := linear_map.ext_iff.1 h₁,
  ..f }

@[simp] theorem of_linear_apply (f : β →ₗ γ) (g : γ →ₗ β) {h₁ h₂}
  (x : β) : of_linear f g h₁ h₂ x = f x := rfl

@[simp] theorem of_linear_symm_apply (f : β →ₗ γ) (g : γ →ₗ β) {h₁ h₂}
  (x : γ) : (of_linear f g h₁ h₂).symm x = g x := rfl

@[simp] protected theorem ker (f : β ≃ₗ γ) : (f : β →ₗ γ).ker = ⊥ :=
linear_map.ker_eq_bot.2 f.to_equiv.bijective.1

@[simp] protected theorem range (f : β ≃ₗ γ) : (f : β →ₗ γ).range = ⊤ :=
linear_map.range_eq_top.2 f.to_equiv.bijective.2

def of_top (p : submodule α β) (h : p = ⊤) : p ≃ₗ β :=
{ inv_fun   := λ x, ⟨x, h.symm ▸ trivial⟩,
  left_inv  := λ ⟨x, h⟩, rfl,
  right_inv := λ x, rfl,
  .. p.subtype }

@[simp] theorem of_top_apply (p : submodule α β) {h} (x : p) :
  of_top p h x = x := rfl

@[simp] theorem of_top_symm_apply (p : submodule α β) {h} (x : β) :
  ↑((of_top p h).symm x) = x := rfl

end ring

section comm_ring
variables [comm_ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
include α

def congr_right (f : γ ≃ₗ δ) : (β →ₗ γ) ≃ₗ (β →ₗ δ) :=
of_linear
  f.to_linear_map.congr_right
  f.symm.to_linear_map.congr_right
  (linear_map.ext $ λ _, linear_map.ext $ λ _, f.6 _)
  (linear_map.ext $ λ _, linear_map.ext $ λ _, f.5 _)

end comm_ring

end linear_equiv

namespace linear_map
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables (f : β →ₗ γ)

/-- First Isomorphism Law -/
noncomputable def quot_ker_equiv_range : f.ker.quotient ≃ₗ f.range :=
have hr : ∀ x : f.range, ∃ y, f y = ↑x := λ x, x.2.imp $ λ _, and.right,
let F : f.ker.quotient →ₗ f.range :=
  f.ker.liftq (cod_restrict f.range f $ λ x, ⟨x, trivial, rfl⟩)
    (λ x hx, by simp; apply subtype.coe_ext.2; simpa using hx) in
{ inv_fun    := λx, submodule.quotient.mk (classical.some (hr x)),
  left_inv   := by rintro ⟨x⟩; exact
    (submodule.quotient.eq _).2 (sub_mem_ker_iff.2 $
      classical.some_spec $ hr $ F $ submodule.quotient.mk x),
  right_inv  := λ x : range f, subtype.eq $ classical.some_spec (hr x),
  .. F }

open submodule
/-- Second Isomorphism Law -/
noncomputable def sup_quotient_equiv_quotient_inf (p p' : submodule α β) :
  (comap p.subtype (p ⊓ p')).quotient ≃ₗ
  (comap (p ⊔ p').subtype p').quotient :=
begin
  let F : (comap p.subtype (p ⊓ p')).quotient →ₗ
          (comap (p ⊔ p').subtype p').quotient :=
    (comap p.subtype (p ⊓ p')).liftq
      ((comap (p ⊔ p').subtype p').mkq.comp (of_le le_sup_left)) begin
    rw [ker_comp, of_le, comap_cod_restrict, ker_mkq, map_comap_subtype],
    exact comap_mono (inf_le_inf le_sup_left (le_refl _)),
  end,
  have hsup : ∀ x : p ⊔ p', ∃ y : p, ↑x - ↑y ∈ p',
  { rintro ⟨x, hx⟩,
    rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩,
    exact ⟨⟨y, hy⟩, by simp [hz]⟩ },
  let G := λ x, classical.some (hsup x),
  have hG : ∀ x : p ⊔ p', ↑x - ↑(G x) ∈ p' :=
    λ x, classical.some_spec (hsup x),
  refine {
    to_fun := F,
    inv_fun := λ q, quotient.lift_on' q (λ x, submodule.quotient.mk (G x)) _,
    ..F, .. },
  { refine λ x y h, (submodule.quotient.eq _).2 ⟨(G x - G y : p).2, _⟩,
    simpa using add_mem _ (sub_mem p' h (hG x)) (hG y) },
  { rintro ⟨x⟩,
    refine ((submodule.quotient.eq _).2 _).symm,
    exact ⟨(x - G _ : p).2, hG ⟨↑x, _⟩⟩ },
  { rintro ⟨x⟩, refine (quot.sound _).symm, exact hG x }
end

end linear_map
