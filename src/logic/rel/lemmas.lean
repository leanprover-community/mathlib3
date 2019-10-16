/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Yury Kudryashov
-/
import logic.rel.defs data.set.basic

/-!
# Various properties of relations

In this file we prove various simple properties of relations that do not involve `≤`.
-/

universes u v w x

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace function

variable (α)

lemma graph'_id : function.graph' (@id α) = rel.id α := rfl

variables {α} (g : β → γ) (f : α → β)

lemma graph'_right_unique : (function.graph' f).right_unique :=
λ x y₁ y₂ h₁ h₂, h₁.symm.trans h₂

lemma graph'_left_total : (function.graph' f).left_total :=
λ x, ⟨f x, rfl⟩

lemma graph'_comp (g : β → γ) (f : α → β) :
  function.graph' (g ∘ f) = rel.comp (function.graph' g) (function.graph' f) :=
by ext x z; symmetry; apply exists_eq_right'

theorem graph'_mk (f : α → β) (x : α) : graph' f x (f x) := eq.refl (f x)

theorem graph'_inj : function.injective $ @function.graph' α β :=
assume f g h, funext $ assume x,
show graph' f x (g x),
from h.symm ▸ graph'_mk g x

lemma graph_def (f : α → β) : function.graph f = { x : α × β | f x.1 = x.2 } := rfl

variable {f}

lemma injective.graph'_left_unique (h : injective f) : (graph' f).left_unique :=
λ x₁ x₂ y h₁ h₂, h (eq.trans h₁ h₂.symm)

lemma graph'_left_unique_iff_injective : (graph' f).left_unique ↔ injective f :=
⟨λ h x₁ x₂ hx, h hx rfl, injective.graph'_left_unique⟩

lemma surjective.graph'_right_total (h : surjective f) : (graph' f).right_total := h

lemma graph'_right_total_iff_surjective : (graph' f).right_total ↔ surjective f := iff.rfl

end function


namespace rel

-- Even if we mark it with `@[extensionality]`, `ext` won't use it.
lemma ext {r r' : rel α β} (h : ∀ x y, r x y ↔ r' x y) : r = r' := by ext; apply h

variables (r : rel α β) (rcd : rel γ δ) {rbc : rel β γ} {rab : rel α β}

lemma conv_def (x : α) (y : β) : r.conv y x ↔ r x y := iff.rfl

@[simp] lemma conv_conv : r.conv.conv = r := rfl

lemma conv_inj : function.injective (@rel.conv α β) :=
λ r r' h, congr_arg rel.conv h

local infixr ` ∘r `:80 := rel.comp

lemma comp_mk {x y z} (hyz : rbc y z) (hxy : rab x y) : (rbc ∘r rab) x z :=
⟨y, ⟨hyz, hxy⟩⟩

variables (rbc rab)

lemma comp_assoc: (rcd ∘r rbc) ∘r rab = rcd ∘r rbc ∘r rab :=
ext $ assume x w,
  ⟨λ ⟨y, ⟨⟨z, ⟨hzw, hyz⟩⟩, hxy⟩⟩, comp_mk hzw (comp_mk hyz hxy),
   λ ⟨z, ⟨hzw, ⟨y, ⟨hyz, hxy⟩⟩⟩⟩, ⟨y, ⟨⟨z, ⟨hzw, hyz⟩⟩, hxy⟩⟩⟩

@[simp] lemma comp_id : r ∘r (rel.id α) = r :=
by { ext, apply exists_eq_right' }

@[simp] lemma id_comp : (rel.id β) ∘r r = r :=
by { ext, apply exists_eq_left }

lemma iff_eq_id : (↔) = (rel.id Prop) := by funext; apply iff_eq_eq

@[simp] lemma comp_iff (r : rel Prop α) : r ∘r (↔) = r :=
iff_eq_id.symm ▸ comp_id r

@[simp] lemma iff_comp (r : rel α Prop) : (↔) ∘r r = r :=
iff_eq_id.symm ▸ id_comp r

@[simp] lemma conv_id : (rel.id α).conv = rel.id α :=
by { ext x y, apply eq_comm }

@[simp] lemma conv_comp (r : rel β γ) (s : rel α β) :
  (r ∘r s).conv = s.conv ∘r r.conv :=
by { ext x z, simp only [comp, conv_def, and.comm] }

lemma diag_conv (r : rel α α) : r.conv.diag = r.diag := rfl

lemma mem_graph {x : α × β} : x ∈ r.graph ↔ r x.fst x.snd := iff.rfl

lemma mk_mem_graph {x : α} {y : β} : (x, y) ∈ r.graph ↔ r x y := iff.rfl

lemma graph_of_graph (s : set (α × β)) : (of_graph s).graph = s := function.uncurry'_curry s

lemma of_graph_graph : of_graph r.graph = r := function.curry_uncurry' r

lemma codom_conv : r.conv.codom = r.dom := rfl

lemma dom_conv : r.conv.dom = r.codom := rfl

lemma image_def (s : set α) : image r s = {y | ∃ x ∈ s, r x y} := rfl

variable {r}

lemma mem_image (y : β) (s : set α) : y ∈ image r s ↔ ∃ x ∈ s, r x y :=
iff.rfl

variables (r)

lemma image_singleton (x : α) : r.image {x} = set_of (r x) :=
by ext y; simp [rel.image, set.mem_singleton_iff, exists_prop, exists_eq_left]

@[simp] lemma image_id (s : set α) : image (rel.id α) s = s :=
by { ext x, simp only [mem_image, rel.id, exists_prop, exists_eq_right] }

@[simp] lemma image_comp (s : set α) : image (rbc ∘r rab) s = image rbc (image rab s) :=
set.subset.antisymm
  (λ z ⟨x, ⟨xs, ⟨y, ⟨hyz, hxy⟩⟩⟩⟩, ⟨y, ⟨⟨x, ⟨xs, hxy⟩⟩, hyz⟩⟩)
  (λ z ⟨y, ⟨⟨x, ⟨xs, hxy⟩⟩, hyz⟩⟩, ⟨x, ⟨xs, ⟨y, ⟨hyz, hxy⟩⟩⟩⟩)

lemma image_univ : r.image set.univ = r.codom := by { ext y, simp [mem_image, codom] }

lemma mem_preimage (x : α) (s : set β) : x ∈ preimage r s ↔ ∃ y ∈ s, r x y :=
iff.rfl

lemma preimage_def (s : set β) : preimage r s = {x | ∃ y ∈ s, r x y} :=
rfl

lemma preimage_singleton (y : β) : r.preimage {y} = set_of (flip r y) :=
r.conv.image_singleton y

lemma preimage_id (s : set α) : (rel.id α).preimage s = s :=
by simp only [preimage, conv_id, image_id]

lemma preimage_comp (s : set γ) : (rbc ∘r rab).preimage s = rab.preimage (rbc.preimage s) :=
by simp only [preimage, conv_comp, image_comp]

lemma preimage_univ : r.preimage set.univ = r.dom :=
r.conv.image_univ

lemma mem_core (x : α) (s : set β) : x ∈ core r s ↔ ∀ y, r x y → y ∈ s :=
iff.rfl

lemma core_univ : r.core set.univ = set.univ := set.ext (by simp [mem_core])

lemma core_id (s : set α) : (rel.id α).core s = s :=
by simp [core, rel.id]

lemma core_comp (s : set γ) : (rbc ∘r rab).core s = rab.core (rbc.core s) :=
set.subset.antisymm
  (λ x h y hxy z hyz, h ⟨y, ⟨hyz, hxy⟩⟩)
  (λ x h z ⟨y, ⟨hyz, hxy⟩⟩, h hxy hyz)

lemma compl_dom_subset_core (s : set β) : - r.dom ⊆ r.core s :=
assume x hx y rxy,
absurd (Exists.intro y rxy) hx

/-- Restrict the domain of a relation -/
def restrict_domain (s : set α) : rel {x // x ∈ s} β :=
λ x y, r x.val y

theorem image_subset_iff (s : set α) (t : set β) : image r s ⊆ t ↔ s ⊆ core r t :=
iff.intro
  (λ h x xs y rxy, h ⟨x, xs, rxy⟩)
  (λ h y ⟨x, xs, rxy⟩, h xs rxy)

variables (rac : rel α γ) (rbd : rel β δ)

lemma conv_rel : (rac ⟹ rbd).conv = (rac.conv ⟹ rbd.conv) :=
rel.ext $ λ f g, ⟨λ hfg y x hxy, hfg hxy, λ hfg x y hxy, hfg hxy⟩

lemma rel_id : (rac ⟹ rac) id id := λ x y, id

lemma rel_imp : ((↔) ⟹ ((↔)  ⟹ (↔))).diag implies :=
assume p q h r s l, imp_congr h l

lemma rel_not : ((↔) ⟹ (↔)).diag not :=
assume p q h, not_congr h

lemma rel_and : ((↔) ⟹ (↔) ⟹ (↔)).diag (∧) :=
assume a b h₁ c d h₂, and_congr h₁ h₂

lemma rel_or : ((↔) ⟹ (↔) ⟹ (↔)).diag (∨) :=
assume a b h₁ c d h₂, or_congr h₁ h₂

lemma rel_iff : ((↔) ⟹ (↔) ⟹ (↔)).diag (↔) :=
assume a b h₁ c d h₂, iff_congr h₁ h₂

lemma rel_comp {α α' β β' γ γ' : Type*} {ra : rel α α'} {rb : rel β β'} {rc : rel γ γ'} :
  ((rb ⟹ rc) ⟹ (ra ⟹ rb) ⟹ (ra ⟹ rc)) (@function.comp α β γ) (@function.comp α' β' γ') :=
assume g₁ g₂ hg f₁ f₂ hf x₁ x₂ hx, hg (hf hx)

variables {r}

variables (α) {r}

lemma left_total_id : left_total (rel.id α) := λ x, ⟨x, rfl⟩
lemma right_total_id : right_total (rel.id α) := λ x, ⟨x, rfl⟩
lemma bi_total_id : bi_total (rel.id α) := ⟨left_total_id α, right_total_id α⟩

lemma left_unique_id : left_unique (rel.id α) := λ a b c hab hcb, hab.trans hcb.symm
lemma right_unique_id : right_unique (rel.id α) := λ a b c hab hac, hab.symm.trans hac
lemma bi_unique_id : bi_unique (rel.id α) := ⟨left_unique_id α, right_unique_id α⟩

variable {α}

lemma left_total.conv (h : r.left_total) : r.conv.right_total := h
lemma right_total.conv (h : r.right_total) : r.conv.left_total := h
lemma bi_total.conv (h : r.bi_total) : r.conv.bi_total := and.symm h

lemma left_unique.conv (h : r.left_unique) : r.conv.right_unique := λ a b c hab, h hab
lemma right_unique.conv (h : r.right_unique) : r.conv.left_unique := λ a b c hab, h hab
lemma bi_unique.conv (h : r.bi_unique) : r.conv.bi_unique := ⟨h.2.conv, h.1.conv⟩

variables {rbc rab}

lemma left_total.comp (hbc : rbc.left_total) (hab : rab.left_total) :
  (rbc.comp rab).left_total :=
begin
  intro x,
  rcases (hab x) with ⟨y, hxy⟩,
  rcases (hbc y) with ⟨z, hyz⟩,
  exact ⟨z, ⟨y, ⟨hyz, hxy⟩⟩⟩
end

lemma right_total.comp (hbc : rbc.right_total) (hab : rab.right_total) :
  (rbc.comp rab).right_total :=
by simpa only [conv_comp, conv_conv] using (hab.conv.comp hbc.conv).conv

lemma bi_total.comp (hbc : rbc.bi_total) (hab : rab.bi_total) : (rbc.comp rab).bi_total :=
⟨hbc.1.comp hab.1, hbc.2.comp hab.2⟩

lemma left_unique.comp (hbc : rbc.left_unique) (hab : rab.left_unique) :
  (rbc.comp rab).left_unique :=
begin
  rintros x₁ x₂ z ⟨y₁, ⟨hy₁z, hx₁y₁⟩⟩ ⟨y₂, ⟨hy₂z, hx₂y₂⟩⟩,
  have : y₁ = y₂ := hbc hy₁z hy₂z,
  subst y₂,
  exact hab hx₁y₁ hx₂y₂
end

lemma right_unique.comp (hbc : rbc.right_unique) (hab : rab.right_unique) :
  (rbc.comp rab).right_unique :=
by simpa only [conv_comp, conv_conv] using (hab.conv.comp hbc.conv).conv

lemma bi_unique.comp (hbc : rbc.bi_unique) (hab : rab.bi_unique) : (rbc.comp rab).bi_unique :=
⟨hbc.1.comp hab.1, hbc.2.comp hab.2⟩

lemma bi_unique.rel_eq (hr : r.bi_unique) : (r ⟹ r ⟹ (↔)) (=) (=) :=
assume x y h₁ x' y' h₂,
iff.intro
  begin intro h, subst h, exact hr.right h₁ h₂ end
  begin intro h, subst h, exact hr.left h₁ h₂ end

lemma left_total.rel_forall (hr : r.left_total) :
  ((r ⟹ (rel.conv implies)) ⟹ (rel.conv implies)) (λp, ∀i, p i) (λq, ∀i, q i) :=
assume p q Hrel H a, let ⟨b, Rab⟩ := hr a in Hrel Rab (H b)

lemma right_total.rel_forall (hr : r.right_total) :
  ((r ⟹ implies) ⟹ implies) (λp, ∀i, p i) (λq, ∀i, q i) :=
assume p q Hrel H b, let ⟨a, Rab⟩ := hr b in Hrel Rab (H a)

lemma left_total.rel_exists (hr : r.left_total) :
  ((r ⟹ implies) ⟹ implies) (λp, ∃i, p i) (λq, ∃i, q i) :=
assume p q Hrel ⟨a, pa⟩, let ⟨b, hab⟩ := hr a in ⟨b, Hrel hab pa⟩

lemma right_total.rel_exists (hr : r.right_total) :
  ((r ⟹ (rel.conv implies)) ⟹ (rel.conv implies)) (λp, ∃i, p i) (λq, ∃i, q i) :=
assume p q Hrel ⟨b, qb⟩, let ⟨a, hab⟩ := hr b in ⟨a, Hrel hab qb⟩

lemma comap₂_def (f : α → β) (g : γ → δ) (r : rel β δ) (x y) :
  r.comap₂ f g x y = r (f x) (g y) := rfl

lemma comap₂_comap₂ {α₁ α₂ α₃ β₁ β₂ β₃ : Type*}
  (f₂ : α₂ → α₃) (f₁ : α₁ → α₂) (g₂ : β₂ → β₃) (g₁ : β₁ → β₂) (r : rel α₃ β₃) :
  (r.comap₂ f₂ g₂).comap₂ f₁ g₁ = r.comap₂ (f₂ ∘ f₁) (g₂ ∘ g₁) :=
rfl

lemma comap_def (f : α → β) (r : rel β β) (x y : α) : r.comap f x y = r (f x) (f y) := rfl

lemma comap_comap (g : β → γ) (f : α → β) (r : rel γ γ) :
  (r.comap g).comap f = r.comap (g ∘ f) :=
rfl

lemma map₂_def (f : α → β) (g : γ → δ) (r : rel α γ) (x y) :
  r.map₂ f g x y ↔ ∃ a c, f a = x ∧ g c = y ∧ r a c :=
⟨λ ⟨c, hc, a, hr, ha⟩, ⟨a, c, ha, hc, hr⟩,
  λ ⟨a, c, ha, hc, hr⟩, ⟨c, hc, a, hr, ha⟩⟩

lemma map₂_map₂ {α₁ α₂ α₃ β₁ β₂ β₃ : Type*}
  (f₂ : α₂ → α₃) (f₁ : α₁ → α₂) (g₂ : β₂ → β₃) (g₁ : β₁ → β₂) (r : rel α₁ β₁) :
  (r.map₂ f₁ g₁).map₂ f₂ g₂ = r.map₂ (f₂ ∘ f₁) (g₂ ∘ g₁) :=
by simp only [map₂, function.graph'_comp g₂ g₁, function.graph'_comp f₂ f₁,
              conv_comp, rel.comp_assoc]

lemma map_def (f : α → β) (r : rel α α) (x y : β) :
  r.map f x y ↔ ∃ a b, f a = x ∧ f b = y ∧ r a b :=
r.map₂_def f f x y

lemma map_map (g : β → γ) (f : α → β) (r : rel α α) :
  (r.map f).map g = r.map (g ∘ f) :=
r.map₂_map₂ g f g f

end rel
