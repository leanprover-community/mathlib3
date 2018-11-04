/-
Copyright (c) 2018 Mario Carneiro and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro and Kevin Buzzard
-/
import order.order_iso
import tactic.tidy

import linear_algebra.subtype_module
import linear_algebra.quotient_module
import linear_algebra.prod_module

local attribute [instance] classical.dec
open lattice function set

structure {u v} submodule (α : Type u) (β : Type v) [ring α] [module α β] : Type v :=
(carrier : set β)
(to_is_submodule : is_submodule carrier)

namespace submodule
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} [ring α] [module α β] [module α γ] [module α δ]
include α

instance : has_coe (submodule α β) (set β) := ⟨submodule.carrier⟩
instance (s : submodule α β) : is_submodule (s : set β) := submodule.to_is_submodule _
instance : has_mem β (submodule α β) := ⟨λ x y, x ∈ (y : set β)⟩

@[simp] theorem mem_coe {b : β} {s : submodule α β} : b ∈ (s : set β) ↔ b ∈ s := iff.rfl

instance : has_subset (submodule α β) := ⟨λ s t, (s : set β) ⊆ t⟩

@[extensionality] theorem ext {s t : submodule α β} (h : (s : set β) = t) : s = t :=
by cases s; cases t; congr'

protected theorem ext_iff {s t : submodule α β}  : (s : set β) = t ↔ s = t :=
iff.intro ext (assume h, h ▸ rfl)

instance : partial_order (submodule α β) :=
partial_order.lift (coe : submodule α β → set β) $ λ a b, ext

def span (s : set β) : submodule α β := ⟨span s, is_submodule_span⟩

theorem span_subset_iff {s : set β} {t : submodule α β} : span s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_span, span_minimal t.2⟩

lemma span_singleton_subset {b : β} {s : submodule α β} : span {b} ⊆ s ↔ b ∈ s :=
by rw [submodule.span_subset_iff, set.singleton_subset_iff]; refl

lemma mem_span_singleton {b₁ b₂ : β} : b₁ ∈ span ({b₂} : set β) ↔ ∃c, b₁ = c • b₂ :=
show b₁ ∈ _root_.span ({b₂} : set β) ↔ ∃c, b₁ = c • b₂,
  by simp [_root_.span_singleton, eq_comm]

protected def galois_insertion :
  galois_insertion (@span α β _ _) coe :=
{ choice := λ s h, ⟨s, by rw le_antisymm (by exact subset_span) h; exact is_submodule_span⟩,
  gc := λ s t, span_subset_iff,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, by ext1; exact le_antisymm (by exact subset_span) h }

instance : complete_lattice (submodule α β) := submodule.galois_insertion.lift_complete_lattice

instance : has_zero (submodule α β) := ⟨⊥⟩

@[simp] theorem sInter_set (S : set (submodule α β)) :
  ((Inf S : submodule α β) : set β) = ⋂ s ∈ S, ↑s := rfl

@[simp] theorem bot_set :  ((⊥ : submodule α β) : set β) = {0} := span_empty

@[simp] theorem span_empty : (span ∅ : submodule α β) = ⊥ := rfl

@[simp] theorem top_set : ((⊤ : submodule α β) : set β) = univ := rfl

@[simp] theorem Union_set_of_directed {ι} (hι : nonempty ι)
  (S : ι → submodule α β)
  (H : ∀ i j, ∃ k, S i ≤ S k ∧ S j ≤ S k) :
  ((supr S : submodule α β) : set β) = ⋃ i, S i :=
begin
  suffices su : is_submodule (⋃ i, (S i : set β)),
  { refine le_antisymm (_ : supr S ≤ ⟨_, su⟩) _,
    { exact supr_le (subset_Union (λ i, ↑(S i))) },
    { exact Union_subset (le_supr S) } },
   unfreezeI,
   exact {
    zero_ := by cases hι with i; simp [-mem_coe];
                exact ⟨i, is_submodule.zero⟩,
    add_ := begin
      simp, intros x y i hi j hj,
      rcases H i j with ⟨k, ik, jk⟩,
      exact ⟨k, is_submodule.add (ik hi) (jk hj)⟩
    end,
    smul := by simp [-mem_coe]; exact λ a x i hi,
      ⟨i, is_submodule.smul a hi⟩ }
end

theorem span_union (s t : set β) : (span (s ∪ t) : submodule α β) = span s ⊔ span t :=
(@submodule.galois_insertion α β _ _).gc.l_sup

/-- The pushforward -/
def map (f : β → γ) (h : is_linear_map f) (m : submodule α β) : submodule α γ :=
by letI := m.to_is_submodule; exact ⟨f '' m, is_submodule.image h⟩

lemma coe_map (f : β → γ) {h : is_linear_map f} (m : submodule α β) :
  (map f h m : set γ) = f '' m := rfl

lemma map_id : map (@id β) is_linear_map.id = @id (submodule α β) :=
by ext; simp [-mem_coe, coe_map]

lemma map_comp (f : β → γ) (g : γ → δ) {hf : is_linear_map f} {hg : is_linear_map g} :
  map (g ∘ f) (is_linear_map.comp hg hf) = map g hg ∘ map f hf :=
by ext : 2; simp [-mem_coe, coe_map, (set.image_comp g f _).symm]

lemma injective_map (f : β → γ) (h : is_linear_map f) (hf : injective f) : injective (map f h) :=
assume a b eq, by rwa [← submodule.ext_iff, coe_map, coe_map, image_eq_image hf, submodule.ext_iff] at eq

/-- The pullback -/
def comap (f : β → γ) (h : is_linear_map f) (m : submodule α γ) : submodule α β :=
by letI := m.to_is_submodule; exact ⟨f ⁻¹' m, is_submodule.preimage h⟩

lemma coe_comap (f : β → γ) {h : is_linear_map f} (m : submodule α γ) :
  (comap f h m : set β) = f ⁻¹' m := rfl

lemma comap_id : comap (@id β) is_linear_map.id = @id (submodule α β) :=
by ext; simp [-mem_coe, coe_comap]

lemma comap_comp (f : β → γ) (g : γ → δ) {hf : is_linear_map f} {hg : is_linear_map g} :
  comap (g ∘ f) (is_linear_map.comp hg hf) = comap f hf ∘ comap g hg :=
by ext : 2; simp [-mem_coe, coe_comap, set.preimage_comp.symm]

lemma injective_comap (f : β → γ) (h : is_linear_map f) (hf : surjective f) : injective (comap f h) :=
assume a b eq,
  by rwa [← submodule.ext_iff, coe_comap, coe_comap, preimage_eq_preimage hf, submodule.ext_iff] at eq

lemma comap_map_eq {f : β → γ} (hf : is_linear_map f) (m : submodule α β) (h : ∀x, f x = 0 → x ∈ m) :
  comap f hf (map f hf m) = m :=
begin
  rw [← submodule.ext_iff, coe_comap, coe_map],
  refine subset.antisymm _ (set.subset_preimage_image _ _),
  rintros x ⟨y, hy, eq⟩,
  have : f (y - x) = 0, { simp [eq, hf.sub, sub_self, -sub_eq_add_neg] },
  have : y - x ∈ m, from h _ this,
  suffices : y - (y - x) ∈ m, { simpa },
  exact is_submodule.sub hy this
end

section subtype
variables (α β) (s : set β) [is_submodule s]

def map_subtype : submodule α s → submodule α β :=
map (coe : s → β) (is_submodule.is_linear_map_coe _)

lemma map_subtype_subset (m : submodule α s) : ↑(map_subtype α β s m) ⊆ s :=
by rintros x ⟨y, Hy, rfl⟩; exact y.property

/-- If N ⊆ M then submodules of N are the same as submodules of M contained in N -/
def map_subtype.order_iso :
  ((≤) : submodule α s → submodule α s → Prop) ≃o
  ((≤) : {m : submodule α β // ↑m ⊆ s} → {m : submodule α β // ↑m ⊆ s} → Prop) :=
{ to_fun := λP, ⟨map_subtype α β s P, map_subtype_subset α β s P⟩,
  inv_fun := λ Q, comap (coe : s → β) (is_submodule.is_linear_map_coe _) Q,
  left_inv := by tidy,
  right_inv := by tidy,
  ord := λ X Y, ⟨by tidy, assume h : subtype.val '' ↑X ⊆ subtype.val '' ↑Y, show X ⊆ Y, from
      (image_subset_image_iff subtype.val_injective).1 h⟩ }

def map_subtype.le_order_embedding :
  ((≤) : submodule α s → submodule α s → Prop) ≼o ((≤) : submodule α β → submodule α β → Prop) :=
order_embedding.trans (order_iso.to_order_embedding $ map_subtype.order_iso α β s) (subtype.order_embedding _ _)

@[simp] lemma map_subtype_embedding_eq (P : submodule α s) :
  map_subtype.le_order_embedding α β s P = map_subtype α β s P := rfl

def lt_order_embedding :
  ((<) : submodule α s → submodule α s → Prop) ≼o ((<) : submodule α β → submodule α β → Prop) :=
(map_subtype.le_order_embedding α β s).lt_embedding_of_le_embedding

end subtype

section quotient
open quotient_module is_submodule
variables (α β) (s : set β) [is_submodule s]

def comap_quotient : submodule α (quotient β s) → submodule α β :=
submodule.comap quotient_module.mk (is_linear_map_quotient_mk s)

lemma subset_comap_quotient (m : submodule α (quotient β s)) : s ⊆ comap_quotient α β s m :=
assume n hn, show ↑n ∈ m,
by rw [← quotient_module.coe_eq_zero s] at hn;
from hn.symm ▸ @is_submodule.zero _ _ _ _ (m : set (quotient β s)) _

/-- Correspondence Theorem -/
def comap_quotient.order_iso :
  ((≤) : submodule α (quotient β s) → submodule α (quotient β s) → Prop) ≃o
  ((≤) : {m : submodule α β // s ⊆ m} → {m : submodule α β // s ⊆ m} → Prop) :=
{ to_fun := λm, ⟨comap_quotient α β s m, subset_comap_quotient α β s m⟩,
  inv_fun := λ X, submodule.map quotient_module.mk (is_linear_map_quotient_mk s) X,
  left_inv := λ P, submodule.ext $ set.image_preimage_eq quotient_module.quotient.exists_rep,
  right_inv :=
  begin
    rintros ⟨P, hP⟩,
    have : ∀ (x : β), (x : quotient β s) = (0 : quotient β s) → x ∈ P,
    { assume a, rw [quotient_module.coe_eq_zero s], exact @hP a },
    simp [comap_quotient, comap_map_eq (is_linear_map_quotient_mk s) P this]
  end,
  ord := by tidy }

end quotient

section prod

def prod (s : submodule α β) (t : submodule α γ) : submodule α (β × γ) :=
comap prod.fst prod.is_linear_map_prod_fst s ⊓ comap prod.snd prod.is_linear_map_prod_snd t

lemma coe_prod (s : submodule α β) (t : submodule α γ) : (prod s t : set (β × γ)) = set.prod s t :=
rfl

end prod

end submodule

namespace quotient_module

def le_order_embedding (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
  ((≤) : submodule R (quotient M N) → submodule R (quotient M N) → Prop) ≼o
  ((≤): submodule R M → submodule R M → Prop) :=
order_embedding.trans (order_iso.to_order_embedding $
  submodule.comap_quotient.order_iso R M N) (subtype.order_embedding _ _)

def lt_order_embedding (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
  ((<) : submodule R (quotient M N) → submodule R (quotient M N) → Prop) ≼o
  ((<) : submodule R M → submodule R M → Prop) :=
(quotient_module.le_order_embedding R M N).lt_embedding_of_le_embedding

end quotient_module
