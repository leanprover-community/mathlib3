/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import tactic.basic

/-!
# Extra facts about `prod`

This file defines `prod.swap : α × β → β × α` and proves various simple lemmas about `prod`.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

@[simp] lemma prod_map (f : α → γ) (g : β → δ) (p : α × β) : prod.map f g p = (f p.1, g p.2) := rfl

namespace prod

@[simp] theorem «forall» {p : α × β → Prop} : (∀ x, p x) ↔ (∀ a b, p (a, b)) :=
⟨assume h a b, h (a, b), assume h ⟨a, b⟩, h a b⟩

@[simp] theorem «exists» {p : α × β → Prop} : (∃ x, p x) ↔ (∃ a b, p (a, b)) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

theorem forall' {p : α → β → Prop} : (∀ x : α × β, p x.1 x.2) ↔ ∀ a b, p a b :=
prod.forall

theorem exists' {p : α → β → Prop} : (∃ x : α × β, p x.1 x.2) ↔ ∃ a b, p a b :=
prod.exists

@[simp] lemma snd_comp_mk (x : α) : prod.snd ∘ (prod.mk x : β → α × β) = id := rfl

@[simp] lemma fst_comp_mk (x : α) : prod.fst ∘ (prod.mk x : β → α × β) = function.const β x := rfl

@[simp] lemma map_mk (f : α → γ) (g : β → δ) (a : α) (b : β) : map f g (a, b) = (f a, g b) := rfl

lemma map_fst (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).1 = f (p.1) := rfl

lemma map_snd (f : α → γ) (g : β → δ) (p : α × β) : (map f g p).2 = g (p.2) := rfl

lemma map_fst' (f : α → γ) (g : β → δ) : (prod.fst ∘ map f g) = f ∘ prod.fst :=
funext $ map_fst f g

lemma map_snd' (f : α → γ) (g : β → δ) : (prod.snd ∘ map f g) = g ∘ prod.snd :=
funext $ map_snd f g

/--
Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions.
-/
lemma map_comp_map {ε ζ : Type*}
  (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) :
  prod.map g g' ∘ prod.map f f' = prod.map (g ∘ f) (g' ∘ f') :=
rfl

/--
Composing a `prod.map` with another `prod.map` is equal to
a single `prod.map` of composed functions, fully applied.
-/
lemma map_map {ε ζ : Type*}
  (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ) (x : α × γ) :
  prod.map g g' (prod.map f f' x) = prod.map (g ∘ f) (g' ∘ f') x :=
rfl

@[simp] theorem mk.inj_iff {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ (a₁ = a₂ ∧ b₁ = b₂) :=
⟨prod.mk.inj, by cc⟩

lemma mk.inj_left {α β : Type*} (a : α) :
  function.injective (prod.mk a : β → α × β) :=
by { intros b₁ b₂ h, simpa only [true_and, prod.mk.inj_iff, eq_self_iff_true] using h }

lemma mk.inj_right {α β : Type*} (b : β) :
  function.injective (λ a, prod.mk a b : α → α × β) :=
by { intros b₁ b₂ h, by simpa only [and_true, eq_self_iff_true, mk.inj_iff] using h }

lemma ext_iff {p q : α × β} : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 :=
by rw [← @mk.eta _ _ p, ← @mk.eta _ _ q, mk.inj_iff]

@[ext]
lemma ext {α β} {p q : α × β} (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q :=
ext_iff.2 ⟨h₁, h₂⟩

lemma map_def {f : α → γ} {g : β → δ} : prod.map f g = λ (p : α × β), (f p.1, g p.2) :=
funext (λ p, ext (map_fst f g p) (map_snd f g p))

lemma id_prod : (λ (p : α × α), (p.1, p.2)) = id :=
funext $ λ ⟨a, b⟩, rfl

lemma fst_surjective [h : nonempty β] : function.surjective (@fst α β) :=
λ x, h.elim $ λ y, ⟨⟨x, y⟩, rfl⟩

lemma snd_surjective [h : nonempty α] : function.surjective (@snd α β) :=
λ y, h.elim $ λ x, ⟨⟨x, y⟩, rfl⟩

lemma fst_injective [subsingleton β] : function.injective (@fst α β) :=
λ x y h, ext h (subsingleton.elim _ _)

lemma snd_injective [subsingleton α] : function.injective (@snd α β) :=
λ x y h, ext (subsingleton.elim _ _) h

/-- Swap the factors of a product. `swap (a, b) = (b, a)` -/
def swap : α × β → β × α := λp, (p.2, p.1)

@[simp] lemma swap_swap : ∀ x : α × β, swap (swap x) = x
| ⟨a, b⟩ := rfl

@[simp] lemma fst_swap {p : α × β} : (swap p).1 = p.2 := rfl

@[simp] lemma snd_swap {p : α × β} : (swap p).2 = p.1 := rfl

@[simp] lemma swap_prod_mk {a : α} {b : β} : swap (a, b) = (b, a) := rfl

@[simp] lemma swap_swap_eq : swap ∘ swap = @id (α × β) :=
funext swap_swap

@[simp] lemma swap_left_inverse : function.left_inverse (@swap α β) swap :=
swap_swap

@[simp] lemma swap_right_inverse : function.right_inverse (@swap α β) swap :=
swap_swap

lemma swap_injective : function.injective (@swap α β) :=
swap_left_inverse.injective

lemma swap_surjective : function.surjective (@swap α β) :=
swap_left_inverse.surjective

lemma swap_bijective : function.bijective (@swap α β) :=
⟨swap_injective, swap_surjective⟩

@[simp] lemma swap_inj {p q : α × β} : swap p = swap q ↔ p = q := swap_injective.eq_iff

lemma eq_iff_fst_eq_snd_eq : ∀{p q : α × β}, p = q ↔ (p.1 = q.1 ∧ p.2 = q.2)
| ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ := by simp

lemma fst_eq_iff : ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
| ⟨a, b⟩ x := by simp

lemma snd_eq_iff : ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
| ⟨a, b⟩ x := by simp

theorem lex_def (r : α → α → Prop) (s : β → β → Prop)
  {p q : α × β} : prod.lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2 :=
⟨λ h, by cases h; simp *,
 λ h, match p, q, h with
 | (a, b), (c, d), or.inl h := lex.left _ _ h
 | (a, b), (c, d), or.inr ⟨e, h⟩ :=
   by change a = c at e; subst e; exact lex.right _ h
 end⟩

instance lex.decidable [decidable_eq α]
  (r : α → α → Prop) (s : β → β → Prop) [decidable_rel r] [decidable_rel s] :
  decidable_rel (prod.lex r s) :=
λ p q, decidable_of_decidable_of_iff (by apply_instance) (lex_def r s).symm

@[refl] lemma lex.refl_left (r : α → α → Prop) (s : β → β → Prop) [is_refl α r] :
  ∀ x, prod.lex r s x x
| (x₁, x₂) := lex.left _ _ (refl _)

instance is_refl_left {r : α → α → Prop} {s : β → β → Prop} [is_refl α r] :
  is_refl (α × β) (lex r s) :=
⟨lex.refl_left _ _⟩

@[refl] lemma lex.refl_right (r : α → α → Prop) (s : β → β → Prop) [is_refl β s] :
  ∀ x, prod.lex r s x x
| (x₁, x₂) := lex.right _ (refl _)

instance is_refl_right {r : α → α → Prop} {s : β → β → Prop} [is_refl β s] :
  is_refl (α × β) (lex r s) :=
⟨lex.refl_right _ _⟩

@[trans] lemma lex.trans {r : α → α → Prop} {s : β → β → Prop} [is_trans α r] [is_trans β s] :
  ∀ {x y z : α × β}, prod.lex r s x y → prod.lex r s y z → prod.lex r s x z
| (x₁, x₂) (y₁, y₂) (z₁, z₂) (lex.left _ _ hxy₁) (lex.left _ _ hyz₁) :=
    lex.left _ _ (trans hxy₁ hyz₁)
| (x₁, x₂) (y₁, y₂) (z₁, z₂) (lex.left _ _ hxy₁) (lex.right _ hyz₂) := lex.left _ _ hxy₁
| (x₁, x₂) (y₁, y₂) (z₁, z₂) (lex.right _ _) (lex.left _ _ hyz₁) := lex.left _ _ hyz₁
| (x₁, x₂) (y₁, y₂) (z₁, z₂) (lex.right _ hxy₂) (lex.right _ hyz₂) := lex.right _ (trans hxy₂ hyz₂)

instance {r : α → α → Prop} {s : β → β → Prop} [is_trans α r] [is_trans β s] :
  is_trans (α × β) (lex r s) :=
⟨λ _ _ _, lex.trans⟩

instance {r : α → α → Prop} {s : β → β → Prop} [is_strict_order α r] [is_antisymm β s] :
  is_antisymm (α × β) (lex r s) :=
⟨λ x₁ x₂ h₁₂ h₂₁, match x₁, x₂, h₁₂, h₂₁ with
  | (a₁, b₁), (a₂, b₂), lex.left _ _ hr₁, lex.left _ _ hr₂ := (irrefl a₁ (trans hr₁ hr₂)).elim
  | (a₁, b₁), (a₂, b₂), lex.left _ _ hr₁, lex.right _ _ := (irrefl _ hr₁).elim
  | (a₁, b₁), (a₂, b₂), lex.right _ _, lex.left _ _ hr₂ := (irrefl _ hr₂).elim
  | (a₁, b₁), (a₂, b₂), lex.right _ hs₁, lex.right _ hs₂ := antisymm hs₁ hs₂ ▸ rfl
end⟩

instance is_total_left {r : α → α → Prop} {s : β → β → Prop} [is_total α r] :
  is_total (α × β) (lex r s) :=
⟨λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, (is_total.total a₁ a₂).imp (lex.left _ _) (lex.left _ _)⟩

instance is_total_right {r : α → α → Prop} {s : β → β → Prop} [is_trichotomous α r] [is_total β s] :
  is_total (α × β) (lex r s) :=
⟨λ ⟨i, a⟩ ⟨j, b⟩, begin
  obtain hij | rfl | hji := trichotomous_of r i j,
  { exact or.inl (lex.left _ _ hij) },
  { exact (total_of (s) a b).imp (lex.right _) (lex.right _), },
  { exact or.inr (lex.left _ _ hji) }
end⟩

end prod

open function

lemma function.injective.prod_map {f : α → γ} {g : β → δ} (hf : injective f) (hg : injective g) :
  injective (prod.map f g) :=
λ x y h, prod.ext (hf (prod.ext_iff.1 h).1) (hg $ (prod.ext_iff.1 h).2)

lemma function.surjective.prod_map {f : α → γ} {g : β → δ} (hf : surjective f) (hg : surjective g) :
  surjective (prod.map f g) :=
λ p, let ⟨x, hx⟩ := hf p.1 in let ⟨y, hy⟩ := hg p.2 in ⟨(x, y), prod.ext hx hy⟩
