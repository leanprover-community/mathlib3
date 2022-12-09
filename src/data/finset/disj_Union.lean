/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
import data.finset.sigma
import data.finset.powerset
import data.set.pairwise

/-!
# Disjoint bounded union of finite sets

This file is about the bounded union of a disjoint indexed family `t : α → finset β` of finite
sets over a finite set `s : finset α`. In most cases `finset.bUnion` should be preferred.
-/

namespace finset

variables {α β γ : Type*}

section disj_Union
variables {s s₁ s₂ : finset α} {t t₁ t₂ : α → finset β}

open multiset

/-- `disj_Union s f h` is the set such that `a ∈ disj_Union s f` iff `a ∈ f i` for some `i ∈ s`.
It is the same as `s.bUnion f`, but it does not require decidable equality on the type. The
hypothesis ensures that the sets are disjoint. -/
def disj_Union (s : finset α) (t : α → finset β)
  (hf : (s : set α).pairwise_disjoint t) : finset β :=
⟨(s.val.bind (finset.val ∘ t)), multiset.nodup_bind.mpr
  ⟨λ a ha, (t a).nodup, s.nodup.pairwise $ λ a ha b hb hab, finset.disjoint_val.1 $ hf ha hb hab⟩⟩

@[simp] theorem disj_Union_val (s : finset α) (t : α → finset β) (h) :
  (s.disj_Union t h).1 = (s.1.bind (λ a, (t a).1)) := rfl

@[simp] theorem disj_Union_empty (t : α → finset β) : disj_Union ∅ t (by simp) = ∅ := rfl

@[simp] lemma mem_disj_Union {b : β} {h} :
  b ∈ s.disj_Union t h ↔ ∃ a ∈ s, b ∈ t a :=
by simp only [mem_def, disj_Union_val, mem_bind, exists_prop]

@[simp, norm_cast] lemma coe_disj_Union {h} : (s.disj_Union t h : set β) = ⋃ x ∈ (s : set α), t x :=
by simp only [set.ext_iff, mem_disj_Union, set.mem_Union, iff_self, mem_coe, implies_true_iff]

@[simp] theorem disj_Union_cons (a : α) (s : finset α) (ha : a ∉ s) (f : α → finset β) (H) :
  disj_Union (cons a s ha) f H = (f a).disj_union
    (s.disj_Union f $
      λ b hb c hc, H (mem_cons_of_mem hb) (mem_cons_of_mem hc))
    (disjoint_left.mpr $ λ b hb h, let ⟨c, hc, h⟩ := mem_disj_Union.mp h in
      disjoint_left.mp
        (H (mem_cons_self a s) (mem_cons_of_mem hc) (ne_of_mem_of_not_mem hc ha).symm) hb h)
      :=
eq_of_veq $ multiset.cons_bind _ _ _

@[simp] lemma singleton_disj_Union (a : α) {h} : finset.disj_Union {a} t h = t a :=
eq_of_veq $ multiset.singleton_bind _ _


lemma disj_Union_disj_Union (s : finset α) (f : α → finset β) (g : β → finset γ) (h1 h2) :
  (s.disj_Union f h1).disj_Union g h2 =
    s.attach.disj_Union (λ a, (f a).disj_Union g $
      λ b hb c hc, h2 (mem_disj_Union.mpr ⟨_, a.prop, hb⟩) (mem_disj_Union.mpr ⟨_, a.prop, hc⟩))
      (λ a ha b hb hab, disjoint_left.mpr $ λ x hxa hxb, begin
        obtain ⟨xa, hfa, hga⟩ := mem_disj_Union.mp hxa,
        obtain ⟨xb, hfb, hgb⟩ := mem_disj_Union.mp hxb,
        refine disjoint_left.mp (h2
          (mem_disj_Union.mpr ⟨_, a.prop, hfa⟩) (mem_disj_Union.mpr ⟨_, b.prop, hfb⟩) _) hga hgb,
        rintro rfl,
        exact disjoint_left.mp (h1 a.prop b.prop $ subtype.coe_injective.ne hab) hfa hfb,
      end) :=
eq_of_veq $ multiset.bind_assoc.trans (multiset.attach_bind_coe _ _).symm

lemma disj_Union_filter_eq_of_maps_to [decidable_eq β] {s : finset α} {t : finset β} {f : α → β}
  (h : ∀ x ∈ s, f x ∈ t) :
  t.disj_Union (λ a, s.filter $ (λ c, f c = a))
    (λ x' hx y' hy hne, disjoint_filter_filter' _ _ begin
      simp_rw [pi.disjoint_iff, Prop.disjoint_iff],
      rintros i ⟨rfl, rfl⟩,
      exact hne rfl,
    end) = s :=
ext $ λ b, by simpa using h b

@[simp] lemma disj_Union_eq_bUnion [decidable_eq β] (s : finset α) (f : α → finset β) (hf) :
  s.disj_Union f hf = s.bUnion f :=
begin
  dsimp [disj_Union, finset.bUnion, function.comp],
  generalize_proofs h,
  exact eq_of_veq h.dedup.symm,
end

end disj_Union

section map

theorem map_disj_Union {f : α ↪ β} {s : finset α} {t : β → finset γ} {h} :
  (s.map f).disj_Union t h = s.disj_Union (λa, t (f a))
    (λ a ha b hb hab, h (mem_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.injective.ne hab)) :=
eq_of_veq $ multiset.bind_map _ _ _

theorem disj_Union_map {s : finset α} {t : α → finset β} {f : β ↪ γ} {h} :
  (s.disj_Union t h).map f = s.disj_Union (λa, (t a).map f)
    (λ a ha b hb hab, disjoint_left.mpr $ λ x hxa hxb, begin
      obtain ⟨xa, hfa, rfl⟩ := mem_map.mp hxa,
      obtain ⟨xb, hfb, hfab⟩ := mem_map.mp hxb,
      obtain rfl := f.injective hfab,
      exact disjoint_left.mp (h ha hb hab) hfa hfb,
    end) :=
eq_of_veq $ multiset.map_bind _ _ _

end map

section fold
variables {op : β → β → β} [is_commutative β op] [is_associative β op] {f : α → β}
local notation (name := op) a ` * ` b := op a b

theorem fold_disj_Union {ι : Type*} {s : finset ι} {t : ι → finset α} {b : ι → β} {b₀ : β} (h) :
  (s.disj_Union t h).fold op (s.fold op b₀ b) f = s.fold op b₀ (λ i, (t i).fold op (b i) f) :=
(congr_arg _ $ multiset.map_bind _ _ _).trans (multiset.fold_bind _ _ _ _ _)

end fold

section sigma
open function

@[simp]
lemma disj_Union_map_sigma_mk {ι : Type*} {α : ι → Type*} {s : finset ι} {t : Π i, finset (α i)} :
  s.disj_Union (λ i, (t i).map (embedding.sigma_mk i))
    pairwise_disjoint_map_sigma_mk = s.sigma t := rfl

end sigma

section powerset
variables {s t : finset α}

lemma powerset_card_disj_Union (s : finset α) :
  finset.powerset s =
    (range (s.card + 1)).disj_Union (λ i, powerset_len i s)
      (s.pairwise_disjoint_powerset_len.set_pairwise _) :=
begin
  refine ext (λ a, ⟨λ ha, _, λ ha, _ ⟩),
  { rw mem_disj_Union,
    exact ⟨a.card, mem_range.mpr (nat.lt_succ_of_le (card_le_of_subset (mem_powerset.mp ha))),
      mem_powerset_len.mpr ⟨mem_powerset.mp ha, rfl⟩⟩ },
  { rcases mem_disj_Union.mp ha with ⟨i, hi, ha⟩,
    exact mem_powerset.mpr (mem_powerset_len.mp ha).1, }
end

end powerset

end finset
