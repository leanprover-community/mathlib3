/-
Copyright (c) 2017 Mario Carneiro and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro and Kevin Buzzard
-/

import linear_algebra.subtype_module
import tactic.tidy -- for cheap proofs
import order.order_iso -- because we're going to prove order embeddings

local attribute [instance] classical.dec
open set lattice

-- Mario wrote the next 30 lines and KMB moved them here from noetherian.lean

-- KMB says: why not use a subtype? Is s and sub preferable to val and property?
-- We lose all the API for subtype this way. Not that I ever use it...
structure {u v} submodule (α : Type u) (β : Type v)
  [ring α] [module α β] : Type v :=
(s : set β)
(sub : is_submodule s)

namespace submodule
universes u v
variables {α : Type u} {β : Type v} [ring α] [module α β]

instance : has_coe (submodule α β) (set β) := ⟨submodule.s⟩

instance (s : submodule α β) : is_submodule (s : set β) :=
submodule.sub _

instance : has_mem β (submodule α β) := ⟨λ x y, x ∈ (y : set β)⟩

@[simp] theorem mem_coe {b : β} {s : submodule α β} :
  b ∈ (s : set β) ↔ b ∈ s := iff.rfl

instance : has_subset (submodule α β) := ⟨λ s t, (s : set β) ⊆ t⟩

@[extensionality] theorem ext {s t : submodule α β}
  (H : (s : set β) = t) : s = t :=
by cases s; cases t; congr'

instance : partial_order (submodule α β) :=
{ le := (⊆),
  le_refl := λ a, subset.refl _,
  le_trans := λ a b c, subset.trans,
  le_antisymm := λ a b h₁ h₂, ext (subset.antisymm h₁ h₂) }

-- the next 50 or so lines is KMB

theorem eq : ∀ {s t : submodule α β}, s.s = t.s → s = t
| ⟨ss,_⟩ ⟨_,_⟩ rfl := rfl  

definition pushforward {R} [ring R] {M} [module R M] {N} [module R N] (f : M → N) (h : is_linear_map f)
  (P : submodule R M) : submodule R N :=
by haveI : is_submodule (P.s) := P.sub;exact { s := f '' P.s, sub := is_submodule.image h}

definition pullback {R} [ring R] {M} [module R M] {N} [module R N] (f : M → N) (h : is_linear_map f)
  (Q : submodule R N) : submodule R M :=
by haveI : is_submodule (Q.s) := Q.sub;exact { s := f ⁻¹' Q.s, sub := is_submodule.preimage h}

-- this proof is rubbish
def pushforward_injective_of_injective {R} [ring R] {M} [module R M] {N} [module R N] (f : M → N)
  (h : is_linear_map f) (hinj : function.injective f) : function.injective (pushforward f h) :=
λ P Q HPQ, submodule.eq $ begin 
  rw ←preimage_image_eq P.s hinj, 
  rw ←preimage_image_eq Q.s hinj, 
  congr' 1,
  unfold pushforward at HPQ,
  revert HPQ,simp,
end

-- so is this one
def pullback_injective_of_surjective {R} [ring R] {M} [module R M] {N} [module R N] (f : M → N)
  (h : is_linear_map f) (hsurj : function.surjective f) : function.injective (pullback f h) :=
λ P Q HPQ, submodule.eq $ begin 
  rw ←@image_preimage_eq _ _ _ P.s hsurj,
  rw ←@image_preimage_eq _ _ _ Q.s hsurj,
  congr' 1,
  unfold pullback at HPQ,
  revert HPQ,simp,
end

/-- If N ⊆ M then submodules of N are the same as submodules of M contained in N -/
definition order_iso (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
(has_le.le : submodule R N → submodule R N → Prop) ≃o
  (has_le.le : {Q : submodule R M // Q.s ⊆ N} → {Q : submodule R M // Q.s ⊆ N} → Prop) := 
{ to_fun := λ P,⟨pushforward (subtype.val : N → M)
    (@is_submodule.is_linear_map_inclusion R M _ _ N _) P,
    λ x Hx,begin cases Hx with y Hy,rw ←Hy.2,exact y.property end⟩,
  inv_fun := λ Q,pullback (subtype.val : N → M)
    (@is_submodule.is_linear_map_inclusion R M _ _ N _) Q.val,
  left_inv := by tidy, -- a.k.a. begin intros x, ext1, ext1, cases x_1, dsimp at *, simp at *, fsplit, work_on_goal 0 { intros a, cases a, cases a_h, cases a_w, dsimp at *, induction a_h_right, assumption }, intros a, fsplit, work_on_goal 0 { fsplit, work_on_goal 1 { assumption } }, dsimp at *, simp at *, assumption end,
  right_inv := by tidy, -- a.k.a. begin intros x, cases x, dsimp at *, simp at *, ext1, ext1, simp at *, fsplit, work_on_goal 0 { intros a, cases a, cases a_h, cases a_w, induction a_h_right, assumption }, intros a, fsplit, work_on_goal 0 { fsplit, work_on_goal 1 { solve_by_elim } }, dsimp at *, simp at *, assumption end,
  ord := λ X Y,⟨by tidy,begin 
    show subtype.val '' ↑X ⊆ subtype.val '' ↑Y → X ⊆ Y,
    intros H x Hx,
    rcases @H x.val ⟨x,Hx,rfl⟩ with ⟨x',H1,H2⟩, -- probably why tidy failed. Can this proof be tidied?
    convert H1,exact subtype.eq H2.symm,
  end⟩
}

definition submodule_of_submodule (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
  submodule R N → submodule R M := pushforward (subtype.val : N → M) (is_submodule.is_linear_map_inclusion)

definition le_order_embedding (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
(has_le.le : submodule R N → submodule R N → Prop) ≼o
  (has_le.le : submodule R M → submodule R M → Prop) := 
order_embedding.trans (order_iso.to_order_embedding $ order_iso R M N) (subtype.order_embedding _ _)

@[simp] lemma embedding_eq (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] (P : submodule R N) :
  le_order_embedding R M N P = submodule_of_submodule R M N P := rfl

definition submodule_lt_equiv (R) [ring R] (M) [module R M] (N : set M) [is_submodule N]
  (X Y : submodule R N) :
X < Y ↔ ((le_order_embedding R M N) X) < ((le_order_embedding R M N) Y) :=
by simp [lt_iff_le_not_le,(order_iso R M N).ord];refl -- why do I need refl after simp??

definition lt_order_embedding (R) [ring R] (M) [module R M] (N : set M) [is_submodule N] :
(has_lt.lt : submodule R N → submodule R N → Prop) ≼o (has_lt.lt : submodule R M → submodule R M → Prop) :=
{ to_fun := submodule_of_submodule R M N,
  inj := (le_order_embedding R M N).inj,
  ord := submodule_lt_equiv R M N
  }

-- now back to Mario
def span (s : set β) : submodule α β := ⟨span s, is_submodule_span⟩

theorem span_subset_iff {s : set β} {t : submodule α β} :
  span s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_span, span_minimal t.2⟩

protected def galois_insertion :
  galois_insertion (@span α β _ _) coe :=
{ choice := λ s h, ⟨s,
    by rw le_antisymm (by exact subset_span) h;
       exact is_submodule_span⟩,
  gc := λ s t, span_subset_iff,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, by ext1; exact
    le_antisymm (by exact subset_span) h }

instance : complete_lattice (submodule α β) :=
submodule.galois_insertion.lift_complete_lattice

@[simp] theorem sInter_set (S : set (submodule α β)) :
  ((Inf S : submodule α β) : set β) = ⋂ s ∈ S, ↑s := rfl

@[simp] theorem bot_set :
  ((⊥ : submodule α β) : set β) = {0} := span_empty

@[simp] theorem span_empty : (span ∅ : submodule α β) = ⊥ := rfl

@[simp] theorem top_set :
  ((⊤ : submodule α β) : set β) = univ := rfl

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

theorem span_union (s t : set β) :
  (span (s ∪ t) : submodule α β) = span s ⊔ span t :=
(@submodule.galois_insertion α β _ _).gc.l_sup

end submodule