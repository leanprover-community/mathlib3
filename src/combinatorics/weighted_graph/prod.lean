/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.weighted_graph.basic

/-!
# Weighted graphs in the product type
-/

variables {ι α β W W' : Type*} {σ : ι → Type*}

namespace weighted_graph

/-! ### Product type -/

section prod

/-- The product of two weighted graphs. -/
protected def prod (G : weighted_graph α W) (H : weighted_graph β W') :
  weighted_graph (α × β) (W × W') :=
{ weight := λ a b, (G.weight a.1 b.1).elim none (λ w, (H.weight a.2 b.2).elim none $ λ w', (w, w')),
  weight_self := λ a, by { rw G.weight_self, refl },
  weight_comm := λ a b, by rw [G.weight_comm, H.weight_comm] }

variables (G : weighted_graph (α × β) W)

/-- `G.no_fst` means `G` has no edges of the form `((a, b), (a, c))`. -/
def no_fst : Prop := ∀ a b c, ¬ G.adj (a, b) (a, c)

/-- `G.no_snd` means `G` has no edges of the form `((b, a), (c, a))`. -/
def no_snd : Prop := ∀ a b c, ¬ G.adj (b, a) (c, a)

variables {G}

lemma no_fst.fst_ne (hG : G.no_fst) {a b : α × β} (h : G.adj a b) : a.1 ≠ b.1 :=
λ hab, hG a.1 a.2 b.2 $ by rwa [prod.mk.eta, hab, prod.mk.eta]

lemma no_snd.snd_ne (hG : G.no_snd) {a b : α × β} (h : G.adj a b) : a.2 ≠ b.2 :=
λ hab, hG a.2 a.1 b.1 $ by rwa [prod.mk.eta, hab, prod.mk.eta]

end prod

/-! ### Pi type -/

section pi
open_locale classical

/-- The product of weighted graphs. -/
protected noncomputable def pi [nonempty ι] {W : ι → Type*} (G : Π i, weighted_graph (σ i) (W i)) :
  weighted_graph (Π i, σ i) (Π i, W i) :=
{ weight := λ a b, begin
    refine if h : (∀ i, (G i).weight (a i) (b i) ≠ none) then
      (some $ λ i, ((G i).weight (a i) (b i)).elim _ id) else none,
    sorry
  end,
  weight_self := λ a, dif_neg (λ h, h (classical.arbitrary ι) ((G _).weight_self _)),
  weight_comm := λ a b, begin
    split_ifs with h h' h' h',
    { ext i,
      rw (G i).weight_comm },
    { exact h' (λ i, λ H, h i $ ((G i).weight_comm _ _).trans H) },
    { exact h (λ i, λ H, h' i $ ((G i).weight_comm _ _).trans H) },
    { refl }
  end }

end pi
end weighted_graph
