/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of modules over commutative rings,
indexed by a discrete type.
-/

import linear_algebra.basic
import algebra.pi_instances
import data.dfinsupp

universes u v w u₁

variables (R : Type u) [comm_ring R]
variables (ι : Type v) [decidable_eq ι] (β : ι → Type w)
variables [Π i, module R (β i)]
include R

def direct_sum : Type* := ι →ₚ β

namespace direct_sum

variables {R ι β}
def mk (s : finset ι) (f : dfinsupp.finset ι β s) : direct_sum R ι β :=
dfinsupp.mk s f
local attribute [instance] dfinsupp.to_has_scalar'
instance direct_sum.module : module R (direct_sum R ι β) :=
dfinsupp.to_module

theorem mk_linear (s : finset ι) : is_linear_map (@mk _ _ _ _ β _ s) :=
{ add := λ x y, by ext i; dsimp [mk]; simp; split_ifs; [refl, simp],
  smul := λ c x, by ext i; dsimp [mk]; simp; split_ifs; [refl, simp] }

theorem mk_inj (s : finset ι) : function.injective (@mk _ _ _ _ β _ s) :=
dfinsupp.mk_inj s

def of (i : ι) (x : β i) : direct_sum R ι β :=
dfinsupp.single i x

theorem of_linear (i : ι) : is_linear_map (@of _ _ _ _ β _ i) :=
{ add := λ x y, dfinsupp.single_add,
  smul := λ c x, by ext j; dsimp [of]; simp; split_ifs; [{subst h}, simp] }

@[simp] lemma of_add (i : ι) (x y : β i) : of i (x + y) = of i x + of i y :=
(of_linear _).add _ _

@[simp] lemma of_zero (i : ι) : of i (0 : β i) = 0 :=
(of_linear _).zero

@[simp] lemma of_neg (i : ι) (x : β i) : of i (-x) = -of i x :=
(of_linear _).neg _

@[simp] lemma of_sub (i : ι) (x y : β i) : of i (x - y) = of i x - of i y :=
(of_linear _).sub _ _

@[simp] lemma of_smul (c : R) (i : ι) (x : β i) : of i (c • x) = c • of i x :=
(of_linear _).smul _ _

theorem of_inj (i : ι) : function.injective (@of _ _ _ _ β _ i) :=
λ x y H, congr_fun (mk_inj _ H) ⟨i, by simp [finset.to_set]⟩

@[elab_as_eliminator]
protected theorem induction_on {C : direct_sum R ι β → Prop}
  (x : direct_sum R ι β) (H_zero : C 0)
  (H_basic : ∀ i x, C (of i x))
  (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  apply dfinsupp.induction x H_zero,
  intros i b f h1 h2 ih,
  solve_by_elim
end

variables {γ : Type u₁} [module R γ]
variables (φ : Π i, β i → γ) (hφ : Π i, is_linear_map (φ i))
include hφ

def to_module (f : direct_sum R ι β) : γ :=
dfinsupp.lift_on' f (λ s x, s.sum $ λ i, if H : i ∈ s then φ i (x ⟨i, H⟩) else 0) $
begin
  intros s t x hst,
  refine eq.trans (finset.sum_congr rfl _) (finset.sum_subset hst _),
  { intros i h1, simp [h1, hst h1] },
  { intros i h1 h2, simp [h1, h2, (hφ i).zero] }
end 

variables {φ}

theorem to_module.linear : is_linear_map (to_module φ hφ) :=
begin
  constructor,
  { intros f g,
    refine dfinsupp.induction_on f (λ s x, _),
    refine dfinsupp.induction_on g (λ t y, _),
    change finset.sum _ _ = _,
    rw dfinsupp.mk_eq_of_subset (s ∪ t) x finset.subset_union_left,
    rw dfinsupp.mk_eq_of_subset (s ∪ t) y finset.subset_union_right,
    dsimp [to_module],
    rw ← finset.sum_add_distrib,
    apply finset.sum_congr rfl,
    intros i h1, dsimp at *,
    split_ifs; apply (hφ i).add },
  { intros c f,
    refine dfinsupp.induction_on f (λ s x, _),
    refine eq.trans (finset.sum_congr rfl _) (finset.sum_hom _ _ _),
    { intros i h1, dsimp at *, simp [h1, (hφ i).smul] },
    all_goals { simp [smul_add] } }
end

@[simp] lemma to_module.of (i x) : to_module φ hφ (of i x) = φ i x :=
by dsimp [to_module, of, dfinsupp.single]; simp

@[simp] lemma to_module.add (f g) : to_module φ hφ (f + g) = to_module φ hφ f + to_module φ hφ g :=
(to_module.linear _).add _ _

@[simp] lemma to_module.zero : to_module φ hφ 0 = 0 :=
(to_module.linear _).zero

@[simp] lemma to_module.neg (f) : to_module φ hφ (-f) = -to_module φ hφ f :=
(to_module.linear _).neg _

@[simp] lemma to_module.sub (f g) : to_module φ hφ (f - g) = to_module φ hφ f - to_module φ hφ g :=
(to_module.linear _).sub _ _

@[simp] lemma to_module.smul (c f) : to_module φ hφ (c • f) = c • to_module φ hφ f :=
(to_module.linear _).smul _ _

variables (ψ : direct_sum R ι β → γ) (hψ : is_linear_map ψ)
variables (H1 : ∀ i x, ψ (of i x) = to_module φ hφ (of i x))

theorem to_module.unique (f : direct_sum R ι β) : ψ f = to_module φ hφ f :=
direct_sum.induction_on f
  (hψ.zero.trans (to_module.linear _).zero.symm) H1 $ λ f g ihf ihg,
by rw [hψ.add, (to_module.linear _).add, ihf, ihg]

variables (ψ' : direct_sum R ι β → γ) (hψ' : is_linear_map ψ')
variables (H2 : ∀ i x, ψ (of i x) = ψ' (of i x))
omit hφ

theorem to_module.ext (f : direct_sum R ι β) : ψ f = ψ' f :=
direct_sum.induction_on f
  (hψ.zero.trans hψ'.zero.symm) H2 $ λ f g ihf ihg,
by rw [hψ.add, hψ'.add, ihf, ihg]

def set_to_set (S T : set ι) (H : S ⊆ T)
  (f : direct_sum R S (β ∘ subtype.val)) :
  direct_sum R T (β ∘ subtype.val) :=
to_module (λ (i : S) x, of ⟨i.1, H i.2⟩ x) (λ _, of_linear _) f

protected def id (M : Type v) [module R M] :
  direct_sum R punit (λ _, M) ≃ₗ M :=
{ to_fun := to_module (λ _, id) (λ _, is_linear_map.id),
  inv_fun := λ x, of punit.star x,
  left_inv := λ x, by refine to_module.ext _
      (is_linear_map.comp (of_linear _) (to_module.linear _)) _
      is_linear_map.id (λ u _, _) x;
    cases u; simp,
  right_inv := λ x, by simp,
  linear_fun := to_module.linear _ }

def to_pi (f : direct_sum R ι β) : Π i, β i :=
begin
  refine to_module (λ i x j, if h : i = j then (eq.rec_on h x) else 0) (λ i, _) f,
  constructor; intros; funext j,
  { change _ = _ + _,
    split_ifs, { subst h },
    simp },
  change _ = c • _,
  split_ifs, { subst h },
  simp
end

end direct_sum