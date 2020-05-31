/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of modules over commutative rings, indexed by a discrete type.
-/
import algebra.direct_sum
import linear_algebra.basic

universes u v w u₁

variables (R : Type u) [semiring R]
variables (ι : Type v) [decidable_eq ι] (M : ι → Type w)
variables [Π i, add_comm_group (M i)] [Π i, semimodule R (M i)]
include R

namespace direct_sum

variables {R ι M}

instance : semimodule R (direct_sum ι M) := dfinsupp.to_semimodule

variables R ι M
def lmk : Π s : finset ι, (Π i : (↑s : set ι), M i.1) →ₗ[R] direct_sum ι M :=
dfinsupp.lmk M R

def lof : Π i : ι, M i →ₗ[R] direct_sum ι M :=
dfinsupp.lsingle M R
variables {ι M}

lemma single_eq_lof (i : ι) (b : M i) :
  dfinsupp.single i b = lof R ι M i b := rfl

theorem mk_smul (s : finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x :=
(lmk R ι M s).map_smul c x

theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x :=
(lof R ι M i).map_smul c x

variables {N : Type u₁} [add_comm_group N] [semimodule R N]
variables (φ : Π i, M i →ₗ[R] N)

variables (ι N φ)
def to_module : direct_sum ι M →ₗ[R] N :=
{ to_fun := to_group (λ i, φ i),
  add := to_group_add _,
  smul := λ c x, direct_sum.induction_on x
    (by rw [smul_zero, to_group_zero, smul_zero])
    (λ i x, by rw [← of_smul, to_group_of, to_group_of, (φ i).map_smul c x])
    (λ x y ihx ihy, by rw [smul_add, to_group_add, ihx, ihy, to_group_add, smul_add]) }
variables {ι N φ}

@[simp] lemma to_module_lof (i) (x : M i) : to_module R ι N φ (lof R ι M i x) = φ i x :=
to_group_of (λ i, φ i) i x

variables (ψ : direct_sum ι M →ₗ[R] N)

theorem to_module.unique (f : direct_sum ι M) : ψ f = to_module R ι N (λ i, ψ.comp $ lof R ι M i) f :=
to_group.unique ψ f

variables {ψ} {ψ' : direct_sum ι M →ₗ[R] N}

theorem to_module.ext (H : ∀ i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) (f : direct_sum ι M) :
  ψ f = ψ' f :=
by rw [to_module.unique R ψ, to_module.unique R ψ', funext H]

def lset_to_set (S T : set ι) (H : S ⊆ T) :
  direct_sum S (M ∘ subtype.val) →ₗ direct_sum T (M ∘ subtype.val) :=
to_module R _ _ $ λ i, lof R T (M ∘ @subtype.val _ T) ⟨i.1, H i.2⟩

protected def lid (M : Type v) [add_comm_group M] [semimodule R M] :
  direct_sum punit (λ _, M) ≃ₗ M :=
{ .. direct_sum.id M,
  .. to_module R punit M (λ i, linear_map.id) }

variables (ι M)
def component (i : ι) : direct_sum ι M →ₗ[R] M i :=
{ to_fun := λ f, f i,
  add := λ _ _, dfinsupp.add_apply,
  smul := λ _ _, dfinsupp.smul_apply }

variables {ι M}
@[simp] lemma lof_apply (i : ι) (b : M i) : ((lof R ι M i) b) i = b :=
by rw [lof, dfinsupp.lsingle_apply, dfinsupp.single_apply, dif_pos rfl]

lemma apply_eq_component (f : direct_sum ι M) (i : ι) :
  f i = component R ι M i f := rfl

@[simp] lemma component.lof_self (i : ι) (b : M i) :
  component R ι M i ((lof R ι M i) b) = b :=
lof_apply R i b

lemma component.of (i j : ι) (b : M j) :
  component R ι M i ((lof R ι M j) b) =
  if h : j = i then eq.rec_on h b else 0 :=
dfinsupp.single_apply

@[ext] lemma ext {f g : direct_sum ι M}
  (h : ∀ i, component R ι M i f = component R ι M i g) : f = g :=
dfinsupp.ext h

lemma ext_iff {f g : direct_sum ι M} : f = g ↔
  ∀ i, component R ι M i f = component R ι M i g :=
⟨λ h _, by rw h, ext R⟩

end direct_sum
