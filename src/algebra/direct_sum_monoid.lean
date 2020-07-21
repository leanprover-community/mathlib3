/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of additive commutative monoids, indexed by a discrete type.
-/
import data.dfinsupp

open_locale big_operators

universes u v w u₁

variables (ι : Type v) [decidable_eq ι] (β : ι → Type w) [Π i, add_comm_monoid (β i)]

def direct_sum : Type* := Π₀ i, β i

namespace direct_sum

variables {ι β}

instance : add_comm_monoid (direct_sum ι β) :=
dfinsupp.add_comm_monoid

instance : inhabited (direct_sum ι β) := ⟨0⟩

variables β
def mk : Π s : finset ι, (Π i : (↑s : set ι), β i.1) → direct_sum ι β :=
dfinsupp.mk

def of : Π i : ι, β i → direct_sum ι β :=
dfinsupp.single
variables {β}

instance mk.is_add_monoid_hom (s : finset ι) : is_add_monoid_hom (mk β s) :=
{ map_add := λ _ _, dfinsupp.mk_add,
  map_zero := dfinsupp.mk_zero}


@[simp] lemma mk_zero (s : finset ι) : mk β s 0 = 0 :=
is_add_monoid_hom.map_zero _

@[simp] lemma mk_add (s : finset ι) (x y) : mk β s (x + y) = mk β s x + mk β s y :=
is_add_hom.map_add _ x y

instance of.is_add_monoid_hom (i : ι) : is_add_monoid_hom (of β i) :=
{ map_add := λ _ _, dfinsupp.single_add,
  map_zero := dfinsupp.single_zero }

@[simp] lemma of_zero (i : ι) : of β i 0 = 0 :=
is_add_monoid_hom.map_zero _

@[simp] lemma of_add (i : ι) (x y) : of β i (x + y) = of β i x + of β i y :=
is_add_hom.map_add _ x y

theorem mk_injective (s : finset ι) : function.injective (mk β s) :=
dfinsupp.mk_injective s

theorem of_injective (i : ι) : function.injective (of β i) :=
λ x y H, congr_fun (mk_injective _ H) ⟨i, by simp⟩

@[elab_as_eliminator]
protected theorem induction_on {C : direct_sum ι β → Prop}
  (x : direct_sum ι β) (H_zero : C 0)
  (H_basic : ∀ (i : ι) (x : β i), C (of β i x))
  (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  apply dfinsupp.induction x H_zero,
  intros i b f h1 h2 ih,
  solve_by_elim
end


variables {γ : Type u₁} [add_comm_monoid γ]
variables (φ : Π i, β i → γ) [Π i, is_add_monoid_hom (φ i)]

variables (φ)
def to_add_monoid (f : direct_sum ι β) : γ :=
quotient.lift_on f (λ x, ∑ i in x.2.to_finset, φ i (x.1 i)) $ λ x y H,
begin
  have H1 : x.2.to_finset ∩ y.2.to_finset ⊆ x.2.to_finset, from finset.inter_subset_left _ _,
  have H2 : x.2.to_finset ∩ y.2.to_finset ⊆ y.2.to_finset, from finset.inter_subset_right _ _,
  refine (finset.sum_subset H1 _).symm.trans ((finset.sum_congr rfl _).trans (finset.sum_subset H2 _)),
  { intros i H1 H2, rw finset.mem_inter at H2, rw H i,
    simp only [multiset.mem_to_finset] at H1 H2,
    rw [(y.3 i).resolve_left (mt (and.intro H1) H2), is_add_monoid_hom.map_zero (φ i)] },
  { intros i H1, rw H i },
  { intros i H1 H2, rw finset.mem_inter at H2, rw ← H i,
    simp only [multiset.mem_to_finset] at H1 H2,
    rw [(x.3 i).resolve_left (mt (λ H3, and.intro H3 H1) H2), is_add_monoid_hom.map_zero (φ i)] }
end
variables {φ}

instance to_add_monoid.is_add_monoid_hom : is_add_monoid_hom (to_add_monoid φ) :=
{ map_add := assume f g,
begin
  refine quotient.induction_on f (λ x, _),
  refine quotient.induction_on g (λ y, _),
  change ∑ i in _, _ = (∑ i in _, _) + (∑ i in _, _),
  simp only, conv { to_lhs, congr, skip, funext, rw is_add_hom.map_add (φ i) },
  simp only [finset.sum_add_distrib],
  congr' 1,
  { refine (finset.sum_subset _ _).symm,
    { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inl },
    { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
      rw [(x.3 i).resolve_left H2, is_add_monoid_hom.map_zero (φ i)] } },
  { refine (finset.sum_subset _ _).symm,
    { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inr },
    { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
      rw [(y.3 i).resolve_left H2, is_add_monoid_hom.map_zero (φ i)] } }
end,
  map_zero := rfl}

variables (φ)
@[simp] lemma to_add_monoid_zero : to_add_monoid φ 0 = 0 :=
is_add_monoid_hom.map_zero _

@[simp] lemma to_add_monoid_add (x y) : to_add_monoid φ (x + y) = to_add_monoid φ x + to_add_monoid φ y :=
is_add_hom.map_add _ x y

@[simp] lemma to_add_monoid_of (i) (x : β i) : to_add_monoid φ (of β i x) = φ i x :=
(add_zero _).trans $ congr_arg (φ i) $ show (if H : i ∈ ({i} : finset _) then x else 0) = x,
from dif_pos $ finset.mem_singleton_self i

variables (ψ : direct_sum ι β → γ) [is_add_monoid_hom ψ]

theorem to_add_monoid.unique (f : direct_sum ι β) :
  ψ f = @to_add_monoid _ _ _ _ _ _ (λ i, ψ ∘ of β i) (λ i, is_add_monoid_hom.comp (of β i) ψ) f :=
by haveI : ∀ i, is_add_monoid_hom (ψ ∘ of β i) := (λ _, is_add_monoid_hom.comp _ _); exact
direct_sum.induction_on f
  (by rw [is_add_monoid_hom.map_zero ψ, is_add_monoid_hom.map_zero (to_add_monoid (λ i, ψ ∘ of β i))])
  (λ i x, by rw [to_add_monoid_of])
  (λ x y ihx ihy, by rw [is_add_hom.map_add ψ, is_add_hom.map_add (to_add_monoid (λ i, ψ ∘ of β i)), ihx, ihy])

protected def id (M : Type v) [add_comm_monoid M] : direct_sum punit (λ _, M) ≃ M :=
{ to_fun := direct_sum.to_add_monoid (λ _, id),
  inv_fun := of (λ _, M) punit.star,
  left_inv := λ x, direct_sum.induction_on x
    (by rw [to_add_monoid_zero, of_zero])
    (λ ⟨⟩ x, by rw [to_add_monoid_of]; refl)
    (λ x y ihx ihy, by rw [to_add_monoid_add, of_add, ihx, ihy]),
  right_inv := λ x, to_add_monoid_of _ _ _ }

instance : has_coe_to_fun (direct_sum ι β) :=
dfinsupp.has_coe_to_fun

end direct_sum
