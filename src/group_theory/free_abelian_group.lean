/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Free abelian groups as abelianization of free groups.
-/
import algebra.pi_instances
import group_theory.free_group
import group_theory.abelianization

universes u v

variables (α : Type u)

def free_abelian_group : Type u :=
additive $ abelianization $ free_group α

instance : add_comm_group (free_abelian_group α) :=
@additive.add_comm_group _ $ abelianization.comm_group _

variable {α}

namespace free_abelian_group

def of (x : α) : free_abelian_group α :=
abelianization.of $ free_group.of x

def lift {β : Type v} [add_comm_group β] (f : α → β) (x : free_abelian_group α) : β :=
@abelianization.lift _ _ (multiplicative β) _ (@free_group.to_group _ (multiplicative β) _ f) _ x

namespace lift
variables {β : Type v} [add_comm_group β] (f : α → β)
open free_abelian_group

instance is_add_group_hom : is_add_group_hom (lift f) :=
⟨λ x y, @is_group_hom.mul _ (multiplicative β) _ _ _ (abelianization.lift.is_group_hom _) x y⟩

@[simp] protected lemma add (x y : free_abelian_group α) :
  lift f (x + y) = lift f x + lift f y :=
is_add_group_hom.add _ _ _

@[simp] protected lemma neg (x : free_abelian_group α) : lift f (-x) = -lift f x :=
is_add_group_hom.neg _ _

@[simp] protected lemma sub (x y : free_abelian_group α) :
  lift f (x - y) = lift f x - lift f y :=
by simp

@[simp] protected lemma zero : lift f 0 = 0 :=
is_add_group_hom.zero _

@[simp] protected lemma of (x : α) : lift f (of x) = f x :=
by unfold of; unfold lift; simp

protected theorem unique (g : free_abelian_group α → β) [is_add_group_hom g]
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
@abelianization.lift.unique (free_group α) _ (multiplicative β) _ _ _ g
  ⟨λ x y, @is_add_group_hom.add (additive $ abelianization (free_group α)) _ _ _ _ _ x y⟩ (λ x,
  @free_group.to_group.unique α (multiplicative β) _ _ (g ∘ abelianization.of)
    ⟨λ m n, is_add_group_hom.add g (abelianization.of m) (abelianization.of n)⟩ hg _) _

protected theorem ext (g h : free_abelian_group α → β)
  [is_add_group_hom g] [is_add_group_hom h]
  (H : ∀ x, g (of x) = h (of x)) {x} :
  g x = h x :=
(lift.unique (g ∘ of) g (λ _, rfl)).trans $
eq.symm $ lift.unique _ _ $ λ x, eq.symm $ H x

lemma map_hom {α β γ} [add_comm_group β] [add_comm_group γ]
  (a : free_abelian_group α) (f : α → β) (g : β → γ) [is_add_group_hom g] :
  g (a.lift f) = a.lift (g ∘ f) :=
show (g ∘ lift f) a = a.lift (g ∘ f),
begin
  apply @lift.unique,
  assume a,
  simp only [(∘), lift.of]
end

def universal : (α → β) ≃ { f : free_abelian_group α → β // is_add_group_hom f } :=
{ to_fun := λ f, ⟨_, lift.is_add_group_hom f⟩,
  inv_fun := λ f, f.1 ∘ of,
  left_inv := λ f, funext $ λ x, lift.of f x,
  right_inv := λ f, subtype.eq $ funext $ λ x, eq.symm $ by letI := f.2; from
    lift.unique _ _ (λ _, rfl) }

end lift

local attribute [instance] quotient_group.left_rel normal_subgroup.to_is_subgroup

@[elab_as_eliminator]
protected theorem induction_on
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ of x)
  (Cn : ∀ x, C (of x) → C (-of x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on z $ λ x, quot.induction_on x $ λ L,
list.rec_on L C0 $ λ ⟨x, b⟩ tl ih,
bool.rec_on b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)

instance is_add_group_hom_lift' {α} (β) [add_comm_group β] (a : free_abelian_group α) :
  is_add_group_hom (λf, (a.lift f : β)) :=
begin
  refine ⟨assume f g, free_abelian_group.induction_on a _ _ _ _⟩,
  { simp [is_add_group_hom.zero (free_abelian_group.lift f)] },
  { simp [lift.of], assume x, refl },
  { simp [is_add_group_hom.neg (free_abelian_group.lift f)],
    assume x h, show - (f x + g x) = -f x + - g x, exact neg_add _ _ },
  { simp [is_add_group_hom.add (free_abelian_group.lift f)],
    assume x y hx hy,
    rw [hx, hy],
    ac_refl }
end

variables {β : Type u}

instance : monad free_abelian_group.{u} :=
{ pure := λ α, of,
  bind := λ α β x f, lift f x }

@[elab_as_eliminator]
protected theorem induction_on'
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ pure x)
  (Cn : ∀ x, C (pure x) → C (-pure x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
free_abelian_group.induction_on z C0 C1 Cn Cp

@[simp] lemma map_pure (f : α → β) (x : α) : f <$> (pure x : free_abelian_group α) = pure (f x) :=
lift.of _ _

@[simp] lemma map_zero (f : α → β) : f <$> (0 : free_abelian_group α) = 0 :=
lift.zero (of ∘ f)

@[simp] lemma map_add (f : α → β) (x y : free_abelian_group α) : f <$> (x + y) = f <$> x + f <$> y :=
lift.add _ _ _

@[simp] lemma map_neg (f : α → β) (x : free_abelian_group α) : f <$> (-x) = -(f <$> x) :=
lift.neg _ _

@[simp] lemma map_sub (f : α → β) (x y : free_abelian_group α) : f <$> (x - y) = f <$> x - f <$> y :=
lift.sub _ _ _

@[simp] lemma pure_bind (f : α → free_abelian_group β) (x) : pure x >>= f = f x :=
lift.of _ _

@[simp] lemma zero_bind (f : α → free_abelian_group β) : 0 >>= f = 0 :=
lift.zero f

@[simp] lemma add_bind (f : α → free_abelian_group β) (x y : free_abelian_group α) : x + y >>= f = (x >>= f) + (y >>= f) :=
lift.add _ _ _

@[simp] lemma neg_bind (f : α → free_abelian_group β) (x : free_abelian_group α) : -x >>= f = -(x >>= f) :=
lift.neg _ _

@[simp] lemma sub_bind (f : α → free_abelian_group β) (x y : free_abelian_group α) : x - y >>= f = (x >>= f) - (y >>= f) :=
lift.sub _ _ _

@[simp] lemma pure_seq (f : α → β) (x : free_abelian_group α) : pure f <*> x = f <$> x :=
pure_bind _ _

@[simp] lemma zero_seq (x : free_abelian_group α) : (0 : free_abelian_group (α → β)) <*> x = 0 :=
zero_bind _

@[simp] lemma add_seq (f g : free_abelian_group (α → β)) (x : free_abelian_group α) : f + g <*> x = (f <*> x) + (g <*> x) :=
add_bind _ _ _

@[simp] lemma neg_seq (f : free_abelian_group (α → β)) (x : free_abelian_group α) : -f <*> x = -(f <*> x) :=
neg_bind _ _

@[simp] lemma sub_seq (f g : free_abelian_group (α → β)) (x : free_abelian_group α) : f - g <*> x = (f <*> x) - (g <*> x) :=
sub_bind _ _ _

instance is_add_group_hom_seq (f : free_abelian_group (α → β)) : is_add_group_hom ((<*>) f) :=
⟨λ x y, show lift (<$> (x+y)) _ = _, by simp only [map_add]; exact
@@is_add_group_hom.add _ _ _ (@@free_abelian_group.is_add_group_hom_lift' (free_abelian_group β) _ _) _ _⟩

@[simp] lemma seq_zero (f : free_abelian_group (α → β)) : f <*> 0 = 0 :=
is_add_group_hom.zero _

@[simp] lemma seq_add (f : free_abelian_group (α → β)) (x y : free_abelian_group α) : f <*> (x + y) = (f <*> x) + (f <*> y) :=
is_add_group_hom.add _ _ _

@[simp] lemma seq_neg (f : free_abelian_group (α → β)) (x : free_abelian_group α) : f <*> (-x) = -(f <*> x) :=
is_add_group_hom.neg _ _

@[simp] lemma seq_sub (f : free_abelian_group (α → β)) (x y : free_abelian_group α) : f <*> (x - y) = (f <*> x) - (f <*> y) :=
is_add_group_hom.sub _ _ _

instance : is_lawful_monad free_abelian_group.{u} :=
{ id_map := λ α x, free_abelian_group.induction_on' x (map_zero id) (λ x, map_pure id x)
    (λ x ih, by rw [map_neg, ih]) (λ x y ihx ihy, by rw [map_add, ihx, ihy]),
  pure_bind := λ α β x f, pure_bind f x,
  bind_assoc := λ α β γ x f g, free_abelian_group.induction_on' x
    (by iterate 3 { rw zero_bind }) (λ x, by iterate 2 { rw pure_bind })
    (λ x ih, by iterate 3 { rw neg_bind }; rw ih)
    (λ x y ihx ihy, by iterate 3 { rw add_bind }; rw [ihx, ihy]) }

instance : is_comm_applicative free_abelian_group.{u} :=
{ commutative_prod := λ α β x y, free_abelian_group.induction_on' x
    (by rw [map_zero, zero_seq, seq_zero])
    (λ p, by rw [map_pure, pure_seq]; exact free_abelian_group.induction_on' y
      (by rw [map_zero, map_zero, zero_seq])
      (λ q, by rw [map_pure, map_pure, pure_seq, map_pure])
      (λ q ih, by rw [map_neg, map_neg, neg_seq, ih])
      (λ y₁ y₂ ih1 ih2, by rw [map_add, map_add, add_seq, ih1, ih2]))
    (λ p ih, by rw [map_neg, neg_seq, seq_neg, ih])
    (λ x₁ x₂ ih1 ih2, by rw [map_add, add_seq, seq_add, ih1, ih2]) }

end free_abelian_group
