/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Scott Morrison
-/
import data.finset.lattice
import data.multiset.functor

/-!
# Functoriality of `finset`

## TODO

Currently, all instances are classical because

-/

universes u v w

open function list

namespace finset
section to_move
variables {α β : Type*}

@[simp] lemma mem_image_const [decidable_eq α] {s : finset β} {a b : α} :
  a ∈ s.image (const β b) ↔ s.nonempty ∧ b = a :=
begin
  rw mem_image,
  simp only [exists_prop, const_apply, exists_and_distrib_right],
  refl,
end

lemma mem_image_const_self [decidable_eq α] {s : finset β} {a : α} :
  a ∈ s.image (const β a) ↔ s.nonempty :=
mem_image_const.trans $ and_iff_left rfl

@[simp] lemma sup_bot [semilattice_sup α] [order_bot α] (s : finset β) : s.sup (λ _, ⊥) = (⊥ : α) :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact sup_empty },
  { exact sup_const hs _ }
end

@[simp] lemma inf_top [semilattice_inf α] [order_top α] (s : finset β) : s.inf (λ _, ⊤) = (⊤ : α) :=
@sup_bot (order_dual α) _ _ _ _

@[simp] lemma sup_singleton'' [decidable_eq α] (s : finset β) (f : β → α) :
  s.sup (λ b, {f b}) = s.image f :=
by { ext a, rw [mem_sup, mem_image], simp only [mem_singleton, eq_comm] }

end to_move

/-! ### Functor -/

section functor
variables {α β : Type u} [Π P, decidable P]

/-- Because `finset.image` requires a `decidable_eq` instance for the target type, we can only
construct `functor finset` when working classically. -/
instance : functor finset :=
{ map := λ α β f s, s.image f }

instance : is_lawful_functor finset :=
{ id_map := λ α s, image_id,
  comp_map := λ α β γ f g s, image_image.symm }

@[simp] lemma fmap_def {s : finset α} (f : α → β) : f <$> s = s.image f := rfl

end functor

/-! ### Pure -/

instance : has_pure finset := ⟨λ α x, {x}⟩

@[simp] lemma pure_def {α} : (pure : α → finset α) = singleton := rfl

/-! ### Applicative functor -/

section applicative
variables {α β : Type u} [Π P, decidable P]

instance : applicative finset :=
{ seq := λ α β t s, t.sup (λ f, s.image f),
  seq_left := λ α β s t, if t = ∅ then ∅ else s,
  seq_right := λ α β s t, if s = ∅ then ∅ else t,
  .. finset.functor,
  .. finset.has_pure }

@[simp] lemma seq_def (s : finset α) (t : finset (α → β)) : t <*> s = t.sup (λ f, s.image f) := rfl
@[simp] lemma seq_left_def (s : finset α) (t : finset β)  : s <* t = if t = ∅ then ∅ else s := rfl
@[simp] lemma seq_right_def (s : finset α) (t : finset β)  : s *> t = if s = ∅ then ∅ else t := rfl

instance : is_lawful_applicative finset :=
{ seq_left_eq := λ α β s t, begin
    rw [seq_def, fmap_def, seq_left_def],
    obtain rfl | ht := t.eq_empty_or_nonempty,
    { simp_rw [if_pos rfl, image_empty], exact (sup_bot _).symm },
    { ext a,
      rw [if_neg ht.ne_empty, mem_sup],
      refine ⟨λ ha, ⟨const β a, mem_image_of_mem _ ha, mem_image_const_self.2 ht⟩, _⟩,
      rintro ⟨f, hf, ha⟩,
      rw mem_image at hf ha,
      obtain ⟨b, hb, rfl⟩ := hf,
      obtain ⟨_, _, rfl⟩ := ha,
      exact hb }
  end,
  seq_right_eq := λ α β s t, begin
    rw [seq_def, fmap_def, seq_right_def],
    obtain rfl | hs := s.eq_empty_or_nonempty,
    { rw [if_pos rfl, image_empty, sup_empty, bot_eq_empty] },
    { ext a,
      rw [if_neg hs.ne_empty, mem_sup],
      refine ⟨λ ha, ⟨id, mem_image_const_self.2 hs, by rwa image_id⟩, _⟩,
      rintro ⟨f, hf, ha⟩,
      rw mem_image at hf ha,
      obtain ⟨b, hb, rfl⟩ := ha,
      obtain ⟨_, _, rfl⟩ := hf,
      exact hb }
  end,
  pure_seq_eq_map := λ α β f s, sup_singleton,
  map_pure := λ α β f a, image_singleton _ _,
  seq_pure := λ α β s a, sup_singleton'' _ _,
  seq_assoc := λ α β γ s t u, begin
    ext a,
    simp_rw [seq_def, fmap_def],
    simp only [exists_prop, mem_sup, mem_image],
    split,
    { rintro ⟨g, hg, b, ⟨f, hf, a, ha, rfl⟩, rfl⟩,
      exact ⟨g ∘ f, ⟨comp g, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩ },
    { rintro ⟨c, ⟨_, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩,
      exact ⟨g, hg, f a, ⟨f, hf, a, ha, rfl⟩, rfl⟩ }
  end,
  .. finset.is_lawful_functor }

instance : is_comm_applicative finset :=
{ commutative_prod := λ α β s t, begin
    simp_rw [seq_def, fmap_def, sup_image, sup_eq_bUnion],
    change s.bUnion (λ a, t.image $ λ b, (a, b)) = t.bUnion (λ b, s.image $ λ a, (a, b)),
    transitivity s.product t;
      [rw product_eq_bUnion, rw product_eq_bUnion_right]; congr; ext; simp_rw mem_image,
  end,
  .. finset.is_lawful_applicative }

end applicative

/-! ### Monad -/

section monad
variables [Π P, decidable P]

instance : monad finset :=
{ bind := λ α β, @sup _ _ _ _,
  .. finset.applicative }

@[simp] lemma bind_def {α β} : (>>=) = @sup (finset α) β _ _ := rfl

instance : is_lawful_monad finset :=
{ bind_pure_comp_eq_map := λ α β f s, sup_singleton'' _ _,
  bind_map_eq_seq := λ α β t s, rfl,
  pure_bind := λ α β t s, sup_singleton,
  bind_assoc :=  λ α β γ s f g, by { convert sup_bUnion _ _, exact sup_eq_bUnion _ _ },
  .. finset.is_lawful_applicative }

end monad

/-! ### Alternative functor -/

section alternative
variables [Π P, decidable P]

instance : alternative finset :=
{ orelse := λ α, (∪),
  failure := λ α, ∅,
  .. finset.applicative }

end alternative

/-! ### Traversable functor -/

section traversable
variables

variables {α β γ : Type u} [Π P, decidable P] {F G H : Type u → Type u}
  [applicative F] [applicative G] [applicative H] [is_comm_applicative F] [is_comm_applicative G]
  [is_comm_applicative H]

open is_lawful_traversable is_comm_applicative

/-- Traverse function for `finset`. -/
def traverse (f : α → F β) (s :  finset α) : F (finset β) :=
multiset.to_finset <$> multiset.traverse f s.1

open functor
open traversable is_lawful_traversable

@[simp] lemma map_comp_coe (h : α → β) :
  functor.map h ∘ multiset.to_finset = multiset.to_finset ∘ functor.map h :=
funext $ λ s, image_to_finset

@[simp] lemma id_traverse (s : finset α) : traverse id.mk s = s :=
by { rw [traverse, multiset.id_traverse], exact s.val_to_finset }

lemma comp_traverse (g : α → G β) (h : β → H γ) (s : finset α) :
  traverse (comp.mk ∘ functor.map h ∘ g) s = comp.mk (functor.map (traverse h) (traverse g s)) :=
begin
  unfold traverse,
  simp [multiset.comp_traverse] with functor_norm,
  congr' 2,
  ext m,
  simp [traverse],
  ext,
end

lemma map_traverse (g : α → G β) (h : β → γ) (s : finset α) :
  functor.map (functor.map h) (traverse g s) = traverse (functor.map h ∘ g) s :=
begin
  unfold traverse,
  simp only [map_comp_coe] with functor_norm,
  rw [is_lawful_functor.comp_map, multiset.map_traverse],
end

lemma traverse_image (g : α → β) (h : β → G γ) (s : finset α) :
  traverse h (image g s) = traverse (h ∘ g) s :=
begin
  simp [traverse];
    rw [← multiset.traverse_map g h],


end

lemma naturality (eta : applicative_transformation G H) {α β : Type*} (f : α → G β) (s : finset α) :
  eta (traverse f s) = traverse (@eta _ ∘ f) s :=
begin

end

end traversable
end finset
