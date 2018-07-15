
import tactic.cache
import category.traversable.basic

universe variables w u v w' u' v'

open is_lawful_traversable
open function (hiding comp)
open functor

lemma map_id_mk {α β : Type u}
  (f : α → β) :
  map f ∘ @id.mk α = @id.mk β ∘ f :=
rfl

attribute [norm] is_lawful_traversable.naturality

section traversable

variable {t : Type u → Type u}
variables [traversable t] [is_lawful_traversable t]
variables {G H : Type u → Type u}

variables [applicative G] [is_lawful_applicative G]
variables [applicative H] [is_lawful_applicative H]
variables {α β γ : Type u}
variables g : α → G β
variables h : β → H γ
variables f : β → γ

variables G H

def pure_transformation : applicative_transformation id G :=
begin
  refine { F := @pure G _, .. } ;
  intros, { refl }, { simp with norm, refl }
end

variables {G H}

lemma traverse_eq_map_ident (x : t β) :
  traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
calc
      traverse (id.mk ∘ f) x
    = traverse id.mk (map f x) : by rw [← traverse_map]
... = map f <$> x              : by simp [id_traverse]; refl

lemma purity (x : t α) :
  traverse pure x = (pure x : G (t α)) :=
let eta := pure_transformation G in
calc   traverse (@pure G _ _) x
     = traverse (pure ∘ id.mk) x   : rfl
 ... = traverse (@eta _ ∘ id.mk) x : rfl
 ... = eta (traverse id.mk x)      : by rw [naturality]
 ... = eta x                       : by rw [id_traverse]
 ... = pure x                      : rfl

lemma id_sequence (x : t α) :
  sequence (id.mk <$> x) = id.mk x :=
by simp [sequence,traverse_map,id_traverse]; refl

lemma comp_sequennce (x : t (G (H α))) :
  sequence (comp.mk <$> x) = comp.mk (sequence <$> sequence x) :=
by simp [sequence,traverse_map]; rw ← comp_traverse; simp [map_id]

lemma naturality' (eta : applicative_transformation G H) (x : t (G α)) :
  eta (sequence x) = sequence (@eta _ <$> x) :=
by simp [sequence,naturality,traverse_map]

end traversable
