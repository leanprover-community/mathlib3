
import data.qpf.indexed.mvpfunctor.basic
import data.qpf.indexed.constructions.basic

import category_theory.products

universes u

namespace mvfunctor

variables {I I' J J' : Type u}
  (F : fam I  ⥤ fam J )
  (G : fam I' ⥤ fam J')

def prod.fst (X : fam (I ⊕ I')) : fam I
| i := X $ sum.inl i

def prod.snd (X : fam (I ⊕ I')) : fam I'
| i := X $ sum.inr i

protected def prod.obj (X : fam (I ⊕ I')) : fam (J ⊕ J')
| (sum.inl j) := F.obj (prod.fst X) j
| (sum.inr j) := G.obj (prod.snd X) j

protected def prod.map.fst ⦃X Y : fam (I ⊕ I')⦄ : (X ⟶ Y) → (prod.fst X ⟶ prod.fst Y)
| f i x := f x

protected def prod.map.snd ⦃X Y : fam (I ⊕ I')⦄ : (X ⟶ Y) → (prod.snd X ⟶ prod.snd Y)
| f i x := f x

protected def prod.map ⦃X Y : fam (I ⊕ I')⦄ : (X ⟶ Y) → (prod.obj F G X ⟶ prod.obj F G Y)
| f (sum.inl j) := λ x, F.map (map.fst f) x
| f (sum.inr j) := λ x, G.map (map.snd f) x
-- | f (sum.inr j) := λ x, G.map (λ i y, f ‹ _ ›) x

protected def prod.map' ⦃X Y : fam (I ⊕ I')⦄ :
  (prod.fst X ⟶ prod.fst Y) → (prod.snd X ⟶ prod.snd Y) → (X ⟶ Y)
| f g (sum.inl i) x := f x
| f g (sum.inr i) x := g x

@[simp] lemma prod.map.fst_id ⦃X : fam (I ⊕ I')⦄ : map.fst (𝟙 X) = 𝟙 _ := by ext; refl

@[simp] lemma prod.map.snd_id ⦃X : fam (I ⊕ I')⦄ : map.snd (𝟙 X) = 𝟙 _ := by ext; refl

@[simp] lemma prod.map.fst_comp ⦃X Y Z : fam (I ⊕ I')⦄ (f : X ⟶ Y) (g : Y ⟶ Z) :
  map.fst (f ≫ g) = map.fst f ≫ map.fst g := by ext; refl

@[simp] lemma prod.map.snd_comp ⦃X Y Z : fam (I ⊕ I')⦄ (f : X ⟶ Y) (g : Y ⟶ Z) :
  map.snd (f ≫ g) = map.snd f ≫ map.snd g := by ext; refl

def prod : fam (I ⊕ I') ⥤ fam (J ⊕ J') :=
{ obj := prod.obj F G,
  map := prod.map F G,
  map_id' := by { intros, ext ⟨ ⟩ ⟨ ⟩; simp [prod.map,prod.obj]; refl },
  map_comp' := by { intros, ext ⟨ ⟩ ⟨ ⟩; simp [prod.map,- pfunctor.then_def]; refl } }

def prod_obj (X : fam I) (Y : fam I') : fam (I ⊕ I')
| (sum.inl i) := X i
| (sum.inr i) := Y i

def prod_mk : Π X : fam (I ⊕ I'), prod_obj (F.obj $ prod.fst X) (G.obj $ prod.snd X) ⟶ (prod F G).obj X
| X (sum.inl j) x := x
| X (sum.inr j) x := x

def prod_get : Π X : fam (I ⊕ I'), (prod F G).obj X ⟶ prod_obj (F.obj $ prod.fst X) (G.obj $ prod.snd X)
| X (sum.inl j) x := x
| X (sum.inr j) x := x

def prod_map {X X' : fam I} {Y Y' : fam I'} : Π (f : X ⟶ X') (g : Y ⟶ Y'), prod_obj X Y ⟶ prod_obj X' Y'
| f g (sum.inl j) x := f x
| f g (sum.inr j) x := g x

@[simp,reassoc]
lemma prod_mk_get {X : fam (I ⊕ I')} :
  prod_mk F G X ≫ prod_get F G X = 𝟙 _ :=
by ext1 ⟨ ⟩; refl

@[simp,reassoc]
lemma prod_get_mk {X : fam (I ⊕ I')} :
  prod_get F G X ≫ prod_mk F G X = 𝟙 _ :=
by ext1 ⟨ ⟩; refl

@[simp]
lemma prod_map_id {X : fam I} {X' : fam I'} :
  mvfunctor.prod_map (𝟙 X) (𝟙 X') = 𝟙 _ :=
by ext1 ⟨ ⟩; refl

@[simp,reassoc]
lemma prod_map_comp_map {X Y Z : fam I} {X' Y' Z' : fam I'} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') :
  mvfunctor.prod_map f f' ≫ mvfunctor.prod_map g g' = mvfunctor.prod_map (f ≫ g) (f' ≫ g') :=
by ext1 ⟨ ⟩; refl

@[simp,reassoc]
lemma prod_mk_nat {X Y : fam (I⊕I')}
  (f : X ⟶ Y)  :
  prod_mk F G _ ≫ (prod F G).map f =
  mvfunctor.prod_map (F.map $ mvfunctor.prod.map.fst f) (G.map $ mvfunctor.prod.map.snd f) ≫ prod_mk F G _ :=
by ext1 ⟨ ⟩; refl

end mvfunctor

namespace pfunctor

variables {I I' J J' : Type u}
  (F : pfunctor I  J)
  (G : pfunctor I' J')

def boo : Π (i : J ⊕ J'), sum.elim (F.A) (G.A) i → fam (I ⊕ I')
| (sum.inl i) x (sum.inl j) := F.B i x j
| (sum.inr i) x (sum.inr j) := G.B i x j
| _ _ _ := pempty

open mvfunctor (prod_obj prod.fst prod.snd)

def fst_boo {X : fam I} : Π (i : J') (x : (G.A) i),
  mvfunctor.prod.fst (boo F G (sum.inr i) x) ⟶ X .

def snd_boo {X : fam I'} : Π (i : J) (x : (F.A) i),
  mvfunctor.prod.snd (boo F G (sum.inl i) x) ⟶ X .

def prod : pfunctor (I ⊕ I') (J ⊕ J') :=
⟨ sum.elim F.A G.A, boo F G ⟩

def prod_mk : Π X : fam (I ⊕ I'), prod_obj (F.obj $ mvfunctor.prod.fst X) (G.obj $ mvfunctor.prod.snd X) ⟶ (prod F G).obj X
| X (sum.inl j) ⟨x,f⟩ := ⟨x,mvfunctor.prod.map' f (snd_boo F G _ _)⟩
| X (sum.inr j) ⟨x,f⟩ := ⟨x,mvfunctor.prod.map' (fst_boo F G _ _) f⟩

def prod_get : Π X : fam (I ⊕ I'), (prod F G).obj X ⟶ prod_obj (F.obj $ mvfunctor.prod.fst X) (G.obj $ mvfunctor.prod.snd X)
| X (sum.inl j) x := ⟨x.1,mvfunctor.prod.map.fst x.2⟩
| X (sum.inr j) x := ⟨x.1,mvfunctor.prod.map.snd x.2⟩

@[simp,reassoc]
lemma prod_mk_get {X : fam (I ⊕ I')} :
  prod_mk F G X ≫ prod_get F G X = 𝟙 _ :=
by { ext1 ⟨ ⟩, ext ⟨_,_ ⟩; intros, refl, cases a, simp, ext _ ⟨ ⟩, dsimp [prod_get,prod_mk,mvfunctor.prod.map.fst,mvfunctor.prod.map'], ext, refl,
     ext ⟨ ⟩, refl, rintros ⟨ ⟩, dsimp [prod_get,prod_mk,mvfunctor.prod.map.fst,mvfunctor.prod.map'], ext, refl, rintros _ _ ⟨ ⟩,
     simp [prod_get,prod_mk,mvfunctor.prod.map.fst,mvfunctor.prod.map'], ext, refl }

@[simp,reassoc]
lemma prod_get_mk {X : fam (I ⊕ I')} :
  prod_get F G X ≫ prod_mk F G X = 𝟙 _ :=
by { ext1 ⟨ ⟩; ext1 ⟨_,_ ⟩, dsimp [prod_mk,prod_get,mvfunctor.prod.map',mvfunctor.prod.map.fst],
     refine congr_arg _ _, ext ⟨ ⟩ : 2, refl, ext ⟨ ⟩, ext ⟨ ⟩ ⟨ ⟩, refl, rintro ⟨ ⟩, simp, ext1 ⟨ ⟩, ext1 ⟨ ⟩,
     dsimp [prod_get,prod_mk,mvfunctor.prod.map.snd], ext, refl, }

@[simp]
lemma prod_map_id {X : fam I} {X' : fam I'} :
  mvfunctor.prod_map (𝟙 X) (𝟙 X') = 𝟙 _ :=
by ext ⟨ ⟩; refl

@[simp,reassoc]
lemma prod_map_comp_map {X Y Z : fam I} {X' Y' Z' : fam I'} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') :
  mvfunctor.prod_map f f' ≫ mvfunctor.prod_map g g' = mvfunctor.prod_map (f ≫ g) (f' ≫ g') :=
by ext ⟨ ⟩; refl

@[simp,reassoc]
lemma prod_get_nat {X Y : fam (I⊕I')} (f : X ⟶ Y) :
  (prod F G).map f ≫ prod_get F G _ =
  prod_get F G _ ≫ mvfunctor.prod_map (F.map $ mvfunctor.prod.map.fst f) (G.map $ mvfunctor.prod.map.snd f) :=
by { ext1 ⟨ ⟩; ext1 ⟨ ⟩; intros; refl }

end pfunctor

namespace mvqpf
variables {I I' J J' : Type u}
  (F : fam I  ⥤ fam J ) [q  : mvqpf F]
  (G : fam I' ⥤ fam J') [q' : mvqpf G]

attribute [ext fam] funext

open category_theory


namespace prod
open mvfunctor mvpfunctor
variables {F G} {α β : fam J} (f : α ⟶ β)

include q q'

local attribute [simp] category_theory.functor.map_comp_map category_theory.functor.map_comp_map_assoc
local attribute [-simp] functor.map_comp

open mvfunctor.prod (fst snd)

instance : mvqpf (prod F G) :=
{ P         := pfunctor.prod (P F) (P G),
  abs       := λ α, pfunctor.prod_get _ _ _ ≫ prod_map (abs _ (fst α)) (abs _ (snd α)) ≫ prod_mk F G _,
  repr      := λ α, prod_get _ _ _ ≫ prod_map (repr _ _) (repr _ _) ≫ pfunctor.prod_mk _ _ _,
  abs_repr  := by { intros, simp, },
  abs_map   := by { intros, simp, },
 }

end prod

end mvqpf
