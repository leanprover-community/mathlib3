/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import category_theory.category
import category_theory.types
import category_theory.pi.basic
import category_theory.limits.pi
import logic.relation

/-!
Indexed type families and their categorical structure.

Features:

`fam I`      : family of types and its instance of `category`

Also, support functions for operating with n-tuples of types, such as:

`append1 α β`    : append type J-indexed `β` family to I-indexed `α` family to obtain a `(I⊕J)`-indexed family
`drop α`         : drop the right component of a `(I⊕J)`-indexed family
`last α`         : take the right component of a `(I⊕J)`-indexed family
`append_fun f g` : appends two families of functions `f` and `g`
`drop_fun f`     : drops the right function family from a `(I⊕J)`-indexed family
`last_fun f`     : returns the right function family of a `(I⊕J)`-indexed family

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/

universes u v w

open category_theory

/-- Type family indexed by `I`; we call `fam (I ⊕ J)` the product
of `fam I` and `fam J` (despite being formulated using a sum type) -/
@[reducible]
def fam (I : Type u) := I → Type u

instance {I} : has_one (fam I) :=
⟨ λ _, punit ⟩

namespace fam

variables {I J : Type u}

/-- retain the left side of a product family -/
def drop : fam (I ⊕ J) → fam I :=
λ x i, x (sum.inl i)

/-- retain the right side of a product family -/
def last : fam (I ⊕ J) → fam J :=
λ x i, x (sum.inr i)

/-- combine two families with different indices their product -/
def append1 (f : fam I) (g : fam J) : fam (I ⊕ J)
| (sum.inl i) := f i
| (sum.inr i) := g i

end fam

section pis

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

instance pi.category {α : Type w} : category $ α → C :=
{ hom := λ X Y, Π ⦃i⦄, X i ⟶ Y i,
  id := λ X i, 𝟙 (X i),
  comp := λ X Y Z f g i, @f i ≫ @g i }

end pis

instance fam.category {I : Type u} : category $ fam I :=
pi.category

namespace fam

variables {I J : Type u}

lemma ext (X Y : fam I) (f g : X ⟶ Y) (h : ∀ i (x : X i), f x = g x) : f = g :=
funext $ λ i, funext $ h _

/-- obtain an arrow over the product of two families by combining an arrow over its left side and
an arrow over its right side  -/
def split_fun {α β : fam (I⊕J)} :
  Π (f : drop α ⟶ drop β) (g : last α ⟶ last β), α ⟶ β
| f g (sum.inl i) x := f x
| f g (sum.inr i) x := g x

/-- combine two arrows over different categories of families into an arrow on their product -/
def append_fun {α β : fam I} {α' β' : fam J} (f : α ⟶ β) (g : α' ⟶ β') : (α.append1 α' ⟶ β.append1 β') :=
split_fun f g

lemma split_fun_comp {α β γ : fam (I⊕J)}
  (f : drop α ⟶ drop β) (g : drop β ⟶ drop γ) (f' : last α ⟶ last β) (g' : last β ⟶ last γ) :
  split_fun (f ≫ g) (f' ≫ g') = split_fun f f' ≫ split_fun g g' :=
by ext (x|x) : 1; ext; refl

lemma append_fun_comp {α β γ : fam I} {α' β' γ' : fam J}
  (f : α ⟶ β) (f' : α' ⟶ β') (g : β ⟶ γ) (g' : β' ⟶ γ') :
  append_fun (f ≫ g) (f' ≫ g') = append_fun f f' ≫ append_fun g g' :=
by erw ← split_fun_comp; refl

lemma append_fun_comp_right {α γ : fam I} {α' β' γ' : fam J}
  (f : α ⟶ γ) (f' : α' ⟶ β') (g' : β' ⟶ γ') :
  append_fun f (f' ≫ g') = append_fun f f' ≫ append_fun (𝟙 _) g' :=
by erw ← split_fun_comp; refl

lemma split_fun_comp_right {α : fam (I⊕J)} {β γ : fam J} {γ' : fam I}
  (f : drop α ⟶ γ')
  (f' : last α ⟶ β) (g' : β ⟶ γ) :
  (split_fun f (f' ≫ g') : α ⟶ γ'.append1 γ) =
  (split_fun f f' : α ⟶ γ'.append1 β) ≫ split_fun (𝟙 _) g' :=
by rw [← split_fun_comp,category.comp_id]

/-- take the left side of an arrow on a product of two families -/
def drop_fun {α β : fam (I⊕J)} : Π (f : α ⟶ β), drop α ⟶ drop β
| f i x := f x

/-- take the right side of an arrow on a product of two families -/
def last_fun {α β : fam (I⊕J)} : Π (f : α ⟶ β), last α ⟶ last β
| f i x := f x

theorem eq_of_drop_last_eq {α β : fam (I⊕J)} {f g : α ⟶ β}
  (h₀ : ∀ j (x : α (sum.inl j)), drop_fun f x = drop_fun g x) (h₁ : last_fun f = last_fun g) :
  f = g :=
by { ext1 (i|j); ext1 x, apply h₀, apply congr_fun (congr_fun h₁ j), }
-- by ext1 i; rcases i with ⟨j, ieq⟩ | ieq; [apply h₀, apply h₁]

@[simp]
theorem split_drop_fun_last_fun {α α' : fam (I⊕J)} (f : α ⟶ α') :
  split_fun (drop_fun f) (last_fun f) = f :=
eq_of_drop_last_eq (λ _ _, rfl) (funext $ λ _, funext $ λ _, rfl)

theorem append_fun_id_id {α : fam I} {β : fam J} :
  append_fun (𝟙 α) (𝟙 β) = 𝟙 _ :=
by apply eq_of_drop_last_eq; intros; try { ext }; refl

/-- `unit i` is an object in `fam I` such that has only one
member and that its index is `i` -/
inductive unit (i : I) : I → Type u
| rfl {} : unit i

instance {i : I} : inhabited (unit i i) := ⟨ unit.rfl ⟩

/-- given a value of a type family, give an arrow to that object -/
def value (i) (X : fam I) : X i → (unit i ⟶ X)
| x j unit.rfl := x

theorem value.get {i} {X : fam I} (f g : unit i ⟶ X) (h : f = g) : f unit.rfl = g unit.rfl :=
by rw h

theorem value.ext {i} {X : fam I} (f g : unit i ⟶ X) (h : f unit.rfl = g unit.rfl) : f = g :=
by ext _ ⟨ ⟩; exact h

@[simp]
lemma value_eq  (i) (X : fam I) (x : X i) : Π {u : unit i i}, value i X x u = x
| unit.rfl := rfl

section subtype

variables {F : fam I ⥤ fam J}

/-- predicate over the values in type family `α` -/
@[pp_nodot, derive inhabited]
def Pred (α : fam I) : Sort* := ∀ i, α i → Prop

/-- introduction rule for `Pred α` -/
def Pred.mk {α : fam I} (p : Π i, (unit i ⟶ α) → Prop) : Pred α :=
λ i x, p i $ value i _ x

/-- elimination rule for `Pred α` -/
def Pred.apply {α : fam I} (p : Pred α) : ∀ ⦃i⦄, (unit i ⟶ α) → Prop :=
λ i f, p i $ f unit.rfl

@[simp]
lemma Pred.apply_mk {α : fam I} (p : Π i, (unit i ⟶ α) → Prop) :
  Pred.apply (Pred.mk p) = p :=
by ext : 2; simp [Pred.apply,Pred.mk]; congr'; ext _ ⟨ ⟩; refl

@[simp]
lemma Pred.mk_to_fun {α : fam I} (p : Π i, (unit i ⟶ α) → Prop) {i} (x : α i) :
  Pred.mk p i x = p i (value i _ x) := rfl

@[simp]
lemma Pred.mk_apply {α : fam I} (p : Pred α) :
  Pred.mk (Pred.apply p) = p := by ext; refl

/-- contravariant map function for `Pred` -/
def Pred.map {α β : fam I} (f : α ⟶ β) (p : Pred β) : Pred α :=
λ i x, p i (f x)

lemma Pred.map_mk {α β : fam I} (f : α ⟶ β) (p : Π ⦃i⦄, (unit i ⟶ β) → Prop) :
  Pred.map f (Pred.mk p) = Pred.mk (λ i g, p (g ≫ f)) :=
by ext; simp [Pred.mk,Pred.map]; congr'; ext _ ⟨ ⟩; refl

/-- subtypes as an object of a type family category -/
@[reducible]
def subtype {α : fam I} (p : Pred α) : fam I :=
λ i, subtype (p i)

/-- elimination rule for `subtype` object -/
def subtype.val {α : fam I} {p : Pred α} : fam.subtype p ⟶ α :=
λ i, subtype.val

/-- map function on the predicate of `subtype` -/
def subtype.map {α β : fam I} (p : Pred α) (q : Pred β)
  (f : α ⟶ β) (h : ∀ i x, p i x → q i (f x)) :
  fam.subtype p ⟶ fam.subtype q :=
λ i (x : subtype p i), subtype.mk (f x.1) (h i _ x.2)

lemma subtype.ext {α : fam I} {p : Pred α } {X} (a b : X ⟶ subtype p)
  (h : a ≫ subtype.val = b ≫ subtype.val) : a = b :=
by ext : 2; rw subtype.ext_iff; apply congr_fun (congr_fun h x)

lemma subtype.map_val {α β : fam I} {p : Pred α} {q : Pred β} (a : α ⟶ β) (h) :
  subtype.map p q a h ≫ subtype.val = subtype.val ≫ a :=
by ext _ ⟨ ⟩ : 2; refl

local attribute [instance] has_limit_of_has_limit_comp_eval
instance : has_binary_products (fam I) := ⟨by apply_instance⟩

/-- binary product in the category `fam I` -/
def prod (α β : fam I) : fam I
| i := α i × β i

localized "infix ` ⊗ `:35 := fam.prod" in fam

/-- left projection of binary product in the category `fam I` -/
def prod.fst : Π {α β : fam I}, α ⊗ β ⟶ α
| α β i x := _root_.prod.fst x

/-- right projection of binary product in the category `fam I` -/
def prod.snd : Π {α β : fam I}, α ⊗ β ⟶ β
| α β i x := _root_.prod.snd x

/-- map function of the binary product in the category `fam I` -/
def prod.map {α β α' β' : fam I} : (α ⟶ β) → (α' ⟶ β') → (α ⊗ α' ⟶ β ⊗ β')
| f g i x := (f x.1,g x.2)

localized "infix ` ⊗' `:35 := fam.prod.map" in fam

@[simp, reassoc]
lemma prod.map_fst {α β α' β' : fam I} (f : α ⟶ β) (g : α' ⟶ β') :
  prod.map f g ≫ prod.fst = prod.fst ≫ f :=
by ext; refl

@[simp, reassoc]
lemma prod.map_snd {α β α' β' : fam I} (f : α ⟶ β) (g : α' ⟶ β') :
  prod.map f g ≫ prod.snd = prod.snd ≫ g :=
by ext; refl

lemma prod.ext {α β β' : fam I} (f g : α ⟶ β ⊗ β')
  (h :  f ≫ prod.fst = g ≫ prod.fst)
  (h' : f ≫ prod.snd = g ≫ prod.snd) :
  f = g :=
by { ext i x,
     apply congr_fun (congr_fun h  i) x,
     apply congr_fun (congr_fun h' i) x }

@[simp]
lemma prod.map_id {α β : fam I} :
  prod.map (𝟙 α) (𝟙 β) = 𝟙 _ :=
by apply prod.ext; simp

@[simp, reassoc]
lemma prod.map_comp {α β γ α' β' γ' : fam I}
  (f :  α  ⟶ β)  (g  : β  ⟶ γ)
  (f' : α' ⟶ β') (g' : β' ⟶ γ') :
  prod.map f f' ≫ prod.map g g' = prod.map (f ≫ g) (f' ≫ g') :=
by apply prod.ext; simp

@[simp]
lemma prod.map_mk {α β α' β' : fam I}
  (f :  α  ⟶ β) (g  : α'  ⟶ β') {i} (x : α i) (y : α' i) :
  prod.map f g (x,y) = (f x,g y) :=
rfl

/-- diagonal arrow of the binary product in the category `fam I` -/
def diag : Π {α : fam I}, α ⟶ α ⊗ α
| α i x := (x,x)

@[reassoc]
lemma diag_map {α β : fam I} (f : α ⟶ β) : diag ≫ (f ⊗' f) = f ≫ diag :=
by ext; refl

@[reassoc]
lemma diag_map_fst_snd {α β : fam I} : diag ≫ (prod.fst ⊗' prod.snd) = 𝟙 (α ⊗ β) :=
by ext _ ⟨ ⟩; refl

@[reassoc]
lemma diag_map_comp {α β γ γ' : fam I} (f : α ⟶ β) (g : β ⟶ γ) (g' : β ⟶ γ') :
  diag ≫ (f ≫ g ⊗' f ≫ g') = f ≫ diag ≫ (g ⊗' g') :=
by ext; refl

@[reassoc]
lemma diag_map_fst_snd_comp {α β γ γ' : fam I} (g : α ⟶ γ) (g' : β ⟶ γ') :
  diag ≫ (prod.fst ≫ g ⊗' prod.snd ≫ g') = (g ⊗' g') :=
by ext _ ⟨ ⟩; refl

/-- binary coproduct in the category `fam I` -/
def sum (α β : fam I) : fam I
| i := α i ⊕ β i

localized "infix ` ⊕' `:35 := fam.sum" in fam

/-- map function of the binary coproduct in the category `fam I` -/
def sum.map {α β α' β' : fam I} : (α ⟶ β) → (α' ⟶ β') → (α ⊕' α' ⟶ β ⊕' β')
| f g i (sum.inl x) := sum.inl $ f x
| f g i (sum.inr x) := sum.inr $ g x

localized "infix ` ⊕'' `:35 := fam.sum.map" in fam

/-- left introduction arrow of the binary coproduct in the category `fam I` -/
def sum.inl : Π {α β : fam I}, α ⟶ α ⊕' β
| α β i x := _root_.sum.inl x

/-- right introduction arrow of the binary coproduct in the category `fam I` -/
def sum.inr : Π {α β : fam I}, β ⟶ α ⊕' β
| α β i x := _root_.sum.inr x

@[simp, reassoc]
lemma sum.inl_map {α β α' β' : fam I} (f : α ⟶ β) (g : α' ⟶ β') :
  sum.inl ≫ sum.map f g = f ≫ sum.inl :=
by ext; refl

@[simp, reassoc]
lemma sum.inr_map {α β α' β' : fam I} (f : α ⟶ β) (g : α' ⟶ β') :
  sum.inr ≫ sum.map f g = g ≫ sum.inr :=
by ext; refl

lemma sum.ext {α β α' : fam I} (f g : α ⊕' α' ⟶ β)
  (h :  sum.inl ≫ f = sum.inl ≫ g)
  (h' : sum.inr ≫ f = sum.inr ≫ g) :
  f = g :=
by { ext i (x|x),
     apply congr_fun (congr_fun h  i) x,
     apply congr_fun (congr_fun h' i) x }

@[simp, reassoc]
lemma sum.map_comp {α β γ α' β' γ' : fam I}
  (f :  α  ⟶ β)  (g  : β  ⟶ γ)
  (f' : α' ⟶ β') (g' : β' ⟶ γ') :
  sum.map f f' ≫ sum.map g g' = sum.map (f ≫ g) (f' ≫ g') :=
by apply sum.ext; simp

/-- co-diagonal arrow of the binary coproduct in the category `fam I` -/
def codiag : Π {α : fam I}, α ⊕' α ⟶ α
| α i (_root_.sum.inl x) := x
| α i (_root_.sum.inr x) := x

end subtype

open_locale fam

@[simp]
lemma comp_app {α β γ : fam I} (f : α ⟶ β) (g : β ⟶ γ) {i} (x : α i) : (f ≫ g) x = g (f x) := rfl

/-- Propositional equality between values as a `Pred` -/
protected def eq (α : fam I) : Pred (α ⊗ α) :=
λ i x, x.1 = x.2

/-- Application of predicate `p` to the target of arrow `f`. `f ⊨ p` is a proposition that
states that predicate `p` holds on the target object of `f`. -/
def sat {X α : fam J} (f : X ⟶ α) (p : fam.Pred α) : Prop :=
∃ f' : X ⟶ subtype p, f = f' ≫ fam.subtype.val

infix ` ⊨ `:50 := sat

lemma congr_arrow {X Y : fam J} {f g : X ⟶ Y} (h : f = g) : ∀ ⦃i⦄ x, @f i x = @g i x :=
λ i, congr_fun (congr_fun h i)

lemma sat_intro {X α : fam J} (f : X ⟶ α) (p : fam.Pred α) (h : ∀ i x, p i (f x)) : f ⊨ p :=
⟨λ i x, ⟨f x,h i x⟩,by ext; refl⟩

lemma sat_elim {X α : fam J} (f : X ⟶ α) (p : fam.Pred α) : f ⊨ p → ∀ ⦃i⦄ x, p i (f x)
| ⟨a,b⟩ i x := b.symm ▸ (a x).property

lemma sat_mk_elim {X α : fam J} (f : X ⟶ α) (p : Π i, (unit i ⟶ α) → Prop) :
  f ⊨ Pred.mk p → ∀ ⦃i⦄ x, p i (x ≫ f)
| ⟨a,b⟩ i x := by convert (a $ x unit.rfl).property; ext _ ⟨ ⟩; rw b; refl

lemma sat_mk_intro {X α : fam J} (f : X ⟶ α) (p : Π i, (unit i ⟶ α) → Prop) (h : ∀ ⦃i⦄ x, p i (x ≫ f)) :
  f ⊨ Pred.mk p := sat_intro _ _ $ λ i x,
by simp; convert h (value i _ x); ext _ ⟨ ⟩; refl

lemma sat_map {α β X : fam J} (x : X ⟶ β) (f : β ⟶ α) (g : α ⟶ β)
  (r : Pred β) (hh : f ≫ g = 𝟙 _) :
  x ⊨ r → x ≫ f ⊨ r.map g
| ⟨h,h'⟩ := ⟨λ i y, ⟨f (h y).1,
  by { replace hh := congr_arrow hh, simp at hh,
       simp [Pred.map,hh], apply (h y).2 }⟩,
  by { ext, simp [h'], refl } ⟩

lemma sat_map₀ {α β X : fam J} (x : X ⟶ α) (g : α ⟶ β)
  (r : Pred β) :
  x ≫ g ⊨ r → x ⊨ r.map g
| ⟨h,h'⟩ := ⟨λ i y, ⟨x y,
  by { replace h' := congr_arrow h' y, simp at h',
       simp [Pred.map,h'], apply (h y).2 }⟩, by ext; refl⟩

lemma sat_map₁ {α β X : fam J} (x : X ⟶ α) (g : α ⟶ β)
  (r : Pred β) :
  x ⊨ r.map g → x ≫ g ⊨ r
| ⟨h,h'⟩ := ⟨λ i y, ⟨g (x y), h'.symm ▸ (h y).2⟩, by ext; refl ⟩

lemma comp_sat {α β X : fam J} (x : X ⟶ α) (g : α ⟶ β)
  (r : Pred β) :
  g ⊨ r → x ≫ g ⊨ r
| ⟨f,h⟩ := ⟨x ≫ f,by rw [h,category.assoc]⟩

lemma sat_map' {α β X : fam J} (x : X ⟶ β) (f : β ⟶ α) (g : α ⟶ β)
  (r : Pred β) (hh : f ≫ g = 𝟙 _) :
  x ≫ f ⊨ r.map g → x ⊨ r
| ⟨h,h'⟩ := ⟨λ i x, ⟨g (h x).1,(h x).2⟩,
            by { ext, replace h' := congr_arrow h' x_2, simp [subtype.val] at h',
                 replace hh := congr_arrow hh, simp at hh,
                 simp [subtype.val,h'.symm,hh], refl }⟩

/-- quotient type as an object of category `fam I` -/
def quot {α : fam I} (r : Pred (α ⊗ α)) : fam I :=
λ i, quot (λ x y, r i (x,y))

namespace quot

variables {α β γ : fam I}  (r : Pred (α ⊗ α))

/-- elimination rule for `fam.quot` -/
def lift (f : α ⟶ β)
  (h : ∀ {i} (a : unit i ⟶ α⊗α), a ⊨ r → a ≫ prod.fst ≫ f = a ≫ prod.snd ≫ f) :
  (quot r ⟶ β) :=
λ i x, quot.lift (@f i) (λ a b h',
  let d := value i (fam.subtype r) (subtype.mk (a,b) h') in
  value.get _ _ (h (value i _ (a,b)) ⟨d,by ext _ ⟨ ⟨ rfl ⟩ ⟩; refl⟩) ) x

/-- introduction rule for `fam.quot` -/
def mk : α ⟶ quot r :=
λ (i : I) (x : α i), quot.mk _ x

/-- noncomputable elimination rule for `fam.quot` -/
noncomputable def out : quot r ⟶ α :=
λ i x, quot.out x

variables {r}

@[simp, reassoc]
lemma mk_lift (g : α ⟶ β) (h) :
  quot.mk r ≫ lift r g h = g :=
by ext; refl

@[reassoc]
lemma lift_comp (f : α ⟶ β) (g : β ⟶ γ) (h) :
  lift r f h ≫ g = lift r (f ≫ g) (by intros; reassoc h; rw h _ a_1) :=
by { ext, dsimp [lift,(≫)], induction x_1 using quot.ind, refl }

lemma lift_ext (f g : quot r ⟶ β)
      (hh : quot.mk r ≫ f = quot.mk r ≫ g) :
  f = g :=
begin
  ext a b, apply quot.induction_on b,
  intros y, apply congr_arrow hh
end

lemma sound (f : β ⟶ α⊗α)
      (hh : f ⊨ r) :
  f ≫ prod.fst ≫ quot.mk r = f ≫ prod.snd ≫ quot.mk r :=
begin
  cases hh with f' hh, rw hh,
  ext, simp [(≫)], apply quot.sound,
  rcases (f' x_1) with ⟨⟨a,b⟩,h⟩, exact h
end

lemma sound'' {f g : β ⟶ quot r} (f' g' : β ⟶ α)
      (hh : diag ≫ fam.prod.map f' g' ⊨ r)
      (hh_f : f = f' ≫ quot.mk r)
      (hh_g : g = g' ≫ quot.mk r) :
  f = g :=
by { ext; rw [hh_f,hh_g];
     apply _root_.quot.sound; cases hh with h h',
     replace h' := congr_arrow h' x_1,
     simp [fam.prod.map,diag] at h', erw [h'];
     apply subtype.property }

lemma sound' (f g : β ⟶ α)
      (hh : diag ≫ fam.prod.map f g ⊨ r) :
  f ≫ quot.mk r = g ≫ quot.mk r :=
by apply sound'' f g hh rfl rfl

lemma ind_on (f : β ⟶ quot r) : (∃ g, f = g ≫ quot.mk _) :=
⟨f ≫ fam.quot.out _, by ext; simp [mk,out]⟩

@[simp, reassoc]
lemma out_mk (r : Pred (α ⊗ α)) : quot.out r ≫ quot.mk r = 𝟙 _ :=
by ext; simp [mk,out]; refl

open function

@[simp, reassoc]
lemma prod.diag_fst : diag ≫ fam.prod.fst = 𝟙 α :=
by ext; refl

@[simp, reassoc]
lemma prod.diag_snd : diag ≫ fam.prod.snd = 𝟙 α :=
by ext; refl

/-- swap the components of a product -/
def prod.swap : α ⊗ β ⟶ β ⊗ α :=
diag ≫ (prod.snd ⊗' prod.fst)

@[simp, reassoc]
lemma prod.swap_fst : prod.swap ≫ fam.prod.fst = (fam.prod.snd : α ⊗ β ⟶ β) :=
by simp [prod.swap]

@[simp, reassoc]
lemma prod.swap_snd : prod.swap ≫ fam.prod.snd = (fam.prod.fst : α ⊗ β ⟶ α) :=
by simp [prod.swap]

/-- reassociate the components of two nested products -/
def prod.assoc : α ⊗ β ⊗ γ ⟶ α ⊗ (β ⊗ γ) :=
diag ≫ (prod.fst ≫ prod.fst ⊗' diag ≫ (prod.fst ≫ prod.snd ⊗' prod.snd))

/-!
The following three definitions, `to_ab`, `to_bc` and `to_ac`,
are used to select two objects from a triple. They are used to
formulate transitivity using categorical notation.  -/

/-- Projection from a product of three components to the
two left-most components -/
def to_ab : α ⊗ β ⊗ γ ⟶ α ⊗ β := fam.prod.fst

/-- Projection from a product of three components to the
two right-most components -/
def to_bc : α ⊗ β ⊗ γ ⟶ β ⊗ γ := fam.prod.snd ⊗' 𝟙 _

/-- Projection from a product of three components to the
left-most and right-most components -/
def to_ac : α ⊗ β ⊗ γ ⟶ α ⊗ γ := fam.prod.fst ⊗' 𝟙 _

/--
Definition of equivalence relations for predicates on products
-/
structure equiv (r : Pred (α ⊗ α)) : Prop :=
(refl : diag ⊨ r)
(symm : ∀ {i} (f : unit i ⟶ α ⊗ α), f ⊨ r → f ≫ prod.swap ⊨ r)
  /- `trans` encodes transitivity: forall all triple of variables `(a,b,c)`,
     (which we call `abc : unit i ⟶ α ⊗ α ⊗ α`),
     if `r (a,b)` (encoded `abc ≫ to_ab ⊨ r`) and
     if `r (b,c)` (encoded `abc ≫ to_bc ⊨ r`)
     then `r (a,c)` (encoded `abc ≫ to_ac ⊨ r`)  -/
(trans : ∀ {i} (abc : unit i ⟶ α ⊗ α ⊗ α), abc ≫ to_ab ⊨ r → abc ≫ to_bc ⊨ r → abc ≫ to_ac ⊨ r)

lemma equiv.to_equivalence {r : Pred (α ⊗ α)} (h : equiv r) :
  ∀ i, equivalence $ curry (r i) :=
begin
  cases h, intro j, refine ⟨_,_,_⟩,
  { intros x, apply sat_elim _ _ h_refl },
  { intros x y h,
    have : value j (α ⊗ α) (x, y) ⊨ r,
    { apply sat_intro _ _, rintro _ ⟨ ⟩, exact h },
    specialize h_symm (value j _ (x,y)) this,
    exact sat_elim _ _ h_symm unit.rfl },
  { intros x y z h h',
    specialize h_trans (value j _ ((x,y),z)) _ _,
    { exact sat_elim _ _ h_trans unit.rfl },
    all_goals { apply sat_intro, rintros _ ⟨ ⟩, assumption }, },
end

lemma exact {r : Pred (β ⊗ β)} {f g : α ⟶ β} (h : f ≫ mk r = g ≫ mk r) (h' : equiv r) :
  diag ≫ (f ⊗' g) ⊨ r :=
begin
  apply sat_intro, intros i x,
  replace h' : ∀ i, equivalence $ curry (r i) := equiv.to_equivalence h',
  simp [diag,prod.map],
  change curry (r i) _ _, rw ← relation.eqv_gen_iff_of_equivalence (h' i),
  apply quot.exact, replace h := congr_arrow h x, simp [mk] at h, exact h,
end

lemma lift_eq_out (r : Pred (α ⊗ α)) (h : equiv r) (f : α ⟶ β) (h') : lift r f h' = out r ≫ f :=
lift_ext _ _
begin
  simp; ext i a, simp [out,mk],
  have : ∀ {i} x y, r i (x,y) → f x = f y,
  { intros j, introv hh, specialize h' (value j _ (x,y)) (sat_intro _ _ _),
    exact value.get _ _ h',
    rintro _ ⟨ ⟩, exact hh },
  replace h : ∀ i, equivalence $ curry (r i) := equiv.to_equivalence h,
  apply this, change curry (r i) _ _,
  rw ← relation.eqv_gen_iff_of_equivalence (h i),
  apply _root_.quot.exact,
  rw quot.out_eq, refl,
end

end quot

end fam

universes u' v'

namespace category_theory

namespace functor
open category_theory

section map_comp

variables {C : Type u} {D : Type u'} [category.{v} C] [category.{v'} D] (F : C ⥤ D)

@[reassoc]
lemma map_comp_map {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : F.map f ≫ F.map g = F.map (f ≫ g) :=
(category_theory.functor.map_comp _ _ _).symm

end map_comp

/-!
In the following, we treat arrows `f : X ⟶ F.obj α` as collections of objects of type
`α i`, for any `i`. The notion of containment is made formal by the definition of support set:
`supp f i : set (α i)`. Intuitively, `f` contains `a : α i` if, forall `i : I`, `x : X i`,
the `f x` evaluates to an object from which `a` can be retrieved.
-/

namespace fam

open_locale fam

variables {I J : Type u} {F G : fam I ⥤ fam J}

/-- given an arrow `x` to `F.obj α`, does `p` hold for every `α` related to `x`. -/
def liftp {α : fam I} (p : fam.Pred α) {X : fam J} (x : X ⟶ F.obj α) : Prop :=
∃ u : X ⟶ F.obj (fam.subtype p), u ≫ F.map fam.subtype.val = x

/-- `liftr r x y` relates `x` and `y` iff `x` and `y` have the same shape and that
we can pair values `a` from `x` and `b` from `y` so that `r a b` holds -/
def liftr {α β : fam I} (r : fam.Pred (α ⊗ β)) {X : fam J} (x : X ⟶ F.obj α) (y : X ⟶ F.obj β) : Prop :=
∃ u : X ⟶ F.obj (fam.subtype r),
  u ≫ F.map (fam.subtype.val ≫ fam.prod.fst) = x ∧
  u ≫ F.map (fam.subtype.val ≫ fam.prod.snd) = y

/-- `supp x` is the set of values of type `α` that `x` contains -/
def supp {α : fam I} {X : fam J} (x : X ⟶ F.obj α) (ι : I) : set (α ι) :=
{ y : α ι | ∀ ⦃p⦄, liftp p x → p _ y }

theorem of_mem_supp {α : fam I} {X : fam J} {x : X ⟶ F.obj α} {p : fam.Pred α} (h : liftp p x) :
  ∀ i (y ∈ supp x i), p _ y :=
λ i y hy, hy h

lemma liftp_comp {α : fam I} {X : fam J} {p : Π i, α i → Prop}
  (x : X ⟶ F.obj α) (h : F ⟶ G) :
  liftp p x → liftp p (x ≫ h.app _)
| ⟨u,h'⟩ := ⟨u ≫ nat_trans.app h _, by rw ← h'; simp,⟩

lemma liftp_comp' {α : fam I} {X : fam J} {p : Π i, α i → Prop}
  (x : X ⟶ F.obj α) (T : F ⟶ G) (T' : G ⟶ F)
  (h_inv : ∀ {α}, T.app α ≫ T'.app α = 𝟙 _) :
  liftp p x ↔ liftp p (x ≫ T.app _) :=
⟨ liftp_comp x T,
 λ ⟨u,h'⟩, ⟨u ≫ T'.app _,by rw [category.assoc,← nat_trans.naturality,← category.assoc,h',category.assoc,h_inv,category.comp_id]⟩ ⟩

lemma liftr_comp {α : fam I} {X : fam J} (p : fam.Pred (α ⊗ α)) (x y : X ⟶ F.obj α)
   (T : F ⟶ G) :
  liftr p x y → liftr p (x ≫ T.app _) (y ≫ T.app _)
| ⟨u,h,h'⟩ := ⟨u ≫ T.app _,
  by { reassoc! h h',
       rw ← h'; simp only [category.assoc, (nat_trans.naturality _ _).symm,*,eq_self_iff_true, and_self] }⟩

end fam

end functor

end category_theory
