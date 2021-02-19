import category_theory.eq_to_hom
import category_theory.limits.shapes.zero
import algebra.ring
import algebra.homology.chain_complex
import tactic.linarith

open category_theory
open category_theory.limits

variables {V : Type*} [category V] [has_zero_morphisms V]

section tra
variables {α : Type*} (f : α → V)

def tra {a b : α} (h : a = b . obviously) : f a ⟶ f b :=
eq_to_hom (congr_arg f h)

@[simp] lemma tra_refl (a : α) : tra f (eq.refl a) = 𝟙 (f a) := rfl
@[simp, reassoc] lemma tra_comp {a b c : α} (h : a = b) (g : b = c) :
  tra f h ≫ tra f g = tra f (h.trans g) :=
by { induction h, induction g, simp, }

end tra

variables {N : Type*} [add_comm_monoid N]
variables (V)

meta def d_squared_tac : tactic unit :=
`[{ intros n m h, simp at h, try { subst h}, obviously }]

structure hc (a b : N) :=
(X : N → V)
(d : Π n : N, X (n + a) ⟶ X (n + b))
(d_squared' : ∀ (n m : N) (h : n + b = m + a), d n ≫ tra X h ≫ d m = 0 . d_squared_tac)

restate_axiom hc.d_squared'
attribute [simp] hc.d_squared

namespace hc

variables {V} {a b : N}

@[ext]
structure hom (C D : hc V a b) :=
(f : Π n, C.X n ⟶ D.X n)
(comm' : ∀ n, f (n+a) ≫ D.d n = C.d n ≫ f (n+b) . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

namespace hom

@[simp, reassoc]
lemma f_tra {C D : hc V a b} (f : hom C D) {i j : N} (h : i = j) :
  f.f i ≫ tra D.X h = tra C.X h ≫ f.f j :=
begin
  induction h, simp,
end

@[simps]
def id (C : hc V a b) : hom C C :=
{ f := λ n, 𝟙 _,
  comm' := λ n, by simp, }

@[simps]
def comp {C D E : hc V a b} (f : hom C D) (g : hom D E) : hom C E :=
{ f := λ n, f.f n ≫ g.f n,
  comm' := λ n, by simp, }

end hom

instance : category (hc V a b) :=
{ hom := hom,
  id := λ C, hom.id C,
  comp := λ C D E f g, hom.comp f g, }

@[simp] lemma id_f (C : hc V a b) (n : N) : hom.f (𝟙 C) n = 𝟙 (C.X n) := rfl
@[simp] lemma comp_f {C D E : hc V a b} (f : C ⟶ D) (g : D ⟶ E) (n : N) :
  (f ≫ g).f n = f.f n ≫ g.f n := rfl

end hc

-- @[simp, reassoc]
-- lemma cochain_complex_d_tra (C : cochain_complex V) {i j : ℤ} (h : i + 1 = j + 1) :
--   C.d i ≫ (tra C.X h : _) = tra C.X begin dsimp, linarith, end ≫ C.d j :=
-- by { sorry, }

@[simp, reassoc]
lemma cochain_complex_f_tra {C D : cochain_complex V} (f : C ⟶ D) {i j : ℤ} (h : i = j) :
  f.f i ≫ tra D.X h = tra C.X h ≫ f.f j :=
by { induction h, simp, }

@[simps]
def foo : hc V (0 : ℤ) (1 : ℤ) ⥤ cochain_complex V :=
{ obj := λ C,
  { X := λ i, C.X i,
    d := λ i, tra C.X ≫ C.d i, },
  map := λ C D f,
  { f := λ i, f.f i, } }

@[simps]
def bar : cochain_complex V ⥤ hc V (0 : ℤ) (1 : ℤ) :=
{ obj := λ C,
  { X := λ i, C.X i,
    d := λ i, tra C.X ≫ C.d i, },
  map := λ C D f,
  { f := λ i, f.f i, } }.

local attribute [reducible] tra

def quux : hc V (0 : ℤ) (1 : ℤ) ≌ cochain_complex V :=
{ functor := foo V,
  inverse := bar V,
  unit_iso := nat_iso.of_components
    (λ C, { hom := { f := λ i, 𝟙 _, }, inv := { f := λ i, 𝟙 _, }})
    (by tidy),
  counit_iso := nat_iso.of_components
    (λ C, { hom := { f := λ i, 𝟙 _, }, inv := { f := λ i, 𝟙 _, }})
    sorry, }
