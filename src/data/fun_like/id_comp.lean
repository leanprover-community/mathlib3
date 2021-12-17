import data.fun_like.equiv
import tactic.congr

universes u v

-- Don't want this to be a global instance because it'll insert `coe_fn` everywhere
-- if you're not careful.
def function.fun_like (A : Sort*) (B : A → Sort*) : fun_like (Π x : A, B x) A B :=
{ coe := id, coe_injective' := λ _ _ h, h }

-- Structure-based attempt:

/-- The class `has_id F A` states the bundled `A`-endomorphisms of type `I` include an
identity map `has_id.id`. -/
class has_id (I : Sort u) (A : out_param $ Sort v) [fun_like I A (λ _, A)] : Type u :=
(id [] : I) (id_apply [] : ∀ x, id x = x)

namespace has_id

variables (I : Sort*) {A : Sort*} [fun_like I A (λ _, A)] [i : has_id I A]
include i

@[simp] lemma coe : coe_fn (id I) = _root_.id := funext (id_apply I)

end has_id

/-
/-- An `id_fun F` is the identity function as a bundled morphism of type `F`. -/
structure id_fun (F : Sort*) {A : Sort*} [fun_like F A (λ _, A)] :=
(to_fun : F) (apply' : ∀ x, to_fun x = x)

namespace id_fun

instance (A : Sort*) : inhabited (id_fun (A → A)) := ⟨⟨id, λ x, rfl⟩⟩

variables (F : Sort*) {A : Sort*} [i : fun_like F A (λ _, A)]
include i

instance : has_coe (id_fun F) F := ⟨to_fun⟩

instance : has_coe_to_fun (id_fun F) (λ _, A → A) := ⟨λ id, ⇑(to_fun id)⟩

instance : equiv_like (id_fun F) A A :=
{ coe := λ id, ⇑(to_fun id), inv := λ id, ⇑(to_fun id),
  coe_injective' := λ f g h₁ h₂, by { cases f with f, cases g with g,
                                      have : f = g := fun_like.coe_injective h₁, congr' },
  left_inv := λ e x, (apply' _ _).trans (apply' _ _),
  right_inv := λ e x, (apply' _ _).trans (apply' _ _) }

lemma subsingleton : subsingleton (id_fun F) :=
⟨λ i i', fun_like.ext i i' $ λ x, (apply' i x).trans (apply' i' x).symm⟩

variables {F A} (id : id_fun F)

@[simp] lemma coe_coe : ⇑(↑id : F) = (⇑id : A → A) := rfl

lemma apply (x : A) : id x = x := id.apply' x
@[simp] lemma coe : (id : A → A) = _root_.id := funext $ apply id

end id_fun
-/

/-- A `symm_fun E E'` sends a bundled morphism in `E` to its two-sided inverse in `E'` -/
@[nolint has_inhabited_instance]
structure symm_fun (E E' : Sort*) {A B : Sort*}
  [fun_like E A (λ _, B)] [fun_like E' B (λ _, A)] :=
(to_fun : E → E')
(symm_apply_apply' : ∀ (e : E) (x : A), to_fun e (e x) = x)
(apply_symm_apply' : ∀ (e : E) (x : B), e (to_fun e x) = x)

namespace symm_fun

section fun_like

variables (E E' : Sort*) {A B : Sort*}
variables [i₁ : fun_like E A (λ _, B)] [i₂ : fun_like E' B (λ _, A)]
include i₁ i₂

instance : has_coe_to_fun (symm_fun E E') (λ _, E → E') := ⟨to_fun⟩

instance symm_fun.fun_like : fun_like (symm_fun E E') E (λ _, E') :=
{ coe := to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' } }

variables {E E'} (symm : symm_fun E E') (e : E) (e' : E')

@[simp] lemma symm_apply_apply (x : A) : symm e (e x) = x := symm_apply_apply' symm e x
@[simp] lemma apply_symm_apply (x : B) : e (symm e x) = x := apply_symm_apply' symm e x

/-- Use the existence of a `symm_fun` to promote a `fun_like` to an `equiv_like`. -/
protected def equiv_like (symm : symm_fun E E') : equiv_like E A B :=
{ coe := λ e, e, inv := λ e, symm e,
  left_inv := λ e x, symm.symm_apply_apply e x,
  right_inv := λ e x, symm.apply_symm_apply e x,
  coe_injective' := λ e e' h₁ h₂, fun_like.coe_injective h₁, }

theorem left_inverse : function.left_inverse (symm e) e := symm.symm_apply_apply e

theorem right_inverse : function.right_inverse (symm e) e := symm.apply_symm_apply e

end fun_like

section equiv_like

variables {E E' A B : Sort*}
variables [i₁ : equiv_like E A B] [i₂ : equiv_like E' B A]
include i₁ i₂
variables (symm : symm_fun E E') (e : E) (e' : E')

theorem apply_eq_iff_eq_symm_apply {x : A} {y : B} :
  e x = y ↔ x = symm e y :=
begin
  conv_lhs { rw ← symm.apply_symm_apply e y, },
  rw equiv_like.apply_eq_iff_eq,
end

lemma symm_apply_eq {x y} : symm e x = y ↔ x = e y :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

lemma eq_symm_apply {x y} : y = symm e x ↔ e y = x :=
(eq_comm.trans (symm.symm_apply_eq e)).trans eq_comm

@[simp] theorem symm_symm (symm' : symm_fun E' E) : symm' (symm e) = e :=
fun_like.ext _ _ $ λ x, by rw [symm_apply_eq, symm_apply_apply]

end equiv_like

end symm_fun

section id_symm

open has_id

@[simp] theorem id_symm {E A : Sort*} [equiv_like E A A] [has_id E A]
  (symm : symm_fun E E) : symm (id E) = id E :=
fun_like.ext _ _ $ λ x,
by rw [← id_apply E (symm (id E) x), symm.apply_symm_apply (id E) x, id_apply]

end id_symm

/-- A `comp_fun FBC FAB FAC` composes bundled morphisms in `FBC` after `FAB` giving `FAC`. -/
structure comp_fun (FBC FAB FAC : Sort*) {A B C : Sort*}
  [fun_like FAB A (λ _, B)] [fun_like FBC B (λ _, C)] [fun_like FAC A (λ _, C)] :=
(to_fun : FBC → FAB → FAC) (apply : ∀ f g x, to_fun f g x = f (g x))

namespace comp_fun

variables (FBC FAB FAC : Sort*) {A B C : Sort*}

local attribute [instance] function.fun_like

instance : inhabited (comp_fun (B → C) (A → B) (A → C)) := ⟨⟨(∘), λ f g x, rfl⟩⟩

variables [i₁ : fun_like FAB A (λ _, B)] [i₂ : fun_like FBC B (λ _, C)] [i₃ : fun_like FAC A (λ _, C)]
include i₁ i₂ i₃

instance : has_coe_to_fun (comp_fun FBC FAB FAC) (λ _, FBC → FAB → FAC) := ⟨to_fun⟩

instance comp_fun.fun_like : fun_like (comp_fun FBC FAB FAC) FBC (λ _, FAB → FAC) :=
{ coe := to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' } }

lemma subsingleton : subsingleton (comp_fun FBC FAB FAC) :=
⟨λ c c', fun_like.ext c c' $ λ f, funext $ λ g, fun_like.ext (c f g) (c' f g) $ λ x,
  (apply c f g x).trans (apply c' f g x).symm⟩

variables {FBC FAB FAC} (comp : comp_fun FBC FAB FAC) (f : FBC) (g : FAB)

@[simp] lemma coe : (comp f g : A → C) = f ∘ g := funext $ apply comp f g

end comp_fun

-- TODO: can we deduplicate everything below?
/-- A `trans_fun FAB FBC FAC` composes bundled morphisms in `FAB` after `FBC` giving `FAC`.

This is exactly the same as `comp_fun` with the order of its arguments flipped,
for nicer notation involving `equiv`s.
-/
structure trans_fun (FAB FBC FAC : Sort*) {A B C : Sort*}
  [fun_like FAB A (λ _, B)] [fun_like FBC B (λ _, C)] [fun_like FAC A (λ _, C)] :=
(to_fun : FAB → FBC → FAC) (apply' : ∀ f g x, to_fun f g x = g (f x))

namespace trans_fun

variables (FBC FAB FAC : Sort*) {A B C : Sort*}

local attribute [instance] function.fun_like

instance : inhabited (trans_fun (A → B) (B → C) (A → C)) := ⟨⟨λ f g, g ∘ f, λ f g x, rfl⟩⟩

variables [i₁ : fun_like FAB A (λ _, B)] [i₂ : fun_like FBC B (λ _, C)] [i₃ : fun_like FAC A (λ _, C)]
include i₁ i₂ i₃

instance : has_coe_to_fun (trans_fun FAB FBC FAC) (λ _, FAB → FBC → FAC) := ⟨to_fun⟩

instance trans_fun.fun_like : fun_like (trans_fun FAB FBC FAC) FAB (λ _, FBC → FAC) :=
{ coe := to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' } }

lemma subsingleton : subsingleton (trans_fun FAB FBC FAC) :=
⟨λ c c', fun_like.ext c c' $ λ f, funext $ λ g, fun_like.ext (c f g) (c' f g) $ λ x,
  (apply' c f g x).trans (apply' c' f g x).symm⟩

variables {FBC FAB FAC} (trans : trans_fun FAB FBC FAC) (f : FAB) (g : FBC)

lemma apply (x : A) : trans f g x = g (f x) := apply' trans f g x

@[simp] lemma coe : (trans f g : A → C) = g ∘ f := funext $ apply trans f g

lemma assoc {FAD FBD FCD D}
  [fun_like FAD A (λ _, D)] [fun_like FBD B (λ _, D)] [fun_like FCD C (λ _, D)]
  (transABC : trans_fun FAB FBC FAC) (transACD : trans_fun FAC FCD FAD)
  (transABD : trans_fun FAB FBD FAD) (transBCD : trans_fun FBC FCD FBD)
  (h : FCD) :
  transACD (transABC f g) h = transABD f (transBCD g h) :=
fun_like.ext _ _ $ λ x, by rw [apply, apply, apply, apply]

end trans_fun

section id_symm_trans

open has_id

variables {FAA FAB FBB A B : Sort*}
variables [fun_like FAA A (λ _, A)] [fun_like FAB A (λ _, B)] [fun_like FBB B (λ _, B)]
variables [has_id FAA A] [has_id FBB B]
variables (transAAB : trans_fun FAA FAB FAB) (transABB : trans_fun FAB FBB FAB)

@[simp] theorem trans_id (f : FAB) : transABB f (id FBB) = f :=
fun_like.ext _ _ $ λ x, by simp

@[simp] theorem id_trans (f : FAB) : transAAB (id FAA) f = f :=
fun_like.ext _ _ $ λ x, by simp

variables {FBA : Sort*} [fun_like FBA B (λ _, A)]
variables (symmAB : symm_fun FAB FBA)
variables (transABA : trans_fun FAB FBA FAA) (transBAB : trans_fun FBA FAB FBB)

@[simp] theorem symm_trans_self (e : FAB) : transBAB (symmAB e) e = id FBB :=
fun_like.ext _ _ $ λ x, by simp

@[simp] theorem self_trans_symm (e : FAB) : transABA e (symmAB e) = id FAA :=
fun_like.ext _ _ $ λ x, by simp

end id_symm_trans
