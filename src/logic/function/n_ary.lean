
import tactic.congr

universes v u

@[nolint has_nonempty_instance]
def function_of' {ι : Type*} (α : ι → Type u) (β : Type max v u) : list ι → Type max v u
| []       := β
| (i :: l) := α i → function_of' l

namespace function_of'
variables {ι : Type*} {α : ι → Type u} [s : Π i, setoid (α i)] {β γ : Type max v u}

@[simp] def map : Π {l : list ι},
  (β → γ) → function_of' α β l → function_of' α γ l
| []       f x := f x
| (i :: l) f x := λ a, map f (x a)

include s

protected def equiv : Π {l : list ι}, function_of' α β l → function_of' α β l → Prop
| []       f₁ f₂ := f₁ = f₂
| (i :: l) f₁ f₂ := ∀ a b : α i, a ≈ b → equiv (f₁ a) (f₂ b)

lemma equiv.map : Π {l : list ι}
  {x y : function_of' α β l} (h : x.equiv y) (f : β → γ), (x.map f).equiv (y.map f)
| []       x y h f := congr_arg _ h
| (i :: l) x y h f := λ a b hab, (h a b hab).map f

def quotient_lift_aux : Π {l : list ι},
  Σ' lift : Π (f : function_of' α β l), function_of'.equiv f f →
    function_of' (λ i, quotient (s i)) β l,
    ∀ {f f' : function_of' α β l} (h h'), function_of'.equiv f f' → lift f h = lift f' h'
| []     := ⟨λ f _, f, λ _ _ _ _, id⟩
| (i::l) := ⟨λ f h, quotient.lift (λ a, quotient_lift_aux.1 (f a) ((h a a (@setoid.refl _ _ a))))
      (λ a a' ha, quotient_lift_aux.2 _ _ (h _ _ ha)),
    λ f f' h h' hf, (by { congr', ext a, -- I'm not sure if it's possible to avoid `quot.sound`
      exact quotient_lift_aux.2 _ _ (hf _ _ (@setoid.refl _ _ a)) })⟩

def quotient_lift {l : list ι} (f : function_of' α β l) :
  function_of'.equiv f f → function_of' (λ i, quotient (s i)) β l :=
quotient_lift_aux.1 f

@[simp] lemma quotient_lift_nil (f : function_of' α β []) (h) :
  quotient_lift f h = f :=
rfl

@[simp] lemma quotient_lift_cons {i : ι} {l : list ι} (f : function_of' α β (i::l)) (h) :
  quotient_lift f h = quotient.lift (λ a, quotient_lift (f a) (h a a (setoid.refl a)))
      (λ a a' ha, quotient_lift_aux.2 _ _ (h _ _ ha)) :=
rfl

omit s

end function_of'

@[nolint has_nonempty_instance]
def function_of {ι : Type*} (α : ι → Type u) (β : Type u) : list ι → Type u :=
function_of'.{u} α β

namespace function_of
variables {ι : Type*} {α : ι → Type u} [s : Π i, setoid (α i)] {β γ : Type u}

@[simp] def map {l : list ι} : (β → γ) → function_of α β l → function_of α γ l :=
function_of'.map

include s

protected def equiv {l : list ι} : function_of α β l → function_of α β l → Prop :=
function_of'.equiv

lemma equiv.map {l : list ι} {x y : function_of α β l} (h : x.equiv y) (f : β → γ) :
  (x.map f).equiv (y.map f) :=
function_of'.equiv.map h f

def quotient_lift {l : list ι} (f : function_of α β l) :
  function_of.equiv f f → function_of (λ i, quotient (s i)) β l :=
function_of'.quotient_lift f

@[simp] lemma quotient_lift_nil (f : function_of α β []) (h) :
  quotient_lift f h = f :=
rfl

@[simp] lemma quotient_lift_cons {i : ι} {l : list ι} (f : function_of α β (i::l)) (h) :
  quotient_lift f h = quotient.lift (λ a, quotient_lift (f a) (h a a (setoid.refl a)))
    (λ a a' ha, function_of'.quotient_lift_aux.2 _ _ (h _ _ ha)) :=
rfl

omit s

end function_of

/-- The type of `n`-ary functions `α → α → ... → β`. -/
def arity (α β : Type u) (n : ℕ) : Type u := function_of (λ _, α) β (list.replicate n ())

@[simp] theorem arity_zero (α β : Type u) : arity α β 0 = β := rfl
@[simp] theorem arity_succ (α β : Type u) (n : ℕ) : arity α β n.succ = (α → arity α β n) := rfl

namespace arity

variables (α : Type u) [s : setoid α] {β γ : Type u} (b : β)

/-- Constant `n`-ary function with value `a`. -/
def const : ∀ n, arity α β n
| 0     := b
| (n+1) := λ _, const n

@[simp] theorem const_zero : const α b 0 = b := rfl
@[simp] theorem const_succ (n : ℕ) : const α b n.succ = λ _, const α b n := rfl

variable {α}

theorem const_succ_apply (n : ℕ) (x : α) : const α b n.succ x = const α b n := rfl

instance arity.inhabited [inhabited β] {n} : inhabited (arity α β n) := ⟨const _ default _⟩

variables {n : ℕ}
include s

/-- Function equivalence is defined so that `f ~ g` iff `∀ x y, x ~ y → f x = g y`. This extends to
equivalence of `n`-ary functions. -/
protected def equiv : arity α β n → arity α β n → Prop := function_of.equiv

@[simp] lemma equiv_zero_iff (a b : arity α β 0) : arity.equiv a b ↔ a = b := iff.rfl
@[simp] lemma equiv_succ_iff (a b : arity α β n.succ) :
  arity.equiv a b ↔ ∀ x y, x ≈ y → arity.equiv (a x) (b y) := iff.rfl

lemma equiv_const : ∀ n, (const α b n).equiv (const α b n)
| 0     := rfl
| (n+1) := λ x y h, equiv_const _

@[simp] lemma equiv.refl_zero (b : β) : @arity.equiv α s β 0 b b := by exact rfl

variables (n)

def quotient_lift {n : ℕ} (f : arity α β n) : arity.equiv f f → arity (quotient s) β n :=
function_of.quotient_lift f

omit s
variables {n}

@[simp] def map : (β → γ) → arity α β n → arity α γ n := function_of.map

include s

lemma equiv.map {x y : arity α β n} : ∀ (h : x.equiv y) (f : β → γ), (x.map f).equiv (y.map f) :=
function_of.equiv.map

omit s

end arity
