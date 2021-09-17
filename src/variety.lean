import data.fin

/-- a signature consists of, for every `n`, a type of `n`-ary 'function symbols' -/
structure signature :=
(symbol : Π n : ℕ, Type)

variable (σ : signature)

/-- a structure of a given signature consists of an intepretation of every `n`-ary function symbol
as an `n`-ary function -/
class struct (A : Type) :=
(function : Π {n : ℕ} (s : σ.symbol n), (fin n → A) → A)

/-- this coercion lets us write `[σ A]` to say that `A` is a `σ-struct` -/
instance : has_coe_to_fun signature := ⟨_, struct⟩

variable {σ}

def signature.symbol.app {n} (s : σ.symbol n) {A} [σ A] (v : fin n → A) : A :=
struct.function s v

variable (σ)

/-- a morphism of structures is a function on the underlying sets which commutes with all function
symbols -/
@[ext] structure signature.hom (A B) [σ A] [σ B] :=
(to_fun : A → B)
(app_comm' : ∀ {n} (s : σ.symbol n) (v : fin n → A),
  to_fun (s.app v) = s.app (to_fun ∘ v))

/-- a morphism of structures can be coerced to a function -/
instance (A B) [struct σ A] [struct σ B] : has_coe_to_fun (σ.hom A B) :=
⟨_, signature.hom.to_fun⟩

variable {σ}

@[simp] lemma signature.hom.app_comm {A B} [σ A] [σ B] (f : σ.hom A B) {n} (s : σ.symbol n)
  (v : fin n → A) : f (s.app v) = s.app (f ∘ v) := f.app_comm' s v

variable (σ)

/-- the free structure on a given signature. we use this to describe operations derived from the
primitive ones, like how `a*b + a*c` is derived from `+` and `*`. -/
inductive free_struct (A : Type) : Type
| of : A → free_struct
| function (n : ℕ) (f : σ.symbol n) (v : fin n → free_struct) : free_struct

/-- the tautological structure on the free struct -/
@[simps] instance (A) : struct σ (free_struct σ A) :=
{ function := free_struct.function }

/-- two homs out of a free structure are equal if they agree on generators -/
@[ext] lemma free_stuff_ext (A B) [σ B] (f g : σ.hom (free_struct σ A) B)
  (h : ∀ a, f (free_struct.of a) = g (free_struct.of a)) : f = g :=
begin
  ext x,
  induction x with a n s v ih,
  { apply h },
  { rw ←free_struct.struct_function,
    change f (s.app v) = g (s.app v),
    rw [f.app_comm, g.app_comm],
    congr' 1,
    ext,
    apply ih, }
end

/-- thinking of an element of `free_struct A` as a polynomial expression in variables `A`, this
function lets us evaluate the expression in a struct `B`, provided we have an assignment `A → B` of
variables. -/
def eval' {A B} (g : A → B) [σ B] : free_struct σ A → B
| (free_struct.of a) := g a
| (free_struct.function n s v) := s.app $ λ i, eval' (v i)

/-- evaluation is a hom -/
def eval {A B} (g : A → B) [σ B] : σ.hom (free_struct σ A) B :=
{ to_fun := eval' σ g, app_comm' := λ n s v, rfl }

/-- the identity hom on a struct -/
def signature.id_hom (A) [σ A] : σ.hom A A := ⟨id, λ n s v, rfl⟩

variable {σ}

/-- composition of homs -/
def signature.hom.comp {A B C} [σ A] [σ B] [σ C] (f : σ.hom B C) (g : σ.hom A B) :
  σ.hom A C :=
{ to_fun    := f ∘ g,
  app_comm' := by intros; rw [function.comp_app, function.comp.assoc, g.app_comm, f.app_comm] }

/-- evaluation is natural in structure homs -/
lemma eval_naturality {A B C} [σ B] [σ C] (g : A → B) (f : σ.hom B C) :
  f.comp (eval σ g) = eval σ (f ∘ g) :=
by ext; refl

/-- if `f = g` then `f a = g a` -/
lemma signature.hom.congr_fun {A B} [σ A] [σ B] {f g : σ.hom A B} (h : f = g) (a : A) :
  f a = g a :=
  by rw h

variable (σ)

/-- the product structure -/
instance (A B) [σ A] [σ B] : struct σ (A × B) :=
{ function := λ n s v, (s.app (prod.fst ∘ v), s.app (prod.snd ∘ v)) }

/-- projection onto first factor is a hom -/
def fst_hom (A B) [σ A] [σ B] : σ.hom (A × B) A :=
{ to_fun := prod.fst, app_comm' := by intros; refl }

/-- projection onto second factor is a hom -/
def snd_hom (A B) [σ A] [σ B] : σ.hom (A × B) B :=
{ to_fun := prod.snd, app_comm' := by intros; refl }

/-- an axiom in a given signature consists of an arity `n` together with two polynomial
expressions `lhs, rhs` in `n` variables, which are required to equal one another for any choice
of inputs -/
structure axio :=
(arity : ℕ)
(lhs : free_struct σ (fin arity))
(rhs : free_struct σ (fin arity))

/-- a theory is an indexed family of axioms -/
structure theory :=
(ι : Type)
(to_fun : Π i : ι, axio σ)

/-- the relation 'a is an axiom in theory T' -/
instance : has_mem (axio σ) (theory σ) := ⟨λ a T, a ∈ set.range T.to_fun⟩

variables {σ} (T : theory σ)

/-- a struct models some theory if it satisfies all its axioms. to be more in line with mathlib,
this should bundle the struct -/
class lawful_struct (A) [struct σ A] : Prop :=
(lhs_eq_rhs : ∀ (a ∈ T) (v : fin (axio.arity a) → A),
  eval σ v a.lhs = eval σ v a.rhs)

/-- a product of lawful structures is lawful -/
instance (A B) [struct σ A] [struct σ B] [lawful_struct T A] [lawful_struct T B] :
  lawful_struct T (A × B) :=
{ lhs_eq_rhs := begin
    intros a ha v,
    ext,
    { change fst_hom σ A B _ = fst_hom σ A B _,
      erw signature.hom.congr_fun (eval_naturality _ (fst_hom σ A B)),
      erw signature.hom.congr_fun (eval_naturality _ (fst_hom σ A B)),
      exact lawful_struct.lhs_eq_rhs a ha (prod.fst ∘ v), },
    { change snd_hom σ A B _ = snd_hom σ A B _,
      erw signature.hom.congr_fun (eval_naturality _ (snd_hom σ A B)),
      erw signature.hom.congr_fun (eval_naturality _ (snd_hom σ A B)),
      exact lawful_struct.lhs_eq_rhs a ha (prod.snd ∘ v), }
  end }
