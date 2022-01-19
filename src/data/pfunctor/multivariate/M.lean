/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import data.pfunctor.univariate
import data.pfunctor.multivariate.basic

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

 * `M.mk`     - constructor
 * `M.dest`   - destructor
 * `M.corec`  - corecursor: useful for formulating infinite, productive computations
 * `M.bisim`  - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

 * `Mp`: polynomial functor
 * `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `Mp` as:

 * A := a possibly infinite tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   from the root of `t` to any given node.

As a result `Mp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

universe u

open_locale mvfunctor

namespace mvpfunctor
open typevec

variables {n : ℕ} (P : mvpfunctor.{u} (n+1))

/-- A path from the root of a tree to one of its node -/
inductive M.path : P.last.M → fin2 n → Type u
| root (x : P.last.M) (a : P.A) (f : P.last.B a → P.last.M) (h : pfunctor.M.dest x = ⟨a, f⟩)
       (i : fin2 n) (c : P.drop.B a i) :
    M.path x i
| child (x : P.last.M) (a : P.A) (f : P.last.B a → P.last.M) (h : pfunctor.M.dest x = ⟨a, f⟩)
      (j : P.last.B a) (i : fin2 n) (c : M.path (f j) i) :
    M.path x i

instance M.path.inhabited (x : P.last.M) {i} [inhabited (P.drop.B x.head i)] :
  inhabited (M.path P x i) :=
⟨ M.path.root _ (pfunctor.M.head x) (pfunctor.M.children x)
  (pfunctor.M.cases_on' x $
    by intros; simp [pfunctor.M.dest_mk]; ext; rw pfunctor.M.children_mk; refl) _
    (default _) ⟩

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `Wp.obj α` is made of a tree and a function
from its valid paths to the values it contains -/
def Mp : mvpfunctor n :=
{ A := P.last.M, B := M.path P }

/-- `n`-ary M-type for `P` -/
def M (α : typevec n) : Type* := P.Mp.obj α

instance mvfunctor_M : mvfunctor P.M := by delta M; apply_instance
instance inhabited_M {α : typevec _}
  [I : inhabited P.A]
  [Π (i : fin2 n), inhabited (α i)] :
  inhabited (P.M α) :=
@obj.inhabited _ (Mp P) _ (@pfunctor.M.inhabited P.last I) _

/-- construct through corecursion the shape of an M-type
without its contents -/
def M.corec_shape {β : Type u}
    (g₀ : β → P.A)
    (g₂ : Π b : β, P.last.B (g₀ b) → β) :
  β → P.last.M :=
pfunctor.M.corec (λ b, ⟨g₀ b, g₂ b⟩)

/-- Proof of type equality as an arrow -/
def cast_dropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' :=
λ i b, eq.rec_on h b

/-- Proof of type equality as a function -/
def cast_lastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' :=
λ b, eq.rec_on h b

/-- Using corecursion, construct the contents of an M-type -/
def M.corec_contents {α : typevec.{u} n} {β : Type u}
    (g₀ : β → P.A)
    (g₁ : Π b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : Π b : β, P.last.B (g₀ b) → β) :
  Π x b, x = M.corec_shape P g₀ g₂ b → M.path P x ⟹ α
| ._ b h ._ (M.path.root x a f h' i c)    :=
  have a = g₀ b,
    by { rw [h, M.corec_shape, pfunctor.M.dest_corec] at h', cases h', refl },
  g₁ b i (P.cast_dropB this i c)
| ._ b h ._ (M.path.child x a f h' j i c) :=
  have h₀ : a = g₀ b,
    by { rw [h, M.corec_shape, pfunctor.M.dest_corec] at h', cases h', refl },
  have h₁ : f j = M.corec_shape P g₀ g₂ (g₂ b (cast_lastB P h₀ j)),
    by { rw [h, M.corec_shape, pfunctor.M.dest_corec] at h', cases h', refl },
  M.corec_contents (f j) (g₂ b (P.cast_lastB h₀ j)) h₁ i c

/-- Corecursor for M-type of `P` -/
def M.corec' {α : typevec n} {β : Type u}
    (g₀ : β → P.A)
    (g₁ : Π b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : Π b : β, P.last.B (g₀ b) → β) :
  β → P.M α :=
λ b, ⟨M.corec_shape P g₀ g₂ b, M.corec_contents P g₀ g₁ g₂ _ _ rfl⟩

/-- Corecursor for M-type of `P` -/
def M.corec {α : typevec n} {β : Type u} (g : β → P.obj (α.append1 β)) :
  β → P.M α :=
M.corec' P
  (λ b, (g b).fst)
  (λ b, drop_fun (g b).snd)
  (λ b, last_fun (g b).snd)

/-- Implementation of destructor for M-type of `P` -/
def M.path_dest_left {α : typevec n} {x : P.last.M}
    {a : P.A} {f : P.last.B a → P.last.M} (h : pfunctor.M.dest x = ⟨a, f⟩)
    (f' : M.path P x ⟹ α) :
  P.drop.B a ⟹ α :=
λ i c, f' i (M.path.root x a f h i c)

/-- Implementation of destructor for M-type of `P` -/
def M.path_dest_right {α : typevec n} {x : P.last.M}
    {a : P.A} {f : P.last.B a → P.last.M} (h : pfunctor.M.dest x = ⟨a, f⟩)
    (f' : M.path P x ⟹ α) :
  Π j : P.last.B a, M.path P (f j) ⟹ α :=
λ j i c, f' i (M.path.child x a f h j i c)

/-- Destructor for M-type of `P` -/
def M.dest' {α : typevec n} {x : P.last.M}
    {a : P.A} {f : P.last.B a → P.last.M} (h : pfunctor.M.dest x = ⟨a, f⟩)
    (f' : M.path P x ⟹ α) :
  P.obj (α.append1 (P.M α)) :=
⟨a, split_fun (M.path_dest_left P h f') (λ x, ⟨f x, M.path_dest_right P h f' x⟩)⟩

/-- Destructor for M-types -/
def M.dest {α : typevec n} (x : P.M α) : P.obj (α ::: P.M α) :=
M.dest' P (sigma.eta $ pfunctor.M.dest x.fst).symm x.snd

/-- Constructor for M-types -/
def M.mk  {α : typevec n} : P.obj (α.append1 (P.M α)) → P.M α :=
M.corec _ (λ i, append_fun id (M.dest P) <$$> i)

theorem M.dest'_eq_dest' {α : typevec n} {x : P.last.M}
    {a₁ : P.A} {f₁ : P.last.B a₁ → P.last.M} (h₁ : pfunctor.M.dest x = ⟨a₁, f₁⟩)
    {a₂ : P.A} {f₂ : P.last.B a₂ → P.last.M} (h₂ : pfunctor.M.dest x = ⟨a₂, f₂⟩)
    (f' : M.path P x ⟹ α) : M.dest' P h₁ f' = M.dest' P h₂ f' :=
by cases h₁.symm.trans h₂; refl

theorem M.dest_eq_dest' {α : typevec n} {x : P.last.M}
    {a : P.A} {f : P.last.B a → P.last.M} (h : pfunctor.M.dest x = ⟨a, f⟩)
    (f' : M.path P x ⟹ α) : M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
M.dest'_eq_dest' _ _ _ _

theorem M.dest_corec' {α : typevec.{u} n} {β : Type u}
    (g₀ : β → P.A)
    (g₁ : Π b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : Π b : β, P.last.B (g₀ b) → β)
    (x : β) :
  M.dest P (M.corec' P g₀ g₁ g₂ x)  =
    ⟨g₀ x, split_fun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ (g₂ x))⟩ :=
rfl

theorem M.dest_corec {α : typevec n} {β : Type u} (g : β → P.obj (α.append1 β)) (x : β) :
  M.dest P (M.corec P g x) = append_fun id (M.corec P g) <$$> g x :=
begin
  transitivity, apply M.dest_corec',
  cases g x with a f, dsimp,
  rw mvpfunctor.map_eq, congr,
  conv { to_rhs, rw [←split_drop_fun_last_fun f, append_fun_comp_split_fun] },
  refl
end

lemma M.bisim_lemma {α : typevec n}
  {a₁ : (Mp P).A} {f₁ : (Mp P).B a₁ ⟹ α}
  {a' : P.A} {f' : (P.B a').drop ⟹ α} {f₁' : (P.B a').last → M P α}
  (e₁ : M.dest P ⟨a₁, f₁⟩ = ⟨a', split_fun f' f₁'⟩) :
  ∃ g₁' (e₁' : pfunctor.M.dest a₁ = ⟨a', g₁'⟩),
    f' = M.path_dest_left P e₁' f₁ ∧
    f₁' = λ (x : (last P).B a'),
      ⟨g₁' x, M.path_dest_right P e₁' f₁ x⟩ :=
begin
  generalize_hyp ef : @split_fun n _ (append1 α (M P α)) f' f₁' = ff at e₁,
  cases e₁' : pfunctor.M.dest a₁ with a₁' g₁',
  rw M.dest_eq_dest' _ e₁' at e₁,
  cases e₁, exact ⟨_, e₁', split_fun_inj ef⟩,
end

theorem M.bisim {α : typevec n} (R : P.M α → P.M α → Prop)
  (h : ∀ x y, R x y → ∃ a f f₁ f₂,
    M.dest P x = ⟨a, split_fun f f₁⟩ ∧
    M.dest P y = ⟨a, split_fun f f₂⟩ ∧
    ∀ i, R (f₁ i) (f₂ i))
  (x y) (r : R x y) : x = y :=
begin
  cases x with a₁ f₁,
  cases y with a₂ f₂,
  dsimp [Mp] at *,
  have : a₁ = a₂, {
    refine pfunctor.M.bisim
      (λ a₁ a₂, ∃ x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) _ _ _
      ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩,
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩,
    rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h'⟩,
    rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩,
    rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩,
    rw [e₁', e₂'],
    exact ⟨_, _, _, rfl, rfl, λ b, ⟨_, _, h' b, rfl, rfl⟩⟩ },
  subst this, congr' with i p,
  induction p with x a f h' i c x a f h' i c p IH generalizing f₁ f₂;
  try {
    rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h''⟩,
    rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩,
    rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', e₃, rfl⟩,
    cases h'.symm.trans e₁',
    cases h'.symm.trans e₂' },
  { exact (congr_fun (congr_fun e₃ i) c : _) },
  { exact IH _ _ (h'' _) }
end

theorem M.bisim₀ {α : typevec n} (R : P.M α → P.M α → Prop)
  (h₀ : equivalence R)
  (h : ∀ x y, R x y →
    (id ::: quot.mk R) <$$> M.dest _ x = (id ::: quot.mk R) <$$> M.dest _ y)
  (x y) (r : R x y) : x = y :=
begin
  apply M.bisim P R _ _ _ r, clear r x y,
  introv Hr, specialize h _ _ Hr, clear Hr,
  rcases M.dest P x with ⟨ax,fx⟩, rcases M.dest P y with ⟨ay,fy⟩,
  intro h, rw [map_eq,map_eq] at h, injection h with h₀ h₁, subst ay,
  simp at h₁, clear h,
  have Hdrop : drop_fun fx = drop_fun fy,
  { replace h₁ := congr_arg drop_fun h₁,
    simpa using h₁, },
  existsi [ax,drop_fun fx,last_fun fx,last_fun fy],
  rw [split_drop_fun_last_fun,Hdrop,split_drop_fun_last_fun],
  simp, intro i,
  replace h₁ := congr_fun (congr_fun h₁ fin2.fz) i,
  simp [(⊚),append_fun,split_fun] at h₁,
  replace h₁ := quot.exact _  h₁,
  rw h₀.eqv_gen_iff at h₁,
  exact h₁,
end

theorem M.bisim' {α : typevec n} (R : P.M α → P.M α → Prop)
  (h : ∀ x y, R x y →
    (id ::: quot.mk R) <$$> M.dest _ x = (id ::: quot.mk R) <$$> M.dest _ y)
  (x y) (r : R x y) : x = y :=
begin
  have := M.bisim₀ P (eqv_gen R) _ _,
  { solve_by_elim [eqv_gen.rel] },
  { apply eqv_gen.is_equivalence },
  { clear r x y, introv Hr,
    have : ∀ x y, R x y → eqv_gen R x y := @eqv_gen.rel _ R,
    induction Hr,
    { rw ← quot.factor_mk_eq R (eqv_gen R) this,
      rwa [append_fun_comp_id,← mvfunctor.map_map,← mvfunctor.map_map,h] },
    all_goals { cc } }
end

theorem M.dest_map {α β : typevec n} (g : α ⟹ β) (x : P.M α) :
  M.dest P (g <$$> x) = append_fun g (λ x, g <$$> x) <$$> M.dest P x :=
begin
  cases x with a f,
  rw map_eq,
  conv { to_rhs, rw [M.dest, M.dest', map_eq, append_fun_comp_split_fun] },
  reflexivity
end

theorem M.map_dest {α β : typevec n} (g : α ::: P.M α ⟹ β ::: P.M β) (x : P.M α)
  (h : ∀ x : P.M α, last_fun g x = (drop_fun g <$$> x : P.M β) ):
  g <$$> M.dest P x = M.dest P (drop_fun g <$$> x) :=
begin
  rw M.dest_map, congr,
  apply eq_of_drop_last_eq; simp,
  ext1, apply h
end

end mvpfunctor
