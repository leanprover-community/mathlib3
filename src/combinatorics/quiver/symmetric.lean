import combinatorics.quiver.basic
import combinatorics.quiver.path


universes v u

namespace quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_nonempty_instance]
def symmetrify (V) : Type u := V

instance symmetrify_quiver (V : Type u) [quiver V] : quiver (symmetrify V) :=
⟨λ a b : V, (a ⟶ b) ⊕ (b ⟶ a)⟩

variables (V : Type u) [quiver.{v+1} V]

/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class has_reverse :=
(reverse' : Π {a b : V}, (a ⟶ b) → (b ⟶ a))

/-- Reverse the direction of an arrow. -/
def reverse {V} [quiver.{v+1} V] [has_reverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  has_reverse.reverse'

/-- A quiver `has_involutive_reverse` if reversing twice is the identity.`-/
class has_involutive_reverse extends has_reverse V :=
(inv' : Π {a b : V} (f : a ⟶ b), reverse (reverse f) = f)

@[simp] lemma reverse_reverse {V} [quiver.{v+1} V] [h : has_involutive_reverse V]
  {a b : V} (f : a ⟶ b) : reverse (reverse f) = f := by apply h.inv'

variables {V}

instance : has_reverse (symmetrify V) := ⟨λ a b e, e.swap⟩
instance : has_involutive_reverse (symmetrify V) :=
{ to_has_reverse := ⟨λ a b e, e.swap⟩,
  inv' := λ a b e, congr_fun sum.swap_swap_eq e }

/-- Reverse the direction of a path. -/
@[simp] def path.reverse [has_reverse V] {a : V} : Π {b}, path a b → path b a
| a path.nil := path.nil
| b (path.cons p e) := (reverse e).to_path.comp p.reverse

@[simp] lemma path.reverse_to_path [has_reverse V] {a b : V} (f : a ⟶ b) :
  f.to_path.reverse = (reverse f).to_path := rfl

@[simp] lemma path.reverse_comp [has_reverse V] {a b c : V} (p : path a b) (q : path b c) :
  (p.comp q).reverse = q.reverse.comp p.reverse := by
{ induction q, { simp, }, { simp [q_ih], }, }

@[simp] lemma path.reverse_reverse [h : has_involutive_reverse V] {a b : V} (p : path a b) :
  p.reverse.reverse = p := by
{ induction p,
  { simp, },
  { simp only [path.reverse, path.reverse_comp, path.reverse_to_path, reverse_reverse, p_ih],
    refl, }, }

namespace symmetrify

/-- The inclusion of a quiver in its symmetrification -/
def of : prefunctor V (symmetrify V) :=
{ obj := id,
  map := λ X Y f, sum.inl f }

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def lift {V' : Type*} [quiver V'] [has_reverse V'] (φ : prefunctor V V') :
  prefunctor (symmetrify V) V' :=
{ obj := φ.obj,
  map := λ X Y f, sum.rec (λ fwd, φ.map fwd) (λ bwd, reverse (φ.map bwd)) f }

lemma lift_spec  (V' : Type*) [quiver V'] [has_reverse V'] (φ : prefunctor V V') :
  of.comp (lift φ) = φ :=
begin
  fapply prefunctor.ext,
  { rintro X, refl, },
  { rintros X Y f, refl, },
end

lemma lift_reverse  (V' : Type*) [quiver V'] [h : has_involutive_reverse V']
  (φ : prefunctor V V')
  {X Y : symmetrify V} (f : X ⟶ Y) :
  (lift φ).map (quiver.reverse f) = quiver.reverse ((lift φ).map f) :=
begin
  dsimp [lift], cases f,
  { simp only, refl, },
  { simp only, rw h.inv', refl, }
end

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
lemma lift_unique (V' : Type*) [quiver V'] [has_reverse V']
  (φ : prefunctor V V')
  (Φ : prefunctor (symmetrify V) V')
  (hΦ : of.comp Φ = φ)
  (hΦinv : ∀ {X Y : V} (f : X ⟶ Y), Φ.map (reverse f) = reverse (Φ.map f)) :
  Φ = lift φ :=
begin
  subst_vars,
  fapply prefunctor.ext,
  { rintro X, refl, },
  { rintros X Y f,
    cases f,
    { refl, },
    { dsimp [lift,of],
      convert hΦinv (sum.inl f), }, },
end

end symmetrify

namespace push

variables {W : Type*} (σ : V → W)


instance [has_reverse V] : has_reverse (quiver.push σ) :=
{ reverse' := λ a b F, by { cases F, constructor, apply reverse, exact F_f, } }

instance [h : quiver.has_involutive_reverse V] : quiver.has_involutive_reverse (push σ) :=
{ reverse' := λ a b F, by { cases F, constructor, apply reverse, exact F_f, },
  inv' :=  λ a b F, by
  { cases F, dsimp [reverse], congr, apply h.inv', } }

@[simp] lemma of_reverse [h : has_involutive_reverse V]  (X Y : V) (f : X ⟶ Y):
  (reverse $ ((of σ)).map f) = ((of σ)).map (reverse f) := rfl

end push


namespace path

def is_reducible {V} [quiver V] [has_involutive_reverse V] {X Y : V} (r : path X Y) :=
  ( ∃ (Z W : V) (p : path X Z) (f : Z ⟶ W) (q : path Z Y),
        r = ((p.comp (f.to_path.cons $ quiver.reverse f)).comp q) )

end path

/--
`V` is a forest if there is at most one path between any two of its vertices, in the
symmetrification of `V`
-/
def is_forest (V) [quiver V] [has_involutive_reverse V] :=
  ∀ (X Y : V), subsingleton { p : path X Y | ¬ p.is_reducible }

end quiver
