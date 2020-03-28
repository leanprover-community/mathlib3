import graph_theory.hedetniemi

universes v u v₁ u₁

variables {V : Type u} (G : multigraph.{v} V)

namespace multigraph

inductive path : V → V → Type (max u v)
| nil (a : V) : path a a
| app {a b c : V} (p : path a b) (e : G.edge b c) : path a c

end multigraph
open multigraph

namespace path
variable {G}

def of {a b : V} : G.edge a b → G.path a b := path.app (path.nil _ _)

def comp : Π {a b c : V}, G.path a b → G.path b c → G.path a c
| _ _ _ p (path.nil _ _) := p
| _ _ _ p (path.app q e) := path.app (comp p q) e

lemma comp_app {a b c d : V} {p : G.path a b} {q : G.path b c} {e : G.edge c d} :
  comp p (path.app q e) = path.app (comp p q) e := rfl

@[simp]
lemma comp_nil {a b : V} {p : G.path a b} : comp p (path.nil _ _) = p := rfl

@[simp]
lemma nil_comp : ∀ {a b : V} {p : G.path a b}, comp (path.nil _ _) p = p
| _ _ (path.nil _ _) := rfl
| _ _ (path.app p e) := by rw [comp_app, nil_comp]

@[simp]
lemma comp_assoc : ∀ {a b c d : V} {p : G.path a b} {q : G.path b c} {r : G.path c d},
  comp (comp p q) r = comp p (comp q r)
| _ _ _ _ _ _ (path.nil _ _) := rfl
| _ _ _ _ _ _ (path.app _ _) := by {rw [comp_app, comp_app, comp_app, comp_assoc]}

lemma app_eq_comp_of {a b c} (p : G.path a b) (e : G.edge b c) :
  path.app p e = comp p (of e) := rfl

lemma comp_induction {C : Π {a b} (p : G.path a b), Sort*}
  (h_nil : ∀ a, C (@path.nil _ _ a))
  (h_of : ∀ {a b} (e : G.edge a b), C (of e))
  (h_comp : ∀ {a b c} {p : G.path a b} {q : G.path b c}, C p → C q → C (comp p q)) :
  ∀ {a b} (p : G.path a b), C p
| _ _ (path.nil _ _) := h_nil _
| _ _ (path.app p e) := by {rw app_eq_comp_of, exact h_comp (comp_induction p) (h_of e)}

end path
open path

namespace path

variable {G}

def length : Π {a b}, G.path a b → ℕ
| _ _ (path.nil _ _) := 0
| _ _ (path.app p _) := length p + 1

lemma length_nil {a : V} : length (path.nil G a) = 0 :=
rfl

lemma length_comp {a b c} (p : G.path a b) (q : G.path b c) :
  length (comp p q) = length p + length q :=
begin
  induction q,
  { refl, },
  { dsimp [comp, length], erw q_ih, simp, } -- This `erw` is yucky, let's fix.
end

lemma length_of {a b} (e : G.edge a b) : length (of e) = 1 := rfl

lemma length_app {a b c} (p : G.path a b) (e : G.edge b c) :
  length (path.app p e) = length p + 1 := rfl

end path

-- TODO: define "reversible" multigraphs and the free groupoid
