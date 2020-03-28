import graph_theory.hedetniemi

universes v u

variables {V : Type u} (G : directed_multigraph.{v} V)

-- instance : has_coe (multigraph.{v} V) (directed_multigraph.{v} V) := ⟨multigraph.to_directed_multigraph⟩
namespace directed_multigraph

inductive path : V → V → Type (max v u)
| nil  : Π (h : V), path h h
| cons : Π {h s t : V} (e : G.edge h s) (l : path s t), path h t

abbreviation tour (x : V) : Type (max v u) := path G x x

end directed_multigraph

namespace multigraph

abbreviation path (H : multigraph.{v} V) := directed_multigraph.path H.to_directed_multigraph

end multigraph

open directed_multigraph

namespace path

def length : Π {s t}, path G s t → ℕ
| _ _ (path.nil _ _) := 0
| _ _ (@path.cons _ _ _ _ _ e l) := length l + 1

notation a :: b := path.cons a b
notation `p[` l:(foldr `, ` (h t, path.cons h t) path.nil _ _ `]`) := l

variables {G}

-- The pattern matching trick used here was explained by Jeremy Avigad
-- at https://groups.google.com/d/msg/lean-user/JqaI12tdk3g/F9MZDxkFDAAJ
@[simp]
def concat : Π {x y z}, G.path x y → G.path y z → G.path x z
| ._ ._ _ (path.nil _ _)               q := q
| ._ ._ _ (@path.cons ._ _ _ _ _ e p') q := path.cons e (concat p' q)

@[simp]
lemma concat_nil : ∀ {x y} (p : G.path x y), concat p (path.nil G y) = p
| x ._ (path.nil G y) := rfl
| x y (e :: p') := begin dsimp, congr, apply concat_nil, end

@[simp]
lemma concat_assoc : ∀ {w x y z} (p : G.path w x) (q : G.path x y) (r : G.path y z),
  concat p (concat q r) = concat (concat p q) r
| ._ ._ y z (path.nil G x) q r := rfl
| w x y z (e :: p) q r := begin dsimp, congr' 1, apply concat_assoc, end


variables {H : multigraph.{v} V}

inductive mem : Π {w x y z : V} (e : H.edge x y) (p : H.path w z), Prop
| head : ∀ {x y z} (e : H.edge x y) (p : H.path y z), mem e (e :: p)
| head_symm : ∀ {x y z} (e : H.edge x y) (p : H.path y z), mem (H.inv x y e) (e :: p)
| tail : ∀ {v w x y z} (e : H.edge v w) (e' : H.edge x y) (p : H.path w z) (m : mem e' p), mem e' (e :: p)

inductive is_trail : Π {x y} (p : H.path x y), Prop
| nil : ∀ (x), is_trail (path.nil H.to_directed_multigraph x) -- fixme
| cons : ∀ {x y z} (e : H.edge x y) (p : H.path y z) (h : ¬ mem e p), is_trail (e :: p)

def is_Eulerian {x y} (p : H.path x y) : Prop :=
is_trail p ∧ ∀ {x' y'} (e : H.edge x' y'), mem e p

end path

open path

variables (H : multigraph.{v} V)

def is_Eulerian : Prop :=
∃ {x : V} (p : tour H.to_directed_multigraph x), is_Eulerian p

/--
I thought about defining an inductive type
```
inductive Konigsberg
| Kneiphof
| Aldstadt
| Vorstadt
| Lomse
```
but it was too horrible to contemplate.
-/
def KonigsbergBridges : multigraph (fin 4) :=
multigraph_of_edges [(0,1), (0,2), (0,3), (1,2), (1,2), (2,3), (2,3)]

def KonigsbergBridgesProblem : Prop :=
¬ is_Eulerian KonigsbergBridges

-- inductive path_of_paths (G : multigraph.{v} V) : V → V → Type (max v u)
-- | nil  : Π (h : V), path_of_paths h h
-- | cons : Π {h s t} (e : G.path h s) (l : path_of_paths s t), path_of_paths h t

-- namespace path_of_paths

-- notation a :: b := path_of_paths.cons a b
-- notation `pp[` l:(foldr `, ` (h t, path_of_paths.cons h t) path_of_paths.nil _ `]`) := l

-- def concatenate_path_of_paths : Π {x y}, G.path_of_paths x y → G.path x y
-- | ._ ._ (path_of_paths.nil G X) := path.nil G X
-- | ._ ._ (@path_of_paths.cons ._ _ _ _ _ e p') :=
--   concat e (concatenate_path_of_paths p')

-- end path_of_paths
