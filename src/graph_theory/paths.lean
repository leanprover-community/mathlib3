import graph_theory.basic

universes v u

variables {V : Type u} (G : directed_multigraph.{v} V)

namespace directed_multigraph

inductive path : V → V → Type (max v u)
| nil  : Π (h : V), path h h
| cons : Π {h s t : V} (e : G.edge h s) (l : path s t), path h t

notation a :: b := path.cons a b
notation `p[` l:(foldr `, ` (h t, path.cons h t) path.nil _ `]`) := l

abbreviation tour (x : V) : Type (max v u) := path G x x

end directed_multigraph

namespace multigraph

abbreviation path (H : multigraph.{v} V) := directed_multigraph.path H.to_directed_multigraph

end multigraph

open directed_multigraph

namespace path

variables {G}

def length : Π {s t}, path G s t → ℕ
| _ _ p[] := 0
| _ _ (_ :: l) := length l + 1

@[simp]
def concat : Π {x y z}, G.path x y → G.path y z → G.path x z
| _ _ _ p[]               q := q
| _ _ _ (e :: p') q := e :: concat p' q

lemma cons_as_concat {x y z} (e : G.edge x y) (l : G.path y z) :
  e :: l = concat p[e] l := rfl

@[simp]
lemma concat_nil : ∀ {x y} (p : G.path x y), concat p p[] = p
| _ _ p[] := rfl
| _ _ (_ :: _) := by rw [concat, concat_nil]

@[simp]
lemma concat_assoc : ∀ {w x y z} (p : G.path w x) (q : G.path x y) (r : G.path y z),
  concat p (concat q r) = concat (concat p q) r
| _ _ _ _ p[] _ _ := rfl
| _ _ _ _ (_ :: _) _ _ := by rw [concat, concat, concat, concat_assoc]

/-- A based version of path.rec_on. -/
def based_rec_on {t : V} {C : Π s (p : G.path s t), Sort*}
  {s} (p : G.path s t)
  (hn : C t p[])
  (hc : Π s h (e : G.edge s h) (l : G.path h t), C h l → C s (e::l))
  : C s p :=
by { induction p with _ s h t e l ih, { exact hn }, { exact hc s h e l (ih hn hc) }, }

@[simp]
def is_nil : Π {s t} (p : G.path s t), Prop
| _ _ (p[]) := true
| _ _ (_ :: _) := false
-- Maybe we should instead have an inductive type saying "this list is not nil", and pattern
-- match on the inhabitant on this type instead of this "false.elim" nonsense.

def mid : Π {s t} {p : G.path s t}, ¬ is_nil p → V
| _ _ (p[]) h := false.elim $ h trivial
| _ _ (@path.cons _ _ _ s' _ _ _) _ := s'

def head : Π {s t} {p : G.path s t} (h : ¬ is_nil p), G.edge s (mid h)
| _ _ (p[]) h := false.elim $ h trivial
| _ _ (e :: _) _ := e

def tail : Π {s t} {p : G.path s t} (h : ¬ is_nil p), G.path (mid h) t
| _ _ p[] h := false.elim $ h trivial
| _ _ (_ :: l) _ := l

lemma length_eq_length_tail_plus_one {s t} {p : G.path s t} (h : ¬ is_nil p) :
  length p = length (tail h) + 1 :=
by { cases p, { simpa using h }, { refl } }

def path_of_eq : Π {s t} (h : s = t), G.path s t
| _ _ rfl := p[]

variables {H : multigraph.{v} V}

inductive mem : Π {w x y z : V} (e : H.edge x y) (p : H.path w z), Prop
| head : ∀ {x y z} (e : H.edge x y) (p : H.path y z), mem e (e :: p)
| head_symm : ∀ {x y z} (e : H.edge x y) (p : H.path y z), mem (H.inv x y e) (e :: p)
| tail : ∀ {v w x y z} (e : H.edge v w) (e' : H.edge x y) (p : H.path w z) (m : mem e' p), mem e' (e :: p)

inductive is_trail : Π {x y} (p : H.path x y), Prop
| nil : ∀ (x), is_trail (path.nil x)
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
