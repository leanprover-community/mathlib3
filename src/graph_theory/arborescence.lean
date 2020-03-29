import graph_theory.paths
open path directed_multigraph

noncomputable theory
local attribute [instance] classical.prop_decidable

universes v u

variables {V : Type u} (G : directed_multigraph.{v+1} V) (root : V)

def subgraph := Π a b, set (G.edge a b)

class arborescence :=
(path : Π s, G.path s root)
(unique : ∀ s (p : G.path s root), p = path s)

variable {G}

def graph_of_subgraph (RR : subgraph G) : directed_multigraph V :=
⟨λ s t, RR s t⟩

def based_rec' : Π (s t : V) (p : G.path s t) (C : Π s' (p' : G.path s' t), Sort*)
  (hn : C t (path.nil _ _)) (hc : Π s' m (e : G.edge s' m) (l : G.path m t),
    C m l → C s' (e::l)), C s p
| _ _ (path.nil _ _) C hn _ := hn
| s t (@path.cons _ _ _ m _ e l) C hn hc := hc s m e l (based_rec' m t l C hn hc)

def based_rec_on {t : V} {C : Π s (p : G.path s t), Sort*} {s} (p : G.path s t)
  (hn : C t (path.nil _ _)) (hc : Π s m (e : G.edge s m) (l : G.path m t),
    C m l → C s (e::l)) : C s p :=
based_rec' s t p C hn hc

def is_nil : Π {s t} (p : G.path s t), Prop
| _ _ (path.nil _ _) := true
| _ _ (_ :: _) := false

lemma eq_of_is_nil : Π {s t} (p : G.path s t), is_nil p → s = t
| _ _ (path.nil _ _) _ := rfl
| _ _ (_ :: _) h := false.elim h

def mid : Π {s t} (p : G.path s t), ¬ is_nil p → V
| _ _ (path.nil _ _) h := false.elim $ h trivial
| _ _ (@path.cons _ _ _ s' _ _ _) _ := s'

def head : Π {s t} (p : G.path s t) (h : ¬ is_nil p), G.edge s (mid _ h)
| _ _ (path.nil _ _) h := false.elim $ h trivial
| _ _ (e :: _) _ := e

def tail : Π {s t} (p : G.path s t) (h : ¬ is_nil p), G.path (mid _ h) t
| _ _ (path.nil _ _) h := false.elim $ h trivial
| _ _ (_ :: l) _ := l

lemma length_eq_length_tail_plus_one : Π {s t} (p : G.path s t) (h : ¬ is_nil p),
  length _ p = length _ (tail _ h) + 1
| _ _ (path.nil _ _) h := false.elim $ h trivial
| _ _ (_ :: _) _ := rfl

def path_of_eq : Π {s t} (h : s = t), G.path s t
| _ _ rfl := path.nil _ _

variable (RR : ∀ s, nonempty (G.path s root))
include RR

def shortest_path (s : V) : G.path s root :=
well_founded.min (measure_wf $ λ p : G.path s root, length _ p) set.univ
  (@set.univ_nonempty _ $ RR s)

lemma shortest_path_spec (s : V) (p : G.path s root) :
  length _ (shortest_path _ RR s) ≤ length _ p :=
begin
  have : ¬ (length _ p < length _ (shortest_path _ RR s)),
  exact well_founded.not_lt_min (measure_wf _) set.univ _ trivial,
  simpa using this,
end

lemma shortest_nnil (s) (h : s ≠ root) : ¬ is_nil (shortest_path _ RR s) :=
mt (eq_of_is_nil $ shortest_path _ RR s) h

inductive geodesic_subgraph : Π (s t : V) (e : G.edge s t), Prop
| intro (s : V) (h : s ≠ root) : geodesic_subgraph s
  (mid _ (shortest_nnil _ RR s h)) (head _ (shortest_nnil _ RR s h))

def geodesic_graph : directed_multigraph V :=
graph_of_subgraph $ geodesic_subgraph _ RR

abbreviation height (s : V) : ℕ := length _ $ shortest_path _ RR s

lemma height_le {s} (h : s ≠ root) :
  height _ RR (mid _ $ shortest_nnil _ RR s h) < height _ RR s := begin
  have : height _ RR _ ≤ length _ (tail _ $ shortest_nnil _ RR s h),
  { apply shortest_path_spec },
  apply lt_of_le_of_lt this,
  have : height _ RR s = length _ (tail _ $ shortest_nnil _ RR s h) + 1,
  { apply length_eq_length_tail_plus_one },
  rw this,
  simp,
end

noncomputable def geodesic_path : Π s, path (geodesic_graph _ RR) s root
| s := dite (s = root) (λ h, path_of_eq h)
       (λ h, have _ := height_le _ RR h,
            ⟨_, geodesic_subgraph.intro RR s h⟩ :: geodesic_path _)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (height _ RR)⟩],
  dec_tac := `[assumption]}

lemma geodesic_path_def : Π s, geodesic_path _ RR s = dite (s = root) (λ h, path_of_eq h)
       (λ h, ⟨_, geodesic_subgraph.intro RR s h⟩ :: geodesic_path _ RR _) :=
well_founded.fix_eq _ _

lemma geodesic_path_unique (s) (p : path (geodesic_graph _ RR) s root) :
  p = geodesic_path _ RR s := @based_rec_on V (geodesic_graph _ RR) root
  (λ s p, p = geodesic_path _ RR s) s p (by { rw [geodesic_path_def, dif_pos rfl], simpa })
begin
  intros s m e l h,
  cases e with e p,
  cases p with _ n,
  rw geodesic_path_def,
  rw dif_neg n,
  simpa using h,
end

instance geodesic_arboresence : arborescence (geodesic_graph root RR) root :=
{ path := geodesic_path root RR,
  unique := geodesic_path_unique root RR}
