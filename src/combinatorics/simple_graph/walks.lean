import combinatorics.simple_graph.basic
import combinatorics.simple_graph.hom
import combinatorics.simple_graph.subgraph
open simple_graph

/-!
# Walks in a simple graph

We define two ways of dealing with walks in a simple graph.  The
first, `walk`, is by using an inductive type that is essentially lists
of adjacent vertices.  The second, `walk'`, is graph homomorphisms
from path graphs.  We prove these are equivalent in
`walk_equiv_walk'`, and there are supporting simp lemmas that show these
are structurally equivalent.

As a convenience, we also supply `===` between different paths, which
is a heterogeneous equality that equates indices (hence `heqi`).  This
can be useful in case the endpoints of a walk after some
transformation are not definitionally equal to what is expected.

-/

namespace simple_graph
universes u v

/--
Walks as a list of adjacent vertices.  A convenient representation because, for example, concatenation yields
a walk with start and end vertices that are definitionally what they are supposed to be.
`walk.nil` is a length-zero walk at a vertex, and `walk.cons` adds an edge to the beginning.
-/
inductive walk {G : simple_graph.{u}} : V G → V G → Type u
| nil {v : V G} : walk v v
| cons {u v w : V G} (h : u ~g v) (p : walk v w) : walk u w

attribute [refl] walk.nil

namespace walk
variables {G : simple_graph}

def heqi.t := Σ (u v : V G), walk u v
def heqi {u v u' v' : V G} (p : walk u v) (p' : walk u' v') :=
(⟨u, v, p⟩ : heqi.t) = ⟨u', v', p'⟩

infix ` === `:50  := heqi

@[refl]
lemma heqi.refl {u v : V G} {p : walk u v} : p === p := eq.refl _

@[symm]
lemma heqi.symm {u v u' v' : V G}
  {p : walk u v} {p' : walk u' v'} :
  p === p' → p' === p := eq.symm

@[trans]
lemma heqi.trans {u v u' v' u'' v'' : V G}
  {p : walk u v} {p' : walk u' v'} {p'' : walk u'' v''}:
  p === p' → p' === p'' → p === p'' := eq.trans

def heqi_of_eq {u v : V G} (p p' : walk u v) (h : p = p') : p === p' :=
by { subst p }

/--
Put `heqi` into the form Reid suggested.
-/
lemma heqi.subst {u v u' v' : V G} (p : walk u v) (p' : walk u' v')
  {ι : Sort*} (C : Π ⦃u v : V G⦄, walk u v → ι)
  (h : p === p') : C p = C p' :=
by { cases h, refl }

lemma heqi.unsubst {u v u' v' : V G} (p : walk u v) (p' : walk u' v')
  (h : Π (C : Π ⦃u v : V G⦄, walk u v → Prop), C p = C p') :
  p === p' :=
by { have h' := h (λ u v p, p === p'), dsimp at h', rw h' }

def eq_of_heqi {u v : V G} (p p' : walk u v) (h : p === p') : p = p' :=
by { cases h, refl }

lemma heqi.head {u v u' v' : V G} (p : walk u v) (p' : walk u' v')
  (h : p === p') : u = u' :=
heqi.subst p p' (λ u v p, u) h

lemma heqi.tail {u v u' v' : V G} (p : walk u v) (p' : walk u' v')
  (h : p === p') : v = v' :=
heqi.subst p p' (λ u v p, v) h

private def heqi.cons.second_vert : Π {u v : V G}, walk u v → V G
| u v nil := v
| u v (@cons _ _ w _ _ _) := w

lemma heqi.cons_vert {u v w u' v' w' : V G}
  (h : u ~g v) (p : walk v w)
  (h' : u' ~g v') (p' : walk v' w')
  (eq : cons h p === cons h' p') : v = v' :=
begin
  have key := heqi.subst (cons h p) (cons h' p') (λ u v p, heqi.cons.second_vert p) eq,
  exact key,
end

private def heqi.cons.tail : Π {u v : V G}, walk u v → Σ (w v : V G), walk w v
| u v nil := ⟨u, v, nil⟩
| u v (@cons _ _ w _ h p) := ⟨w, v, p⟩

lemma heqi.cons {u v w u' v' w' : V G}
  (h : u ~g v) (p : walk v w)
  (h' : u' ~g v') (p' : walk v' w')
  (eq : cons h p === cons h' p') : p === p' :=
begin
  have key := heqi.subst (cons h p) (cons h' p') (λ u v p, @heqi.cons.tail _ u v p) eq,
  exact key,
end

lemma heqi.cons_iff {u v w u' v' w' : V G}
  (h : u ~g v) (p : walk v w)
  (h' : u' ~g v') (p' : walk v' w') :
  cons h p === cons h' p' ↔ u = u' ∧ v = v' ∧ p === p' :=
begin
  split,
  { intro heq, exact ⟨heqi.head (cons h p) (cons h' p') heq, heqi.cons_vert h p h' p' heq, heqi.cons h p h' p' heq⟩, },
  { rintros ⟨rfl, rfl, heq⟩, cases heq, refl, },
end

/--
Map from an edge between vertices to a walk between them.
-/
@[reducible]
def of_adj {u v : V G} (h : u ~g v) : walk u v := cons h nil

@[simp]
lemma of_adj_eq_cons {u v w : V G} (h : u ~g v) (p : walk v w)  :
  (of_adj h) = cons h nil := rfl

protected
def reverse_aux : Π {u v w : V G}, walk u v → walk u w → walk v w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := reverse_aux p (cons (G.symm h) q)

@[symm]
def reverse {u v : V G} (p : walk u v) : walk v u := walk.reverse_aux p nil

@[simp]
lemma nil_reverse {u : V G} : (nil : walk u u).reverse = nil := rfl

@[simp]
lemma of_adj_reverse {u v : V G} (h : u ~g v): (of_adj h).reverse = of_adj (G.symm h) := rfl

@[trans]
def concat : Π {u v w : V G}, walk u v → walk v w → walk u w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := cons h (concat p q)

@[simp]
lemma cons_concat {u v w x : V G} (h : u ~g v) (p : walk v w) (q : walk w x) :
  (cons h p).concat q = cons h (p.concat q) := rfl

@[simp]
lemma concat_nil {u v : V G} (p : walk u v) :
  p.concat nil = p :=
by { induction p, refl, dsimp [concat], rw p_ih, }

@[simp]
lemma nil_concat {u v : V G} (p : walk u v) :
  nil.concat p = p := rfl

lemma concat_assoc {u v w x : V G} (p : walk u v) (q : walk v w) (r : walk w x) :
  p.concat (q.concat r) = (p.concat q).concat r :=
by { induction p, refl, dsimp [concat], rw p_ih, }

/--
This lemma has a `cons` as the second argument to avoid rewriting when it's `nil`.
-/
@[simp]
protected
lemma reverse_aux_extract {u v w x : V G} (p : walk u v) (h : u ~g w) (q : walk w x) :
  walk.reverse_aux p (cons h q) = (walk.reverse_aux p nil).concat (cons h q) :=
begin
  induction p generalizing q h w x,
  { refl },
  { dsimp [walk.reverse_aux],
    rw p_ih, conv_rhs { rw p_ih },
    rw ←concat_assoc, simp, }
end

@[simp]
protected
lemma concat_reverse_aux {u v w : V G} (p : walk v u) (q : walk v w) :
  walk.reverse_aux p q = p.reverse.concat q :=
by { cases q, rw concat_nil, refl, rw walk.reverse_aux_extract, refl }

@[simp]
lemma concat_reverse {u v w : V G} (p : walk u v) (q : walk v w) :
  (p.concat q).reverse = q.reverse.concat p.reverse :=
begin
  induction p generalizing q w,
  { simp },
  { rw cons_concat, dsimp [reverse, walk.reverse_aux],
    simp only [walk.reverse_aux_extract, walk.concat_reverse_aux, concat_nil],
    rw [p_ih, concat_assoc], }
end

@[simp]
lemma reverse_invol {u v : V G} (p : walk u v) : p.reverse.reverse = p :=
begin
  induction p,
  { refl },
  { dsimp [reverse, walk.reverse_aux],
    simp [p_ih], }
end

/--
The length of a walk is the number of edges along it.
-/
def length : Π {u v : V G}, walk u v → ℕ
| _ _ nil := 0
| _ _ (cons _ q) := q.length.succ

lemma heqi_length {u v u' v' : V G} {p : walk u v} {p' : walk u' v'} (h : p === p') :
  p.length = p'.length :=
walk.heqi.subst p p' (λ u v p, p.length) h

@[simp]
lemma nil_length {u : V G} : (nil : walk u u).length = 0 := rfl

@[simp]
lemma cons_length {u v w : V G} (h : u ~g v) (p : walk v w) : (cons h p).length = p.length + 1 := rfl

@[simp]
lemma concat_length {u v w : V G} (p : walk u v) (q : walk v w) :
  (p.concat q).length = p.length + q.length :=
begin
  induction p, simp,
  dsimp [concat, length], rw p_ih, repeat { rw nat.succ_eq_add_one }, ring,
end

protected
lemma reverse_aux_length {u v w : V G} (p : walk u v) (q : walk u w) :
  (walk.reverse_aux p q).length = p.length + q.length :=
begin
  induction p,
  { dunfold walk.reverse_aux, simp, },
  { dunfold reverse_aux, rw p_ih, simp only [cons_length], ring, },
end

@[simp]
lemma reverse_length {u v : V G} (p : walk u v) : p.reverse.length = p.length :=
by { convert walk.reverse_aux_length p nil }

def get_vert : Π {u v : V G} (i : ℕ) (p : walk u v), V G
| u v 0 _ := u
| _ v (i+1) (cons _ q) := get_vert i q
| _ v (i+1) nil := v

lemma heqi_get_vert {u v u' v' : V G} {p : walk u v} {p' : walk u' v'} (eq : p === p') (i : ℕ) :
  p.get_vert i = p'.get_vert i :=
heqi.subst p p' (λ u v p, get_vert i p) eq

@[simp]
lemma get_vert_0 {u v : V G} (p : walk u v) : p.get_vert 0 = u := rfl

@[simp]
lemma get_vert_n {u v : V G} (p : walk u v) : p.get_vert p.length = v :=
by { induction p, refl, exact p_ih }

@[simp]
lemma get_vert_nil {u : V G} (i : ℕ) : (@nil _ u).get_vert i = u :=
by { cases i, simp, dsimp [get_vert], refl, }

@[simp]
lemma get_vert_cons {u v w : V G} (h : u ~g v) (p : walk v w) (i : ℕ) : (cons h p).get_vert (i + 1) = p.get_vert i := rfl

lemma walk_ext_aux {u v : V G} (n : ℕ) (p : walk u v) (p' : walk u v)
  (h₁ : p.length = n) (h₁' : p'.length = n)
  (h₂ : ∀ i, i < n + 1 → p.get_vert i = p'.get_vert i) :
  p = p' :=
begin
  induction n generalizing u v p p',
  { cases p, cases p', refl, exfalso, simpa using h₁', exfalso, simpa using h₁, },
  cases p, cases p', refl,
  rw ←h₁ at h₁', exfalso, simpa using h₁',
  cases p',
  rw ←h₁ at h₁', exfalso, simpa using h₁',
  have key₁ := h₂ 1 (by { change 1 < n_n + 1 + 1, linarith }),
  dsimp [get_vert] at key₁,
  subst p'_v,
  rw cons_length at h₁ h₁',
  congr, apply n_ih p_p p'_p (nat.succ.inj h₁) (nat.succ.inj h₁'),
  intros i h,
  exact h₂ (i + 1) (by { change _ < n_n + 1 + 1, linarith }),
end

lemma walk_ext {u v : V G} (p : walk u v) (p' : walk u v)
  (h₁ : p.length = p'.length)
  (h₂ : ∀ i, i < p.length + 1 → p.get_vert i = p'.get_vert i) :
  p = p' :=
walk_ext_aux p.length p p' rfl h₁.symm h₂

/--
Heterogenous equality version of `walk_ext`.
-/
lemma walk_ext_heqi {u v u' v' : V G} (p : walk u v) (p' : walk u' v')
  (h₁ : p.length = p'.length)
  (h₂ : ∀ i, i < p.length + 1 → p.get_vert i = p'.get_vert i) :
  p === p' :=
begin
  have h0 := h₂ 0 (by linarith),
  repeat { rw get_vert_0 at h0 },
  have hn := h₂ p.length (by linarith),
  conv_rhs at hn { rw h₁ },
  repeat { rw get_vert_n at hn },
  subst u', subst v',
  rw walk_ext p p' h₁ h₂,
end

def walk_ext_heqi_iff {u v u' v' : V G} (p : walk u v) (p' : walk u' v') :
  (p.length = p'.length ∧ ∀ i, i < p.length + 1 → p.get_vert i = p'.get_vert i) ↔
  p === p' :=
begin
  split,
  { intros h, exact walk_ext_heqi p p' h.1 h.2, },
  { intro h, split, exact heqi_length h,
    intros i hi, exact heqi_get_vert h i, }
end

lemma get_vert_rel {u v : V G} (p : walk u v) (i : ℕ) (h : i < p.length) :
  p.get_vert i ~g p.get_vert (i + 1) :=
begin
  induction i generalizing u v p,
  { cases p, exfalso, change 0 < 0 at h, linarith,
    cases p_p, exact p_h,
    exact p_h, },
  cases p,
  exfalso, change _ < 0 at h, linarith,
  cases p_p, exfalso, change _ + 1 < 1 at h, linarith,
  change (cons p_p_h p_p_p).get_vert i_n ~g (cons p_p_h p_p_p).get_vert i_n.succ,
  apply i_ih,
  change i_n + 1 < p_p_p.length.succ + 1 at h,
  dsimp [length], linarith,
end

end walk

/--
Walks as homomorphisms of path graphs.
-/
structure walk' {G : simple_graph.{u}} (u v : V G) : Type u:=
(length : ℕ)
(f : ↟(path_graph length) →g G)
(f0 : f (⟨0, by omega⟩ : fin (length+1)) = u)
(fn : f (⟨length, by omega⟩ : fin (length+1)) = v)

namespace walk'
variables {G : simple_graph}

def nil {v : V G} : walk' v v :=
{ length := 0,
  f := { to_fun := λ _, v,
         map_rel' := begin
           rintros ⟨i, hi⟩ ⟨j, hj⟩, have hi' : i = 0, linarith, have hj' : j = 0, linarith,
           subst i, subst j, simp, end },
  f0 := rfl,
  fn := rfl }

def cons {u v w : V G} (h : u ~g v) (p : walk' v w) : walk' u w :=
{ length := p.length + 1,
  f := {
    to_fun := λ i, match i with
            | ⟨0, h⟩ := u
            | ⟨i'+1, h⟩ := p.f (⟨i', by linarith⟩ : fin (p.length + 1))
            end,
    map_rel' := begin
      rintros ⟨i,hi⟩ ⟨j,hj⟩,
      wlog : i ≤ j, rw path_graph_adj, dsimp,
      cases i, cases j, simp,
      cases j, simp, cases p, subst v, subst w, exact h,
      dsimp, intro h, exfalso, cases h, change j + 2 = 1 at h_1, linarith, linarith,
      intro h,
        cases h, subst j, dsimp [walk'.cons._match_1], apply p.f.map_rel', rw path_graph_adj, dsimp, left, omega,
        cases j, exfalso, change i+1 ≤ 0 at case, linarith,
        dsimp [walk'.cons._match_1], apply p.f.map_rel', rw path_graph_adj, dsimp, right, omega,
      specialize this hj hi (simple_graph.symm _ a), exact simple_graph.symm _ this,
    end },
  f0 := rfl,
  fn := begin
    dsimp [walk'.cons._match_1], exact p.fn,
  end }


def get_vert {u v : V G} (i : ℕ) (p : walk' u v) : V G :=
if h : i < p.length + 1 then p.f ⟨i, h⟩ else v

@[simp]
lemma get_vert_0 {u v : V G} (p : walk' u v) : p.get_vert 0 = u :=
by { dsimp [get_vert], simp, exact p.f0 }

@[simp]
lemma get_vert_n {u v : V G} (p : walk' u v) : p.get_vert p.length = v :=
by { dsimp [get_vert], simp, exact p.fn, }

@[simp]
lemma get_vert_cons {u v w : V G} (h : u ~g v) (p : walk' v w) (i : ℕ) : (cons h p).get_vert (i + 1) = p.get_vert i :=
begin
  dsimp [get_vert, cons], cases p, subst v, subst w, dsimp,
  have k : i + 1 < p_length + 1 + 1 ↔ i < p_length + 1, omega, simp [k],
end

@[ext]
def ext {u v : V G} (p : walk' u v) (p' : walk' u v)
  (hn : p.length = p'.length)
  (h₂ : ∀ i, i < p.length + 1 → p.get_vert i = p'.get_vert i) :
  p = p' :=
begin
  cases p, cases p', dsimp [get_vert] at h₂, dsimp at hn, subst p'_length,
  subst u, subst v, congr, ext w, cases w with i hi,
  specialize h₂ i hi, simpa [hi] using h₂,
end
.

@[simp]
lemma nil_length {u : V G} : (@nil _ u).length = 0 := rfl

lemma length_0 {u v : V G} (p : walk' u v) (h : p.length = 0) : u = v :=
by { cases p, dsimp at h, subst p_length, subst u, subst v }

@[simp]
lemma cons_length {u v w : V G} (h : u ~g v) (p : walk' v w) : (cons h p).length = p.length + 1 := rfl

@[simp]
lemma nil_get_vert {u : V G} (i : ℕ) : (@nil _ u).get_vert i = u :=
by { dunfold get_vert, split_ifs, refl, refl }

@[simp]
lemma cons_get_vert_0 {u v w : V G} (h : u ~g v) (p : walk' v w) : (cons h p).get_vert 0 = u :=
begin dsimp [get_vert], simp, refl, end

@[simp]
lemma cons_get_vert_succ {u v w : V G} (h : u ~g v) (p : walk' v w) (i : ℕ) : (cons h p).get_vert (i + 1) = p.get_vert i :=
begin dsimp [get_vert], simp, refl, end

lemma walk_adj {u v : V G} (p : walk' u v) (i : ℕ) (h : i < p.length) : p.get_vert i ~g p.get_vert (i+1) :=
begin
  have h' : i < p.length + 1, linarith,
  dsimp [get_vert], simp [h, h'],
  apply p.f.map_rel', rw path_graph_adj, left, simp,
end

lemma walk_adj₀ {u v : V G} (p : walk' u v) (h : 0 < p.length) : u ~g p.get_vert 1 :=
by { convert walk_adj p 0 h, simp, }

def path_map_drop' {n : ℕ} (f : ↟(path_graph (n+1)) →g G) : ↟(path_graph n) →g G :=
{ to_fun := λ n, f ⟨n.val + 1, by { cases n, linarith }⟩,
  map_rel' := begin
    rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
    apply f.map_rel',
    rw path_graph_adj at h ⊢, dsimp at h ⊢,
    cases h; subst h, left, refl, right, refl,
  end }
.

--def path_map_drop {n : ℕ} (f : ↟(path_graph n) →g G) : ↟(path_graph (n-1)) →g G :=
--{ to_fun := λ n, f
--}.

def tail {u v : V G} (p : walk' u v) : walk' (p.get_vert 1) v :=
{ length := p.length - 1,
  f := { to_fun := λ n, p.get_vert (n.val + 1),
         map_rel' := begin
           rintros ⟨i, hi⟩ ⟨j, hj⟩ h,
           rw path_graph_adj at h, dsimp at h,
           cases h,
           subst j, dsimp, apply walk_adj, omega,
           subst i, dsimp, rw adj_symm, apply walk_adj, omega,
         end },
  f0 := by refl,
  fn := begin
    simp [get_vert], split_ifs, have h' : 0 < p.length, omega, --have key : p.length - 1 + 1 = p.length, omega,
    convert_to p.f ⟨p.length, by linarith⟩ = v, congr, omega, exact p.fn, refl,
  end }.

@[simp]
lemma tail_length {u v : V G} (p : walk' u v) : (tail p).length = p.length - 1 := rfl

@[simp]
def tail_get_vert {u v : V G} (p : walk' u v) (i : ℕ) : (tail p).get_vert i = p.get_vert (i + 1) :=
begin
  cases p, dsimp [get_vert, tail], cases p_length, simp, split_ifs; refl,
  subst u, subst v, simp, simp [nat.succ_eq_add_one],
  by_cases key : i < p_length + 1, simp [key], simp [key],
end

def cons_tail_eq {u v : V G} (p : walk' u v) (h : 0 < p.length) : cons (walk_adj₀ p h) (tail p) = p :=
begin
  ext, simp, omega,
  intros i,
  cases i, simp,
  simp,
end

--def tail_cons {u v w : V G} (h : u ~g v) (p : walk' v w) (heq : v = (cons h p).get_vert 1) : tail (cons h p) = eq.rec p heq :=
--begin
--  ext, simp, tidy,
--end

def of_walk : Π {u v : V G}, walk u v → walk' u v
| _ _ walk.nil := nil
| _ _ (walk.cons h p) := cons h (of_walk p)

@[simp]
lemma of_walk_nil {u : V G} : of_walk (@walk.nil _ u) = nil := rfl

@[simp]
lemma of_walk_cons {u v w : V G} (h : u ~g v) (p : walk v w) : of_walk (walk.cons h p) = cons h (of_walk p) := rfl

@[simp]
lemma of_walk_length {u v : V G} (p : walk u v) : (of_walk p).length = p.length :=
by { induction p, refl, simpa using p_ih }

@[simp]
lemma of_walk_get_vert {u v : V G} (i : ℕ) (p : walk u v) : (of_walk p).get_vert i = p.get_vert i :=
begin
  induction p generalizing i, simp,
  simp, induction i, refl, simp, apply p_ih,
end

def to_walk {u v : V G} (p : walk' u v) : walk u v :=
@nat.rec_on (λ n, Π (u v : V G) (p : walk' u v) (h : p.length = n), walk u v)
p.length
(λ u v p h, begin have h := length_0 p h, subst u, end)
(λ n f u v p h, begin refine walk.cons (walk_adj₀ p _) (f _ _ (tail p) _), rw h, apply nat.succ_pos, simp [h], end)
u v p (rfl : p.length = p.length)

@[simp]
def to_walk_nil {u : V G} : to_walk (@nil _ u) = walk.nil := rfl

lemma simp_nat_rec {C : ℕ → Sort*} (h0 : C 0) (hn : Π (n : ℕ), C n → C n.succ) (n : ℕ) :
  @nat.rec C h0 hn (n + 1) = hn n (@nat.rec C h0 hn n) :=
begin change @nat.rec C h0 hn n.succ = _, simp, end

lemma simp_nat_rec0 {C : ℕ → Sort*} (h0 : C 0) (hn : Π (n : ℕ), C n → C n.succ) :
  @nat.rec C h0 hn 0 = h0 :=
begin change @nat.rec C h0 hn nat.zero = h0, simp, end

@[simp]
lemma to_walk_cons {u v w : V G} (h : u ~g v) (p : walk' v w) : to_walk (cons h p) = walk.cons h (to_walk p) :=
begin
  dunfold to_walk, simp, rw simp_nat_rec,
  cases p, subst v, subst w, dsimp at *, simp, congr, dsimp [tail], simp, ext, cases p_f, simp [get_vert],
  cases x, simp at x_property, simp [x_property],
end

@[simp]
lemma to_walk_get_vert_aux {u v : V G} (i : ℕ) (p : walk' u v) (n : ℕ) (h : p.length = n) : (to_walk p).get_vert i = p.get_vert i :=
begin
  induction n generalizing u v i p,
  { cases p, subst u, subst v, dsimp at h, subst p_length, dsimp [to_walk], simp [simp_nat_rec0], dsimp [get_vert], split_ifs,
    have hh : i = 0, omega, subst i, refl, refl, },
  have key := cons_tail_eq p (by omega),
  rw ←key, simp, cases i, refl, simp, rw n_ih, simp, simp, rw h, refl,
end

@[simp]
lemma to_walk_get_vert {u v : V G} (i : ℕ) (p : walk' u v) : (to_walk p).get_vert i = p.get_vert i :=
to_walk_get_vert_aux i p p.length rfl

@[simp]
lemma to_walk_length_aux {u v : V G} (p : walk' u v) (n : ℕ) (h : p.length = n) : (to_walk p).length = p.length :=
begin
  induction n generalizing p u v,
  { cases p, subst u, subst v, dsimp at h, subst p_length, refl, },
  have key := cons_tail_eq p (by omega), rw ← key, simp, rw n_ih, simp, simp, rw h, refl,
end

@[simp]
lemma to_walk_length {u v : V G} (p : walk' u v) : (to_walk p).length = p.length :=
to_walk_length_aux p p.length rfl

@[simp]
def to_walk_right_inv {u v : V G} (x : walk' u v) :
  of_walk (to_walk x) = x :=
begin
  ext, simp,
  intros i h, simp at h, simp,
end

@[simp]
def to_walk_left_inv {u v : V G} (x : walk u v) :
  to_walk (of_walk x) = x :=
by { induction x, refl, simpa using x_ih }

-- def rec_aux (n : ℕ) {C : Π (u v : V G), walk' u v → Sort*} {u v : V G}
--   (hnil : Π {v : V G}, C v v nil)
--   (hcons : Π (m : ℕ) (hm : m < n) {u v w : V G} (h : u ~g v) (p : walk' v w) (heq : p.length = m), C v w p → C u w (cons h p))
--   (p : walk' u v) (heq : p.length = n) :
--   C u v p :=
-- begin
--   induction n generalizing C hnil hcons u v p heq,
--   { cases p, subst u, subst v, dsimp at heq, subst p_length, have hh := @hnil (p_f 0), convert hh, ext, cases x, have hh : x_val = 0, linarith, subst x_val, refl, },
--   have key := cons_tail_eq p _, rw ←key,
--   swap, rw heq, apply nat.succ_pos,
--   apply hcons p.tail.length,
--   rw ← heq, simp, rw heq, change n_n+1-1 < n_n+1, apply nat.sub_lt, apply nat.succ_pos, apply nat.succ_pos, refl,
--   apply n_ih,
--   intro v, apply hnil,
--   swap, simp, rw heq, refl,
--   rintros _ hm u v w h p rfl hc,
--   apply hcons p.length, change p.length < n_n+1, linarith, refl, exact hc,
-- end.

-- @[elab_as_eliminator]
-- def rec_on_cons {C : Π (u v : V G), walk' u v → Sort*} {u v : V G} (p : walk' u v)
--   (hnil : Π {v : V G}, C v v nil)
--   (hcons : Π {u v w : V G} (h : u ~g v) (p : walk' v w), C v w p → C u w (cons h p)) :
--   C u v p :=
-- begin
--   refine @rec_aux _ p.length C u v _ _ p rfl,
--   intro v, apply hnil,
--   intros m hm u v w h p rfl hc,
--   apply hcons, exact hc,
-- end

-- @[simp]
-- lemma rec_on_cons_nil {C : Π (u v : V G), walk' u v → Sort*} {u : V G}
--   (hnil : Π {v : V G}, C v v nil)
--   (hcons : Π {u v w : V G} (h : u ~g v) (p : walk' v w), C v w p → C u w (cons h p)) :
--   @rec_on_cons _ C u u nil @hnil @hcons = @hnil u := rfl

-- @[simp]
-- lemma rec_on_cons_cons {C : Π (u v : V G), walk' u v → Sort*} {u v w : V G} (h : u ~g v) (p : walk' v w)
--   (hnil : Π {v : V G}, C v v nil)
--   (hcons : Π {u v w : V G} (h : u ~g v) (p : walk' v w), C v w p → C u w (cons h p)) :
--   @rec_on_cons _ C u w (cons h p) @hnil @hcons = @hcons u v w h p (@rec_on_cons _ C v w p @hnil @hcons) :=
-- begin
--   refine rec_on_cons (cons h p) _ _,
--   intro v, simp,
-- --  cases p, subst v, subst w, dsimp,
-- --  induction p_length, simp,
-- --  dsimp [rec_on_cons, rec_aux], cases p, subst v, subst w, dsimp,
-- --  induction p_length generalizing p_f u hnil hcons, dsimp [], have h' : 0 + 1 = 1 := rfl, simp [h'],
-- end



-- def path_map_drop {n : ℕ} (f : ↟(path_graph (n+1)) →g G) : ↟(path_graph n) →g G :=
-- { to_fun := λ n, f ⟨n.val + 1, by { cases n, linarith }⟩,
--   map_rel' := begin
--     rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
--     apply f.map_rel',
--     rw path_graph_adj at h ⊢, dsimp at h ⊢,
--     cases h; subst h, left, refl, right, refl,
--   end }

-- lemma path_graph_adj (n : ℕ) (i : ℕ) (h : i < n) :
--   @adj' ↟(path_graph n) (⟨i, by linarith⟩ : fin (n+1)) (⟨i + 1, by linarith⟩ : fin (n+1)) :=
-- by { rw path_graph_adj, left, refl }

end walk'

def walk_equiv_walk' {G : simple_graph} (u v : V G) : walk u v ≃ walk' u v :=
{ to_fun := walk'.of_walk,
  inv_fun := walk'.to_walk,
  right_inv := λ x, by simp,
  left_inv := λ x, by simp }

namespace walk
variables {G : simple_graph}

/--
Convert a walk (as a `walk`) to a graph homomorphism.
-/
def to_map {u v : V G} (p : walk u v) : ↟(path_graph p.length) →g G :=
begin
  have h := walk'.of_walk_length p,
  rw ←h,
  exact (walk'.of_walk p).f,
end

end walk

/-!
## old stuff
-/

-- First step, defining the monoid of path graphs.
--set_option pp.notation false
/-- thinking of a `path_graph (n + m)` as being a path of length n
followed by a path of length m, includes the first path. --/
def path_graph.incl₁ (n m : ℕ) : ↟(path_graph n) →g ↟(path_graph (n + m)) :=
{ to_fun := λ v, ⟨v.1, by { cases v, linarith }⟩,
  map_rel' := begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩,
    repeat { rw path_graph_adj },
    dsimp,
    intro h, cases h; rw h,
    left, linarith, right, linarith
  end }

/-- thinking of a `path_graph (n + m)` as being a path of length n
followed by a path of length m, includes the second path. --/
def path_graph.incl₂ (n m : ℕ) : ↟(path_graph m) →g ↟(path_graph (n + m)) :=
{ to_fun := λ v, ⟨n + v.1, by { cases v, linarith }⟩,
  map_rel' := begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩,
    repeat { rw path_graph_adj },
    dsimp,
    intro h, cases h; rw h,
    left, linarith, right, linarith
  end }

variables (G : simple_graph)

/-
The composition of paths, following `pn` first and then `pm`.
-/
def walk_join {n m : ℕ} (pn : ↟(path_graph n) →g G) (pm : ↟(path_graph m) →g G) : ↟(path_graph (n + m)) →g G :=
{ to_fun := λ v, if h : ↑v < n
                 then pn ⟨v, by linarith [h]⟩
                 else pm (by { cases v with v hv, rw [nat.add_assoc, nat.add_comm] at hv,
                               apply fin.sub_nat n ⟨v, hv⟩, dsimp at h, push_neg at h, exact h }),
  map_rel' := begin
    rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
    dsimp,
    repeat { rw path_graph_adj at h },
    dsimp at h,
    cases h,
    subst w,
    split_ifs,
    apply pn.map_rel', rw path_graph_adj, left, simp,
    push_neg at h_1, have h' : n = v + 1, linarith, subst n,
--    split_ifs,
--    simp, --split_ifs,
--    {apply pn.map_adj',   },
    sorry, sorry, sorry, sorry,
  end }

/--
"Flip over" the elements of `fin (n + 1)`, reversing `0` and `n`.
-/
def fin.flip (n : ℕ) : fin (n + 1) → fin (n + 1) := λ v, ((n - (v : ℕ) : ℕ) : fin (n + 1))

lemma fin.flip.invol (n : ℕ) : function.involutive (fin.flip n) :=
begin
  intro v, dsimp [fin.flip],
  rw fin.coe_coe_of_lt, swap, exact nat.sub_lt_succ n ↑v,
  cases v,
  convert_to ↑v_val = _, dsimp,
  have h : n - (n - v_val) = v_val, { have : v_val ≤ n, linarith, omega, },
  rw h, apply subtype.val_injective, dsimp,
  exact fin.coe_coe_of_lt v_property,
end

/--
A path graph is isomorphic to itself where the endpoints are swapped.
-/
def path_graph.invol (n : ℕ) : ↟(path_graph n) ≃g ↟(path_graph n) :=
{ to_fun := fin.flip n,
  inv_fun := fin.flip n,
  left_inv := fin.flip.invol n,
  right_inv := fin.flip.invol n,
  map_rel_iff' := begin
    intros v w, simp,
    split,
    intro h,
    unfold fin.flip,
    apply symm,
    rw path_graph_adj,
    rw path_graph_adj at h,
    cases h with hl hr,
    left,
    simp at hl,
    rw hl,
    have h1 : ↑v + 1 < n + 1,
    rw ← hl,
    exact fin.is_lt _,
    simp,
    rw nat.mod_eq_of_lt,
    rw nat.mod_eq_of_lt,
    rw nat.sub_add_eq_add_sub,
    rw nat.add_sub_add_right,
    simp at h1,
    exact nat.succ_le_iff.mpr h1,
    exact nat.sub_lt_succ n (↑v + 1),
    rw nat.succ_eq_add_one,
    exact nat.sub_lt_succ n ↑v,

    right,
    simp at hr,
    rw hr,
    have h1 : ↑w + 1 < n + 1,
    rw ← hr,
    exact fin.is_lt _,
    simp,
    rw nat.mod_eq_of_lt,
    rw nat.mod_eq_of_lt,
    rw nat.sub_add_eq_add_sub,
    simp,
    simp at h1,
    exact nat.succ_le_iff.mpr h1,
    exact nat.sub_lt_succ n (↑w + 1),
    rw nat.succ_eq_add_one,
    exact nat.sub_lt_succ n ↑w,

    intro h,
    unfold fin.flip at h,
    apply symm,
    rw path_graph_adj,
    rw path_graph_adj at h,
    cases h with hl hr,
    left,
    simp at hl,
    rw nat.mod_eq_of_lt at hl,
    rw nat.mod_eq_of_lt at hl,
    simp,
    have : ↑v < n + 1,
    exact fin.is_lt _,
    have : ↑w < n + 1,
    exact fin.is_lt _,
    rw ← nat.succ_eq_add_one (n - ↑v) at hl,
    have h2 := nat.lt_of_sub_eq_succ,
    specialize h2 hl,
    rw nat.succ_eq_add_one (n - ↑v) at hl,
    --apply add_right_cancel n,

    sorry,
    exact nat.sub_lt_succ n ↑v,
    exact nat.sub_lt_succ n ↑w,
    sorry,
--    split, rintros ⟨h₁, h₂⟩,
--    cases h₂, rw h₂.1 at h₁ ⊢, dunfold fin.flip, sorry, sorry, sorry,
  end }

lemma path_graph.invol.prop₁ (n : ℕ) : (path_graph.invol n) 0 = n := by tidy
lemma path_graph.invol.prop₂ (n : ℕ) : (path_graph.invol n) n = 0 :=
begin
  change fin.flip n n = 0,
  dunfold fin.flip,
  apply subtype.val_injective, dsimp,
  sorry,
--  rw fin.coe_val_of_lt, rw fin.coe_coe_of_lt; linarith, omega,
end

/--
A path of length `n` in a graph between vertices `v` and `w` is a sequence of `n + 1` *distinct* vertices,
each related to the next by adjacency -- the `n` counts the edges along the way.
We model a path as a graph embedding from a length-`n` path graph.
-/
def path (n : ℕ) (v w : V G) := { f : ↟(path_graph n) →g G // function.injective f ∧ v = f 0 ∧ w = f n }

/-- The relation that there exists a walk of any length between two vertices. -/
def exists_walk : V G → V G → Prop := λ v w, nonempty (walk v w)

/-- The relation that there exists a path of any length between two vertices. -/
def exists_path : V G → V G → Prop := λ v w, nonempty (Σ (n : ℕ), path G n v w)

@[refl] lemma exists_walk.refl (v : V G) : exists_walk G v v :=
by { use walk.nil, }

@[symm] lemma exists_walk.symm ⦃v w : V G⦄ (hvw : exists_walk G v w) : exists_walk G w v :=
by { tactic.unfreeze_local_instances, cases hvw, use hvw.reverse, }

@[trans] lemma exists_walk.trans ⦃u v w : V G⦄ (huv : exists_walk G u v) (hvw : exists_walk G v w) : exists_walk G u w :=
begin
  tactic.unfreeze_local_instances, cases hvw,
  tactic.unfreeze_local_instances, cases huv,
  use huv.concat hvw,
end

lemma exists_walk.is_equivalence : equivalence (exists_walk G) :=
mk_equivalence _ (exists_walk.refl G) (exists_walk.symm G) (exists_walk.trans G)

def exists_walk.setoid : setoid (V G) := setoid.mk _ (exists_walk.is_equivalence G)

lemma exists_path_eq_exists_walk : exists_path G = exists_walk G :=
begin
  ext v w,
  sorry,
  sorry,
end

section path

def disjoint (n m : ℕ) (v w : V G) (p : path G n v w) (q : path G m v w) : Prop :=
  ∃ k : ℕ, p.1 k ≠ q.1 k

end path

/--
The equivalence relation generated by `adj G` is another way `exists_walk G` could be defined.
-/
lemma exists_walk_eq_eqv_gen : exists_walk G = eqv_gen G.adj :=
begin
  sorry
end

/--
Quotient of the vertex type by existence of walks.
-/
def connected_components := quotient (exists_walk.setoid G)

/-- Determines if a graph is connected -/
def is_connected : Prop := ∀ v w, exists_walk G v w

/-- The graph does not contain a cycle -/
def is_acyclic : Prop := ∀ (n : ℕ) (h : 3 ≤ n) (f : ↟(cycle_graph n h) →g G), ¬function.injective f

/-- A tree is an acyclic connected graph -/
def is_tree : Prop := is_connected G ∧ is_acyclic G



end simple_graph
