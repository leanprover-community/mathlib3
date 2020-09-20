import combinatorics.simple_graph.basic
import combinatorics.simple_graph.hom
import combinatorics.simple_graph.subgraph
open simple_graph

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

/--
Walks as homomorphisms of path graphs.
-/
@[ext]
structure walk' (u v : V G) :=
(n : ℕ)
(f : ↟(path_graph n) →g G)
(f0 : f (⟨0, by omega⟩ : fin (n+1)) = u)
(fn : f (⟨n, by omega⟩ : fin (n+1)) = v)

def to_walk' {u v : V G} (p : walk u v) : walk' u v :=
{ n := p.length,
  f := { to_fun := λ n, p.get_vert n.val,
         map_rel' := begin
           rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
           rw path_graph_adj at h,
           dsimp at h, dsimp [get_vert],
           cases h,
           { subst h, apply get_vert_rel, linarith, },
           { subst h,
             rw adj_symm,
             apply get_vert_rel, linarith, }
         end },
  f0 := by simp,
  fn := by simp }

-- 340:1: walk.rec :
--   Π {G : simple_graph} {C : Π (a a_1 : G.V), walk a a_1 → Sort u_2},
--     (Π {v : G.V}, C v v nil) →
--     (Π {u v w : G.V} (h : u ~g v) (p : walk v w), C v w p → C u w (cons h p)) →
--     Π {a a_1 : G.V} (n : walk a a_1), C a a_1 n

def walk'.cons {u v w : V G} (h : u ~g v) (p : walk' v w) : walk' u w :=
{ n := p.n + 1,
  f := {
    to_fun := λ i, match i with
            | ⟨0, h⟩ := u
            | ⟨i'+1, h⟩ := p.f (⟨i', by linarith⟩ : fin (p.n + 1))
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
    end
  },
  f0 := rfl,
  fn := begin
    dsimp [walk'.cons._match_1], exact p.fn,
  end }

def path_map_drop {n : ℕ} (f : ↟(path_graph (n+1)) →g G) : ↟(path_graph n) →g G :=
{ to_fun := λ n, f ⟨n.val + 1, by { cases n, linarith }⟩,
  map_rel' := begin
    rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
    apply f.map_rel',
    rw path_graph_adj at h ⊢, dsimp at h ⊢,
    cases h; subst h, left, refl, right, refl,
  end }

lemma path_graph_adj (n : ℕ) (i : ℕ) (h : i < n) :
  @adj' ↟(path_graph n) (⟨i, by linarith⟩ : fin (n+1)) (⟨i + 1, by linarith⟩ : fin (n+1)) :=
by { rw path_graph_adj, left, refl }

/--
Convert a walk (as a graph homomorphism) to a `walk`.
-/
protected
def to_walk_aux : Π {n : ℕ} (f : ↟(path_graph n) →g G), walk (f (⟨0, by linarith⟩ : fin (n+1))) (f (⟨n, by linarith⟩ : fin (n+1)))
| 0 f := nil
| (n+1) f := cons (f.map_rel' (path_graph_adj (n+1) 0 (by linarith))) (to_walk_aux (path_map_drop f))

def walk'.nil {v : V G} : walk' v v :=
{ n := 0,
  f := { to_fun := λ _, v,
         map_rel' := begin
           rintros ⟨i, hi⟩ ⟨j, hj⟩, have hi' : i = 0, linarith, have hj' : j = 0, linarith,
           subst i, subst j, simp, end },
  f0 := rfl,
  fn := rfl }

def to_walk' : Π {u v : V G}, walk u v → walk' u v
| _ _ nil := walk'.nil
| _ _ (cons h p) := walk'.cons h (to_walk' p)

@[simp]
lemma get_vert_to_walk_aux {n : ℕ} (f : ↟(path_graph n) →g G) (i : ℕ) (h : i < n+1) :
  get_vert i (walk.to_walk_aux f) = f (⟨i, h⟩ : fin (n+1)) :=
begin
  induction n generalizing f i h,
  { have : i = 0, linarith, subst i, refl },
  dsimp [walk.to_walk_aux],
  cases i, refl,
  dsimp [get_vert],
  rw n_ih, refl,
  change i+1 < n_n+1+1 at h, linarith,
end

@[simp]
protected
lemma length_of_to_walk_aux {n : ℕ} (f : ↟(path_graph n) →g G) :
  (walk.to_walk_aux f).length = n :=
by { induction n, refl, dsimp [walk.to_walk_aux], rw n_ih }

def to_walk {u v : V G} (p : walk' u v) : walk u v :=
@eq.rec_on _ _ (λ x, walk u x) _ p.fn $
@eq.rec_on _ _ (λ x, walk x (p.f (⟨p.n, by linarith⟩ : fin (p.n + 1)))) _ p.f0 $
walk.to_walk_aux p.f

lemma to_walk_nil {u : V G} : to_walk (@nil _ u) = @n

-- lemma to_walk_heq {u v : V G} (p : walk' u v) :
--   to_walk p == walk.to_walk_aux p.f :=
-- rec_heq_of_heq p.fn (rec_heq_of_heq p.f0 heq.rfl)

lemma walk_rec_heqi_head {u v u' : V G} (eq : u = u') (p : walk u v) :
  @eq.rec _ _ (λ x, walk x v) p _ eq === p :=
by subst eq

lemma walk_rec_heqi_tail {u v v' : V G} (eq : v = v') (p : walk u v) :
  @eq.rec _ _ (λ x, walk u x) p _ eq === p :=
by subst eq

lemma to_walk_heq_to_walk_aux {u v : V G} (p : walk' u v) :
  to_walk p === walk.to_walk_aux p.f :=
by { refine heqi.trans (walk_rec_heqi_tail _ _) _,
     refine heqi.trans (walk_rec_heqi_head _ _) _,
     refl, }

@[simp]
lemma length_of_to_walk' {u v : V G} (p : walk u v) :
  (to_walk' p).n = p.length := rfl

@[simp]
lemma length_of_to_walk {u v : V G} (p : walk' u v) :
  (to_walk p).length = p.n :=
begin
  have h := heqi.subst _ _ (λ u v p, p.length) (to_walk_heq_to_walk_aux p),
  dsimp at h, rw h, simp,
end

@[simp]
def to_walk_left_inv {u v : V G} (x : walk u v) :
  to_walk (to_walk' x) = x :=
begin
  apply eq_of_heqi,
  refine heqi.trans (to_walk_heq_to_walk_aux _) _,
  induction x,
  { refl, },
  dsimp [walk.to_walk_aux, to_walk'],
  rw heqi.cons_iff,
  dsimp [get_vert],
  simp only [true_and, eq_self_iff_true],
  exact x_ih,
end



-- REMOVE probably not true!
-- def path_heq_iff_eq {n n' : ℕ} (f : ↟(path_graph n) →g G) (f' : ↟(path_graph n') →g G) :
--   f == f' ↔ (∃ (h : n = n'), @eq.rec _ _ (λ m, ↟(path_graph m) →g G) f _ h = f') :=
-- begin
--   split, swap, rintro ⟨rfl, rfl⟩, refl,
--   intro h, wlog : n ≤ n',
--   swap,
--   { rcases this f' f h.symm with ⟨h, he⟩, use h.symm, subst h, symmetry, simpa using he, },
--   cases lt_or_eq_of_le case,
--   swap,
--   { subst n', use rfl, simpa using h, },
--   exfalso,
--   let f'' := cast (type_eq_of_heq h) f, have oeu := @heq.refl,
-- end

@[simp]
def to_walk_right_inv_aux {u v : V G} (n : ℕ) (x : walk' u v) (hx : x.n = n) :
  to_walk' (to_walk x) = x :=
begin
  induction n generalizing x u v,
  dsimp [to_walk, to_walk'], 
  cases x, change x_n = 0 at hx, subst u, subst v, subst x_n, simp, ext n, cases n, dsimp,
  induction n_val, refl, dsimp at n_property, simp at n_property, change n_val_n + 1 < 1 at n_property, exfalso, linarith,
  cases x, subst u, subst v, change x_n = n_n+1 at hx, subst x_n, dsimp [to_walk, walk.to_walk_aux, to_walk'],
  have h' := n_ih (path_map_drop x_f),
end

@[simp]
def to_walk_right_inv {u v : V G} (x : walk' u v) :
  to_walk' (to_walk x) = x :=
begin
  ext1, simp,
  generalize eq : (to_walk x).to_walk'.f = ff,
  have h : (to_walk x).to_walk'.n = x.n, simp,
  have h' := congr_arg (λ n, ↟(path_graph n) →g G) h, dsimp at h',
  have hc := cast_heq h' ff,
  simp [h],

  rw length_of_to_walk' at ff,
  rw length_of_to_walk at ff,
  cases x,  cases ff,
  -- cases x, subst u, subst v,
  -- dsimp [to_walk'], congr,
  -- simp,
  -- swap, apply proof_irrel_heq,
  -- dsimp [to_walk], cases x_f, congr,
  -- repeat { rw [walk.length_of_to_walk_aux], },
  -- simp,
  -- ext n, rw get_vert_to_walk_aux, cases n, dsimp, congr,
  -- apply proof_irrel_heq,
end

def walk_equiv_walk' (u v : V G) : walk u v ≃ walk' u v :=
{ to_fun := to_walk',
  inv_fun := to_walk,
  right_inv := begin
    intro x,
    have h := to_walk_right_inv x,
  end,
  left_inv := begin
    intro x,
  end
}



/--
Convert a walk (as a `walk`) to a graph homomorphism.
-/
def to_map {u v : V G} (p : walk u v) : ↟(path_graph p.length) →g G :=
{ to_fun := λ n, p.get_vert n.val,
  map_rel' := begin
    rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
    rw path_graph_adj at h,
    dsimp at h, dsimp [get_vert],
    cases h,
    { subst h, apply get_vert_rel, linarith, },
    { subst h,
      rw adj_symm,
      apply get_vert_rel, linarith, }
  end }

/--
Convert a walk (as a graph homomorphism) to a `walk`.
-/
def of_map : Π {n : ℕ} (f : ↟(path_graph n) →g G), walk (f (⟨0, by linarith⟩ : fin (n+1))) (f (⟨n, by linarith⟩ : fin (n+1)))
| 0 f := nil
| (n+1) f := cons (f.map_rel' (path_graph_adj (n+1) 0 (by linarith))) (of_map (path_map_drop f))

@[simp]
lemma of_map_length_eq {n : ℕ} (f : ↟(path_graph n) →g G) :
  (of_map f).length = n :=
begin
  induction n, refl,
  dsimp [of_map], rw n_ih,
end

@[simp]
def of_map_of_to_map {u v : V G} (x : walk u v) :
  of_map x.to_map == x :=
begin
  induction x, refl,
  dsimp [to_map, of_map], congr,
  dsimp [get_vert'], apply get_vert_n,
  dsimp [path_map_drop], exact x_ih,
end

def of_map' {n : ℕ} {u v : V G} (f : ↟(path_graph n) →g G)
  (hu : f (⟨0, by linarith⟩ : fin (n+1)) = u)
  (hv : f (⟨n, by linarith⟩ : fin (n+1)) = v) : walk u v :=
begin
  let w := of_map f,
  rw [hu, hv] at w,
  exact w,
end

@[simp]
def of_map'_heq {n : ℕ} {u v : V G} (f : ↟(path_graph n) →g G)
  (hu : f (⟨0, by linarith⟩ : fin (n+1)) = u)
  (hv : f (⟨n, by linarith⟩ : fin (n+1)) = v) : of_map' f hu hv == of_map f :=
by { dsimp [of_map'], tidy }

@[simp]
def of_map'_heq' {X : Sort*} {C : Π {u v : V G}, walk u v → X}
  {n : ℕ} {u v : V G} (f : ↟(path_graph n) →g G)
  (hu : f (⟨0, by linarith⟩ : fin (n+1)) = u)
  (hv : f (⟨n, by linarith⟩ : fin (n+1)) = v) : C (of_map' f hu hv) = C (of_map f) :=
by { dsimp [of_map'], tidy }


def of_map'_length_eq {n : ℕ} {u v : V G} (f : ↟(path_graph n) →g G)
  (hu : f (⟨0, by linarith⟩ : fin (n+1)) = u)
  (hv : f (⟨n, by linarith⟩ : fin (n+1)) = v) : (of_map' f hu hv).length = n :=
begin
  have h' := @of_map'_heq' _ _ (λ _ _ x, length x = n) _ _ _ f hu hv,
  apply eq.mpr h',
  simp,
end

@[simp]
def of_map'_of_to_map {u v : V G} (x : walk u v)
  (hu : x.to_map (⟨0, by linarith⟩ : fin (x.length+1)) = u)
  (hv : x.to_map (⟨x.length, by linarith⟩ : fin (x.length+1)) = v) :
  of_map' x.to_map hu hv = x :=
begin
  dsimp [of_map', to_map], 
end

def walk_equiv_walk' (u v : V G) : walk u v ≃ walk' u v :=
{ to_fun := λ p,
  { n := p.length,
    f := p.to_map,
    f0 := by { dsimp [to_map], refl },
    fn := by { dsimp [to_map], simp } },
  inv_fun := λ p, of_map' p.f p.f0 p.fn,
  left_inv := begin
    tidy,
  end,
  right_inv := begin
    intros p',
    cases p', dsimp [],
    tidy, rw of_map'_length_eq,
  end
}



def walk_concat {n m : ℕ} (pn : ↟(path_graph n) →g G) (pm : ↟(path_graph m) →g G)
  (h : pn (⟨n, by linarith⟩ : fin (n+1)) = pm 0)  :
  ↟(path_graph (n + m)) →g G :=
begin
  let w1 := of_map pn,
  let w2 := of_map pm,
  have hw1 : n = w1.length,
  { rw of_map_length_eq, },
  have hw2 : m = w2.length,
  { rw of_map_length_eq, },
  rw hw1, rw hw2,
  rw h at w1,
  let f := to_map (w1.concat w2),
  convert f,
  rw concat_length,
  simp, rw ←of_map_length_eq pn,
  rw ←of_map_length_eq pm,

  exact f,
  rw concat_length at f,
  repeat { rw of_map_length_eq at f },
end

end walk

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
    intros v w, simp, sorry,
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
A walk of length `n` in a graph between vertices `v` and `w` is a sequence of `n + 1` vertices,
each related to the next by adjacency -- the `n` counts the edges along the way.
We model a walk as a graph homomorphism from a length-`n` path graph.
-/
def walk (n : ℕ) (v w : V G) := { f : ↟(path_graph n) →g G // v = f 0 ∧ w = f n }

/--
Reverse a walk.
-/
def walk.symm {n : ℕ} {v w : V G} (p : walk G n v w) : walk G n w v :=
⟨p.val.comp ↑(path_graph.invol n), begin
  simp, erw [path_graph.invol.prop₁ n, path_graph.invol.prop₂ n],
  use [p.2.2, p.2.1],
end⟩

/--
A path of length `n` in a graph between vertices `v` and `w` is a sequence of `n + 1` *distinct* vertices,
each related to the next by adjacency -- the `n` counts the edges along the way.
We model a path as a graph embedding from a length-`n` path graph.
-/
def path (n : ℕ) (v w : V G) := { f : ↟(path_graph n) →g G // function.injective f ∧ v = f 0 ∧ w = f n }

/-- The relation that there exists a walk of any length between two vertices. -/
def exists_walk : V G → V G → Prop := λ v w, nonempty (Σ (n : ℕ), walk G n v w)

/-- The relation that there exists a path of any length between two vertices. -/
def exists_path : V G → V G → Prop := λ v w, nonempty (Σ (n : ℕ), path G n v w)

@[refl] lemma exists_walk.refl (v : V G) : exists_walk G v v :=
by { use [0, λ _, v], delta path_graph, sorry, sorry, }

@[symm] lemma exists_walk.symm ⦃v w : V G⦄ (hvw : exists_walk G v w) : exists_walk G w v :=
by { tactic.unfreeze_local_instances, cases hvw, rcases hvw with ⟨n, p⟩, use [n, walk.symm G p], }

@[trans] lemma exists_walk.trans ⦃u v w : V G⦄ (huv : exists_walk G u v) (hvw : exists_walk G v w) : exists_walk G u w :=
begin
  tactic.unfreeze_local_instances, cases hvw, rcases hvw with ⟨m, pv⟩,
  tactic.unfreeze_local_instances, cases huv, rcases huv with ⟨n, pu⟩,
  --rcases huv with ⟨n, ⟨pu⟩⟩, rcases hvw with ⟨m, ⟨pv⟩⟩,
  use n+m,
  -- now need to concatenate walks  probably better to define path concatenation elsewhere and then use it here!
  sorry
end

lemma exists_walk.is_equivalence : equivalence (exists_walk G) :=
mk_equivalence _ (exists_walk.refl G) (exists_walk.symm G) (exists_walk.trans G)

def exists_walk.setoid : setoid (V G) := setoid.mk _ (exists_walk.is_equivalence G)

lemma exists_path_eq_exists_walk : exists_path G = exists_walk G :=
begin
  ext v w,
  sorry,
end

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
