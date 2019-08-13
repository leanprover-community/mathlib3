import system.io
import logic.basic
import data.list.min_max
import tactic.vampire.reify
import tactic.vampire.cnf
import tactic.vampire.skolemize

namespace vampire

local notation `#`      := term.fn
local notation t `&t` s := term.tp t s
local notation t `&v` k := term.vp t k

local notation `$`      := atom.rl
local notation a `^t` t := atom.tp a t
local notation a `^v` t := atom.vp a t

local notation `-*` := lit.neg
local notation `+*` := lit.pos
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt
local notation `∀*`            := form.qua ff

local notation R `;` F `;` V `⊨` f := form.holds R F V f
run_cmd mk_simp_attr `sugars

attribute [sugars]
  -- logical constants
  or_false  false_or
  and_false false_and
  or_true   true_or
  and_true  true_and
  -- implication elimination
  classical.imp_iff_not_or
  classical.iff_iff_not_or_and_or_not
  -- NNF
  classical.not_not
  not_exists
  not_or_distrib
  classical.not_and_distrib
  classical.not_forall

meta def desugar := `[try {simp only with sugars}]

meta def get_domain_core : expr → tactic expr
| `(¬ %%p)     := get_domain_core p
| `(%%p ∨ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ∧ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ↔ %%q) := get_domain_core p <|> get_domain_core q
| (expr.pi _ _ p q) :=
  mcond (tactic.is_prop p) (get_domain_core p <|> get_domain_core q) (return p)
| `(@Exists %%t _)  := return t
| _ := tactic.failed

meta def get_domain : tactic expr :=
(tactic.target >>= get_domain_core) <|> return `(unit)

meta def get_inhabitance (αx : expr) : tactic expr :=
do ihx ← tactic.to_expr ``(inhabited),
   tactic.mk_instance (expr.app ihx αx)

variables {α : Type} [inhabited α]

inductive proof (m : mat) : cla → Type
| ins (k : nat) (μ : mappings) : proof ((m.nth k).substs μ)
| res (a : atom) (c d : cla) :
  proof ((-* a) :: c) →
  proof ((+* a) :: d) →
  proof (c ++ d)
| rot (k : nat) (c : cla) :
  proof c → proof (c.rot k)
| con (l : lit) (c : cla) :
  proof (l :: l :: c) → proof (l :: c)

/- Same as is.fs.read_to_end and io.cmd,
   except for configurable read length. -/
def io.fs.read_to_end' (h : io.handle) : io char_buffer :=
io.iterate mk_buffer $ λ r,
  do done ← io.fs.is_eof h,
    if done
    then return none
    else do
      c ← io.fs.read h 65536,
      return $ some (r ++ c)

def io.cmd' (args : io.process.spawn_args) : io string :=
do child ← io.proc.spawn { stdout := io.process.stdio.piped, ..args },
  buf ← io.fs.read_to_end' child.stdout,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return buf.to_string
open tactic

def term.to_rr : term → string
| (term.fn k)   := k.repr ++  " fn"
| (term.tp t s) := string.join [t.to_rr, " ", s.to_rr, " tp"]
| (term.vp t k) := string.join [t.to_rr, " ", k.repr, " vp"]

def atom.to_rr : atom → string
| (atom.rl k)   := k.repr ++  " rl"
| (atom.tp a t) := string.join [a.to_rr, " ", t.to_rr, " tp"]
| (atom.vp a k) := string.join [a.to_rr, " ", k.repr, " vp"]

def lit.to_rr : lit → string
| (-* a) := a.to_rr ++ " ng"
| (+* a) := a.to_rr ++ " ps"

def cla.to_rr : cla → string
| []       := "nl"
| (l :: c) := cla.to_rr c ++ " " ++ l.to_rr ++ " cs"

def mat.to_rr : mat → string
| []       := "nl"
| (c :: m) := mat.to_rr m ++ " " ++ c.to_rr ++ " cs"

meta def get_rr (m : mat) : tactic string :=
unsafe_run_io $ io.cmd'
{ cmd := "main.pl",
  args := [m.to_rr] }

meta inductive item : Type
| nm  (n : nat)            : item
| trm (t : term)           : item
| mps (m : mappings)       : item
| prf (x : expr) (c : cla) : item

meta def mapping.to_expr : mapping → expr
| (k, t) := expr.mk_app `(@prod.mk nat term) [k.to_expr, t.to_expr]

meta def mappings.to_expr : mappings → expr
| []        := `(@list.nil mapping)
| (m :: ms) := expr.mk_app `(@list.cons mapping) [m.to_expr, mappings.to_expr ms]

meta def build_proof_core (m : mat) (mx : expr) :
  list item → list char → tactic expr
| (item.prf x _ :: stk) [] := return x
| stk (' ' :: chs) :=
  build_proof_core stk chs
| stk ('\n' :: chs) :=
  build_proof_core stk chs
| stk ('n' :: chs) :=
  build_proof_core (item.nm 0 :: stk) chs
| (item.nm k :: stk) ('0' :: chs) :=
  build_proof_core (item.nm (k * 2) :: stk) chs
| (item.nm k :: stk) ('1' :: chs) :=
  build_proof_core (item.nm ((k * 2) + 1) :: stk) chs
| (item.mps μs :: item.nm k :: stk) ('a' :: infs) :=
  let c := (m.nth k).substs μs in
  let πx := expr.mk_app `(@proof.ins) [mx, k.to_expr, μs.to_expr] in
  build_proof_core (item.prf πx c :: stk) infs
| ((item.prf σx ((+* a) :: d)) :: (item.prf πx ((-* b) :: c)) :: stk) ('r' :: infs) :=
  let πx := expr.mk_app `(@proof.res) [mx, a.to_expr, cla.to_expr c, cla.to_expr d, πx, σx] in
  build_proof_core (item.prf πx (c ++ d) :: stk) infs
| ((item.prf πx c) :: item.nm k :: stk) ('t' :: chs) :=
  let πx := expr.mk_app `(@proof.rot) [mx, k.to_expr, c.to_expr, πx] in
  build_proof_core (item.prf πx (c.rot k) :: stk) chs
| ((item.prf πx (l :: _ :: c)) :: stk) ('c' :: chs) :=
  let πx := expr.mk_app `(@proof.con) [mx, l.to_expr, cla.to_expr c, πx] in
  build_proof_core (item.prf πx (l :: c) :: stk) chs
| stk ('e' :: chs) :=
  build_proof_core (item.mps [] :: stk) chs
| (item.nm k :: stk) ('s' :: chs) :=
  build_proof_core (item.trm (term.fn k) :: stk) chs
| (item.trm s :: item.trm t :: stk) ('p' :: chs) :=
  build_proof_core (item.trm (term.tp t s) :: stk) chs
| (item.trm t :: item.nm k :: item.mps μ :: stk) ('m' :: infs) :=
  build_proof_core (item.mps ((k, t) :: μ) :: stk) infs
| _ _ := fail "invalid inference"

variables {R : rls α} {F : fns α} {V : vas α}
variables {b : bool} (f g : form)

local notation R `; ` F `; ` V ` ⊨ ` f := form.holds R F V f

def normalize (f : form) : form :=
skolemize $ pnf $ f.neg

def clausify (f : form) : mat :=
cnf $ form.strip_fa $ normalize f

lemma lit.holds_substs (μs : mappings) (l : lit) :
  (l.substs μs).holds R F V ↔
  l.holds R F (V.substs F μs) :=
by { cases l with a a;
     simp only [lit.holds, lit.substs, vas.substs,
     list.map_map, atom.val_substs] }

lemma cla.holds_substs {μs : mappings} {c : cla} :
  (c.substs μs).holds R F V ↔
  c.holds R F (V.substs F μs)
  :=
by { apply @list.exists_mem_map_iff,
     apply lit.holds_substs }

open list

lemma holds_cla_of_proof {m : mat}
  (h0 : ∀ V : vas α, m.holds R F V) :
  ∀ {c : cla}, proof m c →
  (∀ V : vas α, c.holds R F V) :=
begin
  intros c π V, induction π with
  k μs
  t c1 c2 π1 π2 h1 h2
  k d π h1
  l d π h1,
  { unfold mat.nth,
    cases h1 : list.nth m k;
    unfold option.get_or_else,
    { simp only [cla.substs, cla.tautology,
        list.map, lit.substs, atom.substs],
      apply holds_tautology },
    rw cla.holds_substs,
    apply h0,
    apply list.mem_iff_nth.elim_right,
    refine ⟨_, h1⟩ },
  { apply exists_mem_append.elim_right,
    rcases h1 with ⟨la, hla1 | hla1, hla2⟩,
    { rcases h2 with ⟨lb, hlb1 | hlb1, hlb2⟩,
      { subst hla1, subst hlb1, cases hla2 hlb2 },
      right, refine ⟨_, hlb1, hlb2⟩ },
    left, refine ⟨_, hla1, hla2⟩ },
  { rcases h1 with ⟨t, ht1, ht2⟩,
    refine ⟨t, _, ht2⟩,
    apply mem_rot _ ht1 },
  { rcases h1 with ⟨t, h2 | h2 | h2, h3⟩;
    refine ⟨_, _, h3⟩,
    { left, exact h2 },
    { left, exact h2 },
    right, exact h2 }
end

lemma frxffx_of_proof
  (rn : nat) (R : rls α) (fn : nat) (F : fns α) (f : form) :
  (normalize f).vnew = 0 →
  proof (clausify f) [] → f.frxffx rn R fn F :=
begin
  intros hz h0,
  apply frxffx_of_forall_rxt,
  intros R' h1 F' h2,
  apply classical.by_contradiction,
  rw ← holds_neg, intro h3,
  rw ← pnf_eqv at h3,
  rcases holds_skolemize h3 with ⟨F'', h4, h5⟩,
  have hAF : (skolemize (pnf (form.neg f))).AF,
  { apply AF_skolemize,
    apply QF_pnf },
  have h6 := holds_strip_fa hAF _ (forall_ext_zero h5),
  { have h7 : ∀ (W : vas α), (clausify f).holds R' F'' W,
    { intro W, apply holds_cnf _ (h6 _),
      apply F_strip_fa _ hAF },
    have h8 := holds_cla_of_proof h7 h0 (Vdf α),
    apply not_holds_empty_cla h8 },
  apply le_of_eq hz
end

instance decidable_vnew_eq_zero (f : form) :
  decidable ((normalize f).vnew = 0) := by apply_instance

meta def build_proof (chs : list char)
  (αx ix : expr) (f : form) (m : mat) : tactic expr :=
do πx ← build_proof_core m m.to_expr [] chs,
   let rnx : expr := f.rnew.to_expr,
   let fnx : expr := f.fnew.to_expr,
   let Rx : expr := `(Rdf %%αx),
   let Fx : expr := `(@Fdf %%αx %%ix),
   let fx : expr := f.to_expr,
   let eqx  : expr := `(form.vnew (normalize %%fx) = 0 : Prop),
   let decx : expr := expr.mk_app `(vampire.decidable_vnew_eq_zero) [fx],
   let hx   : expr := expr.mk_app `(@of_as_true) [eqx, decx, `(trivial)],
   let x : expr := expr.mk_app `(@frxffx_of_proof)
     [αx, ix, rnx, Rx, fnx, Fx, fx, hx, πx],
   return x

meta def vampire (inp : option string) : tactic unit :=
do desugar,
   αx ← get_domain,
   ix ← get_inhabitance αx,
   f  ← reify αx,
   let m := clausify f,
   s ← (inp <|> get_rr m),
   x ← build_proof s.data αx ix f m,
   apply x,
   if inp = none
   then trace s
   else skip

end vampire

open lean.parser interactive vampire tactic

meta def tactic.interactive.vampire
  (ids : parse (many ident))
  (inp : option string := none) : tactic unit :=
( if `all ∈ ids
  then local_context >>= monad.filter is_proof >>=
       revert_lst >> skip
  else do hs ← mmap tactic.get_local ids,
               revert_lst hs, skip ) >>
vampire inp
