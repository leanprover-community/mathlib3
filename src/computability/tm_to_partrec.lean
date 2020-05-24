import computability.halting
import computability.turing_machine
import data.num.lemmas

open function (update)
open relation

namespace turing

namespace to_partrec

inductive code
| zero'
| succ
| tail
| cons : code → code → code
| comp : code → code → code
| case : code → code → code
| fix : code → code

def code.eval : code → list ℕ →. list ℕ
| code.zero' := λ v, pure (0 :: v)
| code.succ := λ v, pure [v.head.succ]
| code.tail := λ v, pure v.tail
| (code.cons f fs) := λ v, do n ← code.eval f v, ns ← code.eval fs v, pure (n.head :: ns)
| (code.comp f g) := λ v, g.eval v >>= f.eval
| (code.case f g) := λ v, v.head.elim (f.eval v.tail) (λ y _, g.eval (y :: v.tail))
| (code.fix f) := pfun.fix $ λ v, (f.eval v).map $ λ v,
  if v.head = 0 then sum.inl v.tail else sum.inr v.tail

namespace code

def nil : code := tail.comp succ
def id : code := tail.comp zero'
def head : code := cons id nil
def zero : code := cons zero' nil
def pred : code := case zero head
def rfind (f : code) : code := comp pred $ comp (fix $ cons f $ cons succ tail) zero'
def prec (f g : code) : code :=
let c := cons tail $ cons succ $ cons (comp pred tail) $
  cons (comp g $ cons id $ comp tail tail) $ comp tail $ comp tail tail in
cons (comp (case id $ comp (comp (comp tail tail) (fix c)) zero')
  (cons head $ cons (comp f tail) tail)) nil

local attribute [simp] is_lawful_monad.pure_bind eval
local attribute [simp] theorem nil_eval (v) : nil.eval v = pure [] := by simp [nil]
local attribute [simp] theorem id_eval (v) : id.eval v = pure v := by simp [id]
local attribute [simp] theorem head_eval (v) : head.eval v = pure [v.head] := by simp [head]
local attribute [simp] theorem zero_eval (v) : zero.eval v = pure [0] := by simp [zero]
local attribute [simp] theorem pred_eval (v) : pred.eval v = pure [v.head.pred] :=
by simp [pred]; cases v.head; simp

local attribute [-simp] roption.bind_eq_bind roption.map_eq_map roption.pure_eq_some

theorem exists_code.comp {m n} {f : vector ℕ n →. ℕ} {g : fin n → vector ℕ m →. ℕ}
  (hf : ∃ c : code, ∀ v : vector ℕ n, c.eval v.1 = (λ n, [n]) <$> f v)
  (hg : ∀ i, ∃ c : code, ∀ v : vector ℕ m, c.eval v.1 = (λ n, [n]) <$> g i v) :
  ∃ c : code, ∀ v : vector ℕ m, c.eval v.1 = (λ n, [n]) <$> (vector.m_of_fn (λ i, g i v) >>= f) :=
begin
  suffices : ∃ c : code, ∀ v : vector ℕ m,
    c.eval v.1 = subtype.val <$> vector.m_of_fn (λ i, g i v),
  { obtain ⟨cf, hf⟩ := hf, obtain ⟨cg, hg⟩ := this,
    exact ⟨cf.comp cg, λ v, by simp [hg, hf, map_bind, seq_bind_eq, (∘)]; refl⟩ },
  clear hf f, induction n with n IH,
  { exact ⟨nil, λ v, by simp [vector.m_of_fn]; refl⟩ },
  { obtain ⟨cg, hg₁⟩ := hg 0, obtain ⟨cl, hl⟩ := IH (λ i, hg i.succ),
    exact ⟨cons cg cl, λ v, by simp [vector.m_of_fn, hg₁, map_bind,
      seq_bind_eq, bind_assoc, (∘), hl]; refl⟩ },
end

theorem exists_code {n} {f : vector ℕ n →. ℕ} (hf : nat.partrec' f) :
  ∃ c : code, ∀ v : vector ℕ n, c.eval v.1 = (λ n, [n]) <$> f v :=
begin
  induction hf with n f hf,
  induction hf,
  case nat.primrec'.zero { exact ⟨zero', λ ⟨[], _⟩, rfl⟩ },
  case nat.primrec'.succ { exact ⟨succ, λ ⟨[v], _⟩, rfl⟩ },
  case nat.primrec'.nth : n i {
    refine fin.succ_rec (λ n, _) (λ n i IH, _) i,
    { exact ⟨head, λ ⟨list.cons a as, _⟩, by simp; refl⟩ },
    { obtain ⟨c, h⟩ := IH,
      exact ⟨c.comp tail, λ v, by simpa [← vector.nth_tail] using h v.tail⟩ } },
  case nat.primrec'.comp : m n f g hf hg IHf IHg {
    simpa [roption.bind_eq_bind] using exists_code.comp IHf IHg },
  case nat.primrec'.prec : n f g hf hg IHf IHg {
    obtain ⟨cf, hf⟩ := IHf, obtain ⟨cg, hg⟩ := IHg,
    simp only [roption.map_eq_map, roption.map_some, pfun.coe_val] at hf hg,
    refine ⟨prec cf cg, λ v, _⟩, rw ← v.cons_head_tail,
    specialize hf v.tail, replace hg := λ a b, hg (a :: b :: v.tail),
    simp only [vector.cons_val, vector.tail_val] at hf hg,
    simp only [roption.map_eq_map, roption.map_some, vector.cons_val,
      vector.cons_tail, vector.cons_head, pfun.coe_val, vector.tail_val],
    simp only [← roption.pure_eq_some] at hf hg ⊢,
    induction v.head with n IH; simp [prec, hf, bind_assoc, ← roption.map_eq_map,
      ← bind_pure_comp_eq_map],
    suffices : ∀ a b, a + b = n →
      (n.succ :: 0 :: g (n :: nat.elim (f v.tail) (λ y IH, g (y::IH::v.tail)) n :: v.tail)
         :: v.val.tail : list ℕ) ∈
      pfun.fix (λ v : list ℕ, do
        x ← cg.eval (v.head :: v.tail.tail),
        pure $ if v.tail.head = 0
          then sum.inl (v.head.succ :: v.tail.head.pred :: x.head :: v.tail.tail.tail : list ℕ)
          else sum.inr (v.head.succ :: v.tail.head.pred :: x.head :: v.tail.tail.tail))
        (a :: b :: nat.elim (f v.tail) (λ y IH, g (y::IH::v.tail)) a :: v.val.tail),
    { rw (_ : pfun.fix _ _ = pure _), swap, exact roption.eq_some_iff.2 (this 0 n (zero_add n)),
      simp only [list.head, pure_bind, list.tail_cons] },
    intros a b e, induction b with b IH generalizing a e,
    { refine pfun.mem_fix_iff.2 (or.inl $ roption.eq_some_iff.1 _),
      simp only [hg, ← e, pure_bind, list.tail_cons], refl },
    { refine pfun.mem_fix_iff.2 (or.inr ⟨_, _, IH (a+1) (by rwa add_right_comm)⟩),
      simp only [hg, eval, pure_bind, nat.elim_succ, list.tail],
      exact roption.mem_some_iff.2 rfl } },
  case nat.partrec'.comp : m n f g hf hg IHf IHg { exact exists_code.comp IHf IHg },
  case nat.partrec'.rfind : n f hf IHf {
    obtain ⟨cf, hf⟩ := IHf, refine ⟨rfind cf, λ v, _⟩,
    replace hf := λ a, hf (a :: v),
    simp only [roption.map_eq_map, roption.map_some, vector.cons_val, pfun.coe_val] at hf ⊢,
    refine roption.ext (λ x, _),
    simp only [rfind, roption.bind_eq_bind, roption.pure_eq_some, roption.map_eq_map,
      roption.bind_some, exists_prop, eval, list.head, pred_eval, roption.map_some,
      bool.ff_eq_to_bool_iff, roption.mem_bind_iff, list.length,
      roption.mem_map_iff, nat.mem_rfind, list.tail, bool.tt_eq_to_bool_iff,
      roption.mem_some_iff, roption.map_bind],
    split,
    { rintro ⟨v', h1, rfl⟩,
      suffices : ∀ (v₁ : list ℕ), v' ∈ pfun.fix
        (λ v, (cf.eval v).bind $ λ y, roption.some $ if y.head = 0 then
          sum.inl (v.head.succ :: v.tail) else sum.inr (v.head.succ :: v.tail)) v₁ →
        ∀ n, v₁ = n :: v.val → (∀ m < n, ¬f (m :: v) = 0) →
        (∃ (a : ℕ), (f (a :: v) = 0 ∧ ∀ {m : ℕ}, m < a → ¬f (m :: v) = 0) ∧ [a] = [v'.head.pred]),
      { exact this _ h1 0 rfl (by rintro _ ⟨⟩) },
      clear h1, intros v₀ h1,
      refine pfun.fix_induction h1 (λ v₁ h2 IH, _), clear h1,
      rintro n rfl hm,
      have := pfun.mem_fix_iff.1 h2,
      simp only [hf, roption.bind_some] at this,
      split_ifs at this,
      { simp only [list.head, exists_false, or_false, roption.mem_some_iff,
          list.tail_cons, false_and] at this,
        subst this, exact ⟨_, ⟨h, hm⟩, rfl⟩ },
      { simp only [list.head, exists_eq_left, roption.mem_some_iff,
          list.tail_cons, false_or] at this,
        refine IH _ this (by simp [hf, h]) _ rfl (λ m h', _),
        obtain h|rfl := nat.lt_succ_iff_lt_or_eq.1 h', exacts [hm _ h, h] } },
    { rintro ⟨n, ⟨hn, hm⟩, rfl⟩, refine ⟨n.succ :: v.1, _, rfl⟩,
      have : (n.succ :: v.1 : list ℕ) ∈ pfun.fix
        (λ v, (cf.eval v).bind $ λ y, roption.some $ if y.head = 0 then
          sum.inl (v.head.succ :: v.tail) else sum.inr (v.head.succ :: v.tail)) (n :: v.val) :=
        pfun.mem_fix_iff.2 (or.inl (by simp [hf, hn])),
      generalize_hyp : (n.succ :: v.1 : list ℕ) = w at this ⊢, clear hn,
      induction n with n IH, {exact this},
      refine IH (λ m h', hm (nat.lt_succ_of_lt h')) (pfun.mem_fix_iff.2 (or.inr ⟨_, _, this⟩)),
      simp only [hf, hm n.lt_succ_self, roption.bind_some, list.head, eq_self_iff_true,
        if_false, roption.mem_some_iff, and_self, list.tail_cons] } }
end

end code

inductive cont
| halt
| cons₁ : code → list ℕ → cont → cont
| cons₂ : list ℕ → cont → cont
| comp : code → cont → cont
| fix : code → cont → cont

def cont.eval : cont → list ℕ →. list ℕ
| cont.halt := pure
| (cont.cons₁ fs as k) := λ v, do ns ← code.eval fs as, cont.eval k (v.head :: ns)
| (cont.cons₂ ns k) := λ v, cont.eval k (ns.head :: v)
| (cont.comp f k) := λ v, code.eval f v >>= cont.eval k
| (cont.fix f k) := λ v, if v.head = 0 then k.eval v.tail else f.fix.eval v.tail >>= k.eval

inductive cfg
| normal : code → cont → list ℕ → cfg
| ret : cont → list ℕ → cfg
| halt : list ℕ → cfg

def step_normal : code → cont → list ℕ → cfg
| code.zero' k v := cfg.ret k (0 :: v)
| code.succ k v := cfg.ret k [v.head.succ]
| code.tail k v := cfg.ret k v.tail
| (code.cons f fs) k v := step_normal f (cont.cons₁ fs v k) v
| (code.comp f g) k v := step_normal g (cont.comp f k) v
| (code.case f g) k v :=
  v.head.elim (step_normal f k v.tail) (λ y _, step_normal g k (y :: v.tail))
| (code.fix f) k v := step_normal f (cont.fix f k) v

def step_ret : cont → list ℕ → cfg
| cont.halt v := cfg.halt v
| (cont.cons₁ fs as k) v := step_normal fs (cont.cons₂ v k) as
| (cont.cons₂ ns k) v := step_ret k (ns.head :: v)
| (cont.comp f k) v := step_normal f k v
| (cont.fix f k) v := if v.head = 0 then step_ret k v.tail else
  step_normal f (cont.fix f k) v.tail

def step : cfg → option cfg
| (cfg.normal c k v) := some (step_normal c k v)
| (cfg.ret k v) := some (step_ret k v)
| (cfg.halt _) := none

def cont.then : cont → cont → cont
| cont.halt k' := k'
| (cont.cons₁ fs as k) k' := cont.cons₁ fs as (k.then k')
| (cont.cons₂ ns k) k' := cont.cons₂ ns (k.then k')
| (cont.comp f k) k' := cont.comp f (k.then k')
| (cont.fix f k) k' := cont.fix f (k.then k')

theorem cont.then_eval {k k' : cont} {v} : (k.then k').eval v = k.eval v >>= k'.eval :=
begin
  induction k generalizing v; simp only [cont.eval, cont.then, bind_assoc, pure_bind, *],
  { simp only [← k_ih] },
  { split_ifs; [refl, simp only [← k_ih, bind_assoc]] }
end

def cfg.then : cfg → cont → cfg
| (cfg.normal c k v) k' := cfg.normal c (k.then k') v
| (cfg.ret k v) k' := cfg.ret (k.then k') v
| (cfg.halt v) k' := step_ret k' v

theorem step_normal_then (c) (k k' : cont) (v) :
  step_normal c (k.then k') v = (step_normal c k v).then k' :=
begin
  induction c generalizing k v;
    simp only [cont.then, step_normal, cfg.then, *] {constructor_eq := ff},
  { rw [← c_ih_a, cont.then] },
  { rw [← c_ih_a_1, cont.then] },
  { cases v.head; simp only [nat.elim] },
  { rw [← c_ih, cont.then] },
end

theorem step_ret_then {k k' : cont} {v} :
  step_ret (k.then k') v = (step_ret k v).then k' :=
begin
  induction k generalizing v;
    simp only [cont.then, step_ret, cfg.then, *],
  { rw ← step_normal_then, refl },
  { rw ← step_normal_then },
  { split_ifs, {rw ← k_ih}, {rw ← step_normal_then, refl} },
end

def cfg.result : cfg → option (list ℕ)
| (cfg.halt v) := some v
| _ := none

def code.ok (c : code) :=
∀ k v, eval step (step_normal c k v) = code.eval c v >>= λ v, eval step (cfg.ret k v)

theorem code.ok.zero {c} (h : code.ok c) {v} :
  eval step (step_normal c cont.halt v) = cfg.halt <$> code.eval c v :=
begin
  rw [h, ← is_lawful_monad.bind_pure_comp_eq_map], congr, funext v,
  exact roption.eq_some_iff.2 (mem_eval.2 ⟨refl_trans_gen.single rfl, rfl⟩),
end

theorem code.ok.zero' {c} (h : code.ok c) {v} : code.eval c v =
  eval step (step_normal c cont.halt v) >>= λ v, cfg.result v :=
begin
  rw [h cont.halt, bind_assoc],
  refine (eq.trans _ (bind_pure _)).symm, congr, funext v,
  apply roption.eq_some_iff.2,
  rw [roption.bind_eq_bind, roption.mem_bind_iff],
  exact ⟨_, mem_eval.2 ⟨refl_trans_gen.single rfl, rfl⟩, roption.mem_coe.2 rfl⟩,
end

theorem step_normal.is_ret (c k v) : ∃ k' v', step_normal c k v = cfg.ret k' v' :=
begin
  induction c with _ _ IH1 IH2 _ _ IH1 IH2 _ _ IH1 IH2 _ IH generalizing k v,
  iterate 3 { exact ⟨_, _, rfl⟩ },
  { apply IH1 },
  { apply IH2 },
  { rw step_normal, cases v.head; simp only [nat.elim]; [apply IH1, apply IH2] },
  { apply IH },
end

theorem cont_eval_fix {f k v} (fok : code.ok f) :
  eval step (step_normal f (cont.fix f k) v) = f.fix.eval v >>= λ v, eval step (cfg.ret k v) :=
begin
  refine roption.ext (λ x, _),
  simp only [roption.bind_eq_bind, roption.mem_bind_iff],
  split,
  { suffices :
      ∀ c, x ∈ eval step c →
      ∀ v c', c = cfg.then c' (cont.fix f k) → reaches step (step_normal f cont.halt v) c' →
      ∃ v₁ ∈ f.eval v,
      ∃ v₂ ∈ (if list.head v₁ = 0 then pure v₁.tail else f.fix.eval v₁.tail),
      x ∈ eval step (cfg.ret k v₂),
    { intro h,
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (step_normal_then _ cont.halt _ _) refl_trans_gen.refl,
      refine ⟨v₂, pfun.mem_fix_iff.2 _, h₃⟩,
      simp only [roption.eq_some_iff.2 hv₁, roption.map_some],
      split_ifs at hv₂ ⊢,
      { rw roption.mem_some_iff.1 hv₂, exact or.inl (roption.mem_some _) },
      { exact or.inr ⟨_, roption.mem_some _, hv₂⟩ } },
    refine λ c he, eval_induction he (λ y h IH, _),
    rintro v (⟨c,k',v'⟩ | ⟨k',v'⟩ | ⟨v'⟩) rfl hr; rw cfg.then at h IH,
    { rw reaches_eval at h, swap, exact refl_trans_gen.single rfl,
      exact IH _ h rfl _ _ (step_normal_then _ _ _ _) (refl_trans_gen.tail hr rfl) },
    { rw reaches_eval at h, swap, exact refl_trans_gen.single rfl,
      exact IH _ h rfl _ _ step_ret_then (refl_trans_gen.tail hr rfl) },
    { have := mem_eval.2 ⟨hr, rfl⟩,
      rw [fok, roption.bind_eq_bind, roption.mem_bind_iff] at this,
      obtain ⟨v'', h₁, h₂⟩ := this,
      rw reaches_eval at h₂, swap, exact refl_trans_gen.single rfl,
      cases roption.mem_unique h₂ (mem_eval.2 ⟨refl_trans_gen.refl, rfl⟩),
      refine ⟨v', h₁, _⟩, rw [step_ret] at h,
      revert h, by_cases he : v'.head = 0; simp only [exists_prop, if_pos, if_false, he]; intro h,
      { refine ⟨_, roption.mem_some _, _⟩,
        rw reaches_eval, exact h, exact refl_trans_gen.single rfl },
      { obtain ⟨k₀, v₀, e₀⟩ := step_normal.is_ret f cont.halt v'.tail,
        have e₁ := step_normal_then f cont.halt (cont.fix f k) v'.tail,
        rw [e₀, cont.then, cfg.then] at e₁,
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (step_ret (k₀.then (cont.fix f k)) v₀) _ _ v'.tail _ step_ret_then _,
        { refine ⟨_, pfun.mem_fix_iff.2 _, h₃⟩,
          simp only [roption.eq_some_iff.2 hv₁, roption.map_some, roption.mem_some_iff],
          split_ifs at hv₂ ⊢; [exact or.inl (roption.mem_some_iff.1 hv₂),
            exact or.inr ⟨_, rfl, hv₂⟩] },
        { rwa [← @reaches_eval _ _ (cfg.ret (k₀.then (cont.fix f k)) v₀), ← e₁],
          exact refl_trans_gen.single rfl },
        { rw [step_ret, if_neg he, e₁], refl },
        { apply refl_trans_gen.single, rw e₀, exact rfl } } } },
  { rintro ⟨v', he, hr⟩,
    rw reaches_eval at hr, swap, exact refl_trans_gen.single rfl,
    refine pfun.fix_induction he (λ v (he : v' ∈ f.fix.eval v) IH, _),
    rw [fok, roption.bind_eq_bind, roption.mem_bind_iff],
    obtain he | ⟨v'', he₁', he₂'⟩ := pfun.mem_fix_iff.1 he,
    { obtain ⟨v', he₁, he₂⟩ := (roption.mem_map_iff _).1 he, split_ifs at he₂; cases he₂,
      refine ⟨_, he₁, _⟩,
      rw reaches_eval, swap, exact refl_trans_gen.single rfl,
      rwa [step_ret, if_pos h] },
    { obtain ⟨v₁, he₁, he₂⟩ := (roption.mem_map_iff _).1 he₁', split_ifs at he₂; cases he₂,
      clear he₂ he₁', change _ ∈ f.fix.eval _ at he₂',
      refine ⟨_, he₁, _⟩,
      rw reaches_eval, swap, exact refl_trans_gen.single rfl,
      rwa [step_ret, if_neg h],
      exact IH v₁.tail he₂' ((roption.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩) } }
end

theorem code_is_ok (c) : code.ok c :=
begin
  induction c; intros k v; rw step_normal,
  iterate 3 { simp only [code.eval, pure_bind] },
  case code.cons : f fs IHf IHfs {
    rw [code.eval, IHf], -- swap, exact ⟨λ k' v, IHfs _, h⟩,
    simp only [bind_assoc, cont.eval, pure_bind], congr, funext v,
    rw [reaches_eval], swap, exact refl_trans_gen.single rfl,
    rw [step_ret, IHfs], congr, funext v',
    refine eq.trans _ (eq.symm _);
    try {exact reaches_eval (refl_trans_gen.single rfl)} },
  case code.comp : f g IHf IHg {
    rw [code.eval, IHg], -- swap, exact ⟨λ k' v, IHfs _, h⟩,
    simp only [bind_assoc, cont.eval, pure_bind], congr, funext v,
    rw [reaches_eval], swap, exact refl_trans_gen.single rfl,
    rw [step_ret, IHf] },
  case code.case : f g IHf IHg {
    simp only [code.eval], cases v.head; simp only [nat.elim, code.eval];
    [apply IHf, apply IHg] },
  case code.fix : f IHf { rw cont_eval_fix IHf },
end

theorem step_ret_eval {k v} : eval step (step_ret k v) = cfg.halt <$> k.eval v :=
begin
  induction k generalizing v,
  case cont.halt : {
    simp only [mem_eval, cont.eval, map_pure],
    exact roption.eq_some_iff.2 (mem_eval.2 ⟨refl_trans_gen.refl, rfl⟩) },
  case cont.cons₁ : fs as k IH {
    rw [cont.eval, step_ret, code_is_ok],
    simp only [← bind_pure_comp_eq_map, bind_assoc], congr, funext v',
    rw [reaches_eval], swap, exact refl_trans_gen.single rfl,
    rw [step_ret, IH, bind_pure_comp_eq_map] },
  case cont.cons₂ : ns k IH { rw [cont.eval, step_ret], exact IH },
  case cont.comp : f k IH {
    rw [cont.eval, step_ret, code_is_ok],
    simp only [← bind_pure_comp_eq_map, bind_assoc], congr, funext v',
    rw [reaches_eval], swap, exact refl_trans_gen.single rfl,
    rw [IH, bind_pure_comp_eq_map] },
  case cont.fix : f k IH {
    rw [cont.eval, step_ret], simp only [bind_pure_comp_eq_map],
    split_ifs, { exact IH },
    simp only [← bind_pure_comp_eq_map, bind_assoc, cont_eval_fix (code_is_ok _)],
    congr, funext, rw [bind_pure_comp_eq_map, ← IH],
    exact reaches_eval (refl_trans_gen.single rfl) },
end

end to_partrec

namespace partrec_to_TM2

section
open to_partrec

@[derive [decidable_eq, inhabited]]
inductive Γ'
| Cons
| cons
| bit0
| bit1

@[derive decidable_eq]
inductive K' | main | rev | aux | stack
open K'

inductive cont'
| halt
| cons₁ : code → cont' → cont'
| cons₂ : cont' → cont'
| comp : code → cont' → cont'
| fix : code → cont' → cont'

inductive Λ'
| move (p : Γ' → bool) (k₁ k₂ : K') (q : Λ')
| clear (p : Γ' → bool) (k : K') (q : Λ')
| copy (q : Λ')
| push (k : K') (s : option Γ' → option Γ') (q : Λ')
| read (f : option Γ' → Λ')
| succ (q : Λ')
| pred (q₁ q₂ : Λ')
| ret (k : cont')

def σ' := option Γ'

def stmt' := TM2.stmt (λ _:K', Γ') Λ' σ'
def cfg' := TM2.cfg (λ _:K', Γ') Λ' σ'

open TM2.stmt

def nat_end : Γ' → bool
| Γ'.Cons := tt
| Γ'.cons := tt
| _ := ff

local attribute [simp] def pop' (k : K') : stmt' → stmt' := pop k (λ x v, v)
local attribute [simp] def peek' (k : K') : stmt' → stmt' := peek k (λ x v, v)
local attribute [simp] def push' (k : K') : stmt' → stmt' := push k (λ x, x.iget)

def unrev := Λ'.move (λ _, ff) rev main

def move_excl (p k₁ k₂ q) :=
Λ'.move p k₁ k₂ $ Λ'.push k₁ id q

def move₂ (p k₁ k₂ q) := move_excl p k₁ rev $ Λ'.move (λ _, ff) rev k₂ q

def head (k : K') (q : Λ') : Λ' :=
Λ'.move nat_end k rev $
Λ'.push rev (λ _, some Γ'.cons) $
Λ'.read $ λ s,
(if s = some Γ'.Cons then id else Λ'.clear (λ x, x = Γ'.Cons) k) $
unrev q

local attribute [simp] def tr_normal : code → cont' → Λ'
| code.zero' k := Λ'.push main (λ _, some Γ'.cons) $ Λ'.ret k
| code.succ k := head main $ Λ'.succ $ Λ'.ret k
| code.tail k := Λ'.clear nat_end main $ Λ'.ret k
| (code.cons f fs) k :=
  Λ'.push stack (λ _, some Γ'.Cons) $
  Λ'.move (λ _, ff) main rev $ Λ'.copy $
  tr_normal f (cont'.cons₁ fs k)
| (code.comp f g) k := tr_normal g (cont'.comp f k)
| (code.case f g) k := Λ'.pred (tr_normal f k) (tr_normal g k)
| (code.fix f) k := tr_normal f (cont'.fix f k)

local attribute [simp] def tr : Λ' → stmt'
| (Λ'.move p k₁ k₂ q) :=
  pop' k₁ $ branch (λ s, s.elim tt p)
  ( goto $ λ _, q )
  ( push' k₂ $ goto $ λ _, Λ'.move p k₁ k₂ q )
| (Λ'.push k f q) :=
  branch (λ s, (f s).is_some)
  ( push k (λ s, (f s).iget) $ goto $ λ _, q )
  ( goto $ λ _, q )
| (Λ'.read q) := goto q
| (Λ'.clear p k q) :=
  pop' k $ branch (λ s, s.elim tt p)
  ( goto $ λ _, q )
  ( goto $ λ _, Λ'.clear p k q )
| (Λ'.copy q) :=
  pop' rev $ branch option.is_some
  ( push' main $ push' stack $ goto $ λ _, Λ'.copy q )
  ( goto $ λ _, q )
| (Λ'.succ q) :=
  pop' main $ branch (λ s, s = some Γ'.bit1)
  ( push rev (λ _, Γ'.bit0) $
    goto $ λ _, Λ'.succ q ) $
  branch (λ s, s = some Γ'.cons)
  ( push main (λ _, Γ'.cons) $
    push main (λ _, Γ'.bit1) $
    goto $ λ _, unrev q )
  ( push main (λ _, Γ'.bit1) $
    goto $ λ _, unrev q )
| (Λ'.pred q₁ q₂) :=
  pop' main $ branch (λ s, s = some Γ'.bit0)
  ( push rev (λ _, Γ'.bit1) $
    goto $ λ _, Λ'.pred q₁ q₂ ) $
  branch (λ s, nat_end s.iget)
  ( goto $ λ _, q₁ )
  ( peek' main $ branch (λ s, nat_end s.iget)
    ( goto $ λ _, unrev q₂ )
    ( push rev (λ _, Γ'.bit0) $
      goto $ λ _, unrev q₂ ) )
| (Λ'.ret (cont'.cons₁ fs k)) := goto $ λ _,
  move₂ (λ _, ff) main aux $
  move₂ (λ s, s = Γ'.Cons) stack main $
  move₂ (λ _, ff) aux stack $
  tr_normal fs (cont'.cons₂ k)
| (Λ'.ret (cont'.cons₂ k)) := goto $ λ _, head stack $ Λ'.ret k
| (Λ'.ret (cont'.comp f k)) := goto $ λ _, tr_normal f k
| (Λ'.ret (cont'.fix f k)) :=
  pop' main $ goto $ λ s,
  cond (nat_end s.iget) (Λ'.ret k) $
  Λ'.clear nat_end main $ tr_normal f (cont'.fix f k)
| (Λ'.ret cont'.halt) := halt

def tr_cont : cont → cont'
| cont.halt := cont'.halt
| (cont.cons₁ c _ k) := cont'.cons₁ c (tr_cont k)
| (cont.cons₂ _ k) := cont'.cons₂ (tr_cont k)
| (cont.comp c k) := cont'.comp c (tr_cont k)
| (cont.fix c k) := cont'.fix c (tr_cont k)

def tr_pos_num : pos_num → list Γ'
| pos_num.one := [Γ'.bit1]
| (pos_num.bit0 n) := Γ'.bit0 :: tr_pos_num n
| (pos_num.bit1 n) := Γ'.bit1 :: tr_pos_num n

def tr_num : num → list Γ'
| num.zero := []
| (num.pos n) := tr_pos_num n

def tr_nat (n : ℕ) : list Γ' := tr_num n

local attribute [simp] theorem tr_nat_zero : tr_nat 0 = [] := rfl

local attribute [simp] def tr_list : list ℕ → list Γ'
| [] := []
| (n :: ns) := tr_nat n ++ Γ'.cons :: tr_list ns

local attribute [simp] def tr_llist : list (list ℕ) → list Γ'
| [] := []
| (l :: ls) := tr_list l ++ Γ'.Cons :: tr_llist ls

local attribute [simp] def cont_stack : cont → list (list ℕ)
| cont.halt := []
| (cont.cons₁ _ ns k) := ns :: cont_stack k
| (cont.cons₂ ns k) := ns :: cont_stack k
| (cont.comp _ k) := cont_stack k
| (cont.fix _ k) := cont_stack k

def tr_cont_stack (k : cont) := tr_llist (cont_stack k)

local attribute [simp] def K'.elim (a b c d : list Γ') : K' → list Γ'
| K'.main := a
| K'.rev := b
| K'.aux := c
| K'.stack := d

local attribute [simp] theorem K'.elim_update_main {a b c d a'} :
  update (K'.elim a b c d) main a' = K'.elim a' b c d := by funext x; cases x; refl
local attribute [simp] theorem K'.elim_update_rev {a b c d b'} :
  update (K'.elim a b c d) rev b' = K'.elim a b' c d := by funext x; cases x; refl
local attribute [simp] theorem K'.elim_update_aux {a b c d c'} :
  update (K'.elim a b c d) aux c' = K'.elim a b c' d := by funext x; cases x; refl
local attribute [simp] theorem K'.elim_update_stack {a b c d d'} :
  update (K'.elim a b c d) stack d' = K'.elim a b c d' := by funext x; cases x; refl

def tr_cfg : cfg → cfg' → Prop
| (cfg.normal c k v) c' := ∃ s, c' =
  ⟨some (tr_normal c (tr_cont k)), s, K'.elim (tr_list v) [] [] (tr_cont_stack k)⟩
| (cfg.ret k v) c' := ∃ s, c' =
  ⟨some (Λ'.ret (tr_cont k)), s, K'.elim (tr_list v) [] [] (tr_cont_stack k)⟩
| (cfg.halt v) c' := ∃ s, c' = ⟨none, s, K'.elim (tr_list v) [] [] []⟩

local attribute [simp] TM2.step_aux TM2.step

def split_at_pred {α} (p : α → bool) : list α → list α × option α × list α
| [] := ([], none, [])
| (a :: as) := cond (p a) ([], some a, as) $
  let ⟨l₁, o, l₂⟩ := split_at_pred as in ⟨a :: l₁, o, l₂⟩

theorem split_at_pred_eq {α} (p : α → bool) : ∀ L l₁ o l₂,
  (∀ x ∈ l₁, p x = ff) →
  option.elim o (L = l₁ ∧ l₂ = []) (λ a, p a = tt ∧ L = l₁ ++ a :: l₂) →
  split_at_pred p L = (l₁, o, l₂)
| [] _ none _ _ ⟨rfl, rfl⟩ := rfl
| [] l₁ (some o) l₂ h₁ ⟨h₂, h₃⟩ := by simp at h₃; contradiction
| (a :: L) l₁ o l₂ h₁ h₂ := begin
    rw [split_at_pred],
    have IH := split_at_pred_eq L,
    cases o,
    { cases l₁ with a' l₁; rcases h₂ with ⟨⟨⟩, rfl⟩,
      rw [h₁ a (or.inl rfl), cond, IH L none [] _ ⟨rfl, rfl⟩], refl,
      exact λ x h, h₁ x (or.inr h) },
    { cases l₁ with a' l₁; rcases h₂ with ⟨h₂, ⟨⟩⟩, {rw [h₂, cond]},
      rw [h₁ a (or.inl rfl), cond, IH l₁ (some o) l₂ _ ⟨h₂, _⟩]; try {refl},
      exact λ x h, h₁ x (or.inr h) },
  end

theorem split_at_pred_ff {α} (L : list α) : split_at_pred (λ _, ff) L = (L, none, []) :=
split_at_pred_eq _ _ _ _ _ (λ _ _, rfl) ⟨rfl, rfl⟩

theorem move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → list Γ'}
  (h₁ : k₁ ≠ k₂) (e : split_at_pred p (S k₁) = (L₁, o, L₂)) :
  reaches₁ (TM2.step tr)
    ⟨some (Λ'.move p k₁ k₂ q), s, S⟩
    ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverse_core (S k₂))⟩ :=
begin
  induction L₁ with a L₁ IH generalizing S s,
  { rw [(_ : [].reverse_core _ = _), function.update_eq_self],
    swap, { rw function.update_noteq h₁.symm, refl },
    refine trans_gen.head' rfl _,
    simp, cases S k₁ with a Sk, {cases e, refl},
    simp [split_at_pred] at e ⊢,
    cases p a; simp at e ⊢,
    { revert e, rcases split_at_pred p Sk with ⟨_, _, _⟩, rintro ⟨⟩ },
    { simp only [e] } },
  { refine trans_gen.head rfl _, simp,
    cases e₁ : S k₁ with a' Sk; rw [e₁, split_at_pred] at e, {cases e},
    cases e₂ : p a'; simp only [e₂, cond] at e, swap, {cases e},
    rcases e₃ : split_at_pred p Sk with ⟨_, _, _⟩, rw [e₃, split_at_pred] at e, cases e,
    simp [e₂],
    convert @IH (update (update S k₁ Sk) k₂ (a :: S k₂)) _ _ using 2;
      simp [function.update_noteq, h₁, h₁.symm, e₃, list.reverse_core],
    simp [function.update_comm h₁.symm] }
end

theorem unrev_ok {q s} {S : K' → list Γ'} :
  reaches₁ (TM2.step tr) ⟨some (unrev q), s, S⟩
    ⟨some q, none, update (update S rev []) main (list.reverse_core (S rev) (S main))⟩ :=
move_ok dec_trivial $ split_at_pred_ff _

theorem move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → list Γ'}
  (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂) (h₂ : S rev = [])
  (e : split_at_pred p (S k₁) = (L₁, o, L₂)) :
  reaches₁ (TM2.step tr)
    ⟨some (move₂ p k₁ k₂ q), s, S⟩
    ⟨some q, none, update (update S k₁ (o.elim id list.cons L₂)) k₂ (L₁ ++ S k₂)⟩ :=
begin
  refine (move_ok h₁.1 e).trans (trans_gen.head rfl _),
  cases o; simp only [option.elim, tr, id.def],
  { convert move_ok h₁.2.1.symm (split_at_pred_ff _) using 2,
    simp only [function.update_comm h₁.1, function.update_idem],
    rw show update S rev [] = S, by rw [← h₂, function.update_eq_self],
    simp only [function.update_noteq h₁.2.2.symm, function.update_noteq h₁.2.1,
      function.update_noteq h₁.1.symm, list.reverse_core_eq, h₂,
      function.update_same, list.append_nil, list.reverse_reverse] },
  { convert move_ok h₁.2.1.symm (split_at_pred_ff _) using 2,
    simp only [h₂, function.update_comm h₁.1,
      list.reverse_core_eq, function.update_same, list.append_nil, function.update_idem],
    rw show update S rev [] = S, by rw [← h₂, function.update_eq_self],
    simp only [function.update_noteq h₁.1.symm,
      function.update_noteq h₁.2.2.symm, function.update_noteq h₁.2.1,
      function.update_same, list.reverse_reverse] },
end

theorem clear_ok {p k q s L₁ o L₂} {S : K' → list Γ'}
  (e : split_at_pred p (S k) = (L₁, o, L₂)) :
  reaches₁ (TM2.step tr) ⟨some (Λ'.clear p k q), s, S⟩ ⟨some q, o, update S k L₂⟩ :=
begin
  induction L₁ with a L₁ IH generalizing S s,
  { refine trans_gen.head' rfl _,
    simp, cases S k with a Sk, {cases e, refl},
    simp [split_at_pred] at e ⊢,
    cases p a; simp at e ⊢,
    { revert e, rcases split_at_pred p Sk with ⟨_, _, _⟩, rintro ⟨⟩ },
    { simp only [e] } },
  { refine trans_gen.head rfl _, simp,
    cases e₁ : S k with a' Sk; rw [e₁, split_at_pred] at e, {cases e},
    cases e₂ : p a'; simp only [e₂, cond] at e, swap, {cases e},
    rcases e₃ : split_at_pred p Sk with ⟨_, _, _⟩, rw [e₃, split_at_pred] at e, cases e,
    simp [e₂],
    convert @IH (update S k Sk) _ _ using 2; simp [e₃] }
end

theorem copy_ok (q s a b c d) :
  reaches₁ (TM2.step tr)
    ⟨some (Λ'.copy q), s, K'.elim a b c d⟩
    ⟨some q, none, K'.elim (list.reverse_core b a) [] c (list.reverse_core b d)⟩ :=
begin
  induction b with x b IH generalizing a d s,
  { refine trans_gen.single _, simp, refl },
  refine trans_gen.head rfl _, simp, exact IH _ _ _,
end

theorem tr_pos_num_nat_end : ∀ n (x ∈ tr_pos_num n), nat_end x = ff
| pos_num.one _ (or.inl rfl) := rfl
| (pos_num.bit0 n) _ (or.inl rfl) := rfl
| (pos_num.bit0 n) _ (or.inr h) := tr_pos_num_nat_end n _ h
| (pos_num.bit1 n) _ (or.inl rfl) := rfl
| (pos_num.bit1 n) _ (or.inr h) := tr_pos_num_nat_end n _ h

theorem tr_num_nat_end : ∀ n (x ∈ tr_num n), nat_end x = ff
| (num.pos n) x h := tr_pos_num_nat_end n x h

theorem tr_nat_nat_end (n) : ∀ x ∈ tr_nat n, nat_end x = ff := tr_num_nat_end _

theorem tr_list_ne_Cons : ∀ l (x ∈ tr_list l), x ≠ Γ'.Cons
| (a :: l) x h := begin
  simp [tr_list] at h,
  obtain h | rfl | h := h,
  { rintro rfl, cases tr_nat_nat_end _ _ h },
  { rintro ⟨⟩ },
  { exact tr_list_ne_Cons l _ h }
end

theorem head_main_ok {q s L} {c d : list Γ'} :
  reaches₁ (TM2.step tr)
    ⟨some (head main q), s, K'.elim (tr_list L) [] c d⟩
    ⟨some q, none, K'.elim (tr_list [L.head]) [] c d⟩ :=
begin
  let o : option Γ' := list.cases_on L none (λ _ _, some Γ'.cons),
  refine (move_ok dec_trivial
    (split_at_pred_eq _ _ (tr_nat L.head) o (tr_list L.tail) (tr_nat_nat_end _) _)).trans
    (trans_gen.head rfl (trans_gen.head rfl _)),
  { cases L; exact ⟨rfl, rfl⟩ },
  simp [show o ≠ some Γ'.Cons, by cases L; rintro ⟨⟩],
  refine (clear_ok (split_at_pred_eq _ _ _ none [] _ ⟨rfl, rfl⟩)).trans _,
  { exact λ x h, (to_bool_ff (tr_list_ne_Cons _ _ h)) },
  convert unrev_ok, simp [list.reverse_core_eq],
end

theorem head_stack_ok {q s L₁ L₂ L₃} :
  reaches₁ (TM2.step tr)
    ⟨some (head stack q), s, K'.elim (tr_list L₁) [] [] (tr_list L₂ ++ Γ'.Cons :: L₃)⟩
    ⟨some q, none, K'.elim (tr_list (L₂.head :: L₁)) [] [] L₃⟩ :=
begin
  cases L₂ with a L₂,
  { refine trans_gen.trans (move_ok dec_trivial
      (split_at_pred_eq _ _ [] (some Γ'.Cons) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
      (trans_gen.head rfl (trans_gen.head rfl _)),
    convert unrev_ok, simp, refl },
  { refine trans_gen.trans (move_ok dec_trivial
      (split_at_pred_eq _ _ (tr_nat a) (some Γ'.cons)
        (tr_list L₂ ++ Γ'.Cons :: L₃) (tr_nat_nat_end _) ⟨rfl, by simp⟩))
      (trans_gen.head rfl (trans_gen.head rfl _)),
    simp,
    refine trans_gen.trans (clear_ok
      (split_at_pred_eq _ _ (tr_list L₂) (some Γ'.Cons) L₃
        (λ x h, (to_bool_ff (tr_list_ne_Cons _ _ h))) ⟨rfl, by simp⟩)) _,
    convert unrev_ok, simp [list.reverse_core_eq] },
end

theorem succ_ok {q s n} {c d : list Γ'} :
  reaches₁ (TM2.step tr)
    ⟨some (Λ'.succ q), s, K'.elim (tr_list [n]) [] c d⟩
    ⟨some q, none, K'.elim (tr_list [n.succ]) [] c d⟩ :=
begin
  simp [tr_nat, num.add_one],
  cases (n:num),
  { refine trans_gen.head rfl _, simp,
    rw if_neg, swap, rintro ⟨⟩, rw if_pos, swap, refl,
    convert unrev_ok, simp, refl },
  simp [num.succ, tr_num, num.succ'],
  suffices : ∀ l₁,
    ∃ l₁' l₂' s', list.reverse_core l₁ (tr_pos_num a.succ) = list.reverse_core l₁' l₂' ∧
    reaches₁ (TM2.step tr)
      ⟨some q.succ, s, K'.elim (tr_pos_num a ++ [Γ'.cons]) l₁ c d⟩
      ⟨some (unrev q), s', K'.elim (l₂' ++ [Γ'.cons]) l₁' c d⟩,
  { obtain ⟨l₁', l₂', s', e, h⟩ := this [], simp [list.reverse_core] at e,
    refine h.trans _, convert unrev_ok using 2, simp [e, list.reverse_core_eq] },
  induction a with m IH m IH generalizing s; intro l₁,
  { refine ⟨Γ'.bit0 :: l₁, [Γ'.bit1], some Γ'.cons, rfl, trans_gen.head rfl (trans_gen.single _)⟩,
    simp [tr_pos_num], refl },
  { obtain ⟨l₁', l₂', s', e, h⟩ := IH (Γ'.bit0 :: l₁),
    refine ⟨l₁', l₂', s', e, trans_gen.head _ h⟩, swap,
    simp [pos_num.succ, tr_pos_num] },
  { refine ⟨l₁, _, some Γ'.bit0, rfl, trans_gen.single _⟩, simp, refl },
end

theorem pred_ok (q₁ q₂ s v) (c d : list Γ') :
  ∃ s', reaches₁ (TM2.step tr)
    ⟨some (Λ'.pred q₁ q₂), s, K'.elim (tr_list v) [] c d⟩
    (v.head.elim
      ⟨some q₁, s', K'.elim (tr_list v.tail) [] c d⟩
      (λ n _, ⟨some q₂, s', K'.elim (tr_list (n :: v.tail)) [] c d⟩)) :=
begin
  rcases v with _|⟨_|n, v⟩,
  { refine ⟨none, trans_gen.single _⟩, simp, refl },
  { refine ⟨some Γ'.cons, trans_gen.single _⟩, simp, refl },
  refine ⟨none, _⟩, simp [tr_nat, num.add_one, num.succ, tr_num],
  cases (n:num),
  { simp [tr_pos_num, tr_num, show num.zero.succ' = pos_num.one, from rfl],
    refine trans_gen.head rfl _, convert unrev_ok, simp, refl },
  simp [tr_num, num.succ'],
  suffices : ∀ l₁,
    ∃ l₁' l₂' s', list.reverse_core l₁ (tr_pos_num a) = list.reverse_core l₁' l₂' ∧
    reaches₁ (TM2.step tr)
      ⟨some (q₁.pred q₂), s, K'.elim (tr_pos_num a.succ ++ Γ'.cons :: tr_list v) l₁ c d⟩
      ⟨some (unrev q₂), s', K'.elim (l₂' ++ Γ'.cons :: tr_list v) l₁' c d⟩,
  { obtain ⟨l₁', l₂', s', e, h⟩ := this [], simp [list.reverse_core] at e,
    refine h.trans _, convert unrev_ok using 2, simp [e, list.reverse_core_eq] },
  induction a with m IH m IH generalizing s; intro l₁,
  { refine ⟨Γ'.bit1 :: l₁, [], some Γ'.cons, rfl, trans_gen.head rfl (trans_gen.single _)⟩,
    simp [tr_pos_num, show pos_num.one.succ = pos_num.one.bit0, from rfl], refl },
  { obtain ⟨l₁', l₂', s', e, h⟩ := IH (some Γ'.bit0) (Γ'.bit1 :: l₁),
    refine ⟨l₁', l₂', s', e, trans_gen.head _ h⟩, simp, refl },
  { obtain ⟨a, l, e, h⟩ : ∃ a l, tr_pos_num m = a :: l ∧ nat_end a = ff,
    { cases m; refine ⟨_, _, rfl, rfl⟩ },
    refine ⟨Γ'.bit0 :: l₁, _, some a, rfl, trans_gen.single _⟩,
    simp [tr_pos_num, pos_num.succ, e, h, nat_end,
      show some Γ'.bit1 ≠ some Γ'.bit0, from dec_trivial] },
end

theorem tr_normal_respects (c k v s) : ∃ b₂, tr_cfg (step_normal c k v) b₂ ∧
  reaches₁ (TM2.step tr)
    ⟨some (tr_normal c (tr_cont k)), s, K'.elim (tr_list v) [] [] (tr_cont_stack k)⟩ b₂ :=
begin
  induction c generalizing k v s,
  case zero': { refine ⟨_, ⟨s, rfl⟩, trans_gen.single _⟩, simp },
  case succ: { refine ⟨_, ⟨none, rfl⟩, head_main_ok.trans succ_ok⟩ },
  case tail: {
    let o : option Γ' := list.cases_on v none (λ _ _, some Γ'.cons),
    refine ⟨_, ⟨o, rfl⟩, _⟩, convert clear_ok _, simp, swap,
    refine split_at_pred_eq _ _ (tr_nat v.head) _ _ (tr_nat_nat_end _) _,
    cases v; exact ⟨rfl, rfl⟩ },
  case cons: f fs IHf IHfs {
    obtain ⟨c, h₁, h₂⟩ := IHf (cont.cons₁ fs v k) v none,
    refine ⟨c, h₁, trans_gen.head rfl $ (move_ok dec_trivial (split_at_pred_ff _)).trans _⟩,
    simp [step_normal],
    refine (copy_ok _ none [] (tr_list v).reverse _ _).trans _,
    convert h₂ using 2,
    simp [list.reverse_core_eq, tr_cont_stack] },
  case comp: f g IHf IHg { exact IHg (cont.comp f k) v s },
  case case: f g IHf IHg {
    rw step_normal,
    obtain ⟨s', h⟩ := pred_ok _ _ s v _ _,
    cases v.head with n,
    { obtain ⟨c, h₁, h₂⟩ := IHf k _ s', exact ⟨_, h₁, h.trans h₂⟩ },
    { obtain ⟨c, h₁, h₂⟩ := IHg k _ s', exact ⟨_, h₁, h.trans h₂⟩ } },
  case fix: f IH { apply IH }
end

theorem tr_ret_respects (k v s) : ∃ b₂, tr_cfg (step_ret k v) b₂ ∧
  reaches₁ (TM2.step tr)
    ⟨some (Λ'.ret (tr_cont k)), s, K'.elim (tr_list v) [] [] (tr_cont_stack k)⟩ b₂ :=
begin
  induction k generalizing v s,
  case halt: { exact ⟨_, ⟨s, rfl⟩, trans_gen.single rfl⟩ },
  case cons₁: fs as k IH {
    obtain ⟨s', h₁, h₂⟩ := tr_normal_respects fs (cont.cons₂ v k) as none,
    refine ⟨s', h₁, trans_gen.head rfl _⟩, simp,
    refine (move₂_ok dec_trivial _ (split_at_pred_ff _)).trans _, {refl}, simp,
    refine (move₂_ok dec_trivial _ _).trans _, swap 4, {refl},
    swap 4, {exact (split_at_pred_eq _ _ _ (some Γ'.Cons) _
      (λ x h, to_bool_ff (tr_list_ne_Cons _ _ h)) ⟨rfl, rfl⟩)},
    refine (move₂_ok dec_trivial _ (split_at_pred_ff _)).trans _, {refl}, simp,
    exact h₂ },
  case cons₂: ns k IH {
    obtain ⟨c, h₁, h₂⟩ := IH (ns.head :: v) none,
    exact ⟨c, h₁, trans_gen.head rfl $ head_stack_ok.trans h₂⟩ },
  case comp: f k IH {
    obtain ⟨s', h₁, h₂⟩ := tr_normal_respects f k v s,
    exact ⟨_, h₁, trans_gen.head rfl h₂⟩ },
  case fix: f k IH {
    rw [step_ret],
    have : if v.head = 0
      then nat_end (tr_list v).head'.iget = tt ∧ (tr_list v).tail = tr_list v.tail
      else nat_end (tr_list v).head'.iget = ff ∧
        (tr_list v).tail = (tr_nat v.head).tail ++ Γ'.cons :: tr_list v.tail,
    { cases v with n, {exact ⟨rfl, rfl⟩}, cases n, {exact ⟨rfl, rfl⟩},
      rw [tr_list, list.head, tr_nat, nat.cast_succ, num.add_one, num.succ, list.tail],
      cases (n:num).succ'; exact ⟨rfl, rfl⟩ },
    by_cases v.head = 0; simp [h] at this ⊢,
    { obtain ⟨c, h₁, h₂⟩ := IH v.tail (tr_list v).head',
      refine ⟨c, h₁, trans_gen.head rfl _⟩,
      simp [tr_cont, tr_cont_stack, this], exact h₂ },
    { obtain ⟨s', h₁, h₂⟩ := tr_normal_respects f (cont.fix f k) v.tail (some Γ'.cons),
      refine ⟨_, h₁, trans_gen.head rfl $ trans_gen.trans _ h₂⟩,
      swap 3, simp [tr_cont, this.1],
      convert clear_ok (split_at_pred_eq _ _ (tr_nat v.head).tail (some Γ'.cons) _ _ _) using 2,
      { simp },
      { exact λ x h, tr_nat_nat_end _ _ (list.tail_subset _ h) },
      { exact ⟨rfl, this.2⟩ } } },
end

theorem tr_respects : respects step (TM2.step tr) tr_cfg
| (cfg.normal c k v) _ ⟨s, rfl⟩ := tr_normal_respects _ _ _ _
| (cfg.ret k v) _ ⟨s, rfl⟩ := tr_ret_respects _ _ _
| (cfg.halt v) _ ⟨s, rfl⟩ := rfl

end

end partrec_to_TM2

end turing
