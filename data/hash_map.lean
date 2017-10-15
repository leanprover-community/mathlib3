/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.list.basic data.pnat data.array.lemmas

universes u v w

def bucket_array (α : Type u) (β : α → Type v) (n : ℕ+) :=
array (list Σ a, β a) n.1

def hash_map.mk_idx (n : ℕ+) (i : nat) : fin n.1 :=
⟨i % n.1, nat.mod_lt _ n.2⟩

namespace bucket_array
section
parameters {α : Type u} {β : α → Type v} (hash_fn : α → nat)
variables {n : ℕ+} (data : bucket_array α β n)

def read (a : α) : list Σ a, β a :=
let bidx := hash_map.mk_idx n (hash_fn a) in
data.read bidx

def write (hash_fn : α → nat) (a : α) (l : list Σ a, β a) : bucket_array α β n :=
let bidx := hash_map.mk_idx n (hash_fn a) in
data.write bidx l

def modify (hash_fn : α → nat) (a : α) (f : list (Σ a, β a) → list (Σ a, β a)) : bucket_array α β n :=
let bidx := hash_map.mk_idx n (hash_fn a) in
array.write data bidx (f (array.read data bidx))

def as_list : list Σ a, β a :=
data.foldl [] (λbkt r, r ++ bkt)

theorem mem_as_list {a : Σ a, β a} : a ∈ data.as_list ↔ ∃i, a ∈ array.read data i :=
suffices ∀j h, a ∈ array.iterate_aux data (λ_ bkt r, r ++ bkt) j h [] ↔
  ∃ (i : fin n.1), i.1 < j ∧ a ∈ array.read data i, from
(this _ _).trans (exists_congr $ λi, and_iff_right i.2),
begin
  intros, induction j with j IH,
  { exact ⟨false.elim, λ⟨i, h, _⟩, absurd h (nat.not_lt_zero _)⟩ },
  { suffices : a ∈ array.read data ⟨j, h⟩ ∨ (∃ (i : fin (n.val)), i.val < j ∧ a ∈ array.read data i) ↔
      ∃ (i : fin (n.val)), i.val ≤ j ∧ a ∈ array.read data i,
    { simpa [array.iterate_aux, nat.lt_succ_iff, IH (le_of_lt h)] },
    exact ⟨λo, or.elim o
      (λm, ⟨⟨j, h⟩, nat.le_refl _, m⟩)
      (λ⟨i, il, im⟩, ⟨i, le_of_lt il, im⟩),
    λ⟨i, le, m⟩, (lt_or_eq_of_le le).elim
      (λl, or.inr ⟨i, l, m⟩)
      (λe, or.inl $ by rwa [← show i = ⟨j, h⟩, from fin.eq_of_veq e])⟩ }
end

def foldl {δ : Type w} (d : δ) (f : δ → Π a, β a → δ) : δ :=
data.foldl d (λ b d, b.foldl (λ r a, f r a.1 a.2) d)

theorem foldl_eq_lem {γ : Type u} {δ : Type w} (d : δ) (f : δ → γ → δ) : Π l : list (list γ),
  l.foldr (λ (b:list γ) d, b.foldl f d) d = (l.foldr (λ(bkt r : list γ), r ++ bkt) []).foldl f d
| []      := rfl
| (l::ls) := show l.foldl f (ls.foldr (λ (b:list γ) d, b.foldl f d) d) =
  (ls.foldr (λ (bkt r : list γ), r ++ bkt) [] ++ l).foldl f d, by rw [list.append_foldl, foldl_eq_lem ls]

theorem foldl_eq {δ : Type w} (d : δ) (f : δ → Π a, β a → δ) :
  data.foldl d f = data.as_list.foldl (λ r a, f r a.1 a.2) d :=
let f' : δ → (Σ a, β a) → δ := λ r a, f r a.1 a.2 in
let g : list (Σ a, β a) → δ → δ := λ b d, b.foldl f' d in
calc array.foldl data d g = data.rev_list.foldr g d : data.foldl_eq d g
   ... = (data.rev_list.foldr (λ(bkt r : list (Σa, β a)), r ++ bkt) []).foldl f' d : foldl_eq_lem _ _ _
   ... = (array.foldl data [] (λbkt r, r ++ bkt)).foldl f' d : by rw array.foldl_eq data [] (λbkt r, r ++ bkt)
end
end bucket_array

namespace hash_map
section
parameters {α : Type u} {β : α → Type v} (hash_fn : α → nat)

def reinsert_aux {n} (data : bucket_array α β n) (a : α) (b : β a) : bucket_array α β n :=
data.modify hash_fn a (λl, ⟨a, b⟩ :: l)

parameter [decidable_eq α]

def find_aux (a : α) : list (Σ a, β a) → option (β a)
| []          := none
| (⟨a',b⟩::t) := if h : a' = a then some (eq.rec_on h b) else find_aux t

theorem find_aux_iff {a : α} {b : β a} : Π {l : list Σ a, β a}, (l.map sigma.fst).nodup → (find_aux a l = some b ↔ sigma.mk a b ∈ l)
| []          nd := ⟨λn, by injection n, false.elim⟩
| (⟨a',b'⟩::t) nd := begin
  by_cases a' = a,
  { clear find_aux_iff, subst h,
    suffices : b' = b ↔ b' = b ∨ sigma.mk a' b ∈ t, {simpa [find_aux, eq_comm]},
    refine (or_iff_left_of_imp (λ m, _)).symm,
    have : a' ∉ t.map sigma.fst, from list.not_mem_of_nodup_cons nd,
    exact this.elim (list.mem_map_of_mem _ m) },
  { have : sigma.mk a b ≠ ⟨a', b'⟩,
    { intro e, injection e with e, exact h e.symm },
    simp at nd, simp [find_aux, h, ne.symm h, find_aux_iff, nd] }
end

def contains_aux (a : α) (l : list Σ a, β a) : bool :=
(find_aux a l).is_some

theorem contains_aux_iff {a : α} {l : list Σ a, β a} (nd : (l.map sigma.fst).nodup) : contains_aux a l ↔ a ∈ l.map sigma.fst :=
begin
  unfold contains_aux,
  cases h : find_aux a l with b; simp [option.is_some],
  { assume (b : β a) (m : sigma.mk a b ∈ l),
    rw (find_aux_iff nd).2 m at h,
    contradiction },
  { show ∃ (b : β a), sigma.mk a b ∈ l,
    exact ⟨_, (find_aux_iff nd).1 h⟩ },
end

def replace_aux (a : α) (b : β a) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then ⟨a, b⟩::t else ⟨a', b'⟩ :: replace_aux t

def erase_aux (a : α) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then t else ⟨a', b'⟩ :: erase_aux t

inductive valid_aux {α : Type u} {β : α → Type v} (idx : α → nat) : Π (l : list (list Σ a, β a)) (sz : nat), Prop
| nil {} : valid_aux [] 0
| cons : Π (c : list Σ a, β a) {l sz}, valid_aux l sz → (c.map sigma.fst).nodup →
  (∀ a ∈ c, idx (sigma.fst a) = l.length) → valid_aux (c::l) (sz + c.length)

theorem valid_aux.unfold_cons {idx : α → nat} : Π {c l sz}, valid_aux idx (c::l) sz →
  ∃ sz', valid_aux idx l sz' ∧ (c.map sigma.fst).nodup ∧ (∀ a ∈ c, idx (sigma.fst a) = l.length) ∧ sz = sz' + c.length
| ._ ._ ._ (@valid_aux.cons ._ ._ ._ c l sz' v nd e) := ⟨sz', v, nd, e, rfl⟩

theorem valid_aux.nodup {idx : α → nat} : Π {l : list (list Σ a, β a)} {sz : nat}, valid_aux idx l sz →
  ∀ ⦃c : list Σ a, β a⦄, c ∈ l → (c.map sigma.fst).nodup
| ._ ._ valid_aux.nil                            c' cl := false.elim cl
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) c' cl := or.elim cl (λe, by rwa e) (λm : c' ∈ l, valid_aux.nodup v m)

theorem valid_aux.eq {idx : α → nat} : Π {l : list (list Σ a, β a)} {sz : nat}, valid_aux idx l sz →
  ∀ {i h a b}, sigma.mk a b ∈ l.nth_le i h → idx a = l.length - 1 - i
| ._ ._ valid_aux.nil                            i     h _ _ _  := absurd h (nat.not_lt_zero _)
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) 0     h a b el := e ⟨a, b⟩ el
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) (i+1) h a b el :=
  have idx a = list.length l - 1 - i, from valid_aux.eq v el,
  by rwa [nat.sub_sub, nat.add_comm] at this

private lemma valid_aux.insert_lemma1 {idx : α → nat} : Π {l : list (list Σ a, β a)} {sz : nat}, valid_aux idx l sz →
  ∀ {i h a b}, sigma.mk a b ∈ l.nth_le i h → idx a = l.length - 1 - i
| ._ ._ valid_aux.nil                            i     h _ _ _  := absurd h (nat.not_lt_zero _)
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) 0     h a b el := e ⟨a, b⟩ el
| ._ ._ (@valid_aux.cons ._ ._ ._ c l sz v nd e) (i+1) h a b el :=
  have idx a = list.length l - 1 - i, from valid_aux.eq v el,
  by rwa [nat.sub_sub, nat.add_comm] at this

def valid {n} (bkts : bucket_array α β n) (sz : nat) : Prop :=
valid_aux (λa, (mk_idx n (hash_fn a)).1) bkts.rev_list sz

theorem valid.nodup {n} {bkts : bucket_array α β n} {sz : nat} : valid bkts sz → ∀i, ((array.read bkts i).map sigma.fst).nodup :=
λv i, valid_aux.nodup v ((bkts.mem_iff_rev_list_mem _).1 (bkts.read_mem i))

theorem valid.eq {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz)
 {i h a b} (el : sigma.mk a b ∈ array.read bkts ⟨i, h⟩) : (mk_idx n (hash_fn a)).1 = i :=
begin
  have v : valid_aux (λa, (mk_idx n (hash_fn a)).1) (array.to_list bkts).reverse sz,
  { rw array.to_list_reverse, exact v },
  have : sigma.mk a b ∈ list.nth_le (array.to_list bkts) i (by simp [*, array.to_list_length]),
  { rw array.to_list_nth, exact el },
  rw [← list.nth_le_reverse bkts.to_list i
    (by simp [*, array.to_list_length, nat.sub_one_sub_lt])] at this,
  apply (v.eq this).trans,
  have : i ≤ list.length (array.to_list bkts) - 1,
  { simpa [array.to_list_length] using nat.pred_le_pred h },
  simp [nat.sub_sub_self this]
end

theorem valid.eq' {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz)
 {i a b} (el : sigma.mk a b ∈ array.read bkts i) : mk_idx n (hash_fn a) = i :=
fin.eq_of_veq (match i, el with ⟨j, h⟩, el := v.eq _ el end)

theorem valid.as_list_nodup {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) : (bkts.as_list.map sigma.fst).nodup :=
suffices ∀i h, ((bkts.iterate_aux (λ _ bkt r, r ++ bkt) i h []).map sigma.fst).nodup ∧
  ∀ a b, sigma.mk a b ∈ bkts.iterate_aux (λ _ bkt r, r ++ bkt) i h [] → (mk_idx n (hash_fn a)).1 < i,
from (this n.1 (le_refl _)).left, begin
  intros, induction i with i IH,
  { exact ⟨list.nodup_nil, λ_ _, false.elim⟩ },
  { cases IH (le_of_lt h) with nd al,
    suffices : ∀ (a : α) (b : β a),
      (∀ (m1 : sigma.mk a b ∈ bkts.iterate_aux (λ _ bkt r, r ++ bkt) i _ [])
         (b' : β a), sigma.mk a b' ∉ array.read bkts ⟨i, h⟩) ∧
      (sigma.mk a b ∈ array.read bkts ⟨i, h⟩ ∨
       sigma.mk a b ∈ bkts.iterate_aux (λ _ bkt r, r ++ bkt) i _ [] →
       (mk_idx n (hash_fn a)).val ≤ i),
    { simpa [array.iterate_aux, list.nodup_append, nd, v.nodup _ _,
             nat.lt_succ_iff, list.disjoint, forall_and_distrib.symm] },
    refine λ a b, ⟨λ m1 b' m2, _,
      λ m, m.elim (λ m2, _) (λ m1, le_of_lt (al _ _ m1))⟩,
    { have hlt := al a b m1,
      rw v.eq _ m2 at hlt,
      exact lt_irrefl _ hlt },
    { rw v.eq _ m2 } }
end

theorem valid.as_list_length {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) : bkts.as_list.length = sz :=
have ∀ l sz, valid_aux (λ (a : α), (mk_idx n (hash_fn a)).val) l sz → ∀t, (l.foldr (λbkt r, r ++ bkt) t).length = sz + t.length,
by intros; induction a; simp [list.foldr, *],
by simpa [(array.foldl_eq _ _ _).symm] using this _ _ v []

theorem valid.mk (n : ℕ+) : @valid n (mk_array n.1 []) 0 :=
let bkts : bucket_array α β n := mk_array n.1 [] in
suffices ∀ i (h : i ≤ n.1), valid_aux (λa, (mk_idx n (hash_fn a)).1) (bkts.iterate_aux (λ_ v l, v :: l) i h []) 0,
from this _ (le_refl _), begin
  intros, induction i with i IH,
  { exact valid_aux.nil },
  { exact valid_aux.cons _ (IH (le_of_lt h)) list.nodup_nil (λ_, false.elim) }
end

theorem valid.find_aux_iff {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) (a : α) (b : β a) :
  find_aux a (bkts.read hash_fn a) = some b ↔ sigma.mk a b ∈ bkts.as_list :=
(find_aux_iff (v.nodup _ _)).trans $
  iff.trans (by exact ⟨λm, ⟨_, m⟩, λ⟨⟨i, h⟩, m⟩, let h := v.eq' _ m in by rwa [←h] at m⟩)
    bkts.mem_as_list.symm

theorem valid.contains_aux_iff {n} {bkts : bucket_array α β n} {sz : nat} (v : valid bkts sz) (a : α) :
  contains_aux a (bkts.read hash_fn a) ↔ a ∈ bkts.as_list.map sigma.fst :=
begin
  unfold contains_aux,
  cases h : find_aux a (bkts.read hash_fn a) with b,
  { refine ⟨λn, by contradiction, _⟩,
    suffices : ∀ (b : β a), sigma.mk a b ∈ bkts.as_list → _, {simpa},
    intros b m, rw (v.find_aux_iff _ a b).2 m at h, contradiction },
  { exact ⟨λ_, list.mem_map_of_mem _ ((v.find_aux_iff _ a b).1 h), λ_, dec_trivial⟩ }
end

theorem mk_as_list (n : ℕ+) : bucket_array.as_list (mk_array n.1 [] : bucket_array α β n) = [] :=
list.eq_nil_of_length_eq_zero ((valid.mk n).as_list_length _)

section
  parameters {n : ℕ+} {bkts : bucket_array α β n}
             {bidx : fin n.1} {f : list (Σ a, β a) → list (Σ a, β a)}
             (u v1 v2 w : list Σ a, β a)

  local notation `L` := array.read bkts bidx
  private def bkts' : bucket_array α β n := array.write bkts bidx (f L)

  private lemma valid.modify_aux1 {δ fn} {b : δ} : Π (i) (h : i ≤ n.1) (hb : i ≤ bidx.1),
    array.iterate_aux bkts fn i h b = array.iterate_aux bkts' fn i h b
  | 0     h hb := by simp [array.iterate_aux]
  | (i+1) h (hb : i < bidx.1) := begin
    have : array.read bkts ⟨i, h⟩ = array.read bkts' ⟨i, h⟩,
    { have bn : bidx ≠ ⟨i, h⟩ := λhh, ne_of_lt hb $ fin.veq_of_eq $ eq.symm hh,
      unfold bkts', rw array.read_write_ne _ _ _ _ bn },
    simp [array.iterate_aux, valid.modify_aux1 i (le_of_lt h) (le_of_lt hb), this]
  end

  variables (hl : L = u ++ v1 ++ w)
            (hfl : f L = u ++ v2 ++ w)
  include hl hfl

  private lemma append_of_modify_aux : Π (i) (h : i ≤ n.1) (hb : i > bidx.1),
    ∃ u' w', bkts.iterate_aux (λ_ bkt r, r ++ bkt) i h [] = u' ++ v1 ++ w' ∧
             bkts'.iterate_aux (λ_ bkt r, r ++ bkt) i h [] = u' ++ v2 ++ w'
  | 0     _ hb := (nat.not_lt_zero _).elim hb
  | (i+1) h hb := begin
    cases lt_or_eq_of_le (nat.le_of_succ_le_succ hb) with hl e,
    { have bn : bidx ≠ ⟨i, h⟩ := λhh, ne_of_gt hl $ fin.veq_of_eq $ eq.symm hh,
      have he : array.read bkts' ⟨i, h⟩ = array.read bkts ⟨i, h⟩,
      { unfold bkts', rw array.read_write_ne _ _ _ _ bn },
      dsimp [array.iterate_aux], rw he,
      rcases append_of_modify_aux i (le_of_lt h) hl with ⟨u', w', hb, hb'⟩,
      exact ⟨u', w' ++ array.read bkts ⟨i, h⟩, by simp [hb], by simp [hb']⟩ },
    { subst i, dsimp [array.iterate_aux],
      refine ⟨bkts.iterate_aux (λ_ bkt r, r ++ bkt) bidx.1 (le_of_lt h) [] ++ u, w, _⟩,
      rw [← show bidx = ⟨bidx.1, h⟩, from fin.eq_of_veq rfl,
          show array.read bkts' bidx = f L, by apply array.read_write_eq,
          ← valid.modify_aux1 _ _ (le_refl _), hfl, hl],
      simp }
  end

  theorem append_of_modify : ∃ u' w', bkts.as_list = u' ++ v1 ++ w' ∧ bkts'.as_list = u' ++ v2 ++ w' :=
  append_of_modify_aux hl hfl _ _ bidx.2

  variables (hvnd : (v2.map sigma.fst).nodup)
            (hal : ∀ (a : Σ a, β a), a ∈ v2 → mk_idx n (hash_fn a.1) = bidx)
            (djuv : (u.map sigma.fst).disjoint (v2.map sigma.fst))
            (djwv : (w.map sigma.fst).disjoint (v2.map sigma.fst))
  include hvnd hal djuv djwv

  private lemma valid.modify_aux2 : Π (i) (h : i ≤ n.1) (hb : i > bidx.1) {sz : ℕ},
    valid_aux (λa, (mk_idx n (hash_fn a)).1) (array.iterate_aux bkts (λ_ v l, v :: l) i h []) sz → sz + v2.length ≥ v1.length ∧
    valid_aux (λa, (mk_idx n (hash_fn a)).1) (array.iterate_aux bkts' (λ_ v l, v :: l) i h []) (sz + v2.length - v1.length)
  | 0     _ hb sz := absurd hb (nat.not_lt_zero _)
  | (i+1) h hb sz := begin
    cases lt_or_eq_of_le (nat.le_of_succ_le_succ hb) with hl e,
    { have bn : bidx ≠ ⟨i, h⟩ := λhh, ne_of_gt hl $ fin.veq_of_eq $ eq.symm hh,
      have he : array.read bkts' ⟨i, h⟩ = array.read bkts ⟨i, h⟩,
      { unfold bkts', rw array.read_write_ne _ _ _ _ bn },
      dsimp [array.iterate_aux], rw he,
      intro vv,
      rcases vv.unfold_cons with ⟨s, v, nd, al, e⟩,
      cases valid.modify_aux2 i (le_of_lt h) hl v with hsz v',
      have : (s + (array.read bkts ⟨i, h⟩).length) + v2.length - v1.length =
        s + v2.length - v1.length + (array.read bkts ⟨i, h⟩).length,
      { rw ← nat.sub_add_comm hsz, simp },
      rw [e, this],
      existsi le_trans hsz (nat.add_le_add_right (nat.le_add_right _ _) _),
      apply v'.cons _ nd,
      rw bkts'.rev_list_length_aux,
      rwa bkts.rev_list_length_aux at al },
    { subst i, dsimp [array.iterate_aux],
      rw [← show bidx = ⟨bidx.1, h⟩, from fin.eq_of_veq rfl,
          show array.read bkts' bidx = f L, by apply array.read_write_eq,
          ← valid.modify_aux1 _ _ (le_refl _), hfl, hl],
      intro vv,
      rcases vv.unfold_cons with ⟨s, v, nd, al, e⟩,
      have nd' : ((u ++ v2 ++ w).map sigma.fst).nodup,
      { simp [list.nodup_append] at nd djuv djwv,
        simp [list.nodup_append, nd, djuv, djwv, hvnd] },
      constructor,
      { subst e,
        have := nat.le_add_right v1.length (s + (u ++ v2 ++ w).length),
        rw (_ : v1.length + (s + (u ++ v2 ++ w).length) = _) at this, exact this,
        -- TODO(Mario): Why does simp fail here?
        have :
          s + (u.length + (v1.length + (v2.length + w.length))) =
          s + (v2.length + (u.length + (v1.length + w.length))), {simp},
        simp, exact this },
      { rw show sz + v2.length - v1.length = s + (u ++ v2 ++ w).length,
          by subst e; simpa using nat.add_sub_cancel (s + (u ++ v2 ++ w).length) v1.length,
        apply v.cons _ nd', simp at al ⊢,
        intros a b muvw,
        rcases muvw with mu | mv | mw,
        { exact al a b (or.inl mu) },
        { rw [bkts.rev_list_length_aux, hal _ mv] },
        { exact al a b (or.inr (or.inr mw)) } } }
    end

  theorem valid.modify {sz : ℕ} : valid bkts sz → sz + v2.length ≥ v1.length ∧ valid bkts' (sz + v2.length - v1.length) :=
  valid.modify_aux2 hl hfl hvnd hal djuv djwv _ _ bidx.2
end

theorem valid.replace_aux (a : α) (b : β a) : Π (l : list (Σ a, β a)), a ∈ l.map sigma.fst →
  ∃ (u w : list Σ a, β a) b', l = u ++ [⟨a, b'⟩] ++ w ∧ replace_aux a b l = u ++ [⟨a, b⟩] ++ w ∧ a ∉ u.map sigma.fst
| []            := false.elim
| (⟨a', b'⟩::t) := begin
  by_cases a' = a with e,
  { subst a',
    suffices : ∃ u w (b'' : β a),
      (∀ (x : β a), sigma.mk a x ∉ u) ∧
      sigma.mk a b' :: t = u ++ ⟨a, b''⟩ :: w ∧
      replace_aux a b (⟨a, b'⟩ :: t) = u ++ ⟨a, b⟩ :: w, {simpa},
    refine ⟨[], t, b', _⟩, simp [replace_aux] },
  { suffices : ∀ (x : β a) (_ : sigma.mk a x ∈ t), ∃ u w (b'' : β a),
      (∀ (x : β a), sigma.mk a x ∉ u) ∧
      sigma.mk a' b' :: t = u ++ ⟨a, b''⟩ :: w ∧
      sigma.mk a' b' :: replace_aux a b t = u ++ ⟨a, b⟩ :: w,
    { simpa [replace_aux, ne.symm e, e] },
    intros x m,
    have IH : ∀ (x : β a) (_ : sigma.mk a x ∈ t), ∃ u w (b'' : β a),
      (∀ (x : β a), sigma.mk a x ∉ u) ∧
      t = u ++ ⟨a, b''⟩ :: w ∧ replace_aux a b t = u ++ ⟨a, b⟩ :: w,
    { simpa using valid.replace_aux t },
    rcases IH x m with ⟨u, w, b'', nin, hl, hfl⟩,
    exact ⟨⟨a', b'⟩ :: u, w, b'', by simp [hl, hfl.symm, ne.symm e, nin]⟩ }
end

theorem valid.replace {n : ℕ+}
  {bkts : bucket_array α β n} {sz : ℕ} (a : α) (b : β a)
  (Hc : contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (bkts.modify hash_fn a (replace_aux a b)) sz :=
begin
  have nd := v.nodup hash_fn (mk_idx n (hash_fn a)),
  rcases valid.replace_aux a b (array.read bkts (mk_idx n (hash_fn a)))
    ((contains_aux_iff nd).1 Hc) with ⟨u, w, b', hl, hfl, nin⟩,
  refine (v.modify hash_fn
    u [⟨a, b'⟩] [⟨a, b⟩] w hl hfl (list.nodup_singleton _)
    (λa' e, by simp at e; rw e)
    (λa' e1 e2, by simp at e2; subst a'; contradiction)
    (λa' e1 e2, _)).2,
  rw hl at nd, revert e1,
  simp at e2, subst a',
  simp [list.nodup_append] at nd, simp [nd]
end

theorem valid.insert {n : ℕ+}
  {bkts : bucket_array α β n} {sz : ℕ} (a : α) (b : β a)
  (Hnc : ¬ contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (reinsert_aux bkts a b) (sz+1) :=
begin
  have nd := v.nodup hash_fn (mk_idx n (hash_fn a)),
  refine (v.modify hash_fn
    [] [] [⟨a, b⟩] (bkts.read hash_fn a) rfl rfl (list.nodup_singleton _)
    (λa' e, by simp at e; rw e)
    (λa', false.elim)
    (λa' e1 e2, _)).2,
  simp at e2, subst a',
  exact Hnc ((contains_aux_iff nd).2 e1)
end

theorem valid.erase_aux (a : α) : Π (l : list (Σ a, β a)), a ∈ l.map sigma.fst →
  ∃ (u w : list Σ a, β a) b, l = u ++ [⟨a, b⟩] ++ w ∧ erase_aux a l = u ++ [] ++ w
| []            := false.elim
| (⟨a', b'⟩::t) := begin
  by_cases a' = a with e,
  { subst a',
    simpa [erase_aux] using show ∃ u w (x : β a),
      t = u ++ w ∧ sigma.mk a b' :: t = u ++ ⟨a, x⟩ :: w, from ⟨[], t, b', by simp⟩ },
  { simp [erase_aux, e, ne.symm e],
    suffices : ∀ (b : β a) (_ : sigma.mk a b ∈ t), ∃ u w (x : β a),
      sigma.mk a' b' :: t = u ++ ⟨a, x⟩ :: w ∧
      sigma.mk a' b' :: erase_aux a t = u ++ w,
    { simpa [replace_aux, ne.symm e, e] },
    intros b m,
    have IH : ∀ (x : β a) (_ : sigma.mk a x ∈ t), ∃ u w (x : β a),
      t = u ++ ⟨a, x⟩ :: w ∧ erase_aux a t = u ++ w,
    { simpa using valid.erase_aux t },
    rcases IH b m with ⟨u, w, b'', hl, hfl⟩,
    exact ⟨⟨a', b'⟩ :: u, w, b'', by simp [hl, hfl.symm]⟩ }
end

theorem valid.erase {n} {bkts : bucket_array α β n} {sz}
  (a : α) (Hc : contains_aux a (bkts.read hash_fn a))
  (v : valid bkts sz) : valid (bkts.modify hash_fn a (erase_aux a)) (sz-1) :=
begin
  have nd := v.nodup _ (mk_idx n (hash_fn a)),
  rcases valid.erase_aux a (array.read bkts (mk_idx n (hash_fn a)))
    ((contains_aux_iff nd).1 Hc) with ⟨u, w, b, hl, hfl⟩,
  refine (v.modify hash_fn u [⟨a, b⟩] [] w hl hfl list.nodup_nil _ _ _).2;
  intros; simp at *; contradiction
end

end
end hash_map

structure hash_map (α : Type u) [decidable_eq α] (β : α → Type v) :=
(hash_fn : α → nat)
(size : ℕ)
(nbuckets : ℕ+)
(buckets : bucket_array α β nbuckets)
(is_valid : hash_map.valid hash_fn buckets size)

def mk_hash_map {α : Type u} [decidable_eq α] {β : α → Type v} (hash_fn : α → nat) (nbuckets := 8) : hash_map α β :=
let n := if nbuckets = 0 then 8 else nbuckets in
let nz : n > 0 := by abstract { cases nbuckets, {simp, tactic.comp_val}, simp [if_pos, nat.succ_ne_zero], apply nat.zero_lt_succ} in
{ hash_fn  := hash_fn,
  size     := 0,
  nbuckets := ⟨n, nz⟩,
  buckets  := mk_array n [],
  is_valid := hash_map.valid.mk _ _ }

namespace hash_map
variables {α : Type u} {β : α → Type v} [decidable_eq α]

def find (m : hash_map α β) (a : α) : option (β a) :=
find_aux a (m.buckets.read m.hash_fn a)

def contains (m : hash_map α β) (a : α) : bool :=
(m.find a).is_some

instance : has_mem α (hash_map α β) := ⟨λa m, m.contains a⟩

def fold {δ : Type w} (m : hash_map α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
m.buckets.foldl d f

def entries (m : hash_map α β) : list Σ a, β a :=
m.buckets.as_list

def keys (m : hash_map α β) : list α :=
m.entries.map sigma.fst

theorem find_iff (m : hash_map α β) (a : α) (b : β a) :
  m.find a = some b ↔ sigma.mk a b ∈ m.entries :=
m.is_valid.find_aux_iff _ _ _

theorem contains_iff (m : hash_map α β) (a : α) :
  m.contains a ↔ a ∈ m.keys :=
m.is_valid.contains_aux_iff _ _

theorem entries_empty (hash_fn : α → nat) (n) :
  (@mk_hash_map α _ β hash_fn n).entries = [] :=
by dsimp [entries, mk_hash_map]; rw mk_as_list hash_fn

theorem keys_empty (hash_fn : α → nat) (n) :
  (@mk_hash_map α _ β hash_fn n).keys = [] :=
by dsimp [keys]; rw entries_empty; refl

theorem find_empty (hash_fn : α → nat) (n a) :
  (@mk_hash_map α _ β hash_fn n).find a = none :=
by ginduction (@mk_hash_map α _ β hash_fn n).find a with h; [refl,
   { have := (find_iff _ _ _).1 h, rw entries_empty at this, contradiction }]

theorem not_contains_empty (hash_fn : α → nat) (n a) :
  ¬ (@mk_hash_map α _ β hash_fn n).contains a :=
by apply bool_iff_false.2; dsimp [contains]; rw [find_empty]; refl

theorem insert_lemma (hash_fn : α → nat) {n n'}
  {bkts : bucket_array α β n} {sz} (v : valid hash_fn bkts sz) :
  valid hash_fn (bkts.foldl (mk_array _ [] : bucket_array α β n') (reinsert_aux hash_fn)) sz :=
begin
  suffices : ∀ (l : list Σ a, β a) (t : bucket_array α β n') sz,
    valid hash_fn t sz → ((l ++ t.as_list).map sigma.fst).nodup →
    valid hash_fn (l.foldl (λr (a : Σ a, β a), reinsert_aux hash_fn r a.1 a.2) t) (sz + l.length),
  { have p := this bkts.as_list _ _ (valid.mk _ _),
    rw [mk_as_list hash_fn, list.append_nil, zero_add, v.as_list_length _] at p,
    rw bucket_array.foldl_eq,
    exact p (v.as_list_nodup _) },
  intro l, induction l with c l IH; intros t sz v nd, {exact v},
  rw show sz + (c :: l).length = sz + 1 + l.length, by simp,
  rcases (show (l.map sigma.fst).nodup ∧
      ((bucket_array.as_list t).map sigma.fst).nodup ∧
      c.fst ∉ l.map sigma.fst ∧
      c.fst ∉ (bucket_array.as_list t).map sigma.fst ∧
      (l.map sigma.fst).disjoint ((bucket_array.as_list t).map sigma.fst),
    by simpa [list.nodup_append, not_or_distrib] using nd)
    with ⟨nd1, nd2, nm1, nm2, dj⟩,
  have v' := v.insert _ _ c.2 (λHc, nm2 $ (v.contains_aux_iff _ c.1).1 Hc),
  apply IH _ _ v',
  suffices : ∀ ⦃a : α⦄ (b : β a), sigma.mk a b ∈ l →
    ∀ (b' : β a), sigma.mk a b' ∈  (reinsert_aux hash_fn t c.1 c.2).as_list → false,
  { simpa [list.nodup_append, nd1, v'.as_list_nodup _, list.disjoint] },
  intros a b m1 b' m2,
  rcases (reinsert_aux hash_fn t c.1 c.2).mem_as_list.1 m2 with ⟨i, im⟩,
  have : sigma.mk a b' ∉ array.read t i,
  { intro m3,
    have : a ∈ list.map sigma.fst t.as_list := list.mem_map_of_mem _ (t.mem_as_list.2 ⟨_, m3⟩),
    exact dj (list.mem_map_of_mem sigma.fst m1) this },
  by_cases mk_idx n' (hash_fn c.1) = i with h,
  { subst h,
    have e : sigma.mk a b' = ⟨c.1, c.2⟩,
    { simpa [reinsert_aux, bucket_array.modify, array.read_write_eq, this] using im },
    injection e with e, subst a,
    exact nm1.elim (@list.mem_map_of_mem _ _ _ _ _ m1) },
  { apply this,
    simpa [reinsert_aux, bucket_array.modify, array.read_write_ne _ _ _ _ h] using im }
end

def insert : Π (m : hash_map α β) (a : α) (b : β a), hash_map α β
| ⟨hash_fn, size, n, buckets, v⟩ a b :=
let bkt := buckets.read hash_fn a in
if hc : contains_aux a bkt then
{ hash_fn  := hash_fn,
  size     := size,
  nbuckets := n,
  buckets  := buckets.modify hash_fn a (replace_aux a b),
  is_valid := v.replace _ a b hc }
else
let size'    := size + 1,
    buckets' := buckets.modify hash_fn a (λl, ⟨a, b⟩::l),
    valid'   := v.insert _ a b hc in
if size' ≤ n.1 then
{ hash_fn  := hash_fn,
  size     := size',
  nbuckets := n,
  buckets  := buckets',
  is_valid := valid' }
else
let n'        : ℕ+ := ⟨n.1 * 2, mul_pos n.2 dec_trivial⟩,
    buckets'' : bucket_array α β n' :=
                buckets'.foldl (mk_array _ []) (reinsert_aux hash_fn) in
{ hash_fn  := hash_fn,
  size     := size',
  nbuckets := n',
  buckets  := buckets'',
  is_valid := insert_lemma _ valid' }

theorem mem_insert : Π (m : hash_map α β) (a b a' b'),
  sigma.mk a' b' ∈ (m.insert a b).entries ↔
  if a = a' then b == b' else sigma.mk a' b' ∈ m.entries
| ⟨hash_fn, size, n, bkts, v⟩ a b a' b' := begin
  let bkt := bkts.read hash_fn a,
  have nd : (bkt.map sigma.fst).nodup := v.nodup hash_fn (mk_idx n (hash_fn a)),
  have lem : Π (bkts' : bucket_array α β n) (v1 u w)
    (hl : bucket_array.as_list bkts = u ++ v1 ++ w)
    (hfl : bucket_array.as_list bkts' = u ++ [⟨a, b⟩] ++ w)
    (veq : (v1 = [] ∧ ¬ contains_aux a bkt) ∨ ∃b'', v1 = [⟨a, b''⟩]),
    sigma.mk a' b' ∈ bkts'.as_list ↔
    if a = a' then b == b' else sigma.mk a' b' ∈ bkts.as_list,
  { intros bkts' v1 u w hl hfl veq,
    rw [hl, hfl],
    by_cases a = a' with h,
    { subst a',
      suffices : b = b' ∨ sigma.mk a b' ∈ u ∨ sigma.mk a b' ∈ w ↔ b = b', {simpa [eq_comm]},
      refine or_iff_left_of_imp (not.elim $ not_or_distrib.2 _),
      rcases veq with ⟨e, Hnc⟩ | ⟨b'', e⟩; subst v1,
      { have na := (not_iff_not_of_iff $ v.contains_aux_iff _ _).1 Hnc,
        simp [hl, not_or_distrib] at na, simp [na] },
      { have nd' := v.as_list_nodup _,
        simp [hl, list.nodup_append] at nd', simp [nd'] } },
    { suffices : sigma.mk a' b' ∉ v1, {simp [h, ne.symm h, this]},
      rcases veq with ⟨e, Hnc⟩ | ⟨b'', e⟩; subst v1; simp [ne.symm h] } },
  by_cases (contains_aux a bkt : Prop) with Hc,
  { rcases valid.replace_aux a b (array.read bkts (mk_idx n (hash_fn a)))
      ((contains_aux_iff nd).1 Hc) with ⟨u', w', b'', hl', hfl', _⟩,
    rcases (append_of_modify u' [⟨a, b''⟩] [⟨a, b⟩] w' hl' hfl') with ⟨u, w, hl, hfl⟩,
    simpa [insert, @dif_pos (contains_aux a bkt) _ Hc]
      using lem _ _ u w hl hfl (or.inr ⟨b'', rfl⟩) },
  { let size' := size + 1,
    let bkts' := bkts.modify hash_fn a (λl, ⟨a, b⟩::l),
    have mi : sigma.mk a' b' ∈ bkts'.as_list ↔
        if a = a' then b == b' else sigma.mk a' b' ∈ bkts.as_list :=
      let ⟨u, w, hl, hfl⟩ := append_of_modify [] [] [⟨a, b⟩] _ rfl rfl in
      lem bkts' _ u w hl hfl $ or.inl ⟨rfl, Hc⟩,
    simp [insert, @dif_neg (contains_aux a bkt) _ Hc],
    by_cases size' ≤ n.1 with h,
    -- TODO(Mario): Why does the by_cases assumption look different than the stated one?
    { simpa [show size' ≤ n.1, from h] using mi },
    { let n' : ℕ+ := ⟨n.1 * 2, mul_pos n.2 dec_trivial⟩,
      let bkts'' : bucket_array α β n' := bkts'.foldl (mk_array _ []) (reinsert_aux hash_fn),
      suffices : sigma.mk a' b' ∈ bkts''.as_list ↔ sigma.mk a' b' ∈ bkts'.as_list.reverse,
      { simpa [show ¬ size' ≤ n.1, from h, mi] },
      rw [show bkts'' = bkts'.as_list.foldl _ _, from bkts'.foldl_eq _ _,
          ← list.foldr_reverse],
      induction bkts'.as_list.reverse with a l IH,
      { simp [mk_as_list hash_fn n'] },
      { cases a with a'' b'',
        let B := l.foldr (λ (y : sigma β) (x : bucket_array α β n'),
          reinsert_aux hash_fn x y.1 y.2) (mk_array n'.1 []),
        rcases append_of_modify [] [] [⟨a'', b''⟩] _ rfl rfl with ⟨u, w, hl, hfl⟩,
        simp [IH.symm, show B.as_list = _, from hl,
              show (reinsert_aux hash_fn B a'' b'').as_list = _, from hfl] } } }
end

theorem find_insert_eq (m : hash_map α β) (a : α) (b : β a) : (m.insert a b).find a = some b :=
(find_iff (m.insert a b) a b).2 $ (mem_insert m a b a b).2 $ by rw if_pos rfl

theorem find_insert_ne (m : hash_map α β) (a a' : α) (b : β a) (h : a ≠ a') :
  (m.insert a b).find a' = m.find a' :=
option.eq_of_eq_some $ λb',
let t := mem_insert m a b a' b' in
(find_iff _ _ _).trans $ iff.trans (by rwa if_neg h at t) (find_iff _ _ _).symm

theorem find_insert (m : hash_map α β) (a' a : α) (b : β a) :
  (m.insert a b).find a' = if h : a = a' then some (eq.rec_on h b) else m.find a' :=
if h : a = a' then by rw dif_pos h; exact
  match a', h with ._, rfl := find_insert_eq m a b end
else by rw dif_neg h; exact find_insert_ne m a a' b h

def insert_all (l : list (Σ a, β a)) (m : hash_map α β) : hash_map α β :=
l.foldl (λ m ⟨a, b⟩, insert m a b) m

def of_list (l : list (Σ a, β a)) (hash_fn): hash_map α β :=
insert_all l (mk_hash_map hash_fn (2 * l.length))

def erase (m : hash_map α β) (a : α) : hash_map α β :=
match m with ⟨hash_fn, size, n, buckets, v⟩ :=
  if hc : contains_aux a (buckets.read hash_fn a) then
  { hash_fn  := hash_fn,
    size     := size - 1,
    nbuckets := n,
    buckets  := buckets.modify hash_fn a (erase_aux a),
    is_valid := v.erase _ a hc }
  else m
end

theorem mem_erase : Π (m : hash_map α β) (a a' b'),
  sigma.mk a' b' ∈ (m.erase a).entries ↔
  a ≠ a' ∧ sigma.mk a' b' ∈ m.entries
| ⟨hash_fn, size, n, bkts, v⟩ a a' b' := begin
  let bkt := bkts.read hash_fn a,
  by_cases (contains_aux a bkt : Prop) with Hc,
  { let bkts' := bkts.modify hash_fn a (erase_aux a),
    suffices : sigma.mk a' b' ∈ bkts'.as_list ↔ a ≠ a' ∧ sigma.mk a' b' ∈ bkts.as_list,
    { simpa [erase, @dif_pos (contains_aux a bkt) _ Hc] },
    have nd := v.nodup _ (mk_idx n (hash_fn a)),
    rcases valid.erase_aux a bkt ((contains_aux_iff nd).1 Hc) with ⟨u', w', b, hl', hfl'⟩,
    rcases append_of_modify u' [⟨a, b⟩] [] _ hl' hfl' with ⟨u, w, hl, hfl⟩,
    suffices : ∀_:sigma.mk a' b' ∈ u ∨ sigma.mk a' b' ∈ w, a ≠ a',
    { have : sigma.mk a' b' ∈ u ∨ sigma.mk a' b' ∈ w ↔ (¬a = a' ∧ a' = a) ∧ b' == b ∨
        ¬a = a' ∧ (sigma.mk a' b' ∈ u ∨ sigma.mk a' b' ∈ w),
      { simp [eq_comm, not_and_self_iff, and_iff_right_of_imp this] },
      simpa [hl, show bkts'.as_list = _, from hfl, and_or_distrib_left] },
    intros m e, subst a', revert m, apply not_or_distrib.2,
    have nd' := v.as_list_nodup _,
    simp [hl, list.nodup_append] at nd', simp [nd'] },
  { suffices : ∀_:sigma.mk a' b' ∈ bucket_array.as_list bkts, a ≠ a',
    { simp [erase, @dif_neg (contains_aux a bkt) _ Hc, entries, and_iff_right_of_imp this] },
    intros m e, subst a',
    exact Hc ((v.contains_aux_iff _ _).2 (list.mem_map_of_mem sigma.fst m)) }
end

theorem find_erase_eq (m : hash_map α β) (a : α) : (m.erase a).find a = none :=
begin
  cases h : (m.erase a).find a with b, {refl},
  exact absurd rfl ((mem_erase m a a b).1 ((find_iff (m.erase a) a b).1 h)).left
end

theorem find_erase_ne (m : hash_map α β) (a a' : α) (h : a ≠ a') :
  (m.erase a).find a' = m.find a' :=
option.eq_of_eq_some $ λb',
(find_iff _ _ _).trans $ (mem_erase m a a' b').trans $
  (and_iff_right h).trans (find_iff _ _ _).symm

theorem find_erase (m : hash_map α β) (a' a : α) :
  (m.erase a).find a' = if a = a' then none else m.find a' :=
if h : a = a' then by subst a'; simp [find_erase_eq m a]
else by rw if_neg h; exact find_erase_ne m a a' h

section string
variables [has_to_string α] [∀ a, has_to_string (β a)]
open prod
private def key_data_to_string (a : α) (b : β a) (first : bool) : string :=
(if first then "" else ", ") ++ sformat!"{a} ← {b}"

private def to_string (m : hash_map α β) : string :=
"⟨" ++ (fst (fold m ("", tt) (λ p a b, (fst p ++ key_data_to_string a b (snd p), ff)))) ++ "⟩"

instance : has_to_string (hash_map α β) :=
⟨to_string⟩

end string

section format
open format prod
variables [has_to_format α] [∀ a, has_to_format (β a)]

private meta def format_key_data (a : α) (b : β a) (first : bool) : format :=
(if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt a ++ space ++ to_fmt "←" ++ space ++ to_fmt b

private meta def to_format (m : hash_map α β) : format :=
group $ to_fmt "⟨" ++ nest 1 (fst (fold m (to_fmt "", tt) (λ p a b, (fst p ++ format_key_data a b (snd p), ff)))) ++
        to_fmt "⟩"

meta instance : has_to_format (hash_map α β) :=
⟨to_format⟩
end format
end hash_map
