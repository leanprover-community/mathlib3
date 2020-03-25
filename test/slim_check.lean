
import .nat
import .prime
import .fin

import category.functor

import data.nat.prime
import data.nat.modeq
import data.nat.totient
import tactic.slim_check
import tactic.linarith
import tactic.omega
import tactic.abel

local attribute [instance, priority 0] nat.has_pow

namespace slim_check.examples
-- #eval (nat.prime 101 : bool)

example : ∀ n : ℕ, nat.prime n → n ≤ 1000000 :=
by slim_check

-- #check nat.gcd
-- structure sieve :=
-- (next : ℕ)
-- (factors : ℕ)
-- (is_prime : nat.prime next)
-- (ohters )
open function (uncurry)

def prod (ls : list $ ℕ × ℕ) : ℕ := (ls.map (uncurry (^))).prod

structure sieve :=
(current : ℕ)
(prod : ℕ)
(is_prime : nat.prime current)
(h : ∀ i, nat.coprime i current ↔ ∀ j ≤ current, ¬ j ∣ i)

section WF

variables {p : ℕ → Prop}
  (hp : ∃ i, p i)

structure MyType (p : ℕ → Prop) :=
(val : ℕ)
(below : ∀ i < val, ¬ p i)

instance : preorder (MyType p) :=
preorder.lift MyType.val infer_instance
-- { le := λ x y, x.val ≤ y.val }


-- instance : has_lt (MyType p) :=
-- { lt := λ x y, x.val < y.val }

-- lemma MyType.lt_trans {x y z : MyType p} : x < y → y < z → x < z :=
-- nat.lt_trans

def MyType.succ : ∀ (x : MyType p), ¬ p x.val → MyType p
| n h' := ⟨n.val.succ,
  λ i (h₀ : i.succ ≤ nat.succ n.val),
    or.elim (lt_or_eq_of_le h₀)
      (λ h₁, n.below _ $ nat.lt_of_succ_lt_succ h₁)
      (λ h₁, (nat.succ_inj h₁).symm ▸ h')⟩

open nat

def nat_subtype_wf' (p : ℕ → Prop) (i : ℕ) (h : p i) : @well_founded (MyType p) (>) :=
have h₀ : ∀ x : MyType p, x.val ≤ i, from
  λ x, by_contradiction $ λ hx, x.below i (lt_of_not_ge hx) h,
suffices @well_founded (MyType p) (measure $ λ x, i - x.val),
  by { convert this, ext, simp [measure,inv_image,nat.sub_lt_sub_left_iff (h₀ x)], refl },
measure_wf _

def nat_subtype_wf : @well_founded (MyType p) (>) :=
Exists.cases_on hp (nat_subtype_wf' p)

include hp

def MyType' := MyType p

instance MyType'.preorder : preorder (MyType' hp) :=
(infer_instance : preorder (MyType p))

lemma succ_gt (x : MyType' hp) (h : ¬p x.val) : x.succ h > x := nat.lt_succ_self _

instance : has_well_founded (MyType' hp) :=
{ r := (>),
  wf := nat_subtype_wf hp }

end WF


-- section

-- variables  (p : ℕ → Prop) (h : ∃ i, p i)
-- include h

-- structure up :=
-- (val : ℕ)
-- (h' : ∀ i ≤ val, ¬ p i)

-- instance : has_lt (up p h) :=
-- ⟨ λ x y, x.val > y.val ⟩

-- variables p h

-- lemma up_acc (i : ℕ) (h' : p i) : ∀ (a : up p h), acc gt a
-- | a := ⟨_, _⟩

-- lemma up_wf : @well_founded (up p h) (>) :=
-- ⟨ up_acc _ _ ⟩

-- def up.succ (x : up p h) (h' : ¬ p x.val.succ) : up p h :=
-- ⟨_, x.val.succ, by { introv h, cases h, exact h', exact x.h' _ h_a }⟩

-- instance : has_well_founded (up p h) :=
-- { r := (>) }

-- end

-- #print instances has_well_founded
-- (setenv "LEAN_PATH")
def mdecidable (m : Type → Type*) (p : Prop) := m (decidable p)
def mdecidable_pred {α} (m : Type → Type*) (p : α → Prop) := ∀ x, mdecidable m (p x)
open nat (succ)
def find_counted' {m} [monad m]
  (p : ℕ → Prop) (f : mdecidable_pred m p) (h : ∃ i, p i) (x : MyType' h) :
  ℕ → ∀ y : MyType' h, x < y → m (subtype (> x) ⊕ subtype p)
| 0 n hn := pure (sum.inl ⟨n,hn⟩)
| (succ p) n hn := do
  d ← f n.val,
  match d with
  | is_true h := pure $ sum.inr ⟨n.val,h⟩
  | is_false h' := find_counted' p (n.succ h') (lt_trans hn $ succ_gt _ _ _)
  end
-- using_well_founded
-- { dec_tac := `[apply succ_gt] }

def find_counted {m} [monad m]
  (p : ℕ → Prop) (f : mdecidable_pred m p) (h : ∃ i, p i) :  MyType' h → m (subtype p)
| n := do
  -- d ← find_counted' p f h n 100 n _,
  d ← f n.val,
  match d with
  | is_true h := pure ⟨n.val,h⟩
  | is_false h' :=
    do r ← find_counted' p f h n 100 (n.succ h') (succ_gt _ _ _),
       match r with
       | sum.inr r := pure r
       | sum.inl ⟨p,hp⟩ := find_counted p
       end
  end
using_well_founded
{ dec_tac := `[assumption] }

def find' {m} [monad m]
  (p : ℕ → Prop) (f : mdecidable_pred m p) (h : ∃ i, p i) : MyType' h → m { x : MyType' h // p x.val }
| n := do
  d ← f n.val,
  match d with
  | is_true h := pure ⟨n,h⟩
  | is_false h' := find' (n.succ h')
  end
using_well_founded
{ dec_tac := `[apply succ_gt] }

def find (p : ℕ → Prop) [f : decidable_pred p] (h : ∃ i, p i) (n : MyType' h) : ℕ :=
MyType.val $ subtype.val $ id.run $ find' p f h n
--   if h' : p n.val then n.val
--   else
--     find (n.succ h')
-- using_well_founded
-- { dec_tac := `[apply succ_gt] }

-- def find_sat (p : ℕ → Prop) [decidable_pred p] (h : ∃ i, p i) : ∀ x : MyType' h, p (find p h x)
-- | n :=
--   if h' : p n.val then by rwa [find,dif_pos h']
--   else
--     by rwa [find,dif_neg h'];
--     from find_sat (n.succ h')
-- using_well_founded
-- { dec_tac := `[apply succ_gt] }

def find_rec (p : ℕ → Prop) (q : ℕ → Sort*) [f : decidable_pred p] (h : ∃ i, p i) (n : MyType' h)
  (h₀ : ∀ i, p i → (∀ j < i, ¬ p j) → q i) :
  q (find p h n) :=
let x : id _ := find' p f h n in
have hx : _, from x.property,
h₀ _ hx $ x.val.below

def find_eq' (p : ℕ → Prop) [decidable_pred p] (h : ∃ i, p i) (y: ℕ) (x : MyType' h)
  (h₀ : p y)
  (h₁ : ∀ i < y, ¬ p i):
  y = find p h x :=
find_rec p _ h _ $ λ i hi hj,
le_antisymm
  (le_of_not_lt $ λ h₂, h₁ i h₂ hi)
  (le_of_not_lt $ λ h₁, hj y h₁ h₀)

-- def find_sat' (p : ℕ → Prop) [decidable_pred p] (h : ∃ i, p i) : ∀ (x : MyType' h) (y = find p h x), p y :=
-- λ x y h', h'.symm ▸ find_sat p h x

def sieve.succ' (n : ℕ) : ℕ :=
have ∀ (i : ℕ), i < n → ¬(n < i ∧ nat.prime i),
  from λ i h, not_and_of_not_or_not $ or.inl $ not_lt_of_le $ le_of_lt h,
find (λ x, n < x ∧ nat.prime x) (nat.exists_infinite_primes _ ) ⟨n,this⟩

def sieve.succ (n : ℕ) : subtype nat.prime :=
have _, from find_sat' _ _ _ (sieve.succ' n) rfl,
⟨ sieve.succ' n, this.2 ⟩

def nth_prime (n : ℕ) : subtype nat.prime :=
nat.iterate (sieve.succ ∘ subtype.val) n ⟨2,nat.prime_two⟩

lemma iterate_hom {α β} (f : α → α) (f' : β → β) (g : α → β) (n) (x : α)
  (h : ∀ x, g (f x) = f' (g x)) :
  g (nat.iterate f n x) = nat.iterate f' n (g x) :=
begin
  induction n generalizing x,
  { refl },
  { rw [nat.iterate,n_ih,h,nat.iterate] }
end

def iter_acc {α} (f : α → α) (x : α × list α) : α × list α :=
(f x.1, x.2 ++ [x.1])

def first_n_primes_f (x : ℕ × list (subtype nat.prime)) : ℕ × list (subtype nat.prime) :=
  let p := sieve.succ x.1 in
  (p.1, p :: x.2)

def first_n_primes (n : ℕ) : list (subtype nat.prime) :=
(nat.iterate first_n_primes_f n (0,[])).2.reverse

lemma iterate_iter_acc {α} (f : α → α) (n : ℕ) (x : α) (xs : list α) :
  (nat.iterate (iter_acc f) n (x,xs)) =
  (nat.iterate f n x, xs ++ (list.range n).map (λ i, nat.iterate f i x)) :=
begin
  induction n,
  { simp only [list.range_eq_range', nat.nat_zero_eq_zero, list.range', list.append_nil,
      prod.mk.inj_iff, list.map_nil, nat.iterate_zero, and_self, list.map, eq_self_iff_true], },
  rw [nat.iterate_succ',nat.iterate_succ',n_ih,list.range_concat,list.map_append,iter_acc,list.append_assoc],
  refl,
end

#check @nat.iterate₁

def first_n_primes_def (n : ℕ) :
  first_n_primes n = (list.range n).map nth_prime :=
begin
  rw [first_n_primes],
  let two : nat.primes := ⟨2, nat.prime_two⟩,
  have : sieve.succ 0 = two,
  { dsimp [sieve.succ,two,sieve.succ'], simp [sieve.succ'], },
  let f : nat.primes → nat.primes := sieve.succ ∘ subtype.val,
  let g : ℕ × list nat.primes → nat.primes × list nat.primes :=
    λ x : _ × _, (sieve.succ x.1, list.reverse x.2),
  have h := @nat.iterate₁ _ _ first_n_primes_f (iter_acc f) g _ n (0,[]),
  { simp [g, prod.map, list.reverse_nil, list.reverse_cons, list.nil_append, subtype.val, prod.map, prod.mk.inj_iff, prod.fst] at h,
    replace h := congr_arg prod.snd h,
    dsimp at h,
    rw [← h,iterate_iter_acc], dsimp,
    congr, ext, simp [nth_prime,f,this] },
  { rintro ⟨a,b⟩, simp only [first_n_primes_f,f,iter_acc,g,list.reverse_cons,prod.mk.inj_iff,and_self,eq_self_iff_true] }

end

-- def first_n_primes_succ (n : ℕ) :
--   first_n_primes (succ n) = first_n_primes n ++ [nth_prime n] :=
-- begin
--   rw [first_n_primes],
--   -- rw ← prod.map_snd id list.reverse,
--   -- change (list.reverse ∘ prod.snd) _ = _,
--   -- have :
--   let two : nat.primes := ⟨2, nat.prime_two⟩,
--   have : first_n_primes_f (0, []) = (2, [two]), admit,
--   let f : nat.primes → nat.primes := sieve.succ ∘ subtype.val,
--   have h := @nat.iterate₁ _ _ (iter_acc f) first_n_primes_f (prod.map subtype.val list.reverse) _ n (two,[two]),
--   { admit },
--   -- { simp only [prod.map, list.reverse_nil, list.reverse_cons, list.nil_append, subtype.val, prod.map] at h,
--   --   rw [nat.iterate_succ,this,h,prod.map_snd,list.reverse_reverse,iterate_iter_acc],
--   --   erw h, },
--   rw [iterate_hom first_n_primes_f (iter_acc f) (prod.map subtype.val list.reverse) (succ n),nat.iterate], -- (list.reverse ∘ prod.snd),


-- -- transitivity, apply iterate_hom _ (list.reverse ∘ prod.snd),
--   -- induction n,
-- end
-- #eval first_n_primes 20

def first_1000' : list nat.primes :=
first_n_primes 1000

lemma first_1000'_le {n} (p ∈ first_n_primes n) (q): q < p → q ∈ first_n_primes n :=
begin
  dsimp [first_n_primes] at *,
  induction n, dsimp [first_n_primes] at H, cases H,
end

def first_1000 : list ℕ :=
by
do let xs := (first_n_primes 1000).map subtype.val,
   let n : expr := reflect xs,
   tactic.exact n

-- #print first_1000

namespace nat

lemma lt_of_mul_lt_mul {x y z : ℕ} (h₃ : 0 < y) (h : x * y < z * y) : x < z :=
by rwa [← nat.mul_div_cancel x h₃,nat.div_lt_iff_lt_mul _ _ h₃]

-- lemma gcd_ne_self_foo {a n : ℕ} (h₀ : n < a) (h₁ : a < 2 * n) : nat.gcd a n ≠ n :=
-- begin
--   intro h₂,
--   rw ← nat.gcd_eq_right_iff_dvd at h₂,
--   cases h₂ with k hk, subst a,
--   have h₃ : 0 < n, linarith,
--   have h₂ : k < 2,
--   { apply lt_of_mul_lt_mul h₃, rwa mul_comm },
--   have h₄ : 1 < k,
--   { apply lt_of_mul_lt_mul h₃,
--     rwa [one_mul,mul_comm] },
--   apply not_le_of_lt h₂ h₄,
-- end
open nat (totient)

-- #exit

section
open finset function (embedding)

-- lemma {u v} card_eq_of_bijective'
--   {α : Type u} {β : Type v}
--   [decidable_eq β] {s : finset α} {s' : finset β}
--   (H : equiv.{u+1 v+1} (↑s : set α) (↑s' : set β)) :
--   card s = card s' :=
-- begin
--   let t : Type u := (↑s : set α),
--   let t' : Type v := (↑s' : set β),
--   let H : t ≃ t' := H,
--   let H' : t ↪ t' := H.to_embedding,
--   transitivity (s.attach).card,
--   { simp },
--   transitivity (s.attach.map H').card,
--   { rw finset.card_map },
--   transitivity (s'.attach).card,
--   { congr, ext, simp,
--     let a' := H.symm a,
--     existsi [a'.1,a'.2],
--     dsimp [H], symmetry,
--     rw ← equiv.symm_apply_eq, rw subtype.ext },
--   { rw card_attach }
-- end

end
-- #check @finset.card_eq_of_bijective

-- def to_subtype {α β} {p : α → Prop} {q : β → Prop}
--   (f : α → β) (h : ∀ x, p x → q (f x)) : subtype p → subtype q
-- | ⟨x,hx⟩ := ⟨f x, h _ hx⟩
-- p^φ(n) * p ≡ 1 [MOD n]
-- lemma totient_mul {m n : ℕ} (hm : m > 0) (hn : n > 0) (h : coprime m n) : totient (m * n) = totient m * totient n :=
-- _

-- lemma totient_mul {m n : ℕ} (hm : m > 0) (hn : n > 0) (h : coprime m n) : totient (m * n) = totient m * totient n :=
-- begin
--   -- classical,
--   rw [totient,totient,totient,← finset.card_product],
--   -- type_check finset ℕ,
--   -- apply finset.card_eq_of_bijective (λ i _, i+1); dsimp,
--   apply card_eq_of_bijective',
--   let f : ℕ → ℕ × ℕ := λ x, (x%m, x/m),
--   let g : ℕ × ℕ → ℕ := sorry,
--   refine ⟨to_subtype f _,to_subtype g _,_,_⟩,
--   { simp, intros x hx hgcd,
--     have h := coprime.coprime_mul_left hgcd,
--     have h' := coprime.coprime_mul_right hgcd,
--     have hh : x / m < n,
--     { rwa [div_lt_iff_lt_mul,mul_comm], exact hm },
--     refine ⟨⟨mod_lt _ hm,_⟩,hh,_ ⟩,
--     rw [coprime,gcd_comm,← gcd_rec],
--     exact h', exact h,
--      },
--   { simp,  },
--   -- simp,
--   -- { admit },
--   -- { simp, admit },
--   -- { simp, }
-- end

open_locale totient

-- local prefix `φ `:65 := nat.totient

-- lemma totient_pow {p n : ℕ} (h : nat.prime p) : φ (p^succ n) = p^n * (p - 1) :=
-- begin
--   induction n,
--   { simp [totient_eq_of_prime,*] },
--   { rw [nat.pow_succ,totient_mul,n_ih,nat.pow_succ], }
-- end

-- lemma mul_inj {p x y n : ℕ} (hp : coprime p n) (hq : coprime x n)
--   (h : p * x ≡ p * y [MOD n]) : x ≡ y [MOD n] :=
-- sorry


open nat (coprime)
-- lemma coprime_prod {α} {s : finset α} {f : α → ℕ} {q : ℕ}
--   (h : ∀ p ∈ s, coprime (f p) q) :
--   coprime (s.prod f) q :=
-- sorry

-- #print fin.of_nat


-- lemma modeq_of_fin_eq {p q n} (hn : 0 < n) (h : fin.of_nat_pos hn p = fin.of_nat_pos hn q) :
--   p ≡ q [MOD n] :=
-- fin.veq_of_eq h

-- set_option pp.implicit true

-- def swap {α β} [decidable_eq α] (x y : α) (f : α ↪ β) : α ↪ β :=
-- ⟨ λ i, if i = x then f y
--        else if i = y then f x
--        else f i ,
-- begin
--   intros i j hij, dsimp at hij,
--   split_ifs at hij,
--   all_goals {
--     replace hij := f.inj hij;
--     subst_vars;
--     { exact hij <|> { symmetry; exact hij } <|> contradiction } },
-- end ⟩

-- lemma prod_swap {α β} [comm_monoid β] [decidable_eq α] (s : finset α) (f : α → β)
--   (g : {x // x ∈ s} ↪ α)
--   (x y : { x // x ∈ s }) : (s.attach.map (swap x y g)).prod f = (s.attach.map g).prod f :=
-- sorry

-- @[simp]
-- lemma swap_apply {α β} [decidable_eq α]
--   (g : α ↪ β)
--   (x y : α) : swap x y g x = g y :=
-- by dsimp [swap]; simp

-- section
-- open finset
-- universes u
-- variables {α : Type u}

-- def embedding.insert_subtype [decidable_eq α] (a : α) (s : finset α) :
--   {x // x ∈ s} ↪ {x // x ∈ insert a s} :=
-- ⟨(λ (x : {x // x ∈ s}), ⟨x.val, mem_insert_of_mem x.property⟩),
--   by introv _ h; simp [subtype.ext] at h; rw [subtype.ext,h] ⟩

-- @[simp] lemma attach_insert' [decidable_eq α] {a : α} {s : finset α} :
--   attach (insert a s) = insert (⟨a, mem_insert_self a s⟩ : {x // x ∈ insert a s})
--     ((attach s).map $ embedding.insert_subtype a s) :=
-- by rw [attach_insert,map_eq_image]; refl

-- end

-- lemma prod_bij {α β} [comm_monoid β] (s : finset α) (f : α → β)
--   (g : {x // x ∈ s} ↪ α) (h : ∀ x, g x ∈ s) :
--   (s.attach.map g).prod f = s.prod f  :=
-- begin
--   classical,
--   -- by_cases h' : s = ∅,
--   -- { admit },
--   -- simp [finset.eq_empty_iff_forall_not_mem] at h',
--   -- cases h' with x h',
--   -- haveI : inhabited  := inhabited.mk (),
--   induction s using finset.induction_on
--     with a s h_as ih generalizing g,
--   { simp },
--   { haveI : inhabited { x // x ∈ insert a s } :=
--           inhabited.mk ⟨a, finset.mem_insert_self _ _⟩,
--     haveI : inhabited α := inhabited.mk a,

--     let g' : {x // x ∈ insert a s} → α := ⇑g,
--     -- do {  e ← tactic.to_expr ```(gt) >>= tactic.infer_type, tactic.whnf e >>= tactic.trace },
--     let b : { x // x ∈ insert a s } := ⟨a,finset.mem_insert_self a s⟩,
--     let c : { x // x ∈ insert a s } := function.inv_fun (⇑g) a,
--     rw ← prod_swap _ _ _ b c,
--     simp only [attach_insert', finset.map_insert,finset.map_map],
--     rw [finset.prod_insert,finset.prod_insert,swap_apply],
--     have : function.surjective g, admit,
--     congr' 1,
--     { dsimp [c],
--       rw function.right_inverse_inv_fun this },
--     { rw ih, intros, dsimp [swap,embedding.insert_subtype,c],
--       split_ifs,
--       { admit /- contradiction -/ },
-- rw h_2 at h_1,

-- rw function.right_inverse_inv_fun this, } }
-- end

-- lemma pow_totient (p q : ℕ) (h : coprime p q) : p ^ (φ q) ≡ 1 [MOD q] :=
-- begin
--   classical,
--   let S : finset ℕ := { p ∈ finset.range q | coprime q p },
--   have : S.prod  (λ x, x) * 1 ≡
--          S.prod  (* p) [MOD q],
--   { by_cases 0 < q,
--     { haveI : fact (0 < q) := h,
--       apply modeq_of_fin_eq h,
--       rw [← finset.prod_hom _ (fin.of_nat_pos h),mul_one,
--           ← finset.prod_hom _ (fin.of_nat_pos h)],
--       simp [is_monoid_hom.map_mul (fin.of_nat_pos h)],
--       have hF : ∀ x ∈ S, x < q, admit,
--       let F : { x // x ∈ S } ↪ ℕ,
--       { -- refine ⟨λ x, x * fin.of_nat_pos h p,_⟩,
--         -- rintros ⟨x,hx⟩ ⟨y,hy⟩ hxy,
--         -- dsimp at hxy, congr,
--         admit },
--       have hF' : ∀ x : { x // x ∈ S }, fin.of_nat_pos h x.val * fin.of_nat_pos h p = fin.of_nat_pos h (F x),
--       { admit },
--       conv_rhs { rw [← @finset.attach_map_val _ S,
--                      finset.prod_map,function.embedding.subtype], },
--       simp [function.embedding.subtype], simp only [hF'],
--       conv_rhs { rw ← finset.prod_map }  }, },
--   rw [finset.prod_mul_distrib,finset.prod_const] at this,
--   symmetry, rw [totient,← nat.pow_eq_pow],
--   convert mul_inj _ _ this,
--   { apply coprime_prod, simp,
--     intros, apply coprime.symm, assumption },
--   { apply coprime_one_left, }
-- end

-- #exit
open nat (mod_pow_mod dvd_iff_mod_eq_zero modeq prime.coprime_iff_not_dvd mod_lt) nat.prime
lemma fermat_prime_test {a n : ℕ} (ha₂ : ¬ n ∣ a) (h : nat.prime n) : a^(n-1) ≡ 1 [MOD n] :=
begin
  have hh' : 0 < a % n,
  { apply lt_of_le_of_ne (nat.zero_le _), symmetry,
    intro h, rw [← dvd_iff_mod_eq_zero] at h,
    contradiction },
  have hn : 1 < n, from h.one_lt,
  have hn' : 0 < n, from lt_trans (by norm_num) hn,
  rw [← nat.totient_eq_of_prime h],
  apply nat.pow_totient,
  apply nat.coprime.symm,
  exact (prime.coprime_iff_not_dvd h).2 ha₂,
end

lemma fermat_prime_test' {a n : ℕ} (ha₀ : 0 < a) (ha₁ : a < n) (h : nat.prime n) : a^(n-1) ≡ 1 [MOD n] :=
begin
  have hh' : 0 < a % n,
  { rw nat.mod_eq_of_lt ha₁, exact ha₀ },
  apply fermat_prime_test _ h,
  intro hh, cases hh, subst a,
  rw nat.mul_mod_right at hh',
  exact nat.not_succ_le_zero 0 hh',
end

-- #exit



end nat
open nat (succ pred)
lemma succ_le_iff_le_pred {p q} (hq : 0 < q) : succ p ≤ q ↔ p ≤ pred q :=
begin
  cases q, cases hq,
  apply nat.succ_le_succ_iff
end
open bounded_random
def fermat_test' (n : ℕ) : ℕ → rand (half_decision (¬ nat.prime n))
| 0 := pure half_decision.unknown
| (nat.succ k) :=
     if h : 2 ≤ n then
       have 1 ≤ n - 1, from nat.le_pred_of_lt h,
       have 0 < n, from nat.lt_of_succ_lt h,
       do ⟨a,ha,ha'⟩ ← random_r _ 1 (n - 1) ,
          have h_an : a < n, from (succ_le_iff_le_pred this).2 ha',
          if hh : nat.gcd a n = 1 then
            if hk : nat.modpow n (n-1) a = 1 then fermat_test' k
            else
              have hk' : ¬ (a^(n-1) % n) = 1 % n,
                by rwa [← nat.modpow_eq,nat.mod_eq_of_lt]; assumption,
              pure $ half_decision.is_true $ λ h, hk' $ nat.fermat_prime_test' ha h_an h
          else
            have hh₃ : nat.gcd a n ≠ n,
              by { apply ne_of_lt, apply lt_of_le_of_lt (nat.gcd_le_left _ ha) h_an, },
            have han : nat.gcd a n ∣ n, from nat.gcd_dvd_right _ _,
            have h' : n ≠ 0, from ne_of_gt this,
            have hh' : ¬nat.gcd a n = 0,
              from λ h, h' $ nat.eq_zero_of_gcd_eq_zero_right h,
            have hgcd : 2 ≤ nat.gcd a n, by omega,
            pure $ half_decision.is_true $ λ hh', hh₃ ((nat.dvd_prime_two_le hh' hgcd).1 han)
     else pure $ half_decision.is_true $ λ h', h $ nat.prime.one_lt h'

def fermat_test (n : ℕ) : rand (half_decision (¬ nat.prime n)) :=
fermat_test' n 5

section prob_test

variables
  (test : Π n, rand (half_decision (¬ nat.prime n)))

def prob_test' (n : ℕ) : gen (decidable (nat.prime n)) :=
do half_decision.is_true h ← monad_lift (test n) | pure infer_instance,
   pure $ decidable.is_false h

lemma mul_dvd_iff_left (x y p : ℕ) (hx : 0 < x) (Hcoprime : nat.coprime x y) : x * y ∣ p ↔ x ∣ p ∧ y ∣ p :=
begin
  split,
  { intro h, have h' := h, rw mul_comm at h',
    rcases h with ⟨k,h⟩, rcases h' with ⟨k',h'⟩,
    rw mul_assoc at h h', split; [rw h, rw h']; apply dvd_mul_right },
  { rintro ⟨⟨kx,h₀⟩,h₁⟩,
    rw [h₀,nat.mul_dvd_mul_iff_left hx],
    rw h₀ at h₁, apply nat.coprime.dvd_of_dvd_mul_left Hcoprime.symm h₁},
end

lemma prod_dvd : ∀ (xs : list ℕ) x, 1 < xs.prod → (xs.prod ∣ x ↔ (∀ i ∈ xs, i ∣ x))
| [] x := by simp
| (x :: xs) y :=
  by { simp [or_and_distrib_right,exists_or_distrib]; intro h,
       rw [mul_dvd_iff_left,prod_dvd], }

def prob_test_aux (n : ℕ) (hn₂ : 2 ≤ n) :
  ∀ (xs : list (subtype nat.prime)) (s : set (subtype nat.prime)),
  -- (∀ p : subtype nat.prime, p.val ≤ 1000 → p ∈ xs) →
  (∀ (m ∈ xs) (p < m), p ∈ s) →
  (∀ (m : subtype nat.prime), m ∈ s → 2 ≤ m.val → m.val ≤ nat.sqrt n → ¬m.val ∣ n) →
  gen (decidable (nat.prime n))
| [] _ _ _ := prob_test' test _
| (p'@⟨p,hp⟩::ps) s hs' hs :=
  if h_sqrt : p*p ≤ n then
     if h : p ∣ n then
         have h_le_sqrt : p ≤ nat.sqrt n,
           by rwa nat.le_sqrt,
         have h_not_prime : ¬ nat.prime n,
           from λ h', (nat.prime_def_le_sqrt.1 h').2 p (nat.prime.two_le hp) h_le_sqrt h,
         pure $ is_false h_not_prime
     else
       have h₀ : (∀ (m ∈ ps) (p < m), p ∈ s ∪ {p'}),
         from λ m hm p' hp', or.inl $ (hs' m (or.inr hm) _) hp',
       have h₁  : (∀ (m : subtype nat.prime), m ∈ s ∪ {p'} → 2 ≤ m.val → m.val ≤ nat.sqrt n → ¬m.val ∣ n),
         from λ m hm₀ hm₁ hm₂, or.cases_on hm₀
           (λ hm₀, hs _ hm₀ hm₁ hm₂)
           (λ hm₀, by simp at hm₀; rw hm₀; exact h),
       prob_test_aux ps (s ∪ {p'}) h₀ h₁
  else
    have h_sqrt : n.sqrt < p, by apply lt_of_not_ge; rwa [(≥),nat.le_sqrt],
    have hh : ∀ (m : ℕ), 2 ≤ m → m ≤ nat.sqrt n → ¬m ∣ n,
      from λ m hm hm' Hdvd,
        have nat.min_fac m ∣ n, from dvd_trans (nat.min_fac_dvd _) Hdvd,
        have Hne_one : m ≠ 1, from λ h, not_lt_of_le hm $ h.symm ▸ dec_trivial,
        have Hm_lt_p : m < p, from lt_of_le_of_lt hm' h_sqrt,
        have hm₀ : 0 < m, from lt_of_lt_of_le dec_trivial hm,
        have Hprime : (nat.min_fac m).prime,
          from nat.min_fac_prime Hne_one,
        have Hmin_fac_lt_sqrt : nat.min_fac m ≤ n.sqrt,
          from le_trans (nat.min_fac_le hm₀) hm',
        have Hmin_fac_lt_p : nat.min_fac m < p,
          from lt_of_le_of_lt Hmin_fac_lt_sqrt h_sqrt,
        hs ⟨nat.min_fac m, Hprime⟩
          (hs' p' (or.inl rfl) _ $ by exact Hmin_fac_lt_p)
          (nat.prime.two_le Hprime) Hmin_fac_lt_sqrt this,
        -- by rw [← nat.prod_factors hm₀],
    pure $ is_true $ nat.prime_def_le_sqrt.2 ⟨hn₂, hh⟩

-- #check nat.prod_factors

def prob_test (n : ℕ) :
  gen (decidable (nat.prime n)) :=
if h : 2 ≤ n then
  prob_test_aux test _ h first_1000' ∅
    (_)
    (by simp)
else
  pure $ is_false $ λ h', h $ nat.prime.two_le h'

#exit

end prob_test

def sieve.succ₂ (n : ℕ) : gen (subtype nat.prime) :=
have ∀ (i : ℕ), i < n → ¬(n < i ∧ nat.prime i),
  from λ i h, not_and_of_not_or_not $ or.inl $ not_lt_of_le $ le_of_lt h,
subtype.map id (λ i, and.elim_right) <$> find' (λ x, n < x ∧ nat.prime x)
  (λ x, @and.decidable _ _ _ <$> prob_test' fermat_test x)
  (nat.exists_infinite_primes _ ) ⟨n,this⟩

def sieve.succ₃ (n : ℕ) : gen (subtype nat.prime) :=
have ∀ (i : ℕ), i < n → ¬(n < i ∧ nat.prime i),
  from λ i h, not_and_of_not_or_not $ or.inl $ not_lt_of_le $ le_of_lt h,
subtype.map id (λ i, and.elim_right) <$> find_counted (λ x, n < x ∧ nat.prime x)
  (λ x, @and.decidable _ _ _ <$> prob_test' fermat_test x)
  (nat.exists_infinite_primes _ ) ⟨n,this⟩

def sieve.succ₄ (n : ℕ) : gen (subtype nat.prime) :=
have ∀ (i : ℕ), i < n → ¬(n < i ∧ nat.prime i),
  from λ i h, not_and_of_not_or_not $ or.inl $ not_lt_of_le $ le_of_lt h,
subtype.map id (λ i, and.elim_right) <$> find' (λ x, n < x ∧ nat.prime x)
  (λ x, @and.decidable _ _ _ <$> prob_test' miller_rabin x)
  (nat.exists_infinite_primes _ ) ⟨n,this⟩
-- have _, from find_sat' _ _ _ (sieve.succ' n) rfl,
-- ⟨ sieve.succ' n, this.2 ⟩

-- def prime.nth : ℕ → subtype nat.prime :=
-- stream.iterate sieve.succ ⟨2,dec_trivial⟩

def nat.prime.arbitrary₁ : slim_check.arbitrary (subtype nat.prime) :=
{ arby :=
  do { n ← arby ℕ,
       pure $ sieve.succ n },
       -- sieve.succ₂ n },
       -- sieve.succ₃ n },
  shrink := λ _, lazy_list.nil }

def nat.prime.arbitrary₂ : slim_check.arbitrary (subtype nat.prime) :=
{ arby :=
  do { n ← arby ℕ,
       -- pure $ sieve.succ n },
       sieve.succ₂ n },
       -- sieve.succ₃ n },
  shrink := λ _, lazy_list.nil }

def nat.prime.arbitrary₃ : slim_check.arbitrary (subtype nat.prime) :=
{ arby :=
  do { n ← arby ℕ,
       -- pure $ sieve.succ n },
       -- sieve.succ₂ n },
       sieve.succ₃ n },
  shrink := λ _, lazy_list.nil }

def nat.prime.arbitrary₄ : slim_check.arbitrary (subtype nat.prime) :=
{ arby :=
  do { n ← arby ℕ,
       -- pure $ sieve.succ n },
       -- sieve.succ₂ n },
       sieve.succ₄ n },
  shrink := λ _, lazy_list.nil }


-- structure state :=
-- (current : ℕ)
-- (sieve : stream (list $ ℕ × ℕ))
-- (all : ∀ i,  prod (sieve i))

-- #exit

def size := 7700
def bound := 1000000000000

#exit

section
local attribute [instance ] nat.prime.arbitrary₁

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size}

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 50 }
-- by success_if_fail { slim_check { max_size := size} }; admit

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 100 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 150 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 200 }
end
#exit
section
local attribute [instance ] nat.prime.arbitrary₂

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size}
-- by success_if_fail { slim_check { max_size := size} }; admit

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 50 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 100 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 150 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 200 }
end

#exit
section
local attribute [instance ] nat.prime.arbitrary₃

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size}
-- by success_if_fail { slim_check { max_size := size} }; admit

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 50 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 100 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 150 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 200 }
end

#exit

section
local attribute [instance ] nat.prime.arbitrary₄

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size}
-- by success_if_fail { slim_check { max_size := size} }; admit

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 50 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 100 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 150 }

example : ∀ n : ℕ, nat.prime n → n ≤ bound :=
by slim_check { max_size := size + 200 }
end

#exit

example : ∀ n : ℕ, n > n+1 :=
by success_if_fail { slim_check }; admit

example : ∀ n : ℕ, n < 20 :=
by success_if_fail { slim_check }; admit

open slim_check

run_cmd tactic.unsafe_run_io $ @testable.check (∀ n : ℕ, n > n+1) _ { }
run_cmd tactic.unsafe_run_io $ @testable.check (∀ n m : ℕ, n ≤ m)  _ { }
run_cmd tactic.unsafe_run_io $ @testable.check (∀ n m : ℕ, 2*m + n < 100)  _ { }
run_cmd tactic.unsafe_run_io $ @testable.check (∀ n m : ℕ, 0 ≤ m + n)  _ { }
run_cmd tactic.unsafe_run_io $ @testable.check
                     (∀ (n : ℤ) (xs : list ℤ) x,
                                 x ∈ xs → x < n)  _ { }

example : ∀ n : ℕ, n < n+1 :=
by slim_check

example : 1 < (2 : ℕ) :=
by slim_check

def even (n : ℕ) : bool :=
n % 2 = 0

section
variables (α : Type)

variables [has_add α] [has_one α] [decidable_eq α]

-- example (xs : list α) : 10 ∈ xs → ∃ (x ∈ xs), x = (10 : α) :=
-- by slim_check

example : (∀ (xs : list α), xs ≠ [] → ∃ (x ∈ xs), x = (10 : α)) :=
by success_if_fail { slim_check, }; admit

example : (∀ (xs : list α), ∃ (x ∈ xs), ∃ y ∈ xs, x ≠ y) :=
by success_if_fail { slim_check }; admit -- remaining meta variables

end

example : (∀ (x ∈ [1,2,3,4]), x ≠ 10) :=
by slim_check -- no error message or warning:
              -- slim_check actually proves the statement

example : (∃ (x ∈ [1,2,3,9]), x = 10) :=
by success_if_fail { slim_check }; admit

example : (∀ (α : Type) (xs : list α), xs.length < 10) :=
by success_if_fail { slim_check }; admit

example : (∀ n m : ℕ, 2*m + n < 100) :=
by success_if_fail { slim_check }; admit

-- example : (∀ n m : ℕ, 2*m + n < 10000000000) :=
-- by success_if_fail { slim_check }; admit

example : (∀ n m : ℕ, 2*m + n < 1000000000000) :=
by { slim_check }

example : (∀ (n : ℤ) (xs : list ℤ) x, x ∈ xs → x ≤ n) :=
by success_if_fail { slim_check }; admit

example : (∀ (xs : list ℤ), ∃ x ∈ xs, ∀ y ∈ xs, x ≤ y) :=
by success_if_fail { slim_check }; admit

example : (∀ (xs : list ℤ), xs = [] ∨ ∃ x ∈ xs, ∀ y ∈ xs, x ≤ y) :=
by slim_check

-- example : (∀ (xs : list ℤ), xs ≠ [] → ∃ x ∈ xs, ∀ y ∈ xs, x ≤ y) :=
-- by slim_check

example : (∀ n m : ℕ, even m → ¬ even n → ¬ even (m+n)) :=
by slim_check

variables n m : ℕ

example : (false → even m → ¬ even n → even (m+n)) :=
by success_if_fail { slim_check }; admit

example (xs : list ℕ) (n ∈ xs) : 5*(n+1) ≥ list.length xs :=
by slim_check

end slim_check.examples
