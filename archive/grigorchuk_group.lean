import analysis.special_functions.log.basic
import topology.algebra.order.intermediate_value
import group_theory.perm.fibered
import group_theory.free_group
import data.bool.count

/-!
-/

noncomputable theory
open list set function cardinal
open_locale cardinal

namespace grigorchuk_group

inductive generator
| a : generator
| bcd : fin 3 → generator

namespace generator

def to_fun : generator → list bool → list bool
| _ [] := []
| a (x::xs) := (!x::xs)
| (bcd n) (ff :: l) := ff :: (if n = 0 then l else to_fun a l)
| (bcd n) (tt :: l) := tt :: to_fun (bcd (n + 1)) l

instance : has_coe_to_fun generator (λ _, list bool → list bool) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe : to_fun = coe_fn := rfl

def b := bcd 0
def c := bcd 1
def d := bcd 2

@[simp] lemma range_bcd : range bcd = {b, c, d} :=
by { simp only [fin.range_fin_succ, range_unique], refl }

@[simp] lemma apply_nil (x : generator) : x [] = [] := by cases x; refl

@[simp] lemma a_cons (x : bool) (l : list bool) : a (x :: l) = !x :: l := rfl

protected lemma «forall» {p : generator → Prop} : (∀ x, p x) ↔ p a ∧ ∀ n, p (bcd n) :=
⟨λ h, ⟨h a, λ n, h (bcd n)⟩, λ h, by { rintro (_|n), exacts [h.1, h.2 n] }⟩

protected lemma forall' {p : generator → Prop} : (∀ x, p x) ↔ p a ∧ p b ∧ p c ∧ p d :=
by { rw [generator.forall, fin.forall_fin_succ, fin.forall_fin_two], refl }

protected lemma «exists» {p : generator → Prop} : (∃ x, p x) ↔ p a ∨ ∃ n, p (bcd n) :=
⟨by { rintro ⟨_|n, h⟩, exacts [or.inl h, or.inr ⟨n, h⟩] },
  λ h, h.elim (λ ha, ⟨a, ha⟩) (λ ⟨n, hn⟩, ⟨bcd n, hn⟩)⟩

protected lemma exists' {p : generator → Prop} : (∃ x, p x) ↔ p a ∨ p b ∨ p c ∨ p d :=
by { rw [generator.exists, fin.exists_fin_succ, fin.exists_fin_two], refl }

@[simp] lemma range_eq {α} (f : generator → α) : range f = {f a, f b, f c, f d} :=
set.ext $ λ y, by { simp only [set.mem_range, generator.exists', @eq_comm _ _ y], refl }

def equiv_with_bot : generator ≃ with_bot (fin 3) :=
{ to_fun := λ x, generator.cases_on x ⊥ coe,
  inv_fun := λ x, with_bot.rec_bot_coe a bcd x,
  left_inv := generator.forall.2 ⟨rfl, λ n, rfl⟩,
  right_inv := option.forall.2 ⟨rfl, λ n, rfl⟩ }

instance : linear_order generator := linear_order.lift' equiv_with_bot equiv_with_bot.injective

lemma bcd_cons_ff (n : fin 3) (l : list bool) : bcd n (ff :: l) = ff :: if n = 0 then l else a l :=
rfl

@[simp] lemma bcd_cons_tt (n : fin 3) (l : list bool) : bcd n (tt :: l) = tt :: bcd (n + 1) l := rfl

@[simp] lemma length_apply : ∀ (x : generator) (l : list bool),
  length (x l) = length l
| _ [] := by rw [apply_nil]
| a (y::l) := rfl
| (bcd n) (tt::l) := by rw [bcd_cons_tt, length_cons, length_apply, length_cons]
| (bcd n) (ff::l) :=
  by { rw [bcd_cons_ff], split_ifs, { refl }, { rw [length_cons, length_apply, length_cons] } }

protected lemma involutive : ∀ x : generator, involutive x
| _ [] := by rw [apply_nil, apply_nil]
| a (x::l) := by rw [a_cons, a_cons, bnot_bnot]
| (bcd n) (tt::l) := by rw [bcd_cons_tt, bcd_cons_tt, involutive]
| (bcd n) (ff::l) := by { rw [bcd_cons_ff, bcd_cons_ff], split_ifs; simp [involutive a l] }

@[simp] lemma apply_apply (x : generator) (l : list bool) : x (x l) = l := x.involutive l
@[simp] lemma comp_self (x : generator) : x ∘ x = id := x.involutive.comp_self

protected lemma bijective (x : generator) : bijective x := x.involutive.bijective
protected lemma injective (x : generator) : injective x := x.involutive.injective
protected lemma surjective (x : generator) : surjective x := x.involutive.surjective

@[simp] lemma apply_eq_iff (x : generator) {l₁ l₂ : list bool} : x l₁ = x l₂ ↔ l₁ = l₂ :=
x.injective.eq_iff

lemma bcd_apply_bcd_of_ne {m n : fin 3} (h : m ≠ n) (l : list bool) :
  bcd m (bcd n l) = bcd (-m - n) l :=
begin
  induction l with x l ihl generalizing m n, { refl },
  cases x,
  { simp only [bcd_cons_ff], refine ⟨rfl, _⟩,
    have h2 : (2 : fin 3) = -1 := rfl,
    fin_cases n; fin_cases m; try { exact absurd rfl h }; simp only [h2, if_pos rfl, neg_eq_zero,
      neg_neg, if_neg one_ne_zero, sub_zero, sub_self, neg_zero, zero_sub, apply_apply] },
  { replace h : m + 1 ≠ n + 1 := mt add_right_cancel h,
    have h2 : (-1 - 1 : fin 3) = 1 := rfl,
    simp only [bcd_cons_tt, ihl h, neg_add, add_sub_add_comm, h2, eq_self_iff_true, true_and] }
end

lemma bcd_comp_bcd_of_ne {m n : fin 3} (h : m ≠ n) : bcd m ∘ bcd n = bcd (-m -n) :=
funext $ bcd_apply_bcd_of_ne h

@[simp] lemma b_apply_c (l : list bool) : b (c l) = d l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma c_apply_b (l : list bool) : c (b l) = d l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma b_apply_d (l : list bool) : b (d l) = c l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma d_apply_b (l : list bool) : d (b l) = c l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma c_apply_d (l : list bool) : c (d l) = b l := bcd_apply_bcd_of_ne dec_trivial l
@[simp] lemma d_apply_c (l : list bool) : d (c l) = b l := bcd_apply_bcd_of_ne dec_trivial l

@[simp] lemma b_comp_c : b ∘ c = d := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma c_comp_b : c ∘ b = d := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma b_comp_d : b ∘ d = c := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma d_comp_b : d ∘ b = c := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma c_comp_d : c ∘ d = b := bcd_comp_bcd_of_ne dec_trivial
@[simp] lemma d_comp_c : d ∘ c = b := bcd_comp_bcd_of_ne dec_trivial

@[simp] lemma head'_a : ∀ l : list bool, head' (a l) = (head' l).map bnot
| [] := rfl
| (x :: l) := rfl

@[simp] lemma head'_bcd (n : fin 3) : ∀ l : list bool, head' (bcd n l) = head' l
| [] := rfl
| (ff::l) := rfl
| (tt::l) := rfl

lemma coe_ne_id : ∀ x : generator, ⇑x ≠ id
| a := ne_iff.2 ⟨[ff], dec_trivial⟩
| (bcd ⟨0, _⟩) := ne_iff.2 ⟨[tt, ff, tt], dec_trivial⟩
| (bcd ⟨k + 1, _⟩) := ne_iff.2 ⟨[ff, tt], dec_trivial⟩

lemma to_fun_a_ne_bcd (n : fin 3) : ⇑a ≠ bcd n :=
λ h, absurd (congr_fun h [tt]) $ by simp

lemma to_fun_injective : injective to_fun :=
begin
  rintro (_|m) (_|n) h,
  { refl },
  { exact absurd h (to_fun_a_ne_bcd _) },
  { exact absurd h.symm (to_fun_a_ne_bcd _) },
  { rw [to_fun_eq_coe] at h, simp only,
    refine by_contra (λ hne, coe_ne_id (bcd (-m - n)) _),
    rw [← bcd_comp_bcd_of_ne hne, h, comp_self] }
end

instance equiv_like : equiv_like generator (list bool) (list bool) :=
{ coe := to_fun,
  inv := to_fun,
  left_inv := apply_apply,
  right_inv := apply_apply,
  coe_injective' := λ x y h₁ h₂, to_fun_injective h₁ }

end generator

open generator

@[derive monoid] def word : Type := free_monoid generator

local notation `W` := word

namespace word

instance : has_coe_t generator W := ⟨free_monoid.of⟩

@[simp] lemma length_coe (x : generator) : (x : W).length = 1 := rfl

@[elab_as_eliminator]
protected def rec_on {C : W → Sort*} (w : W) (h1 : C 1)
  (h : ∀ (a : generator) g, C g → C (a * g)) : C w :=
free_monoid.rec_on w h1 h

@[simp] lemma closure_abcd : submonoid.closure ({a, b, c, d} : set W) = ⊤ :=
by { rw [← generator.range_eq, ← free_monoid.closure_range_of], refl }

end word

@[ext] structure noncancellable : Type :=
(to_word : W)
(chain'_xor : chain' (λ x y, xor (x = a) (y = a) ∧ x ≠ y) to_word)

local notation `NC` := noncancellable

namespace noncancellable

@[simp] lemma mk_to_word (g : NC) (hg : _ := g.2) : mk g.to_word hg = g := by { cases g, refl }

instance : has_coe_t generator NC := ⟨λ x, ⟨x, chain'_singleton _⟩⟩

@[simp, norm_cast] lemma to_word_coe (g : generator) : (g : NC).to_word = g := rfl
@[simp] lemma mk_singleton (g : generator) (h) : mk g h = g := rfl

instance : has_one NC := ⟨⟨[], chain'_nil⟩⟩

@[simp] lemma one_to_word : to_word 1 = 1 := rfl
@[simp] lemma mk_nil (h) : mk [] h = 1 := rfl

def tail (l : NC) : NC := ⟨l.to_word.tail, l.2.tail⟩

instance : has_inv NC :=
⟨λ l, ⟨l.to_word.reverse, chain'_reverse.2 (l.2.imp $ λ x y h, by rwa [flip, xor_comm, ne_comm])⟩⟩

@[simp] lemma inv_to_word (g : NC) : (g⁻¹).to_word = g.to_word.reverse := rfl

@[simps] def cons (x : generator) (g : NC)
  (hxg : chain' (λ x y, xor (x = a) (y = a) ∧ x ≠ y) (x :: g.to_word)) : NC :=
⟨x :: g.to_word, hxg⟩

@[simps] def update_bcd (m n : fin 3) (l : W)
  (h : chain' (λ x y, xor (x = a) (y = a) ∧ x ≠ y) (bcd n :: l)) : NC :=
cons (bcd m) ⟨l, h.tail⟩ $ h.imp_head $ λ z hz,
  by { simp only [xor_false, id] at hz, rcases hz with ⟨rfl, -⟩,
       simp only [xor_false, ne.def, id, not_false_iff, and_true] }

end noncancellable

namespace generator

def cons_noncancellable : generator → NC → NC
| x ⟨[], _⟩ := x
| a ⟨a :: l, h⟩ := ⟨l, h.tail⟩
| a ⟨bcd n :: l, h⟩ := ⟨a :: bcd n :: l, h.cons $
  by simp only [eq_self_iff_true, xor_true, not_false_iff, ne.def, true_and]⟩
| (bcd m) ⟨a :: l, h⟩ := ⟨bcd m :: a :: l, h.cons $
  by simp only [eq_self_iff_true, xor_false, ne.def, not_false_iff, id, true_and]⟩
| (bcd m) ⟨bcd n :: l, h⟩ :=
  if m = n then ⟨l, h.tail⟩ else noncancellable.update_bcd (-m - n) _ _ h

lemma cons_noncancellable_one (x : generator) : x.cons_noncancellable 1 = x :=
by cases x; refl

lemma length_cons_noncancellable_le (x : generator) (g : NC) :
  length (cons_noncancellable x g).to_word ≤ length g.to_word + 1 :=
begin
  cases x with m; rcases g with ⟨_|⟨_|n, l⟩, hl⟩;
    simp only [cons_noncancellable, length, word.length_coe, noncancellable.to_word_coe],
  { exact ((lt_add_one _).trans (lt_add_one _)).le },
  { split_ifs,
    exacts [((lt_add_one _).trans (lt_add_one _)).le, (lt_add_one _).le] }
end

end generator

namespace noncancellable

lemma cons_eq_cons {x : generator} {g : NC}
  (hxg : chain' (λ x y, xor (x = a) (y = a) ∧ x ≠ y) (x :: g.to_word)) :
  cons x g hxg = x.cons_noncancellable g :=
by cases g with l hl; cases x; rcases l with (_|⟨(_|_), l⟩);
  simp only [generator.cons_noncancellable, cons]; try { refl }; apply absurd hxg.rel_head; simp

lemma mk_cons {x : generator} {l : W} (h : chain' (λ x y, xor (x = a) (y = a) ∧ x ≠ y) (x :: l)) :
  mk (x :: l) h = cons x ⟨l, h.tail⟩ h :=
rfl

@[simp] lemma cons_one (x : generator)
  (h : chain' (λ x y, xor (x = a) (y = a) ∧ x ≠ y) [x] := chain'_singleton _) :
  cons x 1 h = x :=
rfl

@[elab_as_eliminator]
def rec_on_cons {C : NC → Sort*} (g : NC) (h1 : C 1) (hcons : ∀ x g' h, C g' → C (cons x g' h)) :
  C g :=
by { cases g with l hl, induction l with x l ihl, exacts [h1, hcons x ⟨l, hl.tail⟩ _ (ihl _)] }

@[elab_as_eliminator]
def cases_on_cons {C : NC → Sort*} (g : NC) (h1 : C 1) (hcons : ∀ x g' h, C (cons x g' h)) :
  C g :=
rec_on_cons g h1 (λ x g' h _, hcons x g' h)

instance : mul_action W NC := free_monoid.mk_mul_action generator.cons_noncancellable

lemma cons_smul (x : generator) (l : W) (g : NC) :
  @has_smul.smul W NC _ (x :: l) g = x.cons_noncancellable (l • g) := rfl

lemma length_smul_le (w : W) (g : NC) : length (w • g).to_word ≤ length w + length g.to_word :=
begin
  induction w with x w ihw, { exact (zero_add _).ge },
  rw [cons_smul, length_cons, add_right_comm],
  exact (x.length_cons_noncancellable_le _).trans (add_le_add_right ihw _)
end

instance : mul_one_class NC :=
{ mul := λ g₁ g₂, g₁.to_word • g₂,
  one_mul := λ a, rfl,
  mul_one := λ g,
    begin
      induction g using grigorchuk_group.noncancellable.rec_on_cons with x l hxl ihl,
      { refl },
      { conv_rhs { erw [cons_eq_cons, ← ihl] }, refl }
    end,
  .. noncancellable.has_one }

lemma to_word_smul (g₁ g₂ : NC) : g₁.to_word • g₂ = g₁ * g₂ := rfl

lemma coe_mul (x : generator) (g : NC) : ↑x * g = x.cons_noncancellable g := rfl
@[simp] lemma coe_smul (x : generator) (g : NC) : (x : W) • g = x * g := rfl
lemma cons_mul {x g g' h} : cons x g h * g' = x * (g * g') := rfl

lemma length_mul_le (g₁ g₂ : NC) :
  (g₁ * g₂).to_word.length ≤ g₁.to_word.length + g₂.to_word.length :=
length_smul_le _ _

lemma coe_smul_one (x : generator) : (x : W) • (1 : NC) = x := mul_one (x : NC)

@[simp] lemma coe_mul_cons_self {x : generator} {g : NC} (h) : ↑x * cons x g h = g :=
by { cases g, cases x, exacts [rfl, if_pos rfl] }

lemma cons_eq_coe_mul {x g} (h) : cons x g h = x * g := cons_eq_cons h

lemma bcd_mul_cons_bcd {m n : fin 3} {g : NC} (hmn : m ≠ n)
  (h : chain' (λ x y, xor (x = a) (y = a) ∧ x ≠ y) (bcd n :: g.to_word)) :
  ↑(bcd m) * cons (bcd n) g h = update_bcd (-m - n) n g.to_word h :=
if_neg hmn

lemma coe_mul_coe_cancel_left : ∀ (x : generator) (g : NC), ↑x * (↑x * g) = g
| x ⟨[], _⟩ :=
  begin
    rw [mk_nil, mul_one], conv_lhs { congr, skip, rw [← cons_one] },
    exact coe_mul_cons_self _
  end
| a ⟨a :: l, h⟩ := by rw [mk_cons, coe_mul_cons_self, cons_eq_coe_mul]
| a ⟨bcd n :: l, h⟩ := rfl
| (bcd m) ⟨a :: l, h⟩ := if_pos rfl
| (bcd m) ⟨bcd n :: l, h⟩ :=
  begin
    rcases eq_or_ne m n with rfl|hmn,
    { rw [mk_cons, coe_mul_cons_self, cons_eq_coe_mul] },
    { rw [mk_cons, bcd_mul_cons_bcd hmn, update_bcd, bcd_mul_cons_bcd, ext_iff],
      { simp only [update_bcd_to_word, cons_to_word, ← sub_add, sub_self, zero_add] },
      { rwa [← neg_one_mul, show ((-1 : fin 3) = 2), from rfl, two_mul, add_sub_assoc,
          ne.def, self_eq_add_right, sub_eq_zero] } },
  end

lemma bcd_mul_bcd_left {m n : fin 3} (h : m ≠ n) (g : NC) :
  ↑(bcd m) * (↑(bcd n) * g) = bcd (-m - n) * g :=
begin
  induction g using grigorchuk_group.noncancellable.cases_on_cons with x g hxg,
  { rw [mul_one, mul_one], exact if_neg h },
  { cases x with k,
    { rw [← @cons_eq_coe_mul (bcd n), bcd_mul_cons_bcd h], refl,
      refine hxg.cons _, simp },
    { rcases eq_or_ne n k with rfl|hnk,
      { rw [coe_mul_cons_self, bcd_mul_cons_bcd, neg_sub, sub_sub_cancel_left, neg_neg,
          update_bcd, cons_eq_coe_mul, mk_to_word],
        { rwa [sub_eq_add_neg, ← neg_one_mul n, show ((-1 : fin 3) = 2), from rfl, two_mul,
            ← add_assoc, ne.def, add_left_eq_self, neg_add_eq_zero] } },
      { rw [bcd_mul_cons_bcd hnk, update_bcd],
        rcases eq_or_ne m (-n - k) with rfl|hmnk,
        { rw [coe_mul_cons_self, mk_to_word, neg_sub, sub_neg_eq_add, add_sub_cancel,
            coe_mul_cons_self] },
        { rw [bcd_mul_cons_bcd hmnk, bcd_mul_cons_bcd, ext_iff, update_bcd_to_word,
            update_bcd_to_word], dsimp only,
          { congr' 2,
            fin_cases m; fin_cases n; try { exact absurd rfl h }; fin_cases k;
              try { exact absurd rfl hnk }; try { exact absurd rfl hmnk }; refl },
          { rintro rfl, apply hmnk,
            rw [sub_sub_eq_add_sub, neg_add_self, zero_sub, neg_neg] } } } } }
end

instance : is_scalar_tower W NC NC :=
begin
  refine is_scalar_tower.of_mclosure_eq_top word.closure_abcd _,
  rw [← generator.range_eq, forall_range_iff],
  intros x g g',
  rw [smul_eq_mul, smul_eq_mul, coe_smul, coe_smul],
  induction g using grigorchuk_group.noncancellable.cases_on_cons with y g hyg generalizing x,
  { rw [one_mul, mul_one] },
  { by_cases h : xor (x = a) (y = a) ∧ x ≠ y,
    { rw [← cons_eq_coe_mul, cons_mul], exact hyg.cons h },
    { rw [not_and_distrib, not_xor, ne.def, not_not] at h,
      cases x with m; cases y with n; try { exact absurd h (by simp) }; clear h,
      { rw [coe_mul_cons_self, cons_mul, coe_mul_coe_cancel_left] },
      { rcases eq_or_ne m n with rfl|hmn,
        { rw [coe_mul_cons_self, cons_mul, coe_mul_coe_cancel_left] },
        { simp only [cons_mul, bcd_mul_cons_bcd hmn, update_bcd, mk_to_word,
            bcd_mul_bcd_left hmn] } } } }
end

instance : group NC :=
{ mul_assoc := λ x y z, smul_mul_assoc x.to_word y z,
  mul_left_inv := λ x,
    begin
      induction x using grigorchuk_group.noncancellable.rec_on_cons with x g hxg ihg,
      { refl },
      { erw [← to_word_smul, inv_to_word, cons_to_word, reverse_cons, ← free_monoid.mul_def,
          mul_smul, coe_smul, coe_mul_cons_self],
        exact ihg }
    end,
  .. noncancellable.mul_one_class, .. noncancellable.has_inv }

@[simp] lemma coe_mul_self (x : generator) : (x * x : NC) = 1 :=
by rw [← coe_mul_coe_cancel_left x 1, mul_one]

lemma bcd_mul_bcd {m n : fin 3} (h : m ≠ n) : (bcd m * bcd n : NC) = bcd (-m - n) :=
if_neg h

@[simp] lemma b_mul_c : (b * c : NC) = d := bcd_mul_bcd dec_trivial
@[simp] lemma b_mul_d : (b * d : NC) = c := bcd_mul_bcd dec_trivial
@[simp] lemma c_mul_b : (c * b : NC) = d := bcd_mul_bcd dec_trivial
@[simp] lemma c_mul_d : (c * d : NC) = b := bcd_mul_bcd dec_trivial
@[simp] lemma d_mul_b : (d * b : NC) = c := bcd_mul_bcd dec_trivial
@[simp] lemma d_mul_c : (d * c : NC) = b := bcd_mul_bcd dec_trivial
@[simp] lemma inv_coe (x : generator) : (x : NC)⁻¹ = x := rfl

end noncancellable

namespace word

def cancel : W →* NC := free_monoid.lift coe

@[simp, norm_cast] lemma cancel_coe (x : generator) : cancel x = x := rfl

lemma cancel_eq_smul_one (w : W) : cancel w = w • 1 :=
by { rw [cancel, free_monoid.lift_apply, list.prod_eq_foldr, foldr_map], refl }

lemma length_cancel_le (w : W) : length (cancel w).to_word ≤ length w :=
(cancel_eq_smul_one w).symm ▸ (noncancellable.length_smul_le _ _).trans_eq (add_zero _)

end word

@[simp] lemma noncancellable.cancel_to_word (g : NC) : g.to_word.cancel = g :=
by rw [word.cancel_eq_smul_one, noncancellable.to_word_smul, mul_one]

namespace noncancellable

@[simp] lemma mclosure_abcd : submonoid.closure ({a, b, c, d} : set NC) = ⊤ :=
begin
  refine top_unique (λ g hg, _),
  rw [← cancel_to_word g, ← generator.range_eq],
  exact submonoid.list_prod_mem _
    (forall_mem_map_iff.2 $ λ x hx, submonoid.subset_closure $ mem_range_self _)
end

@[simp] lemma closure_abcd : subgroup.closure ({a, b, c, d} : set NC) = ⊤ :=
subgroup.closure_eq_top_of_mclosure_eq_top mclosure_abcd

end noncancellable

def _root_.grigorchuk_group : subgroup (equiv.perm (list bool)) :=
subgroup.closure (range (coe : generator → equiv.perm (list bool)))

local notation `G` := grigorchuk_group

instance fun_like : fun_like G (list bool) (λ _, list bool) :=
{ coe := λ f, f.1,
  coe_injective' := λ f g h₁, subtype.ext $ equiv.coe_fn_injective h₁ }

instance : has_coe_t generator G := ⟨λ x, ⟨x, subgroup.subset_closure $ mem_range_self _⟩⟩

@[simp] lemma inv_coe (x : generator) : (x : G)⁻¹ = x := rfl
@[simp] lemma coe_mul_self (x : generator) : (x * x : G) = 1 := fun_like.ext' x.comp_self
@[simp, norm_cast] lemma coe_fn_coe_gen (x : generator) : ⇑(x : G) = x := rfl
@[simp, norm_cast] lemma coe_fn_coe (x : G) : ⇑(x : equiv.perm (list bool)) = x := rfl
@[simp, norm_cast] lemma coe_coe (x : generator) : ((x : G) : equiv.perm (list bool)) = x := rfl
@[simp] lemma coe_fn_one : ⇑(1 : G) = id := rfl
lemma one_apply (l : list bool) : (1 : G) l = l := rfl
@[simp] lemma coe_fn_mul (g₁ g₂ : G) : ⇑(g₁ * g₂) = g₁ ∘ g₂ := rfl
lemma mul_apply (g₁ g₂ : G) (l : list bool) : (g₁ * g₂) l = g₁ (g₂ l) := rfl

lemma bcd_mul_of_ne {m n : fin 3} (h : m ≠ n) : (bcd m * bcd n : G) = bcd (-m - n) :=
fun_like.ext' $ generator.bcd_comp_bcd_of_ne h

@[simp] lemma b_mul_c : (b * c : G) = d := bcd_mul_of_ne dec_trivial
@[simp] lemma c_mul_d : (c * d : G) = b := bcd_mul_of_ne dec_trivial
@[simp] lemma d_mul_b : (d * b : G) = c := bcd_mul_of_ne dec_trivial
@[simp] lemma c_mul_b : (c * b : G) = d := bcd_mul_of_ne dec_trivial
@[simp] lemma d_mul_c : (d * c : G) = b := bcd_mul_of_ne dec_trivial
@[simp] lemma b_mul_d : (b * d : G) = c := bcd_mul_of_ne dec_trivial

def to_perm : G →* equiv.perm (list bool) := subgroup.subtype _

@[simp] lemma coe_to_perm : ⇑to_perm = coe := rfl
@[simp] lemma to_perm_range : to_perm.range = G := subgroup.subtype_range G
lemma to_perm_injective : injective to_perm := subtype.coe_injective

@[simp] lemma closure_abcd : subgroup.closure ({a, b, c, d} : set G) = ⊤ :=
subgroup.map_injective to_perm_injective $ by rw [monoid_hom.map_closure, ← generator.range_eq,
  ← range_comp, ← monoid_hom.range_eq_map, to_perm_range, coe_to_perm, (∘), funext coe_coe,
   grigorchuk_group]

@[simp] lemma mclosure_abcd : submonoid.closure ({a, b, c, d} : set G) = ⊤ :=
by simp only [← subgroup.top_to_submonoid, ← closure_abcd, subgroup.closure_to_submonoid,
  inv_insert, inv_singleton, inv_coe, union_self]

#exit

def of_word : free_monoid (fin 4) →* G := free_monoid.lift abcd

@[simp] lemma of_word_nil : of_word [] = 1 := rfl

@[simp] lemma of_word_of (n : fin 4) : of_word (free_monoid.of n) = abcd n :=
free_monoid.lift_eval_of _ _

lemma of_word_singleton (n : fin 4) : of_word [n] = abcd n := of_word_of n

@[simp] lemma of_word_cons (n : fin 4) (g : free_monoid (fin 4)) :
  of_word (n :: g) = abcd n * of_word g :=
prod_cons

@[simp] lemma mrange_of_word : of_word.mrange = ⊤ :=
by simp only [of_word, free_monoid.mrange_lift, range_abcd, mclosure_abcd]

lemma surjective_of_word : surjective of_word :=
monoid_hom.mrange_top_iff_surjective.1 mrange_of_word

instance : countable G :=
by { haveI : countable (free_monoid (fin 4)) := list.countable, exact surjective_of_word.countable }

/-- `to_word g` is the shortest list that represents `g`. -/
def to_word (g : G) : free_monoid (fin 4) :=
argmin_on length nat.well_founded_lt.1 (of_word ⁻¹' {g}) (surjective_of_word g)

lemma of_word_to_word (g : G) : of_word (to_word g) = g :=
argmin_on_mem length _ (of_word ⁻¹' {g}) _

def is_minimal (g : free_monoid (fin 4)) : Prop :=
∀ g', of_word g = of_word g' → length g ≤ length g'

lemma is_minimal.length_eq {g₁ g₂ : free_monoid (fin 4)} (h₁ : is_minimal g₁) (h₂ : is_minimal g₂)
  (h : of_word g₁ = of_word g₂) : length g₁ = length g₂ :=
(h₁ g₂ h).antisymm (h₂ g₁ h.symm)

lemma is_minimal.length_lt {g₁ g₂ : free_monoid (fin 4)} (h₁ : is_minimal g₁) (h₂ : ¬is_minimal g₂)
  (h : of_word g₁ = of_word g₂) : length g₁ < length g₂ :=
(h₁ g₂ h).lt_of_ne $ λ h', h₂ $ λ g hg, h' ▸ h₁ _ (h.trans hg)

@[simp] lemma is_minimal_nil : is_minimal [] := λ _ _, zero_le _

lemma is_minimal_to_word (g : G) : is_minimal (to_word g) :=
λ g' hg', argmin_on_le _ _ _ $ hg'.symm.trans $ of_word_to_word g

lemma exists_is_minimal_of_word_eq (g : G) : ∃ g', is_minimal g' ∧ of_word g' = g :=
⟨to_word g, is_minimal_to_word g, of_word_to_word g⟩

lemma length_to_word_of_word_le (g : free_monoid (fin 4)) :
  length (to_word (of_word g)) ≤ length g :=
is_minimal_to_word _ _ $ of_word_to_word _

lemma is_minimal.to_infix {g₁ g₂ : free_monoid (fin 4)} (h₁ : is_minimal g₁) (h₂ : g₂ <:+: g₁) :
  is_minimal g₂ :=
begin
  rcases h₂ with ⟨g, g', rfl⟩,
  intros g₂' h₂,
  have H := h₁ (g * g₂' * g') (by simp only [← free_monoid.mul_def, map_mul, h₂]),
  simpa only [free_monoid.mul_def, length_append, add_le_add_iff_left, add_le_add_iff_right] using H
end

protected lemma is_minimal.tail {g : free_monoid (fin 4)} (h : is_minimal g) :
  is_minimal (tail g) :=
h.to_infix (tail_suffix g).is_infix

protected lemma is_minimal.chain' {g : free_monoid (fin 4)} (h : is_minimal g) :
  g.chain' (λ m n, is_minimal [m, n]) :=
(chain'_is_infix g).imp $ λ m n, h.to_infix

def cancel : free_monoid (fin 4) → free_monoid (fin 4)
| [] := []
| [x] := [x]
|

lemma is_minimal.ne {m n : fin 4} (h : is_minimal [m, n]) : m ≠ n :=
begin
  rintro rfl,
  refine (h 1 _).not_lt two_pos,
  rw [map_one, of_word_cons, of_word_singleton],
  exact abcd_mul_self m
end

lemma is_minimal.chain'_ne {g : free_monoid (fin 4)} (h : is_minimal g) : g.chain' (≠) :=
h.chain'.imp $ λ _ _, is_minimal.ne

lemma is_minimal.eq_0_or_eq_0 {m n : fin 4} (h : is_minimal [m, n]) : m = 0 ∨ n = 0 :=
begin
  have hne : m ≠ n := h.ne,
  contrapose! h, cases h with hm hn,
  rcases fin.exists_succ_eq_iff.mpr hm with ⟨m, rfl⟩,
  rcases fin.exists_succ_eq_iff.mpr hn with ⟨n, rfl⟩,
  replace hne : m ≠ n := ne_of_apply_ne _ hne,
  simp_rw [is_minimal, not_forall, show length [_, _] = 2, from rfl, not_le, exists_prop,
    of_word_cons, of_word_nil, mul_one, abcd_succ, bcd_mul_of_ne hne],
  exact ⟨_, (of_word_of _).symm, one_lt_two⟩
end

lemma is_minimal.chain'_eq_0 {g : free_monoid (fin 4)} (h : is_minimal g) :
  g.chain' (λ m n : fin 4, m = 0 ∨ n = 0) :=
h.chain'.imp $ λ _ _, is_minimal.eq_0_or_eq_0

lemma le_length_preserving : G ≤ equiv.perm.fiberwise length :=
(subgroup.closure_le _).2 $ range_subset_iff.2 $ fin.forall_fin_succ.2
  ⟨pre.length_a, λ n l, by { rw [matrix.cons_val_succ], apply pre.length_bcd }⟩

def to_length_preserving : G →* equiv.perm.fiberwise (@length bool) :=
subgroup.inclusion le_length_preserving

@[simp] lemma coe_to_length_preserving (g : G) : ⇑(to_length_preserving g) = g := rfl

@[simp] lemma length_apply (g : G) (l : list bool) : length (g l) = length l :=
le_length_preserving g.2 l

@[simp] lemma apply_nil (g : G) : g [] = [] := length_eq_zero.1 $ length_apply g _

lemma head'_of_word (g : free_monoid (fin 4)) (l : list bool) :
  (of_word g l).head' = l.head'.map (bnot^[count 0 g]) :=
begin
  induction g using free_monoid.rec_on with x g ihg,
  { exact (congr_fun option.map_id l.head').symm },
  { rw [map_mul, of_word_of, free_monoid.mul_def, free_monoid.of_def, singleton_append,
      count_cons, mul_apply],
    revert x, refine fin.forall_fin_succ.2 ⟨_, λ x, _⟩,
    { rw [← a, if_pos rfl, iterate_succ', head'_a, ihg, option.map_map] },
    { rw [abcd_succ, head'_bcd, ihg, if_neg],
      exact x.succ_ne_zero.symm } }
end

def head_preserving : subgroup G := (equiv.perm.fiberwise head').comap to_perm

local notation `H` := head_preserving

lemma mem_head_preserving {g : G} : g ∈ H ↔ ∀ l, (g l).head' = l.head' := iff.rfl

namespace head_preserving

@[simp] lemma of_word_mem (g : free_monoid (fin 4)) : of_word g ∈ H ↔ even (count 0 g) :=
calc of_word g ∈ H ↔ ∀ o : option bool, o.map (bnot ^[count 0 g]) = id o :
  by simp only [mem_head_preserving, head'_of_word, surjective_head'.forall, id]
... ↔ (bnot ^[count 0 g]) = id : by simp only [← funext_iff, option.map_eq_id]
... ↔ even (count 0 g) : bool.involutive_bnot.iterate_eq_id bool.bnot_ne_id

@[simp] lemma a_nmem : a ∉ H := show abcd 0 ∉ H, by { rw [← of_word_of, of_word_mem], dec_trivial }

lemma ne_top : H ≠ ⊤ := λ h, a_nmem $ h.symm ▸ subgroup.mem_top _

@[simp] lemma bcd_mem (n : fin 3) : bcd n ∈ H :=
begin
  rw [← abcd_succ, ← of_word_of, of_word_mem, free_monoid.of_def, count_singleton',
    if_neg n.succ_pos.ne],
  exact even_zero
end

@[simp] lemma abcd_mem : ∀ {n : fin 4}, abcd n ∈ H ↔ n ≠ 0 :=
fin.forall_fin_succ.2 ⟨by simp, λ k, by simp [fin.succ_ne_zero]⟩

@[simp] lemma b_mem : b ∈ H := bcd_mem _
@[simp] lemma c_mem : c ∈ H := bcd_mem _
@[simp] lemma d_mem : d ∈ H := bcd_mem _

@[simp] lemma mul_mem_iff {g₁ g₂ : G} : g₁ * g₂ ∈ H ↔ (g₁ ∈ H ↔ g₂ ∈ H) :=
begin
  rcases surjective_of_word g₁ with ⟨g₁, rfl⟩,
  rcases surjective_of_word g₂ with ⟨g₂, rfl⟩,
  simp_rw [← map_mul, of_word_mem, free_monoid.mul_def, count_append, nat.even_add]
end

instance : subgroup.normal H := ⟨λ g₁ h g₂, by simp [h]⟩

lemma a_mul_mem {g : G} : a * g ∈ H ↔ g ∉ H := by simp
lemma bcd_mul_mem {n : fin 3} {g : G} : bcd n * g ∈ H ↔ g ∈ H := by simp
lemma b_mul_mem {g : G} : b * g ∈ H ↔ g ∈ H := by simp
lemma c_mul_mem {g : G} : c * g ∈ H ↔ g ∈ H := by simp
lemma d_mul_mem {g : G} : d * g ∈ H ↔ g ∈ H := by simp

lemma mul_a_mem {g : G} : g * a ∈ H ↔ g ∉ H := by simp
lemma mul_b_mem {g : G} : g * b ∈ H ↔ g ∈ H := by simp
lemma mul_c_mem {g : G} : g * c ∈ H ↔ g ∈ H := by simp
lemma mul_d_mem {g : G} : g * d ∈ H ↔ g ∈ H := by simp

@[simp] lemma index_eq : subgroup.index H = 2 := subgroup.index_eq_two_iff.2 $ ⟨a, λ g, mul_a_mem⟩

lemma sq_mem (x : G) : x ^ 2 ∈ H := subgroup.sq_mem_of_index_two index_eq _

lemma cons_tail_apply {g : G} (hg : g ∈ H) (x : bool) (l : list bool) :
  x :: (g (x :: l)).tail = g (x :: l) :=
cons_head'_tail $ by simp only [mem_head_preserving.1 hg, head', option.mem_def]

def atom' (x : bool) (n : fin 3) : free_monoid (fin 4) := cond x [0, n.succ, 0] [n.succ]

@[simp] lemma length_atom' (x : bool) (n : fin 3) : length (atom' x n) = cond x 3 1 :=
by cases x; refl

lemma of_word_atom' (x : bool) (n : fin 3) : of_word (atom' x n) = cond x (a * bcd n * a) (bcd n) :=
by cases x; simp only [atom', cond, of_word_cons, of_word_singleton, a, abcd_succ, mul_assoc]

lemma range_of_word_atom :
  range (of_word ∘ uncurry atom') = {b, c, d, a * b * a, a * c * a, a * d * a} :=
begin
  ext x,
  simp only [set.mem_range, fin.exists_fin_succ, fin.exists_fin_two, prod.exists, bool.exists_bool,
    (∘), uncurry, of_word_atom', set.mem_insert_iff, mem_singleton_iff, mul_assoc, or_assoc,
    @eq_comm _ x],
  refl
end

lemma of_word_atom'_mem (x : bool) (n : fin 3) : of_word (atom' x n) ∈ H := by cases x; simp [atom']

def atom (x : bool) (n : fin 3) : H := ⟨of_word (atom' x n), of_word_atom'_mem x n⟩

lemma coe_fn_atom (x : bool) (n : fin 3) :
  ⇑(atom x n) = (cond x (a * bcd n * a) (bcd n) : G) :=
by cases x; refl

def mk : free_monoid (bool × fin 3) →* H := free_monoid.lift (uncurry atom)

def mk' : free_monoid (bool × fin 3) →* free_monoid (fin 4) := free_monoid.lift (uncurry atom')

lemma of_word_comp_mk' : of_word.comp mk' = (subgroup.subtype _).comp mk :=
by { simp only [mk', mk, free_monoid.comp_lift], refl }

lemma of_word_mk' (l : free_monoid (bool × fin 3)) : of_word (mk' l) = mk l :=
monoid_hom.congr_fun of_word_comp_mk' l

lemma mk'_cons (a : bool × fin 3) (l : free_monoid (bool × fin 3)) :
  mk' (a :: l) = atom' a.1 a.2 * mk' l :=
by simp only [mk', ← free_monoid.of_mul_eq_cons, map_mul, free_monoid.lift_eval_of, uncurry]

lemma mk'_singleton (a : bool × fin 3) : mk' [a] = atom' a.1 a.2 :=
free_monoid.lift_eval_of _ _

lemma mk_cons (a : bool × fin 3) (l : free_monoid (bool × fin 3)) :
  mk (a :: l) = atom a.1 a.2 * mk l :=
by simp only [mk, ← free_monoid.of_mul_eq_cons, map_mul, free_monoid.lift_eval_of, uncurry]

lemma _root_.grigorchuk_group.is_minimal.chain'_ne_fst {l : free_monoid (bool × fin 3)}
  (hl : is_minimal (mk' l)) : l.chain' ((≠) on prod.fst) :=
begin
  induction l with x l ihl, { exact chain'_nil },
  cases l with y l, { exact chain'_singleton _ },
  rw [mk'_cons] at hl,
  specialize ihl (hl.to_infix (suffix_append _ _).is_infix),
  refine ihl.cons (_ : x.1 ≠ y.1),
  rw [mk'_cons, ← mul_assoc] at hl,
  replace hl := hl.to_infix (prefix_append _ _).is_infix,
  rcases ⟨x, y⟩ with ⟨⟨x, n⟩, y, m⟩, rintro (rfl : x = y),
  cases x; simp only [atom, cond, free_monoid.mul_def, cons_append, nil_append] at hl,
  { simpa [fin.succ_ne_zero] using hl.eq_0_or_eq_0 },
  { exact hl.chain'_ne.tail.tail.rel_head rfl }
end

lemma _root_.grigorchuk_group.is_minimal.chain'_ne_map_fst {l : free_monoid (bool × fin 3)}
  (hl : is_minimal (mk' l)) : (map prod.fst l).chain' (≠) :=
(chain'_map _).2 hl.chain'_ne_fst

lemma length_mk' (g : free_monoid (bool × fin 3)) :
  length (mk' g) = length g + 2 * count tt (map prod.fst g) :=
begin
  induction g with x g ihg, { refl },
  rw [mk'_cons, free_monoid.mul_def, length_append, ihg, count, map_cons, countp_cons,
    length_atom'],
  rcases x with ⟨(_|_), _⟩; simp only [cond, if_pos rfl, if_false, length_cons]; ring
end

lemma le_length_mk' (g : free_monoid (bool × fin 3)) : length g ≤ length (mk' g) :=
(length_mk' g).symm ▸ le_add_right le_rfl

@[simp] lemma even_length_mk' {g} : even (length (mk' g)) ↔ even (length g) :=
by simp only [length_mk', nat.even_add, even_two_mul, true_or, iff_true]

lemma exists_mk'_eq : ∀ {g : free_monoid (fin 4)}, is_minimal g → of_word g ∈ H →
  ∃ l, mk' l = g
| [] _ _ := ⟨[], rfl⟩
| (⟨n + 1, hn⟩ :: g) hmin hmem :=
  let ⟨l, hl⟩ := @exists_mk'_eq g hmin.tail (by simpa [fin.ext_iff] using hmem)
  in ⟨(ff, ⟨n, nat.lt_pred_iff.2 hn⟩) :: l,
    hl ▸ by simp only [mk'_cons, atom', cond, free_monoid.mul_def, singleton_append, fin.succ_mk]⟩
| [⟨0, _⟩] _ h := absurd h $ by simp only [fin.mk_zero, of_word_mem, count_singleton,
  nat.not_even_one, not_false_iff]
| (⟨0, _⟩ :: ⟨0, _⟩ :: g) hmin hmem := (hmin.chain'_ne.rel_head rfl).elim
| [⟨0, _⟩, ⟨n + 1, hn⟩] hmin hmem := absurd hmem $
  by simp [count_singleton', fin.ext_iff, n.succ_ne_zero.symm]
| (⟨0, _⟩ :: ⟨n + 1, hn⟩ :: ⟨m + 1, hm⟩ :: g) hmin hmem :=
  absurd hmin.chain'_eq_0.tail.rel_head $ by simp [fin.ext_iff]
| (⟨0, _⟩ :: ⟨n + 1, hn⟩ :: ⟨0, _⟩ :: g) hmin hmem :=
  let ⟨l, hl⟩ := @exists_mk'_eq g hmin.tail.tail.tail
    (by simpa [count_cons, fin.ext_iff, n.succ_ne_zero.symm, nat.even_add_one] using hmem)
  in ⟨(tt, ⟨n, nat.lt_pred_iff.2 hn⟩) :: l, hl ▸ by simp only [mk'_cons, atom', cond,
    free_monoid.mul_def, cons_append, nil_append, fin.mk_zero, fin.succ_mk]⟩

lemma exists_mk_eq (g : H) : ∃ l, mk l = g ∧ is_minimal (mk' l) :=
begin
  cases g with g hg,
  rcases exists_is_minimal_of_word_eq g with ⟨g, hmin, rfl⟩,
  rcases exists_mk'_eq hmin hg with ⟨l, rfl⟩,
  refine ⟨l, subtype.ext _, hmin⟩,
  rw [← of_word_mk', subtype.coe_mk]
end

lemma mk_surjective : surjective mk := λ g, (exists_mk_eq g).imp $ λ l, and.left

@[simp] lemma mclosure_range_atom : submonoid.closure (range $ uncurry atom) = ⊤ :=
begin
  refine top_unique (λ g hg, _), clear hg,
  rcases exists_mk_eq g with ⟨g, rfl, hmin⟩,
  exact list_prod_mem (list.forall_mem_map_iff.2 $
    λ x hx, submonoid.subset_closure $ mem_range_self _)
end

@[simp] lemma closure_range_atom : subgroup.closure (range $ uncurry atom) = ⊤ :=
(subgroup.eq_top_iff' _).2 $
  λ x, subgroup.le_closure_to_submonoid _ (mclosure_range_atom.symm ▸ trivial)

/-- The subgroup of head preserving elements is generated by `b`, `c`, `d`, `a * b * a`,
`a * c * a`, and `a * d * a`. -/
lemma eq_closure : H = subgroup.closure {b, c, d, a * b * a, a * c * a, a * d * a} :=
begin
  rw [← range_of_word_atom, ← subgroup.subtype_range H, monoid_hom.range_eq_map,
    ← closure_range_atom, monoid_hom.map_closure, ← range_comp],
  refl
end

/-- Restrict head preserving elements of the Grigorchuk group to lists with a fixed head. -/
def restr_to_perm (x : bool) : H →* equiv.perm (list bool) :=
monoid_hom.to_hom_perm $
{ to_fun := λ g l, (g (x :: l)).tail,
  map_one' := rfl,
  map_mul' := λ g₁ g₂, funext $ λ l, congr_arg tail $ congr_arg g₁ $
    (cons_tail_apply g₂.2 _ _).symm }

lemma restr_to_perm_apply (x : bool) (g : H) (l : list bool) :
  restr_to_perm x g l = (g (x :: l)).tail :=
rfl

def atom_restr (x y : bool) (n : fin 3) : G :=
if x = y then if n = 1 then 1 else a else bcd (n + 1)

lemma restr_to_perm_atom (x y : bool) (n : fin 3) : restr_to_perm x (atom y n) = atom_restr x y n :=
begin
  refine equiv.ext (λ l, _),
  rw [restr_to_perm_apply, atom_restr, coe_fn_atom],
  cases x; cases y; simp only [a_apply_cons, bnot, cond, coe_bcd_eq_pre, coe_fn_coe, coe_fn_mul,
    (∘), eq_self_iff_true, if_false, if_true, not_true, pre.bcd, tail_cons];
    by_cases hn : n = 1; simp only [if_pos, if_false, hn]; refl
end

lemma restr_to_perm_comp_mk (x : bool) :
  (restr_to_perm x).comp mk =
    (subgroup.subtype G).comp (free_monoid.lift (uncurry $ atom_restr x)) :=
by simp only [mk, free_monoid.comp_lift, (∘), uncurry, restr_to_perm_atom, subgroup.coe_subtype]

lemma restr_to_perm_mk (x : bool) (l : free_monoid (bool × fin 3)) :
  restr_to_perm x (mk l) = (free_monoid.lift (uncurry $ atom_restr x) l : G) :=
monoid_hom.congr_fun (restr_to_perm_comp_mk x) l

lemma restr_to_perm_mem (x : bool) : ∀ g, restr_to_perm x g ∈ G :=
mk_surjective.forall.2 $ λ l, (restr_to_perm_mk x l).symm ▸ set_like.coe_mem _

/-- Restrict a head-preserving element of the Grigorchuk group to lists that start with a given
boolean value. -/
def restr (x : bool) : head_preserving →* G :=
(restr_to_perm x).cod_restrict _ $ restr_to_perm_mem x

@[simp] lemma restr_apply (x : bool) (g : H) (l : list bool) :
  restr x g l = (g (x :: l)).tail :=
rfl

lemma restr_atom (x y : bool) (n : fin 3) : restr x (atom y n) = atom_restr x y n :=
subtype.ext $ restr_to_perm_atom x y n

lemma restr_mk (x : bool) (l : free_monoid (bool × fin 3)) :
  restr x (mk l) = free_monoid.lift (uncurry $ atom_restr x) l :=
subtype.ext $ restr_to_perm_mk x l

lemma restr_comp_mk (x : bool) : (restr x).comp mk = free_monoid.lift (uncurry $ atom_restr x) :=
monoid_hom.ext $ restr_mk x

@[simp] lemma range_restr (x : bool) : (restr x).range = ⊤ :=
begin
  have : x ≠ !x, by cases x; dec_trivial,
  simp_rw [← top_le_iff, ← closure_abcd, subgroup.closure_le, ← range_bcd, insert_subset,
    range_subset_iff, set_like.mem_coe],
  refine ⟨⟨atom x 0, _⟩, λ n, ⟨atom (!x) (n - 1), _⟩⟩;
    simp only [restr_atom, atom_restr, sub_add_cancel, if_pos rfl, if_neg zero_ne_one, if_neg this]
end

lemma surjective_restr (b : bool) : surjective (restr b) :=
(subgroup.eq_top_iff' _).mp (range_restr b)

lemma card_eq' : #H = #G := le_antisymm (mk_set_le H) (mk_le_of_surjective $ surjective_restr ff)

instance : countable H := subtype.coe_injective.countable

def atom_restr' (x y : bool) (n : fin 3) : free_monoid (fin 4) :=
if x = y then if n = 1 then 1 else [0] else [(n + 1).succ]

lemma length_atom_restr' (x y : bool) (n : fin 3) :
  length (atom_restr' x y n) = if x = y ∧ n = 1 then 0 else 1 :=
by { rw [atom_restr'], by_cases hxy : x = y; by_cases hn : n = 1; simp [*, free_monoid.one_def] }

@[simp] lemma of_word_atom_restr' (x y : bool) (n : fin 3) :
  of_word (atom_restr' x y n) = atom_restr x y n :=
by { rw [atom_restr, atom_restr'], split_ifs; simp only [map_one, of_word_singleton]; refl }

def mk_restr' (x : bool) : free_monoid (bool × fin 3) →* free_monoid (fin 4) :=
free_monoid.lift (uncurry $ atom_restr' x)

lemma of_word_mk_restr' (x : bool) (l : free_monoid (bool × fin 3)) :
  of_word (mk_restr' x l) = restr x (mk l) :=
by simp only [mk_restr', mk, free_monoid.hom_map_lift, (∘), uncurry, of_word_atom_restr',
  restr_atom]

@[simp] lemma length_mk_restr' (x : bool) (g : free_monoid (bool × fin 3)) :
  length (mk_restr' x g) = length g - count (x, 1) g :=
begin
  induction g with y g ihg, { refl }, cases y with y z,
  simp only [mk_restr', free_monoid.lift_apply, map_cons, prod_cons, free_monoid.mul_def, uncurry,
    length_append, length_atom_restr', length, count_cons', prod.mk.inj_iff, @eq_comm (fin 3) 1]
    at ihg ⊢,
  rw [ihg],
  split_ifs,
  { rw [zero_add, nat.succ_sub_succ_eq_sub] },
  { rw [add_zero, add_comm _ 1, nat.add_sub_assoc],
    exact count_le_length _ _ }
end

lemma length_mk_restr'_le (x : bool) (g : free_monoid (bool × fin 3)) :
  length (mk_restr' x g) ≤ length g :=
(length_mk_restr' x g).trans_le tsub_le_self

lemma length_mk_restr'_le_length_mk' (x : bool) (g : free_monoid (bool × fin 3)) :
  length (mk_restr' x g) ≤ length (mk' g) :=
(length_mk_restr'_le x g).trans (le_length_mk' _)

lemma length_mk_restr'_lt_length_mk' {x : bool} {g : free_monoid (bool × fin 3)} :
  length (mk_restr' x g) < length (mk' g) ↔
    tt ∈ map prod.fst g ∨ @has_mem.mem _ (list _) _ (x, (1 : fin 3)) g :=
by rw [length_mk_restr', length_mk', tsub_lt_iff_right (count_le_length _ _), add_assoc,
  lt_add_iff_pos_right, add_pos_iff, count_pos, two_mul, add_pos_iff, or_self, count_pos]

lemma forall_length_mk_restr'_lt_length_mk' {g : free_monoid (bool × fin 3)}
  (hg : is_minimal (mk' g)) :
  (∀ x, length (mk_restr' x g) < length (mk' g)) ↔ g ≠ [] ∧ ∀ n, g ≠ [(ff, n)] :=
begin
  simp only [length_mk_restr'_lt_length_mk'],
  refine ⟨λ h, _, λ h x, _⟩,
  { simp only [ne.def, ← not_exists, ← not_or_distrib],
    rintro (rfl|⟨n, rfl⟩); simpa using h tt },
  { rcases exists_cons_of_ne_nil h.1 with ⟨y, g, rfl⟩,
    left,
    cases g with z g,
    { rw [map_singleton, list.mem_singleton, eq_comm],
      rcases y with ⟨_|_, n⟩,
      exacts [(h.2 n rfl).elim, rfl] },
    { rw [map_cons, map_cons, mem_cons_iff, mem_cons_iff, ← or_assoc],
      left,
      have : y.1 ≠ z.1 := hg.chain'_ne_fst.rel_head,
      cases z.1,
      { left, symmetry, simpa using this },
      { exact or.inr rfl } } }
end

lemma two_mul_length_mk_restr'_le_length_mk'_succ {x : bool} {g : free_monoid (bool × fin 3)}
  (hmin : is_minimal (mk' g)) :
  2 * length (mk_restr' x g) ≤ length (mk' g) + 1 :=
begin
  rw [length_mk_restr', length_mk', mul_tsub, tsub_le_iff_right, add_assoc, add_assoc, two_mul,
    add_le_add_iff_left, ← tsub_le_iff_right],
  refine le_trans _ (hmin.chain'_ne_map_fst.length_sub_one_le_two_mul_count_bool _),
  rw [length_map],
  exact tsub_le_tsub_left (le_add_right le_rfl) _
end

lemma two_mul_length_mk_restr'_le_length_mk' {x : bool} {g : free_monoid (bool × fin 3)}
  (hmin : is_minimal (mk' g)) (he : even (length g)) :
  2 * length (mk_restr' x g) ≤ length (mk' g) :=
begin
  refine nat.lt_succ_iff.1
    (lt_of_le_of_ne (two_mul_length_mk_restr'_le_length_mk'_succ hmin) $ λ h, _),
  rw [← @not_not (even _), ← even_length_mk', ← nat.even_add_one, ← nat.succ_eq_add_one, ← h] at he,
  exact he (even_two_mul _)
end

lemma two_mul_length_mk_restr'_lt_length_mk' {x : bool} {g : free_monoid (bool × fin 3)}
  (hmin : is_minimal (mk' g)) (he : even (length g)) :
  2 * length (mk_restr' x g) < length (mk' g) ↔ @has_mem.mem _ (list (bool × fin 3)) _ (x, 1) g :=
begin
  rw [length_mk_restr', length_mk', mul_tsub,
    tsub_lt_iff_right (mul_le_mul_left' (count_le_length _ _) _), add_assoc, two_mul,
    add_lt_add_iff_left, hmin.chain'_ne_map_fst.two_mul_count_bool_of_even, length_map,
    lt_add_iff_pos_right, two_mul, add_pos_iff, or_self, count_pos],
  rwa [length_map]
end

lemma restr_injective' {g₁ g₂} (h : ∀ x, restr x g₁ = restr x g₂) : g₁ = g₂ :=
begin
  refine subtype.ext (fun_like.ext _ _ $ λ l, _),
  cases l with hd tl, { simp only [apply_nil] },
  erw [← cons_tail_apply g₁.coe_prop, ← cons_tail_apply g₂.coe_prop, ← restr_apply, h,
    ← restr_apply]
end

lemma restr_injective : injective (λ g, (restr ff g, restr tt g)) :=
λ g₁ g₂ h, restr_injective' $ bool.forall_bool.2 (prod.mk.inj_iff.1 h)

end head_preserving

section head_preserving

open head_preserving

instance : infinite G :=
⟨λ h, (@mk_set_lt _ h a H a_nmem).ne card_eq'⟩

instance : infinite H := infinite_iff.mpr $ (aleph_0_le_mk G).trans_eq card_eq'.symm

lemma of_word_pow_two_pow_length (g : free_monoid (fin 4)) : of_word g ^ (2 ^ length g) = 1 :=
begin
  have Hle : ∀ {g} {k l : ℕ}, k ≤ l → of_word g ^ 2 ^ k = 1 → of_word g ^ 2 ^ l = 1,
  { intros g k l hle h1,
    rw [← add_tsub_cancel_of_le hle, pow_add, pow_mul, h1, one_pow] },
  induction hN : length g using nat.strong_induction_on with N ihN generalizing g,
  replace ihN : ∀ g' : free_monoid (fin 4), length g' < N → of_word g' ^ 2 ^ length g' = 1,
    from λ g' hg', ihN _ hg' _ rfl,
  revert g, -- TODO: use the new `wlog`
  suffices : ∀ g : free_monoid (fin 4), length g = N → is_minimal g → of_word g ^ 2 ^ N = 1,
  { rintro g rfl,
    rcases exists_is_minimal_of_word_eq (of_word g) with ⟨g', hmin, hg'⟩,
    cases (hmin g hg').eq_or_lt with hlen hlt,
    { rw [← hg', this g' hlen hmin] },
    { rw [← hg', Hle hlt.le (ihN _ hlt)] } },
  have hH : ∀ g : free_monoid (fin 4), length g = N → is_minimal g → of_word g ∈ H →
    of_word g ^ 2 ^ N = 1,
  { rintro g rfl hmin hmem,
    rcases exists_mk_eq ⟨of_word g, hmem⟩ with ⟨l, hlg, hl⟩,
    rw [← subtype.coe_inj, subtype.coe_mk, ← of_word_mk'] at hlg,
    rw [hmin.length_eq hl hlg.symm] at ihN ⊢,
    rw [← hlg],
    clear hlg hmin hmem g,
    by_cases hlt : ∀ x, length (mk_restr' x l) < length (mk' l),
    { suffices : mk l ^ 2 ^ length (mk' l) = 1,
        by rw [of_word_mk', ← subgroup.coe_pow, this, subgroup.coe_one],
      refine restr_injective' (λ x, _),
      rw [map_pow, map_one, ← of_word_mk_restr', Hle (hlt _).le (ihN _ (hlt _))] },
    { rw [forall_length_mk_restr'_lt_length_mk' hl, ne.def, ← not_exists, ← not_or_distrib, not_not]
        at hlt,
      rcases hlt with rfl|⟨n, rfl⟩,
      { refl },
      { rw [mk'_singleton, of_word_atom', cond, length_atom', cond, pow_one, sq,
          bcd_mul_self] } } },
  have hnomin : ∀ g : free_monoid (fin 4), length g = N → is_minimal g → ¬is_minimal (g ^ 2) →
    of_word g ^ 2 ^ N = 1,
  { rintro g rfl hmin hmin₂,
    rcases exists_mk_eq ⟨of_word g^2, sq_mem _⟩ with ⟨g', h', hmin'⟩,
    have hlt : length (mk' g') < 2 * length g,
  },


  -- induction; WLOG, `g` is a minimal word
  -- suffices : ∀ g, is_minimal g →
  --   (∀ g' : free_monoid (fin 4), length g' < length g → of_word g' ^ (2 ^ length g') = 1) →
  --   of_word g ^ (2 ^ length g) = 1,
  -- { induction hn : length g using nat.strong_induction_on with n' ihn generalizing g, subst n',
  --   exact ihn _ (hg'.trans_le (length_to_word_of_word_le _)) _ rfl },
  -- clear g, intros g hmin ihg,
  -- -- Trivial cases `g = []` and `g = [_]`
  -- cases lt_or_le (length g) 2 with h₂ h₂,
  -- { cases g with n g, { exact one_pow _ },
  --   cases g with m g, { rw [length_singleton, pow_one, of_word_singleton, sq, abcd_mul_self] },
  --   exact absurd h₂ (by simp [bit0]) },

end

lemma exists_pow_two_pow_eq_one (g : G) : ∃ k : ℕ, g ^ (2 ^ k) = 1 :=
begin


end

end head_preserving

lemma exists_eta : ∃ η ∈ Ioo (0.81053 : ℝ) 0.81054, η ^ 3 + η ^ 2 + η = (2 : ℝ) :=
mem_image_iff_bex.1 $ intermediate_value_Ioo (by norm_num)
  (continuous.continuous_on $ by continuity) (by norm_num)

def eta : ℝ := exists_eta.some

local notation `η` := grigorchuk_group.eta

lemma eta_gt_081053 : 0.81053 < η := exists_eta.some_spec.fst.1
lemma eta_lt_081054 : η < 0.81054 := exists_eta.some_spec.fst.2

lemma eta_pos : 0 < η := lt_trans (by norm_num) eta_gt_081053
lemma eta_lt_one : η < 1 := eta_lt_081054.trans (by norm_num)
lemma eta_lt_two : η < 2 := eta_lt_one.trans one_lt_two

def alpha : ℝ := log 2 / log (2 / η)

local notation `α` := alpha

lemma alpha_lt_one : α < 1 :=
(div_lt_one $ log_pos $ (one_lt_div eta_pos).2 eta_lt_two).2 $
  log_lt_log two_pos $ (lt_div_iff eta_pos).2 $
  calc 2 * η < 2 * 1 : (mul_lt_mul_left two_pos).2 eta_lt_one
  ... = 2 : mul_one _

/-
definitions: normed group, multiplication operation.
definition: equiv. of norms
lemma: for f.g. group, canonical equiv. class of norms

definition: growth of a group = function gamma(n) = #{g in G | |g|<=n}.
definition: gamma ≾, (asymptotic domination) delta if exist C: gamma(n)<=delta(C n). ~ equiv relation.
lemma: independent of choice of metric, for f.g. group

theorem: exp(C n^(1/2)) <= gamma(n) <= exp(C n^alpha)
theorem: exp(n^(1/2)) <~ gamma(n) <~ exp(n^alpha)

-------------------------------------------------
H subgroup of index 2
|.| on G, defined using eta

psi: H -> GxG.

1) psi almost bijection: injective, image has index 8.

2) if psi(h) = (g_0,g_1), then |g_0|+|g_1| <= eta*(|h|+|a|)
              (so: "essentially" gamma(n) <= 1/2 gamma(eta n)^2, by finding good g_0,g_1)
--> upper bound

3) similarly, |h| <= 2(|g_0|+|g_1|) + constant
              (so: "essentially" gamma(n) >= 8gamma(n/2)^2, by finding good h)
--> lower bound

-/

end grigorchuk_group
