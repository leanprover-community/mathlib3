import group_theory.subgroup.basic
import group_theory.congruence
import group_theory.submonoid.membership

/-!
-/

open free_monoid function list set

def free_prod_con (M N : Type*) [monoid M] [monoid N] :
  con (free_monoid (M ⊕ N)) :=
Inf {c |
  (∀ x y : M, c (of (sum.inl (x * y))) (of (sum.inl x) * of (sum.inl y)))
  ∧ (∀ x y : N, c (of (sum.inr (x * y))) (of (sum.inr x) * of (sum.inr y)))
  ∧ c (of $ sum.inl 1) 1 ∧ c (of $ sum.inr 1) 1}

@[derive monoid] def free_prod (M N : Type*) [monoid M] [monoid N] := (free_prod_con M N).quotient

local infix ` ⋆ `:70 := free_prod

namespace free_prod

variables {M N P : Type*} [monoid M] [monoid N] [monoid P]

def lift (f : free_monoid (M ⊕ N) →* P)
  (hM₁ : f (of (sum.inl 1)) = 1) (hN₁ : f (of (sum.inr 1)) = 1)
  (hM : ∀ x y, f (of (sum.inl (x * y))) = f (of (sum.inl x) * of (sum.inl y)))
  (hN : ∀ x y, f (of (sum.inr (x * y))) = f (of (sum.inr x) * of (sum.inr y))) :
  M ⋆ N →* P :=
con.lift _ f $ Inf_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

def lift₂ (f : M →* P) (g : N →* P) : M ⋆ N →* P :=
lift (free_monoid.lift $ sum.elim f g)
  (by simp only [lift_eval_of, sum.elim_inl, map_one])
  (by simp only [lift_eval_of, sum.elim_inr, map_one])
  (λ x y, by simp only [lift_eval_of, sum.elim_inl, map_mul])
  (λ x y, by simp only [lift_eval_of, sum.elim_inr, map_mul])

def fst : M ⋆ N →* M := lift₂ (monoid_hom.id M) 1

def snd : M ⋆ N →* N := lift₂ 1 (monoid_hom.id N)

def to_prod : M ⋆ N →* M × N := lift₂ (monoid_hom.inl _ _) (monoid_hom.inr _ _)

def mk : free_monoid (M ⊕ N) →* M ⋆ N := con.mk' _

@[simp] lemma con_ker_mk : con.ker mk = free_prod_con M N := con.mk'_ker _

lemma mk_surjective : surjective (@mk M N _ _) := surjective_quot_mk _

@[simp] lemma mrange_mk : (@mk M N _ _).mrange = ⊤ :=
monoid_hom.mrange_top_iff_surjective.2 mk_surjective

@[derive decidable_rel]
def ncword_rel (x y : M ⊕ N) : Prop := bxor x.is_left y.is_left

lemma forall_not_ncword_rel {r : M ⊕ N → M ⊕ N → Prop} :
  (∀ x y, ¬ncword_rel x y → r x y) ↔
    (∀ x y, r (sum.inl x) (sum.inl y)) ∧ (∀ x y, r (sum.inr x) (sum.inr y)) :=
sum.forall.trans $ and_congr
  (forall_congr $ λ x, sum.forall.trans $ by simp [ncword_rel])
  (forall_congr $ λ x, sum.forall.trans $ by simp [ncword_rel])

lemma forall_ncword_rel {r : M ⊕ N → M ⊕ N → Prop} :
  (∀ x y, ncword_rel x y → r x y) ↔
    (∀ x y, r (sum.inl x) (sum.inr y)) ∧ (∀ x y, r (sum.inr x) (sum.inl y)) :=
sum.forall.trans $ and_congr
  (forall_congr $ λ x, sum.forall.trans $ by simp [ncword_rel])
  (forall_congr $ λ x, sum.forall.trans $ by simp [ncword_rel])

@[simp] lemma ncword_rel_inl {x : M} {y : M ⊕ N} : ncword_rel (sum.inl x) y ↔ sum.is_right y :=
by cases y; simp [ncword_rel]

@[simp] lemma ncword_rel_inr {x : N} {y : M ⊕ N} : ncword_rel (sum.inr x) y ↔ sum.is_left y :=
by cases y; simp [ncword_rel]

section dec_eq

@[ext] structure word (M N : Type*) [monoid M] [monoid N] :=
(to_list : list (M ⊕ N))
(ne_one_left : ∀ x ∈ to_list, x ≠ sum.inl (1 : M))
(ne_one_right : ∀ x ∈ to_list, x ≠ sum.inr (1 : N))
(chain'_rel : to_list.chain' ncword_rel)

namespace word

instance : has_one (word M N) := ⟨⟨[], λ x, false.elim, λ x, false.elim, chain'_nil⟩⟩

@[simp] lemma to_list_one : (1 : word M N).to_list = [] := rfl

variables [decidable_eq M] [decidable_eq N]

def cons' (x : M ⊕ N) (w : word M N) (h : chain' ncword_rel (x :: w.to_list)) : word M N :=
if hx : x ≠ sum.inl 1 ∧ x ≠ sum.inr 1
then ⟨x :: w.to_list, forall_mem_cons.2 ⟨hx.1, w.2⟩, forall_mem_cons.2 ⟨hx.2, w.3⟩, h⟩
else w

def of (x : M ⊕ N) : word M N := cons' x 1 (chain'_singleton _)

def cons : M ⊕ N → word M N → word M N
| x ⟨[], _, _, _⟩ := of x
| (sum.inl x) ⟨sum.inl y :: l, hl, hr, h⟩ :=
  cons' (sum.inl (x * y)) ⟨l, (forall_mem_cons.1 hl).2, (forall_mem_cons.1 hr).2, h.tail⟩ $
    h.imp_head $ λ z, id
| (sum.inl x) ⟨sum.inr y :: l, hl, hr, h⟩ :=
  cons' (sum.inl x) ⟨sum.inr y :: l, hl, hr, h⟩ (h.cons $ by simp)
| (sum.inr x) ⟨sum.inl y :: l, hl, hr, h⟩ :=
  cons' (sum.inr x) ⟨sum.inl y :: l, hl, hr, h⟩ (h.cons $ by simp)
| (sum.inr x) ⟨sum.inr y :: l, hl, hr, h⟩ :=
  cons' (sum.inr (x * y)) ⟨l, (forall_mem_cons.1 hl).2, (forall_mem_cons.1 hr).2, h.tail⟩ $
    h.imp_head $ λ z, id

@[simp] lemma cons_one (x : M ⊕ N) : cons x 1 = of x := by cases x; refl

lemma cons'_eq_cons {x : M ⊕ N} {w : word M N} (h : chain' ncword_rel (x :: w.to_list)) :
  cons' x w h = cons x w :=
by cases x; rcases w with ⟨(_|⟨(_|_), _⟩), _, _, _⟩; try { refl }; apply absurd h.rel_head; simp

instance : mul_action (free_monoid (M ⊕ N)) (word M N) := free_monoid.mk_mul_action cons

instance : has_mul (word M N) := ⟨λ w₁ w₂, free_monoid.of_list w₁.to_list • w₂⟩

lemma mul_def (w₁ w₂ : word M N) : w₁ * w₂ = free_monoid.of_list w₁.to_list • w₂ := rfl

instance : mul_one_class (word M N) :=
{ one_mul := λ w, rfl,
  mul_one := λ ⟨w, hl, hr, hc⟩,
    begin
      induction w with x w ihw, { refl },
      simp only [forall_mem_cons, mul_def, smul_def, to_list_of_list, foldr_cons] at hl hr ⊢ ihw,
      specialize ihw hl.2 hr.2 hc.tail,
      rw [ihw, ← cons'_eq_cons, cons', dif_pos (and.intro hl.1 hr.1)]
    end,
  .. word.has_one, .. word.has_mul }

instance : is_scalar_tower (free_monoid (M ⊕ N)) (word M N) (word M N) :=
is_scalar_tower.of_mclosure_eq_top free_monoid.closure_range_of $ forall_range_iff.2 $ λ x w₁ w₂,


end dec_eq

end word

end free_prod
