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

def inl : M →* M ⋆ N :=
⟨λ x, con.mk' _ (free_monoid.of (sum.inl x)), (con.eq _).2 $ λ c hc, hc.2.2.1,
  λ x y, (con.eq _).2 $ λ c hc, hc.1 x y⟩

def inr : N →* M ⋆ N :=
⟨λ x, con.mk' _ (free_monoid.of (sum.inr x)), (con.eq _).2 $ λ c hc, hc.2.2.2,
  λ x y, (con.eq _).2 $ λ c hc, hc.2.1 x y⟩

def clift (f : free_monoid (M ⊕ N) →* P)
  (hM₁ : f (of (sum.inl 1)) = 1) (hN₁ : f (of (sum.inr 1)) = 1)
  (hM : ∀ x y, f (of (sum.inl (x * y))) = f (of (sum.inl x) * of (sum.inl y)))
  (hN : ∀ x y, f (of (sum.inr (x * y))) = f (of (sum.inr x) * of (sum.inr y))) :
  M ⋆ N →* P :=
con.lift _ f $ Inf_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

@[simp] lemma clift_apply_inl (f : free_monoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : M) :
  clift f hM₁ hN₁ hM hN (inl x) = f (free_monoid.of (sum.inl x)) :=
rfl

@[simp] lemma clift_apply_inr (f : free_monoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : N) :
  clift f hM₁ hN₁ hM hN (inr x) = f (free_monoid.of (sum.inr x)) :=
rfl

def lift (f : M →* P) (g : N →* P) : M ⋆ N →* P :=
clift (free_monoid.lift $ sum.elim f g)
  (by simp only [lift_eval_of, sum.elim_inl, map_one])
  (by simp only [lift_eval_of, sum.elim_inr, map_one])
  (λ x y, by simp only [lift_eval_of, sum.elim_inl, map_mul])
  (λ x y, by simp only [lift_eval_of, sum.elim_inr, map_mul])

@[simp] lemma lift_apply_inl (f : M →* P) (g : N →* P) (x : M) :
  lift f g (inl x) = f x :=
(clift_apply_inl _ _ _ _ _ _).trans (free_monoid.lift_eval_of _ _)

@[simp] lemma lift_comp_inl (f : M →* P) (g : N →* P) : (lift f g).comp inl = f :=
fun_like.ext _ _ $ lift_apply_inl f g

@[simp] lemma lift_apply_inr (f : M →* P) (g : N →* P) (x : N) :
  lift f g (inr x) = g x :=
(clift_apply_inr _ _ _ _ _ _).trans (free_monoid.lift_eval_of _ _)

@[simp] lemma lift_comp_inr (f : M →* P) (g : N →* P) : (lift f g).comp inr = g :=
fun_like.ext _ _ $ lift_apply_inr f g

@[simp] lemma mclosure_range_inl_union_inr :
  submonoid.closure (range inl ∪ range inr : set (M ⋆ N)) = ⊤ :=
by { rw [← con.mrange_mk', monoid_hom.mrange_eq_map, ← free_monoid.closure_range_of,
         monoid_hom.map_mclosure, ← range_comp, sum.range_eq], refl }

@[simp] lemma mrange_inl_sup_mrange_inr :
  (inl : M →* M ⋆ N).mrange ⊔ (inr : N →* M ⋆ N).mrange = ⊤ :=
by rw [← mclosure_range_inl_union_inr, submonoid.closure_union, ← monoid_hom.coe_mrange,
  ← monoid_hom.coe_mrange, submonoid.closure_eq, submonoid.closure_eq]

def lift_equiv : (M ⋆ N →* P) ≃ (M →* P) × (N →* P) :=
{ to_fun := λ f, ⟨f.comp inl, f.comp inr⟩,
  inv_fun := λ fg, lift fg.1 fg.2,
  left_inv := λ f, monoid_hom.eq_of_eq_on_mdense mclosure_range_inl_union_inr $ eq_on_union.2
    ⟨eq_on_range.2 $ funext $ lift_apply_inl _ _, eq_on_range.2 $ funext $ lift_apply_inr _ _⟩,
  right_inv := λ ⟨f, g⟩, prod.ext (lift_comp_inl _ _) (lift_comp_inr _ _) }

def fst : M ⋆ N →* M := lift (monoid_hom.id M) 1

def snd : M ⋆ N →* N := lift 1 (monoid_hom.id N)

def to_prod : M ⋆ N →* M × N := lift (monoid_hom.inl _ _) (monoid_hom.inr _ _)

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



@[ext] structure word (M N : Type*) [monoid M] [monoid N] :=
(to_list : list (M ⊕ N))
(inl_one_nmem : sum.inl 1 ∉ to_list)
(inr_one_nmem : sum.inr (1 : N) ∉ to_list)
(chain'_rel : to_list.chain' ncword_rel)

namespace word

instance : has_one (word M N) := ⟨⟨[], not_mem_nil _, not_mem_nil _, chain'_nil⟩⟩

@[simp] lemma to_list_one : (1 : word M N).to_list = [] := rfl
@[simp] lemma mk_nil (h₁ h₂ h₃) : (mk [] h₁ h₂ h₃ : word M N) = 1 := rfl

@[simp] lemma mk_to_list (w : word M N) (h₁ := w.2) (h₂ := w.3) (h₃ := w.4) :
  mk w.1 h₁ h₂ h₃ = w :=
ext _ _ rfl

variables [decidable_eq M] [decidable_eq N]

def cons' (x : M ⊕ N) (w : word M N) (h : chain' ncword_rel (x :: w.to_list)) : word M N :=
if hx : x ≠ sum.inl 1 ∧ x ≠ sum.inr 1
then ⟨x :: w.to_list, not_or_distrib.2 ⟨hx.1.symm, w.2⟩, not_or_distrib.2 ⟨hx.2.symm, w.3⟩, h⟩
else w

lemma mk_cons {x : M ⊕ N} {l : list (M ⊕ N)} (h₁ h₂ h₃) :
  mk (x :: l) h₁ h₂ h₃ =
    cons' x ⟨l, (not_or_distrib.1 h₁).2, (not_or_distrib.1 h₂).2, h₃.tail⟩ h₃ :=
eq.symm $ dif_pos ⟨ne.symm (not_or_distrib.1 h₁).1, ne.symm (not_or_distrib.1 h₂).1⟩

@[simp] lemma cons'_inl_one {w : word M N} (hw) :
  cons' (sum.inl 1) w hw = w :=
dif_neg $ by simp

@[simp] lemma cons'_inr_one {w : word M N} (hw) :
  cons' (sum.inr 1) w hw = w :=
dif_neg $ by simp

def of (x : M ⊕ N) : word M N := cons' x 1 (chain'_singleton _)

@[simp] lemma cons'_one (x : M ⊕ N) (h := chain'_singleton _) : cons' x 1 h = of x := rfl
@[simp] lemma of_inl_one : of (sum.inl 1 : M ⊕ N) = 1 := cons'_inl_one _
@[simp] lemma of_inr_one : of (sum.inr 1 : M ⊕ N) = 1 := cons'_inr_one _

def cons : M ⊕ N → word M N → word M N
| x ⟨[], _, _, _⟩ := of x
| (sum.inl x) ⟨sum.inl y :: l, hl, hr, h⟩ :=
  cons' (sum.inl (x * y)) ⟨l, mt (mem_cons_of_mem _) hl, mt (mem_cons_of_mem _) hr, h.tail⟩ $
    h.imp_head $ λ z, id
| (sum.inl x) ⟨sum.inr y :: l, hl, hr, h⟩ :=
  cons' (sum.inl x) ⟨sum.inr y :: l, hl, hr, h⟩ (h.cons $ by simp)
| (sum.inr x) ⟨sum.inl y :: l, hl, hr, h⟩ :=
  cons' (sum.inr x) ⟨sum.inl y :: l, hl, hr, h⟩ (h.cons $ by simp)
| (sum.inr x) ⟨sum.inr y :: l, hl, hr, h⟩ :=
  cons' (sum.inr (x * y)) ⟨l, mt (mem_cons_of_mem _) hl, mt (mem_cons_of_mem _) hr, h.tail⟩ $
    h.imp_head $ λ z, id

@[simp] lemma cons_one (x : M ⊕ N) : cons x 1 = of x := by cases x; refl

@[simp] lemma cons_inl_one (w : word M N) : cons (sum.inl 1) w = w :=
begin
  rcases w with ⟨(_|⟨(x|x), l⟩), hl, hr, hc⟩,
  { simp },
  { simp_rw [cons, one_mul, mk_cons], refl },
  { simp_rw [cons, cons'_inl_one, eq_self_iff_true, true_and] }
end

@[simp] lemma cons_inr_one (w : word M N) : cons (sum.inr 1) w = w :=
begin
  rcases w with ⟨(_|⟨(x|x), l⟩), hl, hr, hc⟩,
  { simp },
  { simp_rw [cons, cons'_inr_one, eq_self_iff_true, true_and] },
  { simp_rw [cons, one_mul, mk_cons], refl },
end

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
      simp only [mul_def, smul_def, to_list_of_list, foldr_cons, mem_cons_iff, not_or_distrib]
        at hl hr ⊢ ihw,
      specialize ihw hl.2 hr.2 hc.tail,
      rw [ihw, ← cons'_eq_cons, cons', dif_pos (and.intro (ne.symm hl.1) (ne.symm hr.1))], refl
    end,
  .. word.has_one, .. word.has_mul }

lemma cons'_inl_mul {x y : M} {w : word M N} (h) :
  cons' (sum.inl (x * y)) w h = cons (sum.inl x) (cons' (sum.inl y) w (h.imp_head $ λ _, id)) :=
begin
  rcases eq_or_ne x 1 with rfl|hx, { simp only [one_mul, cons_inl_one] },
  rcases eq_or_ne y 1 with rfl|hy, { simp only [cons'_eq_cons, cons_inl_one, mul_one] },
  simp only [cons', dif_neg, dif_pos, hy, ne.def, not_false_iff, and_true, cons, mk_to_list]
end

lemma cons'_inr_mul {x y : N} {w : word M N} (h) :
  cons' (sum.inr (x * y)) w h = cons (sum.inr x) (cons' (sum.inr y) w (h.imp_head $ λ _, id)) :=
begin
  rcases eq_or_ne x 1 with rfl|hx, { simp only [one_mul, cons_inr_one] },
  rcases eq_or_ne y 1 with rfl|hy, { simp only [cons'_eq_cons, cons_inr_one, mul_one] },
  simp only [cons', dif_neg, dif_pos, hy, ne.def, not_false_iff, and_true, cons, mk_to_list]
end

lemma of_mul (x : M ⊕ N) (w : word M N) : of x * w = cons x w :=
begin
  rcases eq_or_ne x (sum.inl 1) with rfl|hxl, { simp },
  rcases eq_or_ne x (sum.inr 1) with rfl|hxr, { simp },
  simp only [of, cons', dif_pos (and.intro hxl hxr), mul_def, smul_def, to_list_of_list,
    to_list_one, foldr]
end

def inl : M →* word M N :=
{ to_fun := λ x, of (sum.inl x),
  map_one' := of_inl_one,
  map_mul' := λ x y, by rw [of, cons'_inl_mul, ← of_mul, cons'_one] }

def inr : N →* word M N :=
{ to_fun := λ x, of (sum.inr x),
  map_one' := of_inr_one,
  map_mul' := λ x y, by rw [of, cons'_inr_mul, ← of_mul, cons'_one] }

lemma of_inl (x : M) : of (sum.inl x) = (inl x : word M N) := rfl
lemma of_inr (x : N) : of (sum.inr x) = (inr x : word M N) := rfl

lemma cons'_mul (x : M ⊕ N) (w₁ w₂ : word M N) (h) : cons' x w₁ h * w₂ = cons x (w₁ * w₂) :=
begin
  rw [cons'],
  split_ifs with hx,
  { simp only [mul_def, smul_def, to_list_of_list, foldr] },
  { simp only [not_and_distrib, ne.def, not_not] at hx,
    rcases hx with (rfl|rfl); simp only [cons_inl_one, cons_inr_one] }
end

lemma cons_inl_mul (x y : M) (w : word M N) :
  cons (sum.inl (x * y)) w = cons (sum.inl x) (cons (sum.inl y) w) :=
begin
  rcases w with ⟨(_|⟨(z|z), l⟩), hl, hr, hc⟩,
  { simp only [mk_nil, mul_one, ← of_mul, of_inl, map_mul] },
  { simp only [cons, mul_assoc, cons'_inl_mul] },
  { simp only [cons, cons'_inl_mul] }
end

lemma cons_inr_mul (x y : N) (w : word M N) :
  cons (sum.inr (x * y)) w = cons (sum.inr x) (cons (sum.inr y) w) :=
begin
  rcases w with ⟨(_|⟨(z|z), l⟩), hl, hr, hc⟩,
  { simp only [mk_nil, mul_one, ← of_mul, of_inr, map_mul] },
  { simp only [cons, cons'_inr_mul] },
  { simp only [cons, mul_assoc, cons'_inr_mul] }
end

lemma cons_mul (x : M ⊕ N) (w₁ w₂ : word M N) : cons x (w₁ * w₂) = cons x w₁ * w₂ :=
begin
  rcases w₁ with ⟨(_|⟨y, l⟩), hl, hr, hc⟩,
  { simp only [mk_nil, cons_one, one_mul, of_mul] },
  rw [mul_def, smul_def, to_list_of_list, foldr_cons],
  cases x; cases y,
  { simp_rw [cons, cons'_mul, cons_inl_mul], refl },
  { simp_rw [cons, cons'_mul], refl },
  { simp_rw [cons, cons'_mul], refl },
  { simp_rw [cons, cons'_mul, cons_inr_mul], refl }
end

instance : is_scalar_tower (free_monoid (M ⊕ N)) (word M N) (word M N) :=
is_scalar_tower.of_mclosure_eq_top free_monoid.closure_range_of $ forall_range_iff.2 $ λ x w₁ w₂,
  by simp only [free_monoid.of_smul, smul_eq_mul, cons_mul]

instance : monoid (word M N) :=
{ mul_assoc := λ a b c, smul_assoc (of_list a.to_list) b c,
  .. word.mul_one_class }

variables {G H : Type*} [group G] [group H] [decidable_eq G] [decidable_eq H]

instance : has_inv (word G H) :=
⟨λ w, ⟨(w.to_list.map (sum.map has_inv.inv has_inv.inv)).reverse,
    by simpa only [mem_reverse, mem_map, sum.exists, sum.map_inl, sum.map_inr, inv_eq_one,
      false_and, exists_false, or_false, @and.comm _ (_ = _), exists_eq_left] using w.2,
    by simpa only [mem_reverse, mem_map, sum.exists, sum.map_inl, sum.map_inr, inv_eq_one,
      false_and, exists_false, false_or, @and.comm _ (_ = _), exists_eq_left] using w.3,
    chain'_reverse.2 ((chain'_map _).2 $ w.4.imp $ λ a b h, by cases a; cases b; assumption)⟩⟩

lemma to_list_inv (w : word G H) :
  (w⁻¹).to_list = (w.to_list.map (sum.map has_inv.inv has_inv.inv)).reverse :=
rfl

instance : group (word G H) :=
{ mul_left_inv := λ ⟨l, hl, hr, hc⟩,
    begin
      induction l with x l ihl, { refl },
      specialize ihl (mt (mem_cons_of_mem _) hl) (mt (mem_cons_of_mem _) hr) hc.tail,
      simp only [to_list_inv, map_cons, mul_def, reverse_cons, smul_def, to_list_of_list,
        foldr_append, foldr] at ihl ⊢,
      cases x;
        simpa only [sum.map_inl, sum.map_inr, cons, inv_mul_self, cons'_inl_one, cons'_inr_one]
    end,
  .. word.monoid, .. word.has_inv }

end word

end free_prod
