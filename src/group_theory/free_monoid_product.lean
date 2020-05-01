import algebra.free_monoid group_theory.congruence tactic.simp_rw algebra.opposites

open opposite

variables {ι : Type*} (M : Π i : ι, Type*)

section

open free_monoid (of)

def free_monoid_product.con [Π i, monoid (M i)] : con (free_monoid $ Σ i, M i) :=
Inf {r | (∀ i x y, r (of ⟨i, x * y⟩) (of ⟨i, x⟩ * of ⟨i, y⟩)) ∧ (∀ i, r (of ⟨i, 1⟩) 1)}

def free_monoid_product [Π i, monoid (M i)] := (free_monoid_product.con M).quotient

end

namespace free_monoid_product

variables [Π i, monoid (M i)]

instance : monoid (free_monoid_product M) := (con M).monoid

def mk : free_monoid (Σ i, M i) →* free_monoid_product M :=
(con M).mk'

def of (i : ι) : M i →* free_monoid_product M :=
{ to_fun := λ x, mk M (free_monoid.of ⟨i, x⟩),
  map_one' := (con M).eq.2 $ λ r hr, hr.2 i,
  map_mul' := λ x y, (con M).eq.2 $ λ r hr, hr.1 i x y }

variable {M}

lemma mk_apply (x) : mk M x = (con M).mk' x := rfl

@[simp] lemma quot_mk_eq_mk (x) : quot.mk (@setoid.r _ (con M).to_setoid) x = mk M x := rfl

lemma of_apply (i : ι) (x : M i) : of M i x = mk M (free_monoid.of ⟨i, x⟩) := rfl

lemma mk_cons' (i : ι) (x : M i) (tl : free_monoid (Σ i, M i)) :
  mk M (⟨i, x⟩ :: tl) = of M i x * mk M tl :=
rfl

lemma mk_cons (hd : Σ i, M i) (tl : free_monoid (Σ i, M i)) :
  mk M (hd :: tl) = of M hd.fst hd.snd * mk M tl :=
by { cases hd, refl }

lemma mk_eq_mk {x y} : mk M x = mk M y ↔ con M x y := (con M).eq

lemma of_one (i : ι) : of M i 1 = 1 := (of M i).map_one

lemma of_mul (i : ι) (x y : M i) : of M i (x * y) = of M i x * of M i y :=
(of M i).map_mul x y

lemma induction_on {C : free_monoid_product M → Prop} (y : free_monoid_product M)
  (h : ∀ x, C (mk M x)) : C y :=
con.induction_on y h

lemma induction_on' {C : free_monoid_product M → Prop} (y : free_monoid_product M)
  (h1 : C 1) (hcons : ∀ i x l, C l → C ((of M i x) * l)) : C y :=
induction_on y $ λ l, list.rec_on l h1 $ λ ⟨i, x⟩ tl htl, hcons i x (mk M tl) htl

def lift_on {β : Type*} (x : free_monoid_product M) (f : free_monoid (Σ i, M i) → β)
  (hmul : ∀ ⦃x₁ x₂⦄ (hx : f x₁ = f x₂) ⦃y₁ y₂⦄ (hy : f y₁ = f y₂), f (x₁ * y₁) = f (x₂ * y₂))
  (h1 : ∀ i, f (free_monoid.of ⟨i, 1⟩) = f 1)
  (h : ∀ i x y, f (free_monoid.of ⟨i, x * y⟩) = f (free_monoid.of ⟨i, x⟩ * free_monoid.of ⟨i, y⟩)) :
  β :=
con.lift_on x f $ λ a b hab,
  hab { mul' := λ _ _ _ _ h₁ h₂, hmul h₁ h₂, .. setoid.comap f ⊥ } $ ⟨h, h1⟩

lemma hom_eq {N : Type*} [monoid N]  ⦃f g : free_monoid_product M →* N⦄
  (h : ∀ i x, f (of M i x) = g (of M i x)) : f = g :=
(monoid_hom.cancel_right con.mk'_surjective).1 $ free_monoid.hom_eq $ λ ⟨i, x⟩, h i x

section lift

variables (M) (N : Type*) [monoid N]

def lift : (Π i, M i →* N) ≃ (free_monoid_product M →* N) :=
{ to_fun := λ f, (con M).lift (free_monoid.lift (Σ i, M i) N $ λ x, f x.1 x.2) $
    Inf_le ⟨λ i x y,
      by simp only [con.ker_rel, monoid_hom.map_mul, free_monoid.lift_eval_of],
      λ i, by simp only [con.ker_rel, free_monoid.lift_eval_of, monoid_hom.map_one]⟩,
  inv_fun := λ f i, f.comp (of M i),
  left_inv := λ f, funext $ λ i, monoid_hom.ext $ λ x, free_monoid.lift_eval_of _ _,
  right_inv := λ f, hom_eq (λ i x, free_monoid.lift_eval_of _ _) }

end lift

section group

variables {G : ι → Type*} [Π i, group (G i)]

def inv_aux (xs : free_monoid (Σ i, G i)) :
  free_monoid_product G :=
mk G $ list.reverse $ list.map (λ x : Σ i, G i, ⟨x.fst, x.snd⁻¹⟩) xs

lemma inv_aux_mul_rev (xs ys : free_monoid (Σ i, G i)) :
  inv_aux (xs * ys) = inv_aux ys * inv_aux xs :=
begin
  dunfold inv_aux,
  rw [free_monoid.mul_def, list.map_append, list.reverse_append, ← free_monoid.mul_def,
    (mk G).map_mul]
end

lemma inv_aux_of (i : ι) (x : G i) : inv_aux (free_monoid.of ⟨i, x⟩) = of G i x⁻¹ := rfl

instance has_inv : has_inv (free_monoid_product G) :=
⟨λ x, lift_on x inv_aux
  (λ x₁ x₂ hx y₁ y₂ hy, by simp only [inv_aux_mul_rev, *])
  (λ i, show of G i 1⁻¹ = 1, by rw [one_inv, (of G i).map_one])
  (λ i x y, by simp only [inv_aux_of, inv_aux_mul_rev, mul_inv_rev, (of G i).map_mul])⟩

protected lemma mul_inv_rev (x y : free_monoid_product G) :
  (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
by rcases x; rcases y; exact inv_aux_mul_rev _ _

lemma of_inv (i x) : (of G i x)⁻¹ = of G i x⁻¹ := rfl

instance group : group (free_monoid_product G) :=
{ inv := has_inv.inv,
  mul_left_inv := λ x, show (λ x : free_monoid_product G, x⁻¹ * x = 1) x,
    from induction_on' x rfl $ λ i x xs hxs,
    by rw [free_monoid_product.mul_inv_rev, mul_assoc, ← mul_assoc _ _ xs, of_inv, ← of_mul,
      mul_left_inv, of_one, one_mul, hxs],
  .. free_monoid_product.monoid G}

end group

def is_normalized : list (Σ i, {x : M i // x ≠ 1}) → Prop :=
list.chain' $ λ x y, x.fst ≠ y.fst

variables (M)

def normalized := subtype (@is_normalized _ M _)

variables {M} [decidable_eq ι] [Π i, decidable_eq (M i)]

namespace normalized

instance : decidable_pred (@is_normalized _ M _) := by delta is_normalized; apply_instance

def tail (x : normalized M) : normalized M := ⟨x.val.tail, x.property.tail⟩

def cancel_two (a b : Σ i, {x : M i // x ≠ 1}) :
  list (Σ i, {x : M i // x ≠ 1}) :=
if hij : a.fst = b.fst then
  if hxy : a.snd.val * (eq.rec_on hij.symm b.snd.val) = 1 then []
  else [⟨a.fst, _, hxy⟩]
else [a, b]

/-- Prepend `a : Σ i, {x : M i // x ≠ 1}` to `l : normalized M` and cancel
it with `l.head` if required. -/
def cons (a : Σ i, {x : M i // x ≠ 1}) : normalized M → normalized M
| ⟨[], _⟩ := ⟨[a], list.chain'_singleton a⟩
| ⟨b :: l, h⟩ := subtype.mk (cancel_two a b ++ l)
begin
  dunfold cancel_two,
  split_ifs; simp only [list.cons_append, list.nil_append],
  { exact h.tail },
  { exact h.imp' (λ _ _, id) (λ c hb ha, hb (‹a.fst = b.fst› ▸ ha)) },
  { exact h.cons ‹¬a.fst = b.fst› }
end

lemma cons_nil (a : Σ i, {x : M i // x ≠ 1}) (h) :
  cons a ⟨[], h⟩ = ⟨[a], list.chain'_singleton a⟩ := rfl

/-- If `a :: l` is normalized and `, then `cons a l = a :: l`. -/
lemma cons_head_tail {a : Σ i, {x : M i // x ≠ 1}} {l hl} (hal) :
  cons a ⟨l, hl⟩ = ⟨a :: l, hal⟩ :=
begin
  apply subtype.eq,
  rcases l with _|⟨b, tl⟩,
  { congr },
  { have hij : a.fst ≠ b.fst, from (list.chain'_cons.1 hal).1,
    simp only [cons, cancel_two],
    rw [dif_neg hij], refl }
end

instance : has_mul (normalized M) :=
⟨λ xs ys, list.foldr normalized.cons ys xs.val⟩

lemma mul_def (xs ys : normalized M) : xs * ys = list.foldr normalized.cons ys xs.val := rfl

lemma cons_mul' (x xs hxs ys) :
  @has_mul.mul (normalized M) _ ⟨x :: xs, hxs⟩ ys = cons x (⟨xs, hxs.tail⟩ * ys) :=
rfl

lemma cons_eq_mul (x) (xs : normalized M) :
  cons x xs = ⟨[x], list.chain'_singleton x⟩ * xs :=
rfl

lemma is_normalized_cancel_two_append (a b : Σ i, {x : M i // x ≠ 1}) (l : list _)
  (hl : is_normalized l) (hbl : is_normalized (b :: l)) :
  is_normalized (cancel_two a b ++ l) :=
begin
  rcases a with ⟨i, x, hx⟩,
  rcases b with ⟨j, y, hy⟩,
  by_cases hij : i = j,
  { subst j,
     }
end


lemma cons_mul_aux₁ {i : ι} {x y z : M i} (hx hy hz l hl) :
  cons ⟨i, x, hx⟩ (cons ⟨i, y, hy⟩ ⟨⟨i, z, hz⟩ :: l, hl⟩) =
    list.foldr cons ⟨⟨i, z, hz⟩ :: l, hl⟩ (cancel_two ⟨i, x, hx⟩ ⟨i, y, hy⟩) :=
begin
  simp only [cancel_two, dif_pos rfl],
  split_ifs with hxy; dsimp at *;
    simp only [cons, cancel_two, dif_pos rfl]; split_ifs with hyz; dsimp at *,
  { have : x = z, by rw [← mul_one x, ← hyz, ← mul_assoc, hxy, one_mul],
    subst z,
    apply cons_head_tail },
  { have : x * (y * z) ≠ 1, by rwa [← mul_assoc, hxy, one_mul, ne.def],
    simp only [cons, cancel_two, dif_pos rfl, dif_neg this, list.cons_append, list.nil_append],
    congr,
    rw [← mul_assoc, hxy, one_mul] },
  { have A : x * y * z = x, by rw [mul_assoc, hyz, mul_one],
    have : x * y * z ≠ 1, by rwa [A],
    simp only [dif_neg this, A],
    have hxl : is_normalized (⟨i, x, hx⟩ :: l) := hl.imp' (λ _ _, id) (λ _, id),
    rw [cons_head_tail hxl], refl },
  { apply subtype.eq, dsimp,
    symmetry, -- Otherwise `split_ifs` fails to split `dite` in RHS
    split_ifs with hxyz; rw mul_assoc at hxyz; simp only [cons, cancel_two, dif_pos rfl]; dsimp,
    { rw [dif_pos hxyz, list.nil_append] },
    { rw [dif_neg hxyz, list.cons_append, list.nil_append],
      congr' 3,
      apply mul_assoc } }
end

lemma cons_mul_aux {i : ι} {x y : M i} (hx hy l) :
  cons ⟨i, x, hx⟩ (cons ⟨i, y, hy⟩ l) = list.foldr cons l (cancel_two ⟨i, x, hx⟩ ⟨i, y, hy⟩) :=
begin
  cases l with l hl,
  by_cases H : is_normalized (⟨i, y, hy⟩ :: l),
  { simp only [cons_head_tail H, cons, cancel_two, dif_pos rfl],
    split_ifs with hxy, refl,
    dsimp [list.foldr] at hxy ⊢,
    exact (cons_head_tail _).symm },
  { rcases l with _|⟨⟨j, z, hz⟩, l⟩,
    { exact absurd (list.chain'_singleton _) H },
    { replace H : i = j, from not_not.1 (λ hne, H $ hl.cons hne),
      subst j,
      apply cons_mul_aux₁ } }
end

lemma cons_mul (x) (xs ys : normalized M) :
  (cons x xs) * ys = cons x (xs * ys) :=
begin
  rcases xs with ⟨l, hl⟩,
  cases l with hd,
  { refl },
  { rcases x with ⟨i, x, hx⟩,
    rcases hd with ⟨j, y, hy⟩,
    by_cases hij : i = j,
    { subst j,
      simp only [mul_def, list.foldr_cons, cons, list.foldr_append],
      apply (cons_mul_aux _ _ _).symm },
    { simp only [mul_def, cons, cancel_two, dif_neg hij,
        list.foldr_append, list.foldr_cons, list.foldr_nil] } }
end

def cons' (x : Σ i, M i) (xs : normalized M) : normalized M :=
if h : x.snd = 1 then xs else cons ⟨x.fst, x.snd, h⟩ xs

lemma cons'_mul (x) (xs ys : normalized M) :
  (cons' x xs) * ys = cons' x (xs * ys) :=
begin
  dunfold cons',
  split_ifs,
  { refl },
  { apply cons_mul }
end

instance : has_one (normalized M) := ⟨⟨[], trivial⟩⟩

lemma one_def : (1 : normalized M) = ⟨[], trivial⟩ := rfl

lemma nil_eq_one (hl) : (⟨[], hl⟩ : normalized M) = (1 : normalized M) := rfl

instance : monoid (normalized M) :=
{ one := 1,
  mul := (*),
  mul_one :=
    begin
      rintros ⟨l, hl⟩,
      induction l with hd tl htl,
      { refl },
      { rw [cons_mul', htl, cons_head_tail] }
    end,
  one_mul := λ xs, rfl,
  mul_assoc := λ xs ys zs,
    begin
      rcases xs with ⟨xs, xs_norm⟩,
      induction xs with x xs hxs xs_norm,
      { refl },
      { rw [cons_mul', cons_mul', ← hxs, cons_mul] }
    end }

end normalized

section

variable (M)

private def normalize_aux : free_monoid_product M →* normalized M :=
begin
  refine (con M).lift ⟨_, _, _⟩ _,
  { exact list.foldr normalized.cons' 1 },
  { refl },
  { intros xs ys,
    induction xs with x xs hxs,
    { simp_rw [list.foldr_nil, free_monoid.one_def.symm, one_mul] },
    { erw [list.foldr_cons, normalized.cons'_mul, hxs] }},
  { refine Inf_le ⟨λ i x y, _, λ i, _⟩;
      simp only [con.ker_rel, monoid_hom.coe_mk, free_monoid.of_def, free_monoid.mul_def,
        list.cons_append, list.nil_append, list.foldr, normalized.cons'],
    { dsimp, symmetry,
      by_cases hx : x = 1; [subst x, rw [dif_neg hx]];
        by_cases hy : y = 1; [subst y, rw [dif_neg hy], subst y, rw [dif_neg hy]];
        try { simp only [dif_pos rfl, one_mul, mul_one] },
      { rw [dif_pos], apply mul_one },
      { rw [dif_neg], rwa [one_mul] },
      { rw [dif_neg], rwa [mul_one] },
      { simp only [normalized.one_def, normalized.cons_nil, normalized.cons, list.append_nil,
          normalized.cancel_two, dif_pos rfl],
        dsimp,
        split_ifs; refl }
      },
    { simp only [dif_pos rfl], refl  } }
end

private def of_normalized : normalized M →* free_monoid_product M :=
{ to_fun := λ xs, mk M (list.map (λ x : Σ i, {x : M i // x ≠ 1}, ⟨x.fst, x.snd.val⟩) xs.val),
  map_one' := rfl,
  map_mul' := λ xs ys,
  begin
    cases xs with xs hxs,
    induction xs with x xs ihx,
    { refl },
    { rw [list.map_cons, mk_cons, mul_assoc, ← ihx hxs.tail, ← mk_cons',
        ← list.map_cons (λ x : Σ i, {x : M i // ¬x=1}, (⟨x.1, x.2.1⟩ : Σ i, M i))],
      apply congr_arg, apply congr_arg,
       }
  end
}

lemma normalize_aux_of_normalized (xs : normalized M) :
  (normalize_aux M : free_monoid_product M → normalized M)
    (of_normalized xs) = xs :=
begin
  cases xs with xs hxs,
  induction xs with x xs ihx,
  { refl },
  { simp only [of_normalized, list.map_cons, mk_cons, monoid_hom.map_mul, of_apply], }
end

def to_normalized : free_monoid_product M ≃* normalized M :=
begin
  refine { .. normalize_aux M, .. },
  { exact λ xs,  },
  { rintros ⟨xs⟩; rw [quot_mk_eq_mk],
    induction xs with x xs ihx,
    { refl },
    { rw [mk_cons, monoid_hom.map_mul', normalized.mul_def],  } }
end

end

namespace normalized

section lift

variables (M) (N : Type*) [monoid N]


section group

variables {G : ι → Type*} [Π i, group (G i)] [Π i, decidable_eq (G i)]

instance : has_inv (normalized G) :=
has_inv.mk $
begin
  refine λ xs, ⟨list.reverse (xs.val.map $ λ x, ⟨x.fst, x.snd.val⁻¹, _⟩), _⟩,
  { refine (λ h, x.snd.property $ inv_inj _),
    rwa one_inv },
  { refine list.chain'_reverse.mpr ((list.chain'_map _).mpr $ xs.2.imp _),
    exact (λ a b h, h.symm) }
end

instance : group (normalized G) :=
{ one := 1,
  mul := (*),
  inv := has_inv.inv,
  mul_left_inv :=
    begin
      rintros ⟨l, hl⟩,
      induction l with hd tl htl,
      { refl },
      { unfold_projs at htl ⊢,
        have : group.inv hd.snd.val * hd.snd.val = 1,
          from mul_left_inv hd.snd.val,
        simp only [list.map_cons, list.reverse_cons, list.foldr_append, list.foldr_cons,
          list.foldr_nil, cons, cancel_two, dif_pos rfl, dif_pos this, list.nil_append],
        exact htl _, }
    end,
  .. normalized.monoid }

end group

end normalized

end free_monoid_product
