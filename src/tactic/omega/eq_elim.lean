/- Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Correctness lemmas for equality elimination.
See 5.5 of <http://www.decision-procedures.org/> for details. -/

import tactic.omega.clause

open list.func

namespace omega

def symdiv (i j : int) : int :=
if (2 * (i % j)) < j
then i / j
else (i / j) + 1

def symmod (i j : int) : int :=
if (2 * (i % j)) < j
then i % j
else (i % j) - j

lemma symmod_add_one_self {i : int} :
  0 < i → symmod i (i+1) = -1 :=
begin
  intro h1,
  unfold symmod,
  rw [int.mod_eq_of_lt (le_of_lt h1) (lt_add_one _), if_neg],
  simp only [add_comm, add_neg_cancel_left,
    neg_add_rev, sub_eq_add_neg],
  have h2 : 2 * i = (1 + 1) * i := rfl,
  simpa only [h2, add_mul, one_mul,
    add_lt_add_iff_left, not_lt] using h1
end

lemma mul_symdiv_eq {i j : int} :
j * (symdiv i j) = i - (symmod i j) :=
begin
  unfold symdiv, unfold symmod,
  by_cases h1 : (2 * (i % j)) < j,
  { repeat {rw if_pos h1},
    rw [int.mod_def, sub_sub_cancel] },
  { repeat {rw if_neg h1},
    rw [int.mod_def, sub_sub, sub_sub_cancel,
      mul_add, mul_one] }
end

lemma symmod_eq {i j : int} :
  symmod i j = i - j * (symdiv i j) :=
by rw [mul_symdiv_eq, sub_sub_cancel]

/-- (sgm v b as n) is the new value assigned to the nth variable
after a single step of equality elimination using valuation v,
term ⟨b, as⟩, and variable index n. If v satisfies the initial
constraint set, then (v ⟨n ↦ sgm v b as n⟩) satisfies the new
constraint set after equality elimination. -/
def sgm (v : nat → int) (b : int) (as : list int) (n : nat) :=
let a_n : int := get n as in
let m : int := a_n + 1 in
((symmod b m) + (coeffs.val v (as.map (λ x, symmod x m)))) / m

open_locale list.func

def rhs : nat → int → list int → term
| n b as :=
  let m := get n as + 1 in
  ⟨(symmod b m), (as.map (λ x, symmod x m)) {n ↦ -m}⟩

lemma rhs_correct_aux {v : nat → int} {m : int} {as : list int} :
∀ {k}, ∃ d, (m * d +
  coeffs.val_between v (as.map (λ (x : ℤ), symmod x m)) 0 k =
      coeffs.val_between v as 0 k)
| 0 :=
  begin
    existsi (0 : int),
    simp only [add_zero, mul_zero, coeffs.val_between]
  end
| (k+1) :=
  begin
    simp only [zero_add, coeffs.val_between, list.map],
    cases @rhs_correct_aux k with d h1, rw ← h1,
    by_cases hk : k < as.length,
    { rw [get_map hk, symmod_eq, sub_mul],
      existsi (d + (symdiv (get k as) m * v k)),
      ring },
    { rw not_lt at hk,
      repeat {rw get_eq_default_of_le},
      existsi d,
      rw add_assoc,
      exact hk,
      simp only [hk, list.length_map] }
  end

open_locale omega

lemma rhs_correct {v : nat → int}
  {b : int} {as : list int} (n : nat) :
  0 < get n as →
  0 = term.val v (b,as) →
  v n = term.val (v ⟨n ↦ sgm v b as n⟩) (rhs n b as) :=
begin
  intros h0 h1,
  let a_n := get n as,
  let m := a_n + 1,
  have h3 : m ≠ 0,
  { apply ne_of_gt, apply lt_trans h0, simp [a_n, m] },
  have h2 : m * (sgm v b as n) = (symmod b m) +
    coeffs.val v (as.map (λ x, symmod x m)),
  { simp only [sgm, mul_comm m],
    rw [int.div_mul_cancel],
    have h4 : ∃ c, m * c + (symmod b (get n as + 1) +
      coeffs.val v (as.map (λ (x : ℤ), symmod x m))) = term.val v (b,as),
    { have h5: ∃ d,  m * d +
        (coeffs.val v (as.map (λ x, symmod x m))) = coeffs.val v as,
      { simp only [coeffs.val, list.length_map], apply rhs_correct_aux },
      cases h5 with d h5, rw symmod_eq,
      existsi (symdiv b m + d),
      unfold term.val, rw ← h5,
      simp only [term.val, mul_add, add_mul, m, a_n],
      ring },
    cases h4 with c h4,
    rw [dvd_add_iff_right (dvd_mul_right m c), h4, ← h1],
    apply dvd_zero },
  apply calc v n
      = -(m * sgm v b as n) + (symmod b m) +
        (coeffs.val_except n v (as.map (λ x, symmod x m))) :
        begin
          rw [h2, ← coeffs.val_except_add_eq n],
          have hn : n < as.length,
          { by_contra hc, rw not_lt at hc,
            rw (get_eq_default_of_le n hc) at h0,
            cases h0 },
          rw get_map hn,
          simp only [a_n, m],
          rw [add_comm, symmod_add_one_self h0],
          ring
        end
  ... = term.val (v⟨n↦sgm v b as n⟩) (rhs n b as) :
        begin
          unfold rhs, unfold term.val,
          rw [← coeffs.val_except_add_eq n, get_set, update_eq],
          have h2 : ∀ a b c : int, a + b + c = b + (c + a) := by {intros, ring},
          rw (h2 (- _)),
          apply fun_mono_2 rfl,
          apply fun_mono_2,
          { rw coeffs.val_except_update_set },
          { simp only [m, a_n], ring }
        end
end

def sym_sym (m b : int) : int :=
symdiv b m + symmod b m

def coeffs_reduce : nat → int → list int → term
| n b as :=
  let a := get n as in
  let m := a + 1 in
  (sym_sym m b, (as.map (sym_sym m)) {n ↦ -a})

lemma coeffs_reduce_correct
  {v : nat → int} {b : int} {as : list int} {n : nat} :
  0 < get n as →
  0 = term.val v (b,as) →
  0 = term.val (v ⟨n ↦ sgm v b as n⟩) (coeffs_reduce n b as) :=
begin
  intros h1 h2,
  let a_n := get n as,
  let m := a_n + 1,
  have h3 : m ≠ 0,
  { apply ne_of_gt,
    apply lt_trans h1,
    simp only [m, lt_add_iff_pos_right] },
  have h4 : 0 = (term.val (v⟨n↦sgm v b as n⟩) (coeffs_reduce n b as)) * m :=
  calc  0
      = term.val v (b,as) : h2
  ... = b + coeffs.val_except n v as
          + a_n * ((rhs n b as).val (v⟨n ↦ sgm v b as n⟩)) :
        begin
          unfold term.val,
          rw [← coeffs.val_except_add_eq n, rhs_correct n h1 h2],
          simp only [a_n, add_assoc],
        end
  ... = -(m * a_n * sgm v b as n) + (b + a_n * (symmod b m)) +
        (coeffs.val_except n v as +
        a_n * coeffs.val_except n v (as.map (λ x, symmod x m))) :
          begin
            simp only [term.val, rhs, mul_add, m, a_n,
              add_assoc, add_left_inj, add_comm, add_left_comm],
            rw [← coeffs.val_except_add_eq n,
              get_set, update_eq, mul_add],
            apply fun_mono_2,
            { rw coeffs.val_except_eq_val_except
              update_eq_of_ne (get_set_eq_of_ne _) },
            simp only [m], ring,
          end
  ... = -(m * a_n * sgm v b as n) + (b + a_n * (symmod b m))
        + coeffs.val_except n v (as.map (λ a_i, a_i + a_n * (symmod a_i m))) :
        begin
          apply fun_mono_2 rfl,
          simp only [coeffs.val_except, mul_add],
          repeat {rw ← coeffs.val_between_map_mul},
          have h4 : ∀ {a b c d : int},
            a + b + (c + d) = (a + c) + (b + d),
          { intros, ring }, rw h4,
          have h5 : add as (list.map (has_mul.mul a_n)
            (list.map (λ (x : ℤ), symmod x (get n as + 1)) as)) =
            list.map (λ (a_i : ℤ), a_i + a_n * symmod a_i m) as,
          { rw [list.map_map, ←map_add_map],
            apply fun_mono_2,
            { have h5 : (λ x : int, x) = id,
              { rw function.funext_iff, intro x, refl },
              rw [h5, list.map_id] },
            { apply fun_mono_2 _ rfl,
              rw function.funext_iff, intro x,
              simp only [m] } },
          simp only [list.length_map],
          repeat { rw [← coeffs.val_between_add, h5] },
        end
  ... = -(m * a_n * sgm v b as n) + (m * sym_sym m b)
        + coeffs.val_except n v (as.map (λ a_i, m * sym_sym m a_i)) :
        begin
          repeat {rw add_assoc}, apply fun_mono_2, refl,
          rw ← add_assoc,
          have h4 : ∀ (x : ℤ), x + a_n * symmod x m = m * sym_sym m x,
          { intro x, have h5 : a_n = m - 1,
            { simp only [m],
              rw add_sub_cancel },
            rw [h5, sub_mul, one_mul, add_sub,
              add_comm, add_sub_assoc, ← mul_symdiv_eq],
            simp only [sym_sym, mul_add, add_comm] },
          apply fun_mono_2 (h4 _),
          apply coeffs.val_except_eq_val_except; intros x h5, refl,
          apply congr_arg,
          apply fun_mono_2 _ rfl,
          rw function.funext_iff,
          apply h4
        end
  ... = (-(a_n * sgm v b as n) + (sym_sym m b)
        + coeffs.val_except n v (as.map (sym_sym m))) * m :
        begin
          simp only [add_mul _ _ m],
          apply fun_mono_2, ring,
          simp only [coeffs.val_except, add_mul _ _ m],
          apply fun_mono_2,
          { rw [mul_comm _ m, ← coeffs.val_between_map_mul, list.map_map] },
          simp only [list.length_map, mul_comm _ m],
          rw [← coeffs.val_between_map_mul, list.map_map]
        end
  ... = (sym_sym m b + (coeffs.val_except n v (as.map (sym_sym m)) +
          (-a_n * sgm v b as n))) * m : by ring
  ... = (term.val (v ⟨n ↦ sgm v b as n⟩) (coeffs_reduce n b as)) * m :
        begin
          simp only [coeffs_reduce, term.val, m, a_n],
          rw [← coeffs.val_except_add_eq n,
            coeffs.val_except_update_set, get_set, update_eq]
        end,
  rw [← int.mul_div_cancel (term.val _ _) h3, ← h4, int.zero_div]
end

-- Requires : t1.coeffs[m] = 1
def cancel (m : nat) (t1 t2 : term) : term :=
term.add (t1.mul (-(get m (t2.snd)))) t2

def subst (n : nat) (t1 t2 : term) : term :=
term.add (t1.mul (get n t2.snd)) (t2.fst, t2.snd {n ↦ 0})

lemma subst_correct {v : nat → int} {b : int}
 {as : list int} {t : term} {n : nat} :
  0 < get n as → 0 = term.val v (b,as) →
  term.val v t = term.val (v ⟨n ↦ sgm v b as n⟩) (subst n (rhs n b as) t) :=
begin
  intros h1 h2,
  simp only [subst, term.val, term.val_add, term.val_mul],
  rw ← rhs_correct _ h1 h2,
  cases t with b' as',
  simp only [term.val],
  have h3 : coeffs.val (v ⟨n ↦ sgm v b as n⟩) (as' {n ↦ 0}) =
    coeffs.val_except n v as',
  { rw [← coeffs.val_except_add_eq n, get_set,
      zero_mul, add_zero, coeffs.val_except_update_set] },
  rw [h3, ← coeffs.val_except_add_eq n], ring
end

/-- The type of equality elimination rules. -/
@[derive has_reflect]
inductive ee : Type
| drop   : ee
| nondiv : int → ee
| factor : int → ee
| neg    : ee
| reduce : nat → ee
| cancel : nat → ee

namespace ee

def repr : ee → string
| drop   := "↓"
| (nondiv i) := i.repr ++ "∤"
| (factor i) := "/" ++ i.repr
| neg    := "-"
| (reduce n) := "≻" ++ n.repr
| (cancel n) := "+" ++ n.repr

instance has_repr : has_repr ee := ⟨repr⟩

meta instance has_to_format : has_to_format ee := ⟨λ x, x.repr⟩

end ee

/-- Apply a given sequence of equality elimination steps to a clause. -/
def eq_elim : list ee → clause → clause
| []     ([], les)     := ([],les)
| []     ((_::_), les) := ([],[])
| (_::_) ([], les)     := ([],[])
| (ee.drop::es) ((eq::eqs), les) := eq_elim es (eqs, les)
| (ee.neg::es)  ((eq::eqs), les) := eq_elim es ((eq.neg::eqs), les)
| (ee.nondiv i::es) ((b,as)::eqs, les) :=
  if ¬(i ∣ b) ∧ (∀ x ∈ as, i ∣ x)
  then ([],[⟨-1,[]⟩])
  else ([],[])
| (ee.factor i::es) ((b,as)::eqs, les) :=
  if (i ∣ b) ∧ (∀ x ∈ as, i ∣ x)
  then eq_elim es ((term.div i (b,as)::eqs), les)
  else ([],[])
| (ee.reduce n::es) ((b,as)::eqs, les) :=
  if 0 < get n as
  then let eq' := coeffs_reduce n b as in
       let r := rhs n b as in
       let eqs' := eqs.map (subst n r) in
       let les' := les.map (subst n r) in
       eq_elim es ((eq'::eqs'), les')
  else ([],[])
| (ee.cancel m::es) ((eq::eqs), les)  :=
  eq_elim es ((eqs.map (cancel m eq)), (les.map (cancel m eq)))

open tactic

lemma sat_empty : clause.sat ([],[]) :=
⟨λ _,0, ⟨dec_trivial, dec_trivial⟩⟩

lemma sat_eq_elim :
  ∀ {es : list ee} {c : clause}, c.sat → (eq_elim es c).sat
| []     ([], les) h := h
| (e::_) ([], les) h :=
  by {cases e; simp only [eq_elim]; apply sat_empty}
| [] ((_::_), les) h := sat_empty
| (ee.drop::es) ((eq::eqs), les) h1 :=
  begin
    apply (@sat_eq_elim es _ _),
    rcases h1 with ⟨v,h1,h2⟩,
    refine ⟨v, list.forall_mem_of_forall_mem_cons h1, h2⟩
  end
| (ee.neg::es) ((eq::eqs), les) h1 :=
  begin
    simp only [eq_elim], apply sat_eq_elim,
    cases h1 with v h1,
    existsi v,
    cases h1 with hl hr,
    apply and.intro _ hr,
    rw list.forall_mem_cons at *,
    apply and.intro _ hl.right,
    rw term.val_neg,
    rw ← hl.left,
    refl
  end
| (ee.nondiv i::es) ((b,as)::eqs, les) h1 :=
  begin
    unfold eq_elim,
    by_cases h2 : (¬i ∣ b ∧ ∀ (x : ℤ), x ∈ as → i ∣ x),
    { exfalso, cases h1 with v h1,
      have h3 : 0 = b + coeffs.val v as := h1.left _ (or.inl rfl),
      have h4 : i ∣ coeffs.val v as     := coeffs.dvd_val h2.right,
      have h5 : i ∣ b + coeffs.val v as := by { rw ← h3, apply dvd_zero },
      rw ← dvd_add_iff_left h4 at h5, apply h2.left h5 },
    rw if_neg h2, apply sat_empty
  end
| (ee.factor i::es) ((b,as)::eqs, les) h1 :=
  begin
    simp only [eq_elim],
    by_cases h2 : (i ∣ b) ∧ (∀ x ∈ as, i ∣ x),
    { rw if_pos h2, apply sat_eq_elim, cases h1 with v h1,
      existsi v, cases h1 with h3 h4, apply and.intro _ h4,
      rw list.forall_mem_cons at *, cases h3 with h5 h6,
      apply and.intro _ h6,
      rw [term.val_div h2.left h2.right, ← h5, int.zero_div] },
    { rw if_neg h2, apply sat_empty }
  end
| (ee.reduce n::es) ((b,as)::eqs, les) h1 :=
  begin
    simp only [eq_elim],
    by_cases h2 : 0 < get n as,
    tactic.rotate 1,
    { rw if_neg h2, apply sat_empty },
    rw if_pos h2,
    apply sat_eq_elim,
    cases h1 with v h1,
    existsi v ⟨n ↦ sgm v b as n⟩,
    cases h1 with h1 h3,
    rw list.forall_mem_cons at h1,
    cases h1 with h4 h5,
    constructor,
    { rw list.forall_mem_cons,
      constructor,
      { apply coeffs_reduce_correct h2 h4 },
      { intros x h6, rw list.mem_map at h6,
        cases h6 with t h6, cases h6 with h6 h7,
        rw [← h7, ← subst_correct h2 h4], apply h5 _ h6 } },
    { intros x h6, rw list.mem_map at h6,
      cases h6 with t h6, cases h6 with h6 h7,
      rw [← h7, ← subst_correct h2 h4], apply h3 _ h6 }
   end
| (ee.cancel m::es) ((eq::eqs), les) h1 :=
  begin
    unfold eq_elim,
    apply sat_eq_elim,
    cases h1 with v h1,
    existsi v,
    cases h1 with h1 h2,
    rw list.forall_mem_cons at h1, cases h1 with h1 h3,
    constructor; intros t h4; rw list.mem_map at h4;
    rcases h4 with ⟨s,h4,h5⟩; rw ← h5;
    simp only [term.val_add, term.val_mul, cancel];
    rw [← h1, mul_zero, zero_add],
    { apply h3 _ h4 },
    { apply h2 _ h4 }
  end

/-- If the result of equality elimination is unsatisfiable, the original clause is unsatisfiable. -/
lemma unsat_of_unsat_eq_elim (ee : list ee) (c : clause) :
  (eq_elim ee c).unsat → c.unsat :=
by {intros h1 h2, apply h1, apply sat_eq_elim h2}

end omega
