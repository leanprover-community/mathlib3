/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

A tactic for discharging Presburger arithmetic goals using the Omega test.
-/

import tactic.omega.clause 

def sgm (v : nat → int) (b : int) (as : list int) (n) := 
let a_n : int := as.get n in
let m : int := a_n + 1 in
((symmod b m) + (coeffs.val v (as.map (λ x, symmod x m)))) / m

def rhs : nat → int → coeffs → term 
| n b as := 
  let m := as.get n + 1 in
  ⟨(symmod b m), (as.map (λ x, symmod x m)){n ↦ -m}⟩ 

lemma rhs_correct_aux {m v} {as : coeffs} :
∀ {k}, ∃ d, (m * d + 
  coeffs.val_between v (as.map (λ (x : ℤ), symmod x m)) 0 k =
      coeffs.val_between v as 0 k) 
| 0 := begin existsi (0 : int), simp_omega end
| (k+1) := 
  begin 
    simp_omega, 
    cases @rhs_correct_aux k with d h1, rw ← h1,
    by_cases hk : k < as.length, 
    { rw [list.get_map hk, symmod_eq, sub_mul], 
      existsi (d + (symdiv (list.get k as) m * v k)), 
      ring }, 
    { rw not_lt at hk, 
      repeat {rw list.get_eq_zero_of_le},  
      existsi d, rw add_assoc, exact hk,
      simp only [hk, list.length_map] }
  end

lemma rhs_correct {v b} {as : coeffs} (n) :
  0 < as.get n → 
  0 = term.val v (b,as) → 
  v n = term.val (v⟨n ↦ sgm v b as n⟩) (rhs n b as) := 
begin
  intros h0 h1,
  let a_n := as.get n,
  let m := a_n + 1,
  have h3 : m ≠ 0 := 
       begin 
         apply ne_of_gt, apply lt_trans h0,
         simp [a_n, m],
       end,
  have h2 : m * (sgm v b as n) = (symmod b m) + 
    coeffs.val v (as.map (λ x, symmod x m)),
  { simp only [sgm, mul_comm m],
    rw [int.div_mul_cancel], 
    have h4 : ∃ c,  
    m * c + (symmod b (list.get n as + 1) + 
      coeffs.val v (as.map (λ (x : ℤ), symmod x m))) = 
      term.val v (b,as),
    { have h5: ∃ d,  m * d + 
        (coeffs.val v (as.map (λ x, symmod x m))) = coeffs.val v as,
      { simp only [coeffs.val, list.length_map], apply rhs_correct_aux },
      cases h5 with d h5, rw symmod_eq,
      existsi (symdiv b m + d), 
      simp only [term.val], rw ← h5,
      simp only [term.val, mul_add, 
      add_mul, m, a_n], ring },
    cases h4 with c h4,
    rw [dvd_add_iff_right (dvd_mul_right m c), h4, ← h1],
    apply dvd_zero },
  apply calc v n 
      = -(m * sgm v b as n) + (symmod b m) + 
        (coeffs.val_except n v (as.map (λ x, symmod x m))) :
        begin
          rw h2, simp, rw ← coeffs.val_except_add_eq n,
          simp, 
          have hn : n < as.length,
          { by_contra hc, rw not_lt at hc,
            rw (list.get_eq_zero_of_le n hc) at h0,
            cases h0 },
          rw list.get_map hn, simp [a_n, m], 
          rw [add_comm, symmod_add_one_self h0], ring
        end
  ... = term.val (v⟨n↦sgm v b as n⟩) (rhs n b as) : 
        begin
          simp only [rhs, term.val], 
          rw [← coeffs.val_except_add_eq n, list.get_set, update_eq],  
          have h2 : ∀ a b c : int, a + b + c = b + (c + a) := by {intros, ring},
          rw (h2 (- _)), apply fun_mono_2 rfl, apply fun_mono_2,
          { rw coeffs.val_except_update_set },
          { simp [m, a_n], ring }
        end
end

def sym_sym (m b : int) : int := 
symdiv b m + symmod b m

def coeffs_reduce : nat → int → list int → term 
| n b as := 
  let a := as.get n in
  let m := a + 1 in 
  (sym_sym m b, (as.map (sym_sym m)){n ↦ -a}) 

lemma coeffs_reduce_correct {v b} {as : coeffs} {n} :
  0 < as.get n → 
  0 = term.val v (b,as) → 
  0 = term.val (v⟨n ↦ sgm v b as n⟩) (coeffs_reduce n b as) := 
begin
  intros h1 h2, 
  let a_n := as.get n,
  let m := a_n + 1,
  have h3 : m ≠ 0 := 
       begin apply ne_of_gt, apply lt_trans h1, simp [m] end,
  have h4 : 0 = (term.val (v⟨n↦sgm v b as n⟩) (coeffs_reduce n b as)) * m :=
  calc 0 
      = term.val v (b,as) : h2
  ... = b + coeffs.val_except n v as 
          + a_n * ((rhs n b as).val (v⟨n ↦ sgm v b as n⟩)) : 
        begin
          simp only [term.val],
          rw [← coeffs.val_except_add_eq n,
              rhs_correct n h1 h2], 
          simp only [a_n, add_assoc], 
        end
  ... = -(m * a_n * sgm v b as n) + (b + a_n * (symmod b m)) 
        + (coeffs.val_except n v as 
        + a_n * coeffs.val_except n v (as.map (λ x, symmod x m))) : 
          begin
            simp [term.val, rhs, mul_add, m, a_n], 
           rw [← coeffs.val_except_add_eq n,
            list.get_set, update_eq, mul_add],
            apply fun_mono_2, 
            { rw coeffs.val_except_eq_val_except 
              update_eq_of_ne list.get_set_eq_of_ne },
            { simp only [m], ring },
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
          have h5 : list.add as (list.map (has_mul.mul a_n) 
            (list.map (λ (x : ℤ), symmod x (list.get n as + 1)) as)) =
            list.map (λ (a_i : ℤ), a_i + a_n * symmod a_i m) as,
          { rw [list.map_map, list.map_add_map], 
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
            { simp only [m], rw add_sub_cancel },
              rw [h5, sub_mul, one_mul, add_sub,
                add_comm, add_sub_assoc, ← mul_symdiv_eq],
             simp only [sym_sym, mul_add, add_comm] },
          apply fun_mono_2 (h4 _),
          apply coeffs.val_except_eq_val_except; intros x h5, refl,
          apply congr_arg, apply fun_mono_2 _ rfl,
          rw function.funext_iff, apply h4,
        end
  ... = (-(a_n * sgm v b as n) + (sym_sym m b) 
        + coeffs.val_except n v (as.map (sym_sym m))) * m : 
        begin
          simp only [add_mul _ _ m], apply fun_mono_2, ring,
          simp only [coeffs.val_except], simp only [add_mul _ _ m], 
          apply fun_mono_2,
          { rw [mul_comm _ m, ← coeffs.val_between_map_mul, list.map_map] },
          { simp only [list.length_map, mul_comm _ m],
            rw [← coeffs.val_between_map_mul, list.map_map] } 
        end
  ... = (term.val (v⟨n↦sgm v b as n⟩) (coeffs_reduce n b as)) * m :
        begin
          simp_omega [coeffs_reduce, add_mul],
          rw [add_comm _ (sym_sym m b * m), add_assoc],
          apply fun_mono_2, refl, 
          rw [← coeffs.val_except_add_eq n, list.get_set,
            update_eq, add_comm, add_mul], apply fun_mono_2,
          { apply congr_arg (λ x, x * m), 
            apply coeffs.val_except_eq_val_except; intros x h4,
            { rw update_eq_of_ne _ h4 },
            { rw list.get_set_eq_of_ne _ h4 } },
          { apply congr_arg (λ x, x * m), 
            simp only [neg_mul_eq_neg_mul] }
        end,
  rw [← int.mul_div_cancel (term.val _ _) h3, ← h4, int.zero_div]
end

-- Requires : t1.coeffs[m] = 1
def cancel (m : nat) (t1 t2 : term) : term := 
term.add (t1.mul (-t2.snd.get m)) t2

def subst (n : nat) (t1 t2 : term) : term := 
term.add (t1.mul (t2.snd.get n)) (t2.fst,t2.snd{n ↦ 0})

lemma subst_correct {v t n b} {as : coeffs} :
  0 < as.get n → 0 = term.val v (b,as) → 
  term.val v t = term.val (v⟨n↦sgm v b as n⟩) (subst n (rhs n b as) t) :=
begin
  intros h1 h2, simp_omega [subst],
  rw ← rhs_correct _ h1 h2, cases t with b' as',
  simp_omega,
  have h3 : coeffs.val (v⟨n↦sgm v b as n⟩) (as'{n↦0}) = 
    coeffs.val_except n v as', 
  { rw [← coeffs.val_except_add_eq n, list.get_set,
      zero_mul, add_zero, coeffs.val_except_update_set] },
  rw [h3, ← coeffs.val_except_add_eq n], ring
end

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
  if 0 < as.get n
  then let eq' := coeffs_reduce n b as in
       let r := rhs n b as in 
       let eqs' := eqs.map (subst n r) in
       let les' := les.map (subst n r) in
       eq_elim es ((eq'::eqs'), les')
  else ([],[])
| (ee.cancel m::es) ((eq::eqs), les)  := 
  eq_elim es ((eqs.map (_root_.cancel m eq)), 
    (les.map (_root_.cancel m eq)))

open tactic

lemma sat_empty : clause.sat ([],[]) := 
⟨λ _,0, ⟨dec_trivial, dec_trivial⟩⟩ 

lemma sat_eq_elim : ∀ {es} {c : clause}, c.sat → (eq_elim es c).sat
| []     ([], les) h := h
| (e::_) ([], les) h := 
  begin cases e; simp only [eq_elim]; apply sat_empty end
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
    cases h1 with v h1, existsi v,
    cases h1 with hl hr, apply and.intro _ hr,
    rw list.forall_mem_cons at *,
    apply and.intro _ hl.right,
    rw term.val_neg, rw ← hl.left, refl
  end
| (ee.nondiv i::es) ((b,as)::eqs, les) h1 := 
  begin
    simp only [eq_elim],
    by_cases h2 : (¬i ∣ b ∧ ∀ (x : ℤ), x ∈ as → i ∣ x),
    { exfalso, cases h1 with v h1, 
      have h3 : 0 = b + coeffs.val v as := h1.left _ (or.inl rfl), 
      have h4 : i ∣ coeffs.val v as     := coeffs.dvd_val h2.right,
      have h5 : i ∣ b + coeffs.val v as := by { rw ← h3, apply dvd_zero },
      rw ← dvd_add_iff_left h4 at h5, apply h2.left h5 },
    { rw if_neg h2, apply sat_empty }
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
    simp only [eq_elim], by_cases h2 : 0 < list.get n as,
    tactic.rotate 1, { rw if_neg h2, apply sat_empty },
    rw if_pos h2, apply sat_eq_elim, cases h1 with v h1, 
    existsi v⟨n ↦ sgm v b as n⟩, cases h1 with h1 h3,
    rw list.forall_mem_cons at h1, cases h1 with h4 h5,
    constructor, apply list.forall_mem_cons_of,
    apply coeffs_reduce_correct h2 h4,
    { intros x h6, rw list.mem_map at h6,
      cases h6 with t h6, cases h6 with h6 h7,
      rw [← h7, ← subst_correct h2 h4], apply h5 _ h6 },
    { intros x h6, rw list.mem_map at h6,
      cases h6 with t h6, cases h6 with h6 h7,
      rw [← h7, ← subst_correct h2 h4], apply h3 _ h6 } 
   end
| (ee.cancel m::es) ((eq::eqs), les) h1 :=  
  begin
    simp only [eq_elim], apply sat_eq_elim,
    cases h1 with v h1, existsi v, cases h1 with h1 h2,
    rw list.forall_mem_cons at h1, cases h1 with h1 h3,
    constructor; intros t h4; rw list.mem_map at h4; 
    rcases h4 with ⟨s,h4,h5⟩; rw ← h5;
    simp only [term.val_add, term.val_mul, cancel];
    rw [← h1, mul_zero, zero_add],
    { apply h3 _ h4 }, { apply h2 _ h4}
  end

lemma unsat_of_unsat_eq_elim (ee c) :
  (eq_elim ee c).unsat → c.unsat :=
begin intros h1 h2, apply h1, apply sat_eq_elim h2 end