import analysis.special_functions.log
import group_theory.subsemigroup.basic

namespace test

variables {X Y : Type}

def orbit (f : Y → X → X) (x : X) : set X := ⋂₀{O | x∈O ∧ ∀(x∈O) y, f y x∈O}

def reaches (f : Y → X → X) (x y : X) : Prop := y∈(orbit f x)

def myf : fin 2 → fin 4 → fin 4 := ![![2,2,2,2],![0,0,0,3]]

lemma start (f : Y → X → X) (x : X) : {x} ⊆ orbit f x := begin
    intros _ h _ hO,
    rw set.eq_of_mem_singleton h,
    exact hO.1
end

lemma extend (f : Y → X → X) (x : X) (O : set X) : O ⊆ orbit f x → (O ∪ ⋃(y : Y), (f y) '' O) ⊆ orbit f x := begin
    intros h x' k,
    cases k,
    { exact h k },
    { rw set.mem_Union at k, cases k, cases k_h, sorry }
/-let aaa := h k_h_h.1,
intros U hU, have bbb : O ⊆ U, { rw orbit at h, rw ← set.Inf_eq_sInter at h, let ccc := Inf_le hU, exact le_trans h ccc, },  }-/
end

lemma foundorbit (f : Y → X → X) (x : X) (O : set X) : O ⊆ orbit f x → x ∈ O → ∀(y : Y), f y '' O ⊆ O → O = orbit f x := begin
    sorry
end

theorem myf_orbit3 : orbit myf 3 = {0,2,3} := begin
    have iter1 : ({3} : set (fin 4)) ⊆ orbit myf 3, exact start myf 3,
    have iter2 : ({2,3} : set (fin 4)) ⊆ orbit myf 3, { let temp := extend myf 3 {3} iter1, rw myf at temp, finish },
    have iter3 : ({0,2,3} : set (fin 4)) ⊆ orbit myf 3, exact extend myf 3 {2,3} iter2,
    exact foundorbit myf 3 {0,2,3} iter3 iter1 (by sorry)
end

theorem myf_orbit0 : orbit myf 0 = {0,2} := begin
    ext1, split,
    { intros h, 
      sorry,
    },
    {
    have iter1 : ({0} : set (fin 4)) ⊆ orbit myf 0, exact start myf 0,
    have iter2 : ({0,2} : set (fin 4)) ⊆ orbit myf 0, { let temp := extend myf 0 {0} iter1, rw myf at temp, finish },
    }
end

theorem wow : reaches myf 3 0 := begin
    rw reaches,
    rw myf_orbit3,
    norm_num,
end

theorem wow2 : ¬ reaches myf 0 3 := begin
    rw reaches,
    rw myf_orbit0,
    norm_num
end

end test
