/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen
-/

import tactic.operand
import tactic.interactive

open tactic

lemma eq_big_sum_Z (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)  
  : finset.sum S (λ s, f s) = finset.sum S (λ s, g s) :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},                     
  },                
end

lemma eq_big_prod_Z (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)  
  : finset.prod S (λ s, f s) = finset.prod S (λ s, g s) :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},    
  },                
end

lemma eq_big_fold_Z (f g : ℤ → ℤ) (S : finset ℤ) 
  (h : ∀ m ∈ S, f m = g m)  
  : finset.fold (+) 0 (λ s, f s) S = finset.fold (+) 0 (λ s, g s) S :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},     
  },                
end

lemma sum_of_odd_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))  
  : finset.sum S (λ s, f s) = finset.sum S (λ s, - f (- s)) :=
begin
  conv {
      to_lhs,
      operand {rw [(h s) s_mem]},                
    },    
end

lemma prod_of_odd_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))  
  : finset.prod S (λ s, f s) = finset.prod S (λ s, - f (- s)) :=
begin
  conv {
      to_lhs,
      operand {rw [(h s) s_mem]},                 
    },    
end

lemma fold_of_odd_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))  
  : finset.fold (+) 0 (λ s, f s) S = finset.fold (+) 0 (λ s, - f (- s)) S :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},                 
  },    
end

lemma sum_test_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0)  
  : finset.sum S (λ s, f s) = 0 :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},                 
  },    
  exact multiset.sum_map_zero, --library_search
end

lemma prod_test_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 1)  
  : finset.prod S (λ s, f s) = 1 :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},                
  },    
  exact multiset.prod_map_one, --library_search
end

lemma fold_test_Z (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0)  
  : finset.fold (+) 0 (λ s, f s) S = 0 :=
begin
  conv { 
    to_lhs,
    operand {rw [(h s) s_mem]}, 
  },    
  exact multiset.sum_map_zero, --library_search
end

lemma eq_big_sum_Z_no_lambda (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)  
  : finset.sum S f = finset.sum S (λ s, g s) :=
begin
  conv {
    to_lhs,
    operand { 
      rw [(h s) s_mem],
      },                     
  },                
end

lemma eq_big_prod_Z_no_lamda (f g : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = g m)  
  : finset.prod S f = finset.prod S (λ s, g s) :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},    
  },                
end

lemma eq_big_fold_Z_no_lamda (f g : ℤ → ℤ) (S : finset ℤ) 
  (h : ∀ m ∈ S, f m = g m)  
  : finset.fold (+) 0 f S = finset.fold (+) 0 (λ s, g s) S :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},     
  },                
end

lemma sum_of_odd_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))  
  : finset.sum S f = finset.sum S (λ s, - f (- s)) :=
begin
  conv {
      to_lhs,
      operand {rw [(h s) s_mem]},                
    },    
end

lemma prod_of_odd_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))  
  : finset.prod S f = finset.prod S (λ s, - f (- s)) :=
begin
  conv {
      to_lhs,
      operand {rw [(h s) s_mem]},                 
    },    
end

lemma fold_of_odd_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = - f (- m))  
  : finset.fold (+) 0 f S = finset.fold (+) 0 (λ s, - f (- s)) S :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},                 
  },    
end

lemma sum_test_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0)  
  : finset.sum S f = 0 :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},                 
  },    
  exact multiset.sum_map_zero, --library_search
end

lemma prod_test_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 1)  
  : finset.prod S f = 1 :=
begin
  conv {
    to_lhs,
    operand {rw [(h s) s_mem]},                
  },    
  exact multiset.prod_map_one, --library_search
end

lemma fold_test_Z_no_lamda (f : ℤ → ℤ) (S : finset ℤ) (h : ∀ m ∈ S, f m = 0)  
  : finset.fold (+) 0 f S = 0 :=
begin
  conv { 
    to_lhs,
    operand {rw [(h s) s_mem]}, 
  },    
  exact multiset.sum_map_zero, --library_search
end

example : true :=
begin
  success_if_fail { conv { operand { skip }, }, },
  trivial
end
