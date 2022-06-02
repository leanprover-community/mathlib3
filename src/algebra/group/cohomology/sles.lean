import algebra.group.cohomology.wabagoosa
-- ("short long exact sequence")
universes v u

variables {G : Type u} [group G]
noncomputable theory

namespace stuff

def one_cocycles_map {M N : Type u} [add_comm_group M] [distrib_mul_action G M]
  [add_comm_group N] [distrib_mul_action G N] (f : M →+[G] N) :
  one_cocycles G M →+ one_cocycles G N :=
((add_monoid_hom.comp_left (f : M →+ N) G).comp (one_cocycles G M).subtype).cod_restrict _ $ λ x,
begin
  intros g h,
  dsimp,
  norm_cast,
  rw [one_cocycles_map_mul, f.map_add, f.map_smul],
  abel,
end

def firstcoh_map {M N : Type u} [add_comm_group M] [distrib_mul_action G M]
  [add_comm_group N] [distrib_mul_action G N] (f : M →+[G] N) :
  firstcoh G M →+ firstcoh G N :=
((first_iso G N).to_add_monoid_hom.comp (cohomology_map f 1)).comp (first_iso G M).symm.to_add_monoid_hom

lemma firstcoh_map_apply {M N : Type u} [add_comm_group M] [distrib_mul_action G M]
  [add_comm_group N] [distrib_mul_action G N] (f : M →+[G] N) (x : one_cocycles G M) (g : G) :
  firstcoh_map f x = (one_cocycles_map f x : firstcoh G N) := sorry

-- here we go...
variables {M N P : Type u} [add_comm_group M] [add_comm_group N] [add_comm_group P]
  [distrib_mul_action G M] [distrib_mul_action G N] [distrib_mul_action G P]
  (f : M →+[G] N) (g : N →+[G] P) (hf : add_monoid_hom.ker (f : M →+ N) = ⊥)
  (hfg : add_monoid_hom.ker (g : N →+ P) = add_monoid_hom.range (f : M →+ N))
  (hg : function.surjective g) -- lol

-- i cba, these shouldn't exist. not sure which hyps i need
lemma cochains_ses_left_exact (ι : Type*) (hf : add_monoid_hom.ker (f : M →+ N) = ⊥) :
  (add_monoid_hom.comp_left (f : M →+ N) ι).ker = ⊥ := sorry

lemma cochains_ses_exact (ι : Type*) (hf : add_monoid_hom.ker (f : M →+ N) = ⊥)
  (hfg : add_monoid_hom.ker (g : N →+ P) = add_monoid_hom.range (f : M →+ N)) :
  (add_monoid_hom.comp_left (g : N →+ P) ι).ker = (add_monoid_hom.comp_left (f : M →+ N) ι).range :=
sorry

lemma cochains_ses_right_exact (ι : Type*) (hg : function.surjective g) :
  function.surjective (add_monoid_hom.comp_left (g : N →+ P) ι) := sorry

lemma invariants_ses_left_exact (hf : add_monoid_hom.ker (f : M →+ N) = ⊥) :
  (invariants_map G f).ker = ⊥ := sorry

lemma invariants_ses_exact (hf : add_monoid_hom.ker (f : M →+ N) = ⊥)
  (hfg : add_monoid_hom.ker (g : N →+ P) = add_monoid_hom.range (f : M →+ N)) :
  (invariants_map G g).ker = (invariants_map G f).range :=
sorry

def invariants_connecting_hom_aux (hf : add_monoid_hom.ker (f : M →+ N) = ⊥)
  (hfg : add_monoid_hom.ker (g : N →+ P) = add_monoid_hom.range (f : M →+ N))
  (hg : function.surjective g)
  (x : invariants G P) : one_cocycles G M :=
begin
  let X := classical.some (hg (x : P)),
  let hX : g X = x := classical.some_spec (hg (x : P)),
  have HXx : (λ g : G, g • X - X) ∈ (add_monoid_hom.comp_left (g : N →+ P) G).ker :=
  begin
    rw add_monoid_hom.mem_ker,
    ext y,
    dsimp,
    rw [g.coe_fn_coe, distrib_mul_action_hom.map_sub, g.map_smul, hX, coe_invariants y, sub_self],
  end,
  erw cochains_ses_exact f g G hf hfg at HXx,
  let Y := classical.some HXx,
  let hY : (add_monoid_hom.comp_left (f : M →+ N) G) Y = (λ g : G, g • X - X) := classical.some_spec HXx,
  use Y,
  sorry,
end

def invariants_connecting_hom (hf : add_monoid_hom.ker (f : M →+ N) = ⊥)
  (hfg : add_monoid_hom.ker (g : N →+ P) = add_monoid_hom.range (f : M →+ N))
  (hg : function.surjective g) : invariants G P →+ firstcoh G M :=
(quotient_add_group.mk' _).comp ⟨invariants_connecting_hom_aux f g hf hfg hg, sorry, sorry⟩

lemma connecting_hom_exact (hf : add_monoid_hom.ker (f : M →+ N) = ⊥)
  (hfg : add_monoid_hom.ker (g : N →+ P) = add_monoid_hom.range (f : M →+ N))
  (hg : function.surjective g) :
  (invariants_connecting_hom f g hf hfg hg).ker = (invariants_map G g).range := sorry

--lol.
end stuff
