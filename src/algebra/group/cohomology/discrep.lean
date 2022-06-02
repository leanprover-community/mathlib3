import topology.category.Profinite.projective

#exit
import algebra.group.cohomology.group_ring
import category_theory.abelian.right_derived
universes v u
variables {k G : Type u} [comm_ring k] [topological_space G] [group G] [topological_group G]
{V : Type u} [add_comm_group V] [module k V] (ρ : representation k G V) (v : V)
noncomputable def stabilizer (v : V) :
 subgroup G :=
{ carrier := { g | ρ g v = v },
  mul_mem' := λ g h (hg : _ = _) (hh : _ = _), show _ = _, by {rw ρ.map_mul, dsimp, rw hh, rw hg},
  one_mem' := show ρ 1 v = v, by rw ρ.map_one; refl,
  inv_mem' := λ x (hx : _ = _), show _ = _, by {conv_lhs {rw ←hx},
  show (ρ x⁻¹ * ρ x) v = v,
  rw ←ρ.map_mul, rw inv_mul_self, rw ρ.map_one, refl}}

instance : topological_space (Mon.of G) :=
by assumption

instance seriously : group (Mon.of G) :=
by assumption

instance : topological_group (Mon.of G) :=
by assumption

structure DiscRep (k : Type u) [comm_ring k] (G : Type u) [topological_space G] [group G] [topological_group G] :=
(A : Rep k G)
[is_top : topological_space A]
[is_disc : discrete_topology A]
(open_stabilizer : ∀ a : A, is_open (↑(stabilizer A.ρ a) : set (Mon.of G)))

namespace DiscRep
open category_theory
open category_theory.limits

instance : category (DiscRep k G) :=
{ hom := λ M N, M.A ⟶ N.A,
  id := λ M, 𝟙 M.A,
  comp := λ M N K f g, f.comp g, }

def DiscRep.of {k : Type u} [comm_ring k] {G : Type u} [topological_space G] [group G] [topological_group G]
  {A : Type u} [add_comm_group A] [module k A] (ρ : representation k G A) [topological_space A] [discrete_topology A]
  (H : ∀ a : A, is_open (stabilizer ρ a : set G)) :
  DiscRep k G :=
{ A := Rep.of ρ,
  is_top := by assumption,
  is_disc := by assumption,
  open_stabilizer := H }

def fixed_by (s : set G) :
  submodule k V :=
{ carrier := {x | ∀ g ∈ s, ρ g x = x},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

def union_fixed: submodule k V :=
{ carrier := ⋃ U ∈ set_of (@is_open G _), fixed_by ρ U,
  add_mem' := λ x y hx hy,
  begin
    obtain ⟨Ux, ⟨hUx, hρx⟩⟩ := set.mem_Union₂.1 hx,
    obtain ⟨Uy, ⟨hUy, hρy⟩⟩ := set.mem_Union₂.1 hy,
    rw set.mem_Union₂,
    use Ux ∩ Uy,
    split,
    exact is_open.inter hUx hUy,
    intros g hg,
    rw map_add,
    rw hρx g ((set.mem_inter_iff _ _ _).1 hg).1,
    rw hρy g ((set.mem_inter_iff _ _ _).1 hg).2,
  end,
  zero_mem' := set.mem_Union₂.2 $
  begin
    use set.univ,
    split,
    exact is_open_univ,
    intros g hg,
    exact map_zero _,
  end,
  smul_mem' := sorry }

instance : has_coe (union_fixed ρ) V :=
{ coe := λ x, x.1 }

def union_ρ : G →* (union_fixed ρ →ₗ[k] union_fixed ρ) :=
{ to_fun := λ g, ((ρ g).comp (union_fixed ρ).subtype).cod_restrict _ sorry,
  map_one' := sorry,
  map_mul' := sorry }

instance eugh : topological_space (union_fixed ρ) := ⊥

instance sdf : discrete_topology (union_fixed ρ) := by apply_instance

lemma open_stabilizer_union (x : union_fixed ρ) : is_open (stabilizer (union_ρ ρ) x : set G) :=
sorry
/--/
lemma open_stabilizer_disc (A : Rep k G) (x : (to_disc_obj A)) :
  is_open (stabilizer (to_disc_obj A).ρ x : set (Mon.of G)) :=
open_stabilizer_union _ _-/

def to_disc_obj (A : Rep k G) : DiscRep k G :=
{ A := { V := union_fixed A.ρ,
  ρ := union_ρ A.ρ },
  is_top := DiscRep.eugh A.ρ,
  is_disc := DiscRep.sdf A.ρ,
  open_stabilizer := open_stabilizer_union _ }

def union_map {M N : Type u} [add_comm_group M] [add_comm_group N] [module k M] [module k N]
  (ρM : representation k G M) (ρN : representation k G N)
  (f : M →ₗ[k] N) :
  union_fixed ρM →ₗ[k] union_fixed ρN :=
(f.comp (union_fixed ρM).subtype).cod_restrict _ sorry

def to_disc_map (M N : Rep k G) (f : M ⟶ N) :
  to_disc_obj M ⟶ to_disc_obj N :=
{ hom := union_map M.ρ N.ρ f.hom,
  comm' := sorry }

#check to_disc_map
--def DiscRep.hom_mk (M N : DiscRep k G) (f : M.A ⟶ N.A)

def to_disc : Rep k G ⥤ DiscRep k G :=
{ obj := λ A, to_disc_obj A,
  map := λ M N f, to_disc_map M N f,
  map_id' := sorry,
  map_comp' := sorry }

instance : enough_injectives (DiscRep k G) := sorry

instance :
