import data.set.basic init.function data.equiv init.logic 
import algebra.group

open set

universes u v
variables {G : Type u} {H : Type v}

class subgroup [group G] (S : set G) : Prop := 
    (mul_mem : ∀ {a b}, a ∈ S → b ∈ S → a * b ∈ S) 
    (one_mem : (1 : G) ∈ S)
    (inv_mem : ∀ {a}, a ∈ S → a⁻¹ ∈ S) 

class normal_subgroup [group G] (S : set G) extends subgroup S : Prop :=
    (normal : ∀ n ∈ S, ∀ g : G, g * n * g⁻¹ ∈ S)
             
namespace subgroup
variable [group G]

attribute [simp] subgroup.one_mem 
                 subgroup.inv_mem 
                 subgroup.mul_mem
                 normal_subgroup.normal

-- Subgroup is a group
instance (S : set G) [subgroup S] : group S :=
{   mul := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, mul_mem hx hy⟩,
    mul_assoc := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, subtype.eq $ mul_assoc x y z,
    one := ⟨1, one_mem S⟩,
    one_mul := λ ⟨x, hx⟩, subtype.eq $ one_mul x,
    mul_one := λ ⟨x, hx⟩, subtype.eq $ mul_one x,
    inv := λ ⟨x, hx⟩, ⟨x⁻¹, inv_mem hx⟩,
    mul_left_inv := λ ⟨x, hx⟩, subtype.eq $ mul_left_inv x }

-- Normal subgroup properties
lemma mem_norm_comm {a b : G} {S : set G} [normal_subgroup S] (hab : a * b ∈ S) : b * a ∈ S := 
    have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ S, from normal_subgroup.normal (a * b) hab a⁻¹,
    by simp at h; exact h

-- Examples of subgroups
@[simp]
def trivial (G : Type u) [group G] : set G := {1}

instance trivial_in : normal_subgroup (trivial G) :=
    by refine {..}; simp {contextual := tt}

instance univ_in : subgroup (@univ G) :=
    by split; simp

def center (G : Type u) [group G] : set G := {z | ∀ g, g * z = z * g}

instance center_normal_in : normal_subgroup (center G) := {
    one_mem := by simp [center],
    mul_mem := begin
    intros a b ha hb g,
    rw [center, mem_set_of_eq] at *,
    rw [←mul_assoc, ha g, mul_assoc, hb g, ←mul_assoc]
    end,
    inv_mem := begin
    assume a ha g,
    simp [center] at *,
    calc
        g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹     : by simp [ha g]
        ...     = a⁻¹ * g                 : by rw [←mul_assoc, mul_assoc]; simp
    end,
    normal := begin
    simp [center, mem_set_of_eq],
    intros n ha g h,
    calc
        h * (g * n * g⁻¹) = h * n               : by simp [ha g, mul_assoc]
        ...               = g * g⁻¹ * n * h     : by rw ha h; simp
        ...               = g * n * g⁻¹ * h     : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc]
    end
}

end subgroup

-- Homomorphism subgroups
namespace is_group_hom
open subgroup
variables [group G] [group H]

@[simp]
def kernel (f : G → H) [is_group_hom f] : set G := preimage f (trivial H)

@[simp] lemma mem_ker_one {f : G → H} [is_group_hom f] {x : G} (h : x ∈ kernel f) : f x = 1 := by simp [kernel] at h; simp [h]

@[simp] lemma one_ker_inv {f : G → H} [is_group_hom f] {a b : G} (h : f (a * b⁻¹) = 1) : f a = f b := by rw ←inv_inv (f b); rw [mul f, inv f] at h; exact eq_inv_of_mul_eq_one h

@[simp] lemma inv_ker_one {f : G → H} [is_group_hom f] {a b : G} (h : f a = f b) : f (a * b⁻¹) = 1 :=
    have f a * (f b)⁻¹ = 1, by rw h; apply mul_right_inv,
    by rw [←inv f, ←mul f] at this; exact this

@[simp] lemma ker_inv {f : G → H} [is_group_hom f] {a b : G} (h : a * b⁻¹ ∈ kernel f) : f a = f b := one_ker_inv $ mem_ker_one h

@[simp] lemma inv_ker {f : G → H} [is_group_hom f] {a b : G} (h : f a = f b) : a * b⁻¹ ∈ kernel f := by simp [mem_set_of_eq]; exact inv_ker_one h

lemma one_iff_ker_inv (f : G → H) [is_group_hom f] (a b : G) : f a = f b ↔ f (a * b⁻¹) = 1 :=
    ⟨inv_ker_one, one_ker_inv⟩

lemma inv_iff_ker (f : G → H) [w : is_group_hom f] (a b : G) : f a = f b ↔ a * b⁻¹ ∈ kernel f :=
    ⟨@inv_ker _ _ _ _ f w _ _, @ker_inv _ _ _ _ f w _ _⟩ -- TODO: I don't understand why I can't just write ⟨inv_ker, ker_inv⟩ here. (This gives typeclass errors; it can't find `w`.)

instance image_in (f : G → H) [is_group_hom f] (S : set G) [subgroup S] : subgroup (f '' S) := {
    subgroup .
    mul_mem := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ * b₂, mul_mem hb₁ hb₂, by simp [eq₁, eq₂, mul f]⟩,
    one_mem := ⟨1, one_mem S, one f⟩,
    inv_mem := assume a ⟨b, hb, eq⟩,
    ⟨b⁻¹, inv_mem hb, by rw inv f; simp *⟩ 
}

instance preimage_in (f : G → H) [is_group_hom f] (S : set H) [subgroup S] : subgroup (f ⁻¹' S) :=
    by refine {..}; simp [mul f, one f, inv f] {contextual:=tt}

instance preimage_norm_in (f : G → H) [is_group_hom f] (S : set H) [normal_subgroup S] : normal_subgroup (f ⁻¹' S) :=
    by refine {..}; simp [mul f, one f, inv f] {contextual:=tt}

instance kernel_in (f : G → H) [is_group_hom f] : normal_subgroup (kernel f) := 
    is_group_hom.preimage_norm_in f (trivial H)

lemma inj_of_trivial_kernel {f : G → H} [is_group_hom f] (h : kernel f = trivial G) : function.injective f :=
    begin
    dsimp [function.injective] at *,
    intros a₁ a₂ hfa,
    simp [set_eq_def, mem_set_of_eq] at h,
    have ha : a₁ * a₂⁻¹ = 1, by rw ←h; exact inv_ker_one hfa,
    rw [eq_inv_of_mul_eq_one ha, inv_inv a₂]
    end

lemma trivial_kernel_of_inj {f : G → H} [is_group_hom f] (h : function.injective f) : kernel f = trivial G :=
    begin
    dsimp [function.injective] at *,
    simp [set_eq_def, mem_set_of_eq],
    intro,
    split,
    { 
        assume hx, 
        have hi : f x = f 1 := by simp [one f, hx],
        simp [h hi, one f]
    },
    { assume hx, simp [hx, one f] }
    end

lemma inj_iff_trivial_kernel {f : G → H} [w : is_group_hom f] : function.injective f ↔ kernel f = trivial G :=
    ⟨@trivial_kernel_of_inj _ _ _ _ f w, @inj_of_trivial_kernel _ _ _ _ f w⟩ -- TODO again, why can't it find w by itself?

end is_group_hom