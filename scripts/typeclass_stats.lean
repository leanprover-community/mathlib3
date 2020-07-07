import algebra.group.defs

open tactic declaration environment native

meta def pos_line (p : option pos) : string :=
match p with
| some x := to_string x.line
| _      := ""
end

def prepare_filename₁ : string → list string :=
λ xs, ((xs.split_on '/').drop_while (λ x, x ≠ "library" ∧ x ≠ "src"))

def prepare_filename₂ : list string → list string
| ("library" :: l) := ("core" :: l)
| ("src" :: l)     := l
| _                := []

def filename : string → string :=
"/".intercalate ∘ prepare_filename₂ ∘ prepare_filename₁

def topic : string → string :=
list.head ∘ prepare_filename₂ ∘ prepare_filename₁

structure item :=
(file : string)
(line : string)
(name : string)
(topic : string)

structure node extends item.

namespace node

def jsonify : node → string :=
λ n,
"{ \"name\" : \"" ++ n.name ++ "\",\n" ++
  "\"topic\" : \"" ++ n.topic ++ "\",\n" ++
  "\"file\" : \"" ++ n.file ++ "\",\n" ++
  "\"line\" : " ++ n.line ++ " }\n"

instance : has_to_string node := ⟨jsonify⟩

end node

structure edge extends item :=
(source : string)
(target : string)

namespace edge

def jsonify : edge → string :=
λ e,
"{ \"name\" : \"" ++ e.name ++ "\",\n" ++
  "\"topic\" : \"" ++ e.topic ++ "\",\n" ++
  "\"source\" : \"" ++ e.source ++ "\",\n" ++
  "\"target\" : \"" ++ e.target ++ "\",\n" ++
  "\"file\" : \"" ++ e.file ++ "\",\n" ++
  "\"line\" : " ++ e.line ++ " }\n"

instance : has_to_string edge := ⟨jsonify⟩

end edge

/- parses information about `decl` if it is an instance or a class. -/
meta def parse_decl (env : environment) (decl : declaration) :
  tactic (option (node ⊕ edge)) :=
let name := decl.to_name in
do
    if (env.decl_olean name).is_some
    then do
      olean_file ← env.decl_olean name,
      let I : item :=
      { name := to_string name,
        file := filename olean_file,
        line := pos_line (env.decl_pos name),
        topic := topic olean_file },
      is_c ← succeeds (tactic.has_attribute `class name),
      if is_c then
        let N : node := { .. I } in
        return (some (sum.inl N))
      else do
      is_i ← succeeds (tactic.has_attribute `instance name),
      if is_i then do
        (l, tgt) ← return decl.type.pi_binders,
        -- guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
        -- guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
        let src := to_string l.ilast.type.erase_annotations.get_app_fn.const_name,
        let tgt := to_string tgt.erase_annotations.get_app_fn.const_name,
        -- guard (src ≠ tgt),
        let E : edge := { source := src, target := tgt, .. I },
        return (some (sum.inr E))
      else do return none
    else do return none

variables {α β : Type*}

def list.remove_none : list (option α) → list α
| []            := []
| (none :: l)   := l.remove_none
| (some a :: l) := a :: l.remove_none

def list.split_sum : list (α ⊕ β) → (list α) × (list β)
| []  := ([], [])
| ((sum.inl a) :: l) := let L := l.split_sum in ((a :: L.1), L.2)
| ((sum.inr b) :: l) := let L := l.split_sum in (L.1, (b :: L.2))

/-- prints information about unary classes and forgetful instances in the environment.
  It only prints instances and classes that have at most 1 argument
  that is not a type-class argument (within square brackets),
  and the instances can only be forgetful instances
  (where the conclusion is a class applied to a variable) -/
meta def print_content : tactic unit :=
do curr_env ← get_env,
   o ← (curr_env.fold [] list.cons).mmap (λ x, parse_decl curr_env x <|> pure none),
   let (ns, es) := o.remove_none.split_sum,
   trace "{ \"nodes\" : \n",
   trace (to_string ns),
   trace ",\n  \"edges\" :\n",
   trace (to_string es),
   trace "}",
   skip

meta def test : tactic unit :=
do curr_env ← get_env,
   d ← get_decl `comm_monoid.to_comm_semigroup,
   trace (to_string d.to_name),
   o ← parse_decl curr_env d,
   trace (to_string o),
   skip

-- run_cmd test

run_cmd print_content
