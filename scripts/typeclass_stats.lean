import all

open tactic declaration environment native

meta def pos_line (p : option pos) : string :=
match p with
| some x := to_string x.line
| _      := ""
end

/- prints information about `decl` if it is an instance or a class. If `print_args` is true, it also prints
  arguments of the class as "instances" (like `topological_monoid -> monoid`). -/
meta def print_item_yaml (env : environment) (print_args : bool) (decl : declaration)
  : tactic unit :=
let name := decl.to_name in
do
    when (env.decl_olean name).is_some $ do
      olean_file ← env.decl_olean name,
      let s:= ":\n  File: " ++ olean_file ++ "\n  Line: " ++
              pos_line (env.decl_pos name),
      tactic.has_attribute `instance name >> (do
            (l, tgt) ← return decl.type.pi_binders,
            guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
            guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
            let src := to_string l.ilast.type.erase_annotations.get_app_fn.const_name,
            let tgt := to_string tgt.erase_annotations.get_app_fn.const_name,
            guard (src ≠ tgt),
            trace $ to_string decl.to_name ++ s,
            trace "  Type: instance",
            trace $ "  Source: " ++ src,
            trace $ "  Target: " ++ tgt) <|>
      tactic.has_attribute `class name >> (do
            (l, tgt) ← return decl.type.pi_binders,
            guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
            trace $ to_string decl.to_name ++ s,
            trace "  Type: class",
            when print_args $ l.tail.mmap' (λ arg, do
              let nm := arg.type.erase_annotations.get_app_fn.const_name.to_string,
              trace $ "arg_of_" ++ decl.to_name.to_string ++ "_" ++ nm ++ s,
              trace "  Type: instance",
              trace $ "  Source: " ++ decl.to_name.to_string,
              trace $ "  Target: " ++ nm)
            ) <|>
      skip

/-- prints information about unary classes and forgetful instances in the environment.
  It only prints instances and classes that have at most 1 argument that is not a type-class argument (within square brackets), and the instances can only be forgetful instances (where the conclusion is a class applied to a variable) -/
meta def print_content : tactic unit :=
do curr_env ← get_env,
   (curr_env.fold list.nil list.cons).mmap' (print_item_yaml curr_env tt)

meta def test : tactic unit :=
do curr_env ← get_env,
   d ← get_decl `topological_monoid,
   trace (to_string d.to_name),
   print_item_yaml curr_env tt d

-- run_cmd test
run_cmd print_content

