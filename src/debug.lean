import all

set_option trace.class_instances true

--#check @prod.nonempty
--
--instance normed_space.path_connected {α : Type*} [normed_group α] [normed_space ℝ α] :
--  path_connected_space α := by apply_instance

local attribute [-instance] topological_add_group.path_connected

example : ∀ {α : Type*} {β : Type*} [h : nonempty α], nonempty (α × β) :=
by apply_instance
