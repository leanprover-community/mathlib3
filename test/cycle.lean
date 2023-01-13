import data.list.cycle

run_cmd guard ("c[1, 4, 3, 2]" = repr (↑[1, 4, 3, 2] : cycle ℕ))
run_cmd guard ("c[1, 4, 3, 2]" = repr (↑[1, 4, 3, 2] : cycle ℕ))
run_cmd guard ("c[-1, 2, 1, 4]" = repr ([(-1 : ℤ), 2, 1, 4] : cycle ℤ))
