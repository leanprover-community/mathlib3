import data.list.cycle

run_cmd guard ("c[1, 4, 3, 2]" = repr (↑[1, 4, 3, 2] : cycle ℕ))
run_cmd guard ("c[1, 4, 3, 2]" = repr (↑[2, 1, 4, 3] : cycle ℕ))
run_cmd guard ("c[-1, 2, 1, 4]" = repr (↑[(2 : ℤ), 1, 4, -1] : cycle ℤ))
