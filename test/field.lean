import tactic.polya.field

open polya.field tactic tactic.polya.field

meta def test_on (e : expr) : tactic unit :=
do
  (t, s) ← (term_of_expr e).run ∅,
  let nt := norm γ t,
  trace nt,
  nterm_to_expr s nt >>= trace

constants x y z : ℚ

run_cmd test_on `(x - y + z)

def i : num := 0
def j : num := 1
def t1 : nterm ℚ := i * (1 / 2 : ℚ) + i * (1 / 2 : ℚ) - i * (1 : ℚ)
def t2 : nterm ℚ := i * 1 - i

--def t : nterm ℚ := ( i * (1 / 2) + i * (1 / 2) ) * i⁻¹
def t : nterm ℚ := i * i⁻¹
run_cmd ( trace t.norm)

theorem slow : t1.norm = 0 := rfl
theorem fast : t2.norm = 0 := rfl

--theorem test : x * (1 / 10) + x * (1 / 10) - x * (1 / 5) = 0 :=
--by field1

set_option trace.app_builder true

theorem test' : x * (1 / 4) + x * (1 / 4) = x * (1 / 2):=
begin
  field1,
end

run_cmd ( do
  e ← to_expr ``( (x * (1 / 2) + x * (1 / 2)) * x ⁻¹ ),
  (new_e, pr, mv, l, s) ← norm_expr e ∅,
  trace new_e
)

example : true :=
by do
  e ← to_expr ``(x * x⁻¹),
  --this should create no new goals
  (new_e, pr, mv, mvs, s) ← norm_expr e ∅,
  exact `(trivial)