import tactic.field

open field tactic

def i : num := 0
def j : num := 1
def t1 : @nterm ℚ _ := i * (1 / 2 : ℚ) + i * (1 / 2 : ℚ) - i * (1 : ℚ)
def t2 : @nterm ℚ _ := i - i

theorem slow : t1.norm = 0 := rfl
theorem fast : t2.norm = 0 := rfl

constants (x y : ℚ) (hx : x ≠ 0) (hy : y = 0)

--theorem test : x * (1 / 10) + x * (1 / 10) - x * (1 / 5) = 0 :=
--by field1

theorem test' : x * (1 / 2) + x * (1 / 2) - x = 0 :=
by field1