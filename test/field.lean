import tactic.field

open field tactic

def i : num := 0
def j : num := 1
def t1 : @nterm ℚ _ := i * (1 / 10 : ℚ) + i * (1 / 10 : ℚ) - i * (1 / 5 : ℚ)
def t2 : @nterm ℚ _ := i - i

--lemma slow : t1.norm = 0 := rfl
lemma fast : t2.norm = 0 := rfl

namespace pmerge

def foo (n : ℕ) : ℕ → @nterm ℚ _
| 0     := nterm.atom n
| (i+1) := foo i * nterm.atom (n-i-1)

def bar (n : ℕ) : ℕ → @nterm ℚ _
| 0     := nterm.atom 0
| (i+1) := nterm.atom (i+1) * bar i

def n : ℕ := 10

set_option profiler true
theorem test_1 : (foo n n).norm = foo n n := rfl
theorem test_2 : (bar n n).norm = foo n n := rfl

end pmerge
