import tactic.field

open field tactic

def f (n : ℕ) : ℕ → @nterm ℚ _
| 0     := nterm.atom n * 1
| (i+1) := f i + nterm.atom (n-i-1) * 1
--f produces a normalized term

def g (n : ℕ) : ℕ → @nterm ℚ _
| 0     := nterm.atom 0 * 1
| (i+1) := (nterm.atom (i+1) * 1) + (g i)
--g produces a term that should normalize to f


def h (n : ℕ) : ℕ → @nterm ℚ _
| 0     := nterm.atom 0 * 1
| (i+1) := nterm.norm_sum (nterm.atom (i+1) * 1) (h i)
--h builds a term following the same pattern as g,
--but using norm_sum which adds terms while maintaining the normalized form

set_option profiler true

def n : ℕ := 10
theorem fast : (h n n) = (f n n)  := rfl
theorem slow : (g n n).norm = (f n n) * 1 := rfl

