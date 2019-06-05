import tactic.field

open field tactic

/- benchmak -/
--set_option profiler true

def i : num := 0
def j : num := 1
def t1 : @nterm ℚ _ := i * (1 / 10 : ℚ) + i * (1 / 10 : ℚ) - i * (1 / 5 : ℚ)
def t2 : @nterm ℚ _ := i - i

lemma slow : t1.norm = 0 := rfl
lemma fast : t2.norm = 0 := rfl

constants u v w x y z : ℝ
constants (h1 : x ≠ 0) (h2 : z ≠ 0) (h3 : x + y ≠ 0)

theorem example_1 : x * (1 / 10 : ℚ) + x * (1 / 10 : ℚ) - x * (1 / 5 : ℚ) = 0 :=
begin
  field1,
end

theorem example_2 :
  (x + y) ^ 2 / (x + y) ^ 2 * x * y / x
  = y * (z + 2 * y * x - x * y * 2) * z⁻¹:=
begin
  field1,
  { exact h2 },
  { exact h1 },
  { exact h3 },
end

theorem example_3 :
  x * ((y * w) * (z * (u * z) * v) * w)
  = w^2 * v * z^2 * u * y * x :=
begin
  field1,
end

theorem example_4 : (x / x) ^ 0 = 1 :=
begin
  field1,
end

theorem ex5 : y * (y / y) = y :=
begin
  field1,
end
