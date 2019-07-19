import .norm

namespace polya.field

@[derive decidable_eq, derive has_reflect]
inductive term : Type
| atom : num → term
| add  : term → term → term
| sub  : term → term → term
| mul  : term → term → term
| div  : term → term → term
| neg  : term → term
| inv  : term → term
| numeral : ℕ → term
| pow_nat : term → ℕ → term
| pow_int : term → ℤ → term

namespace term

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def eval (ρ : dict α) : term → α
| (atom i)  := ρ.val i
| (add x y) := eval x + eval y
| (sub x y) := eval x - eval y
| (mul x y) := eval x * eval y
| (div x y) := (eval x) / (eval y)
| (neg x)   := - eval x
| (inv x)   := (eval x)⁻¹
| (numeral n)   := (n : α)
| (pow_nat x n) := eval x ^ n
| (pow_int x n) := eval x ^ n

def to_nterm : term → nterm γ
| (atom i)  := nterm.atom i
| (add x y) := to_nterm x + to_nterm y
| (sub x y) := to_nterm x - to_nterm y
| (mul x y) := to_nterm x * to_nterm y
| (div x y) := to_nterm x / to_nterm y
| (neg x)   := - to_nterm x
| (inv x)   := (to_nterm x)⁻¹
| (numeral n)   := (nterm.const (n : γ))
| (pow_nat x n) := to_nterm x ^ n
| (pow_int x n) := to_nterm x ^ n

theorem correctness {x : term} :
  nterm.eval ρ (@to_nterm γ _ x) = eval ρ x :=
begin
  induction x with
    i           --atom
    x y ihx ihy --add
    x y ihx ihy --sub
    x y ihx ihy --mul
    x y ihx ihy --div
    x ihx       --neg
    x ihx       --inv
    n           --numeral
    x n ihx     --pow_nat
    x n ihx,    --pow_int
  repeat { unfold to_nterm, unfold eval },
  repeat { simp [nterm.eval] },
  repeat { simp [nterm.eval, ihx] },
  repeat { simp [nterm.eval, ihx, ihy] },
end

end term

def norm (γ : Type) [const_space γ] (x : term) : nterm γ :=
x.to_nterm.norm

def norm_hyps (γ : Type) [const_space γ] (x : term) : list (nterm γ) :=
x.to_nterm.norm_hyps

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

theorem correctness {x : term} {ρ : dict α} :
  (∀ t ∈ norm_hyps γ x, nterm.eval ρ t ≠ 0) →
  term.eval ρ x = nterm.eval ρ (norm γ x) :=
begin
  intro H,
  unfold norm,
  apply eq.symm, apply eq.trans,
  { apply nterm.correctness, unfold nterm.nonzero,
    intros t ht, apply H, exact ht },
  { apply term.correctness }
end

end polya.field