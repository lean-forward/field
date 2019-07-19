import .sform .pform

namespace polya.field

namespace nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

instance coe_atom  : has_coe num (nterm γ) := ⟨atom⟩
instance coe_const : has_coe γ (nterm γ) := ⟨const⟩

instance : has_zero (nterm γ) := ⟨const 0⟩
instance : has_one (nterm γ) := ⟨const 1⟩

instance : has_add (nterm γ) := ⟨sform.add⟩
instance : has_mul (nterm γ) := ⟨pform.mul⟩
instance : has_pow (nterm γ) ℤ := ⟨λ (x : nterm γ) (n : ℤ), pow_mul (n : znum) x⟩

instance : has_neg (nterm γ) := ⟨scale (-1)⟩
instance : has_sub (nterm γ) := ⟨λ x y, x + -y⟩
instance : has_inv (nterm γ) := ⟨λ x, x ^ (-1 : ℤ)⟩
instance : has_div (nterm γ) := ⟨λ x y, x * y⁻¹⟩

instance pow_nat : has_pow (nterm γ) ℕ := ⟨λ (x : nterm γ) (n : ℕ), x ^ (n : ℤ)⟩

section

variables {x y : nterm γ} {i : num} {n : ℤ} {c : γ}

@[simp] theorem eval_zero  : eval ρ (0 : nterm γ) = 0 := by apply morph.morph_zero'
@[simp] theorem eval_one   : eval ρ (1 : nterm γ) = 1 := by apply morph.morph_one'
@[simp] theorem eval_const : eval ρ (const c) = c     := rfl
@[simp] theorem eval_atom  : eval ρ (atom i : nterm γ) = ρ.val i := rfl

@[simp] theorem eval_add : eval ρ (x + y) = eval ρ x + eval ρ y := sform.eval_add
@[simp] theorem eval_mul : eval ρ (x * y) = eval ρ x * eval ρ y := pform.eval_mul
@[simp] theorem eval_pow : eval ρ (x ^ n) = eval ρ x ^ n        := by { convert eval_pow_mul, rw znum.to_of_int }

@[simp] theorem eval_neg : eval ρ (-x)    = - x.eval ρ          := by { refine eq.trans eval_scale _, rw [morph.morph_neg, morph.morph_one', mul_neg_one] }
@[simp] theorem eval_sub : eval ρ (x - y) = x.eval ρ - y.eval ρ := by { refine eq.trans eval_add _, rw [eval_neg, sub_eq_add_neg] }
@[simp] theorem eval_inv : eval ρ (x⁻¹)   = (x.eval ρ)⁻¹        := by { rw [← fpow_inv, ← eval_pow], refl }
@[simp] theorem eval_div : eval ρ (x / y) = x.eval ρ / y.eval ρ := by { rw [division_def, ← eval_inv, ← eval_mul], refl }

@[simp] theorem eval_pow_nat {n : ℕ} : eval ρ (x ^ n) = eval ρ x ^ n := eval_pow

end

end nterm

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

theorem correctness {x : term} : nterm.eval ρ (@to_nterm γ _ x) = eval ρ x :=
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
  repeat { simp [nterm.eval, ihx, ihy] }
end

--def to_nterm : term → nterm γ
--| (atom i)  := nterm.atom i
--| (add x y) := nterm.add (to_nterm x) (to_nterm y)
--| (sub x y) := nterm.add (to_nterm x) (nterm.mul (to_nterm y) (nterm.const (-1)))
--| (mul x y) := nterm.mul (to_nterm x) (to_nterm y)
--| (div x y) := nterm.mul (to_nterm x) (nterm.pow (to_nterm y) (-1))
--| (neg x)   := nterm.mul (to_nterm x) (nterm.const (-1))
--| (inv x)   := nterm.pow (to_nterm x) (-1)
--| (numeral n)   := nterm.const (n : γ)
--| (pow_nat x n) := nterm.pow (to_nterm x) (n : znum)
--| (pow_int x n) := nterm.pow (to_nterm x) (n : znum)
--
--theorem correctness {x : term} : nterm.eval ρ (@to_nterm γ _ x) = eval ρ x :=
--by sorryk

end term

def norm (γ : Type) [const_space γ] (x : term) : nterm γ :=
@term.to_nterm γ _ x

def norm_hyps (γ : Type) [const_space γ] (x : term) : list (nterm γ) :=
[]

variables {γ : Type} [const_space γ]
variables {α : Type} [discrete_field α]
variables [morph γ α] {ρ : dict α}

theorem correctness {x : term} {ρ : dict α} :
  (∀ t ∈ norm_hyps γ x, nterm.eval ρ t ≠ 0) →
  term.eval ρ x = nterm.eval ρ (norm γ x) :=
begin
  intro h, apply eq.symm,
  apply term.correctness
end

end polya.field