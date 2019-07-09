import .sform .pform

namespace field
namespace nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

instance coe_atom : has_coe num (nterm γ) := ⟨atom⟩
instance coe_const: has_coe γ (nterm γ) := ⟨const⟩
instance : has_zero (nterm γ) := ⟨const 0⟩
instance : has_one (nterm γ) := ⟨const 1⟩
instance : has_add (nterm γ) := ⟨sform.add⟩
instance : has_mul (nterm γ) := ⟨pform.mul⟩
instance : has_pow (nterm γ) znum := ⟨λ x n, if n = 0 then 1 else sorry⟩
instance pow_nat : has_pow (nterm γ) ℕ := ⟨λ (x : nterm γ) (n : ℕ), x ^ (n : znum)⟩ --test
instance pow_int : has_pow (nterm γ) ℤ := ⟨λ (x : nterm γ) (n : ℤ), x ^ (n : znum)⟩ --test

def neg (x : nterm γ) : nterm γ := x.scale (-1)
def sub (x y : nterm γ) : nterm γ := x + neg y
def inv (x : nterm γ) : nterm γ := x ^ (-1 : znum)
def div (x y : nterm γ) : nterm γ := x * (inv y)

instance : has_neg (nterm γ) := ⟨neg⟩
instance : has_sub (nterm γ) := ⟨sub⟩
instance : has_inv (nterm γ) := ⟨inv⟩
instance : has_div (nterm γ) := ⟨div⟩

section
variables {x y : nterm γ} {i : num} {n : znum} {c : γ}

@[simp] theorem eval_zero  : eval ρ (0 : nterm γ) = 0       := by apply morph.morph0
@[simp] theorem eval_one   : eval ρ (1 : nterm γ) = 1       := by apply morph.morph1
@[simp] theorem eval_atom  : eval ρ (i : nterm γ) = ρ.val i := rfl
@[simp] theorem eval_const : eval ρ (c : nterm γ) = c       := rfl

@[simp] theorem eval_add : eval ρ (x + y) = eval ρ x + eval ρ y := sform.eval_add
@[simp] theorem eval_mul : eval ρ (x * y) = eval ρ x * eval ρ y := pform.eval_mul
@[simp] theorem eval_pow : eval ρ (x ^ n) = eval ρ x ^ (n : ℤ)  := sorry

@[simp] theorem eval_neg : eval ρ (-x)    = - x.eval ρ          := by { refine eq.trans eval_scale _, rw [morph.morph_neg, morph.morph1, mul_neg_one] }
@[simp] theorem eval_sub : eval ρ (x - y) = x.eval ρ - y.eval ρ := sorry
@[simp] theorem eval_inv : eval ρ (x⁻¹)   = (x.eval ρ)⁻¹        := sorry
@[simp] theorem eval_div : eval ρ (x / y) = x.eval ρ / y.eval ρ := sorry

@[simp] theorem eval_pow_nat {n : ℕ} : eval ρ (x ^ n) = eval ρ x ^ n := sorry
@[simp] theorem eval_pow_int {n : ℤ} : eval ρ (x ^ n) = eval ρ x ^ n := sorry

end

end nterm
end field