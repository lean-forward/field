import .sform .pform

namespace field
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
instance : has_pow (nterm γ) ℤ := ⟨λ (x : nterm γ) (n : ℤ), pform.pow x (n : znum)⟩

instance : has_neg (nterm γ) := ⟨scale (-1)⟩
instance : has_sub (nterm γ) := ⟨λ x y, x + -y⟩
instance : has_inv (nterm γ) := ⟨λ x, x ^ (-1 : ℤ)⟩
instance : has_div (nterm γ) := ⟨λ x y, x * y⁻¹⟩

instance pow_nat : has_pow (nterm γ) ℕ := ⟨λ (x : nterm γ) (n : ℕ), x ^ (n : ℤ)⟩

section

variables {x y : nterm γ} {i : num} {n : ℤ} {c : γ}

@[simp] theorem eval_zero  : eval ρ (0 : nterm γ) = 0       := by apply morph.morph0
@[simp] theorem eval_one   : eval ρ (1 : nterm γ) = 1       := by apply morph.morph1
@[simp] theorem eval_atom  : eval ρ (i : nterm γ) = ρ.val i := rfl
@[simp] theorem eval_const : eval ρ (c : nterm γ) = c       := rfl

@[simp] theorem eval_add : eval ρ (x + y) = eval ρ x + eval ρ y := sform.eval_add
@[simp] theorem eval_mul : eval ρ (x * y) = eval ρ x * eval ρ y := pform.eval_mul
@[simp] theorem eval_pow : eval ρ (x ^ n) = eval ρ x ^ n        := by { convert pform.eval_pow, rw znum.to_of_int }

@[simp] theorem eval_neg : eval ρ (-x)    = - x.eval ρ          := by { refine eq.trans eval_scale _, rw [morph.morph_neg, morph.morph1, mul_neg_one] }
@[simp] theorem eval_sub : eval ρ (x - y) = x.eval ρ - y.eval ρ := by { refine eq.trans eval_add _, rw [eval_neg, sub_eq_add_neg] }
@[simp] theorem eval_inv : eval ρ (x⁻¹)   = (x.eval ρ)⁻¹        := by { rw [← fpow_inv, ← eval_pow], refl }
@[simp] theorem eval_div : eval ρ (x / y) = x.eval ρ / y.eval ρ := by { rw [division_def, ← eval_inv, ← eval_mul], refl }

@[simp] theorem eval_pow_nat {n : ℕ} : eval ρ (x ^ n) = eval ρ x ^ n := eval_pow

end

end nterm
end field