import .basic

namespace field
namespace nterm

@[reducible] def pform (γ) [const_space γ] := option (nterm γ)

namespace pform

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

--instance : has_one (pform γ) := ⟨none⟩
instance : has_coe (pform γ) (nterm γ) := ⟨λ x, x.get_or_else (const 1)⟩

private lemma eval_none : eval ρ ((none : pform γ) : nterm γ) = 1 :=
by apply morph.morph1

private lemma eval_some {x : nterm γ } : eval ρ (some x : nterm γ) = eval ρ x := rfl

private def to_pform : nterm γ → pform γ | x :=
if x = const 1 then none else some x --TODO

private lemma eval_to_pform {x : nterm γ} : eval ρ (to_pform x : nterm γ) = eval ρ x :=
begin
  unfold to_pform,
  by_cases h1 : x = const 1,
  { rw [if_pos h1, h1, eval_none], simp [eval] },
  { rw [if_neg h1, eval_some] }
end

private def mul' : pform γ → nterm γ → nterm γ
| (some x) y := mul x y
| none y := y

private lemma eval_mul' {x : pform γ} {y : nterm γ} :
  eval ρ (mul' x y) = eval ρ (x : nterm γ) * eval ρ y :=
begin
  cases x,
  { unfold mul', rw [eval_none, one_mul]  },
  { unfold mul', unfold eval, rw eval_some}
end

private def mul_pform : pform γ → pform γ → pform γ
| x y := mul' x y --TODO

private lemma eval_mul_pform {P Q : pform γ} : eval ρ (mul_pform P Q : nterm γ) = eval ρ (P : nterm γ) * eval ρ (Q : nterm γ) :=
by apply eval_mul'

protected def mul (x y : nterm γ) : nterm γ :=
mul (mul_pform (to_pform x.term) (to_pform y.term)) (const (x.coeff * y.coeff))

theorem eval_mul {x y : nterm γ} : eval ρ (pform.mul x y) = eval ρ x * eval ρ y :=
begin
  unfold pform.mul, unfold eval,
  rw [eval_mul_pform, eval_to_pform, eval_to_pform, morph.morph_mul],
  rw [mul_assoc, mul_comm (↑(coeff x)), ← mul_assoc (eval ρ (term y))],
  rw [← eval_term_coeff, mul_comm (eval ρ y), ← mul_assoc],
  rw [← eval_term_coeff], refl
end

protected def pow (x : nterm γ) (n : znum) : nterm γ :=
if n = 0 then const 1 else pow x.mem (x.exp * n)

--TODO: instace : has_pow α znum
theorem eval_pow {x : nterm γ} {n : znum} : eval ρ (pform.pow x n) = eval ρ x ^ (n : ℤ) :=
begin
  unfold pform.pow,
  by_cases h1 : n = 0,
  { rw [if_pos h1, h1, znum.cast_zero, fpow_zero], simp [eval] },
  { rw [if_neg h1], unfold eval,
    by_cases h2 : eval ρ (mem x) = 0,
    { rw [if_pos h2, eval_mem_zero.mpr h2, zero_fpow],
      rw ← znum.cast_zero, intro h, apply h1,
      apply znum.cast_inj.mp, apply h },
    { rw [if_neg h2, eval_mem_exp x, znum.cast_mul, fpow_mul],
      intro h, apply h2, rw ← eval_mem_zero, apply h}}
end

end pform
end nterm
end field
