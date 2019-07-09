import .basic

namespace field
namespace nterm
namespace pform

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

instance : has_coe (option (nterm γ)) (nterm γ) := ⟨λ x, x.get_or_else (const 1)⟩

private lemma eval_none : eval ρ ((none : option (nterm γ)) : nterm γ) = 1 :=
by apply morph.morph1

private lemma eval_some {x : nterm γ } : eval ρ (some x : nterm γ) = eval ρ x := rfl

private def mul' : option (nterm γ) → nterm γ → nterm γ
| (some x) y := mul x y
| none y := y

private lemma eval_mul' {x : option (nterm γ)} {y : nterm γ} :
  eval ρ (mul' x y) = eval ρ (mul (x : nterm γ) y) :=
begin
  cases x,
  { unfold mul', unfold eval,
    rw eval_none, simp },
  { unfold mul', unfold eval, rw eval_some}
end

protected def mul (x y : nterm γ) : nterm γ :=
sorry

theorem eval_mul {x y : nterm γ} : eval ρ (pform.mul x y) = eval ρ x * eval ρ y :=
by sorry

end pform
end nterm
end field