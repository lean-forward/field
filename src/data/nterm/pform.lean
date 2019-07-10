import .basic

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

private def left : nterm γ → pform γ
| (mul x _) := some x
| _ := none

private def right : nterm γ → (nterm γ)
| (mul _ x) := x
| x := x

def rest (P : nterm γ) : pform γ := (left P.mem).map (pow_mul P.exp)

def lead (P : nterm γ) : nterm γ := pow_mul P.exp (right P.mem)

theorem eval_left_right (x : nterm γ) :
  eval ρ x = eval ρ (left x : nterm γ) * eval ρ (right x) :=
begin
  cases x,
  case mul : x y { unfold left, unfold right, unfold eval, rw eval_some },
  repeat { unfold left, unfold right, unfold eval, rw [eval_none, one_mul] }
end

theorem eval_rest_lead {P : nterm γ} :
  eval ρ P = eval ρ (rest P : nterm γ) * eval ρ (lead P) :=
begin
  rw [eval_mem_exp, eval_left_right, mul_fpow],
  congr' 1,
  { unfold rest, cases (mem P),
    case mul : { dsimp [left, option.map], rw [eval_some, eval_some, eval_pow_mul] },
    repeat { dsimp [left, option.map], rw [eval_none, one_fpow] }},
  { unfold lead, rw eval_pow_mul }
end

private def mul_pform : pform γ → pform γ → pform γ
| x y := mul' x y --TODO

private lemma eval_mul_pform {P Q : pform γ} : eval ρ (mul_pform P Q : nterm γ) = eval ρ (P : nterm γ) * eval ρ (Q : nterm γ) :=
by apply eval_mul'

protected def mul (x y : nterm γ) : nterm γ :=
if x = const 0 ∨ y = const 0 then
  const 0
else
  mul (mul_pform (to_pform x.term) (to_pform y.term)) (const (x.coeff * y.coeff))

theorem eval_mul {x y : nterm γ} : eval ρ (pform.mul x y) = eval ρ x * eval ρ y :=
begin
  unfold pform.mul,
  by_cases h1 : x = const 0 ∨ y = const 0,
  { rw if_pos h1, cases h1; rw h1; simp [eval] },
  { rw if_neg h1, unfold eval,
    rw [eval_mul_pform, eval_to_pform, eval_to_pform, morph.morph_mul],
    rw [mul_assoc, mul_comm (↑(coeff x)), ← mul_assoc (eval ρ (term y))],
    rw [← eval_term_coeff, mul_comm (eval ρ y), ← mul_assoc],
    rw [← eval_term_coeff] }
end

end pform
end nterm
