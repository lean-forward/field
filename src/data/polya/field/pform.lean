import .basic

namespace polya.field

namespace nterm

namespace pform

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

instance : has_coe (option (nterm γ)) (nterm γ) := ⟨λ x, x.get_or_else (const 1)⟩

private lemma eval_none : eval ρ ((none : option (nterm γ)) : nterm γ) = 1 :=
by apply morph.morph_one'

private lemma eval_some {x : nterm γ} : eval ρ (some x : nterm γ) = eval ρ x := rfl

local attribute [simp] eval_none
local attribute [simp] eval_some

private def to_pform : nterm γ → option (nterm γ) | x :=
if x = const 1 then none else some x --TODO

private lemma eval_to_pform {x : nterm γ} : eval ρ (to_pform x : nterm γ) = eval ρ x :=
begin
  unfold to_pform,
  by_cases h1 : x = const 1,
  repeat { simp [h1, eval] },
end

@[simp] theorem eval_pow_mul_option {x : option (nterm γ)} {n : znum} : eval ρ (x.map (pow_mul n) : nterm γ) = eval ρ (x : nterm γ) ^ (n : ℤ) :=
by cases x; simp

private def mul' : option (nterm γ) → nterm γ → nterm γ
| (some x) y :=
  let d := znum.gcd x.exp y.exp in
    some $ pow_mul d $ mul (x.pow_div d) (y.pow_div d)
| none y := y

private lemma eval_mul' {x : option (nterm γ)} {y : nterm γ} :
  eval ρ (mul' x y) = eval ρ (x : nterm γ) * eval ρ y :=
begin
  cases x with x,
  { simp [mul'] },
  rw eval_some, unfold mul',
  --generalize : d = znum.gcd (exp x) (exp y) : znum,
  --have h1 : (d : znum) ∣ exp x, from sorry,
  --have h2 : (d : znum) ∣ exp y, from sorry,
  rw [eval_some, eval_pow_mul], unfold eval,
  rw [mul_fpow, eval_pow_div, eval_pow_div],
  { sorry },
  { sorry }
end

private def left : nterm γ → option (nterm γ)
| (mul x _) := some x
| _ := none

private def right : nterm γ → (nterm γ)
| (mul _ x) := x
| x := x

def rest (P : nterm γ) : option (nterm γ) := (left P.mem).map (pow_mul P.exp)

def lead (P : nterm γ) : nterm γ := pow_mul P.exp (right P.mem)

theorem eval_left_right (x : nterm γ) :
  eval ρ x = eval ρ (left x : nterm γ) * eval ρ (right x) :=
begin
  cases x,
  case mul : x y { simp [left, right, eval] }, 
  repeat { simp [left, right, eval] } 
end

theorem eval_rest_lead {P : nterm γ} :
  eval ρ P = eval ρ (rest P : nterm γ) * eval ρ (lead P) :=
begin
  rw [eval_mem_exp, eval_left_right, mul_fpow],
  congr' 1,
  { unfold rest, cases (mem P); simp [left] },
  { unfold lead, rw eval_pow_mul }
end

inductive r : option (nterm γ) → option (nterm γ) → Prop
| none {S : nterm γ} : r none (some S)
| rest {S : nterm γ} : r (rest S) (some S)

namespace wf

private lemma acc_r_none : @acc (option (nterm γ)) r none :=
begin
  apply acc.intro, intros x h, cases h
end

private def g : nterm γ → ℕ
| (add x _) := g x + 1
| (mul x (const _)) := g x
| _ := 0

private def f : option (nterm γ) → ℕ
| (some x) := g x + 1
| none := 0

private lemma g_scale {x : nterm γ} {a : γ} : g (x.scale a) ≤ g x :=
begin
  sorry
end

private lemma f_none {S : nterm γ} : f (none : option (nterm γ)) < f (some S) :=
by { unfold f, linarith }

private lemma f_map_scale {x : option (nterm γ)} {a : γ} : f (x.map (scale a)) ≤ f x :=
by { cases x; simp [f, g_scale] }

private lemma f_rest {S : nterm γ} : f (rest S) < f (some S) :=
begin
  sorry
end

theorem r_wf : @well_founded (option (nterm γ)) r :=
begin
  apply subrelation.wf,
  intros x y h,
  show f x < f y,
  cases h, { apply f_none }, { apply f_rest },
  apply measure_wf
end

meta def rel_tac : tactic unit := `[exact ⟨psigma.lex r (λ _, r), psigma.lex_wf wf.r_wf (λ _, wf.r_wf)⟩]

meta def dec_tac : tactic unit :=
`[apply psigma.lex.left, assumption, done]
<|> `[apply psigma.lex.right, assumption, done]

end wf

private def aux (x y : nterm γ) (p1 p2 p3 : option (nterm γ)) : nterm γ :=
if x.mem = y.mem then
  if x.exp + y.exp = 0 then (p1 : nterm γ)
  else mul' p1 (pow x.mem (x.exp + y.exp))
else if x.term < y.term then --TODO
  mul' p2 x
else
  mul' p3 y

private lemma eval_aux_1 {x y : nterm γ} {p1 p2 p3 : option (nterm γ)}
  ( H0 : x.exp + y.exp ≠ 0)
  ( H1 : eval ρ (p2 : nterm γ) = eval ρ (p1 : nterm γ) * eval ρ y )
  ( H2 : eval ρ (p3 : nterm γ) = eval ρ (p1 : nterm γ) * eval ρ x ) :
  eval ρ (aux x y p1 p2 p3) =  eval ρ (p1 : nterm γ) * eval ρ y * eval ρ x :=
begin
  unfold aux,
  by_cases h1 : x.mem = y.mem,
  { rw [if_pos h1, mul_assoc],
    { rw if_neg H0, rw [eval_mul'], congr,
      unfold eval,
      by_cases h2 : exp x = 0,
      { have : eval ρ x = 1, { rw [eval_mem_exp x, h2], simp }, rw [h1, h2, this, eval_mem_exp y], simp, },
      { by_cases h3 : eval ρ (mem x) = 0,
        { have : eval ρ x = 0, { rw [eval_mem_exp x, h3, zero_fpow], rw ← znum.cast_zero, exact_mod_cast h2 },
          rw [h3, zero_fpow, this, mul_zero],
          rw ← znum.cast_zero, exact_mod_cast H0 },
        { rw [znum.cast_add, fpow_add h3],
          rw [← eval_mem_exp, h1, ← eval_mem_exp, mul_comm] }}}},
  { rw if_neg h1,
    by_cases h2 : x.term < y.term,
    { rw if_pos h2, rw [eval_mul'], congr, apply H1 },
    { rw if_neg h2, rw [mul_assoc, mul_comm (eval ρ y), ← mul_assoc, eval_mul'], congr, apply H2 }}
end

private def mul_option : option (nterm γ) → option (nterm γ) → option (nterm γ)
| (some x) (some y) := mul' (some x) y --TODO
| none x := x
| x none := x

private lemma mul_pform_def1 {x : option (nterm γ)} :
  mul_option none x = x :=
by cases x; unfold mul_option

private lemma mul_pform_def2 {x : option (nterm γ)} :
  mul_option x none = x :=
by cases x; unfold mul_option

local attribute [simp] mul_pform_def1
local attribute [simp] mul_pform_def2

private lemma eval_mul_option {P Q : option (nterm γ)} : eval ρ (mul_option P Q : nterm γ) = eval ρ (P : nterm γ) * eval ρ (Q : nterm γ) :=
begin
  cases P, { simp },
  cases Q, { simp },
  exact eval_mul'
end

protected def mul (x y : nterm γ) : nterm γ :=
if x = const 0 ∨ y = const 0 then
  const 0
else
  mul (mul_option (to_pform x.term) (to_pform y.term)) (const (x.coeff * y.coeff))

theorem eval_mul {x y : nterm γ} : eval ρ (pform.mul x y) = eval ρ x * eval ρ y :=
begin
  unfold pform.mul,
  by_cases h1 : x = const 0 ∨ y = const 0,
  { cases h1; simp [h1, eval] },
  { rw if_neg h1, unfold eval,
    rw [eval_mul_option, eval_to_pform, eval_to_pform, morph.morph_mul],
    rw [mul_assoc, mul_comm (↑(coeff x)), ← mul_assoc (eval ρ (term y))],
    rw [← eval_term_coeff, mul_comm (eval ρ y), ← mul_assoc],
    rw [← eval_term_coeff] }
end

end pform

end nterm

end polya.field
