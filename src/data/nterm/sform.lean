import .basic

namespace nterm

@[reducible] def sform (γ) [const_space γ] := option (nterm γ)

namespace sform

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

--instance : has_zero (sform γ) := ⟨none⟩
instance : has_coe (sform γ) (nterm γ) := ⟨λ x, x.get_or_else (const 0)⟩

private lemma eval_none : eval ρ ((none : sform γ) : nterm γ) = 0 :=
by apply morph.morph0

private lemma eval_some {x : nterm γ } : eval ρ (some x : nterm γ) = eval ρ x := rfl

local attribute [simp] eval_none
local attribute [simp] eval_some

def to_sform : nterm γ → sform γ | x :=
if x = const 0 then none else some x --TODO

private lemma eval_to_sform {x : nterm γ} : eval ρ (to_sform x : nterm γ) = eval ρ x :=
begin
  unfold to_sform,
  by_cases h1 : x = const 0,
  repeat { simp [eval, h1] }
end

private def add' : sform γ → nterm γ → nterm γ
| (some x) y := add x y
| none y := y

private lemma eval_add' {x : sform γ} {y : nterm γ} : eval ρ (add' x y) = eval ρ (x : nterm γ) + eval ρ y :=
by { cases x; simp [add', eval] }

local attribute [simp] eval_add'

private def left : nterm γ → sform γ
| (add x _) := some x
| _ := none

private def right : nterm γ → (nterm γ)
| (add _ x) := x
| x := x

def rest (S : nterm γ) : sform γ := (left S.term).map (scale S.coeff)

def lead (S : nterm γ) : nterm γ := scale S.coeff (right S.term)

theorem eval_left_right (x : nterm γ) : eval ρ x = eval ρ (left x : nterm γ) + eval ρ (right x) :=
by cases x; simp [left, right, eval]

theorem eval_rest_lead {S : nterm γ} : eval ρ S = eval ρ (rest S : nterm γ) + eval ρ (lead S) :=
begin
  rw [eval_term_coeff, eval_left_right, add_mul],
  congr' 1,
  { unfold rest, cases (term S), repeat { simp [left] }}, 
  { simp [lead] }
end

@[simp] theorem eval_map_scale {x : sform γ} {a : γ} : eval ρ (x.map (scale a) : nterm γ) = eval ρ (x : nterm γ) * a :=
by cases x; simp

inductive r : sform γ → sform γ → Prop
| none {S : nterm γ} : r none (some S)
| rest {S : nterm γ} : r (rest S) (some S)

namespace wf

private lemma acc_r_none : @acc (sform γ) r none :=
begin
  apply acc.intro, intros x h, cases h
end

private def g : nterm γ → ℕ
| (add x _) := g x + 1
| (mul x (const _)) := g x
| _ := 0

private def f : sform γ → ℕ
| (some x) := g x + 1
| none := 0

theorem g_scale {x : nterm γ} {a : γ} : g (x.scale a) ≤ g x :=
begin
  by_cases h1 : a = 0,
  { simp [scale, h1, g] },
  { cases x,
    case mul : x y { cases y, repeat {simp [scale, h1, g] } },
    repeat { simp [scale, h1, g] }}
end

private lemma f_none {S : nterm γ} : f (none : sform γ) < f (some S) :=
by { unfold f, linarith }

private lemma f_map_scale {x : sform γ} {a : γ} : f (option.map (scale a) x) ≤ f x :=
by { cases x; simp [f, g_scale] }

private lemma f_rest {S : nterm γ} : f (rest S) < f (some S) :=
begin
  --TODO: simplify proof
  show f (rest S) < g S + 1,
  cases S,
  case add : {
      simp only [rest, term, left, coeff, f, g, option.map_some', add_lt_add_iff_right],
      apply lt_of_le_of_lt, { apply g_scale }, { linarith }},
  case mul : x y {
      cases y, case const : {
        simp only [rest, term, left, coeff, g],
        apply lt_of_le_of_lt,
        { apply f_map_scale },
        { cases x, repeat { simp [left, f, g], linarith }}},
      repeat { simp [rest, term, left, coeff, f], linarith }},
  repeat { simp [rest, term, left, f], linarith }
end

theorem r_wf : @well_founded (sform γ) r :=
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

private def aux (x y : nterm γ) (s1 s2 s3 : sform γ) : nterm γ :=
  if x.term = y.term then
    if x.coeff + y.coeff = 0 then s1
    else (add' (s1.map (scale (x.coeff + y.coeff)⁻¹)) x.term).scale (x.coeff + y.coeff)
  else if lt x.term y.term then --TODO
    (add' (s2.map (scale x.coeff⁻¹)) x.term).scale x.coeff
  else
    (add' (s3.map (scale y.coeff⁻¹)) y.term).scale y.coeff

private lemma eval_aux {x y : nterm γ} {s1 s2 s3 : sform γ}
  ( H0 : x.coeff ≠ 0 ∧ y.coeff ≠ 0)
  ( H1 : eval ρ (s2 : nterm γ) = eval ρ (s1 : nterm γ) + eval ρ y )
  ( H2 : eval ρ (s3 : nterm γ) = eval ρ (s1 : nterm γ) + eval ρ x ) :
  eval ρ (aux x y s1 s2 s3) =  eval ρ (s1 : nterm γ) + eval ρ y + eval ρ x :=
begin
  unfold aux,
  by_cases h1 : x.term = y.term,
  { rw if_pos h1,
    by_cases h2 : x.coeff + y.coeff = 0,
    { rw [if_pos h2, add_assoc],
      have : eval ρ y + eval ρ x = 0,
      { have : coeff x = - coeff y, from eq_neg_of_add_eq_zero h2, 
        rw [eval_term_coeff x, eval_term_coeff y, h1],
        rw [this, morph.morph_neg], ring },
      simp [this] },
    { rw if_neg h2, rw [eval_scale, eval_add', add_mul, add_assoc (eval ρ ↑s1)],
      congr' 1,
      { suffices : eval ρ ↑s1 * ↑((coeff x + coeff y)⁻¹ * (coeff x + coeff y)) = eval ρ ↑s1,
        { rw ← this, simp [mul_assoc] },
        rw inv_mul_cancel h2, simp },
      { rw [morph.morph_add, mul_add, ← eval_term_coeff, h1, ← eval_term_coeff, add_comm] }}},
  --TODO: simplify this part:
  { rw if_neg h1,
    by_cases h2 : x.term < y.term,
    { rw if_pos h2, rw [eval_scale, eval_add', add_mul],
      congr' 1,
      { convert H1, rw [eval_map_scale, mul_assoc, ← morph.morph_mul, inv_mul_cancel H0.left], simp },
      { rw ← eval_term_coeff }},
    { rw if_neg h2, rw [eval_scale, eval_add', add_mul, add_assoc, add_comm (eval ρ y), ← add_assoc],
      congr' 1,
      { convert H2, rw [eval_map_scale, mul_assoc, ← morph.morph_mul, inv_mul_cancel H0.right], simp },
      { rw ← eval_term_coeff }}}
end

private def add_sform : sform γ → sform γ → sform γ
| (some S) (some T) :=
  have h1 : r (rest S) (some S), from r.rest,
  have h2 : r (rest T) (some T), from r.rest,
  let s1 := (add_sform (rest S) (rest T)) in
  let s2 := (add_sform (rest S) (some T)) in
  let s3 := (add_sform (some S) (rest T)) in
  if (lead S).coeff ≠ 0 ∧ (lead T).coeff ≠ 0 then
    some (aux (lead S) (lead T) s1 s2 s3)
  else
    add S T --should not happen
| none x := x
| x none := x
using_well_founded {
    rel_tac := λ _ _, wf.rel_tac,
    dec_tac := wf.dec_tac,
}

private lemma add_sform_def1 {x : sform γ} :
  add_sform none x = x :=
by cases x; unfold add_sform

private lemma add_sform_def2 {x : sform γ} :
  add_sform x none = x :=
by cases x; unfold add_sform

private lemma add_sform_def3 : Π {S T : nterm γ},
  (lead S).coeff ≠ 0 ∧ (lead T).coeff ≠ 0 →
  add_sform (some S) (some T) =
  some (aux (lead S) (lead T)
    (add_sform (rest S) (rest T))
    (add_sform (rest S) (some T))
    (add_sform (some S) (rest T)) ) :=
begin
  intros S T h0,
  simp [h0, add_sform]
end

theorem eval_add_sform : Π (S T : sform γ),
  eval ρ (add_sform S T : nterm γ) = eval ρ (S : nterm γ) + eval ρ (T : nterm γ)
| (some S) (some T) :=
  have h1 : r (rest S) (some S), from r.rest,
  have h2 : r (rest T) (some T), from r.rest,
  let ih1 := eval_add_sform (rest S) in
  let ih2 := eval_add_sform (some S) (rest T) in
  begin
    by_cases h0 : (lead S).coeff ≠ 0 ∧ (lead T).coeff ≠ 0,
    { rw [eval_some, eval_some, add_sform_def3 h0],
      rw [eval_some, eval_aux h0],
      { rw [ih1, add_assoc (eval ρ ↑(rest S)), ← eval_rest_lead],
        rw [add_comm (eval ρ ↑(rest S)), add_assoc, ← eval_rest_lead],
        apply add_comm },
      { rw [ih1, ih1, add_assoc, ← eval_rest_lead], refl },
      { rw [ih2, ih1, add_comm (eval ρ ↑(rest S)), add_assoc, ← eval_rest_lead],
        apply add_comm }},
    { simp [add_sform, h0], refl }
  end
| none x := by rw [add_sform_def1]; simp
| x none := by rw [add_sform_def2]; simp
using_well_founded {
    rel_tac := λ _ _, wf.rel_tac,
    dec_tac := wf.dec_tac,
}

protected def add (x y : nterm γ) : nterm γ :=
add_sform (to_sform x) (to_sform y)

protected theorem eval_add {x y : nterm γ} : eval ρ (sform.add x y) = eval ρ x + eval ρ y :=
by { unfold sform.add, rw [eval_add_sform, eval_to_sform, eval_to_sform] }

end sform
end nterm