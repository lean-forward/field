import .basic

namespace nterm


namespace sform

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

instance : has_coe (option (nterm γ)) (nterm γ) := ⟨λ x, x.get_or_else (const 0)⟩

private lemma eval_none : eval ρ ((none : option (nterm γ)) : nterm γ) = 0 :=
by apply morph.morph0

private lemma eval_some {x : nterm γ } : eval ρ (some x : nterm γ) = eval ρ x := rfl

local attribute [simp] eval_none
local attribute [simp] eval_some

def to_option : nterm γ → option (nterm γ) | x :=
if x = const 0 then none else some x --TODO

private lemma eval_to_option {x : nterm γ} : eval ρ (to_option x : nterm γ) = eval ρ x :=
begin
  unfold to_option,
  by_cases h1 : x = const 0,
  repeat { simp [eval, h1] }
end

private def add' : option (nterm γ) → nterm γ → nterm γ
| (some x) y := if y.coeff = 0 then x else scale (coeff y) $ add (x.scale y.coeff⁻¹) y.term
| none y := y

private lemma eval_add' {x : option (nterm γ)} {y : nterm γ} : eval ρ (add' x y) = eval ρ (x : nterm γ) + eval ρ y :=
begin
  cases x,
  { simp [add'] },
  { by_cases h1 : y.coeff = 0,
    { rw [eval_term_coeff y, h1], simp [add', h1] },
    { unfold add', rw [if_neg h1, eval_scale], unfold eval, rw eval_scale,
      rw [add_mul, mul_assoc, ← morph.morph_mul, inv_mul_cancel h1, ← eval_term_coeff],
      simp }}
end

local attribute [simp] eval_add'

private def left : nterm γ → option (nterm γ)
| (add x _) := some x
| _ := none

private def right : nterm γ → (nterm γ)
| (add _ x) := x
| x := x

def rest (S : nterm γ) : option (nterm γ) := (left S.term).map (scale S.coeff)

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

@[simp] theorem eval_scale_option {x : option (nterm γ)} {a : γ} : eval ρ (x.map (scale a) : nterm γ) = eval ρ (x : nterm γ) * a :=
by cases x; simp

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
  by_cases h1 : a = 0,
  { simp [scale, h1, g] },
  { cases x,
    case mul : x y { cases y, repeat {simp [scale, h1, g] } },
    repeat { simp [scale, h1, g] }}
end

private lemma f_none {S : nterm γ} : f (none : option (nterm γ)) < f (some S) :=
by { unfold f, linarith }

private lemma f_scale_option {x : option (nterm γ)} {a : γ} : f (x.map (scale a)) ≤ f x :=
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
        { apply f_scale_option },
        { cases x, repeat { simp [left, f, g], linarith }}},
      repeat { simp [rest, term, left, coeff, f], linarith }},
  repeat { simp [rest, term, left, f], linarith }
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

private def aux (x y : nterm γ) (s1 s2 s3 : option (nterm γ)) : nterm γ :=
  if x.term = y.term then
    if x.coeff + y.coeff = 0 then (s1 : nterm γ)
    else add' s1 (mul x.term (const (x.coeff + y.coeff)))
  else if lt x.term y.term then --TODO
    add' s2 x
  else
    add' s3 y

private lemma eval_aux {x y : nterm γ} {s1 s2 s3 : option (nterm γ)}
  ( H0 : x.coeff ≠ 0 ∧ y.coeff ≠ 0)
  ( H1 : eval ρ (s2 : nterm γ) = eval ρ (s1 : nterm γ) + eval ρ y )
  ( H2 : eval ρ (s3 : nterm γ) = eval ρ (s1 : nterm γ) + eval ρ x ) :
  eval ρ (aux x y s1 s2 s3) =  eval ρ (s1 : nterm γ) + eval ρ y + eval ρ x :=
begin
  unfold aux,
  by_cases h1 : x.term = y.term,
  { rw [if_pos h1, add_assoc],
    by_cases h2 : x.coeff + y.coeff = 0,
    { rw [if_pos h2],
      have : eval ρ y + eval ρ x = 0,
      { have : coeff x = - coeff y, from eq_neg_of_add_eq_zero h2, 
        rw [eval_term_coeff x, eval_term_coeff y, h1],
        rw [this, morph.morph_neg], ring },
      simp [this] },
    { rw if_neg h2, rw [eval_add'], congr,
      unfold eval, rw [morph.morph_add, mul_add],
      rw [← eval_term_coeff, h1, ← eval_term_coeff, add_comm] }},
  { rw if_neg h1,
    by_cases h2 : x.term < y.term,
    { rw if_pos h2, rw [eval_add'], congr, apply H1 },
    { rw if_neg h2, rw [add_assoc, add_comm (eval ρ y), ← add_assoc, eval_add'], congr, apply H2 }}
end

private def add_option : option (nterm γ) → option (nterm γ) → option (nterm γ)
| (some S) (some T) :=
  have h1 : r (rest S) (some S), from r.rest,
  have h2 : r (rest T) (some T), from r.rest,
  let s1 := (add_option (rest S) (rest T)) in
  let s2 := (add_option (rest S) (some T)) in
  let s3 := (add_option (some S) (rest T)) in
  if (lead S).coeff ≠ 0 ∧ (lead T).coeff ≠ 0 then
    some $ aux (lead S) (lead T) s1 s2 s3
  else
    add S T --should not happen
| none x := x
| x none := x
using_well_founded {
    rel_tac := λ _ _, wf.rel_tac,
    dec_tac := wf.dec_tac,
}

private lemma add_option_def1 {x : option (nterm γ)} :
  add_option none x = x :=
by cases x; unfold add_option

private lemma add_option_def2 {x : option (nterm γ)} :
  add_option x none = x :=
by cases x; unfold add_option

private lemma add_option_def3 : Π {S T : nterm γ},
  (lead S).coeff ≠ 0 ∧ (lead T).coeff ≠ 0 →
  add_option (some S) (some T) =
  some (aux (lead S) (lead T)
    (add_option (rest S) (rest T))
    (add_option (rest S) (some T))
    (add_option (some S) (rest T)) ) :=
begin
  intros S T h0,
  simp [h0, add_option]
end

private lemma eval_add_option : Π (S T : option (nterm γ)),
  eval ρ (add_option S T : nterm γ) = eval ρ (S : nterm γ) + eval ρ (T : nterm γ)
| (some S) (some T) :=
  have h1 : r (rest S) (some S), from r.rest,
  have h2 : r (rest T) (some T), from r.rest,
  let ih1 := eval_add_option (rest S) in
  let ih2 := eval_add_option (some S) (rest T) in
  begin
    by_cases h0 : (lead S).coeff ≠ 0 ∧ (lead T).coeff ≠ 0,
    { rw [eval_some, eval_some, add_option_def3 h0],
      rw [eval_some, eval_aux h0],
      { rw [ih1, add_assoc (eval ρ ↑(rest S)), ← eval_rest_lead],
        rw [add_comm (eval ρ ↑(rest S)), add_assoc, ← eval_rest_lead],
        apply add_comm },
      { rw [ih1, ih1, add_assoc, ← eval_rest_lead], refl },
      { rw [ih2, ih1, add_comm (eval ρ ↑(rest S)), add_assoc, ← eval_rest_lead],
        apply add_comm }},
    { simp [add_option, h0], refl }
  end
| none x := by rw [add_option_def1]; simp
| x none := by rw [add_option_def2]; simp
using_well_founded {
    rel_tac := λ _ _, wf.rel_tac,
    dec_tac := wf.dec_tac,
}

protected def add (x y : nterm γ) : nterm γ :=
add_option (to_option x) (to_option y)

protected theorem eval_add {x y : nterm γ} : eval ρ (sform.add x y) = eval ρ x + eval ρ y :=
by { unfold sform.add, rw [eval_add_option, eval_to_option, eval_to_option] }

end sform
end nterm
