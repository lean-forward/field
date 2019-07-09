import data.real.basic data.num.lemmas

section

local attribute [semireducible] reflected

meta instance rat.reflect : has_reflect ℚ
| ⟨n, d, _, _⟩ := `(rat.mk_nat %%(reflect n) %%(reflect d))

end

meta def tactic.interactive.intros' : tactic unit :=
`[repeat {intro}, resetI]

attribute [elim_cast] znum.cast_inj
attribute [squash_cast] znum.to_of_int
attribute [squash_cast] znum.cast_zero
attribute [move_cast] znum.cast_add
--TODO

namespace option

theorem map_map {α β γ} {f : α → β} {g : β → γ} {x : option α} :
  option.map g (option.map f x) = option.map (g ∘ f) x :=
begin
  sorry
end

end option

namespace list

theorem filter_perm {α} {p : α → Prop} [decidable_pred p] {l : list α} :
  l ~ l.filter p ++ l.filter (not ∘ p) :=
begin
  induction l with x xs ih,
  { simp },
  { by_cases hx : p x,
    { simp [filter, hx, perm.skip, ih] },
    { calc
      x::xs ~ x::(filter p xs ++ filter (not ∘ p) xs) : perm.skip _ ih
      ... ~ filter p xs ++ x::filter (not ∘ p) xs : perm.symm perm_middle
      ... ~ filter p (x::xs) ++ filter (not ∘ p) (x::xs) : by simp [hx] }}
end

theorem prod_ones {α} [monoid α] {l : list α} :
  (∀ x : α, x ∈ l → x = 1) → l.prod = 1 :=
begin
  intro h,
  induction l with x xs ih,
  { refl },
  { have h1 : x = 1, by { apply h, simp },
    have h2 : prod xs = 1, by { apply ih, intros _ hx, apply h, simp [hx] },
    simp [h1, h2] }
end

theorem sum_zeros {α} [add_monoid α] {l : list α} :
  (∀ x : α, x ∈ l → x = 0) → l.sum = 0 :=
begin
  intro h,
  induction l with x xs ih,
  { refl },
  { have h1 : x = 0, by { apply h, simp },
    have h2 : sum xs = 0, by { apply ih, intros _ hx, apply h, simp [hx] },
    simp [h1, h2] }
end

end list

namespace field

structure dict (α : Type) :=
(val : num → α)

class morph (γ : Type) [discrete_field γ] (α : Type) [discrete_field α] :=
(cast   : has_coe γ α)
(morph0 : ((0 : γ) : α) = 0)
(morph1 : ((1 : γ) : α) = 1)
(morph_add : ∀ a b : γ, ((a + b : γ) : α) = a + b)
(morph_neg : ∀ a : γ, ((-a : γ) : α) = -a)
(morph_mul : ∀ a b : γ, ((a * b : γ) : α) = a * b)
(morph_inv : ∀ a : γ, ((a⁻¹ : γ) : α) = a⁻¹)
(morph_inj : ∀ a : γ, (a : α) = 0 → a = 0)

namespace morph

instance rat_morph {α} [discrete_field α] [char_zero α] : morph ℚ α :=
{ cast      := by apply_instance,
  morph0    := rat.cast_zero,
  morph1    := rat.cast_one,
  morph_add := rat.cast_add,
  morph_neg := rat.cast_neg,
  morph_mul := rat.cast_mul,
  morph_inv := rat.cast_inv,
  morph_inj := begin
      intros a ha,
      apply rat.cast_inj.mp,
      { rw rat.cast_zero, apply ha },
      { resetI, apply_instance }
    end,
}

attribute [simp] morph.morph0
attribute [simp] morph.morph1
attribute [simp] morph.morph_mul
--TODO

variables {α : Type} [discrete_field α]
variables {γ : Type} [discrete_field γ]
variables [morph γ α]
variables {a b : γ}

instance has_coe : has_coe γ α := morph.cast γ α

@[squash_cast] theorem morph0' : ((0 : γ) : α) = 0 := by apply morph.morph0
@[squash_cast] theorem morph1' : ((1 : γ) : α) = 1 := by apply morph.morph1

@[move_cast] theorem morph_add' : ∀ a b : γ, ((a + b : γ) : α) = a + b := by apply morph_add
@[move_cast] theorem morph_neg' : ∀ a : γ, ((-a : γ) : α) = -a := by apply morph_neg
@[move_cast] theorem morph_mul' : ∀ a b : γ, ((a * b : γ) : α) = a * b := by apply morph_mul
@[move_cast] theorem morph_inv' : ∀ a : γ, ((a⁻¹ : γ) : α) = a⁻¹ := by apply morph_inv

@[move_cast] theorem morph_sub : ((a - b : γ) : α) = a - b :=
by rw [sub_eq_add_neg, morph.morph_add, morph.morph_neg, ← sub_eq_add_neg]

@[elim_cast] theorem morph_inj' : ∀ a b : γ, (a : α) = b ↔ a = b :=
begin
  intros a b,
  apply iff.intro,
  { intro h, apply eq_of_sub_eq_zero,
    apply morph.morph_inj (a - b),
    rw morph.morph_sub,
    apply sub_eq_zero_of_eq,
    apply h },
  { intro h, subst h }
end

@[move_cast] theorem morph_div : ((a / b : γ) : α) = a / b :=
by rw [division_def, morph.morph_mul, morph.morph_inv, ← division_def]

@[move_cast] theorem morph_pow_nat (n : ℕ) : ((a ^ n : γ) : α) = a ^ n :=
begin
  induction n with _ ih,
  { rw [pow_zero, pow_zero, morph.morph1] },
  { by_cases ha : a = 0,
    { rw [ha, morph.morph0, zero_pow, zero_pow],
      { apply morph.morph0 },
      { apply nat.succ_pos },
      { apply nat.succ_pos }},
    { rw [pow_succ, morph.morph_mul, ih, ← pow_succ] }}
end

@[move_cast] theorem morph_pow (n : ℤ) : ((a ^ n : γ) : α) = a ^ n :=
begin
  cases n,
  { rw [int.of_nat_eq_coe, fpow_of_nat, fpow_of_nat],
    apply morph_pow_nat },
  { rw [int.neg_succ_of_nat_coe, fpow_neg, fpow_neg],
    rw [morph_div, morph.morph1],
    rw [fpow_of_nat, fpow_of_nat],
    rw morph_pow_nat }
end

end morph

class const_space (γ : Type) : Type :=
(df : discrete_field γ)
(lt : γ → γ → Prop)
(dec : decidable_rel lt)

namespace const_space
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]

instance discrete_field : discrete_field γ := const_space.df γ
instance has_lt : has_lt γ := ⟨const_space.lt⟩
instance decidable_rel : @decidable_rel γ (<) := const_space.dec γ

end const_space

@[derive decidable_eq, derive has_reflect]
--TODO: make γ explicit
inductive nterm (γ : Type) [const_space γ] : Type
| atom  {} : num → nterm
| const {} : γ → nterm
| add   {} : nterm → nterm → nterm
| mul   {} : nterm → nterm → nterm
| pow   {} : nterm → znum → nterm

namespace nterm
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def blt :
  nterm γ → nterm γ → bool
| (const a) (const b) := a < b
| (const _) _         := tt
| _         (const _) := ff
| (atom i)  (atom j)  := i < j
| (atom _)  _         := tt
| _         (atom _)  := ff
| (add x y) (add z w) := if y = w then blt x z else blt y w
| (add _ _) _         := tt
| _         (add _ _) := ff
| (mul x y) (mul z w) := if y = w then blt x z else blt y w
| (mul _ _) _         := tt
| _         (mul _ _) := ff
| (pow x n) (pow y m) := if x = y then n < m else blt x y

def lt : nterm γ → nterm γ → Prop := λ x y, blt x y
instance : has_lt (nterm γ) := ⟨lt⟩
instance dec_lt : decidable_rel (@lt γ _) := by dunfold lt; apply_instance

--instance trans_le : is_trans _ (@le γ _) := by sorry
--instance antisymm_le : is_antisymm _ (@le γ _) := by sorry
--instance is_total : is_total _ (@le γ _) := by sorry

def eval (ρ : dict α) : nterm γ → α
| (atom i)  := ρ.val i
| (const c) := ↑c
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x n) := if eval x = 0 then 0 else eval x ^ (n : ℤ)

meta def to_str [has_to_string γ] : (nterm γ) → string
| (atom i)  := "#" ++ to_string (i : ℕ)
| (const c) := to_string c
| (add x y) := "(" ++ to_str x ++ " + " ++ to_str y ++ ")"
| (mul x y) := "(" ++ to_str x ++ " * " ++ to_str y ++ ")"
| (pow x n) := to_str x ++ " ^ " ++ to_string (n : ℤ)

meta instance [has_to_string γ] : has_to_string (nterm γ) := ⟨to_str⟩
meta instance [has_to_string γ] : has_to_tactic_format (nterm γ) := ⟨λ x, return (to_str x : format)⟩

def sum : list (nterm γ) → nterm γ
| []      := const 0
| [x]     := x
| (x::xs) := add (sum xs) x

def prod : list (nterm γ) → nterm γ
| []      := const 1
| [x]     := x
| (x::xs) := mul (prod xs) x

theorem eval_sum (xs : list (nterm γ)) :
  (sum xs).eval ρ = list.sum (xs.map (nterm.eval ρ)) :=
begin
  induction xs with x0 xs ih,
  { simp [sum, eval] },
  { cases xs with x1 xs,
    { simp [sum] },
    { unfold sum, rw [list.map_cons, list.sum_cons, eval, ih, add_comm] }}
end

theorem eval_prod (xs : list (nterm γ)) :
  (prod xs).eval ρ = list.prod (xs.map (nterm.eval ρ)) :=
begin
  induction xs with x0 xs ih,
  { simp [prod, eval] },
  { cases xs with x1 xs,
    { simp [prod] },
    { unfold prod, rw [list.map_cons, list.prod_cons, eval, ih, mul_comm] }}
end

def nonzero (ρ : dict α) (ts : list (nterm γ)) : Prop :=
∀ t ∈ ts, nterm.eval ρ t ≠ 0

theorem nonzero_union {xs ys : list (nterm γ)} :
nonzero ρ (xs ∪ ys) ↔ nonzero ρ xs ∧ nonzero ρ ys :=
begin
  apply iff.intro,
  { intro h1, split; { intros _ h2, apply h1, simp [h2] }},
  { intros h1 t ht, cases h1 with h1 h2, rw list.mem_union at ht, cases ht,
    {apply h1, apply ht}, {apply h2, apply ht}}
end

theorem nonzero_subset {xs ys : list (nterm γ)} :
  xs ⊆ ys → nonzero ρ ys → nonzero ρ xs :=
begin
  intros h1 h2, intros x hx,
  apply h2, apply h1, apply hx
end

theorem nonzero_iff_zero_not_mem (ts : list (nterm γ)) :
nonzero ρ ts ↔ (0 : α) ∉ ts.map (nterm.eval ρ) :=
begin
  apply iff.intro,
  { intro h, simpa using h },
  { intro h, simp at h, apply h }
end

def scale (a : γ) (x : nterm γ) : nterm γ :=
match x with
| (mul x (const b)) := mul x (const (a * b))
| x := mul x (const a) --should not happen
end

def coeff : nterm γ → γ
| (mul x (const a)) := a
| x := 1 --should not happen

def term : nterm γ → nterm γ
| (mul x (const a)) := x
| x := x --should not happen

theorem eval_scale {a : γ} {x : nterm γ} :
  eval ρ (x.scale a) = eval ρ x * a :=
begin
  unfold scale, cases x,
  case mul : x y { 
    cases y,
    case const : b {
      unfold scale, unfold eval,
      rw [mul_assoc, mul_comm a, morph.morph_mul],
      refl },
    repeat { refl }},
  repeat { refl }
end
theorem eval_scale_add {a b : γ} {x : nterm γ} :
  eval ρ (x.scale (a + b)) = eval ρ (x.scale a) + eval ρ (x.scale b) :=
by rw [eval_scale, eval_scale, eval_scale, morph.morph_add, mul_add]
theorem eval_scale_zero {x : nterm γ} :
  eval ρ (x.scale 0) = 0 :=
by rw [eval_scale, morph.morph0, mul_zero]
theorem eval_scale_one {x : nterm γ} :
  eval ρ (x.scale 1) = eval ρ x :=
by rw [eval_scale, morph.morph1, mul_one]
theorem eval_scale_neg {a : γ} {x : nterm γ} :
  eval ρ (x.scale (-a)) = - eval ρ (x.scale a) :=
by rw [eval_scale, eval_scale, morph.morph_neg, neg_mul_eq_mul_neg]
theorem scale_comp {a b : γ} : scale a ∘ scale b = scale (a * b) :=
begin
  funext x, cases x,
  case mul : x y {
    cases y, case const : a { dsimp [function.comp, scale], rw mul_assoc, refl },
    repeat { dsimp [function.comp, scale], refl }},
  repeat { dsimp [function.comp, scale], refl }
end

theorem eval_term_coeff (x : nterm γ) :
  eval ρ x = eval ρ x.term * x.coeff :=
begin
  cases x,
  case mul : x y { 
    cases y,
    case const : { unfold coeff, unfold term, refl },
    repeat { unfold coeff, unfold term, rw [morph.morph1, mul_one] },
  },
  repeat { unfold coeff, unfold term, rw [morph.morph1, mul_one] }
end

instance : has_coe (option (nterm γ)) (nterm γ) :=
⟨λ x, x.get_or_else (const 0)⟩
theorem eval_none : eval ρ ((none : option (nterm γ)) : nterm γ) = 0 :=
by apply morph.morph0
theorem eval_some {x : nterm γ } : eval ρ (some x : nterm γ) = eval ρ x := rfl

def left : nterm γ → option (nterm γ)
| (add x _) := some x
| _ := none

def right : nterm γ → (nterm γ)
| (add _ x) := x
| x := x

def rest (S : nterm γ) : option (nterm γ) :=
S.term.left.map (scale S.coeff)

def lead (S : nterm γ) : nterm γ :=
scale S.coeff S.term.right

theorem eval_left_right (x : nterm γ) :
  eval ρ x = eval ρ (x.left : nterm γ) + eval ρ x.right :=
begin
  cases x,
  case add : x y { unfold left, unfold right, unfold eval, rw eval_some },
  repeat { unfold left, unfold right, unfold eval, rw [eval_none, zero_add] }
end

theorem eval_rest_lead {S : nterm γ} :
  eval ρ S = eval ρ (S.rest : nterm γ) + eval ρ S.lead :=
begin
  rw [eval_term_coeff, eval_left_right, add_mul],
  congr' 1,
  { unfold rest, cases (term S),
    case add : { dsimp [left, option.map], rw [eval_some, eval_some, eval_scale] },
    repeat { dsimp [left, option.map], rw [eval_none, zero_mul] }},
  { unfold lead, rw eval_scale }
end

def add0 : option (nterm γ) → nterm γ → nterm γ
| (some x) y := add x y
| none y := y

theorem eval_add0 {x : option (nterm γ)} {y : nterm γ} :
  eval ρ (add0 x y) = eval ρ (add (x : nterm γ) y) :=
begin
  cases x,
  { unfold add0, unfold eval,
    rw eval_none, simp },
  { unfold add0, unfold eval, rw eval_some}
end

inductive r : option (nterm γ) → option (nterm γ) → Prop
| none {S : nterm γ} : r none (some S)
| rest {S : nterm γ} : r S.rest (some S)

lemma acc_r_none : @acc (option (nterm γ)) r none :=
begin
  apply acc.intro, intros x h, cases h
end

def g : nterm γ → ℕ
| (add x _) := 1 + g x
| (mul x (const _)) := g x
| _ := 0
def f : option (nterm γ) → ℕ
| (some x) := 1 + g x
| none := 0

theorem g_scale {x : nterm γ} {a : γ} : g (x.scale a) = g x :=
begin
  cases x, case mul : x y {
    cases y, case const : b { refl },
    repeat { refl }},
  repeat { refl }
end

theorem f_none {S : nterm γ} : f (none : option (nterm γ)) < f (some S) :=
by { unfold f, linarith }

theorem foo {x : option (nterm γ)} {a : γ} : f (option.map (scale a) x) = f x :=
by { cases x, {refl}, {simp [f, g_scale]} }

theorem f_rest {S : nterm γ} : f S.rest < f (some S) :=
begin
  show f S.rest < 1 + g S,
  unfold rest,
  cases S,
  case add : { simp [term, left, coeff, f, g, g_scale], linarith },
  case mul : x y { rw foo, cases y,
    case const : { cases x, repeat { simp [term, left, f, g], linarith }},
    repeat { simp [term, left, f], linarith }},
  repeat { simp [term, left, f], linarith }
end

theorem r_wf : @well_founded (option (nterm γ)) r :=
begin
  apply subrelation.wf,
  intros x y h,
  show f x < f y,
  cases h, { apply f_none }, { apply f_rest },
  apply measure_wf
end

def aux (x y : nterm γ) (s1 s2 s3 : option (nterm γ)) : nterm γ :=
if x.term = y.term then
  if x.coeff + y.coeff = 0 then s1
  else (add0 (s1.map (scale (x.coeff + y.coeff)⁻¹)) x.term).scale (x.coeff + y.coeff)
else if lt x.term y.term then
  (add0 (s2.map (scale x.coeff⁻¹)) x.term).scale x.coeff
else
  (add0 (s3.map (scale y.coeff⁻¹)) y.term).scale y.coeff

lemma eval_aux {x y : nterm γ} {s1 s2 s3 : option (nterm γ)}
  ( H0 : x.coeff ≠ 0 ∧ y.coeff ≠ 0)
  ( H1 : eval ρ (s2 : nterm γ) = eval ρ (s1 : nterm γ) + eval ρ y )
  ( H2 : eval ρ (s3 : nterm γ) = eval ρ (s1 : nterm γ) + eval ρ x ) :
  eval ρ (aux x y s1 s2 s3) =  eval ρ (s1 : nterm γ) + eval ρ y + eval ρ x :=
begin
  unfold aux,
  by_cases h1 : x.term = y.term,
  { rw [add_assoc, add_comm (eval ρ y)],
    by_cases h2 : x.coeff + y.coeff = 0,
    { rw [if_pos h1, if_pos h2],
      rw [eval_term_coeff x, h1],
      rw [eval_term_coeff y, ← mul_add, ← morph.morph_add],
      rw [h2, morph.morph0, mul_zero, add_zero] },
    { rw [if_pos h1, if_neg h2, eval_scale, eval_add0],
      unfold eval, rw add_mul, congr' 1,
      { cases s1,
        { dsimp [option.map], rw [eval_none, zero_mul] },
        { dsimp [option.map], rw [eval_some, eval_some, eval_scale],
          rw [mul_assoc, morph.morph_inv, inv_mul_cancel, mul_one],
          intro contrad, apply h2, apply morph.morph_inj _ contrad }},
      { rw [morph.morph_add, mul_add],
        rw [← eval_term_coeff, h1, ← eval_term_coeff] }}},
  { by_cases h2 : x.term < y.term,
    { rw [if_neg h1, if_pos h2, eval_scale, eval_add0],
      unfold eval, rw add_mul, congr' 1,
      { convert H1, cases s2,
        { dsimp [option.map], rw [eval_none, zero_mul] },
        { dsimp [option.map], rw [eval_some, eval_some, eval_scale],
          rw [mul_assoc, morph.morph_inv, inv_mul_cancel, mul_one],
          intro contrad, apply H0.left, apply morph.morph_inj _ contrad }},
      { rw ← eval_term_coeff }},
    { rw [if_neg h1, if_neg h2, eval_scale, eval_add0],
      rw [add_assoc, add_comm (eval ρ y), ← add_assoc],
      unfold eval, rw add_mul, congr' 1,
      { convert H2, cases s3,
        { dsimp [option.map], rw [eval_none, zero_mul] },
        { dsimp [option.map], rw [eval_some, eval_some, eval_scale],
          rw [mul_assoc, morph.morph_inv, inv_mul_cancel, mul_one],
          intro contrad, apply H0.right, apply morph.morph_inj _ contrad }},
      { rw ← eval_term_coeff }}}
end


meta def dec_tac : tactic unit :=
`[apply psigma.lex.left, assumption, done]
<|> `[apply psigma.lex.right, assumption, done]

def norm_add_aux : option (nterm γ) → option (nterm γ) → option (nterm γ)
| (some S) (some T) :=
  have h1 : r S.rest (some S), from r.rest,
  have h2 : r T.rest (some T), from r.rest,
  let s1 := (norm_add_aux S.rest T.rest) in
  let s2 := (norm_add_aux S.rest (some T)) in
  let s3 := (norm_add_aux (some S) T.rest) in
  if S.lead.coeff ≠ 0 ∧ T.lead.coeff ≠ 0 then
    some (aux S.lead T.lead s1 s2 s3)
  else
    add S T --should not happen
| none x := x
| x none := x
using_well_founded {
    rel_tac := λ _ _, `[exact ⟨psigma.lex r (λ _, r), psigma.lex_wf r_wf (λ _, r_wf)⟩],
    dec_tac := dec_tac
 }

def norm_add (x y : nterm γ) : nterm γ :=
norm_add_aux (some x) (some y)

lemma norm_add_aux_def1 {x : option (nterm γ)} :
  norm_add_aux none x = x :=
by cases x; unfold norm_add_aux
lemma norm_add_aux_def2 {x : option (nterm γ)} :
  norm_add_aux x none = x :=
by cases x; unfold norm_add_aux
lemma norm_add_aux_def3 : Π {S T : nterm γ},
  S.lead.coeff ≠ 0 ∧ T.lead.coeff ≠ 0 →
  norm_add_aux (some S) (some T) =
  some (aux S.lead T.lead
    (norm_add_aux S.rest T.rest)
    (norm_add_aux S.rest (some T))
    (norm_add_aux (some S) T.rest) ) :=
begin
  intros S T h0,
  simp [h0, norm_add_aux]
end

theorem eval_norm_add_aux : Π (S T : option (nterm γ)),
  eval ρ (norm_add_aux S T : nterm γ) = eval ρ (S : nterm γ) + eval ρ (T : nterm γ)
| (some S) (some T) :=
  have h1 : r S.rest (some S), from r.rest,
  have h2 : r T.rest (some T), from r.rest,
  let ih1 := eval_norm_add_aux S.rest in
  let ih2 := eval_norm_add_aux (some S) T.rest in
  begin
    by_cases h0 : S.lead.coeff ≠ 0 ∧ T.lead.coeff ≠ 0,
    { rw [eval_some, eval_some, norm_add_aux_def3 h0],
      rw [eval_some, eval_aux h0],
      { rw [ih1, add_assoc (eval ρ ↑(rest S)), ← eval_rest_lead],
        rw [add_comm (eval ρ ↑(rest S)), add_assoc, ← eval_rest_lead],
        apply add_comm },
      { rw [ih1, ih1, add_assoc, ← eval_rest_lead], refl },
      { rw [ih2, ih1, add_comm (eval ρ ↑(rest S)), add_assoc, ← eval_rest_lead],
        apply add_comm }},
    { simp [norm_add_aux, h0], refl }
  end
| none x := by rw [norm_add_aux_def1, eval_none, zero_add]
| x none := by rw [norm_add_aux_def2, eval_none, add_zero]
using_well_founded {
    rel_tac := λ _ _, `[exact ⟨psigma.lex r (λ _, r), psigma.lex_wf r_wf (λ _, r_wf)⟩],
    dec_tac := dec_tac
}

theorem eval_norm_add {x y : nterm γ} :
  eval ρ (norm_add x y) = eval ρ x + eval ρ y :=
by apply eval_norm_add_aux

end nterm

namespace nterm
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

instance coe_atom : has_coe num (nterm γ) := ⟨atom⟩
instance coe_const: has_coe γ (nterm γ) := ⟨const⟩
instance : has_zero (nterm γ) := ⟨const 0⟩
instance : has_one (nterm γ) := ⟨const 1⟩
instance : has_add (nterm γ) := ⟨norm_add⟩
instance : has_mul (nterm γ) := ⟨sorry⟩
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

@[simp] theorem eval_add : eval ρ (x + y) = eval ρ x + eval ρ y := eval_norm_add
@[simp] theorem eval_mul : eval ρ (x * y) = eval ρ x * eval ρ y := sorry
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
