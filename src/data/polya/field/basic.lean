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
by cases x; refl

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

namespace polya.field

structure dict (α : Type) :=
(val : num → α)

class morph (γ : Type) [discrete_field γ] (α : Type) [discrete_field α] :=
(cast       : has_coe γ α)
(morph_zero : ((0 : γ) : α) = 0)
(morph_one  : ((1 : γ) : α) = 1)
(morph_add  : ∀ a b : γ, ((a + b : γ) : α) = a + b)
(morph_neg  : ∀ a : γ, ((-a : γ) : α) = -a)
(morph_mul  : ∀ a b : γ, ((a * b : γ) : α) = a * b)
(morph_inv  : ∀ a : γ, ((a⁻¹ : γ) : α) = a⁻¹)
(morph_inj  : ∀ a : γ, (a : α) = 0 → a = 0)

namespace morph

variables {α : Type} [discrete_field α]
variables {γ : Type} [discrete_field γ]
variables [morph γ α]
variables {a b : γ}

instance has_coe : has_coe γ α := morph.cast γ α

@[simp, squash_cast] theorem morph_zero' : ((0 : γ) : α) = 0 := by apply morph.morph_zero
@[simp, squash_cast] theorem morph_one'  : ((1 : γ) : α) = 1 := by apply morph.morph_one

@[simp, move_cast] theorem morph_add' : ((a + b : γ) : α) = a + b := by apply morph_add
@[simp, move_cast] theorem morph_neg' : ((-a : γ) : α) = -a       := by apply morph_neg
@[simp, move_cast] theorem morph_mul' : ((a * b : γ) : α) = a * b := by apply morph_mul
@[simp, move_cast] theorem morph_inv' : ((a⁻¹ : γ) : α) = a⁻¹     := by apply morph_inv

@[simp, move_cast] theorem morph_sub : ((a - b : γ) : α) = a - b :=
by rw [sub_eq_add_neg, morph.morph_add, morph.morph_neg, ← sub_eq_add_neg]

@[simp, elim_cast] theorem morph_inj' : (a : α) = b ↔ a = b :=
begin
  apply iff.intro,
  { intro h, apply eq_of_sub_eq_zero,
    apply morph.morph_inj (a - b),
    rw morph.morph_sub,
    apply sub_eq_zero_of_eq,
    apply h },
  { intro h, subst h }
end

@[simp, move_cast] theorem morph_div : ((a / b : γ) : α) = a / b :=
by rw [division_def, morph.morph_mul, morph.morph_inv, ← division_def]

@[simp, move_cast] theorem morph_pow_nat {n : ℕ} : ((a ^ n : γ) : α) = a ^ n :=
begin
  induction n with _ ih,
  { rw [pow_zero, pow_zero, morph.morph_one] },
  { by_cases ha : a = 0,
    { rw [ha, morph.morph_zero, zero_pow, zero_pow],
      { apply morph.morph_zero },
      { apply nat.succ_pos },
      { apply nat.succ_pos }},
    { rw [pow_succ, morph.morph_mul, ih, ← pow_succ] }}
end

@[simp, move_cast] theorem morph_pow {n : ℤ} : ((a ^ n : γ) : α) = a ^ n :=
begin
  cases n,
  { rw [int.of_nat_eq_coe, fpow_of_nat, fpow_of_nat],
    apply morph_pow_nat },
  { rw [int.neg_succ_of_nat_coe, fpow_neg, fpow_neg],
    rw [morph_div, morph.morph_one],
    rw [fpow_of_nat, fpow_of_nat],
    rw morph_pow_nat }
end

@[simp, squash_cast] theorem morph_nat {n : ℕ} : ((n : γ) : α) = (n : α) :=
by { induction n with n ih, { simp }, { simp [ih] } }

@[simp, squash_cast] theorem morph_num {n : num} : ((n : γ) : α) = (n : α) :=
by rw [← num.cast_to_nat, ← num.cast_to_nat, morph_nat, num.cast_to_nat, num.cast_to_nat]

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

def eval (ρ : dict α) : nterm γ → α
| (atom i)  := ρ.val i
| (const c) := (c : α)
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x n) := eval x ^ (n : ℤ)

meta def to_str [has_to_string γ] : (nterm γ) → string
| (atom i)  := "#" ++ to_string (i : ℕ)
| (const c) := to_string c
| (add x y) := "(" ++ to_str x ++ " + " ++ to_str y ++ ")"
| (mul x y) := "(" ++ to_str x ++ " * " ++ to_str y ++ ")"
| (pow x n) := to_str x ++ " ^ " ++ to_string (n : ℤ)

meta instance [has_to_string γ] : has_to_string (nterm γ) := ⟨to_str⟩
meta instance [has_to_string γ] : has_to_tactic_format (nterm γ) := ⟨λ x, return (to_str x : format)⟩

def scale (a : γ) (x : nterm γ) : nterm γ :=
if a = 0 then
  const 0
else
  match x with
  | (mul x (const b)) := mul x (const (b * a))
  | x := mul x (const a) --should not happen
  end

def coeff : nterm γ → γ
| (mul x (const a)) := a
| x := 1 --should not happen

def term : nterm γ → nterm γ
| (mul x (const a)) := x
| x := x --should not happen

@[simp] theorem eval_scale {a : γ} {x : nterm γ} :
  eval ρ (x.scale a) = eval ρ x * a :=
begin
  unfold scale,
  by_cases h1 : a = 0,
  { rw [if_pos h1, h1], simp [eval] },
  { rw [if_neg h1],
    cases x, case mul : x y { 
      cases y, case const : b {
        unfold scale, unfold eval,
        rw [mul_assoc, morph.morph_mul'] },
      repeat { refl }},
    repeat { refl }}
end

theorem eval_term_coeff (x : nterm γ) : eval ρ x = eval ρ x.term * x.coeff :=
begin
  cases x,
  case mul : x y { 
    cases y,
    case const : { unfold coeff, unfold term, refl },
    repeat { unfold coeff, unfold term, rw [morph.morph_one, mul_one] },
  },
  repeat { unfold coeff, unfold term, rw [morph.morph_one, mul_one] }
end

--theorem eval_scale_add {a b : γ} {x : nterm γ} : eval ρ (x.scale (a + b)) = eval ρ (x.scale a) + eval ρ (x.scale b) :=
--by rw [eval_scale, eval_scale, eval_scale, morph.morph_add, mul_add]

--theorem eval_scale_zero {x : nterm γ} :
--  eval ρ (x.scale 0) = 0 :=
--by rw [eval_scale, morph.morph_zero, mul_zero]

--theorem eval_scale_one {x : nterm γ} : eval ρ (x.scale 1) = eval ρ x :=
--by rw [eval_scale, morph.morph_one, mul_one]
--theorem eval_scale_neg {a : γ} {x : nterm γ} : eval ρ (x.scale (-a)) = - eval ρ (x.scale a) :=
--by rw [eval_scale, eval_scale, morph.morph_neg, neg_mul_eq_mul_neg]

--theorem scale_comp {a b : γ} : scale a ∘ scale b = scale (a * b) :=
--begin
--  funext x, cases x,
--  case mul : x y {
--    cases y, case const : a { dsimp [function.comp, scale], rw mul_assoc, refl },
--    repeat { dsimp [function.comp, scale], refl }},
--  repeat { dsimp [function.comp, scale], refl }
--end

def exp : nterm γ → znum
| (pow _ n) := n
| _ := 1

def mem : nterm γ → nterm γ
| (pow x _) := x
| x := x

theorem eval_mem_exp (x : nterm γ) : eval ρ x = eval ρ (mem x) ^ (exp x : ℤ) :=
begin
  cases x,
  case pow : x n { dsimp [mem, exp, eval], refl },
  repeat { dsimp [mem, exp, eval], rw fpow_one }
end

--theorem eval_mem_zero {x : nterm γ} : eval ρ x = 0 → eval ρ (mem x) = 0 :=
--begin
--  intro h1, cases x,
--  case pow : x n { unfold mem, by_contradiction h2, exact fpow_ne_zero_of_ne_zero h2 _ h1 },
--  repeat { exact h1 },
--end

def pow_mul (n : znum) (x : nterm γ) : nterm γ :=
if n = 0 then
  const 1
else if x.exp * n = 1 then
  x.mem
else
  pow x.mem (x.exp * n)

def pow_div (n : znum) (x : nterm γ) : nterm γ :=
if n = x.exp then
  x.mem
else
  pow x.mem (x.exp / n)

@[simp] theorem eval_pow_mul {n : znum} {x : nterm γ} : eval ρ (pow_mul n x) = eval ρ x ^ (n : ℤ) :=
begin
  unfold pow_mul,
  by_cases h1 : n = 0,
  { simp [eval, h1] },
  { by_cases h2 : x.exp * n = 1,
    { rw [if_neg h1, if_pos h2, eval_mem_exp x],
      rw [← fpow_mul, ← znum.cast_mul, h2],
      simp },
    { rw [if_neg h1, if_neg h2], unfold eval,
      rw [znum.cast_mul, fpow_mul, ← eval_mem_exp]}}
end

@[simp] theorem eval_pow_div {n : znum} {x : nterm γ} : n ∣ x.exp → eval ρ (pow_div n x) ^ (n : ℤ) = eval ρ x :=
begin
  intro h1, cases h1 with d h1,
  unfold pow_div,
  by_cases h2 : n = exp x,
  { rw [if_pos h2, h2, ← eval_mem_exp] },
  { by_cases h3 : n = 0,
    { apply absurd _ h2, have : exp x = 0, { rw h1, simp [h3] }, rw [h3, this] },
    { rw [if_neg h2, h1], unfold eval,
      rw [znum.div_to_int, znum.cast_mul, int.mul_div_cancel_left],
      { rw [← fpow_mul, int.mul_comm, ← znum.cast_mul, ← h1, ← eval_mem_exp] },
      { rw [← znum.cast_zero], exact_mod_cast h3 }}}
end

def nonzero (ρ : dict α) (ts : list (nterm γ)) : Prop := ∀ t ∈ ts, nterm.eval ρ t ≠ 0

theorem nonzero_union {xs ys : list (nterm γ)} : nonzero ρ (xs ∪ ys) ↔ nonzero ρ xs ∧ nonzero ρ ys :=
begin
  apply iff.intro,
  { intro h1, split; { intros _ h2, apply h1, simp [h2] }},
  { intros h1 t ht, cases h1 with h1 h2, rw list.mem_union at ht, cases ht,
    {apply h1, apply ht}, {apply h2, apply ht}}
end

theorem nonzero_subset {xs ys : list (nterm γ)} : xs ⊆ ys → nonzero ρ ys → nonzero ρ xs :=
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

end nterm

--TODO: at some point, pform and sform should move here

end polya.field