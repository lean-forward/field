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
(le : has_le γ)
(dec_le : decidable_rel le.le)

namespace const_space
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]

instance : discrete_field γ := const_space.df γ
instance : has_le γ := const_space.le γ
instance : decidable_rel (@has_le.le γ _) := const_space.dec_le γ

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

instance : inhabited (nterm γ) := ⟨const 0⟩

def ble :
  nterm γ → nterm γ → bool
| (const a) (const b) := a ≤ b
| (const _) _         := tt
| _         (const _) := ff
| (atom i)  (atom j)  := i ≤ j
| (atom _)  _         := tt
| _         (atom _)  := ff
| (add x y) (add z w) := if y = w then ble x z else ble y w
| (add _ _) _         := tt
| _         (add _ _) := ff
| (mul x y) (mul z w) := if y = w then ble x z else ble y w
| (mul _ _) _         := tt
| _         (mul _ _) := ff
| (pow x n) (pow y m) := if x = y then n ≤ m else ble x y

def le : nterm γ → nterm γ → Prop := λ x y, ble x y
def lt : nterm γ → nterm γ → Prop := λ x y, ble x y ∧ x ≠ y
instance : has_le (nterm γ) := ⟨le⟩
instance : has_lt (nterm γ) := ⟨lt⟩
instance dec_le : decidable_rel (@le γ _) := by dunfold le; apply_instance
instance dec_lt : decidable_rel (@lt γ _) := by dunfold lt; apply_instance

--instance trans_le : is_trans _ (@le γ _) := by sorry
--instance antisymm_le : is_antisymm _ (@le γ _) := by sorry
--instance is_total : is_total _ (@le γ _) := by sorry

instance coe_atom : has_coe num (nterm γ) := ⟨atom⟩
instance coe_const: has_coe γ (nterm γ) := ⟨const⟩
instance : has_zero (nterm γ) := ⟨const 0⟩
instance : has_one (nterm γ) := ⟨const 1⟩
instance : has_add (nterm γ) := ⟨add⟩
instance : has_mul (nterm γ) := ⟨mul⟩
instance : has_pow (nterm γ) znum := ⟨pow⟩
instance pow_nat : has_pow (nterm γ) ℕ := ⟨λ x n, x.pow (n : znum)⟩ --test
instance pow_int : has_pow (nterm γ) ℤ := ⟨λ x n, x.pow (n : znum)⟩ --test

def neg (x : nterm γ) : nterm γ := mul x (const (-1))
def sub (x y : nterm γ) : nterm γ := add x (neg y)
def inv (x : nterm γ) : nterm γ := pow x (-1)
def div (x y : nterm γ) : nterm γ := mul x (inv y)

instance : has_neg (nterm γ) := ⟨neg⟩
instance : has_sub (nterm γ) := ⟨sub⟩
instance : has_inv (nterm γ) := ⟨inv⟩
instance : has_div (nterm γ) := ⟨div⟩

def eval (ρ : dict α) : nterm γ → α
| (atom i)  := ρ.val i
| (const c) := ↑c
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x 0) := if eval x = 0 then 0 else 1
| (pow x n) := eval x ^ (n : ℤ)

section
variables {x y : nterm γ} {i : num} {n : znum} {c : γ}
@[simp] theorem eval_zero : (0 : nterm γ).eval ρ = 0 := by apply morph.morph0
@[simp] theorem eval_one : (1 : nterm γ).eval ρ = 1 := by apply morph.morph1
@[simp] theorem eval_atom : (i : nterm γ).eval ρ = ρ.val i := rfl
@[simp] theorem eval_const : (c : nterm γ).eval ρ = c := rfl
@[simp] theorem eval_add : (x + y).eval ρ = x.eval ρ + y.eval ρ := rfl
@[simp] theorem eval_mul : (x * y).eval ρ = x.eval ρ * y.eval ρ := rfl
@[simp] theorem eval_pow : n ≠ 0 → (x ^ n).eval ρ = x.eval ρ ^ (n : ℤ) :=
begin
  intro h,
  suffices : eval ρ (pow x n) = eval ρ x ^ (n : ℤ),
  { rw ← this, refl },
  cases n,
  { contradiction },
  { refl }, { refl },
end

@[simp] theorem eval_neg : (-x).eval ρ = - x.eval ρ :=
begin
  suffices : eval ρ (neg x) = - x.eval ρ,
  { rw ← this, refl },
  unfold neg, unfold eval,
  rw [morph.morph_neg, morph.morph1, mul_neg_one]
end
@[simp] theorem eval_sub : (x - y).eval ρ = x.eval ρ - y.eval ρ := sorry
@[simp] theorem eval_inv : (x⁻¹).eval ρ = (x.eval ρ)⁻¹ := sorry
@[simp] theorem eval_div : (x / y).eval ρ = x.eval ρ / y.eval ρ := sorry

end

meta def to_str [has_to_string γ] : (nterm γ) → string
| (atom i)  := "#" ++ to_string (i : ℕ)
| (const c) := to_string c
| (add x y) := "(" ++ to_str x ++ " + " ++ to_str y ++ ")"
| (mul x y) := "(" ++ to_str x ++ " * " ++ to_str y ++ ")"
| (pow x n) := to_str x ++ " ^ " ++ to_string (n : ℤ)

meta instance [has_to_string γ] : has_to_string (nterm γ) := ⟨to_str⟩
meta instance [has_to_string γ] : has_to_tactic_format (nterm γ) := ⟨λ x, return (to_str x : format)⟩

def sum : list (nterm γ) → nterm γ
| []      := (0 : nterm γ)
| [x]     := x
| (x::xs) := sum xs + x

def prod : list (nterm γ) → nterm γ
| []      := (1 : nterm γ) 
| [x]     := x
| (x::xs) := prod xs * x

theorem eval_sum (xs : list (nterm γ)) :
  (sum xs).eval ρ = list.sum (xs.map (nterm.eval ρ)) :=
begin
  induction xs with x0 xs ih,
  { simp [sum] },
  { cases xs with x1 xs,
    { simp [sum] },
    { unfold sum, rw [list.map_cons, list.sum_cons, eval_add, ih, add_comm] }}
end

theorem eval_prod (xs : list (nterm γ)) :
  (prod xs).eval ρ = list.prod (xs.map (nterm.eval ρ)) :=
begin
  induction xs with x0 xs ih,
  { simp [prod] },
  { cases xs with x1 xs,
    { simp [prod] },
    { unfold prod, rw [list.map_cons, list.prod_cons, eval_mul, ih, mul_comm] }}
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

def scale (a : γ) : nterm γ → nterm γ
| (mul x (const b)) := mul x (const (a * b))
| x := mul x (const a)

theorem eval_scale {a : γ} {x : nterm γ} :
  eval ρ (x.scale a) = eval ρ x * a :=
by sorry
theorem eval_scale_add {a b : γ} {x : nterm γ} :
  eval ρ (x.scale (a + b)) = eval ρ (x.scale a) + eval ρ (x.scale b) :=
by sorry
theorem eval_scale_zero {x : nterm γ} :
  eval ρ (x.scale 0) = 0 :=
by sorry
theorem eval_scale_neg {a : γ} {x : nterm γ} :
  eval ρ (x.scale (-a)) = - eval ρ (x.scale a) :=
by sorry

def coeff : nterm γ → γ
| (mul x (const a)) := a
| x := 1 
def term : nterm γ → nterm γ
| (mul x (const a)) := x
| x := x

theorem eval_term_scale_coeff (x : nterm γ) :
  eval ρ x = eval ρ (scale x.coeff x.term) :=
begin
  sorry
end

def add0 : option (nterm γ) → nterm γ → nterm γ
| (some x) y := add x y
| none y := y

inductive r : option (nterm γ) → option (nterm γ) → Prop
| none {x : nterm γ} : r none x
| add {x y : nterm γ} : r x (add x y)

lemma acc_r_none : @acc (option (nterm γ)) r none :=
begin
  apply acc.intro, intros x h, cases h
end

theorem r_wf : @well_founded (option (nterm γ)) r :=
begin
  apply well_founded.intro,
  intro x, cases x with x,
  { apply acc_r_none },
  { induction x,
    case add : x y ihx ihy {
      apply acc.intro, intros z h,
      cases h,
      { apply acc_r_none },
      { apply ihx }},
    repeat {
      apply acc.intro,
      intros y h, cases h,
      apply acc_r_none }}
end

def sizeof' : option (nterm γ) → ℕ
| none := 0
| (some (add x _)) := 1 + sizeof' (some x)
| (some x) := 1

instance : has_coe (option (nterm γ)) (nterm γ) :=
⟨λ x, x.get_or_else (const 0)⟩

theorem eval_none : eval ρ ((none : option (nterm γ)) : nterm γ) = 0 :=
by apply morph.morph0
theorem eval_some {x : nterm γ } : eval ρ (some x : nterm γ) = eval ρ x := rfl

theorem eval_add0 {x : option (nterm γ)} {y : nterm γ} :
  eval ρ (add0 x y) = eval ρ (add (x : nterm γ) y) :=
begin
  cases x,
  { unfold add0, unfold eval,
    rw eval_none, simp },
  { unfold add0, unfold eval, rw eval_some}
end

def split_add : Π (S : nterm γ),
  { x : option (nterm γ) × nterm γ // r x.fst (some S) }
| (add x y) := { val := (some x, y), property := r.add }
| x := { val := (none, x), property := r.none }

theorem eval_split_add (S : nterm γ) :
  eval ρ S = eval ρ ((split_add S).val.fst : nterm γ) + eval ρ (split_add S).val.snd :=
begin
  sorry
end
  
def aux (x y : nterm γ) (s1 s2 s3 : option (nterm γ)) : nterm γ :=
  if x.term = y.term then
    if x.coeff + y.coeff = 0 then s1
    else add0 s1 (x.term.scale (x.coeff + y.coeff))
  else if lt x.term y.term then
    add0 s2 x
  else
    add0 s3 y

lemma foo {x y : nterm γ} {s1 s2 s3 : option (nterm γ)}
  ( H1 : eval ρ (s2 : nterm γ) = eval ρ (s1 : nterm γ) + eval ρ y )
  ( H2 : eval ρ (s3 : nterm γ) = eval ρ (s1 : nterm γ) + eval ρ x ) :
  eval ρ (aux x y s1 s2 s3) =  eval ρ (s1 : nterm γ) + eval ρ y + eval ρ x :=
begin
  unfold aux,
  by_cases h1 : x.term = y.term,
  { by_cases h2 : x.coeff + y.coeff = 0,
    { rw [if_pos h1, if_pos h2],
      rw [eval_term_scale_coeff x, eval_term_scale_coeff y, h1],
      rw [eq_neg_of_add_eq_zero h2, eval_scale_neg],
      simp },
    { rw [if_pos h1, if_neg h2],
      rw [add_assoc, eval_add0], unfold eval, congr,
      rw [add_comm, eval_scale_add],
      rw [← eval_term_scale_coeff, h1, ← eval_term_scale_coeff],
      refl }},
  { by_cases h2 : x.term < y.term,
    { rw [if_neg h1, if_pos h2],
      rw [eval_add0], unfold eval, rw H1 },
    { rw [if_neg h1, if_neg h2],
      rw [eval_add0], unfold eval, rw H2,
      rw [add_assoc, add_assoc], congr' 1,
      apply add_comm }}
end

theorem r_split_add {S : nterm γ} :
  r (S.split_add.val.fst) (some S) :=
begin
  cases S,
  case add : { apply r.add },
  repeat { apply r.none }
end

def norm_sum_aux : option (nterm γ) → option (nterm γ) → option (nterm γ)
| (some S) (some T) :=
  have h1 : r S.split_add.val.fst (some S), from r_split_add,
  have h2 : r T.split_add.val.fst (some T), from r_split_add,
  some (aux S.split_add.val.snd T.split_add.val.snd
    (norm_sum_aux S.split_add.val.fst T.split_add.val.fst)
    (norm_sum_aux S.split_add.val.fst (some T))
    (norm_sum_aux (some S) T.split_add.val.fst) ) 
| none x := x
| x none := x
using_well_founded {
    rel_tac := λ _ _, `[exact ⟨psigma.lex r (λ _, r), psigma.lex_wf r_wf (λ _, r_wf)⟩],
    dec_tac := `[apply psigma.lex.left, assumption, done] <|> `[apply psigma.lex.right, assumption, done]
 }

def norm_sum (x y : nterm γ) : nterm γ :=
norm_sum_aux (some x) (some y)

lemma norm_sum_aux_def1 {x : option (nterm γ)} :
  norm_sum_aux none x = x :=
by cases x; unfold norm_sum_aux
lemma norm_sum_aux_def2 {x : option (nterm γ)} :
  norm_sum_aux x none = x :=
by cases x; unfold norm_sum_aux

#check @norm_sum_aux._main._pack
lemma norm_sum_aux_def3 : Π {S T : nterm γ},
  norm_sum_aux (some S) (some T) =
  some (aux S.split_add.val.snd T.split_add.val.snd
    (norm_sum_aux S.split_add.val.fst T.split_add.val.fst)
    (norm_sum_aux S.split_add.val.fst (some T))
    (norm_sum_aux (some S) T.split_add.val.fst) ) :=
by { intros, unfold norm_sum_aux }

theorem foobar : Π (S T : option (nterm γ)),
  eval ρ (norm_sum_aux S T : nterm γ) = eval ρ (S : nterm γ) + eval ρ (T : nterm γ)
| (some S) (some T) :=
  have h1 : r S.split_add.val.fst (some S), from r_split_add,
  have h2 : r T.split_add.val.fst (some T), from r_split_add,
  let foobar1 := foobar S.split_add.val.fst in
  let foobar2 := foobar (some S) T.split_add.val.fst in
  begin
    rw [eval_some, eval_some, norm_sum_aux_def3],
    apply eq.trans,
    { apply foo,
      { rw [foobar1, eval_some, foobar1],
        rw [add_assoc, ← eval_split_add],
        refl },
      { rw [foobar2, eval_some, foobar1],
        rw [add_assoc, add_comm _ (eval _ (prod.snd _)), ← add_assoc], 
        rw [← eval_split_add], refl }},
    { rw [foobar1, add_assoc, add_assoc, ← add_assoc _ (eval _ (prod.snd _)), ← eval_split_add],
      rw [add_comm (eval _ T) _, ← add_assoc, ← eval_split_add],
      refl }
  end
| none x := by rw [norm_sum_aux_def1, eval_none, zero_add]
| x none := by rw [norm_sum_aux_def2, eval_none, add_zero]
using_well_founded {
    rel_tac := λ _ _, `[exact ⟨psigma.lex r (λ _, r), psigma.lex_wf r_wf (λ _, r_wf)⟩],
    dec_tac := `[apply psigma.lex.left, assumption, done] <|> `[apply psigma.lex.right, assumption, done]
}

end nterm

end field
