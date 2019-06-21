import data.real.basic data.num.lemmas

section

local attribute [semireducible] reflected

meta instance rat.reflect : has_reflect ℚ
| ⟨n, d, _, _⟩ := `(rat.mk_nat %%(reflect n) %%(reflect d))

meta instance rat.to_pexpr : has_to_pexpr ℚ :=
⟨λ ⟨n, d, _, _⟩, ``(rat.mk_nat %%(reflect n) %%(reflect d))⟩

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

attribute [squash_cast] morph0
attribute [squash_cast] morph1

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
inductive nterm {γ : Type} [const_space γ] : Type
| atom  : num → nterm
| const : γ → nterm
| add   : nterm → nterm → nterm
| mul   : nterm → nterm → nterm
| pow   : nterm → znum → nterm

namespace nterm
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

instance : inhabited (@nterm γ _) := ⟨const 0⟩

def ble :
  @nterm γ _ → @nterm γ _ → bool
| (const a) (const b) := a ≤ b
| (const _) _         := tt
| _         (const _) := ff
| (atom i)  (atom j)  := i ≤ j
| (atom _)  _         := tt
| _         (atom _)  := ff
| (add x y) (add z w) := if x = z then ble y w else ble x z
| (add _ _) _         := tt
| _         (add _ _) := ff
| (mul x y) (mul z w) := if x = z then ble y w else ble x z
| (mul _ _) _         := tt
| _         (mul _ _) := ff
| (pow x n) (pow y m) := if x = y then n ≤ m else ble x y

def le : @nterm γ _ → @nterm γ _ → Prop := λ x y, ble x y
def lt : @nterm γ _ → @nterm γ _ → Prop := λ x y, ble x y ∧ x ≠ y
instance : has_le (@nterm γ _) := ⟨le⟩
instance : has_lt (@nterm γ _) := ⟨lt⟩
instance dec_le : decidable_rel (@le γ _) := by dunfold le; apply_instance
instance dec_lt : decidable_rel (@lt γ _) := by dunfold lt; apply_instance

--instance trans_le : is_trans _ (@le γ _) := by sorry
--instance antisymm_le : is_antisymm _ (@le γ _) := by sorry
--instance is_total : is_total _ (@le γ _) := by sorry

instance coe_atom : has_coe num (@nterm γ _) := ⟨atom⟩
instance coe_const: has_coe γ (@nterm γ _) := ⟨const⟩
instance : has_zero (@nterm γ _) := ⟨const 0⟩
instance : has_one (@nterm γ _) := ⟨const 1⟩
instance : has_add (@nterm γ _) := ⟨add⟩
instance : has_mul (@nterm γ _) := ⟨mul⟩
instance : has_pow (@nterm γ _) znum := ⟨pow⟩
instance pow_nat : has_pow (@nterm γ _) ℕ := ⟨λ x n, x.pow (n : znum)⟩ --test
instance pow_int : has_pow (@nterm γ _) ℤ := ⟨λ x n, x.pow (n : znum)⟩ --test

def neg (x : @nterm γ _) : @nterm γ _ := x * (-1 : γ)
instance : has_neg (@nterm γ _) := ⟨neg⟩
def sub (x y : @nterm γ _) : @nterm γ _ := x + (-y)
instance : has_sub (@nterm γ _) := ⟨sub⟩
def inv (x : @nterm γ _) : @nterm γ _ := pow x (-1)
instance : has_inv (@nterm γ _) := ⟨inv⟩
def div (x y : @nterm γ _) : @nterm γ _ := x * y⁻¹
instance : has_div (@nterm γ _) := ⟨div⟩

def eval (ρ : dict α) : @nterm γ _ → α
| (atom i)  := ρ.val i
| (const c) := ↑c
| (add x y) := eval x + eval y
| (mul x y) := eval x * eval y
| (pow x n) := eval x ^ (n : ℤ)

section
variables {x y : @nterm γ _} {i : num} {n : znum} {c : γ}
@[simp] theorem eval_zero : (0 : @nterm γ _).eval ρ = 0 := by apply morph.morph0
@[simp] theorem eval_one : (1 : @nterm γ _).eval ρ = 1 := by apply morph.morph1
@[simp] theorem eval_atom : (i : @nterm γ _).eval ρ = ρ.val i := rfl
@[simp] theorem eval_const : (c : @nterm γ _).eval ρ = c := rfl
@[simp] theorem eval_add : (x + y).eval ρ = x.eval ρ + y.eval ρ := rfl
@[simp] theorem eval_mul : (x * y).eval ρ = x.eval ρ * y.eval ρ := rfl
@[simp] theorem eval_pow : (x ^ n).eval ρ = x.eval ρ ^ (n : ℤ) := rfl
@[simp] theorem eval_pow_zero : (x ^ (0 : znum)).eval ρ = 1 := by simp

@[simp] theorem eval_neg : (-x).eval ρ = - x.eval ρ :=
calc
eval ρ (-x)
    = eval ρ (neg x) : rfl
... = - eval ρ x     : by simp [neg, morph.morph_neg, morph.morph1]

@[simp] theorem eval_sub : (x - y).eval ρ = x.eval ρ - y.eval ρ :=
calc
eval ρ (x - y)
    = eval ρ (sub x y)    : rfl
... = eval ρ x - eval ρ y : by simp [sub, sub_eq_add_neg]

@[simp] theorem eval_inv : (x⁻¹).eval ρ = (x.eval ρ)⁻¹ :=
calc
eval ρ (x⁻¹)
    = eval ρ (inv x)        : rfl
... = (eval ρ x) ^ (-1 : ℤ) : by simp [inv, eval]
... = (eval ρ x)⁻¹          : fpow_inv _

@[simp] theorem eval_div : (x / y).eval ρ = x.eval ρ / y.eval ρ :=
calc
eval ρ (x / y)
    = eval ρ (div x y)    : rfl
... = eval ρ x / eval ρ y : by simp [div, div_eq_mul_inv]

end

meta def to_str [has_to_string γ] : (@nterm γ _) → string
| (atom i)  := "#" ++ to_string (i : ℕ)
| (const c) := to_string c
| (add x y) := "(" ++ to_str x ++ " + " ++ to_str y ++ ")"
| (mul x y) := "(" ++ to_str x ++ " * " ++ to_str y ++ ")"
| (pow x n) := to_str x ++ " ^ " ++ to_string (n : ℤ)

meta instance [has_to_string γ] : has_to_string (@nterm γ _) := ⟨to_str⟩
meta instance [has_to_string γ] : has_to_tactic_format (@nterm γ _) := ⟨λ x, return (to_str x : format)⟩

def sum : list (@nterm γ _) → @nterm γ _
| []      := (0 : @nterm γ _)
| [x]     := x
| (x::xs) := sum xs + x

def prod : list (@nterm γ _) → @nterm γ _
| []      := (1 : @nterm γ _)
| [x]     := x
| (x::xs) := prod xs * x

theorem eval_sum (xs : list (@nterm γ _)) :
  (sum xs).eval ρ = list.sum (xs.map (nterm.eval ρ)) :=
begin
  induction xs with x0 xs ih,
  { simp [sum] },
  { cases xs with x1 xs,
    { simp [sum] },
    { unfold sum, rw [list.map_cons, list.sum_cons, eval_add, ih, add_comm] }}
end

theorem eval_prod (xs : list (@nterm γ _)) :
  (prod xs).eval ρ = list.prod (xs.map (nterm.eval ρ)) :=
begin
  induction xs with x0 xs ih,
  { simp [prod] },
  { cases xs with x1 xs,
    { simp [prod] },
    { unfold prod, rw [list.map_cons, list.prod_cons, eval_mul, ih, mul_comm] }}
end

def nonzero (ρ : dict α) (ts : list (@nterm γ _)) : Prop :=
∀ t ∈ ts, nterm.eval ρ t ≠ 0

theorem nonzero_union {xs ys : list (@nterm γ _)} :
nonzero ρ (xs ∪ ys) ↔ nonzero ρ xs ∧ nonzero ρ ys :=
begin
  apply iff.intro,
  { intro h1, split; { intros _ h2, apply h1, simp [h2] }},
  { intros h1 t ht, cases h1 with h1 h2, rw list.mem_union at ht, cases ht,
    {apply h1, apply ht}, {apply h2, apply ht}}
end

theorem nonzero_subset {xs ys : list (@nterm γ _)} :
  xs ⊆ ys → nonzero ρ ys → nonzero ρ xs :=
begin
  intros h1 h2, intros x hx,
  apply h2, apply h1, apply hx
end

theorem nonzero_iff_zero_not_mem (ts : list (@nterm γ _)) :
nonzero ρ ts ↔ (0 : α) ∉ ts.map (nterm.eval ρ) :=
begin
  apply iff.intro,
  { intro h, simpa using h },
  { intro h, simp at h, apply h }
end

end nterm

end field

