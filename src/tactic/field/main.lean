import data.nterm

namespace list

def pall {α : Type*} (l : list α) (f : α → Prop) : Prop :=
l.foldr (λ a r, f a ∧ r) true

theorem pall_iff_forall_prop :
  ∀ {α : Type*} {p : α → Prop} [_inst_1 : decidable_pred p] {l : list α},
  list.pall l p ↔ ∀ (a : α), a ∈ l → p a :=
begin
  intros,
  apply iff.trans, swap,
  { exact @list.all_iff_forall_prop _ _ _inst_1 _ },
  { unfold pall, induction l with x xs ih,
    { simp },
    { simp [ih] }}
end

open field tactic

meta def expr_reflect (type : expr) : list expr → tactic expr
| [] := to_expr ``([] : list %%type)
| (h::t) := do e ← expr_reflect t, to_expr ``(list.cons (%%h : %%type) %%e)

def to_dict {α} [inhabited α] (l : list α) : dict α :=
⟨λ i, list.func.get i l.reverse⟩

end list

--namespace finmap
--open field
--
--def to_dict {α} [discrete_field α] (m : finmap (λ _ : num, α)) : dict α :=
--⟨λ i, match finmap.lookup i m with (some x) := x | _ := 0 end⟩
--
--end finmap

namespace field

@[derive decidable_eq, derive has_reflect]
inductive eterm (γ : Type) [const_space γ] : Type
| zero  {} : eterm
| one   {} : eterm
| const {} : γ → eterm
| atom  {} : num → eterm
| add   {} : eterm → eterm → eterm
| sub   {} : eterm → eterm → eterm
| mul   {} : eterm → eterm → eterm
| div   {} : eterm → eterm → eterm
| neg   {} : eterm → eterm
| inv   {} : eterm → eterm
| pow_nat {} : eterm → ℕ → eterm
| pow_int {} : eterm → ℤ → eterm

namespace eterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def eval (ρ : dict α) : eterm γ → α
| zero      := 0
| one       := 1
| (const r) := ↑r
| (atom i)  := ρ.val i
| (add x y) := eval x + eval y
| (sub x y) := eval x - eval y
| (mul x y) := eval x * eval y
| (div x y) := (eval x) / (eval y)
| (neg x)   := - eval x
| (inv x)   := (eval x)⁻¹
| (pow_nat x n) := eval x ^ n
| (pow_int x n) := eval x ^ n

def to_nterm : eterm γ → nterm γ
| zero      := 0
| one       := 1
| (const c) := c
| (atom i)  := i
| (add x y) := to_nterm x + to_nterm y
| (sub x y) := to_nterm x - to_nterm y
| (mul x y) := to_nterm x * to_nterm y
| (div x y) := to_nterm x / to_nterm y
| (neg x)   := - to_nterm x
| (inv x)   := (to_nterm x)⁻¹
| (pow_nat x n) := to_nterm x ^ n
| (pow_int x n) := to_nterm x ^ n

theorem correctness {x : eterm γ} :
  nterm.eval ρ (to_nterm x) = eval ρ x :=
begin
  induction x with
    c           --const
    i           --atom
    x y ihx ihy --add
    x y ihx ihy --sub
    x y ihx ihy --mul
    x y ihx ihy --div
    x ihx       --neg
    x ihx       --inv
    x n ihx     --pow_nat
    x n ihx,    --pow_int
  repeat {unfold to_nterm, unfold eval},
  repeat { simp },
  repeat { simp [ihx] },
  repeat { simp [ihx, ihy] }
end

end eterm

section norm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def norm (x : eterm γ) : nterm γ :=
x.to_nterm

def norm_hyps (x : eterm γ) : list (nterm γ) :=
sorry

theorem correctness {x : eterm γ} {ρ : dict α} :
  (∀ t ∈ norm_hyps x, nterm.eval ρ t ≠ 0) →
  eterm.eval ρ x = nterm.eval ρ (norm x) :=
begin
  sorry
end

end norm

end field

namespace tactic
open native tactic

namespace field
open field field.eterm

meta structure cache_ty :=
( new_atom : num )
( atoms    : rb_map expr num )
( dict     : rb_map num expr )

meta instance : has_emptyc cache_ty :=
⟨⟨0, rb_map.mk _ _, rb_map.mk _ _⟩⟩

meta def state_dict : Type → Type := state_t cache_ty tactic

namespace state_dict
meta instance : monad state_dict := state_t.monad
meta instance : monad_state cache_ty state_dict := state_t.monad_state
meta instance : alternative state_dict := state_t.alternative
meta instance {α} : has_coe (tactic α) (state_dict α) := ⟨state_t.lift⟩
end state_dict

meta def get_atom (e : expr) : state_dict num :=
get >>= λ s,
match s.atoms.find e with
| (some i) := return i
| none     := do
    let i := s.new_atom,
    put ⟨i + 1, s.atoms.insert e i, s.dict.insert i e⟩,
    return i
end

meta def cache_ty.dict_expr (s : cache_ty) : tactic expr :=
do
    e ← s.dict.values.expr_reflect `(ℝ), --TODO: for any α
    mk_app `list.to_dict [e]

@[reducible]
def γ := ℚ

instance : const_space γ :=
{ df := by apply_instance,
  lt := (<),
  dec := by apply_instance
}

meta def eterm_of_expr : expr → state_dict (eterm γ) | e :=
match e with
| `(0 : ℝ) := return zero
| `(1 : ℝ) := return one
| `(%%a + %%b) := do y ← eterm_of_expr b, x ← eterm_of_expr a, return (add x y)
| `(%%a - %%b) := do y ← eterm_of_expr b, x ← eterm_of_expr a, return (sub x y)
| `(%%a * %%b) := do y ← eterm_of_expr b, x ← eterm_of_expr a, return (mul x y)
| `(%%a / %%b) := do y ← eterm_of_expr b, x ← eterm_of_expr a, return (div x y)
| `(-%%a)      := do x ← eterm_of_expr a, return (neg x)
| `((%%a)⁻¹)   := do x ← eterm_of_expr a, return (inv x)
| `(%%a ^ %%b) := ( do
                    n ← eval_expr ℕ b,
                    x ← eterm_of_expr a,
                    return (pow_nat x n)
                  ) <|> ( do
                    n ← eval_expr ℤ b,
                    x ← eterm_of_expr a,
                    return (pow_int x n)
                  ) 
| `(↑%%a)      := do c ← eval_expr γ a, return (const c)
| _ := failure
--| `(@has_coe.coe ℚ ℝ %%h %%a) := do c ← eval_expr γ a, return (const c)
end <|> do i ← get_atom e, return (atom i)

--private meta def znum_of_expr : expr → option znum
--| `(@has_zero.zero %%α %%s)   := some 0
--| `(@has_one.one %%α %%s)     := some 1
--| `(@bit0 %%α %%s %%v)        := bit0 <$> znum_of_expr v
--| `(@bit1 %%α %%s1 %%s2 %%v)  := bit1 <$> znum_of_expr v
--| `(@has_neg.neg %%α %%s %%a) := has_neg.neg <$> znum_of_expr a
--| _                           := none <|> do i ← get_atom e, return (atom i)

private meta def pexpr_of_pos_num (α h_one h_add : expr) : pos_num → pexpr
| pos_num.one := ``(@has_one.one %%α %%h_one)
| (pos_num.bit0 n) := ``(@bit0 %%α %%h_add (%%(pexpr_of_pos_num n)))
| (pos_num.bit1 n) := ``(@bit1 %%α %%h_one %%h_add (%%(pexpr_of_pos_num n)))

private meta def expr_of_num (α : expr) (n : num) : tactic expr :=
match n with
| num.zero := do
  h_zero ← mk_app `has_zero [α] >>= mk_instance',
  to_expr ``(@has_zero.zero %%α %%h_zero)
| (num.pos (pos_num.one)) := do
  h_one ← mk_app `has_one [α] >>= mk_instance',
  to_expr ``(@has_one.one %%α %%h_one)
| (num.pos m) := do
  h_one ← mk_app `has_one [α] >>= mk_instance',
  h_add ← mk_app `has_add [α] >>= mk_instance',
  to_expr (pexpr_of_pos_num α h_one h_add m)
end

private meta def expr_of_znum (α : expr) (n : znum) : tactic expr :=
match n with
| znum.zero := do
  h_zero ← mk_app `has_zero [α] >>= mk_instance',
  to_expr ``(@has_zero.zero %%α %%h_zero)
| (znum.pos n) :=
  expr_of_num α (num.pos n)
| (znum.neg n) := do
  h_neg ← mk_app `has_neg [α] >>= mk_instance',
  e ← expr_of_num α (num.pos n),
  to_expr ``(@has_neg.neg %%α %%h_neg %%e)
end

meta def nterm_to_expr (α : expr) (s : cache_ty) : nterm γ → tactic expr
| (nterm.atom i)  := s.dict.find i
| (nterm.const c) := to_expr ``(%%(rat.reflect c) : %%α)
| (nterm.add x y) := do a ← nterm_to_expr x, b ← nterm_to_expr y, to_expr ``(%%a + %%b)
| (nterm.mul x y) := do a ← nterm_to_expr x, b ← nterm_to_expr y, to_expr ``(%%a * %%b)
| (nterm.pow x n) := do a ← nterm_to_expr x, b ← expr_of_znum `(ℤ) n, to_expr ``(%%a ^ %%b)

meta def prove_norm_hyps (t : eterm ℚ) (s : cache_ty) : tactic (list expr × expr) :=
do
  let t_expr : expr := reflect t,
  ρ ← s.dict_expr,

  let nhyps := norm_hyps t,
  nhyps ← monad.mapm (nterm_to_expr `(ℝ) s) nhyps,
  nhyps ← monad.mapm (λ e, to_expr ``(%%e ≠ 0)) nhyps,
  mvars ← monad.mapm mk_meta_var nhyps,

  h ← to_expr ``(∀ x ∈ norm_hyps %%t_expr, nterm.eval %%ρ x ≠ 0),
  pe ← to_expr ( mvars.foldr (λ e pe, ``((and.intro %%e %%pe))) ``(trivial) ) tt ff,
  ((), pr) ← solve_aux h (refine ``(list.pall_iff_forall_prop.mp _) >> exact pe >> done),

  return (mvars, pr)

-- norm_expr e s = (new_e, pr, mv, mvs, new_s)
-- new_e is the canonized expression
-- pr is a proof that e = new_e
-- mv is a meta-variable to prove by reflexivity
-- mvs are neta-variables for the nonzero hypothesis made by the normalizer
-- new_s is the updated cache
meta def norm_expr (e : expr) (s : cache_ty) :
  tactic (expr × expr × expr × list expr × cache_ty) :=
do
  (t, s) ← (eterm_of_expr e).run s,
  let t_expr : expr := reflect t,
  let norm_t := norm t,
  norm_t_expr ← to_expr ``(norm %%t_expr),
  ρ_expr ← s.dict_expr,

  (mvars, pr0) ← prove_norm_hyps t s,

  --reflexivity from expr to eterm
  h1 ← to_expr ``(%%e = eterm.eval %%ρ_expr %%t_expr),
  ((), pr1) ← solve_aux h1 `[refl, done],

  --correctness theorem
  --h2 ← to_expr ``(eterm.eval %%ρ_expr %%t_expr = nterm.eval %%ρ_expr %%norm_t_expr),
  pr2 ← mk_app `field.correctness [pr0],

  --reflexivity from nterm to expr
  new_e ← nterm_to_expr `(ℝ) s norm_t,
  h3 ← to_expr ``(nterm.eval %%ρ_expr %%norm_t_expr = %%new_e),
  pr3 ← mk_meta_var h3, --heavy computation in the kernel

  pr ← mk_eq_trans pr2 pr3 >>= mk_eq_trans pr1,
  return (new_e, pr, pr3, mvars, s)

end field

meta def prove_by_reflexivity (mvs : list expr) : tactic unit :=
do
  gs ← get_goals,
  set_goals mvs,
  all_goals reflexivity,
  set_goals gs

end tactic

open tactic interactive interactive.types lean.parser
open tactic.field

meta def tactic.interactive.field1 : tactic unit :=
do
  `(%%e1 = %%e2) ← target,

  (new_e1, pr1, mv1, mvs, s) ← norm_expr e1 ∅,
  (new_e2, pr2, mv2, mvs', s) ← norm_expr e2 s,

  ( do
    is_def_eq new_e1 new_e2,
    prove_by_reflexivity [mv1, mv2],
    gs ← get_goals,
    set_goals (gs ++ mvs ++ mvs'),
    mk_eq_symm pr2 >>= mk_eq_trans pr1 >>= tactic.exact
  ) <|> ( do
    pr0 ← to_expr ``(%%new_e1 = %%new_e2) >>= mk_meta_var,
    pr ← mk_eq_symm pr2 >>= mk_eq_trans pr0 >>= mk_eq_trans pr1,
    prove_by_reflexivity [mv1, mv2],
    gs ← get_goals,
    set_goals (gs ++ [pr0] ++ mvs ++ mvs'),
    tactic.exact pr
  )
