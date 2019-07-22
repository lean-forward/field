import data.polya.field

namespace tactic

meta def pexpr_of_pos_num (α h_one h_add : expr) : pos_num → pexpr
| pos_num.one      := ``(@has_one.one %%α %%h_one)
| (pos_num.bit0 n) := ``(@bit0 %%α %%h_add (%%(pexpr_of_pos_num n)))
| (pos_num.bit1 n) := ``(@bit1 %%α %%h_one %%h_add (%%(pexpr_of_pos_num n)))

meta def expr_of_num (α : expr) (n : num) : tactic expr :=
match n with
| num.zero := do
  h_zero ← mk_app `has_zero [α] >>= mk_instance,
  to_expr ``(@has_zero.zero %%α %%h_zero)
| (num.pos (pos_num.one)) := do
  h_one ← mk_app `has_one [α] >>= mk_instance,
  to_expr ``(@has_one.one %%α %%h_one)
| (num.pos m) := do
  h_one ← mk_app `has_one [α] >>= mk_instance,
  h_add ← mk_app `has_add [α] >>= mk_instance,
  to_expr (pexpr_of_pos_num α h_one h_add m)
end

meta def expr_of_znum (α : expr) (n : znum) : tactic expr :=
match n with
| znum.zero := do
  h_zero ← mk_app `has_zero [α] >>= mk_instance,
  to_expr ``(@has_zero.zero %%α %%h_zero)
| (znum.pos n) :=
  expr_of_num α (num.pos n)
| (znum.neg n) := do
  h_neg ← mk_app `has_neg [α] >>= mk_instance,
  e ← expr_of_num α (num.pos n),
  to_expr ``(@has_neg.neg %%α %%h_neg %%e)
end

meta def expr_of_rat (α : expr) (q : ℚ) : tactic expr :=
let n : znum := q.num in
let d : znum := q.denom in
if d = 1 then
  expr_of_znum α n
else do
  a ← expr_of_znum α n,
  b ← expr_of_znum α d,
  to_expr ``(%%a / %%b)

end tactic

namespace rat

open polya.field

instance : const_space ℚ :=
{ df := by apply_instance,
  lt := (<),
  dec := by apply_instance,
}

instance {α} [discrete_field α] [char_zero α] : morph ℚ α :=
{ cast       := by apply_instance,
  morph_zero := rat.cast_zero,
  morph_one  := rat.cast_one,
  morph_add  := rat.cast_add,
  morph_neg  := rat.cast_neg,
  morph_mul  := rat.cast_mul,
  morph_inv  := rat.cast_inv,
  morph_inj  := begin
      intros a ha,
      apply rat.cast_inj.mp,
      { rw rat.cast_zero, apply ha },
      { resetI, apply_instance }
    end,
}

end rat

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

open polya.field tactic

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

namespace tactic
open native tactic

namespace polya.field
open polya.field polya.field.term

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

meta def cache_ty.dict_expr (α : expr) (s : cache_ty) : tactic expr :=
do
    e ← s.dict.values.expr_reflect α,
    mk_app `list.to_dict [e]

meta def term_of_expr : expr → state_dict term | e :=
match e with
| `(%%a + %%b) := do y ← term_of_expr b, x ← term_of_expr a, return (add x y)
| `(%%a - %%b) := do y ← term_of_expr b, x ← term_of_expr a, return (sub x y)
| `(%%a * %%b) := do y ← term_of_expr b, x ← term_of_expr a, return (mul x y)
| `(%%a / %%b) := do y ← term_of_expr b, x ← term_of_expr a, return (div x y)
| `(-%%a)      := do x ← term_of_expr a, return (neg x)
| `((%%a)⁻¹)   := do x ← term_of_expr a, return (inv x)
| `(%%a ^ %%b) := do x ← term_of_expr a, ( (do n ← b.to_nat, return (pow_nat x n)) <|> (do n ← b.to_int, return (pow_int x n)) )
| _            := do n ← e.to_nat, return (numeral n)
end <|> do i ← get_atom e, return (atom i)

--TODO: more generic
@[reducible] def α := ℚ
@[reducible] def γ := ℚ

meta def nterm_to_expr (s : cache_ty) : nterm γ → tactic expr
| (nterm.atom i)  := s.dict.find i
| (nterm.const c) := expr_of_rat `(α) c
| (nterm.add x y) := do a ← nterm_to_expr x, b ← nterm_to_expr y, to_expr ``(%%a + %%b)
| (nterm.mul x y) := do a ← nterm_to_expr x, b ← nterm_to_expr y, to_expr ``(%%a * %%b)
| (nterm.pow x n) := do a ← nterm_to_expr x, b ← expr_of_znum `(ℤ) n, to_expr ``(%%a ^ %%b)

meta def prove_norm_hyps (t : term) (s : cache_ty) : tactic (list expr × expr) :=
do
  let t_expr : expr := reflect t,
  ρ ← s.dict_expr `(α),

  let nhyps := norm_hyps γ t,
  nhyps ← monad.mapm (nterm_to_expr s) nhyps,
  nhyps ← monad.mapm (λ e, to_expr ``(%%e ≠ 0)) nhyps,
  mvars ← monad.mapm mk_meta_var nhyps,

  h ← to_expr ``(∀ x ∈ norm_hyps γ %%t_expr, nterm.eval %%ρ x ≠ 0),
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
  (t, s) ← (term_of_expr e).run s,
  let t_expr : expr := reflect t,
  let norm_t := norm γ t,
  norm_t_expr ← to_expr ``(norm γ %%t_expr),
  ρ_expr ← s.dict_expr `(α),

  (mvars, pr0) ← prove_norm_hyps t s,

  --reflexivity from expr to term
  h1 ← to_expr ``(%%e = term.eval %%ρ_expr %%t_expr),
  ((), pr1) ← solve_aux h1 `[refl, done],

  --correctness theorem
  --h2 ← to_expr ``(term.eval %%ρ_expr %%t_expr = nterm.eval %%ρ_expr %%norm_t_expr),
  pr2 ← mk_app `polya.field.correctness [pr0],

  --reflexivity from nterm to expr
  new_e ← nterm_to_expr s norm_t,
  h3 ← to_expr ``(nterm.eval %%ρ_expr %%norm_t_expr = %%new_e),
  pr3 ← mk_meta_var h3, --heavy computation in the kernel

  pr ← mk_eq_trans pr2 pr3 >>= mk_eq_trans pr1,
  return (new_e, pr, pr3, mvars, s)

end polya.field

meta def prove_by_reflexivity (mvs : list expr) : tactic unit :=
do
  gs ← get_goals,
  set_goals mvs,
  all_goals reflexivity,
  set_goals gs

end tactic

open tactic interactive interactive.types lean.parser
open tactic.polya.field

meta def tactic.interactive.field1 : tactic unit :=
do
  `(%%e1 = %%e2) ← target,

  (new_e1, pr1, mv1, mvs, s) ← norm_expr e1 ∅,
  (new_e2, pr2, mv2, mvs', s) ← norm_expr e2 s,

  ( do
    unify new_e1 new_e2,
    prove_by_reflexivity [mv1, mv2],
    gs ← get_goals,
    set_goals (gs ++ mvs ++ mvs'),
    pr ← mk_eq_symm pr2 >>= mk_eq_trans pr1,
    tactic.exact pr
  ) <|> ( do
    prove_by_reflexivity [mv1, mv2],
    pr0 ← to_expr ``(%%new_e1 = %%new_e2) >>= mk_meta_var,
    gs ← get_goals,
    set_goals (gs ++ [pr0] ++ mvs ++ mvs'),
    pr ← mk_eq_symm pr2 >>= mk_eq_trans pr0 >>= mk_eq_trans pr1,
    tactic.exact pr
  )
