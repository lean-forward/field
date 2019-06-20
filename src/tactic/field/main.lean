import .norm

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
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

@[derive decidable_eq, derive has_reflect]
inductive eterm {γ} [const_space γ] : Type
| zero  : eterm
| one   : eterm
| const : γ → eterm
| atom  : num → eterm
| add   : eterm → eterm → eterm
| sub   : eterm → eterm → eterm
| mul   : eterm → eterm → eterm
| div   : eterm → eterm → eterm
| neg   : eterm → eterm
| inv   : eterm → eterm
| pow   : eterm → ℤ → eterm

namespace eterm

def eval (ρ : dict α) : @eterm γ _ → α
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
| (pow x n) := eval x ^ n

def to_nterm : @eterm γ _ → @nterm γ _
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
| (pow x n) := to_nterm x ^ (n : znum)

theorem correctness {x : @eterm γ _} :
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
    x n ihx;    --pow
  unfold to_nterm; unfold eterm.eval,
  repeat { simp },
  repeat { simp [ihx] },
  repeat { simp [ihx, ihy] }
end

end eterm

def norm (x : @eterm γ _) : @nterm γ _ :=
x.to_nterm.norm

def norm_hyps (x : @eterm γ _) : list (@nterm γ _) :=
x.to_nterm.norm_hyps

theorem correctness {x : @eterm γ _} {ρ : dict α} :
  (∀ t ∈ norm_hyps x, nterm.eval ρ t ≠ 0) →
  eterm.eval ρ x = nterm.eval ρ (norm x) :=
begin
  intro H,
  unfold norm,
  apply eq.symm, apply eq.trans,
  { apply nterm.correctness, unfold nterm.nonzero,
    intros t ht, apply H, exact ht },
  { apply eterm.correctness }
end

end field

namespace tactic
open native tactic

namespace field
open field field.eterm

meta structure cache_ty :=
(new_atom : num)
(atoms : rb_map expr num)
(dict: rb_map num expr)

meta instance : has_emptyc cache_ty :=
⟨⟨0, rb_map.mk _ _, rb_map.mk _ _⟩⟩

meta def state_dict : Type → Type := state cache_ty

meta instance state_dict_monad : monad state_dict := state_t.monad
meta instance state_dict_monad_state : monad_state cache_ty state_dict := state_t.monad_state

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
  le := by apply_instance,
  dec_le := by apply_instance,
}

meta def aux_const : expr → option γ
| `(@has_zero.zero %%α %%s)  := some 0
| `(@has_one.one %%α %%s)    := some 1
| `(@bit0 %%α %%s %%v)       := bit0 <$> aux_const v
| `(@bit1 %%α %%s₁ %%s₂ %%v) := bit1 <$> aux_const v
| `(%%a / %%b)               := do
    x ← aux_const a,
    y ← aux_const b,
    return (x / y)
| _                          := none

meta def aux_num : expr → option ℤ
| `(@has_zero.zero %%α %%s)  := some 0
| `(@has_one.one %%α %%s)    := some 1
| `(@bit0 %%α %%s %%v)       := bit0 <$> aux_num v
| `(@bit1 %%α %%s₁ %%s₂ %%v) := bit1 <$> aux_num v
| `(- %%a)                   := has_neg.neg <$> aux_num a
| _                          := none

meta def eterm_of_expr : expr → state_dict (@eterm γ _) | e :=
match e with
| `(0 : ℝ) := return zero
| `(1 : ℝ) := return one
| `(%%a + %%b) := do
    y ← eterm_of_expr b,
    x ← eterm_of_expr a,
    return (add x y)
| `(%%a - %%b) := do
    y ← eterm_of_expr b,
    x ← eterm_of_expr a,
    return (sub x y)
| `(%%a * %%b) := do
    y ← eterm_of_expr b,
    x ← eterm_of_expr a,
    return (mul x y)
| `(%%a / %%b) := do
    y ← eterm_of_expr b,
    x ← eterm_of_expr a,
    return (div x y)
| `(-%%a) := do
    x ← eterm_of_expr a,
    return (neg x)
| `((%%a)⁻¹) := do
    x ← eterm_of_expr a,
    return (inv x)
| `(%%a ^ %%n) :=
    match aux_num n with
    | (some n) := (λ x, pow x n) <$> eterm_of_expr a
    | none     := atom <$> get_atom e
    end
| `(↑%%e) :=
    match aux_const e with
    | (some n) := return (const n)
    | none     := atom <$> get_atom e
    end
| _ := atom <$> get_atom e
end

meta def nterm_to_expr (α : expr) (s : cache_ty) : @nterm γ _ → tactic expr
| (nterm.atom i)  := do
  e ← s.dict.find i,
  return e
| (nterm.const c) := do
  to_expr ``(%%(reflect c) : %%α)
| (nterm.add x y) := do
  a ← nterm_to_expr x,
  b ← nterm_to_expr y,
  to_expr ``(%%a + %%b)
| (nterm.mul x y) := do
  a ← nterm_to_expr x,
  b ← nterm_to_expr y,
  to_expr ``(%%a * %%b)
| (nterm.pow x n) := do
  a ← nterm_to_expr x,
  to_expr ``(%%a ^ (%%(reflect n) : ℤ))

meta def norm_expr (e : expr) (s : cache_ty) : tactic (expr × expr × cache_ty) :=
do
  let (t, s) := (eterm_of_expr e).run s,
  let t_expr : expr := reflect t,
  let norm_t := norm t,
  norm_t_expr ← to_expr ``(norm %%t_expr),
  ρ_expr ← s.dict_expr,

  --creating mvars and new goals for the assumptions
  let nhyps := norm_hyps t,
  nhyps ← monad.mapm (nterm_to_expr `(ℝ) s) nhyps,
  nhyps ← monad.mapm (λ e, to_expr ``(%%e ≠ 0)) nhyps,
  mvars ← monad.mapm mk_meta_var nhyps,

  --proving the premise of the correctness theorem using mvars
  pe ← to_expr $ mvars.foldr (λ e pe, ``((and.intro %%e %%pe))) ``(trivial),
  --infer_type pe >>= trace,
  h0 ← to_expr ``(∀ x ∈ norm_hyps %%t_expr, nterm.eval %%ρ_expr x ≠ 0),
  ((), pr0) ← solve_aux h0
    (refine ``(list.pall_iff_forall_prop.mp _) >> exact pe >> done),

  --reflexivity from expr to eterm
  h1 ← to_expr ``(%%e = eterm.eval %%ρ_expr %%t_expr),
  ((), pr1) ← solve_aux h1 `[refl, done],

  --correctness theorem
  --h2 ← to_expr ``(eterm.eval %%ρ_expr %%t_expr = nterm.eval %%ρ_expr %%norm_t_expr),
  pr2 ← mk_app `field.correctness [pr0],

  --reflexivity from nterm to expr
  new_e ← nterm_to_expr `(ℝ) s norm_t,
  h3 ← to_expr ``(nterm.eval %%ρ_expr %%norm_t_expr = %%new_e),
  ((), pr3) ← solve_aux h3 `[refl, done],

  pr ← mk_eq_trans pr2 pr3 >>= mk_eq_trans pr1,
  return (new_e, pr, s)

end field
end tactic

open tactic interactive interactive.types lean.parser
open tactic.field

meta def tactic.interactive.field1 : tactic unit :=
do
  `(%%e1 = %%e2) ← target,
  (new_e1, pr1, s) ← field.norm_expr e1 ∅,
  (new_e2, pr2, s) ← norm_expr e2 s,
  is_def_eq new_e1 new_e2,

  pr ← mk_eq_symm pr2 >>= mk_eq_trans pr1,
  tactic.exact pr

