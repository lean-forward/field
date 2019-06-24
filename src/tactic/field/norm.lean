import .sterm .pterm

namespace list

theorem subset_union_left {α : Type*} [decidable_eq α]
  {l1 l2 : list α} : l1 ⊆ l1 ∪ l2 :=
by {intros a ha, apply list.mem_union_left, exact ha}

end list

namespace field

inductive alt {γ} [const_space γ] : bool → Type
| sform : list (@nterm γ _) → @sterm γ _ → alt tt
| pform : list (@nterm γ _) → @pterm γ _ → alt ff

namespace alt
open nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def of_const (a : γ) : Π {b}, @alt γ _ b
| tt := sform [] (sterm.of_const a)
| ff := pform [] (pterm.of_const a)

def singleton (x : @nterm γ _) : Π {b}, @alt γ _ b
| tt := sform ∅ (sterm.singleton x)
| ff := pform ∅ (pterm.singleton x)

def to_nterm : @alt γ _ tt → @nterm γ _
| (sform _ S) := S.to_nterm

def to_sterm : @alt γ _ tt → @sterm γ _
| (sform _ S) := S

def to_pterm : @alt γ _ ff → @pterm γ _
| (pform _ P) := P

def hyps : Π {b}, @alt γ _ b → list (@nterm γ _)
| ._ (sform ts _) := ts
| ._ (pform ts _) := ts

def eval (ρ : dict α) : Π {b}, @alt γ _ b → α
| ._ (sform _ S) := sterm.eval ρ S
| ._ (pform _ P) := pterm.eval ρ P

def to_sform : Π {b}, @alt γ _ b → @alt γ _ tt
| ._ (sform ts S) := sform ts S
| ._ (pform ts P) := sform (ts ∪ P.reduce_hyps) (sterm.of_nterm P.reduce.to_nterm)

def to_pform : Π {b}, @alt γ _ b → @alt γ _ ff
| ._ (sform ts S) := pform ts (pterm.of_nterm S.to_nterm)
| ._ (pform ts P) := pform ts P

def hyps_to_sform {a} {x : @alt γ _ a} :
  x.hyps ⊆ x.to_sform.hyps :=
begin
  cases x,
  { simp [to_sform] },
  { unfold to_sform, unfold hyps, exact list.subset_union_left }
end

def hyps_to_pform {a} {x : @alt γ _ a} :
  x.hyps = x.to_pform.hyps :=
by cases x; simp [hyps, to_pform]

theorem eval_def {x : @alt γ _ tt} :
  eval ρ x = nterm.eval ρ x.to_nterm :=
by {cases x, simp [eval, to_nterm, sterm.eval_to_nterm]}

theorem eval_of_const {b} {c : γ} :
  eval ρ (of_const c : @alt γ _ b) = (c : α) :=
by cases b; simp [of_const, eval, pterm.eval_of_const, sterm.eval_of_const]

theorem eval_singleton {b} {x : @nterm γ _} :
  eval ρ (singleton x : @alt γ _ b) = nterm.eval ρ x :=
begin
  cases b,
  { unfold singleton, unfold eval,
    rw ← pterm.eval_singleton },
  { unfold singleton, unfold eval,
    rw ← sterm.eval_singleton }
end

theorem eval_to_sform {b} {x : @alt γ _ b} :
  nonzero ρ x.to_sform.hyps →
  eval ρ x.to_sform = eval ρ x :=
begin
  intro H, cases x,
  { refl },
  { unfold to_sform, unfold eval,
    rw [sterm.eval_of_nterm, ← pterm.eval_to_nterm],
    rw ← pterm.eval_reduce,
    intros t ht, apply H,
    unfold to_sform, unfold hyps,
    apply list.mem_union_right,
    exact ht }
end

theorem eval_to_pform {b} {x : @alt γ _ b} :
  eval ρ x.to_pform = eval ρ x :=
begin
  cases x,
  { unfold to_pform, unfold eval,
    rw [pterm.eval_of_nterm, ← sterm.eval_to_nterm] },
  { refl }
end

theorem eval_to_sterm {x : @alt γ _ tt} :
  sterm.eval ρ x.to_sterm = eval ρ x :=
begin
  cases x, unfold to_sterm, unfold eval
end

theorem eval_to_pterm {x : @alt γ _ ff} :
  eval ρ x = pterm.eval ρ x.to_pterm :=
begin
  cases x, unfold to_pterm, unfold eval
end

--TODO:
--more cases to avoid switching form too often
--when applying operators

def add_sform (x y : @alt γ _ tt) : @alt γ _ tt :=
sform (x.hyps ∪ y.hyps) (x.to_sterm + y.to_sterm)

def mul_pform (x y : @alt γ _ ff) : @alt γ _ ff :=
pform (x.hyps ∪ y.hyps) (x.to_pterm * y.to_pterm)

def pow_pform (x : @alt γ _ ff) (n : znum) : @alt γ _ ff :=
if n = 0 then singleton (1 : γ)
else pform x.hyps (x.to_pterm ^ n)

instance : has_add (@alt γ _ tt) := ⟨add_sform⟩
instance : has_mul (@alt γ _ ff) := ⟨mul_pform⟩
instance : has_pow (@alt γ _ ff) znum := ⟨pow_pform⟩

def add {a b} (x : @alt γ _ a) (y : @alt γ _ b) : @alt γ _ tt :=
x.to_sform + y.to_sform

def mul {a b} (x : @alt γ _ a) (y : @alt γ _ b) : @alt γ _ ff :=
x.to_pform * y.to_pform

def pow {a} (x : @alt γ _ a) (n : znum) : @alt γ _ ff :=
x.to_pform ^ n

theorem hyps_singleton {b} {x : @nterm γ _} :
  (singleton x : @alt γ _ b).hyps = ∅ :=
by cases b; simp [singleton, hyps]

theorem hyps_add_sform {x y : @alt γ _ tt} :
  (x + y).hyps = x.hyps ∪ y.hyps :=
by simp [has_add.add, add_sform, hyps]

theorem hyps_mul_pform {x y : @alt γ _ ff} :
  (x * y).hyps = x.hyps ∪ y.hyps :=
by simp [has_mul.mul, mul_pform, hyps]

theorem hyps_pow_pform {x : @alt γ _ ff} {n : znum} :
  (x ^ n).hyps = if n = 0 then ∅ else x.hyps :=
begin
  by_cases h0 : n = 0;
  by_cases h1 : n = 1;
  simp [has_pow.pow, pow_pform, h0, h1, hyps, hyps_singleton]
end

theorem hyps_add {a b} {x : @alt γ _ a} {y : @alt γ _ b} :
  hyps (add x y) = hyps x.to_sform ∪ hyps y.to_sform :=
by cases x; cases y; simp [add, to_sform, hyps_add_sform]

theorem hyps_mul {a b} {x : @alt γ _ a} {y : @alt γ _ b} :
  hyps (mul x y) = hyps x.to_pform ∪ hyps y.to_pform :=
by cases x; cases y; simp [mul, to_pform, hyps_mul_pform]

theorem hyps_pow {a} {x : @alt γ _ a} {n : znum} :
  hyps (pow x n) = if n = 0 then ∅ else hyps x.to_pform :=
by simp [pow, hyps, hyps_pow_pform]

theorem eval_add_sform {x y : @alt γ _ tt} :
  eval ρ (x + y) = eval ρ x + eval ρ y :=
begin
  suffices : eval ρ (add_sform x y) = eval ρ x + eval ρ y,
  by exact this,
  cases x, cases y,
  unfold add_sform, unfold to_sterm, unfold eval,
  apply sterm.eval_add
end

theorem eval_add {a b} {x : @alt γ _ a} {y : @alt γ _ b} :
  nonzero ρ (hyps (add x y)) →
  eval ρ (add x y) = eval ρ x + eval ρ y :=
begin
  intro H, rw [hyps_add, nonzero_union] at H,
  cases H with H1 H2,
  unfold add, rw [eval_add_sform, eval_to_sform, eval_to_sform],
  { exact H2 },
  { exact H1 }
end

theorem eval_mul_pform {x y : @alt γ _ ff} :
  eval ρ (x * y) = eval ρ x * eval ρ y :=
begin
  suffices : eval ρ (mul_pform x y) = eval ρ x * eval ρ y,
  by exact this,
  cases x, cases y,
  unfold mul_pform, unfold to_pterm, unfold eval,
  apply pterm.eval_mul
end

theorem eval_mul {a b} {x : @alt γ _ a} {y : @alt γ _ b} :
  eval ρ (mul x y) = eval ρ x * eval ρ y :=
begin
  unfold mul, rw [eval_mul_pform, eval_to_pform, eval_to_pform]
end

theorem eval_pow_pform {x : @alt γ _ ff} {n : znum} :
  eval ρ (x ^ n) = eval ρ x ^ (n : ℤ) :=
begin
  suffices : eval ρ (pow_pform x n) = eval ρ x ^ (n : ℤ),
  by exact this,
  cases x,
  unfold pow_pform, unfold to_pterm,
  by_cases hn : n = 0,
  { rw if_pos hn, unfold eval, simp [hn, eval_singleton] },
  { rw if_neg hn, unfold eval, apply pterm.eval_pow }
end

theorem eval_pow {a} {x : @alt γ _ a} {n : znum} :
  eval ρ (pow x n) = eval ρ x ^ (n : ℤ) :=
begin
  unfold pow, rw [eval_pow_pform, eval_to_pform]
end

@[reducible]
def aux_of_nterm : @nterm γ _ → bool
| (nterm.add _ _) := tt
| (nterm.mul _ _) := ff
| (nterm.pow _ _) := ff
| _ := tt

def of_nterm : Π (x : @nterm γ _), @alt γ _ (aux_of_nterm x)
| (nterm.add x y) := add (of_nterm x) (of_nterm y)
| (nterm.mul x y) := mul (of_nterm x) (of_nterm y)
| (nterm.pow x n) := pow (of_nterm x) n
| (nterm.const a) := of_const a
| (nterm.atom i)  := singleton i

theorem eval_of_nterm {x : @nterm γ _} :
  nonzero ρ (of_nterm x).hyps →
  eval ρ (of_nterm x) = nterm.eval ρ x :=
begin
  induction x with i c x y ihx ihy x y ihx ihy x n ihx,
  { intro, unfold of_nterm, rw eval_singleton, refl },
  { intro, unfold of_nterm, rw eval_of_const, simp [nterm.eval] },
  { unfold of_nterm, intro H,
    rw [hyps_add,  nonzero_union] at H,
    rw [eval_add, ihx, ihy],
    { exact nterm.eval_add },
    { apply nonzero_subset (hyps_to_sform), exact H.right},
    { apply nonzero_subset (hyps_to_sform), exact H.left },
    { rw [hyps_add, nonzero_union], exact H }},
  { unfold of_nterm, intro H,
    rw [hyps_mul,  nonzero_union] at H,
    rw [eval_mul, ihx, ihy],
    { exact nterm.eval_mul },
    { rw hyps_to_pform, exact H.right },
    { rw hyps_to_pform, exact H.left }},
  { unfold of_nterm, intro H,
    by_cases hn : n = 0,
    { rw [eval_pow, hn, znum.cast_zero, fpow_zero],
      suffices : nterm.eval ρ (x ^ (0 : znum)) = 1,
      by exact this,
      rw [nterm.eval_pow, znum.cast_zero, fpow_zero] },
    { rw [hyps_pow, if_neg hn] at H,
      rw [eval_pow, ihx],
      { exact nterm.eval_pow },
      { rw hyps_to_pform, exact H }}}
end

end alt

namespace nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def norm (x : @nterm γ _) : @nterm γ _ :=
(alt.of_nterm x).to_sform.to_nterm

def norm_hyps (x : @nterm γ _) : list (@nterm γ _) :=
(alt.of_nterm x).to_sform.hyps

def correctness {x : @nterm γ _} :
  nonzero ρ (norm_hyps x) →
  nterm.eval ρ (norm x) = nterm.eval ρ x :=
begin
  intro H, unfold norm,
  rw [← alt.eval_def, ← alt.eval_of_nterm, alt.eval_to_sform],
  { intros t ht, apply H, exact ht },
  { intros t ht, apply H, apply alt.hyps_to_sform, exact ht }
end

--section soundness
--variables {x y : @nterm γ _} {i : num} {n : znum} {c : γ}
--
--theorem sound_atom : @norm γ _ i = i :=
--begin
--  sorry
--end
--
--theorem sound_const : @norm γ _ c = c :=
--begin
--  sorry
--end
--
--theorem sound_add :
--  norm (x + y) = (sterm.of_nterm x.norm
--    + sterm.of_nterm y.norm).to_nterm :=
--begin
--  sorry
--end
--
--theorem sound_mul :
--  norm (x * y) = (pterm.of_nterm x.norm
--    * pterm.of_nterm y.norm).reduce.to_nterm :=
--begin
--  sorry
--end
--
--theorem sound_pow :
--  norm (x ^ n) = (pterm.of_nterm x.norm ^ n).reduce.to_nterm :=
--begin
--  sorry
--end
--
--def naive_norm : @nterm γ _ → @nterm γ _
--| (add x y) := (sterm.of_nterm (naive_norm x) + sterm.of_nterm (naive_norm y)).to_nterm
--| (mul x y) := (pterm.of_nterm (naive_norm x) * pterm.of_nterm (naive_norm y)).reduce.to_nterm
--| (pow x n) := (pterm.of_nterm (naive_norm x) ^ n).reduce.to_nterm
--| x := x
--
--theorem soundness {x : @nterm γ _} :
--  norm x = naive_norm x :=
--begin
--  sorry
--  --TODO: this theorem is not required,
--  --but it could be an interesting
--  --first step to prove soundness
--end
--
--end soundness

end nterm

end field

