import .sform .pform .norm

namespace polya.field

--namespace nterm
--
--variables {α : Type} [discrete_field α]
--variables {γ : Type} [const_space γ]
--variables [morph γ α] {ρ : dict α}
--
--instance coe_atom  : has_coe num (nterm γ) := ⟨atom⟩
--instance coe_const : has_coe γ (nterm γ) := ⟨const⟩
--
--instance : has_zero (nterm γ) := ⟨const 0⟩
--instance : has_one (nterm γ) := ⟨const 1⟩
--
--instance : has_add (nterm γ) := ⟨sform.add⟩
--instance : has_mul (nterm γ) := ⟨pform.mul⟩
--instance : has_pow (nterm γ) ℤ := ⟨λ (x : nterm γ) (n : ℤ), pow_mul (n : znum) x⟩
--
--instance : has_neg (nterm γ) := ⟨scale (-1)⟩
--instance : has_sub (nterm γ) := ⟨λ x y, x + -y⟩
--instance : has_inv (nterm γ) := ⟨λ x, x ^ (-1 : ℤ)⟩
--instance : has_div (nterm γ) := ⟨λ x y, x * y⁻¹⟩
--
--instance pow_nat : has_pow (nterm γ) ℕ := ⟨λ (x : nterm γ) (n : ℕ), x ^ (n : ℤ)⟩
--
--section
--
--variables {x y : nterm γ} {i : num} {n : ℤ} {c : γ}
--
--@[simp] theorem eval_zero  : eval ρ (0 : nterm γ) = 0 := by apply morph.morph_zero'
--@[simp] theorem eval_one   : eval ρ (1 : nterm γ) = 1 := by apply morph.morph_one'
--@[simp] theorem eval_const : eval ρ (const c) = c     := rfl
--@[simp] theorem eval_atom  : eval ρ (atom i : nterm γ) = ρ.val i := rfl
--
--@[simp] theorem eval_add : eval ρ (x + y) = eval ρ x + eval ρ y := sform.eval_add
--@[simp] theorem eval_mul : eval ρ (x * y) = eval ρ x * eval ρ y := pform.eval_mul
--@[simp] theorem eval_pow : eval ρ (x ^ n) = eval ρ x ^ n        := by { convert eval_pow_mul, rw znum.to_of_int }
--
--@[simp] theorem eval_neg : eval ρ (-x)    = - x.eval ρ          := by { refine eq.trans eval_scale _, rw [morph.morph_neg, morph.morph_one', mul_neg_one] }
--@[simp] theorem eval_sub : eval ρ (x - y) = x.eval ρ - y.eval ρ := by { refine eq.trans eval_add _, rw [eval_neg, sub_eq_add_neg] }
--@[simp] theorem eval_inv : eval ρ (x⁻¹)   = (x.eval ρ)⁻¹        := by { rw [← fpow_inv, ← eval_pow], refl }
--@[simp] theorem eval_div : eval ρ (x / y) = x.eval ρ / y.eval ρ := by { rw [division_def, ← eval_inv, ← eval_mul], refl }
--
--@[simp] theorem eval_pow_nat {n : ℕ} : eval ρ (x ^ n) = eval ρ x ^ n := eval_pow
--
--end
--
--end nterm

@[derive decidable_eq, derive has_reflect]
inductive term : Type
| atom : num → term
| add  : term → term → term
| sub  : term → term → term
| mul  : term → term → term
| div  : term → term → term
| neg  : term → term
| inv  : term → term
| numeral : ℕ → term
| pow_nat : term → ℕ → term
| pow_int : term → ℤ → term

namespace term

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def eval (ρ : dict α) : term → α
| (atom i)  := ρ.val i
| (add x y) := eval x + eval y
| (sub x y) := eval x - eval y
| (mul x y) := eval x * eval y
| (div x y) := (eval x) / (eval y)
| (neg x)   := - eval x
| (inv x)   := (eval x)⁻¹
| (numeral n)   := (n : α)
| (pow_nat x n) := eval x ^ n
| (pow_int x n) := eval x ^ n

def to_nterm : term → nterm γ
| (atom i)  := ↑i
| (add x y) := to_nterm x + to_nterm y
| (sub x y) := to_nterm x - to_nterm y
| (mul x y) := to_nterm x * to_nterm y
| (div x y) := to_nterm x / to_nterm y
| (neg x)   := - to_nterm x
| (inv x)   := (to_nterm x)⁻¹
| (numeral n)   := ↑(n : γ)
| (pow_nat x n) := to_nterm x ^ n
| (pow_int x n) := to_nterm x ^ n

theorem correctness {x : term} :
  nterm.eval ρ (@to_nterm γ _ x) = eval ρ x :=
begin
  induction x with
    i           --atom
    x y ihx ihy --add
    x y ihx ihy --sub
    x y ihx ihy --mul
    x y ihx ihy --div
    x ihx       --neg
    x ihx       --inv
    n           --numeral
    x n ihx     --pow_nat
    x n ihx,    --pow_int
  repeat { unfold to_nterm, unfold eval },
  repeat { simp [nterm.eval] },
  repeat { simp [nterm.eval, ihx] },
  repeat { simp [nterm.eval, ihx, ihy] },
  --{ rw [fpow_inv, division_def] },
  --{ rw fpow_inv }
end

end term

def norm (γ : Type) [const_space γ] (x : term) : nterm γ :=
nterm.norm $ @term.to_nterm γ _ x

def norm_hyps (γ : Type) [const_space γ] (x : term) : list (nterm γ) :=
nterm.norm_hyps $ @term.to_nterm γ _ x

variables {γ : Type} [const_space γ]
variables {α : Type} [discrete_field α]
variables [morph γ α] {ρ : dict α}

theorem correctness {x : term} {ρ : dict α} :
  (∀ t ∈ norm_hyps γ x, nterm.eval ρ t ≠ 0) →
  term.eval ρ x = nterm.eval ρ (norm γ x) :=
begin
  intro H,
  unfold norm,
  apply eq.symm, apply eq.trans,
  { apply nterm.correctness, unfold nterm.nonzero,
    intros t ht, apply H, exact ht },
  { apply term.correctness }
end

open nterm

def aux1 (t1 t2 : nterm γ) : nterm γ × nterm γ × γ :=
if t2.coeff = 0 then
  (t1.term, 0, t1.coeff)
else
  (t2.term, t1.scale (t2.coeff⁻¹), -t2.coeff)

def aux2 (t1 t2 : nterm γ) : nterm γ × nterm γ × γ :=
if t2.term < t1.term then
  aux1 (t2.scale (-1)) (t1.scale (-1))
else
  aux1 t1 t2

theorem eval_aux1 {t1 t2 t3 t4 : nterm γ} {c : γ} :
  (t3, t4, c) = aux1 t1 t2 →
  eval ρ t1 - eval ρ t2 = (eval ρ t3 - eval ρ t4) * c :=
begin
  unfold aux1,
  by_cases h1 : t2.coeff = 0,
  { rw if_pos h1, intro h2,
    rw [prod.mk.inj_iff] at h2, cases h2 with h2 h3,
    rw [prod.mk.inj_iff] at h3, cases h3 with h3 h4,
    rw [eval_term_coeff t1, eval_term_coeff t2, h1, h2, h3, h4],
    simp [morph.morph_neg] },
  { rw if_neg h1, intro h2,
    rw [prod.mk.inj_iff] at h2, cases h2 with h2 h3,
    rw [prod.mk.inj_iff] at h3, cases h3 with h3 h4,
    rw [h2, h3, h4],
    rw [morph.morph_neg, mul_neg_eq_neg_mul_symm, neg_mul_eq_neg_mul, neg_sub, sub_mul],
    rw [← eval_term_coeff], congr' 1,
    rw [eval_scale, mul_assoc, ← morph.morph_mul, inv_mul_cancel],
    rw [morph.morph_one, mul_one], --simp
    exact h1 }
end

theorem eval_aux2 {t1 t2 t3 t4 : nterm γ} {c : γ} :
  (t3, t4, c) = aux2 t1 t2 →
  eval ρ t1 - eval ρ t2 = (eval ρ t3 - eval ρ t4) * c :=
begin
  unfold aux2,
  by_cases h1 : t2.term < t1.term,
  { rw if_pos h1, intro h2,
    have : eval ρ (t2.scale (-1)) - eval ρ (t1.scale (-1)) = (eval ρ t3 - eval ρ t4) * ↑c,
    { exact eval_aux1 h2 },
    rw ← this, simp [morph.morph_neg] },
  { rw if_neg h1, intro h2, exact eval_aux1 h2 }
end

def norm2 (γ : Type) [const_space γ] (t1 t2 : term) : nterm γ × nterm γ × γ :=
  aux2 (norm γ t1) (norm γ t2)

theorem eval_norm2 {t1 t2 : term} {nt1 nt2 : nterm γ} {c : γ} :
  nonzero ρ (norm_hyps γ t1) →
  nonzero ρ (norm_hyps γ t2) →
  (nt1, nt2, c) = norm2 γ t1 t2 →
  term.eval ρ t1 - term.eval ρ t2 =
    (nterm.eval ρ nt1 - nterm.eval ρ nt2) * c :=
begin
  unfold norm2,
  intros h1 h2 h3,
  apply eq.trans,
  { show _ = eval ρ (norm γ t1) - eval ρ (norm γ t2), rw [correctness h1, correctness h2] },
  { exact eval_aux2 h3 }
end

end polya.field