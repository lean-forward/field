import .nterm

namespace field

open nterm

--@[derive decidable_eq]
structure xterm (γ : Type) [const_space γ] : Type :=
(term : nterm γ)
(exp : znum)

namespace xterm
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def to_nterm (x : xterm γ) : nterm γ :=
if x.exp = 0 then x.term / x.term
else if x.exp = 1 then x.term
else x.term ^ x.exp

def eval (ρ : dict α) (x : xterm γ) : α :=
let a := nterm.eval ρ x.term in
if a = 0 then 0 else a ^ (x.exp : ℤ)

def eval_to_nterm {x : xterm γ} :
 nterm.eval ρ x.to_nterm = xterm.eval ρ x :=
begin
  by_cases hx : nterm.eval ρ x.term = 0;
  { by_cases h1 : x.exp = 0,
    { simp [hx, h1, nterm.eval, xterm.eval, to_nterm] },
    { have : (x.exp : ℤ) ≠ 0, by {rw ← znum.cast_zero, exact_mod_cast h1 },
      by_cases h2 : x.exp = 1;
      simp [hx, h1, h2, nterm.eval, xterm.eval, to_nterm, zero_fpow, this] }}
end

theorem eval_to_nterm' :
  nterm.eval ρ ∘ @xterm.to_nterm γ _ = xterm.eval ρ :=
begin
  unfold function.comp,
  simp [eval_to_nterm]
end

theorem eval_def {x : nterm γ} {n : znum} :
  xterm.eval ρ ⟨x, n⟩ =
    if nterm.eval ρ x = 0 then 0
    else nterm.eval ρ x ^ (n : ℤ) :=
rfl

theorem eval_add {x : nterm γ} {n m : znum} :
  xterm.eval ρ ⟨x, n + m⟩ = xterm.eval ρ ⟨x, n⟩ * xterm.eval ρ ⟨x, m⟩ :=
begin
  by_cases hx : nterm.eval ρ x = 0;
  simp [xterm.eval, fpow_add, hx]
end

def pmerge : list (xterm γ) → list (xterm γ) → list (xterm γ)
| (x::xs) (y::ys) :=
  if x.term = y.term then
    ⟨x.term, x.exp + y.exp⟩ :: pmerge xs ys
  else if x.term < y.term then
    x :: pmerge xs (y::ys)
  else
    y :: pmerge (x::xs) ys
| xs [] := xs
| [] ys := ys

lemma pmerge_nil_left {ys : list (xterm γ)} :
  pmerge [] ys = ys :=
begin
  induction ys with y ys ih,
  { unfold pmerge },
  { unfold pmerge }
end

lemma pmerge_nil_right {xs : list (xterm γ)} :
  pmerge xs [] = xs :=
begin
  induction xs with x xs ih,
  { unfold pmerge },
  { unfold pmerge }
end

lemma pmerge_def1 {x y : xterm γ} {xs ys : list (xterm γ)} :
  x.term = y.term →
  pmerge (x::xs) (y::ys) = ⟨x.term, x.exp + y.exp⟩ :: pmerge xs ys :=
by intro h; simp [pmerge, h]
lemma pmerge_def2 {x y : xterm γ} {xs ys : list (xterm γ)} :
  x.term ≠ y.term → x.term < y.term →
  pmerge (x::xs) (y::ys) = x :: pmerge xs (y :: ys) :=
by intros h1 h2; simp [pmerge, h1, h2]
lemma pmerge_def3 {x y : xterm γ} {xs ys : list (xterm γ)} :
  x.term ≠ y.term → ¬ x.term < y.term →
  pmerge (x::xs) (y::ys) = y :: pmerge (x::xs) ys :=
by intros h1 h2; simp [pmerge, h1, h2]

theorem eval_pmerge (xs ys : list (xterm γ)) :
  list.prod (list.map (xterm.eval ρ) (pmerge xs ys))
  = list.prod (list.map (xterm.eval ρ) xs)
    * list.prod (list.map (xterm.eval ρ) ys) :=
begin
  revert ys,
  induction xs with x xs ihx,
  { intro ys, simp [pmerge_nil_left] },
  { intro ys, induction ys with y ys ihy,
    { simp [pmerge_nil_right] },
    { by_cases h1 : x.term = y.term,
      { rw pmerge_def1 h1,
        cases x with x n, cases y with y m,
        simp only [] at h1, rw h1 at *,
        repeat {rw [list.map_cons, list.prod_cons]},
        rw [eval_add, ihx ys], ring },
      { by_cases h2 : x.term < y.term,
        { rw pmerge_def2 h1 h2,
          repeat {rw [list.map_cons, list.prod_cons]},
          rw [ihx (y::ys), list.map_cons, list.prod_cons],
          ring},
        { rw pmerge_def3 h1 h2,
          repeat {rw [list.map_cons, list.prod_cons]},
          rw [ihy, list.map_cons, list.prod_cons],
          ring }}}}
end

theorem eval_pow {x : xterm γ} {n : znum} :
  n ≠ 0 → xterm.eval ρ ⟨x.term, x.exp * n⟩ = xterm.eval ρ x ^ (n : ℤ) :=
begin
  intro h0,
  have h1 : (n : ℤ) ≠ 0, by {rw ← znum.cast_zero, exact_mod_cast h0},
  by_cases hx : nterm.eval ρ x.term = 0,
  { simp [hx, xterm.eval, zero_fpow, h1] },
  { simp [hx, xterm.eval, fpow_mul] }
end

theorem eval_prod_pow {xs : list (xterm γ)} {n : znum} :
  n ≠ 0 → list.prod (list.map (xterm.eval ρ) xs) ^ (n : ℤ)
    = list.prod (list.map (λ x : xterm γ, xterm.eval ρ ⟨x.term, x.exp * n⟩) xs) :=
begin
  intro hn,
  induction xs with x xs ih,
  { simp },
  { repeat {rw [list.map_cons, list.prod_cons]},
    rw [eval_pow hn, mul_fpow, ih] }
end

end xterm

structure pterm (γ : Type) [const_space γ] : Type :=
(terms : list (xterm γ))
(coeff : γ)

namespace pterm
variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

def of_const (a : γ) : pterm γ :=
{ terms := [], coeff := a, }

def singleton (x : nterm γ) : pterm γ :=
{ terms := [⟨x, 1⟩], coeff := 1 }

def eval (ρ : dict α) (P : pterm γ) : α :=
list.prod (P.terms.map (xterm.eval ρ)) * ↑P.coeff

theorem eval_of_const (a : γ) :
  pterm.eval ρ (of_const a) = ↑a :=
by simp [of_const, pterm.eval, xterm.eval]

theorem eval_singleton (x : nterm γ) :
  pterm.eval ρ (singleton x) = nterm.eval ρ x :=
begin
  by_cases hx : nterm.eval ρ x = 0,
  repeat {simp [singleton, pterm.eval, xterm.eval, hx]}
end

def mul (P1 P2 : pterm γ) : pterm γ :=
if P1.coeff = 0 ∨ P2.coeff = 0 then
  { terms := [],
    coeff := 0,
  }
else
  { terms := xterm.pmerge P1.terms P2.terms,
    coeff := P1.coeff * P2.coeff,
  }

def pow (P : pterm γ) (n : znum) : pterm γ :=
if n = 0 then
  of_const 1
else
  { terms := P.terms.map (λ x, ⟨x.term, x.exp * n⟩),
    coeff := P.coeff ^ (n : ℤ),
  }

instance : has_mul (pterm γ) := ⟨mul⟩
instance : has_pow (pterm γ) znum := ⟨pow⟩

theorem mul_terms {P Q : pterm γ} :
  P.coeff ≠ 0 ∧ Q.coeff ≠ 0 →
  (P * Q).terms = xterm.pmerge P.terms Q.terms :=
begin
  intro h,
  simp [has_mul.mul, mul, h]
end

theorem mul_terms' {P Q : pterm γ} :
  P.coeff = 0 ∨ Q.coeff = 0 →
  (P * Q).terms = [] :=
begin
  intro h,
  simp [has_mul.mul, mul, h]
end

theorem mul_coeff {P Q : pterm γ} :
  (P * Q).coeff = P.coeff * Q.coeff :=
begin
  by_cases h : P.coeff = 0 ∨ Q.coeff = 0,
  { apply eq.trans,
    { show (P * Q).coeff = 0, simp [has_mul.mul, mul, h] },
    { simp [h] }},
  { simp [has_mul.mul, mul, h] }
end

theorem eval_mul {P Q : pterm γ} :
  pterm.eval ρ (P * Q) = pterm.eval ρ P * pterm.eval ρ Q :=
begin
  unfold pterm.eval, rw mul_coeff,
  by_cases h0 : P.coeff = 0 ∨ Q.coeff = 0,
  { cases h0; simp [h0, morph.morph0] },
  { have : P.coeff ≠ 0 ∧ Q.coeff ≠ 0,
    from (decidable.not_or_iff_and_not _ _).mp h0,
    rw [mul_terms this, xterm.eval_pmerge, morph.morph_mul],
    ring }
end

theorem pow_def {P : pterm γ} {n : znum} :
  n ≠ 0 → pterm.eval ρ (P.pow n) =
    list.prod (list.map (λ x : xterm γ, xterm.eval ρ ⟨x.term, x.exp * n⟩) P.terms) * ↑P.coeff ^ (n : ℤ) :=
begin
  intro hn,
  rw [← morph.morph_pow],
  simp [has_pow.pow, pow, hn, pterm.eval]
end

theorem eval_pow {P : pterm γ} {n : znum} :
  pterm.eval ρ (P ^ n) = pterm.eval ρ P ^ (n : ℤ) :=
begin
  by_cases hn : n = 0,
  { rw [hn, znum.cast_zero, fpow_zero],
    simp [has_pow.pow, pow, of_const, pterm.eval] },
  { cases P with xs c,
    simp only [pterm.eval],
    rw [mul_fpow, ← morph.morph_pow],
    congr,
    { rw xterm.eval_prod_pow hn,
      simp [has_pow.pow, pow, hn] },
    { simp [has_pow.pow, pow, hn] }}
end

def to_nterm (P : pterm γ) : nterm γ :=
--if P.terms.empty then P.coeff
--else if P.coeff = 1 then prod (P.terms.map (xterm.to_nterm))
--else prod (P.terms.map xterm.to_nterm) * P.coeff
prod (P.terms.map xterm.to_nterm) * P.coeff

theorem eval_to_nterm {P : pterm γ} :
  pterm.eval ρ P = nterm.eval ρ P.to_nterm :=
begin
  --cases P with xs c,
  --by_cases h1 : xs.empty = ff,
  --{ by_cases h2 : c = 1,
  --  { rw h2, simp [pterm.eval, to_nterm, h1, eval_prod, xterm.eval_to_nterm'] },
  --  { suffices : list.prod (list.map (xterm.eval ρ) xs) * ↑c =
  --      nterm.eval ρ (prod (list.map xterm.to_nterm xs)) * ↑c,
  --    by { simp [to_nterm, pterm.eval, this, h1, h2] },
  --    rw [eval_prod, list.map_map],
  --    rw xterm.eval_to_nterm' }},
  ----this is silly TODO
  --{ have h1' : xs.empty = tt, by { cases xs,
  --    { refl },
  --    { by_contradiction, apply h1, unfold list.empty }},
  --  cases xs,
  --  { simp [pterm.eval, nterm.eval, to_nterm, h1'] },
  --  { by_contradiction, apply h1, unfold list.empty }
  --}
  cases P with xs c,
  suffices : list.prod (list.map (xterm.eval ρ) xs) * ↑c =
    nterm.eval ρ (prod (list.map xterm.to_nterm xs)) * ↑c,
  by { simp [to_nterm, pterm.eval, this] },
  rw [eval_prod, list.map_map],
  rw xterm.eval_to_nterm'
end

def reduce (P : pterm γ) : pterm γ :=
{ terms := P.terms.filter (λ x, x.exp ≠ 0),
  coeff := P.coeff
}

def reduce_hyps (P : pterm γ) : list (nterm γ) :=
list.map xterm.term (P.terms.filter (λ x, x.exp = 0))

private lemma lemma_eval_reduce {x : xterm γ} :
  x.exp = 0 ∧ nterm.eval ρ x.term ≠ 0 →
  xterm.eval ρ x = 1 :=
begin
  cases x with x n,
  simp only [],
  intro h, cases h with hn hx,
  simp [xterm.eval, hn, hx]
end

theorem eval_reduce {P : pterm γ} :
  nonzero ρ P.reduce_hyps →
  pterm.eval ρ P = pterm.eval ρ P.reduce :=
begin
  intro H,
  have H1 : ∀ x : xterm γ, x ∈ P.terms → x.exp = 0 → nterm.eval ρ (x.term) ≠ 0,
  by { intros x h1 h2, apply H, simp [reduce_hyps], existsi x, simp [h1, h2] },
  have H2 : ∀ x : xterm γ, x ∈ P.terms.filter (λ x, x.exp = 0) → nterm.eval ρ (x.term) ≠ 0,
  by { intros x hx, have : x ∈ P.terms ∧ x.exp = 0, from list.mem_filter.mp hx,
       cases this, apply H1; assumption },

  have : P.terms ~ P.terms.filter (λ x, x.exp = 0) ++ P.terms.filter (λ x, x.exp ≠ 0),
  from list.filter_perm,

  unfold pterm.eval,
  rw list.prod_eq_of_perm (list.perm_map _ this),
  rw [list.map_append, list.prod_append],

  have : ∀ x ∈ P.terms.filter (λ x, x.exp = 0), xterm.eval ρ x = 1,
  by {
    intros x hx,
    apply lemma_eval_reduce,
    split,
    { exact (list.mem_filter.mp hx).right },
    { apply H2, exact hx }},

  have : ∀ a ∈ (list.map (xterm.eval ρ) (P.terms.filter (λ x, x.exp = 0))), a = 1,
  by { intros a ha, rw list.mem_map at ha,
    cases ha with x hx,
    cases hx with hx ha,
    rw ← ha, apply this,
    assumption },

  simp [reduce, list.prod_ones this]
end

def of_nterm : nterm γ → pterm γ
| (nterm.mul x y) := of_nterm x * of_nterm y
| (nterm.pow x n) := of_nterm x ^ n
| (nterm.const a) := of_const a
| x := singleton x

theorem eval_of_nterm {x : nterm γ} :
  pterm.eval ρ (of_nterm x) = nterm.eval ρ x :=
begin
  induction x with i c x y ihx ihy x y ihx ihy x n ihx,
  { simp [of_nterm, eval_singleton] },
  { simp [of_nterm, eval_of_const, nterm.eval] },
  { simp [of_nterm, eval_singleton] },
  { simp [of_nterm, eval_mul, nterm.eval, ihx, ihy] },
  { simp [of_nterm, eval_pow, nterm.eval, ihx] }
end

end pterm

end field

