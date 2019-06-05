import .nterm

namespace field

open nterm

variables {α : Type} [discrete_field α]
variables {γ : Type} [const_space γ]
variables [morph γ α] {ρ : dict α}

--@[derive decidable_eq]
structure cterm : Type :=
(term : @nterm γ _)
(coeff : γ)
(pr : coeff ≠ 0)

namespace cterm

instance : inhabited (@cterm γ _) := ⟨⟨nterm.const 0, 1, by simp⟩⟩

def to_nterm (x : @cterm γ _) : @nterm γ _ :=
if x.coeff = 0 then 0
else if x.coeff = 1 then x.term
else x.term * x.coeff

def eval (ρ : dict α) (x : @cterm γ _) : α :=
nterm.eval ρ x.term * ↑x.coeff

def eval_to_nterm {x : @cterm γ _} :
 nterm.eval ρ x.to_nterm = cterm.eval ρ x :=
begin
  by_cases h1 : x.coeff = 0;
  by_cases h2 : x.coeff = 1;
  simp [nterm.eval, cterm.eval, to_nterm, h1, h2]
end

theorem eval_to_nterm' :
  @nterm.eval _ _ γ _ _ ρ ∘ cterm.to_nterm = cterm.eval ρ :=
begin
  unfold function.comp,
  simp [eval_to_nterm]
end

--TODO
theorem eval_def {x : @nterm γ _} {c : γ} {hc : c ≠ 0} :
  cterm.eval ρ ⟨x, c, hc⟩ = nterm.eval ρ x * ↑c :=
rfl

theorem eval_add {x : @nterm γ _} {a b : γ}
  {ha : a ≠ 0} {hb : b ≠ 0} {hc : a + b ≠ 0} :
  cterm.eval ρ ⟨x, a + b, hc⟩ = cterm.eval ρ ⟨x, a, ha⟩ + cterm.eval ρ ⟨x, b, hb⟩ :=
begin
  simp [eval_def, morph.morph_add, mul_add],
end

def mul (x : @cterm γ _) (a : γ) (ha : a ≠ 0) : @cterm γ _ :=
⟨x.term, x.coeff * a, by simp [ha, x.pr]⟩

theorem eval_mul {x : @cterm γ _} {a : γ} {ha : a ≠ 0} :
  cterm.eval ρ (x.mul a ha) = cterm.eval ρ x * ↑a :=
begin
  simp [cterm.eval, morph.morph_mul, mul], ring
end

theorem eval_sum_mul {xs : list (@cterm γ _)} {a : γ} {ha : a ≠ 0} :
  list.sum (list.map (cterm.eval ρ) xs) * ↑a
    = list.sum (list.map (λ x : cterm, cterm.eval ρ (x.mul a ha)) xs) :=
begin
  induction xs with x xs ih,
  { simp },
  { repeat {rw [list.map_cons, list.sum_cons]},
    rw [eval_mul, add_mul, ih] }
end

def smerge : list (@cterm γ _) → list (@cterm γ _) → list (@cterm γ _)
| (x::xs) (y::ys) :=
  if x.term = y.term then
    let c := x.coeff + y.coeff in
    if hc : c = 0 then smerge xs ys
    else ⟨x.term, c, hc⟩ :: smerge xs ys
  else if x.term < y.term then
    x :: smerge xs (y::ys)
  else
    y :: smerge (x::xs) ys
| xs [] := xs
| [] ys := ys

lemma smerge_nil_left {ys : list (@cterm γ _)} :
  smerge [] ys = ys :=
begin
  induction ys with y ys ih,
  { unfold smerge },
  { unfold smerge }
end

lemma smerge_nil_right {xs : list (@cterm γ _)} :
  smerge xs [] = xs :=
begin
  induction xs with x xs ih,
  { unfold smerge },
  { unfold smerge }
end

lemma smerge_def1 {x y : @cterm γ _} {xs ys : list (@cterm γ _)} :
  x.term = y.term → x.coeff + y.coeff = 0 →
  smerge (x::xs) (y::ys) = smerge xs ys :=
by intros h1 h2; simp [smerge, h1, h2]
lemma smerge_def2 {x y : @cterm γ _} {xs ys : list (@cterm γ _)} :
  x.term = y.term → Π (hc : x.coeff + y.coeff ≠ 0),
  smerge (x::xs) (y::ys) = ⟨x.term, x.coeff + y.coeff, hc⟩ :: smerge xs ys :=
by intros h1 h2; simp [smerge, h1, h2]
lemma smerge_def3 {x y : @cterm γ _} {xs ys : list (@cterm γ _)} :
  x.term ≠ y.term → x.term < y.term →
  smerge (x::xs) (y::ys) = x :: smerge xs (y :: ys) :=
by intros h1 h2; simp [smerge, h1, h2]
lemma smerge_def4 {x y : @cterm γ _} {xs ys : list (@cterm γ _)} :
  x.term ≠ y.term → ¬ x.term < y.term →
  smerge (x::xs) (y::ys) = y :: smerge (x::xs) ys :=
by intros h1 h2; simp [smerge, h1, h2]

theorem eval_smerge (xs ys : list (@cterm γ _)) :
  list.sum (list.map (cterm.eval ρ) (smerge xs ys))
  = list.sum (list.map (cterm.eval ρ) xs)
    + list.sum (list.map (cterm.eval ρ) ys) :=
begin
  revert ys,
  induction xs with x xs ihx,
  { intro ys, simp [smerge_nil_left] },
  { intro ys, induction ys with y ys ihy,
    { simp [smerge_nil_right] },
    { by_cases h1 : x.term = y.term,
      { by_cases h2 : x.coeff + y.coeff = 0,
        { have : eval ρ x = - eval ρ y,
          by {
            rw add_eq_zero_iff_eq_neg at h2,
            unfold cterm.eval, rw [h1, h2, morph.morph_neg],
            ring },
          rw [smerge_def1 h1 h2, ihx],
          repeat {rw [list.map_cons, list.sum_cons]},
          rw this, ring },
        { rw smerge_def2 h1 h2,
          cases x with x n, cases y with y m,
          simp only [] at h1, rw h1 at *,
          repeat {rw [list.map_cons, list.sum_cons]},
          rw [eval_add, ihx ys], { simp },
          repeat {assumption }}},
      { by_cases h2 : x.term < y.term,
        { rw smerge_def3 h1 h2,
          repeat {rw [list.map_cons, list.sum_cons]},
          rw [ihx (y::ys), list.map_cons, list.sum_cons],
          ring},
        { rw smerge_def4 h1 h2,
          repeat {rw [list.map_cons, list.sum_cons]},
          rw [ihy, list.map_cons, list.sum_cons],
          ring}}}}
end

end cterm

structure sterm : Type :=
(terms : list (@cterm γ _))

namespace sterm

def of_const (a : γ) : @sterm γ _ :=
if ha : a = 0 then { terms := [] }
else { terms := [⟨1, a, ha⟩] }

def singleton (x : @nterm γ _) : @sterm γ _ :=
{ terms := [⟨x, 1, by simp⟩] }

def eval (ρ : dict α) (S : @sterm γ _) : α :=
list.sum (S.terms.map (cterm.eval ρ))

theorem eval_of_const (a : γ) :
  sterm.eval ρ (of_const a) = ↑a :=
begin
  by_cases ha : a = 0;
  simp [of_const, sterm.eval, cterm.eval, ha]
end

theorem eval_singleton (x : @nterm γ _) :
  sterm.eval ρ (singleton x) = nterm.eval ρ x :=
begin
  by_cases hx : nterm.eval ρ x = 0,
  repeat {simp [singleton, sterm.eval, cterm.eval, hx]}
end

--mul
def add (S T : @sterm γ _) : @sterm γ _ :=
{ terms := cterm.smerge S.terms T.terms, }

--pow
def mul (S : @sterm γ _) (a : γ) : @sterm γ _ :=
if ha : a = 0 then { terms := [] }
else { terms := S.terms.map (λ x, cterm.mul x a ha), }

instance : has_add (@sterm γ _) := ⟨add⟩

theorem add_terms {S T : @sterm γ _} :
  (S + T).terms = cterm.smerge S.terms T.terms :=
by simp [has_add.add, add]

theorem eval_add {S T : @sterm γ _} :
  sterm.eval ρ (S + T) = sterm.eval ρ S + sterm.eval ρ T :=
begin
  unfold sterm.eval,
  rw [add_terms, cterm.eval_smerge]
end

theorem eval_mul {S : @sterm γ _} {a : γ} :
  sterm.eval ρ (S.mul a) = sterm.eval ρ S * ↑a :=
begin
  by_cases ha : a = 0,
  { simp [mul, eval, ha] },
  { unfold sterm.eval, unfold mul,
    rw cterm.eval_sum_mul,
     { simp [ha] },
     { exact ha }}
end

def to_nterm (S : @sterm γ _) : @nterm γ _ :=
if S.terms.empty then 0
else
  --let a := S.terms.head.coeff in
  if S.terms.head.coeff = 1 then
    sum (list.map (cterm.to_nterm) S.terms)
  else
    sum (list.map (cterm.to_nterm) (S.mul (S.terms.head.coeff⁻¹)).terms) * S.terms.head.coeff

theorem eval_to_nterm_aux {S : @sterm γ _} :
  sterm.eval ρ S = nterm.eval ρ (sum (list.map (cterm.to_nterm) S.terms)) :=
by {unfold eval, rw [nterm.eval_sum, list.map_map, cterm.eval_to_nterm']}

theorem eval_to_nterm {S : @sterm γ _} :
  sterm.eval ρ S = nterm.eval ρ S.to_nterm :=
begin
  by_cases h1 : S.terms.empty = tt,
  { cases S with ts, cases ts,
    { simp [to_nterm, eval, list.empty, h1] },
    { cases h1 }},
  { unfold to_nterm, rw if_neg h1,
    by_cases h2 : S.terms.head.coeff = 1,
    { rw if_pos h2, apply eval_to_nterm_aux },
    { rw if_neg h2,
      generalize h3 : S.terms.head.coeff = a,
      rw [nterm.eval_mul, nterm.eval_const],
      rw ← @mul_div_cancel' α _ (eval ρ S) ↑a,
      { rw [division_def, ← morph.morph_inv, ← eval_mul],
        rw eval_to_nterm_aux, apply mul_comm },
      { intro ha,
        have : a = 0, from morph.morph_inj a ha,
        have : a ≠ 0, by {rw ← h3, apply S.terms.head.pr },
        contradiction }}}
end

def of_nterm : @nterm γ _ → @sterm γ _
| (nterm.add x y) := of_nterm x + of_nterm y
| (nterm.mul x (nterm.const a)) := (of_nterm x).mul a
| (nterm.const a) := of_const a
| x := singleton x

theorem eval_of_nterm {x : @nterm γ _} :
  sterm.eval ρ (of_nterm x) = nterm.eval ρ x :=
begin
  induction x with i c x y ihx ihy x y ihx ihy x n ihx,
  { simp [of_nterm, eval_singleton] },
  { simp [of_nterm, eval_of_const, nterm.eval] },
  { simp [of_nterm, eval_add, nterm.eval, ihx, ihy] },
  { cases y; try {simp [of_nterm, eval_singleton]},
    simp [eval_mul, nterm.eval, ihx] },
  { simp [of_nterm, eval_singleton] }
end

end sterm

end field

