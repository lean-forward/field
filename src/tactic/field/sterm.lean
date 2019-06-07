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
(coeff1 : γ)
(terms : list (@cterm γ _))

namespace sterm

def of_const (a : γ) : @sterm γ _ :=
{ coeff1 := a, terms := [] }

def singleton (x : @nterm γ _) : @sterm γ _ :=
{ coeff1 := 0, terms := [⟨x, 1, by simp⟩] }

def eval (ρ : dict α) (S : @sterm γ _) : α :=
list.sum (S.terms.map (cterm.eval ρ)) + S.coeff1

theorem eval_of_const (a : γ) :
  sterm.eval ρ (of_const a) = ↑a :=
by simp [of_const, sterm.eval, cterm.eval]

theorem eval_singleton (x : @nterm γ _) :
  sterm.eval ρ (singleton x) = nterm.eval ρ x :=
begin
  by_cases hx : nterm.eval ρ x = 0,
  repeat {simp [singleton, sterm.eval, cterm.eval, hx]}
end

--mul
def add (S T : @sterm γ _) : @sterm γ _ :=
{ coeff1 := S.coeff1 + T.coeff1,
  terms := cterm.smerge S.terms T.terms, }

--pow
def mul (S : @sterm γ _) (a : γ) : @sterm γ _ :=
if ha : a = 0 then
  of_const 0
else
  { coeff1 := S.coeff1 * a,
    terms := S.terms.map (λ x, cterm.mul x a ha),
  }

instance : has_add (@sterm γ _) := ⟨add⟩

theorem add_terms {S T : @sterm γ _} :
  (S + T).terms = cterm.smerge S.terms T.terms :=
by simp [has_add.add, add]

theorem add_coeff {S T : @sterm γ _} :
  (S + T).coeff1 = S.coeff1 + T.coeff1 :=
by simp [has_add.add, add]

theorem eval_add {S T : @sterm γ _} :
  sterm.eval ρ (S + T) = sterm.eval ρ S + sterm.eval ρ T :=
begin
  unfold sterm.eval,
  rw [add_terms, cterm.eval_smerge, add_coeff, morph.morph_add],
  ring
end

theorem eval_mul {S : @sterm γ _} {a : γ} :
  sterm.eval ρ (S.mul a) = sterm.eval ρ S * ↑a :=
begin
  by_cases ha : a = 0,
  { simp [mul, eval, ha, of_const] },
  { unfold sterm.eval, unfold mul,
    rw [add_mul, cterm.eval_sum_mul],
    simp [ha], apply add_comm } --TODO
end


def to_nterm (S : @sterm γ _) : @nterm γ _ :=
if h : S.coeff1 = 0 then
  let _ := trace "oups" () in
  match S.terms with
  | []      := 0
  | (x::xs) :=
    if x.coeff = 1 then
      nterm.sum (S.terms.map cterm.to_nterm)
    else
      (nterm.sum (S.terms.map (λ x, (x.mul x.coeff⁻¹ (by simp [x.pr])).to_nterm))) * x.coeff
  end
else if S.coeff1 = 1 then
  nterm.sum (S.terms.map cterm.to_nterm)
else
  if S.terms.empty then
    S.coeff1
  else
    have h' : S.coeff1⁻¹ ≠ 0, by simp [h],
    (nterm.sum (S.terms.map (λ x, (x.mul S.coeff1⁻¹ h').to_nterm)) + 1) * S.coeff1

theorem eval_to_nterm {S : @sterm γ _} :
  sterm.eval ρ S = nterm.eval ρ S.to_nterm :=
begin
  sorry
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

