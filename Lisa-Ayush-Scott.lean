import Mathlib
open Real Complex

noncomputable section

def c : ℤ → ℕ
  | -1 => 1
  | 0 => 0
  | 1 => 196884
  | 2 => 21493760
  | 3 => 864299970
  | 4 => 20245856256
  | 5 => 333202640600
  | _ => 0


def E:=
  {(ℓ, j, k) : (ℕ × ℕ × ℕ) | (1 ≤ k) ∧  (k ≤ c j) ∧ (ℓ < j)}

def c_coeff (ℓ j : ℕ) : ℂ :=
  (-1)^(ℓ + 1) * ↑(Nat.choose (j - 1) ℓ) * ↑(ℓ + 1) * ↑(j - ℓ)

inductive X_type --this is the set of generators
| none : X_type
| H1 (s : ℂ) : X_type
| H2 (s : ℂ) : X_type
| X_neg1 (u : ℂ) : X_type
| Y_neg1 (u : ℂ) : X_type
| X_ljk (ℓjk : E) (u : ℂ) : X_type
| Y_ljk (ℓjk : E) (u : ℂ) : X_type

open X_type

abbrev F : Type := FreeGroup X_type

def fg (t : X_type) := FreeGroup.of t

def com (a b : ℝ) := Complex.mk a b

/-! ### Small helpers to read indices out of `e : E` -/
@[inline] def ellOf (e : E) : ℕ := e.1.1        -- ℓ
@[inline] def jOf   (e : E) : ℕ := e.1.2.1      -- j
@[inline] def kOf   (e : E) : ℕ := e.1.2.2      -- k
@[inline] def cCoeffOf (e : E) : ℂ := c_coeff (ellOf e) (jOf e)

/-! ### (Re:0)  ẇ_{-1}(s) := X_{-1}(s) · Y_{-1}(-s^{-1}) · X_{-1}(s) -/
def wtilde_neg1 (s : ℂˣ) : F :=
  fg (X_neg1 (↑s)) *
  fg (Y_neg1 (-(↑(s⁻¹)))) *
  fg (X_neg1 (↑s))

abbrev wtilde_neg1_one : F := wtilde_neg1 (1 : ℂˣ)

/-! ### (Im:0)  ẇ_{ℓ,jk}(s) := X_{ℓ,jk}(s) · Y_{ℓ,jk}((-s^{-1})/c_{ℓ j}) · X_{ℓ,jk}(s) -/
def wtilde_ljk (e : E) (s : ℂˣ) : F :=
  fg (X_ljk e (↑s)) *
  fg (Y_ljk e (-(↑(s⁻¹)) / cCoeffOf e)) *
  fg (X_ljk e (↑s))

abbrev wtilde_ljk_one (e : E) : F := wtilde_ljk e (1 : ℂˣ)



def rels (s t: ℂˣ) (u v : ℂ) : String → F
  | "H:1a" => fg (H1 s) * fg (H1 t) * (fg (H1 (s*t)))⁻¹
  | "H:1b" => fg (H2 s) * fg (H2 t) * (fg (H2 (s*t)))⁻¹
  | "H:2" => fg (H1 s) * fg (H2 t) * (fg (H2 t))⁻¹ * (fg (H1 s))⁻¹
  | "Re:1a" => fg (X_neg1 u) * fg (X_neg1 v) * (fg (X_neg1 (u+v)))⁻¹
  | "Re:1b" => fg (Y_neg1 u) * fg (Y_neg1 v) * (fg (Y_neg1 (u+v)))⁻¹
  | "Re:2" => fg (Y_neg1 (-t)) * fg (X_neg1 s) * fg (Y_neg1 t) * (fg (X_neg1 (-1*t⁻¹)))⁻¹ * (fg (Y_neg1 (-1*t*t*s)))⁻¹ * (fg (X_neg1 (1*t⁻¹)))⁻¹
   | "Re:3"  =>
      wtilde_neg1 s * wtilde_neg1_one *
      (fg (H1 (-(s : ℂ))) * fg (H2 (-(↑(s⁻¹)))))⁻¹
  | "Re:4a" =>
      wtilde_neg1_one * fg (X_neg1 u) * (wtilde_neg1_one)⁻¹ * (fg (Y_neg1 (-u)))⁻¹
  | "Re:4b" =>
      wtilde_neg1_one * fg (Y_neg1 u) * (wtilde_neg1_one)⁻¹ * (fg (X_neg1 (-u)))⁻¹
  | "Re:5a" =>
      wtilde_neg1_one * fg (H1 (s : ℂ)) * (wtilde_neg1_one)⁻¹ * (fg (H2 (s : ℂ)))⁻¹
  | "Re:5b" =>
      wtilde_neg1_one * fg (H2 (s : ℂ)) * (wtilde_neg1_one)⁻¹ * (fg (H1 (s : ℂ)))⁻¹
  | "Re:6a" =>
      fg (H1 (s : ℂ)) * fg (X_neg1 u) * (fg (H1 (s : ℂ)))⁻¹ *
      (fg (X_neg1 ((s : ℂ) * u)))⁻¹
  | "Re:6b" =>
      fg (H2 (s : ℂ)) * fg (X_neg1 u) * (fg (H2 (s : ℂ)))⁻¹ *
      (fg (X_neg1 ((↑(s⁻¹)) * u)))⁻¹
  | "Re:6c" =>
      fg (H1 (s : ℂ)) * fg (Y_neg1 u) * (fg (H1 (s : ℂ)))⁻¹ *
      (fg (Y_neg1 ((↑(s⁻¹)) * u)))⁻¹
  | "Re:6d" =>
      fg (H2 (s : ℂ)) * fg (Y_neg1 u) * (fg (H2 (s : ℂ)))⁻¹ *
      (fg (Y_neg1 ((s : ℂ) * u)))⁻¹
  |_ => (1 : F)

  def rels_ljk (e : E) (s t : ℂˣ) (u v : ℂ) : String → F
  | "Im:1a" =>
      fg (X_ljk e u) * fg (X_ljk e v) * (fg (X_ljk e (u + v)))⁻¹
  | "Im:1b" =>
      fg (Y_ljk e u) * fg (Y_ljk e v) * (fg (Y_ljk e (u + v)))⁻¹
  | "Im:2"  =>
      fg (Y_ljk e (-(t : ℂ))) * fg (X_ljk e (s : ℂ)) * fg (Y_ljk e (t : ℂ)) *
      (fg (X_ljk e (-(↑(t⁻¹)) / cCoeffOf e)))⁻¹ *
      (fg (Y_ljk e (-(cCoeffOf e) * ((t : ℂ) ^ 2 * (s : ℂ)))))⁻¹ *
      (fg (X_ljk e ((↑(t⁻¹)) / cCoeffOf e)))⁻¹
  | "Im:3"  =>
      wtilde_ljk e (s ^ ((ellOf e + 1) * (jOf e - ellOf e))) * wtilde_ljk_one e *
      (fg (H1 ((- (s : ℂ)) ^ (jOf e - ellOf e))) *
       fg (H2 ((- (s : ℂ)) ^ (ellOf e + 1))))⁻¹
  | "Im:4a" =>
      wtilde_ljk_one e * fg (X_ljk e u) * (wtilde_ljk_one e)⁻¹ *
      (fg (Y_ljk e (-(u / cCoeffOf e))))⁻¹
  | "Im:4b" =>
      wtilde_ljk_one e * fg (Y_ljk e u) * (wtilde_ljk_one e)⁻¹ *
      (fg (X_ljk e (-(cCoeffOf e) * u)))⁻¹
  | "Im:5a" =>
      wtilde_ljk_one e * fg (H1 ((s : ℂ) ^ (jOf e - ellOf e))) * (wtilde_ljk_one e)⁻¹ *
      (fg (H2 (((s : ℂ) ^ (ellOf e + 1))⁻¹)))⁻¹
  | "Im:5b" =>
      wtilde_ljk_one e * fg (H2 ((s : ℂ) ^ (ellOf e + 1))) * (wtilde_ljk_one e)⁻¹ *
      (fg (H1 (((s : ℂ) ^ (jOf e - ellOf e))⁻¹)))⁻¹
  | "Im:6a" =>
      fg (H1 (s : ℂ)) * fg (X_ljk e u) * (fg (H1 (s : ℂ)))⁻¹ *
      (fg (X_ljk e (((s : ℂ) ^ (ellOf e + 1)) * u)))⁻¹
  | "Im:6b" =>
      fg (H2 (s : ℂ)) * fg (X_ljk e u) * (fg (H2 (s : ℂ)))⁻¹ *
      (fg (X_ljk e (((s : ℂ) ^ (jOf e - ellOf e)) * u)))⁻¹
  | "Im:6c" =>
      fg (H1 (s : ℂ)) * fg (Y_ljk e u) * (fg (H1 (s : ℂ)))⁻¹ *
      (fg (Y_ljk e (((s : ℂ) ^ (ellOf e + 1))⁻¹ * u)))⁻¹
  | "Im:6d" =>
      fg (H2 (s : ℂ)) * fg (Y_ljk e u) * (fg (H2 (s : ℂ)))⁻¹ *
      (fg (Y_ljk e (((s : ℂ) ^ (jOf e - ellOf e))⁻¹ * u)))⁻¹
  | _ => (1 : F)

def R : Set F :=
  { g | ∃ (s t : ℂˣ) (u v : ℂ) (lbl : String), g = rels s t u v lbl }

abbrev Q : Type := PresentedGroup (R)

abbrev proj : F →* Q := PresentedGroup.mk R

@[simp] lemma proj_rels (s t : ℂˣ) (u v : ℂ) (lbl : String) :
  proj (rels s t u v lbl) = 1 := by
  -- `PresentedGroup.one_of_mem` kills any relation in `R`
  simpa [proj] using
    (PresentedGroup.one_of_mem (rels := R) (x := rels s t u v lbl)
      ⟨s, t, u, v, lbl, rfl⟩)

macro "relsimp" : tactic => `(tactic| simp [rels, map_mul, map_inv, Units.val_mul,
                                           mul_comm, mul_left_comm, mul_assoc])


lemma H1a_pointfree (s t : ℂˣ) :
  proj (fg (H1 ↑s)) * proj (fg (H1 ↑t)) * (proj (fg (H1 (↑s * ↑t))))⁻¹ = 1 := by
  -- combine factors through the hom, then apply the relation
  simpa [rels, map_mul, map_inv, Units.val_mul,
         mul_comm, mul_left_comm, mul_assoc]
    using proj_rels s t 0 0 "H:1a"

#eval 19 + Complex.mk 3 4
end

example : 1=1 := by simp


