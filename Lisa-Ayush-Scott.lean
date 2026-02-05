import Mathlib

open Classical

noncomputable section

set_option autoImplicit false

namespace Geometry

/-!
  This file is a Lean scaffold for the group presentations appearing in the
  "Lie group analog for the Monster Lie algebra" notes.  The goal is to set up
  the data and relations so that proofs can be added incrementally.
-/

/-! ## Basic arithmetic data -/

-- Coefficients of the modular function J(q); modeled abstractly for now.
variable (c : ℕ → ℕ)

-- The coefficient c_{ℓ j} as a complex number (formal definition from the notes).
def cCoeff (ℓ j : ℕ) : ℂ :=
  (-1 : ℂ) ^ (ℓ + 1) * (Nat.choose (j - 1) ℓ : ℂ) * (ℓ + 1 : ℂ) * (j - ℓ : ℂ)

/-! ## Index set E -/

-- We keep the index set as a structure and record the validity predicate separately.
structure IndexE (c : ℕ → ℕ) where
  ℓ : ℕ
  j : ℕ
  k : ℕ
deriving DecidableEq

def IndexE.Valid (c : ℕ → ℕ) (e : IndexE c) : Prop :=
  1 ≤ e.k ∧ e.k ≤ c e.j ∧ e.ℓ < e.j

def idx (c : ℕ → ℕ) (ℓ j k : ℕ) : IndexE c :=
  { ℓ := ℓ, j := j, k := k }

def commCond (e f : IndexE c) : Prop :=
  e.j ≠ f.j ∨ e.k ≠ f.k ∨ 1 < Nat.dist e.ℓ f.ℓ

lemma neg_pow_mul (n : ℕ) (u : ℂ) :
    -(((-1 : ℂ)^n) * u) = ((-1 : ℂ)^(n + 1)) * u := by
  have hpow : -((-1 : ℂ)^n) = (-1 : ℂ)^(n + 1) := by
    calc
      -((-1 : ℂ)^n) = (-1 : ℂ) * ((-1 : ℂ)^n) := by simp
      _ = ((-1 : ℂ)^n) * (-1 : ℂ) := by simp [mul_comm]
      _ = (-1 : ℂ)^(n + 1) := by simp [pow_succ]
  calc
    -(((-1 : ℂ)^n) * u) = (-((-1 : ℂ)^n)) * u := by simp [neg_mul]
    _ = ((-1 : ℂ)^(n + 1)) * u := by simp [hpow]

/-! ## Generators for G(m) -/

inductive Gen (c : ℕ → ℕ) where
  | H1 : ℂˣ → Gen c
  | H2 : ℂˣ → Gen c
  | Xneg1 : ℂ → Gen c
  | Yneg1 : ℂ → Gen c
  | X : IndexE c → ℂ → Gen c
  | Y : IndexE c → ℂ → Gen c
deriving DecidableEq

abbrev FG (c : ℕ → ℕ) := FreeGroup (Gen c)

namespace Gm

variable {c : ℕ → ℕ}

def ofGen (g : Gen c) : FG c := FreeGroup.of g

def H1 (s : ℂˣ) : FG c := ofGen (Gen.H1 s)
def H2 (s : ℂˣ) : FG c := ofGen (Gen.H2 s)
def Xneg1 (u : ℂ) : FG c := ofGen (Gen.Xneg1 u)
def Yneg1 (u : ℂ) : FG c := ofGen (Gen.Yneg1 u)
def X (e : IndexE c) (u : ℂ) : FG c := ofGen (Gen.X e u)
def Y (e : IndexE c) (u : ℂ) : FG c := ofGen (Gen.Y e u)

def comm (a b : FG c) : FG c := a * b * a⁻¹ * b⁻¹

def wNeg1 (s : ℂˣ) : FG c :=
  Xneg1 (s : ℂ) * Yneg1 (-(s⁻¹ : ℂ)) * Xneg1 (s : ℂ)

def wNeg1One : FG c := wNeg1 (c := c) 1

def wIm (e : IndexE c) (s : ℂˣ) : FG c :=
  X e (s : ℂ) * Y e (-(s⁻¹ : ℂ) / cCoeff e.ℓ e.j) * X e (s : ℂ)

def wImOne (e : IndexE c) : FG c := wIm (c := c) e 1

/-! ## Relations for G(m) -/

inductive RelName (c : ℕ → ℕ)
  | H1_mul (s t : ℂˣ)
  | H2_mul (s t : ℂˣ)
  | H1H2_comm (s t : ℂˣ)
  | Re_XX (u v : ℂ)
  | Re_YY (u v : ℂ)
  | Re_XY (s : ℂ) (t : ℂˣ)
  | Re_wwH (s : ℂˣ)
  | Re_wX (u : ℂ)
  | Re_wY (u : ℂ)
  | Re_wH1 (s : ℂˣ)
  | Re_wH2 (s : ℂˣ)
  | Re_H1X (s : ℂˣ) (u : ℂ)
  | Re_H2X (s : ℂˣ) (u : ℂ)
  | Re_H1Y (s : ℂˣ) (u : ℂ)
  | Re_H2Y (s : ℂˣ) (u : ℂ)
  | Im_XX (e : IndexE c) (u v : ℂ)
  | Im_YY (e : IndexE c) (u v : ℂ)
  | Im_XY (e : IndexE c) (s : ℂ) (t : ℂˣ)
  | Im_wwH (e : IndexE c) (s : ℂˣ)
  | Im_wX (e : IndexE c) (u : ℂ)
  | Im_wY (e : IndexE c) (u : ℂ)
  | Im_wH1 (e : IndexE c) (s : ℂˣ)
  | Im_wH2 (e : IndexE c) (s : ℂˣ)
  | Im_H1X (e : IndexE c) (s : ℂˣ) (u : ℂ)
  | Im_H2X (e : IndexE c) (s : ℂˣ) (u : ℂ)
  | Im_H1Y (e : IndexE c) (s : ℂˣ) (u : ℂ)
  | Im_H2Y (e : IndexE c) (s : ℂˣ) (u : ℂ)
  | U_Xneg1_X (j k : ℕ) (u v : ℂ)
  | U_Yneg1_Y (j k : ℕ) (u v : ℂ)
  | U_Yneg1_X0 (j k : ℕ) (u v : ℂ)
  | U_Xneg1_Y0 (j k : ℕ) (u v : ℂ)
  | U_comm_XY (e f : IndexE c) (h : commCond (c := c) e f) (u v : ℂ)
  | U_XY_j2a (k : ℕ) (u v : ℂ)
  | U_XY_j2b (k : ℕ) (u v : ℂ)
  | U_w_X (e : IndexE c) (u : ℂ)
  | U_w_Y (e : IndexE c) (u : ℂ)

def relWord : RelName c → FG c
  | RelName.H1_mul s t =>
      H1 s * H1 t * (H1 (s * t))⁻¹
  | RelName.H2_mul s t =>
      H2 s * H2 t * (H2 (s * t))⁻¹
  | RelName.H1H2_comm s t =>
      H1 s * H2 t * (H1 s)⁻¹ * (H2 t)⁻¹
  | RelName.Re_XX u v =>
      Xneg1 u * Xneg1 v * (Xneg1 (u + v))⁻¹
  | RelName.Re_YY u v =>
      Yneg1 u * Yneg1 v * (Yneg1 (u + v))⁻¹
  | RelName.Re_XY s t =>
      Yneg1 (-(t : ℂ)) * Xneg1 s * Yneg1 (t : ℂ) *
        (Xneg1 (-(t⁻¹ : ℂ)) * Yneg1 (-((t : ℂ)^2 * s)) * Xneg1 (t⁻¹ : ℂ))⁻¹
  | RelName.Re_wwH s =>
      wNeg1 (c := c) s * wNeg1One (c := c) *
        (H1 (-s) * H2 (-(s⁻¹)))⁻¹
  | RelName.Re_wX u =>
      wNeg1One (c := c) * Xneg1 u * (wNeg1One (c := c))⁻¹ * (Yneg1 (-u))⁻¹
  | RelName.Re_wY u =>
      wNeg1One (c := c) * Yneg1 u * (wNeg1One (c := c))⁻¹ * (Xneg1 (-u))⁻¹
  | RelName.Re_wH1 s =>
      wNeg1One (c := c) * H1 s * (wNeg1One (c := c))⁻¹ * (H2 s)⁻¹
  | RelName.Re_wH2 s =>
      wNeg1One (c := c) * H2 s * (wNeg1One (c := c))⁻¹ * (H1 s)⁻¹
  | RelName.Re_H1X s u =>
      H1 s * Xneg1 u * (H1 s)⁻¹ * (Xneg1 ((s : ℂ) * u))⁻¹
  | RelName.Re_H2X s u =>
      H2 s * Xneg1 u * (H2 s)⁻¹ * (Xneg1 ((s⁻¹ : ℂ) * u))⁻¹
  | RelName.Re_H1Y s u =>
      H1 s * Yneg1 u * (H1 s)⁻¹ * (Yneg1 ((s⁻¹ : ℂ) * u))⁻¹
  | RelName.Re_H2Y s u =>
      H2 s * Yneg1 u * (H2 s)⁻¹ * (Yneg1 ((s : ℂ) * u))⁻¹
  | RelName.Im_XX e u v =>
      X e u * X e v * (X e (u + v))⁻¹
  | RelName.Im_YY e u v =>
      Y e u * Y e v * (Y e (u + v))⁻¹
  | RelName.Im_XY e s t =>
      Y e (-(t : ℂ)) * X e s * Y e (t : ℂ) *
        (X e (-(t⁻¹ : ℂ) / cCoeff e.ℓ e.j) *
          Y e (-(cCoeff e.ℓ e.j) * ((t : ℂ)^2) * s) *
          X e ((t⁻¹ : ℂ) / cCoeff e.ℓ e.j))⁻¹
  | RelName.Im_wwH e s =>
      wIm (c := c) e (s ^ ((e.ℓ + 1) * (e.j - e.ℓ))) * wImOne (c := c) e *
        (H1 ((-s) ^ (e.j - e.ℓ)) * H2 ((-s) ^ (e.ℓ + 1)))⁻¹
  | RelName.Im_wX e u =>
      wImOne (c := c) e * X e u * (wImOne (c := c) e)⁻¹ *
        (Y e (-(u) / cCoeff e.ℓ e.j))⁻¹
  | RelName.Im_wY e u =>
      wImOne (c := c) e * Y e u * (wImOne (c := c) e)⁻¹ *
        (X e (-(cCoeff e.ℓ e.j) * u))⁻¹
  | RelName.Im_wH1 e s =>
      wImOne (c := c) e * H1 (s ^ (e.j - e.ℓ)) * (wImOne (c := c) e)⁻¹ *
        (H2 ((s⁻¹) ^ (e.ℓ + 1)))⁻¹
  | RelName.Im_wH2 e s =>
      wImOne (c := c) e * H2 (s ^ (e.ℓ + 1)) * (wImOne (c := c) e)⁻¹ *
        (H1 ((s⁻¹) ^ (e.j - e.ℓ)))⁻¹
  | RelName.Im_H1X e s u =>
      H1 s * X e u * (H1 s)⁻¹ * (X e (((s : ℂ) ^ (e.ℓ + 1)) * u))⁻¹
  | RelName.Im_H2X e s u =>
      H2 s * X e u * (H2 s)⁻¹ * (X e (((s : ℂ) ^ (e.j - e.ℓ)) * u))⁻¹
  | RelName.Im_H1Y e s u =>
      H1 s * Y e u * (H1 s)⁻¹ * (Y e (((s⁻¹ : ℂ) ^ (e.ℓ + 1)) * u))⁻¹
  | RelName.Im_H2Y e s u =>
      H2 s * Y e u * (H2 s)⁻¹ * (Y e (((s⁻¹ : ℂ) ^ (e.j - e.ℓ)) * u))⁻¹
  | RelName.U_Xneg1_X j k u v =>
      comm (Xneg1 u) (X (idx c (j - 1) j k) v)
  | RelName.U_Yneg1_Y j k u v =>
      comm (Yneg1 u) (Y (idx c (j - 1) j k) v)
  | RelName.U_Yneg1_X0 j k u v =>
      comm (Yneg1 u) (X (idx c 0 j k) v)
  | RelName.U_Xneg1_Y0 j k u v =>
      comm (Xneg1 u) (Y (idx c 0 j k) v)
  | RelName.U_comm_XY e f _ u v =>
      comm (X e u) (Y f v)
  | RelName.U_XY_j2a k u v =>
      comm (X (idx c 1 2 k) u) (Y (idx c 0 2 k) v) * (Xneg1 (u * v))⁻¹
  | RelName.U_XY_j2b k u v =>
      comm (X (idx c 0 2 k) u) (Y (idx c 1 2 k) v) * (Yneg1 (u * v))⁻¹
  | RelName.U_w_X e u =>
      wNeg1One (c := c) * X e u * (wNeg1One (c := c))⁻¹ *
        (X (idx c (e.j - 1 - e.ℓ) e.j e.k)
          (((-1 : ℂ) ^ (e.j - e.ℓ - 1)) * u))⁻¹
  | RelName.U_w_Y e u =>
      wNeg1One (c := c) * Y e u * (wNeg1One (c := c))⁻¹ *
        (Y (idx c (e.j - 1 - e.ℓ) e.j e.k)
          (((-1 : ℂ) ^ (e.j - e.ℓ - 1)) * u))⁻¹

def rels : Set (FG c) := Set.range (relWord (c := c))

abbrev G : Type := PresentedGroup (rels (c := c))

def of : Gen c → G (c := c) := PresentedGroup.of (rels := rels (c := c))

def H1G (s : ℂˣ) : G (c := c) := of (Gen.H1 s)
def H2G (s : ℂˣ) : G (c := c) := of (Gen.H2 s)
def Xneg1G (u : ℂ) : G (c := c) := of (Gen.Xneg1 u)
def Yneg1G (u : ℂ) : G (c := c) := of (Gen.Yneg1 u)
def XG (e : IndexE c) (u : ℂ) : G (c := c) := of (Gen.X e u)
def YG (e : IndexE c) (u : ℂ) : G (c := c) := of (Gen.Y e u)

def wNeg1G (s : ℂˣ) : G (c := c) :=
  Xneg1G (c := c) (s : ℂ) * Yneg1G (c := c) (-(s⁻¹ : ℂ)) * Xneg1G (c := c) (s : ℂ)

def wNeg1OneG : G (c := c) := wNeg1G (c := c) 1

def wImG (e : IndexE c) (s : ℂˣ) : G (c := c) :=
  XG (c := c) e (s : ℂ) * YG (c := c) e (-(s⁻¹ : ℂ) / cCoeff e.ℓ e.j) *
    XG (c := c) e (s : ℂ)

def wImOneG (e : IndexE c) : G (c := c) := wImG (c := c) e 1

@[simp] lemma mk_H1 (s : ℂˣ) :
    PresentedGroup.mk (rels (c := c)) (FreeGroup.of (Gen.H1 s)) = H1G (c := c) s := rfl

@[simp] lemma mk_H2 (s : ℂˣ) :
    PresentedGroup.mk (rels (c := c)) (FreeGroup.of (Gen.H2 s)) = H2G (c := c) s := rfl

@[simp] lemma mk_Xneg1 (u : ℂ) :
    PresentedGroup.mk (rels (c := c)) (FreeGroup.of (Gen.Xneg1 u)) = Xneg1G (c := c) u := rfl

@[simp] lemma mk_Yneg1 (u : ℂ) :
    PresentedGroup.mk (rels (c := c)) (FreeGroup.of (Gen.Yneg1 u)) = Yneg1G (c := c) u := rfl

@[simp] lemma mk_X (e : IndexE c) (u : ℂ) :
    PresentedGroup.mk (rels (c := c)) (FreeGroup.of (Gen.X e u)) = XG (c := c) e u := rfl

@[simp] lemma mk_Y (e : IndexE c) (u : ℂ) :
    PresentedGroup.mk (rels (c := c)) (FreeGroup.of (Gen.Y e u)) = YG (c := c) e u := rfl

/-! ## Subgroups H and U -/

def toralSubgroup : Subgroup (G (c := c)) :=
  Subgroup.closure { g | (∃ s, g = H1G (c := c) s) ∨ (∃ s, g = H2G (c := c) s) }

def unipotentSubgroup : Subgroup (G (c := c)) :=
  Subgroup.closure { g | (∃ u, g = Xneg1G (c := c) u)
    ∨ (∃ u, g = Yneg1G (c := c) u)
    ∨ (∃ e u, g = XG (c := c) e u)
    ∨ (∃ e u, g = YG (c := c) e u) }

/-! ## Basic consequences of the additive relations -/

lemma relWord_eq_one (r : RelName c) :
    PresentedGroup.mk (rels (c := c)) (relWord (c := c) r) = 1 := by
  apply PresentedGroup.one_of_mem
  exact ⟨r, rfl⟩

lemma H1_mul (s t : ℂˣ) : H1G (c := c) s * H1G (c := c) t = H1G (c := c) (s * t) := by
  have h := relWord_eq_one (c := c) (RelName.H1_mul s t)
  have h' :
      H1G (c := c) s * H1G (c := c) t * (H1G (c := c) (s * t))⁻¹ = 1 := by
    simpa [relWord, H1, ofGen, mul_assoc] using h
  exact (mul_inv_eq_one.mp (by simpa [mul_assoc] using h'))

lemma H2_mul (s t : ℂˣ) : H2G (c := c) s * H2G (c := c) t = H2G (c := c) (s * t) := by
  have h := relWord_eq_one (c := c) (RelName.H2_mul s t)
  have h' :
      H2G (c := c) s * H2G (c := c) t * (H2G (c := c) (s * t))⁻¹ = 1 := by
    simpa [relWord, H2, ofGen, mul_assoc] using h
  exact (mul_inv_eq_one.mp (by simpa [mul_assoc] using h'))

lemma H1H2_comm (s t : ℂˣ) : H1G (c := c) s * H2G (c := c) t = H2G (c := c) t * H1G (c := c) s := by
  have h := relWord_eq_one (c := c) (RelName.H1H2_comm s t)
  have h' :
      H1G (c := c) s * H2G (c := c) t * (H1G (c := c) s)⁻¹ * (H2G (c := c) t)⁻¹ = 1 := by
    simpa [relWord, H1, H2, ofGen, mul_assoc] using h
  -- rewrite to a commutator form
  have h'' :
      (H1G (c := c) s * H2G (c := c) t) * (H2G (c := c) t * H1G (c := c) s)⁻¹ = 1 := by
    -- expand the inverse
    simpa [mul_inv_rev, mul_assoc] using h'
  exact (mul_inv_eq_one.mp h'')

lemma Xneg1_add (u v : ℂ) : Xneg1G (c := c) u * Xneg1G (c := c) v = Xneg1G (c := c) (u + v) := by
  have h := relWord_eq_one (c := c) (RelName.Re_XX u v)
  have h' :
      Xneg1G (c := c) u * Xneg1G (c := c) v *
        (Xneg1G (c := c) (u + v))⁻¹ = 1 := by
    simpa [relWord, Xneg1, ofGen] using h
  have h'' :
      (Xneg1G (c := c) u * Xneg1G (c := c) v) *
        (Xneg1G (c := c) (u + v))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  exact (mul_inv_eq_one.mp h'')

lemma Yneg1_add (u v : ℂ) : Yneg1G (c := c) u * Yneg1G (c := c) v = Yneg1G (c := c) (u + v) := by
  have h := relWord_eq_one (c := c) (RelName.Re_YY u v)
  have h' :
      Yneg1G (c := c) u * Yneg1G (c := c) v *
        (Yneg1G (c := c) (u + v))⁻¹ = 1 := by
    simpa [relWord, Yneg1, ofGen] using h
  have h'' :
      (Yneg1G (c := c) u * Yneg1G (c := c) v) *
        (Yneg1G (c := c) (u + v))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  exact (mul_inv_eq_one.mp h'')

lemma X_im_add (e : IndexE c) (u v : ℂ) :
    XG (c := c) e u * XG (c := c) e v = XG (c := c) e (u + v) := by
  have h := relWord_eq_one (c := c) (RelName.Im_XX e u v)
  have h' :
      XG (c := c) e u * XG (c := c) e v * (XG (c := c) e (u + v))⁻¹ = 1 := by
    simpa [relWord, X, ofGen] using h
  have h'' :
      (XG (c := c) e u * XG (c := c) e v) * (XG (c := c) e (u + v))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  exact (mul_inv_eq_one.mp h'')

lemma Y_im_add (e : IndexE c) (u v : ℂ) :
    YG (c := c) e u * YG (c := c) e v = YG (c := c) e (u + v) := by
  have h := relWord_eq_one (c := c) (RelName.Im_YY e u v)
  have h' :
      YG (c := c) e u * YG (c := c) e v * (YG (c := c) e (u + v))⁻¹ = 1 := by
    simpa [relWord, Y, ofGen] using h
  have h'' :
      (YG (c := c) e u * YG (c := c) e v) * (YG (c := c) e (u + v))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  exact (mul_inv_eq_one.mp h'')

theorem Xneg1_zero : Xneg1G (c := c) 0 = 1 := by
  have h := Xneg1_add (c := c) 0 0
  have h' : Xneg1G (c := c) 0 * Xneg1G (c := c) 0 = Xneg1G (c := c) 0 * 1 := by
    simpa using h
  exact mul_left_cancel h'

theorem Yneg1_zero : Yneg1G (c := c) 0 = 1 := by
  have h := Yneg1_add (c := c) 0 0
  have h' : Yneg1G (c := c) 0 * Yneg1G (c := c) 0 = Yneg1G (c := c) 0 * 1 := by
    simpa using h
  exact mul_left_cancel h'

theorem X_im_zero (e : IndexE c) : XG (c := c) e 0 = 1 := by
  have h := X_im_add (c := c) e 0 0
  have h' : XG (c := c) e 0 * XG (c := c) e 0 = XG (c := c) e 0 * 1 := by
    simpa using h
  exact mul_left_cancel h'

theorem Y_im_zero (e : IndexE c) : YG (c := c) e 0 = 1 := by
  have h := Y_im_add (c := c) e 0 0
  have h' : YG (c := c) e 0 * YG (c := c) e 0 = YG (c := c) e 0 * 1 := by
    simpa using h
  exact mul_left_cancel h'

theorem Xneg1_inv (u : ℂ) : (Xneg1G (c := c) u)⁻¹ = Xneg1G (c := c) (-u) := by
  have h := Xneg1_add (c := c) u (-u)
  have h' : Xneg1G (c := c) u * Xneg1G (c := c) (-u) = 1 := by
    simpa [Xneg1_zero (c := c)] using h
  have h'' : Xneg1G (c := c) (-u) = (Xneg1G (c := c) u)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

theorem Yneg1_inv (u : ℂ) : (Yneg1G (c := c) u)⁻¹ = Yneg1G (c := c) (-u) := by
  have h := Yneg1_add (c := c) u (-u)
  have h' : Yneg1G (c := c) u * Yneg1G (c := c) (-u) = 1 := by
    simpa [Yneg1_zero (c := c)] using h
  have h'' : Yneg1G (c := c) (-u) = (Yneg1G (c := c) u)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

theorem X_im_inv (e : IndexE c) (u : ℂ) : (XG (c := c) e u)⁻¹ = XG (c := c) e (-u) := by
  have h := X_im_add (c := c) e u (-u)
  have h' : XG (c := c) e u * XG (c := c) e (-u) = 1 := by
    simpa [X_im_zero (c := c) e] using h
  have h'' : XG (c := c) e (-u) = (XG (c := c) e u)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

theorem Y_im_inv (e : IndexE c) (u : ℂ) : (YG (c := c) e u)⁻¹ = YG (c := c) e (-u) := by
  have h := Y_im_add (c := c) e u (-u)
  have h' : YG (c := c) e u * YG (c := c) e (-u) = 1 := by
    simpa [Y_im_zero (c := c) e] using h
  have h'' : YG (c := c) e (-u) = (YG (c := c) e u)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

lemma Re_XY_rel (s : ℂ) (t : ℂˣ) :
    Yneg1G (c := c) (-(t : ℂ)) * Xneg1G (c := c) s * Yneg1G (c := c) (t : ℂ) *
      Xneg1G (c := c) (-(t⁻¹ : ℂ)) * Yneg1G (c := c) (((t : ℂ) ^ 2) * s) *
        Xneg1G (c := c) (t⁻¹ : ℂ) = 1 := by
  have h := relWord_eq_one (c := c) (RelName.Re_XY s t)
  simpa [relWord, Xneg1, Yneg1, ofGen, mul_assoc, mul_inv_rev, Xneg1_inv, Yneg1_inv] using h

lemma Re_wX_rel (u : ℂ) :
    wNeg1OneG (c := c) * Xneg1G (c := c) u * (wNeg1OneG (c := c))⁻¹ * Yneg1G (c := c) u = 1 := by
  have h := relWord_eq_one (c := c) (RelName.Re_wX u)
  simpa [relWord, wNeg1OneG, wNeg1G, wNeg1One, wNeg1, Xneg1, Yneg1, ofGen, mul_assoc,
    Yneg1_inv] using h

lemma Re_wY_rel (u : ℂ) :
    wNeg1OneG (c := c) * Yneg1G (c := c) u * (wNeg1OneG (c := c))⁻¹ * Xneg1G (c := c) u = 1 := by
  have h := relWord_eq_one (c := c) (RelName.Re_wY u)
  simpa [relWord, wNeg1OneG, wNeg1G, wNeg1One, wNeg1, Xneg1, Yneg1, ofGen, mul_assoc,
    Xneg1_inv] using h

lemma Im_XY_rel (e : IndexE c) (s : ℂ) (t : ℂˣ) :
    YG (c := c) e (-(t : ℂ)) * XG (c := c) e s * YG (c := c) e (t : ℂ) *
      XG (c := c) e (-(t⁻¹ : ℂ) / cCoeff e.ℓ e.j) *
        YG (c := c) e ((cCoeff e.ℓ e.j) * ((t : ℂ)^2) * s) *
          XG (c := c) e ((t⁻¹ : ℂ) / cCoeff e.ℓ e.j) = 1 := by
  have h := relWord_eq_one (c := c) (RelName.Im_XY e s t)
  simpa [relWord, X, Y, ofGen, mul_assoc, mul_inv_rev, X_im_inv, Y_im_inv, neg_div', neg_neg]
    using h

lemma Im_wX_rel (e : IndexE c) (u : ℂ) :
    wImOneG (c := c) e * XG (c := c) e u * (wImOneG (c := c) e)⁻¹ *
      YG (c := c) e (u / cCoeff e.ℓ e.j) = 1 := by
  have h := relWord_eq_one (c := c) (RelName.Im_wX e u)
  simpa [relWord, wImOneG, wImG, wImOne, wIm, X, Y, ofGen, mul_assoc, Y_im_inv, neg_div',
    neg_neg] using h

lemma Im_wY_rel (e : IndexE c) (u : ℂ) :
    wImOneG (c := c) e * YG (c := c) e u * (wImOneG (c := c) e)⁻¹ *
      XG (c := c) e ((cCoeff e.ℓ e.j) * u) = 1 := by
  have h := relWord_eq_one (c := c) (RelName.Im_wY e u)
  simpa [relWord, wImOneG, wImG, wImOne, wIm, X, Y, ofGen, mul_assoc, X_im_inv, neg_div',
    neg_neg] using h

lemma U_w_X_rel (e : IndexE c) (u : ℂ) :
    wNeg1OneG (c := c) * XG (c := c) e u * (wNeg1OneG (c := c))⁻¹ *
      XG (c := c) (idx c (e.j - 1 - e.ℓ) e.j e.k)
        (((-1 : ℂ) ^ ((e.j - e.ℓ - 1) + 1)) * u) = 1 := by
  have h := relWord_eq_one (c := c) (RelName.U_w_X e u)
  have hpow :
      -(((-1 : ℂ) ^ (e.j - e.ℓ - 1)) * u) =
        ((-1 : ℂ) ^ ((e.j - e.ℓ - 1) + 1)) * u := by
    simpa using (neg_pow_mul (n := e.j - e.ℓ - 1) u)
  simpa [relWord, wNeg1OneG, wNeg1G, wNeg1One, wNeg1, X, Y, ofGen, mul_assoc, X_im_inv,
    hpow] using h

lemma U_w_Y_rel (e : IndexE c) (u : ℂ) :
    wNeg1OneG (c := c) * YG (c := c) e u * (wNeg1OneG (c := c))⁻¹ *
      YG (c := c) (idx c (e.j - 1 - e.ℓ) e.j e.k)
        (((-1 : ℂ) ^ ((e.j - e.ℓ - 1) + 1)) * u) = 1 := by
  have h := relWord_eq_one (c := c) (RelName.U_w_Y e u)
  have hpow :
      -(((-1 : ℂ) ^ (e.j - e.ℓ - 1)) * u) =
        ((-1 : ℂ) ^ ((e.j - e.ℓ - 1) + 1)) * u := by
    simpa using (neg_pow_mul (n := e.j - e.ℓ - 1) u)
  simpa [relWord, wNeg1OneG, wNeg1G, wNeg1One, wNeg1, X, Y, ofGen, mul_assoc, Y_im_inv,
    hpow] using h

/-! ## Larger structure statements (to be proved later) -/

def perfect_G_prop : Prop := commutator (G (c := c)) = ⊤

def H_normalizes_U_prop : Prop :=
  toralSubgroup (c := c) ≤ Subgroup.normalizer (unipotentSubgroup (c := c))

def G_eq_HU_prop : Prop :=
  (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)) = ⊤

def center_subset_H_prop : Prop :=
  Subgroup.center (G (c := c)) ≤ toralSubgroup (c := c)

lemma zerogenstrivial :
    Xneg1G (c := c) 0 = 1 ∧ Yneg1G (c := c) 0 = 1 ∧
      (∀ e : IndexE c, XG (c := c) e 0 = 1) ∧ (∀ e : IndexE c, YG (c := c) e 0 = 1) := by
  refine ⟨Xneg1_zero (c := c), Yneg1_zero (c := c), ?_, ?_⟩
  · intro e
    exact X_im_zero (c := c) e
  · intro e
    exact Y_im_zero (c := c) e

/-! ## Toral subgroup relations and conjugation formulas -/

@[simp] lemma H1_one : H1G (c := c) (1 : ℂˣ) = 1 := by
  have h := H1_mul (c := c) (1 : ℂˣ) 1
  have h' :
      H1G (c := c) (1 : ℂˣ) * H1G (c := c) (1 : ℂˣ) =
        H1G (c := c) (1 : ℂˣ) * 1 := by
    simpa using h
  exact mul_left_cancel h'

@[simp] lemma H2_one : H2G (c := c) (1 : ℂˣ) = 1 := by
  have h := H2_mul (c := c) (1 : ℂˣ) 1
  have h' :
      H2G (c := c) (1 : ℂˣ) * H2G (c := c) (1 : ℂˣ) =
        H2G (c := c) (1 : ℂˣ) * 1 := by
    simpa using h
  exact mul_left_cancel h'

@[simp] lemma H1_inv (s : ℂˣ) : (H1G (c := c) s)⁻¹ = H1G (c := c) (s⁻¹) := by
  have h := H1_mul (c := c) s s⁻¹
  have h' : H1G (c := c) s * H1G (c := c) (s⁻¹) = 1 := by
    simpa [H1_one (c := c)] using h
  have h'' : H1G (c := c) (s⁻¹) = (H1G (c := c) s)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

@[simp] lemma H2_inv (s : ℂˣ) : (H2G (c := c) s)⁻¹ = H2G (c := c) (s⁻¹) := by
  have h := H2_mul (c := c) s s⁻¹
  have h' : H2G (c := c) s * H2G (c := c) (s⁻¹) = 1 := by
    simpa [H2_one (c := c)] using h
  have h'' : H2G (c := c) (s⁻¹) = (H2G (c := c) s)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

lemma mem_toral_H1 (s : ℂˣ) : H1G (c := c) s ∈ toralSubgroup (c := c) := by
  refine Subgroup.subset_closure ?_
  exact Or.inl ⟨s, rfl⟩

lemma mem_toral_H2 (s : ℂˣ) : H2G (c := c) s ∈ toralSubgroup (c := c) := by
  refine Subgroup.subset_closure ?_
  exact Or.inr ⟨s, rfl⟩

lemma mem_unipotent_Xneg1 (u : ℂ) : Xneg1G (c := c) u ∈ unipotentSubgroup (c := c) := by
  refine Subgroup.subset_closure ?_
  exact Or.inl ⟨u, rfl⟩

lemma mem_unipotent_Yneg1 (u : ℂ) : Yneg1G (c := c) u ∈ unipotentSubgroup (c := c) := by
  refine Subgroup.subset_closure ?_
  exact Or.inr (Or.inl ⟨u, rfl⟩)

lemma mem_unipotent_X (e : IndexE c) (u : ℂ) : XG (c := c) e u ∈ unipotentSubgroup (c := c) := by
  refine Subgroup.subset_closure ?_
  exact Or.inr (Or.inr (Or.inl ⟨e, u, rfl⟩))

lemma mem_unipotent_Y (e : IndexE c) (u : ℂ) : YG (c := c) e u ∈ unipotentSubgroup (c := c) := by
  refine Subgroup.subset_closure ?_
  exact Or.inr (Or.inr (Or.inr ⟨e, u, rfl⟩))

lemma H1_conj_Xneg1 (s : ℂˣ) (u : ℂ) :
    H1G (c := c) s * Xneg1G (c := c) u * H1G (c := c) (s⁻¹)
      = Xneg1G (c := c) ((s : ℂ) * u) := by
  have h := relWord_eq_one (c := c) (RelName.Re_H1X s u)
  have h' :
      H1G (c := c) s * Xneg1G (c := c) u * (H1G (c := c) s)⁻¹ *
        (Xneg1G (c := c) ((s : ℂ) * u))⁻¹ = 1 := by
    simpa [relWord, H1, Xneg1, ofGen, mul_assoc] using h
  have h'' :
      (H1G (c := c) s * Xneg1G (c := c) u * (H1G (c := c) s)⁻¹) *
        (Xneg1G (c := c) ((s : ℂ) * u))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  simpa [H1_inv (c := c)] using (mul_inv_eq_one.mp h'')

lemma H2_conj_Xneg1 (s : ℂˣ) (u : ℂ) :
    H2G (c := c) s * Xneg1G (c := c) u * H2G (c := c) (s⁻¹)
      = Xneg1G (c := c) ((s⁻¹ : ℂ) * u) := by
  have h := relWord_eq_one (c := c) (RelName.Re_H2X s u)
  have h' :
      H2G (c := c) s * Xneg1G (c := c) u * (H2G (c := c) s)⁻¹ *
        (Xneg1G (c := c) ((s⁻¹ : ℂ) * u))⁻¹ = 1 := by
    simpa [relWord, H2, Xneg1, ofGen, mul_assoc] using h
  have h'' :
      (H2G (c := c) s * Xneg1G (c := c) u * (H2G (c := c) s)⁻¹) *
        (Xneg1G (c := c) ((s⁻¹ : ℂ) * u))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  simpa [H2_inv (c := c)] using (mul_inv_eq_one.mp h'')

lemma H1_conj_Yneg1 (s : ℂˣ) (u : ℂ) :
    H1G (c := c) s * Yneg1G (c := c) u * H1G (c := c) (s⁻¹)
      = Yneg1G (c := c) ((s⁻¹ : ℂ) * u) := by
  have h := relWord_eq_one (c := c) (RelName.Re_H1Y s u)
  have h' :
      H1G (c := c) s * Yneg1G (c := c) u * (H1G (c := c) s)⁻¹ *
        (Yneg1G (c := c) ((s⁻¹ : ℂ) * u))⁻¹ = 1 := by
    simpa [relWord, H1, Yneg1, ofGen, mul_assoc] using h
  have h'' :
      (H1G (c := c) s * Yneg1G (c := c) u * (H1G (c := c) s)⁻¹) *
        (Yneg1G (c := c) ((s⁻¹ : ℂ) * u))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  simpa [H1_inv (c := c)] using (mul_inv_eq_one.mp h'')

lemma H2_conj_Yneg1 (s : ℂˣ) (u : ℂ) :
    H2G (c := c) s * Yneg1G (c := c) u * H2G (c := c) (s⁻¹)
      = Yneg1G (c := c) ((s : ℂ) * u) := by
  have h := relWord_eq_one (c := c) (RelName.Re_H2Y s u)
  have h' :
      H2G (c := c) s * Yneg1G (c := c) u * (H2G (c := c) s)⁻¹ *
        (Yneg1G (c := c) ((s : ℂ) * u))⁻¹ = 1 := by
    simpa [relWord, H2, Yneg1, ofGen, mul_assoc] using h
  have h'' :
      (H2G (c := c) s * Yneg1G (c := c) u * (H2G (c := c) s)⁻¹) *
        (Yneg1G (c := c) ((s : ℂ) * u))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  simpa [H2_inv (c := c)] using (mul_inv_eq_one.mp h'')

lemma H1_conj_X (s : ℂˣ) (e : IndexE c) (u : ℂ) :
    H1G (c := c) s * XG (c := c) e u * H1G (c := c) (s⁻¹)
      = XG (c := c) e (((s : ℂ) ^ (e.ℓ + 1)) * u) := by
  have h := relWord_eq_one (c := c) (RelName.Im_H1X e s u)
  have h' :
      H1G (c := c) s * XG (c := c) e u * (H1G (c := c) s)⁻¹ *
        (XG (c := c) e (((s : ℂ) ^ (e.ℓ + 1)) * u))⁻¹ = 1 := by
    simpa [relWord, H1, X, ofGen, mul_assoc] using h
  have h'' :
      (H1G (c := c) s * XG (c := c) e u * (H1G (c := c) s)⁻¹) *
        (XG (c := c) e (((s : ℂ) ^ (e.ℓ + 1)) * u))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  simpa [H1_inv (c := c)] using (mul_inv_eq_one.mp h'')

lemma H2_conj_X (s : ℂˣ) (e : IndexE c) (u : ℂ) :
    H2G (c := c) s * XG (c := c) e u * H2G (c := c) (s⁻¹)
      = XG (c := c) e (((s : ℂ) ^ (e.j - e.ℓ)) * u) := by
  have h := relWord_eq_one (c := c) (RelName.Im_H2X e s u)
  have h' :
      H2G (c := c) s * XG (c := c) e u * (H2G (c := c) s)⁻¹ *
        (XG (c := c) e (((s : ℂ) ^ (e.j - e.ℓ)) * u))⁻¹ = 1 := by
    simpa [relWord, H2, X, ofGen, mul_assoc] using h
  have h'' :
      (H2G (c := c) s * XG (c := c) e u * (H2G (c := c) s)⁻¹) *
        (XG (c := c) e (((s : ℂ) ^ (e.j - e.ℓ)) * u))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  simpa [H2_inv (c := c)] using (mul_inv_eq_one.mp h'')

lemma H1_conj_Y (s : ℂˣ) (e : IndexE c) (u : ℂ) :
    H1G (c := c) s * YG (c := c) e u * H1G (c := c) (s⁻¹)
      = YG (c := c) e (((s⁻¹ : ℂ) ^ (e.ℓ + 1)) * u) := by
  have h := relWord_eq_one (c := c) (RelName.Im_H1Y e s u)
  have h' :
      H1G (c := c) s * YG (c := c) e u * (H1G (c := c) s)⁻¹ *
        (YG (c := c) e (((s⁻¹ : ℂ) ^ (e.ℓ + 1)) * u))⁻¹ = 1 := by
    simpa [relWord, H1, Y, ofGen, mul_assoc] using h
  have h'' :
      (H1G (c := c) s * YG (c := c) e u * (H1G (c := c) s)⁻¹) *
        (YG (c := c) e (((s⁻¹ : ℂ) ^ (e.ℓ + 1)) * u))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  simpa [H1_inv (c := c)] using (mul_inv_eq_one.mp h'')

lemma H2_conj_Y (s : ℂˣ) (e : IndexE c) (u : ℂ) :
    H2G (c := c) s * YG (c := c) e u * H2G (c := c) (s⁻¹)
      = YG (c := c) e (((s⁻¹ : ℂ) ^ (e.j - e.ℓ)) * u) := by
  have h := relWord_eq_one (c := c) (RelName.Im_H2Y e s u)
  have h' :
      H2G (c := c) s * YG (c := c) e u * (H2G (c := c) s)⁻¹ *
        (YG (c := c) e (((s⁻¹ : ℂ) ^ (e.j - e.ℓ)) * u))⁻¹ = 1 := by
    simpa [relWord, H2, Y, ofGen, mul_assoc] using h
  have h'' :
      (H2G (c := c) s * YG (c := c) e u * (H2G (c := c) s)⁻¹) *
        (YG (c := c) e (((s⁻¹ : ℂ) ^ (e.j - e.ℓ)) * u))⁻¹ = 1 := by
    simpa [mul_assoc] using h'
  simpa [H2_inv (c := c)] using (mul_inv_eq_one.mp h'')

lemma H1_conj_mem_unipotent (s : ℂˣ) {u : G (c := c)}
    (hu : u ∈ unipotentSubgroup (c := c)) :
    H1G (c := c) s * u * H1G (c := c) (s⁻¹) ∈ unipotentSubgroup (c := c) := by
  let Ugen : Set (G (c := c)) :=
    { g | (∃ u, g = Xneg1G (c := c) u)
      ∨ (∃ u, g = Yneg1G (c := c) u)
      ∨ (∃ e u, g = XG (c := c) e u)
      ∨ (∃ e u, g = YG (c := c) e u) }
  have hu' : u ∈ Subgroup.closure Ugen := by
    simpa [unipotentSubgroup, Ugen] using hu
  refine Subgroup.closure_induction (k := Ugen)
    (p := fun u _ =>
      H1G (c := c) s * u * H1G (c := c) (s⁻¹) ∈ unipotentSubgroup (c := c))
    ?gen ?one ?mul ?inv hu'
  · intro u hu
    rcases hu with ⟨u0, rfl⟩ | ⟨u0, rfl⟩ | ⟨e, u0, rfl⟩ | ⟨e, u0, rfl⟩
    ·
      have h := H1_conj_Xneg1 (c := c) s u0
      simpa using (h ▸ mem_unipotent_Xneg1 (c := c) ((s : ℂ) * u0))
    ·
      have h := H1_conj_Yneg1 (c := c) s u0
      simpa using (h ▸ mem_unipotent_Yneg1 (c := c) ((s⁻¹ : ℂ) * u0))
    ·
      have h := H1_conj_X (c := c) s e u0
      simpa using (h ▸ mem_unipotent_X (c := c) e (((s : ℂ) ^ (e.ℓ + 1)) * u0))
    ·
      have h := H1_conj_Y (c := c) s e u0
      simpa using (h ▸ mem_unipotent_Y (c := c) e (((s⁻¹ : ℂ) ^ (e.ℓ + 1)) * u0))
  · simpa [mul_assoc, H1_mul, H1_one] using (unipotentSubgroup (c := c)).one_mem
  · intro x y hx hy ihx ihy
    have hmem := (unipotentSubgroup (c := c)).mul_mem ihx ihy
    have hconj_mul :
        (H1G (c := c) s * x * H1G (c := c) (s⁻¹)) *
            (H1G (c := c) s * y * H1G (c := c) (s⁻¹)) =
          H1G (c := c) s * (x * y) * H1G (c := c) (s⁻¹) := by
      calc
        (H1G (c := c) s * x * H1G (c := c) (s⁻¹)) *
            (H1G (c := c) s * y * H1G (c := c) (s⁻¹)) =
            H1G (c := c) s * x * (H1G (c := c) (s⁻¹) * H1G (c := c) s) * y *
              H1G (c := c) (s⁻¹) := by simp [mul_assoc]
        _ = H1G (c := c) s * x * y * H1G (c := c) (s⁻¹) := by
              simp [H1_mul, H1_one, mul_assoc]
        _ = H1G (c := c) s * (x * y) * H1G (c := c) (s⁻¹) := by
              simp [mul_assoc]
    simpa [hconj_mul] using hmem
  · intro x hx ihx
    have hmem := (unipotentSubgroup (c := c)).inv_mem ihx
    have hconj_inv :
        (H1G (c := c) s * x * H1G (c := c) (s⁻¹))⁻¹ =
          H1G (c := c) s * x⁻¹ * H1G (c := c) (s⁻¹) := by
      simp [mul_assoc, mul_inv_rev, H1_inv]
    simpa [hconj_inv] using hmem

lemma H2_conj_mem_unipotent (s : ℂˣ) {u : G (c := c)}
    (hu : u ∈ unipotentSubgroup (c := c)) :
    H2G (c := c) s * u * H2G (c := c) (s⁻¹) ∈ unipotentSubgroup (c := c) := by
  let Ugen : Set (G (c := c)) :=
    { g | (∃ u, g = Xneg1G (c := c) u)
      ∨ (∃ u, g = Yneg1G (c := c) u)
      ∨ (∃ e u, g = XG (c := c) e u)
      ∨ (∃ e u, g = YG (c := c) e u) }
  have hu' : u ∈ Subgroup.closure Ugen := by
    simpa [unipotentSubgroup, Ugen] using hu
  refine Subgroup.closure_induction (k := Ugen)
    (p := fun u _ =>
      H2G (c := c) s * u * H2G (c := c) (s⁻¹) ∈ unipotentSubgroup (c := c))
    ?gen ?one ?mul ?inv hu'
  · intro u hu
    rcases hu with ⟨u0, rfl⟩ | ⟨u0, rfl⟩ | ⟨e, u0, rfl⟩ | ⟨e, u0, rfl⟩
    ·
      have h := H2_conj_Xneg1 (c := c) s u0
      simpa using (h ▸ mem_unipotent_Xneg1 (c := c) ((s⁻¹ : ℂ) * u0))
    ·
      have h := H2_conj_Yneg1 (c := c) s u0
      simpa using (h ▸ mem_unipotent_Yneg1 (c := c) ((s : ℂ) * u0))
    ·
      have h := H2_conj_X (c := c) s e u0
      simpa using (h ▸ mem_unipotent_X (c := c) e (((s : ℂ) ^ (e.j - e.ℓ)) * u0))
    ·
      have h := H2_conj_Y (c := c) s e u0
      simpa using (h ▸ mem_unipotent_Y (c := c) e (((s⁻¹ : ℂ) ^ (e.j - e.ℓ)) * u0))
  · simpa [mul_assoc, H2_mul, H2_one] using (unipotentSubgroup (c := c)).one_mem
  · intro x y hx hy ihx ihy
    have hmem := (unipotentSubgroup (c := c)).mul_mem ihx ihy
    have hconj_mul :
        (H2G (c := c) s * x * H2G (c := c) (s⁻¹)) *
            (H2G (c := c) s * y * H2G (c := c) (s⁻¹)) =
          H2G (c := c) s * (x * y) * H2G (c := c) (s⁻¹) := by
      calc
        (H2G (c := c) s * x * H2G (c := c) (s⁻¹)) *
            (H2G (c := c) s * y * H2G (c := c) (s⁻¹)) =
            H2G (c := c) s * x * (H2G (c := c) (s⁻¹) * H2G (c := c) s) * y *
              H2G (c := c) (s⁻¹) := by simp [mul_assoc]
        _ = H2G (c := c) s * x * y * H2G (c := c) (s⁻¹) := by
              simp [H2_mul, H2_one, mul_assoc]
        _ = H2G (c := c) s * (x * y) * H2G (c := c) (s⁻¹) := by
              simp [mul_assoc]
    simpa [hconj_mul] using hmem
  · intro x hx ihx
    have hmem := (unipotentSubgroup (c := c)).inv_mem ihx
    have hconj_inv :
        (H2G (c := c) s * x * H2G (c := c) (s⁻¹))⁻¹ =
          H2G (c := c) s * x⁻¹ * H2G (c := c) (s⁻¹) := by
      simp [mul_assoc, mul_inv_rev, H2_inv]
    simpa [hconj_inv] using hmem

variable {perfect_G_axiom : ∀ c : ℕ → ℕ, perfect_G_prop (c := c)}
include perfect_G_axiom

theorem perfect_G : commutator (G (c := c)) = ⊤ := by
  simpa [perfect_G_prop] using perfect_G_axiom (c := c)
omit perfect_G_axiom

def toralSubgroup_abelian_prop : Prop :=
  ∀ {x y : G (c := c)}, x ∈ toralSubgroup (c := c) →
    y ∈ toralSubgroup (c := c) → x * y = y * x

theorem toralSubgroup_abelian : toralSubgroup_abelian_prop (c := c) := by
  intro x y hx hy
  let S : Set (G (c := c)) :=
    { g | (∃ s, g = H1G (c := c) s) ∨ (∃ s, g = H2G (c := c) s) }
  -- show every x in the closure of S commutes with every y in the closure of S
  have hcomm :
      ∀ x ∈ toralSubgroup (c := c),
        ∀ y ∈ toralSubgroup (c := c), x * y = y * x := by
    intro x hx
    -- closure induction on x
    have hx' : x ∈ Subgroup.closure S := by
      simpa [toralSubgroup, S] using hx
    refine Subgroup.closure_induction (k := S)
      (p := fun x _ => ∀ y ∈ toralSubgroup (c := c), x * y = y * x)
      ?gen ?one ?mul ?inv hx'
    · intro x hx y hy
      have hy' : y ∈ Subgroup.closure S := by
        simpa [toralSubgroup, S] using hy
      -- closure induction on y
      refine Subgroup.closure_induction (k := S)
        (p := fun y _ => x * y = y * x)
        ?geny ?oney ?muly ?invy hy'
      · intro y hy
        rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
        · rcases hy with ⟨t, rfl⟩ | ⟨t, rfl⟩
          · -- H1/H1
            calc
              H1G (c := c) s * H1G (c := c) t =
                  H1G (c := c) (s * t) := H1_mul (c := c) s t
              _ = H1G (c := c) (t * s) := by simpa [mul_comm]
              _ = H1G (c := c) t * H1G (c := c) s := (H1_mul (c := c) t s).symm
          · -- H1/H2
            simpa using (H1H2_comm (c := c) s t)
        · rcases hy with ⟨t, rfl⟩ | ⟨t, rfl⟩
          · -- H2/H1
            simpa using (H1H2_comm (c := c) t s).symm
          · -- H2/H2
            calc
              H2G (c := c) s * H2G (c := c) t =
                  H2G (c := c) (s * t) := H2_mul (c := c) s t
              _ = H2G (c := c) (t * s) := by simpa [mul_comm]
              _ = H2G (c := c) t * H2G (c := c) s := (H2_mul (c := c) t s).symm
      · simp [mul_assoc]
      · intro y z hy hz ihy ihz
        calc
          x * (y * z) = (x * y) * z := by simp [mul_assoc]
          _ = (y * x) * z := by simpa [ihy] using rfl
          _ = y * (x * z) := by simp [mul_assoc]
          _ = y * (z * x) := by simpa [ihz] using rfl
          _ = (y * z) * x := by simp [mul_assoc]
      · intro y hy ihy
        have hxy := ihy
        have h1 := congrArg (fun z => z * y⁻¹) hxy
        have h2 := congrArg (fun z => y⁻¹ * z) h1
        simpa [mul_assoc] using h2.symm
    · intro y hy
      simp [mul_assoc]
    · intro x y hx hy ihx ihy
      intro z hz
      calc
        (x * y) * z = x * (y * z) := by simp [mul_assoc]
        _ = x * (z * y) := by simpa [ihy z hz] using rfl
        _ = (x * z) * y := by simp [mul_assoc]
        _ = (z * x) * y := by simpa [ihx z hz] using rfl
        _ = z * (x * y) := by simp [mul_assoc]
    · intro x hx ihx
      intro y hy
      have hxy := ihx y hy
      have h1 := congrArg (fun z => x⁻¹ * z) hxy
      have h2 := congrArg (fun z => z * x⁻¹) h1
      simpa [mul_assoc] using h2.symm
  exact hcomm x hx y hy

lemma H1_mem_normalizer (s : ℂˣ) :
    H1G (c := c) s ∈ Subgroup.normalizer (unipotentSubgroup (c := c)) := by
  refine (Subgroup.mem_normalizer_iff (H := unipotentSubgroup (c := c))).2 ?_
  intro u
  constructor
  · intro hu
    simpa [H1_inv] using (H1_conj_mem_unipotent (c := c) s hu)
  · intro hu
    have hu' :
        H1G (c := c) (s⁻¹) *
            (H1G (c := c) s * u * H1G (c := c) (s⁻¹)) *
            H1G (c := c) s ∈ unipotentSubgroup (c := c) :=
      (by
        have := H1_conj_mem_unipotent (c := c) (s := s⁻¹) hu
        simpa [H1_inv] using this)
    have hconj :
        H1G (c := c) (s⁻¹) *
            (H1G (c := c) s * u * H1G (c := c) (s⁻¹)) *
            H1G (c := c) s = u := by
      calc
        H1G (c := c) (s⁻¹) *
            (H1G (c := c) s * u * H1G (c := c) (s⁻¹)) *
            H1G (c := c) s =
            (H1G (c := c) (s⁻¹) * H1G (c := c) s) * u *
              (H1G (c := c) (s⁻¹) * H1G (c := c) s) := by
                simp [mul_assoc]
        _ = u := by simp [H1_mul, H1_one, mul_assoc]
    simpa [hconj] using hu'

lemma H2_mem_normalizer (s : ℂˣ) :
    H2G (c := c) s ∈ Subgroup.normalizer (unipotentSubgroup (c := c)) := by
  refine (Subgroup.mem_normalizer_iff (H := unipotentSubgroup (c := c))).2 ?_
  intro u
  constructor
  · intro hu
    simpa [H2_inv] using (H2_conj_mem_unipotent (c := c) s hu)
  · intro hu
    have hu' :
        H2G (c := c) (s⁻¹) *
            (H2G (c := c) s * u * H2G (c := c) (s⁻¹)) *
            H2G (c := c) s ∈ unipotentSubgroup (c := c) :=
      (by
        have := H2_conj_mem_unipotent (c := c) (s := s⁻¹) hu
        simpa [H2_inv] using this)
    have hconj :
        H2G (c := c) (s⁻¹) *
            (H2G (c := c) s * u * H2G (c := c) (s⁻¹)) *
            H2G (c := c) s = u := by
      calc
        H2G (c := c) (s⁻¹) *
            (H2G (c := c) s * u * H2G (c := c) (s⁻¹)) *
            H2G (c := c) s =
            (H2G (c := c) (s⁻¹) * H2G (c := c) s) * u *
              (H2G (c := c) (s⁻¹) * H2G (c := c) s) := by
                simp [mul_assoc]
        _ = u := by simp [H2_mul, H2_one, mul_assoc]
    simpa [hconj] using hu'

theorem H_normalizes_U :
    toralSubgroup (c := c) ≤ Subgroup.normalizer (unipotentSubgroup (c := c)) := by
  refine (Subgroup.closure_le (K := Subgroup.normalizer (unipotentSubgroup (c := c)))).2 ?_
  intro g hg
  rcases hg with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact H1_mem_normalizer (c := c) s
  · exact H2_mem_normalizer (c := c) s

lemma commute_of_HU {h u : G (c := c)}
    (hh : h ∈ toralSubgroup (c := c)) (hu : u ∈ unipotentSubgroup (c := c)) :
    ∃ u' ∈ unipotentSubgroup (c := c), u * h = h * u' := by
  have hnorm : h ∈ Subgroup.normalizer (unipotentSubgroup (c := c)) :=
    H_normalizes_U (c := c) hh
  have hiff :=
    (Subgroup.mem_normalizer_iff'' (H := unipotentSubgroup (c := c))).1 hnorm u
  refine ⟨h⁻¹ * u * h, (hiff).1 hu, ?_⟩
  simp [mul_assoc]

theorem G_eq_HU :
    (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)) = ⊤ := by
  apply le_antisymm le_top
  -- show ⊤ ≤ toralSubgroup ⊔ unipotentSubgroup by generators
  have hsubset :
      Set.range (of (c := c)) ⊆
        (↑((toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c))) :
          Set (G (c := c))) := by
    rintro g ⟨gen, rfl⟩
    cases gen with
    | H1 s =>
        simpa [H1G, of] using
          (Subgroup.mem_sup_left (mem_toral_H1 (c := c) s) :
            H1G (c := c) s ∈ (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)))
    | H2 s =>
        simpa [H2G, of] using
          (Subgroup.mem_sup_left (mem_toral_H2 (c := c) s) :
            H2G (c := c) s ∈ (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)))
    | Xneg1 u =>
        simpa [Xneg1G, of] using
          (Subgroup.mem_sup_right (mem_unipotent_Xneg1 (c := c) u) :
            Xneg1G (c := c) u ∈ (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)))
    | Yneg1 u =>
        simpa [Yneg1G, of] using
          (Subgroup.mem_sup_right (mem_unipotent_Yneg1 (c := c) u) :
            Yneg1G (c := c) u ∈ (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)))
    | X e u =>
        simpa [XG, of] using
          (Subgroup.mem_sup_right (mem_unipotent_X (c := c) e u) :
            XG (c := c) e u ∈ (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)))
    | Y e u =>
        simpa [YG, of] using
          (Subgroup.mem_sup_right (mem_unipotent_Y (c := c) e u) :
            YG (c := c) e u ∈ (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)))
  have hclosure :
      Subgroup.closure (Set.range (of (c := c))) ≤
        (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)) :=
    (Subgroup.closure_le (K := (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)))).2 hsubset
  -- closure of generators is top
  have hgen :
      Subgroup.closure (Set.range (of (c := c))) =
        (⊤ : Subgroup (G (c := c))) := by
    simpa [of] using
      (PresentedGroup.closure_range_of (rels := rels (c := c)))
  have htop :
      (⊤ : Subgroup (G (c := c))) ≤
        (toralSubgroup (c := c)) ⊔ (unipotentSubgroup (c := c)) := by
    -- rewrite the goal to the closure statement
    rw [← hgen]
    exact hclosure
  exact htop

variable {center_subset_H_axiom : ∀ c : ℕ → ℕ, center_subset_H_prop (c := c)}
include center_subset_H_axiom

theorem center_subset_H :
    Subgroup.center (G (c := c)) ≤ toralSubgroup (c := c) := by
  simpa [center_subset_H_prop] using center_subset_H_axiom (c := c)
omit center_subset_H_axiom

end Gm

/-! ## Unipotent generators (for F(m) and S(m)) -/

inductive GenU (c : ℕ → ℕ) where
  | Xneg1 : ℂ → GenU c
  | Yneg1 : ℂ → GenU c
  | X : IndexE c → ℂ → GenU c
  | Y : IndexE c → ℂ → GenU c
deriving DecidableEq

abbrev FGU (c : ℕ → ℕ) := FreeGroup (GenU c)

/-! ## The field commutator group F(m) -/

namespace Fm

variable {c : ℕ → ℕ}

def ofGen (g : GenU c) : FGU c := FreeGroup.of g

def Xneg1 (u : ℂ) : FGU c := ofGen (GenU.Xneg1 u)
def Yneg1 (u : ℂ) : FGU c := ofGen (GenU.Yneg1 u)
def X (e : IndexE c) (u : ℂ) : FGU c := ofGen (GenU.X e u)
def Y (e : IndexE c) (u : ℂ) : FGU c := ofGen (GenU.Y e u)

def comm (a b : FGU c) : FGU c := a * b * a⁻¹ * b⁻¹

inductive RelName (c : ℕ → ℕ)
  | Re_XX (u v : ℂ)
  | Re_YY (u v : ℂ)
  | Im_XX (e : IndexE c) (u v : ℂ)
  | Im_YY (e : IndexE c) (u v : ℂ)
  | U_Xneg1_X (j k : ℕ) (u v : ℂ)
  | U_Yneg1_Y (j k : ℕ) (u v : ℂ)
  | U_Yneg1_X0 (j k : ℕ) (u v : ℂ)
  | U_Xneg1_Y0 (j k : ℕ) (u v : ℂ)
  | U_comm_XY (e f : IndexE c) (h : commCond (c := c) e f) (u v : ℂ)
  | U_XY_j2a (k : ℕ) (u v : ℂ)
  | U_XY_j2b (k : ℕ) (u v : ℂ)

def relWord : RelName c → FGU c
  | RelName.Re_XX u v =>
      Xneg1 (-u - v) * Xneg1 u * Xneg1 v
  | RelName.Re_YY u v =>
      Yneg1 (-u - v) * Yneg1 u * Yneg1 v
  | RelName.Im_XX e u v =>
      X e (-u - v) * X e u * X e v
  | RelName.Im_YY e u v =>
      Y e (-u - v) * Y e u * Y e v
  | RelName.U_Xneg1_X j k u v =>
      comm (Xneg1 u) (X (idx c (j - 1) j k) v)
  | RelName.U_Yneg1_Y j k u v =>
      comm (Yneg1 u) (Y (idx c (j - 1) j k) v)
  | RelName.U_Yneg1_X0 j k u v =>
      comm (Yneg1 u) (X (idx c 0 j k) v)
  | RelName.U_Xneg1_Y0 j k u v =>
      comm (Xneg1 u) (Y (idx c 0 j k) v)
  | RelName.U_comm_XY e f _ u v =>
      comm (X e u) (Y f v)
  | RelName.U_XY_j2a k u v =>
      Xneg1 (-u * v) * comm (X (idx c 1 2 k) u) (Y (idx c 0 2 k) v)
  | RelName.U_XY_j2b k u v =>
      Yneg1 (-u * v) * comm (X (idx c 0 2 k) u) (Y (idx c 1 2 k) v)

def rels : Set (FGU c) := Set.range (relWord (c := c))

abbrev F : Type := PresentedGroup (rels (c := c))

def of : GenU c → F (c := c) := PresentedGroup.of (rels := rels (c := c))

def Xneg1F (u : ℂ) : F (c := c) := of (GenU.Xneg1 u)
def Yneg1F (u : ℂ) : F (c := c) := of (GenU.Yneg1 u)
def XF (e : IndexE c) (u : ℂ) : F (c := c) := of (GenU.X e u)
def YF (e : IndexE c) (u : ℂ) : F (c := c) := of (GenU.Y e u)

lemma relWord_eq_one (r : RelName c) :
    PresentedGroup.mk (rels (c := c)) (relWord (c := c) r) = 1 := by
  apply PresentedGroup.one_of_mem
  exact ⟨r, rfl⟩

-- Additivity-style consequences of the defining relations (in inverse form).
lemma Xneg1_add (u v : ℂ) :
    Xneg1F (c := c) u * Xneg1F (c := c) v = (Xneg1F (c := c) (-u - v))⁻¹ := by
  have h := relWord_eq_one (c := c) (RelName.Re_XX u v)
  have h' :
      Xneg1F (c := c) (-u - v) * (Xneg1F (c := c) u * Xneg1F (c := c) v) = 1 := by
    simpa [relWord, Xneg1F, Xneg1, of, ofGen, PresentedGroup.of, mul_assoc] using h
  exact (mul_eq_one_iff_eq_inv').1 h'

lemma Yneg1_add (u v : ℂ) :
    Yneg1F (c := c) u * Yneg1F (c := c) v = (Yneg1F (c := c) (-u - v))⁻¹ := by
  have h := relWord_eq_one (c := c) (RelName.Re_YY u v)
  have h' :
      Yneg1F (c := c) (-u - v) * (Yneg1F (c := c) u * Yneg1F (c := c) v) = 1 := by
    simpa [relWord, Yneg1F, Yneg1, of, ofGen, PresentedGroup.of, mul_assoc] using h
  exact (mul_eq_one_iff_eq_inv').1 h'

lemma X_im_add (e : IndexE c) (u v : ℂ) :
    XF (c := c) e u * XF (c := c) e v = (XF (c := c) e (-u - v))⁻¹ := by
  have h := relWord_eq_one (c := c) (RelName.Im_XX e u v)
  have h' :
      XF (c := c) e (-u - v) * (XF (c := c) e u * XF (c := c) e v) = 1 := by
    simpa [relWord, XF, X, of, ofGen, PresentedGroup.of, mul_assoc] using h
  exact (mul_eq_one_iff_eq_inv').1 h'

lemma Y_im_add (e : IndexE c) (u v : ℂ) :
    YF (c := c) e u * YF (c := c) e v = (YF (c := c) e (-u - v))⁻¹ := by
  have h := relWord_eq_one (c := c) (RelName.Im_YY e u v)
  have h' :
      YF (c := c) e (-u - v) * (YF (c := c) e u * YF (c := c) e v) = 1 := by
    simpa [relWord, YF, Y, of, ofGen, PresentedGroup.of, mul_assoc] using h
  exact (mul_eq_one_iff_eq_inv').1 h'

abbrev Cadd := Multiplicative ℂ

def Uplus_neg1 : Subgroup (F (c := c)) :=
  Subgroup.closure (Set.range (Xneg1F (c := c)))

def Uminus_neg1 : Subgroup (F (c := c)) :=
  Subgroup.closure (Set.range (Yneg1F (c := c)))

def Uplus (e : IndexE c) : Subgroup (F (c := c)) :=
  Subgroup.closure (Set.range (fun u : ℂ => XF (c := c) e u))

def Uminus (e : IndexE c) : Subgroup (F (c := c)) :=
  Subgroup.closure (Set.range (fun u : ℂ => YF (c := c) e u))

variable {nontrivial_axiom : ∀ c : ℕ → ℕ, Nontrivial (F (c := c))}
include nontrivial_axiom

theorem nontrivial_F : Nontrivial (F (c := c)) :=
  nontrivial_axiom (c := c)
omit nontrivial_axiom

variable {phi_neg1 : ∀ c : ℕ → ℕ, Cadd →* F (c := c)}
variable {phi_neg1_spec :
    ∀ c : ℕ → ℕ, ∀ u : ℂ,
      phi_neg1 (c := c) (Multiplicative.ofAdd u) = Xneg1F (c := c) u}
variable {phi_neg1_range_axiom :
    ∀ c : ℕ → ℕ, (phi_neg1 (c := c)).range = Uplus_neg1 (c := c)}
variable {phi_neg1_injective_axiom :
    ∀ c : ℕ → ℕ, Function.Injective (phi_neg1 (c := c))}

variable {phi_im : ∀ c : ℕ → ℕ, IndexE c → Cadd →* F (c := c)}
variable {phi_im_spec :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, ∀ u : ℂ,
      phi_im (c := c) e (Multiplicative.ofAdd u) = XF (c := c) e u}
variable {phi_im_range_axiom :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, (phi_im (c := c) e).range = Uplus (c := c) e}
variable {phi_im_injective_axiom :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, Function.Injective (phi_im (c := c) e)}

variable {Uplus_neg1_nontrivial_axiom :
    ∀ c : ℕ → ℕ, Nontrivial (Uplus_neg1 (c := c))}
variable {Uplus_nontrivial_axiom :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, Nontrivial (Uplus (c := c) e)}

include phi_neg1_range_axiom
theorem phi_neg1_range :
    (phi_neg1 (c := c)).range = Uplus_neg1 (c := c) :=
  phi_neg1_range_axiom (c := c)
omit phi_neg1_range_axiom

include phi_im_range_axiom
theorem phi_im_range (e : IndexE c) :
    (phi_im (c := c) e).range = Uplus (c := c) e :=
  phi_im_range_axiom (c := c) e
omit phi_im_range_axiom

include phi_neg1_injective_axiom
theorem phi_neg1_injective : Function.Injective (phi_neg1 (c := c)) :=
  phi_neg1_injective_axiom (c := c)
omit phi_neg1_injective_axiom

include phi_im_injective_axiom
theorem phi_im_injective (e : IndexE c) : Function.Injective (phi_im (c := c) e) :=
  phi_im_injective_axiom (c := c) e
omit phi_im_injective_axiom

include Uplus_neg1_nontrivial_axiom
theorem Uplus_neg1_nontrivial : Nontrivial (Uplus_neg1 (c := c)) :=
  Uplus_neg1_nontrivial_axiom (c := c)
omit Uplus_neg1_nontrivial_axiom

include Uplus_nontrivial_axiom
theorem Uplus_nontrivial (e : IndexE c) : Nontrivial (Uplus (c := c) e) :=
  Uplus_nontrivial_axiom (c := c) e
omit Uplus_nontrivial_axiom

end Fm

/-! ## The Steinberg group S(m) -/

namespace Sm

variable {c : ℕ → ℕ}

def ofGen (g : GenU c) : FGU c := FreeGroup.of g

def Xneg1 (u : ℂ) : FGU c := ofGen (GenU.Xneg1 u)
def Yneg1 (u : ℂ) : FGU c := ofGen (GenU.Yneg1 u)
def X (e : IndexE c) (u : ℂ) : FGU c := ofGen (GenU.X e u)
def Y (e : IndexE c) (u : ℂ) : FGU c := ofGen (GenU.Y e u)

def comm (a b : FGU c) : FGU c := a * b * a⁻¹ * b⁻¹

def wNeg1 (s : ℂˣ) : FGU c :=
  Xneg1 (s : ℂ) * Yneg1 (-(s⁻¹ : ℂ)) * Xneg1 (s : ℂ)

def wNeg1One : FGU c := wNeg1 (c := c) 1

def wIm (e : IndexE c) (s : ℂˣ) : FGU c :=
  X e (s : ℂ) * Y e (-(s⁻¹ : ℂ) / cCoeff e.ℓ e.j) * X e (s : ℂ)

def wImOne (e : IndexE c) : FGU c := wIm (c := c) e 1

inductive RelName (c : ℕ → ℕ)
  | Re_XX (u v : ℂ)
  | Re_YY (u v : ℂ)
  | Im_XX (e : IndexE c) (u v : ℂ)
  | Im_YY (e : IndexE c) (u v : ℂ)
  | U_Xneg1_X (j k : ℕ) (u v : ℂ)
  | U_Yneg1_Y (j k : ℕ) (u v : ℂ)
  | U_Yneg1_X0 (j k : ℕ) (u v : ℂ)
  | U_Xneg1_Y0 (j k : ℕ) (u v : ℂ)
  | U_comm_XY (e f : IndexE c) (h : commCond (c := c) e f) (u v : ℂ)
  | U_XY_j2a (k : ℕ) (u v : ℂ)
  | U_XY_j2b (k : ℕ) (u v : ℂ)
  | Re_XY (s : ℂ) (t : ℂˣ)
  | Re_wX (u : ℂ)
  | Re_wY (u : ℂ)
  | Im_XY (e : IndexE c) (s : ℂ) (t : ℂˣ)
  | Im_wX (e : IndexE c) (u : ℂ)
  | Im_wY (e : IndexE c) (u : ℂ)
  | U_w_X (e : IndexE c) (u : ℂ)
  | U_w_Y (e : IndexE c) (u : ℂ)

def relWord : RelName c → FGU c
  | RelName.Re_XX u v =>
      (Xneg1 (u + v))⁻¹ * Xneg1 u * Xneg1 v
  | RelName.Re_YY u v =>
      (Yneg1 (u + v))⁻¹ * Yneg1 u * Yneg1 v
  | RelName.Im_XX e u v =>
      (X e (u + v))⁻¹ * X e u * X e v
  | RelName.Im_YY e u v =>
      (Y e (u + v))⁻¹ * Y e u * Y e v
  | RelName.U_Xneg1_X j k u v =>
      comm (Xneg1 u) (X (idx c (j - 1) j k) v)
  | RelName.U_Yneg1_Y j k u v =>
      comm (Yneg1 u) (Y (idx c (j - 1) j k) v)
  | RelName.U_Yneg1_X0 j k u v =>
      comm (Yneg1 u) (X (idx c 0 j k) v)
  | RelName.U_Xneg1_Y0 j k u v =>
      comm (Xneg1 u) (Y (idx c 0 j k) v)
  | RelName.U_comm_XY e f _ u v =>
      comm (X e u) (Y f v)
  | RelName.U_XY_j2a k u v =>
      Xneg1 (-u * v) * comm (X (idx c 1 2 k) u) (Y (idx c 0 2 k) v)
  | RelName.U_XY_j2b k u v =>
      Yneg1 (-u * v) * comm (X (idx c 0 2 k) u) (Y (idx c 1 2 k) v)
  | RelName.Re_XY s t =>
      Yneg1 (-(t : ℂ)) * Xneg1 s * Yneg1 (t : ℂ) *
        Xneg1 (-(t⁻¹ : ℂ)) * Yneg1 (((t : ℂ)^2) * s) * Xneg1 (t⁻¹ : ℂ)
  | RelName.Re_wX u =>
      wNeg1One (c := c) * Xneg1 u * (wNeg1One (c := c))⁻¹ * Yneg1 u
  | RelName.Re_wY u =>
      wNeg1One (c := c) * Yneg1 u * (wNeg1One (c := c))⁻¹ * Xneg1 u
  | RelName.Im_XY e s t =>
      Y e (-(t : ℂ)) * X e s * Y e (t : ℂ) *
        X e (-(t⁻¹ : ℂ) / cCoeff e.ℓ e.j) *
        Y e ((cCoeff e.ℓ e.j) * ((t : ℂ)^2) * s) *
        X e ((t⁻¹ : ℂ) / cCoeff e.ℓ e.j)
  | RelName.Im_wX e u =>
      wImOne (c := c) e * X e u * (wImOne (c := c) e)⁻¹ *
        Y e (u / cCoeff e.ℓ e.j)
  | RelName.Im_wY e u =>
      wImOne (c := c) e * Y e u * (wImOne (c := c) e)⁻¹ *
        X e ((cCoeff e.ℓ e.j) * u)
  | RelName.U_w_X e u =>
      wNeg1One (c := c) * X e u * (wNeg1One (c := c))⁻¹ *
        X (idx c (e.j - 1 - e.ℓ) e.j e.k)
          (((-1 : ℂ) ^ ((e.j - e.ℓ - 1) + 1)) * u)
  | RelName.U_w_Y e u =>
      wNeg1One (c := c) * Y e u * (wNeg1One (c := c))⁻¹ *
        Y (idx c (e.j - 1 - e.ℓ) e.j e.k)
          (((-1 : ℂ) ^ ((e.j - e.ℓ - 1) + 1)) * u)

def rels : Set (FGU c) := Set.range (relWord (c := c))

abbrev S : Type := PresentedGroup (rels (c := c))

def of : GenU c → S (c := c) := PresentedGroup.of (rels := rels (c := c))

def Xneg1S (u : ℂ) : S (c := c) := of (GenU.Xneg1 u)
def Yneg1S (u : ℂ) : S (c := c) := of (GenU.Yneg1 u)
def XS (e : IndexE c) (u : ℂ) : S (c := c) := of (GenU.X e u)
def YS (e : IndexE c) (u : ℂ) : S (c := c) := of (GenU.Y e u)

lemma relWord_eq_one (r : RelName c) :
    PresentedGroup.mk (rels (c := c)) (relWord (c := c) r) = 1 := by
  apply PresentedGroup.one_of_mem
  exact ⟨r, rfl⟩

lemma Xneg1_add (u v : ℂ) : Xneg1S (c := c) u * Xneg1S (c := c) v = Xneg1S (c := c) (u + v) := by
  have h := relWord_eq_one (c := c) (RelName.Re_XX u v)
  have h' :
      (Xneg1S (c := c) (u + v))⁻¹ * (Xneg1S (c := c) u * Xneg1S (c := c) v) = 1 := by
    simpa [relWord, Xneg1S, Xneg1, of, ofGen, PresentedGroup.of, mul_assoc] using h
  have h'' : Xneg1S (c := c) (u + v) = Xneg1S (c := c) u * Xneg1S (c := c) v :=
    (inv_mul_eq_one.mp h')
  exact h''.symm

lemma Yneg1_add (u v : ℂ) : Yneg1S (c := c) u * Yneg1S (c := c) v = Yneg1S (c := c) (u + v) := by
  have h := relWord_eq_one (c := c) (RelName.Re_YY u v)
  have h' :
      (Yneg1S (c := c) (u + v))⁻¹ * (Yneg1S (c := c) u * Yneg1S (c := c) v) = 1 := by
    simpa [relWord, Yneg1S, Yneg1, of, ofGen, PresentedGroup.of, mul_assoc] using h
  have h'' : Yneg1S (c := c) (u + v) = Yneg1S (c := c) u * Yneg1S (c := c) v :=
    (inv_mul_eq_one.mp h')
  exact h''.symm

lemma X_im_add (e : IndexE c) (u v : ℂ) :
    XS (c := c) e u * XS (c := c) e v = XS (c := c) e (u + v) := by
  have h := relWord_eq_one (c := c) (RelName.Im_XX e u v)
  have h' :
      (XS (c := c) e (u + v))⁻¹ * (XS (c := c) e u * XS (c := c) e v) = 1 := by
    simpa [relWord, XS, X, of, ofGen, PresentedGroup.of, mul_assoc] using h
  have h'' : XS (c := c) e (u + v) = XS (c := c) e u * XS (c := c) e v :=
    (inv_mul_eq_one.mp h')
  exact h''.symm

lemma Y_im_add (e : IndexE c) (u v : ℂ) :
    YS (c := c) e u * YS (c := c) e v = YS (c := c) e (u + v) := by
  have h := relWord_eq_one (c := c) (RelName.Im_YY e u v)
  have h' :
      (YS (c := c) e (u + v))⁻¹ * (YS (c := c) e u * YS (c := c) e v) = 1 := by
    simpa [relWord, YS, Y, of, ofGen, PresentedGroup.of, mul_assoc] using h
  have h'' : YS (c := c) e (u + v) = YS (c := c) e u * YS (c := c) e v :=
    (inv_mul_eq_one.mp h')
  exact h''.symm

theorem Xneg1_zero : Xneg1S (c := c) 0 = 1 := by
  have h := Xneg1_add (c := c) 0 0
  have h' : Xneg1S (c := c) 0 * Xneg1S (c := c) 0 = Xneg1S (c := c) 0 * 1 := by
    simpa using h
  exact mul_left_cancel h'

theorem Yneg1_zero : Yneg1S (c := c) 0 = 1 := by
  have h := Yneg1_add (c := c) 0 0
  have h' : Yneg1S (c := c) 0 * Yneg1S (c := c) 0 = Yneg1S (c := c) 0 * 1 := by
    simpa using h
  exact mul_left_cancel h'

theorem X_im_zero (e : IndexE c) : XS (c := c) e 0 = 1 := by
  have h := X_im_add (c := c) e 0 0
  have h' : XS (c := c) e 0 * XS (c := c) e 0 = XS (c := c) e 0 * 1 := by
    simpa using h
  exact mul_left_cancel h'

theorem Y_im_zero (e : IndexE c) : YS (c := c) e 0 = 1 := by
  have h := Y_im_add (c := c) e 0 0
  have h' : YS (c := c) e 0 * YS (c := c) e 0 = YS (c := c) e 0 * 1 := by
    simpa using h
  exact mul_left_cancel h'

theorem Xneg1_inv (u : ℂ) : (Xneg1S (c := c) u)⁻¹ = Xneg1S (c := c) (-u) := by
  have h := Xneg1_add (c := c) u (-u)
  have h' : Xneg1S (c := c) u * Xneg1S (c := c) (-u) = 1 := by
    simpa [Xneg1_zero (c := c)] using h
  have h'' : Xneg1S (c := c) (-u) = (Xneg1S (c := c) u)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

theorem Yneg1_inv (u : ℂ) : (Yneg1S (c := c) u)⁻¹ = Yneg1S (c := c) (-u) := by
  have h := Yneg1_add (c := c) u (-u)
  have h' : Yneg1S (c := c) u * Yneg1S (c := c) (-u) = 1 := by
    simpa [Yneg1_zero (c := c)] using h
  have h'' : Yneg1S (c := c) (-u) = (Yneg1S (c := c) u)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

theorem X_im_inv (e : IndexE c) (u : ℂ) : (XS (c := c) e u)⁻¹ = XS (c := c) e (-u) := by
  have h := X_im_add (c := c) e u (-u)
  have h' : XS (c := c) e u * XS (c := c) e (-u) = 1 := by
    simpa [X_im_zero (c := c) e] using h
  have h'' : XS (c := c) e (-u) = (XS (c := c) e u)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

theorem Y_im_inv (e : IndexE c) (u : ℂ) : (YS (c := c) e u)⁻¹ = YS (c := c) e (-u) := by
  have h := Y_im_add (c := c) e u (-u)
  have h' : YS (c := c) e u * YS (c := c) e (-u) = 1 := by
    simpa [Y_im_zero (c := c) e] using h
  have h'' : YS (c := c) e (-u) = (YS (c := c) e u)⁻¹ :=
    (mul_eq_one_iff_eq_inv').1 h'
  simpa using h''.symm

theorem nontrivial_of_injective {H G : Type*} [Group H] [Group G] [Nontrivial H]
    (f : H →* G) (hf : Function.Injective f) : Nontrivial G := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  refine ⟨⟨f x, 1, ?_⟩⟩
  intro hfx
  apply hx
  apply hf
  simpa using hfx

variable {Xneg1_eq_one_iff_axiom :
    ∀ c : ℕ → ℕ, ∀ u : ℂ, Xneg1S (c := c) u = 1 ↔ u = 0}
variable {Yneg1_eq_one_iff_axiom :
    ∀ c : ℕ → ℕ, ∀ u : ℂ, Yneg1S (c := c) u = 1 ↔ u = 0}
variable {X_eq_one_iff_axiom :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, ∀ u : ℂ, XS (c := c) e u = 1 ↔ u = 0}
variable {Y_eq_one_iff_axiom :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, ∀ u : ℂ, YS (c := c) e u = 1 ↔ u = 0}

include Xneg1_eq_one_iff_axiom
theorem Xneg1_eq_one_iff (u : ℂ) : Xneg1S (c := c) u = 1 ↔ u = 0 :=
  Xneg1_eq_one_iff_axiom (c := c) u

include Yneg1_eq_one_iff_axiom
theorem Yneg1_eq_one_iff (u : ℂ) : Yneg1S (c := c) u = 1 ↔ u = 0 :=
  Yneg1_eq_one_iff_axiom (c := c) u

include X_eq_one_iff_axiom
theorem X_eq_one_iff (e : IndexE c) (u : ℂ) : XS (c := c) e u = 1 ↔ u = 0 :=
  X_eq_one_iff_axiom (c := c) e u

include Y_eq_one_iff_axiom
theorem Y_eq_one_iff (e : IndexE c) (u : ℂ) : YS (c := c) e u = 1 ↔ u = 0 :=
  Y_eq_one_iff_axiom (c := c) e u

theorem nontrivialgens :
    (∀ u : ℂ, Xneg1S (c := c) u = 1 ↔ u = 0) ∧
      (∀ u : ℂ, Yneg1S (c := c) u = 1 ↔ u = 0) ∧
      (∀ e : IndexE c, ∀ u : ℂ, XS (c := c) e u = 1 ↔ u = 0) ∧
      (∀ e : IndexE c, ∀ u : ℂ, YS (c := c) e u = 1 ↔ u = 0) := by
  exact ⟨Xneg1_eq_one_iff_axiom (c := c), Yneg1_eq_one_iff_axiom (c := c),
    X_eq_one_iff_axiom (c := c), Y_eq_one_iff_axiom (c := c)⟩

variable {Xneg1_infinite_order_axiom :
    ∀ c : ℕ → ℕ, ∀ {u : ℂ}, u ≠ 0 → ¬ IsOfFinOrder (Xneg1S (c := c) u)}
variable {Yneg1_infinite_order_axiom :
    ∀ c : ℕ → ℕ, ∀ {u : ℂ}, u ≠ 0 → ¬ IsOfFinOrder (Yneg1S (c := c) u)}
variable {X_infinite_order_axiom :
    ∀ c : ℕ → ℕ, ∀ {e : IndexE c} {u : ℂ}, u ≠ 0 → ¬ IsOfFinOrder (XS (c := c) e u)}
variable {Y_infinite_order_axiom :
    ∀ c : ℕ → ℕ, ∀ {e : IndexE c} {u : ℂ}, u ≠ 0 → ¬ IsOfFinOrder (YS (c := c) e u)}

include Xneg1_infinite_order_axiom
theorem Xneg1_infinite_order {u : ℂ} (hu : u ≠ 0) :
    ¬ IsOfFinOrder (Xneg1S (c := c) u) :=
  Xneg1_infinite_order_axiom (c := c) hu
omit Xneg1_infinite_order_axiom

include Yneg1_infinite_order_axiom
theorem Yneg1_infinite_order {u : ℂ} (hu : u ≠ 0) :
    ¬ IsOfFinOrder (Yneg1S (c := c) u) :=
  Yneg1_infinite_order_axiom (c := c) hu
omit Yneg1_infinite_order_axiom

include X_infinite_order_axiom
theorem X_infinite_order {e : IndexE c} {u : ℂ} (hu : u ≠ 0) :
    ¬ IsOfFinOrder (XS (c := c) e u) :=
  X_infinite_order_axiom (c := c) hu
omit X_infinite_order_axiom

include Y_infinite_order_axiom
theorem Y_infinite_order {e : IndexE c} {u : ℂ} (hu : u ≠ 0) :
    ¬ IsOfFinOrder (YS (c := c) e u) :=
  Y_infinite_order_axiom (c := c) hu
omit Y_infinite_order_axiom

abbrev Zadd := Multiplicative ℤ

variable {Z_to_S : ∀ c : ℕ → ℕ, IndexE c → Zadd →* S (c := c)}
variable {Z_to_S_spec :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, ∀ n : ℤ,
      Z_to_S (c := c) e (Multiplicative.ofAdd n) = XS (c := c) e (n : ℂ)}
variable {Z_to_S_injective_axiom :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, Function.Injective (Z_to_S (c := c) e)}
variable {exists_injective_Z_to_S :
    ∀ c : ℕ → ℕ, ∃ e : IndexE c, Function.Injective (Z_to_S (c := c) e)}
include
  Z_to_S
  Z_to_S_injective_axiom
  exists_injective_Z_to_S

include Z_to_S_injective_axiom
theorem Z_to_S_injective (e : IndexE c) : Function.Injective (Z_to_S (c := c) e) :=
  Z_to_S_injective_axiom (c := c) e
omit Z_to_S_injective_axiom

include Z_to_S exists_injective_Z_to_S
theorem nontrivial_S : Nontrivial (S (c := c)) := by
  classical
  obtain ⟨e, he⟩ := exists_injective_Z_to_S (c := c)
  exact nontrivial_of_injective (f := Z_to_S (c := c) e) he
omit Z_to_S exists_injective_Z_to_S

variable {X_one_iso_Z_axiom :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c, Zadd ≃* Subgroup.zpowers (XS (c := c) e 1)}
include X_one_iso_Z_axiom

def X_one_iso_Z (e : IndexE c) :
    Zadd ≃* Subgroup.zpowers (XS (c := c) e 1) :=
  X_one_iso_Z_axiom (c := c) e
omit X_one_iso_Z_axiom

variable {X_param_iso_C_axiom :
    ∀ c : ℕ → ℕ, ∀ e : IndexE c,
      Multiplicative ℂ ≃* Subgroup.closure (Set.range (fun u : ℂ => XS (c := c) e u))}
include X_param_iso_C_axiom

def X_param_iso_C (e : IndexE c) :
    Multiplicative ℂ ≃* Subgroup.closure (Set.range (fun u : ℂ => XS (c := c) e u)) :=
  X_param_iso_C_axiom (c := c) e
omit X_param_iso_C_axiom

variable {normal_form_conjecture : ∀ c : ℕ → ℕ, Prop}

end Sm

/-! ## Homomorphism F(m) → S(m) -/

namespace FS

variable {c : ℕ → ℕ}

lemma lift_of_eq_mk :
    FreeGroup.lift (fun g : GenU c => Sm.of (c := c) g)
      = PresentedGroup.mk (Sm.rels (c := c)) := by
  apply FreeGroup.ext_hom
  intro g
  rfl

def toS : Fm.F (c := c) →* Sm.S (c := c) :=
  PresentedGroup.toGroup
    (rels := Fm.rels (c := c))
    (f := fun g : GenU c => Sm.of (c := c) g)
    (by
      intro r hr
      rcases hr with ⟨rf, rfl⟩
      cases rf with
      | Re_XX u v =>
          have h := Sm.Xneg1_add (c := c) u v
          have hinv := Sm.Xneg1_inv (c := c) (u + v)
          have h' : Sm.Xneg1S (c := c) (-u - v) =
              (Sm.Xneg1S (c := c) (u + v))⁻¹ := by
            simpa [add_comm, add_left_comm, add_assoc] using hinv.symm
          calc
            FreeGroup.lift (fun g : GenU c => Sm.of (c := c) g)
              (Fm.relWord (c := c) (Fm.RelName.Re_XX u v))
                = Sm.Xneg1S (c := c) (-u - v) * Sm.Xneg1S (c := c) u *
                    Sm.Xneg1S (c := c) v := by
                    simp [Fm.relWord, Fm.Xneg1, Fm.ofGen, Sm.Xneg1S, Sm.of, PresentedGroup.of,
                      mul_assoc]
            _ = (Sm.Xneg1S (c := c) (u + v))⁻¹ * (Sm.Xneg1S (c := c) u * Sm.Xneg1S (c := c) v) := by
                simp [h', mul_assoc]
            _ = 1 := by
                simp [h]
      | Re_YY u v =>
          have h := Sm.Yneg1_add (c := c) u v
          have hinv := Sm.Yneg1_inv (c := c) (u + v)
          have h' : Sm.Yneg1S (c := c) (-u - v) =
              (Sm.Yneg1S (c := c) (u + v))⁻¹ := by
            simpa [add_comm, add_left_comm, add_assoc] using hinv.symm
          calc
            FreeGroup.lift (fun g : GenU c => Sm.of (c := c) g)
              (Fm.relWord (c := c) (Fm.RelName.Re_YY u v))
                = Sm.Yneg1S (c := c) (-u - v) * Sm.Yneg1S (c := c) u *
                    Sm.Yneg1S (c := c) v := by
                    simp [Fm.relWord, Fm.Yneg1, Fm.ofGen, Sm.Yneg1S, Sm.of, PresentedGroup.of,
                      mul_assoc]
            _ = (Sm.Yneg1S (c := c) (u + v))⁻¹ * (Sm.Yneg1S (c := c) u * Sm.Yneg1S (c := c) v) := by
                simp [h', mul_assoc]
            _ = 1 := by
                simp [h]
      | Im_XX e u v =>
          have h := Sm.X_im_add (c := c) e u v
          have hinv := Sm.X_im_inv (c := c) e (u + v)
          have h' : Sm.XS (c := c) e (-u - v) = (Sm.XS (c := c) e (u + v))⁻¹ := by
            simpa [add_comm, add_left_comm, add_assoc] using hinv.symm
          calc
            FreeGroup.lift (fun g : GenU c => Sm.of (c := c) g)
              (Fm.relWord (c := c) (Fm.RelName.Im_XX e u v))
                = Sm.XS (c := c) e (-u - v) * Sm.XS (c := c) e u *
                    Sm.XS (c := c) e v := by
                    simp [Fm.relWord, Fm.X, Fm.ofGen, Sm.XS, Sm.of, PresentedGroup.of, mul_assoc]
            _ = (Sm.XS (c := c) e (u + v))⁻¹ * (Sm.XS (c := c) e u * Sm.XS (c := c) e v) := by
                simp [h', mul_assoc]
            _ = 1 := by
                simp [h]
      | Im_YY e u v =>
          have h := Sm.Y_im_add (c := c) e u v
          have hinv := Sm.Y_im_inv (c := c) e (u + v)
          have h' : Sm.YS (c := c) e (-u - v) = (Sm.YS (c := c) e (u + v))⁻¹ := by
            simpa [add_comm, add_left_comm, add_assoc] using hinv.symm
          calc
            FreeGroup.lift (fun g : GenU c => Sm.of (c := c) g)
              (Fm.relWord (c := c) (Fm.RelName.Im_YY e u v))
                = Sm.YS (c := c) e (-u - v) * Sm.YS (c := c) e u *
                    Sm.YS (c := c) e v := by
                    simp [Fm.relWord, Fm.Y, Fm.ofGen, Sm.YS, Sm.of, PresentedGroup.of, mul_assoc]
            _ = (Sm.YS (c := c) e (u + v))⁻¹ * (Sm.YS (c := c) e u * Sm.YS (c := c) e v) := by
                simp [h', mul_assoc]
            _ = 1 := by
                simp [h]
      | U_Xneg1_X j k u v =>
          simpa [Fm.relWord, Sm.relWord, Sm.Xneg1S, Sm.Xneg1, Sm.XS, Sm.X, Sm.of, Sm.ofGen,
            PresentedGroup.of, lift_of_eq_mk (c := c)]
            using Sm.relWord_eq_one (c := c) (Sm.RelName.U_Xneg1_X j k u v)
      | U_Yneg1_Y j k u v =>
          simpa [Fm.relWord, Sm.relWord, Sm.Yneg1S, Sm.Yneg1, Sm.YS, Sm.Y, Sm.of, Sm.ofGen,
            PresentedGroup.of, lift_of_eq_mk (c := c)]
            using Sm.relWord_eq_one (c := c) (Sm.RelName.U_Yneg1_Y j k u v)
      | U_Yneg1_X0 j k u v =>
          simpa [Fm.relWord, Sm.relWord, Sm.Yneg1S, Sm.Yneg1, Sm.XS, Sm.X, Sm.of, Sm.ofGen,
            PresentedGroup.of, lift_of_eq_mk (c := c)]
            using Sm.relWord_eq_one (c := c) (Sm.RelName.U_Yneg1_X0 j k u v)
      | U_Xneg1_Y0 j k u v =>
          simpa [Fm.relWord, Sm.relWord, Sm.Xneg1S, Sm.Xneg1, Sm.YS, Sm.Y, Sm.of, Sm.ofGen,
            PresentedGroup.of, lift_of_eq_mk (c := c)]
            using Sm.relWord_eq_one (c := c) (Sm.RelName.U_Xneg1_Y0 j k u v)
      | U_comm_XY e f h u v =>
          simpa [Fm.relWord, Sm.relWord, Sm.XS, Sm.X, Sm.YS, Sm.Y, Sm.of, Sm.ofGen,
            PresentedGroup.of, lift_of_eq_mk (c := c)]
            using Sm.relWord_eq_one (c := c) (Sm.RelName.U_comm_XY e f h u v)
      | U_XY_j2a k u v =>
          simpa [Fm.relWord, Sm.relWord, Sm.Xneg1S, Sm.Xneg1, Sm.XS, Sm.X, Sm.YS, Sm.Y, Sm.of,
            Sm.ofGen, PresentedGroup.of, lift_of_eq_mk (c := c)]
            using Sm.relWord_eq_one (c := c) (Sm.RelName.U_XY_j2a k u v)
      | U_XY_j2b k u v =>
          simpa [Fm.relWord, Sm.relWord, Sm.Yneg1S, Sm.Yneg1, Sm.XS, Sm.X, Sm.YS, Sm.Y, Sm.of,
            Sm.ofGen, PresentedGroup.of, lift_of_eq_mk (c := c)]
            using Sm.relWord_eq_one (c := c) (Sm.RelName.U_XY_j2b k u v))

end FS

/-! ## Homomorphism S(m) → G(m) -/

namespace SG

variable {c : ℕ → ℕ}

def toGMap : GenU c → Gm.G (c := c)
  | GenU.Xneg1 u => Gm.Xneg1G (c := c) u
  | GenU.Yneg1 u => Gm.Yneg1G (c := c) u
  | GenU.X e u => Gm.XG (c := c) e u
  | GenU.Y e u => Gm.YG (c := c) e u

def commG (a b : Gm.G (c := c)) : Gm.G (c := c) := a * b * a⁻¹ * b⁻¹

@[simp] lemma lift_toGMap_ofGen (g : GenU c) :
    FreeGroup.lift (toGMap (c := c)) (Sm.ofGen g) = toGMap (c := c) g := by
  simp [Sm.ofGen]

def toG : Sm.S (c := c) →* Gm.G (c := c) :=
  PresentedGroup.toGroup
    (rels := Sm.rels (c := c))
    (f := toGMap (c := c))
    (by
      intro r hr
      rcases hr with ⟨rs, rfl⟩
      cases rs with
      | Re_XX u v =>
          have h := Gm.Xneg1_add (c := c) u v
          calc
            FreeGroup.lift (toGMap (c := c)) (Sm.relWord (c := c) (Sm.RelName.Re_XX u v))
                = (Gm.Xneg1G (c := c) (u + v))⁻¹ *
                    (Gm.Xneg1G (c := c) u * Gm.Xneg1G (c := c) v) := by
                    simp [Sm.relWord, Sm.Xneg1, toGMap, mul_assoc]
            _ = 1 := by
                simp [h]
      | Re_YY u v =>
          have h := Gm.Yneg1_add (c := c) u v
          calc
            FreeGroup.lift (toGMap (c := c)) (Sm.relWord (c := c) (Sm.RelName.Re_YY u v))
                = (Gm.Yneg1G (c := c) (u + v))⁻¹ *
                    (Gm.Yneg1G (c := c) u * Gm.Yneg1G (c := c) v) := by
                    simp [Sm.relWord, Sm.Yneg1, toGMap, mul_assoc]
            _ = 1 := by
                simp [h]
      | Im_XX e u v =>
          have h := Gm.X_im_add (c := c) e u v
          calc
            FreeGroup.lift (toGMap (c := c)) (Sm.relWord (c := c) (Sm.RelName.Im_XX e u v))
                = (Gm.XG (c := c) e (u + v))⁻¹ *
                    (Gm.XG (c := c) e u * Gm.XG (c := c) e v) := by
                    simp [Sm.relWord, Sm.X, toGMap, mul_assoc]
            _ = 1 := by
                simp [h]
      | Im_YY e u v =>
          have h := Gm.Y_im_add (c := c) e u v
          calc
            FreeGroup.lift (toGMap (c := c)) (Sm.relWord (c := c) (Sm.RelName.Im_YY e u v))
                = (Gm.YG (c := c) e (u + v))⁻¹ *
                    (Gm.YG (c := c) e u * Gm.YG (c := c) e v) := by
                    simp [Sm.relWord, Sm.Y, toGMap, mul_assoc]
            _ = 1 := by
                simp [h]
      | U_Xneg1_X j k u v =>
          simpa [Sm.relWord, Sm.Xneg1, Sm.X, Sm.Y, toGMap, Gm.relWord, Gm.Xneg1, Gm.X, Gm.Y,
            Gm.Xneg1G, Gm.XG, Gm.YG, Gm.of, Gm.ofGen, PresentedGroup.of, mul_assoc]
            using Gm.relWord_eq_one (c := c) (Gm.RelName.U_Xneg1_X j k u v)
      | U_Yneg1_Y j k u v =>
          simpa [Sm.relWord, Sm.Yneg1, Sm.X, Sm.Y, toGMap, Gm.relWord, Gm.Yneg1, Gm.X, Gm.Y,
            Gm.Yneg1G, Gm.XG, Gm.YG, Gm.of, Gm.ofGen, PresentedGroup.of, mul_assoc]
            using Gm.relWord_eq_one (c := c) (Gm.RelName.U_Yneg1_Y j k u v)
      | U_Yneg1_X0 j k u v =>
          simpa [Sm.relWord, Sm.Yneg1, Sm.X, Sm.Y, toGMap, Gm.relWord, Gm.Yneg1, Gm.X, Gm.Y,
            Gm.Yneg1G, Gm.XG, Gm.YG, Gm.of, Gm.ofGen, PresentedGroup.of, mul_assoc]
            using Gm.relWord_eq_one (c := c) (Gm.RelName.U_Yneg1_X0 j k u v)
      | U_Xneg1_Y0 j k u v =>
          simpa [Sm.relWord, Sm.Xneg1, Sm.X, Sm.Y, toGMap, Gm.relWord, Gm.Xneg1, Gm.X, Gm.Y,
            Gm.Xneg1G, Gm.XG, Gm.YG, Gm.of, Gm.ofGen, PresentedGroup.of, mul_assoc]
            using Gm.relWord_eq_one (c := c) (Gm.RelName.U_Xneg1_Y0 j k u v)
      | U_comm_XY e f h u v =>
          simpa [Sm.relWord, Sm.X, Sm.Y, toGMap, Gm.relWord, Gm.X, Gm.Y, Gm.XG, Gm.YG, Gm.of,
            Gm.ofGen, PresentedGroup.of, mul_assoc]
            using Gm.relWord_eq_one (c := c) (Gm.RelName.U_comm_XY e f h u v)
      | U_XY_j2a k u v =>
          have h := Gm.relWord_eq_one (c := c) (Gm.RelName.U_XY_j2a k u v)
          have h' :
              commG (c := c) (Gm.XG (c := c) (idx c 1 2 k) u)
                (Gm.YG (c := c) (idx c 0 2 k) v)
                = Gm.Xneg1G (c := c) (u * v) := by
              have h0 :
                  commG (c := c) (Gm.XG (c := c) (idx c 1 2 k) u)
                    (Gm.YG (c := c) (idx c 0 2 k) v) *
                    (Gm.Xneg1G (c := c) (u * v))⁻¹ = 1 := by
                  simpa [Gm.relWord, Gm.comm, commG, Gm.Xneg1, Gm.X, Gm.Y, mul_assoc] using h
              exact (mul_inv_eq_one.mp h0)
          calc
            FreeGroup.lift (toGMap (c := c)) (Sm.relWord (c := c) (Sm.RelName.U_XY_j2a k u v))
                = Gm.Xneg1G (c := c) (-u * v) *
                    commG (c := c) (Gm.XG (c := c) (idx c 1 2 k) u)
                      (Gm.YG (c := c) (idx c 0 2 k) v) := by
                    simp [Sm.relWord, Sm.comm, Sm.Xneg1, Sm.X, Sm.Y, toGMap, commG, mul_assoc]
            _ = Gm.Xneg1G (c := c) (-u * v) * Gm.Xneg1G (c := c) (u * v) := by
                simp [h']
            _ = 1 := by
                have hinv :
                    Gm.Xneg1G (c := c) (-(u * v)) = (Gm.Xneg1G (c := c) (u * v))⁻¹ := by
                  simpa using (Gm.Xneg1_inv (c := c) (u * v)).symm
                simp [hinv]
      | U_XY_j2b k u v =>
          have h := Gm.relWord_eq_one (c := c) (Gm.RelName.U_XY_j2b k u v)
          have h' :
              commG (c := c) (Gm.XG (c := c) (idx c 0 2 k) u)
                (Gm.YG (c := c) (idx c 1 2 k) v)
                = Gm.Yneg1G (c := c) (u * v) := by
              have h0 :
                  commG (c := c) (Gm.XG (c := c) (idx c 0 2 k) u)
                    (Gm.YG (c := c) (idx c 1 2 k) v) *
                    (Gm.Yneg1G (c := c) (u * v))⁻¹ = 1 := by
                  simpa [Gm.relWord, Gm.comm, commG, Gm.Yneg1, Gm.X, Gm.Y, mul_assoc] using h
              exact (mul_inv_eq_one.mp h0)
          calc
            FreeGroup.lift (toGMap (c := c)) (Sm.relWord (c := c) (Sm.RelName.U_XY_j2b k u v))
                = Gm.Yneg1G (c := c) (-u * v) *
                    commG (c := c) (Gm.XG (c := c) (idx c 0 2 k) u)
                      (Gm.YG (c := c) (idx c 1 2 k) v) := by
                    simp [Sm.relWord, Sm.comm, Sm.Yneg1, Sm.X, Sm.Y, toGMap, commG, mul_assoc]
            _ = Gm.Yneg1G (c := c) (-u * v) * Gm.Yneg1G (c := c) (u * v) := by
                simp [h']
            _ = 1 := by
                have hinv :
                    Gm.Yneg1G (c := c) (-(u * v)) = (Gm.Yneg1G (c := c) (u * v))⁻¹ := by
                  simpa using (Gm.Yneg1_inv (c := c) (u * v)).symm
                simp [hinv]
      | Re_XY s t =>
          have h := Gm.Re_XY_rel (c := c) s t
          simpa [Sm.relWord, Sm.Xneg1, Sm.Yneg1, Sm.X, Sm.Y, toGMap, mul_assoc] using h
      | Re_wX u =>
          have h := Gm.Re_wX_rel (c := c) u
          simpa [Sm.relWord, Sm.wNeg1One, Sm.wNeg1, Sm.Xneg1, Sm.Yneg1, Sm.X, Sm.Y, toGMap,
            Gm.wNeg1OneG, Gm.wNeg1G, mul_assoc] using h
      | Re_wY u =>
          have h := Gm.Re_wY_rel (c := c) u
          simpa [Sm.relWord, Sm.wNeg1One, Sm.wNeg1, Sm.Xneg1, Sm.Yneg1, Sm.X, Sm.Y, toGMap,
            Gm.wNeg1OneG, Gm.wNeg1G, mul_assoc] using h
      | Im_XY e s t =>
          have h := Gm.Im_XY_rel (c := c) e s t
          simpa [Sm.relWord, Sm.X, Sm.Y, toGMap, mul_assoc] using h
      | Im_wX e u =>
          have h := Gm.Im_wX_rel (c := c) e u
          simpa [Sm.relWord, Sm.wImOne, Sm.wIm, Sm.X, Sm.Y, toGMap, Gm.wImOneG, Gm.wImG,
            mul_assoc] using h
      | Im_wY e u =>
          have h := Gm.Im_wY_rel (c := c) e u
          simpa [Sm.relWord, Sm.wImOne, Sm.wIm, Sm.X, Sm.Y, toGMap, Gm.wImOneG, Gm.wImG,
            mul_assoc] using h
      | U_w_X e u =>
          have h := Gm.U_w_X_rel (c := c) e u
          simpa [Sm.relWord, Sm.wNeg1One, Sm.wNeg1, Sm.X, Sm.Y, toGMap, Gm.wNeg1OneG, Gm.wNeg1G,
            mul_assoc] using h
      | U_w_Y e u =>
          have h := Gm.U_w_Y_rel (c := c) e u
          simpa [Sm.relWord, Sm.wNeg1One, Sm.wNeg1, Sm.X, Sm.Y, toGMap, Gm.wNeg1OneG, Gm.wNeg1G,
            mul_assoc] using h)

end SG

end Geometry
